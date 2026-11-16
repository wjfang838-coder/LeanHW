"""Typed hierarchy -> resolved network + fixed-read nonblocking processes.

Instance bodies are taken from Slang's actual elaboration, including parameters.
Input/output connections become typed word wires. Child inout aliases and internal
clock generation require additional support; physical top-level inout is retained.
"""
from collections import Counter
from .clocked import ClockedImporter
from .slang import SlangImporter, Term, no_drive_strength
from .importer import require, lean_string


class BodyImporter(ClockedImporter):
    def __init__(self, owner, body, path, mapping):
        self.owner, self.body, self.path, self.mapping = owner, body, path, mapping
        self.members = list(body)
        self.symbols = {x.name:x for x in self.members if x.kind.name in ('Net','Variable')}
        self.input_names = {x.name for x in self.members if x.kind.name=='Port' and x.direction.name=='In'}
        self.counts=Counter();self.expression_reads=set();self.selection_count=0

    def internal(self,name): return self.mapping[name]

    def var(self,name):
        require(name in self.symbols,'unknown hierarchy variable: '+name)
        w=self.width(self.symbols[name].type);n=self.internal(name)
        # Pure input-port aliases share their external edge signal. Preserve
        # that identity in RHS/reset conditions as well as sensitivity lists;
        # otherwise synthesis may misclassify the asynchronous process.
        if name in self.input_names and n in self.owner.clock_aliases:
            n=self.owner.clock_aliases[n]
        return Term(w,f'(.var {lean_string(n)} {w})',frozenset([n]))

    def source_statement(self,stmt):
        if stmt is None or stmt.kind.name=='Empty': return 'Source.Stmt.skip'
        k=stmt.kind.name
        if k=='Block': return self.source_statement(stmt.body)
        if k=='List':
            result='Source.Stmt.skip'
            for child in stmt.list: result=f'(Source.Stmt.seq {result} {self.source_statement(child)})'
            return result
        if k=='ExpressionStatement':
            name,value=self.assignment(stmt.expr,{})
            return f'(Source.Stmt.assign {{name := {lean_string(self.internal(name))}, width := {value.width}, expr := {value.code}}})'
        if k=='Conditional':
            return (f'(Source.Stmt.ite {self.expression(stmt.conditions[0].expr).code} '
                    f'{self.source_statement(stmt.ifTrue)} {self.source_statement(stmt.ifFalse)})')
        if k=='Case':
            arms=f'(Source.Arms.default {self.source_statement(stmt.defaultCase)})'
            for item in reversed(stmt.items):
                labels=', '.join(self.expression(x).code for x in item.expressions)
                arms=f'(Source.Arms.arm [{labels}] {self.source_statement(item.stmt)} {arms})'
            return f'(Source.Stmt.cases {self.expression(stmt.expr).code} {arms})'
        raise ValueError('unsupported reflected hierarchy statement: '+k)


class SystemImporter(SlangImporter):
    def __init__(self,source,top):
        super().__init__(source,top,allow_inout=True)
        self.registry={};self.frames=[];self.nba_processes=[];self.comb_processes=[]
        self.network_drivers={};self.state_names=set();self.clock_aliases={}
        self.hierarchy=[]
        # Reserve all names up front, including child-instance paths. Length
        # coding distinguishes names that contain underscores.
        candidates=[]
        def scan(body,path):
            for symbol in body:
                if symbol.kind.name in ('Net','Variable') and path:
                    candidates.append(self.path_name(path,symbol.name))
                elif symbol.kind.name=='Instance': scan(symbol.body,path+(symbol.name,))
        scan(self.body,())
        candidates += ['o_'+n for n in self.output_names+self.inout_names]
        self.prefix='_v2_'
        while any(self.prefix+n in self.symbols for n in candidates): self.prefix+='x'
        self.root_mapping={n:(self.prefix+'o_'+n if n in self.output_names+self.inout_names else n) for n in self.symbols}

    @staticmethod
    def path_name(path,name):
        return 'h_'+''.join(str(len(x))+'_'+x+'_' for x in path+(name,))

    def frame(self,body,path):
        mapping={s.name:(self.prefix+self.path_name(path,s.name) if path else self.root_mapping[s.name])
                 for s in body if s.kind.name in ('Net','Variable')}
        frame=BodyImporter(self,body,path,mapping)
        ports={s.name:s for s in frame.members if s.kind.name=='Port'}
        for name,symbol in frame.symbols.items():
            n=frame.internal(name)
            require(n not in self.registry,'hierarchy name collision')
            require(symbol.type.isFourState,'two-state hierarchy signal requires unknown coercion')
            width=self.width(symbol.type)
            self.registry[n]={'name':n,'width':width,'kind':symbol.kind.name,'port':None,
                              'origin':'.'.join(path+(name,)),
                              'input':not path and name in self.input_names,
                              'local_input':name in frame.input_names}
            if not path and name in self.inout_names:self.registry[n]['port']=name
            if not path and name in self.input_names and width==1:self.clock_aliases[n]=name
        for name,port in ports.items():
            require(port.direction.name in ('In','Out') or (not path and port.direction.name=='InOut'),
                    'child inout needs bidirectional alias support')
            require(port.internalSymbol is not None and port.internalSymbol.name==name,'complex hierarchy port binding unsupported')
            typ=port.type;w=self.width(typ)
            require(not typ.hasFixedRange or (typ.fixedRange.right==0 and typ.fixedRange.left==w-1),
                    'nondefault hierarchy port layout unsupported')
        self.frames.append(frame)
        self.hierarchy.append({'path':'.'.join(path) or self.top,'module':body.definition.name,
                               'signals':len(frame.symbols)})
        return frame

    def drive(self,name,value):
        require(name in self.registry and not self.registry[name]['input'],'unknown/input hierarchy driver: '+name)
        require(value.width==self.registry[name]['width'],'hierarchy connection width mismatch: '+name)
        self.network_drivers.setdefault(name,[]).append(value)

    def connect(self,parent,instance,child):
        for connection in instance.portConnections:
            port,expr=connection.port,connection.expression
            require(expr is not None and connection.ifaceConn == (None,None),'unconnected/interface port needs explicit support')
            name=child.internal(port.name)
            if port.direction.name=='In':
                self.drive(name,parent.expression(expr))
                direct=expr
                while direct.kind.name=='Conversion' and self.width(direct.type)==self.width(direct.operand.type):
                    direct=direct.operand
                if direct.kind.name=='NamedValue':
                    root=self.clock_aliases.get(parent.internal(direct.symbol.name))
                    if root is not None:self.clock_aliases[name]=root
            else:
                require(port.direction.name=='Out' and expr.kind.name=='Assignment' and not expr.isNonBlocking
                        and not expr.isCompound and expr.timingControl is None,
                        'unsupported output hierarchy connection')
                require(expr.left.kind.name=='NamedValue' and expr.right.kind.name=='EmptyArgument',
                        'output slices/conversions require port assignment lowering')
                self.drive(parent.internal(expr.left.symbol.name),child.var(port.name))

    def visit(self,frame):
        for symbol in frame.members:
            kind=symbol.kind.name
            if kind in ('Port','Parameter'): continue
            if kind in ('Net','Variable'):
                if kind=='Net':
                    require(symbol.delay is None and symbol.chargeStrength is None and no_drive_strength(symbol)
                            and symbol.netType.netKind.name in ('Wire','Tri'),'hierarchy net type/delay/strength unsupported')
                if symbol.initializer is not None:
                    require(kind=='Net','hierarchy state initialization needs initial-event semantics')
                    self.drive(frame.internal(symbol.name),frame.expression(symbol.initializer))
                continue
            if kind=='Instance':
                require(symbol.isModule and not symbol.arrayPath,'interface/instance array unsupported')
                child=self.frame(symbol.body,frame.path+(symbol.name,))
                self.connect(frame,symbol,child);self.visit(child);continue
            if kind=='ContinuousAssign':
                require(symbol.delay is None and no_drive_strength(symbol),'continuous hierarchy delay/strength unsupported')
                name,value=frame.assignment(symbol.assignment,{})
                self.drive(frame.internal(name),value);continue
            require(kind=='ProceduralBlock','unsupported hierarchy member: '+kind)
            body=symbol.body
            if symbol.procedureKind.name=='AlwaysComb' or (symbol.procedureKind.name=='Always' and body.kind.name=='Timed' and body.timing.kind.name=='ImplicitEvent'):
                if symbol.procedureKind.name=='Always':body=body.stmt
                values=frame.statement(body,{})
                written={frame.internal(n) for n in values}
                require(all(not (value.deps & written) for value in values.values()),'combinational hierarchy latch/read before write')
                self.comb_processes.append((frame.source_statement(body),{frame.internal(n):v for n,v in values.items()}))
                for name,value in values.items():self.drive(frame.internal(name),value)
                continue
            require(symbol.procedureKind.name=='Always' and body.kind.name=='Timed'
                    and body.timing.kind.name in ('EventList','SignalEvent'),'unsupported hierarchy process timing')
            events=list(body.timing.events) if body.timing.kind.name=='EventList' else [body.timing]
            reflected=[]
            for event in events:
                require(event.kind.name=='SignalEvent' and event.edge.name in ('PosEdge','NegEdge')
                        and event.iffCondition is None and event.expr.kind.name=='NamedValue','unsupported hierarchy edge control')
                root=self.clock_aliases.get(frame.internal(event.expr.symbol.name))
                require(root is not None,'internally generated clock/reset needs event network semantics')
                reflected.append((root,event.edge.name=='PosEdge'))
            require(bool(reflected),'empty hierarchy event list')
            targets=set();stmt=frame.nba_statement(body.stmt,targets)
            global_targets=sorted(frame.internal(n) for n in targets)
            require(not self.state_names.intersection(global_targets),'multiple hierarchy processes write one state')
            self.state_names.update(global_targets)
            self.nba_processes.append((reflected,global_targets,stmt))

    def build(self):
        root=self.frame(self.body,());self.visit(root)
        require(bool(self.nba_processes),'system path requires clocked state')
        require(not self.state_names.intersection(self.network_drivers),'hierarchy state has another driver')
        known={n for n,d in self.registry.items() if d['input']} | self.state_names
        pending={n:self.network_drivers.get(n,[]) for n in self.registry if n not in known}
        nodes=[]
        while pending:
            ready=[n for n,drivers in pending.items() if all(v.deps<=known for v in drivers)]
            require(bool(ready),'resolved hierarchy cycle/undriven state: '+', '.join(pending))
            for n in ready:
                drivers=pending.pop(n);info=self.registry[n];w=info['width']
                if info['kind']=='Variable' and not info['local_input']:
                    require(len(drivers)==1,'uninitialized/multiple-driven hierarchy variable: '+n)
                if info['port'] is not None or len(drivers)>1:
                    port='none' if info['port'] is None else 'some '+lean_string(info['port'])
                    nodes.append(f'(.net {{name := {lean_string(n)}, width := {w}, port := {port}, drivers := [{", ".join(v.code for v in drivers)}]}})')
                else:
                    value=drivers[0].code if drivers else f'(@Expr.fill {w} .z)'
                    nodes.append(f'(.wire {{name := {lean_string(n)}, width := {w}, expr := {value}}})')
                known.add(n)
        for frame in self.frames:
            require({frame.internal(n) for n in frame.expression_reads}<=known,'unbound hierarchical process read')
        states=[(n,d['width']) for n,d in self.registry.items() if n in self.state_names]
        signed_ports=[m.name for m in self.members if m.kind.name=='Port' and m.type.isSigned]
        scalar_ports=[m.name for m in self.members if m.kind.name=='Port' and m.type.isScalar]
        def ports(pairs):return ', '.join(f'{{name := {lean_string(n)}, width := {w}}}' for n,w in pairs)
        def out_wire(n):
            v=root.var(n)
            return f'{{name := {lean_string(n)}, width := {v.width}, expr := {v.code}}}'
        definitions=[];processes=[];proofs=[];certificates=[]
        for i,(events,targets,stmt) in enumerate(self.nba_processes):
            pname=f'nba_process_{i}';definitions.append(f'def {pname} : NBA.Stmt := {stmt}')
            es=', '.join(f'{{name := {lean_string(n)}, positive := {str(pos).lower()}}}' for n,pos in events)
            ts=', '.join(lean_string(n) for n in targets)
            processes.append(f'{{events := [{es}], targets := [{ts}], body := {pname}}}')
            for j,name in enumerate(targets):
                n=lean_string(name);w=self.registry[name]['width'];theorem=f'source_nba_{i}_{j}_correct'
                certificates += [f'theorem {theorem} (env : Env) :',
                    f'  eval (NBA.lower {pname} {n} (.var {n} {w})) env =',
                    f'    NBA.execute {pname} {n} env (eval (.var {n} {w}) env) := NBA.lower_correct _ _ _ _']
                proofs.append(theorem)
        for i,(stmt,values) in enumerate(self.comb_processes):
            pname=f'comb_process_{i}';definitions.append(f'def {pname} : Source.Stmt := {stmt}')
            certificates += [f'theorem {pname}_valid : Source.stmtValid source_scope {pname} = true := by decide +kernel']
            for j,(name,value) in enumerate(sorted(values.items())):
                target=f'(Expr.var {lean_string(name)} {value.width})';theorem=f'source_comb_{i}_{j}_correct'
                certificates += [f'theorem {theorem} (env : Env) :',
                    f'  eval {value.code} env = eval {target} (Source.execute {pname} env) := by',
                    f'  have h := Source.lower_correct {pname} source_scope {pname}_valid {target} (by decide +kernel) env',
                    f'  simp only [{pname}, Source.lower, Source.lowerArms, Source.substOne, Source.ifTest, Source.caseTest, reduceIte, reduceDIte, String.reduceEq] at h',
                    '  simpa only [eval, Source.mux_same] using h']
                proofs.append(theorem)
        proofs += ['source_resolution_step','source_resolution_observe']
        self.metadata.update(source_semantics='elaborated hierarchy; resolved top inout; fixed-read NBA; pre-edge stable combinational inputs',
            hierarchy=self.hierarchy,state_bits=sum(w for _,w in states),states=[{'name':n,'width':w} for n,w in states],
            state_origins={n:self.registry[n]['origin'] for n,_ in states},
            events=[e for e,_,_ in self.nba_processes],signed_ports=signed_ports,network_nodes=len(nodes),
            scalar_ports=scalar_ports,
            clock_aliases={n:r for n,r in self.clock_aliases.items() if n!=r},
            dynamic_selections=sum(f.selection_count for f in self.frames),source_proofs=proofs,
            source_proof_scope='actual reflected blocking/NBA processes and resolved-vs-lowered state/observation bridge; elaboration, hierarchy connections, selection expansion and HDL serialization remain frontend boundaries')
        self.model_text=f'''import LeanRTL.Core.FourStateSystem
open LeanRTL.FourState
set_option maxRecDepth 32768
set_option maxHeartbeats 16000000
{chr(10).join(definitions)}
def impl : Resolved.System := {{
  network := {{
    name := {lean_string(self.top)}
    inputs := [{ports(self.inputs+states)}]
    nodes := [{','.join(nodes)}]
    outputs := [{', '.join(out_wire(n) for n in self.output_names)}]
  }}
  states := [{ports(states)}]
  processes := [{', '.join(processes)}]
  portOrder := [{', '.join(lean_string(n) for n in self.ports)}]
  signedPorts := [{', '.join(lean_string(n) for n in signed_ports)}]
  scalarPorts := [{', '.join(lean_string(n) for n in scalar_ports)}]
}}
def source_scope := Source.allScope impl.network.lower
theorem system_valid : impl.valid = true := by decide +kernel
{chr(10).join(certificates)}
theorem source_resolution_step (state : NBA.Snapshot) (before after : Env) :
  impl.lower.step state before after = impl.step state before after := Resolved.system_step_correct _ _ _ _
theorem source_resolution_observe (state : NBA.Snapshot) (input : Env) :
  impl.lower.observe state input = impl.observe state input := Resolved.system_observe_correct _ _ _
{chr(10).join('#print axioms '+p for p in proofs)}
'''
        external='n'
        for n in reversed(self.inout_names): external=f'if n == {lean_string(n)} then {lean_string("__external_"+n)} else ({external})'
        return self.model_text+f'''
def parseInputs (line : String) : NBA.Snapshot :=
  (line.splitOn " ").filterMap fun token =>
    match token.splitOn "=" with
    | [n,v] => some (({external}),v.toList.reverse.map fun c => match c with
        | '0' => Bit.zero | '1' => .one | 'z' => .z | _ => .x)
    | _ => none
def main (args : List String) : IO UInt32 := do
  match args with
  | ["export", path] => IO.FS.writeFile path impl.emit; return 0
  | ["eval", path] =>
    let text ← IO.FS.readFile path
    let mut state := impl.initial
    let mut before : Env := fun _ _ => .x
    for line in text.splitOn "\\n" do
      if !line.isEmpty then
        let inputs := parseInputs line
        let after := valuesEnv inputs (fun _ _ => .x)
        state := impl.step state before after
        IO.println (String.intercalate " " ((impl.observe state after).map fun (n,v) => n ++ "=" ++ v))
        before := after
    return 0
  | _ => throw (IO.userError "usage: export FILE | eval INPUTS")
'''
