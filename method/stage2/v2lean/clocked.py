"""Direct AST import of nonblocking-only edge processes and packed selections.

The clocked profile models input transitions and settled NBA commit. It keeps
the source process tree and rejects mixed blocking/NBA updates and shared state
writers. Hierarchy and resolved buses will be composed with this domain later.
"""
from .slang import SlangImporter, Term, const, node, no_drive_strength
from .importer import require, lean_string


class ClockedImporter(SlangImporter):
    def __init__(self, source, top, *, materialize_combinational=False):
        super().__init__(source, top)
        self.materialize_combinational = materialize_combinational
        prefix = '__nba_'
        while any(prefix+n in self.symbols for n in self.output_names): prefix += '_'
        self.aliases = {n: prefix+n for n in self.output_names}
        self.clocked_processes = []
        self.state_names = set()
        self.selection_count = 0
        self.expression_reads = set()

    def internal(self, name):
        return self.aliases.get(name, name)

    def var(self, name):
        value = super().var(name)
        return Term(value.width, f'(.var {lean_string(self.internal(name))} {value.width})', value.deps)

    @staticmethod
    def slice(value, lo, width):
        return Term(width, f'(.slice {lo} {width} {{}})', value.deps, (value,))

    def padded_slice(self, value, lo, width):
        """Constant packed slice, with X for every out-of-range read bit."""
        high = min(value.width, lo+width)
        low = max(0, lo)
        if high <= low: return Term(width, f'(@Expr.fill {width} .x)')
        result = self.slice(value, low, high-low)
        if low > lo:
            result = self.concat(result, Term(low-lo, f'(@Expr.fill {low-lo} .x)'))
        if high < lo+width:
            result = self.concat(Term(lo+width-high, f'(@Expr.fill {lo+width-high} .x)'), result)
        return result

    def selection(self, expr):
        require(expr.value.type.hasFixedRange, 'packed selection requires a fixed range')
        span = expr.value.type.fixedRange
        total = self.width(expr.value.type)
        require(span.right == 0 and span.left == total-1, 'nondefault packed layout unsupported')
        width = self.width(expr.type)
        if expr.kind.name == 'ElementSelect':
            index = expr.selector
        elif expr.selectionKind.name == 'Simple':
            high, low = self.integer(expr.left), self.integer(expr.right)
            require(high-low+1 == width, 'packed range direction mismatch')
            return width, low, None
        else:
            require(expr.selectionKind.name == 'IndexedUp', 'descending indexed selection needs support')
            require(self.integer(expr.right) == width, 'indexed selection width mismatch')
            index = expr.left
        if index.constant is not None and not index.constant.value.hasUnknown:
            return width, self.integer(index), None
        value = self.expression(index)
        # Enumerate only base indices whose selected interval intersects the
        # declaration, without making assumptions about the expression's range.
        minimum = -(1 << (value.width-1)) if index.type.isSigned else 0
        maximum = (1 << (value.width-(1 if index.type.isSigned else 0)))-1
        bases = range(max(minimum, 1-width), min(maximum, total-1)+1)
        self.selection_count += 1
        return width, None, (value, bases)

    def expression(self, expr, local=None):
        if expr.kind.name == 'NamedValue' and expr.symbol.kind.name != 'Parameter':
            self.expression_reads.add(expr.symbol.name)
        if expr.kind.name in ('RangeSelect', 'ElementSelect'):
            value = self.expression(expr.value, local)
            width, fixed, dynamic = self.selection(expr)
            if dynamic is None: return self.padded_slice(value, fixed, width)
            index, bases = dynamic
            result = Term(width, f'(@Expr.fill {width} .x)')
            for base in reversed(list(bases)):
                result = node(width, 'mux', node(1, 'caseEq', index, const(index.width, base)),
                              self.padded_slice(value, base, width), result)
            return result
        return super().expression(expr, local)

    def nba_assignment(self, expr, targets):
        require(expr.kind.name == 'Assignment' and expr.isNonBlocking and not expr.isCompound
                and expr.timingControl is None, 'clocked process requires untimed nonblocking assignments')
        lhs = expr.left
        if lhs.kind.name == 'NamedValue':
            base = lhs
            width, fixed, dynamic = self.width(lhs.type), 0, None
        else:
            require(lhs.kind.name in ('RangeSelect','ElementSelect') and lhs.value.kind.name == 'NamedValue',
                    'unsupported nonblocking lvalue')
            base = lhs.value
            width, fixed, dynamic = self.selection(lhs)
        name = base.symbol.name
        require(name in self.symbols and self.symbols[name].kind.name == 'Variable'
                and name not in self.input_names, 'NBA destination must be a local variable')
        targets.add(name)
        rhs = self.expression(expr.right)
        require(rhs.width == width, 'NBA assignment width mismatch')
        total = self.width(base.type)
        def write_at(lo):
            start, stop = max(0,lo), min(total,lo+width)
            if stop <= start: return 'NBA.Stmt.skip'
            part = rhs if start == lo and stop == lo+width else self.slice(rhs,start-lo,stop-start)
            return f'(NBA.Stmt.write {lean_string(self.internal(name))} {start} {part.code})'
        if dynamic is None: return write_at(fixed)
        index,bases = dynamic
        arms = '(NBA.Arms.default NBA.Stmt.skip)'
        for lo in reversed(list(bases)):
            arms = f'(NBA.Arms.arm [{const(index.width,lo).code}] {write_at(lo)} {arms})'
        return f'(NBA.Stmt.cases {index.code} {arms})'

    def nba_statement(self, stmt, targets):
        if stmt is None or stmt.kind.name == 'Empty': return 'NBA.Stmt.skip'
        kind = stmt.kind.name
        if kind == 'Block':
            require(stmt.blockKind.name == 'Sequential', 'parallel clocked block unsupported')
            return self.nba_statement(stmt.body,targets)
        if kind == 'List':
            result = 'NBA.Stmt.skip'
            for child in stmt.list:
                result = f'(NBA.Stmt.seq {result} {self.nba_statement(child,targets)})'
            return result
        if kind == 'ExpressionStatement': return self.nba_assignment(stmt.expr,targets)
        if kind == 'Conditional':
            require(len(stmt.conditions)==1 and stmt.conditions[0].pattern is None, 'pattern if unsupported')
            return (f'(NBA.Stmt.ite {self.expression(stmt.conditions[0].expr).code} '
                    f'{self.nba_statement(stmt.ifTrue,targets)} {self.nba_statement(stmt.ifFalse,targets)})')
        if kind == 'Case':
            require(stmt.condition.name=='Normal' and stmt.check.name=='None_', 'casez/casex/unique/priority unsupported')
            arms = f'(NBA.Arms.default {self.nba_statement(stmt.defaultCase,targets)})'
            for item in reversed(stmt.items):
                labels = ', '.join(self.expression(x).code for x in item.expressions)
                require(bool(labels), 'empty case label')
                arms = f'(NBA.Arms.arm [{labels}] {self.nba_statement(item.stmt,targets)} {arms})'
            return f'(NBA.Stmt.cases {self.expression(stmt.expr).code} {arms})'
        raise ValueError('unsupported clocked statement: '+kind)

    def build(self):
        for symbol in self.members:
            kind = symbol.kind.name
            if kind in ('Port','Parameter'): continue
            if kind in ('Net','Variable'):
                require(symbol.type.isFourState, 'two-state declarations require unknown coercion')
                if kind == 'Net':
                    require(symbol.delay is None and symbol.chargeStrength is None and no_drive_strength(symbol)
                            and symbol.netType.netKind.name in ('Wire','Tri'), 'net type/delay/strength unsupported')
                if symbol.initializer is not None:
                    require(kind == 'Net', 'state initialization needs initial-event support')
                    self.add_driver(symbol.name,self.expression(symbol.initializer))
                continue
            if kind == 'ContinuousAssign':
                require(symbol.delay is None and no_drive_strength(symbol), 'continuous delay/strength unsupported')
                name,value = self.assignment(symbol.assignment,{})
                self.add_driver(name,value)
                continue
            require(kind == 'ProceduralBlock' and symbol.procedureKind.name == 'Always',
                    'unsupported clocked module member: '+kind)
            body = symbol.body
            require(body.kind.name == 'Timed', 'clocked process must have an event control')
            timing = body.timing
            require(timing.kind.name in ('EventList','SignalEvent'), 'clocked process needs edge controls')
            events = list(timing.events) if timing.kind.name == 'EventList' else [timing]
            reflected_events = []
            for event in events:
                require(event.kind.name == 'SignalEvent' and event.edge.name in ('PosEdge','NegEdge')
                        and event.iffCondition is None and event.expr.kind.name == 'NamedValue',
                        'only direct input posedge/negedge controls supported')
                name = event.expr.symbol.name
                require(name in self.input_names and self.var(name).width == 1,
                        'edge control must name a scalar input')
                reflected_events.append((name,event.edge.name=='PosEdge'))
            require(bool(reflected_events), 'empty event list')
            targets = set()
            stmt = self.nba_statement(body.stmt,targets)
            require(not targets & self.state_names, 'multiple processes write the same state')
            self.state_names.update(targets)
            self.clocked_processes.append((reflected_events,sorted(targets),stmt))
        require(bool(self.clocked_processes), 'no clocked processes')
        require(not self.state_names & self.drivers.keys(), 'state also has a continuous driver')
        require({n for n,s in self.symbols.items() if s.kind.name=='Variable'} == self.state_names,
                'unmodeled variable or combinational process')
        pending = dict(self.drivers)
        known = self.input_names | self.state_names
        while pending:
            ready = [n for n,v in pending.items() if v.deps <= known]
            require(bool(ready), 'clocked combinational cycle or undriven input: '+', '.join(pending))
            for name in ready:
                self.wires.append((name,pending.pop(name))); known.add(name)
        require(set(self.output_names) <= known, 'undriven clocked output')
        require(self.expression_reads <= known, 'undriven clocked expression reference')
        original_wires, self.wires = self.wires, []
        reserved = set(self.symbols) | set(self.aliases.values())
        cache, counter = {}, 0
        def materialize(term):
            nonlocal counter
            if not self.materialize_combinational: return term
            if not term.args: return term
            if term in cache: return cache[term]
            args = tuple(materialize(a) for a in term.args)
            while f'__nba_expr{counter}' in reserved: counter += 1
            name = f'__nba_expr{counter}'; counter += 1; reserved.add(name)
            value = Term(term.width,term.pattern,frozenset().union(*(a.deps for a in args)),args)
            self.wires.append((name,value))
            result = Term(term.width,f'(.var {lean_string(name)} {term.width})',frozenset([name]))
            cache[term] = result
            return result
        for name,value in original_wires:
            self.wires.append((name,materialize(value)))
        state_order = [n for n in self.symbols if n in self.state_names]
        signed_ports = [m.name for m in self.members if m.kind.name=='Port' and m.type.isSigned]
        def ports(pairs):
            return ', '.join(f'{{name := {lean_string(n)}, width := {w}}}' for n,w in pairs)
        def wires(pairs):
            return ',\n'.join(f'{{name := {lean_string(n)}, width := {v.width}, expr := {v.code}}}' for n,v in pairs)
        definitions, processes, certificates = [], [], []
        self.metadata['source_proofs'] = ['source_comb_correct']
        for i,(events,targets,stmt) in enumerate(self.clocked_processes):
            pname = f'process_{i}'
            definitions.append(f'def {pname} : NBA.Stmt := {stmt}')
            es = ', '.join(f'{{name := {lean_string(n)}, positive := {str(pos).lower()}}}' for n,pos in events)
            ts = ', '.join(lean_string(self.internal(n)) for n in targets)
            processes.append(f'{{events := [{es}], targets := [{ts}], body := {pname}}}')
            for j,name in enumerate(targets):
                n,w = lean_string(self.internal(name)), self.var(name).width
                theorem = f'source_process_{i}_{j}_correct'
                certificates += [f'theorem {theorem} (env : Env) :',
                    f'  eval (NBA.lower {pname} {n} (.var {n} {w})) env =',
                    f'    NBA.execute {pname} {n} env (eval (.var {n} {w}) env) := NBA.lower_correct _ _ _ _',
                    f'#print axioms {theorem}']
                self.metadata['source_proofs'].append(theorem)
        self.metadata.update(source_semantics='nonblocking-only processes; fixed old-state RHS; direct input edges; settled commit',
            source_proof_scope='reflected process lowering; packed AST selection expansion and HDL frontend remain trusted',
            state_bits=sum(self.var(n).width for n in state_order),
            states=[{'name':self.internal(n),'width':self.var(n).width} for n in state_order],
            events=[events for events,_,_ in self.clocked_processes], dynamic_selections=self.selection_count)
        self.metadata['expression_wires'] = len(cache)
        self.metadata['signed_ports'] = signed_ports
        self.model_text = f'''import LeanRTL.Core.FourStateClocked
open LeanRTL.FourState
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000
{chr(10).join(definitions)}
def impl : NBA.Clocked := {{
  name := {lean_string(self.top)}
  inputs := [{ports(self.inputs)}]
  states := [{ports([(self.internal(n),self.var(n).width) for n in state_order])}]
  wires := [{wires([(self.internal(n),v) for n,v in self.wires])}]
  outputs := [{wires([(n,self.var(n)) for n in self.output_names])}]
  processes := [{', '.join(processes)}]
  portOrder := [{', '.join(lean_string(n) for n in self.ports)}]
  signedPorts := [{', '.join(lean_string(n) for n in signed_ports)}]
}}
theorem combinational_valid : impl.combinational.valid = true := by decide +kernel
theorem clocked_valid : impl.valid = true := by decide +kernel
def source_comb : Module := {{
  name := impl.name
  inputs := impl.inputs ++ impl.states
  wires := [{wires([(self.internal(n),v) for n,v in original_wires])}]
  outputs := impl.outputs
}}
theorem source_comb_inlined : Source.inlinedOutputs impl.combinational = Source.inlinedOutputs source_comb := by source_kernel_rfl
theorem source_comb_correct (env : Env) : impl.combinational.eval env = source_comb.eval env :=
  Source.module_equiv_of_inlined _ _ (by decide +kernel) (by decide +kernel) source_comb_inlined env
#print axioms source_comb_correct
{chr(10).join(certificates)}
'''
        return self.model_text + '''
def parseInputs (line : String) : NBA.Snapshot :=
  (line.splitOn " ").filterMap fun token =>
    match token.splitOn "=" with
    | [n,v] => some (n,v.toList.reverse.map fun c => match c with
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
        let outputs := impl.observe state after
        IO.println (String.intercalate " " (outputs.map fun (n,v) => n ++ "=" ++ v))
        before := after
    return 0
  | _ => throw (IO.userError "usage: export FILE | eval INPUTS")
'''
