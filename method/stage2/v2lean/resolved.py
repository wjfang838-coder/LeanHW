"""Typed continuous-assignment netlists with equal-strength resolved inout wires.

The external drive is a separate evaluator input; native HDL emission keeps the
physical bidirectional wire and every internal driver. Cyclic drive dependencies,
strengths, pull nets, hierarchy and procedural/stateful blocks are rejected.
"""
from .slang import SlangImporter, Term, no_drive_strength
from .importer import require, lean_string


class ResolvedImporter(SlangImporter):
    def __init__(self, source, top):
        super().__init__(source, top, allow_inout=True)
        require(all(not m.type.isSigned for m in self.members if m.kind.name == 'Port'),
                'signed physical ports need layout support')
        prefix = '_sv_'
        while any(prefix+n in self.symbols for n in self.output_names+self.inout_names): prefix += '_'
        self.aliases = {n: prefix+n for n in self.output_names+self.inout_names}
        self.nodes = []
        self.net_metadata = []

    def var(self, name):
        term = super().var(name)
        return Term(term.width, f'(.var {lean_string(self.aliases.get(name,name))} {term.width})', term.deps)

    def add_driver(self, name, value):
        require(name not in self.input_names, 'cannot drive an input')
        require(self.symbols[name].kind.name == 'Net', 'resolved profile requires wire assignments')
        self.drivers.setdefault(name, []).append(value)

    def build(self):
        for symbol in self.members:
            kind = symbol.kind.name
            if kind in ('Port','Parameter'): continue
            if kind == 'Net':
                require(symbol.delay is None and symbol.chargeStrength is None and no_drive_strength(symbol),
                        'net delay or strength unsupported')
                require(symbol.netType.netKind.name in ('Wire','Tri'), 'pull or resolved net type unsupported')
                if symbol.initializer is not None:
                    self.add_driver(symbol.name,self.expression(symbol.initializer))
                continue
            if kind == 'ContinuousAssign':
                require(symbol.delay is None and no_drive_strength(symbol), 'assignment delay or strength unsupported')
                name,value = self.assignment(symbol.assignment,{})
                self.add_driver(name,value)
                continue
            raise ValueError('unsupported resolved module member: '+kind)
        pending = {n: self.drivers.get(n,[]) for n in self.symbols if n not in self.input_names}
        known = set(self.input_names)
        reserved = set(self.symbols) | set(self.aliases.values())
        counter = 0
        while pending:
            ready = [n for n,ds in pending.items() if all(d.deps <= known for d in ds)]
            require(bool(ready), 'cyclic resolved drive dependencies: '+', '.join(pending))
            for name in ready:
                drivers = pending.pop(name)
                width = self.width(self.symbols[name].type)
                terms = []
                for driver in drivers:
                    while f'_driver{counter}' in reserved: counter += 1
                    tmp = f'_driver{counter}'; reserved.add(tmp); counter += 1
                    self.nodes.append(f'(.wire {{ name := {lean_string(tmp)}, width := {width}, expr := {driver.code} }})')
                    terms.append(f'(.var {lean_string(tmp)} {width})')
                internal = self.aliases.get(name,name)
                port = f'some {lean_string(name)}' if name in self.inout_names else 'none'
                self.nodes.append(f'(.net {{ name := {lean_string(internal)}, width := {width}, port := {port}, drivers := [{", ".join(terms)}] }})')
                self.net_metadata.append({'name':name,'internal':internal,'width':width,'drivers':len(drivers),
                                          'external_input':'__external_'+name if name in self.inout_names else None})
                known.add(name)
        require(set(self.output_names+self.inout_names) <= known, 'missing resolved outputs')
        inputs = ', '.join(f'{{ name := {lean_string(n)}, width := {w} }}' for n,w in self.inputs)
        outputs = ', '.join(f'{{ name := {lean_string(n)}, width := {self.var(n).width}, expr := {self.var(n).code} }}' for n in self.output_names)
        self.metadata.update(source_semantics='typed continuous-assignment AST; acyclic equal-strength wire resolution; external drive kept distinct',
                             resolved_nets=self.net_metadata, ast_counts=dict(self.counts))
        external = [(m['external_input'],m['name']) for m in self.net_metadata if m['external_input']]
        remap = 'n'
        for key,port in reversed(external): remap=f'if n == {lean_string(key)} then {lean_string(port)} else ({remap})'
        nodes = ',\n'.join(self.nodes)
        return f'''import LeanRTL.Core.FourStateNetlist
import LeanRTL.Core.FourStateModuleCorrect
open LeanRTL.FourState
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
def impl : Resolved.Netlist := {{
  name := {lean_string(self.top)}
  inputs := [{inputs}]
  nodes := [{nodes}]
  outputs := [{outputs}]
  portOrder := [{', '.join(lean_string(n) for n in self.ports)}]
}}
theorem netlist_valid : impl.valid = true := by decide +kernel
theorem resolution_correct (env : Env) : impl.lower.eval env = impl.eval env :=
  Resolved.netlist_correct impl env
#print axioms resolution_correct
def main (args : List String) : IO UInt32 := do
  match args with
  | ["export", path] =>
    IO.FS.writeFile path (Resolved.emit impl)
    return 0
  | ["encode", path] =>
    IO.FS.writeFile path (Encoding.module impl.lower).toRtlilJson
    return 0
  | ["eval", path] =>
    let text ← IO.FS.readFile path
    for line in text.splitOn "\\n" do
      if !line.isEmpty then
        let mut vals : List (String × List Char) := []
        for token in line.splitOn " " do
          match token.splitOn "=" with
          | [n,v] => vals := vals ++ [(n,v.toList.reverse)]
          | _ => throw (IO.userError "invalid resolved input")
        let env : Env := fun n i =>
          let port := {remap}
          match ((vals.lookup port).getD []).getD i 'x' with
          | '0' => .zero
          | '1' => .one
          | 'z' => .z
          | _ => .x
        IO.println (String.intercalate " " ((impl.eval env).map (fun (n,v) => n ++ "=" ++ v)))
    return 0
  | _ => throw (IO.userError "expected export/encode FILE or eval INPUTS")
'''
