"""Typed AST frontend for a constant-delay autonomous register.

Retains physical time and initialization; never sends delays through synthesis.
Only the elaborated default parameter configuration is covered.
"""
from pathlib import Path

from .slang import SlangImporter
from .importer import require, lean_string


class TimedImporter(SlangImporter):
    def build(self):
        require(not self.inputs and len(self.output_names) == 1,
                'timed autonomous model requires one output and no inputs')
        name = self.output_names[0]
        require(set(self.symbols) == {name} and self.symbols[name].kind.name == 'Variable',
                'timed autonomous model requires one register and no other state or nets')
        scale = self.body.timeScale
        require(scale is not None, 'explicit time scale required')
        factors = {'Seconds': 10**15, 'Milliseconds': 10**12, 'Microseconds': 10**9,
                   'Nanoseconds': 10**6, 'Picoseconds': 10**3, 'Femtoseconds': 1}
        unit_fs = scale.base.magnitude.value * factors[scale.base.unit.name]
        precision_fs = scale.precision.magnitude.value * factors[scale.precision.unit.name]
        require(unit_fs >= precision_fs, 'time precision exceeds unit')
        initials, loops = [], []
        for member in self.members:
            kind = member.kind.name
            if kind in ('Port', 'Parameter'): continue
            if kind == 'Variable':
                require(member.initializer is None, 'declaration initialization needs explicit initial process')
                continue
            require(kind == 'ProceduralBlock', 'unsupported timed member: ' + kind)
            if member.procedureKind.name == 'Initial': initials.append(member.body)
            elif member.procedureKind.name == 'Always': loops.append(member.body)
            else: raise ValueError('unsupported timed process: '+member.procedureKind.name)
        require(len(initials) == 1, 'requires exactly one initialization process')
        initial_statements = self.sequence_statements(initials[0])
        # `initial begin q = C; forever #D q = F(q); end` has the same
        # autonomous scheduling as initialization plus a delayed always loop.
        # Accept only a final forever statement; no timing or work is discarded.
        if initial_statements and initial_statements[-1].kind.name == 'ForeverLoop':
            require(not loops, 'multiple autonomous delayed processes')
            loops = [initial_statements[-1].body]
            initial_statements = initial_statements[:-1]
        require(len(loops) == 1, 'requires exactly one delayed process')
        loop = self.single_statement(loops[0])
        require(loop.kind.name == 'Timed' and loop.timing.kind.name == 'Delay',
                'requires a leading constant delay')
        require(loop.timing.expr.type.isIntegral, 'fractional or time-literal delay unsupported')
        evaluated_delay = loop.timing.expr.eval(self.slang.ast.EvalContext(self.body))
        require(isinstance(evaluated_delay.value, self.slang.SVInt)
                and not evaluated_delay.value.hasUnknown, 'delay must elaborate to a known integer')
        delay = int(evaluated_delay.value)
        require(delay > 0, 'delay must be positive; zero-delay scheduler unsupported')
        self.initial_write_count = 0
        initial_values, initial_source = {}, 'Source.Stmt.skip'
        for statement in initial_statements:
            initial_values, reflected = self.initial_program(statement, initial_values)
            initial_source = f'(Source.Stmt.seq {initial_source} {reflected})'
        require(self.initial_write_count == 1, 'multiple same-time initial writes require event preservation')
        require(set(initial_values) == {name} and not initial_values[name].deps,
                'initial value must be closed and completely assigned')
        next_values = self.statement(loop.stmt, {})
        require(self.max_writes(loop.stmt) <= 1, 'multiple same-time update writes require event preservation')
        require(set(next_values) == {name} and next_values[name].deps <= {name},
                'update must assign the autonomous register only')
        update_source = self.source_statement(loop.stmt)
        initial, update = initial_values[name], next_values[name]
        width = initial.width
        self.period_fs = delay * unit_fs
        require(self.period_fs < 2**64, 'delay exceeds 64-bit simulator time')
        self.metadata.update(source_semantics='one autonomous register; initialized at t=0; fixed positive delay; post-active observations',
                             period_fs=self.period_fs, unit_fs=unit_fs, precision_fs=precision_fs,
                             source_time_scale=str(scale), parameter_scope='elaborated defaults only',
                             parameters={m.name: str(m.value) for m in self.members if m.kind.name == 'Parameter'})
        lines = ['import LeanRTL.Core.FourStateTimed', 'import LeanRTL.Core.FourStateProcedural',
                 'open LeanRTL.FourState', 'set_option maxRecDepth 32768', 'set_option maxHeartbeats 4000000',
                 'set_option linter.unusedSimpArgs false',
                 'def impl : Timed.Signal := {',
                 f'  name := {lean_string(name)}, width := {width}, periodFS := {self.period_fs}',
                 f'  initial := {initial.code}', f'  next := {update.code}', '}',
                 'theorem signal_valid : impl.valid = true := by decide +kernel',
                 f'def source_scope : List (String × Nat) := [({lean_string(name)}, {width})]']
        names = []
        for label, stmt, field in [('initial', initial_source, 'initial'), ('update', update_source, 'next')]:
            target = f'(Expr.var {lean_string(name)} {width})'
            pname = 'source_'+label
            theorem = pname+'_correct'
            lines += [f'def {pname} : Source.Stmt := {stmt}',
                      f'theorem {pname}_valid : Source.stmtValid source_scope {pname} = true := by decide +kernel',
                      f'theorem {theorem} (env : Env) :',
                      f'  eval impl.{field} env = eval {target} (Source.execute {pname} env) := by',
                      f'  have h := Source.lower_correct {pname} source_scope {pname}_valid {target} (by decide +kernel) env',
                      f'  simp only [{pname}, Source.lower, Source.lowerArms, Source.substOne, Source.ifTest, Source.caseTest, reduceIte, reduceDIte, String.reduceEq] at h',
                      '  simpa only [impl, eval, Source.mux_same] using h']
            names.append(theorem)
        lines += ['#print axioms '+n for n in names]
        self.metadata['source_proofs'] = names
        self.metadata['source_proof_scope'] = 'initial and one delayed blocking update match reflected source statements; physical period is explicit; AST parsing and constant elaboration are separate boundaries'
        self.model_text = '\n'.join(lines)+'\n'
        lines += [
            'def main (args : List String) : IO UInt32 := do',
            '  match args with',
            '  | ["export", path] =>',
            f'    IO.FS.writeFile path (Timed.emit {lean_string(self.top)} impl)',
            '    return 0',
            '  | ["eval", path] =>',
            '    let text ← IO.FS.readFile path',
            '    for line in text.splitOn "\\n" do',
            '      if !line.isEmpty then',
            '        match line.toNat? with',
            '        | none => throw (IO.userError "invalid femtosecond timestamp")',
            '        | some t => IO.println (toString t ++ " " ++ impl.name ++ "=" ++ impl.renderAt t)',
            '    return 0',
            '  | _ => throw (IO.userError "expected export FILE or eval TIMESTAMPS")']
        return '\n'.join(lines)+'\n'

    @staticmethod
    def sequence_statements(stmt):
        if stmt.kind.name == 'Block':
            require(stmt.blockKind.name == 'Sequential', 'parallel initialization unsupported')
            return TimedImporter.sequence_statements(stmt.body)
        if stmt.kind.name == 'List':
            return [child for s in stmt.list for child in TimedImporter.sequence_statements(s)]
        return [stmt]

    @staticmethod
    def single_statement(stmt):
        while stmt.kind.name in ('Block', 'List'):
            if stmt.kind.name == 'Block':
                require(stmt.blockKind.name == 'Sequential', 'parallel delayed block unsupported')
                stmt = stmt.body
            else:
                children = list(stmt.list)
                require(len(children) == 1, 'work outside the leading delay is unsupported')
                stmt = children[0]
        return stmt

    def initial_program(self, stmt, before):
        """Resolve constant control only; an active display or timing action is rejected."""
        if stmt is None or stmt.kind.name == 'Empty': return dict(before), 'Source.Stmt.skip'
        kind = stmt.kind.name
        if kind == 'Block':
            require(stmt.blockKind.name == 'Sequential', 'parallel initialization unsupported')
            return self.initial_program(stmt.body, before)
        if kind == 'List':
            result, source = dict(before), 'Source.Stmt.skip'
            for child in stmt.list:
                result, reflected = self.initial_program(child, result)
                source = f'(Source.Stmt.seq {source} {reflected})'
            return result, source
        if kind == 'Conditional':
            require(len(stmt.conditions) == 1 and stmt.conditions[0].pattern is None, 'pattern initialization unsupported')
            condition = self.integer(stmt.conditions[0].expr)
            return self.initial_program(stmt.ifTrue if condition else stmt.ifFalse, before)
        require(kind == 'ExpressionStatement', 'unsupported initial statement: '+kind)
        self.initial_write_count = getattr(self, 'initial_write_count', 0) + 1
        return self.statement(stmt, before), self.source_statement(stmt)

    def max_writes(self, stmt):
        """Bound visible writes on each path, preserving same-time output edges."""
        if stmt is None or stmt.kind.name == 'Empty': return 0
        kind = stmt.kind.name
        if kind == 'Block': return self.max_writes(stmt.body)
        if kind == 'List': return sum(self.max_writes(s) for s in stmt.list)
        if kind == 'Conditional': return max(self.max_writes(stmt.ifTrue),self.max_writes(stmt.ifFalse))
        if kind == 'Case': return max([self.max_writes(stmt.defaultCase)]+[self.max_writes(i.stmt) for i in stmt.items])
        require(kind == 'ExpressionStatement', 'unsupported delayed statement: '+kind)
        return 1
