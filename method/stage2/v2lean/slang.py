"""Direct, typed SystemVerilog AST -> four-state LeanRTL (optional pyslang).

No Yosys/proc/netlist is used by this frontend. This starts with combinational
word expressions and blocking procedural control; unsupported constructs fail
explicitly. It is a separate implementation, not a proven Verilog frontend.
"""
from collections import Counter
from dataclasses import dataclass
import re
from pathlib import Path
import hashlib

from .fourstate import FourStateImporter
from .importer import lean_string, require


@dataclass(frozen=True)
class Term:
    width: int
    pattern: str
    deps: frozenset = frozenset()
    args: tuple = ()

    @property
    def code(self):
        return self.pattern.format(*(a.code for a in self.args)) if self.args else self.pattern


def node(width, op, *args):
    return Term(width, f"(.{op} " + " ".join("{}" for _ in args) + ")",
                frozenset().union(*(a.deps for a in args)), tuple(args))


def const(width, value):
    return Term(width, f"(.const (BitVec.ofNat {width} {value % (1 << width)}))")


def fit(a, width, signed=False):
    require(width > 0, "zero-width AST value")
    if a.width == width: return a
    if a.width > width: return Term(width, f"(.slice 0 {width} {{}})", a.deps, (a,))
    return Term(width, f"(.{'sext' if signed else 'zext'} {width-a.width} {{}})", a.deps, (a,))


def truth(a):
    return node(1, 'not', node(1, 'eq', a, const(a.width, 0)))


def no_drive_strength(symbol):
    try:
        return symbol.driveStrength == (None, None)
    except TypeError:
        # pyslang 11 does not bind nonempty DriveStrength enum values.
        # Reject that declaration; never treat an unreadable strength as absent.
        return False


class SlangImporter:
    def __init__(self, source, top, *, allow_inout=False):
        import pyslang as slang
        require(slang.__version__ == "11.0.0", "direct AST frontend currently pins pyslang 11.0.0")
        self.slang = slang
        self.top = top
        options = slang.ast.CompilationOptions()
        options.topModules = {top}
        self.compilation = slang.ast.Compilation(slang.Bag([options]))
        self.source_manager = slang.SourceManager()
        self.compilation.addSyntaxTree(slang.syntax.SyntaxTree.fromFile(str(source), self.source_manager))
        tops = list(self.compilation.getRoot().topInstances)
        diagnostics = list(self.compilation.getAllDiagnostics())
        require(not any(d.isError() for d in diagnostics),
                'slang elaboration errors: ' + ', '.join(str(d.code) for d in diagnostics if d.isError()))
        require(len(tops) == 1 and tops[0].name == top, 'slang top selection mismatch')
        self.body = tops[0].body
        self.members = list(self.body)
        self.symbols = {x.name: x for x in self.members if x.kind.name in ('Net', 'Variable')}
        self.inputs, self.output_names, self.inout_names, self.ports = [], [], [], {}
        self.wires, self.states, self.port_layouts = [], [], {}
        self.counts = Counter()
        self.drivers = {}
        self.processes = []
        for symbol in self.members:
            if symbol.kind.name != 'Port': continue
            name, width = symbol.name, self.width(symbol.type)
            require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', name), 'unsupported port identifier')
            require(symbol.direction.name in (('In', 'Out', 'InOut') if allow_inout else ('In', 'Out')),
                    'inout requires resolved driver semantics')
            require(symbol.internalSymbol is not None and symbol.internalSymbol.name == name,
                    'nontrivial port connection unsupported')
            typ = symbol.type
            require(not typ.hasFixedRange or (typ.fixedRange.right == 0 and typ.fixedRange.left == width-1),
                    'nondefault port layout unsupported in four-state emitter')
            direction = {'In': 'input', 'Out': 'output', 'InOut': 'inout'}[symbol.direction.name]
            self.ports[name] = {'direction': direction, 'bits': list(range(width))}
            if direction == 'input': self.inputs.append((name, width))
            elif direction == 'output': self.output_names.append(name)
            else: self.inout_names.append(name)
        self.input_names = {n for n, _ in self.inputs}
        library = next(Path(slang.__file__).parent.glob('pyslang*.so'))
        self.metadata = {'frontend': 'pyslang', 'version': slang.__version__,
                         'native_library_sha256': hashlib.sha256(library.read_bytes()).hexdigest(),
                         'source_semantics': 'typed SystemVerilog AST; combinational; no Yosys proc',
                         'diagnostics': [str(d.code) for d in diagnostics],
                         'modules': {top: {'ports': self.ports}}}

    @staticmethod
    def width(typ):
        require(typ.isIntegral and not typ.isUnpackedArray and typ.bitWidth > 0,
                'unsupported nonintegral or unpacked AST value')
        return typ.bitWidth

    def var(self, name):
        require(name in self.symbols, 'unknown AST variable: ' + name)
        return Term(self.width(self.symbols[name].type),
                    f"(.var {lean_string(name)} {self.width(self.symbols[name].type)})", frozenset([name]))

    def literal(self, value, width):
        require(value.bitWidth == width, 'AST constant width mismatch')
        bits = [str(value[i]).lower() for i in range(width)]
        require(set(bits) <= set('01xz'), 'invalid four-state literal')
        # Coalesce same-state and binary runs without changing bit order.
        chunks, i = [], 0
        while i < width:
            j = i+1
            if bits[i] in 'xz':
                while j < width and bits[j] == bits[i]: j += 1
                part = Term(j-i, f"(@Expr.fill {j-i} .{bits[i]})")
            else:
                while j < width and bits[j] in '01': j += 1
                part = const(j-i, sum(int(b) << k for k, b in enumerate(bits[i:j])))
            chunks.append(part); i = j
        result = chunks[0]
        for high in chunks[1:]: result = self.concat(high, result)
        return result

    @staticmethod
    def concat(high, low):
        return Term(high.width+low.width, f"(@Expr.concat {high.width} {low.width} {{}} {{}})",
                    high.deps | low.deps, (high, low))

    def integer(self, expr):
        if expr.kind.name == 'IntegerLiteral': value = expr.value
        elif expr.kind.name == 'NamedValue' and expr.symbol.kind.name == 'Parameter': value = expr.symbol.value.value
        else:
            require(expr.constant is not None, 'nonconstant AST index/count')
            value = expr.constant.value
        require(not value.hasUnknown, 'unknown AST index/count')
        return int(value)

    def expression(self, expr, local=None):
        local = {} if local is None else local
        kind, width = expr.kind.name, self.width(expr.type)
        self.counts['expr.' + kind] += 1
        if kind == 'IntegerLiteral': return self.literal(expr.value, width)
        if kind == 'NamedValue':
            if expr.symbol.kind.name == 'Parameter': return self.literal(expr.symbol.value.value, width)
            return local.get(expr.symbol.name, self.var(expr.symbol.name))
        if kind == 'Conversion':
            operand = self.expression(expr.operand, local)
            require(expr.type.isFourState or not expr.operand.type.isFourState,
                    'four-state to two-state cast needs explicit unknown coercion')
            # Propagated expression context determines signedness before width
            # extension; ordinary assignment casts retain the source sign.
            signed = expr.type.isSigned if expr.conversionKind.name == "Propagated" else expr.operand.type.isSigned
            return fit(operand, width, signed)
        if kind == 'Call':
            require(expr.isSystemCall and expr.subroutineName in ('$signed', '$unsigned')
                    and len(expr.arguments) == 1, 'unsupported AST function call')
            result = self.expression(expr.arguments[0], local)
            require(result.width == width, 'sign cast width mismatch')
            return result
        if kind == 'Replication':
            part, count = self.expression(expr.concat, local), self.integer(expr.count)
            require(count > 0 and part.width * count == width, 'invalid replication width')
            result = part
            for _ in range(count-1): result = self.concat(result, part)
            return result
        if kind == 'Concatenation':
            operands = [self.expression(x, local) for x in expr.operands]
            require(bool(operands), 'empty concatenation')
            result = operands[0]
            for low in operands[1:]: result = self.concat(result, low)
            require(result.width == width, 'concatenation width mismatch')
            return result
        if kind in ('RangeSelect', 'ElementSelect'):
            a = self.expression(expr.value, local)
            span = expr.value.type.fixedRange
            if kind == 'RangeSelect':
                require(expr.selectionKind.name == 'Simple', 'indexed part select not implemented')
                high, low = self.integer(expr.left), self.integer(expr.right)
                index = span.translateIndex(low)
                require(span.translateIndex(high) == index+width-1, 'range select direction mismatch')
            else: index = span.translateIndex(self.integer(expr.selector))
            require(0 <= index and index+width <= a.width, 'out-of-range AST selection needs X padding')
            return Term(width, f"(.slice {index} {width} {{}})", a.deps, (a,))
        if kind == 'UnaryOp':
            a, op = self.expression(expr.operand, local), expr.op.name
            if op == 'Plus': return fit(a, width, expr.operand.type.isSigned)
            if op == 'Minus': return node(width, 'sub', const(width, 0), fit(a, width, expr.operand.type.isSigned))
            if op == 'BitwiseNot': return node(width, 'not', a)
            if op == 'LogicalNot': return node(1, 'not', truth(a))
            if op in ('BitwiseAnd', 'BitwiseNand'):
                result = node(1, 'eq', a, const(a.width, (1 << a.width)-1))
            elif op in ('BitwiseOr', 'BitwiseNor'): result = truth(a)
            elif op in ('BitwiseXor', 'BitwiseXnor'):
                parts = [Term(1, f"(.extract {i} {{}})", a.deps, (a,)) for i in range(a.width)]
                result = parts[0]
                for part in parts[1:]: result = node(1, 'xor', result, part)
            else: raise ValueError('unsupported AST unary operator: ' + op)
            return node(1, 'not', result) if op in ('BitwiseNand', 'BitwiseNor', 'BitwiseXnor') else result
        if kind == 'BinaryOp':
            a, b = self.expression(expr.left, local), self.expression(expr.right, local)
            op = expr.op.name
            binary = {'Add':'add', 'Subtract':'sub', 'Multiply':'mul', 'BinaryAnd':'and',
                      'BinaryOr':'or', 'BinaryXor':'xor', 'BinaryXnor':'xor', 'Equality':'eq',
                      'Inequality':'eq', 'CaseEquality':'caseEq', 'CaseInequality':'caseEq'}
            if op in binary:
                require(a.width == b.width, 'slang arithmetic/comparison operands not coerced to common width')
                result = node(width, binary[op], a, b)
                return node(width, 'not', result) if op in ('Inequality','CaseInequality','BinaryXnor') else result
            if op == 'Divide':
                require(not expr.left.type.isSigned and not expr.right.type.isSigned,
                        'signed four-state division is unsupported')
                require(a.width == b.width == width, 'division operands not coerced to result width')
                return node(width, 'udiv', a, b)
            if op in ('LogicalAnd','LogicalOr'):
                return node(1, 'and' if op == 'LogicalAnd' else 'or', truth(a), truth(b))
            if op in ('LessThan','LessThanEqual','GreaterThan','GreaterThanEqual'):
                require(a.width == b.width, 'comparison operand width mismatch')
                operation = 'slt' if expr.left.type.isSigned and expr.right.type.isSigned else 'ult'
                if op in ('GreaterThan','LessThanEqual'): a,b = b,a
                result = node(1, operation, a,b)
                return node(1,'not',result) if op in ('LessThanEqual','GreaterThanEqual') else result
            if op in ('LogicalShiftLeft','ArithmeticShiftLeft','LogicalShiftRight','ArithmeticShiftRight'):
                operation = 'shl' if op.endswith('Left') else (
                    'sshr' if op == 'ArithmeticShiftRight' and expr.left.type.isSigned else 'shr')
                require(a.width == width, 'shift operand width not context-coerced')
                return node(width, operation, a,b)
            raise ValueError('unsupported AST binary operator: '+op)
        if kind == 'ConditionalOp':
            require(len(expr.conditions) == 1 and expr.conditions[0].pattern is None, 'pattern conditional unsupported')
            return node(width, 'mux', truth(self.expression(expr.conditions[0].expr, local)),
                        self.expression(expr.left, local), self.expression(expr.right, local))
        raise ValueError('unsupported AST expression: ' + kind)

    def assignment(self, expr, local):
        require(expr.kind.name == 'Assignment' and not expr.isNonBlocking and not expr.isCompound
                and expr.timingControl is None, 'only untimed blocking assignments supported')
        require(expr.left.kind.name == 'NamedValue', 'partial/array lvalue needs separate support')
        name = expr.left.symbol.name
        value = self.expression(expr.right, local)
        require(value.width == self.var(name).width, 'assignment type width mismatch')
        return name, value

    def merge(self, selector, left, right, before):
        result = dict(before)
        for name in left.keys() | right.keys():
            a, b = left.get(name, before.get(name, self.var(name))), right.get(name, before.get(name, self.var(name)))
            result[name] = a if a == b else node(a.width, 'mux', selector, a, b)
        return result

    def statement(self, stmt, before):
        if stmt is None: return dict(before)
        kind = stmt.kind.name
        self.counts['stmt.'+kind] += 1
        if kind == 'Empty': return dict(before)
        if kind == 'Block':
            require(stmt.blockKind.name == 'Sequential', 'parallel block unsupported')
            return self.statement(stmt.body, before)
        if kind == 'List':
            result = dict(before)
            for child in stmt.list: result = self.statement(child, result)
            return result
        if kind == 'ExpressionStatement':
            name, value = self.assignment(stmt.expr, before)
            return dict(before) | {name: value}
        if kind == 'Conditional':
            require(len(stmt.conditions) == 1 and stmt.conditions[0].pattern is None, 'pattern if unsupported')
            # Procedural if takes a branch only on a definite truth value, unlike ?: merging.
            selector = node(1, 'caseEq', truth(self.expression(stmt.conditions[0].expr, before)), const(1,1))
            return self.merge(selector, self.statement(stmt.ifTrue, before),
                              self.statement(stmt.ifFalse, before), before)
        if kind == 'Case':
            require(stmt.condition.name == 'Normal' and stmt.check.name == 'None_', 'casez/casex/unique/priority unsupported')
            selector = self.expression(stmt.expr, before)
            result = self.statement(stmt.defaultCase, before)
            for item in reversed(stmt.items):
                tests = [node(1, 'caseEq', selector, self.expression(x, before)) for x in item.expressions]
                require(bool(tests), 'empty case label')
                test = tests[0]
                for alternative in tests[1:]: test = node(1,'or',test,alternative)
                result = self.merge(test, self.statement(item.stmt, before), result, before)
            return result
        raise ValueError('unsupported AST statement: ' + kind)

    def source_statement(self, stmt):
        """Reflect procedural structure without symbolic substitution or mux lowering."""
        if stmt is None or stmt.kind.name == 'Empty': return 'Source.Stmt.skip'
        kind = stmt.kind.name
        if kind == 'Block': return self.source_statement(stmt.body)
        if kind == 'List':
            result = 'Source.Stmt.skip'
            for child in stmt.list: result = f'(Source.Stmt.seq {result} {self.source_statement(child)})'
            return result
        if kind == 'ExpressionStatement':
            name, value = self.assignment(stmt.expr, {})
            return f'(Source.Stmt.assign {{ name := {lean_string(name)}, width := {value.width}, expr := {value.code} }})'
        if kind == 'Conditional':
            cond = self.expression(stmt.conditions[0].expr)
            return f'(Source.Stmt.ite {cond.code} {self.source_statement(stmt.ifTrue)} {self.source_statement(stmt.ifFalse)})'
        if kind == 'Case':
            selector = self.expression(stmt.expr)
            arms = f'(Source.Arms.default {self.source_statement(stmt.defaultCase)})'
            for item in reversed(stmt.items):
                labels = ', '.join(self.expression(x).code for x in item.expressions)
                arms = f'(Source.Arms.arm [{labels}] {self.source_statement(item.stmt)} {arms})'
            return f'(Source.Stmt.cases {selector.code} {arms})'
        raise ValueError('unsupported reflected source statement: '+kind)

    def source_certificates(self, raw_wires, outputs):
        def entries(values):
            return ',\n'.join(f'{{ name := {lean_string(n)}, width := {e.width}, expr := {e.code} }}' for n,e in values)
        inputs = ', '.join(f'{{ name := {lean_string(n)}, width := {w} }}' for n,w in self.inputs)
        scope = ', '.join(f'({lean_string(n)}, {self.width(v.type)})' for n,v in self.symbols.items() if v.type.isIntegral)
        lines = [f'def source_scope : List (String × Nat) := [{scope}]',
                 'def source_impl : Module := {', f'  name := {lean_string(self.top)}',
                 f'  inputs := [{inputs}]', f'  wires := [{entries(raw_wires)}]',
                 f'  outputs := [{entries(outputs)}]', '}',
                 'theorem source_inlined : Source.inlinedOutputs impl = Source.inlinedOutputs source_impl := by source_kernel_rfl',
                 'theorem source_dag_correct (env : Env) : impl.eval env = source_impl.eval env :=',
                 '  Source.module_equiv_of_inlined impl source_impl (by decide +kernel) (by decide +kernel) source_inlined env']
        proofs = ['source_dag_correct']
        for index, (stmt, values) in enumerate(self.processes):
            pname = f'source_process_{index}'
            lines += [f'def {pname} : Source.Stmt := {stmt}',
                      f'theorem {pname}_valid : Source.stmtValid source_scope {pname} = true := by decide +kernel']
            for number, (name,value) in enumerate(sorted(values.items())):
                theorem = f'source_process_{index}_{number}_correct'
                target = f'(Expr.var {lean_string(name)} {value.width})'
                lines += [f'theorem {theorem} (env : Env) :',
                          f'  LeanRTL.FourState.eval {value.code} env = LeanRTL.FourState.eval {target} (Source.execute {pname} env) := by',
                          f'  have h := Source.lower_correct {pname} source_scope {pname}_valid {target} (by decide +kernel) env',
                          f'  simp only [{pname}, Source.lower, Source.lowerArms, Source.substOne, Source.ifTest, Source.caseTest, reduceIte, reduceDIte, String.reduceEq] at h',
                          '  simpa only [LeanRTL.FourState.eval, Source.mux_same] using h']
                proofs.append(theorem)
        lines += ['#print axioms '+name for name in proofs]
        self.metadata['source_proofs'] = proofs
        self.metadata['source_proof_scope'] = ('actual materialized module equals pre-DAG module; each reflected '
            'procedural observation equals its Python-lowered expression; expression AST reflection and Verilog parsing remain separate boundaries')
        return '\n'.join(lines)+'\n'

    def add_driver(self, name, value):
        require(name not in self.input_names and name not in self.drivers, 'multiple/input drivers: ' + name)
        self.drivers[name] = value

    def build(self):
        require(not self.inout_names, 'inout requires the resolved netlist build path')
        for symbol in self.members:
            kind = symbol.kind.name
            if kind in ('Port','Parameter'): continue
            if kind in ('Net','Variable'):
                if kind == 'Net':
                    require(symbol.delay is None and symbol.chargeStrength is None
                            and no_drive_strength(symbol), 'net delay/strength unsupported')
                    require(symbol.netType.netKind.name in ('Wire', 'Tri'),
                            'net type requires pull/driver resolution: '+symbol.netType.netKind.name)
                if symbol.initializer is not None:
                    require(kind == 'Net', 'variable initialization is state, not a continuous assignment')
                    self.add_driver(symbol.name, self.expression(symbol.initializer))
                continue
            if kind == 'ContinuousAssign':
                require(symbol.delay is None and no_drive_strength(symbol), 'delay/drive strength unsupported')
                name, value = self.assignment(symbol.assignment, {})
                self.add_driver(name, value)
            elif kind == 'ProceduralBlock':
                require(symbol.procedureKind.name in ('Always','AlwaysComb'), 'clocked/initial procedural block unsupported')
                body = symbol.body
                if symbol.procedureKind.name == 'Always':
                    require(body.kind.name == 'Timed' and body.timing.kind.name == 'ImplicitEvent',
                            'only always @* sensitivity supported')
                    body = body.stmt
                values = self.statement(body, {})
                written = set(values)
                require(all(not (value.deps & written) for value in values.values()),
                        'procedural read before write/latch requires old-state/event semantics')
                saved_counts = self.counts.copy()
                reflected = self.source_statement(body)
                self.counts = saved_counts
                self.processes.append((reflected, values))
                for name, value in values.items(): self.add_driver(name, value)
            else: raise ValueError('unsupported module AST member: ' + kind)
        known = set(self.input_names)
        pending = dict(self.drivers)
        while pending:
            ready = [n for n,v in pending.items() if v.deps <= known]
            require(bool(ready), 'combinational cycle, latch, or undriven reference: ' + ', '.join(pending))
            for name in ready:
                value = pending.pop(name)
                self.wires.append((name, value)); known.add(name)
        # Materialize the expression DAG before encoding. A nested four-state
        # mux otherwise repeats both encoded planes in each merge branch.
        original_wires, self.wires = self.wires, []
        cache, counter = {}, 0
        reserved = set(self.symbols) | {'_sv_' + n for n in self.output_names}
        def materialize(term):
            nonlocal counter
            if not term.args: return term
            if term in cache: return cache[term]
            args = tuple(materialize(a) for a in term.args)
            while '_sv_expr' + str(counter) in reserved: counter += 1
            name = '_sv_expr' + str(counter)
            counter += 1
            value = Term(term.width, term.pattern, frozenset().union(*(a.deps for a in args)), args)
            self.wires.append((name, value))
            result = Term(term.width, f"(.var {lean_string(name)} {term.width})", frozenset([name]))
            cache[term] = result
            return result
        for name, term in original_wires:
            self.wires.append((name, materialize(term)))
        self.metadata['expression_wires'] = len(cache)
        outputs = []
        # Output names must differ from internal wire names in LeanRTL.Module.valid.
        rename = {n: '_sv_' + n for n in self.output_names}
        require(not set(rename.values()) & set(self.symbols), 'generated output alias collision')
        for n in self.output_names:
            require(n in known, 'undriven AST output: '+n)
            outputs.append((n, Term(self.var(n).width, f"(.var {lean_string(rename[n])} {self.var(n).width})")))
        def renamed(term):
            code = term.code
            for old,new in rename.items(): code = code.replace('(.var '+lean_string(old)+' ', '(.var '+lean_string(new)+' ')
            return Term(term.width, code, frozenset(rename.get(n,n) for n in term.deps))
        self.wires = [(rename.get(n,n), renamed(value)) for n,value in self.wires]
        self.metadata['ast_counts'] = dict(self.counts)
        self.metadata['wire_order'] = [n for n,_ in self.wires]
        raw_wires = [(rename.get(n,n), renamed(value)) for n,value in original_wires]
        text = 'import LeanRTL.Core.FourStateProcedural\n' + FourStateImporter.render(self, outputs)
        return text.replace('def main (args', self.source_certificates(raw_wires, outputs)+'def main (args')


def audit_source_proofs(stdout, metadata):
    expected = metadata['source_proofs']
    require(bool(expected) and len(set(expected)) == len(expected), 'missing/duplicate source proof names')
    records = re.findall(r"'(source_[^']+)' depends on axioms: \[([^\]]*)\]", stdout, re.S)
    free = re.findall(r"'(source_[^']+)' does not depend on any axioms", stdout)
    require(len(records)+len(free) == len(expected) and set(n for n,_ in records)|set(free) == set(expected),
            'missing or ambiguous source proof axiom audit')
    dependencies = {n: sorted({a.strip() for a in axs.split(',') if a.strip()}) for n,axs in records}
    dependencies.update({n: [] for n in free})
    require(all(set(axs) <= {'propext','Classical.choice','Quot.sound'} for axs in dependencies.values()),
            'untrusted source lowering proof axiom')
    return {'status': 'kernel_checked', 'theorems': dependencies, 'scope': metadata['source_proof_scope']}
