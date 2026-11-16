"""Import supported word-level RTLIL operators/storage as checked LeanRTL data.

Connections are resolved by bit ID. Unknown values in executable connections
remain unsupported; net-name metadata is not executable logic.
"""
from dataclasses import dataclass
import json
import re


class Unsupported(ValueError):
    pass


def require(condition, message):
    if not condition:
        raise Unsupported(message)


def lean_string(value):
    # Identifiers accepted by the prototype are printable ASCII; JSON quoting
    # also escapes quotes/backslashes for the generated Lean string literal.
    require(all(32 <= ord(c) < 127 for c in value), "non-ASCII signal name")
    return json.dumps(value)


@dataclass(frozen=True)
class Expr:
    width: int
    code: str


def resize(expr, width, signed=False):
    require(width > 0, "zero-width expression")
    if expr.width == width:
        return expr
    if expr.width < width:
        return Expr(width, f"(.{'sext' if signed else 'zext'} {width - expr.width} {expr.code})")
    return Expr(width, f"(.slice 0 {width} {expr.code})")


def parameter(cell, key):
    raw = cell.get("parameters", {}).get(key)
    require(isinstance(raw, str) and re.fullmatch("[01]+", raw),
            f"{cell['type']}: missing/unknown binary parameter {key}")
    return int(raw, 2)


class Importer:
    BINARY = {"$add": "add", "$sub": "sub", "$mul": "mul",
              "$and": "and", "$or": "or", "$xor": "xor"}
    COMPARE = {"$eq", "$ne", "$lt", "$le", "$gt", "$ge"}
    REDUCE = {"$reduce_and", "$reduce_or", "$reduce_bool", "$reduce_xor", "$reduce_xnor", "$logic_not"}
    UNARY = {"$not", "$neg"} | REDUCE
    SHIFT = {"$shl", "$shr", "$sshl", "$sshr"}
    LOGIC = {"$logic_and", "$logic_or"}
    GATES = {"$_MUX_": "mux", "$_NOT_": "not", "$_AND_": "and", "$_OR_": "or", "$_XOR_": "xor"}
    SUPPORTED = set(BINARY) | {"$mux", "$xnor", "$shift", "$shiftx", "$div", "$mod"} | COMPARE | UNARY | SHIFT | LOGIC

    STATE = {"$dff", "$adff", "$aldff", "$dlatch"}

    def __init__(self, design, top, *, allow_state=False, allow_port_layouts=False, allow_bit_cells=False,
                 compact_names=False, proof_tables=False):
        require(set(design.get("modules", {})) == {top},
                "prototype requires exactly one module; hierarchy is not flattened implicitly")
        self.module = design["modules"][top]
        self.top = top
        require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", top), "unsupported top name")
        require(not self.module.get("memories"), "memories are unsupported")
        require(not self.module.get("processes"), "unlowered processes are unsupported")
        for attr in ("blackbox", "whitebox"):
            require(not int(self.module.get("attributes", {}).get(attr, "0"), 2),
                    f"{attr} module is unsupported")
        self.ports = self.module.get("ports", {})
        require(self.ports and any(p["direction"] == "output" for p in self.ports.values()),
                "must have observable output ports")
        self.drivers = {}
        self.inputs = []
        self.wires = []
        self.mapping = []
        self.allow_state = allow_state
        self.allow_bit_cells = allow_bit_cells
        self.compact_names = compact_names
        self.proof_tables = proof_tables
        self.registers = []
        self.latches = []
        self.states = []
        self.transition_outputs = []
        self.clock = None
        self.coverage_reasons = []
        self.port_layouts = []
        self.used_names = set(self.ports)
        for name, port in self.ports.items():
            require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", name), "unsupported port name")
            require(port["direction"] in ("input", "output"), "inout port is unsupported")
            nondefault = any(port.get(k, 0) for k in ("signed", "upto", "offset"))
            require(allow_port_layouts or not nondefault,
                    f"{name}: only unsigned [W-1:0] ports are supported")
            if nondefault:
                require(type(port.get("offset", 0)) is int and port.get("signed", 0) in (0, 1)
                        and port.get("upto", 0) in (0, 1), "invalid port layout")
                self.port_layouts.append({"name": name, "signed": bool(port.get("signed", 0)),
                                          "offset": port.get("offset", 0), "upto": bool(port.get("upto", 0))})
            self.check_bits(port["bits"])
            if port["direction"] == "input":
                self.inputs.append((name, len(port["bits"])))
                self.bind(port["bits"], name)
        for name, net in self.module.get("netnames", {}).items():
            # Yosys retains aliases of unused procedural temporaries containing
            # X. These names do not drive anything. Every actual port and cell
            # connection is checked separately and still rejects X/Z.
            require(net["bits"] and all((type(b) is int and b >= 0) or b in ("0", "1", "x", "z") for b in net["bits"]), "malformed net-name metadata")
            require(allow_state or "init" not in net.get("attributes", {}), f"{name}: initial state unsupported")

    def prepare_state(self, pending):
        from .statecheck import init_bits
        initial = init_bits(self.module)
        state_cells = [(n, c) for n, c in pending.items() if c["type"] in self.STATE]
        require(self.allow_state or not state_cells, "state cells require the sequential profile")
        clocks = {tuple(c["connections"]["CLK"]) for _, c in state_cells if "CLK" in c["connections"]}
        direct = [n for n, p in self.ports.items() if p["direction"] == "input" and len(p["bits"]) == 1
                  and clocks == {tuple(p["bits"])}]
        self.clock = direct[0] if direct else None
        self.state_pending = []
        for cell_name, cell in state_cells:
            con = cell["connections"]
            latch = cell["type"] == "$dlatch"
            control = "EN" if latch else "CLK"
            expected = {control, "D", "Q"} | ({"ARST"} if cell["type"] == "$adff" else
                                           {"ALOAD", "AD"} if cell["type"] == "$aldff" else set())
            require(set(con) == expected, "unexpected state cell ports")
            require(cell["port_directions"] == {k: "output" if k == "Q" else "input" for k in expected}, "state directions")
            for bits in con.values(): self.check_bits(bits)
            width = parameter(cell, "WIDTH")
            require(width == len(con["Q"]) == len(con["D"]) and len(con[control]) == 1, "state dimensions")
            require(parameter(cell, control + "_POLARITY") in (0, 1), "state control polarity")
            name = f"{'r' if self.compact_names else '_v2l_reg_'}{len(self.states)}"
            while name in self.used_names or name in self.module.get("netnames", {}): name += "_"
            self.used_names.add(name)
            self.bind(con["Q"], name)
            init = [initial.get(b) for b in con["Q"]]
            require(not latch or all(v is None for v in init), "initialized latch needs explicit init support")
            require(all(v is None for v in init) or all(v is not None for v in init), "partially initialized register")
            value = sum(int(v or 0) << i for i, v in enumerate(init))
            state = {"cell": cell_name, "type": cell["type"], "register": name, "width": width,
                     "bits": con["Q"], "emit_init": init[0] is not None, "init": value}
            self.states.append(state)
            self.mapping.append(state)
            self.state_pending.append((state, cell))
            del pending[cell_name]
        require(set(initial) <= {b for s in self.states for b in s["bits"]}, "initial value on non-register signal")

    def finish_state(self):
        reasons = set()
        edges = set()
        for index, (state, cell) in enumerate(self.state_pending):
            con = cell["connections"]
            width, name = state["width"], state["register"]
            nxt = self.bus(con["D"])
            if cell["type"] == "$dlatch":
                enable = self.bus(con["EN"])
                if not parameter(cell, "EN_POLARITY"):
                    enable = Expr(1, f"(.not {enable.code})")
                self.latches.append("{ " + f"name := {lean_string(name)}, width := {width}, enable := {enable.code}, d := {nxt.code}" + " }")
                self.transition_outputs.extend([(f"v2lean_state_{index}_D", nxt), (f"v2lean_state_{index}_EN", enable)])
                reasons.add("latch")
                continue
            edge = not bool(parameter(cell, "CLK_POLARITY"))
            edges.add(edge)
            fields = [f"name := {lean_string(name)}", f"width := {width}", f"next := {nxt.code}",
                      f"init := BitVec.ofNat {width} {state['init']}",
                      f"emitInit := {str(state['emit_init']).lower()}", f"negedge := {str(edge).lower()}"]
            if not state["emit_init"]: reasons.add("unconstrainedInit")
            if self.clock is None:
                fields.append(f"clockNet := some {self.bus(con['CLK']).code}")
                reasons.add("clockNet")
            for ctrl, polarity, field in (("ARST", "ARST_POLARITY", "asyncReset"), ("ALOAD", "ALOAD_POLARITY", "asyncLoad")):
                if ctrl not in con: continue
                require(len(con[ctrl]) == 1 and parameter(cell, polarity) in (0, 1), "async control dimensions/polarity")
                ctrl_expr = self.bus(con[ctrl])
                driver = self.drivers.get(con[ctrl][0])
                ctrl_name = driver[0] if driver and driver[1:] == (1, 0) else f"_v2l_control_{index}"
                if not driver or driver[1:] != (1, 0):
                    while ctrl_name in self.used_names: ctrl_name += "_"
                    self.used_names.add(ctrl_name)
                    self.wires.append((ctrl_name, ctrl_expr))
                value = f"BitVec.ofNat {width} {parameter(cell, 'ARST_VALUE')}" if ctrl == "ARST" else self.bus(con["AD"]).code
                if ctrl == "ALOAD": require(len(con["AD"]) == width, "async load dimensions")
                fields.append(f"{field} := some ({lean_string(ctrl_name)}, {str(bool(parameter(cell, polarity))).lower()}, {value})")
                reasons.add(field)
            self.registers.append("{ " + ", ".join(fields) + " }")
            for port, bits in con.items():
                if port != "Q": self.transition_outputs.append((f"v2lean_state_{index}_{port}", self.bus(bits)))
        if len(edges) > 1: reasons.add("negedgeMix")
        self.coverage_reasons = [r for r in ("asyncReset", "asyncLoad", "clockNet", "negedgeMix", "latch", "unconstrainedInit") if r in reasons]

    @staticmethod
    def check_bits(bits):
        require(bool(bits), "zero-width net")
        require(all((type(b) is int and b >= 0) or b in ("0", "1") for b in bits),
                "unknown/X/Z bit or malformed net ID")

    def bind(self, bits, name):
        for i, bit in enumerate(bits):
            require(type(bit) is int, f"{name}: a driver output aliases a constant")
            require(bit not in self.drivers, f"{name}: duplicate driver for bit {bit}")
            self.drivers[bit] = (name, len(bits), i)

    def bus(self, bits):
        self.check_bits(bits)
        chunks = []
        pos = 0
        while pos < len(bits):
            bit = bits[pos]
            end = pos + 1
            if isinstance(bit, str):
                while end < len(bits) and isinstance(bits[end], str):
                    end += 1
                value = sum(int(b) << i for i, b in enumerate(bits[pos:end]))
                chunk = Expr(end - pos, f"(.const (BitVec.ofNat {end - pos} {value}))")
            else:
                require(bit in self.drivers, f"undriven bit {bit}")
                name, width, index = self.drivers[bit]
                while end < len(bits) and self.drivers.get(bits[end]) == (name, width, index + end - pos):
                    end += 1
                count = end - pos
                base = f"(.var {lean_string(name)} {width})"
                code = base if index == 0 and count == width else f"(.slice {index} {count} {base})"
                chunk = Expr(count, code)
            chunks.append(chunk)
            pos = end
        result = chunks[0]
        for high in chunks[1:]:
            result = Expr(result.width + high.width, f"(@Expr.concat {high.width} {result.width} {high.code} {result.code})")
        return result

    def cell_expr(self, cell):
        ty = cell["type"]
        conn = cell["connections"]
        width = len(conn["Y"])
        args = {k: self.bus(v) for k, v in conn.items() if k != "Y"}
        if ty in self.GATES:
            require(width == 1 and all(e.width == 1 for e in args.values()), "invalid primitive gate width")
            if ty == "$_MUX_": return Expr(1, f"(.mux {args['S'].code} {args['B'].code} {args['A'].code})")
            if ty == "$_NOT_": return Expr(1, f"(.not {args['A'].code})")
            return Expr(1, f"(.{self.GATES[ty]} {args['A'].code} {args['B'].code})")
        if ty == "$mux":
            require(parameter(cell, "WIDTH") == width and args["A"].width == width
                    and args["B"].width == width and args["S"].width == 1,
                    "invalid mux dimensions")
            return Expr(width, f"(.mux {args['S'].code} {args['B'].code} {args['A'].code})")
        require(parameter(cell, "Y_WIDTH") == width, "Y_WIDTH mismatch")
        for key, expr in args.items():
            require(parameter(cell, f"{key}_WIDTH") == expr.width, f"{key}_WIDTH mismatch")
        if ty == "$shiftx":
            # Dynamic slices fill out-of-range bits with X. A logical shift is
            # equivalent only when every possible count selects entirely inside A.
            bits = conn["B"]
            require(not parameter(cell, "B_SIGNED") or bits[-1] == "0", "shiftx may have a negative index")
            maximum = sum(1 << i for i, b in enumerate(bits) if b != "0")
            require(maximum + width <= args["A"].width, "shiftx may select out-of-range/X bits")
            a, b = args["A"], args["B"]
            return resize(Expr(a.width, f"(.shr {a.code} {b.code})"), width)
        if ty == "$shift":
            # Yosys' generic shift moves right for a non-negative count and,
            # when B is signed, moves left by -B for a negative count.  The
            # A_SIGNED flag controls sign extension and the positive-count
            # right shift, exactly as in Yosys simlib.v.
            a_signed = bool(parameter(cell, "A_SIGNED"))
            b_signed = bool(parameter(cell, "B_SIGNED"))
            a = resize(args["A"], max(width, args["A"].width), a_signed)
            b = args["B"]
            right_op = "sshr" if a_signed else "shr"
            right = f"(.{right_op} {a.code} {b.code})"
            if not b_signed:
                return resize(Expr(a.width, right), width)
            sign = f"(.extract {b.width - 1} {b.code})"
            zero = f"(.const (BitVec.ofNat {b.width} 0))"
            magnitude = f"(.sub {zero} {b.code})"
            left = f"(.shl {a.code} {magnitude})"
            return resize(Expr(a.width, f"(.mux {sign} {left} {right})"), width)
        def truth(expr):
            return Expr(1, f"(.not (.eq {expr.code} (.const (BitVec.ofNat {expr.width} 0))))")
        if ty in self.REDUCE:
            a = args["A"]
            if ty in ("$reduce_or", "$reduce_bool", "$logic_not"):
                e = truth(a)
                if ty == "$logic_not": e = Expr(1, f"(.not {e.code})")
            elif ty == "$reduce_and":
                e = Expr(1, f"(.eq {a.code} (.const (BitVec.ofNat {a.width} {(1 << a.width) - 1})))")
            else:
                bits = [f"(.extract {i} {a.code})" for i in range(a.width)]
                code = bits[0]
                for b in bits[1:]: code = f"(.xor {code} {b})"
                e = Expr(1, f"(.not {code})" if ty == "$reduce_xnor" else code)
            return resize(e, width)
        if ty in self.LOGIC:
            a, b = truth(args["A"]), truth(args["B"])
            return resize(Expr(1, f"(.{'and' if ty == '$logic_and' else 'or'} {a.code} {b.code})"), width)
        if ty in self.SHIFT:
            a = resize(args["A"], max(width, args["A"].width), bool(parameter(cell, "A_SIGNED")))
            op = "shl" if ty in ("$shl", "$sshl") else ("sshr" if ty == "$sshr" and parameter(cell, "A_SIGNED") else "shr")
            return resize(Expr(a.width, f"(.{op} {a.code} {args['B'].code})"), width)
        signed = all(parameter(cell, f"{key}_SIGNED") for key in args)
        if ty in self.COMPARE:
            opwidth = max(e.width for e in args.values())
            a, b = (resize(args[k], opwidth, signed) for k in ("A", "B"))
            if ty in ("$eq", "$ne"):
                code = f"(.eq {a.code} {b.code})"
            else:
                if ty in ("$gt", "$le"): a, b = b, a
                code = f"(.{'slt' if signed else 'ult'} {a.code} {b.code})"
            if ty in ("$ne", "$le", "$ge"): code = f"(.not {code})"
            return resize(Expr(1, code), width)
        common_width = max(width, *(e.width for e in args.values()))
        a = resize(args["A"], common_width, signed)
        if ty in ("$div", "$mod"):
            # Verilog produces X on division by zero. A literal one anywhere
            # in B proves it nonzero for every valuation of the remaining bits.
            require("1" in conn["B"], "division/modulo requires a provably nonzero divisor")
            b = resize(args["B"], common_width, signed)
            op = "udiv" if ty == "$div" else "umod"
            if not signed:
                return resize(Expr(common_width, f"(.{op} {a.code} {b.code})"), width)
            zero = f"(.const (BitVec.ofNat {common_width} 0))"
            sa, sb = (f"(.extract {common_width - 1} {e.code})" for e in (a, b))
            aa = f"(.mux {sa} (.sub {zero} {a.code}) {a.code})"
            ab = f"(.mux {sb} (.sub {zero} {b.code}) {b.code})"
            magnitude = f"(.{op} {aa} {ab})"
            sign = f"(.xor {sa} {sb})" if ty == "$div" else sa
            return resize(Expr(common_width, f"(.mux {sign} (.sub {zero} {magnitude}) {magnitude})"), width)
        if ty == "$not":
            result = Expr(common_width, f"(.not {a.code})")
        elif ty == "$neg":
            result = Expr(common_width, f"(.sub (.const (BitVec.ofNat {common_width} 0)) {a.code})")
        else:
            b = resize(args["B"], common_width, signed)
            op = "xor" if ty == "$xnor" else self.BINARY[ty]
            result = Expr(common_width, f"(.{op} {a.code} {b.code})")
            if ty == "$xnor": result = Expr(common_width, f"(.not {result.code})")
        return resize(result, width)

    def build(self):
        pending = dict(sorted(self.module.get("cells", {}).items()))
        self.prepare_state(pending)
        aliases_by_bits = {}
        for name, net in sorted(self.module.get("netnames", {}).items()):
            if not net.get("hide_name"):
                aliases_by_bits.setdefault(tuple(net["bits"]), []).append(name)
        for name, cell in pending.items():
            require(cell["type"] in self.SUPPORTED or (self.allow_bit_cells and cell["type"] in self.GATES), f"{name}: unsupported cell {cell['type']}")
            expected = {"A", "B", "S", "Y"} if cell["type"] in ("$mux", "$pmux", "$_MUX_") else (
                {"A", "Y"} if cell["type"] in self.UNARY or cell["type"] == "$_NOT_" else {"A", "B", "Y"})
            require(set(cell.get("connections", {})) == expected, f"{name}: unexpected cell ports")
            require(cell.get("port_directions") == {k: "output" if k == "Y" else "input" for k in expected},
                    f"{name}: invalid cell directions")
            for bits in cell["connections"].values():
                self.check_bits(bits)
        while pending:
            progress = False
            for cell_name, cell in list(pending.items()):
                if any(type(b) is int and b not in self.drivers
                       for k, bits in cell["connections"].items() if k != "Y" for b in bits):
                    continue
                expr = self.cell_expr(cell)
                bits = cell["connections"]["Y"]
                name = next((n for n in aliases_by_bits.get(tuple(bits), ()) if n not in self.used_names),
                            f"{'w' if self.compact_names else '_v2l_wire_'}{len(self.wires)}")
                while name in self.used_names:
                    name += "_"
                self.used_names.add(name)
                self.bind(bits, name)
                self.wires.append((name, expr))
                self.mapping.append({"cell": cell_name, "type": cell["type"], "wire": name,
                                     "width": expr.width, "bits": bits,
                                     "source": cell.get("attributes", {}).get("src")})
                del pending[cell_name]
                progress = True
            require(progress, f"undriven inputs or combinational cycle: {list(pending)}")
        self.finish_state()
        outputs = [(n, self.bus(p["bits"])) for n, p in self.ports.items() if p["direction"] == "output"]
        return self.render(outputs)

    def render(self, outputs):
        inputs = ",\n    ".join(f"{{ name := {lean_string(n)}, width := {w} }}" for n, w in self.inputs)
        wire_entries = [f"{{ name := {lean_string(n)}, width := {e.width}, expr := {e.code} }}" for n, e in self.wires]
        wire_defs = ""
        wire_value = "[" + ",\n    ".join(wire_entries) + "]"
        if len(wire_entries) > 128:
            chunks = [wire_entries[i:i + 64] for i in range(0, len(wire_entries), 64)]
            wire_defs = "\n\n".join(f"def wireChunk_{i} : List Wire := [" + ",\n    ".join(chunk) + "]" for i, chunk in enumerate(chunks))
            wire_value = " ++ ".join(f"wireChunk_{i}" for i in range(len(chunks)))
        outs = ",\n    ".join(f"{{ name := {lean_string(n)}, width := {e.width}, expr := {e.code} }}" for n, e in outputs)
        order = ", ".join(lean_string(n) for n in self.ports)
        regs = ",\n    ".join(self.registers)
        latches = ",\n    ".join(self.latches)
        clock = "none" if self.clock is None else "some " + lean_string(self.clock)
        coverage = ".perRegister [" + ", ".join("." + r for r in self.coverage_reasons) + "]" if self.coverage_reasons else ".full"
        checks = "example : impl.wellWidthedb = true := by decide +kernel" if self.coverage_reasons else "example : CheckWidth.moduleChecksb impl = true := by decide +kernel"
        transition_view = ""
        if self.latches:
            # Check the complete combinational transition relation with each Q
            # as an arbitrary input; the cycle simulator does not model latches.
            state_inputs = ", ".join(f"{{ name := {lean_string(s['register'])}, width := {s['width']} }}" for s in self.states)
            transition_view = f'''def transitionView : Module := {{
  name := impl.name
  inputs := impl.inputs ++ [{state_inputs}]
  wires := impl.wires
  outputs := impl.outputs ++ transitionOutputs
}}'''
            checks = "example : CheckWidth.moduleChecksb transitionView = true := by decide +kernel"
        extra = ",\n    ".join(f"{{ name := {lean_string(n)}, width := {e.width}, expr := {e.code} }}" for n, e in self.transition_outputs)
        layouts = ", ".join("{ name := " + lean_string(p["name"]) + f", signed := {str(p['signed']).lower()}, offset := {p['offset']}, upto := {str(p['upto']).lower()} }}" for p in self.port_layouts)
        proof_text = "example : impl.checkErrors = [] := by decide +kernel\n" + checks
        if self.proof_tables:
            from .checkproofs import render
            proof_text = render(self)
        map_import = "import LeanRTL.Core.CheckWidthFast\n" if self.proof_tables and len(self.wires) >= 1024 else ""
        return f'''-- Generated deterministically from RTLIL; no original JSON is embedded.
import LeanRTL.Core.Compiler
import LeanRTL.Core.Semantics
import LeanRTL.Core.Check
import LeanRTL.Core.Coverage
{map_import}
open LeanRTL
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
namespace V2LeanImported

{wire_defs}

def impl : Module := {{
  name := {lean_string(self.top)}
  inputs := [{inputs}]
  wires := {wire_value}
  outputs := [{outs}]
  portOrder := [{order}]
  portLayouts := [{layouts}]
  regs := [{regs}]
  latches := [{latches}]
  clock := {clock}
}}

def transitionOutputs : List OutPort := [{extra}]
{transition_view}

{proof_text}
example : impl.semanticCoverage = {coverage} := by decide +kernel

end V2LeanImported

-- The executable exports the actual checked Module, never cached RTLIL.
def main (args : List String) : IO UInt32 := do
  match args with
  | ["export", path] =>
    IO.FS.writeFile path V2LeanImported.impl.interfaceCore.toRtlilJson
    return 0
  | ["wrapper", path] =>
    IO.FS.writeFile path V2LeanImported.impl.interfaceWrapper
    return 0
  | ["eval"] =>
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let tokens := line.trimAscii.toString.splitOn " "
      let mut vals : List (String × Nat) := []
      for token in tokens do
        match token.splitOn "=" with
        | [n, v] =>
          match v.toNat? with
          | some value => vals := vals ++ [(n, value)]
          | none => throw (IO.userError "invalid input value")
        | _ => throw (IO.userError "invalid input token")
      let base := Env.ofList vals
      let wireValues := V2LeanImported.impl.wires.foldl (evalWireMemoStep base) []
      let env := wireValuesEnv wireValues base
      let outs := (V2LeanImported.impl.outputs ++ V2LeanImported.transitionOutputs).map
        (fun o => (o.name, (eval o.expr env).toNat))
      stdout.putStrLn (String.intercalate " " (outs.map fun (n, v) => n ++ "=" ++ toString v))
    return 0
  | _ =>
    IO.eprintln "expected: export <path> | eval"
    return 1
'''
