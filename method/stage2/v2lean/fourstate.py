"""Experimental four-state combinational importer. Never counted as a local proof.

Consumes proc -noopt RTLIL, retaining explicit X/Z and the pmux default arm.
The ordinary two-state importer and its acceptance checks remain separate.
"""
from .importer import Expr, Importer, lean_string, parameter, require, resize


class FourStateImporter(Importer):
    SUPPORTED = Importer.SUPPORTED - {"$div", "$mod"} | {"$pmux", "$eqx", "$nex"}

    @staticmethod
    def check_bits(bits):
        require(bool(bits) and all((type(b) is int and b >= 0) or
                                  b in ("0", "1", "x", "z") for b in bits),
                "malformed four-state net")

    def bus(self, bits):
        self.check_bits(bits)
        chunks = []
        pos = 0
        while pos < len(bits):
            bit = bits[pos]
            end = pos + 1
            if bit in ("x", "z"):
                while end < len(bits) and bits[end] == bit:
                    end += 1
                chunk = Expr(end - pos, f"(@Expr.fill {end-pos} .{bit})")
            else:
                while end < len(bits) and bits[end] not in ("x", "z"):
                    end += 1
                chunk = super().bus(bits[pos:end])
            chunks.append(chunk)
            pos = end
        result = chunks[0]
        for high in chunks[1:]:
            result = Expr(result.width + high.width,
                          f"(@Expr.concat {high.width} {result.width} {high.code} {result.code})")
        return result

    def cell_expr(self, cell):
        if cell["type"] in ("$eqx", "$nex"):
            con = cell["connections"]
            a, b = (self.bus(con[k]) for k in ("A", "B"))
            w = len(con["Y"])
            require(parameter(cell, "A_WIDTH") == a.width and parameter(cell, "B_WIDTH") == b.width
                    and parameter(cell, "Y_WIDTH") == w, "case equality dimensions")
            signed = bool(parameter(cell, "A_SIGNED") and parameter(cell, "B_SIGNED"))
            common = max(a.width, b.width)
            a, b = resize(a, common, signed), resize(b, common, signed)
            code = f"(.caseEq {a.code} {b.code})"
            if cell["type"] == "$nex": code = f"(.not {code})"
            return resize(Expr(1, code), w)
        if cell["type"] != "$pmux":
            return super().cell_expr(cell)
        con = cell["connections"]
        w, n = parameter(cell, "WIDTH"), parameter(cell, "S_WIDTH")
        require(w > 0 and n > 0 and len(con["Y"]) == len(con["A"]) == w
                and len(con["B"]) == w*n and len(con["S"]) == n, "invalid pmux dimensions")
        a, b, s = (self.bus(con[k]).code for k in ("A", "B", "S"))
        return Expr(w, f"(@Expr.pmux {w} {n} {a} {b} {s})")

    def render(self, outputs):
        require(not self.states and not self.port_layouts,
                "four-state prototype currently supports combinational default-layout ports")
        inputs = ",\n".join(f"{{ name := {lean_string(n)}, width := {w} }}" for n, w in self.inputs)
        def entries(values):
            return ",\n".join(f"{{ name := {lean_string(n)}, width := {e.width}, expr := {e.code} }}"
                              for n, e in values)
        return f'''import LeanRTL.Core.FourStateVerilog
import LeanRTL.Core.FourStateEncoding
open LeanRTL.FourState
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000
def impl : Module := {{
  name := {lean_string(self.top)}
  inputs := [{inputs}]
  wires := [{entries(self.wires)}]
  outputs := [{entries(outputs)}]
}}
example : impl.valid = true := by decide +kernel
def main (args : List String) : IO UInt32 := do
  match args with
  | ["export", path] =>
    IO.FS.writeFile path (Verilog.emit impl)
    return 0
  | ["encode", path] =>
    let encoded := Encoding.module impl
    if !encoded.checkErrors.isEmpty then throw (IO.userError "invalid encoded module")
    IO.FS.writeFile path encoded.toRtlilJson
    return 0
  | ["eval"] =>
    let stdin ← IO.getStdin
    let stdout ← IO.getStdout
    repeat
      let line ← stdin.getLine
      if line.isEmpty then break
      let mut vals : List (String × List Char) := []
      for token in line.trimAscii.toString.splitOn " " do
        match token.splitOn "=" with
        | [n, value] =>
          if !(value.all (fun c => c == '0' || c == '1' || c == 'x' || c == 'z')) then
            throw (IO.userError "invalid four-state input")
          vals := vals ++ [(n, value.toList.reverse)]
        | _ => throw (IO.userError "invalid input token")
      let env : Env := fun n i =>
        match ((vals.lookup n).getD []).getD i 'x' with
        | '0' => .zero
        | '1' => .one
        | 'z' => .z
        | _ => .x
      stdout.putStrLn (String.intercalate " " ((impl.eval env).map (fun (n, v) => n ++ "=" ++ v)))
    return 0
  | _ => return 2
'''
