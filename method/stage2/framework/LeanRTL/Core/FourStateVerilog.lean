import LeanRTL.Core.FourState
namespace LeanRTL.FourState.Verilog
open LeanRTL.FourState
/-- The result bit-width of an `Expr` (its type index). -/
def ewidth {w : Nat} (_ : Expr w) : Nat := w

/-- A `[w-1:0]` range for a bus, empty for a 1-bit scalar. -/
def rangeC (w : Nat) : String := if w == 1 then "" else s!"[{w - 1}:0] "

/-- Escape a name as a Verilog identifier.  Plain identifiers (`[A-Za-z_][A-Za-z0-9_$]*`) pass
    through; anything else (e.g. per-entry register names like `RAM[3]`) becomes a Verilog
    **escaped identifier** `\name ` with a backslash prefix and trailing space. -/
def escV (n : String) : String :=
  let plainHead := n.length > 0 && (n.front.isAlpha || n.front == '_')
  let plainBody := n.all (fun c => c.isAlphanum || c == '_' || c == '$')
  if plainHead && plainBody then n else "\\" ++ n ++ " "

/-- Is `s` a bare Verilog identifier (safe to bit-select / replicate)? -/
def isIdent (s : String) : Bool :=
  s.length > 0 && !s.front.isDigit && s.all (fun c => c.isAlphanum || c == '_')

/-- SSA emitter state: fresh-net counter and accumulated bindings `(name, width, rhs)` (reversed). -/
abbrev SM := StateM (Nat × List (String × Nat × String))

/-- Bind `rhs` to a fresh net of width `w` (prefix `pfx`); return its name. -/
def fresh (pfx : String) (w : Nat) (rhs : String) : SM String := do
  let (n, binds) ← get
  let nm := s!"{pfx}{n}"
  set (n + 1, (nm, w, rhs) :: binds)
  return nm

/-- Force `s` (width `w`) to be a bare identifier — materialize a net if it is a compound
    expression — so it can be bit-selected or replicated. -/
def ensureNet (pfx : String) (w : Nat) (s : String) : SM String :=
  if isIdent s then return s else fresh pfx w s

/-- Emit each operator into a sized net, preserving ternary bit-merging and explicit X/Z. -/
partial def emitCore (pfx : String) : {w : Nat} → Expr w → SM String
  | w, e =>
    match e with
    | .const v      => return s!"{w}'d{v.toNat}"
    | .fill b       => return s!"{w}'b{String.ofList (List.replicate w b.char)}"
    | @Expr.pmux _ n a b s => do
      let an ← emitCore pfx a
      let bn ← ensureNet pfx (w*n) (← emitCore pfx b)
      let sn ← ensureNet pfx n (← emitCore pfx s)
      -- Explicit procedural-if semantics of the Yosys simulation model.
      -- Track definite-one selections; unknown selections are inactive.
      let mut value := an
      let mut active := "1'b0"
      for i in List.range n do
        let selected ← fresh pfx 1 s!"({sn}[{i}] === 1'b1)"
        let choice ← fresh pfx w s!"({active} ? {w}'bx : {bn}[{w*(i+1)-1}:{w*i}])"
        value ← fresh pfx w s!"({selected} ? {choice} : {value})"
        active ← fresh pfx 1 s!"({active} | {selected})"
      return value
    | .var n _      => return escV n
    | .not a        => do let x ← emitCore pfx a; fresh pfx w s!"(~ {x})"
    | .and a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} & {y})"
    | .or a b       => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} | {y})"
    | .xor a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} ^ {y})"
    | .add a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} + {y})"
    | .sub a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} - {y})"
    | .mul a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} * {y})"
    | .udiv a b     => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} / {y})"
    | .shl a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} << {y})"
    | .shr a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} >> {y})"
    | .sshr a b     => do let x ← emitCore pfx a; let y ← emitCore pfx b
                          fresh pfx w s!"($signed({x}) >>> {y})"
    | .eq a b       => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx 1 s!"({x} == {y})"
    | .caseEq a b   => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx 1 s!"({x} === {y})"
    | .ult a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx 1 s!"({x} < {y})"
    | .slt a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b
                          fresh pfx 1 s!"($signed({x}) < $signed({y}))"
    | .mux s a b    => do let sN ← emitCore pfx s; let x ← emitCore pfx a; let y ← emitCore pfx b
                          fresh pfx w s!"({sN} ? {x} : {y})"
    | .concat a b   => do let x ← emitCore pfx a; let y ← emitCore pfx b
                          fresh pfx w ("{" ++ x ++ ", " ++ y ++ "}")
    | .zext k a     => do let x ← ensureNet pfx (ewidth a) (← emitCore pfx a)
                          fresh pfx w ("{ {" ++ toString k ++ "{1'b0}}, " ++ x ++ " }")
    | .sext k a     => do let wa := ewidth a
                          let x ← ensureNet pfx wa (← emitCore pfx a)
                          fresh pfx w ("{ {" ++ toString k ++ "{" ++ x ++ "[" ++ toString (wa - 1)
                                       ++ "]}}, " ++ x ++ " }")
    | .extract i a  => do let x ← ensureNet pfx (ewidth a) (← emitCore pfx a)
                          fresh pfx 1 s!"{x}[{i}]"
    | .slice lo len a => do let x ← ensureNet pfx (ewidth a) (← emitCore pfx a)
                            fresh pfx w s!"{x}[{lo + len - 1}:{lo}]"

/-- Direct HDL renderer for the four-state domain; no two-state Yosys optimization pass. -/
def emit (m : Module) : String := Id.run do
  let used := m.name :: (m.inputs.map (·.name) ++ m.wires.map (·.name) ++ m.outputs.map (·.name))
  let pfx := String.ofList (List.replicate (1 + (used.map String.length).foldl max 0) '_')
  let mut state : Nat × List (String × Nat × String) := (0, [])
  let mut assignments : List String := []
  for wire in m.wires ++ m.outputs do
    let (rhs, next) := (emitCore pfx wire.expr).run state
    state := next
    assignments := assignments ++ [s!"  assign {escV wire.name} = {rhs};"]
  let ports := (m.inputs.map (fun p => s!"input wire {rangeC p.width}{escV p.name}")) ++
               (m.outputs.map (fun p => s!"output wire {rangeC p.width}{escV p.name}"))
  let decls := m.wires.map (fun p => s!"  wire {rangeC p.width}{escV p.name};")
  let temps := state.2.reverse.map (fun (n, w, rhs) => s!"  wire {rangeC w}{n} = {rhs};")
  return String.intercalate "\n" ([s!"module {escV m.name} (", String.intercalate ",\n" ports, ");"] ++
    decls ++ temps ++ assignments ++ ["endmodule", ""])

end LeanRTL.FourState.Verilog
