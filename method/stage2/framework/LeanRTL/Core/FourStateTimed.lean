import LeanRTL.Core.FourStateSubstitution
import LeanRTL.Core.FourStateVerilog

/-! An autonomous register with a positive, constant delay between blocking updates.
Times are integer femtoseconds; observations are after the active region settles.
This domain has no external inputs, competing processes, or zero-delay scheduling. -/
namespace LeanRTL.FourState.Timed

structure Signal where
  name : String
  width : Nat
  initial : Expr width
  next : Expr width
  periodFS : Nat

def Signal.valid (s : Signal) : Bool :=
  s.width > 0 && s.periodFS > 0 && s.periodFS < 2^64 && s.initial.valid [] &&
    s.next.valid [(s.name, s.width)]

abbrev State := List Bit

def Signal.initialState (s : Signal) : State :=
  (List.finRange s.width).map (FourState.eval s.initial (fun _ _ => .x))

def Signal.step (s : Signal) (state : State) : State :=
  let env : Env := fun n i => if n == s.name then state.getD i .x else .x
  (List.finRange s.width).map (FourState.eval s.next env)

def Signal.steps (s : Signal) : Nat → State
  | 0 => s.initialState
  | n+1 => s.step (s.steps n)

def Signal.at (s : Signal) (timeFS : Nat) : State := s.steps (timeFS / s.periodFS)

def Signal.renderAt (s : Signal) (timeFS : Nat) : String :=
  String.ofList ((s.at timeFS).reverse.map Bit.char)

theorem at_zero (s : Signal) : s.at 0 = s.initialState := by
  simp [Signal.at, Signal.steps]

theorem before_first (s : Signal) (t : Nat) (h : t < s.periodFS) :
    s.at t = s.initialState := by
  simp [Signal.at, Nat.div_eq_of_lt h, Signal.steps]

theorem at_tick (s : Signal) (n : Nat) (h : 0 < s.periodFS) :
    s.at (n * s.periodFS) = s.steps n := by
  simp [Signal.at, Nat.mul_div_cancel, h]

theorem trace_equiv (a b : Signal) (h : a = b) (t : Nat) :
    a.renderAt t = b.renderAt t := congrArg (fun s => s.renderAt t) h

/-- Sized SystemVerilog expressions for procedural RHS evaluation. No continuous
helper wires are introduced: a blocking assignment must see earlier blocking writes. -/
partial def inlineExpr : {w : Nat} → Expr w → String
  | w, e =>
    let sized (s : String) := s!"$unsigned({w}'({s}))"
    let binary (a b : String) (op : String) := sized s!"({a} {op} {b})"
    match e with
    | .const v => s!"{w}'d{v.toNat}"
    | .fill b => s!"{w}'b{String.ofList (List.replicate w b.char)}"
    | .var n _ => Verilog.escV n
    | .not a => sized s!"(~{inlineExpr a})"
    | .and a b => binary (inlineExpr a) (inlineExpr b) "&"
    | .or a b => binary (inlineExpr a) (inlineExpr b) "|"
    | .xor a b => binary (inlineExpr a) (inlineExpr b) "^"
    | .add a b => binary (inlineExpr a) (inlineExpr b) "+"
    | .sub a b => binary (inlineExpr a) (inlineExpr b) "-"
    | .mul a b => binary (inlineExpr a) (inlineExpr b) "*"
    | .udiv a b => binary (inlineExpr a) (inlineExpr b) "/"
    | .shl a b => binary (inlineExpr a) (inlineExpr b) "<<"
    | .shr a b => binary (inlineExpr a) (inlineExpr b) ">>"
    | .sshr a b => binary s!"$signed({inlineExpr a})" (inlineExpr b) ">>>"
    | .eq a b => binary (inlineExpr a) (inlineExpr b) "=="
    | .caseEq a b => binary (inlineExpr a) (inlineExpr b) "==="
    | .ult a b => binary (inlineExpr a) (inlineExpr b) "<"
    | .slt a b => binary s!"$signed({inlineExpr a})" s!"$signed({inlineExpr b})" "<"
    | .mux c a b => sized s!"({inlineExpr c} ? {inlineExpr a} : {inlineExpr b})"
    | .concat a b => "{" ++ inlineExpr a ++ ", " ++ inlineExpr b ++ "}"
    | .zext _ a => sized s!"$unsigned({inlineExpr a})"
    | .sext _ a => sized s!"$signed({inlineExpr a})"
    | .extract i a => sized s!"($unsigned({inlineExpr a}) >> {i})"
    | .slice lo _ a => sized s!"($unsigned({inlineExpr a}) >> {lo})"
    | @Expr.pmux _ n a b sel => Id.run do
      let mut result := inlineExpr a
      let mut active := "1'b0"
      for i in List.range n do
        let test := s!"(1'($unsigned({inlineExpr sel}) >> {i}) === 1'b1)"
        let part := sized s!"($unsigned({inlineExpr b}) >> {w*i})"
        result := sized s!"({test} ? ({active} ? {w}'bx : {part}) : {result})"
        active := s!"({active} | {test})"
      return result

/-- Emit physical time explicitly. Scaling to femtoseconds avoids losing the
original time unit when the generated file is compiled alongside other modules. -/
def emit (top : String) (s : Signal) : String :=
  String.intercalate "\n" [
    "`timescale 1fs / 1fs",
    s!"module {Verilog.escV top}(output reg {Verilog.rangeC s.width}{Verilog.escV s.name});",
    s!"  initial {Verilog.escV s.name} = {inlineExpr s.initial};",
    s!"  always #(64'd{s.periodFS}) {Verilog.escV s.name} = {inlineExpr s.next};",
    "endmodule", ""]

end LeanRTL.FourState.Timed
