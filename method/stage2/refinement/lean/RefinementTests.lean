import FrozenRefinement

open SpecIR FrozenRefinement

def freeSpec : Design Unit Unit where
  name := "unconstrained output"
  machine := {init := (), step := fun _ _ => (), out := fun _ _ => [("q", .x 1)]}
  renderIn := fun _ => []

def zeroSpec : Design Unit Unit :=
  {freeSpec with machine := {init := (), step := fun _ _ => (), out := fun _ _ => [("q", .bits 1 0)]}}

def oracleModel : Model Unit where
  State := Nat
  timebase := .fullCycle
  initial := fun o => o "initial" % 2
  step := fun _ _ o => o "next" % 2
  out := fun s _ _ => [("q", .bits 1 s)]

theorem arbitrary_initial_and_every_step : Refines freeSpec oracleModel := by
  apply Certificate.refines
  exact {
    timebase := rfl
    relation := fun _ _ => True
    init := fun _ => True.intro
    step := fun _ _ _ _ _ => True.intro
    observe := by intros; simp [freeSpec, oracleModel, OutputsRefine, ValueRefines]
  }

theorem cannot_choose_only_favorable_initial : ¬ Refines zeroSpec oracleModel := by
  intro h
  have bad := h.2 (fun _ => 1) (fun _ _ => 0) [()]
  simp [zeroSpec, oracleModel, specTrace, Model.traceFrom, OutputsRefine, ValueRefines] at bad

theorem cannot_choose_only_favorable_next : ¬ Refines zeroSpec oracleModel := by
  intro h
  have bad := h.2 (fun _ => 0) (fun _ _ => 1) [(), ()]
  simp [zeroSpec, oracleModel, specTrace, Model.traceFrom, OutputsRefine, ValueRefines] at bad

example : ¬ ValueRefines (.bits 1 0) (.bits 1 1) := by decide
example : ¬ ValueRefines (.bits 1 0) (.x 1) := by decide
example : ¬ ValueRefines (.hole "missing" 1) (.bits 1 0) := by decide
example : ¬ ValueRefines (.z 1) (.bits 1 0) := by decide
example : ¬ ValueRefines (.x 1) (.bits 2 0) := by decide
example : ¬ OutputsRefine [("q", .x 1)] [("other", .bits 1 0)] := by
  simp [OutputsRefine, ValueRefines]

def uninitialized : LeanRTL.Symbolic.Module where
  core := {
    name := "uninitialized"
    inputs := []
    outputs := [{name := "q", width := 1, expr := .var "r" 1}]
    regs := [{name := "r", width := 1, init := 0, emitInit := false, next := .var "r" 1}]
  }
example : uninitialized.initial (fun _ => 1) = [("r", 1)] := by decide
example : uninitialized.initial (fun _ => 0) = [("r", 0)] := by decide

def dualEdge : LeanRTL.FourState.NBA.Clocked where
  name := "dualEdge"
  inputs := [{name := "clk", width := 1}]
  states := [{name := "p", width := 1}, {name := "n", width := 1}]
  wires := []
  outputs := []
  processes := [
    {events := [{name := "clk", positive := true}], targets := ["p"],
      body := .write "p" 0 (@LeanRTL.FourState.Expr.fill 1 .one)},
    {events := [{name := "clk", positive := false}], targets := ["n"],
      body := .write "n" 0 (@LeanRTL.FourState.Expr.fill 1 .one)}]
  portOrder := ["clk"]

-- The current clocked adapter explicitly has fixed-zero initial state.
-- Arbitrary initial-state quantification is tested above for Symbolic.Module.
example : clockedInitial dualEdge (fun n => if n == "p" then 1 else 0) =
    [("p", [.zero]), ("n", [.zero])] := by decide
example : clockedInitial dualEdge (fun n => if n == "n" then 1 else 0) =
    [("p", [.zero]), ("n", [.zero])] := by decide
example : dualEdge.step (clockedInitial dualEdge (fun _ => 0))
    (fun _ _ => .zero) (fun _ _ => .one) = [("p", [.one]), ("n", [.zero])] := by decide
example : dualEdge.step (clockedInitial dualEdge (fun _ => 0))
    (fun _ _ => .one) (fun _ _ => .zero) = [("p", [.zero]), ("n", [.one])] := by decide
example : dualEdge.step (clockedInitial dualEdge (fun _ => 0))
    (fun _ _ => .one) (fun _ _ => .one) = [("p", [.zero]), ("n", [.zero])] := by decide

#print axioms arbitrary_initial_and_every_step
#print axioms cannot_choose_only_favorable_initial
#print axioms cannot_choose_only_favorable_next
#print axioms Certificate.refines
#print axioms specTrace_eq_trace
