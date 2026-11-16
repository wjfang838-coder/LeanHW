import LeanRTL.Core.FourStateClocked

namespace LeanRTL.FourState.NBA

/-- Value queued for a register when its owning process is activated. -/
def Clocked.pendingExpr (m : Clocked) (reg : LeanRTL.InPort) : Expr reg.width :=
  let old := Expr.var reg.name reg.width
  match m.processes.find? (fun p => reg.name ∈ p.targets) with
  | some p => lower p.body reg.name old
  | none => old

def Clocked.pendingValue (m : Clocked) (reg : LeanRTL.InPort) (read : Env) : Value reg.width :=
  let old := eval (.var reg.name reg.width) read
  match m.processes.find? (fun p => reg.name ∈ p.targets) with
  | some p => execute p.body reg.name read old
  | none => old

theorem pending_expr_correct (m : Clocked) (reg : LeanRTL.InPort) (read : Env) :
    eval (m.pendingExpr reg) read = m.pendingValue reg read := by
  unfold Clocked.pendingExpr Clocked.pendingValue
  split
  · exact lower_correct _ _ _ _
  · rfl

/-- Compare every possible process activation, not just those reached by a trace.
Output names are disjoint from physical observations; validity checks freshness. -/
def Clocked.transition (m : Clocked) : FourState.Module :=
  { name := m.name ++ "_transition", inputs := m.inputs ++ m.states, wires := m.wires,
    outputs := m.states.map (fun reg =>
      {name := "next__" ++ reg.name, width := reg.width, expr := m.pendingExpr reg}) ++
      m.outputs.map (fun o => {o with name := "out__" ++ o.name}) }

theorem values_env_append (a b : Snapshot) (input : Env) :
    valuesEnv (a ++ b) input = valuesEnv a (valuesEnv b input) := by
  funext n i
  simp only [valuesEnv, List.lookup_append]
  cases a.lookup n <;> rfl

theorem transition_eval_correct (m : Clocked) (state : Snapshot) (input : Env) :
    m.transition.eval (valuesEnv state input) =
      let read := valuesEnv (m.wireSnapshot state input) input
      m.states.map (fun reg => ("next__" ++ reg.name, renderValue (m.pendingValue reg read))) ++
      m.outputs.map (fun o => ("out__" ++ o.name, renderValue (eval o.expr read))) := by
  simp only [FourState.Module.eval, Clocked.transition, Clocked.wireSnapshot,
    FourState.Module.wireValues, Clocked.combinational, values_env_append,
    List.map_append, List.map_map, Function.comp_def, pending_expr_correct]

/-- The actual edge-controlled step is reconstructed from the pending expressions
using the original four-state edge predicates and unchanged old register values. -/
theorem step_pending_correct (m : Clocked) (state : Snapshot) (before after : Env) :
    m.step state before after =
      let read := valuesEnv (m.wireSnapshot state after) after
      m.states.map fun reg =>
        let old := eval (.var reg.name reg.width) read
        let next := match m.processes.find? (fun p => reg.name ∈ p.targets) with
          | some p => if p.fired before after then eval (m.pendingExpr reg) read else old
          | none => old
        (reg.name, (List.finRange reg.width).map next) := by
  unfold Clocked.step
  apply List.map_congr_left
  intro reg _
  rw [pending_expr_correct]
  unfold Clocked.pendingValue
  cases m.processes.find? (fun p => reg.name ∈ p.targets) <;> simp only [eval]

end LeanRTL.FourState.NBA
