import LeanRTL.Core.FourStateControl

namespace LeanRTL.FourState.Source
open Encoding

mutual
  /-- Untimed blocking procedural control, before mux/SSA lowering. -/
  inductive Stmt where
    | skip
    | assign : FourState.Wire → Stmt
    | seq : Stmt → Stmt → Stmt
    | ite : {k : Nat} → FourState.Expr k → Stmt → Stmt → Stmt
    | cases : {k : Nat} → FourState.Expr k → Arms k → Stmt
  inductive Arms : Nat → Type where
    | default : {k : Nat} → Stmt → Arms k
    | arm : {k : Nat} → List (FourState.Expr k) → Stmt → Arms k → Arms k
end

mutual
  def execute : Stmt → FourState.Env → FourState.Env
    | .skip, env => env
    | .assign binding, env => putValue env binding.name (FourState.eval binding.expr env)
    | .seq first second, env => execute second (execute first env)
    | .ite condition yes no, env =>
      if truthy (FourState.eval condition env) then execute yes env else execute no env
    | .cases selector arms, env => executeArms selector arms env
  def executeArms {k : Nat} (selector : FourState.Expr k) : Arms k → FourState.Env → FourState.Env
    | .default stmt, env => execute stmt env
    | .arm labels stmt rest, env =>
      if labels.any (fun label => labelMatches selector label env) then execute stmt env
      else executeArms selector rest env
end

mutual
  def stmtValid (scope : List (String × Nat)) : Stmt → Bool
    | .skip => true
    | .assign binding => scope.lookup binding.name == some binding.width && binding.expr.valid scope
    | .seq first second => stmtValid scope first && stmtValid scope second
    | .ite condition yes no => condition.valid scope && stmtValid scope yes && stmtValid scope no
    | .cases selector arms => selector.valid scope && armsValid scope arms
  def armsValid (scope : List (String × Nat)) : {k : Nat} → Arms k → Bool
    | _, .default stmt => stmtValid scope stmt
    | _, .arm labels stmt rest => labels.all (fun label => label.valid scope) && stmtValid scope stmt && armsValid scope rest
end

mutual
  /-- Backward substitution of a final observation through blocking statements. -/
  def lower (stmt : Stmt) {w : Nat} (result : FourState.Expr w) : FourState.Expr w :=
    match stmt with
    | .skip => result
    | .assign binding => substOne binding result
    | .seq first second => lower first (lower second result)
    | .ite condition yes no => .mux (ifTest condition) (lower yes result) (lower no result)
    | .cases selector arms => lowerArms selector arms result
  def lowerArms {k : Nat} (selector : FourState.Expr k) (arms : Arms k)
      {w : Nat} (result : FourState.Expr w) : FourState.Expr w :=
    match arms with
    | .default stmt => lower stmt result
    | .arm labels stmt rest => .mux (caseTest selector labels) (lower stmt result) (lowerArms selector rest result)
end

mutual
  theorem lower_valid (stmt : Stmt) (scope : List (String × Nat))
      (hv : stmtValid scope stmt = true) {w : Nat} (result : FourState.Expr w)
      (hr : result.valid scope = true) : (lower stmt result).valid scope = true := by
    have hw := valid_width result scope hr
    cases stmt with
    | skip => exact hr
    | assign binding =>
      apply substOne_valid binding scope _ result hr
      simpa [stmtValid, bindingValid] using hv
    | seq first second =>
      simp only [stmtValid, Bool.and_eq_true] at hv
      exact lower_valid first scope hv.1 _ (lower_valid second scope hv.2 result hr)
    | ite condition yes no =>
      simp only [stmtValid, Bool.and_eq_true] at hv
      simp [lower, FourState.Expr.valid, hw, ifTest_valid condition scope hv.1.1,
        lower_valid yes scope hv.1.2 result hr, lower_valid no scope hv.2 result hr]
    | cases selector arms =>
      simp only [stmtValid, Bool.and_eq_true] at hv
      exact lowerArms_valid selector arms scope hv.1 hv.2 result hr
  termination_by sizeOf stmt
  theorem lowerArms_valid {k : Nat} (selector : FourState.Expr k) (arms : Arms k)
      (scope : List (String × Nat)) (hs : selector.valid scope = true)
      (hv : armsValid scope arms = true) {w : Nat} (result : FourState.Expr w)
      (hr : result.valid scope = true) : (lowerArms selector arms result).valid scope = true := by
    have hw := valid_width result scope hr
    cases arms with
    | default stmt => exact lower_valid stmt scope hv result hr
    | arm labels stmt rest =>
      simp only [armsValid, Bool.and_eq_true] at hv
      simp [lowerArms, FourState.Expr.valid, hw,
        caseTest_valid selector labels scope hs (fun l h => List.all_eq_true.mp hv.1.1 l h),
        lower_valid stmt scope hv.1.2 result hr, lowerArms_valid selector rest scope hs hv.2 result hr]
  termination_by sizeOf arms
end

mutual
  /-- The lowered expression denotes the exact observation after executing the
  source statement, for every four-state environment and every result width. -/
  theorem lower_correct (stmt : Stmt) (scope : List (String × Nat))
      (hv : stmtValid scope stmt = true) {w : Nat} (result : FourState.Expr w)
      (hr : result.valid scope = true) (env : FourState.Env) :
      FourState.eval (lower stmt result) env = FourState.eval result (execute stmt env) := by
    cases stmt with
    | skip => rfl
    | assign binding =>
      apply substOne_correct binding scope _ result env hr
      simpa [stmtValid, bindingValid] using hv
    | seq first second =>
      simp only [stmtValid, Bool.and_eq_true] at hv
      change FourState.eval (lower first (lower second result)) env = _
      rw [lower_correct first scope hv.1 _ (lower_valid second scope hv.2 result hr),
        lower_correct second scope hv.2 result hr]
      rfl
    | ite condition yes no =>
      simp only [stmtValid, Bool.and_eq_true] at hv
      change FourState.eval (.mux (ifTest condition) (lower yes result) (lower no result)) env = _
      rw [eval_boolean_mux _ _ _ env _ (ifTest_correct condition env)]
      simp only [execute]
      split <;> first
        | exact lower_correct yes scope hv.1.2 result hr env
        | exact lower_correct no scope hv.2 result hr env
    | cases selector arms =>
      simp only [stmtValid, Bool.and_eq_true] at hv
      exact lowerArms_correct selector arms scope hv.1 hv.2 result hr env
  termination_by sizeOf stmt
  theorem lowerArms_correct {k : Nat} (selector : FourState.Expr k) (arms : Arms k)
      (scope : List (String × Nat)) (hs : selector.valid scope = true)
      (hv : armsValid scope arms = true) {w : Nat} (result : FourState.Expr w)
      (hr : result.valid scope = true) (env : FourState.Env) :
      FourState.eval (lowerArms selector arms result) env = FourState.eval result (executeArms selector arms env) := by
    cases arms with
    | default stmt => exact lower_correct stmt scope hv result hr env
    | arm labels stmt rest =>
      simp only [armsValid, Bool.and_eq_true] at hv
      change FourState.eval (.mux (caseTest selector labels) (lower stmt result) (lowerArms selector rest result)) env = _
      rw [eval_boolean_mux _ _ _ env _ (caseTest_correct selector labels env)]
      simp only [executeArms]
      split <;> first
        | exact lower_correct stmt scope hv.1.2 result hr env
        | exact lowerArms_correct selector rest scope hs hv.2 result hr env
  termination_by sizeOf arms
end

end LeanRTL.FourState.Source
