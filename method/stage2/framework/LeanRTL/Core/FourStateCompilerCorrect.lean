import LeanRTL.Core.FourStatePmuxCorrect
import LeanRTL.Core.FourStateShiftCorrect

namespace LeanRTL.FourState.Encoding

theorem value_ext {w : Nat} {a b : Value w} (h : ∀ i, a i = b i) : a = b := by
  cases a with | mk a =>
    cases b with | mk b =>
      exact congrArg Value.mk (funext h)

theorem valid_width {w : Nat} (a : FourState.Expr w) (scope : List (String × Nat))
    (h : a.valid scope = true) : 0 < w := by
  cases a <;> simp_all [FourState.Expr.valid]

/-- Every well-formed four-state expression has exactly the same value as its
actual two-plane encoding, at every width and for every encoded environment.
Validity supplies nonzero widths and in-range indices, not input assumptions. -/
theorem compile_correct {w : Nat} (expr : FourState.Expr w)
    (scope : List (String × Nat)) (env : LeanRTL.Env) :
    expr.valid scope = true →
    den (compile expr) env = FourState.eval expr (decodedEnv env) := by
  induction expr with
  | const v => intro _; exact const_step v env
  | fill b => intro _; exact fill_step b env
  | var n w =>
    intro _
    apply value_ext
    exact var_step n w env
  | not a ih =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [not_step, ih hv.2]
    rfl
  | and a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [and_step, ia hv.2.1, ib hv.2.2]
    rfl
  | or a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [or_step, ia hv.2.1, ib hv.2.2]
    rfl
  | xor a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [xor_step, ia hv.2.1, ib hv.2.2]
    rfl
  | add a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [add_step, ia hv.2.1, ib hv.2.2]
    rfl
  | sub a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [sub_step, ia hv.2.1, ib hv.2.2]
    rfl
  | mul a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [mul_step, ia hv.2.1, ib hv.2.2]
    rfl
  | udiv a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [udiv_step, ia hv.2.1, ib hv.2.2]
    rfl
  | shl a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [shl_step, ia hv.2.1, ib hv.2.2]
    simp only [FourState.eval]
    split <;> rfl
  | shr a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [shr_step, ia hv.2.1, ib hv.2.2]
    simp only [FourState.eval]
    split <;> rfl
  | sshr a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [sshr_step, ia hv.2.1, ib hv.2.2]
    simp only [FourState.eval]
    split <;> rfl
  | eq a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [eq_step, ia hv.2.1, ib hv.2.2]
    rfl
  | caseEq a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [caseEq_step, ia hv.2.1, ib hv.2.2]
    rfl
  | ult a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [ult_step, ia hv.2.1, ib hv.2.2]
    rfl
  | slt a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [slt_step, ia hv.2.1, ib hv.2.2]
    rfl
  | concat a b ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [concat_step, ia hv.2.1, ib hv.2.2]
    rfl
  | mux s a b is ia ib =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [mux_step, is hv.2.1.1, ia hv.2.1.2, ib hv.2.2]
    rfl
  | pmux a b s ia ib is =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    rw [pmux_step, ia hv.2.1.1, ib hv.2.1.2, is hv.2.2]
    rfl
  | zext k a ih =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [zext_step, ih hv.2]
    rfl
  | sext k a ih =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [sext_step (valid_width a scope hv.2), ih hv.2]
    rfl
  | extract index a ih =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [extract_step index a hv.2.2, ih hv.2.1]
    rfl
  | slice lo len a ih =>
    intro hv
    simp only [FourState.Expr.valid, Bool.and_eq_true, decide_eq_true_eq] at hv
    apply value_ext
    intro i
    rw [slice_step lo len a hv.2.2, ih hv.2.1]
    rfl

end LeanRTL.FourState.Encoding
