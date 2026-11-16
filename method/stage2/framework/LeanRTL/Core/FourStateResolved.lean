import LeanRTL.Core.FourStateControl
import LeanRTL.Core.FourStateVerilog

namespace LeanRTL.FourState.Resolved

theorem bit_beq (a b : Bit) : (a == b) = decide (a = b) := by
  cases a <;> cases b <;> rfl

theorem resolve_associative (a b c : Bit) :
    Bit.resolve (Bit.resolve a b) c = Bit.resolve a (Bit.resolve b c) := by
  cases a <;> cases b <;> cases c <;> rfl

theorem resolve_idempotent (a : Bit) : Bit.resolve a a = a := by
  cases a <;> rfl

/-- Ordinary equal-strength wire resolution, pointwise over a word. -/
def resolveValue {w : Nat} (a b : Value w) : Value w :=
  ⟨fun i => Bit.resolve (a i) (b i)⟩

/-- Resolution lowered into already certified four-state expression operators. -/
def resolveBitExpr (a b : Expr 1) : Expr 1 :=
  .mux (.caseEq a (.fill .z)) b
    (.mux (.caseEq b (.fill .z)) a (.mux (.caseEq a b) a (.fill .x)))

def resolvePrefix {w : Nat} (a b : Expr w) : (n : Nat) → Expr (n+1)
  | 0 => resolveBitExpr (.extract (w-1) a) (.extract (w-1) b)
  | n+1 => .concat (resolvePrefix a b n) (resolveBitExpr (.extract (w-(n+2)) a) (.extract (w-(n+2)) b))

def resolveExpr : {w : Nat} → Expr w → Expr w → Expr w
  | 0, _, _ => .const 0
  | n+1, a, b => resolvePrefix a b n

theorem resolve_value_z (a : Value w) : resolveValue (fill .z) a = a := by
  apply Encoding.value_ext
  intro i
  exact resolve_z_left (a i)

theorem resolve_bit_correct (a b : Expr 1) (env : Env) :
    eval (resolveBitExpr a b) env = resolveValue (eval a env) (eval b env) := by
  apply Encoding.value_ext
  intro i
  have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
  subst i
  cases ha : (eval a env).bit 0 <;> cases hb : (eval b env).bit 0 <;>
    simp [resolveBitExpr, eval, getBit, fill, ofBitVec, resolveValue, mux, ha, hb, Bit.resolve, List.finRange_succ, bit_beq]

theorem resolve_prefix_bit {w : Nat} (a b : Expr w) (env : Env) (n : Nat)
    (hn : n+1 ≤ w) (i : Fin (n+1)) :
    eval (resolvePrefix a b n) env i =
      Bit.resolve (getBit (eval a env) (w-(n+1)+i.val)) (getBit (eval b env) (w-(n+1)+i.val)) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst i
    simp [resolvePrefix, resolve_bit_correct, resolveValue, eval, fill]
  | succ n ih =>
    simp only [resolvePrefix, eval]
    split
    · rename_i h
      have he : i.val = 0 := by omega
      simp [getBit, he, resolve_bit_correct, resolveValue, eval, fill]
    · rename_i h
      have hi : i.val-1 < n+1 := by omega
      have hj : w-(n+1)+(i.val-1) = w-(n+1+1)+i.val := by omega
      simpa [getBit, hi, hj] using ih (by omega) ⟨i.val-1,hi⟩

theorem resolve_expr_correct {w : Nat} (a b : Expr w) (env : Env) :
    eval (resolveExpr a b) env = resolveValue (eval a env) (eval b env) := by
  apply Encoding.value_ext
  intro i
  cases w with
  | zero => exact Fin.elim0 i
  | succ n =>
    simpa [resolveExpr, resolveValue, getBit, i.isLt] using resolve_prefix_bit a b env n (by omega) i

theorem resolve_bit_valid (scope : List (String × Nat)) (a b : Expr 1)
    (ha : a.valid scope = true) (hb : b.valid scope = true) :
    (resolveBitExpr a b).valid scope = true := by
  simp [resolveBitExpr, Expr.valid, ha, hb]

theorem resolve_prefix_valid (scope : List (String × Nat)) {w : Nat} (a b : Expr w)
    (ha : a.valid scope = true) (hb : b.valid scope = true) (n : Nat) (hn : n+1 ≤ w) :
    (resolvePrefix a b n).valid scope = true := by
  induction n with
  | zero =>
    apply resolve_bit_valid <;> simp [Expr.valid, ha, hb, show w-1 < w by omega]
  | succ n ih =>
    have ha' : (Expr.extract (w-(n+2)) a).valid scope = true := by simp [Expr.valid, ha, show w-(n+2) < w by omega]
    have hb' : (Expr.extract (w-(n+2)) b).valid scope = true := by simp [Expr.valid, hb, show w-(n+2) < w by omega]
    have hr := resolve_bit_valid scope _ _ ha' hb'
    change (n+1+1 > 0 && ((resolvePrefix a b n).valid scope && _)) = true
    simp [hr, ih (by omega)]

theorem resolve_expr_valid (scope : List (String × Nat)) {w : Nat} (a b : Expr w)
    (ha : a.valid scope = true) (hb : b.valid scope = true) :
    (resolveExpr a b).valid scope = true := by
  cases w with
  | zero => have h := ha; unfold Expr.valid at h; simp at h
  | succ n => exact resolve_prefix_valid scope a b ha hb n (by omega)

end LeanRTL.FourState.Resolved
