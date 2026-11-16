import LeanRTL.Core.FourStateArithmeticCorrect

namespace LeanRTL.FourState.Encoding

def decodedEnv (env : LeanRTL.Env) : FourState.Env := fun n i =>
  decodeBit ((env ("t__" ++ n)).testBit i, (env ("d__" ++ n)).testBit i)

theorem const_step {w : Nat} (v : BitVec w) (env : LeanRTL.Env) :
    den (compile (.const v)) env = ofBitVec v :=
  decode_zero_tag v

theorem fill_step {w : Nat} (b : Bit) (env : LeanRTL.Env) :
    den (compile (.fill (w := w) b)) env = fill b := den_constant b env

theorem var_step (n : String) (w : Nat) (env : LeanRTL.Env) (i : Fin w) :
    den (compile (.var n w)) env i = decodedEnv env n i.val := by
  simp only [den, compile, LeanRTL.eval, LeanRTL.Env.lookup, decodedEnv, BitVec.getLsbD_ofNat,
    i.isLt, decide_true, Bool.true_and]

theorem concat_step {a b : Nat} (hi : FourState.Expr a) (lo : FourState.Expr b)
    (env : LeanRTL.Env) (i : Fin (a+b)) :
    den (compile (.concat hi lo)) env i =
      if i.val < b then getBit (den (compile lo) env) i.val
      else getBit (den (compile hi) env) (i.val-b) := by
  change decodeBit (((LeanRTL.eval (compile hi).tag env) ++ (LeanRTL.eval (compile lo).tag env)).getLsbD i.val,
    ((LeanRTL.eval (compile hi).data env) ++ (LeanRTL.eval (compile lo).data env)).getLsbD i.val) = _
  rw [BitVec.getLsbD_append, BitVec.getLsbD_append]
  by_cases h : i.val < b
  · simp [h, getBit, den]
  · have hival := i.isLt
    have hh : i.val-b < a := by omega
    simp [h, hh, getBit, den]

theorem zext_step {w : Nat} (k : Nat) (a : FourState.Expr w) (env : LeanRTL.Env) (i : Fin (w+k)) :
    den (compile (.zext k a)) env i =
      if i.val < w then getBit (den (compile a) env) i.val else .zero := by
  change decodeBit (((LeanRTL.eval (compile a).tag env).setWidth (w+k)).getLsbD i.val,
    ((LeanRTL.eval (compile a).data env).setWidth (w+k)).getLsbD i.val) = _
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth]
  by_cases h : i.val < w
  · simp [i.isLt, h, den, getBit]
  · have ht := BitVec.getLsbD_of_ge (LeanRTL.eval (compile a).tag env) i.val (by omega)
    have hd := BitVec.getLsbD_of_ge (LeanRTL.eval (compile a).data env) i.val (by omega)
    simp [i.isLt, h, ht, hd, decodeBit]

theorem sext_step {w : Nat} (hw : 0 < w) (k : Nat) (a : FourState.Expr w)
    (env : LeanRTL.Env) (i : Fin (w+k)) :
    den (compile (.sext k a)) env i =
      getBit (den (compile a) env) (min i.val (w-1)) := by
  have hm : w-1 < w := by omega
  change decodeBit (((LeanRTL.eval (compile a).tag env).signExtend (w+k)).getLsbD i.val,
    ((LeanRTL.eval (compile a).data env).signExtend (w+k)).getLsbD i.val) = _
  rw [BitVec.getLsbD_signExtend, BitVec.getLsbD_signExtend]
  by_cases h : i.val < w
  · have hmin : min i.val (w-1) = i.val := Nat.min_eq_left (by omega)
    simp [i.isLt, h, hmin, getBit, den]
  · have hmin : min i.val (w-1) = w-1 := Nat.min_eq_right (by omega)
    simp [i.isLt, h, hmin, getBit, hm, den, BitVec.msb_eq_getLsbD_last]

theorem slice_step {w : Nat} (lo len : Nat) (a : FourState.Expr w) (h : lo+len ≤ w)
    (env : LeanRTL.Env) (i : Fin len) :
    den (compile (.slice lo len a)) env i = getBit (den (compile a) env) (lo+i.val) := by
  have hival := i.isLt
  have hi : lo+i.val < w := by omega
  change decodeBit ((((LeanRTL.eval (compile a).tag env) >>> lo).setWidth len).getLsbD i.val,
    (((LeanRTL.eval (compile a).data env) >>> lo).setWidth len).getLsbD i.val) = _
  rw [BitVec.getLsbD_setWidth, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
    BitVec.getLsbD_ushiftRight]
  simp [i.isLt, hi, getBit, den]

theorem extract_step {w : Nat} (index : Nat) (a : FourState.Expr w) (h : index < w)
    (env : LeanRTL.Env) (i : Fin 1) :
    den (compile (.extract index a)) env i = getBit (den (compile a) env) index := by
  have hi : i.val = 0 := by omega
  simp only [den, compile, LeanRTL.eval]
  change decodeBit ((if (LeanRTL.eval (compile a).tag env).getLsbD index then (1 : BitVec 1) else 0).getLsbD i.val,
    (if (LeanRTL.eval (compile a).data env).getLsbD index then (1 : BitVec 1) else 0).getLsbD i.val) = _
  rw [hi]
  cases ht : (LeanRTL.eval (compile a).tag env).getLsbD index <;>
    cases hd : (LeanRTL.eval (compile a).data env).getLsbD index <;>
    simp_all [getBit, den, decodeBit]

end LeanRTL.FourState.Encoding
