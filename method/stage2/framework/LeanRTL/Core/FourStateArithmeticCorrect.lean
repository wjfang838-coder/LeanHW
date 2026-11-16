import LeanRTL.Core.FourStateEncodingCorrect

namespace LeanRTL.FourState.Encoding

theorem toBitVec_get {w : Nat} (a : Value w) (i : Fin w) :
    (toBitVec a).getLsbD i.val = (a i == .one) := by
  simp only [toBitVec, BitVec.getLsbD_setWidth, BitVec.getLsbD_ofBoolListLE]
  simp [i.isLt, List.getD]

theorem toBitVec_ofBitVec {w : Nat} (a : BitVec w) : toBitVec (ofBitVec a) = a := by
  apply BitVec.eq_of_getLsbD_eq_iff.mpr
  intro i hi
  rw [toBitVec_get (ofBitVec a) ⟨i, hi⟩]
  change ((if a.getLsbD i then Bit.one else Bit.zero) == Bit.one) = a.getLsbD i
  cases a.getLsbD i <;> rfl

theorem known_decodeBit (t d : Bool) : (decodeBit (t, d)).known = !t := by
  cases t <;> cases d <;> rfl

theorem known_decodeVectors {w : Nat} (t d : BitVec w) :
    known (decodeVectors t d) = decide (t = 0) := by
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    apply BitVec.eq_of_getLsbD_eq_iff.mpr
    intro i hi
    have hk := List.all_eq_true.mp h ⟨i, hi⟩ (List.mem_finRange ⟨i, hi⟩)
    change (decodeBit (t.getLsbD i, d.getLsbD i)).known = true at hk
    rw [known_decodeBit] at hk
    simpa using hk
  · intro h
    subst t
    apply List.all_eq_true.mpr
    intro i _
    change (decodeBit ((0 : BitVec w).getLsbD i.val, d.getLsbD i.val)).known = true
    rw [known_decodeBit]
    simp

theorem decode_zero_tag {w : Nat} (d : BitVec w) : decodeVectors 0 d = ofBitVec d := by
  apply congrArg Value.mk
  funext i
  simp [decodeVectors, ofBitVec, decodeBit]

theorem den_known {w : Nat} (a : Rails w) (env : LeanRTL.Env) :
    known (den a env) = decide (LeanRTL.eval a.tag env = 0) :=
  known_decodeVectors _ _

theorem den_zero_tag {w : Nat} (a : Rails w) (env : LeanRTL.Env)
    (h : LeanRTL.eval a.tag env = 0) : den a env = ofBitVec (LeanRTL.eval a.data env) := by
  change decodeVectors (LeanRTL.eval a.tag env) (LeanRTL.eval a.data env) = _
  rw [h, decode_zero_tag]

theorem den_choose {w : Nat} (s : LeanRTL.Expr 1) (a b : Rails w) (env : LeanRTL.Env) :
    den (choose s a b) env = if LeanRTL.eval s env = 1 then den a env else den b env := by
  by_cases h : LeanRTL.eval s env = 1 <;> simp_all [den, choose, LeanRTL.eval]

theorem eval_anyBit {w : Nat} (a : LeanRTL.Expr w) (env : LeanRTL.Env) :
    LeanRTL.eval (anyBit a) env = if LeanRTL.eval a env = 0 then 0 else 1 := by
  by_cases h : LeanRTL.eval a env = 0 <;> simp_all [anyBit, zero, LeanRTL.eval]

theorem den_constant {w : Nat} (b : Bit) (env : LeanRTL.Env) : den (constant (w := w) b) env = fill b := by
  cases b <;> apply congrArg Value.mk <;> funext i <;>
    simp [den, constant, encodeBit, zero, ones, LeanRTL.eval, fill, decodeBit, BitVec.neg_one_eq_allOnes, i.isLt]

theorem strictBinary_step {w : Nat}
    (op : LeanRTL.Expr w → LeanRTL.Expr w → LeanRTL.Expr w)
    (valueOp : BitVec w → BitVec w → BitVec w)
    (env : LeanRTL.Env)
    (hop : ∀ x y, LeanRTL.eval (op x y) env = valueOp (LeanRTL.eval x env) (LeanRTL.eval y env))
    (a b : Rails w) :
    den (strictBinary op a b) env = binary valueOp (den a env) (den b env) := by
  rw [strictBinary, den_choose, eval_anyBit]
  by_cases ha : LeanRTL.eval a.tag env = 0 <;> by_cases hb : LeanRTL.eval b.tag env = 0
  all_goals
    simp_all [binary, den_known, den_constant, LeanRTL.eval, BitVec.or_eq_zero_iff]
  rw [den_zero_tag a env ha, den_zero_tag b env hb, toBitVec_ofBitVec, toBitVec_ofBitVec]
  change decodeVectors 0 (LeanRTL.eval (op a.data b.data) env) = _
  rw [decode_zero_tag, hop]

theorem add_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) :
    den (compile (.add a b)) env = binary (· + ·) (den (compile a) env) (den (compile b) env) :=
  strictBinary_step .add (· + ·) env (by intros; rfl) _ _

theorem sub_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) :
    den (compile (.sub a b)) env = binary (· - ·) (den (compile a) env) (den (compile b) env) :=
  strictBinary_step .sub (· - ·) env (by intros; rfl) _ _

theorem mul_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) :
    den (compile (.mul a b)) env = binary (· * ·) (den (compile a) env) (den (compile b) env) :=
  strictBinary_step .mul (· * ·) env (by intros; rfl) _ _

theorem udiv_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) :
    den (compile (.udiv a b)) env =
      FourState.unsignedDiv (den (compile a) env) (den (compile b) env) :=
  strictBinary_step .udiv (· / ·) env (by intros; rfl) _ _

theorem ofBitVec_bool (b : Bool) :
    ofBitVec (if b then (1 : BitVec 1) else 0) = fill (if b then Bit.one else Bit.zero) := by
  apply congrArg Value.mk
  funext i
  have hi : i.val = 0 := by omega
  cases b <;> simp [ofBitVec, fill, hi]

theorem compare_step {w : Nat}
    (op : LeanRTL.Expr w → LeanRTL.Expr w → LeanRTL.Expr 1)
    (valueOp : BitVec w → BitVec w → Bool)
    (env : LeanRTL.Env)
    (hop : ∀ x y, LeanRTL.eval (op x y) env =
      if valueOp (LeanRTL.eval x env) (LeanRTL.eval y env) then 1 else 0)
    (a b : Rails w) :
    den (compare op a b) env = fill (relation valueOp (den a env) (den b env)) := by
  rw [compare, den_choose, eval_anyBit]
  by_cases ha : LeanRTL.eval a.tag env = 0 <;> by_cases hb : LeanRTL.eval b.tag env = 0
  all_goals
    simp_all [relation, den_known, den_constant, LeanRTL.eval, BitVec.or_eq_zero_iff]
  rw [den_zero_tag a env ha, den_zero_tag b env hb, toBitVec_ofBitVec, toBitVec_ofBitVec]
  change decodeVectors 0 (LeanRTL.eval (op a.data b.data) env) = _
  rw [decode_zero_tag, hop]
  simpa using ofBitVec_bool (valueOp (LeanRTL.eval a.data env) (LeanRTL.eval b.data env))

theorem ult_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) :
    den (compile (.ult a b)) env =
      fill (relation (fun x y => x < y) (den (compile a) env) (den (compile b) env)) :=
  compare_step .ult (fun x y => x < y) env (by intros; simp [LeanRTL.eval]) _ _

theorem slt_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) :
    den (compile (.slt a b)) env =
      fill (relation (fun x y => x.toInt < y.toInt) (den (compile a) env) (den (compile b) env)) :=
  compare_step .slt (fun x y => x.toInt < y.toInt) env (by intros; simp [LeanRTL.eval]) _ _

end LeanRTL.FourState.Encoding
