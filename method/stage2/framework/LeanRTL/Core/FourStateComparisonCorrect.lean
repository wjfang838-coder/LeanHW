import LeanRTL.Core.FourStateArithmeticCorrect

namespace LeanRTL.FourState.Encoding

theorem any_bits {w : Nat} (a : BitVec w) :
    (List.finRange w).any (fun i => a.getLsbD i.val) = decide (a ≠ 0) := by
  have h := congrArg Bool.not (known_decodeVectors a (0 : BitVec w))
  simp only [known, decodeVectors, known_decodeBit, List.not_all_eq_any_not, Bool.not_not] at h
  simpa using h

private theorem mismatch_decoded (atg adt btg bdt : Bool) :
    ((decodeBit (atg, adt)).known && (decodeBit (btg, bdt)).known &&
      (decodeBit (atg, adt) != decodeBit (btg, bdt))) =
    (!(atg || btg) && Bool.xor adt bdt) := by
  cases atg <;> cases adt <;> cases btg <;> cases bdt <;> rfl

theorem mismatch_vectors {w : Nat} (t d u v : BitVec w) :
    (List.finRange w).any (fun i =>
      (decodeVectors t d i).known && (decodeVectors u v i).known &&
      decodeVectors t d i != decodeVectors u v i) =
    decide ((~~~(t ||| u) &&& (d ^^^ v)) ≠ 0) := by
  have point (i : Fin w) :
      ((decodeVectors t d i).known && (decodeVectors u v i).known &&
        decodeVectors t d i != decodeVectors u v i) =
      (~~~(t ||| u) &&& (d ^^^ v)).getLsbD i.val := by
    simp only [decodeVectors, mismatch_decoded, BitVec.getLsbD_and, BitVec.getLsbD_not,
      BitVec.getLsbD_or, BitVec.getLsbD_xor, i.isLt, decide_true, Bool.true_and]
  rw [show (fun i : Fin w => (decodeVectors t d i).known && (decodeVectors u v i).known &&
        decodeVectors t d i != decodeVectors u v i) =
      (fun i => (~~~(t ||| u) &&& (d ^^^ v)).getLsbD i.val) from funext point]
  exact any_bits _

theorem eq_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) :
    den (compile (.eq a b)) env = fill (logicalEq (den (compile a) env) (den (compile b) env)) := by
  let ta := LeanRTL.eval (compile a).tag env
  let da := LeanRTL.eval (compile a).data env
  let tb := LeanRTL.eval (compile b).tag env
  let db := LeanRTL.eval (compile b).data env
  have hm := mismatch_vectors ta da tb db
  have hk : (known (den (compile a) env) && known (den (compile b) env)) = decide (ta ||| tb = 0) := by
    simp [den_known, ta, tb, BitVec.or_eq_zero_iff]
  change den (compile (.eq a b)) env = fill (
    if (List.finRange w).any (fun i => (decodeVectors ta da i).known && (decodeVectors tb db i).known &&
        decodeVectors ta da i != decodeVectors tb db i) then .zero
    else if known (den (compile a) env) && known (den (compile b) env) then .one else .x)
  rw [hm, hk]
  by_cases hu : ta ||| tb = 0 <;> by_cases hm0 : (~~~(ta ||| tb) &&& (da ^^^ db)) = 0
  all_goals
    apply congrArg Value.mk
    funext i
    have hi : i.val = 0 := by omega
    simp_all [den, compile, anyBit, zero, LeanRTL.eval, ta, tb, da, db, fill, decodeBit, hi]
  all_goals
    by_cases hz : LeanRTL.eval (compile a).tag env = 0 <;> simp_all

private theorem beq_bit_iff (a b : Bit) : (a == b) = true ↔ a = b := by
  cases a <;> cases b <;> decide

theorem all_beq_iff {w : Nat} (a b : Value w) :
    (List.finRange w).all (fun i => a i == b i) = true ↔ a = b := by
  constructor
  · intro h
    cases a with | mk av =>
      cases b with | mk bv =>
        apply congrArg Value.mk
        funext i
        exact (beq_bit_iff _ _).mp (List.all_eq_true.mp h i (List.mem_finRange i))
  · rintro rfl
    apply List.all_eq_true.mpr
    intro i _
    exact (beq_bit_iff _ _).mpr rfl

theorem caseEq_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) :
    den (compile (.caseEq a b)) env = fill (
      if (List.finRange w).all (fun i => den (compile a) env i == den (compile b) env i)
      then Bit.one else Bit.zero) := by
  have h := (all_beq_iff (den (compile a) env) (den (compile b) env)).trans
    (den_equal_iff (compile a) (compile b) env)
  by_cases ht : LeanRTL.eval (compile a).tag env = LeanRTL.eval (compile b).tag env <;>
    by_cases hd : LeanRTL.eval (compile a).data env = LeanRTL.eval (compile b).data env
  all_goals
    apply congrArg Value.mk
    funext i
    have hi : i.val = 0 := by omega
    simp_all [den, compile, zero, LeanRTL.eval, fill, decodeBit, hi]

end LeanRTL.FourState.Encoding
