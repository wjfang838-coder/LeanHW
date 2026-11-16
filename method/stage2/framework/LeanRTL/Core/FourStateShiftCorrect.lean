import LeanRTL.Core.FourStateArithmeticCorrect

namespace LeanRTL.FourState.Encoding

theorem shl_vectors {w : Nat} (t d : BitVec w) (n : Nat) (i : Fin w) :
    decodeVectors (t <<< n) (d <<< n) i =
      if i.val < n then .zero else getBit (decodeVectors t d) (i.val - n) := by
  have hi : i.val - n < w := by omega
  change decodeBit ((t <<< n).getLsbD i.val, (d <<< n).getLsbD i.val) = _
  rw [BitVec.getLsbD_shiftLeft, BitVec.getLsbD_shiftLeft]
  by_cases h : i.val < n
  · have hn : ¬ n ≤ i.val := by omega
    simp [decodeVectors, getBit, decodeBit, i.isLt, hi, h, hn]
  · have hn : n ≤ i.val := by omega
    simp [decodeVectors, getBit, decodeBit, i.isLt, hi, h, hn]
    rfl

theorem shr_vectors {w : Nat} (t d : BitVec w) (n : Nat) (i : Fin w) :
    decodeVectors (t >>> n) (d >>> n) i =
      if i.val + n < w then getBit (decodeVectors t d) (i.val + n) else .zero := by
  change decodeBit ((t >>> n).getLsbD i.val, (d >>> n).getLsbD i.val) = _
  rw [BitVec.getLsbD_ushiftRight, BitVec.getLsbD_ushiftRight, Nat.add_comm n i.val]
  by_cases h : i.val + n < w
  · simp [decodeVectors, getBit, h]
  · have hge : w ≤ i.val + n := by omega
    rw [BitVec.getLsbD_of_ge t _ hge, BitVec.getLsbD_of_ge d _ hge]
    simp [h, decodeBit]

theorem sshr_vectors {w : Nat} (t d : BitVec w) (n : Nat) (i : Fin w) :
    decodeVectors (t.sshiftRight n) (d.sshiftRight n) i =
      getBit (decodeVectors t d) (min (i.val + n) (w-1)) := by
  have hival := i.isLt
  have hw : w-1 < w := by omega
  have hi : ¬ w ≤ i.val := by omega
  change decodeBit ((t.sshiftRight n).getLsbD i.val, (d.sshiftRight n).getLsbD i.val) = _
  rw [BitVec.getLsbD_sshiftRight, BitVec.getLsbD_sshiftRight, Nat.add_comm n i.val]
  by_cases h : i.val + n < w
  · have hm : min (i.val+n) (w-1) = i.val+n := Nat.min_eq_left (by omega)
    simp [decodeVectors, getBit, hm, h, hi]
  · have hm : min (i.val+n) (w-1) = w-1 := Nat.min_eq_right (by omega)
    simp [decodeVectors, getBit, BitVec.msb_eq_getLsbD_last, hm, h, hi, hw]

theorem den_count {w : Nat} (a : Rails w) (env : LeanRTL.Env) (h : LeanRTL.eval a.tag env = 0) :
    toBitVec (den a env) = LeanRTL.eval a.data env := by
  rw [den_zero_tag a env h, toBitVec_ofBitVec]

theorem shl_step {w k : Nat} (a : FourState.Expr w) (b : FourState.Expr k)
    (env : LeanRTL.Env) (i : Fin w) :
    den (compile (.shl a b)) env i =
      if known (den (compile b) env) then
        if i.val < (toBitVec (den (compile b) env)).toNat then .zero
        else getBit (den (compile a) env) (i.val - (toBitVec (den (compile b) env)).toNat)
      else .x := by
  change den (choose (anyBit (compile b).tag) (constant .x)
    ⟨.shl (compile a).tag (compile b).data, .shl (compile a).data (compile b).data⟩) env i = _
  rw [den_choose, eval_anyBit]
  by_cases h : LeanRTL.eval (compile b).tag env = 0
  · simp_all [den_known]
    rw [den_count _ _ h]
    exact shl_vectors _ _ _ i
  · simp_all [den_known, den_constant, fill]

theorem shr_step {w k : Nat} (a : FourState.Expr w) (b : FourState.Expr k)
    (env : LeanRTL.Env) (i : Fin w) :
    den (compile (.shr a b)) env i =
      if known (den (compile b) env) then
        if i.val + (toBitVec (den (compile b) env)).toNat < w then
          getBit (den (compile a) env) (i.val + (toBitVec (den (compile b) env)).toNat)
        else .zero
      else .x := by
  change den (choose (anyBit (compile b).tag) (constant .x)
    ⟨.shr (compile a).tag (compile b).data, .shr (compile a).data (compile b).data⟩) env i = _
  rw [den_choose, eval_anyBit]
  by_cases h : LeanRTL.eval (compile b).tag env = 0
  · simp_all [den_known]
    rw [den_count _ _ h]
    exact shr_vectors _ _ _ i
  · simp_all [den_known, den_constant, fill]

theorem sshr_step {w k : Nat} (a : FourState.Expr w) (b : FourState.Expr k)
    (env : LeanRTL.Env) (i : Fin w) :
    den (compile (.sshr a b)) env i =
      if known (den (compile b) env) then
        getBit (den (compile a) env) (min (i.val + (toBitVec (den (compile b) env)).toNat) (w-1))
      else .x := by
  change den (choose (anyBit (compile b).tag) (constant .x)
    ⟨.sshr (compile a).tag (compile b).data, .sshr (compile a).data (compile b).data⟩) env i = _
  rw [den_choose, eval_anyBit]
  by_cases h : LeanRTL.eval (compile b).tag env = 0
  · simp_all [den_known]
    rw [den_count _ _ h]
    exact sshr_vectors _ _ _ i
  · simp_all [den_known, den_constant, fill]

end LeanRTL.FourState.Encoding
