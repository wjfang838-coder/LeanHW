import Circuit
import WordMath
open LeanRTL CPUShallow
namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem offset_sign (r : CaseCPU.Reg) :
    (-((r ++ (0#5)).setWidth 33)).getLsbD 32 = (r != 0) := by
  simp only [CaseCPU.Reg]
  bv_decide

theorem offset_cast (r : CaseCPU.Reg) : ((r ++ (0#5)).setWidth 33).toNat = offset r := by
  exact BitVec.toNat_setWidth_of_le (by decide)

theorem signed_shift (r : CaseCPU.Reg) (v : RF) :
    (if (if (-((r ++ (0#5)).setWidth 33)).getLsbD 32 then (1#1) else 0) = 1
      then v <<< (0#33 - (0#33 - (r ++ (0#5)).setWidth 33)).toNat
      else v >>> (0#33 - (r ++ (0#5)).setWidth 33).toNat) = v <<< offset r := by
  simp only [BitVec.zero_sub]
  rw [offset_sign]
  by_cases hr : r = 0
  · subst r; simp [offset]
  · simp only [hr, bne_self_eq_false, bne_iff_ne, ne_eq, not_false_eq_true, decide_true, ↓reduceIte, BitVec.neg_neg, offset_cast]
    rfl

theorem circuit_mask (b : Env) : V_w58 b =
    (0xffffffff#1024) <<< offset ((b.lookup "r14" 32 >>> 7).setWidth 5) := by
  unfold V_w58 V_w27
  exact signed_shift _ _

theorem circuit_insert (b : Env) : V_w59 b =
    (b.lookup "r17" 32).setWidth 1024 <<< offset ((b.lookup "r14" 32 >>> 7).setWidth 5) := by
  unfold V_w59 V_w27
  exact signed_shift _ _

theorem circuit_write (b : Env) : V_w123 b =
    writeRF (b.lookup "r3" 1024) ((b.lookup "r14" 32 >>> 7).setWidth 5) (b.lookup "r17" 32) := by
  simp only [V_w123,V_w25,V_w118,V_w106,V_w96,circuit_mask,circuit_insert,writeRF]
  split <;> simp_all

theorem circuit_reset (seed : RF) : ((seed >>> 32).setWidth 992 ++ (0#32)) = resetRF seed := by
  simp only [RF,resetRF]
  bv_decide

#print axioms circuit_write
#print axioms circuit_reset
end CaseCPU.Bridge
