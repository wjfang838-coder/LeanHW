import MemPhysical
open LeanRTL MemCPUShallow
open CaseCPU.Bridge (RF offset readRF writeRF resetRF)
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
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


theorem circuit_mask (b : Env) : V_w132 b =
    (0xffffffff#1024) <<< offset ((b.lookup "r24" 174 >>> 99).setWidth 5) := by
  unfold V_w132 V_w38
  exact signed_shift _ _

theorem circuit_insert (b : Env) : V_w133 b =
    ((b.lookup "r24" 174 >>> 67).setWidth 32).setWidth 1024 <<<
      offset ((b.lookup "r24" 174 >>> 99).setWidth 5) := by
  unfold V_w133 V_w38
  exact signed_shift _ _

theorem circuit_write (b : Env) : V_w360 b =
    writeRF (b.lookup "r12" 1024) ((b.lookup "r24" 174 >>> 99).setWidth 5)
      ((b.lookup "r24" 174 >>> 67).setWidth 32) := by
  simp only [V_w360,V_w33,V_w336,V_w310,V_w263,circuit_mask,circuit_insert,writeRF]
  split <;> simp_all

theorem circuit_reset (seed : RF) : ((seed >>> 32).setWidth 992 ++ (0#32)) = resetRF seed := by
  simp only [RF,resetRF]
  bv_decide

#print axioms circuit_write
end CaseCPUMem.Source
