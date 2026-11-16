import ISA
import Std.Tactic.BVDecide
import Init.Data.BitVec.Bitblast

namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

abbrev RF := BitVec 1024
def offset (r : CaseCPU.Reg) : Nat := (r ++ (0#5)).toNat
def readRF (rf : RF) (r : CaseCPU.Reg) : Word :=
  if r = 0 then 0 else (rf >>> offset r).setWidth 32
def writeRF (rf : RF) (r : CaseCPU.Reg) (v : Word) : RF :=
  if r = 0 then rf else
  (rf &&& ~~~((0xffffffff#1024) <<< offset r)) ||| (v.setWidth 1024 <<< offset r)
def resetRF (seed : RF) : RF := seed &&& ~~~(0xffffffff#1024)

theorem read_writeRF (rf : RF) (r q : CaseCPU.Reg) (v : Word) :
    readRF (writeRF rf r v) q =
      if q = 0 then 0 else if q = r then v else readRF rf q := by
  by_cases hq : q = 0
  · simp [readRF, hq]
  by_cases hr : r = 0
  · subst r; simp only [writeRF, ↓reduceIte, hq, ↓reduceIte]
  simp only [readRF, hq, ↓reduceIte, writeRF, hr]
  have maskbit (k : Nat) : (0xffffffff#1024).getLsbD k = decide (k<32) := by
    change ((BitVec.allOnes 32).setWidth 1024).getLsbD k = _
    simp only [BitVec.getLsbD_setWidth, BitVec.getLsbD_allOnes]
    by_cases h : k<32 <;> simp_all <;> omega
  have off (z : CaseCPU.Reg) : offset z = 32*z.toNat := by
    unfold offset
    rw [BitVec.toNat_append]
    simp only [BitVec.toNat_ofNat, Nat.zero_mod, Nat.or_zero, Nat.shiftLeft_eq]
    omega
  apply BitVec.eq_of_getLsbD_eq
  intro j hj
  have hqbound := q.isLt
  have hrbound := r.isLt
  by_cases hqr : q = r
  · subst q
    simp only [ ↓reduceIte, off, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      BitVec.getLsbD_shiftLeft, maskbit, BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and,
      show 32*r.toNat+j<1024 by omega, show ¬32*r.toNat+j<32*r.toNat by omega,
      show 32*r.toNat+j-32*r.toNat=j by omega, show j<1024 by omega, hj, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false, Bool.false_or, Bool.or_false, Bool.or_true, Bool.true_or]
  · have hne : q.toNat ≠ r.toNat := fun ht => hqr (BitVec.eq_of_toNat_eq ht)
    by_cases hlt : q.toNat < r.toNat
    · simp only [hqr, ↓reduceIte, off, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_shiftLeft, maskbit, BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and,
        show 32*q.toNat+j<32*r.toNat by omega,
        show 32*q.toNat+j<1024 by omega, hj, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false, Bool.false_or, Bool.or_false, Bool.or_true, Bool.true_or]
    · have hd : 32 ≤ 32*q.toNat+j-32*r.toNat := by omega
      have hv : v.getLsbD (32*q.toNat+j-32*r.toNat) = false := BitVec.getLsbD_of_ge _ _ hd
      simp only [hqr, ↓reduceIte, off, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_shiftLeft, maskbit, BitVec.getLsbD_not, BitVec.getLsbD_or, BitVec.getLsbD_and,
        show 32*q.toNat+j<1024 by omega, show ¬32*q.toNat+j<32*r.toNat by omega,
        show ¬32*q.toNat+j-32*r.toNat<32 by omega, hv, hj, decide_true, decide_false, Bool.true_and, Bool.false_and, Bool.and_true, Bool.and_false, Bool.not_true, Bool.not_false, Bool.false_or, Bool.or_false, Bool.or_true, Bool.true_or]

theorem read_resetRF (rf : RF) (r : CaseCPU.Reg) :
    readRF (resetRF rf) r = readRF rf r := by
  unfold readRF resetRF offset
  bv_decide

theorem high_ofInt (n : Int) :
    ((BitVec.ofInt 64 n >>> 32).setWidth 32) = BitVec.ofInt 32 (n / 2^32) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, BitVec.toNat_ofInt,
    Nat.shiftRight_eq_div_pow]
  have h1 := Int.emod_nonneg n (by decide : (2^64 : Int) ≠ 0)
  have h2 := Int.emod_nonneg (n / 2^32) (by decide : (2^32 : Int) ≠ 0)
  omega

theorem sext_ofInt (a : Word) : a.signExtend 64 = BitVec.ofInt 64 a.toInt := by
  apply BitVec.eq_of_toInt_eq
  rw [BitVec.toInt_signExtend_of_le (by decide), BitVec.toInt_ofInt_eq_self (by decide)]
  · have h := BitVec.le_toInt a; omega
  · have h := BitVec.toInt_lt (x := a); omega

theorem high_ss (a b : Word) :
    ((a.signExtend 64 * b.signExtend 64) >>> 32).setWidth 32 =
      calculate .mulh a b 0 0 := by
  rw [sext_ofInt, sext_ofInt, ← BitVec.ofInt_mul, high_ofInt]
  rfl

theorem zext_ofInt (a : Word) : a.setWidth 64 = BitVec.ofInt 64 (Int.ofNat a.toNat) := by
  simp

theorem high_su (a b : Word) :
    ((a.signExtend 64 * b.setWidth 64) >>> 32).setWidth 32 =
      calculate .mulhsu a b 0 0 := by
  rw [sext_ofInt, zext_ofInt, ← BitVec.ofInt_mul, high_ofInt]
  rfl

theorem high_uu (a b : Word) :
    ((a.setWidth 64 * b.setWidth 64) >>> 32).setWidth 32 =
      calculate .mulhu a b 0 0 := by
  rw [zext_ofInt, zext_ofInt, ← BitVec.ofInt_mul, high_ofInt]
  simp only [calculate]
  change BitVec.ofInt 32 (Int.ofNat (a.toNat*b.toNat / 2^32)) = _
  rfl

theorem signed_div_eq (a b : Word) :
    signedDiv a b = if b = 0 then -1 else a.sdiv b := by
  unfold signedDiv
  split <;> try rfl
  congr 1
  apply BitVec.eq_of_toInt_eq
  simp [BitVec.toInt_sdiv]

theorem signed_rem_eq (a b : Word) : signedRem a b = a.srem b := by
  unfold signedRem
  split
  · rename_i h
    subst b
    simp
  · apply BitVec.eq_of_toInt_eq
    rw [BitVec.toInt_ofInt, BitVec.toInt_srem]
    rw [← BitVec.toInt_srem a b, BitVec.toInt_bmod_cancel]

#print axioms read_writeRF
#print axioms read_resetRF
#print axioms high_ss
#print axioms high_su
#print axioms high_uu
#print axioms signed_div_eq
#print axioms signed_rem_eq
end CaseCPU.Bridge
