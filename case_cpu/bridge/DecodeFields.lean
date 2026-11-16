import DecoderCircuit
import RawCPU
import ALUCircuit
open LeanRTL CPUShallow
namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem instruction_some (w : Word) (h : (CaseCPU.decode w).isSome = true) :
    CaseCPU.decode w = some (instruction w) := by
  cases hd : CaseCPU.decode w <;> simp_all [instruction]

theorem instruction_fields (w : Word) (h : (CaseCPU.decode w).isSome = true) :
    (instruction w).rd = (w >>> 7).setWidth 5 ∧
    (instruction w).rs1 = (w >>> 15).setWidth 5 ∧
    (instruction w).rs2 = (w >>> 20).setWidth 5 ∧
    (instruction w).imm = decodeImm w := by
  have hh := decoded_fields w (instruction w) (instruction_some w h)
  have slice (n : Nat) : (w >>> n).setWidth 5 = BitVec.ofNat 5 (w.toNat/2^n) := by
    apply BitVec.eq_of_toNat_eq
    simp [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  simpa only [slice] using hh

theorem instruction_code (w : Word) (h : (CaseCPU.decode w).isSome = true) :
    codeBits w = opCode (instruction w).op := by
  rw [bits_code,decodeCode,instruction_some w h]

def rtlImmediate (w : Word) : Word :=
  if w.setWidth 7 = 55 ∨ w.setWidth 7 = 23 then
    ((w >>> 12).setWidth 20) ++ (0#12)
  else ((w >>> 20).setWidth 12).signExtend 32

theorem circuit_immediate (b : Env) : immediateBits b = rtlImmediate (b.lookup "r11" 32) := by
  simp only [immediateBits,rtlImmediate,V_w105,V_w87,V_w55,V_w54,Word]
  bv_decide

theorem upperImmediate (w : Word) :
    BitVec.ofNat 32 (w.toNat/4096*4096) = ((w >>> 12).setWidth 20 ++ (0#12)) := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,BitVec.toNat_append,BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow,Nat.zero_mod,Nat.or_zero,Nat.shiftLeft_eq]
  have hb := w.isLt
  omega

theorem immediate_I (w : Word) (h : w.setWidth 7 = 19) : rtlImmediate w = decodeImm w := by
  have hn : w.toNat % 128 = 19 := congrArg BitVec.toNat h
  simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat] at hn
  simp [rtlImmediate,decodeImm,hn,BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,
    Nat.shiftRight_eq_div_pow]
  have h55 : w.setWidth 7 ≠ 55 := by rw [h]; decide
  have h23 : w.setWidth 7 ≠ 23 := by rw [h]; decide
  simp_all
  congr 1
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

theorem immediate_U (w : Word) (h : w.setWidth 7 = 55 ∨ w.setWidth 7 = 23) :
    rtlImmediate w = decodeImm w := by
  have hn : w.toNat % 128 = 55 ∨ w.toNat % 128 = 23 := by
    rcases h with h | h <;> have hh := congrArg BitVec.toNat h <;>
      simp only [BitVec.toNat_setWidth,BitVec.toNat_ofNat] at hh <;> simp [hh]
  rw [rtlImmediate, if_pos h]
  rcases hn with hn | hn <;> simp [decodeImm,hn,upperImmediate]

theorem code_I (w : Word) (c : BitVec 6) (h : codeBits w = c)
    (hc : 10 ≤ c ∧ c ≤ 18) : w.setWidth 7 = 19 := by
  simp only [codeBits,codeFields,Word] at *
  bv_decide

theorem code_U (w : Word) (c : BitVec 6) (h : codeBits w = c)
    (hc : c = 19 ∨ c = 20) : w.setWidth 7 = 55 ∨ w.setWidth 7 = 23 := by
  simp only [codeBits,codeFields,Word] at *
  bv_decide

theorem calculate_immediate (w : Word) (a b pc : Word)
    (h : (CaseCPU.decode w).isSome = true) :
    calculate (instruction w).op a b (rtlImmediate w) pc =
      calculate (instruction w).op a b (instruction w).imm pc := by
  rw [(instruction_fields w h).2.2.2]
  have hh := instruction_code w h
  cases hop : (instruction w).op
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rw [immediate_I w (code_I w _ (by simpa [hop] using hh) (by decide))]
  · rw [immediate_I w (code_I w _ (by simpa [hop] using hh) (by decide))]
  · rw [immediate_I w (code_I w _ (by simpa [hop] using hh) (by decide))]
  · rw [immediate_I w (code_I w _ (by simpa [hop] using hh) (by decide))]
  · rw [immediate_I w (code_I w _ (by simpa [hop] using hh) (by decide))]
  · rw [immediate_I w (code_I w _ (by simpa [hop] using hh) (by decide))]
  · rw [immediate_I w (code_I w _ (by simpa [hop] using hh) (by decide))]
  · rw [immediate_I w (code_I w _ (by simpa [hop] using hh) (by decide))]
  · rw [immediate_I w (code_I w _ (by simpa [hop] using hh) (by decide))]
  · rw [immediate_U w (code_U w _ (by simpa [hop] using hh) (by decide))]
  · rw [immediate_U w (code_U w _ (by simpa [hop] using hh) (by decide))]
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
#print axioms calculate_immediate
#print axioms instruction_fields
#print axioms circuit_immediate
end CaseCPU.Bridge
