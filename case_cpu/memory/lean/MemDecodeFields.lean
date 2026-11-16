import MemDecoderCircuit
import DecodeFields
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def immediate (w : Word) : Word :=
  if w.setWidth 7 = 55 ∨ w.setWidth 7 = 23 then
    (w >>> 12).setWidth 20 ++ (0#12)
  else if w.setWidth 7 = 35 then
    (((w >>> 25).setWidth 7) ++ ((w >>> 7).setWidth 5)).signExtend 32
  else ((w >>> 20).setWidth 12).signExtend 32

inductive Decoded (w : Word) : Instr → Prop
  | base (i : CaseCPU.Instr) (h : CaseCPU.decode w = some i) : Decoded w (fromBase i)
  | load (op : Op) (kind : isLoad op = true) (opc : w.setWidth 7 = (3#7)) :
      Decoded w ⟨op,BitVec.ofNat 5 (w.toNat/128),BitVec.ofNat 5 (w.toNat/32768),0,
        (BitVec.ofNat 12 (w.toNat/1048576)).signExtend 32⟩
  | store (op : Op) (kind : isStore op = true) (opc : w.setWidth 7 = (35#7)) :
      Decoded w ⟨op,0,BitVec.ofNat 5 (w.toNat/32768),BitVec.ofNat 5 (w.toNat/1048576),
        (BitVec.ofNat 12 (w.toNat/2^25*32 + w.toNat/128%32)).signExtend 32⟩
  | fence (rs1 : (w >>> 15).setWidth 5 = (0#5)) : Decoded w ⟨.fence,0,0,0,0⟩

theorem decode_shapes (w : Word) (i : Instr) (h : decode w = some i) : Decoded w i := by
  have hf : w.toNat/4096%8=0 ∨ w.toNat/4096%8=1 ∨ w.toNat/4096%8=2 ∨
      w.toNat/4096%8=3 ∨ w.toNat/4096%8=4 ∨ w.toNat/4096%8=5 ∨
      w.toNat/4096%8=6 ∨ w.toNat/4096%8=7 := by omega
  by_cases hl : w.toNat%128 = 3
  · have ho : w.setWidth 7 = (3#7) := by rw [low_nat,hl]
    rcases hf with hf | hf | hf | hf | hf | hf | hf | hf
    all_goals simp [decode,hl,hf] at h
    all_goals cases h
    all_goals exact Decoded.load _ rfl ho
  · by_cases hs : w.toNat%128 = 35
    · have ho : w.setWidth 7 = (35#7) := by rw [low_nat,hs]
      rcases hf with hf | hf | hf | hf | hf | hf | hf | hf
      all_goals simp [decode,hl,hs,hf] at h
      all_goals cases h
      all_goals exact Decoded.store _ rfl ho
    · by_cases hc : w.toNat%128 = 15 && w.toNat/4096%8 = 0 &&
          BitVec.ofNat 5 (w.toNat/128) = (0#5) && BitVec.ofNat 5 (w.toNat/32768) = (0#5)
      · have hrs : (w >>> 15).setWidth 5 = (0#5) := by
          rw [slice_nat]
          have hc' : ((w.toNat%128 = 15 ∧ w.toNat/4096%8 = 0) ∧
              BitVec.ofNat 5 (w.toNat/128) = (0#5)) ∧
              BitVec.ofNat 5 (w.toNat/32768) = (0#5) := by simpa using hc
          exact hc'.2
        simp [decode,hl,hs,hc] at h
        cases h
        exact Decoded.fence hrs
      · simp only [decode,hl,hs,hc,↓reduceIte] at h
        cases hb : CaseCPU.decode w
        · simp [hb] at h
        · rename_i j
          simp [hb] at h
          subst i
          exact Decoded.base j hb

theorem base_fields (w : Word) (i : CaseCPU.Instr) (h : CaseCPU.decode w = some i) :
    i.rd = (w >>> 7).setWidth 5 ∧ i.rs1 = (w >>> 15).setWidth 5 ∧
    i.rs2 = (w >>> 20).setWidth 5 := by
  have hf := CaseCPU.Bridge.decoded_fields w i h
  simpa only [slice_nat] using ⟨hf.1,hf.2.1,hf.2.2.1⟩

theorem decoded_rs1 (w : Word) (i : Instr) (h : decode w = some i) :
    i.rs1 = (w >>> 15).setWidth 5 := by
  cases decode_shapes w i h with
  | base j hj => exact (base_fields w j hj).2.1
  | load op hl ho => simp [slice_nat]
  | store op hs ho => simp [slice_nat]
  | fence hrs => exact hrs.symm

theorem decoded_rs2 (w : Word) (i : Instr) (h : decode w = some i)
    (hk : isLoad i.op = false) (hf : i.op ≠ .fence) :
    i.rs2 = (w >>> 20).setWidth 5 := by
  cases decode_shapes w i h with
  | base j hj => exact (base_fields w j hj).2.2
  | load op hl ho => simp_all
  | store op hs ho => simp [slice_nat]
  | fence hrs => simp at hf

theorem decoded_rd (w : Word) (i : Instr) (h : decode w = some i)
    (hs : isStore i.op = false) (hf : i.op ≠ .fence) :
    i.rd = (w >>> 7).setWidth 5 := by
  cases decode_shapes w i h with
  | base j hj => exact (base_fields w j hj).1
  | load op hl ho => simp [slice_nat]
  | store op hs' ho => simp_all
  | fence hrs => simp at hf

theorem store_imm_bits (w : Word) :
    BitVec.ofNat 12 (w.toNat/2^25*32 + w.toNat/128%32) =
      (w >>> 25).setWidth 7 ++ (w >>> 7).setWidth 5 := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat,BitVec.toNat_append,BitVec.toNat_setWidth,
    BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]
  have hb := w.isLt
  have hr : w.toNat/33554432 < 128 := by omega
  have hs : w.toNat/128%32 < 32 := Nat.mod_lt _ (by decide)
  rw [←Nat.shiftLeft_add_eq_or_of_lt hs]
  simp only [Nat.shiftLeft_eq]
  omega

theorem memory_immediate (w : Word) (i : Instr) (h : decode w = some i)
    (hk : (isLoad i.op || isStore i.op) = true) : immediate w = i.imm := by
  cases decode_shapes w i h with
  | base j hj => simp [fromBase,isLoad,isStore] at hk
  | load op hl ho =>
    simp [immediate,ho,slice_nat]
  | store op hs ho =>
    simp only [immediate,ho]
    simp only [BitVec.reduceEq,or_self,↓reduceIte]
    exact congrArg (BitVec.signExtend 32) (store_imm_bits w).symm
  | fence hrs => simp [isLoad,isStore] at hk

theorem base_opcode (w : Word) (i : CaseCPU.Instr) (h : CaseCPU.decode w = some i) :
    w.setWidth 7 ≠ (35#7) := by
  have hc := CaseCPU.Bridge.bits_code w
  rw [CaseCPU.Bridge.decodeCode,h] at hc
  simp only [Option.map_some,Option.getD_some] at hc
  have hi : CaseCPU.Bridge.opCode i.op ≠ (63#6) := by cases i.op <;> decide +kernel
  have hb : CaseCPU.Bridge.codeBits w ≠ (63#6) := by rw [hc];exact hi
  simp only [CaseCPU.Bridge.codeBits,CaseCPU.Bridge.codeFields,Word,CaseCPU.Word] at hb ⊢
  bv_decide

theorem base_calculate_immediate (w : Word) (i : CaseCPU.Instr) (h : CaseCPU.decode w = some i)
    (a b pc : Word) :
    CaseCPU.calculate i.op a b (immediate w) pc = CaseCPU.calculate i.op a b i.imm pc := by
  have hh : (CaseCPU.decode w).isSome = true := by simp [h]
  have hi : CaseCPU.Bridge.instruction w = i := by simp [CaseCPU.Bridge.instruction,h]
  have he : immediate w = CaseCPU.Bridge.rtlImmediate w := by
    simp [immediate,CaseCPU.Bridge.rtlImmediate,base_opcode w i h]
  rw [he]
  simpa only [hi] using CaseCPU.Bridge.calculate_immediate w a b pc hh

theorem decoded_calculate (w : Word) (i : Instr) (op : CaseCPU.Op)
    (h : decode w = some i) (hop : i.op = .alu op) (a b pc : Word) :
    CaseCPU.calculate op a b (immediate w) pc = CaseCPU.calculate op a b i.imm pc := by
  cases decode_shapes w i h with
  | base j hj =>
    have he : j.op = op := Op.alu.inj hop
    simpa only [←he,fromBase] using base_calculate_immediate w j hj a b pc
  | load k hl ho => simp only [Instr.op] at hop; subst k; simp [isLoad] at hl
  | store k hs ho => simp only [Instr.op] at hop; subst k; simp [isStore] at hs
  | fence hrs => cases hop

#print axioms decode_shapes
#print axioms memory_immediate
#print axioms base_calculate_immediate
end CaseCPUMem.Source
