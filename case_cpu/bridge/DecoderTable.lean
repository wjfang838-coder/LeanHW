import RawCPU
import DecodeSpec
import Std.Tactic.BVDecide

namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def opCode : Op → BitVec 6
  | .add => 0 | .sub => 1 | .sll => 2 | .slt => 3 | .sltu => 4
  | .xor => 5 | .srl => 6 | .sra => 7 | .or => 8 | .and => 9
  | .addi => 10 | .slti => 11 | .sltiu => 12 | .xori => 13 | .ori => 14
  | .andi => 15 | .slli => 16 | .srli => 17 | .srai => 18 | .lui => 19
  | .auipc => 20 | .mul => 21 | .mulh => 22 | .mulhsu => 23 | .mulhu => 24
  | .div => 25 | .divu => 26 | .rem => 27 | .remu => 28

def decodeCode (w : Word) : BitVec 6 :=
  match CaseCPU.decode w with | some i => opCode i.op | none => 63

theorem decode_code_fields (w : Word) :
    decodeCode w = ((decodeOp (w.toNat%128) (w.toNat/4096%8) (w.toNat/2^25)).map opCode).getD 63 := by
  unfold decodeCode
  rw [decode_decompose]
  cases decodeOp (w.toNat%128) (w.toNat/4096%8) (w.toNat/2^25) <;> rfl

def codeFields (opc : BitVec 7) (f : BitVec 3) (s : BitVec 7) : BitVec 6 :=
  if opc = 0x33 then
    if s = 1 then f.setWidth 6 + 21
    else if s = 0 then
      if f = 0 then 0 else if f = 1 then 2 else if f = 2 then 3
      else if f = 3 then 4 else if f = 4 then 5 else if f = 5 then 6
      else if f = 6 then 8 else 9
    else if s = 32 && f = 0 then 1
    else if s = 32 && f = 5 then 7 else 63
  else if opc = 0x13 then
    if f = 0 then 10 else if f = 2 then 11 else if f = 3 then 12
    else if f = 4 then 13 else if f = 6 then 14 else if f = 7 then 15
    else if f = 1 then (if s = 0 then 16 else 63)
    else (if s = 0 then 17 else if s = 32 then 18 else 63)
  else if opc = 0x37 then 19 else if opc = 0x17 then 20 else 63

def codeBits (w : Word) : BitVec 6 :=
  codeFields (w.setWidth 7) ((w >>> 12).setWidth 3) ((w >>> 25).setWidth 7)

/-- Complete finite decoder table: 128*8*128 combinations, with no data operands.
    Native decision trust is audited explicitly alongside LRAT bridge axioms. -/
theorem code_table : ∀ (opc : BitVec 7) (f : BitVec 3) (s : BitVec 7),
    codeFields opc f s = ((decodeOp opc.toNat f.toNat s.toNat).map opCode).getD 63 := by
  native_decide

theorem bits_code (w : Word) : codeBits w = decodeCode w := by
  rw [decode_code_fields]
  unfold codeBits
  rw [code_table]
  have h : w.toNat/33554432 < 128 := by have hh := w.isLt; omega
  simp only [BitVec.toNat_setWidth, BitVec.toNat_ushiftRight, Nat.shiftRight_eq_div_pow]
  simp only [show (2^7 : Nat) = 128 from rfl, show (2^3 : Nat) = 8 from rfl, show (2^12 : Nat) = 4096 from rfl, show (2^25 : Nat) = 33554432 from rfl]
  rw [Nat.mod_eq_of_lt h]

#print axioms code_table
#print axioms bits_code
end CaseCPU.Bridge
