import ISA

namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def decodeOp (opc f3 f7 : Nat) : Option Op :=
  if opc = 0x33 then
    if f7 = 1 then [Op.mul,.mulh,.mulhsu,.mulhu,.div,.divu,.rem,.remu][f3]?
    else if f7 = 0 then [Op.add,.sll,.slt,.sltu,.xor,.srl,.or,.and][f3]?
    else if f7 = 32 && f3 = 0 then some .sub
    else if f7 = 32 && f3 = 5 then some .sra else none
  else if opc = 0x13 then
    if f3 = 1 then (if f7 = 0 then some .slli else none)
    else if f3 = 5 then (if f7 = 0 then some .srli else if f7 = 32 then some .srai else none)
    else ([some Op.addi,none,some .slti,some .sltiu,some .xori,none,some .ori,some .andi][f3]?).bind id
  else if opc = 0x37 then some .lui
  else if opc = 0x17 then some .auipc else none

def decodeImm (w : Word) : Word :=
  if w.toNat % 128 = 0x13 then (BitVec.ofNat 12 (w.toNat/2^20)).signExtend 32
  else if w.toNat % 128 = 0x37 || w.toNat % 128 = 0x17 then
    BitVec.ofNat 32 (w.toNat/4096*4096)
  else 0

theorem decode_decompose (w : Word) :
    CaseCPU.decode w =
      (decodeOp (w.toNat%128) (w.toNat/4096%8) (w.toNat/2^25)).map
        (fun op => ⟨op,BitVec.ofNat 5 (w.toNat/128),BitVec.ofNat 5 (w.toNat/2^15),
          BitVec.ofNat 5 (w.toNat/2^20),decodeImm w⟩) := by
  have hf : w.toNat/4096%8=0 ∨ w.toNat/4096%8=1 ∨ w.toNat/4096%8=2 ∨
      w.toNat/4096%8=3 ∨ w.toNat/4096%8=4 ∨ w.toNat/4096%8=5 ∨
      w.toNat/4096%8=6 ∨ w.toNat/4096%8=7 := by omega
  rcases hf with hf | hf | hf | hf | hf | hf | hf | hf
  all_goals by_cases hR : w.toNat%128=0x33
  all_goals by_cases hI : w.toNat%128=0x13
  all_goals by_cases hU : w.toNat%128=0x37
  all_goals by_cases hA : w.toNat%128=0x17
  all_goals by_cases hM : w.toNat/2^25=1
  all_goals by_cases hZ : w.toNat/2^25=0
  all_goals by_cases hS : w.toNat/2^25=32
  all_goals simp_all [CaseCPU.decode,decodeOp,decodeImm,Option.map,Option.bind]
  all_goals split <;> simp_all

theorem decoded_fields (w : Word) (i : Instr) (h : CaseCPU.decode w = some i) :
    i.rd = BitVec.ofNat 5 (w.toNat/128) ∧
    i.rs1 = BitVec.ofNat 5 (w.toNat/2^15) ∧
    i.rs2 = BitVec.ofNat 5 (w.toNat/2^20) ∧ i.imm = decodeImm w := by
  rw [decode_decompose] at h
  cases hp : decodeOp (w.toNat%128) (w.toNat/4096%8) (w.toNat/2^25) with
  | none => simp [hp] at h
  | some op =>
    simp only [hp, Option.map_some, Option.some.injEq] at h
    subst i
    exact ⟨rfl,rfl,rfl,rfl⟩

#print axioms decode_decompose
end CaseCPU.Bridge
