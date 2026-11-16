import Std

/-! Frozen transaction specification. No import of the pipeline or RTL. -/
namespace CaseCPU
abbrev Word := BitVec 32
abbrev Reg := BitVec 5

inductive Op where
  | add | sub | sll | slt | sltu | xor | srl | sra | or | and
  | addi | slti | sltiu | xori | ori | andi | slli | srli | srai
  | lui | auipc
  | mul | mulh | mulhsu | mulhu | div | divu | rem | remu
  deriving DecidableEq, Repr, Inhabited

structure Instr where
  op : Op
  rd : Reg
  rs1 : Reg
  rs2 : Reg
  imm : Word := 0
  deriving DecidableEq, Repr, Inhabited

structure Arch where
  regs : Reg → Word
  pc : Word := 0

def readReg (s : Arch) (r : Reg) : Word := if r = 0 then 0 else s.regs r
def writeReg (s : Arch) (r : Reg) (v : Word) : Arch :=
  { s with regs := fun q => if q = 0 then 0 else if q = r then v else s.regs q }

structure Effect where
  rd : Reg
  value : Word
  deriving DecidableEq, Repr, Inhabited

def bit (p : Prop) [Decidable p] : Word := if p then 1 else 0
def signedDiv (a b : Word) : Word :=
  if b = 0 then -1 else BitVec.ofInt 32 (a.toInt.tdiv b.toInt)
def signedRem (a b : Word) : Word :=
  if b = 0 then a else BitVec.ofInt 32 (a.toInt.tmod b.toInt)

/-- ISA arithmetic: wrap at XLEN, shift by the low five bits, signed divide toward zero. -/
def calculate (op : Op) (a b imm pc : Word) : Word :=
  let sh := b.toNat % 32
  let si := imm.toNat % 32
  match op with
  | .add => a + b | .sub => a - b
  | .sll => a <<< sh | .slt => bit (a.toInt < b.toInt)
  | .sltu => bit (a < b) | .xor => a ^^^ b
  | .srl => a >>> sh | .sra => a.sshiftRight sh
  | .or => a ||| b | .and => a &&& b
  | .addi => a + imm | .slti => bit (a.toInt < imm.toInt)
  | .sltiu => bit (a < imm) | .xori => a ^^^ imm
  | .ori => a ||| imm | .andi => a &&& imm
  | .slli => a <<< si | .srli => a >>> si | .srai => a.sshiftRight si
  | .lui => imm | .auipc => pc + imm
  | .mul => a * b
  | .mulh => BitVec.ofInt 32 ((a.toInt * b.toInt) / 2^32)
  | .mulhsu => BitVec.ofInt 32 ((a.toInt * (Int.ofNat b.toNat)) / 2^32)
  | .mulhu => BitVec.ofNat 32 ((a.toNat * b.toNat) / 2^32)
  | .div => signedDiv a b | .divu => if b = 0 then -1 else a / b
  | .rem => signedRem a b | .remu => if b = 0 then a else a % b

def effectFor (s : Arch) (i : Instr) : Effect :=
  ⟨i.rd, calculate i.op (readReg s i.rs1) (readReg s i.rs2) i.imm s.pc⟩

def applyEffect (s : Arch) (e : Effect) : Arch :=
  { writeReg s e.rd e.value with pc := s.pc + 4 }

/-- One transaction = one retired instruction, including an instruction with rd=x0. -/
def isaStep (s : Arch) (i : Instr) : Arch := applyEffect s (effectFor s i)

def isaRun : Arch → List Instr → Arch
  | s, [] => s
  | s, i :: is => isaRun (isaStep s i) is

/-- Strict RV32 encoding decoder; reserved funct fields and unsupported opcodes are rejected. -/
def decode (w : Word) : Option Instr := do
  let n := w.toNat
  let opcode := n % 128
  let f3 := n / 2^12 % 8
  let f7 := n / 2^25
  let rd := BitVec.ofNat 5 (n / 2^7)
  let rs1 := BitVec.ofNat 5 (n / 2^15)
  let rs2 := BitVec.ofNat 5 (n / 2^20)
  let mut imm : Word := 0
  let op ← if opcode = 0x33 then
    if f7 = 1 then
      ([Op.mul, .mulh, .mulhsu, .mulhu, .div, .divu, .rem, .remu][f3]?)
    else if f7 = 0 then
      ([Op.add, .sll, .slt, .sltu, .xor, .srl, .or, .and][f3]?)
    else if f7 = 32 && f3 = 0 then some Op.sub
    else if f7 = 32 && f3 = 5 then some Op.sra else none
  else if opcode = 0x13 then do
    imm := (BitVec.ofNat 12 (n / 2^20)).signExtend 32
    if f3 = 1 then
      if f7 = 0 then pure Op.slli else none
    else if f3 = 5 then
      if f7 = 0 then pure Op.srli else if f7 = 32 then pure Op.srai else none
    else ([some Op.addi, none, some Op.slti, some Op.sltiu,
           some Op.xori, none, some Op.ori, some Op.andi][f3]?).bind id
  else if opcode = 0x37 || opcode = 0x17 then do
    imm := BitVec.ofNat 32 (n / 4096 * 4096)
    pure (if opcode = 0x37 then Op.lui else Op.auipc)
  else none
  return ⟨op, rd, rs1, rs2, imm⟩

theorem x0_after_step (s : Arch) (i : Instr) : readReg (isaStep s i) 0 = 0 := by
  simp [readReg]

theorem div_zero (a : Word) : signedDiv a 0 = -1 := by simp [signedDiv]
theorem rem_zero (a : Word) : signedRem a 0 = a := by simp [signedRem]
theorem signed_overflow : signedDiv 0x80000000 0xffffffff = 0x80000000 := by decide +kernel
theorem rem_overflow : signedRem 0x80000000 0xffffffff = 0 := by decide +kernel

end CaseCPU
