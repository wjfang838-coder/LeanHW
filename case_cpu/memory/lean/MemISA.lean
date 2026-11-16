import ISA
import LeanRTL.Core.Spec.Model

/-! Frozen transaction model for the native-memory case. No pipeline/RTL imports. -/
namespace CaseCPUMem
abbrev Word := BitVec 32
abbrev Reg := BitVec 5
abbrev Address := BitVec 8
abbrev Memory := LeanRTL.Spec.Mem 8 32

inductive Op where
  | alu (op : CaseCPU.Op)
  | lb | lh | lw | lbu | lhu | sb | sh | sw | fence
  deriving DecidableEq,Repr,Inhabited

structure Instr where
  op : Op
  rd : Reg := 0
  rs1 : Reg := 0
  rs2 : Reg := 0
  imm : Word := 0
  deriving DecidableEq,Repr,Inhabited

structure Arch where
  regs : Reg → Word
  pc : Word := 0
  mem : Memory
  fault : BitVec 3 := 0

structure Store where
  addr : Address
  data : Word
  mask : Word
  deriving DecidableEq,Repr,Inhabited

structure Effect where
  rd : Reg := 0
  value : Word := 0
  store : Option Store := none
  fault : BitVec 3 := 0
  deriving DecidableEq,Repr,Inhabited

def readReg (s : Arch) (r : Reg) : Word := if r = (0#5) then 0 else s.regs r

def isLoad : Op → Bool
  | .lb | .lh | .lw | .lbu | .lhu => true
  | _ => false

def isStore : Op → Bool
  | .sb | .sh | .sw => true
  | _ => false

def barrier (op : Op) : Bool := isLoad op || isStore op || op == .fence

def addressOf (a : Word) : Address := (a >>> 2).setWidth 8

def byteShift (a : Word) : Nat := (a.setWidth 2).toNat*8

def accessFault (op : Op) (addr : Word) : BitVec 3 :=
  let store := isStore op
  let badAlign := match op with
    | .lh | .lhu | .sh => addr.getLsbD 0
    | .lw | .sw => addr.setWidth 2 != (0#2)
    | _ => false
  if badAlign then (if store then 2 else 1)
  else if addr >>> 10 != (0#32) then (if store then 4 else 3)
  else 0

def loadValue (op : Op) (addr word : Word) : Word :=
  let shifted := word >>> byteShift addr
  match op with
  | .lb => (shifted.setWidth 8).signExtend 32
  | .lbu => (shifted.setWidth 8).setWidth 32
  | .lh => (shifted.setWidth 16).signExtend 32
  | .lhu => (shifted.setWidth 16).setWidth 32
  | .lw => word
  | _ => 0

def storeMask (op : Op) (addr : Word) : Word :=
  match op with
  | .sb => 0xff <<< byteShift addr
  | .sh => 0xffff <<< byteShift addr
  | .sw => -1
  | _ => 0

def storeEffect (op : Op) (addr data : Word) : Store :=
  ⟨addressOf addr,data <<< byteShift addr,storeMask op addr⟩

def merge (old : Word) (s : Store) : Word := (old &&& ~~~s.mask) ||| (s.data &&& s.mask)

def updateMem (mem : Memory) (s : Store) : Memory :=
  LeanRTL.Spec.Mem.write mem s.addr (merge (mem s.addr) s)

def effectFor (s : Arch) (i : Instr) : Effect :=
  if s.fault != (0#3) then {} else
  match i.op with
  | .alu op => ⟨i.rd,CaseCPU.calculate op (readReg s i.rs1) (readReg s i.rs2) i.imm s.pc,none,0⟩
  | .fence => {}
  | op =>
    let addr := readReg s i.rs1 + i.imm
    let fault := accessFault op addr
    if fault != (0#3) then {fault := fault} else
    if isLoad op then {rd := i.rd,value := loadValue op addr (s.mem (addressOf addr))}
    else {store := some (storeEffect op addr (readReg s i.rs2))}

def applyEffect (s : Arch) (e : Effect) : Arch :=
  if s.fault != (0#3) then s else
  if e.fault != (0#3) then {s with fault := e.fault} else {
    regs := fun q => if q = (0#5) then 0 else if q = e.rd then e.value else s.regs q
    pc := s.pc+4
    mem := match e.store with | none => s.mem | some st => updateMem s.mem st
    fault := 0 }

def isaStep (s : Arch) (i : Instr) : Arch := applyEffect s (effectFor s i)

def isaRun : Arch → List Instr → Arch
  | s,[] => s
  | s,i::xs => isaRun (isaStep s i) xs

def initial (rf : Reg → Word) (mem : Memory) : Arch :=
  {regs := fun r => if r = (0#5) then 0 else rf r,mem := mem}

def fromBase (i : CaseCPU.Instr) : Instr := ⟨.alu i.op,i.rd,i.rs1,i.rs2,i.imm⟩

def decode (w : Word) : Option Instr :=
  let opc := w.toNat % 128
  let f := w.toNat/4096 % 8
  let rd := BitVec.ofNat 5 (w.toNat/128)
  let rs1 := BitVec.ofNat 5 (w.toNat/32768)
  let rs2 := BitVec.ofNat 5 (w.toNat/1048576)
  if opc = 3 then do
    let op ← [some Op.lb,some .lh,some .lw,none,some .lbu,some .lhu,none,none][f]?.bind id
    return ⟨op,rd,rs1,0,(BitVec.ofNat 12 (w.toNat/1048576)).signExtend 32⟩
  else if opc = 35 then do
    let op ← [some Op.sb,some .sh,some .sw,none,none,none,none,none][f]?.bind id
    let imm := BitVec.ofNat 12 (w.toNat/2^25*32 + w.toNat/128%32)
    return ⟨op,0,rs1,rs2,imm.signExtend 32⟩
  else if opc = 15 && f = 0 && rd = (0#5) && rs1 = (0#5) then
    some ⟨.fence,0,0,0,0⟩
  else (CaseCPU.decode w).map fromBase

theorem load_store_word (m : Memory) (a : Address) (v : Word) :
    (updateMem m ⟨a,v,-1⟩) a = v := by
  simp [updateMem,merge,LeanRTL.Spec.Mem.write]
  exact BitVec.and_allOnes

theorem memory_frame (m : Memory) (st : Store) (q : Address) (h : q ≠ st.addr) :
    updateMem m st q = m q := by simp [updateMem,LeanRTL.Spec.Mem.write,h]

theorem reset_preserves_memory (rf : Reg → Word) (m : Memory) : (initial rf m).mem = m := rfl

#print axioms load_store_word
#print axioms memory_frame
end CaseCPUMem
