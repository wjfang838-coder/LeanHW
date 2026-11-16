import LeanRTL.Core.MemSemantics
import LeanRTL.Core.Check

/-!
Whole-design, single-clock native-array semantics. This is a separate execution
profile; the legacy register-only Module.step/compiler theorem is unchanged.
Read addresses in this initial profile depend on registers/physical inputs only.
Asynchronous reads observe the old array, all register D inputs observe those
reads, and enabled writes take effect atomically at the common positive edge.
The imported logic's synthetic read ports are bound by bindReads, never oracles.
-/
namespace LeanRTL.NativeMemory

abbrev Arrays := String → Nat → Nat

structure ReadPort where
  memory : String
  out : String
  addrWidth : Nat
  dataWidth : Nat
  addr : Expr addrWidth

structure WritePort (aw dw : Nat) where
  addr : Expr aw
  data : Expr dw
  mask : Expr dw

structure Memory where
  name : String
  addrWidth : Nat
  dataWidth : Nat
  write : Option (WritePort addrWidth dataWidth) := none

structure State where
  regs : Env
  arrays : Arrays

structure Program where
  /-- Pure combinational/register AST. Synthetic RAM read names are injected below. -/
  logic : LeanRTL.Module
  memories : List Memory
  reads : List ReadPort

/-- Executable acceptance gate for this new profile. The legacy module checker
    retains its existing memory exclusion; callers must select native semantics. -/
def Program.checked (p : Program) : Bool :=
  let readNames := p.reads.map (·.out)
  let memoryNames := p.memories.map (·.name)
  let baseScope := (p.logic.inputs.filter (fun i => !readNames.contains i.name)).map
    (fun i => (i.name,i.width)) ++ p.logic.regs.map (fun r => (r.name,r.width))
  let finalScope := p.logic.allNameWidths
  p.logic.checkErrors.isEmpty && p.logic.latches.isEmpty && p.logic.mems.isEmpty &&
    p.logic.reset.isNone && p.logic.clock.isSome &&
    p.logic.regs.all (fun r => !r.negedge && r.asyncReset.isNone && r.asyncLoad.isNone && r.clockNet.isNone) &&
    decide readNames.Nodup && decide memoryNames.Nodup &&
    p.reads.all (fun r =>
      p.logic.inputs.any (fun i => i.name == r.out && i.width == r.dataWidth) &&
      p.memories.any (fun m => m.name == r.memory && m.addrWidth == r.addrWidth && m.dataWidth == r.dataWidth) &&
      r.addr.varRefs.all (fun v => baseScope.contains v)) &&
    p.memories.all (fun m => 0 < m.addrWidth && 0 < m.dataWidth &&
      match m.write with
      | none => true
      | some w => (w.addr.varRefs ++ w.data.varRefs ++ w.mask.varRefs).all
          (fun v => finalScope.contains v))

/-- A memory remains a function on addresses, not an expanded register vector. -/
def readWord (a : Arrays) (name : String) (aw dw : Nat) (addr : BitVec aw) : BitVec dw :=
  BitVec.ofNat dw (a name addr.toNat)

def writeWord (a : Arrays) (name : String) (aw dw : Nat) (addr : BitVec aw)
    (data mask : BitVec dw) : Arrays :=
  if mask = (0#dw) then a else fun n q => if n = name ∧ q = addr.toNat then
    (((readWord a name aw dw addr) &&& ~~~mask) ||| (data &&& mask)).toNat
  else a n q

/-- Address expressions see the pre-read environment, excluding combinational loops. -/
def bindReads (reads : List ReadPort) (arrays : Arrays) (base : Env) : Env :=
  reads.foldl (fun e r => fun n => if n = r.out then
    (readWord arrays r.memory r.addrWidth r.dataWidth (eval r.addr base)).toNat else e n) base

def Program.base (p : Program) (s : State) (inputs : Env) : Env :=
  cycleEnv s.regs inputs (p.logic.regs.map (·.name))

def Program.comb (p : Program) (s : State) (inputs : Env) : Env :=
  evalWires p.logic.wires (bindReads p.reads s.arrays (p.base s inputs))

def Memory.update (m : Memory) (arrays : Arrays) (e : Env) : Arrays :=
  match m.write with
  | none => arrays
  | some w => writeWord arrays m.name m.addrWidth m.dataWidth
      (eval w.addr e) (eval w.data e) (eval w.mask e)

/-- All write expressions use the same old-state combinational environment.
    Different memories have disjoint names; each memory has at most one write port. -/
def Program.nextArrays (p : Program) (s : State) (inputs : Env) : Arrays :=
  p.memories.foldl (fun a m => m.update a (p.comb s inputs)) s.arrays

def Program.step (p : Program) (s : State) (inputs : Env) : State :=
  let e := p.comb s inputs
  { regs := fun n => match p.logic.regs.find? (·.name = n) with
      | some r => (eval r.next e).toNat
      | none => s.regs n
    arrays := p.nextArrays s inputs }

def Program.outputs (p : Program) (s : State) (inputs : Env) : List (String × Nat) :=
  p.logic.outputs.map (fun o => (o.name,(eval o.expr (p.comb s inputs)).toNat))

def Program.run (p : Program) : State → List Env → State
  | s,[] => s
  | s,i::xs => p.run (p.step s i) xs

@[simp] theorem read_write_same (a : Arrays) (name : String) (aw dw : Nat)
    (addr : BitVec aw) (data mask : BitVec dw) :
    readWord (writeWord a name aw dw addr data mask) name aw dw addr =
      (readWord a name aw dw addr &&& ~~~mask) ||| (data &&& mask) := by
  by_cases hm : mask = (0#dw)
  · subst mask; simp [readWord,writeWord]
  · simp only [writeWord,hm,↓reduceIte,readWord,and_self,BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem read_write_other (a : Arrays) (name other : String) (aw dw : Nat)
    (addr q : BitVec aw) (data mask : BitVec dw)
    (h : other ≠ name ∨ q ≠ addr) :
    readWord (writeWord a name aw dw addr data mask) other aw dw q =
      readWord a other aw dw q := by
  have hn : ¬(other = name ∧ q.toNat = addr.toNat) := by
    intro hh
    rcases h with h | h
    · exact h hh.1
    · exact h (BitVec.eq_of_toNat_eq hh.2)
  by_cases hm : mask = (0#dw)
  · subst mask; simp [writeWord]
  · simp only [readWord,writeWord,hm,↓reduceIte,hn]

@[simp] theorem write_disabled (a : Arrays) (name : String) (aw dw : Nat)
    (addr : BitVec aw) (data : BitVec dw) :
    writeWord a name aw dw addr data 0 = a := by
  simp [writeWord]

end LeanRTL.NativeMemory
