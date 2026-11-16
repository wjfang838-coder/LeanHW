import ISA

namespace CaseCPU

/-- Fixed-latency execution unit: result computed on EX entry, completion delayed.
    This is a latency model, not an iterative multiplier/divider circuit. -/
def latency : Op → Nat
  | .mul | .mulh | .mulhsu | .mulhu => 3
  | .div | .divu | .rem | .remu => 34
  | _ => 1

structure Packet where
  instr : Instr
  effect : Effect
  deriving Repr, Inhabited

structure Pipe where
  arch : Arch
  fetch : Option Instr := none
  decodeStage : Option Instr := none
  execute : Option Packet := none
  memory : Option Packet := none
  writeback : Option Packet := none
  remaining : Nat := 0

structure Input where
  reset : Bool := false
  initRegs : Reg → Word := fun _ => 0
  word : Word := 0
  valid : Bool := false
  stallFetch : Bool := false
  stallDecode : Bool := false
  stallExecute : Bool := false
  stallMemory : Bool := false
  stallWriteback : Bool := false

def initial (rf : Reg → Word) : Pipe :=
  { arch := { regs := fun r => if r = 0 then 0 else rf r } }

def advance (a : Arch) : Option Packet → Arch
  | none => a
  | some p => applyEffect a p.effect

/-- Younger instructions see WB followed by MEM. Thus MEM wins a WAW dependency.
    EX must be empty before dispatch; any previous EX packet has already moved to MEM. -/
def forwarded (s : Pipe) : Arch := advance (advance s.arch s.writeback) s.memory

def retire (s : Pipe) (stall : Bool) : Pipe × Option Instr :=
  if stall then (s, none) else
  match s.writeback with
  | none => (s, none)
  | some p => ({ s with arch := applyEffect s.arch p.effect, writeback := none }, some p.instr)

def moveMemory (s : Pipe) (stall : Bool) : Pipe :=
  if stall then s else
  match s.writeback with
  | some _ => s
  | none => { s with writeback := s.memory, memory := none }

def moveExecute (s : Pipe) (stall : Bool) : Pipe :=
  if stall then s else
  if s.remaining > 0 then { s with remaining := s.remaining - 1 } else
  match s.memory with
  | some _ => s
  | none => { s with memory := s.execute, execute := none }

def dispatch (s : Pipe) (stall : Bool) : Pipe :=
  if stall then s else
  match s.execute, s.decodeStage with
  | none, some i =>
    { s with execute := some ⟨i, effectFor (forwarded s) i⟩,
             remaining := latency i.op - 1, decodeStage := none }
  | _, _ => s

def moveFetch (s : Pipe) : Pipe :=
  match s.decodeStage with
  | some _ => s
  | none => { s with decodeStage := s.fetch, fetch := none }

def accept (s : Pipe) (i : Input) : Pipe × Bool :=
  if i.stallFetch || !i.valid then (s, false) else
  match s.fetch, CaseCPU.decode i.word with
  | none, some ins => ({ s with fetch := some ins }, true)
  | _, _ => (s, false)

structure Outcome where
  state : Pipe
  retired : Option Instr
  accepted : Bool

/-- All decisions use the same edge's old state and temporary next-state values.
    Every instruction crosses at most one boundary per edge, because transfers are
    processed oldest first. Reset has absolute priority, including over retirement. -/
def cycle (s : Pipe) (i : Input) : Outcome :=
  if i.reset then ⟨initial i.initRegs, none, false⟩ else
  let (s1, retired) := retire s i.stallWriteback
  let s2 := moveMemory s1 i.stallMemory
  let s3 := moveExecute s2 i.stallExecute
  let s4 := dispatch s3 i.stallDecode
  let s5 := moveFetch s4
  let (s6, accepted) := accept s5 i
  ⟨s6, retired, accepted⟩

end CaseCPU
