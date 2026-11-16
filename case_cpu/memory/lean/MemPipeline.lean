import MemISA
namespace CaseCPUMem

structure Packet where
  instr : Instr
  effect : Effect
  pc : Word
  deriving Inhabited

structure Pipe where
  arch : Arch
  fetch : Option Instr := none
  decodeStage : Option Instr := none
  execute : Option Packet := none
  memory : Option Packet := none
  writeback : Option Packet := none
  remaining : Nat := 0
  memoryWait : Nat := 0

structure Input where
  reset : Bool := false
  initRegs : Reg → Word := fun _ => 0
  word : Word := 0
  valid : Bool := false
  sf : Bool := false
  sd : Bool := false
  sx : Bool := false
  sm : Bool := false
  sw : Bool := false
  memoryDelay : BitVec 4 := 0

def initialPipe (rf : Reg → Word) (mem : Memory) : Pipe := {arch := initial rf mem}

def advance (a : Arch) : Option Packet → Arch
  | none => a
  | some p => applyEffect a p.effect

def forwarded (s : Pipe) : Arch := advance (advance s.arch s.writeback) s.memory

def backendEmpty (s : Pipe) : Bool :=
  s.execute.isNone && s.memory.isNone && s.writeback.isNone

def packetBarrier : Option Packet → Bool
  | none => false
  | some p => barrier p.instr.op

def blocked (s : Pipe) (op : Op) : Bool :=
  packetBarrier s.execute || packetBarrier s.memory || packetBarrier s.writeback ||
    (barrier op && !backendEmpty s)

def retire (s : Pipe) (stall : Bool) : Pipe × Option Instr :=
  if stall then (s,none) else
  match s.writeback with
  | none => (s,none)
  | some p =>
    let arch := applyEffect s.arch p.effect
    if p.effect.fault != (0#3) then ({arch := arch},some p.instr)
    else ({s with arch := arch,writeback := none},some p.instr)

def moveMemory (s : Pipe) (stall : Bool) : Pipe :=
  if stall then s else
  if s.memoryWait > 0 then {s with memoryWait := s.memoryWait-1} else
  match s.writeback with
  | some _ => s
  | none => {s with writeback := s.memory,memory := none}

def moveExecute (s : Pipe) (stall : Bool) (delay : BitVec 4) : Pipe :=
  if stall then s else
  if s.remaining > 0 then {s with remaining := s.remaining-1} else
  match s.memory with
  | some _ => s
  | none => {s with
    memory := s.execute,execute := none,
    memoryWait := if packetBarrier s.execute then delay.toNat else 0}

def latency : Op → Nat
  | .alu .mul | .alu .mulh | .alu .mulhsu | .alu .mulhu => 3
  | .alu .div | .alu .divu | .alu .rem | .alu .remu => 34
  | _ => 1

def dispatch (s : Pipe) (stall : Bool) : Pipe :=
  if stall then s else
  match s.execute,s.decodeStage with
  | none,some ins =>
    if blocked s ins.op then s else
    let a := forwarded s
    {s with
      execute := some ⟨ins,effectFor a ins,a.pc⟩,
      remaining := latency ins.op-1,decodeStage := none}
  | _,_ => s

def moveFetch (s : Pipe) : Pipe :=
  match s.decodeStage with
  | some _ => s
  | none => {s with decodeStage := s.fetch,fetch := none}

def accept (s : Pipe) (i : Input) : Pipe × Bool :=
  if i.sf || !i.valid then (s,false) else
  match s.fetch,decode i.word with
  | none,some ins => ({s with fetch := some ins},true)
  | _,_ => (s,false)

structure Outcome where
  state : Pipe
  retired : Option Instr
  accepted : Bool

def cycle (s : Pipe) (i : Input) : Outcome :=
  if i.reset then ⟨initialPipe i.initRegs s.arch.mem,none,false⟩ else
  let (s1,retired) := retire s i.sw
  if s1.arch.fault != (0#3) then ⟨s1,retired,false⟩ else
  let s2 := moveMemory s1 i.sm
  let s3 := moveExecute s2 i.sx i.memoryDelay
  let s4 := dispatch s3 i.sd
  let s5 := moveFetch s4
  let (s6,accepted) := accept s5 i
  ⟨s6,retired,accepted⟩

end CaseCPUMem
