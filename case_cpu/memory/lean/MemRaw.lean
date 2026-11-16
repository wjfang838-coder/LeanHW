import MemRefinement
import WordMath
namespace CaseCPUMem.Raw
open CaseCPU.Bridge (RF readRF writeRF resetRF read_writeRF read_resetRF)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure Packet where
  word : Word := 0
  value : Word := 0
  pc : Word := 0
  addr : Word := 0
  data : Word := 0
  fault : BitVec 3 := 0
  deriving Inhabited

structure State where
  rf : RF := 0
  pc : Word := 0
  mem : Memory
  fault : BitVec 3 := 0
  fi : Word := 0
  di : Word := 0
  x : Packet := {}
  m : Packet := {}
  w : Packet := {}
  fv : Bool := false
  dv : Bool := false
  xv : Bool := false
  mv : Bool := false
  wv : Bool := false
  count : BitVec 6 := 0
  waitCount : BitVec 4 := 0

structure Pins where
  reset : Bool := false
  seed : RF := 0
  word : Word := 0
  valid : Bool := false
  sf : Bool := false
  sd : Bool := false
  sx : Bool := false
  sm : Bool := false
  sw : Bool := false
  delay : BitVec 4 := 0
  debugReg : Reg := 0
  debugMem : Address := 0

def input (i : Pins) : Input := {
  reset := i.reset,initRegs := readRF i.seed,word := i.word,valid := i.valid,
  sf := i.sf,sd := i.sd,sx := i.sx,sm := i.sm,sw := i.sw,memoryDelay := i.delay }

def instr (w : Word) : Instr := (decode w).getD default

def effect (mem : Memory) (ready : Bool) (p : Packet) : Effect :=
  if p.fault != (0#3) then {fault := p.fault} else
  match (instr p.word).op with
  | .alu _ => {rd := (instr p.word).rd,value := p.value}
  | .fence => {}
  | op => if isLoad op then {
      rd := (instr p.word).rd,
      value := if ready then p.value else loadValue op p.addr (mem (addressOf p.addr)) }
    else {store := some (storeEffect op p.addr p.data)}

def packet (mem : Memory) (ready : Bool) (p : Packet) : CaseCPUMem.Packet :=
  ⟨instr p.word,effect mem ready p,p.pc⟩

def optPacket (mem : Memory) (ready : Bool) (en : Bool) (p : Packet) : Option CaseCPUMem.Packet :=
  if en then some (packet mem ready p) else none

def optInstr (en : Bool) (w : Word) : Option Instr := if en then some (instr w) else none

def project (s : State) : Pipe := {
  arch := ⟨readRF s.rf,s.pc,s.mem,s.fault⟩,
  fetch := optInstr s.fv s.fi,decodeStage := optInstr s.dv s.di,
  execute := optPacket s.mem false s.xv s.x,memory := optPacket s.mem false s.mv s.m,
  writeback := optPacket s.mem true s.wv s.w,remaining := s.count.toNat,memoryWait := s.waitCount.toNat }

def initial (seed : RF) (mem : Memory) : State := {rf := resetRF seed,mem := mem}

def commit (s : State) (stall : Bool) : State :=
  if s.wv && !stall then
    if s.w.fault != (0#3) then {rf := s.rf,pc := s.pc,mem := s.mem,fault := s.w.fault}
    else {
      s with
      rf := if isStore (instr s.w.word).op || (instr s.w.word).op == .fence then s.rf
        else writeRF s.rf (instr s.w.word).rd s.w.value,
      pc := s.pc+4,wv := false,
      mem := if isStore (instr s.w.word).op then
        updateMem s.mem (storeEffect (instr s.w.word).op s.w.addr s.w.data) else s.mem }
  else s

def finish (mem : Memory) (p : Packet) : Packet :=
  if isLoad (instr p.word).op && p.fault == (0#3) then
    {p with value := loadValue (instr p.word).op p.addr (mem (addressOf p.addr))}
  else p

def memory (s : State) (stall : Bool) : State :=
  if stall then s else
  if s.waitCount != (0#4) then {s with waitCount := s.waitCount-1} else
  if s.wv then s else {s with w := finish s.mem s.m,wv := s.mv,mv := false}

def execute (s : State) (stall : Bool) (delay : BitVec 4) : State :=
  if stall then s else
  if s.count != (0#6) then {s with count := s.count-1} else
  if s.mv then s else {
    s with
      m := s.x,mv := s.xv,xv := false,
      waitCount := if s.xv && barrier (instr s.x.word).op then delay else 0 }

def forwardRF (s : State) : RF :=
  let rf := if s.wv then writeRF s.rf (instr s.w.word).rd s.w.value else s.rf
  if s.mv then writeRF rf (instr s.m.word).rd s.m.value else rf

def forwardPC (s : State) : Word := s.pc+(if s.wv then 4 else 0)+(if s.mv then 4 else 0)

def blocked (s : State) (op : Op) : Bool :=
  (s.xv && barrier (instr s.x.word).op) || (s.mv && barrier (instr s.m.word).op) ||
    (s.wv && barrier (instr s.w.word).op) || (barrier op && (s.xv || s.mv || s.wv))

def issue (s : State) (w : Word) : Packet :=
  let i := instr w
  let rf := forwardRF s
  let a := readRF rf i.rs1
  let b := readRF rf i.rs2
  let addr := a+i.imm
  let pc := forwardPC s
  match i.op with
  | .alu op => ⟨w,CaseCPU.calculate op a b i.imm pc,pc,0,0,0⟩
  | .fence => ⟨w,0,pc,0,0,0⟩
  | op => ⟨w,0,pc,addr,(if isStore op then b else 0),accessFault op addr⟩

def dispatch (s : State) (stall : Bool) : State :=
  if !stall && !s.xv && s.dv && !blocked s (instr s.di).op then {
    s with
      x := issue s s.di,xv := true,dv := false,
      count := BitVec.ofNat 6 (CaseCPUMem.latency (instr s.di).op-1) }
  else s

def fetch (s : State) : State :=
  if s.dv then s else {s with di := s.fi,dv := s.fv,fv := false}

def ready (s : State) (i : Pins) : Bool :=
  !i.reset && !i.sf && !s.fv && (decode i.word).isSome

def accept (s : State) (i : Pins) : State :=
  if i.valid && ready s i then {s with fv := true,fi := i.word} else s

def cycle (s : State) (i : Pins) : State :=
  if i.reset then initial i.seed s.mem else
  let s1 := commit s i.sw
  if s1.fault != (0#3) then s1 else
  accept (fetch (dispatch (execute (memory s1 i.sm) i.sx i.delay) i.sd)) i

/-- Barrier packets are exclusive in the backend. This is a proved scheduling
    invariant, not a restriction on the instruction input stream. -/
def Isolated (s : State) : Prop :=
  (s.xv = true → barrier (instr s.x.word).op = true → s.mv = false ∧ s.wv = false) ∧
  (s.mv = true → barrier (instr s.m.word).op = true → s.xv = false ∧ s.wv = false) ∧
  (s.wv = true → barrier (instr s.w.word).op = true → s.xv = false ∧ s.mv = false)

def WellKind (en : Bool) (p : Packet) : Prop :=
  en = true →
    (decode p.word).isSome = true ∧
    (barrier (instr p.word).op = false → p.fault = (0#3))

def Valid (s : State) : Prop :=
  Isolated s ∧ WellKind s.xv s.x ∧ WellKind s.mv s.m ∧ WellKind s.wv s.w ∧
  (s.fv = true → (decode s.fi).isSome = true) ∧
  (s.dv = true → (decode s.di).isSome = true) ∧
  (s.fault ≠ (0#3) → s.wv = false ∧ s.mv = false ∧ s.xv = false ∧ s.dv = false ∧ s.fv = false)

end CaseCPUMem.Raw
