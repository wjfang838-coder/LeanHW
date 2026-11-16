import Refinement
import WordMath

namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

structure RawPacket where
  word : Word := 0
  value : Word := 0
  pc : Word := 0
  deriving Inhabited

structure Raw where
  rf : RF := 0
  pc : Word := 0
  fi : Word := 0
  di : Word := 0
  x : RawPacket := {}
  m : RawPacket := {}
  w : RawPacket := {}
  fv : Bool := false
  dv : Bool := false
  xv : Bool := false
  mv : Bool := false
  wv : Bool := false
  remaining : BitVec 6 := 0

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
  debug : CaseCPU.Reg := 0

def specInput (i : Pins) : Input := {
  reset := i.reset, initRegs := readRF i.seed, word := i.word, valid := i.valid,
  stallFetch := i.sf, stallDecode := i.sd, stallExecute := i.sx,
  stallMemory := i.sm, stallWriteback := i.sw }

def instruction (w : Word) : Instr := (CaseCPU.decode w).getD default
def packet (p : RawPacket) : Packet := ⟨instruction p.word, ⟨(instruction p.word).rd,p.value⟩⟩
def optPacket (b : Bool) (p : RawPacket) : Option Packet := if b then some (packet p) else none
def optInstruction (b : Bool) (w : Word) : Option Instr := if b then some (instruction w) else none

def project (s : Raw) : Pipe := {
  arch := ⟨readRF s.rf,s.pc⟩,
  fetch := optInstruction s.fv s.fi, decodeStage := optInstruction s.dv s.di,
  execute := optPacket s.xv s.x, memory := optPacket s.mv s.m,
  writeback := optPacket s.wv s.w, remaining := s.remaining.toNat }

def rawInitial (seed : RF) : Raw := { rf := resetRF seed }

def commitRaw (s : Raw) (b : Bool) : Raw :=
  if s.wv && !b then
    { s with rf := writeRF s.rf (instruction s.w.word).rd s.w.value, pc := s.pc+4, wv := false }
  else s

def memoryRaw (s : Raw) (b : Bool) : Raw :=
  if !b && !s.wv then { s with wv := s.mv, w := s.m, mv := false } else s

def executeRaw (s : Raw) (b : Bool) : Raw :=
  if b then s else
  if s.remaining = 0 then
    if !s.mv then { s with mv := s.xv, m := s.x, xv := false } else s
  else { s with remaining := s.remaining - 1 }

def forwardRF (s : Raw) : RF :=
  let rf := if s.wv then writeRF s.rf (instruction s.w.word).rd s.w.value else s.rf
  if s.mv then writeRF rf (instruction s.m.word).rd s.m.value else rf

def forwardPC (s : Raw) : Word := s.pc + (if s.wv then 4 else 0) + (if s.mv then 4 else 0)

def dispatchRaw (s : Raw) (b : Bool) : Raw :=
  if !b && !s.xv && s.dv then
    let ins := instruction s.di
    let rf := forwardRF s
    let pc := forwardPC s
    let v := calculate ins.op (readRF rf ins.rs1) (readRF rf ins.rs2) ins.imm pc
    { s with
      x := ⟨s.di,v,pc⟩
      xv := true
      dv := false
      remaining := BitVec.ofNat 6 (latency ins.op - 1) }
  else s

def fetchRaw (s : Raw) : Raw :=
  if !s.dv then { s with dv := s.fv, di := s.fi, fv := false } else s

def readyRaw (s : Raw) (i : Pins) : Bool := !i.reset && !i.sf && !s.fv && (CaseCPU.decode i.word).isSome
def acceptRaw (s : Raw) (i : Pins) : Raw × Bool :=
  if i.valid && readyRaw s i then ({ s with fv := true, fi := i.word },true) else (s,false)

def beforeAccept (s : Raw) (i : Pins) : Raw :=
  fetchRaw (dispatchRaw (executeRaw (memoryRaw (commitRaw s i.sw) i.sm) i.sx) i.sd)

def rawCycle (s : Raw) (i : Pins) : Raw :=
  if i.reset then rawInitial i.seed else (acceptRaw (beforeAccept s i) i).1

def rawRetired (s : Raw) (i : Pins) : Option Instr :=
  if !i.reset && s.wv && !i.sw then some (instruction s.w.word) else none
def rawAccepted (s : Raw) (i : Pins) : Bool :=
  !i.reset && (acceptRaw (beforeAccept s i) i).2

theorem rf_write_arch (rf : RF) (pc : Word) (r : CaseCPU.Reg) (v : Word) :
    (⟨readRF (writeRF rf r v),pc+4⟩ : Arch) = applyEffect ⟨readRF rf,pc⟩ ⟨r,v⟩ := by
  unfold applyEffect writeReg
  congr 1
  funext q
  exact read_writeRF rf r q v

theorem project_initial (seed : RF) : project (rawInitial seed) = initial (readRF seed) := by
  simp only [project, rawInitial, initial, optPacket, optInstruction, Bool.false_eq_true, ↓reduceIte]
  congr 2
  funext r
  by_cases h : r = 0
  · subst r; simp [readRF]
  · simp only [h, ↓reduceIte]
    exact read_resetRF seed r

theorem project_commit (s : Raw) (b : Bool) :
    project (commitRaw s b) = (retire (project s) b).1 := by
  cases hb : b <;> cases hw : s.wv <;>
    simp [commitRaw, retire, project, optPacket, packet, hb, hw]
  exact rf_write_arch _ _ _ _

theorem project_memory (s : Raw) (b : Bool) :
    project (memoryRaw s b) = moveMemory (project s) b := by
  cases hb : b <;> cases hw : s.wv <;>
    simp [memoryRaw, moveMemory, project, optPacket, hb, hw]

theorem remaining_sub (x : BitVec 6) (h : x ≠ 0) : (x-1).toNat = x.toNat-1 := by
  have hx := x.isLt
  have hn : x.toNat ≠ 0 := fun ht => h (BitVec.eq_of_toNat_eq ht)
  simp [BitVec.toNat_sub]
  omega

theorem project_execute (s : Raw) (b : Bool) :
    project (executeRaw s b) = moveExecute (project s) b := by
  have hz : s.remaining.toNat = 0 ↔ s.remaining = 0 :=
    ⟨fun h => BitVec.eq_of_toNat_eq h, fun h => by rw [h]; rfl⟩
  have hn : 0 < s.remaining.toNat ↔ s.remaining ≠ 0 := by
    constructor
    · intro hp heq
      have heq' : s.remaining.toNat = 0 := congrArg BitVec.toNat heq
      omega
    · intro hne
      have ht : s.remaining.toNat ≠ 0 := fun h => hne (BitVec.eq_of_toNat_eq h)
      omega
  cases hb : b
  · by_cases hr : s.remaining = 0
    · have ht : s.remaining.toNat = 0 := hz.mpr hr
      cases hm : s.mv <;>
        simp only [executeRaw, hb, Bool.false_eq_true, ↓reduceIte, hr,
          Bool.not_false, Bool.not_true, hm, project, moveExecute, ht,
          optPacket, BitVec.toNat_ofNat, Nat.lt_irrefl] <;> simp
    · have ht : 0 < s.remaining.toNat := hn.mpr hr
      simp only [executeRaw, hb, Bool.false_eq_true, ↓reduceIte, hr]
      change { project s with remaining := (s.remaining-1).toNat } = _
      rw [remaining_sub _ hr]
      simp only [moveExecute, project, ht, ↓reduceIte, Bool.false_eq_true]
  · simp only [executeRaw, hb, ↓reduceIte, moveExecute]

theorem forwarded_project (s : Raw) :
    (⟨readRF (forwardRF s),forwardPC s⟩ : Arch) = forwarded (project s) := by
  cases hw : s.wv <;> cases hm : s.mv <;>
    simp [forwardRF, forwardPC, forwarded, advance, project, optPacket, packet,
      hw, hm, ← rf_write_arch]

theorem latency_fits (op : Op) : (BitVec.ofNat 6 (latency op-1)).toNat = latency op-1 := by
  cases op <;> decide

theorem project_dispatch (s : Raw) (b : Bool) :
    project (dispatchRaw s b) = dispatch (project s) b := by
  have hread (rf : RF) (pc : Word) (r : CaseCPU.Reg) :
      readReg ⟨readRF rf,pc⟩ r = readRF rf r := by
    by_cases h : r = 0
    · subst r; simp [readReg,readRF]
    · simp only [readReg,h,↓reduceIte]
  have hp : packet ⟨s.di,
      calculate (instruction s.di).op (readRF (forwardRF s) (instruction s.di).rs1)
        (readRF (forwardRF s) (instruction s.di).rs2) (instruction s.di).imm (forwardPC s),
      forwardPC s⟩ = ⟨instruction s.di,effectFor (forwarded (project s)) (instruction s.di)⟩ := by
    rw [← forwarded_project s]
    simp [packet,effectFor,hread]
  cases hb : b <;> cases hx : s.xv <;> cases hd : s.dv <;>
    simp [dispatchRaw, dispatch, optPacket, optInstruction, hb, hx, hd, latency_fits,
      show (project s).execute = optPacket s.xv s.x from rfl,
      show (project s).decodeStage = optInstruction s.dv s.di from rfl]
    <;> simp_all [project, optPacket, optInstruction]
  cases (instruction s.di).op <;> decide

theorem project_fetch (s : Raw) : project (fetchRaw s) = moveFetch (project s) := by
  cases hd : s.dv <;> simp [fetchRaw, moveFetch, project, optInstruction, hd]

theorem project_accept (s : Raw) (i : Pins) (h : i.reset = false) :
    project (acceptRaw s i).1 = (accept (project s) (specInput i)).1 ∧
      (acceptRaw s i).2 = (accept (project s) (specInput i)).2 := by
  cases hv : i.valid <;> cases hs : i.sf <;> cases hf : s.fv <;>
    cases hd : CaseCPU.decode i.word <;>
    simp [acceptRaw, readyRaw, accept, project, specInput, optInstruction,
      instruction, h, hv, hs, hf, hd]

theorem project_cycle (s : Raw) (i : Pins) :
    project (rawCycle s i) = (cycle (project s) (specInput i)).state := by
  cases hr : i.reset
  · simp only [rawCycle, hr, Bool.false_eq_true, ↓reduceIte]
    rw [(project_accept _ _ hr).1]
    simp only [beforeAccept, project_fetch, project_dispatch, project_execute,
      project_memory, project_commit]
    simp [cycle,specInput,hr]
  · simpa [rawCycle, cycle, specInput, hr] using project_initial i.seed

#print axioms project_cycle
end CaseCPU.Bridge
