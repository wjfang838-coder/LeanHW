import MemRaw
import Std.Tactic.BVDecide
namespace CaseCPUMem.Raw
open CaseCPU.Bridge (RF readRF writeRF resetRF read_writeRF read_resetRF)
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem project_initial (seed : RF) (mem : Memory) :
    project (initial seed mem) = initialPipe (readRF seed) mem := by
  simp only [project,initial,initialPipe,CaseCPUMem.initial,optPacket,optInstr,
    Bool.false_eq_true,↓reduceIte]
  congr 2
  funext r
  by_cases hr : r = (0#5)
  · subst r; simp [readRF]
  · simp only [hr,↓reduceIte]
    exact read_resetRF seed r

@[simp] theorem finish_word (mem : Memory) (p : Packet) : (finish mem p).word = p.word := by
  unfold finish
  split <;> rfl

@[simp] theorem finish_fault (mem : Memory) (p : Packet) : (finish mem p).fault = p.fault := by
  unfold finish
  split <;> rfl

theorem finish_packet (mem : Memory) (p : Packet) : packet mem true (finish mem p) = packet mem false p := by
  by_cases hf : p.fault = (0#3) <;> cases hop : (instr p.word).op <;>
    simp [packet,effect,finish,hf,hop,isLoad]

theorem nonzero_toNat {n : Nat} (v : BitVec n) : (0 < v.toNat) ↔ v ≠ (0#n) := by
  constructor
  · intro h he; subst v; simp at h
  · intro h
    have hn : v.toNat ≠ 0 := fun hz => h (BitVec.eq_of_toNat_eq hz)
    omega

theorem sub4 (v : BitVec 4) (h : v ≠ (0#4)) : (v-1).toNat = v.toNat-1 := by
  have hb := v.isLt
  have hn := (nonzero_toNat v).mpr h
  simp [BitVec.toNat_sub]
  omega

theorem sub6 (v : BitVec 6) (h : v ≠ (0#6)) : (v-1).toNat = v.toNat-1 := by
  have hb := v.isLt
  have hn := (nonzero_toNat v).mpr h
  simp [BitVec.toNat_sub]
  omega

theorem project_memory (s : State) (b : Bool) : project (memory s b) = moveMemory (project s) b := by
  cases hb : b
  · by_cases hc : s.waitCount = (0#4)
    · have hn : s.waitCount.toNat = 0 := by rw [hc]; rfl
      cases hw : s.wv <;>
        simp [memory,hb,hc,project,moveMemory,hn,hw,optPacket,finish_packet]
    · have hn := (nonzero_toNat s.waitCount).mpr hc
      simp [memory,hb,hc,project,moveMemory,hn,sub4 _ hc]
      have hb := s.waitCount.isLt
      omega
  · simp [memory,moveMemory,hb]

theorem barrier_opt (mem : Memory) (en : Bool) (p : Packet) :
    packetBarrier (optPacket mem false en p) = (en && barrier (instr p.word).op) := by
  cases en <;> rfl

theorem project_execute (s : State) (b : Bool) (d : BitVec 4) :
    project (execute s b d) = moveExecute (project s) b d := by
  cases hb : b
  · by_cases hc : s.count = (0#6)
    · have hn : s.count.toNat = 0 := by rw [hc]; rfl
      cases hm : s.mv <;>
        simp [execute,hb,hc,project,moveExecute,hn,hm,optPacket,packetBarrier,packet]
      cases hx : s.xv <;> simp [optPacket,packetBarrier,hx]
      split <;> rfl
    · have hn := (nonzero_toNat s.count).mpr hc
      simp [execute,hb,hc,project,moveExecute,hn,sub6 _ hc]
      have hb := s.count.isLt
      omega
  · simp [execute,moveExecute,hb]

theorem project_fetch (s : State) : project (fetch s) = moveFetch (project s) := by
  cases hd : s.dv <;> simp [fetch,moveFetch,project,optInstr,hd]

theorem project_accept (s : State) (i : Pins) (hr : i.reset = false) :
    project (accept s i) = (CaseCPUMem.accept (project s) (input i)).1 := by
  cases hv : i.valid <;> cases hs : i.sf <;> cases hf : s.fv <;> cases hw : decode i.word <;>
    simp [accept,ready,CaseCPUMem.accept,project,input,optInstr,instr,hv,hs,hf,hw,hr]

/-- Scheduling isolation is independent of arithmetic values and RAM contents. -/
theorem isolated_initial (seed : RF) (mem : Memory) : Isolated (initial seed mem) := by
  simp [Isolated,initial]

theorem isolated_commit (s : State) (b : Bool) (h : Isolated s) : Isolated (commit s b) := by
  unfold commit
  split <;> try exact h
  split
  · simp [Isolated]
  · simp only [Isolated] at *
    bv_decide

theorem isolated_memory (s : State) (b : Bool) (h : Isolated s) : Isolated (memory s b) := by
  unfold memory
  split <;> try exact h
  split <;> try simpa [Isolated] using h
  split <;> try exact h
  simp only [Isolated,finish_word] at *
  bv_decide

theorem isolated_execute (s : State) (b : Bool) (d : BitVec 4) (h : Isolated s) :
    Isolated (execute s b d) := by
  unfold execute
  split <;> try exact h
  split <;> try simpa [Isolated] using h
  split <;> try exact h
  simp only [Isolated] at *
  bv_decide

@[simp] theorem issue_word (s : State) (w : Word) : (issue s w).word = w := by
  cases hop : (instr w).op <;> simp [issue,hop]

theorem isolated_dispatch (s : State) (b : Bool) (h : Isolated s) : Isolated (dispatch s b) := by
  unfold dispatch
  split <;> try exact h
  simp only [Isolated,issue_word] at *
  unfold blocked at *
  bv_decide

theorem isolated_fetch (s : State) (h : Isolated s) : Isolated (fetch s) := by
  unfold fetch
  split <;> simpa [Isolated] using h

theorem isolated_accept (s : State) (i : Pins) (h : Isolated s) : Isolated (accept s i) := by
  unfold accept
  split <;> simpa [Isolated] using h

theorem isolated_cycle (s : State) (i : Pins) (h : Isolated s) : Isolated (cycle s i) := by
  cases hr : i.reset
  · simp only [cycle,hr,Bool.false_eq_true,↓reduceIte]
    change Isolated (if (commit s i.sw).fault != (0#3) then commit s i.sw else
      accept (fetch (dispatch (execute (memory (commit s i.sw) i.sm) i.sx i.delay) i.sd)) i)
    split
    · exact isolated_commit _ _ h
    · exact isolated_accept _ _ (isolated_fetch _ (isolated_dispatch _ _
        (isolated_execute _ _ _ (isolated_memory _ _ (isolated_commit _ _ h)))))
  · simpa [cycle,hr] using isolated_initial i.seed s.mem

theorem kind_issue (s : State) (w : Word) (h : (decode w).isSome = true) :
    WellKind true (issue s w) := by
  intro _
  rw [issue_word]
  refine ⟨h,?_⟩
  cases hop : (instr w).op <;> simp [barrier,isLoad,isStore,hop,issue]

theorem kind_finish (m : Memory) (en : Bool) (p : Packet) (h : WellKind en p) :
    WellKind en (finish m p) := by simpa [WellKind] using h

def Kinds (s : State) : Prop :=
  WellKind s.xv s.x ∧ WellKind s.mv s.m ∧ WellKind s.wv s.w ∧
  (s.fv = true → (decode s.fi).isSome = true) ∧
  (s.dv = true → (decode s.di).isSome = true)

theorem kinds_initial (seed : RF) (mem : Memory) : Kinds (initial seed mem) := by
  simp [Kinds,WellKind,initial]

theorem kinds_commit (s : State) (b : Bool) (h : Kinds s) : Kinds (commit s b) := by
  unfold commit
  split <;> try exact h
  split
  · simp [Kinds,WellKind]
  · simpa [Kinds,WellKind] using ⟨h.1,h.2.1,h.2.2.2⟩

theorem kinds_memory (s : State) (b : Bool) (h : Kinds s) : Kinds (memory s b) := by
  unfold memory
  split <;> try exact h
  split <;> try simpa [Kinds] using h
  split <;> try exact h
  exact ⟨h.1,by simp [WellKind],kind_finish _ _ _ h.2.1,h.2.2.2⟩

theorem kinds_execute (s : State) (b : Bool) (d : BitVec 4) (h : Kinds s) :
    Kinds (execute s b d) := by
  unfold execute
  split <;> try exact h
  split <;> try simpa [Kinds] using h
  split <;> try exact h
  exact ⟨by simp [WellKind],h.1,h.2.2⟩

theorem kinds_dispatch (s : State) (b : Bool) (h : Kinds s) : Kinds (dispatch s b) := by
  unfold dispatch
  split
  · rename_i hg
    have hd : s.dv = true := by simp_all
    exact ⟨kind_issue _ _ (h.2.2.2.2 hd),h.2.1,h.2.2.1,h.2.2.2.1,by simp⟩
  · exact h

theorem kinds_fetch (s : State) (h : Kinds s) : Kinds (fetch s) := by
  unfold fetch
  split
  · exact h
  · exact ⟨h.1,h.2.1,h.2.2.1,by simp,h.2.2.2.1⟩

theorem kinds_accept (s : State) (i : Pins) (h : Kinds s) : Kinds (accept s i) := by
  unfold accept
  split
  · rename_i hg
    have hd : (decode i.word).isSome = true := by simp_all [ready]
    exact ⟨h.1,h.2.1,h.2.2.1,by simpa using hd,h.2.2.2.2⟩
  · exact h

theorem kinds_cycle (s : State) (i : Pins) (h : Kinds s) : Kinds (cycle s i) := by
  cases hr : i.reset
  · simp only [cycle,hr,Bool.false_eq_true,↓reduceIte]
    change Kinds (if (commit s i.sw).fault != (0#3) then commit s i.sw else
      accept (fetch (dispatch (execute (memory (commit s i.sw) i.sm) i.sx i.delay) i.sd)) i)
    split
    · exact kinds_commit _ _ h
    · exact kinds_accept _ _ (kinds_fetch _ (kinds_dispatch _ _
        (kinds_execute _ _ _ (kinds_memory _ _ (kinds_commit _ _ h)))))
  · simpa [cycle,hr] using kinds_initial i.seed s.mem

#print axioms kinds_cycle
end CaseCPUMem.Raw
