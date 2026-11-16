import MemWordRefinement
namespace CaseCPUMem.Raw
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

def PCs (s : State) : Prop :=
  (s.wv = true → s.w.pc = s.pc) ∧
  (s.mv = true → s.m.pc = s.pc+(if s.wv then 4 else 0)) ∧
  (s.xv = true → s.x.pc = s.pc+(if s.wv then 4 else 0)+(if s.mv then 4 else 0))

def ZeroValue (p : Packet) : Prop :=
  (isStore (instr p.word).op || (instr p.word).op == .fence || p.fault != (0#3)) = true → p.value = 0

def Zeros (s : State) : Prop :=
  (s.wv = true → ZeroValue s.w) ∧ (s.mv = true → ZeroValue s.m) ∧ (s.xv = true → ZeroValue s.x)

def Metadata (s : State) : Prop := PCs s ∧ Zeros s

@[simp] theorem finish_pc (m : Memory) (p : Packet) : (finish m p).pc = p.pc := by
  unfold finish
  split <;> rfl

theorem zero_finish (m : Memory) (p : Packet) (h : ZeroValue p) : ZeroValue (finish m p) := by
  by_cases hf : p.fault = (0#3)
  · cases ho : (instr p.word).op <;> simpa [ZeroValue,finish,hf,ho,isLoad,isStore] using h
  · simpa [finish,hf] using h

theorem zero_issue (s : State) (w : Word) : ZeroValue (issue s w) := by
  cases ho : (instr w).op <;> simp [ZeroValue,issue,ho,isStore]

theorem metadata_initial (seed : CaseCPU.Bridge.RF) (m : Memory) : Metadata (initial seed m) := by
  simp [Metadata,PCs,Zeros,initial]

theorem metadata_commit (s : State) (b : Bool) (h : Metadata s) : Metadata (commit s b) := by
  rcases h with ⟨⟨hw,hm,hx⟩,⟨zw,zm,zx⟩⟩
  cases hb : b <;> cases hv : s.wv
  all_goals by_cases hf : s.w.fault = (0#3)
  all_goals simp_all [Metadata,PCs,Zeros,commit]

theorem metadata_memory (s : State) (b : Bool) (h : Metadata s) : Metadata (memory s b) := by
  rcases h with ⟨⟨hw,hm,hx⟩,⟨zw,zm,zx⟩⟩
  have hf : s.mv = true → ZeroValue (finish s.mem s.m) := fun hh => zero_finish _ _ (zm hh)
  cases hb : b
  all_goals by_cases hc : s.waitCount = (0#4)
  all_goals cases hv : s.wv
  all_goals cases hm' : s.mv
  all_goals simp_all [Metadata,PCs,Zeros,memory]

theorem metadata_execute (s : State) (b : Bool) (delay : BitVec 4) (h : Metadata s) :
    Metadata (execute s b delay) := by
  rcases h with ⟨⟨hw,hm,hx⟩,⟨zw,zm,zx⟩⟩
  cases hb : b
  all_goals by_cases hc : s.count = (0#6)
  all_goals cases hm' : s.mv
  all_goals simp_all [Metadata,PCs,Zeros,execute]

theorem metadata_dispatch (s : State) (b : Bool) (h : Metadata s) : Metadata (dispatch s b) := by
  rcases h with ⟨⟨hw,hm,hx⟩,⟨zw,zm,zx⟩⟩
  have hz := zero_issue s s.di
  have hp : (issue s s.di).pc = forwardPC s := by
    cases ho : (instr s.di).op <;> simp [issue,ho]
  unfold dispatch
  split
  · simp_all [Metadata,PCs,Zeros,forwardPC]
  · exact ⟨⟨hw,hm,hx⟩,zw,zm,zx⟩

theorem metadata_fetch (s : State) (h : Metadata s) : Metadata (fetch s) := by
  unfold fetch
  split <;> exact h

theorem metadata_accept (s : State) (i : Pins) (h : Metadata s) : Metadata (accept s i) := by
  unfold accept
  split <;> exact h

theorem metadata_cycle (s : State) (i : Pins) (h : Metadata s) : Metadata (cycle s i) := by
  cases hr : i.reset
  · simp only [cycle,hr,Bool.false_eq_true,↓reduceIte]
    split
    · exact metadata_commit s i.sw h
    · exact metadata_accept _ _ (metadata_fetch _ (metadata_dispatch _ _
        (metadata_execute _ _ _ (metadata_memory _ _ (metadata_commit s i.sw h)))))
  · simpa [cycle,hr] using metadata_initial i.seed s.mem

theorem metadata_run (s : State) (xs : List Pins) (h : Metadata s) : Metadata (run s xs) := by
  induction xs generalizing s with
  | nil => exact h
  | cons i xs ih => exact ih (cycle s i) (metadata_cycle s i h)

#print axioms metadata_run
end CaseCPUMem.Raw
