import MemPipeline
namespace CaseCPUMem
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def checked (a : Arch) : Option Packet → Prop
  | none => True
  | some p => p.effect = effectFor a p.instr

def Inv (s : Pipe) : Prop :=
  checked s.arch s.writeback ∧
  checked (advance s.arch s.writeback) s.memory ∧
  checked (forwarded s) s.execute

theorem initial_inv (rf : Reg → Word) (m : Memory) : Inv (initialPipe rf m) := by
  simp [Inv,initialPipe,checked,forwarded,advance]

theorem retire_inv (s : Pipe) (b : Bool) (h : Inv s) : Inv (retire s b).1 := by
  cases b <;> cases hw : s.writeback <;>
    simp only [retire,hw,Bool.false_eq_true,↓reduceIte]
    <;> try exact h
  split
  · simp [Inv,checked,forwarded,advance]
  · rcases h with ⟨h1,h2,h3⟩
    simp_all [Inv,checked,forwarded,advance]

theorem memory_inv (s : Pipe) (b : Bool) (h : Inv s) : Inv (moveMemory s b) := by
  rcases h with ⟨h1,h2,h3⟩
  cases b <;> by_cases hn : 0 < s.memoryWait <;>
    cases hw : s.writeback <;> cases hm : s.memory <;>
    simp_all [moveMemory,Inv,checked,forwarded,advance]

theorem execute_inv (s : Pipe) (b : Bool) (d : BitVec 4) (h : Inv s) :
    Inv (moveExecute s b d) := by
  cases b <;> by_cases hn : 0 < s.remaining <;>
    cases hw : s.writeback <;> cases hm : s.memory <;> cases he : s.execute <;>
    simp_all [moveExecute,Inv,checked,forwarded,advance]

theorem dispatch_inv (s : Pipe) (b : Bool) (h : Inv s) : Inv (dispatch s b) := by
  cases b <;> cases he : s.execute <;> cases hd : s.decodeStage <;>
    simp only [dispatch,he,hd,Bool.false_eq_true,↓reduceIte]
    <;> try exact h
  split
  · exact h
  · rcases h with ⟨h1,h2,h3⟩
    simp_all [Inv,checked,forwarded,advance]

theorem fetch_inv (s : Pipe) (h : Inv s) : Inv (moveFetch s) := by
  cases hd : s.decodeStage <;> simpa [moveFetch,hd,Inv,forwarded] using h

theorem accept_inv (s : Pipe) (i : Input) (h : Inv s) : Inv (accept s i).1 := by
  unfold accept
  split
  · exact h
  · cases hf : s.fetch <;> cases hd : decode i.word <;> simpa [Inv,forwarded] using h

theorem cycle_inv (s : Pipe) (i : Input) (h : Inv s) : Inv (cycle s i).state := by
  cases hz : i.reset
  · cases hr : retire s i.sw with
    | mk s1 retired =>
      have h1 : Inv s1 := by simpa only [hr] using retire_inv s i.sw h
      simp only [cycle,hz,Bool.false_eq_true,↓reduceIte,hr]
      split
      · exact h1
      · exact accept_inv _ _ (fetch_inv _ (dispatch_inv _ _
          (execute_inv _ _ _ (memory_inv _ _ h1))))
  · simpa [cycle,hz] using initial_inv i.initRegs s.arch.mem

def transaction (a : Arch) : Option Instr → Arch
  | none => a
  | some ins => isaStep a ins

theorem retire_refines (s : Pipe) (b : Bool) (h : Inv s) :
    (retire s b).1.arch = transaction s.arch (retire s b).2 := by
  cases b <;> cases hw : s.writeback <;>
    simp only [retire,hw,Bool.false_eq_true,↓reduceIte]
    <;> try rfl
  split <;> simp_all [transaction,Inv,checked,isaStep]

@[simp] theorem memory_arch (s : Pipe) (b : Bool) : (moveMemory s b).arch = s.arch := by
  cases b <;> by_cases hn : 0 < s.memoryWait <;> cases hw : s.writeback <;>
    simp [moveMemory,hw,hn]

@[simp] theorem execute_arch (s : Pipe) (b : Bool) (d : BitVec 4) :
    (moveExecute s b d).arch = s.arch := by
  unfold moveExecute
  split <;> try rfl
  split <;> try rfl
  cases s.memory <;> rfl

@[simp] theorem dispatch_arch (s : Pipe) (b : Bool) : (dispatch s b).arch = s.arch := by
  cases b <;> cases he : s.execute <;> cases hd : s.decodeStage <;>
    simp only [dispatch,he,hd,Bool.false_eq_true,↓reduceIte]
    <;> try rfl
  split <;> rfl

@[simp] theorem fetch_arch (s : Pipe) : (moveFetch s).arch = s.arch := by
  cases hd : s.decodeStage <;> simp [moveFetch,hd]

@[simp] theorem accept_arch (s : Pipe) (i : Input) : (accept s i).1.arch = s.arch := by
  unfold accept
  split <;> try rfl
  cases s.fetch <;> cases decode i.word <;> rfl

theorem cycle_refines (s : Pipe) (i : Input) (h : Inv s) :
    (cycle s i).state.arch = if i.reset then initial i.initRegs s.arch.mem
      else transaction s.arch (cycle s i).retired := by
  cases hz : i.reset
  · cases hr : retire s i.sw with
    | mk s1 retired =>
      have ha : s1.arch = transaction s.arch retired := by
        simpa only [hr] using retire_refines s i.sw h
      simp only [cycle,hz,Bool.false_eq_true,↓reduceIte,hr]
      split <;> simp only [accept_arch,fetch_arch,dispatch_arch,execute_arch,memory_arch]
      · exact ha
      · exact ha
  · simp [cycle,hz,initialPipe]

def run : Pipe → List Input → Pipe
  | s,[] => s
  | s,i::xs => run (cycle s i).state xs

def reference : Pipe → Arch → List Input → Arch
  | _,a,[] => a
  | s,a,i::xs =>
    let out := cycle s i
    let a' := if i.reset then initial i.initRegs a.mem else transaction a out.retired
    reference out.state a' xs

theorem run_inv (s : Pipe) (xs : List Input) (h : Inv s) : Inv (run s xs) := by
  induction xs generalizing s with
  | nil => exact h
  | cons i xs ih => exact ih _ (cycle_inv _ _ h)

theorem full_refinement (s : Pipe) (xs : List Input) (h : Inv s) :
    (run s xs).arch = reference s s.arch xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih =>
    simp only [run,reference]
    rw [← cycle_refines s i h]
    exact ih _ (cycle_inv _ _ h)

theorem reset_refinement (rf : Reg → Word) (mem : Memory) (xs : List Input) :
    (run (initialPipe rf mem) xs).arch =
      reference (initialPipe rf mem) (initial rf mem) xs :=
  full_refinement _ _ (initial_inv _ _)

#print axioms cycle_inv
#print axioms cycle_refines
#print axioms reset_refinement
end CaseCPUMem
