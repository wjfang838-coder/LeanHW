import MemRefinement
namespace CaseCPUMem
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def packetInstructions (p : Option Packet) : List Instr := p.toList.map (·.instr)
def pending (s : Pipe) : List Instr :=
  packetInstructions s.writeback ++ packetInstructions s.memory ++
  packetInstructions s.execute ++ s.decodeStage.toList ++ s.fetch.toList

def retireAborted (s : Pipe) (b : Bool) : List Instr :=
  if b then [] else match s.writeback with
    | none => []
    | some p => if p.effect.fault != (0#3) then
        packetInstructions s.memory ++ packetInstructions s.execute ++
          s.decodeStage.toList ++ s.fetch.toList else []

theorem retire_order (s : Pipe) (b : Bool) :
    (retire s b).2.toList ++ retireAborted s b ++ pending (retire s b).1 = pending s := by
  cases b <;> cases hw : s.writeback <;>
    simp [retire,retireAborted,pending,packetInstructions,hw,List.append_assoc]
  split <;> simp_all [pending,packetInstructions,List.append_assoc]

theorem memory_order (s : Pipe) (b : Bool) : pending (moveMemory s b) = pending s := by
  cases b <;> by_cases hc : s.memoryWait > 0 <;>
    cases hw : s.writeback <;> cases hm : s.memory <;>
    simp [moveMemory,pending,packetInstructions,hc,hw,hm,List.append_assoc]

theorem execute_order (s : Pipe) (b : Bool) (d : BitVec 4) : pending (moveExecute s b d) = pending s := by
  cases b <;> by_cases hc : s.remaining > 0 <;>
    cases hm : s.memory <;> cases hx : s.execute <;>
    simp [moveExecute,pending,packetInstructions,hc,hm,hx,List.append_assoc]

theorem dispatch_order (s : Pipe) (b : Bool) : pending (dispatch s b) = pending s := by
  cases b <;> cases hx : s.execute <;> cases hd : s.decodeStage <;>
    simp [dispatch,pending,packetInstructions,hx,hd,List.append_assoc]
  split <;> simp_all [pending,packetInstructions,List.append_assoc]

theorem fetch_order (s : Pipe) : pending (moveFetch s) = pending s := by
  cases hd : s.decodeStage <;> cases hf : s.fetch <;>
    simp [moveFetch,pending,hd,hf,List.append_assoc]

def acceptedInstruction (i : Input) (b : Bool) : List Instr :=
  if b then (decode i.word).toList else []

theorem accept_order (s : Pipe) (i : Input) :
    pending (accept s i).1 = pending s ++ acceptedInstruction i (accept s i).2 := by
  unfold accept
  split
  · simp [acceptedInstruction]
  · cases hf : s.fetch <;> cases hd : decode i.word <;>
      simp [pending,acceptedInstruction,hf,hd,List.append_assoc]

def aborted (s : Pipe) (i : Input) : List Instr :=
  if i.reset then pending s else retireAborted s i.sw

/-- Every accepted instruction has a unique FIFO place: retired, explicitly
    aborted by reset/trap, or still pending. No fairness or drain assumption. -/
theorem cycle_conservation (s : Pipe) (i : Input) :
    (cycle s i).retired.toList ++ aborted s i ++ pending (cycle s i).state =
      pending s ++ acceptedInstruction i (cycle s i).accepted := by
  cases hi : i.reset
  · have ho := retire_order s i.sw
    generalize he : retire s i.sw = ev at ho ⊢
    cases ev with | mk s1 retired =>
      simp only [cycle,hi,Bool.false_eq_true,↓reduceIte,he,aborted]
      split
      · simpa [acceptedInstruction] using ho
      · simp only []
        rw [accept_order,fetch_order,dispatch_order,execute_order,memory_order]
        simpa only [List.append_assoc] using congrArg
          (fun q => q ++ acceptedInstruction i
            (accept (moveFetch (dispatch (moveExecute (moveMemory s1 i.sm) i.sx i.memoryDelay) i.sd)) i).2) ho
  · simp [cycle,hi,aborted,initialPipe,pending,packetInstructions,acceptedInstruction]

def completed (s : Pipe) (i : Input) : List Instr :=
  (cycle s i).retired.toList ++ aborted s i

def completions : Pipe → List Input → List Instr
  | _,[] => []
  | s,i::xs => completed s i ++ completions (cycle s i).state xs

def acceptances : Pipe → List Input → List Instr
  | _,[] => []
  | s,i::xs => acceptedInstruction i (cycle s i).accepted ++ acceptances (cycle s i).state xs

theorem trace_conservation (s : Pipe) (xs : List Input) :
    completions s xs ++ pending (run s xs) = pending s ++ acceptances s xs := by
  induction xs generalizing s with
  | nil => simp [completions,run,acceptances]
  | cons i xs ih =>
    simp only [completions,run,acceptances,List.append_assoc]
    rw [ih]
    have hc := cycle_conservation s i
    change completed s i ++ pending (cycle s i).state = _ at hc
    rw [←List.append_assoc,hc,List.append_assoc]

theorem isaRun_append (a : Arch) (xs ys : List Instr) :
    isaRun a (xs ++ ys) = isaRun (isaRun a xs) ys := by
  induction xs generalizing a with
  | nil => rfl
  | cons x xs ih => simpa only [List.cons_append,isaRun] using ih (isaStep a x)

theorem isaRun_halted (a : Arch) (xs : List Instr) (h : a.fault ≠ (0#3)) : isaRun a xs = a := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp [isaRun,isaStep,applyEffect,h,ih]

theorem retire_aborts_halted (s : Pipe) (b : Bool) (h : retireAborted s b ≠ []) :
    (retire s b).1.arch.fault ≠ (0#3) := by
  cases b
  · cases hw : s.writeback
    · simp [retireAborted,hw] at h
    · rename_i p
      by_cases hf : p.effect.fault = (0#3)
      · simp [retireAborted,hw,hf] at h
      · by_cases ha : s.arch.fault = (0#3) <;> simp [retire,hw,hf,applyEffect,ha]
  · simp [retireAborted] at h

theorem cycle_arch_retire (s : Pipe) (i : Input) (hi : i.reset = false) :
    (cycle s i).state.arch = (retire s i.sw).1.arch := by
  simp only [cycle,hi,Bool.false_eq_true,↓reduceIte]
  generalize he : retire s i.sw = ev
  cases ev with | mk s1 event =>
    split
    · rfl
    · simp only [accept_arch,fetch_arch,dispatch_arch,execute_arch,memory_arch]

theorem cycle_isa_completed (s : Pipe) (i : Input) (h : Inv s) (hi : i.reset = false) :
    (cycle s i).state.arch = isaRun s.arch (completed s i) := by
  have he : (cycle s i).state.arch = isaRun s.arch (cycle s i).retired.toList := by
    have hr := cycle_refines s i h
    rw [hi] at hr
    cases hh : (cycle s i).retired <;> simpa [transaction,isaRun,hh] using hr
  rw [completed,isaRun_append,←he]
  by_cases ha : aborted s i = []
  · simp [ha,isaRun]
  · symm
    apply isaRun_halted
    rw [cycle_arch_retire s i hi]
    exact retire_aborts_halted s i.sw (by simpa [aborted,hi] using ha)

theorem trace_isa_completed (s : Pipe) (xs : List Input) (h : Inv s)
    (hn : ∀ i ∈ xs, i.reset = false) :
    (run s xs).arch = isaRun s.arch (completions s xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih =>
    have hi := hn i (by simp)
    have ht : ∀ j ∈ xs, j.reset = false := fun j hj => hn j (by simp [hj])
    simp only [run,completions,isaRun_append]
    rw [ih _ (cycle_inv s i h) ht,←cycle_isa_completed s i h hi]

/-- Draining, including a precise halt that aborts younger work, executes the
    accepted program. The halted ISA makes instructions after the fault no-ops. -/
theorem drained_refinement (rf : Reg → Word) (mem : Memory) (xs : List Input)
    (hn : ∀ i ∈ xs, i.reset = false)
    (hd : pending (run (initialPipe rf mem) xs) = []) :
    (run (initialPipe rf mem) xs).arch =
      isaRun (initial rf mem) (acceptances (initialPipe rf mem) xs) := by
  have hc := trace_conservation (initialPipe rf mem) xs
  rw [hd,List.append_nil] at hc
  have he : completions (initialPipe rf mem) xs = acceptances (initialPipe rf mem) xs := by
    simpa [initialPipe,pending,packetInstructions] using hc
  rw [trace_isa_completed _ xs (initial_inv rf mem) hn,he]
  rfl

#print axioms cycle_conservation
#print axioms trace_conservation
#print axioms drained_refinement
end CaseCPUMem
