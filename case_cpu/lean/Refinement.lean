import Pipeline

namespace CaseCPU
set_option maxRecDepth 4096
set_option linter.unusedSimpArgs false

def checked (a : Arch) : Option Packet → Prop
  | none => True
  | some p => p.effect = effectFor a p.instr

/-- The invariant relates actual stored results to the ISA in program order.
    It does not assume retirement correctness or bound stalls/trace length. -/
def Inv (s : Pipe) : Prop :=
  checked s.arch s.writeback ∧
  checked (advance s.arch s.writeback) s.memory ∧
  checked (forwarded s) s.execute

theorem initial_inv (rf : Reg → Word) : Inv (initial rf) := by
  simp [Inv, initial, checked, forwarded, advance]

theorem retire_inv (s : Pipe) (stall : Bool) (h : Inv s) : Inv (retire s stall).1 := by
  rcases h with ⟨h1, h2, h3⟩
  cases stall <;> cases hw : s.writeback <;>
    simp_all [retire, Inv, checked, forwarded, advance]

theorem memory_inv (s : Pipe) (stall : Bool) (h : Inv s) : Inv (moveMemory s stall) := by
  rcases h with ⟨h1, h2, h3⟩
  cases stall <;> cases hw : s.writeback <;> cases hm : s.memory <;>
    simp_all [moveMemory, Inv, checked, forwarded, advance]

theorem execute_inv (s : Pipe) (stall : Bool) (h : Inv s) : Inv (moveExecute s stall) := by
  rcases h with ⟨h1, h2, h3⟩
  cases stall <;> by_cases hn : s.remaining > 0 <;>
    cases hw : s.writeback <;> cases hm : s.memory <;> cases he : s.execute <;>
    simp_all [moveExecute, Inv, checked, forwarded, advance]

theorem dispatch_inv (s : Pipe) (stall : Bool) (h : Inv s) : Inv (dispatch s stall) := by
  rcases h with ⟨h1, h2, h3⟩
  cases stall <;> cases he : s.execute <;> cases hd : s.decodeStage <;>
    simp_all [dispatch, Inv, checked, forwarded, advance]

theorem fetch_inv (s : Pipe) (h : Inv s) : Inv (moveFetch s) := by
  cases hd : s.decodeStage <;> simpa [moveFetch, hd, Inv, forwarded] using h

theorem accept_inv (s : Pipe) (i : Input) (h : Inv s) : Inv (accept s i).1 := by
  unfold accept
  split
  · exact h
  · cases hf : s.fetch <;> cases hd : CaseCPU.decode i.word <;>
      simpa [Inv, forwarded] using h

theorem cycle_inv (s : Pipe) (i : Input) (h : Inv s) : Inv (cycle s i).state := by
  unfold cycle
  split
  · exact initial_inv _
  · exact accept_inv _ _ (fetch_inv _ (dispatch_inv _ _
      (execute_inv _ _ (memory_inv _ _ (retire_inv _ _ h)))))

def transaction (a : Arch) : Option Instr → Arch
  | none => a
  | some ins => isaStep a ins

theorem retire_refines (s : Pipe) (stall : Bool) (h : Inv s) :
    (retire s stall).1.arch = transaction s.arch (retire s stall).2 := by
  cases stall <;> cases hw : s.writeback <;>
    simp_all [retire, transaction, Inv, checked, isaStep]

@[simp] theorem memory_arch (s : Pipe) (b : Bool) : (moveMemory s b).arch = s.arch := by
  cases b <;> cases hw : s.writeback <;> simp [moveMemory, hw]
@[simp] theorem execute_arch (s : Pipe) (b : Bool) : (moveExecute s b).arch = s.arch := by
  unfold moveExecute
  split <;> try rfl
  split <;> try rfl
  cases s.memory <;> rfl
@[simp] theorem dispatch_arch (s : Pipe) (b : Bool) : (dispatch s b).arch = s.arch := by
  cases b <;> cases he : s.execute <;> cases hd : s.decodeStage <;> simp [dispatch, he, hd]
@[simp] theorem fetch_arch (s : Pipe) : (moveFetch s).arch = s.arch := by
  cases hd : s.decodeStage <;> simp [moveFetch, hd]
@[simp] theorem accept_arch (s : Pipe) (i : Input) : (accept s i).1.arch = s.arch := by
  unfold accept
  split <;> try rfl
  cases s.fetch <;> cases CaseCPU.decode i.word <;> rfl

/-- Non-reset cycles either stutter or perform exactly one ISA transaction. -/
theorem cycle_refines (s : Pipe) (i : Input) (h : Inv s) :
    (cycle s i).state.arch =
      if i.reset then (initial i.initRegs).arch
      else transaction s.arch (cycle s i).retired := by
  unfold cycle
  split <;> simp_all only [ite_true, ite_false]
  simp only [accept_arch, fetch_arch, dispatch_arch, execute_arch, memory_arch]
  exact retire_refines s i.stallWriteback h

def run : Pipe → List Input → Pipe
  | s, [] => s
  | s, i :: is => run (cycle s i).state is

/-- Reference state is computed independently from ISA transactions and reset events.
    Retirement events come from the implementation; separate schedule/order evidence is
    provided by pending_instructions and the acceptance conservation checks. -/
def reference : Pipe → Arch → List Input → Arch
  | _, a, [] => a
  | s, a, i :: is =>
    let o := cycle s i
    let a' := if i.reset then (initial i.initRegs).arch else transaction a o.retired
    reference o.state a' is

theorem run_inv (s : Pipe) (xs : List Input) (h : Inv s) : Inv (run s xs) := by
  induction xs generalizing s with
  | nil => exact h
  | cons i is ih => exact ih _ (cycle_inv s i h)

/-- Unbounded safety refinement: arbitrary words, reset seeds, and stall sequences.
    No fairness assumption is needed; this theorem makes no liveness claim. -/
theorem full_refinement (s : Pipe) (xs : List Input) (h : Inv s) :
    (run s xs).arch = reference s s.arch xs := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih =>
    simp only [run, reference]
    rw [← cycle_refines s i h]
    exact ih _ (cycle_inv s i h)

theorem reset_refinement (rf : Reg → Word) (xs : List Input) :
    (run (initial rf) xs).arch = reference (initial rf) (initial rf).arch xs :=
  full_refinement _ xs (initial_inv rf)

def packetInstructions (p : Option Packet) : List Instr := p.toList.map (·.instr)
def pending (s : Pipe) : List Instr :=
  packetInstructions s.writeback ++ packetInstructions s.memory ++
  packetInstructions s.execute ++ s.decodeStage.toList ++ s.fetch.toList

theorem retire_order (s : Pipe) (b : Bool) :
    (retire s b).2.toList ++ pending (retire s b).1 = pending s := by
  cases b <;> cases hw : s.writeback <;>
    simp [retire, pending, packetInstructions, hw, List.append_assoc]

theorem memory_order (s : Pipe) (b : Bool) : pending (moveMemory s b) = pending s := by
  cases b <;> cases hw : s.writeback <;> cases hm : s.memory <;>
    simp [moveMemory, pending, packetInstructions, hw, hm, List.append_assoc]

theorem execute_order (s : Pipe) (b : Bool) : pending (moveExecute s b) = pending s := by
  cases b <;> by_cases hn : s.remaining > 0 <;>
    cases hm : s.memory <;> cases he : s.execute <;>
    simp [moveExecute, pending, packetInstructions, hn, hm, he, List.append_assoc]

theorem dispatch_order (s : Pipe) (b : Bool) : pending (dispatch s b) = pending s := by
  cases b <;> cases he : s.execute <;> cases hd : s.decodeStage <;>
    simp [dispatch, pending, packetInstructions, he, hd, List.append_assoc]

theorem fetch_order (s : Pipe) : pending (moveFetch s) = pending s := by
  cases hd : s.decodeStage <;> cases hf : s.fetch <;>
    simp [moveFetch, pending, hd, hf, List.append_assoc]

def acceptedInstruction (i : Input) (b : Bool) : List Instr :=
  if b then (CaseCPU.decode i.word).toList else []

theorem accept_order (s : Pipe) (i : Input) :
    pending (accept s i).1 = pending s ++ acceptedInstruction i (accept s i).2 := by
  unfold accept
  split
  · simp [acceptedInstruction]
  · cases hf : s.fetch <;> cases hd : CaseCPU.decode i.word <;>
      simp [pending, acceptedInstruction, hf, hd, List.append_assoc]

/-- A reset discards the entire queue explicitly. Otherwise every accepted instruction
    is either still in flight or appears once, in order, at retirement. -/
theorem cycle_conservation (s : Pipe) (i : Input) (h : i.reset = false) :
    (cycle s i).retired.toList ++ pending (cycle s i).state =
      pending s ++ acceptedInstruction i (cycle s i).accepted := by
  simp only [cycle, h, Bool.false_eq_true, ↓reduceIte]
  rw [accept_order, ← List.append_assoc, fetch_order, dispatch_order,
    execute_order, memory_order, retire_order]

def retirements : Pipe → List Input → List Instr
  | _, [] => []
  | s, i :: is => (cycle s i).retired.toList ++ retirements (cycle s i).state is

def acceptances : Pipe → List Input → List Instr
  | _, [] => []
  | s, i :: is => acceptedInstruction i (cycle s i).accepted ++ acceptances (cycle s i).state is

theorem trace_conservation (s : Pipe) (xs : List Input)
    (hn : ∀ i ∈ xs, i.reset = false) :
    retirements s xs ++ pending (run s xs) = pending s ++ acceptances s xs := by
  induction xs generalizing s with
  | nil => simp [retirements, run, acceptances]
  | cons i is ih =>
    have hi := hn i (by simp)
    have ht : ∀ j ∈ is, j.reset = false := fun j hj => hn j (by simp [hj])
    simp only [retirements, run, acceptances, List.append_assoc]
    rw [ih _ ht, ← List.append_assoc, cycle_conservation s i hi, List.append_assoc]

theorem trace_isa (s : Pipe) (xs : List Input) (h : Inv s)
    (hn : ∀ i ∈ xs, i.reset = false) :
    (run s xs).arch = isaRun s.arch (retirements s xs) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i is ih =>
    have hi := hn i (by simp)
    have ht : ∀ j ∈ is, j.reset = false := fun j hj => hn j (by simp [hj])
    simp only [run, retirements]
    rw [ih _ (cycle_inv s i h) ht, cycle_refines s i h, hi]
    cases hr : (cycle s i).retired <;> simp [transaction, isaRun]

/-- Once drained, execute exactly the accepted program. This combines arithmetic safety
    with acceptance/order conservation, so selecting retirement events cannot hide loss. -/
theorem drained_refinement (rf : Reg → Word) (xs : List Input)
    (hn : ∀ i ∈ xs, i.reset = false)
    (hd : pending (run (initial rf) xs) = []) :
    (run (initial rf) xs).arch = isaRun (initial rf).arch (acceptances (initial rf) xs) := by
  have hc := trace_conservation (initial rf) xs hn
  rw [hd, List.append_nil] at hc
  have he : retirements (initial rf) xs = acceptances (initial rf) xs := by
    simpa [pending, packetInstructions, initial] using hc
  rw [trace_isa _ xs (initial_inv rf) hn, he]

#print axioms cycle_conservation
#print axioms trace_conservation
#print axioms trace_isa
#print axioms drained_refinement

#print axioms cycle_inv
#print axioms cycle_refines
#print axioms full_refinement
#print axioms reset_refinement
end CaseCPU
