import SpecIR

/-! Compile-time checks for the unbounded T10/T11 APIs. -/

namespace SpecIR.FormalDemo

structure In where
  opcode : Nat

def machine : Machine Unit In where
  init := ()
  step := fun _ _ => ()
  out := fun _ i =>
    [("read", Val.mk 1 (if i.opcode == 3 then 1 else 0)),
     ("write", Val.mk 1 (if i.opcode == 35 then 1 else 0))]

theorem complete : GlobalComplete machine := by
  intro s i
  simp [machine, OutputsDetermined, Val.mk]

def readOnLoad : FormalProperty Unit In where
  id := "read-on-load"
  className := "output relationship"
  sources := ["A load reads memory."]
  statement := fun m => ∀ s i, i.opcode = 3 →
    outputValue? (m.out s i) "read" = some (Val.mk 1 1)
  nonvacuous := fun _ => ∃ i : In, i.opcode = 3

theorem readOnLoad_proved : readOnLoad.Holds machine := by
  intro s i h
  simp [machine, outputValue?, h]

theorem readOnLoad_nonvacuous : readOnLoad.Nonvacuous machine := by
  exact ⟨{ opcode := 3 }, rfl⟩

end SpecIR.FormalDemo
