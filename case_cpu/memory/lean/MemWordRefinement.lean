import MemRawBridge
namespace CaseCPUMem.Raw
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

def run : State → List Pins → State
  | s,[] => s
  | s,i::xs => run (cycle s i) xs

theorem run_valid (s : State) (xs : List Pins) (h : Valid s) : Valid (run s xs) := by
  induction xs generalizing s with
  | nil => exact h
  | cons i xs ih => exact ih _ (valid_cycle s i h)

theorem run_projects (s : State) (xs : List Pins) (h : Valid s) :
    project (run s xs) = CaseCPUMem.run (project s) (xs.map input) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i xs ih =>
    simp only [run,List.map_cons,CaseCPUMem.run,ih _ (valid_cycle s i h),project_cycle s i h]

/-- Register-shaped deferred-load model to cycle model. This is NOT a claim
    that the separate imported RTL already implements the register-shaped model. -/
theorem word_cycle_refinement (seed : CaseCPU.Bridge.RF) (mem : Memory) (xs : List Pins) :
    project (run (initial seed mem) xs) =
      CaseCPUMem.run (initialPipe (CaseCPU.Bridge.readRF seed) mem) (xs.map input) := by
  rw [run_projects _ _ (valid_initial _ _),project_initial]

theorem word_isa_refinement (seed : CaseCPU.Bridge.RF) (mem : Memory) (xs : List Pins) :
    (project (run (initial seed mem) xs)).arch =
      reference (initialPipe (CaseCPU.Bridge.readRF seed) mem)
        (CaseCPUMem.initial (CaseCPU.Bridge.readRF seed) mem) (xs.map input) := by
  rw [word_cycle_refinement]
  exact reset_refinement _ _ _

#print axioms word_cycle_refinement
#print axioms word_isa_refinement
end CaseCPUMem.Raw
