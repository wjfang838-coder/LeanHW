import NetlistStep
import DispatchCircuit
import AcceptCircuit
namespace CaseCPU.Bridge
open LeanRTL CPUShallow
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem before_accept_state (b : Env) (hr : (pinsOf b).reset = false)
    (h : Legal (rawOf b)) : postFetch b = beforeAccept (rawOf b) (pinsOf b) := by
  have hc := commit_state b hr h.2.2.2.2
  have he : Legal (postExecute b) := by
    rw [execute_state,memory_state,hc]
    exact legal_execute _ _ (legal_memory _ _ (legal_commit _ _ h))
  rw [fetch_state,dispatch_state b he,execute_state,memory_state,hc]
  rfl

theorem source_cycle (b : Env) (h : Legal (rawOf b)) :
    netNext b = rawCycle (rawOf b) (pinsOf b) := by
  cases hr : (pinsOf b).reset
  · have hc := commit_state b hr h.2.2.2.2
    have he : Legal (postExecute b) := by
      rw [execute_state,memory_state,hc]
      exact legal_execute _ _ (legal_memory _ _ (legal_commit _ _ h))
    rw [accept_state b hr,fetch_state,dispatch_state b he,execute_state,memory_state,hc]
    simp only [rawCycle,hr,Bool.false_eq_true,↓reduceIte,beforeAccept]
  · rw [reset_state b hr]
    simp only [rawCycle,hr,↓reduceIte]

theorem rtl_step_refines (r : Env) (i : Pins) (o : Env) (h : Legal (rawOf r)) :
    rawOf (rtlStep r i o) = rawCycle (rawOf r) i := by
  rw [actual_step,source_cycle _ (by simpa only [base_raw] using h),base_raw,base_pins]

theorem rtl_reset (r : Env) (i : Pins) (o : Env) (h : i.reset = true) :
    rawOf (rtlStep r i o) = rawInitial i.seed := by
  rw [actual_step,reset_state _ (by simpa only [base_pins] using h),base_pins]

theorem rtl_run_refines (r : Env) (xs : List (Pins × Env)) (h : Legal (rawOf r)) :
    rawOf (rtlRun r xs) = rawRun (rawOf r) (xs.map Prod.fst) := by
  induction xs generalizing r with
  | nil => rfl
  | cons io xs ih =>
    have hn : Legal (rawOf (rtlStep r io.1 io.2)) := by
      rw [rtl_step_refines r io.1 io.2 h]
      exact legal_cycle _ _ h
    simp only [rtlRun,List.map_cons,rawRun,ih _ hn,rtl_step_refines _ _ _ h]

/-- First refinement level: the actual imported RTL refines the frozen cycle spec.
    Arbitrary inputs, all five stalls, repeated resets, and all undefined-value choices.
    No one-step equivalence hypothesis is supplied to this theorem. -/
theorem rtl_cycle_refinement (r : Env) (i : Pins) (o : Env)
    (xs : List (Pins × Env)) (hr : i.reset = true) :
    project (rawOf (rtlRun (rtlStep r i o) xs)) =
      run (initial (readRF i.seed)) (xs.map (fun x => specInput x.1)) := by
  have h0 := rtl_reset r i o hr
  rw [rtl_run_refines _ _ (by rw [h0]; exact legal_initial _),h0,projected_run,project_initial]
  simp only [List.map_map,Function.comp_def]

/-- Both refinement levels composed: real imported RTL -> cycle spec -> ISA.
    The reference restarts the architecture on any later synchronous reset. -/
theorem rtl_isa_refinement (r : Env) (i : Pins) (o : Env)
    (xs : List (Pins × Env)) (hr : i.reset = true) :
    (project (rawOf (rtlRun (rtlStep r i o) xs))).arch =
      reference (initial (readRF i.seed)) (initial (readRF i.seed)).arch
        (xs.map (fun x => specInput x.1)) := by
  rw [rtl_cycle_refinement r i o xs hr]
  exact reset_refinement _ _

#print axioms rtl_step_refines
#print axioms rtl_cycle_refinement
#print axioms rtl_isa_refinement
end CaseCPU.Bridge
