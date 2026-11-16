import SourceRefinement
namespace CaseCPU.Bridge
open LeanRTL
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def PcInv (s : Raw) : Prop :=
  (s.wv = true → s.w.pc = s.pc) ∧
  (s.mv = true → s.m.pc = s.pc + (if s.wv then 4 else 0)) ∧
  (s.xv = true → s.x.pc = forwardPC s)

theorem pc_initial (seed : RF) : PcInv (rawInitial seed) := by simp [PcInv,rawInitial]
theorem pc_commit (s : Raw) (b : Bool) (h : PcInv s) : PcInv (commitRaw s b) := by
  unfold commitRaw
  split <;> simp_all [PcInv,forwardPC]

theorem pc_memory (s : Raw) (b : Bool) (h : PcInv s) : PcInv (memoryRaw s b) := by
  unfold memoryRaw
  split <;> simp_all [PcInv,forwardPC]

theorem pc_execute (s : Raw) (b : Bool) (h : PcInv s) : PcInv (executeRaw s b) := by
  unfold executeRaw
  split <;> try exact h
  split <;> try simpa [PcInv,forwardPC] using h
  split <;> simp_all [PcInv,forwardPC]

theorem pc_dispatch (s : Raw) (b : Bool) (h : PcInv s) : PcInv (dispatchRaw s b) := by
  unfold dispatchRaw
  split <;> simp_all [PcInv,forwardPC]

theorem pc_fetch (s : Raw) (h : PcInv s) : PcInv (fetchRaw s) := by
  unfold fetchRaw
  split <;> simpa [PcInv,forwardPC] using h

theorem pc_accept (s : Raw) (i : Pins) (h : PcInv s) : PcInv (acceptRaw s i).1 := by
  unfold acceptRaw
  split <;> simpa [PcInv,forwardPC] using h

theorem pc_cycle (s : Raw) (i : Pins) (h : PcInv s) : PcInv (rawCycle s i) := by
  unfold rawCycle
  split
  · exact pc_initial _
  · exact pc_accept _ _ (pc_fetch _ (pc_dispatch _ _
      (pc_execute _ _ (pc_memory _ _ (pc_commit _ _ h)))))

theorem pc_run (s : Raw) (xs : List Pins) (h : PcInv s) : PcInv (rawRun s xs) := by
  induction xs generalizing s with
  | nil => exact h
  | cons i xs ih => exact ih _ (pc_cycle _ _ h)

theorem rtl_pc_inv (r : Env) (i : Pins) (o : Env) (xs : List (Pins × Env))
    (hr : i.reset = true) : PcInv (rawOf (rtlRun (rtlStep r i o) xs)) := by
  have h0 := rtl_reset r i o hr
  rw [rtl_run_refines _ _ (by rw [h0]; exact legal_initial _),h0]
  exact pc_run _ _ (pc_initial _)

#print axioms pc_cycle
#print axioms rtl_pc_inv
end CaseCPU.Bridge
