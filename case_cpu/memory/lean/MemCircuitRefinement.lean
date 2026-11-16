import MemDispatchRelation
import MemFrontCircuit
import MemWordRefinement
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

theorem reset_ram (s : NativeMemory.State) (i : Raw.Pins) (o : Env) (hr : i.reset = true) :
    (rtlStep s i o).arrays = s.arrays := by
  apply NativeRAM.actual_reset_preserves_ram
  simp [pinEnv,Env.lookup,hr]

theorem boot_related (s : NativeMemory.State) (seed : CaseCPU.Bridge.RF) (o : Env) :
    Related (physical (rtlStep s {reset := true,seed := seed} o).regs)
      (NativeRAM.ramView (rtlStep s {reset := true,seed := seed} o).arrays)
      (Raw.initial seed (NativeRAM.ramView s.arrays)) := by
  rw [actual_state,net_reset _ (by rw [bound_pins]),bound_pins,reset_ram _ _ _ rfl]
  exact reset_related seed (NativeRAM.ramView s.arrays)

theorem circuit_cycle_refinement (s : NativeMemory.State) (i : Raw.Pins) (o : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q) :
    Related (physical (rtlStep s i o).regs) (NativeRAM.ramView (rtlStep s i o).arrays)
      (Raw.cycle q i) := by
  let b := NativeRAM.combInput s (pinEnv i o)
  have hp : pins b = i := bound_pins s i o
  rw [actual_state]
  cases hr : i.reset
  · have hr' : (pins b).reset = false := by rw [hp,hr]
    have hc := commit_refinement s (pinEnv i o) q h hv hr'
    by_cases hz : V_next_fault b = (0#3)
    · have hx := execute_refinement s (pinEnv i o) q h hv hr' hz
      have hk := execute_kinds q i hv
      have hd := dispatch_related b (beforeDispatch q (pins b))
        (NativeRAM.ramView (rtlStep s i o).arrays) hx (by simpa only [hp] using hk) hz
      have hf := fetch_related _ _ _ hd
      have ha := accept_related _ _ _ (pins b) hf
      rw [net_running b hr' hz]
      rw [←fetch_state b hz,←accept_state b hz] at ha
      have hcf : (Raw.commit q i.sw).fault = (0#3) := by
        have hh := hc.fault
        change V_next_fault b = (Raw.commit q (pins b).sw).fault at hh
        rw [←hp]
        exact hh.symm.trans hz
      simpa only [hp,Raw.cycle,hr,Bool.false_eq_true,↓reduceIte,hcf,bne_self_eq_false,
        beforeDispatch] using ha
    · rw [net_halted b hr' hz]
      have hcf : (Raw.commit q i.sw).fault ≠ (0#3) := by
        have hh := hc.fault
        change V_next_fault b = (Raw.commit q (pins b).sw).fault at hh
        rw [hp] at hh
        exact fun hf => hz (hh.trans hf)
      simpa [Raw.cycle,hr,hcf,bound_pins] using hc
  · rw [net_reset _ (by rw [bound_pins,hr]),bound_pins]
    have hm : (rtlStep s i o).arrays = s.arrays := reset_ram s i o hr
    rw [hm]
    simpa [Raw.cycle,hr,h.ram] using reset_related i.seed (NativeRAM.ramView s.arrays)

noncomputable def circuitRun : NativeMemory.State → List (Raw.Pins × Env) → NativeMemory.State
  | s,[] => s
  | s,(i,o)::xs => circuitRun (rtlStep s i o) xs

theorem circuit_run_related (s : NativeMemory.State) (q : Raw.State) (xs : List (Raw.Pins × Env))
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q) :
    Related (physical (circuitRun s xs).regs) (NativeRAM.ramView (circuitRun s xs).arrays)
      (Raw.run q (xs.map Prod.fst)) := by
  induction xs generalizing s q with
  | nil => exact h
  | cons x xs ih =>
    exact ih (rtlStep s x.1 x.2) (Raw.cycle q x.1)
      (circuit_cycle_refinement s x.1 x.2 q h hv) (Raw.valid_cycle q x.1 hv)

def architecture (s : NativeMemory.State) : Arch :=
  ⟨CaseCPU.Bridge.readRF (physical s.regs).rf,(physical s.regs).pc,
    NativeRAM.ramView s.arrays,(physical s.regs).fault⟩

theorem related_architecture (s : NativeMemory.State) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) :
    architecture s = (Raw.project q).arch := by
  simp only [architecture,Raw.project,h.rf,h.pc,h.ram,h.fault]

theorem rtl_isa_refinement (s : NativeMemory.State) (seed : CaseCPU.Bridge.RF) (o : Env)
    (xs : List (Raw.Pins × Env)) :
    architecture (circuitRun (rtlStep s {reset := true,seed := seed} o) xs) =
      reference (initialPipe (CaseCPU.Bridge.readRF seed) (NativeRAM.ramView s.arrays))
        (initial (CaseCPU.Bridge.readRF seed) (NativeRAM.ramView s.arrays))
        ((xs.map Prod.fst).map Raw.input) := by
  have h := circuit_run_related _ _ xs (boot_related s seed o) (Raw.valid_initial _ _)
  rw [related_architecture _ _ h]
  exact Raw.word_isa_refinement seed (NativeRAM.ramView s.arrays) (xs.map Prod.fst)

#print axioms circuit_cycle_refinement
#print axioms rtl_isa_refinement
end CaseCPUMem.Source
