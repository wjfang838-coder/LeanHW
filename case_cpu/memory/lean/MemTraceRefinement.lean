import MemAcceptRefinement
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

noncomputable def acceptedTrace : NativeMemory.State → List (Raw.Pins × Env) → List Instr
  | _,[] => []
  | s,(i,o)::xs =>
    (if acceptedPort s i o then (decode i.word).toList else []) ++
      acceptedTrace (rtlStep s i o) xs

def inputTrace (xs : List (Raw.Pins × Env)) : List Input := xs.map (fun x => Raw.input x.1)

theorem circuit_run_native (s : NativeMemory.State) (xs : List (Raw.Pins × Env)) :
    circuitRun s xs = MemCPUImported.program.run s (xs.map (fun x => pinEnv x.1 x.2)) := by
  induction xs generalizing s with
  | nil => rfl
  | cons x xs ih => exact ih (rtlStep s x.1 x.2)

theorem accepted_trace_refinement (s : NativeMemory.State) (q : Raw.State)
    (xs : List (Raw.Pins × Env))
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q) :
    acceptedTrace s xs = acceptances (Raw.project q) (inputTrace xs) := by
  induction xs generalizing s q with
  | nil => rfl
  | cons x xs ih =>
    simp only [acceptedTrace,inputTrace,List.map_cons,acceptances]
    rw [←accepted_port_refinement s x.1 x.2 q h hv]
    rw [←Raw.project_cycle q x.1 hv]
    rw [ih (rtlStep s x.1 x.2) (Raw.cycle q x.1)
      (circuit_cycle_refinement s x.1 x.2 q h hv) (Raw.valid_cycle q x.1 hv)]
    rfl

def Drained (s : NativeMemory.State) : Prop :=
  (physical s.regs).fv = false ∧ (physical s.regs).dv = false ∧
  (physical s.regs).xv = false ∧ (physical s.regs).mv = false ∧ (physical s.regs).wv = false

theorem related_drained (s : NativeMemory.State) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hd : Drained s) :
    pending (Raw.project q) = [] := by
  simp only [Drained,h.fv,h.dv,h.xv,h.mv,h.wv] at hd
  simp [pending,packetInstructions,Raw.project,Raw.optPacket,Raw.optInstr,
    hd.1,hd.2.1,hd.2.2.1,hd.2.2.2.1,hd.2.2.2.2]

/-- The instruction list comes from the real input ready/valid handshake. Once
    physically drained, actual RF/PC/RAM/fault equal one ISA execution of that
    list. A precise fault may abort younger words; the halted ISA treats them
    as no-ops. No bound on stalls or memory delay and no fairness axiom. -/
theorem rtl_accepted_program_refinement (s : NativeMemory.State) (seed : CaseCPU.Bridge.RF)
    (o : Env) (xs : List (Raw.Pins × Env))
    (hn : ∀ x ∈ xs, x.1.reset = false)
    (hd : Drained (circuitRun (rtlStep s {reset := true,seed := seed} o) xs)) :
    architecture (circuitRun (rtlStep s {reset := true,seed := seed} o) xs) =
      isaRun (initial (CaseCPU.Bridge.readRF seed) (NativeRAM.ramView s.arrays))
        (acceptedTrace (rtlStep s {reset := true,seed := seed} o) xs) := by
  let q := Raw.initial seed (NativeRAM.ramView s.arrays)
  have hb := boot_related s seed o
  have hv : Raw.Valid q := Raw.valid_initial _ _
  have hf := circuit_run_related _ q xs hb hv
  have hp := Raw.word_cycle_refinement seed (NativeRAM.ramView s.arrays) (xs.map Prod.fst)
  have hm : pending (run (initialPipe (CaseCPU.Bridge.readRF seed) (NativeRAM.ramView s.arrays))
      (inputTrace xs)) = [] := by
    have hh := related_drained _ _ hf hd
    rw [hp] at hh
    simpa only [inputTrace,List.map_map,Function.comp_def] using hh
  have hn' : ∀ i ∈ inputTrace xs, i.reset = false := by
    intro i hi
    obtain ⟨x,hx,rfl⟩ := List.mem_map.mp hi
    exact hn x hx
  have ht := drained_refinement (CaseCPU.Bridge.readRF seed) (NativeRAM.ramView s.arrays)
    (inputTrace xs) hn' hm
  rw [related_architecture _ _ hf,hp]
  rw [accepted_trace_refinement _ q xs hb hv,Raw.project_initial]
  simpa only [inputTrace,List.map_map,Function.comp_def] using ht

#print axioms rtl_accepted_program_refinement
end CaseCPUMem.Source
