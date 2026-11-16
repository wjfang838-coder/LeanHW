import MemPortRefinement
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

noncomputable def beforeAccept (q : Raw.State) (i : Raw.Pins) : Raw.State :=
  Raw.fetch (Raw.dispatch (beforeDispatch q i) i.sd)

noncomputable def rawAccepted (q : Raw.State) (i : Raw.Pins) : Bool :=
  if i.reset || (Raw.commit q i.sw).fault != (0#3) then false
    else i.valid && Raw.ready (beforeAccept q i) i

noncomputable def acceptedPort (s : NativeMemory.State) (i : Raw.Pins) (o : Env) : Bool :=
  i.valid && (port s i o "insn_ready" 1 == (1#1))

theorem ready_circuit (b : Env) (hz : V_next_fault b = (0#3)) :
    (V_next_ready b == (1#1)) = readyPhysical (postFetch b) (pins b) := by
  have hd := decoder_w384 b
  have hl := code_legal (b.lookup "insn" 32)
  simp only [V_next_ready,readyPhysical,postFetch,postDispatch,postExecute,postMemory,
    postCommit,physical,pins,V_w697,V_w696,V_w260,V_w29,V_w30,V_w633,V_w436,V_w423,
    V_w333,hz,Word,Packed] at *
  bv_decide

theorem halted_ready (b : Env) (hz : V_next_fault b ≠ (0#3)) : V_next_ready b = (0#1) := by
  simp [V_next_ready,V_w333,hz]

theorem reset_ready (b : Env) (hr : (pins b).reset = true) : V_next_ready b = (0#1) := by
  simp only [pins] at hr
  simp only [V_next_ready,V_w697,V_w696,V_w260,V_w29,V_w30,V_w633,V_w436,V_w423]
  bv_decide

theorem before_accept_related (s : NativeMemory.State) (i : Raw.Pins) (o : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q)
    (hr : i.reset = false) (hz : V_next_fault (NativeRAM.combInput s (pinEnv i o)) = (0#3)) :
    Related (postFetch (NativeRAM.combInput s (pinEnv i o)))
      (NativeRAM.ramView (rtlStep s i o).arrays) (beforeAccept q i) := by
  let b := NativeRAM.combInput s (pinEnv i o)
  have hp : pins b = i := bound_pins s i o
  have hr' : (pins b).reset = false := by rw [hp,hr]
  have hx := execute_refinement s (pinEnv i o) q h hv hr' hz
  have hd := dispatch_related b (beforeDispatch q (pins b))
    (NativeRAM.ramView (rtlStep s i o).arrays) hx (by simpa only [hp] using execute_kinds q i hv) hz
  have hf := fetch_related _ _ _ hd
  rw [←fetch_state b hz] at hf
  simpa only [beforeAccept,hp] using hf

theorem accepted_port_raw (s : NativeMemory.State) (i : Raw.Pins) (o : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q) :
    acceptedPort s i o = rawAccepted q i := by
  let b := NativeRAM.combInput s (pinEnv i o)
  have hp : pins b = i := bound_pins s i o
  simp only [acceptedPort,port_insn_ready]
  cases hr : i.reset
  · have hc := commit_refinement s (pinEnv i o) q h hv (by rw [bound_pins,hr])
    have hcf : V_next_fault b = (Raw.commit q i.sw).fault := by simpa only [bound_pins] using hc.fault
    by_cases hz : V_next_fault b = (0#3)
    · have hf := before_accept_related s i o q h hv hr hz
      rw [ready_circuit b hz]
      have hfv : (postFetch b).fv = (beforeAccept q i).fv := hf.fv
      have he : readyPhysical (postFetch b) (pins b) = Raw.ready (beforeAccept q i) i := by
        simp only [readyPhysical,Raw.ready,hfv,hp]
      rw [he]
      simp [rawAccepted,hr,←hcf,hz]
    · rw [halted_ready b hz]
      simp [rawAccepted,hr,←hcf,hz]
  · rw [reset_ready b (by rw [hp,hr])]
    simp [rawAccepted,hr]

theorem accept_flag (q : Raw.State) (i : Raw.Pins) (hr : i.reset = false) :
    (accept (Raw.project q) (Raw.input i)).2 = (i.valid && Raw.ready q i) := by
  cases hv : i.valid <;> cases hs : i.sf <;> cases hf : q.fv <;> cases hd : decode i.word
  all_goals simp [accept,Raw.project,Raw.input,Raw.optInstr,Raw.ready,hr,hv,hs,hf,hd]

theorem cycle_accepted (s : Pipe) (i : Input) :
    (cycle s i).accepted = if i.reset then false else
      if (retire s i.sw).1.arch.fault != (0#3) then false else
      (accept (moveFetch (dispatch (moveExecute (moveMemory (retire s i.sw).1 i.sm)
        i.sx i.memoryDelay) i.sd)) i).2 := by
  cases hr : i.reset
  · simp only [cycle,hr,Bool.false_eq_true,↓reduceIte]
    generalize he : retire s i.sw = ev
    cases ev with | mk st ev => split <;> rfl
  · simp [cycle,hr]

theorem raw_accepted_model (q : Raw.State) (i : Raw.Pins) (hv : Raw.Valid q) :
    rawAccepted q i = (cycle (Raw.project q) (Raw.input i)).accepted := by
  rw [cycle_accepted]
  cases hr : i.reset
  · have hp := Raw.project_commit q i.sw hv
    have hcf : (retire (Raw.project q) i.sw).1.arch.fault = (Raw.commit q i.sw).fault :=
      congrArg (fun p : Pipe => p.arch.fault) hp.symm
    by_cases hc : (Raw.commit q i.sw).fault = (0#3)
    · have hk := Raw.kinds_commit q i.sw
        ⟨hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.1,hv.2.2.2.2.2.1⟩
      have hm : Raw.project (beforeAccept q i) =
          moveFetch (dispatch (moveExecute (moveMemory (retire (Raw.project q) i.sw).1 i.sm)
            i.sx i.delay) i.sd) := by
        unfold beforeAccept beforeDispatch
        rw [Raw.project_fetch,Raw.project_dispatch_running _ _
          (Raw.kinds_execute _ _ _ (Raw.kinds_memory _ _ hk)) (by simpa using hc),
          Raw.project_execute,Raw.project_memory,hp]
      simp only [rawAccepted,Raw.input,hr,Bool.false_or,hcf,hc,bne_self_eq_false,
        Bool.false_eq_true,↓reduceIte]
      rw [←hm]
      exact (accept_flag _ _ hr).symm
    · simp [rawAccepted,Raw.input,hr,hcf,hc]
  · simp [rawAccepted,Raw.input,hr]

theorem accepted_port_refinement (s : NativeMemory.State) (i : Raw.Pins) (o : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q) :
    acceptedPort s i o = (cycle (Raw.project q) (Raw.input i)).accepted := by
  rw [accepted_port_raw s i o q h hv,raw_accepted_model q i hv]

#print axioms accepted_port_refinement
end CaseCPUMem.Source
