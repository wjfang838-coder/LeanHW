import SourceRefinement
import PacketPC
namespace CaseCPU.Bridge
open LeanRTL CPUShallow
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

/-- Read the real imported module's output list, rather than reconstructing an event
    solely from the handwritten model. -/
def outputPort (r : Env) (i : Pins) (o : Env) (name : String) (width : Nat) : BitVec width :=
  BitVec.ofNat width (((V2LeanImported.core.outputs?eval r (pinEnv i o)).find?
    (fun p => p.1 == name)).map Prod.snd |>.getD 0)

theorem port_retire_valid (r : Env) (i : Pins) (o : Env) :
    outputPort r i o "retire_valid" 1 = V_w113 (base r i o) := by
  have h : outputPort r i o "retire_valid" 1 =
      BitVec.ofNat 1 (BitVec.ofNat 1 (evalWires V2LeanImported.core.wires (base r i o) "w113")).toNat := rfl
  rw [h,value_w113]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem port_retire_insn (r : Env) (i : Pins) (o : Env) :
    outputPort r i o "retire_insn" 32 = V_w129 (base r i o) := by
  have h : outputPort r i o "retire_insn" 32 =
      BitVec.ofNat 32 (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w129")).toNat := rfl
  rw [h,value_w129]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem port_insn_ready (r : Env) (i : Pins) (o : Env) :
    outputPort r i o "insn_ready" 1 = V_w333 (base r i o) := by
  have h : outputPort r i o "insn_ready" 1 =
      BitVec.ofNat 1 (BitVec.ofNat 1 (evalWires V2LeanImported.core.wires (base r i o) "w333")).toNat := rfl
  rw [h,value_w333]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem port_retire_pc (r : Env) (i : Pins) (o : Env) :
    outputPort r i o "retire_pc" 32 = V_w130 (base r i o) := by
  have h : outputPort r i o "retire_pc" 32 =
      BitVec.ofNat 32 (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w130")).toNat := rfl
  rw [h,value_w130]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem port_retire_value (r : Env) (i : Pins) (o : Env) :
    outputPort r i o "retire_value" 32 = V_w132 (base r i o) := by
  have h : outputPort r i o "retire_value" 32 =
      BitVec.ofNat 32 (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w132")).toNat := rfl
  rw [h,value_w132]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem port_retire_rd (r : Env) (i : Pins) (o : Env) :
    outputPort r i o "retire_rd" 5 = V_w131 (base r i o) := by
  have h : outputPort r i o "retire_rd" 5 =
      BitVec.ofNat 5 (BitVec.ofNat 5 (evalWires V2LeanImported.core.wires (base r i o) "w131")).toNat := rfl
  rw [h,value_w131]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem port_debug_data (r : Env) (i : Pins) (o : Env) :
    outputPort r i o "debug_data" 32 = V_w62 (base r i o) := by
  have h : outputPort r i o "debug_data" 32 =
      BitVec.ofNat 32 (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w62")).toNat := rfl
  rw [h,value_w62]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]

theorem debug_read (b : Env) : V_w62 b = readRF (rawOf b).rf (pinsOf b).debug := by
  simp only [V_w62,V_w60,V_w1,rawOf,pinsOf,readRF,offset,Word,RF,CaseCPU.Reg]
  bv_decide

theorem port_debug (r : Env) (i : Pins) (o : Env) :
    outputPort r i o "debug_data" 32 = (project (rawOf r)).arch.regs i.debug := by
  rw [port_debug_data,debug_read,base_raw,base_pins]
  rfl

theorem port_arch_pc (r : Env) (i : Pins) (o : Env) :
    outputPort r i o "arch_pc" 32 = (rawOf r).pc := by
  have h : outputPort r i o "arch_pc" 32 =
      BitVec.ofNat 32 (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "r4")).toNat := rfl
  have he := all_values (base r i o) "r4" (by decide +kernel)
  rw [at_r4] at he
  rw [h,he]
  change BitVec.ofNat 32 (BitVec.ofNat 32 (base r i o "r4")).toNat = _
  simpa only [BitVec.ofNat_toNat,BitVec.setWidth_eq] using base_r4 r i o

def rtlRetired (r : Env) (i : Pins) (o : Env) : Option Instr :=
  if outputPort r i o "retire_valid" 1 = (1#1)
    then CaseCPU.decode (outputPort r i o "retire_insn" 32) else none

theorem rtl_retired_raw (r : Env) (i : Pins) (o : Env) (h : Legal (rawOf r)) :
    rtlRetired r i o = rawRetired (rawOf r) i := by
  have hc := retire_condition (base r i o)
  rw [base_raw,base_pins] at hc
  unfold rtlRetired rawRetired
  simp only [port_retire_valid,port_retire_insn,V_w129,← hc]
  by_cases hv : V_w113 (base r i o) = (1#1)
  · have hw : (rawOf r).wv = true := by
      have hh := hc.mp hv
      simp only [Bool.and_eq_true] at hh
      exact hh.1.2
    have hi := instruction_some (rawOf r).w.word (h.2.2.2.2 hw)
    simpa [hv,base_r14,rawOf] using hi
  · simp [hv]

theorem project_retired (s : Raw) (i : Pins) :
    (cycle (project s) (specInput i)).retired = rawRetired s i := by
  cases hr : i.reset <;> cases hw : s.wv <;> cases hs : i.sw <;>
    simp [cycle,retire,project,specInput,optPacket,packet,rawRetired,hr,hw,hs]

theorem rtl_retired_cycle (r : Env) (i : Pins) (o : Env) (h : Legal (rawOf r)) :
    rtlRetired r i o = (cycle (project (rawOf r)) (specInput i)).retired := by
  rw [rtl_retired_raw _ _ _ h,project_retired]

def rtlAccepted (r : Env) (i : Pins) (o : Env) : Bool :=
  i.valid && (outputPort r i o "insn_ready" 1 == (1#1))

theorem rtl_accepted_raw (r : Env) (i : Pins) (o : Env) (h : Legal (rawOf r)) :
    rtlAccepted r i o = rawAccepted (rawOf r) i := by
  have hc := ready_condition (base r i o)
  have hb : (V_w333 (base r i o) == (1#1)) =
      readyRaw (postFetch (base r i o)) (pinsOf (base r i o)) := by bv_decide
  unfold rtlAccepted
  rw [port_insn_ready,hb]
  cases hr : i.reset
  · rw [before_accept_state _ (by simpa only [base_pins] using hr)
      (by simpa only [base_raw] using h),base_raw,base_pins]
    simp only [rawAccepted,hr,Bool.not_false,Bool.true_and,acceptRaw]
    cases hv : i.valid <;> cases hh : readyRaw (beforeAccept (rawOf r) i) i <;> simp [hv,hh]
  · rw [base_pins]
    simp [readyRaw,hr,rawAccepted]

theorem project_accepted (s : Raw) (i : Pins) :
    rawAccepted s i = (cycle (project s) (specInput i)).accepted := by
  cases hr : i.reset
  · have h := (project_accept (beforeAccept s i) i hr).2
    simpa only [rawAccepted,hr,Bool.not_false,Bool.true_and,cycle,specInput,
      Bool.false_eq_true,↓reduceIte,beforeAccept,project_fetch,project_dispatch,
      project_execute,project_memory,project_commit] using h
  · simp [rawAccepted,cycle,specInput,hr]

theorem rtl_accepted_cycle (r : Env) (i : Pins) (o : Env) (h : Legal (rawOf r)) :
    rtlAccepted r i o = (cycle (project (rawOf r)) (specInput i)).accepted := by
  rw [rtl_accepted_raw _ _ _ h,project_accepted]

theorem retirement_pc (r : Env) (i : Pins) (o : Env) (h : PcInv (rawOf r))
    (hv : outputPort r i o "retire_valid" 1 = (1#1)) :
    outputPort r i o "retire_pc" 32 = (rawOf r).pc := by
  rw [port_retire_valid] at hv
  have hc := (retire_condition (base r i o)).mp hv
  rw [base_raw,base_pins] at hc
  simp only [Bool.and_eq_true] at hc
  have hw := h.1 hc.1.2
  rw [port_retire_pc,V_w130]
  simpa [hv,base_r1,rawOf] using hw

theorem retirement_value (r : Env) (i : Pins) (o : Env)
    (h : Inv (project (rawOf r)))
    (hv : outputPort r i o "retire_valid" 1 = (1#1)) :
    outputPort r i o "retire_value" 32 =
      (effectFor (project (rawOf r)).arch (instruction (rawOf r).w.word)).value := by
  rw [port_retire_valid] at hv
  have hc := (retire_condition (base r i o)).mp hv
  rw [base_raw,base_pins] at hc
  simp only [Bool.and_eq_true] at hc
  have hh := h.1
  simp only [project,optPacket,hc.1.2,↓reduceIte,checked,packet] at hh
  have he := congrArg Effect.value hh
  rw [port_retire_value,V_w132]
  simpa [hv,base_r17,rawOf] using he

/-- The independent transaction reference consumes actual RTL retirement outputs. -/
def rtlReference : Env → Arch → List (Pins × Env) → Arch
  | _,a,[] => a
  | r,a,(i,o)::xs =>
    let a' := if i.reset then (initial (readRF i.seed)).arch else transaction a (rtlRetired r i o)
    rtlReference (rtlStep r i o) a' xs

theorem reference_events (r : Env) (a : Arch) (xs : List (Pins × Env))
    (h : Legal (rawOf r)) :
    rtlReference r a xs = reference (project (rawOf r)) a
      (xs.map (fun x => specInput x.1)) := by
  induction xs generalizing r a with
  | nil => rfl
  | cons io xs ih =>
    have hn : Legal (rawOf (rtlStep r io.1 io.2)) := by
      rw [rtl_step_refines _ _ _ h]
      exact legal_cycle _ _ h
    simp only [rtlReference,reference,List.map_cons]
    rw [ih _ _ hn,rtl_step_refines _ _ _ h,project_cycle,rtl_retired_cycle _ _ _ h]
    rfl

/-- End-to-end architectural safety driven by physical retirement-valid/instruction ports. -/
theorem rtl_isa_physical_events (r : Env) (i : Pins) (o : Env)
    (xs : List (Pins × Env)) (hr : i.reset = true) :
    (project (rawOf (rtlRun (rtlStep r i o) xs))).arch =
      rtlReference (rtlStep r i o) (initial (readRF i.seed)).arch xs := by
  rw [reference_events _ _ _ (by rw [rtl_reset _ _ _ hr]; exact legal_initial _),
    rtl_reset _ _ _ hr,project_initial]
  exact rtl_isa_refinement r i o xs hr

def rtlRetirements : Env → List (Pins × Env) → List Instr
  | _,[] => []
  | r,(i,o)::xs => (rtlRetired r i o).toList ++ rtlRetirements (rtlStep r i o) xs

def rtlAcceptances : Env → List (Pins × Env) → List Instr
  | _,[] => []
  | r,(i,o)::xs => (if rtlAccepted r i o then (CaseCPU.decode i.word).toList else []) ++
      rtlAcceptances (rtlStep r i o) xs

theorem retirement_events (r : Env) (xs : List (Pins × Env)) (h : Legal (rawOf r)) :
    rtlRetirements r xs = retirements (project (rawOf r)) (xs.map (fun x => specInput x.1)) := by
  induction xs generalizing r with
  | nil => rfl
  | cons io xs ih =>
    have hn : Legal (rawOf (rtlStep r io.1 io.2)) := by
      rw [rtl_step_refines _ _ _ h]
      exact legal_cycle _ _ h
    simp only [rtlRetirements,retirements,List.map_cons]
    rw [ih _ hn,rtl_retired_cycle _ _ _ h,rtl_step_refines _ _ _ h,project_cycle]

theorem acceptance_events (r : Env) (xs : List (Pins × Env)) (h : Legal (rawOf r)) :
    rtlAcceptances r xs = acceptances (project (rawOf r)) (xs.map (fun x => specInput x.1)) := by
  induction xs generalizing r with
  | nil => rfl
  | cons io xs ih =>
    have hn : Legal (rawOf (rtlStep r io.1 io.2)) := by
      rw [rtl_step_refines _ _ _ h]
      exact legal_cycle _ _ h
    simp only [rtlAcceptances,acceptances,List.map_cons,acceptedInstruction]
    rw [ih _ hn,rtl_accepted_cycle _ _ _ h,rtl_step_refines _ _ _ h,project_cycle]
    rfl

theorem rtl_conservation (r : Env) (xs : List (Pins × Env)) (h : Legal (rawOf r))
    (hn : ∀ io ∈ xs, io.1.reset = false) :
    rtlRetirements r xs ++ pending (project (rawOf (rtlRun r xs))) =
      pending (project (rawOf r)) ++ rtlAcceptances r xs := by
  rw [retirement_events _ _ h,acceptance_events _ _ h,rtl_run_refines _ _ h,projected_run]
  simp only [List.map_map,Function.comp_def]
  apply trace_conservation
  intro i hi
  rcases List.mem_map.mp hi with ⟨io,hio,rfl⟩
  exact hn io hio

/-- Execute exactly the program accepted at the physical ready/valid interface once drained. -/
theorem rtl_drained_refinement (r : Env) (i : Pins) (o : Env)
    (xs : List (Pins × Env)) (hr : i.reset = true)
    (hn : ∀ io ∈ xs, io.1.reset = false)
    (hd : pending (project (rawOf (rtlRun (rtlStep r i o) xs))) = []) :
    (project (rawOf (rtlRun (rtlStep r i o) xs))).arch =
      isaRun (initial (readRF i.seed)).arch (rtlAcceptances (rtlStep r i o) xs) := by
  have h0 := rtl_reset r i o hr
  rw [acceptance_events _ _ (by rw [h0]; exact legal_initial _),h0,project_initial]
  rw [rtl_cycle_refinement r i o xs hr] at hd ⊢
  apply drained_refinement _ _ _ hd
  intro j hj
  rcases List.mem_map.mp hj with ⟨io,hio,rfl⟩
  exact hn io hio

#print axioms rtl_conservation
#print axioms rtl_drained_refinement
#print axioms retirement_pc
#print axioms retirement_value
#print axioms rtl_accepted_cycle
#print axioms port_debug
#print axioms rtl_isa_physical_events
end CaseCPU.Bridge
