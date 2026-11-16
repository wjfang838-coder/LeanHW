import MemCircuitRefinement
import MemEvents
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

noncomputable def port (s : NativeMemory.State) (i : Raw.Pins) (o : Env)
    (name : String) (width : Nat) : BitVec width :=
  BitVec.ofNat width (((MemCPUImported.program.outputs s (pinEnv i o)).find?
    (fun p => p.1 == name)).map Prod.snd |>.getD 0)

theorem port_insn_ready (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "insn_ready" 1 = V_next_ready (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 1 (BitVec.ofNat 1 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "next_ready")).toNat = _
  rw [value_next_ready]
  simp

theorem port_retire_valid (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "retire_valid" 1 = V_writeback_fire (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 1 (BitVec.ofNat 1 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "writeback_fire")).toNat = _
  rw [value_writeback_fire]
  simp

theorem port_retire_insn (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "retire_insn" 32 = V_w303 (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 32 (BitVec.ofNat 32 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w303")).toNat = _
  rw [value_w303]
  simp

theorem port_retire_rd (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "retire_rd" 5 = V_w305 (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 5 (BitVec.ofNat 5 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w305")).toNat = _
  rw [value_w305]
  simp

theorem port_retire_value (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "retire_value" 32 = V_w306 (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 32 (BitVec.ofNat 32 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w306")).toNat = _
  rw [value_w306]
  simp

theorem port_trap_valid (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "trap_valid" 1 = V_fault_commit (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 1 (BitVec.ofNat 1 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "fault_commit")).toNat = _
  rw [value_fault_commit]
  simp

theorem port_trap_cause (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "trap_cause" 3 = V_w308 (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 3 (BitVec.ofNat 3 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w308")).toNat = _
  rw [value_w308]
  simp

theorem fire_boolean (b : Env) : (V_writeback_fire b == (1#1)) =
    (! (pins b).reset && ((physical b).fault == (0#3)) && (physical b).wv && !(pins b).sw) := by
  simp only [pins,physical,V_writeback_fire,V_w255,V_w254,V_w29,V_w18,V_w27]
  bv_decide

theorem trap_rd_zero (s : NativeMemory.State) (i : Raw.Pins) (o : Env)
    (h : port s i o "trap_valid" 1 = (1#1)) : port s i o "retire_rd" 5 = (0#5) := by
  rw [port_trap_valid] at h
  rw [port_retire_rd]
  delta V_w305 V_w258 V_w19 V_fault_commit V_w32 at *
  bv_decide

noncomputable def retiredPort (s : NativeMemory.State) (i : Raw.Pins) (o : Env) : Option Instr :=
  if port s i o "retire_valid" 1 == (1#1) then decode (port s i o "retire_insn" 32) else none

theorem cycle_retired (s : Pipe) (i : Input) :
    (cycle s i).retired = if i.reset then none else (retire s i.sw).2 := by
  cases hr : i.reset
  · simp only [cycle,hr,Bool.false_eq_true,↓reduceIte]
    generalize he : retire s i.sw = ev
    cases ev with | mk st ev => split <;> rfl
  · simp [cycle,hr]

theorem model_retired (q : Raw.State) (i : Raw.Pins) :
    (cycle (Raw.project q) (Raw.input i)).retired =
      if !i.reset && q.wv && !i.sw then some (Raw.instr q.w.word) else none := by
  rw [cycle_retired]
  cases hr : i.reset <;> cases hw : q.wv <;> cases hs : i.sw
  all_goals simp [Raw.input,Raw.project,Raw.optPacket,Raw.packet,retire,hr,hw,hs]
  all_goals split <;> rfl

theorem retired_port_refinement (s : NativeMemory.State) (i : Raw.Pins) (o : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q) :
    retiredPort s i o = (cycle (Raw.project q) (Raw.input i)).retired := by
  let b := NativeRAM.combInput s (pinEnv i o)
  have hf : (V_writeback_fire b == (1#1)) = (!i.reset && q.wv && !i.sw) := by
    rw [fire_boolean,bound_physical,bound_pins,h.fault,h.wv]
    by_cases hz : q.fault = (0#3)
    · simp [hz]
    · have hw := (hv.2.2.2.2.2.2 hz).1
      simp [hw]
  rw [model_retired]
  simp only [retiredPort,port_retire_valid]
  change (if V_writeback_fire b == (1#1) then decode (port s i o "retire_insn" 32) else none) = _
  rw [hf]
  cases he : (!i.reset && q.wv && !i.sw)
  · rfl
  · have hw : q.wv = true := by bv_decide
    have hg : V_writeback_fire b = (1#1) := by
      have hh := hf
      rw [he] at hh
      simpa using hh
    have hp := h.writebackPacket hw
    have hi := (hv.2.2.2.1 hw).1
    simp only [↓reduceIte,port_retire_insn,V_w303,hg]
    change decode (if V_writeback_fire b = 1 then (b.lookup "r24" 174 >>> 142).setWidth 32 else 0) = _
    rw [hg]
    try simp only [↓reduceIte]
    have hw' : (b.lookup "r24" 174 >>> 142).setWidth 32 = q.w.word := by
      rw [bound_r24]
      exact hp.word
    rw [hw']
    exact decode_some q.w.word hi

noncomputable def rtlReference : NativeMemory.State → Arch → List (Raw.Pins × Env) → Arch
  | _,a,[] => a
  | s,a,(i,o)::xs =>
    let a' := if i.reset then initial (CaseCPU.Bridge.readRF i.seed) a.mem
      else transaction a (retiredPort s i o)
    rtlReference (rtlStep s i o) a' xs

theorem rtl_port_isa_refinement (s : NativeMemory.State) (q : Raw.State)
    (xs : List (Raw.Pins × Env))
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q)
    (hv : Raw.Valid q) (hi : Inv (Raw.project q)) :
    architecture (circuitRun s xs) = rtlReference s (architecture s) xs := by
  induction xs generalizing s q with
  | nil => rfl
  | cons x xs ih =>
    have hc := circuit_cycle_refinement s x.1 x.2 q h hv
    have hp := Raw.project_cycle q x.1 hv
    have hh := cycle_refines (Raw.project q) (Raw.input x.1) hi
    have ha := related_architecture (rtlStep s x.1 x.2) (Raw.cycle q x.1) hc
    rw [hp,hh] at ha
    rw [←related_architecture s q h,←retired_port_refinement s x.1 x.2 q h hv] at ha
    simp only [Raw.input] at ha
    simp only [circuitRun,rtlReference]
    rw [←ha]
    exact ih _ _ hc (Raw.valid_cycle q x.1 hv) (by rw [hp];exact cycle_inv _ _ hi)

theorem rtl_to_transaction_isa (s : NativeMemory.State) (seed : CaseCPU.Bridge.RF)
    (o : Env) (xs : List (Raw.Pins × Env)) :
    architecture (circuitRun (rtlStep s {reset := true,seed := seed} o) xs) =
      rtlReference (rtlStep s {reset := true,seed := seed} o)
        (initial (CaseCPU.Bridge.readRF seed) (NativeRAM.ramView s.arrays)) xs := by
  have hb := boot_related s seed o
  have ha := related_architecture _ _ hb
  rw [Raw.project_initial] at ha
  change architecture _ = initial _ _ at ha
  rw [←ha]
  apply rtl_port_isa_refinement _ _ xs hb (Raw.valid_initial _ _)
  rw [Raw.project_initial]
  exact initial_inv _ _

#print axioms trap_rd_zero
#print axioms rtl_to_transaction_isa
end CaseCPUMem.Source
