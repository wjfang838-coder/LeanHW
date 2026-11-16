import MemStageRefinement
import MemDecoderCircuit
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def fetchPhysical (p : Physical) : Physical :=
  if p.dv then p else {p with di := p.fi,dv := p.fv,fv := false}

def readyPhysical (p : Physical) (i : Raw.Pins) : Bool :=
  !i.reset && !i.sf && !p.fv && (decode i.word).isSome

def acceptPhysical (p : Physical) (i : Raw.Pins) : Physical :=
  if i.valid && readyPhysical p i then {p with fi := i.word,fv := true} else p

def initialPhysical (seed : CaseCPU.Bridge.RF) : Physical :=
  ⟨CaseCPU.Bridge.resetRF seed,0,0,0,0,0,0,0,false,false,false,false,false,0,0⟩

theorem fetch_state (b : Env) (hz : V_next_fault b = (0#3)) :
    postFetch b = fetchPhysical (postDispatch b) := by
  have hp := running_payloads b hz
  simp only [postCommit,physical] at hp
  by_cases hd : V_w592 b = (1#1)
  all_goals simp only [postFetch,fetchPhysical,postDispatch,postExecute,postMemory,postCommit,physical,
    V_w602,V_w601,V_w600,V_w599,V_w333,hz,Packed]
  all_goals simp [hd,Physical.mk.injEq]
  all_goals bv_decide

theorem accept_state (b : Env) (hz : V_next_fault b = (0#3)) :
    postAccept b = acceptPhysical (postFetch b) (pins b) := by
  have hp := running_payloads b hz
  simp only [postCommit,physical] at hp
  have hd := decoder_w384 b
  have hl := code_legal (b.lookup "insn" 32)
  by_cases ha : ((pins b).valid && readyPhysical (postFetch b) (pins b)) = true
  all_goals simp only [postAccept,acceptPhysical,ha,↓reduceIte]
  all_goals simp only [readyPhysical,postFetch,postDispatch,postExecute,
    postMemory,postCommit,physical,pins,V_w706,V_w698,V_w697,V_w696,V_w260,V_w29,V_w30,V_w633,V_w436,V_w423,V_w705,
    V_w600,V_w599,V_w333,hz,Word,Packed] at *
  all_goals simp only [Bool.false_eq_true,↓reduceIte,Physical.mk.injEq]
  all_goals bv_decide

theorem net_running (b : Env) (hr : (pins b).reset = false) (hz : V_next_fault b = (0#3)) :
    netNext b = postAccept b := by
  simp only [pins] at hr
  simp only [netNext,postAccept,postFetch,postDispatch,postExecute,postMemory,postCommit,
    V_w371,V_w297,V_w296,V_w719,V_next_fetch_instruction,V_w668,V_next_decode_instruction,
    V_w729,V_next_execute_packet,V_w421,V_next_memory_packet,V_w420,V_next_writeback_packet,
    V_w720,V_next_fetch_valid,V_w669,V_next_decode_valid,V_w598,V_next_execute_valid,
    V_w422,V_next_memory_valid,V_w370,V_next_writeback_valid,V_w597,V_next_execute_remaining,
    V_w473,V_next_memory_remaining,V_w333,hz]
  simp_all

theorem net_halted (b : Env) (hr : (pins b).reset = false) (hz : V_next_fault b ≠ (0#3)) :
    netNext b = postCommit b := by
  simp only [pins] at hr
  simp only [netNext,postCommit,physical,
    V_w371,V_w297,V_w296,V_w719,V_next_fetch_instruction,V_w668,V_next_decode_instruction,
    V_w729,V_next_execute_packet,V_w421,V_next_memory_packet,V_w420,V_next_writeback_packet,
    V_w720,V_next_fetch_valid,V_w669,V_next_decode_valid,V_w598,V_next_execute_valid,
    V_w422,V_next_memory_valid,V_w370,V_next_writeback_valid,V_w597,V_next_execute_remaining,
    V_w473,V_next_memory_remaining,V_w333,hz]
  simp_all

theorem net_reset (b : Env) (hr : (pins b).reset = true) :
    netNext b = initialPhysical (pins b).seed := by
  have h : b.lookup "rst" 1 = (1#1) := by simpa [pins] using hr
  simp [netNext,initialPhysical,pins,h,V_w371,V_w297,V_w296,V_w719,V_w668,V_w729,V_w421,
    V_w420,V_w720,V_w669,V_w598,V_w422,V_w370,V_w597,V_w473,circuit_reset]

theorem fetch_related (p : Physical) (mem : Memory) (q : Raw.State) (h : Related p mem q) :
    Related (fetchPhysical p) mem (Raw.fetch q) := by
  rcases h with ⟨hrf,hpc,hflt,hram,hfv,hdv,hxv,hmv,hwv,hcount,hwait,hfi,hdi,hx,hmemory,hwpacket⟩
  cases hd : q.dv <;> constructor <;> simp_all [fetchPhysical,Raw.fetch]

theorem accept_related (p : Physical) (mem : Memory) (q : Raw.State) (i : Raw.Pins)
    (h : Related p mem q) : Related (acceptPhysical p i) mem (Raw.accept q i) := by
  have hr : readyPhysical p i = Raw.ready q i := by
    simp only [readyPhysical,Raw.ready,h.fv]
  rcases h with ⟨hrf,hpc,hflt,hram,hfv,hdv,hxv,hmv,hwv,hcount,hwait,hfi,hdi,hx,hmemory,hwpacket⟩
  simp only [acceptPhysical,Raw.accept,hr]
  cases ha : (i.valid && Raw.ready q i)
  all_goals simp only [ha,Bool.false_eq_true,↓reduceIte]
  all_goals constructor <;> simp_all

theorem reset_related (seed : CaseCPU.Bridge.RF) (mem : Memory) :
    Related (initialPhysical seed) mem (Raw.initial seed mem) := by
  constructor <;> simp [initialPhysical,Raw.initial]

#print axioms net_running
#print axioms accept_state
end CaseCPUMem.Source
