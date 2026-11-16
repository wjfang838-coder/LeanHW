import MemControlCircuit
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def loadByCode (c : BitVec 6) (addr word : Word) : Word :=
  if c = 29 then loadValue .lb addr word else if c = 30 then loadValue .lh addr word else
  if c = 31 then loadValue .lw addr word else if c = 32 then loadValue .lbu addr word else
  if c = 33 then loadValue .lhu addr word else 0

def withValue (p : Packed) (v : Word) : Packed := (p >>> 99).setWidth 75 ++ v ++ p.setWidth 67

def finishPhysical (p : Packed) (word : Word) : Packed :=
  if codeLoad (pcode p) && pfault p == (0#3) then
    withValue p (loadByCode (pcode p) (paddr p) word) else p

def memoryPhysical (p : Physical) (stall : Bool) (word : Word) : Physical :=
  if stall then p else if p.waitCount != (0#4) then {p with waitCount := p.waitCount-1} else
  if p.wv then p else {p with w := finishPhysical p.m word,wv := p.mv,mv := false}

theorem load_code (b : Env) : V_w178 b =
    loadByCode (pcode (physical b).m) (paddr (physical b).m) (b.lookup "__native_read_0_0" 32) := by
  simp only [V_w178,V_w162,V_w66,V_w65,V_w67,V_w175,V_w174,V_w138,V_w177,V_w68,V_w176,V_w69,loadByCode,loadValue,physical,pcode,paddr,NativeRAM.packet_shift,Word,Packed]
  bv_decide

theorem running_no_fault_commit (b : Env) (h : V_next_fault b = (0#3)) :
    V_writeback_fire b ≠ (1#1) ∨ (b.lookup "r24" 174).setWidth 3 = (0#3) := by
  simp only [V_next_fault,V_w81,V_w32] at h
  bv_decide

theorem running_payloads (b : Env) (h : V_next_fault b = (0#3)) :
    (postCommit b).m = (physical b).m ∧ (postCommit b).x = (physical b).x ∧
    (postCommit b).w = (physical b).w ∧
    (postCommit b).count = (physical b).count ∧ (postCommit b).waitCount = (physical b).waitCount ∧
    (postCommit b).fv = (physical b).fv ∧ (postCommit b).dv = (physical b).dv ∧
    (postCommit b).xv = (physical b).xv ∧ (postCommit b).mv = (physical b).mv ∧
    (postCommit b).fi = (physical b).fi ∧ (postCommit b).di = (physical b).di := by
  rcases running_no_fault_commit b h with hf | hw
  · simp [postCommit,physical,hf,V_w274,V_w275,V_w276,V_w277,V_w278,V_w279,V_w280,
      V_w282,V_w283,V_w284,V_w285]
  · simp [postCommit,physical,hw,V_w274,V_w275,V_w276,V_w277,V_w278,V_w279,V_w280,
      V_w282,V_w283,V_w284,V_w285,V_w70,V_w71,V_w72,V_w73,V_w74,V_w75,V_w76,
      V_w77,V_w78,V_w79,V_w80,V_w32]

theorem memory_state (b : Env) (hr : V_next_fault b = (0#3)) :
    postMemory b = memoryPhysical (postCommit b) (pins b).sm (b.lookup "__native_read_0_0" 32) := by
  have hp := running_payloads b hr
  simp only [postCommit,physical] at hp
  have hm : V_w277 b = b.lookup "r23" 174 := hp.1
  have hc : V_w274 b = b.lookup "r26" 4 := hp.2.2.2.2.1
  by_cases hs : b.lookup "stall_memory" 1 = (1#1)
  all_goals by_cases hw : b.lookup "r26" 4 = (0#4)
  all_goals by_cases hv : V_w281 b = (1#1)
  all_goals
    simp only [postMemory,memoryPhysical,postCommit,physical,pins,hm,hc]
    simp only [V_w414,V_w413,V_w412,V_w343,V_w344,V_w411,V_w410,V_w385,V_w348,V_w347,
      V_w346,V_w345,V_w273,V_w142,V_w66,V_w68,V_w65,V_w67,V_w69,V_w21,
      V_w356,V_w355,V_w352,V_w350,V_w358,V_w357,V_w353,V_w349,V_w354,V_w351,V_w37,V_w139,
      V_w333,hr,load_code,finishPhysical,withValue,codeLoad,pcode,paddr,pvalue,pfault,physical,
      Word,Packed]
    simp [hs,hw,hv,hm,hc]
    all_goals bv_decide

#print axioms load_code
#print axioms running_payloads
#print axioms memory_state
end CaseCPUMem.Source
