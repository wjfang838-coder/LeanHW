import MemStorageCircuit
import MemDecoderCircuit
open LeanRTL MemCPUShallow
open CaseCPU.Bridge (RF writeRF resetRF)
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def commitPhysical (p : Physical) (stall : Bool) : Physical :=
  if p.fault == (0#3) && p.wv && !stall then
    if pfault p.w != (0#3) then {
      p with
        fault := pfault p.w,fi := 0,di := 0,x := 0,m := 0,w := 0,
        fv := false,dv := false,xv := false,mv := false,wv := false,count := 0,waitCount := 0 }
    else {p with rf := writeRF p.rf (prd p.w) (pvalue p.w),pc := p.pc+4,wv := false}
  else p

theorem fire_condition (b : Env) (hr : (pins b).reset = false) :
    (V_writeback_fire b = (1#1)) ↔
      ((physical b).fault == (0#3) && (physical b).wv && !(pins b).sw) = true := by
  simp only [V_writeback_fire,V_w255,V_w254,V_w29,V_w18,V_w27,physical,pins] at *
  bv_decide

theorem commit_state (b : Env) (hr : (pins b).reset = false) :
    postCommit b = commitPhysical (physical b) (pins b).sw := by
  unfold commitPhysical
  simp only [← fire_condition b hr]
  by_cases hf : V_writeback_fire b = (1#1)
  · by_cases hw : pfault (physical b).w = (0#3)
    all_goals
      simp only [postCommit,physical,pfault] at hw ⊢
      simp only [V_next_registers,V_w361,circuit_write,V_next_committed_pc,V_next_fault,
        V_w81,V_w82,V_w0,V_w32,V_w274,V_w275,V_w276,V_w277,V_w278,V_w279,V_w280,
        V_w281,V_w282,V_w283,V_w284,V_w285,V_w70,V_w71,V_w72,V_w73,V_w74,V_w75,V_w76,
        V_w77,V_w78,V_w79,V_w80,hf,pins,prd,pvalue,pfault,BitVec.ushiftRight_zero]
      simp [hw]
  · simp [postCommit,physical,hf,V_next_registers,V_next_committed_pc,V_next_fault,
        V_w274,V_w275,V_w276,V_w277,V_w278,V_w279,V_w280,
        V_w281,V_w282,V_w283,V_w284,V_w285]

theorem store_condition (b : Env) (hr : (pins b).reset = false) :
    (V_store_commit b = (1#1)) ↔
      ((physical b).fault == (0#3) && (physical b).wv && !(pins b).sw &&
        pfault (physical b).w == (0#3) && codeStore (pcode (physical b).w)) = true := by
  simp only [V_store_commit,V_w258,V_writeback_fire,V_w255,V_w254,V_w29,V_w18,V_w27,V_w19,V_is_store_func_case_cpu_memory_rtl_cpu_sv_524_3__result,V_w143,V_w83,V_w84,V_w85,physical,pins,pfault,pcode,codeStore,Word,Packed] at *
  bv_decide

#print axioms commit_state
#print axioms store_condition
end CaseCPUMem.Source
