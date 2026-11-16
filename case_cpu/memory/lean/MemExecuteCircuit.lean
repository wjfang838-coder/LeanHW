import MemMemoryCircuit
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def executePhysical (p : Physical) (stall : Bool) (delay : BitVec 4) : Physical :=
  if stall then p else if p.count != (0#6) then {p with count := p.count-1} else
  if p.mv then p else {
    p with
      m := p.x,mv := p.xv,xv := false,
      waitCount := if p.xv && codeBarrier (pcode p.x) then delay else 0 }

theorem execute_state (b : Env) (hr : V_next_fault b = (0#3)) :
    postExecute b = executePhysical (postMemory b) (pins b).sx (pins b).delay := by
  have hp := running_payloads b hr
  simp only [postCommit,physical] at hp
  have hx : V_w278 b = b.lookup "r22" 174 := hp.2.1
  have hc : V_w275 b = b.lookup "r25" 6 := hp.2.2.2.1
  by_cases hs : b.lookup "stall_execute" 1 = (1#1)
  all_goals by_cases hw : b.lookup "r25" 6 = (0#6)
  all_goals by_cases hv : V_w358 b = (1#1)
  all_goals
    simp only [postExecute,executePhysical,postMemory,postCommit,physical,pins,hx,hc]
    simp only [V_w405,V_w404,V_w401,V_w34,V_w400,V_w407,V_w406,V_w402,V_w399,V_w409,V_w408,V_w403,V_w398,V_w342,V_w341,V_w140,V_w471,V_w470,V_w469,V_w468,V_w455,V_w432,V_w431,V_w397,V_w396,V_w395,V_w394,V_w340,V_w272,V_w64,V_w63,V_w62,V_w61,V_w60,V_w393,V_w392,V_w391,V_w390,V_w339,V_w271,V_w59,V_w58,V_w57,V_w17,V_w333,hr,codeBarrier,codeLoad,codeStore,pcode,Packed]
    simp [hs,hw,hv,hx,hc]
    all_goals bv_decide

#print axioms execute_state
end CaseCPUMem.Source
