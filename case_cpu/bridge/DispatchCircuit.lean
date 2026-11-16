import Forwarding
open LeanRTL CPUShallow
namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem dispatch_condition (b : Env) : (V_w190 b = (1#1)) ↔
    (!(pinsOf b).sd && !(postExecute b).xv && (postExecute b).dv) = true := by
  simp only [V_w190,V_w189,V_w12,V_w182,pinsOf,postExecute,postMemory,postCommit,rawOf]
  bv_decide

theorem projected_pc (b : Env) : V_w176 b = forwardPC (postExecute b) := by
  simp only [V_w176,V_w152,V_w151,V_w175,forwardPC,postExecute,postMemory,postCommit,rawOf,Word]
  bv_decide

theorem dispatch_state (b : Env) (h : Legal (postExecute b)) :
    postDispatch b = dispatchRaw (postExecute b) (pinsOf b).sd := by
  have hc := dispatch_condition b
  have hdi : (postExecute b).di = b.lookup "r11" 32 := rfl
  unfold dispatchRaw
  simp only [← hc]
  by_cases hd : V_w190 b = (1#1)
  · have hv : (postExecute b).dv = true := by
      have hh := hc.mp hd
      simp only [Bool.and_eq_true] at hh
      exact hh.2
    have hi := h.2.1 hv
    rw [hdi] at hi
    have hop : V_w197 b = opCode (instruction (b.lookup "r11" 32)).op := by
      have hh := instruction_code (b.lookup "r11" 32) hi
      simp only [V_w197,hd,↓reduceIte,circuit_w137]
      exact hh
    have ha : V_w249 b = readRF (forwardRF (postExecute b))
        (instruction (b.lookup "r11" 32)).rs1 := by
      simp only [V_w249,hd,↓reduceIte]
      rw [forward_a,forward_state b _ h,(instruction_fields _ hi).2.1]
      rfl
    have hb : V_w195 b = readRF (forwardRF (postExecute b))
        (instruction (b.lookup "r11" 32)).rs2 := by
      simp only [V_w195,hd,↓reduceIte]
      rw [forward_b,forward_state b _ h,(instruction_fields _ hi).2.2.1]
      rfl
    have hv := circuit_alu b _ hop
    rw [circuit_immediate,ha,hb,projected_pc,calculate_immediate _ _ _ _ hi] at hv
    have hw := latency_state b _ hop
    simp [postDispatch,V_n_xv,V_w198,V_n_xi,V_n_xpc,V_n_xval,V_n_remaining,
      hd,hv,hw,projected_pc,hdi,postExecute,postMemory,postCommit,rawOf]
  · simp [postDispatch,V_n_xv,V_w198,V_n_xi,V_n_xpc,V_n_xval,V_n_remaining,
      hd,postExecute,postMemory,postCommit,rawOf]

#print axioms dispatch_state
end CaseCPU.Bridge
