import ControlCircuit
import DecodeFields
open LeanRTL CPUShallow
namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

theorem decoder_valid (b : Env) : (V_w140 b != (63#6)) =
    (CaseCPU.decode (b.lookup "insn" 32)).isSome := by
  rw [circuit_w140,bits_code]
  unfold decodeCode
  cases hd : CaseCPU.decode (b.lookup "insn" 32)
  · rfl
  · rename_i ins
    change (opCode ins.op != (63#6)) = true
    cases ins.op <;> rfl

theorem ready_condition (b : Env) : (V_w333 b = (1#1)) ↔
    readyRaw (postFetch b) (pinsOf b) = true := by
  have hv := decoder_valid b
  simp only [V_w333,V_w332,V_w82,V_w288,V_w142,V_w13,V_w14,
    readyRaw,postFetch,pinsOf] at *
  bv_decide

theorem accept_condition (b : Env) : (V_w334 b = (1#1)) ↔
    ((pinsOf b).valid && readyRaw (postFetch b) (pinsOf b)) = true := by
  have hr := ready_condition b
  simp only [pinsOf,V_w334] at *
  bv_decide

theorem accept_state (b : Env) (hr : (pinsOf b).reset = false) :
    netNext b = (acceptRaw (postFetch b) (pinsOf b)).1 := by
  have hz : b.lookup "rst" 1 ≠ (1#1) := by simpa [pinsOf] using hr
  unfold acceptRaw
  simp only [← accept_condition]
  by_cases ha : V_w334 b = (1#1) <;>
    simp [netNext,V_w144,V_w143,V_w339,V_w302,V_w212,V_w338,V_w211,V_w186,V_w185,
      V_w184,V_w158,V_w157,V_w156,V_w340,V_w303,V_w213,V_w187,V_w159,V_w301,
      V_n_fv,V_n_fi,postFetch,postDispatch,postExecute,postMemory,postCommit,rawOf,
      pinsOf,hz,ha]

theorem reset_state (b : Env) (hr : (pinsOf b).reset = true) :
    netNext b = rawInitial (pinsOf b).seed := by
  have hz : b.lookup "rst" 1 = (1#1) := by simpa [pinsOf] using hr
  simp [netNext,V_w144,V_w143,V_w339,V_w302,V_w212,V_w338,V_w211,V_w186,V_w185,
    V_w184,V_w158,V_w157,V_w156,V_w340,V_w303,V_w213,V_w187,V_w159,V_w301,
    rawInitial,pinsOf,hz,circuit_reset]

#print axioms ready_condition
#print axioms accept_state
#print axioms reset_state
end CaseCPU.Bridge
