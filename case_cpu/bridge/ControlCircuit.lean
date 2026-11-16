import Physical
import Circuit
import DecoderCircuit
import StorageCircuit
import DecodeFields
open LeanRTL CPUShallow
namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

noncomputable def pinsOf (b : Env) : Pins := {
  reset := b.lookup "rst" 1 == 1, seed := b.lookup "reg_init" 1024,
  word := b.lookup "insn" 32, valid := b.lookup "insn_valid" 1 == 1,
  sf := b.lookup "stall_fetch" 1 == 1, sd := b.lookup "stall_decode" 1 == 1,
  sx := b.lookup "stall_execute" 1 == 1, sm := b.lookup "stall_memory" 1 == 1,
  sw := b.lookup "stall_writeback" 1 == 1, debug := b.lookup "debug_addr" 5 }
noncomputable def postCommit (b : Env) : Raw :=
  { rawOf b with rf := V_n_regs b, pc := V_n_pc b, wv := V_w124 b == 1 }
noncomputable def postMemory (b : Env) : Raw :=
  { postCommit b with
    wv := V_n_wv b == 1, mv := V_w146 b == 1,
    w := ⟨V_n_wi b,V_n_wval b,V_n_wpc b⟩ }
noncomputable def postExecute (b : Env) : Raw :=
  { postMemory b with
    xv := V_w174 b == 1, mv := V_n_mv b == 1,
    m := ⟨V_n_mi b,V_n_mval b,V_n_mpc b⟩, remaining := V_w104 b }
noncomputable def postDispatch (b : Env) : Raw :=
  { postExecute b with
    xv := V_n_xv b == 1, dv := V_w198 b == 1,
    x := ⟨V_n_xi b,V_n_xval b,V_n_xpc b⟩, remaining := V_n_remaining b }
noncomputable def postFetch (b : Env) : Raw :=
  { postDispatch b with dv := V_n_dv b == 1, fv := V_w214 b == 1, di := V_n_di b }
noncomputable def netNext (b : Env) : Raw := {
  rf := V_w144 b, pc := V_w143 b, fi := V_w339 b, di := V_w302 b,
  x := ⟨V_w212 b,V_w338 b,V_w211 b⟩,
  m := ⟨V_w186 b,V_w185 b,V_w184 b⟩,
  w := ⟨V_w158 b,V_w157 b,V_w156 b⟩,
  fv := V_w340 b == 1, dv := V_w303 b == 1, xv := V_w213 b == 1,
  mv := V_w187 b == 1, wv := V_w159 b == 1, remaining := V_w301 b }

theorem retire_condition (b : Env) : (V_w113 b = (1#1)) ↔
    (! (pinsOf b).reset && (rawOf b).wv && !(pinsOf b).sw) = true := by
  simp only [V_w113,V_w81,V_w10,V_w13,pinsOf,rawOf]
  bv_decide

theorem commit_state (b : Env) (hr : (pinsOf b).reset = false)
    (hw : (rawOf b).wv = true → (CaseCPU.decode (rawOf b).w.word).isSome = true) :
    postCommit b = commitRaw (rawOf b) (pinsOf b).sw := by
  have hc : (V_w113 b = (1#1)) ↔ ((rawOf b).wv && !(pinsOf b).sw) = true := by
    rw [retire_condition]
    simp [hr]
  simp only [postCommit,V_n_regs,V_n_pc,V_w124,V_w0,commitRaw,← hc]
  by_cases ht : V_w113 b = (1#1)
  · have hv : (rawOf b).wv = true := by
      have hh := hc.mp ht
      simp only [Bool.and_eq_true] at hh
      exact hh.1
    have hd := (instruction_fields (rawOf b).w.word (hw hv)).1
    simp only [rawOf] at hd
    rw [circuit_write,← hd]
    simp [ht,rawOf]
  · simp [ht,rawOf]

theorem memory_condition (b : Env) : (V_w145 b = (1#1)) ↔
    (!(pinsOf b).sm && !(postCommit b).wv) = true := by
  simp only [V_w145,V_w11,V_w141,pinsOf,postCommit]
  bv_decide

theorem memory_state (b : Env) : postMemory b = memoryRaw (postCommit b) (pinsOf b).sm := by
  simp only [postMemory,V_n_wv,V_n_wi,V_n_wval,V_n_wpc,V_w146,memoryRaw,← memory_condition]
  by_cases hm : V_w145 b = (1#1) <;> simp [hm,postCommit,rawOf]

theorem execute_state (b : Env) : postExecute b = executeRaw (postMemory b) (pinsOf b).sx := by
  by_cases hs : b.lookup "stall_execute" 1 = (1#1) <;>
    by_cases hr : b.lookup "r2" 6 = (0#6) <;>
    by_cases hm : V_w146 b = (1#1) <;>
    simp [postExecute,executeRaw,V_w174,V_n_mv,V_n_mi,V_n_mval,V_n_mpc,
      V_w169,V_w168,V_w167,V_w166,V_w165,V_w164,V_w163,V_w162,V_w161,V_w160,
      V_w104,V_w103,V_w61,V_w26,postMemory,postCommit,rawOf,pinsOf,hs,hr,hm]
    <;> bv_decide

theorem fetch_state (b : Env) : postFetch b = fetchRaw (postDispatch b) := by
  by_cases h : V_w198 b = (1#1) <;>
    simp [postFetch,fetchRaw,V_n_dv,V_n_di,V_w214,postDispatch,postExecute,postMemory,
      postCommit,rawOf,h]

theorem latency_state (b : Env) (op : Op) (h : V_w197 b = opCode op) :
    V_w218 b = BitVec.ofNat 6 (latency op - 1) := by
  cases op <;> simp [V_w218,V_w217,V_w210,V_w209,V_w207,V_w206,V_w205,V_w204,h,opCode,latency]

#print axioms commit_state
#print axioms latency_state
#print axioms memory_state
#print axioms execute_state
#print axioms fetch_state
end CaseCPU.Bridge
