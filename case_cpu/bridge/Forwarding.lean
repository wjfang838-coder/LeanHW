import ControlCircuit
import DecodeFields
open LeanRTL CPUShallow
namespace CaseCPU.Bridge
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false

def bypass (en : Bool) (rd : CaseCPU.Reg) (v : Word) (q : CaseCPU.Reg) (old : Word) : Word :=
  if en && (rd != 0) && (rd == q) then v else old

theorem read_write_bypass (rf : RF) (rd q : CaseCPU.Reg) (v : Word) :
    readRF (writeRF rf rd v) q = bypass true rd v q (readRF rf q) := by
  rw [read_writeRF]
  by_cases hq : q = (0#5)
  · subst q; simp [bypass,readRF]
  · by_cases h : rd = q
    · subst rd; simp [bypass,hq]
    · simp [bypass,hq,h,Ne.symm h]

theorem forward_read (s : Raw) (q : CaseCPU.Reg) :
    readRF (forwardRF s) q =
      bypass s.mv (instruction s.m.word).rd s.m.value q
        (bypass s.wv (instruction s.w.word).rd s.w.value q (readRF s.rf q)) := by
  cases hm : s.mv <;> cases hw : s.wv <;>
    simp [forwardRF,hm,hw,read_write_bypass,bypass]

noncomputable def physicalForward (b : Env) (q : CaseCPU.Reg) : Word :=
  bypass (V_n_mv b == 1) ((V_n_mi b >>> 7).setWidth 5) (V_n_mval b) q
    (bypass (V_n_wv b == 1) ((V_n_wi b >>> 7).setWidth 5) (V_n_wval b) q
      (readRF (V_n_regs b) q))

theorem forward_a (b : Env) : V_w248 b = physicalForward b ((b.lookup "r11" 32 >>> 15).setWidth 5) := by
  simp only [V_w248,V_w208,V_w192,V_w183,V_w178,V_w196,V_w191,V_w180,V_w155,V_w153,
    V_w133,V_w2,V_w127,physicalForward,bypass]
  simp only [readRF,offset,CaseCPU.Reg,Word,RF]
  bv_decide

theorem forward_b (b : Env) : V_w194 b = physicalForward b ((b.lookup "r11" 32 >>> 20).setWidth 5) := by
  simp only [V_w194,V_w193,V_w192,V_w183,V_w179,V_w188,V_w181,V_w180,V_w155,V_w154,
    V_w134,V_w3,V_w128,physicalForward,bypass]
  simp only [readRF,offset,CaseCPU.Reg,Word,RF]
  bv_decide

theorem bypass_instruction (en : Bool) (p : RawPacket) (q : CaseCPU.Reg) (old : Word)
    (h : en = true → (CaseCPU.decode p.word).isSome = true) :
    bypass en ((p.word >>> 7).setWidth 5) p.value q old =
      bypass en (instruction p.word).rd p.value q old := by
  cases he : en
  · rfl
  · rw [(instruction_fields p.word (h he)).1]

theorem forward_state (b : Env) (q : CaseCPU.Reg) (h : Legal (postExecute b)) :
    physicalForward b q = readRF (forwardRF (postExecute b)) q := by
  rw [forward_read]
  have hw := h.2.2.2.2
  have hm := h.2.2.2.1
  have hew := bypass_instruction (postExecute b).wv (postExecute b).w q
    (readRF (postExecute b).rf q) hw
  have hem := bypass_instruction (postExecute b).mv (postExecute b).m q
    (bypass (postExecute b).wv (instruction (postExecute b).w.word).rd
      (postExecute b).w.value q (readRF (postExecute b).rf q)) hm
  unfold physicalForward
  change bypass (postExecute b).mv (((postExecute b).m.word >>> 7).setWidth 5)
    (postExecute b).m.value q
      (bypass (postExecute b).wv (((postExecute b).w.word >>> 7).setWidth 5)
        (postExecute b).w.value q (readRF (postExecute b).rf q)) = _
  rw [hew,hem]

#print axioms forward_state
#print axioms forward_a
#print axioms forward_b
end CaseCPU.Bridge
