import MemTraceRefinement
import MemMetadata
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

theorem port_retire_pc (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "retire_pc" 32 = V_w304 (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 32 (BitVec.ofNat 32 (evalWires MemCPUImported.core.wires
    (NativeRAM.combInput s (pinEnv i o)) "w304")).toNat = _
  rw [value_w304]
  simp

theorem retiring_conditions (s : NativeMemory.State) (i : Raw.Pins) (o : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q)
    (hf : port s i o "retire_valid" 1 = (1#1)) :
    i.reset = false ∧ q.fault = (0#3) ∧ q.wv = true ∧ i.sw = false := by
  rw [port_retire_valid] at hf
  have hh := fire_boolean (NativeRAM.combInput s (pinEnv i o))
  rw [hf,bound_physical,bound_pins,h.fault,h.wv] at hh
  bv_decide

theorem effect_value_metadata (p : Raw.Packet) (m : Memory) (h : Raw.ZeroValue p) :
    (Raw.effect m true p).value = p.value := by
  by_cases hf : p.fault = (0#3)
  · cases ho : (Raw.instr p.word).op <;> simp_all [Raw.effect,Raw.ZeroValue,isLoad,isStore]
  · simp_all [Raw.effect,Raw.ZeroValue]

theorem effect_rd_destination (p : Raw.Packet) (m : Memory) :
    (Raw.effect m true p).rd = (if p.fault != (0#3) then 0 else destination p) := by
  by_cases hf : p.fault = (0#3)
  all_goals cases ho : (Raw.instr p.word).op <;> simp [Raw.effect,destination,hf,ho,isLoad,isStore]

/-- Retiring PC is the current architectural PC, not a speculative successor. -/
theorem retirement_pc (s : NativeMemory.State) (i : Raw.Pins) (o : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hm : Raw.Metadata q)
    (hf : port s i o "retire_valid" 1 = (1#1)) :
    port s i o "retire_pc" 32 = (architecture s).pc := by
  have hw := (retiring_conditions s i o q h hf).2.2.1
  have hp := (h.writebackPacket hw).pc
  rw [port_retire_pc]
  have hfire := hf
  rw [port_retire_valid] at hfire
  rw [V_w304,hfire]
  simp only [↓reduceIte,bound_r24]
  change ppc (physical s.regs).w = (physical s.regs).pc
  rw [hp,(hm.1.1 hw),h.pc]

/-- RD/result outputs agree with the committed effect, including x0, stores,
    FENCE and precise faults. The effect is ISA-derived by the upper invariant. -/
theorem retirement_result (s : NativeMemory.State) (i : Raw.Pins) (o : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hm : Raw.Metadata q)
    (hf : port s i o "retire_valid" 1 = (1#1)) :
    port s i o "retire_rd" 5 = (Raw.effect q.mem true q.w).rd ∧
    port s i o "retire_value" 32 = (Raw.effect q.mem true q.w).value := by
  let b := NativeRAM.combInput s (pinEnv i o)
  have hw := (retiring_conditions s i o q h hf).2.2.1
  have hp : PacketRel (physical b).w q.w := by rw [bound_physical];exact h.writebackPacket hw
  have hrd := hp.rd
  have hval := hp.value
  have hft := hp.fault
  simp only [physical,prd,pvalue,pfault] at hrd hval hft
  have hfire : V_writeback_fire b = (1#1) := by simpa only [port_retire_valid] using hf
  rw [port_retire_rd,port_retire_value,effect_rd_destination,
    effect_value_metadata q.w q.mem (hm.2.1 hw)]
  change V_w305 b = (if q.w.fault != (0#3) then 0 else destination q.w) ∧ V_w306 b = q.w.value
  delta V_w305 V_w258 V_w19 V_w306
  simp only [hfire,BitVec.reduceEq,↓reduceIte,hft,hrd,hval]
  by_cases ht : q.w.fault = (0#3) <;> simp [ht,hft,hrd,hval]

theorem writeback_isa_effect (q : Raw.State) (hi : Inv (Raw.project q)) (hw : q.wv = true) :
    Raw.effect q.mem true q.w = effectFor (Raw.project q).arch (Raw.instr q.w.word) := by
  simpa [Inv,checked,Raw.project,Raw.optPacket,Raw.packet,hw] using hi.1

#print axioms retirement_pc
#print axioms retirement_result
#print axioms Raw.metadata_run

theorem port_retire_store (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "retire_store" 1 = V_store_commit (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 1 (BitVec.ofNat 1 (evalWires MemCPUImported.core.wires
    (NativeRAM.combInput s (pinEnv i o)) "store_commit")).toNat = _
  rw [value_store_commit]
  simp

theorem port_retire_store_data (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "retire_store_data" 32 = V_w375 (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 32 (BitVec.ofNat 32 (evalWires MemCPUImported.core.wires
    (NativeRAM.combInput s (pinEnv i o)) "w375")).toNat = _
  rw [value_w375]
  simp

theorem port_retire_store_mask (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    port s i o "retire_store_mask" 32 = V_w376 (NativeRAM.combInput s (pinEnv i o)) := by
  change BitVec.ofNat 32 (BitVec.ofNat 32 (evalWires MemCPUImported.core.wires
    (NativeRAM.combInput s (pinEnv i o)) "w376")).toNat = _
  rw [value_w376]
  simp

theorem store_packet_lanes (b : Env) (p : Raw.Packet) (h : PacketRel (physical b).w p)
    (hs : isStore (Raw.instr p.word).op = true) :
    V_writeback_shifted_data b = (storeEffect (Raw.instr p.word).op p.addr p.data).data ∧
    V_writeback_mask b = (storeEffect (Raw.instr p.word).op p.addr p.data).mask := by
  have ha := h.addr (by simp [hs])
  have hd := h.data hs
  constructor
  · simp only [storeEffect]
    rw [←ha,←hd]
    simp only [physical,paddr,pdata,V_writeback_shifted_data,NativeRAM.packet_shift]
  · simp only [storeEffect]
    cases ho : (Raw.instr p.word).op
    all_goals simp only [ho,isStore] at hs
    all_goals try contradiction
    all_goals rw [←ha]
    · exact NativeRAM.mask_sb b (by simpa [ho,opCode] using h.code)
    · exact NativeRAM.mask_sh b (by simpa [ho,opCode] using h.code)
    · exact NativeRAM.mask_sw b (by simpa [ho,opCode] using h.code)

theorem retirement_store_lanes (s : NativeMemory.State) (i : Raw.Pins) (o : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q)
    (hv : Raw.Valid q) (hs : port s i o "retire_store" 1 = (1#1)) :
    isStore (Raw.instr q.w.word).op = true ∧ q.w.fault = (0#3) ∧
    port s i o "retire_store_data" 32 = (storeEffect (Raw.instr q.w.word).op q.w.addr q.w.data).data ∧
    port s i o "retire_store_mask" 32 = (storeEffect (Raw.instr q.w.word).op q.w.addr q.w.data).mask := by
  let b := NativeRAM.combInput s (pinEnv i o)
  rw [port_retire_store] at hs
  have hf : V_writeback_fire b = (1#1) := by
    delta V_store_commit V_w258 at hs
    bv_decide
  have hfv : port s i o "retire_valid" 1 = (1#1) := by rw [port_retire_valid];exact hf
  have hc := retiring_conditions s i o q h hfv
  have hh := store_related b (NativeRAM.ramView s.arrays) q (by rw [bound_physical];exact h)
    (by rw [bound_pins];exact hc.1)
  have hsr : q.w.fault = (0#3) ∧ isStore (Raw.instr q.w.word).op = true := by
    have hp := hh.mp hs
    simp only [Bool.and_eq_true,beq_iff_eq] at hp
    exact ⟨hp.1.2,hp.2⟩
  have hpk : PacketRel (physical b).w q.w := by rw [bound_physical];exact h.writebackPacket hc.2.2.1
  have hl := store_packet_lanes b q.w hpk hsr.2
  refine ⟨hsr.2,hsr.1,?_,?_⟩
  · rw [port_retire_store_data,V_w375,hs]
    exact hl.1
  · rw [port_retire_store_mask,V_w376,hs]
    exact hl.2

#print axioms retirement_store_lanes

theorem reachable_retirement_payload (s : NativeMemory.State) (seed : CaseCPU.Bridge.RF)
    (o : Env) (xs : List (Raw.Pins × Env)) (i : Raw.Pins) (nextChoices : Env)
    (hf : port (circuitRun (rtlStep s {reset := true,seed := seed} o) xs) i nextChoices
      "retire_valid" 1 = (1#1)) :
    let t := circuitRun (rtlStep s {reset := true,seed := seed} o) xs
    let q := Raw.run (Raw.initial seed (NativeRAM.ramView s.arrays)) (xs.map Prod.fst)
    let e := effectFor (architecture t) (Raw.instr q.w.word)
    port t i nextChoices "retire_pc" 32 = (architecture t).pc ∧
    port t i nextChoices "retire_rd" 5 = e.rd ∧ port t i nextChoices "retire_value" 32 = e.value := by
  let t := circuitRun (rtlStep s {reset := true,seed := seed} o) xs
  let q := Raw.run (Raw.initial seed (NativeRAM.ramView s.arrays)) (xs.map Prod.fst)
  have hb := boot_related s seed o
  have hv := Raw.valid_initial seed (NativeRAM.ramView s.arrays)
  have h : Related (physical t.regs) (NativeRAM.ramView t.arrays) q := circuit_run_related _ _ xs hb hv
  have hm : Raw.Metadata q := Raw.metadata_run _ _ (Raw.metadata_initial _ _)
  have hi : Inv (Raw.project q) := by
    dsimp [q]
    rw [Raw.word_cycle_refinement]
    exact run_inv _ _ (initial_inv _ _)
  have hw := (retiring_conditions t i nextChoices q h hf).2.2.1
  have he : Raw.effect q.mem true q.w = effectFor (architecture t) (Raw.instr q.w.word) := by
    rw [related_architecture t q h]
    exact writeback_isa_effect q hi hw
  have hp := retirement_pc t i nextChoices q h hm hf
  have hr := retirement_result t i nextChoices q h hm hf
  rw [he] at hr
  exact ⟨hp,hr⟩

#print axioms reachable_retirement_payload
end CaseCPUMem.Source
