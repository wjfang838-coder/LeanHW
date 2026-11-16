import MemIssueCircuit
open LeanRTL MemCPUShallow
open CaseCPU.Bridge (RF readRF writeRF bypass read_write_bypass)
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

theorem raw_forward_read (q : Raw.State) (r : Reg) :
    readRF (Raw.forwardRF q) r =
      bypass q.mv (Raw.instr q.m.word).rd q.m.value r
        (bypass q.wv (Raw.instr q.w.word).rd q.w.value r (readRF q.rf r)) := by
  cases hm : q.mv <;> cases hw : q.wv <;>
    simp [Raw.forwardRF,hm,hw,read_write_bypass,bypass]

theorem bypass_packet (en : Bool) (p : Packed) (q : Raw.Packet) (r : Reg) (old : Word)
    (hp : en = true → PacketRel p q)
    (hk : en = true → barrier (Raw.instr q.word).op = false) :
    bypass en (prd p) (pvalue p) r old = bypass en (Raw.instr q.word).rd q.value r old := by
  cases he : en
  · simp [bypass]
  · have h := hp he
    obtain ⟨a,ha⟩ := Raw.nonbarrier_alu _ (hk he)
    simp [bypass,h.rd,h.value,destination,ha,isStore]

theorem forward_related (p : Physical) (q : Raw.State) (mem : Memory) (r : Reg)
    (h : Related p mem q) (hb : Raw.blocked q (Raw.instr q.di).op = false) :
    forwardPhysical p r = readRF (Raw.forwardRF q) r := by
  have hn := Raw.unblocked_nonbarriers q (Raw.instr q.di).op hb
  rw [raw_forward_read]
  simp only [forwardPhysical,h.mv,h.wv,h.rf]
  rw [bypass_packet q.wv p.w q.w r (readRF q.rf r) h.writebackPacket hn.1,
    bypass_packet q.mv p.m q.m r _ h.memoryPacket hn.2]

theorem barrier_enabled (en : Bool) (p : Packed) (q : Raw.Packet)
    (h : en = true → PacketRel p q) :
    (en && codeBarrier (pcode p)) = (en && barrier (Raw.instr q.word).op) := by
  cases he : en
  · rfl
  · simp [(h he).code,code_barrier]

theorem blocked_related (p : Physical) (q : Raw.State) (mem : Memory)
    (h : Related p mem q) (hx : q.xv = false) (hd : q.dv = true)
    (hi : (decode q.di).isSome = true) :
    blockedPhysical p (codeBits p.di) = Raw.blocked q (Raw.instr q.di).op := by
  have hm := barrier_enabled q.mv p.m q.m h.memoryPacket
  have hw := barrier_enabled q.wv p.w q.w h.writebackPacket
  simp only [blockedPhysical,h.mv,h.wv,h.decodeWord hd,instruction_code q.di hi,code_barrier]
  simp only [hm,hw,Raw.blocked,hx,Bool.false_and,Bool.false_or]

theorem execute_di (b : Env) (hz : V_next_fault b = (0#3)) :
    (postExecute b).di = b.lookup "r21" 32 := (running_payloads b hz).2.2.2.2.2.2.2.2.2.2

theorem execute_kinds (q : Raw.State) (i : Raw.Pins) (hv : Raw.Valid q) :
    Raw.Kinds (beforeDispatch q i) := by
  apply Raw.kinds_execute
  apply Raw.kinds_memory
  apply Raw.kinds_commit
  exact ⟨hv.2.1,hv.2.2.1,hv.2.2.2.1,hv.2.2.2.2.1,hv.2.2.2.2.2.1⟩

#print axioms forward_related

theorem code_fence (op : Op) : (opCode op == (37#6)) = (op == .fence) := by
  cases op with
  | alu a => cases a <;> decide +kernel
  | _ => decide +kernel

theorem issue_related (b : Env) (q : Raw.State) (mem : Memory)
    (h : Related (postExecute b) mem q) (hk : Raw.Kinds q)
    (hz : V_next_fault b = (0#3)) (hg : V_w457 b = (1#1))
    (hb : V_w565 b ≠ (1#1)) (hd : q.dv = true)
    (hn : Raw.blocked q (Raw.instr q.di).op = false) :
    PacketRel (V_w727 b) (Raw.issue q q.di) := by
  have hi := hk.2.2.2.2 hd
  have hh := decode_some q.di hi
  have hw : b.lookup "r21" 32 = q.di := (execute_di b hz).symm.trans (h.decodeWord hd)
  have hc : V_w467 b = opCode (Raw.instr q.di).op := by
    rw [issue_opcode b hz hg,hw,instruction_code q.di hi]
  have args := issue_arguments b hz hg hb
  have ha : V_w577 b = readRF (Raw.forwardRF q) (Raw.instr q.di).rs1 := by
    rw [args.1,hw,forward_related _ q mem _ h hn,←decoded_rs1 q.di _ hh]
  have hr : isLoad (Raw.instr q.di).op = false → (Raw.instr q.di).op ≠ .fence →
      V_w574 b = readRF (Raw.forwardRF q) (Raw.instr q.di).rs2 := by
    intro hl hf
    rw [args.2.1,hw,forward_related _ q mem _ h hn,←decoded_rs2 q.di _ hh hl hf]
  have hm : (isLoad (Raw.instr q.di).op || isStore (Raw.instr q.di).op) = true →
      V_w580 b = (Raw.instr q.di).imm := by
    intro hm
    rw [args.2.2.1,hw,memory_immediate q.di _ hh hm]
  have hp : V_w659 b = Raw.forwardPC q := by
    simpa only [Raw.forwardPC,h.pc,h.wv,h.mv] using args.2.2.2
  have hrd : V_w660 b = (if isStore (Raw.instr q.di).op || (Raw.instr q.di).op == .fence
      then (0#5) else (b.lookup "r21" 32 >>> 7).setWidth 5) := by
    simpa only [hc,code_store,code_fence] using issue_rd b hz hg hb
  have hf := issue_fault b hz hg hb (Raw.instr q.di).op hc
  rw [issued_packet b hg hb]
  cases ho : (Raw.instr q.di).op with
  | alu a =>
    have hb' := hr (by simp [ho,isLoad]) (by simp [ho])
    have hc' : V_w467 b = opCode (.alu a) := by simpa only [ho] using hc
    have hv := circuit_alu b a hc'
    have him := decoded_calculate q.di _ a hh ho
      (readRF (Raw.forwardRF q) (Raw.instr q.di).rs1)
      (readRF (Raw.forwardRF q) (Raw.instr q.di).rs2) (Raw.forwardPC q)
    have hd' := decoded_rd q.di _ hh (by simp [ho,isStore]) (by simp [ho])
    constructor <;> simp_all [Raw.issue,destination,faultForOp,isLoad,isStore,code_store]
  | lb | lh | lw | lbu | lhu | sb | sh | sw | fence =>
    have hv : V_w694 b = (0#32) := issue_nonalu_zero b _ hc (by intro a;simp [ho])
    have him : (isLoad (Raw.instr q.di).op || isStore (Raw.instr q.di).op) = true →
        V_w614 b = readRF (Raw.forwardRF q) (Raw.instr q.di).rs1 + (Raw.instr q.di).imm := by
      intro hk
      simp only [V_w614,ha,hm hk]
    have hd' : isStore (Raw.instr q.di).op = false → (Raw.instr q.di).op ≠ .fence →
        (Raw.instr q.di).rd = (b.lookup "r21" 32 >>> 7).setWidth 5 := by
      intro hs hn
      rw [hw]
      exact decoded_rd q.di _ hh hs hn
    constructor <;> simp_all [Raw.issue,destination,faultForOp,isLoad,isStore,code_store,opCode]

#print axioms issue_related

theorem dispatch_related (b : Env) (q : Raw.State) (mem : Memory)
    (h : Related (postExecute b) mem q) (hk : Raw.Kinds q)
    (hz : V_next_fault b = (0#3)) :
    Related (postDispatch b) mem (Raw.dispatch q (pins b).sd) := by
  have hg' := issue_candidate b hz
  simp only [h.xv,h.dv] at hg'
  by_cases hg : V_w457 b = (1#1)
  · have hc : (pins b).sd = false ∧ q.xv = false ∧ q.dv = true := by
      have hh := hg'.mp hg
      bv_decide
    have hi := hk.2.2.2.2 hc.2.2
    have hb' := issue_blocked b hz hg
    have hbcode : blockedPhysical (postExecute b) (codeBits (b.lookup "r21" 32)) =
        Raw.blocked q (Raw.instr q.di).op := by
      rw [←execute_di b hz]
      exact blocked_related _ q mem h hc.2.1 hc.2.2 hi
    rw [hbcode] at hb'
    by_cases hb : V_w565 b = (1#1)
    · have hn := hb'.mp hb
      rw [dispatch_state b hz]
      simpa [hg,hb,Raw.dispatch,hc.1,hc.2.1,hc.2.2,hn] using h
    · have hn : Raw.blocked q (Raw.instr q.di).op = false := by
        have hh : Raw.blocked q (Raw.instr q.di).op ≠ true := fun hh => hb (hb'.mpr hh)
        exact Bool.eq_false_iff.mpr hh
      have hp := issue_related b q mem h hk hz hg hb hc.2.2 hn
      have hw : b.lookup "r21" 32 = q.di := (execute_di b hz).symm.trans (h.decodeWord hc.2.2)
      have hop : V_w467 b = opCode (Raw.instr q.di).op := by
        rw [issue_opcode b hz hg,hw,instruction_code q.di hi]
      have ht := issue_wait b (Raw.instr q.di).op hop
      rw [dispatch_state b hz]
      simp only [hg,hb,not_false_eq_true,and_self,↓reduceIte]
      simp only [Raw.dispatch,hc.1,hc.2.1,hc.2.2,hn,Bool.not_false,Bool.and_self,↓reduceIte]
      rcases h with ⟨hrf,hpc,hflt,hram,hfv,hdv,hxv,hmv,hwv,hcount,hwait,hfi,hdi,hx,hmemory,hwpacket⟩
      constructor <;> simp_all
  · have hn : (! (pins b).sd && !q.xv && q.dv && !Raw.blocked q (Raw.instr q.di).op) = false := by
      have hh : (! (pins b).sd && !q.xv && q.dv) ≠ true := fun hh => hg (hg'.mpr hh)
      bv_decide
    rw [dispatch_state b hz]
    simpa [hg,Raw.dispatch,hn] using h

#print axioms dispatch_related
end CaseCPUMem.Source
