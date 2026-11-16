import MemRawProof
namespace CaseCPUMem.Raw
open CaseCPU.Bridge (RF readRF writeRF resetRF read_writeRF read_resetRF)
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem read_rf_zero (rf : RF) : readRF rf (0#5) = 0 := by simp [readRF]

theorem write_rf_function (rf : RF) (rd : Reg) (v : Word) :
    readRF (writeRF rf rd v) = fun q => if q = (0#5) then 0 else if q = rd then v else readRF rf q := by
  funext q
  rw [read_writeRF]
  by_cases hq : q = (0#5)
  · subst q; simp [readRF]
  · simp [hq]

theorem zero_effect_regs (rf : RF) :
    (fun q => if q = (0#5) then (0#32) else if q = (0#5) then 0 else readRF rf q) = readRF rf := by
  funext q
  by_cases hq : q = (0#5) <;> simp [hq,readRF]

theorem project_commit_running (s : State) (stall : Bool)
    (hi : Isolated s) (ha : s.fault = (0#3)) :
    project (commit s stall) = (retire (project s) stall).1 := by
  cases hs : stall
  · cases hw : s.wv
    · simp [commit,retire,project,optPacket,hw,hs]
    · by_cases hf : s.w.fault = (0#3)
      · cases hop : (instr s.w.word).op
        all_goals
          have he := hi.2.2 hw
          try have hb : barrier (instr s.w.word).op = true := by simp [barrier,isLoad,isStore,hop]
          try have hx := (he hb).1
          try have hm := (he hb).2
          simp [*,commit,retire,project,optPacket,packet,effect,applyEffect,
            isLoad,isStore,write_rf_function,zero_effect_regs]
          try { funext q; by_cases hq : q = (0#5) <;> simp [hq,readRF] }
      · simp [commit,retire,project,optPacket,optInstr,packet,effect,applyEffect,
          hs,hw,hf,ha]
  · simp [commit,retire,hs]

theorem nonbarrier_alu (op : Op) (h : barrier op = false) : ∃ a, op = .alu a := by
  cases op <;> simp_all [barrier,isLoad,isStore]

theorem advance_nonbarrier (rf : RF) (pc : Word) (mem : Memory) (en : Bool) (p : Packet)
    (h : en = true → barrier (instr p.word).op = false ∧ p.fault = (0#3)) :
    advance ⟨readRF rf,pc,mem,(0#3)⟩ (optPacket mem true en p) =
      ⟨readRF (if en then writeRF rf (instr p.word).rd p.value else rf),
        pc+(if en then 4 else 0),mem,(0#3)⟩ := by
  cases he : en
  · simp [advance,optPacket,he]
  · obtain ⟨op,hop⟩ := nonbarrier_alu _ (h he).1
    simp [advance,optPacket,he,packet,effect,(h he).2,hop,applyEffect,write_rf_function]

theorem unblocked_nonbarriers (s : State) (op : Op) (h : blocked s op = false) :
    (s.wv = true → barrier (instr s.w.word).op = false) ∧
    (s.mv = true → barrier (instr s.m.word).op = false) := by
  unfold blocked at h
  bv_decide

theorem forwarded_project (s : State) (op : Op) (h : blocked s op = false)
    (hk : Kinds s) (ha : s.fault = (0#3)) :
    forwarded (project s) = ⟨readRF (forwardRF s),forwardPC s,s.mem,(0#3)⟩ := by
  have hb := unblocked_nonbarriers s op h
  have hw : s.wv = true → barrier (instr s.w.word).op = false ∧ s.w.fault = (0#3) := by
    intro he; exact ⟨hb.1 he,(hk.2.2.1 he).2 (hb.1 he)⟩
  have hm : s.mv = true → barrier (instr s.m.word).op = false ∧ s.m.fault = (0#3) := by
    intro he; exact ⟨hb.2 he,(hk.2.1 he).2 (hb.2 he)⟩
  have hm' : optPacket s.mem false s.mv s.m = optPacket s.mem true s.mv s.m := by
    cases he : s.mv
    · simp [optPacket,he]
    · obtain ⟨a,hop⟩ := nonbarrier_alu _ (hm he).1
      simp [optPacket,he,packet,effect,hop]
  unfold forwarded project
  simp only [ha,hm',advance_nonbarrier _ _ _ _ _ hw,advance_nonbarrier _ _ _ _ _ hm]
  rfl

theorem blocked_project (s : State) (op : Op) :
    CaseCPUMem.blocked (project s) op = blocked s op := by
  cases hx : s.xv <;> cases hm : s.mv <;> cases hw : s.wv <;>
    simp [CaseCPUMem.blocked,blocked,project,optPacket,packetBarrier,packet,backendEmpty,hx,hm,hw]

theorem readReg_rf (rf : RF) (pc : Word) (mem : Memory) (r : Reg) :
    readReg ⟨readRF rf,pc,mem,(0#3)⟩ r = readRF rf r := by
  by_cases hr : r = (0#5) <;> simp [readReg,hr,readRF]

theorem issue_packet (s : State) (w : Word) :
    packet s.mem false (issue s w) =
      ⟨instr w,effectFor ⟨readRF (forwardRF s),forwardPC s,s.mem,(0#3)⟩ (instr w),forwardPC s⟩ := by
  cases hop : (instr w).op <;>
    simp [packet,issue,hop,effectFor,effect,readReg_rf,isLoad,isStore]

theorem latency_fits (op : Op) :
    (BitVec.ofNat 6 (latency op-1)).toNat = latency op-1 := by
  cases op with
  | alu a => cases a <;> decide +kernel
  | _ => decide +kernel

theorem latency_mod (op : Op) : (latency op-1)%64 = latency op-1 := by
  simpa only [BitVec.toNat_ofNat] using latency_fits op

theorem project_dispatch_running (s : State) (stall : Bool)
    (hk : Kinds s) (ha : s.fault = (0#3)) :
    project (dispatch s stall) = CaseCPUMem.dispatch (project s) stall := by
  cases hs : stall
  · cases hx : s.xv <;> cases hd : s.dv
    · simp [dispatch,CaseCPUMem.dispatch,project,optInstr,optPacket,hs,hx,hd]
    · have hx' : (project s).execute = none := by simp [project,optPacket,hx]
      have hd' : (project s).decodeStage = some (instr s.di) := by simp [project,optInstr,hd]
      cases hb : blocked s (instr s.di).op
      · have hf := forwarded_project s (instr s.di).op hb hk ha
        simp only [CaseCPUMem.dispatch,hs,Bool.false_eq_true,↓reduceIte,hx',hd',
          blocked_project,hb,hf]
        simp [dispatch,project,optInstr,optPacket,hs,hx,hd,hb,issue_packet,latency_mod]
      · simp only [CaseCPUMem.dispatch,hs,Bool.false_eq_true,↓reduceIte,hx',hd',
          blocked_project,hb]
        simp [dispatch,hs,hx,hd,hb]
    · simp [dispatch,CaseCPUMem.dispatch,project,optInstr,optPacket,hs,hx,hd]
    · simp [dispatch,CaseCPUMem.dispatch,project,optInstr,optPacket,hs,hx,hd]
  · simp [dispatch,CaseCPUMem.dispatch,hs]

def HaltedEmpty (s : State) : Prop :=
  s.fault ≠ (0#3) → s.wv = false ∧ s.mv = false ∧ s.xv = false ∧ s.dv = false ∧ s.fv = false

theorem halted_commit (s : State) (b : Bool) (h : HaltedEmpty s) : HaltedEmpty (commit s b) := by
  unfold commit
  split <;> try exact h
  split
  · simp [HaltedEmpty]
  · intro hf; exact ⟨rfl,(h hf).2⟩

@[simp] theorem memory_fault (s : State) (b : Bool) : (memory s b).fault = s.fault := by
  unfold memory; split <;> try rfl
  split <;> try rfl
  split <;> rfl
@[simp] theorem execute_fault (s : State) (b : Bool) (d : BitVec 4) : (execute s b d).fault = s.fault := by
  unfold execute; split <;> try rfl
  split <;> try rfl
  split <;> rfl
@[simp] theorem dispatch_fault (s : State) (b : Bool) : (dispatch s b).fault = s.fault := by
  unfold dispatch; split <;> rfl
@[simp] theorem fetch_fault (s : State) : (fetch s).fault = s.fault := by
  unfold fetch; split <;> rfl
@[simp] theorem accept_fault (s : State) (i : Pins) : (accept s i).fault = s.fault := by
  unfold accept; split <;> rfl

theorem halted_cycle (s : State) (i : Pins) (h : HaltedEmpty s) : HaltedEmpty (cycle s i) := by
  cases hr : i.reset
  · simp only [cycle,hr,Bool.false_eq_true,↓reduceIte]
    change HaltedEmpty (if (commit s i.sw).fault != (0#3) then commit s i.sw else
      accept (fetch (dispatch (execute (memory (commit s i.sw) i.sm) i.sx i.delay) i.sd)) i)
    split
    · exact halted_commit s i.sw h
    · rename_i hf
      have hz : (commit s i.sw).fault = (0#3) := by simpa using hf
      unfold HaltedEmpty
      simp [hz]
  · simp [cycle,hr,HaltedEmpty,initial]

theorem valid_initial (seed : RF) (m : Memory) : Valid (initial seed m) := by
  exact ⟨isolated_initial _ _,(kinds_initial _ _).1,(kinds_initial _ _).2.1,
    (kinds_initial _ _).2.2.1,(kinds_initial _ _).2.2.2.1,(kinds_initial _ _).2.2.2.2,by simp [initial]⟩

theorem valid_cycle (s : State) (i : Pins) (h : Valid s) : Valid (cycle s i) := by
  have hk : Kinds s := ⟨h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩
  have hn := kinds_cycle s i hk
  exact ⟨isolated_cycle _ _ h.1,hn.1,hn.2.1,hn.2.2.1,hn.2.2.2.1,hn.2.2.2.2,halted_cycle s i h.2.2.2.2.2.2⟩

theorem project_commit (s : State) (b : Bool) (h : Valid s) :
    project (commit s b) = (retire (project s) b).1 := by
  by_cases ha : s.fault = (0#3)
  · exact project_commit_running s b h.1 ha
  · have hw := (h.2.2.2.2.2.2 ha).1
    cases b <;> simp [commit,retire,project,optPacket,hw]

theorem project_cycle (s : State) (i : Pins) (h : Valid s) :
    project (cycle s i) = (CaseCPUMem.cycle (project s) (input i)).state := by
  cases hi : i.reset
  · have hk : Kinds (commit s i.sw) := kinds_commit _ _
        ⟨h.2.1,h.2.2.1,h.2.2.2.1,h.2.2.2.2.1,h.2.2.2.2.2.1⟩
    have hc := project_commit s i.sw h
    generalize he : retire (project s) i.sw = ev at hc ⊢
    have hc' : ev.1 = project (commit s i.sw) := hc.symm
    have hev : ev = (project (commit s i.sw),ev.2) := by rw [←hc']
    simp only [CaseCPUMem.cycle,cycle,hi,input,Bool.false_eq_true,↓reduceIte]
    rw [he,hev]
    change project (if (commit s i.sw).fault != (0#3) then commit s i.sw else
        accept (fetch (dispatch (execute (memory (commit s i.sw) i.sm) i.sx i.delay) i.sd)) i) =
      (if (commit s i.sw).fault != (0#3) then
        Outcome.mk (project (commit s i.sw)) ev.2 false
      else
        let s2 := moveMemory (project (commit s i.sw)) i.sm
        let s3 := moveExecute s2 i.sx i.delay
        let s4 := CaseCPUMem.dispatch s3 i.sd
        let s5 := moveFetch s4
        let ac := CaseCPUMem.accept s5 (input i)
        Outcome.mk ac.1 ev.2 ac.2).state
    split
    · rfl
    · rename_i hf
      have hz : (commit s i.sw).fault = (0#3) := by simpa using hf
      rw [project_accept _ _ hi,project_fetch,
        project_dispatch_running _ _ (kinds_execute _ _ _ (kinds_memory _ _ hk)) (by simpa using hz),
        project_execute,project_memory]
  · simpa [cycle,CaseCPUMem.cycle,hi,input] using project_initial i.seed s.mem

#print axioms valid_cycle
#print axioms project_cycle
end CaseCPUMem.Raw
