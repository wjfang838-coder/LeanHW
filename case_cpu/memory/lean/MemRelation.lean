import MemExecuteCircuit
import MemRawBridge
namespace CaseCPUMem.Source
open CaseCPU.Bridge (writeRF)
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

/-- RAM equality here is supplied by the separately proved native masked-write
    transition. It is not a CPU-wide one-step equivalence hypothesis. -/
theorem commit_related (p : Physical) (q : Raw.State) (mem nextMem : Memory) (b : Bool)
    (h : Related p mem q) (hv : Raw.Valid q) (hm : nextMem = (Raw.commit q b).mem) :
    Related (commitPhysical p b) nextMem (Raw.commit q b) := by
  rcases h with ⟨hrf,hpc,hflt,hram,hfv,hdv,hxv,hmv,hwv,hcount,hwait,hfi,hdi,hx,hmemory,hwpacket⟩
  by_cases ha : q.fault = (0#3)
  · cases hw : q.wv
    · constructor <;> simp_all [commitPhysical,Raw.commit]
    · have hp := hwpacket hw
      have hfault := hp.fault
      have hrd := hp.rd
      have hval := hp.value
      cases hb : b
      · by_cases hf : q.w.fault = (0#3)
        · by_cases hs : (isStore (Raw.instr q.w.word).op || (Raw.instr q.w.word).op == .fence) = true
          all_goals constructor <;> simp_all [commitPhysical,Raw.commit,destination,writeRF]
        · constructor <;> simp_all [commitPhysical,Raw.commit,destination]
      · constructor <;> simp_all [commitPhysical,Raw.commit]
  · have hw : q.wv = false := (hv.2.2.2.2.2.2 ha).1
    constructor <;> simp_all [commitPhysical,Raw.commit]

theorem loadByCode_opCode (op : Op) (a w : Word) (h : isLoad op = true) :
    loadByCode (opCode op) a w = loadValue op a w := by
  cases op <;> simp_all [isLoad,loadByCode,opCode]

@[simp] theorem pword_withValue (p : Packed) (v : Word) : pword (withValue p v) = pword p := by
  simp only [pword,withValue,Packed,Word,Reg]
  bv_decide

@[simp] theorem pcode_withValue (p : Packed) (v : Word) : pcode (withValue p v) = pcode p := by
  simp only [pcode,withValue,Packed,Word,Reg]
  bv_decide

@[simp] theorem ppc_withValue (p : Packed) (v : Word) : ppc (withValue p v) = ppc p := by
  simp only [ppc,withValue,Packed,Word,Reg]
  bv_decide

@[simp] theorem prd_withValue (p : Packed) (v : Word) : prd (withValue p v) = prd p := by
  simp only [prd,withValue,Packed,Word,Reg]
  bv_decide

@[simp] theorem pvalue_withValue (p : Packed) (v : Word) : pvalue (withValue p v) = v := by
  simp only [pvalue,withValue,Packed,Word,Reg]
  bv_decide

@[simp] theorem paddr_withValue (p : Packed) (v : Word) : paddr (withValue p v) = paddr p := by
  simp only [paddr,withValue,Packed,Word,Reg]
  bv_decide

@[simp] theorem pdata_withValue (p : Packed) (v : Word) : pdata (withValue p v) = pdata p := by
  simp only [pdata,withValue,Packed,Word,Reg]
  bv_decide

@[simp] theorem pfault_withValue (p : Packed) (v : Word) : pfault (withValue p v) = pfault p := by
  simp only [pfault,withValue,Packed,Word,Reg]
  bv_decide

theorem finish_related (p : Packed) (q : Raw.Packet) (m : Memory) (word : Word)
    (h : PacketRel p q)
    (hw : isLoad (Raw.instr q.word).op = true → word = m (addressOf q.addr)) :
    PacketRel (finishPhysical p word) (Raw.finish m q) := by
  rcases h with ⟨hword,hcode,hpc,hrd,hval,hfault,haddr,hdata⟩
  by_cases hl : isLoad (Raw.instr q.word).op = true
  · have ha := haddr (by simp [hl])
    have hload : loadByCode (pcode p) (paddr p) word =
        loadValue (Raw.instr q.word).op q.addr (m (addressOf q.addr)) := by
      rw [hcode,loadByCode_opCode _ _ _ hl,ha,hw hl]
    by_cases hf : q.fault = (0#3)
    all_goals constructor <;> simp_all [finishPhysical,Raw.finish,destination,code_load]
  · constructor <;> simp_all [finishPhysical,Raw.finish,destination,code_load]

theorem memory_related (p : Physical) (q : Raw.State) (mem : Memory) (stall : Bool) (word : Word)
    (h : Related p mem q)
    (hw : q.mv = true → isLoad (Raw.instr q.m.word).op = true → word = q.mem (addressOf q.m.addr)) :
    Related (memoryPhysical p stall word) mem (Raw.memory q stall) := by
  rcases h with ⟨hrf,hpc,hflt,hram,hfv,hdv,hxv,hmv,hwv,hcount,hwait,hfi,hdi,hx,hmemory,hwpacket⟩
  have hfinish : q.mv = true → PacketRel (finishPhysical p.m word) (Raw.finish q.mem q.m) := by
    intro hm
    exact finish_related p.m q.m q.mem word (hmemory hm) (hw hm)
  cases hs : stall
  · by_cases hc : q.waitCount = (0#4)
    · cases hv : q.wv <;> constructor <;> simp_all [memoryPhysical,Raw.memory]
    · constructor <;> simp_all [memoryPhysical,Raw.memory]
  · constructor <;> simp_all [memoryPhysical,Raw.memory]

theorem execute_related (p : Physical) (q : Raw.State) (mem : Memory) (stall : Bool) (delay : BitVec 4)
    (h : Related p mem q) :
    Related (executePhysical p stall delay) mem (Raw.execute q stall delay) := by
  rcases h with ⟨hrf,hpc,hflt,hram,hfv,hdv,hxv,hmv,hwv,hcount,hwait,hfi,hdi,hx,hmemory,hwpacket⟩
  have hb : q.xv = true → codeBarrier (pcode p.x) = barrier (Raw.instr q.x.word).op := by
    intro he; rw [(hx he).code,code_barrier]
  cases hs : stall
  · by_cases hc : q.count = (0#6)
    · cases hv : q.mv <;> cases he : q.xv <;> constructor <;> simp_all [executePhysical,Raw.execute]
    · constructor <;> simp_all [executePhysical,Raw.execute]
  · constructor <;> simp_all [executePhysical,Raw.execute]

theorem commit_live_m (q : Raw.State) (b : Bool) (hi : Raw.Isolated q)
    (h : (Raw.commit q b).mv = true) :
    (Raw.commit q b).m = q.m ∧ q.mv = true ∧ (Raw.commit q b).mem = q.mem := by
  by_cases hg : (q.wv && !b) = true
  · have hw : q.wv = true := by simp_all
    by_cases hf : q.w.fault = (0#3)
    · have hm : q.mv = true := by simpa [Raw.commit,hg,hf] using h
      by_cases hs : isStore (Raw.instr q.w.word).op = true
      · have hb : barrier (Raw.instr q.w.word).op = true := by simp [barrier,hs]
        have hn := (hi.2.2 hw hb).2
        simp_all
      · simp [Raw.commit,hg,hf,hs,hm]
    · simp [Raw.commit,hg,hf] at h
  · have hm : q.mv = true := by simpa [Raw.commit,hg] using h
    simp [Raw.commit,hg,hm]

#print axioms commit_related
#print axioms finish_related
#print axioms memory_related
#print axioms execute_related
#print axioms commit_live_m
end CaseCPUMem.Source
