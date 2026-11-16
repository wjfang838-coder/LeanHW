import MemNetlistStep
import MemControlCircuit
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem store_related (b : Env) (mem : Memory) (q : Raw.State)
    (h : Related (physical b) mem q) (hr : (pins b).reset = false) :
    (V_store_commit b = (1#1)) ↔
      (q.fault == (0#3) && q.wv && !(pins b).sw && q.w.fault == (0#3) &&
        isStore (Raw.instr q.w.word).op) = true := by
  rw [store_condition b hr,h.fault,h.wv]
  cases hw : q.wv
  · simp
  · have hp := h.writebackPacket hw
    rw [hp.fault,hp.code,code_store]

theorem actual_memory_commit (s : NativeMemory.State) (i : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q)
    (hr : (pins (NativeRAM.combInput s i)).reset = false) :
    NativeRAM.ramView (MemCPUImported.program.step s i).arrays =
      (Raw.commit q (pins (NativeRAM.combInput s i)).sw).mem := by
  let b := NativeRAM.combInput s i
  have hrel : Related (physical b) (NativeRAM.ramView s.arrays) q := by
    simpa only [b,bound_physical] using h
  have hg := store_related b (NativeRAM.ramView s.arrays) q hrel hr
  cases hw : q.wv
  · have hc : V_store_commit b ≠ (1#1) := by simp only [ne_eq,hg]; simp [hw]
    rw [NativeRAM.disabled_write_preserves_ram s i hc]
    simpa [Raw.commit,hw] using h.ram
  · have ha : q.fault = (0#3) := by
      by_cases hz : q.fault = (0#3)
      · exact hz
      · have hh := (hv.2.2.2.2.2.2 hz).1
        simp_all
    have hp := h.writebackPacket hw
    cases hs : (pins b).sw
    · by_cases hf : q.w.fault = (0#3)
      · cases hop : (Raw.instr q.w.word).op with
        | alu a =>
          have hc : V_store_commit b ≠ (1#1) := by simp only [ne_eq,hg]; simp [hop,isStore]
          rw [NativeRAM.disabled_write_preserves_ram s i hc]
          simpa [Raw.commit,hw,hs,hf,hop,isStore,b] using h.ram
        | lb =>
          have hc : V_store_commit b ≠ (1#1) := by simp only [ne_eq,hg]; simp [hop,isStore]
          rw [NativeRAM.disabled_write_preserves_ram s i hc]
          simpa [Raw.commit,hw,hs,hf,hop,isStore,b] using h.ram
        | lh =>
          have hc : V_store_commit b ≠ (1#1) := by simp only [ne_eq,hg]; simp [hop,isStore]
          rw [NativeRAM.disabled_write_preserves_ram s i hc]
          simpa [Raw.commit,hw,hs,hf,hop,isStore,b] using h.ram
        | lw =>
          have hc : V_store_commit b ≠ (1#1) := by simp only [ne_eq,hg]; simp [hop,isStore]
          rw [NativeRAM.disabled_write_preserves_ram s i hc]
          simpa [Raw.commit,hw,hs,hf,hop,isStore,b] using h.ram
        | lbu =>
          have hc : V_store_commit b ≠ (1#1) := by simp only [ne_eq,hg]; simp [hop,isStore]
          rw [NativeRAM.disabled_write_preserves_ram s i hc]
          simpa [Raw.commit,hw,hs,hf,hop,isStore,b] using h.ram
        | lhu =>
          have hc : V_store_commit b ≠ (1#1) := by simp only [ne_eq,hg]; simp [hop,isStore]
          rw [NativeRAM.disabled_write_preserves_ram s i hc]
          simpa [Raw.commit,hw,hs,hf,hop,isStore,b] using h.ram
        | sb =>
          have hc : V_store_commit b = (1#1) := by simp only [ne_eq,hg]; simp [ha,hw,hs,hf,hop,isStore]
          have hop' : (s.regs.lookup "r24" 174 >>> 136).setWidth 6 = (34#6) := by
            simpa only [physical,pcode,hop,opCode] using hp.code
          have haddr : (s.regs.lookup "r24" 174 >>> 35).setWidth 32 = q.w.addr :=
            hp.addr (by simp [hop,isLoad,isStore])
          have hdata : (s.regs.lookup "r24" 174 >>> 3).setWidth 32 = q.w.data :=
            hp.data (by simp [hop,isStore])
          rw [NativeRAM.actual_sb s i hc hop',haddr,hdata,h.ram]
          simp [Raw.commit,hw,hs,hf,hop,isStore,b]
        | sh =>
          have hc : V_store_commit b = (1#1) := by simp only [ne_eq,hg]; simp [ha,hw,hs,hf,hop,isStore]
          have hop' : (s.regs.lookup "r24" 174 >>> 136).setWidth 6 = (35#6) := by
            simpa only [physical,pcode,hop,opCode] using hp.code
          have haddr : (s.regs.lookup "r24" 174 >>> 35).setWidth 32 = q.w.addr :=
            hp.addr (by simp [hop,isLoad,isStore])
          have hdata : (s.regs.lookup "r24" 174 >>> 3).setWidth 32 = q.w.data :=
            hp.data (by simp [hop,isStore])
          rw [NativeRAM.actual_sh s i hc hop',haddr,hdata,h.ram]
          simp [Raw.commit,hw,hs,hf,hop,isStore,b]
        | sw =>
          have hc : V_store_commit b = (1#1) := by simp only [ne_eq,hg]; simp [ha,hw,hs,hf,hop,isStore]
          have hop' : (s.regs.lookup "r24" 174 >>> 136).setWidth 6 = (36#6) := by
            simpa only [physical,pcode,hop,opCode] using hp.code
          have haddr : (s.regs.lookup "r24" 174 >>> 35).setWidth 32 = q.w.addr :=
            hp.addr (by simp [hop,isLoad,isStore])
          have hdata : (s.regs.lookup "r24" 174 >>> 3).setWidth 32 = q.w.data :=
            hp.data (by simp [hop,isStore])
          rw [NativeRAM.actual_sw s i hc hop',haddr,hdata,h.ram]
          simp [Raw.commit,hw,hs,hf,hop,isStore,b]
        | fence =>
          have hc : V_store_commit b ≠ (1#1) := by simp only [ne_eq,hg]; simp [hop,isStore]
          rw [NativeRAM.disabled_write_preserves_ram s i hc]
          simpa [Raw.commit,hw,hs,hf,hop,isStore,b] using h.ram
      · have hc : V_store_commit b ≠ (1#1) := by simp only [ne_eq,hg]; simp [hf]
        rw [NativeRAM.disabled_write_preserves_ram s i hc]
        simpa [Raw.commit,hw,hs,hf,b] using h.ram
    · have hc : V_store_commit b ≠ (1#1) := by simp only [ne_eq,hg]; simp [hs]
      rw [NativeRAM.disabled_write_preserves_ram s i hc]
      simpa [Raw.commit,hw,hs,b] using h.ram

#print axioms actual_memory_commit
end CaseCPUMem.Source
