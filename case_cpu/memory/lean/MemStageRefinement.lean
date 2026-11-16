import MemMemoryCommit
import MemRelation
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

noncomputable def beforeDispatch (q : Raw.State) (i : Raw.Pins) : Raw.State :=
  Raw.execute (Raw.memory (Raw.commit q i.sw) i.sm) i.sx i.delay

theorem commit_refinement (s : NativeMemory.State) (i : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q)
    (hr : (pins (NativeRAM.combInput s i)).reset = false) :
    Related (postCommit (NativeRAM.combInput s i))
      (NativeRAM.ramView (MemCPUImported.program.step s i).arrays)
      (Raw.commit q (pins (NativeRAM.combInput s i)).sw) := by
  rw [commit_state _ hr]
  apply commit_related _ q (NativeRAM.ramView s.arrays) _ _
  · simpa only [bound_physical] using h
  · exact hv
  · exact actual_memory_commit s i q h hv hr

theorem memory_read_after_commit (s : NativeMemory.State) (i : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q)
    (hm : (Raw.commit q (pins (NativeRAM.combInput s i)).sw).mv = true)
    (hl : isLoad (Raw.instr (Raw.commit q (pins (NativeRAM.combInput s i)).sw).m.word).op = true) :
    (NativeRAM.combInput s i).lookup "__native_read_0_0" 32 =
      (Raw.commit q (pins (NativeRAM.combInput s i)).sw).mem
        (addressOf (Raw.commit q (pins (NativeRAM.combInput s i)).sw).m.addr) := by
  have hc := commit_live_m q (pins (NativeRAM.combInput s i)).sw hv.1 hm
  have hp := h.memoryPacket hc.2.1
  have hl' : isLoad (Raw.instr q.m.word).op = true := by simpa only [hc.1] using hl
  have ha : (s.regs.lookup "r23" 174 >>> 35).setWidth 32 = q.m.addr := hp.addr (by simp [hl'])
  rw [hc.1,hc.2.2,←h.ram,←ha,NativeRAM.packed_address]
  exact NativeRAM.mem_read_binding s i

theorem memory_refinement (s : NativeMemory.State) (i : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q)
    (hr : (pins (NativeRAM.combInput s i)).reset = false)
    (hz : V_next_fault (NativeRAM.combInput s i) = (0#3)) :
    Related (postMemory (NativeRAM.combInput s i))
      (NativeRAM.ramView (MemCPUImported.program.step s i).arrays)
      (Raw.memory (Raw.commit q (pins (NativeRAM.combInput s i)).sw)
        (pins (NativeRAM.combInput s i)).sm) := by
  rw [memory_state _ hz]
  apply memory_related
  · exact commit_refinement s i q h hv hr
  · exact memory_read_after_commit s i q h hv

theorem execute_refinement (s : NativeMemory.State) (i : Env) (q : Raw.State)
    (h : Related (physical s.regs) (NativeRAM.ramView s.arrays) q) (hv : Raw.Valid q)
    (hr : (pins (NativeRAM.combInput s i)).reset = false)
    (hz : V_next_fault (NativeRAM.combInput s i) = (0#3)) :
    Related (postExecute (NativeRAM.combInput s i))
      (NativeRAM.ramView (MemCPUImported.program.step s i).arrays)
      (beforeDispatch q (pins (NativeRAM.combInput s i))) := by
  rw [execute_state _ hz]
  exact execute_related _ _ _ _ _ (memory_refinement s i q h hv hr hz)

#print axioms memory_read_after_commit
#print axioms execute_refinement
end CaseCPUMem.Source
