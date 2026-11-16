import NativeCertificate
import MemoryShallow
import Std.Tactic.BVDecide
import MemISA
namespace CaseCPUMem.NativeRAM
open LeanRTL LeanRTL.NativeMemory
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000

abbrev program := MemCPUImported.program

def ramView (arrays : Arrays) : CaseCPUMem.Memory :=
  fun a => readWord arrays "ram" 8 32 a

def oldReads (s : State) (i : Env) : Env :=
  bindReads program.reads s.arrays (program.base s i)

/-- Synthetic RAM inputs are always overwritten by real old-state RAM reads.
    Arbitrary external values supplied under these names cannot affect them. -/
theorem mem_read_binding (s : State) (i : Env) :
    (oldReads s i).lookup "__native_read_0_0" 32 =
      ramView s.arrays ((s.regs.lookup "r23" 174 >>> 37).setWidth 8) := by
  simp only [oldReads,program,MemCPUImported.program,bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,Program.base,cycleEnv]
  simp [MemCPUImported.core,ramView,readWord]
  apply BitVec.eq_of_toNat_eq
  simp

theorem wb_read_binding (s : State) (i : Env) :
    (oldReads s i).lookup "__native_read_0_1" 32 =
      ramView s.arrays ((s.regs.lookup "r24" 174 >>> 37).setWidth 8) := by
  simp only [oldReads,program,MemCPUImported.program,bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,Program.base,cycleEnv]
  simp [MemCPUImported.core,ramView,readWord]
  apply BitVec.eq_of_toNat_eq
  simp

theorem debug_read_binding (s : State) (i : Env) :
    (oldReads s i).lookup "__native_read_0_2" 32 =
      ramView s.arrays (i.lookup "debug_mem_addr" 8) := by
  simp only [oldReads,program,MemCPUImported.program,bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,Program.base,cycleEnv]
  simp [MemCPUImported.core,ramView,readWord]
  apply BitVec.eq_of_toNat_eq
  simp

def writePort : WritePort 8 32 :=
  (MemCPUImported.program.memories[0].write).getD ⟨.const 0,.const 0,.const 0⟩

def writePlan (s : State) (i : Env) : Store :=
  let e := program.comb s i
  ⟨eval writePort.addr e,eval writePort.data e,eval writePort.mask e⟩

theorem ram_write_view (a : Arrays) (addr : Address) (data mask : Word) :
    ramView (writeWord a "ram" 8 32 addr data mask) =
      updateMem (ramView a) ⟨addr,data,mask⟩ := by
  funext q
  by_cases hq : q = addr
  · subst q
    simp only [ramView,read_write_same,updateMem,merge,LeanRTL.Spec.Mem.write,↓reduceIte]
  · rw [ramView,read_write_other a "ram" "ram" 8 32 addr q data mask (Or.inr hq)]
    simp [updateMem,LeanRTL.Spec.Mem.write,hq,ramView]

/-- A theorem about the actual native-memory imported design, independent of
    the unfinished CPU control/datapath connection. No memory oracle is assumed. -/
theorem actual_ram_transition (s : State) (i : Env) :
    ramView (program.step s i).arrays = updateMem (ramView s.arrays) (writePlan s i) := by
  change ramView (writeWord s.arrays "ram" 8 32 _ _ _) = _
  exact ram_write_view _ _ _ _

theorem actual_ram_frame (s : State) (i : Env) (q : Address)
    (h : q ≠ (writePlan s i).addr) :
    ramView (program.step s i).arrays q = ramView s.arrays q := by
  rw [actual_ram_transition]
  exact memory_frame _ _ _ h

theorem write_mask_disabled (e : Env) (h : e.lookup "w363" 1 = (0#1)) :
    eval writePort.mask e = (0#32) := by
  simp only [writePort,MemCPUImported.program,List.getElem_cons_zero,Option.getD_some,eval,h]
  rfl

noncomputable def combInput (s : State) (i : Env) : Env := oldReads s i

theorem bound_rst (s : State) (i : Env) :
    (combInput s i).lookup "rst" 1 = i.lookup "rst" 1 := by
  simp only [combInput,oldReads,program,MemCPUImported.program,bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,Program.base,cycleEnv]
  simp [MemCPUImported.core]

theorem control_reset_no_write (b : Env) (h : b.lookup "rst" 1 = (1#1)) :
    MemCPUShallow.V_w363 b = (0#1) := by
  simp only [MemCPUShallow.V_w363, MemCPUShallow.V_store_commit, MemCPUShallow.V_w258, MemCPUShallow.V_writeback_fire, MemCPUShallow.V_w255, MemCPUShallow.V_w254, MemCPUShallow.V_w29, MemCPUShallow.V_w18, MemCPUShallow.V_w27, MemCPUShallow.V_w19, MemCPUShallow.V_is_store_func_case_cpu_memory_rtl_cpu_sv_524_3__result, MemCPUShallow.V_w143, MemCPUShallow.V_w83, MemCPUShallow.V_w84, MemCPUShallow.V_w85,h]
  bv_decide

theorem comb_enable (s : State) (i : Env) :
    (program.comb s i).lookup "w363" 1 = MemCPUShallow.V_w363 (combInput s i) := by
  simp only [Program.comb,program,MemCPUImported.program,Env.lookup,MemCPUShallow.value_w363,
    BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rfl

/-- Reset preservation is proved for the actual native imported RAM transition,
    not merely for the ISA's abstract memory field. -/
theorem actual_reset_preserves_ram (s : State) (i : Env) (h : i.lookup "rst" 1 = (1#1)) :
    (program.step s i).arrays = s.arrays := by
  have he : (program.comb s i).lookup "w363" 1 = (0#1) := by
    rw [comb_enable]
    exact control_reset_no_write _ (by rw [bound_rst]; exact h)
  have hm := write_mask_disabled (program.comb s i) he
  change writeWord s.arrays "ram" 8 32 (eval writePort.addr (program.comb s i))
    (eval writePort.data (program.comb s i)) (eval writePort.mask (program.comb s i)) = s.arrays
  rw [hm]
  exact write_disabled _ _ _ _ _ _

#print axioms mem_read_binding
#print axioms actual_ram_transition
#print axioms actual_reset_preserves_ram
end CaseCPUMem.NativeRAM
