import MemNativeMemory
namespace CaseCPUMem.NativeRAM
open LeanRTL LeanRTL.NativeMemory MemCPUShallow
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

noncomputable def storePlan (s : State) (i : Env) : Store :=
  let b := combInput s i
  ⟨((s.regs.lookup "r24" 174 >>> 37).setWidth 8),
    V_writeback_shifted_data b,V_writeback_mask b⟩

theorem write_mask_enabled (e : Env) (h : e.lookup "w363" 1 = (1 : BitVec 1)) :
    eval writePort.mask e = (4294967295#32) := by
  simp only [writePort,MemCPUImported.program,List.getElem_cons_zero,Option.getD_some,eval,h]
  rfl

theorem comb_address (s : State) (i : Env) :
    (program.comb s i).lookup "w365" 8 = V_w365 (combInput s i) := by
  simp only [Program.comb,program,MemCPUImported.program,Env.lookup,value_w365,
    BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rfl

theorem comb_data (s : State) (i : Env) :
    (program.comb s i).lookup "w364" 32 = V_w364 (combInput s i) := by
  simp only [Program.comb,program,MemCPUImported.program,Env.lookup,value_w364,
    BitVec.ofNat_toNat,BitVec.setWidth_eq]
  rfl

theorem bound_wb (s : State) (i : Env) :
    (combInput s i).lookup "r24" 174 = s.regs.lookup "r24" 174 := by
  simp only [combInput,oldReads,program,MemCPUImported.program,bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,Program.base,cycleEnv]
  simp [MemCPUImported.core]

theorem full_merge (m : CaseCPUMem.Memory) (st : Store) :
    updateMem m ⟨st.addr,merge (m st.addr) st,(4294967295#32)⟩ = updateMem m st := by
  funext q
  by_cases hq : q = st.addr
  · subst q
    simp [updateMem,LeanRTL.Spec.Mem.write,merge]
    exact BitVec.and_allOnes
  · simp [updateMem,LeanRTL.Spec.Mem.write,hq]

theorem enabled_write_plan (s : State) (i : Env)
    (h : V_store_commit (combInput s i) = (1 : BitVec 1)) :
    writePlan s i =
      ⟨(storePlan s i).addr,merge (ramView s.arrays (storePlan s i).addr) (storePlan s i),
        (4294967295#32)⟩ := by
  have hm : eval writePort.mask (program.comb s i) = (4294967295#32) := by
    apply write_mask_enabled
    rw [comb_enable]
    simp only [V_w363,h,↓reduceIte]
    rfl
  change Store.mk ((program.comb s i).lookup "w365" 8)
      ((program.comb s i).lookup "w364" 32) (eval writePort.mask (program.comb s i)) = _
  rw [hm,comb_address,comb_data]
  simp only [V_w365,V_w364,h,↓reduceIte,bound_wb,storePlan,merge,V_writeback_new_word,V_w311,V_w264,V_w312]
  rw [show (combInput s i).lookup "__native_read_0_1" 32 =
    ramView s.arrays ((s.regs.lookup "r24" 174 >>> 37).setWidth 8) from wb_read_binding s i]

theorem disabled_write_preserves_ram (s : State) (i : Env)
    (h : V_store_commit (combInput s i) ≠ (1 : BitVec 1)) :
    (program.step s i).arrays = s.arrays := by
  have hm : eval writePort.mask (program.comb s i) = (0#32) := by
    apply write_mask_disabled
    rw [comb_enable]
    simp only [V_w363,h,↓reduceIte]
  change writeWord s.arrays "ram" 8 32 (eval writePort.addr (program.comb s i))
    (eval writePort.data (program.comb s i)) (eval writePort.mask (program.comb s i)) = s.arrays
  rw [hm]
  exact write_disabled _ _ _ _ _ _

/-- The actual imported RTL RAM implements an atomic, masked word transaction.
    The control and byte-lane data come from certified source circuit nodes.
    This does not assume a CPU-wide step equivalence. -/
theorem actual_masked_store (s : State) (i : Env) :
    ramView (program.step s i).arrays =
      if V_store_commit (combInput s i) = (1 : BitVec 1) then
        updateMem (ramView s.arrays) (storePlan s i) else ramView s.arrays := by
  split
  · rename_i h
    rw [actual_ram_transition,enabled_write_plan s i h,full_merge]
  · rename_i h
    rw [disabled_write_preserves_ram s i h]

#print axioms actual_masked_store
end CaseCPUMem.NativeRAM
