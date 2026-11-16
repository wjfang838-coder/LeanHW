import MemNativeStore
namespace CaseCPUMem.NativeRAM
open LeanRTL LeanRTL.NativeMemory MemCPUShallow
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

theorem packet_shift (p : BitVec 174) :
    byteShift ((p >>> 35).setWidth 32) = (((p >>> 35).setWidth 2) ++ (0#3)).toNat := by
  have hs : ((p >>> 35).setWidth 32).setWidth 2 = (p >>> 35).setWidth 2 := by bv_decide
  simp only [byteShift,hs,BitVec.toNat_append,BitVec.toNat_ofNat,Nat.zero_mod,Nat.add_zero,Nat.or_zero,Nat.shiftLeft_eq]

theorem nat_shift_word (n k : Nat) :
    BitVec.ofNat 32 (n <<< k) = (BitVec.ofNat 32 n) <<< k := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_shiftLeft,Nat.shiftLeft_eq,Nat.mul_mod]

theorem mask_sb (b : Env) (h : (b.lookup "r24" 174 >>> 136).setWidth 6 = (34#6)) :
    V_writeback_mask b = storeMask .sb ((b.lookup "r24" 174 >>> 35).setWidth 32) := by
  simp only [V_writeback_mask,V_w161,V_w84,V_w83,V_w247,V_w136,V_w248,V_w85,V_w135,storeMask,packet_shift]
  have hd : (b.lookup "r24" 174 >>> 35).setWidth 2 = (0#2) ∨
      (b.lookup "r24" 174 >>> 35).setWidth 2 = (1#2) ∨
      (b.lookup "r24" 174 >>> 35).setWidth 2 = (2#2) ∨
      (b.lookup "r24" 174 >>> 35).setWidth 2 = (3#2) := by bv_decide
  rcases hd with hd | hd | hd | hd
  all_goals rw [hd]; bv_decide

theorem mask_sh (b : Env) (h : (b.lookup "r24" 174 >>> 136).setWidth 6 = (35#6)) :
    V_writeback_mask b = storeMask .sh ((b.lookup "r24" 174 >>> 35).setWidth 32) := by
  simp only [V_writeback_mask,V_w161,V_w84,V_w83,V_w247,V_w136,V_w248,V_w85,V_w135,storeMask,packet_shift]
  have hd : (b.lookup "r24" 174 >>> 35).setWidth 2 = (0#2) ∨
      (b.lookup "r24" 174 >>> 35).setWidth 2 = (1#2) ∨
      (b.lookup "r24" 174 >>> 35).setWidth 2 = (2#2) ∨
      (b.lookup "r24" 174 >>> 35).setWidth 2 = (3#2) := by bv_decide
  rcases hd with hd | hd | hd | hd
  all_goals rw [hd]; bv_decide

theorem mask_sw (b : Env) (h : (b.lookup "r24" 174 >>> 136).setWidth 6 = (36#6)) :
    V_writeback_mask b = storeMask .sw ((b.lookup "r24" 174 >>> 35).setWidth 32) := by
  simp only [V_writeback_mask,V_w161,V_w84,V_w83,V_w247,V_w136,V_w248,V_w85,V_w135,storeMask,packet_shift]
  have hd : (b.lookup "r24" 174 >>> 35).setWidth 2 = (0#2) ∨
      (b.lookup "r24" 174 >>> 35).setWidth 2 = (1#2) ∨
      (b.lookup "r24" 174 >>> 35).setWidth 2 = (2#2) ∨
      (b.lookup "r24" 174 >>> 35).setWidth 2 = (3#2) := by bv_decide
  rcases hd with hd | hd | hd | hd
  all_goals rw [hd]; bv_decide

theorem load_lb (b : Env) (h : (b.lookup "r23" 174 >>> 136).setWidth 6 = (29#6)) :
    V_w178 b = loadValue .lb ((b.lookup "r23" 174 >>> 35).setWidth 32)
      (b.lookup "__native_read_0_0" 32) := by
  simp only [V_w178,V_w162,V_w66,V_w65,V_w67,V_w175,V_w174,V_w138,V_w177,V_w68,V_w176,V_w69,loadValue,packet_shift]
  bv_decide

theorem load_lh (b : Env) (h : (b.lookup "r23" 174 >>> 136).setWidth 6 = (30#6)) :
    V_w178 b = loadValue .lh ((b.lookup "r23" 174 >>> 35).setWidth 32)
      (b.lookup "__native_read_0_0" 32) := by
  simp only [V_w178,V_w162,V_w66,V_w65,V_w67,V_w175,V_w174,V_w138,V_w177,V_w68,V_w176,V_w69,loadValue,packet_shift]
  bv_decide

theorem load_lw (b : Env) (h : (b.lookup "r23" 174 >>> 136).setWidth 6 = (31#6)) :
    V_w178 b = loadValue .lw ((b.lookup "r23" 174 >>> 35).setWidth 32)
      (b.lookup "__native_read_0_0" 32) := by
  simp only [V_w178,V_w162,V_w66,V_w65,V_w67,V_w175,V_w174,V_w138,V_w177,V_w68,V_w176,V_w69,loadValue,packet_shift]
  bv_decide

theorem load_lbu (b : Env) (h : (b.lookup "r23" 174 >>> 136).setWidth 6 = (32#6)) :
    V_w178 b = loadValue .lbu ((b.lookup "r23" 174 >>> 35).setWidth 32)
      (b.lookup "__native_read_0_0" 32) := by
  simp only [V_w178,V_w162,V_w66,V_w65,V_w67,V_w175,V_w174,V_w138,V_w177,V_w68,V_w176,V_w69,loadValue,packet_shift]
  bv_decide

theorem load_lhu (b : Env) (h : (b.lookup "r23" 174 >>> 136).setWidth 6 = (33#6)) :
    V_w178 b = loadValue .lhu ((b.lookup "r23" 174 >>> 35).setWidth 32)
      (b.lookup "__native_read_0_0" 32) := by
  simp only [V_w178,V_w162,V_w66,V_w65,V_w67,V_w175,V_w174,V_w138,V_w177,V_w68,V_w176,V_w69,loadValue,packet_shift]
  bv_decide

theorem packed_address (p : BitVec 174) :
    addressOf ((p >>> 35).setWidth 32) = (p >>> 37).setWidth 8 := by
  simp only [addressOf,Word,Address]
  bv_decide

theorem shifted_store_data (b : Env) : V_writeback_shifted_data b =
    ((b.lookup "r24" 174 >>> 3).setWidth 32) <<<
      byteShift ((b.lookup "r24" 174 >>> 35).setWidth 32) := by
  rw [packet_shift]
  unfold V_writeback_shifted_data
  rfl

theorem actual_sb (s : State) (i : Env)
    (hc : V_store_commit (combInput s i) = (1 : BitVec 1))
    (hop : (s.regs.lookup "r24" 174 >>> 136).setWidth 6 = (34#6)) :
    ramView (program.step s i).arrays = updateMem (ramView s.arrays)
      (storeEffect .sb ((s.regs.lookup "r24" 174 >>> 35).setWidth 32)
        ((s.regs.lookup "r24" 174 >>> 3).setWidth 32)) := by
  rw [actual_masked_store]
  simp only [hc,↓reduceIte]
  have hm := mask_sb (combInput s i) (by rw [bound_wb]; exact hop)
  simp only [storePlan,hm,shifted_store_data,bound_wb,storeEffect,packed_address]

theorem actual_sh (s : State) (i : Env)
    (hc : V_store_commit (combInput s i) = (1 : BitVec 1))
    (hop : (s.regs.lookup "r24" 174 >>> 136).setWidth 6 = (35#6)) :
    ramView (program.step s i).arrays = updateMem (ramView s.arrays)
      (storeEffect .sh ((s.regs.lookup "r24" 174 >>> 35).setWidth 32)
        ((s.regs.lookup "r24" 174 >>> 3).setWidth 32)) := by
  rw [actual_masked_store]
  simp only [hc,↓reduceIte]
  have hm := mask_sh (combInput s i) (by rw [bound_wb]; exact hop)
  simp only [storePlan,hm,shifted_store_data,bound_wb,storeEffect,packed_address]

theorem actual_sw (s : State) (i : Env)
    (hc : V_store_commit (combInput s i) = (1 : BitVec 1))
    (hop : (s.regs.lookup "r24" 174 >>> 136).setWidth 6 = (36#6)) :
    ramView (program.step s i).arrays = updateMem (ramView s.arrays)
      (storeEffect .sw ((s.regs.lookup "r24" 174 >>> 35).setWidth 32)
        ((s.regs.lookup "r24" 174 >>> 3).setWidth 32)) := by
  rw [actual_masked_store]
  simp only [hc,↓reduceIte]
  have hm := mask_sw (combInput s i) (by rw [bound_wb]; exact hop)
  simp only [storePlan,hm,shifted_store_data,bound_wb,storeEffect,packed_address]

theorem control_stall_no_write (b : Env) (h : b.lookup "stall_writeback" 1 = (1#1)) :
    V_store_commit b ≠ (1 : BitVec 1) := by
  simp only [V_store_commit,V_w258,V_writeback_fire,V_w255,V_w254,V_w29,V_w18,V_w27,V_w19,V_is_store_func_case_cpu_memory_rtl_cpu_sv_524_3__result,V_w143,V_w83,V_w84,V_w85,h]
  bv_decide

theorem bound_stall (s : State) (i : Env) :
    (combInput s i).lookup "stall_writeback" 1 = i.lookup "stall_writeback" 1 := by
  simp only [combInput,oldReads,program,MemCPUImported.program,bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,Program.base,cycleEnv]
  simp [MemCPUImported.core]

theorem actual_wb_stall_preserves_ram (s : State) (i : Env)
    (h : i.lookup "stall_writeback" 1 = (1#1)) : (program.step s i).arrays = s.arrays := by
  apply disabled_write_preserves_ram
  exact control_stall_no_write _ (by rw [bound_stall]; exact h)

#print axioms mask_sb
#print axioms load_lb
#print axioms actual_sb
#print axioms actual_wb_stall_preserves_ram
end CaseCPUMem.NativeRAM
