import MemPhysical
open LeanRTL MemCPUShallow
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false
theorem step_r12 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r12" 1024 = V_w371 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r12" =
      (BitVec.ofNat 1024 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w371")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w371]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r13 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r13" 32 = V_w297 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r13" =
      (BitVec.ofNat 32 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w297")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w297]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r14 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r14" 3 = V_w296 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r14" =
      (BitVec.ofNat 3 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w296")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w296]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r15 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r15" 1 = V_w720 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r15" =
      (BitVec.ofNat 1 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w720")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w720]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r16 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r16" 1 = V_w669 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r16" =
      (BitVec.ofNat 1 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w669")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w669]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r17 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r17" 1 = V_w598 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r17" =
      (BitVec.ofNat 1 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w598")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w598]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r18 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r18" 1 = V_w422 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r18" =
      (BitVec.ofNat 1 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w422")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w422]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r19 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r19" 1 = V_w370 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r19" =
      (BitVec.ofNat 1 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w370")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w370]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r20 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r20" 32 = V_w719 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r20" =
      (BitVec.ofNat 32 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w719")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w719]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r21 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r21" 32 = V_w668 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r21" =
      (BitVec.ofNat 32 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w668")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w668]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r22 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r22" 174 = V_w729 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r22" =
      (BitVec.ofNat 174 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w729")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w729]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r23 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r23" 174 = V_w421 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r23" =
      (BitVec.ofNat 174 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w421")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w421]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r24 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r24" 174 = V_w420 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r24" =
      (BitVec.ofNat 174 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w420")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w420]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r25 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r25" 6 = V_w597 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r25" =
      (BitVec.ofNat 6 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w597")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w597]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r26 (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (rtlStep s i o).regs.lookup "r26" 4 = V_w473 (NativeRAM.combInput s (pinEnv i o)) := by
  have hs : (rtlStep s i o).regs "r26" =
      (BitVec.ofNat 4 (evalWires MemCPUImported.core.wires (NativeRAM.combInput s (pinEnv i o)) "w473")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w473]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem actual_state (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    physical (rtlStep s i o).regs = netNext (NativeRAM.combInput s (pinEnv i o)) := by
  simp only [physical,netNext,step_r12,step_r13,step_r14,step_r15,step_r16,step_r17,step_r18,step_r19,step_r20,step_r21,step_r22,step_r23,step_r24,step_r25,step_r26]
theorem bound_r12 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r12" 1024 = s.regs.lookup "r12" 1024 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r13 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r13" 32 = s.regs.lookup "r13" 32 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r14 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r14" 3 = s.regs.lookup "r14" 3 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r15 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r15" 1 = s.regs.lookup "r15" 1 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r16 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r16" 1 = s.regs.lookup "r16" 1 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r17 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r17" 1 = s.regs.lookup "r17" 1 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r18 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r18" 1 = s.regs.lookup "r18" 1 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r19 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r19" 1 = s.regs.lookup "r19" 1 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r20 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r20" 32 = s.regs.lookup "r20" 32 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r21 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r21" 32 = s.regs.lookup "r21" 32 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r22 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r22" 174 = s.regs.lookup "r22" 174 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r23 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r23" 174 = s.regs.lookup "r23" 174 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r24 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r24" 174 = s.regs.lookup "r24" 174 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r25 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r25" 6 = s.regs.lookup "r25" 6 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_r26 (s : NativeMemory.State) (i : Env) :
    (NativeRAM.combInput s i).lookup "r26" 4 = s.regs.lookup "r26" 4 := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core]
theorem bound_physical (s : NativeMemory.State) (i : Env) :
    physical (NativeRAM.combInput s i) = physical s.regs := by
  simp only [physical,bound_r12,bound_r13,bound_r14,bound_r15,bound_r16,bound_r17,bound_r18,bound_r19,bound_r20,bound_r21,bound_r22,bound_r23,bound_r24,bound_r25,bound_r26]
theorem bound_pin_rst (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "rst" 1 = BitVec.ofNat 1 i.reset.toNat := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_reg_init (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "reg_init" 1024 = i.seed := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_insn (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "insn" 32 = i.word := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_insn_valid (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "insn_valid" 1 = BitVec.ofNat 1 i.valid.toNat := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_stall_fetch (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "stall_fetch" 1 = BitVec.ofNat 1 i.sf.toNat := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_stall_decode (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "stall_decode" 1 = BitVec.ofNat 1 i.sd.toNat := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_stall_execute (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "stall_execute" 1 = BitVec.ofNat 1 i.sx.toNat := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_stall_memory (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "stall_memory" 1 = BitVec.ofNat 1 i.sm.toNat := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_stall_writeback (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "stall_writeback" 1 = BitVec.ofNat 1 i.sw.toNat := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_memory_delay (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "memory_delay" 4 = i.delay := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_debug_reg_addr (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "debug_reg_addr" 5 = i.debugReg := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bound_pin_debug_mem_addr (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    (NativeRAM.combInput s (pinEnv i o)).lookup "debug_mem_addr" 8 = i.debugMem := by
  simp only [NativeRAM.combInput,NativeRAM.oldReads,NativeRAM.program,MemCPUImported.program,NativeMemory.bindReads,List.foldl_cons,List.foldl_nil]
  simp only [Env.lookup,eval,NativeMemory.Program.base,cycleEnv]
  simp [MemCPUImported.core,pinEnv]
theorem bool_bit (b : Bool) : (BitVec.ofNat 1 b.toNat == 1) = b := by cases b <;> rfl
theorem bound_pins (s : NativeMemory.State) (i : Raw.Pins) (o : Env) :
    pins (NativeRAM.combInput s (pinEnv i o)) = i := by
  simp only [pins,bound_pin_rst,bound_pin_reg_init,bound_pin_insn,bound_pin_insn_valid,bound_pin_stall_fetch,bound_pin_stall_decode,bound_pin_stall_execute,bound_pin_stall_memory,bound_pin_stall_writeback,bound_pin_memory_delay,bound_pin_debug_reg_addr,bound_pin_debug_mem_addr,bool_bit]
#print axioms actual_state
end CaseCPUMem.Source
