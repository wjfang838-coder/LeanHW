import Shallow
import ControlCircuit
namespace CaseCPU.Bridge
open LeanRTL CPUShallow
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
theorem step_r0 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r0" 32 = V_w184 (base r i o) := by
  have hs : rtlStep r i o "r0" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w184")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w184]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r1 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r1" 32 = V_w156 (base r i o) := by
  have hs : rtlStep r i o "r1" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w156")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w156]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r2 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r2" 6 = V_w301 (base r i o) := by
  have hs : rtlStep r i o "r2" = (BitVec.ofNat 6 (evalWires V2LeanImported.core.wires (base r i o) "w301")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w301]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r3 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r3" 1024 = V_w144 (base r i o) := by
  have hs : rtlStep r i o "r3" = (BitVec.ofNat 1024 (evalWires V2LeanImported.core.wires (base r i o) "w144")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w144]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r4 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r4" 32 = V_w143 (base r i o) := by
  have hs : rtlStep r i o "r4" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w143")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w143]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r5 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r5" 1 = V_w340 (base r i o) := by
  have hs : rtlStep r i o "r5" = (BitVec.ofNat 1 (evalWires V2LeanImported.core.wires (base r i o) "w340")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w340]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r6 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r6" 1 = V_w303 (base r i o) := by
  have hs : rtlStep r i o "r6" = (BitVec.ofNat 1 (evalWires V2LeanImported.core.wires (base r i o) "w303")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w303]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r7 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r7" 1 = V_w213 (base r i o) := by
  have hs : rtlStep r i o "r7" = (BitVec.ofNat 1 (evalWires V2LeanImported.core.wires (base r i o) "w213")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w213]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r8 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r8" 1 = V_w187 (base r i o) := by
  have hs : rtlStep r i o "r8" = (BitVec.ofNat 1 (evalWires V2LeanImported.core.wires (base r i o) "w187")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w187]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r9 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r9" 1 = V_w159 (base r i o) := by
  have hs : rtlStep r i o "r9" = (BitVec.ofNat 1 (evalWires V2LeanImported.core.wires (base r i o) "w159")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w159]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r10 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r10" 32 = V_w339 (base r i o) := by
  have hs : rtlStep r i o "r10" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w339")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w339]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r11 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r11" 32 = V_w302 (base r i o) := by
  have hs : rtlStep r i o "r11" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w302")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w302]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r12 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r12" 32 = V_w212 (base r i o) := by
  have hs : rtlStep r i o "r12" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w212")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w212]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r13 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r13" 32 = V_w186 (base r i o) := by
  have hs : rtlStep r i o "r13" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w186")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w186]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r14 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r14" 32 = V_w158 (base r i o) := by
  have hs : rtlStep r i o "r14" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w158")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w158]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r15 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r15" 32 = V_w338 (base r i o) := by
  have hs : rtlStep r i o "r15" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w338")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w338]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r16 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r16" 32 = V_w185 (base r i o) := by
  have hs : rtlStep r i o "r16" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w185")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w185]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r17 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r17" 32 = V_w157 (base r i o) := by
  have hs : rtlStep r i o "r17" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w157")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w157]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem step_r18 (r : Env) (i : Pins) (o : Env) :
    (rtlStep r i o).lookup "r18" 32 = V_w211 (base r i o) := by
  have hs : rtlStep r i o "r18" = (BitVec.ofNat 32 (evalWires V2LeanImported.core.wires (base r i o) "w211")).toNat := rfl
  unfold Env.lookup
  rw [hs,value_w211]
  simp only [BitVec.ofNat_toNat,BitVec.setWidth_eq]
theorem actual_step (r : Env) (i : Pins) (o : Env) :
    rawOf (rtlStep r i o) = netNext (base r i o) := by
  simp only [rawOf,netNext,step_r0, step_r1, step_r2, step_r3, step_r4, step_r5, step_r6, step_r7, step_r8, step_r9, step_r10, step_r11, step_r12, step_r13, step_r14, step_r15, step_r16, step_r17, step_r18]
theorem bool_bit (b : Bool) : (BitVec.ofNat 1 b.toNat == 1) = b := by
  cases b <;> rfl

theorem base_r0 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r0" 32 = r.lookup "r0" 32 := by rfl
theorem base_r1 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r1" 32 = r.lookup "r1" 32 := by rfl
theorem base_r2 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r2" 6 = r.lookup "r2" 6 := by rfl
theorem base_r3 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r3" 1024 = r.lookup "r3" 1024 := by rfl
theorem base_r4 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r4" 32 = r.lookup "r4" 32 := by rfl
theorem base_r5 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r5" 1 = r.lookup "r5" 1 := by rfl
theorem base_r6 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r6" 1 = r.lookup "r6" 1 := by rfl
theorem base_r7 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r7" 1 = r.lookup "r7" 1 := by rfl
theorem base_r8 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r8" 1 = r.lookup "r8" 1 := by rfl
theorem base_r9 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r9" 1 = r.lookup "r9" 1 := by rfl
theorem base_r10 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r10" 32 = r.lookup "r10" 32 := by rfl
theorem base_r11 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r11" 32 = r.lookup "r11" 32 := by rfl
theorem base_r12 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r12" 32 = r.lookup "r12" 32 := by rfl
theorem base_r13 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r13" 32 = r.lookup "r13" 32 := by rfl
theorem base_r14 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r14" 32 = r.lookup "r14" 32 := by rfl
theorem base_r15 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r15" 32 = r.lookup "r15" 32 := by rfl
theorem base_r16 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r16" 32 = r.lookup "r16" 32 := by rfl
theorem base_r17 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r17" 32 = r.lookup "r17" 32 := by rfl
theorem base_r18 (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "r18" 32 = r.lookup "r18" 32 := by rfl
theorem base_rst (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "rst" 1 = BitVec.ofNat 1 i.reset.toNat := by
  simp [base,cycleEnv,V2LeanImported.core,pinEnv,Env.lookup]
theorem base_reg_init (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "reg_init" 1024 = i.seed := by
  simp [base,cycleEnv,V2LeanImported.core,pinEnv,Env.lookup]
theorem base_insn (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "insn" 32 = i.word := by
  simp [base,cycleEnv,V2LeanImported.core,pinEnv,Env.lookup]
theorem base_insn_valid (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "insn_valid" 1 = BitVec.ofNat 1 i.valid.toNat := by
  simp [base,cycleEnv,V2LeanImported.core,pinEnv,Env.lookup]
theorem base_stall_fetch (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "stall_fetch" 1 = BitVec.ofNat 1 i.sf.toNat := by
  simp [base,cycleEnv,V2LeanImported.core,pinEnv,Env.lookup]
theorem base_stall_decode (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "stall_decode" 1 = BitVec.ofNat 1 i.sd.toNat := by
  simp [base,cycleEnv,V2LeanImported.core,pinEnv,Env.lookup]
theorem base_stall_execute (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "stall_execute" 1 = BitVec.ofNat 1 i.sx.toNat := by
  simp [base,cycleEnv,V2LeanImported.core,pinEnv,Env.lookup]
theorem base_stall_memory (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "stall_memory" 1 = BitVec.ofNat 1 i.sm.toNat := by
  simp [base,cycleEnv,V2LeanImported.core,pinEnv,Env.lookup]
theorem base_stall_writeback (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "stall_writeback" 1 = BitVec.ofNat 1 i.sw.toNat := by
  simp [base,cycleEnv,V2LeanImported.core,pinEnv,Env.lookup]
theorem base_debug_addr (r : Env) (i : Pins) (o : Env) :
    (base r i o).lookup "debug_addr" 5 = i.debug := by
  simp [base,cycleEnv,V2LeanImported.core,pinEnv,Env.lookup]
theorem base_raw (r : Env) (i : Pins) (o : Env) : rawOf (base r i o) = rawOf r := by
  simp only [rawOf,base_r0, base_r1, base_r2, base_r3, base_r4, base_r5, base_r6, base_r7, base_r8, base_r9, base_r10, base_r11, base_r12, base_r13, base_r14, base_r15, base_r16, base_r17, base_r18]
theorem base_pins (r : Env) (i : Pins) (o : Env) : pinsOf (base r i o) = i := by
  simp only [pinsOf,base_rst, base_reg_init, base_insn, base_insn_valid, base_stall_fetch, base_stall_decode, base_stall_execute, base_stall_memory, base_stall_writeback, base_debug_addr, bool_bit]
#print axioms actual_step
end CaseCPU.Bridge
