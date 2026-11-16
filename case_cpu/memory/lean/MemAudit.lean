import MemOutputRefinement
import MemoryDiagnosis
import MemWordRefinement
import MemEvents
import MemNativeLanes

/-! Axiom audit for the complete imported native-RAM CPU proof.
    The top-level theorems derive the circuit bridge; they do not assume it. -/
#print axioms MemoryDiagnosis.revised_determined
#print axioms CaseCPUMem.NativeCertificate.checked
#print axioms MemCPUShallow.all_values
#print axioms CaseCPUMem.NativeRAM.mem_read_binding
#print axioms CaseCPUMem.NativeRAM.wb_read_binding
#print axioms CaseCPUMem.NativeRAM.actual_ram_transition
#print axioms CaseCPUMem.NativeRAM.actual_ram_frame
#print axioms CaseCPUMem.NativeRAM.actual_reset_preserves_ram
#print axioms CaseCPUMem.NativeRAM.actual_masked_store
#print axioms CaseCPUMem.NativeRAM.actual_sb
#print axioms CaseCPUMem.NativeRAM.actual_sh
#print axioms CaseCPUMem.NativeRAM.actual_sw
#print axioms CaseCPUMem.NativeRAM.actual_wb_stall_preserves_ram
#print axioms CaseCPUMem.NativeRAM.load_lb
#print axioms CaseCPUMem.NativeRAM.load_lh
#print axioms CaseCPUMem.NativeRAM.load_lw
#print axioms CaseCPUMem.NativeRAM.load_lbu
#print axioms CaseCPUMem.NativeRAM.load_lhu
#print axioms CaseCPUMem.Raw.valid_cycle
#print axioms CaseCPUMem.Raw.word_cycle_refinement
#print axioms CaseCPUMem.Raw.word_isa_refinement
#print axioms CaseCPUMem.reset_refinement
#print axioms CaseCPUMem.cycle_conservation
#print axioms CaseCPUMem.trace_conservation
#print axioms CaseCPUMem.drained_refinement

#print axioms CaseCPUMem.Source.circuit_cycle_refinement
#print axioms CaseCPUMem.Source.rtl_isa_refinement
#print axioms CaseCPUMem.Source.retired_port_refinement
#print axioms CaseCPUMem.Source.accepted_port_refinement
#print axioms CaseCPUMem.Source.trap_rd_zero
#print axioms CaseCPUMem.Source.rtl_to_transaction_isa
#print axioms CaseCPUMem.Source.rtl_accepted_program_refinement

#print axioms CaseCPUMem.Raw.metadata_run
#print axioms CaseCPUMem.Source.reachable_retirement_payload
#print axioms CaseCPUMem.Source.retirement_store_lanes
