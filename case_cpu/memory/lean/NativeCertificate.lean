import NativeImported
namespace CaseCPUMem.NativeCertificate
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000

theorem checked : MemCPUImported.program.checked = true := by native_decide

theorem native_shape : MemCPUImported.program.memories.length = 1 ∧
    MemCPUImported.program.reads.length = 3 ∧
    MemCPUImported.program.logic.regs.length = 27 := by decide +kernel

#print axioms checked
#print axioms native_shape
end CaseCPUMem.NativeCertificate
