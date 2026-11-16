import ImportedData
namespace CaseCPU.Bridge
open LeanRTL
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

theorem imported_checks : V2LeanImported.core.checkErrors = [] := by native_decide
theorem imported_widths : V2LeanImported.core.wellWidthedb = true := by native_decide
theorem imported_state_shape :
    V2LeanImported.core.latches = [] ∧ V2LeanImported.core.reset = none ∧
    V2LeanImported.core.clock = some "clk" ∧
    (V2LeanImported.core.regs.map (·.negedge)).all (! ·) = true ∧
    (V2LeanImported.core.regs.map (·.emitInit)).any id = false := by decide +kernel
#print axioms imported_checks
#print axioms imported_widths
#print axioms imported_state_shape
end CaseCPU.Bridge
