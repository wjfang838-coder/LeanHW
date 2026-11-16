import LeanRTL.Core.Compiler
import LeanRTL.Core.Check
import LeanRTL.Core.Coverage
import LeanRTL.Core.ProcVerilog
open LeanRTL

def layout : Module := {
  name := "layout"
  inputs := [{name := "a", width := 3}, {name := "b", width := 3}]
  outputs := [{name := "y", width := 3, expr := .xor (.var "a" 3) (.var "b" 3)},
              {name := "lt", width := 1, expr := .ult (.var "a" 3) (.var "b" 3)},
              {name := "slt", width := 1, expr := .slt (.var "a" 3) (.var "b" 3)}]
  portOrder := ["y", "a", "b", "lt", "slt"]
  portLayouts := [{name := "a", signed := true, offset := 1},
                  {name := "b", offset := -2, upto := true},
                  {name := "y", offset := 5, upto := true}]
}
example : layout.checkErrors = [] := by decide
example : layout.semanticCoverage = .full := by decide
example : ProcVerilog.emitProcVerilog layout = none := by decide

example : layout.interfaceCore.outputs = layout.outputs := rfl
example : (compileModule layout).portLayouts.map (fun p => (p.name, p.signed, p.offset, p.upto))
    = [("a", true, 1, false), ("b", false, -2, true), ("y", false, 5, true)] := by decide
