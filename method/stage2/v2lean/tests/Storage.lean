import LeanRTL.Core.Compiler
import LeanRTL.Core.Semantics
import LeanRTL.Core.Check
import LeanRTL.Core.Coverage

open LeanRTL

def uninitialized : Module := {
  name := "storage"
  inputs := [{ name := "clk", width := 1 }, { name := "d", width := 4 }]
  outputs := [{ name := "q", width := 4, expr := .var "state" 4 }]
  regs := [{ name := "state", width := 4, next := .var "d" 4,
             init := 10, emitInit := false }]
  clock := some "clk"
  portOrder := ["clk", "q", "d"]
}

def initialized : Module :=
  { uninitialized with regs := uninitialized.regs.map (fun r => { r with emitInit := true }) }

example : uninitialized.checkErrors = [] := by decide
example : ((compileModule uninitialized).netnames.find? (fun n => n.name == "state")).map (·.attrs)
    = some [] := by decide
example : ((compileModule initialized).netnames.find? (fun n => n.name == "state")).map (·.attrs)
    = some [("init", "1010")] := by decide
example : uninitialized.semanticCoverage = .perRegister [.unconstrainedInit] := by decide
example : initialized.semanticCoverage = .full := by decide
example : (compileModule uninitialized).ports.map (·.name) = ["clk", "q", "d"] := by decide
example : ({ uninitialized with portOrder := ["clk", "clk", "d"] }).checkErrors != [] := by decide

-- Initial-state constraints do not alter the transition law from a given state.
example (state inputs : Env) (reset : Bool) :
    uninitialized.step state inputs reset = initialized.step state inputs reset := by
  funext name
  by_cases h : "state" = name <;> simp [Module.step, uninitialized, initialized, h]
