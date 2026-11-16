import LeanRTL.Core.Compiler
import LeanRTL.Core.Check
import LeanRTL.Core.MemSemantics
open LeanRTL

def image : MemBlock := {
  name := "mem"
  addrWidth := 1
  dataWidth := 8
  init := some [0x12, 0xA5]
  reads := [{ addr := .var "a" 1, out := "rd" }]
}
def initialized : Module := {
  name := "init_test"
  inputs := [{name := "a", width := 1}]
  outputs := [{name := "q", width := 8, expr := .var "rd" 8}]
  mems := [image]
}
def unknownInit : Module := { initialized with mems := [{image with init := none}] }
example : initialized.checkErrors = [] := by decide +kernel
example : ({initialized with mems := [{image with init := some [0]}]}).checkErrors != [] := by decide +kernel
example : ((compileModule initialized).cells.find? (fun c => c.type == "$mem_v2")).map
  (fun c => c.parameters.lookup "INIT") = some (some "1010010100010010") := by decide +kernel
example : ((compileModule unknownInit).cells.find? (fun c => c.type == "$mem_v2")).map
  (fun c => c.parameters.lookup "INIT") = some (some "xxxxxxxxxxxxxxxx") := by decide +kernel
example (arbitrary : Spec.Mem 1 8) :
  (MemBlock.initialContents image arbitrary).read 0 = 0x12 := by rfl
