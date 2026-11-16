import LeanRTL.Core.Compiler
import LeanRTL.Core.Check
import LeanRTL.Core.MemSemantics
open LeanRTL

def boundedMem : MemBlock := {
  name := "small"
  addrWidth := 3
  dataWidth := 8
  size := 2
  init := some [0x12, 0xA5]
  reads := [{addr := .var "a" 3, out := "rd"}]
}
def boundedModule : Module := {
  name := "bounds"
  inputs := [{name := "a", width := 3}]
  outputs := [{name := "q", width := 8, expr := .var "rd" 8}]
  mems := [boundedMem]
}
example : boundedModule.checkErrors = [] := by decide +kernel
example : ({boundedModule with mems := [{boundedMem with size := 0}]}).checkErrors != [] := by decide +kernel
example : ({boundedModule with mems := [{boundedMem with size := 9}]}).checkErrors != [] := by decide +kernel
example : ({boundedModule with mems := [{boundedMem with init := some [0,0,0,0,0,0,0,0]}]}).checkErrors != [] := by decide +kernel
example : ((compileModule boundedModule).cells.find? (fun c => c.type == "$mem_v2")).map
  (fun c => (c.parameters.lookup "SIZE", c.parameters.lookup "ABITS", c.parameters.lookup "INIT")) =
  some (some "00000000000000000000000000000010", some "00000000000000000000000000000011", some "1010010100010010") := by decide +kernel
example (mem : Spec.Mem 3 8) (e : Env) :
  MemBlock.readBounded boundedMem mem (.const 2) e = none := by
  apply MemBlock.read_bounded_invalid
  change ¬ (2 : Nat) < 2
  decide
example (mem : Spec.Mem 3 8) (e : Env) :
  MemBlock.writeBounded boundedMem {clock := .const 1, en := .const 1, addr := .const 2, data := .const 0xFF} mem e = mem := by
  apply MemBlock.write_bounded_invalid
  change ¬ (2 : Nat) < 2
  decide
example (mem : Spec.Mem 3 8) (e : Env) :
  MemBlock.readBounded boundedMem
    (MemBlock.writeBounded boundedMem {clock := .const 1, en := .const 1, addr := .const 1, data := .const 0xAB} mem e)
    (.const 1) e = some 0xAB := by
  apply MemBlock.read_bounded_after_write
  · rfl
  · change (1 : Nat) < 2
    decide
example (mem : Spec.Mem 3 8) :
  (MemBlock.initialContents boundedMem mem).read 2 = mem.read 2 := by rfl
