import LeanRTL.Core.Check
open LeanRTL
namespace CheckerAcceptance

def base : Module := {
 name := "lint_probe"
 inputs := [{name := "a", width := 1}, {name := "b", width := 8}]
 wires := [{name := "w", width := 8, expr := .var "b" 8}]
 outputs := [{name := "y", width := 8, expr := .var "w" 8}]
}
def cases : List Module := [
 base,
 {base with inputs := base.inputs ++ [{name := "a", width := 1}]},
 {base with wires := [{name := "b", width := 8, expr := .var "b" 8}]},
 {base with outputs := [{name := "y", width := 8, expr := .var "missing" 8}]},
 {base with outputs := [{name := "y", width := 1, expr := .var "w" 1}]},
 {base with wires := [{name := "v", width := 8, expr := .var "w" 8}] ++ base.wires},
 {base with clock := some "b"},
 {base with reset := some "w"},
 {base with clock := some "a"},
 {base with portOrder := ["a", "b", "a"]},
 {base with portLayouts := [{name := "missing"}]},
 {base with regs := [{name := "r", width := 8, init := 0, next := .var "w" 8, asyncReset := some ("b", true, 0)}]},
 {base with regs := [{name := "r", width := 8, init := 0, next := .var "w" 8, asyncReset := some ("a", true, 0), asyncLoad := some ("a", true, .var "w" 8)}]},
 {base with latches := [{name := "l", width := 8, enable := .var "a" 1, d := .var "w" 8}]},
 {base with latches := [{name := "l", width := 8, enable := .var "bad" 1, d := .var "w" 8}]},
 {base with regs := [{name := "r", width := 8, init := 0, next := .var "w" 8, clockNet := some (.var "missing" 1)}]},
 {base with regs := [{name := "r", width := 8, init := 0, next := .var "w" 8, asyncLoad := some ("missing", true, .var "w" 8)}]},
 {base with regs := [{name := "r", width := 8, init := 0, next := .var "w" 8, asyncLoad := some ("a", true, .var "w" 8)}]},
 {base with mems := [{name := "mem", addrWidth := 2, dataWidth := 8, reads := [{addr := .var "b" 2, out := "rd"}]}]},
 {base with mems := [{name := "mem", addrWidth := 8, dataWidth := 8, reads := [{addr := .var "b" 8, out := "rd"}]}], wires := [{name := "w", width := 8, expr := .var "rd" 8}]},
 {base with mems := [{name := "mem", addrWidth := 8, dataWidth := 8, reads := [{addr := .var "b" 8, out := "w"}]}]},
 {base with portLayouts := [{name := "a"}, {name := "a"}]}
]
example : cases.map (fun m => m.checkErrors.isEmpty) =
 [true, false, false, false, false, false, false, false, true, false, false, false, false, true, false,
  false, false, true, false, true, false, false] := by decide +kernel

end CheckerAcceptance
