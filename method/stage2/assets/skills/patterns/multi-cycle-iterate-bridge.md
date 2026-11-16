---
id: multi-cycle-iterate-bridge
layer: pattern
applies_to: multi-cycle datapaths bridged to real simulation
principle: commuting-square-and-generic-induction
tactics: [apply-infer-envs]
lib: LeanRTL/Lib/MultiCycle.lean (iterate / stepClosed / iterate_stepClosed_eq_regTrace)
example: GcdIter / Div (LeanRTL/Designs/Examples/GcdIter.lean, WholeDesign/L5Div.lean)
maturity: promoted
---
# Multi-cycle iterate bridge

The abstract `iterate f k s` reasoning (used for termination and loop invariants) is only meaningful if it equals what the real hardware does. `iterate_stepClosed_eq_regTrace` bridges `MultiCycle.iterate` (via `stepClosed m inp rst`, the register-only transition with fixed input/reset) to `Module.regTrace` — so the ∃K / measure arguments (well-founded-termination) transfer to the actual `Module.simulate`. Grounded in `MultiCycle.lean` + `GcdIter.lean` + `L5Div.lean`. Gotcha: `stepClosed` freezes the input/reset for the iteration window — this matches a multi-cycle op that holds its operands, not a design whose inputs change every cycle; check the operand-hold assumption before bridging.

## Worked example

```lean
theorem iterate_stepClosed_eq_regTrace (m : Module) (inp : Env) (rst : Bool) :
    ∀ K, iterate (stepClosed m inp rst) K m.initRegs
       = CompilerCorrectSeq.regTrace m (fun _ => inp) (fun _ => rst) K := by …
```
> Source: LeanRTL/Lib/MultiCycle.lean:130
