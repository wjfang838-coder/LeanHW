---
id: asyncload-value-trace
layer: pattern
applies_to: $aldff asynchronous dynamic-load registers
principle: commuting-square-and-generic-induction
tactics: [bv-decide-for-fixed-width]
lib: LeanRTL/Core/Semantics.lean (Reg.aldffDen); LeanRTL/Designs/Cvdp/CvdpLfsr8bit0001.lean:58 (stepAld / regTraceAld)
example: AsyncLoad (LeanRTL/Designs/Cvdp/CvdpLfsr8bit0001.lean:58)
maturity: promoted
---
# Async-load value trace

An `$aldff` register (`Reg.asyncLoad := some (net, activeHi, val)`) is asynchronously forced to `eval val` while `net` is active, else clocks `next`. Such a design is excluded from the whole-design M6 theorem (`moduleChecksb = false`), so prove a **value-level** whole-trace theorem instead: a new advance `stepAld` guards each register's next-state with `Reg.aldffDen` (`q' = active ? val : next`), and `regTraceAld` composes the per-register value law to the whole trace (CORE §1.3 Stage 2). `stepAld` is a conservative extension of `Module.step` — for `asyncLoad = none` registers `aldffDen` reduces to `eval r.next`. Gotcha: never combine `asyncLoad` with `asyncReset` on one register (the compiler drops the load — CORE §1.3).

## Worked example

```lean
def stepAld (m : Module) (regVals inputs : Env) (resetActive : Bool) : Env :=
  let e := aldCycleEnv m regVals inputs
  fun n =>
    match m.regs.find? (·.name = n) with
    | some r => if resetActive then r.init.toNat else (r.aldffDen e).toNat
    | none   => regVals n

def regTraceAld (m : Module) (inputs : Nat → Env) (reset : Nat → Bool) : Nat → Env
  | 0     => m.initRegs
  | t + 1 => stepAld m (regTraceAld m inputs reset t) (inputs t) (reset t)
```
> Source: LeanRTL/Designs/Cvdp/CvdpLfsr8bit0001.lean:58
