---
id: stutter-refines-protocol
layer: pattern
applies_to: non-lockstep handshake / ready-valid protocols
principle: commuting-square-and-generic-induction
tactics: [specenv-repack]
lib: LeanRTL/Core/Refine.lean (StutterRefines / committedTrace / StutterRefines.trace)
example: axi_register (LeanRTL/Designs/Examples/AxiRegister.lean)
maturity: promoted
---
# Stutter-refines protocol

When the hardware advances the spec state only on some cycles (a handshake commits when `ready & valid`), a lockstep `SimRefines` is too strong. `StutterRefines` adds a `commit : Env → Env → Bool` trigger: the abstract state steps on commit cycles and stutters (holds) otherwise, and `StutterRefines.trace` relates the run to `committedTrace`. Grounded in `Refine.lean` (`encnt_stutter_refines`, an enable-gated counter) and `Protocol/AxiRegister.lean`. Gotcha: define `commit` from the *observable* handshake signals (the mux/eq on ready-valid), and repack the abstract state env to match the step env at commit cycles (see specenv-repack), or `step_α` will not close on the stutter branch.

## Worked example

```lean
theorem write_channel_refines (inputs : Nat → Env) (hleg : ∀ t, impl.LegalInputs (inputs t))
    (t : Nat) :
    α (regTrace impl inputs (fun _ => false) t)
      = committedTrace impl specStepW s0 commitW inputs t :=
  (write_stutter_refines.trace inputs hleg t).2
```
> Source: LeanRTL/Designs/Examples/AxiRegister.lean:325
