---
id: partial-product-invariant
layer: pattern
applies_to: iterative shift-add multipliers / accumulators
principle: leaf-is-decision-not-induction
tactics: [restate-to-avoid-sat-blowup, nat-mod-eq-of-lt, omega-for-bounds]
lib: LeanRTL/Core/Refine.lean (SimRefines) — arithmetic is design-local
example: multi_16bit (LeanRTL/Designs/Rtllm/Multi16bit.lean:290)
maturity: promoted
---
# Partial-product invariant

An iterative multiplier's miter is SAT-hard, so do NOT let `bv_decide` chew the whole product. Instead carry an invariant that restates the partial result: `yout = (a mod 2^k) · b`, and peel one bit per cycle. The peel is exactly core Lean's `Nat.mod_mul` at `2^(k+1) = 2^k · 2` (see `mod_pow_succ_testBit`/`mod_pow_succ_mul` in `L5Mul16.lean`), with the quotient bit named by `testBit`. Never materialize the full `Σ`. Gotcha: keep every quantity `< 2^32` (via `mul16_lt` + `Nat.mod_eq_of_lt`) so the register widths never wrap mid-invariant; then each step is `omega`, not SAT.

## Worked example

```lean
theorem mod_pow_succ_testBit (a k : Nat) :
    a % 2 ^ (k + 1) = a % 2 ^ k + (if a.testBit k then 2 ^ k else 0) := by
  have hmm : a % (2 ^ k * 2) = a % 2 ^ k + 2 ^ k * (a / 2 ^ k % 2) := Nat.mod_mul
  …
```
> Source: LeanRTL/Designs/Rtllm/Multi16bit.lean:290
