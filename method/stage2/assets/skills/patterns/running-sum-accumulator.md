---
id: running-sum-accumulator
layer: pattern
applies_to: accumulators / gated running sums (L5)
principle: commuting-square-and-generic-induction
tactics: [nat-mod-eq-of-lt, omega-for-bounds]
lib: LeanRTL/Lib/Semantic/Accum.lean (accumulator_reads)
example: pe (LeanRTL/Designs/Rtllm/PE.lean:137)
maturity: promoted
---
# Running-sum accumulator

The L5 statement `acc(t) = acc₀ + Σ (gated inputs up to t)`. After the L3 lift gives `acc` as a `t`-fold `specStep`, the cycle-index induction that recognises the fold as a running sum is now a **reusable combinator** — `accumulator_reads` (and its gated twin `accumulator_reads_gated`) in `LeanRTL/Lib/Semantic/Accum.lean`. A design supplies only its per-cycle **accumulate fact** `specStep s (inputs k) = s + f(input k)` (usually `next_correct` specialised to the non-reset cone) and picks the element function `f` / width `w` / gate `g`; the induction (unfolding `specTrace_succ` once per cycle, re-bracketing with `BitVec.add_assoc`) lives in the library. The sum is in `BitVec w`, i.e. exact **mod `2^w`** — it wraps exactly like the register add; compose with an in-range bound (`omega`/`nat-mod-eq-of-lt`) for an exact `Nat` sum. Does **not** fit: saturating accumulators (`SetBitStreamCalculator`, clamps at 255 — different arithmetic) and grouped/periodic-reset accumulators (`accu`, `(cnt, acc, …)` tuple that clears `acc` every group). Gotcha: keep the enable inside the spec fold (`accumulator_reads_gated`'s `if g then f else 0`), not as a side condition, or the induction step will not close.

## Worked example

```lean
theorem closed (inputs : Nat → Env)
    (hrst : ∀ k, BitVec.ofNat 1 (inputs k "rst") = 0) (t : Nat) :
    specTrace specN 0 inputs t = macSum inputs t := by
  have hstep : ∀ (s : BitVec 32) (k : Nat), specN s (inputs k) = s + mac (inputs k) := by
    intro s k
    show spec s (BitVec.ofNat 32 (inputs k "a")) (BitVec.ofNat 32 (inputs k "b"))
        (BitVec.ofNat 1 (inputs k "rst")) = s + mac (inputs k)
    rw [hrst k]
    simp only [spec, mac, if_neg (by decide : ¬((0 : BitVec 1) = 1))]
  simp only [macSum]
  rw [accumulator_reads specN 0 inputs mac hstep t]
  exact BitVec.zero_add _
```
> Source: LeanRTL/Designs/Rtllm/PE.lean:137 (`pe` MAC; combinator `accumulator_reads` at LeanRTL/Lib/Semantic/Accum.lean:88, gated variant at :72)
