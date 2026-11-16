---
id: rule30-iterate-compose
layer: pattern
applies_to: cellular-automata / free-running state generators
principle: commuting-square-and-generic-induction
tactics: [bv-decide-for-fixed-width]
lib: LeanRTL/Lib/MultiCycle.lean (iterate)
example: pseudoRandGenerator_ca (LeanRTL/Designs/CvdpAgentic/PseudoRandGeneratorCa.lean, nextState_correct)
maturity: sediment
strike: 1
---
# Rule-30 iterate compose

For a free-running generator (cellular automaton, LFSR), the whole-trace headline is `state(t) = iterate rule t seed`: compose the per-step law under the generic time induction (`iterate` in MultiCycle). In `PseudoRandGeneratorCa.lean` the per-cell CA rule is proven whole-word: `nextState_correct` shows the emitted next-state ≡ Rule 110 (if `rule_sel = 01`) else Rule 30, and `reg_correct` handles reset. Gotcha: this design currently proves only the **per-step** law + reset — the `iterate`-composed whole-trace corollary is not yet materialized for it; the composition combinator lives in `MultiCycle.lean`. Prove the step law first (bv_decide over all 3-cell neighbourhoods), compose second.

## Worked example

```lean
theorem nextState_correct (s : BitVec 16) (rsel : BitVec 2) :
    eval nextState (envS s rsel) = specNext16 s rsel := by
  have ec : (envS s rsel) "CA_out" = s.toNat := by simp [envS]
  have er : (envS s rsel) "rule_sel" = rsel.toNat := by simp [envS]
  simp only [nextState, nb, eval, Env.lookup, ec, er, specNext16, Lword, Rword,
    BitVec.ofNat_toNat, BitVec.setWidth_eq]
  bv_decide
```
> Source: LeanRTL/Designs/CvdpAgentic/PseudoRandGeneratorCa.lean:70

Note: this is the **per-step** law only. The `iterate`-composed whole-trace corollary
(`state(t) = iterate rule t seed`, combinator in `LeanRTL/Lib/MultiCycle.lean`) is not yet
materialized for this design — prove the step law first, compose second.
