---
id: well-founded-termination
layer: pattern
applies_to: multi-cycle iterative controllers that must halt
principle: commuting-square-and-generic-induction
tactics: [omega-for-bounds, bounded-nat-case-split]
lib: LeanRTL/Lib/MultiCycle.lean (loop_latch / loop_correct)
example: GcdIter (LeanRTL/Designs/Examples/GcdIter.lean)
maturity: promoted
---
# Well-founded termination (∃K)

For a multi-cycle loop, prove it reaches `done` in finitely many cycles by exhibiting a strictly-decreasing measure `μ`. `MultiCycle.loop_latch` combines a preserved invariant with termination to give an end-to-end "after K cycles the output = the math function" theorem; the ∃K driver is a design-local well-founded recursion on the measure. Worked in `GcdIter.lean`: `run_preserves` (invariant `Nat.gcd` stable) + `run_reaches` (measure `x+y` strictly decreases) → `run_end_to_end`. Gotcha: the measure must decrease on the *stepped* state under the loop condition — state and prove `μ (run s) < μ s` given "not done", not just that `μ` is bounded.

## Worked example

```lean
theorem run_reaches : ∀ (n : Nat) (x y : BitVec 8) (res : BitVec 8) (dn : BitVec 1),
    x.toNat + y.toNat ≤ n → ∃ K, (iterate run K ⟨1, x, y, res, dn⟩).st = 2 := by …

theorem run_end_to_end (A B : BitVec 8) :
    ∃ K, (iterate run K ⟨1, A, B, 0, 0⟩).res.toNat = Nat.gcd A.toNat B.toNat ∧
         (iterate run K ⟨1, A, B, 0, 0⟩).dn = 1 ∧
         (iterate run K ⟨1, A, B, 0, 0⟩).st = 2 := by …
```
> Source: LeanRTL/Designs/Examples/GcdIter.lean:293 (run_end_to_end at :347)
