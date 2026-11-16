---
id: leaf-is-decision-not-induction
layer: principle
applies_to: all proofs — where to spend effort
lib: LeanRTL/Lib/Lift.lean (single_step / hstep_simp)
maturity: principle
---
# The leaf is a decision, not an induction

Induction is only for taming the time quantifier (see commuting-square-and-generic-induction). Once the single-step goal is exposed, it is a **finite, quantifier-free** claim about combinational next-state logic — close it with a decision procedure, never with more induction. Fixed-width BitVec equalities go to `bv_decide` (SAT + LRAT); structural rewrites to `simp only` + `rfl`; linear side goals to `omega`; small enumerations to `decide`. The `single_step`/`hstep_simp` plumbing in `Lift.lean` reduces the step obligation to exactly such a leaf. If a leaf resists decision, restate it (see restate-to-avoid-sat-blowup); do not induct.
