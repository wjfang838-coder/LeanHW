---
id: omega-for-bounds
layer: tactic
applies_to: linear arithmetic side goals
principle: leaf-is-decision-not-induction
lib: "—"
maturity: promoted
---
# `omega` for linear side goals

The default closer for linear Nat/Int side conditions: index-in-range, `k+1 < N`, carry boundaries, measure decrease. After `nat-mod-eq-of-lt` removes the moduli and the BitVec↔Nat conversions are done, most L5 arithmetic steps are one `omega`. Gotcha: `omega` is linear only — it cannot see multiplication of two variables or a live `%`/`/`. Feed it the non-linear facts as hypotheses (bounds, the peeled `testBit` value) and let it finish the linear combination.
