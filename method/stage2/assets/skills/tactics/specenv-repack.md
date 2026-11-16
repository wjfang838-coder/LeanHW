---
id: specenv-repack
layer: tactic
applies_to: record/tuple-state refinements (queues, stutter protocols)
principle: commuting-square-and-generic-induction
lib: LeanRTL/Lib/EvalLookup.lean (specEnv)
maturity: sediment
strike: 2
---
# Repack the spec env to match the step env

When the abstract state is a record/tuple (a queue, a protocol state), `step_α` leaves the spec-side environment packed differently from the `cycleEnv` step side. Repack it with the record's projections in the `simp only` set (double-unfold), rather than reaching for a `funext` env-bridge. The `funext` bridge is only sound when the register env is `.toNat`-normalized (a real trace value), which the `regTrace` payoff guarantees but the raw universally-quantified `r` in the step obligation does NOT (strike 2, record-env-bridge family; the `l3_4` precedent). Rule: for St/record-env designs, project-and-unfold; do not `funext` unless `r` is pinned to a reduced value.
