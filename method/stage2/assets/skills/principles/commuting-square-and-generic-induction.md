---
id: commuting-square-and-generic-induction
layer: principle
applies_to: every sequential design that needs a whole-trace theorem
lib: LeanRTL/Core/Refine.lean (SimRefines.trace)
maturity: principle
---
# Commuting square + generic induction

Prove the cross-cycle induction over time ONCE, generically, and make each design supply only a single-step commuting square. `SimRefines.trace` (in `Refine.lean`) runs the `∀t` induction over `regTrace` for all designs; a design only discharges the four `SimRefines` obligations — chiefly `step_α : α (m.step r i) = specStep (α r) i`, the square that says "abstract, then step spec" equals "step hardware, then abstract". No design re-proves anything about `simulate`/`regTrace`. This is why lifting a per-cycle proof to a whole-run proof is near-mechanical: the reusable machinery already carries the temporal quantifier.
