---
id: apply-infer-envs
layer: tactic
applies_to: invoking the Lift/Refine combinators
principle: commuting-square-and-generic-induction
lib: LeanRTL/Lib/Lift.lean (cycleEnv); LeanRTL/Lib/EvalLookup.lean (specEnv)
maturity: sediment
---
# `apply … _ _` to infer the envs

When applying `simRefines_single`/`refines_single_*`, write `apply <lemma> _ _` and let elaboration infer the `cycleEnv`/`specEnv` arguments from the goal, rather than supplying them explicitly. Passing the envs by hand forces a `whnf` on the full environment expression and times the elaborator out. Let unification place them. Same discipline for any combinator whose environment argument is large: leave it as a metavariable the goal pins down.
