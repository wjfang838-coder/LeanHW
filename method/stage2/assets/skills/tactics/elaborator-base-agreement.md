---
id: elaborator-base-agreement
layer: tactic
applies_to: base wire/lookup-agreement lemmas over many names
principle: leaf-is-decision-not-induction
lib: LeanRTL/Lib/EvalLookup.lean (eval_lookup_congr)
maturity: sediment
---
# Base agreement by `simp only [forall_mem_*]`, not `decide`

For the base `.lookup`-agreement lemma of computed-wire-congruence (a `∀ nw ∈ wires.flatMap …` goal), discharge it with `simp only [forall_mem_cons, forall_mem_nil]` over a precomputed list of `rfl` facts — NOT with `decide` or `fin_cases`. On a wide wire set the latter force the elaborator to whnf the entire membership predicate and it times out. Unfold the `∀ ∈` into an explicit conjunction of per-name equalities and let each be `rfl`. This keeps `deq_hcones`-style lemmas fast and reusable N times.
