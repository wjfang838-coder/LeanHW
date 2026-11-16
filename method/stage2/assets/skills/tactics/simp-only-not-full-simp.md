---
id: simp-only-not-full-simp
layer: tactic
applies_to: any leaf goal carrying named lemmas
principle: leaf-is-decision-not-induction
lib: "—"
maturity: promoted
---
# `simp only`, not full `simp`

Use `simp only [<explicit set>]`, never bare `simp`, in the step/observation leaf. Full `simp` normalizes literals — it will rewrite `% 64` to a concrete modulus and destroy the syntactic form your bespoke lemma (`ofNat_mod64`, a `<reg>_correct`) matches against, so the follow-up rewrite silently fails. Keep the simp set explicit and minimal; add lemmas one at a time until the goal closes. This is the recurring cause of "my lemma is right but the rewrite does nothing".
