---
id: trailing-rfl-decidable
layer: tactic
applies_to: output cones that are comparisons / muxes / eq-against-const
principle: leaf-is-decision-not-induction
lib: "—"
maturity: promoted
strike: 2
---
# Trailing `rfl` for the invisible Decidable

An output/next-state cone that is a comparison or `ite` against a named BitVec constant elaborates through an `OfNat`-literal / `Decidable` instance the `simp only` set does not touch, leaving the goal defeq-but-not-syntactically-closed. Append a bare `rfl` after the `simp only [eval, …]`. Seen in queue (`entry`/`empty`/`full_correct`), async_fifo, and every L4 `hobs` whose output is a combinational compare rather than a bare `.var` read (strike 2; a `.const`-normalizing HWLib lemma is the promotion candidate). Rule of thumb: any leaf after a `simp only` that "looks done" but isn't — try `rfl` before reaching for more lemmas.
