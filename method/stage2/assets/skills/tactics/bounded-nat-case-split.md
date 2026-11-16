---
id: bounded-nat-case-split
layer: tactic
applies_to: small bounded Nat case analysis (core-Lean only)
principle: leaf-is-decision-not-induction
lib: "—"
maturity: sediment
---
# Bounded Nat case-split without Mathlib

This repo is core-Lean (no Mathlib), so `interval_cases` is unavailable. To split a bounded index `k ≤ K` into cases, use `rcases (by omega : k = 0 ∨ k = 1 ∨ … ∨ k = K) with …`, discharging the disjunction with `omega`. It is verbose but dependency-free and fast. Use it for per-bit peels, small counter states, and addressed-word transports. Gotcha: keep the bound tight — an over-wide disjunction makes `omega` enumerate needlessly; derive `k ≤ K` first.
