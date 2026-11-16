---
id: nat-mod-eq-of-lt
layer: tactic
applies_to: arithmetic leaves where all quantities are in range
principle: leaf-is-decision-not-induction
lib: "—"
maturity: promoted
---
# `Nat.mod_eq_of_lt` to drop the `%`

When every quantity is provably `< 2^w`, the modulus that BitVec arithmetic introduces is a no-op: `Nat.mod_eq_of_lt` rewrites `x % 2^w` to `x`, after which the goal is pure linear arithmetic for `omega`. This is the workhorse of the factorial and multiplier developments (`L5Mul16.lean`: bound each operand `< 2^16`, the product `< 2^32`, then the mod vanishes). Gotcha: you must supply the `< 2^w` bound first (via `Nat.mod_le`, `isLt`, or a `mul16_lt`-style helper) — `omega` alone will not see the modulus.
