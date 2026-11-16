---
id: restate-to-avoid-sat-blowup
layer: tactic
applies_to: multipliers / wide arithmetic where SAT explodes
principle: leaf-is-decision-not-induction
lib: "—"
maturity: promoted
---
# Restate to dodge SAT blow-up

`bv_decide` on a full 16×16 multiplier miter is exponential and will not return. When a leaf is SAT-hard, do not brute it — restate the goal as an inductive invariant whose per-step obligation IS decidable (partial-product-invariant: carry `yout = (a mod 2^k)·b`, peel one bit via `Nat.mod_mul`). The restatement moves the hardness into a small arithmetic step (`omega` / `nat-mod-eq-of-lt`) that closes in milliseconds. Rule: if `bv_decide` hangs, the fix is almost always a better statement, not a bigger timeout.
