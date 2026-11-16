---
id: bitvec-ofnat-zero-not-rfl
layer: tactic
applies_to: wide register inits (reset to 0 at large widths)
principle: leaf-is-decision-not-induction
lib: "—"
maturity: sediment
---
# Wide zero init: `BitVec.ofNat_zero`, not `rfl`

For a wide register initialized to zero (e.g. 512-bit), do NOT close `initRegs`/`init_α` with `rfl` — that forces Lean to compute `2^512` and stalls. Use `BitVec.ofNat_zero` / a targeted `simp` that rewrites the zero symbolically. The same caution applies to any leaf where `rfl` would trigger a large `2^w` evaluation: rewrite by lemma, never by definitional unfolding, once `w` is big.
