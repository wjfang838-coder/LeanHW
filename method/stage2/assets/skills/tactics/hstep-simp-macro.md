---
id: hstep-simp-macro
layer: tactic
applies_to: the single-step obligation of every lift
principle: commuting-square-and-generic-induction
lib: LeanRTL/Lib/Lift.lean (macro hstep_simp)
maturity: promoted
---
# `hstep_simp` bundled simp set

`hstep_simp [<extra lemmas>]` is the macro (defined in `Lift.lean`) that bundles the standard simp set for the `step_α` obligation: the `cycleEnv_reg`/`cycleEnv_input` bridge lemmas, `ofNat_toNat_ofNat`, `eval`, `Env.lookup`, and the BitVec normalizers — you append only the design's `env` def and its `<reg>_correct` lemmas. It replaces a fragile hand-assembled `simp only` list that every lift used to re-write. Gotcha: pass the design-specific lemmas in the brackets; do not fall back to full `simp`, which defeats the careful ordering (simp-only-not-full-simp).
