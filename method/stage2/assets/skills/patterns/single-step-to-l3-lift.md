---
id: single-step-to-l3-lift
layer: pattern
applies_to: any sequential design with proven per-register next-state lemmas
principle: commuting-square-and-generic-induction
tactics: [hstep-simp-macro, apply-infer-envs, ofnat-tonat-ofnat-simp]
lib: LeanRTL/Lib/Lift.lean (simRefines_single / _rec / simRefines_pair / simRefines_triple / simRefines_triv)
example: up_down_counter (LeanRTL/Designs/Rtllm/UpDownCounter.lean:86)
maturity: promoted
---
# Single-step → L3 whole-trace lift

Turns isolated `<reg>_correct : eval regNext env = specReg …` lemmas into a whole-run theorem: at every cycle `t` the registers equal the `t`-fold transition from reset. Bundle the per-register single-step lemmas into a `SimRefines` (via `simRefines_single`/`_pair`/`_triple`, or `simRefines_triv` for a hand-built `α`), discharge the four obligations, then read off `.trace`. The move is mechanical because `SimRefines.trace` carries the `∀t` induction. Gotcha: `Module.step` evaluates next-state under `cycleEnv`, but your lemmas are over the design's `env` helper — bridge with `show cycleEnv … = … from rfl` inside `hstep_simp`. See `.claude/skills/leanrtl-full-temporal/SKILL.md` for the full recipe.

## Worked example

```lean
theorem updown_refines :
    SimRefines impl α specN 0 (fun _ => True) :=
  simRefines_single impl "count" 16 countNext 0 specN 0 ⟨rfl, rfl⟩ hstep rfl

theorem updown_trace (inputs : Nat → Env) (t : Nat) :
    α (regTrace impl inputs (fun _ => false) t) = specTrace specN 0 inputs t :=
  regTrace_through_α updown_refines inputs t
```
> Source: LeanRTL/Designs/Rtllm/UpDownCounter.lean:86
