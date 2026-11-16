---
id: l3-to-l4-observation
layer: pattern
applies_to: designs needing observed output ports + reset streams
principle: commuting-square-and-generic-induction
tactics: [trailing-rfl-decidable, apply-infer-envs]
lib: LeanRTL/Lib/Lift.lean (refines_single_moore / refines_single_out / refines_single_out_rec)
example: L4BatchB (LeanRTL/Designs/VEval/Prob048M2014Q4c.lean:78)
maturity: promoted
---
# L3 → L4 output observation

Upgrades a whole-trace register theorem (L3) to an **observed** theorem (L4): what the output ports read at each cycle, over legal resetful input streams. Uses the `Refines` structure (adds reset streams, `Module.LegalInputs`, and an output-observation obligation) via `refines_single_moore` (registered Moore output) or `refines_single_out` (combinational output cone). The extra obligation is a single-cycle output-equation check. Gotcha: a combinational output cone (comparison/mux, not a bare `.var` read) elaborates through an invisible `Decidable`/`OfNat` instance — append a trailing `rfl` after the `simp only` (see trailing-rfl-decidable).

## Worked example

```lean
theorem dff_refines_full : Refines impl α specN specObs 0 (fun _ => True) :=
  refines_single_moore impl "q" "q" 1 qNext 0 specN 0 ⟨rfl, rfl⟩ rfl hstep rfl
```
> Source: LeanRTL/Designs/VEval/Prob048M2014Q4c.lean:78
