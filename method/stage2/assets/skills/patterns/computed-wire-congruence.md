---
id: computed-wire-congruence
layer: pattern
applies_to: designs whose register next-state reads computed wires
principle: leaf-is-decision-not-induction
tactics: [elaborator-base-agreement, apply-infer-envs]
lib: LeanRTL/Lib/EvalLookup.lean (eval_lookup_congr / evalWires_specEnv_round / evalWires_eval_congr)
example: dynamic_equalizer / load_store_unit (LeanRTL/Designs/CvdpAgentic/DynamicEqualizer.lean:694, deq_hcones)
maturity: promoted
---
# Computed-wire congruence

When a register's next-state cone reads through named `Wire`s, the step obligation needs the wire environment under `cycleEnv` to agree with the spec environment. Prove the BASE `.lookup`-agreement between the two envs ONCE (a `deq_hcones`-style lemma over `me.wires.flatMap (·.expr.varsW)`), then `evalWires_specEnv_round` / `evalWires_eval_congr` reuse it for every wire and every register — no per-register re-derivation. Grounded in `HierLifts.lean` (`deq_hcones`, N reuses). Gotcha: state the base agreement with `simp only [forall_mem_*]` over a precomputed `rfl` list, not `decide`/`fin_cases`, which whnf-times-out on wide wire sets (see elaborator-base-agreement).

## Worked example

```lean
theorem sα_xr_0 (r i : Env) :
    BitVec.ofNat 16 ((me.step r i false) "eq_core_inst.xr_0")
      = eval (Expr.slice 0 16 (Expr.var "data_in_real" 16)) (evalWires me.wires (specEnv (α r) i)) := by
  show BitVec.ofNat 16 ((eval (Expr.slice 0 16 (Expr.var "data_in_real" 16)) (Eb r i)).toNat) = _
  apply evalWires_specEnv_round me.wires (Expr.slice 0 16 (Expr.var "data_in_real" 16)) _ _
  · exact deq_hcones r i
  · deq_htgt
```
> Source: LeanRTL/Designs/CvdpAgentic/DynamicEqualizer.lean:694
