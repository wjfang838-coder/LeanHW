---
id: fold-induction-forall-n
layer: pattern
applies_to: parametric ∀N reducers (adders, filters)
principle: leaf-is-decision-not-induction
tactics: [omega-for-bounds, restate-to-avoid-sat-blowup]
lib: LeanRTL/Lib/Param helpers — proof is list-induction, no combinator
example: cascaded_adder / low_pass_filter (LeanRTL/Designs/Param/CascadedAdder.lean, LowPassFilter.lean)
maturity: promoted
---
# Fold induction for ∀N

For a genuinely parametric design (`impl : Nat → Module`), a fixed-width SAT proof does not scale. Instead prove that `eval` commutes with the structural reducer (`.add` / `.foldl` over a list of taps) by **induction on the list**, giving a single ∀N theorem with no per-N SAT. The base case is the empty/singleton reducer; the step folds one more tap. Grounded in `CascadedAdder.lean` and `LowPassFilter.lean` (the FIR sum). Anchor the ∀N theorem to real Verilog per-N with a Yosys miter (see per-n-miter-anchor). Gotcha: state the reducer with the SAME associativity/initial value the emitter uses, or the fold's base case will not match the netlist.

## Worked example

```lean
def sumExpr (W NS : Nat) : Expr (W + clog2 NS) :=
  (List.range NS).foldl (fun acc i => .add acc (elemExpr W NS i)) (.const 0)

theorem foldl_add_eval (W NS : Nat) (env : Env) :
    ∀ (l : List Nat) (a0 : Expr (W + clog2 NS)),
      eval (l.foldl (fun acc i => .add acc (elemExpr W NS i)) a0) env
        = l.foldl (fun acc i => acc + eval (elemExpr W NS i) env) (eval a0 env) := by
  intro l; induction l with
  | nil => intro a0; rfl
  | cons x xs ih => intro a0; simp only [List.foldl]; rw [ih]; rfl
```
> Source: LeanRTL/Designs/Param/CascadedAdder.lean:40 (foldl_add_eval at :72)
