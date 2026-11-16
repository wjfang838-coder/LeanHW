---
id: width-cast-sextto
layer: pattern
applies_to: heterogeneous-width signed arithmetic
principle: leaf-is-decision-not-induction
tactics: [restate-to-avoid-sat-blowup]
lib: LeanRTL/Designs/Param/LowPassFilter.lean (sextTo / eval_sextTo) — design-local, not yet in Lib
example: low_pass_filter FIR (LeanRTL/Designs/Param/LowPassFilter.lean)
maturity: sediment
strike: 1
---
# Width cast via `sextTo`

When a datapath grows a signed operand to a wider accumulator (`w`-bit tap → `OW`-bit sum), the width mismatch is a compile error unless you cast. `sextTo t h e : Expr t` sign-extends and the proof obligation of the width cast is discharged ONCE by `eval_sextTo : eval (sextTo t h e) env = (eval e env).signExtend t`. Downstream arithmetic then works at the uniform wide width and the cast never re-appears in leaf goals. Gotcha: this lemma currently lives in the LowPassFilter design file, not `LeanRTL/Lib/` — promotion candidate if a second signed-widening design lands. Use `sextTo` (proven), not a raw `BitVec.signExtend` sprinkled through the Expr, which leaves unproven casts.

## Worked example

```lean
def sextTo (t : Nat) {w : Nat} (h : w ≤ t) (e : Expr w) : Expr t :=
  castW (w_add_sub h) (.sext (t - w) e)

theorem eval_sextTo {t w : Nat} (h : w ≤ t) (e : Expr w) (env : Env) :
    eval (sextTo t h e) env = (eval e env).signExtend t := by
  unfold sextTo
  rw [eval_castW]
  simp only [eval]
  exact signExtend_cast (w_add_sub h) (eval e env)
```
> Source: LeanRTL/Designs/Param/LowPassFilter.lean:54 (design-local; promotion candidate)
