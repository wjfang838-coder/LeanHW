---
id: genuine-parametric-emission
layer: pattern
applies_to: designs where dev-TB config conflicts with spec default
principle: spec-is-the-oracle
tactics: []
lib: LeanRTL/Core/ParamBackend.lean; LeanRTL/Designs/Param/Registry.lean
example: signed_comparator (LeanRTL/Designs/Param/SignedComparator.lean)
maturity: promoted
strike: 2
---
# Genuine parametric emission

When the dev testbench instantiates one config but the spec's DEFAULT parameters imply another (and the hidden scorer uses env-default `-P` bindings — see dev-tb-not-oracle), do not hard-code either: emit a genuinely parametric `ParamModule` and let the scorer pick N. `SignedComparator.lean` is the `.comparator` template family (value-parameterised comparison window + structural output-stage toggle), registered in `Registry.lean` with one axis key per parameter. Anchor per-N with a miter (per-n-miter-anchor). Gotcha: the axis-key registration boilerplate is hand-repeated (strike 2 after queue's 4 keys) — a `mkAxisKeys` helper is the promotion candidate; register the cfg defaults = the gen's fixed axes so the default config still routes through the verified compiler.

## Worked example

```lean
def impl (N regOut enTol tol shl : Nat) : Module := …   -- SignedComparator.lean:122

-- Registry.lean: one axis key per parameter; the default config routes through the compiler
{ key := "signed_comparator", paramName := "DATA_WIDTH", defaultN := 16,
  gen := fun w => SignedComparator.impl w 0 0 0 0,
  cls := .comparator { dwParam := "DATA_WIDTH", regParam := "REGISTER_OUTPUT",
                       etParam := "ENABLE_TOLERANCE", tolParam := "TOLERANCE",
                       shParam := "SHIFT_LEFT", dwDefault := 16, regDefault := 0,
                       etDefault := 0, tolDefault := 0, shDefault := 0 } }
```
> Source: LeanRTL/Designs/Param/Registry.lean:223
