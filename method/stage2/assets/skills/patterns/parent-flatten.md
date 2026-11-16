---
id: parent-flatten
layer: pattern
applies_to: hierarchical / multi-module sequential designs
principle: commuting-square-and-generic-induction
tactics: [apply-infer-envs]
lib: LeanRTL/Core/HierSeqCorrect.lean (flattenParentSeq / HierSeqCorrect); LeanRTL/Lib/EvalLookup.lean
example: sync_serial (LeanRTL/Designs/CvdpAgentic/SyncSerialTxRx.lean)
maturity: promoted
strike: 3
---
# Parent flatten to a plain Module

A `Parent` (composable, sequential child modules) has no whole-trace object of its own until you flatten it. `compileParent` / `flattenParentSeq` turns the hierarchy into a single plain `Module`, over which `Parent.regTrace` and the standard L3 lift apply. This was the strike-3 Parent-gap promotion (recorded across `stragglers_lift`, `AgenticTraceD`, `StragglersTrace`). Gotcha: `compileParentM`'s single pass resolves a forward `.var "<inst>.<port>"` to a dangling net, so a TRUE instance-level cycle (child both feeds and is fed by a sibling — async_fifo, ethernet_mii core↔fifo) does NOT flatten; those still need the flat-core + structural-wrapper split until `compileParentM` goes two-pass.

## Worked example

```lean
def Parent.regTrace (p : Parent) (inputs : Nat → Env) (reset : Nat → Bool) : Nat → Env :=
  CompilerCorrectSeq.regTrace (flattenParentSeq p) inputs reset
```
> Source: LeanRTL/Core/HierRefine.lean:52
