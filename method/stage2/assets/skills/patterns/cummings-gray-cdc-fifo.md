---
id: cummings-gray-cdc-fifo
layer: pattern
applies_to: asynchronous (dual-clock) FIFOs
principle: leaf-is-decision-not-induction
tactics: [bv-decide-for-fixed-width]
lib: LeanRTL/Core/Syntax.lean (Reg.clockNet)
example: async_fifo (LeanRTL/Designs/CvdpAgentic/AsyncFifo.lean)
maturity: sediment
strike: 1
---
# Cummings Gray-pointer CDC FIFO

Model an async FIFO with the standard Cummings construction: binary pointers increment on `en & ~flag`, Gray-coded (`bin2gray`) for the crossing, and the read port lives in its own clock domain via `Reg.clockNet`. Prove the exact empty/full flag laws — full is the *next* Gray write pointer versus the synchronized read pointer with the **top two bits inverted** (`^ 2^16+2^15`), empty is the *next* Gray read pointer equalling the synchronized write pointer (initializes to 1). The instance graph is cyclic, so `Parent` cannot wire it — use the flat-core split (see parent-flatten). Gotcha: the two-bit-inverted full test and the empty-init-to-1 are easy to get subtly wrong; state them exactly, `bv_decide` per flag.

## Worked example

```lean
theorem full_flag_exact (w r : BitVec 17) :
    b2gS w = (b2gS r ^^^ flipMask) ↔ w = r + 65536 := by
  constructor <;> (intro h; revert h; simp only [b2gS, flipMask]; bv_decide)
```
> Source: LeanRTL/Designs/CvdpAgentic/AsyncFifo.lean:193
