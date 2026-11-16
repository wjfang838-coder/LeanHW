---
id: f9-wire-free-emission
layer: pattern
applies_to: agentic sequential controllers (self-emitted)
principle: proof-carrying-reaches-artifact
tactics: []
lib: docs/instructions/CORE.md §2.8; scripts/f9_emit.py
example: cache_controller / dma_xfer_engine (LeanRTL/Designs/CvdpAgentic/CacheController.lean)
maturity: promoted
strike: 3
---
# F9 emission must be wire-free

`leanrtl vverilog` (F9) recomputes each register's next-state cone with blocking temporaries inside the clocked block and lowers decision muxes to if/else — but a named `Wire` still emits as a module-level continuous assign. Any register next-state that references a wire then (a) misses same-tick input writes by one delta, and (b) can absorb a `z`/`x` from a dangling input through a continuous ternary straight into the state register (cache_controller hit both). Rule (strike-3, CORE §2.8): **agentic sequential designs use `wires := []`** — inline all selection into register/output Exprs, and put any mux whose SELECT may be z in decision position (if/else), never in a continuous ternary. Small storage (≤32) → a named register bank, not a MemBlock (`$mem` disables F9 and powers up X).

## Worked example

```lean
/-! ## Inlined condition/data expressions (NO wires — see the header note) -/
…
def impl : Module :=
  { name    := "cache_controller"
    inputs  := [ … ]
    outputs := [ {name := "read_data", width := 32, expr := rdOutE}, … ]
    regs    := cacheRegs ++ [ … ]
    clock   := some "clk" }   -- no `wires :=` field: every mux inlined into Exprs
```
> Source: LeanRTL/Designs/CvdpAgentic/CacheController.lean:163 (NO-wires note at :72)
