---
id: dual-edge-two-registers
layer: pattern
applies_to: designs mixing posedge and negedge flops
principle: commuting-square-and-generic-induction
tactics: [bv-decide-for-fixed-width]
lib: LeanRTL/Core/Compiler.lean (CLK_POLARITY); LeanRTL/Designs/VEval/Prob046Dff8p.lean:88 (WholeDesignM6)
example: Prob046_dff8p (LeanRTL/Designs/VEval/Prob046Dff8p.lean:88)
maturity: promoted
---
# Dual edge = two opposite-polarity registers

A single-edge `negedge` register (`Reg.negedge := true`) is INSIDE the flagship whole-design M6 theorem — `moduleChecksb` gates `asyncReset`/`asyncLoad`/`clockNet`/`mems` but NOT `negedge`, so a negedge-only design passes verbatim (`Negedge.lean` packages this as `WholeDesignM6` for `Prob046_dff8p`; `CLK_POLARITY = if r.negedge then 0 else 1` in the compiler). A design that mixes a posedge and a negedge flop on one clock is supported by modelling each edge as its own register and proving per-register + cosim — the sub-cycle interleaving is captured by the two registers. Gotcha: the same FF sampling BOTH edges (true DDR) is a genuine limit (CORE §1.2) — do not model it as one register; two opposite-polarity registers is the only supported shape.

**Emission: a dual-edge module goes out through F9, one `always` block per edge.** `emitProcVerilog` groups registers by `Reg.negedge` and writes `always @(posedge clk)` then `always @(negedge clk)`; a single-edge module still emits exactly one block, byte-for-byte as before. This used to return `none` and fall back to `write_verilog`, and the fallback lost designs: Yosys lifts the reset test onto continuous-assign wires (`_09_ = ~rst; _08_ = _09_ | …`), whose deltas land *after* the clock edge, so a testbench that releases reset in the same timestep as an edge sees the flop sample the pre-release value and the whole trace runs one cycle late. F9 computes the same test with a blocking assignment inside the block — post-edge, which is the property F9 exists for. Measured on ChipBench `Prob016_odd-number_division_with_a_duty_cycle_of_half`: 172/621 mismatches on the fallback, **0/621** through F9, miter still `Equivalence successfully proven!`.

Note what this does *not* buy. `Module.step` advances every register — posedge and negedge alike — from one pre-edge environment, so the cycle model still cannot place the negedge flop half a cycle later than the posedge one. `semanticCoverage` keeps reporting `CoverageReason.negedgeMix` and the scorer keeps printing OUT OF THE REFERENCE SEMANTICS. That is correct and should stay: the *emitted Verilog* is now certified equal to the verified RTLIL, but the whole-trace theorem is stated in a coarser timing model than the hardware runs in.

## Worked example

```lean
theorem wholeDesignM6_of_checked (m : Module) (hr : m.reset = none)
    (hchk : moduleChecksb m = true) : WholeDesignM6 m :=
  fun Q inputs => compileModule_seq_correct_wires_checked m hr hchk Q inputs
```
> Source: LeanRTL/Designs/VEval/Prob046Dff8p.lean:88
