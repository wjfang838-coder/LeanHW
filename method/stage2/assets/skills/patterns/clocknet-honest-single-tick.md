---
id: clocknet-honest-single-tick
layer: pattern
applies_to: multi-clock / gated / derived-clock designs
principle: leaf-is-decision-not-induction
tactics: [bv-decide-for-fixed-width]
lib: LeanRTL/Core/Syntax.lean (Reg.clockNet); docs/instructions/CORE.md §1.3
example: GFCM / async_fifo (LeanRTL/Designs/Cvdp/CvdpGFCM0001.lean, CvdpAgentic/AsyncFifo.lean)
maturity: promoted
---
# clockNet: honest single-tick + cosim

A register on a second clock (`Reg.clockNet := some (.var "clk2" 1)`) does NOT enter `Module.simulate` — the two edge streams interleave arbitrarily, so no whole-design cycle theorem is claimed (`moduleChecksb` declines). Prove instead the honest single-tick next-cone per clock domain and validate the crossing by co-simulation. In `CvdpGFCM0001.lean`: `clk1_en_correct` (module clock), `clk2_en_correct` (sampled on each `clk2 ↑`), and `clock_domains` pinning the per-register `clockNet` list. Gotcha: CDC metastability lives in the per-access/cosim layer, not in Lean — do not claim a whole-design trace across two clocks; state exactly which edge each register samples.

## Worked example

```lean
theorem clk2_en_correct (clk1 clk2 sel clk1_en clk2_en : BitVec 1) :
    eval en2Next (env clk1 clk2 sel clk1_en clk2_en) = specEn2 sel clk1_en := by …

theorem clock_domains :
    impl.clock = some "clk1"
      ∧ impl.regs.map (·.clockNet) = [none, some (.var "clk2" 1)] := by
  exact ⟨rfl, rfl⟩
```
> Source: LeanRTL/Designs/Cvdp/CvdpGFCM0001.lean:103
