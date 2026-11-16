---
id: fixed-latency-delay-law
layer: pattern
applies_to: pipeline / shift-register delay lines
principle: commuting-square-and-generic-induction
tactics: [apply-infer-envs]
lib: LeanRTL/Lib/Semantic/Delay.lean (delay_reads)
example: shift / history (LeanRTL/Designs/Rtllm/RightShifter.lean:110)
maturity: promoted
---
# Fixed-latency delay law

A registered delay line has a whole-trace law: the output at cycle `t` equals the input at cycle `t − L` (for fixed latency `L`). The generic induction lives once in `LeanRTL/Lib/Semantic/Delay.lean`; a design supplies only its **per-stage shift `specStep` fact** and reads the closed form off in one composed call, then `.trans`-es it onto the design's L3 `<slug>_trace`. Combinators:

* `delayBit` / `delay_reads` — new serial bit enters the **LSB** (`σ' = σ.setWidth w ++ sb`): bit `i(t) = in(t−1−i)`, deepest bit `out(t) = in(t−(w+1))`. Used by `sipo_bit_reads`, `history_reads`.
* `delayBitDown` — new serial bit enters the **MSB** (`σ' = (σ >>> 1) ||| sb <<< w`): bit `i(t) = in(t−(w+1−i))`. Used by `rightshifter_reads`.
* `specTrace_run` + `applyN_ushiftRight/_shiftLeft/_sshiftRight` — the orthogonal *load-then-iterate* law (`σ(a+n) = opⁿ σ(a)`) closing the variable-shift `q = d >>> k` / `d <<< k` family. Used by `shift4_reads`, `shift18_shl_reads`, `shift18_asr_reads`.

The caller's `specStep` fact is `fun _ => rfl` for an always-shifting design, or proved from per-cycle enable/valid hypotheses (`history_reads`). Design and L3 files stay untouched — the delay statement is a corollary in the WholeDesign layer. Gotcha: pin the exact latency `L = w+1 = register depth` (registered output reads one cycle late in cocotb, see delay-off-by-one) — an off-by-one in `L` makes the corollary false even though the L3 trace is correct.

## Worked example

```lean
theorem rightshifter_reads (inputs : Nat → Env) (t i : Nat) (hi : i < 8) :
    (BitVec.ofNat 8 (regTrace impl inputs (fun _ => false) t "q")).getLsbD i
      = if 8 - i ≤ t then (BitVec.ofNat 1 (inputs (t - (8 - i)) "d")).getLsbD 0
        else false :=
  (congrArg (fun v => v.getLsbD i) (rightshifter_trace inputs t)).trans
    (delayBitDown (w := 7) (fun inp => BitVec.ofNat 1 (inp "d")) inputs specN (fun _ => rfl) t i hi)
```
> Source: LeanRTL/Designs/Rtllm/RightShifter.lean:110 (rightshifter_reads)
