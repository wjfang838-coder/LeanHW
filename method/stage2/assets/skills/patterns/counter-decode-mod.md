---
id: counter-decode-mod
layer: pattern
applies_to: free-running / modulo counters (L5 semantic headline)
principle: leaf-is-decision-not-induction
tactics: [nat-mod-eq-of-lt, omega-for-bounds, decide-for-finite]
lib: LeanRTL/Lib/Semantic/DecodeMod.lean (decode_mod)
example: count10 / count15 / counter_12 (LeanRTL/Designs/VEval/Prob040Count10.lean:96)
maturity: promoted
---
# Counter decode to `t mod N`

The L5 headline for a free-running counter is a closed function of the cycle index: after `t` reset-free ticks the register reads `f t` (`t mod N`, `1 + t mod N`, `t` for a period-`2^w` counter). The closed-form induction is no longer hand-rolled — it lives once in `LeanRTL/Lib/Semantic/DecodeMod.lean`. A design pins its reset/enable inputs so the abstract step collapses to a canonical wrap-`N` transition, then hands that one-line fact to the matching combinator:

- `decode_mod N` — 0-based `if q = ofNat w (N−1) then 0 else q+1` (`incrMod`) ⟶ `ofNat w (t % N)` (`count10`, `counter_12`, `countslow`).
- `decode_mod_from N c` — the `[c, c+N−1]` counter (`incrModFrom`) ⟶ `ofNat w (c + t % N)` (`count1to10`, `c = 1`).
- `decode_add1` — period-`2^w` counter whose step is a bare `q+1` ⟶ `ofNat w t` (`count15`, `up_down` up-mode).

The combinator owns the width-generic arithmetic (`mod_step`: only ONE state wraps at `N−1`, off it `m+1 < N` makes the `%` vanish; the wrap uses `Nat.mod_self` and the succ uses `BitVec.ofNat_add`, both good for a **variable** `N` where `omega` cannot divide) and the induction on `t`. The design supplies only the `specStep = incr-mod-N` equation. Toggle-tap dividers (`freq_div`, `square_wave`) are tuples `(counter, ⌊t/N⌋ mod 2)`; they reuse only the arithmetic `mod_step`, not the single-register `decode_*`.

## Worked example

```lean
theorem closed (inputs : Nat → Env)
    (hnr : ∀ k, BitVec.ofNat 1 (inputs k "reset") = 0) (t : Nat) :
    specTrace specN 0 inputs t = BitVec.ofNat 4 (t % 10) := by
  refine decode_mod 10 (by decide) (by decide) (fun q n => ?_) t
  show spec q (BitVec.ofNat 1 (inputs n "reset")) = incrMod 4 10 q
  rw [hnr n, spec, if_neg (by decide)]; rfl
```
> Source: LeanRTL/Designs/VEval/Prob040Count10.lean:96 (`Count10.closed`)
