import LeanRTL.Core.Refine
import LeanRTL.Lib.Semantic.BitVecArith
/-!
# `Lib/Semantic/DecodeMod` — the reusable **L5 mod-`N` decode combinator**

The L5 "headline" for a free-running counter is a *closed arithmetic function of the cycle index*:
after `t` reset-free clock ticks the register reads `f t` for an explicit `f` (`t mod N`,
`1 + t mod N`, `t` for a period-`2^w` counter, …).  The L3 `*_trace` bridge already gives
`α (regTrace impl inputs (fun _=>false) t) = specTrace specStep s0 inputs t`; what remained
hand-rolled in ~5 counter designs was the **closed-form induction** that evaluates the opaque
`t`-fold `specTrace` iterate to `BitVec.ofNat w (f t)`.

This file extracts that induction once.  A counter design supplies ONLY its
`specStep = increment-mod-N` fact (`∀ q n, specStep q (inputs n) = incrMod w N q`, i.e. "on this
input stream my abstract step is the canonical wrap-at-`N` transition on every state") and gets the
closed form for free.  The three shapes:

| combinator        | spec step                          | closed form            | example        |
| ----------------- | ---------------------------------- | ---------------------- | -------------- |
| `decode_add1`     | `q + 1` (period `2^w`, no wrap `if`) | `ofNat w t`          | `count15`      |
| `decode_mod`      | `incrMod w N q` (wrap `N-1 → 0`)     | `ofNat w (t % N)`    | `count10`, `counter_12`, `countslow` |
| `decode_mod_from` | `incrModFrom w N c q` (values `[c,c+N-1]`, wrap `→ c`) | `ofNat w (c + t % N)` | `count1to10`   |

## The arithmetic core

Everything rests on two width-generic Nat↔BitVec bridges, so `N`/`w` are genuine parameters (no
per-width `mod_step4`/`mod_step3`/`mod_step6` copies):

* `ofNat_succ` — `ofNat w m + 1 = ofNat w (m+1)` (via `BitVec.ofNat_add`), replacing the per-width
  `bv_omega` succ lemmas;
* `mod_step` / `mod_step_from` — the single decode step: `incrMod w N (ofNat w m) = ofNat w
  ((m+1) % N)` for `m < N`, `N ≤ 2^w`.  The wrap branch closes with `Nat.mod_self` (works for a
  *variable* `N`, unlike `omega`); the increment branch with `Nat.mod_eq_of_lt` + `ofNat_succ`.

The per-design induction then reuses `specTrace_succ` and lines the closed form up with the
variable-`N` step via `Nat.mod_add_mod` (`(n % N + 1) % N = (n + 1) % N`, again `omega`-proof for
a *literal* `N` but a library lemma for a variable one).
-/

namespace LeanRTL.Lib.Semantic.DecodeMod
open LeanRTL LeanRTL.CompilerCorrectSeq LeanRTL.Refine

/-! ## Width-generic Nat ↔ BitVec bridges

`ofNat_succ` (`ofNat w m + 1 = ofNat w (m+1)`) and `bv_ne_of_ne` (in-range decode disequality) are
bare `BitVec`/`Nat` facts — nothing counter-specific — so they now live in
`LeanRTL/Lib/Semantic/BitVecArith.lean`.  They are re-exported here so existing
`DecodeMod.ofNat_succ` / `DecodeMod.bv_ne_of_ne` references (and the unqualified uses in `mod_step`
below) keep resolving unchanged. -/

export LeanRTL.Lib.Semantic.BitVecArith (ofNat_succ bv_ne_of_ne)

/-! ## `decode_add1` — pure free-running increment (period `2^w`, no wrap conditional) -/

/-- **Pure-increment closed form.**  If the spec step is a bare `q + 1` on the given stream (a
    counter whose period is exactly `2^w`, so the wrap is the natural BitVec overflow and there is
    no `mod N` decode), then the width-`w` register reads `ofNat w t` at every cycle. -/
theorem decode_add1 {w : Nat} {inputs : Nat → Env} {specStep : BitVec w → Env → BitVec w}
    (hstep : ∀ (q : BitVec w) (n : Nat), specStep q (inputs n) = q + 1) (t : Nat) :
    specTrace specStep 0 inputs t = BitVec.ofNat w t := by
  induction t with
  | zero => rfl
  | succ n ih => rw [specTrace_succ, ih, hstep, ofNat_succ]

/-! ## `decode_mod` — 0-based wrap-mod-`N` counter -/

/-- The canonical **0-based increment-mod-`N`** transition on a width-`w` decode: wrap at the top
    residue `N-1` back to `0`, otherwise `+1`.  This is the shape every mod-`N` counter's abstract
    step collapses to once its reset/enable inputs are pinned. -/
def incrMod (w N : Nat) (q : BitVec w) : BitVec w :=
  if q = BitVec.ofNat w (N - 1) then 0 else q + 1

/-- **The single decode step** (width-generic, `N ≤ 2^w`).  From a decode `ofNat w m` with `m < N`,
    the `incrMod` transition lands on `ofNat w ((m+1) % N)`.  Replaces the per-width
    `mod_step4`/`mod_step3`/`mod_step6` copies. -/
theorem mod_step {w : Nat} (N m : Nat) (hm : m < N) (hN : N ≤ 2 ^ w) :
    incrMod w N (BitVec.ofNat w m) = BitVec.ofNat w ((m + 1) % N) := by
  have hmw : m < 2 ^ w := by omega
  unfold incrMod
  by_cases hc : m = N - 1
  · rw [if_pos (by rw [hc]), hc, show N - 1 + 1 = N by omega, Nat.mod_self]; rfl
  · have hlt : m + 1 < N := by omega
    have hne : BitVec.ofNat w m ≠ BitVec.ofNat w (N - 1) :=
      bv_ne_of_ne hmw (by omega) hc
    rw [if_neg hne, Nat.mod_eq_of_lt hlt, ofNat_succ]

/-- **The 0-based mod-`N` closed form.**  If, on the given input stream, the spec step acts as the
    canonical increment-mod-`N` transition on every state
    (`hstep : ∀ q n, specStep q (inputs n) = incrMod w N q`), then the spec trace from `s0 = 0`
    reads `ofNat w (t % N)` at every cycle. -/
theorem decode_mod {w : Nat} {inputs : Nat → Env} {specStep : BitVec w → Env → BitVec w}
    (N : Nat) (hpos : 0 < N) (hN : N ≤ 2 ^ w)
    (hstep : ∀ (q : BitVec w) (n : Nat), specStep q (inputs n) = incrMod w N q)
    (t : Nat) :
    specTrace specStep 0 inputs t = BitVec.ofNat w (t % N) := by
  induction t with
  | zero => show (0 : BitVec w) = BitVec.ofNat w (0 % N); rw [Nat.zero_mod]; rfl
  | succ n ih =>
    rw [specTrace_succ, ih, hstep, mod_step N (n % N) (Nat.mod_lt n hpos) hN, Nat.mod_add_mod]

/-! ## `decode_mod_from` — offset wrap-mod-`N` counter (values in `[c, c+N-1]`) -/

/-- The **offset increment-mod-`N`** transition: values live in `[c, c+N-1]`, wrap at the top
    `c+N-1` back to `c`, otherwise `+1`.  `incrMod` is the `c = 0` case (kept separate because
    `0 + N - 1` is not definitionally `N - 1`). -/
def incrModFrom (w N c : Nat) (q : BitVec w) : BitVec w :=
  if q = BitVec.ofNat w (c + N - 1) then BitVec.ofNat w c else q + 1

/-- **The single offset decode step** (`c + N ≤ 2^w`).  From `ofNat w (c + m)` with `m < N`, the
    `incrModFrom` transition lands on `ofNat w (c + (m+1) % N)`. -/
theorem mod_step_from {w : Nat} (N c m : Nat) (hm : m < N) (hbound : c + N ≤ 2 ^ w) :
    incrModFrom w N c (BitVec.ofNat w (c + m)) = BitVec.ofNat w (c + (m + 1) % N) := by
  unfold incrModFrom
  by_cases hc : m = N - 1
  · rw [if_pos (by rw [hc]; congr 1; omega), hc, show (N - 1 + 1) % N = 0 by
        rw [show N - 1 + 1 = N by omega, Nat.mod_self]]
    congr 1
  · have hlt : m + 1 < N := by omega
    have hne : BitVec.ofNat w (c + m) ≠ BitVec.ofNat w (c + N - 1) :=
      bv_ne_of_ne (by omega) (by omega) (by omega)
    rw [if_neg hne, Nat.mod_eq_of_lt hlt, ofNat_succ, show c + m + 1 = c + (m + 1) by omega]

/-- **The offset mod-`N` closed form.**  If the spec step acts as `incrModFrom w N c` on every state
    (`hstep`), the spec trace from `s0 = ofNat w c` reads `ofNat w (c + t % N)` at every cycle —
    e.g. `c = 1` gives the `1..N` counter `1 + (t mod N)`. -/
theorem decode_mod_from {w : Nat} {inputs : Nat → Env} {specStep : BitVec w → Env → BitVec w}
    (N c : Nat) (hpos : 0 < N) (hbound : c + N ≤ 2 ^ w)
    (hstep : ∀ (q : BitVec w) (n : Nat), specStep q (inputs n) = incrModFrom w N c q)
    (t : Nat) :
    specTrace specStep (BitVec.ofNat w c) inputs t = BitVec.ofNat w (c + t % N) := by
  induction t with
  | zero => show BitVec.ofNat w c = BitVec.ofNat w (c + 0 % N); rw [Nat.zero_mod, Nat.add_zero]
  | succ n ih =>
    rw [specTrace_succ, ih, hstep, mod_step_from N c (n % N) (Nat.mod_lt n hpos) hbound,
        Nat.mod_add_mod]

end LeanRTL.Lib.Semantic.DecodeMod
