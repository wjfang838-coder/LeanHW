import LeanRTL.Core.Refine
/-!
# `Lib/Semantic/Divider` — the ÷N toggle-tap engine (shared by every frequency divider)

Every clock divider / periodic generator in the corpus is a **mod-`N` counter feeding a toggle
output**: a phase counter wraps at `N−1` (period `N`), and a one-bit tap flips exactly on the wrap
cycle.  The output level at cycle `t` is therefore the *parity of completed periods*,
`⌊t/N⌋ mod 2` — a 50 %-duty square wave of period `2N`.  Closing that reads-law needs three
width- and divisor-generic Euclidean facts, hand-rolled once inside `L5Freq` and shared here so the
four post-split divider designs (`square_wave`, `freq_div`, `freq_divbyeven`, …) draw on one engine.

The counter half (`cnt = t mod N`, the `incrMod` wrap step) is `DecodeMod.mod_step`; this file adds
the **toggle-parity** half:

* `succ_wrap` / `succ_nowrap` — how `(n+1)`'s Euclidean quotient/remainder move for a **variable**
  divisor `F` (from `Nat.div_add_mod`; `omega` cannot divide by a non-literal), at and off the wrap;
* `bv1_toggle` — the 1-bit tap absorption `~~~(ofNat 1 (m % 2)) = ofNat 1 ((m+1) % 2)` (the tap is
  the parity `⌊t/N⌋ mod 2`, and complementing it is the parity successor).
-/

namespace LeanRTL.Lib.Semantic.Divider

/-- **1-bit toggle = parity successor**: `~~~(ofNat 1 (m % 2)) = ofNat 1 ((m+1) % 2)`.  A tap that
    complements each period turns the parity of completed periods into its successor. -/
theorem bv1_toggle (m : Nat) :
    ~~~ (BitVec.ofNat 1 (m % 2)) = BitVec.ofNat 1 ((m + 1) % 2) := by
  rcases Nat.mod_two_eq_zero_or_one m with h | h <;>
    rw [h, show (m + 1) % 2 = (m % 2 + 1) % 2 by omega, h] <;> decide

/-- **Euclidean wrap step (variable divisor).**  At a wrap cycle (`n mod F = F−1`) the remainder
    returns to 0 and the quotient — the number of completed periods — advances by one. -/
theorem succ_wrap {F n : Nat} (hF : 0 < F) (h : n % F = F - 1) :
    (n + 1) % F = 0 ∧ (n + 1) / F = n / F + 1 := by
  have hd := Nat.div_add_mod n F
  have hn1 : n + 1 = F * (n / F + 1) := by rw [Nat.mul_add, Nat.mul_one]; omega
  refine ⟨?_, ?_⟩
  · rw [hn1]; exact Nat.mul_mod_right F _
  · rw [hn1]; exact Nat.mul_div_cancel_left _ hF

/-- **Euclidean non-wrap step (variable divisor).**  Off the wrap cycle the remainder increments
    and the quotient holds. -/
theorem succ_nowrap {F n : Nat} (hF : 0 < F) (h : n % F ≠ F - 1) :
    (n + 1) % F = n % F + 1 ∧ (n + 1) / F = n / F := by
  have hd := Nat.div_add_mod n F
  have hlt : n % F < F := Nat.mod_lt n hF
  have hlt' : n % F + 1 < F := by omega
  have hn1 : n + 1 = F * (n / F) + (n % F + 1) := by omega
  refine ⟨?_, ?_⟩
  · rw [hn1, Nat.mul_add_mod]; exact Nat.mod_eq_of_lt hlt'
  · rw [hn1, Nat.mul_add_div hF, Nat.div_eq_of_lt hlt', Nat.add_zero]

end LeanRTL.Lib.Semantic.Divider
