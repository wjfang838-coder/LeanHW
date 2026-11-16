import LeanRTL.Core.Refine
/-!
# `Lib/Semantic/Delay` — reusable L5 combinators for fixed-latency shift / delay lines

A registered delay line is the recurring L5 shape "output at cycle `t` is a serial input sampled a
fixed number of cycles ago".  Three flavours keep re-appearing across the corpus, each with the
*same* induction on the cycle index unfolding `specTrace_succ` through a per-stage shift; this file
extracts the induction once so a design supplies only its **per-stage shift `specStep` fact** and
reads the closed form off in one call.

| combinator          | spec-step shape (per cycle)                            | closed form |
| ------------------- | ------------------------------------------------------ | ----------- |
| `delayBit`          | `σ' = σ.setWidth w ++ sb`  (new bit enters at the LSB) | `bit i(t) = in(t−1−i)` |
| `delay_reads`       | ↑ specialised to the deepest bit `w`                   | `out(t) = in(t−(w+1))` |
| `delayBitDown`      | `σ' = (σ >>> 1) ||| sb <<< w`  (new bit enters at MSB) | `bit i(t) = in(t−(w+1−i))` |
| `specTrace_run`     | `σ' = op σ` on a window of beats                       | `σ(a+n) = opⁿ σ(a)` |

`delayBit`/`delayBitDown` give the whole per-bit law for a `(w+1)`-deep register (the serial input
`sb : Env → BitVec 1` extracted from the pins, register state `BitVec (w+1)`, init `0`).  The scalar
`delay_reads` is the headline "fixed latency `k = w+1`": once `w+1` bits have streamed, the deepest
bit reads the input delayed by exactly the register depth.  `specTrace_run` is the orthogonal
*load-then-iterate* law (a loaded word passed through `n` identical shift beats reads `opⁿ` of the
load), which combined with the `applyN_*` shift-power lemmas closes the variable-shift `q = d >>> k`
family.  All are stated on the reset-free spec trace (`specTrace specStep 0`), exactly the L3 traces
the WholeDesign corollaries compose with; zero `sorry`, axiom-clean.
-/

namespace LeanRTL.Lib.Semantic.Delay
open LeanRTL LeanRTL.CompilerCorrectSeq LeanRTL.Refine

/-! ## 1. Append-at-LSB delay line (new serial bit enters the LSB, ages toward the MSB)

The spec step is `σ' = {σ[w-1:0], sb}` — drop the MSB, shift up, insert the fresh serial bit `sb`
at the LSB.  So bit `i` of the register at cycle `t` is the serial input sampled `i+1` cycles ago
(`false` before it has streamed that deep).  Caller supplies `hstep`, the per-cycle *shift fact*
`specStep σ(n) (inputs n) = σ(n).setWidth w ++ sb (inputs n)` — for the always-shifting design this
is `fun _ => rfl`; a gated design proves it from its per-cycle enable/valid hypotheses. -/

/-- **Per-bit fixed-latency delay law** (append-at-LSB).  For a `(w+1)`-deep shift register whose
    spec step shifts a fresh serial bit `sb` in at the LSB every cycle, bit `i` at cycle `t` reads
    the serial input sampled `i+1` cycles ago (or `false` if that is before power-up). -/
theorem delayBit {w : Nat} (sb : Env → BitVec 1) (inputs : Nat → Env)
    (specStep : BitVec (w + 1) → Env → BitVec (w + 1))
    (hstep : ∀ n, specStep (specTrace specStep 0 inputs n) (inputs n)
                  = (specTrace specStep 0 inputs n).setWidth w ++ sb (inputs n)) :
    ∀ t i, i < w + 1 →
      (specTrace specStep 0 inputs t).getLsbD i
        = if i < t then (sb (inputs (t - 1 - i))).getLsbD 0 else false := by
  intro t
  induction t with
  | zero =>
    intro i _
    rw [if_neg (Nat.not_lt_zero i)]
    show (0 : BitVec (w + 1)).getLsbD i = false
    simp
  | succ n ih =>
    intro i hi
    rw [specTrace_succ, hstep n, BitVec.getLsbD_append]
    match i with
    | 0 =>
      rw [if_pos (by omega : (0 : Nat) < 1), if_pos (Nat.succ_pos n)]
      rfl
    | i + 1 =>
      rw [if_neg (by omega : ¬ (i + 1 < 1)), Nat.add_sub_cancel,
          BitVec.getLsbD_setWidth, ih i (by omega)]
      by_cases hin : i < n
      · rw [if_pos hin, if_pos (by omega : i + 1 < n + 1),
            (by omega : n + 1 - 1 - (i + 1) = n - 1 - i),
            decide_eq_true (by omega : i < w), Bool.true_and]
      · rw [if_neg hin, if_neg (by omega : ¬ (i + 1 < n + 1)), Bool.and_false]

/-- **Scalar fixed-latency delay** (append-at-LSB).  The deepest bit `w` of a `(w+1)`-deep append
    shift register reads the serial input delayed by exactly the register depth `w+1`:
    `out(t) = in(t − (w+1))` for `t ≥ w+1`.  The headline `out(t) = in(t−k)` with latency `k = w+1`. -/
theorem delay_reads {w : Nat} (sb : Env → BitVec 1) (inputs : Nat → Env)
    (specStep : BitVec (w + 1) → Env → BitVec (w + 1))
    (hstep : ∀ n, specStep (specTrace specStep 0 inputs n) (inputs n)
                  = (specTrace specStep 0 inputs n).setWidth w ++ sb (inputs n))
    (t : Nat) (ht : w + 1 ≤ t) :
    (specTrace specStep 0 inputs t).getLsbD w = (sb (inputs (t - (w + 1)))).getLsbD 0 := by
  rw [delayBit sb inputs specStep hstep t w (Nat.lt_succ_self w), if_pos (by omega : w < t),
      (by omega : t - 1 - w = t - (w + 1))]

/-! ## 2. Insert-at-MSB delay line (new serial bit enters the MSB, ages toward the LSB)

The mirror of §1: the spec step is `σ' = (σ >>> 1) ||| (sb <<< w)` — right-shift by one and insert
the fresh serial bit at the MSB (bit `w`).  So bit `i` at cycle `t` is the serial input sampled
`(w+1)−i` cycles ago; the deepest bit `0` is the input delayed by the full depth `w+1`. -/

/-- **Per-bit fixed-latency delay law** (insert-at-MSB).  For a `(w+1)`-deep shift register whose
    spec step right-shifts and inserts the fresh serial bit `sb` at the MSB every cycle, bit `i` at
    cycle `t` reads the serial input sampled `(w+1)−i` cycles ago (or `false` if before power-up). -/
theorem delayBitDown {w : Nat} (sb : Env → BitVec 1) (inputs : Nat → Env)
    (specStep : BitVec (w + 1) → Env → BitVec (w + 1))
    (hstep : ∀ n, specStep (specTrace specStep 0 inputs n) (inputs n)
                  = (specTrace specStep 0 inputs n >>> 1)
                    ||| ((sb (inputs n)).setWidth (w + 1) <<< w)) :
    ∀ t i, i < w + 1 →
      (specTrace specStep 0 inputs t).getLsbD i
        = if w + 1 - i ≤ t then (sb (inputs (t - (w + 1 - i)))).getLsbD 0 else false := by
  intro t
  induction t with
  | zero =>
    intro i hi
    rw [if_neg (by omega : ¬ (w + 1 - i ≤ 0))]
    show (0 : BitVec (w + 1)).getLsbD i = false
    simp
  | succ n ih =>
    intro i hi
    rw [specTrace_succ, hstep n, BitVec.getLsbD_or, BitVec.getLsbD_ushiftRight,
        BitVec.getLsbD_shiftLeft]
    by_cases hiw : i < w
    · rw [show (!decide (i < w)) = false by simp [hiw], Bool.and_false, Bool.false_and,
          Bool.or_false, ih (1 + i) (by omega)]
      by_cases hle : w + 1 - i ≤ n + 1
      · rw [if_pos (by omega : w + 1 - (1 + i) ≤ n), if_pos hle,
            (by omega : n - (w + 1 - (1 + i)) = n + 1 - (w + 1 - i))]
      · rw [if_neg (by omega : ¬ (w + 1 - (1 + i) ≤ n)), if_neg hle]
    · have hiw2 : i = w := by omega
      subst hiw2
      have hout : (specTrace specStep 0 inputs n).getLsbD (1 + i) = false := by
        cases h : (specTrace specStep 0 inputs n).getLsbD (1 + i) with
        | false => rfl
        | true => exact absurd (BitVec.lt_of_getLsbD h) (by omega)
      rw [hout, Bool.false_or, if_pos (by omega : i + 1 - i ≤ n + 1),
          (by omega : n + 1 - (i + 1 - i) = n)]
      simp

/-! ## 3. Load-then-iterate: a loaded word passed through `n` identical shift beats

Orthogonal to the streaming delays above: a *loaded* word run through `n` identical beats (each
applying a fixed operator `op` — shift-by-one, rotate-by-one, …) reads `opⁿ` of the load.  Combined
with the `applyN_*` shift-power lemmas this closes the variable-shift `q = d >>> k` / `d <<< k`
family in one call.  `applyN op n` is the `n`-fold self-composition of `op` (self-contained; no
`Function.iterate` dependency). -/

/-- `n`-fold self-composition of `op` — `applyN op (n+1) s = op (applyN op n s)`. -/
def applyN {S : Type _} (op : S → S) : Nat → S → S
  | 0,     s => s
  | n + 1, s => op (applyN op n s)

/-- `n` right-shift-by-one beats equal one right-shift by `n`. -/
theorem applyN_ushiftRight {w : Nat} (x : BitVec w) :
    ∀ k, applyN (fun y : BitVec w => y >>> 1) k x = x >>> k
  | 0     => (BitVec.ushiftRight_zero x).symm
  | k + 1 => by
      simp only [applyN]
      rw [applyN_ushiftRight x k]; exact (BitVec.shiftRight_add x k 1).symm

/-- `n` left-shift-by-one beats equal one left-shift by `n`. -/
theorem applyN_shiftLeft {w : Nat} (x : BitVec w) :
    ∀ k, applyN (fun y : BitVec w => y <<< 1) k x = x <<< k
  | 0     => (BitVec.shiftLeft_zero x).symm
  | k + 1 => by
      simp only [applyN]
      rw [applyN_shiftLeft x k]; exact (BitVec.shiftLeft_add x k 1).symm

/-- `n` arithmetic-shift-right-by-one beats equal one arithmetic shift right by `n`. -/
theorem applyN_sshiftRight {w : Nat} (x : BitVec w) :
    ∀ k, applyN (fun y => y.sshiftRight 1) k x = x.sshiftRight k
  | 0     => BitVec.sshiftRight_zero.symm
  | k + 1 => by
      simp only [applyN]
      rw [applyN_sshiftRight x k]
      exact (BitVec.sshiftRight_add (x := x) (m := k) (n := 1)).symm

/-- **Windowed iterate law.**  If on the window `[a, a+n)` every spec step acts as the fixed
    operator `op` (the design proves this from its per-beat run/enable hypotheses), then the spec
    trace at `a+n` is `opⁿ` of the trace at `a` — the load-then-shift closed form.  Compose with a
    load fact `specTrace … a = d` and an `applyN_*` shift-power lemma to read `q = op-power d`. -/
theorem specTrace_run {S : Type _} (specStep : S → Env → S) (s0 : S) (inputs : Nat → Env)
    (a : Nat) (op : S → S) :
    ∀ n, (∀ j, j < n → specStep (specTrace specStep s0 inputs (a + j)) (inputs (a + j))
                        = op (specTrace specStep s0 inputs (a + j))) →
    specTrace specStep s0 inputs (a + n) = applyN op n (specTrace specStep s0 inputs a)
  | 0,     _   => rfl
  | n + 1, hop => by
      show specTrace specStep s0 inputs ((a + n) + 1)
          = applyN op (n + 1) (specTrace specStep s0 inputs a)
      rw [specTrace_succ, hop n (Nat.lt_succ_self n),
          specTrace_run specStep s0 inputs a op n (fun j hj => hop j (Nat.lt_succ_of_lt hj))]
      rfl

end LeanRTL.Lib.Semantic.Delay
