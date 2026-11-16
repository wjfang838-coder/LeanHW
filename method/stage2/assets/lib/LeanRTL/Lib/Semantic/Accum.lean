import LeanRTL.Core.Refine
/-!
# `Lib/Semantic/Accum` — the reusable running-sum accumulator combinator (L5)

Roughly seven whole-design L5 headlines ("the accumulator reads a running sum `Σ`") hand-roll the
*same* induction: a spec whose step is `acc := acc + f(input)` (optionally gated by an enable)
has `t`-fold iterate `acc(t) = acc₀ + Σ_{j<t} (gated f(input j))`.  Only the element function `f`,
the accumulator width `w`, and the (optional) gate `g` change between designs; the induction on the
cycle index — reusing `specTrace_succ`, growing the sum by one term per cycle — is identical.

This file extracts that induction *once*.  A design supplies only its per-cycle **accumulate fact**
(`specStep s (inputs k) = s + f (inputs k)`, itself usually the design's `next_correct` specialised
to the non-reset cone) and gets the `Σ` closed form via a single `accumulator_reads` call — no
bespoke `induction t` needed.

Everything is stated in `BitVec w`, so the sum is exact **mod `2^w`** — it wraps precisely like the
hardware register add.  A design that additionally wants an *exact* `Nat` sum (no wrap) composes the
`BitVec` law with its own in-range bound, exactly as before (`accu`/`cascaded_adder`).

| combinator                 | spec step                                    | closed form                       |
| -------------------------- | -------------------------------------------- | --------------------------------- |
| `accumulator_reads`        | `acc := acc + f(i)`                          | `acc₀ + Σ_{j<t} f(input j)`       |
| `accumulator_reads_gated`  | `acc := acc + (if g(i) then f(i) else 0)`    | `acc₀ + Σ_{j<t} gated f(input j)` |

**Does not fit** (and why): saturating accumulators (`SetBitStreamCalculator`, which clamps at 255
instead of wrapping — a different arithmetic, needs the `Σ ≤ 255` bound) and grouped/periodic-reset
accumulators (`accu`, whose state is a `(cnt, acc, …)` tuple that clears `acc` every 4 beats, not a
single monotone accumulator).  Those keep their bespoke proofs.
-/

namespace LeanRTL.Lib.Semantic.Accum
open LeanRTL LeanRTL.CompilerCorrectSeq LeanRTL.Refine

/-! ## The running sums (in `BitVec w`, i.e. exact mod `2^w`) -/

/-- The ungated running sum `Σ_{j<t} f(input j)`, folded in `BitVec w` (wraps mod `2^w`). -/
def sumBV {w : Nat} (f : Env → BitVec w) (inputs : Nat → Env) : Nat → BitVec w
  | 0     => 0
  | t + 1 => sumBV f inputs t + f (inputs t)

@[simp] theorem sumBV_zero {w : Nat} (f : Env → BitVec w) (inputs : Nat → Env) :
    sumBV f inputs 0 = 0 := rfl

theorem sumBV_succ {w : Nat} (f : Env → BitVec w) (inputs : Nat → Env) (t : Nat) :
    sumBV f inputs (t + 1) = sumBV f inputs t + f (inputs t) := rfl

/-- The gated running sum `Σ_{j<t} (if g(input j) then f(input j) else 0)`, folded in `BitVec w`.
    An un-enabled cycle contributes `0`, so the accumulator holds only across live beats. -/
def gatedSumBV {w : Nat} (f : Env → BitVec w) (g : Env → Bool) (inputs : Nat → Env) : Nat → BitVec w
  | 0     => 0
  | t + 1 => gatedSumBV f g inputs t + (if g (inputs t) then f (inputs t) else 0)

@[simp] theorem gatedSumBV_zero {w : Nat} (f : Env → BitVec w) (g : Env → Bool)
    (inputs : Nat → Env) : gatedSumBV f g inputs 0 = 0 := rfl

theorem gatedSumBV_succ {w : Nat} (f : Env → BitVec w) (g : Env → Bool) (inputs : Nat → Env)
    (t : Nat) :
    gatedSumBV f g inputs (t + 1)
      = gatedSumBV f g inputs t + (if g (inputs t) then f (inputs t) else 0) := rfl

/-! ## The reusable running-sum inductions -/

/-- **The running-sum accumulator combinator (gated).**  If a spec whose state is a `BitVec w`
    accumulator adds a *gated* element each cycle — `specStep s (inputs k) = s + (if g(input k)
    then f(input k) else 0)` — then its `t`-fold trace from `s0` is `s0` plus the running gated
    sum.  Proved once, by induction on the cycle count reusing `specTrace_succ`; the sum grows by
    exactly one (possibly zero) term per cycle, and `BitVec` `+` associativity re-brackets it.

    The accumulate fact `hstep` is quantified over the cycle index `k` (not an arbitrary `Env`), so
    a design may use its per-cycle side hypotheses (e.g. "reset never asserted at cycle `k`") to
    reduce `specStep` to the bare accumulate on *this* input stream. -/
theorem accumulator_reads_gated {w : Nat} (specStep : BitVec w → Env → BitVec w) (s0 : BitVec w)
    (inputs : Nat → Env) (f : Env → BitVec w) (g : Env → Bool)
    (hstep : ∀ (s : BitVec w) (k : Nat),
        specStep s (inputs k) = s + (if g (inputs k) then f (inputs k) else 0))
    (t : Nat) :
    specTrace specStep s0 inputs t = s0 + gatedSumBV f g inputs t := by
  induction t with
  | zero => exact (BitVec.add_zero s0).symm
  | succ n ih =>
    rw [specTrace_succ, hstep, ih, gatedSumBV_succ, BitVec.add_assoc]

/-- **The running-sum accumulator combinator (ungated).**  The plain accumulator `specStep s
    (inputs k) = s + f(input k)`: its `t`-fold trace from `s0` is `s0 + Σ_{j<t} f(input j)`.  This
    is the workhorse for un-gated MAC / running-sum designs (e.g. `pe`); it is the `g := fun _ =>
    true` instance of `accumulator_reads_gated`, but stated directly against `sumBV` so callers get
    a clean sum with no residual `if true then … else 0`. -/
theorem accumulator_reads {w : Nat} (specStep : BitVec w → Env → BitVec w) (s0 : BitVec w)
    (inputs : Nat → Env) (f : Env → BitVec w)
    (hstep : ∀ (s : BitVec w) (k : Nat), specStep s (inputs k) = s + f (inputs k))
    (t : Nat) :
    specTrace specStep s0 inputs t = s0 + sumBV f inputs t := by
  induction t with
  | zero => exact (BitVec.add_zero s0).symm
  | succ n ih =>
    rw [specTrace_succ, hstep, ih, sumBV_succ, BitVec.add_assoc]

/-! ## The tuple-state (projection) running-sum inductions

`accumulator_reads` covers designs whose *whole* spec state is the `BitVec w` accumulator (`pe`).
Most accumulator designs, however, carry a **tuple** state `S` (the accumulator plus companion
registers — output latches, valid flags, a decimation phase counter, …), and only *one projection*
`π : S → BitVec w` is the running sum.  The induction is identical: as long as the projected step
adds the (gated) element each cycle — `π (specStep s (inputs k)) = π s + …` — its `t`-fold projected
trace is `π s0` plus the running sum.  The companion registers ride along untouched; `π` discards
them.  Proved once, exactly as the single-register versions above. -/

/-- **The projected running-sum accumulator combinator (gated).**  For a tuple-state spec with a
    `BitVec w` accumulator projection `π`, if the projected step adds a *gated* element each cycle,
    then the projected `t`-fold trace from `s0` is `π s0` plus the running gated sum. -/
theorem accumulator_reads_proj_gated {S : Type _} {w : Nat} (specStep : S → Env → S) (s0 : S)
    (π : S → BitVec w) (inputs : Nat → Env) (f : Env → BitVec w) (g : Env → Bool)
    (hstep : ∀ (s : S) (k : Nat),
        π (specStep s (inputs k)) = π s + (if g (inputs k) then f (inputs k) else 0))
    (t : Nat) :
    π (specTrace specStep s0 inputs t) = π s0 + gatedSumBV f g inputs t := by
  induction t with
  | zero => exact (BitVec.add_zero (π s0)).symm
  | succ n ih =>
    rw [specTrace_succ, hstep, ih, gatedSumBV_succ, BitVec.add_assoc]

/-- **The projected running-sum accumulator combinator (ungated).**  The `g := fun _ => true` case
    of `accumulator_reads_proj_gated`, stated directly against `sumBV`: for a tuple-state spec whose
    accumulator projection `π` adds `f(input k)` each cycle, the projected trace reads `π s0 +
    Σ_{j<t} f(input j)` (used by any tuple-state MAC / running-sum design, e.g. the CIC integrator
    stage whose companion state is the decimation phase counter and downstream comb registers). -/
theorem accumulator_reads_proj {S : Type _} {w : Nat} (specStep : S → Env → S) (s0 : S)
    (π : S → BitVec w) (inputs : Nat → Env) (f : Env → BitVec w)
    (hstep : ∀ (s : S) (k : Nat), π (specStep s (inputs k)) = π s + f (inputs k))
    (t : Nat) :
    π (specTrace specStep s0 inputs t) = π s0 + sumBV f inputs t := by
  induction t with
  | zero => exact (BitVec.add_zero (π s0)).symm
  | succ n ih =>
    rw [specTrace_succ, hstep, ih, sumBV_succ, BitVec.add_assoc]

end LeanRTL.Lib.Semantic.Accum
