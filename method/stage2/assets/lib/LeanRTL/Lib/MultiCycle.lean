import LeanRTL.Core.Semantics
import LeanRTL.Core.CompilerCorrectSeq
/-!
# MultiCycle — a reusable *end-to-end* multi-cycle correctness framework

Per-cycle correctness (`next_correct` in the design files) proves that **one** clock edge performs
exactly the described next-state function.  That is a statement about a single `Module.step`.  This
file is the next proof-depth layer: **after `K` cycles the output equals a mathematical function of
the inputs**, obtained by *induction over cycles* rather than by hand-unrolling the loop per design.

The framework has three parts:

1. **A combinator** `iterate f K` — iterate a per-cycle state-transition `f : S → S` exactly `K`
   times.  Instantiated at `f = stepClosed m inp rst` it is the `K`-fold single-clock `Module.step`.

2. **Reusable induction-over-cycles lemmas** — design-agnostic (`S` arbitrary):
   * `invariant_iterate`  — an invariant preserved by every step survives `K` steps;
   * `iterate_indexed`    — a *step-indexed* invariant advanced one index per step holds at cycle `K`;
   * `loop_latch`         — **compute-then-latch**: if the step fixes every `done` state and preserves
                            an invariant that pins the answer once `done`, then reaching `done` at
                            *any* cycle `K` gives the spec (no need to know the exact completion cycle);
   * `loop_correct`       — **invariant-until-done**: an invariant preserved while `¬done`, with `done`
                            first true at cycle `K`, forces the spec at cycle `K`.
   A design supplies `f`, the invariant `I`, `done`, the spec, and a per-step (one-cycle) proof — the
   framework contributes the cycle induction, so no design re-rolls it.

3. **A connection to the *actual* simulated hardware** — `iterate (stepClosed m inp rst)` from the
   initial registers is *definitionally* the register trace `CompilerCorrectSeq.regTrace` under
   constant inputs (`iterate_stepClosed_eq_regTrace`), and `simulate_result_regTrace` transfers a
   register fact through the executable `Module.simulate` (the very simulator layer-7 co-simulation
   runs, via the audited `simulate_eq_simTrace`) to its emitted output stream.  So the multi-cycle
   theorem is about the hardware the harness simulates, not a separate paper model.
-/

namespace LeanRTL.MultiCycle

open LeanRTL

/-! ## 1. The iterate combinator (self-contained; no Mathlib `Function.iterate` notation) -/

/-- Iterate a per-cycle transition `f` exactly `K` times: `iterate f 0 = id`,
    `iterate f (K+1) s = iterate f K (f s)`. -/
def iterate {S : Type _} (f : S → S) : Nat → S → S
  | 0,     s => s
  | k + 1, s => iterate f k (f s)

@[simp] theorem iterate_zero {S} (f : S → S) (s : S) : iterate f 0 s = s := rfl

/-- Peel one step off the *front*: `iterate f (k+1) s = iterate f k (f s)` (definitional). -/
theorem iterate_succ_left {S} (f : S → S) (k : Nat) (s : S) :
    iterate f (k + 1) s = iterate f k (f s) := rfl

/-- Peel one step off the *back*: `iterate f (k+1) s = f (iterate f k s)`. -/
theorem iterate_succ_right {S} (f : S → S) (k : Nat) (s : S) :
    iterate f (k + 1) s = f (iterate f k s) := by
  induction k generalizing s with
  | zero => rfl
  | succ n ih =>
    show iterate f (n + 1) (f s) = f (iterate f (n + 1) s)
    rw [ih (f s)]; rfl

/-! ## 2. Reusable induction-over-cycles lemmas -/

/-- **Invariant preserved ⇒ preserved after `K` cycles.**  The simplest cycle induction: if `I`
    survives one step it survives `K` steps. -/
theorem invariant_iterate {S} (f : S → S) (I : S → Prop)
    (hstep : ∀ s, I s → I (f s)) :
    ∀ K s, I s → I (iterate f K s) := by
  intro K
  induction K with
  | zero => intro s hs; simpa using hs
  | succ n ih => intro s hs; rw [iterate_succ_left]; exact ih (f s) (hstep s hs)

/-- **Step-indexed invariant.**  If `I 0` holds at the start and each step advances the index of a
    step-indexed invariant `I : Nat → S → Prop`, then `I K` holds after `K` cycles.  This is the
    fixed-count induction schema (e.g. "after bit `k` the partial result is …").

    TEMPLATE — no current in-tree caller (the `loop_latch` companion covers the corpus so far).
    Kept as the fixed-count member of the cycle-induction family cited by the well-founded-termination
    skill and plan.v0.9's Evo-1; the symmetric partner of `loop_correct`. -/
theorem iterate_indexed {S} (f : S → S) (I : Nat → S → Prop) (s0 : S)
    (h0 : I 0 s0) (hstep : ∀ k s, I k s → I (k + 1) (f s)) :
    ∀ K, I K (iterate f K s0) := by
  intro K
  induction K with
  | zero => simpa using h0
  | succ n ih => rw [iterate_succ_right]; exact hstep n _ ih

/-- **Compute-then-latch schema.**  If every step preserves an invariant `I` that (a) pins the answer
    once `done`, and the computation *reaches* `done` at some cycle `K`, then the spec holds at cycle
    `K`.  No need to know the *exact* completion cycle — only that `done` is reached — because `I` is
    preserved on every cycle (including the idle/latched cycles after completion). -/
theorem loop_latch {S} (f : S → S) (I : S → Prop) (done spec : S → Prop) (s0 : S)
    (hinit : I s0) (hpres : ∀ s, I s → I (f s))
    (hspec : ∀ s, I s → done s → spec s)
    (K : Nat) (hK : done (iterate f K s0)) :
    spec (iterate f K s0) :=
  hspec _ (invariant_iterate f I hpres K s0 hinit) hK

/-- **Invariant-until-done schema** (the classic loop-invariant rule, over cycles).  Given a loop
    invariant `I` preserved *while `¬done`*, with `done` first true exactly at cycle `K`, the spec
    (implied by `I ∧ done`) holds at cycle `K`.

    TEMPLATE — no current in-tree caller (GcdIter uses the `loop_latch` variant, which does not need
    "`done` first true exactly at `K`").  Kept as the `¬done`-guarded member of the cycle-induction
    family cited by the well-founded-termination skill and plan.v0.9's Evo-1. -/
theorem loop_correct {S} (f : S → S) (I done spec : S → Prop) (s0 : S) (K : Nat)
    (hinit : I s0)
    (hpres : ∀ s, I s → ¬ done s → I (f s))
    (hnd : ∀ j, j < K → ¬ done (iterate f j s0))
    (hdone : done (iterate f K s0))
    (hspec : ∀ s, I s → done s → spec s) :
    spec (iterate f K s0) := by
  have hI : ∀ j, j ≤ K → I (iterate f j s0) := by
    intro j
    induction j with
    | zero => intro _; simpa using hinit
    | succ n ih =>
      intro hj
      rw [iterate_succ_right]
      exact hpres _ (ih (Nat.le_of_succ_le hj)) (hnd n (Nat.lt_of_succ_le hj))
  exact hspec _ (hI K (Nat.le_refl K)) hdone

/-! ## 3. Connecting the combinator to the actual `Module.simulate`

`stepClosed m inp rst` is the single-clock register update of a module under a *fixed* per-cycle
input `inp` and reset flag `rst` — the endofunction on the register environment that the combinator
iterates.  Under constant inputs it is exactly the register trace the executable simulator threads. -/

/-- The one-cycle register update of `m` under a fixed input environment `inp` and reset flag `rst`,
    as an endofunction on the register environment. -/
def stepClosed (m : Module) (inp : Env) (rst : Bool) : Env → Env :=
  fun rv => m.step rv inp rst

/-- **The combinator IS the hardware register trace.**  Iterating `stepClosed` from the initial
    registers equals `CompilerCorrectSeq.regTrace` driven by constant inputs — the register state the
    denotational (and, via `simulate_eq_simTrace`, the executable) simulator carries cycle by cycle. -/
theorem iterate_stepClosed_eq_regTrace (m : Module) (inp : Env) (rst : Bool) :
    ∀ K, iterate (stepClosed m inp rst) K m.initRegs
       = CompilerCorrectSeq.regTrace m (fun _ => inp) (fun _ => rst) K := by
  intro K
  induction K with
  | zero => rfl
  | succ n ih =>
    rw [iterate_succ_right, ih, CompilerCorrectSeq.regTrace_succ]
    rfl

end LeanRTL.MultiCycle
