import LeanRTL.Core.Semantics
import LeanRTL.Core.CompilerCorrectSeq
import LeanRTL.Core.Spec.Model
/-!
# Refinement — the bridge between the spec layer and the cycle-accurate impl (v0.7)

`spec` (an abstract, impl-agnostic model) and `impl` (a cycle-accurate `Module`) are two independent
layers.  This file provides the **refinement** that connects them:

* `α : Env → S` — the abstraction function (carries the *gluing invariant*; a design decision).
* `SimRefines m α specStep s0 inv` — the original lockstep, reset-free forward simulation (kept
  intact for existing proofs).
* `Refines m α specStep specOut s0 inv` — the **full obligation set** (v0.7): lockstep simulation
  PLUS (a) a **reset** obligation, so the trace theorem holds for *arbitrary* reset streams (the
  eval_v3 round showed 3/8 designs blocked on the reset ≡ false hardwiring); (b) a **boundary
  legality** hypothesis `Module.LegalInputs` (each input `< 2^width` — real pins cannot carry the
  out-of-range `Nat`s that made fifo16's `wr = 2` divergence spurious); (c) an
  **observation-respecting** obligation `obs` tying the impl's REAL output ports to the spec's
  outputs (anti-cheat gate #3: a vacuous α that ignores the outputs no longer "refines").
* `StutterRefines m α specStep s0 inv commit` — **non-lockstep** refinement: an abstract step fires
  only on cycles where `commit` holds; other cycles must not move `α` (warm-up/dead cycles, multi-
  cycle datapaths — the AXI/mul32 shapes lockstep cannot express).

The spec *terms* (`Queue`, `Mem`, …) live behind the structural wall in `LeanRTL/Spec/Model.lean`,
which imports nothing from the impl side.  This file is the ONE place allowed to import both layers.
-/

namespace LeanRTL

/-- Boundary legality: every input carries a value representable at its port width.
    Generated Verilog can never present anything else, so refinement obligations may
    (honestly) assume it — this kills the out-of-range-`Nat` divergence class. -/
def Module.LegalInputs (m : Module) (i : Env) : Prop :=
  ∀ p ∈ m.inputs, i p.name < 2 ^ p.width

end LeanRTL

namespace LeanRTL.Refine
open LeanRTL LeanRTL.CompilerCorrectSeq

/-! ## Lockstep, reset-free simulation (original v0.7 core — unchanged) -/

/-- The abstract spec trace: iterate `specStep` from `s0` under the boundary input stream. -/
def specTrace {S : Type _} (specStep : S → Env → S) (s0 : S) (inputs : Nat → Env) : Nat → S
  | 0     => s0
  | t + 1 => specStep (specTrace specStep s0 inputs t) (inputs t)

theorem specTrace_succ {S : Type _} (specStep : S → Env → S) (s0 : S) (inputs : Nat → Env) (t : Nat) :
    specTrace specStep s0 inputs (t + 1) = specStep (specTrace specStep s0 inputs t) (inputs t) := rfl

/-- **Forward simulation with a gluing invariant.**  `α` abstracts the impl register state to the spec
    state `S`; `inv` is the gluing invariant (the reachable-state condition `α` relies on); each
    non-reset impl step commutes with the abstract `specStep` on `inv`-states. -/
structure SimRefines (m : Module) {S : Type _} (α : Env → S) (specStep : S → Env → S) (s0 : S)
    (inv : Env → Prop) : Prop where
  init_inv : inv m.initRegs
  init_α   : α m.initRegs = s0
  step_inv : ∀ (r inputs : Env), inv r → inv (m.step r inputs false)
  step_α   : ∀ (r inputs : Env), inv r → α (m.step r inputs false) = specStep (α r) inputs

/-- **Refinement theorem (reusable bridge).**  Under `SimRefines`, the impl's register trace viewed
    through `α` IS the abstract spec trace — every cycle, all input streams.  The gluing invariant
    holds throughout. -/
theorem SimRefines.trace {m : Module} {S : Type _} {α : Env → S} {specStep s0 inv}
    (h : SimRefines m α specStep s0 inv) (inputs : Nat → Env) (t : Nat) :
    inv (regTrace m inputs (fun _ => false) t) ∧
    α (regTrace m inputs (fun _ => false) t) = specTrace specStep s0 inputs t := by
  induction t with
  | zero => rw [regTrace_zero]; exact ⟨h.init_inv, h.init_α⟩
  | succ n ih =>
    rw [regTrace_succ]
    exact ⟨h.step_inv _ _ ih.1, by rw [h.step_α _ _ ih.1, ih.2, specTrace_succ]⟩

/-- The observable form: any output read off the abstract state matches at every cycle. -/
theorem SimRefines.observe {m : Module} {S O : Type _} {α specStep s0 inv}
    (h : SimRefines m α specStep s0 inv) (obs : S → O) (inputs : Nat → Env) (t : Nat) :
    obs (α (regTrace m inputs (fun _ => false) t)) = obs (specTrace specStep s0 inputs t) := by
  rw [(h.trace inputs t).2]

/-! ## Resetful spec trace -/

/-- The abstract spec trace under an arbitrary reset stream: a reset cycle re-establishes `s0`
    (matching the impl's synchronous reset re-establishing `initRegs`). -/
def specTraceR {S : Type _} (specStep : S → Env → S) (s0 : S) (inputs : Nat → Env)
    (reset : Nat → Bool) : Nat → S
  | 0     => s0
  | t + 1 => cond (reset t) s0 (specStep (specTraceR specStep s0 inputs reset t) (inputs t))

@[simp] theorem specTraceR_zero {S : Type _} (specStep : S → Env → S) (s0 : S)
    (inputs : Nat → Env) (reset : Nat → Bool) :
    specTraceR specStep s0 inputs reset 0 = s0 := rfl

theorem specTraceR_succ {S : Type _} (specStep : S → Env → S) (s0 : S)
    (inputs : Nat → Env) (reset : Nat → Bool) (t : Nat) :
    specTraceR specStep s0 inputs reset (t + 1)
      = cond (reset t) s0 (specStep (specTraceR specStep s0 inputs reset t) (inputs t)) := rfl

/-- With reset never asserted, `specTraceR` is the plain `specTrace`. -/
theorem specTraceR_no_reset {S : Type _} (specStep : S → Env → S) (s0 : S)
    (inputs : Nat → Env) (t : Nat) :
    specTraceR specStep s0 inputs (fun _ => false) t = specTrace specStep s0 inputs t := by
  induction t with
  | zero => rfl
  | succ n ih => rw [specTraceR_succ, specTrace_succ, ih]; rfl

/-! ## `Refines` — the full v0.7 obligation set (reset + legality + observation) -/

/-- **Full refinement.**  Lockstep forward simulation with a gluing invariant, PLUS:

    * `reset_inv` / `reset_α` — a synchronous-reset step keeps the invariant and re-establishes
      the initial abstract state, so the trace theorem quantifies over ALL reset streams;
    * boundary legality — `step_α`/`obs` may assume `m.LegalInputs`, since generated hardware
      cannot present out-of-range input values;
    * `obs` — **observation-respecting α** (anti-cheat gate #3): the impl's real output ports
      denote exactly the spec's outputs on the abstracted state.  A refinement that gets the
      registers right but wires the outputs wrong does not hold. -/
structure Refines (m : Module) {S : Type _} (α : Env → S) (specStep : S → Env → S)
    (specOut : S → Env → List (String × Nat)) (s0 : S) (inv : Env → Prop) : Prop where
  init_inv  : inv m.initRegs
  init_α    : α m.initRegs = s0
  step_inv  : ∀ (r i : Env), inv r → m.LegalInputs i → inv (m.step r i false)
  step_α    : ∀ (r i : Env), inv r → m.LegalInputs i →
                α (m.step r i false) = specStep (α r) i
  reset_inv : ∀ (r i : Env), inv r → inv (m.step r i true)
  reset_α   : ∀ (r i : Env), inv r → α (m.step r i true) = s0
  obs       : ∀ (r i : Env), inv r → m.LegalInputs i →
                m.outputs?eval r i = specOut (α r) i

/-- **Trace theorem for `Refines`** — over arbitrary input AND reset streams (of legal inputs):
    the impl's register trace viewed through `α` is the resetful abstract trace, every cycle. -/
theorem Refines.trace {m : Module} {S : Type _} {α : Env → S} {specStep specOut s0 inv}
    (h : Refines m α specStep specOut s0 inv) (inputs : Nat → Env) (reset : Nat → Bool)
    (hleg : ∀ t, m.LegalInputs (inputs t)) (t : Nat) :
    inv (regTrace m inputs reset t) ∧
    α (regTrace m inputs reset t) = specTraceR specStep s0 inputs reset t := by
  induction t with
  | zero => rw [regTrace_zero]; exact ⟨h.init_inv, h.init_α⟩
  | succ n ih =>
    rw [regTrace_succ, specTraceR_succ]
    cases hr : reset n with
    | true  =>
      exact ⟨h.reset_inv _ _ ih.1, by rw [h.reset_α _ _ ih.1]; rfl⟩
    | false =>
      exact ⟨h.step_inv _ _ ih.1 (hleg n),
             by rw [h.step_α _ _ ih.1 (hleg n), ih.2]; rfl⟩

/-- **Observable correctness** for `Refines`: the impl's real output ports match the spec's
    outputs on the abstract trace — every cycle, all legal input streams, all reset streams. -/
theorem Refines.observe {m : Module} {S : Type _} {α : Env → S} {specStep specOut s0 inv}
    (h : Refines m α specStep specOut s0 inv) (inputs : Nat → Env) (reset : Nat → Bool)
    (hleg : ∀ t, m.LegalInputs (inputs t)) (t : Nat) :
    m.outputs?eval (regTrace m inputs reset t) (inputs t)
      = specOut (specTraceR specStep s0 inputs reset t) (inputs t) := by
  have ht := h.trace inputs reset hleg t
  rw [h.obs _ _ ht.1 (hleg t), ht.2]

/-- A `Refines` restricted to the reset-free stream is a `SimRefines` whose step obligations
    additionally carry legality (downgrade lemma, for reusing existing `SimRefines` corollaries
    on legal input streams). -/
theorem Refines.toSimTrace {m : Module} {S : Type _} {α : Env → S} {specStep specOut s0 inv}
    (h : Refines m α specStep specOut s0 inv) (inputs : Nat → Env)
    (hleg : ∀ t, m.LegalInputs (inputs t)) (t : Nat) :
    α (regTrace m inputs (fun _ => false) t) = specTrace specStep s0 inputs t := by
  rw [(h.trace inputs (fun _ => false) hleg t).2, specTraceR_no_reset]

/-! ## `StutterRefines` — non-lockstep refinement via a commit predicate

For multi-cycle datapaths (GCD, dividers), warm-up/dead cycles (AXI FSMs), and pipelines, one
abstract step corresponds to ONE distinguished impl cycle (`commit r i = true` — e.g. "handshake
fires", "done rises") and every other cycle must be invisible through `α`.  This is stuttering
forward simulation; the reusable payoff is `StutterRefines.trace` against `committedTrace`. -/

structure StutterRefines (m : Module) {S : Type _} (α : Env → S) (specStep : S → Env → S)
    (s0 : S) (inv : Env → Prop) (commit : Env → Env → Bool) : Prop where
  init_inv     : inv m.initRegs
  init_α       : α m.initRegs = s0
  step_inv     : ∀ (r i : Env), inv r → m.LegalInputs i → inv (m.step r i false)
  /-- On a commit cycle the impl performs exactly one abstract step. -/
  step_commit  : ∀ (r i : Env), inv r → m.LegalInputs i → commit r i = true →
                   α (m.step r i false) = specStep (α r) i
  /-- On a non-commit cycle the abstraction must not move (the stutter). -/
  step_stutter : ∀ (r i : Env), inv r → m.LegalInputs i → commit r i = false →
                   α (m.step r i false) = α r

/-- The spec state the impl should abstract to at cycle `t`: fold `specStep` over exactly the
    committed cycles of the (reset-free) run. -/
def committedTrace (m : Module) {S : Type _} (specStep : S → Env → S) (s0 : S)
    (commit : Env → Env → Bool) (inputs : Nat → Env) : Nat → S
  | 0     => s0
  | t + 1 =>
    cond (commit (regTrace m inputs (fun _ => false) t) (inputs t))
      (specStep (committedTrace m specStep s0 commit inputs t) (inputs t))
      (committedTrace m specStep s0 commit inputs t)

theorem committedTrace_succ (m : Module) {S : Type _} (specStep : S → Env → S) (s0 : S)
    (commit : Env → Env → Bool) (inputs : Nat → Env) (t : Nat) :
    committedTrace m specStep s0 commit inputs (t + 1)
      = cond (commit (regTrace m inputs (fun _ => false) t) (inputs t))
          (specStep (committedTrace m specStep s0 commit inputs t) (inputs t))
          (committedTrace m specStep s0 commit inputs t) := rfl

/-- **Stuttering trace theorem.**  Through `α`, the impl's register trace is the fold of
    `specStep` over exactly the committed cycles — uncommitted cycles are invisible. -/
theorem StutterRefines.trace {m : Module} {S : Type _} {α : Env → S} {specStep s0 inv commit}
    (h : StutterRefines m α specStep s0 inv commit) (inputs : Nat → Env)
    (hleg : ∀ t, m.LegalInputs (inputs t)) (t : Nat) :
    inv (regTrace m inputs (fun _ => false) t) ∧
    α (regTrace m inputs (fun _ => false) t) = committedTrace m specStep s0 commit inputs t := by
  induction t with
  | zero => rw [regTrace_zero]; exact ⟨h.init_inv, h.init_α⟩
  | succ n ih =>
    rw [regTrace_succ, committedTrace_succ]
    cases hc : commit (regTrace m inputs (fun _ => false) n) (inputs n) with
    | true  =>
      exact ⟨h.step_inv _ _ ih.1 (hleg n),
             by rw [h.step_commit _ _ ih.1 (hleg n) hc, ih.2]; rfl⟩
    | false =>
      exact ⟨h.step_inv _ _ ih.1 (hleg n),
             by rw [h.step_stutter _ _ ih.1 (hleg n) hc, ih.2]; rfl⟩

/-! ## Abstract models

The spec-layer models (`Queue`, `Mem`, …) live behind the structural wall in
`LeanRTL/Spec/Model.lean` — a file that imports NOTHING from the impl side, so specs written
in its vocabulary are impl-agnostic by construction (grep-checkable).  The old
`LeanRTL.Refine.Queue` moved there; the alias below keeps the type name available here. -/

abbrev Queue (w : Nat) := LeanRTL.Spec.Queue w

/-! ## Minimal demos — validate each bridge on a counter (these double as usage templates). -/
namespace Demo

/-- A 4-bit free-running counter `c' = c + 1`, sync reset to 0. -/
def cnt : Module :=
  { name := "ctr", inputs := [{name:="clk",width:=1},{name:="rst",width:=1}],
    outputs := [{name:="q",width:=4, expr := .var "c" 4}],
    regs := [{name:="c", width:=4, next := .add (.var "c" 4) (.const 1), init := 0}],
    clock := some "clk", reset := some "rst" }

/-- Abstract spec: a `BitVec 4` register that increments each step (no notion of gates). -/
def specStep (s : BitVec 4) (_ : Env) : BitVec 4 := s + 1

/-- α reads the impl's `c` register as the abstract counter value. -/
def α (env : Env) : BitVec 4 := BitVec.ofNat 4 (env "c")

/-- The counter refines the abstract increment-counter (original lockstep form). -/
theorem cnt_refines : SimRefines cnt α specStep 0 (fun _ => True) where
  init_inv := trivial
  init_α   := rfl
  step_inv := fun _ _ _ => trivial
  step_α   := by
    intro r inputs _
    show BitVec.ofNat 4 ((cnt.step r inputs false) "c") = α r + 1
    simp [cnt, Module.step, evalWires, eval, cycleEnv, Env.lookup, α]
    bv_omega

/-- Spec-side outputs: the abstract counter is directly visible on `q`. -/
def specOut (s : BitVec 4) (_ : Env) : List (String × Nat) := [("q", s.toNat)]

/-- The FULL v0.7 refinement: reset re-establishes `s0`, and the real output port `q`
    is observation-respecting.  Validates `Refines.trace`/`Refines.observe`. -/
theorem cnt_refines_full : Refines cnt α specStep specOut 0 (fun _ => True) where
  init_inv  := trivial
  init_α    := rfl
  step_inv  := fun _ _ _ _ => trivial
  step_α    := by
    intro r inputs _ _
    show BitVec.ofNat 4 ((cnt.step r inputs false) "c") = α r + 1
    simp [cnt, Module.step, evalWires, eval, cycleEnv, Env.lookup, α]
    bv_omega
  reset_inv := fun _ _ _ => trivial
  reset_α   := by
    intro r inputs _
    show BitVec.ofNat 4 ((cnt.step r inputs true) "c") = 0
    rfl
  obs       := by
    intro r inputs _ _
    show cnt.outputs?eval r inputs = [("q", (α r).toNat)]
    simp [cnt, Module.outputs?eval, evalWires, cycleEnv, eval, Env.lookup, α]

/-- An enabled counter: increments only when `en` is high — one abstract step per
    enabled cycle, a stutter otherwise. -/
def encnt : Module :=
  { name := "enctr", inputs := [{name:="clk",width:=1},{name:="en",width:=1}],
    outputs := [{name:="q",width:=4, expr := .var "c" 4}],
    regs := [{name:="c", width:=4,
              next := .mux (.var "en" 1) (.add (.var "c" 4) (.const 1)) (.var "c" 4),
              init := 0}],
    clock := some "clk" }

/-- Commit = the enable bit is set this cycle (decoded exactly as the impl's 1-bit port). -/
def commit (_r i : Env) : Bool := decide (BitVec.ofNat 1 (i "en") = 1)

/-- The enabled counter stutter-refines the increment counter: `α` moves by `specStep`
    exactly on enabled cycles and is frozen otherwise.  Validates `StutterRefines.trace`. -/
theorem encnt_stutter_refines :
    StutterRefines encnt α specStep 0 (fun _ => True) commit where
  init_inv := trivial
  init_α   := rfl
  step_inv := fun _ _ _ _ => trivial
  step_commit := by
    intro r i _ _ hc
    simp only [commit, decide_eq_true_eq] at hc
    show BitVec.ofNat 4 ((encnt.step r i false) "c") = α r + 1
    simp [encnt, Module.step, evalWires, eval, cycleEnv, Env.lookup, α, hc]
    bv_omega
  step_stutter := by
    intro r i _ _ hc
    simp only [commit, decide_eq_false_iff_not] at hc
    show BitVec.ofNat 4 ((encnt.step r i false) "c") = α r
    simp [encnt, Module.step, evalWires, eval, cycleEnv, Env.lookup, α]
    exact hc

end Demo
end LeanRTL.Refine
