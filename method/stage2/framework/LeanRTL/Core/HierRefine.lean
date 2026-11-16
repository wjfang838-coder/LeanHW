import LeanRTL.Core.HierSeqCorrect
import LeanRTL.Core.Refine
/-!
# `Parent.regTrace` — the whole-trace (L3/L4) refinement bridge for hierarchical `Parent`s

`HierSeqCorrect.lean` flattens a sequential `Parent` into a single register-shaped flat `Module`
(`flattenParentSeq p`) whose per-instance next-state / output is proved faithful to the child's own
`Module.step` / `Module.outputs?eval` (`flatNext_eq_childStep` / `flatOut_eq_childOut`).  Until now the
whole-*run* of a hierarchy had **no** trace theorem: the corpus lifted only sequential *child* modules
(`SimRefines <child> …`), and the `Parent`-level whole-trace was the recorded STRIKE-3 "Parent
whole-trace gap".

The key insight closing that gap is that **`flattenParentSeq p` IS a plain `Module`**, so
`CompilerCorrectSeq.regTrace (flattenParentSeq p)` already denotes the hierarchy's whole register
trace, and the existing `SimRefines`/`Refines` forward-simulation bridges (`LeanRTL/Refine.lean`)
apply to it verbatim.  The framework layer is therefore *thin*:

* `Parent.regTrace p inputs reset` — the parent's whole register trace, defined as the flat module's
  `regTrace`; with `@[simp]` `zero`/`succ` unfoldings (both `rfl` via the `Module` ones).
* `Parent.simRefines_trace` / `Parent.simRefines_observe` — specialise `SimRefines.trace` /
  `SimRefines.observe` to `flattenParentSeq p`, so a downstream lift proves an ordinary
  `SimRefines (flattenParentSeq p) α specStep s0 inv` and gets back the Parent whole-trace
  `α (Parent.regTrace p inputs (fun _=>false) t) = specTrace specStep s0 inputs t`.
* `Parent.refines_trace` / `Parent.refines_observe` — the L4 `Refines` analogues (arbitrary reset
  streams + real output-port observation).

## Honest scope of the delivered whole-trace

The delivered whole-trace is stated over the **flat `Module`** `flattenParentSeq p` — i.e. over the
register file keyed by the flattened names `"<inst>.<reg>"`, stepped by `(flattenParentSeq p).step`.
This is a *genuine* whole-trace: `flattenParentSeq p` is a real register-shaped `Module` that the
compiler lowers to the very same instance netlist (`HierSeqCorrect`), and its per-instance next-state
is pinned faithful to the child's `Module.step` by `flatNext_eq_childStep`.

Bridging the *flat* register step all the way to the **hierarchical** `Parent.nextFlat` /
`Parent.simulateSeq` state threading is the strongest possible form.  `flatNext_eq_childStep` supplies
exactly the per-register equation for that bridge, **but only for a wire-free child** (its `hw :
inst.child.wires = []` hypothesis).  Both proof-of-concept designs here (`sync_serial`'s `core` carries
`nrst`/`serial_out`; the equalizer's children carry large FIR/LMS cones) have wire-carrying children,
so that route does not apply to them; the flat-`Module` whole-trace is the honest delivered form for
those designs and is what `Parent.simRefines_trace` produces.  (When a hierarchy's children ARE
wire-free, `flatNext_eq_childStep` closes the extra step directly — left as the natural extension.)
-/

namespace LeanRTL
open LeanRTL.CompilerCorrectSeq LeanRTL.Refine

/-- **The whole register trace of a sequential `Parent`.**  A `Parent` flattens (`flattenParentSeq`)
    into a single register-shaped flat `Module`; its whole register trace is that flat module's
    `regTrace`.  Cycle 0 is the flattened init state; cycle `t+1` is one flat `Module.step`.  This is
    the object the `SimRefines`/`Refines` bridges view through `α`. -/
def Parent.regTrace (p : Parent) (inputs : Nat → Env) (reset : Nat → Bool) : Nat → Env :=
  CompilerCorrectSeq.regTrace (flattenParentSeq p) inputs reset

@[simp] theorem Parent.regTrace_zero (p : Parent) (inputs : Nat → Env) (reset : Nat → Bool) :
    p.regTrace inputs reset 0 = (flattenParentSeq p).initRegs := rfl

@[simp] theorem Parent.regTrace_succ (p : Parent) (inputs : Nat → Env) (reset : Nat → Bool) (t : Nat) :
    p.regTrace inputs reset (t + 1)
      = (flattenParentSeq p).step (p.regTrace inputs reset t) (inputs t) (reset t) := rfl

/-! ## L3 — specialise the reset-free `SimRefines` bridge to `flattenParentSeq p` -/

/-- **Parent whole-trace (L3).**  From an ordinary `SimRefines (flattenParentSeq p) α specStep s0 inv`
    — proved by lifting the children's per-register `*_correct` through the flattening — the parent's
    whole register trace viewed through `α` IS the abstract spec trace, every cycle, all input
    streams; the gluing invariant holds throughout.  This is `SimRefines.trace` at `flattenParentSeq
    p`, restated over `Parent.regTrace`. -/
theorem Parent.simRefines_trace {p : Parent} {S : Type _} {α : Env → S}
    {specStep : S → Env → S} {s0 : S} {inv : Env → Prop}
    (h : SimRefines (flattenParentSeq p) α specStep s0 inv) (inputs : Nat → Env) (t : Nat) :
    inv (p.regTrace inputs (fun _ => false) t) ∧
    α (p.regTrace inputs (fun _ => false) t) = specTrace specStep s0 inputs t :=
  h.trace inputs t

/-- The payoff equation alone (drop the invariant conjunct):
    `α (Parent.regTrace p inputs (fun _=>false) t) = specTrace specStep s0 inputs t`. -/
theorem Parent.simRefines_trace_α {p : Parent} {S : Type _} {α : Env → S}
    {specStep : S → Env → S} {s0 : S} {inv : Env → Prop}
    (h : SimRefines (flattenParentSeq p) α specStep s0 inv) (inputs : Nat → Env) (t : Nat) :
    α (p.regTrace inputs (fun _ => false) t) = specTrace specStep s0 inputs t :=
  (h.trace inputs t).2

/-- **Observable Parent whole-trace (L3).**  Any observation read off the abstract state matches at
    every cycle — `SimRefines.observe` at `flattenParentSeq p`. -/
theorem Parent.simRefines_observe {p : Parent} {S O : Type _} {α : Env → S}
    {specStep : S → Env → S} {s0 : S} {inv : Env → Prop}
    (h : SimRefines (flattenParentSeq p) α specStep s0 inv) (obs : S → O) (inputs : Nat → Env)
    (t : Nat) :
    obs (α (p.regTrace inputs (fun _ => false) t)) = obs (specTrace specStep s0 inputs t) :=
  h.observe obs inputs t

/-! ## L4 — specialise the full `Refines` bridge (reset streams + output observation) -/

/-- **Parent whole-trace (L4).**  From a full `Refines (flattenParentSeq p) α specStep specOut s0 inv`
    the parent's whole register trace viewed through `α` is the resetful abstract trace — every cycle,
    all legal input streams, ALL reset streams.  `Refines.trace` at `flattenParentSeq p`. -/
theorem Parent.refines_trace {p : Parent} {S : Type _} {α : Env → S}
    {specStep : S → Env → S} {specOut : S → Env → List (String × Nat)} {s0 : S} {inv : Env → Prop}
    (h : Refines (flattenParentSeq p) α specStep specOut s0 inv) (inputs : Nat → Env)
    (reset : Nat → Bool) (hleg : ∀ t, (flattenParentSeq p).LegalInputs (inputs t)) (t : Nat) :
    inv (p.regTrace inputs reset t) ∧
    α (p.regTrace inputs reset t) = specTraceR specStep s0 inputs reset t :=
  h.trace inputs reset hleg t

/-- **Observable Parent whole-trace (L4).**  The flattened parent's real output ports match the
    spec's outputs on the resetful abstract trace — `Refines.observe` at `flattenParentSeq p`. -/
theorem Parent.refines_observe {p : Parent} {S : Type _} {α : Env → S}
    {specStep : S → Env → S} {specOut : S → Env → List (String × Nat)} {s0 : S} {inv : Env → Prop}
    (h : Refines (flattenParentSeq p) α specStep specOut s0 inv) (inputs : Nat → Env)
    (reset : Nat → Bool) (hleg : ∀ t, (flattenParentSeq p).LegalInputs (inputs t)) (t : Nat) :
    (flattenParentSeq p).outputs?eval (p.regTrace inputs reset t) (inputs t)
      = specOut (specTraceR specStep s0 inputs reset t) (inputs t) :=
  h.observe inputs reset hleg t

end LeanRTL
