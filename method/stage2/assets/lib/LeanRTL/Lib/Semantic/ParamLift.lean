import LeanRTL.Lib.Lift
/-!
# `ParamLift` — parametric (∀N) whole-trace refinement: the **L3 ∀N** machinery (M34c)

The fixed-`Module` combinators in `Lib/Lift.lean` lift ONE concrete design to a whole-trace theorem
(`simRefines_single … : SimRefines m α specStep s0 inv`).  A *parametric* design is a whole family
`impl : Nat → Module` (the `Designs/Param/` convention), and a genuine parametric whole-trace result
must quantify the refinement over `N` — with the catch that **the abstraction `α` and its
state TYPE vary with `N`**: a register of width `f N` abstracts to `BitVec (f N)`, so `α N : Env →
BitVec (f N)` and the abstract-state type itself depends on `N`.  This is the "only remaining gap = L3 ∀N"
gap noted in `docs/plan/proof-levels.md`: `simRefines_single` takes a *concrete* width `w`, so it
cannot produce a ∀N theorem where the width is a function of `N`.

This file closes that gap for the **single-register parametric-width** design class:

| shape                                                        | combinator                     |
| ------------------------------------------------------------ | ------------------------------ |
| the ∀N obligation itself                                     | `ParamSimRefines`              |
| its whole-trace payoff (∀N ∀t), reusing `SimRefines.trace`   | `ParamSimRefines.trace`        |
| 1 reg, width `= f N`, ANY record (async/negedge/…), no wires | `paramSimRefines_single_rec`   |
| 1 reg, width `= f N`, default record, no wires               | `paramSimRefines_single`       |

**Scope (honest).**  The machinery covers a single register whose width is an arbitrary function of
`N` (`(reg N).width`), including non-default register records (async-reset — as in
`UniversalShiftReg` — negedge, `$aldff`, `clockNet`), reset-free/output-blind (the L3 target).  The
per-cycle obligations become ∀N-quantified; the `cycleEnv` projection lemmas
(`cycleEnv_reg`/`cycleEnv_input`) are already width-generic, so the combinator is a thin ∀N wrapper
over `simRefines_single_rec` — the real content is the *statement* (`S : Nat → Type`, `α : ∀ N, …`)
that the fixed combinators cannot even phrase.  Multi-register parametric families (tuple `α N`) and
the resetful/observed L4 `Refines` ∀N form are the documented next steps (§ Scope, bottom).
-/

namespace LeanRTL.Lib.Semantic.ParamLift
open LeanRTL LeanRTL.CompilerCorrectSeq LeanRTL.Refine LeanRTL.Designs.WholeDesign.Lift

/-! ## 1. The parametric obligation and its whole-trace payoff -/

/-- **Parametric forward simulation** — the ∀N lift of `SimRefines`.  A family of designs `impl N`,
    each carrying its own abstract-state type `S N`, abstraction `α N : Env → S N`, transition
    `specStep N`, initial state `s0 N`, and gluing invariant `inv N`, refines its spec at EVERY
    width `N`.  The state type `S N` and abstraction `α N` VARY with `N` — the fixed-`Module`
    combinators cannot express this (they fix a concrete `S`/width). -/
def ParamSimRefines (impl : Nat → Module) (S : Nat → Type _)
    (α : ∀ N, Env → S N) (specStep : ∀ N, S N → Env → S N) (s0 : ∀ N, S N)
    (inv : ∀ _ : Nat, Env → Prop) : Prop :=
  ∀ N, SimRefines (impl N) (α N) (specStep N) (s0 N) (inv N)

/-- **Parametric whole-trace theorem.**  Definitional reuse of `SimRefines.trace`: for every width
    `N` and every cycle `t`, the impl's register trace of `impl N` viewed through `α N` IS the
    abstract spec trace `specTrace (specStep N) (s0 N)`.  This is the L3 ∀N payoff — one theorem
    covering all widths and all time. -/
theorem ParamSimRefines.trace {impl : Nat → Module} {S : Nat → Type _} {α : ∀ N, Env → S N}
    {specStep : ∀ N, S N → Env → S N} {s0 : ∀ N, S N} {inv : ∀ _ : Nat, Env → Prop}
    (h : ParamSimRefines impl S α specStep s0 inv) (inputs : Nat → Env) (N t : Nat) :
    α N (regTrace (impl N) inputs (fun _ => false) t) = specTrace (specStep N) (s0 N) inputs t :=
  ((h N).trace inputs t).2

/-- The parametric invariant is preserved along the whole trace, at every width — the invariant half
    of `ParamSimRefines.trace` (handed out separately for callers needing the gluing invariant). -/
theorem ParamSimRefines.invariant {impl : Nat → Module} {S : Nat → Type _} {α : ∀ N, Env → S N}
    {specStep : ∀ N, S N → Env → S N} {s0 : ∀ N, S N} {inv : ∀ _ : Nat, Env → Prop}
    (h : ParamSimRefines impl S α specStep s0 inv) (inputs : Nat → Env) (N t : Nat) :
    inv N (regTrace (impl N) inputs (fun _ => false) t) :=
  ((h N).trace inputs t).1

/-! ## 2. The ∀N single-register combinator (the real work)

The crux the fixed combinators cannot do: the register WIDTH is a function of `N`.  `simRefines_single`
takes a *concrete* width `w`; `simRefines_single_rec` takes a *concrete* `Reg` (its width `reg.width`
is one fixed `Nat`).  Here the register is `reg N : Reg` — a **function of `N`** — so its width
`(reg N).width` varies, the abstract state type is `fun N => BitVec (reg N).width`, and the
abstraction is `fun N r => BitVec.ofNat (reg N).width (r (reg N).name)`.  The obligations
(`hshape`/`hstep`/`hinit`) become ∀N-quantified; each `N`-instance is discharged by the width-generic
`simRefines_single_rec`.  So the combinator is a thin ∀N wrapper — the friction was never in the
per-`N` proof (that library was already width-generic) but in phrasing the ∀N *statement* with a
`N`-dependent state type, which `ParamSimRefines` supplies. -/

/-- **The ∀N single-register lift, over the full `Reg` record** (async-reset / negedge / `$aldff` /
    `clockNet` all fine — the reset-free cycle reads a register through only `find?`+`eval reg.next`).
    For a family `impl N` whose sole register is `reg N` (width `(reg N).width` an ARBITRARY function
    of `N`) and that has no wires, forward-simulate the per-width abstraction
    `α N r = BitVec.ofNat (reg N).width (r (reg N).name)` against `specN N`, for EVERY `N`.  Callers
    supply the ∀N-quantified analogues of `simRefines_single_rec`'s obligations:

    * `hshape` : `∀ N, (impl N).regs = [reg N] ∧ (impl N).wires = []` — usually `fun _ => ⟨rfl, rfl⟩`;
    * `hstep`  : the design's `next_correct`, ∀N-quantified and re-aimed at `cycleEnv r i [(reg N).name]`;
    * `hinit`  : `∀ N, BitVec.ofNat (reg N).width ((impl N).initRegs (reg N).name) = s0 N`.

    Returns a `ParamSimRefines`, whose `.trace` is the L3 ∀N whole-trace theorem. -/
theorem paramSimRefines_single_rec (impl : Nat → Module) (reg : Nat → Reg)
    (specN : ∀ N, BitVec (reg N).width → Env → BitVec (reg N).width)
    (s0 : ∀ N, BitVec (reg N).width)
    (hshape : ∀ N, (impl N).regs = [reg N] ∧ (impl N).wires = [])
    (hstep : ∀ N (r i : Env),
        eval (reg N).next (cycleEnv r i [(reg N).name])
          = specN N (BitVec.ofNat (reg N).width (r (reg N).name)) i)
    (hinit : ∀ N, BitVec.ofNat (reg N).width ((impl N).initRegs (reg N).name) = s0 N) :
    ParamSimRefines impl (fun N => BitVec (reg N).width)
      (fun N r => BitVec.ofNat (reg N).width (r (reg N).name)) specN s0 (fun _ _ => True) :=
  fun N => simRefines_single_rec (impl N) (reg N) (specN N) (s0 N) (hshape N) (hstep N) (hinit N)

/-- **The ∀N single-register lift** (default `{name,width,next,init}` record; width `= f N`).  The
    width-uniform-family instance of `paramSimRefines_single_rec`: the register is named `rn`
    (constant across `N`) with width `f N`, next-state `rnNext N`, init `i0 N`.  The direct ∀N
    analogue of `simRefines_single`; use `_rec` when the register carries a non-default field
    (async-reset etc.). -/
theorem paramSimRefines_single (impl : Nat → Module) (rn : String) (f : Nat → Nat)
    (rnNext : ∀ N, Expr (f N)) (i0 : ∀ N, BitVec (f N))
    (specN : ∀ N, BitVec (f N) → Env → BitVec (f N)) (s0 : ∀ N, BitVec (f N))
    (hshape : ∀ N, (impl N).regs = [{ name := rn, width := f N, next := rnNext N, init := i0 N }]
                    ∧ (impl N).wires = [])
    (hstep : ∀ N (r i : Env),
        eval (rnNext N) (cycleEnv r i [rn]) = specN N (BitVec.ofNat (f N) (r rn)) i)
    (hinit : ∀ N, BitVec.ofNat (f N) ((impl N).initRegs rn) = s0 N) :
    ParamSimRefines impl (fun N => BitVec (f N))
      (fun N r => BitVec.ofNat (f N) (r rn)) specN s0 (fun _ _ => True) :=
  fun N => simRefines_single (impl N) rn (f N) (rnNext N) (i0 N) (specN N) (s0 N)
    (hshape N) (hstep N) (hinit N)

/-! ## Scope / next steps (honest boundary)

* **Covered.**  A single register whose width is any `f N` (`(reg N).width`), any register record,
  reset-free & output-blind (`SimRefines`, the L3 target) — the `UniversalShiftReg` class.
* **Not yet.**  (a) Multi-register parametric families need a tuple `α N` (`BitVec (f₁ N) × …`); the
  `simRefines_pair`/`simRefines_triple` shapes lift to ∀N the same way but each arity needs its own
  ∀N wrapper (future `paramSimRefines_pair` …).  (b) The resetful + observed L4 `Refines` ∀N form
  (a `ParamRefines` over `Refines`) is the analogous next rung.  (c) An L5 ∀N end-to-end
  (`gcd_top`-style) rides on the multi-cycle `StutterRefines` ∀N form.  All three reuse this file's
  pattern: state the `N`-dependent obligation as `∀ N, <fixed bridge> (… N)`, and discharge each
  `N`-instance with the (already width-generic) fixed combinator. -/

end LeanRTL.Lib.Semantic.ParamLift
