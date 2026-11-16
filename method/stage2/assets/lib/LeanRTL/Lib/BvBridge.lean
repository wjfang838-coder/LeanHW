import LeanRTL.Core.Semantics
/-!
# `BvBridge` — lemmas that un-stick `bv_decide` on env round-trips, signed compares, and Nat specs

`bv_decide` bit-blasts a goal by abstracting every term it does not understand into an *opaque*
bit-vector variable.  When a spec/impl equality feeds it a term outside its fragment it reports a
**"potentially spurious counterexample: abstracted the following unsupported expressions as opaque
variables: [ … ]"** and fails — even though the goal is true.  Across the blind-authoring corpus 67
designs independently hit the same four shapes.  This file names the fix for each.

## COOKBOOK — read the abstracted term in the counterexample, pick the move
1. `BitVec.ofNat w (r "n")` / `BitVec.ofNat w (x.toNat)` stays opaque, **width a LITERAL**
     → `rw [ofNat_toNat_id]`  (collapses `BitVec.ofNat w x.toNat = x`, the `α`/`Env.lookup` round-trip).
2. same shape but the **width is a COMPUTED SUM** (`1+(1+1)` from `concat`/`extract` chains):
     `ofNat_toNat_id` (and `ofNat_toNat`+`setWidth_eq`) will NOT fire — they need a literal width.
     → *technique, not a lemma*: **re-encode the cone at word level** (`shr`/`and`/`shl`/`or`/`xor`
       over the full literal-width word) so the round-trip collapses; OR `generalize hk :
       BitVec.ofNat _ (e "n") = k` each opaque sub-term to a fresh atom before `bv_decide`
       (also avoids `maxRecDepth` blow-ups on deep concat trees).
3. `x.toInt < y.toInt` abstracted (a `.slt` — its `eval` is an `Int` compare, OUTSIDE the fragment):
     → `rw [slt_to_ult_msb]`  (rewrites to `ult ⊕ msb`, all in-fragment; then `bv_decide`).
4. `BitVec.ofNat 1 (n % 2)` abstracted (a mod-2 residual on a 1-bit net):
     → `rw [ofNat_mod_two]`  (or just `bv_omega`/`omega`).
5. `BitVec.ofNat w (a.toNat + b.toNat)` abstracted (a `Nat`-arithmetic spec):
     → `rw [ofNat_add_toNat]`  (becomes `a.setWidth w + b.setWidth w`, a genuine BitVec add);
       fallback: `apply BitVec.eq_of_toNat_eq; simp only [BitVec.toNat_add, …]; omega` (carry `isLt`).
-/

namespace LeanRTL.BvBridge

open BitVec

/-! ## Class 1 — the `Env.lookup` / `α` round-trip (`BitVec.ofNat w (x.toNat)`) -/

/-- **Use when `bv_decide` abstracts `BitVec.ofNat w (x.toNat)` (or `BitVec.ofNat w (r "n")`) as an
opaque variable at a LITERAL width.**  This is the `Env.lookup`/whole-trace-`α` round-trip the
`Semantics` docstring promises: it collapses `BitVec.ofNat w x.toNat` back to `x` in one rewrite,
so the spec reduces to a plain `BitVec`-variable identity `bv_decide` can bit-blast.  (For a
*computed-sum* width — from `concat`/`extract` chains — this cannot fire; see cookbook item 2.) -/
theorem ofNat_toNat_id {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]

/-! ## Class 2 — signed less-than (`.slt`) is an `Int` compare outside the fragment -/

/-- **Use when `bv_decide` abstracts `x.toInt < y.toInt` as opaque** — the shape `eval` produces for
`.slt` (`if (eval a e).toInt < (eval b e).toInt then 1 else 0`).  The signed compare is an `Int`
inequality, outside `bv_decide`'s BitVec fragment.  This rewrites the `Int`-compare `if` into the
equivalent **unsigned-compare ⊕ sign-bit** form (`(x.msb != y.msb).xor (x.ult y)`), whose every
operation (`ult`, `msb`, `xor`, `!=`) IS in the fragment — `bv_decide` then closes it.  Works for
any branches `u v` (so it also fixes a `.mux` steered by a `.slt`). -/
theorem slt_to_ult_msb {w n : Nat} (x y : BitVec w) (u v : BitVec n) :
    (if x.toInt < y.toInt then u else v)
      = (if (x.msb != y.msb).xor (x.ult y) then u else v) := by
  have h : (x.msb != y.msb).xor (x.ult y) = decide (x.toInt < y.toInt) := by
    rw [← BitVec.slt_eq_ult, BitVec.slt_eq_decide]
  rw [h]
  by_cases hc : x.toInt < y.toInt <;> simp [hc]

/-! ## Class 3 — mod-2 residuals on a 1-bit net (`BitVec.ofNat 1 (n % 2)`) -/

/-- **Use when `bv_decide` abstracts `BitVec.ofNat 1 (n % 2)`** — a mod-2 residual left on a 1-bit
signal (e.g. a parity/LSB cone).  The outer `BitVec.ofNat 1` already truncates to one bit, so the
`% 2` is redundant; this discharges the equality (it is also provable by `bv_omega`/`omega`). -/
theorem ofNat_mod_two (n : Nat) : BitVec.ofNat 1 (n % 2) = BitVec.ofNat 1 n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, Nat.pow_one]
  omega

/-- General form of `ofNat_mod_two` at any width: a `% 2^w` inside `BitVec.ofNat w` is absorbed. -/
theorem ofNat_mod_two_pow (w n : Nat) : BitVec.ofNat w (n % 2 ^ w) = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat]
  exact Nat.mod_mod_of_dvd n (Nat.dvd_refl _)

/-! ## Class 4 — `Nat`-arithmetic specs (`BitVec.ofNat w (a.toNat + b.toNat)`) -/

/-- **Use when `bv_decide` abstracts `BitVec.ofNat w (a.toNat + b.toNat)` as opaque** — the shape a
`Nat`-level spec (`sum = ofNat 5 (x.toNat + y.toNat)` for an N→N+1 adder) hands the prover.  A
`BitVec.ofNat` wrapping a *`Nat` addition of `toNat`s* is not something `bv_decide` bit-blasts.
This rewrites it to a genuine **BitVec addition of width-`w` operands** (`a.setWidth w + b.setWidth
w`), which is in the fragment.  Holds for ALL `w` (no `w ≥ width` side-condition): both sides equal
`(a.toNat + b.toNat) % 2^w` by `Nat.add_mod`. -/
theorem ofNat_add_toNat {wa wb : Nat} (a : BitVec wa) (b : BitVec wb) (w : Nat) :
    BitVec.ofNat w (a.toNat + b.toNat) = a.setWidth w + b.setWidth w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_add, BitVec.toNat_setWidth]
  exact Nat.add_mod _ _ _

/-- Multiplication companion to `ofNat_add_toNat`: `BitVec.ofNat w (a.toNat * b.toNat)` becomes a
real width-`w` BitVec multiply.  Same `bv_decide` symptom (opaque `ofNat` of a `Nat` product); same
fix.  (`bv_decide` still bit-blasts the multiply — keep wide multiplies out of `bv_decide` goals; but
when the product must appear, this is its in-fragment normal form.) -/
theorem ofNat_mul_toNat {wa wb : Nat} (a : BitVec wa) (b : BitVec wb) (w : Nat) :
    BitVec.ofNat w (a.toNat * b.toNat) = a.setWidth w * b.setWidth w := by
  apply BitVec.eq_of_toNat_eq
  simp only [BitVec.toNat_ofNat, BitVec.toNat_mul, BitVec.toNat_setWidth]
  exact Nat.mul_mod _ _ _

/-! ## Demonstrations — shapes that FAILED `bv_decide` in the blind corpus, now closing

Each `example` is the exact opaque-term shape from a blind-authoring note, discharged by the bridge
lemma above (the `eval` form is unfolded first, mirroring what a real proof sees). -/

/-- Class 1 (float_multi round 2): the `α`/`Env.lookup` round-trip `BitVec.ofNat 8 (x.toNat)` that
`bv_decide` left opaque now collapses. -/
example (e : Env) :
    BitVec.ofNat 8 ((eval (.var "r" 8) e).toNat) = eval (.var "r" 8) e := by
  rw [ofNat_toNat_id]

/-- Class 2 (float_multi round 1 / Prob016 signed-compare cousin): the `.slt` `eval` form
(`if _.toInt < _.toInt then 1 else 0`) that was OUTSIDE `bv_decide`'s fragment now rewrites to the
in-fragment `ult ⊕ msb` shape. -/
example (e : Env) :
    eval (.slt (.var "a" 8) (.var "b" 8)) e
      = (if ((e.lookup "a" 8).msb != (e.lookup "b" 8).msb).xor
             ((e.lookup "a" 8).ult (e.lookup "b" 8)) then 1 else 0) := by
  -- `eval (.slt …)` is *definitionally* this `Int`-compare `if`; restate it (a `simp only [eval]`
  -- leaves `eval` un-reduced inside the `Decidable` instance, blocking the rewrite).
  show (if (e.lookup "a" 8).toInt < (e.lookup "b" 8).toInt then (1 : BitVec 1) else 0) = _
  rw [slt_to_ult_msb]

/-- Class 4 (Prob016_m2014_q4j): the 4→5-bit adder spec `BitVec.ofNat 5 (x.toNat + y.toNat)` that
`bv_decide` abstracted as opaque now equals the design's zero-extended BitVec add. -/
example (e : Env) :
    eval (.add (.zext 1 (.var "x" 4)) (.zext 1 (.var "y" 4))) e
      = BitVec.ofNat 5 ((e.lookup "x" 4).toNat + (e.lookup "y" 4).toNat) := by
  simp only [eval]
  rw [ofNat_add_toNat]

end LeanRTL.BvBridge
