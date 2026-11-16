import LeanRTL.Core.Semantics
/-!
# `eval_lookup_congr` — the `.lookup`-keyed `eval` congruence and its wire-fold lift

The whole-trace lift of a sequential design abstracts its register file to a `BitVec` tuple `s`
and re-packages that tuple as an `Env` (`specEnv s i`, registers bound to `s.k.toNat`, everything
else to the inputs `i`).  A register whose next-state cone references a **computed wire** needs the
abstract transition `specStep_k := eval reg_k.next (evalWires m.wires (specEnv s i))` — the wires
re-run over the abstract base.  Discharging the forward-simulation square then means proving

    eval reg.next (evalWires m.wires (cycleEnv r i regNames))          -- the step env `E`
      = eval reg.next (evalWires m.wires (specEnv (α r) i))            -- the abstract env

i.e. two `evalWires` folds evaluate the SAME cone equally.  `HierCorrect.eval_congr` cannot bridge
them: it demands *raw* env agreement `E₁ n = E₂ n`, but the step base holds a register's raw value
`r name` while the abstract base holds `(BitVec.ofNat wₖ (r name)).toNat = (r name) % 2^wₖ` — these
differ raw as soon as `r name ≥ 2^wₖ`.  They agree only at **`Env.lookup name wₖ`** (which re-applies
`BitVec.ofNat wₖ`, absorbing the mod).  Since `eval` reads an env ONLY through `.lookup`, the correct
congruence is keyed on `.lookup`-agreement, not raw agreement.

This file supplies that missing congruence:

* `eval_lookup_congr` — two envs agreeing at `.lookup` on every `(name, width)` an expression reads
  (`Expr.varsW`) evaluate it equally.  It is width-*precise*: a register is only read at ITS declared
  width, where the `.toNat` round-trip closes; an all-width `∀ w'` hypothesis is genuinely FALSE
  between `cycleEnv` and `specEnv` (they disagree above the register width), so width-precision is
  not a cosmetic choice but what makes the lemma usable at all.
* `evalWires_lookup_congr` — that agreement is *preserved through the wire fold*: given base
  agreement on the wire cones' reads and on a target pair-list `L`, the folded envs agree at `.lookup`
  on `L`.  (A wire, once bound, holds the SAME raw `Nat` on both sides — the cones evaluate equally —
  so wire names agree at every width; base names inherit their per-width agreement.)  Proved by
  `List.foldl` induction reusing `eval_lookup_congr`.
* `evalWires_eval_congr` / `evalWires_specEnv_round` — the two composed together: the fold-vs-fold
  cone equality (the latter also absorbing the `BitVec.ofNat _ (·.toNat)` round-trip on the step
  side, i.e. the exact per-register bridge shape).  This replaces the bespoke 30-line `simp only`
  macro that every computed-wire design (`mac_tx_ctrl`, `direct_map_cache`, `load_store_unit`, …)
  re-derived by hand.
-/

namespace LeanRTL

/-- The `(name, width)` pairs an expression reads — the width-carrying refinement of `Expr.vars`.
    A `.var n w` leaf contributes exactly `(n, w)`; every other node unions its children (mirroring
    `Expr.vars`).  This is what `eval_lookup_congr` quantifies over: `eval` reads each name at the
    width its AST node declares, so agreement is needed only at those precise pairs. -/
def Expr.varsW : {w : Nat} → Expr w → List (String × Nat)
  | _, .const _      => []
  | _, .var n w      => [(n, w)]
  | _, .not a        => a.varsW
  | _, .and a b      => a.varsW ++ b.varsW
  | _, .or a b       => a.varsW ++ b.varsW
  | _, .xor a b      => a.varsW ++ b.varsW
  | _, .add a b      => a.varsW ++ b.varsW
  | _, .sub a b      => a.varsW ++ b.varsW
  | _, .mul a b      => a.varsW ++ b.varsW
  | _, .shl a b      => a.varsW ++ b.varsW
  | _, .shr a b      => a.varsW ++ b.varsW
  | _, .sshr a b     => a.varsW ++ b.varsW
  | _, .udiv a b     => a.varsW ++ b.varsW
  | _, .umod a b     => a.varsW ++ b.varsW
  | _, .eq a b       => a.varsW ++ b.varsW
  | _, .ult a b      => a.varsW ++ b.varsW
  | _, .slt a b      => a.varsW ++ b.varsW
  | _, .mux s a b    => s.varsW ++ a.varsW ++ b.varsW
  | _, .concat a b   => a.varsW ++ b.varsW
  | _, .zext _ a     => a.varsW
  | _, .sext _ a     => a.varsW
  | _, .extract _ a  => a.varsW
  | _, .slice _ _ a  => a.varsW

/-- **The `.lookup`-keyed `eval` congruence.**  Two environments that agree at `Env.lookup` on every
    `(name, width)` pair the expression reads evaluate it to the same bit-vector.  The leaf case is
    exactly where `.lookup` absorbs the width-mod discrepancy between a raw and a mod-reduced env. -/
theorem eval_lookup_congr {w : Nat} (e : Expr w) (E₁ E₂ : Env)
    (h : ∀ nw ∈ e.varsW, E₁.lookup nw.1 nw.2 = E₂.lookup nw.1 nw.2) :
    eval e E₁ = eval e E₂ := by
  induction e with
  | const v => rfl
  | var n w => simp only [eval]; exact h (n, w) (List.mem_singleton.mpr rfl)
  | not a ih => simp only [eval]; rw [ih h]
  | zext k a ih => simp only [eval]; rw [ih h]
  | sext k a ih => simp only [eval]; rw [ih h]
  | extract i a ih => simp only [eval]; rw [ih h]
  | slice lo len a ih => simp only [eval]; rw [ih h]
  | mux s a b ihs iha ihb =>
      simp only [eval]
      rw [ihs (fun nw hnw => h nw (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hnw))))),
          iha (fun nw hnw => h nw (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hnw))))),
          ihb (fun nw hnw => h nw (List.mem_append.mpr (Or.inr hnw)))]
  | and a b iha ihb | or a b iha ihb | xor a b iha ihb | add a b iha ihb | sub a b iha ihb
  | mul a b iha ihb | shl a b iha ihb | shr a b iha ihb | sshr a b iha ihb | udiv a b iha ihb
  | umod a b iha ihb | eq a b iha ihb | ult a b iha ihb | slt a b iha ihb | concat a b iha ihb =>
      simp only [eval]
      rw [iha (fun nw hnw => h nw (List.mem_append.mpr (Or.inl hnw))),
          ihb (fun nw hnw => h nw (List.mem_append.mpr (Or.inr hnw)))]

/-- `evalWires` on a cons: bind the head wire against the incoming base, then fold the rest.  `rfl`
    (definitional `List.foldl` on cons). -/
theorem evalWires_cons (wr : Wire) (rest : List Wire) (B : Env) :
    evalWires (wr :: rest) B
      = evalWires rest (fun n => if n = wr.name then (eval wr.expr B).toNat else B n) := rfl

/-- **The wire fold preserves `.lookup`-agreement.**  If `B₁`, `B₂` agree at `Env.lookup` on every
    pair read by any wire cone (`hcones`) and on a target pair-list `L` (`hL`), then the wire-extended
    envs `evalWires wires B₁`, `evalWires wires B₂` agree at `Env.lookup` on `L`.  Proved by
    `List.foldl` induction reusing `eval_lookup_congr` (a wire's bound value is the SAME raw `Nat` on
    both sides, so it agrees at every width; base names keep their per-width agreement). -/
theorem evalWires_lookup_congr : ∀ (wires : List Wire) (B₁ B₂ : Env),
    (∀ wr ∈ wires, ∀ nw ∈ wr.expr.varsW, B₁.lookup nw.1 nw.2 = B₂.lookup nw.1 nw.2) →
    ∀ (L : List (String × Nat)),
    (∀ nw ∈ L, B₁.lookup nw.1 nw.2 = B₂.lookup nw.1 nw.2) →
    ∀ nw ∈ L, (evalWires wires B₁).lookup nw.1 nw.2 = (evalWires wires B₂).lookup nw.1 nw.2 := by
  intro wires
  induction wires with
  | nil => intro B₁ B₂ _ L hL nw hnw; exact hL nw hnw
  | cons wr rest ih =>
      intro B₁ B₂ hcones L hL nw hnw
      rw [evalWires_cons, evalWires_cons]
      have hwr : eval wr.expr B₁ = eval wr.expr B₂ :=
        eval_lookup_congr wr.expr B₁ B₂ (hcones wr (List.mem_cons_self ..))
      have hstep : ∀ (m : String) (w'' : Nat), B₁.lookup m w'' = B₂.lookup m w'' →
          Env.lookup (fun n => if n = wr.name then (eval wr.expr B₁).toNat else B₁ n) m w''
            = Env.lookup (fun n => if n = wr.name then (eval wr.expr B₂).toNat else B₂ n) m w'' := by
        intro m w'' hm
        simp only [Env.lookup]
        by_cases hmw : m = wr.name
        · rw [if_pos hmw, if_pos hmw, hwr]
        · rw [if_neg hmw, if_neg hmw]; exact hm
      exact ih (fun n => if n = wr.name then (eval wr.expr B₁).toNat else B₁ n)
               (fun n => if n = wr.name then (eval wr.expr B₂).toNat else B₂ n)
               (fun wr' hwr' nw' hnw' =>
                  hstep nw'.1 nw'.2 (hcones wr' (List.mem_cons_of_mem wr hwr') nw' hnw'))
               L (fun nw' hnw' => hstep nw'.1 nw'.2 (hL nw' hnw')) nw hnw

/-- **The fold-vs-fold cone congruence** (the payoff combinator).  Given base agreement at `.lookup`
    on the wire cones' reads and on the target expression's reads, evaluating `e` under the two
    wire-extended envs is equal — `eval_lookup_congr` composed through `evalWires_lookup_congr`. -/
theorem evalWires_eval_congr (wires : List Wire) {w : Nat} (e : Expr w) (B₁ B₂ : Env)
    (hcones : ∀ wr ∈ wires, ∀ nw ∈ wr.expr.varsW, B₁.lookup nw.1 nw.2 = B₂.lookup nw.1 nw.2)
    (htgt : ∀ nw ∈ e.varsW, B₁.lookup nw.1 nw.2 = B₂.lookup nw.1 nw.2) :
    eval e (evalWires wires B₁) = eval e (evalWires wires B₂) :=
  eval_lookup_congr e (evalWires wires B₁) (evalWires wires B₂)
    (evalWires_lookup_congr wires B₁ B₂ hcones e.varsW htgt)

/-- **The per-register bridge shape.**  `evalWires_eval_congr` with the step side's
    `BitVec.ofNat w (·.toNat)` round-trip pre-absorbed and the wire-cone hypothesis flattened to a
    single `flatMap` pair-list (so a caller discharges it with one membership check).  This is exactly
    the goal a computed-wire design's `sα_k` faces after `show BitVec.ofNat w ((eval reg.next E).toNat)
    = eval reg.next (evalWires m.wires (specEnv (α r) i))`. -/
theorem evalWires_specEnv_round (wires : List Wire) {w : Nat} (e : Expr w) (B₁ B₂ : Env)
    (hcones : ∀ nw ∈ wires.flatMap (fun wr => wr.expr.varsW),
        B₁.lookup nw.1 nw.2 = B₂.lookup nw.1 nw.2)
    (htgt : ∀ nw ∈ e.varsW, B₁.lookup nw.1 nw.2 = B₂.lookup nw.1 nw.2) :
    BitVec.ofNat w ((eval e (evalWires wires B₁)).toNat) = eval e (evalWires wires B₂) := by
  rw [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact evalWires_eval_congr wires e B₁ B₂
    (fun wr hwr nw hnw => hcones nw (List.mem_flatMap.mpr ⟨wr, hwr, hnw⟩)) htgt

end LeanRTL
