import LeanRTL.Core.CompilerCorrect
/-!
# Compiler determinism (the ∀σ direction of compiler correctness)

`CompilerCorrect.lean` proves the *existence* direction (`sound` / `compile_correct`): for every
combinational `Expr e` there EXISTS a net valuation σ under which every emitted RTLIL cell holds
and the output bus denotes `eval e`.  That leaves a trust hole: nothing yet says the netlist
*forces* that value.  This file closes it with the ∀σ direction:

> **`compile_deterministic`** — for EVERY net valuation σ that (a) satisfies every cell in the
> compiled state (`ConsistentCells`) and (b) reproduces the denotational environment on the
> bound signal buses (`CEnvOK`), the compiled output bus denotes exactly `eval e`.

Together with `compile_correct` this pins the compiled netlist's behaviour completely: the set of
consistent valuations is non-empty, and *all* of them agree that the output is `eval e`
(`compile_correct_unique`).

The proof is a structural induction mirroring `sound`, but is *simpler* in one crucial way: σ is
fixed once for the whole netlist, so no `setRange` σ-extension, no frame lemmas, and no
freshness / single-driver invariants are needed.  A single σ satisfying *all* cells at once means
each cell's Y-equation can be chained functionally through the sub-expression IHs.  The only new
ingredient is `compileExpr_cells_sub`: compilation only ever *prepends* cells, so consistency of
the final cell list restricts to consistency of every intermediate cell list.
-/
namespace LeanRTL.CompilerDeterministic
open LeanRTL LeanRTL.Backend LeanRTL.BackendSem LeanRTL.CompilerCorrect

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Cells are only ever prepended -/

/-- `compileExpr` never removes cells: every cell present before compilation is still present
    after.  (Compilation conses new cells onto `s.cells`.) -/
theorem compileExpr_cells_sub {w : Nat} (e : Expr w) :
    ∀ (s : CState), ∀ c ∈ s.cells, c ∈ ((compileExpr e).run s).2.cells := by
  induction e with
  | const v => intro s c hc; exact hc
  | var n w =>
    intro s c hc
    cases h : s.env.lookup n with
    | some bus => rw [compileExpr_var_some h]; exact hc
    | none =>
      have hcells : ((compileExpr (.var n w)).run s).2.cells = s.cells := by
        simp [compileExpr, h]
      rw [hcells]; exact hc
  | not a iha =>
    intro s c hc
    rw [compileExpr_not_cells]
    exact List.mem_cons_of_mem _ (iha s c hc)
  | and a b iha ihb =>
    intro s c hc
    rw [compileExpr_and]; simp only [run_bind, emitBin_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | or a b iha ihb =>
    intro s c hc
    rw [compileExpr_or]; simp only [run_bind, emitBin_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | xor a b iha ihb =>
    intro s c hc
    rw [compileExpr_xor]; simp only [run_bind, emitBin_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | add a b iha ihb =>
    intro s c hc
    rw [compileExpr_add]; simp only [run_bind, emitBin_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | sub a b iha ihb =>
    intro s c hc
    rw [compileExpr_sub]; simp only [run_bind, emitBin_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | mul a b iha ihb =>
    intro s c hc
    rw [compileExpr_mul]; simp only [run_bind, emitBin_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | udiv a b iha ihb =>
    intro s c hc
    rw [compileExpr_udiv]; simp only [run_bind, emitBin_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | umod a b iha ihb =>
    intro s c hc
    rw [compileExpr_umod]; simp only [run_bind, emitBin_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | eq a b iha ihb =>
    intro s c hc
    rw [compileExpr_eq]; simp only [run_bind, emitCmp_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | ult a b iha ihb =>
    intro s c hc
    rw [compileExpr_ult]; simp only [run_bind, emitCmp_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | slt a b iha ihb =>
    intro s c hc
    rw [compileExpr_slt]; simp only [run_bind, emitCmpS_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | shl a b iha ihb =>
    intro s c hc
    rw [compileExpr_shl]; simp only [run_bind, emitShift_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | shr a b iha ihb =>
    intro s c hc
    rw [compileExpr_shr]; simp only [run_bind, emitShift_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | sshr a b iha ihb =>
    intro s c hc
    rw [compileExpr_sshr]; simp only [run_bind, emitShift_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha s c hc))
  | mux sg a b ihs iha ihb =>
    intro s c hc
    rw [compileExpr_mux_cells]
    exact List.mem_cons_of_mem _ (ihb _ c (iha _ c (ihs s c hc)))
  | concat ea eb ihea iheb =>
    intro s c hc
    rw [compileExpr_concat]; simp only [run_bind, run_pure]
    exact iheb _ c (ihea s c hc)
  | zext k a iha =>
    intro s c hc
    rw [compileExpr_zext]; simp only [run_bind, run_pure]
    exact iha s c hc
  | sext k a iha =>
    intro s c hc
    rw [compileExpr_sext]; simp only [run_bind, run_pure]
    exact iha s c hc
  | extract idx a iha =>
    intro s c hc
    rw [compileExpr_extract]; simp only [run_bind, run_pure]
    exact iha s c hc
  | slice lo len a iha =>
    intro s c hc
    rw [compileExpr_slice]; simp only [run_bind, run_pure]
    exact iha s c hc

/-! ## Per-shape forcing helpers

Each helper packages the common reasoning for one cell-emitting compilation shape:
restrict consistency to the operand runs, invoke the IHs (with the *same* σ — no σ-surgery),
then read the head cell's equation.  The `hext` argument is the per-cell "uniqueness projection":
the definitional unfolding of `cellHolds` at the concrete cell (supplied as `fun h => h` at each
use site, exactly like the `show`-based unfoldings in `sound`). -/

/-- Forcing for the eight `emitBin`-based operators (`$and/$or/$xor/$add/$sub/$mul/$div/$mod`). -/
private theorem binForce {w : Nat} {a b : Expr w} {env : Env} {s : CState} {σ : Nat → Bool}
    (op : {n : Nat} → BitVec n → BitVec n → BitVec n) (ty : String)
    (iha : ∀ (s' : CState) (σ' : Nat → Bool), WidthOK s'.env a → CEnvOK σ' s'.env env →
        ConsistentCells σ' ((compileExpr a).run s').2.cells →
        busDen σ' w ((compileExpr a).run s').1 = eval a env)
    (ihb : ∀ (s' : CState) (σ' : Nat → Bool), WidthOK s'.env b → CEnvOK σ' s'.env env →
        ConsistentCells σ' ((compileExpr b).run s').2.cells →
        busDen σ' w ((compileExpr b).run s').1 = eval b env)
    (hwa : WidthOK s.env a) (hwb : WidthOK s.env b) (hmem : CEnvOK σ s.env env)
    (hcons : ConsistentCells σ
      (binCell ((compileExpr b).run ((compileExpr a).run s).2).2 w ty
          ((compileExpr a).run s).1 ((compileExpr b).run ((compileExpr a).run s).2).1
        :: ((compileExpr b).run ((compileExpr a).run s).2).2.cells))
    (hext : cellHolds σ (binCell ((compileExpr b).run ((compileExpr a).run s).2).2 w ty
          ((compileExpr a).run s).1 ((compileExpr b).run ((compileExpr a).run s).2).1) →
        busDen σ (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w).length
            (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w)
          = op (busDen σ (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w).length
                  ((compileExpr a).run s).1)
               (busDen σ (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w).length
                  ((compileExpr b).run ((compileExpr a).run s).2).1)) :
    busDen σ w (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w)
      = op (eval a env) (eval b env) := by
  have henva : ((compileExpr a).run s).2.env = s.env := compileExpr_env a s
  obtain ⟨hcell, hconsB⟩ := List.forall_mem_cons.1 hcons
  have hconsA : ConsistentCells σ ((compileExpr a).run s).2.cells :=
    fun c hc => hconsB c (compileExpr_cells_sub b _ c hc)
  have vala : busDen σ w ((compileExpr a).run s).1 = eval a env := iha s σ hwa hmem hconsA
  have valb : busDen σ w ((compileExpr b).run ((compileExpr a).run s).2).1 = eval b env :=
    ihb _ σ (by rw [henva]; exact hwb) (by rw [henva]; exact hmem) hconsB
  have hY := hext hcell
  have hflen : (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w).length = w := by
    simp [freshBus]
  rw [hflen] at hY
  rw [hY, vala, valb]

/-- Forcing for the comparison operators (`$eq`, unsigned/signed `$lt`), emitted by
    `emitCmp`/`emitCmpSigned` with a 1-bit result. -/
private theorem cmpForce {w : Nat} {a b : Expr w} {env : Env} {s : CState} {σ : Nat → Bool}
    (op : {n : Nat} → BitVec n → BitVec n → BitVec 1) (ty : String) (sgn : Nat)
    (iha : ∀ (s' : CState) (σ' : Nat → Bool), WidthOK s'.env a → CEnvOK σ' s'.env env →
        ConsistentCells σ' ((compileExpr a).run s').2.cells →
        busDen σ' w ((compileExpr a).run s').1 = eval a env)
    (ihb : ∀ (s' : CState) (σ' : Nat → Bool), WidthOK s'.env b → CEnvOK σ' s'.env env →
        ConsistentCells σ' ((compileExpr b).run s').2.cells →
        busDen σ' w ((compileExpr b).run s').1 = eval b env)
    (hwa : WidthOK s.env a) (hwb : WidthOK s.env b) (hmem : CEnvOK σ s.env env)
    (hcons : ConsistentCells σ
      (cmpCell ((compileExpr b).run ((compileExpr a).run s).2).2 w ty sgn
          ((compileExpr a).run s).1 ((compileExpr b).run ((compileExpr a).run s).2).1
        :: ((compileExpr b).run ((compileExpr a).run s).2).2.cells))
    (hext : cellHolds σ (cmpCell ((compileExpr b).run ((compileExpr a).run s).2).2 w ty sgn
          ((compileExpr a).run s).1 ((compileExpr b).run ((compileExpr a).run s).2).1) →
        busDen σ 1 (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 1)
          = op (busDen σ ((compileExpr a).run s).1.length ((compileExpr a).run s).1)
               (busDen σ ((compileExpr a).run s).1.length
                  ((compileExpr b).run ((compileExpr a).run s).2).1)) :
    busDen σ 1 (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 1)
      = op (eval a env) (eval b env) := by
  have henva : ((compileExpr a).run s).2.env = s.env := compileExpr_env a s
  obtain ⟨hcell, hconsB⟩ := List.forall_mem_cons.1 hcons
  have hconsA : ConsistentCells σ ((compileExpr a).run s).2.cells :=
    fun c hc => hconsB c (compileExpr_cells_sub b _ c hc)
  have vala : busDen σ w ((compileExpr a).run s).1 = eval a env := iha s σ hwa hmem hconsA
  have valb : busDen σ w ((compileExpr b).run ((compileExpr a).run s).2).1 = eval b env :=
    ihb _ σ (by rw [henva]; exact hwb) (by rw [henva]; exact hmem) hconsB
  have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a (supp_all a) s hwa
  have hY := hext hcell
  rw [hlenA] at hY
  rw [hY, vala, valb]

/-- Forcing for the variable-shift operators (`$shl/$shr/$sshr`), whose shift count is the
    nat value of the (width-`k`) B bus. -/
private theorem shiftForce {w k : Nat} {a : Expr w} {b : Expr k} {env : Env} {s : CState}
    {σ : Nat → Bool}
    (op : {n : Nat} → BitVec n → Nat → BitVec n) (ty : String) (aSigned : Nat)
    (iha : ∀ (s' : CState) (σ' : Nat → Bool), WidthOK s'.env a → CEnvOK σ' s'.env env →
        ConsistentCells σ' ((compileExpr a).run s').2.cells →
        busDen σ' w ((compileExpr a).run s').1 = eval a env)
    (ihb : ∀ (s' : CState) (σ' : Nat → Bool), WidthOK s'.env b → CEnvOK σ' s'.env env →
        ConsistentCells σ' ((compileExpr b).run s').2.cells →
        busDen σ' k ((compileExpr b).run s').1 = eval b env)
    (hwa : WidthOK s.env a) (hwb : WidthOK s.env b) (hmem : CEnvOK σ s.env env)
    (hcons : ConsistentCells σ
      (shiftCell ((compileExpr b).run ((compileExpr a).run s).2).2 aSigned w k ty
          ((compileExpr a).run s).1 ((compileExpr b).run ((compileExpr a).run s).2).1
        :: ((compileExpr b).run ((compileExpr a).run s).2).2.cells))
    (hext : cellHolds σ (shiftCell ((compileExpr b).run ((compileExpr a).run s).2).2 aSigned w k ty
          ((compileExpr a).run s).1 ((compileExpr b).run ((compileExpr a).run s).2).1) →
        busDen σ (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w).length
            (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w)
          = op (busDen σ (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w).length
                  ((compileExpr a).run s).1)
               (busValNat σ ((compileExpr b).run ((compileExpr a).run s).2).1)) :
    busDen σ w (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w)
      = op (eval a env) (eval b env).toNat := by
  have henva : ((compileExpr a).run s).2.env = s.env := compileExpr_env a s
  obtain ⟨hcell, hconsB⟩ := List.forall_mem_cons.1 hcons
  have hconsA : ConsistentCells σ ((compileExpr a).run s).2.cells :=
    fun c hc => hconsB c (compileExpr_cells_sub b _ c hc)
  have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [henva]; exact hwb
  have vala : busDen σ w ((compileExpr a).run s).1 = eval a env := iha s σ hwa hmem hconsA
  have valb : busDen σ k ((compileExpr b).run ((compileExpr a).run s).2).1 = eval b env :=
    ihb _ σ hwb' (by rw [henva]; exact hmem) hconsB
  have hlenB : ((compileExpr b).run ((compileExpr a).run s).2).1.length = k :=
    compileExpr_len b (supp_all b) _ hwb'
  have hBv : busValNat σ ((compileExpr b).run ((compileExpr a).run s).2).1
      = (eval b env).toNat := by
    rw [← valb]; exact (busDen_toNat σ _ k hlenB).symm
  have hY := hext hcell
  have hflen : (freshBus ((compileExpr b).run ((compileExpr a).run s).2).2 w).length = w := by
    simp [freshBus]
  rw [hflen] at hY
  rw [hY, vala, hBv]

/-! ## The determinism theorem -/

set_option maxHeartbeats 1000000 in
/-- **Compiler determinism (M6, ∀σ direction).**  For every combinational expression `e` and
    EVERY net valuation σ that satisfies all cells of the compiled state and reproduces the
    denotational environment on the bound signal buses, the compiled output bus is FORCED to
    denote `eval e env`.  No freshness or boundedness of the starting state is required: a
    single σ satisfying every cell simultaneously pins the whole cone functionally. -/
theorem compile_deterministic {w : Nat} (e : Expr w) (env : Env) :
    ∀ (s : CState) (σ : Nat → Bool),
      WidthOK s.env e → CEnvOK σ s.env env →
      ConsistentCells σ ((compileExpr e).run s).2.cells →
      busDen σ w ((compileExpr e).run s).1 = eval e env := by
  induction e with
  | const v =>
    intro s σ _ _ _
    simp [compileExpr_const, eval, busDen_constBits]
  | var n w =>
    intro s σ hwf hmem _
    obtain ⟨bus, hl, hlen⟩ := hwf
    rw [compileExpr_var_some hl]
    subst hlen
    simpa [eval, Env.lookup] using hmem n bus hl
  | @not w a iha =>
    intro s σ hwf hmem hcons
    simp only [compileExpr_not_fst, compileExpr_not_cells] at hcons ⊢
    obtain ⟨hcell, hconsA⟩ := List.forall_mem_cons.1 hcons
    have vala : busDen σ w ((compileExpr a).run s).1 = eval a env := iha s σ hwf hmem hconsA
    have hY : busDen σ (freshBus ((compileExpr a).run s).2 w).length
          (freshBus ((compileExpr a).run s).2 w)
        = ~~~ busDen σ (freshBus ((compileExpr a).run s).2 w).length ((compileExpr a).run s).1 :=
      hcell
    have hflen : (freshBus ((compileExpr a).run s).2 w).length = w := by simp [freshBus]
    rw [hflen] at hY
    simp only [eval]
    rw [hY, vala]
  | @and w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_and, run_bind, emitBin_fst, emitBin_cells] at hcons ⊢
    simp only [eval]
    exact binForce (· &&& ·) "$and" iha ihb hwa hwb hmem hcons (fun h => h)
  | @or w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_or, run_bind, emitBin_fst, emitBin_cells] at hcons ⊢
    simp only [eval]
    exact binForce (· ||| ·) "$or" iha ihb hwa hwb hmem hcons (fun h => h)
  | @xor w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_xor, run_bind, emitBin_fst, emitBin_cells] at hcons ⊢
    simp only [eval]
    exact binForce (· ^^^ ·) "$xor" iha ihb hwa hwb hmem hcons (fun h => h)
  | @add w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_add, run_bind, emitBin_fst, emitBin_cells] at hcons ⊢
    simp only [eval]
    exact binForce (· + ·) "$add" iha ihb hwa hwb hmem hcons (fun h => h)
  | @sub w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_sub, run_bind, emitBin_fst, emitBin_cells] at hcons ⊢
    simp only [eval]
    exact binForce (· - ·) "$sub" iha ihb hwa hwb hmem hcons (fun h => h)
  | @mul w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_mul, run_bind, emitBin_fst, emitBin_cells] at hcons ⊢
    simp only [eval]
    exact binForce (· * ·) "$mul" iha ihb hwa hwb hmem hcons (fun h => h)
  | @udiv w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_udiv, run_bind, emitBin_fst, emitBin_cells] at hcons ⊢
    simp only [eval]
    exact binForce (· / ·) "$div" iha ihb hwa hwb hmem hcons (fun h => h)
  | @umod w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_umod, run_bind, emitBin_fst, emitBin_cells] at hcons ⊢
    simp only [eval]
    exact binForce (· % ·) "$mod" iha ihb hwa hwb hmem hcons (fun h => h)
  | @eq w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_eq, run_bind, emitCmp_fst, emitCmp_cells] at hcons ⊢
    simp only [eval]
    exact cmpForce (fun x y => if x = y then 1 else 0) "$eq" 0 iha ihb hwa hwb hmem hcons
      (fun h => h)
  | @ult w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_ult, run_bind, emitCmp_fst, emitCmp_cells] at hcons ⊢
    simp only [eval]
    exact cmpForce (fun x y => if x < y then 1 else 0) "$lt" 0 iha ihb hwa hwb hmem hcons
      (fun h => h)
  | @slt w a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_slt, run_bind, emitCmpS_fst, emitCmpS_cells] at hcons ⊢
    simp only [eval]
    exact cmpForce (fun x y => if x.toInt < y.toInt then 1 else 0) "$lt" 1 iha ihb hwa hwb hmem
      hcons (fun h => h)
  | @shl w k a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_shl, run_bind, emitShift_fst, emitShift_cells] at hcons ⊢
    simp only [eval]
    exact shiftForce BitVec.shiftLeft "$shl" 0 iha ihb hwa hwb hmem hcons (fun h => h)
  | @shr w k a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_shr, run_bind, emitShift_fst, emitShift_cells] at hcons ⊢
    simp only [eval]
    exact shiftForce BitVec.ushiftRight "$shr" 0 iha ihb hwa hwb hmem hcons (fun h => h)
  | @sshr w k a b iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwa, hwb⟩ := hwf
    simp only [compileExpr_sshr, run_bind, emitShift_fst, emitShift_cells] at hcons ⊢
    simp only [eval]
    exact shiftForce BitVec.sshiftRight "$sshr" 1 iha ihb hwa hwb hmem hcons (fun h => h)
  | @mux w sg a b ihs iha ihb =>
    intro s σ hwf hmem hcons
    obtain ⟨hws, hwa, hwb⟩ := hwf
    have henvs : ((compileExpr sg).run s).2.env = s.env := compileExpr_env sg s
    have henva : ((compileExpr a).run ((compileExpr sg).run s).2).2.env
        = ((compileExpr sg).run s).2.env := compileExpr_env a ((compileExpr sg).run s).2
    simp only [compileExpr_mux_fst, compileExpr_mux_cells] at hcons ⊢
    obtain ⟨hcell, hconsB⟩ := List.forall_mem_cons.1 hcons
    have hconsA : ConsistentCells σ ((compileExpr a).run ((compileExpr sg).run s).2).2.cells :=
      fun c hc => hconsB c (compileExpr_cells_sub b _ c hc)
    have hconsS : ConsistentCells σ ((compileExpr sg).run s).2.cells :=
      fun c hc => hconsA c (compileExpr_cells_sub a _ c hc)
    have vals : busDen σ 1 ((compileExpr sg).run s).1 = eval sg env := ihs s σ hws hmem hconsS
    have vala : busDen σ w ((compileExpr a).run ((compileExpr sg).run s).2).1 = eval a env :=
      iha _ σ (by rw [henvs]; exact hwa) (by rw [henvs]; exact hmem) hconsA
    have valb : busDen σ w
        ((compileExpr b).run ((compileExpr a).run ((compileExpr sg).run s).2).2).1 = eval b env :=
      ihb _ σ (by rw [henva, henvs]; exact hwb) (by rw [henva, henvs]; exact hmem) hconsB
    generalize hGS : (compileExpr sg).run s = RS at *
    generalize hGA : (compileExpr a).run RS.2 = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hY : busDen σ (freshBus RB.2 w).length (freshBus RB.2 w)
        = if busDen σ 1 RS.1 = 1 then busDen σ (freshBus RB.2 w).length RA.1
          else busDen σ (freshBus RB.2 w).length RB.1 := hcell
    have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
    rw [hflen] at hY
    simp only [eval]
    rw [hY, vals, vala, valb]
  | @concat a b ea eb ihea iheb =>
    intro s σ hwf hmem hcons
    obtain ⟨hwea, hweb⟩ := hwf
    have henva : ((compileExpr ea).run s).2.env = s.env := compileExpr_env ea s
    simp only [compileExpr_concat, run_bind, run_pure] at hcons ⊢
    have hconsA : ConsistentCells σ ((compileExpr ea).run s).2.cells :=
      fun c hc => hcons c (compileExpr_cells_sub eb _ c hc)
    have hweb' : WidthOK ((compileExpr ea).run s).2.env eb := by rw [henva]; exact hweb
    have vala : busDen σ a ((compileExpr ea).run s).1 = eval ea env := ihea s σ hwea hmem hconsA
    have valb : busDen σ b ((compileExpr eb).run ((compileExpr ea).run s).2).1 = eval eb env :=
      iheb _ σ hweb' (by rw [henva]; exact hmem) hcons
    have hlenA : ((compileExpr ea).run s).1.length = a := compileExpr_len ea (supp_all ea) s hwea
    have hlenB : ((compileExpr eb).run ((compileExpr ea).run s).2).1.length = b :=
      compileExpr_len eb (supp_all eb) _ hweb'
    simp only [eval]
    rw [busDen_concat σ a b ((compileExpr ea).run s).1
          ((compileExpr eb).run ((compileExpr ea).run s).2).1 hlenA hlenB, vala, valb]
  | @zext w k a iha =>
    intro s σ hwf hmem hcons
    simp only [compileExpr_zext, run_bind, run_pure] at hcons ⊢
    have vala : busDen σ w ((compileExpr a).run s).1 = eval a env := iha s σ hwf hmem hcons
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a (supp_all a) s hwf
    simp only [eval]
    rw [busDen_zext σ w k ((compileExpr a).run s).1 hlenA, vala]
  | @sext w k a iha =>
    intro s σ hwf hmem hcons
    simp only [compileExpr_sext, run_bind, run_pure] at hcons ⊢
    have vala : busDen σ w ((compileExpr a).run s).1 = eval a env := iha s σ hwf hmem hcons
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a (supp_all a) s hwf
    simp only [eval]
    rw [busDen_sext σ w k ((compileExpr a).run s).1 hlenA, vala]
  | @extract w idx a iha =>
    intro s σ hwf hmem hcons
    simp only [compileExpr_extract, run_bind, run_pure] at hcons ⊢
    have vala : busDen σ w ((compileExpr a).run s).1 = eval a env := iha s σ hwf hmem hcons
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a (supp_all a) s hwf
    simp only [eval]
    rw [busDen_extract σ w ((compileExpr a).run s).1 hlenA idx, vala]
  | @slice w lo len a iha =>
    intro s σ hwf hmem hcons
    simp only [compileExpr_slice, run_bind, run_pure] at hcons ⊢
    have vala : busDen σ w ((compileExpr a).run s).1 = eval a env := iha s σ hwf hmem hcons
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a (supp_all a) s hwf
    simp only [eval]
    rw [busDen_slice σ w lo len ((compileExpr a).run s).1 hlenA, vala]

/-! ## Downstream-facing corollaries -/

/-- **Forcing form** for downstream use: fixing the compilation (`e`, `s`) once, every consistent,
    env-respecting valuation is forced to place `eval e env` on the output bus.  Composes with
    `compile_correct` (existence) to fully pin the netlist's behaviour. -/
theorem compile_forces {w : Nat} (e : Expr w) (env : Env) (s : CState)
    (hwf : WidthOK s.env e) :
    ∀ σ : Nat → Bool,
      ConsistentCells σ ((compileExpr e).run s).2.cells →
      CEnvOK σ s.env env →
      busDen σ w ((compileExpr e).run s).1 = eval e env :=
  fun σ hcons hmem => compile_deterministic e env s σ hwf hmem hcons

/-- Any two consistent, env-respecting valuations agree on the compiled output bus: the
    netlist has a *unique* output value per input environment. -/
theorem compile_output_unique {w : Nat} (e : Expr w) (env : Env) (s : CState)
    (σ σ' : Nat → Bool) (hwf : WidthOK s.env e)
    (hmem : CEnvOK σ s.env env) (hmem' : CEnvOK σ' s.env env)
    (hcons : ConsistentCells σ ((compileExpr e).run s).2.cells)
    (hcons' : ConsistentCells σ' ((compileExpr e).run s).2.cells) :
    busDen σ w ((compileExpr e).run s).1 = busDen σ' w ((compileExpr e).run s).1 := by
  rw [compile_deterministic e env s σ hwf hmem hcons,
      compile_deterministic e env s σ' hwf hmem' hcons']

/-- **Two-sided compiler correctness.**  Combines `sound` (existence) with
    `compile_deterministic` (forcing): the compiled netlist admits a consistent,
    env-respecting valuation, and EVERY such valuation makes the output bus denote
    `eval e env`.  This is the complete `⟦·⟧` ↔ RTLIL characterisation for the
    combinational `Expr` algebra. -/
theorem compile_correct_unique {w : Nat} (e : Expr w) (env : Env) (s : CState) (σ₀ : Nat → Bool)
    (hwf : WidthOK s.env e) (hmem : CEnvOK σ₀ s.env env) (hbnd : EnvBounded s.env s.nextId)
    (hcons : ConsistentCells σ₀ s.cells) (hcb : CellsBounded s.cells s.nextId) :
    (∃ σ : Nat → Bool,
        ConsistentCells σ ((compileExpr e).run s).2.cells ∧ CEnvOK σ s.env env) ∧
    (∀ σ : Nat → Bool,
        ConsistentCells σ ((compileExpr e).run s).2.cells → CEnvOK σ s.env env →
        busDen σ w ((compileExpr e).run s).1 = eval e env) := by
  constructor
  · obtain ⟨σ, hex, hcc, _, _, _, _, _⟩ := sound e env (supp_all e) s σ₀ hwf hmem hbnd hcons hcb
    exact ⟨σ, hcc, CEnvOK_frame hbnd (fun k hk => (hex k hk).symm) hmem⟩
  · intro σ hcc hmem'
    exact compile_deterministic e env s σ hwf hmem' hcc

end LeanRTL.CompilerDeterministic
