import LeanRTL.Core.Semantics
/-!
# A verified optimizer (plan v0.3 M12): constant folding / peephole

`foldConst : Expr w → Expr w` is a bottom-up constant-folding / peephole optimizer:
it folds an operation applied to literal `const`s into a single `const`, and otherwise
recurses structurally into the sub-expressions (leaving `var` alone).

The headline theorem `foldConst_correct` proves it preserves the denotational semantics:
`eval (foldConst e) env = eval e env` for *every* expression and environment.  Composed
with the already-proven `CompilerCorrect.compile_correct` (⟦e⟧ = ⟦compile e⟧) this gives an
end-to-end "optimize-correct + compile-correct" guarantee: the optimizer can rewrite a design
and the lowered netlist is still proven equivalent to the original specification.

This file is purely additive — it imports only `Semantics` (hence `Syntax`) and touches no
existing proof.  The correctness proof uses only the structural `eval` equations (no
decision-procedure reflection), so it stays axiom-clean with the standard axioms only.
-/

namespace LeanRTL.Optimize

open LeanRTL

set_option linter.unusedVariables false

/-! ## Smart constructors

Each `mk*` is a *peephole*: it pattern-matches its (already-folded) argument(s) and, when they
are literal `const`s, returns a single folded `const`; otherwise it rebuilds the node unchanged.
Each comes with an `eval` lemma stating it denotes exactly the corresponding `eval` clause — so
the lemmas compose cleanly in `foldConst_correct`. -/

/-- `not` of a constant folds to the bitwise complement. -/
def mkNot {w : Nat} (a : Expr w) : Expr w :=
  match a with
  | .const x => .const (~~~ x)
  | a        => .not a

/-- `and` of two constants folds to their bitwise and. -/
def mkAnd {w : Nat} (a b : Expr w) : Expr w :=
  match a, b with
  | .const x, .const y => .const (x &&& y)
  | a, b               => .and a b

def mkOr {w : Nat} (a b : Expr w) : Expr w :=
  match a, b with
  | .const x, .const y => .const (x ||| y)
  | a, b               => .or a b

def mkXor {w : Nat} (a b : Expr w) : Expr w :=
  match a, b with
  | .const x, .const y => .const (x ^^^ y)
  | a, b               => .xor a b

def mkAdd {w : Nat} (a b : Expr w) : Expr w :=
  match a, b with
  | .const x, .const y => .const (x + y)
  | a, b               => .add a b

def mkSub {w : Nat} (a b : Expr w) : Expr w :=
  match a, b with
  | .const x, .const y => .const (x - y)
  | a, b               => .sub a b

def mkMul {w : Nat} (a b : Expr w) : Expr w :=
  match a, b with
  | .const x, .const y => .const (x * y)
  | a, b               => .mul a b

def mkUdiv {w : Nat} (a b : Expr w) : Expr w :=
  match a, b with
  | .const x, .const y => .const (x / y)
  | a, b               => .udiv a b

def mkUmod {w : Nat} (a b : Expr w) : Expr w :=
  match a, b with
  | .const x, .const y => .const (x % y)
  | a, b               => .umod a b

/-- Logical left shift of two constants folds to the concrete shift. -/
def mkShl {w k : Nat} (a : Expr w) (b : Expr k) : Expr w :=
  match a, b with
  | .const x, .const y => .const (BitVec.shiftLeft x y.toNat)
  | a, b               => .shl a b

def mkShr {w k : Nat} (a : Expr w) (b : Expr k) : Expr w :=
  match a, b with
  | .const x, .const y => .const (BitVec.ushiftRight x y.toNat)
  | a, b               => .shr a b

def mkSshr {w k : Nat} (a : Expr w) (b : Expr k) : Expr w :=
  match a, b with
  | .const x, .const y => .const (BitVec.sshiftRight x y.toNat)
  | a, b               => .sshr a b

/-- `eq` of two constants folds to the concrete one-bit truth value. -/
def mkEq {w : Nat} (a b : Expr w) : Expr 1 :=
  match a, b with
  | .const x, .const y => .const (if x = y then 1 else 0)
  | a, b               => .eq a b

def mkUlt {w : Nat} (a b : Expr w) : Expr 1 :=
  match a, b with
  | .const x, .const y => .const (if x < y then 1 else 0)
  | a, b               => .ult a b

def mkSlt {w : Nat} (a b : Expr w) : Expr 1 :=
  match a, b with
  | .const x, .const y => .const (if x.toInt < y.toInt then 1 else 0)
  | a, b               => .slt a b

/-- `mux` with a constant selector folds away the multiplexer entirely (even when the data
    inputs are not constants). -/
def mkMux {w : Nat} (s : Expr 1) (a b : Expr w) : Expr w :=
  match s with
  | .const sv => if sv = 1 then a else b
  | _         => .mux s a b

/-- `concat` of two constants folds to a single wider constant. -/
def mkConcat {a b : Nat} (ea : Expr a) (eb : Expr b) : Expr (a + b) :=
  match ea, eb with
  | .const x, .const y => .const (x ++ y)
  | ea, eb             => .concat ea eb

def mkZext {w : Nat} (k : Nat) (a : Expr w) : Expr (w + k) :=
  match a with
  | .const x => .const (x.setWidth (w + k))
  | a        => .zext k a

def mkSext {w : Nat} (k : Nat) (a : Expr w) : Expr (w + k) :=
  match a with
  | .const x => .const (x.signExtend (w + k))
  | a        => .sext k a

def mkExtract {w : Nat} (i : Nat) (a : Expr w) : Expr 1 :=
  match a with
  | .const x => .const (if x.getLsbD i then 1 else 0)
  | a        => .extract i a

def mkSlice {w : Nat} (lo len : Nat) (a : Expr w) : Expr len :=
  match a with
  | .const x => .const ((x >>> lo).setWidth len)
  | a        => .slice lo len a

/-! ### `eval` laws for the smart constructors -/

theorem mkNot_eval {w : Nat} (a : Expr w) (env : Env) :
    eval (mkNot a) env = ~~~ eval a env := by
  unfold mkNot; split <;> rfl

theorem mkAnd_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkAnd a b) env = eval a env &&& eval b env := by
  unfold mkAnd; split <;> rfl

theorem mkOr_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkOr a b) env = eval a env ||| eval b env := by
  unfold mkOr; split <;> rfl

theorem mkXor_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkXor a b) env = eval a env ^^^ eval b env := by
  unfold mkXor; split <;> rfl

theorem mkAdd_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkAdd a b) env = eval a env + eval b env := by
  unfold mkAdd; split <;> rfl

theorem mkSub_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkSub a b) env = eval a env - eval b env := by
  unfold mkSub; split <;> rfl

theorem mkMul_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkMul a b) env = eval a env * eval b env := by
  unfold mkMul; split <;> rfl

theorem mkUdiv_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkUdiv a b) env = eval a env / eval b env := by
  unfold mkUdiv; split <;> rfl

theorem mkUmod_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkUmod a b) env = eval a env % eval b env := by
  unfold mkUmod; split <;> rfl

theorem mkShl_eval {w k : Nat} (a : Expr w) (b : Expr k) (env : Env) :
    eval (mkShl a b) env = BitVec.shiftLeft (eval a env) (eval b env).toNat := by
  unfold mkShl; split <;> rfl

theorem mkShr_eval {w k : Nat} (a : Expr w) (b : Expr k) (env : Env) :
    eval (mkShr a b) env = BitVec.ushiftRight (eval a env) (eval b env).toNat := by
  unfold mkShr; split <;> rfl

theorem mkSshr_eval {w k : Nat} (a : Expr w) (b : Expr k) (env : Env) :
    eval (mkSshr a b) env = BitVec.sshiftRight (eval a env) (eval b env).toNat := by
  unfold mkSshr; split <;> rfl

theorem mkEq_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkEq a b) env = if eval a env = eval b env then 1 else 0 := by
  unfold mkEq; split <;> rfl

theorem mkUlt_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkUlt a b) env = if eval a env < eval b env then 1 else 0 := by
  unfold mkUlt; split <;> rfl

theorem mkSlt_eval {w : Nat} (a b : Expr w) (env : Env) :
    eval (mkSlt a b) env = if (eval a env).toInt < (eval b env).toInt then 1 else 0 := by
  unfold mkSlt; split <;> rfl

theorem mkMux_eval {w : Nat} (s : Expr 1) (a b : Expr w) (env : Env) :
    eval (mkMux s a b) env = if eval s env = 1 then eval a env else eval b env := by
  unfold mkMux; split
  · rename_i sv
    have hsv : eval (Expr.const sv) env = sv := rfl
    rw [hsv]
    by_cases h : sv = 1
    · rw [if_pos h, if_pos h]
    · rw [if_neg h, if_neg h]
  · rfl

theorem mkConcat_eval {a b : Nat} (ea : Expr a) (eb : Expr b) (env : Env) :
    eval (mkConcat ea eb) env = eval ea env ++ eval eb env := by
  unfold mkConcat; split <;> rfl

theorem mkZext_eval {w : Nat} (k : Nat) (a : Expr w) (env : Env) :
    eval (mkZext k a) env = (eval a env).setWidth (w + k) := by
  unfold mkZext; split <;> rfl

theorem mkSext_eval {w : Nat} (k : Nat) (a : Expr w) (env : Env) :
    eval (mkSext k a) env = (eval a env).signExtend (w + k) := by
  unfold mkSext; split <;> rfl

theorem mkExtract_eval {w : Nat} (i : Nat) (a : Expr w) (env : Env) :
    eval (mkExtract i a) env = if (eval a env).getLsbD i then 1 else 0 := by
  unfold mkExtract; split <;> rfl

theorem mkSlice_eval {w : Nat} (lo len : Nat) (a : Expr w) (env : Env) :
    eval (mkSlice lo len a) env = ((eval a env) >>> lo).setWidth len := by
  unfold mkSlice; split <;> rfl

/-! ## The optimizer -/

/-- Bottom-up constant-folding / peephole optimizer.  Every node first folds its children,
    then applies the matching smart constructor; literal sub-trees collapse to a single
    `const`.  `var` is left untouched. -/
def foldConst : {w : Nat} → Expr w → Expr w
  | _, .const v       => .const v
  | _, .var n w       => .var n w
  | _, .not a         => mkNot (foldConst a)
  | _, .and a b       => mkAnd (foldConst a) (foldConst b)
  | _, .or a b        => mkOr (foldConst a) (foldConst b)
  | _, .xor a b       => mkXor (foldConst a) (foldConst b)
  | _, .add a b       => mkAdd (foldConst a) (foldConst b)
  | _, .sub a b       => mkSub (foldConst a) (foldConst b)
  | _, .mul a b       => mkMul (foldConst a) (foldConst b)
  | _, .shl a b       => mkShl (foldConst a) (foldConst b)
  | _, .shr a b       => mkShr (foldConst a) (foldConst b)
  | _, .sshr a b      => mkSshr (foldConst a) (foldConst b)
  | _, .udiv a b      => mkUdiv (foldConst a) (foldConst b)
  | _, .umod a b      => mkUmod (foldConst a) (foldConst b)
  | _, .eq a b        => mkEq (foldConst a) (foldConst b)
  | _, .ult a b       => mkUlt (foldConst a) (foldConst b)
  | _, .slt a b       => mkSlt (foldConst a) (foldConst b)
  | _, .mux s a b     => mkMux (foldConst s) (foldConst a) (foldConst b)
  | _, .concat a b    => mkConcat (foldConst a) (foldConst b)
  | _, .zext k a      => mkZext k (foldConst a)
  | _, .sext k a      => mkSext k (foldConst a)
  | _, .extract i a   => mkExtract i (foldConst a)
  | _, .slice lo len a => mkSlice lo len (foldConst a)

/-! ## The headline theorem: `foldConst` preserves `eval` -/

/-- `foldConst` is semantics-preserving: optimizing an expression does not change what it
    denotes, for every environment.  Proof is structural induction over `Expr`; each folded
    node is discharged by its smart-constructor `eval` law plus the induction hypotheses,
    and each recursive node by congruence.  Axiom-clean: standard axioms only. -/
theorem foldConst_correct : ∀ {w : Nat} (e : Expr w) (env : Env),
    eval (foldConst e) env = eval e env := by
  intro w e env
  induction e with
  | const v => rfl
  | var n w => rfl
  | not a ih => simp only [foldConst, mkNot_eval, eval, ih]
  | and a b iha ihb => simp only [foldConst, mkAnd_eval, eval, iha, ihb]
  | or a b iha ihb => simp only [foldConst, mkOr_eval, eval, iha, ihb]
  | xor a b iha ihb => simp only [foldConst, mkXor_eval, eval, iha, ihb]
  | add a b iha ihb => simp only [foldConst, mkAdd_eval, eval, iha, ihb]
  | sub a b iha ihb => simp only [foldConst, mkSub_eval, eval, iha, ihb]
  | mul a b iha ihb => simp only [foldConst, mkMul_eval, eval, iha, ihb]
  | shl a b iha ihb => simp only [foldConst, mkShl_eval, eval, iha, ihb]
  | shr a b iha ihb => simp only [foldConst, mkShr_eval, eval, iha, ihb]
  | sshr a b iha ihb => simp only [foldConst, mkSshr_eval, eval, iha, ihb]
  | udiv a b iha ihb => simp only [foldConst, mkUdiv_eval, eval, iha, ihb]
  | umod a b iha ihb => simp only [foldConst, mkUmod_eval, eval, iha, ihb]
  | eq a b iha ihb => simp only [foldConst, mkEq_eval, eval, iha, ihb]
  | ult a b iha ihb => simp only [foldConst, mkUlt_eval, eval, iha, ihb]
  | slt a b iha ihb => simp only [foldConst, mkSlt_eval, eval, iha, ihb]
  | mux s a b ihs iha ihb => simp only [foldConst, mkMux_eval, eval, ihs, iha, ihb]
  | concat a b iha ihb => simp only [foldConst, mkConcat_eval, eval, iha, ihb]
  | zext k a ih => simp only [foldConst, mkZext_eval, eval, ih]
  | sext k a ih => simp only [foldConst, mkSext_eval, eval, ih]
  | extract i a ih => simp only [foldConst, mkExtract_eval, eval, ih]
  | slice lo len a ih => simp only [foldConst, mkSlice_eval, eval, ih]

/-! ## Module-level lift

`optimizeModule` runs `foldConst` over every output expression, internal wire, and register
next-state expression.  Names, widths, ports, clock and reset are untouched, so the module's
*shape* is preserved and only the combinational expression trees are optimized. -/

def optimizeModule (m : Module) : Module :=
  { m with
    outputs := m.outputs.map (fun o => { o with expr := foldConst o.expr })
    wires   := m.wires.map   (fun wr => { wr with expr := foldConst wr.expr })
    regs    := m.regs.map    (fun r => { r with next := foldConst r.next }) }

/-! ### Generic "map `foldConst` over a field" laws

Each list of structures (`Wire`/`OutPort`/`Reg`) appearing in a module is rewritten by
mapping `foldConst` over one expression field.  Names, widths and `init` values are untouched,
and `foldConst_correct` makes the rewritten expression denote the same value — so every list
the module semantics consumes is provably unchanged. -/

/-- `evalWires` is invariant under folding every wire's expression: the environment it builds
    is pointwise unchanged (each wire denotes the same value, names are preserved). -/
theorem evalWires_mapFold (ws : List Wire) (e : Env) :
    evalWires (ws.map (fun wr => ({ wr with expr := foldConst wr.expr } : Wire))) e
      = evalWires ws e := by
  induction ws generalizing e with
  | nil => rfl
  | cons wr ws ih =>
    have hstep :
        (fun n => if n = wr.name then (eval (foldConst wr.expr) e).toNat else e n)
          = (fun n => if n = wr.name then (eval wr.expr e).toNat else e n) := by
      funext n; rw [foldConst_correct]
    calc
      evalWires ((wr :: ws).map (fun wr => ({ wr with expr := foldConst wr.expr } : Wire))) e
          = evalWires (ws.map (fun wr => ({ wr with expr := foldConst wr.expr } : Wire)))
              (fun n => if n = wr.name then (eval (foldConst wr.expr) e).toNat else e n) := by
            simp only [List.map_cons, evalWires, List.foldl_cons]
      _ = evalWires (ws.map (fun wr => ({ wr with expr := foldConst wr.expr } : Wire)))
              (fun n => if n = wr.name then (eval wr.expr e).toNat else e n) := by rw [hstep]
      _ = evalWires ws (fun n => if n = wr.name then (eval wr.expr e).toNat else e n) := ih _
      _ = evalWires (wr :: ws) e := by simp only [evalWires, List.foldl_cons]

/-- The register *names* are preserved when only the `next` expression is folded. -/
theorem regName_mapFold (rs : List Reg) :
    (rs.map (fun r => ({ r with next := foldConst r.next } : Reg))).map (·.name)
      = rs.map (·.name) := by
  rw [List.map_map]; apply List.map_congr_left; intro r _; rfl

/-- The initial-state list `(name, init)` is preserved when only `next` is folded. -/
theorem regInit_mapFold (rs : List Reg) :
    (rs.map (fun r => ({ r with next := foldConst r.next } : Reg))).map
        (fun r => (r.name, r.init.toNat))
      = rs.map (fun r => (r.name, r.init.toNat)) := by
  rw [List.map_map]; apply List.map_congr_left; intro r _; rfl

/-- The next-state list `(name, if rst then init else ⟦next⟧)` is preserved (folding `next`
    keeps the denotation by `foldConst_correct`). -/
theorem regNext_mapFold (rs : List Reg) (e : Env) (rst : Bool) :
    (rs.map (fun r => ({ r with next := foldConst r.next } : Reg))).map
        (fun r => (r.name, if rst then r.init.toNat else (eval r.next e).toNat))
      = rs.map (fun r => (r.name, if rst then r.init.toNat else (eval r.next e).toNat)) := by
  rw [List.map_map]; apply List.map_congr_left
  intro r _; simp only [Function.comp_apply, foldConst_correct]

/-- The output list `(name, ⟦expr⟧)` is preserved (folding each output keeps its denotation). -/
theorem outMap_mapFold (os : List OutPort) (e : Env) :
    (os.map (fun o => ({ o with expr := foldConst o.expr } : OutPort))).map
        (fun o => (o.name, (eval o.expr e).toNat))
      = os.map (fun o => (o.name, (eval o.expr e).toNat)) := by
  rw [List.map_map]; apply List.map_congr_left
  intro o _; simp only [Function.comp_apply, foldConst_correct]

/-- One cycle of combinational outputs is preserved by optimization. -/
theorem optimizeModule_outputs?eval (m : Module) (regVals inputs : Env) :
    (optimizeModule m).outputs?eval regVals inputs = m.outputs?eval regVals inputs := by
  simp only [Module.outputs?eval, optimizeModule, regName_mapFold, evalWires_mapFold,
             outMap_mapFold]

/-- A combinational (leaf) module's output map is preserved by optimization. -/
theorem optimizeModule_combOut (m : Module) (inputs : List (String × Nat)) :
    (optimizeModule m).combOut inputs = m.combOut inputs := by
  simp only [Module.combOut, optimizeModule, evalWires_mapFold, outMap_mapFold]

/-- The full sequential simulation is preserved by optimization: every per-cycle output map and
    every next-register state is unchanged, so the whole trace is identical. -/
theorem optimizeModule_simulate (m : Module) (cycles : List (List (String × Nat))) :
    (optimizeModule m).simulate cycles = m.simulate cycles := by
  simp only [Module.simulate, optimizeModule, regName_mapFold, regInit_mapFold,
             evalWires_mapFold, outMap_mapFold, regNext_mapFold]

end LeanRTL.Optimize
