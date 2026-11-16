import LeanRTL.Core.Semantics
import LeanRTL.Core.Refine
import Std.Tactic.BVDecide
/-!
# `StepSimp` — one-shot unfolding of `Module.step` / `cycleEnv` / `outputs?eval`

Proving a whole-trace obligation (`Refines.step_α`, `.reset_α`, `.obs`, or the `SimRefines`
lockstep square) always ends the same way: **reduce the cycle simulator to bare `BitVec`
arithmetic** so `bv_omega` / `bv_decide` / `decide` can finish.  The recurring failure is that
`simp only [...]` leaves `Module.step`, `cycleEnv`, `List.find?`, or `evalWires` *stuck*, and then
`bv_decide` reports a **spurious counterexample** because it abstracted the still-opaque
`eval … (cycleEnv …)` as a fresh opaque variable.

────────────────────────────────────────────────────────────────────────────────────────────────
THE RECIPE — closes a step / reset / obs obligation in ≤ 2 tactic lines:

  1.  `step_simp [Module.step, impl, next, α, spec]`     -- a `step_α` / next-state goal
      `step_simp [Module.outputs?eval, impl, α]`         -- an `obs` / output goal
      (List the goal's HEAD def — `Module.step` or `Module.outputs?eval` — then your design's own
       `impl` / next-state expr / `α` / spec defs.  `step_simp` appends the machinery unfolds
       `evalWires, eval, cycleEnv, Env.lookup`; register lookups then reduce automatically.)
  2.  if a `BitVec` residue survives:  `bv_omega`  (or `bv_decide`).   `reset_α` is usually `rfl`.

Use FULL `simp` (what `step_simp` does), NOT `simp only`: under `simp only` the conditional
`cycleEnv_reg`/`cycleEnv_input` do not auto-discharge their `List.contains` side-goal (the classic
"cycleEnv List.contains stuck") — you would have to pass `cycleEnv_reg r i names "x" (by decide)`
by hand for every signal.  `bv_omega` (not `bv_decide`) is the safe finisher: full `simp` may
rewrite the `.toNat` round-trip into `BitVec.ofNat w (… % 2^w)` and `bv_omega` sees through that.
────────────────────────────────────────────────────────────────────────────────────────────────

Everything here is `rfl`/`simp`-proven — no `sorry`, no axioms.  For the *packaged* combinators
(`simRefines_single`, `refines_pair`, …) that assemble a whole `Refines` from per-register
bridges, see `LeanRTL/Lib/Lift.lean`; this file is the lower-level "make the term reduce" layer
those bridges — and any bespoke `Module.step` proof — stand on.
-/

namespace LeanRTL.StepSimp
open LeanRTL

/-! ## 1. `cycleEnv` lookups — the load-bearing reductions

`Module.step` / `outputs?eval` evaluate every expression under `cycleEnv regVals inputs regNames`,
which reads a *register* name from `regVals` and *anything else* from `inputs`.  These two `@[simp]`
lemmas fire on a concrete name + register-name list; under full `simp` the `List.contains`
side-goal is discharged automatically (under `simp only`, pass them applied: `cycleEnv_reg r i
names "x" (by decide)`). -/

/-- A signal that IS a register name reads from the register file. -/
@[simp] theorem cycleEnv_reg (rv i : Env) (names : List String) (n : String)
    (h : names.contains n = true) : cycleEnv rv i names n = rv n := by
  simp only [cycleEnv, h]; rfl

/-- A signal that is NOT a register name reads from the inputs. -/
@[simp] theorem cycleEnv_input (rv i : Env) (names : List String) (n : String)
    (h : names.contains n = false) : cycleEnv rv i names n = i n := by
  simp only [cycleEnv, h]; rfl

/-- With no internal wires the cycle environment IS `cycleEnv` (collapses the `evalWires` fold). -/
@[simp] theorem evalWires_nil (e : Env) : evalWires [] e = e := rfl

/-! ## 2. `Module.step` / `initRegs` reductions

`step_single` / `reset_single` are the clean single-register, wire-free reductions: they take
`Module.step` straight to `eval next (cycleEnv r i [rn])` (no leftover `evalWires`/`map`).  Their
`find?`-keyed cousins `step_find` / `reset_find` handle *any* module (multiple registers, wires).
Both `h`-hypotheses are discharged by `rfl` on a concrete module (the register list is a literal,
so `find?` computes). -/

/-- **The single-register step reduction.**  One non-reset clock of a wire-free 1-register module is
    its `next` expression evaluated in this cycle's environment `cycleEnv r i [reg.name]`. -/
theorem step_single {m : Module} {reg : Reg}
    (hregs : m.regs = [reg]) (hwires : m.wires = []) (r i : Env) :
    (m.step r i false) reg.name = (eval reg.next (cycleEnv r i [reg.name])).toNat := by
  have hfind : m.regs.find? (·.name = reg.name) = some reg := by rw [hregs]; simp
  have hmap : m.regs.map (·.name) = [reg.name] := by rw [hregs]; simp
  simp only [Module.step, hwires, evalWires, List.foldl_nil, hfind, hmap]; rfl

/-- A reset clock of a wire-free 1-register module loads `reg.init`. -/
theorem reset_single {m : Module} {reg : Reg} (hregs : m.regs = [reg]) (r i : Env) :
    (m.step r i true) reg.name = reg.init.toNat := by
  have hfind : m.regs.find? (·.name = reg.name) = some reg := by rw [hregs]; simp
  simp only [Module.step, hfind, if_true]

/-- **General non-reset step** (any module, keyed on `find?`): register `n`'s `next` evaluated in the
    full cycle environment (`evalWires` over `cycleEnv`).  Use for multi-register / wire-carrying
    modules; `h` is `rfl` on a concrete `m`. -/
theorem step_find (m : Module) (r i : Env) (n : String) (reg : Reg)
    (h : m.regs.find? (·.name = n) = some reg) :
    (m.step r i false) n
      = (eval reg.next (evalWires m.wires (cycleEnv r i (m.regs.map (·.name))))).toNat := by
  simp only [Module.step, h, if_neg Bool.false_ne_true]

/-- **General reset step**: a synchronous reset loads register `n` to its `init` (any module). -/
theorem reset_find (m : Module) (r i : Env) (n : String) (reg : Reg)
    (h : m.regs.find? (·.name = n) = some reg) :
    (m.step r i true) n = reg.init.toNat := by
  simp only [Module.step, h, if_true]

/-- A name that is NOT a register passes through unchanged (either reset phase). -/
theorem step_absent (m : Module) (r i : Env) (n : String) (rst : Bool)
    (h : m.regs.find? (·.name = n) = none) :
    (m.step r i rst) n = r n := by
  simp only [Module.step, h]

/-- `Module.initRegs` on a present register reads back its `init` — pairs with `reset_find` to make
    the `reset_α` obligation defeq to `init_α`. -/
theorem initRegs_find (m : Module) (n : String) (reg : Reg)
    (h : m.regs.find? (·.name = n) = some reg) :
    m.initRegs n = reg.init.toNat := by
  simp only [Module.initRegs, h]

/-! ## 3. `outputs?eval` reduction

`Module.outputs?eval` is definitionally the output-expression map over the same cycle environment;
`step_simp [Module.outputs?eval, …]` unfolds it and the §1 lemmas reduce each `eval o.expr
(cycleEnv …)`. -/

/-- `outputs?eval` as the explicit per-output map over the cycle environment (`rfl`). -/
theorem outputs?eval_def (m : Module) (r i : Env) :
    m.outputs?eval r i
      = m.outputs.map (fun o =>
          (o.name, (eval o.expr (evalWires m.wires (cycleEnv r i (m.regs.map (·.name))))).toNat)) :=
  rfl

/-! ## 4. `step_simp` — the one-shot tactic

`step_simp [head, design-defs…]` = full `simp` with the machinery unfolds appended.  Pass the goal's
HEAD (`Module.step` / `Module.outputs?eval`) and your design's `impl` / next-state / `α` / spec
defs; the machinery (`evalWires, eval, cycleEnv, Env.lookup`) and this file's `@[simp]` lemmas come
for free.  Follow with `bv_omega` / `bv_decide` if a `BitVec` goal remains. -/
open Lean.Parser.Tactic in
macro "step_simp" "[" args:simpLemma,* "]" : tactic =>
  `(tactic| simp [$args,*, evalWires, eval, cycleEnv, Env.lookup])

/-! ## 5. Worked test — the recipe closes real 1-register obligations in ≤ 2 lines.
    These `example`s are the regression test AND the copy-paste template for a new author. -/
namespace Test

/-- Synchronous 4-bit counter `c' = reset ? 0 : c+1` (the `Prob038_count15` shape). -/
def qNext : Expr 4 :=
  .mux (.eq (.var "reset" 1) (.const 1)) (.const 0) (.add (.var "c" 4) (.const 1))
def impl : Module :=
  { name := "TopModule", inputs := [{name := "clk", width := 1}, {name := "reset", width := 1}],
    outputs := [{name := "q", width := 4, expr := .var "c" 4}],
    regs := [{name := "c", width := 4, next := qNext, init := 0}], clock := some "clk" }
def α (r : Env) : BitVec 4 := BitVec.ofNat 4 (r "c")
def specN (c : BitVec 4) (i : Env) : BitVec 4 := if BitVec.ofNat 1 (i "reset") = 1 then 0 else c + 1

/-- `step_α`: one `step_simp` reduces AND closes the goal. -/
example (r i : Env) : α (impl.step r i false) = specN (α r) i := by
  step_simp [Module.step, impl, qNext, α, specN]

/-- `reset_α`: a reset cycle loads `init`; closes by `rfl`. -/
example (r i : Env) : α (impl.step r i true) = 0 := rfl

/-- `obs`: the real output port `q` denotes the abstracted register — one `step_simp`. -/
example (r i : Env) : impl.outputs?eval r i = [("q", (α r).toNat)] := by
  step_simp [Module.outputs?eval, impl, α]

/-- The clean single-register reduction used directly (`h` = `rfl`). -/
example (r i : Env) : (impl.step r i false) "c" = (eval qNext (cycleEnv r i ["c"])).toNat :=
  step_single (m := impl) (reg := {name := "c", width := 4, next := qNext, init := 0}) rfl rfl r i

/-! ### The `bv_omega` finish — the motivation's exact scenario.
    8-bit accumulator `s' = s + d`: `step_simp` reduces the simulator; `bv_omega` closes the
    `BitVec` residue.  (Without `step_simp` first, `bv_decide` abstracts the opaque
    `eval … (cycleEnv …)` and reports a spurious counterexample.) -/
def sNext : Expr 8 := .add (.var "s" 8) (.var "d" 8)
def acc : Module :=
  { name := "Acc", inputs := [{name := "clk", width := 1}, {name := "d", width := 8}],
    outputs := [{name := "s", width := 8, expr := .var "s" 8}],
    regs := [{name := "s", width := 8, next := sNext, init := 0}], clock := some "clk" }
def αA (r : Env) : BitVec 8 := BitVec.ofNat 8 (r "s")

example (r i : Env) : αA (acc.step r i false) = αA r + BitVec.ofNat 8 (i "d") := by
  step_simp [Module.step, acc, sNext, αA]
  bv_omega

end Test
end LeanRTL.StepSimp
