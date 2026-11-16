import LeanRTL.Core.FourStateModuleCorrect
import Lean

open Lean Elab Tactic Meta in
/-- Construct reflexivity and leave conversion checking to the kernel. Unlike `rfl`,
this avoids first expanding a large inlined circuit in the elaborator as well.
The enclosing declaration still fails kernel checking if its sides differ. -/
elab "source_kernel_rfl" : tactic => do
  let goal ← getMainGoal
  let target ← goal.getType
  let some (_, lhs, _) := target.eq? | throwError "expected equality"
  goal.assign (← mkEqRefl lhs)
  replaceMainGoal []

namespace LeanRTL.FourState.Source
open Encoding

/-- One typed blocking assignment substituted into a later expression. -/
def substOne (binding : FourState.Wire) : {w : Nat} → FourState.Expr w → FourState.Expr w
  | _, .const v => .const v
  | _, .fill b => .fill b
  | w, .var name _ =>
    if name = binding.name then
      if h : binding.width = w then h ▸ binding.expr else .var name w
    else .var name w
  | _, .not a => .not (substOne binding a)
  | _, .and a b => .and (substOne binding a) (substOne binding b)
  | _, .or a b => .or (substOne binding a) (substOne binding b)
  | _, .xor a b => .xor (substOne binding a) (substOne binding b)
  | _, .add a b => .add (substOne binding a) (substOne binding b)
  | _, .sub a b => .sub (substOne binding a) (substOne binding b)
  | _, .mul a b => .mul (substOne binding a) (substOne binding b)
  | _, .udiv a b => .udiv (substOne binding a) (substOne binding b)
  | _, .shl a b => .shl (substOne binding a) (substOne binding b)
  | _, .shr a b => .shr (substOne binding a) (substOne binding b)
  | _, .sshr a b => .sshr (substOne binding a) (substOne binding b)
  | _, .eq a b => .eq (substOne binding a) (substOne binding b)
  | _, .caseEq a b => .caseEq (substOne binding a) (substOne binding b)
  | _, .ult a b => .ult (substOne binding a) (substOne binding b)
  | _, .slt a b => .slt (substOne binding a) (substOne binding b)
  | _, .mux s a b => .mux (substOne binding s) (substOne binding a) (substOne binding b)
  | _, .pmux a b s => .pmux (substOne binding a) (substOne binding b) (substOne binding s)
  | _, .concat a b => .concat (substOne binding a) (substOne binding b)
  | _, .zext k a => .zext k (substOne binding a)
  | _, .sext k a => .sext k (substOne binding a)
  | _, .extract i a => .extract i (substOne binding a)
  | _, .slice lo len a => .slice lo len (substOne binding a)

/-- A declaration fixes every occurrence of this name to the same width. -/
def bindingValid (scope : List (String × Nat)) (binding : FourState.Wire) : Prop :=
  scope.lookup binding.name = some binding.width ∧ binding.expr.valid scope = true

theorem substOne_valid (binding : FourState.Wire) (scope : List (String × Nat))
    (hb : bindingValid scope binding) {w : Nat} (expr : FourState.Expr w) :
    expr.valid scope = true → (substOne binding expr).valid scope = true := by
  induction expr <;> intro hv
  all_goals try simp_all [substOne, FourState.Expr.valid]
  rename_i name width
  by_cases hn : name = binding.name
  · subst name
    have hw : binding.width = width := Option.some.inj (hb.1.symm.trans hv.2)
    subst width
    simpa [substOne] using hb.2
  · simp_all [substOne, FourState.Expr.valid]

theorem substOne_correct (binding : FourState.Wire) (scope : List (String × Nat))
    (hb : bindingValid scope binding) {w : Nat} (expr : FourState.Expr w) (env : FourState.Env) :
    expr.valid scope = true →
    FourState.eval (substOne binding expr) env =
      FourState.eval expr (putValue env binding.name (FourState.eval binding.expr env)) := by
  induction expr <;> intro hv
  all_goals try simp_all [substOne, FourState.Expr.valid, FourState.eval]
  rename_i name width
  by_cases hn : name = binding.name
  · subst name
    have hw : binding.width = width := Option.some.inj (hb.1.symm.trans hv.2)
    subst width
    apply value_ext
    intro i
    simp [substOne, FourState.eval, putValue, getBit, i.isLt]
  · simp_all [substOne, FourState.eval, putValue]

/-- Inline an ordered wire/assignment list backwards, preserving blocking order. -/
def inlineWires (wires : List FourState.Wire) {w : Nat} (expr : FourState.Expr w) : FourState.Expr w :=
  wires.foldr (fun b e => substOne b e) expr

theorem inlineWires_valid (wires : List FourState.Wire) (scope : List (String × Nat))
    (hw : ∀ binding ∈ wires, bindingValid scope binding) {w : Nat} (expr : FourState.Expr w)
    (he : expr.valid scope = true) : (inlineWires wires expr).valid scope = true := by
  induction wires with
  | nil => exact he
  | cons binding rest ih =>
    exact substOne_valid binding scope (hw binding (by simp)) _
      (ih (fun b h => hw b (by simp [h])))

theorem inlineWires_correct (wires : List FourState.Wire) (scope : List (String × Nat))
    (hw : ∀ binding ∈ wires, bindingValid scope binding) {w : Nat} (expr : FourState.Expr w)
    (he : expr.valid scope = true) (env : FourState.Env) :
    FourState.eval (inlineWires wires expr) env =
      FourState.eval expr (wires.foldl valueWireStep env) := by
  induction wires generalizing env with
  | nil => rfl
  | cons binding rest ih =>
    have hr : ∀ b ∈ rest, bindingValid scope b := fun b h => hw b (by simp [h])
    change FourState.eval (substOne binding (inlineWires rest expr)) env = _
    rw [substOne_correct binding scope (hw binding (by simp)) _ env
      (inlineWires_valid rest scope hr expr he)]
    exact ih hr _


def allScope (m : FourState.Module) : List (String × Nat) :=
  m.inputs.map (fun p => (p.name,p.width)) ++ m.wires.map (fun p => (p.name,p.width))

def moduleTyped (m : FourState.Module) : Bool :=
  m.wires.all (fun p => (allScope m).lookup p.name == some p.width && p.expr.valid (allScope m)) &&
    m.outputs.all (fun p => p.expr.valid (allScope m))

def inlinedOutputs (m : FourState.Module) : List FourState.Wire :=
  m.outputs.map (fun p => {p with expr := inlineWires m.wires p.expr})

theorem module_inline_correct (m : FourState.Module) (hv : moduleTyped m = true) (env : FourState.Env) :
    (inlinedOutputs m).map (fun p => (p.name, renderValue (FourState.eval p.expr env))) = m.eval env := by
  simp only [moduleTyped, Bool.and_eq_true] at hv
  have hw : ∀ binding ∈ m.wires, bindingValid (allScope m) binding := by
    intro binding hb
    have h := List.all_eq_true.mp hv.1 binding hb
    simpa only [bindingValid, Bool.and_eq_true, beq_iff_eq] using h
  dsimp only [inlinedOutputs, FourState.Module.eval]
  rw [wireValues_correct, List.map_map]
  apply List.map_congr_left
  intro output ho
  dsimp only [Function.comp_def]
  rw [inlineWires_correct m.wires (allScope m) hw output.expr (List.all_eq_true.mp hv.2 output ho)]

theorem module_equiv_of_inlined (a b : FourState.Module)
    (ha : moduleTyped a = true) (hb : moduleTyped b = true)
    (h : inlinedOutputs a = inlinedOutputs b) (env : FourState.Env) : a.eval env = b.eval env := by
  rw [← module_inline_correct a ha env, ← module_inline_correct b hb env, h]

end LeanRTL.FourState.Source
