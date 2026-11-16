import LeanRTL.Core.FourStateComparisonCorrect
import LeanRTL.Core.FourStateStructuralCorrect

namespace LeanRTL.FourState.Encoding

/-- The value/found state in the Yosys pmux simulation algorithm. -/
def selectedStep {α β : Type} (collision : β) (read : α → β) (acc : β × Bool) (i : α) : β × Bool :=
  (if acc.2 then collision else read i, true)

theorem saturated_fold {α β : Type} (collision : β) (read : α → β) (xs : List α) :
    xs.foldl (selectedStep collision read) (collision, true) = (collision, true) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simpa [List.foldl, selectedStep] using ih

theorem selected_fold {α β : Type} (collision initial : β) (read : α → β) (xs : List α) :
    (xs.foldl (selectedStep collision read) (initial, false)).1 =
      match xs with
      | [] => initial
      | [i] => read i
      | _ => collision := by
  cases xs with
  | nil => rfl
  | cons x xs =>
    cases xs with
    | nil => rfl
    | cons y ys =>
      change (ys.foldl (selectedStep collision read) (collision, true)).1 = collision
      rw [saturated_fold]

theorem filtered_selected_fold {α β : Type} (collision initial : β) (read : α → β)
    (active : α → Bool) (xs : List α) :
    (xs.foldl (fun acc i => if active i then selectedStep collision read acc i else acc)
      (initial, false)).1 =
      match xs.filter active with
      | [] => initial
      | [i] => read i
      | _ => collision := by
  rw [← List.foldl_filter]
  exact selected_fold collision initial read _

theorem pmux_eval_fold {w n : Nat} (a : FourState.Expr w) (b : FourState.Expr (w*n))
    (s : FourState.Expr n) (env : FourState.Env) :
    FourState.eval (.pmux a b s) env =
      ((List.finRange n).foldl (fun (acc : Value w × Bool) j =>
        if FourState.eval s env j == .one then
          selectedStep (fill .x) (fun j => ⟨fun i => getBit (FourState.eval b env) (w*j.val+i.val)⟩) acc j
        else acc) (FourState.eval a env, false)).1 := by
  symm
  rw [← List.foldl_filter, selected_fold]
  simp only [FourState.eval]
  cases h : (List.finRange n).filter (fun j => FourState.eval s env j == .one) with
  | nil => simp_all
  | cons j rest =>
    cases rest with
    | nil => simp_all
    | cons k tail => simp_all

theorem range_from_finRange (n : Nat) : List.range n = (List.finRange n).map Fin.val := by
  apply List.ext_getElem <;> simp


theorem active_extract_eval {n : Nat} (s : Rails n) (env : LeanRTL.Env) (j : Fin n) :
    LeanRTL.eval (.extract j.val (active s)) env =
      if den s env j == .one then (1 : BitVec 1) else 0 := by
  simp only [active, LeanRTL.eval, BitVec.getLsbD_and, BitVec.getLsbD_not,
    j.isLt, decide_true, Bool.true_and, den]
  have hb (t d : Bool) : (!t && d) = (decodeBit (t,d) == .one) := by
    cases t <;> cases d <;> rfl
  rw [hb]
  rfl

def pmuxEncodedStep {w n : Nat} (b : Rails (w*n)) (s : Rails n)
    (acc : Rails w × LeanRTL.Expr 1) (j : Fin n) : Rails w × LeanRTL.Expr 1 :=
  let isActive := LeanRTL.Expr.extract j.val (active s)
  let word : Rails w := ⟨.slice (w*j.val) w b.tag, .slice (w*j.val) w b.data⟩
  (choose isActive (choose acc.2 (constant .x) word) acc.1, .or acc.2 isActive)

def pmuxDecodedState {w : Nat} (env : LeanRTL.Env) (acc : Rails w × LeanRTL.Expr 1) : Value w × Bool :=
  (den acc.1 env, decide (LeanRTL.eval acc.2 env = 1))

theorem pmux_word {w n : Nat} (b : FourState.Expr (w*n)) (env : LeanRTL.Env) (j : Fin n) :
    den (⟨.slice (w*j.val) w (compile b).tag, .slice (w*j.val) w (compile b).data⟩ : Rails w) env =
      ⟨fun i => getBit (den (compile b) env) (w*j.val+i.val)⟩ := by
  apply congrArg Value.mk
  funext i
  have hb : w*j.val+w ≤ w*n := by
    have := Nat.mul_le_mul_left w (Nat.succ_le_of_lt j.isLt)
    simpa [Nat.mul_add] using this
  exact slice_step (w*j.val) w b hb env i

theorem pmux_encoded_step {w n : Nat} (b : FourState.Expr (w*n)) (s : FourState.Expr n)
    (env : LeanRTL.Env) (acc : Rails w × LeanRTL.Expr 1) (j : Fin n) :
    pmuxDecodedState env (pmuxEncodedStep (compile b) (compile s) acc j) =
      if den (compile s) env j == .one then
        selectedStep (fill .x)
          (fun j => ⟨fun i => getBit (den (compile b) env) (w*j.val+i.val)⟩)
          (pmuxDecodedState env acc) j
      else pmuxDecodedState env acc := by
  unfold pmuxDecodedState pmuxEncodedStep
  simp only [den_choose, active_extract_eval, den_constant, pmux_word]
  have ha := active_extract_eval (compile s) env j
  simp only [LeanRTL.eval] at ha
  simp only [LeanRTL.eval]
  rcases BitVec.eq_zero_or_eq_one (LeanRTL.eval acc.2 env) with hf | hf <;>
    cases hs : (den (compile s) env j == .one) <;>
    simp_all [selectedStep]


theorem pmux_step {w n : Nat} (a : FourState.Expr w) (b : FourState.Expr (w*n))
    (s : FourState.Expr n) (env : LeanRTL.Env) :
    den (compile (.pmux a b s)) env =
      match (List.finRange n).filter (fun i => den (compile s) env i == .one) with
      | [] => den (compile a) env
      | [j] => ⟨fun i => getBit (den (compile b) env) (w*j.val+i.val)⟩
      | _ => fill .x := by
  let step := pmuxEncodedStep (compile b) (compile s)
  let valueStep := fun (acc : Value w × Bool) (j : Fin n) =>
    if den (compile s) env j == .one then
      selectedStep (fill .x)
        (fun j => ⟨fun i => getBit (den (compile b) env) (w*j.val+i.val)⟩) acc j
    else acc
  have hh := List.foldl_hom (pmuxDecodedState env) (g₁ := step) (g₂ := valueStep)
    (l := List.finRange n) (init := (compile a, zero 1))
    (fun acc j => (pmux_encoded_step b s env acc j).symm)
  have hv := congrArg Prod.fst hh
  change ((List.finRange n).foldl valueStep (den (compile a) env, false)).1 =
    den (((List.finRange n).foldl step (compile a, zero 1)).1) env at hv
  change den (((List.range n).foldl _ (compile a, zero 1)).1) env = _
  rw [range_from_finRange, List.foldl_map]
  change den (((List.finRange n).foldl step (compile a, zero 1)).1) env = _
  rw [← hv]
  dsimp only [valueStep]
  rw [← List.foldl_filter, selected_fold]
  cases h : (List.finRange n).filter (fun j => den (compile s) env j == .one) with
  | nil => simp_all
  | cons j rest =>
    cases rest with
    | nil => simp_all
    | cons k tail => simp_all

end LeanRTL.FourState.Encoding
