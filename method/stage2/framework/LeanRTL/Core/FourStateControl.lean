import LeanRTL.Core.FourStateSubstitution

namespace LeanRTL.FourState.Source
open Encoding

def booleanValue (b : Bool) : Value 1 := fill (if b then .one else .zero)

def truthy {w : Nat} (value : Value w) : Bool :=
  (List.finRange w).any (fun i => value i == .one)

def ifTest {w : Nat} (condition : FourState.Expr w) : FourState.Expr 1 :=
  .caseEq (.not (.eq condition (.const 0))) (.const 1)

def labelMatches {w : Nat} (selector label : FourState.Expr w) (env : FourState.Env) : Bool :=
  (List.finRange w).all (fun i => FourState.eval selector env i == FourState.eval label env i)

def caseTest {w : Nat} (selector : FourState.Expr w) (labels : List (FourState.Expr w)) : FourState.Expr 1 :=
  match labels with
  | [] => .const 0
  | first::rest => rest.foldl (fun acc label => .or acc (.caseEq selector label)) (.caseEq selector first)

private theorem mismatch_zero_bit (a : Bit) :
    (a.known && Bit.zero.known && a != .zero) = (a == .one) := by cases a <;> rfl

theorem logical_not_zero_one {w : Nat} (a : Value w) :
    ((logicalEq a (ofBitVec 0)).inv == .one) = truthy a := by
  have hm : (List.finRange w).any (fun i => (a i).known && ((ofBitVec (0 : BitVec w)) i).known &&
      a i != ofBitVec (0 : BitVec w) i) = truthy a := by
    apply congrArg (fun f : Fin w → Bool => (List.finRange w).any f)
    funext i
    simpa [ofBitVec] using mismatch_zero_bit (a i)
  have hk : known (ofBitVec (0 : BitVec w)) = true := by simp [known, ofBitVec, Bit.known]
  simp only [logicalEq, hm, hk, Bool.and_true]
  cases ht : truthy a <;> cases ha : known a <;> rfl

theorem ifTest_correct {w : Nat} (condition : FourState.Expr w) (env : FourState.Env) :
    FourState.eval (ifTest condition) env = booleanValue (truthy (FourState.eval condition env)) := by
  have h := logical_not_zero_one (FourState.eval condition env)
  simpa [ifTest, FourState.eval, booleanValue, ofBitVec, fill, List.finRange] using congrArg
    (fun b => booleanValue b) h

theorem eval_or_boolean (a b : FourState.Expr 1) (env : FourState.Env) (x y : Bool)
    (ha : FourState.eval a env = booleanValue x) (hb : FourState.eval b env = booleanValue y) :
    FourState.eval (.or a b) env = booleanValue (x || y) := by
  cases x <;> cases y <;> simp [FourState.eval, ha, hb, booleanValue, fill, Bit.bor]

theorem caseTest_fold_correct {w : Nat} (selector : FourState.Expr w) (labels : List (FourState.Expr w))
    (env : FourState.Env) (acc : FourState.Expr 1) (initial : Bool)
    (ha : FourState.eval acc env = booleanValue initial) :
    FourState.eval (labels.foldl (fun acc label => .or acc (.caseEq selector label)) acc) env =
      booleanValue (initial || labels.any (fun label => labelMatches selector label env)) := by
  induction labels generalizing acc initial with
  | nil => simpa using ha
  | cons label rest ih =>
    have hb : FourState.eval (.caseEq selector label) env = booleanValue (labelMatches selector label env) := rfl
    have h := ih (.or acc (.caseEq selector label)) (initial || labelMatches selector label env)
      (eval_or_boolean _ _ env _ _ ha hb)
    simpa [List.any_cons, Bool.or_assoc] using h

theorem caseTest_correct {w : Nat} (selector : FourState.Expr w) (labels : List (FourState.Expr w))
    (env : FourState.Env) : FourState.eval (caseTest selector labels) env =
      booleanValue (labels.any (fun label => labelMatches selector label env)) := by
  cases labels with
  | nil => apply value_ext; intro i; have hi : i.val = 0 := by omega
           simp [caseTest, FourState.eval, booleanValue, ofBitVec, fill, hi]
  | cons first rest => exact caseTest_fold_correct selector rest env (.caseEq selector first) _ rfl

theorem eval_boolean_mux {w : Nat} (selector : FourState.Expr 1) (a b : FourState.Expr w)
    (env : FourState.Env) (choose : Bool) (h : FourState.eval selector env = booleanValue choose) :
    FourState.eval (.mux selector a b) env = if choose then FourState.eval a env else FourState.eval b env := by
  cases choose <;> simp [FourState.eval, h, booleanValue, getBit, fill, FourState.mux]

theorem ifTest_valid {w : Nat} (condition : FourState.Expr w) (scope : List (String × Nat))
    (h : condition.valid scope = true) : (ifTest condition).valid scope = true := by
  have hw := valid_width condition scope h
  simp [ifTest, FourState.Expr.valid, h, hw]

theorem caseTest_valid {w : Nat} (selector : FourState.Expr w) (labels : List (FourState.Expr w))
    (scope : List (String × Nat)) (hs : selector.valid scope = true)
    (hl : ∀ label ∈ labels, label.valid scope = true) : (caseTest selector labels).valid scope = true := by
  cases labels with
  | nil => simp [caseTest, FourState.Expr.valid]
  | cons first rest =>
    have hf : (FourState.Expr.caseEq selector first).valid scope = true := by
      simp [FourState.Expr.valid, hs, hl first (by simp)]
    have hr : ∀ label ∈ rest, label.valid scope = true := fun label h => hl label (by simp [h])
    have go (ls : List (FourState.Expr w)) (hl : ∀ l ∈ ls, l.valid scope = true)
        (acc : FourState.Expr 1) (ha : acc.valid scope = true) :
        (ls.foldl (fun acc label => .or acc (.caseEq selector label)) acc).valid scope = true := by
      induction ls generalizing acc with
      | nil => exact ha
      | cons label ls ih =>
        apply ih (fun l h => hl l (by simp [h]))
        simp [FourState.Expr.valid, ha, hs, hl label (by simp)]
    exact go rest hr _ hf


theorem mux_same {w : Nat} (selector : Bit) (a : Value w) : FourState.mux selector a a = a := by
  cases selector with
  | zero => rfl
  | one => rfl
  | x => exact mux_unknown_same a
  | z => exact mux_unknown_same a

end LeanRTL.FourState.Source
