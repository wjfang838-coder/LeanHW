import LeanRTL.Core.FourStateCompilerCorrect

namespace LeanRTL.FourState.Encoding

/-- Equality only at declared widths. Unused and out-of-range bits are irrelevant. -/
def ScopeAgree (scope : List (String × Nat)) (a b : FourState.Env) : Prop :=
  ∀ name width, scope.lookup name = some width → ∀ i : Fin width, a name i.val = b name i.val

theorem eval_scope_congr {w : Nat} (expr : FourState.Expr w) (scope : List (String × Nat))
    (a b : FourState.Env) (he : ScopeAgree scope a b) :
    expr.valid scope = true → FourState.eval expr a = FourState.eval expr b := by
  induction expr <;> intro hv
  all_goals simp_all [FourState.Expr.valid, FourState.eval]
  funext i
  exact he _ _ hv.2 i

theorem compile_correct_related {w : Nat} (expr : FourState.Expr w)
    (scope : List (String × Nat)) (enc : LeanRTL.Env) (original : FourState.Env)
    (hv : expr.valid scope = true) (he : ScopeAgree scope (decodedEnv enc) original) :
    den (compile expr) enc = FourState.eval expr original :=
  (compile_correct expr scope enc hv).trans (eval_scope_congr expr scope _ _ he hv)

theorem tag_data_names_ne (a b : String) : "t__" ++ a ≠ "d__" ++ b := by
  intro h
  have hh := congrArg (fun s : String => s.toList.head?) h
  simp at hh


def putNat (env : LeanRTL.Env) (name : String) (value : Nat) : LeanRTL.Env :=
  fun n => if n = name then value else env n

def putValue {w : Nat} (env : FourState.Env) (name : String) (value : Value w) : FourState.Env :=
  fun n i => if n = name then getBit value i else env n i

theorem put_tag_agree (scope : List (String × Nat)) (env : LeanRTL.Env)
    (name : String) (value : Nat) (hf : scope.lookup name = none) :
    ScopeAgree scope (decodedEnv (putNat env ("t__" ++ name) value)) (decodedEnv env) := by
  intro n w hn i
  have hne : n ≠ name := by intro h; subst n; simp_all
  simp [decodedEnv, putNat, hne, (tag_data_names_ne name n).symm]

theorem compile_data_fresh {w : Nat} (expr : FourState.Expr w) (scope : List (String × Nat))
    (env : LeanRTL.Env) (name : String) (value : Nat)
    (hv : expr.valid scope = true) (hf : scope.lookup name = none) :
    LeanRTL.eval (compile expr).data (putNat env ("t__" ++ name) value) =
      LeanRTL.eval (compile expr).data env := by
  have h := (compile_correct_related expr scope _ (decodedEnv env) hv
    (put_tag_agree scope env name value hf)).trans (compile_correct expr scope env hv).symm
  exact ((vectors_equal_iff _ _ _ _).mp h).2

theorem put_rails_agree {w : Nat} (scope : List (String × Nat)) (enc : LeanRTL.Env)
    (original : FourState.Env) (name : String) (r : Rails w) (value : Value w)
    (he : ScopeAgree scope (decodedEnv enc) original) (hv : den r enc = value) :
    ScopeAgree ((name,w)::scope)
      (decodedEnv (putNat (putNat enc ("t__" ++ name) (LeanRTL.eval r.tag enc).toNat)
        ("d__" ++ name) (LeanRTL.eval r.data enc).toNat))
      (putValue original name value) := by
  intro n k hn i
  by_cases hname : n = name
  · subst n
    simp only [List.lookup_cons, beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hn
    subst k
    have hb := congrArg (fun v : Value w => v i) hv
    simpa [decodedEnv, putNat, putValue, tag_data_names_ne, getBit, i.isLt, den,
      BitVec.testBit_toNat] using hb
  · have hbeq : (n == name) = false := beq_eq_false_iff_ne.mpr hname
    have hlookup : scope.lookup n = some k := by simpa [List.lookup_cons, hbeq] using hn
    simpa [decodedEnv, putNat, putValue, hname, tag_data_names_ne,
      (tag_data_names_ne name n).symm] using he n k hlookup i

end LeanRTL.FourState.Encoding
