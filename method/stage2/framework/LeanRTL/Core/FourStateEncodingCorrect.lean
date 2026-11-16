import LeanRTL.Core.FourStateEncoding
import LeanRTL.Core.Semantics

/-! Arbitrary-width, pointwise preservation lemmas for the four-state encoding
compiler. FourStateCompilerCorrect and FourStateModuleCorrect compose these
local facts into general expression and combinational-module theorems. -/
namespace LeanRTL.FourState.Encoding

def den {w : Nat} (r : Rails w) (env : LeanRTL.Env) : Value w :=
  ⟨fun i => decodeBit ((LeanRTL.eval r.tag env).getLsbD i.val,
                      (LeanRTL.eval r.data env).getLsbD i.val)⟩

def decodeVectors {w : Nat} (tag data : BitVec w) : Value w :=
  ⟨fun i => decodeBit (tag.getLsbD i.val, data.getLsbD i.val)⟩

theorem vectors_equal_iff {w : Nat} (t d u v : BitVec w) :
    decodeVectors t d = decodeVectors u v ↔ t = u ∧ d = v := by
  constructor
  · intro h
    have bits (i : Nat) (hi : i < w) :
        (t.getLsbD i, d.getLsbD i) = (u.getLsbD i, v.getLsbD i) := by
      have point := congrArg (fun a : Value w => a ⟨i, hi⟩) h
      change decodeBit (t.getLsbD i, d.getLsbD i) = decodeBit (u.getLsbD i, v.getLsbD i) at point
      have := congrArg encodeBit point
      simpa only [encode_decode] using this
    constructor
    · apply BitVec.eq_of_getLsbD_eq_iff.mpr
      intro i hi
      exact congrArg Prod.fst (bits i hi)
    · apply BitVec.eq_of_getLsbD_eq_iff.mpr
      intro i hi
      exact congrArg Prod.snd (bits i hi)
  · rintro ⟨rfl, rfl⟩
    rfl

theorem den_equal_iff {w : Nat} (a b : Rails w) (env : LeanRTL.Env) :
    den a env = den b env ↔
      LeanRTL.eval a.tag env = LeanRTL.eval b.tag env ∧
      LeanRTL.eval a.data env = LeanRTL.eval b.data env :=
  vectors_equal_iff _ _ _ _

theorem not_step {w : Nat} (a : FourState.Expr w) (env : LeanRTL.Env) (i : Fin w) :
    den (compile (.not a)) env i = (den (compile a) env i).inv := by
  simp only [den, compile, LeanRTL.eval, BitVec.getLsbD_and, BitVec.getLsbD_not,
    i.isLt, decide_true, Bool.true_and]
  generalize (LeanRTL.eval (compile a).tag env).getLsbD i.val = t
  generalize (LeanRTL.eval (compile a).data env).getLsbD i.val = d
  cases t <;> cases d <;> rfl

theorem and_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) (i : Fin w) :
    den (compile (.and a b)) env i = (den (compile a) env i).band (den (compile b) env i) := by
  simp only [den, compile, active, inactive, LeanRTL.eval, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
  generalize (LeanRTL.eval (compile a).tag env).getLsbD i.val = atag
  generalize (LeanRTL.eval (compile a).data env).getLsbD i.val = adata
  generalize (LeanRTL.eval (compile b).tag env).getLsbD i.val = btag
  generalize (LeanRTL.eval (compile b).data env).getLsbD i.val = bdata
  cases atag <;> cases adata <;> cases btag <;> cases bdata <;> rfl

theorem or_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) (i : Fin w) :
    den (compile (.or a b)) env i = (den (compile a) env i).bor (den (compile b) env i) := by
  simp only [den, compile, active, inactive, LeanRTL.eval, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
  generalize (LeanRTL.eval (compile a).tag env).getLsbD i.val = atag
  generalize (LeanRTL.eval (compile a).data env).getLsbD i.val = adata
  generalize (LeanRTL.eval (compile b).tag env).getLsbD i.val = btag
  generalize (LeanRTL.eval (compile b).data env).getLsbD i.val = bdata
  cases atag <;> cases adata <;> cases btag <;> cases bdata <;> rfl

theorem xor_step {w : Nat} (a b : FourState.Expr w) (env : LeanRTL.Env) (i : Fin w) :
    den (compile (.xor a b)) env i = (den (compile a) env i).bxor (den (compile b) env i) := by
  simp only [den, compile, LeanRTL.eval, BitVec.getLsbD_and,
    BitVec.getLsbD_or, BitVec.getLsbD_xor, BitVec.getLsbD_not, i.isLt, decide_true, Bool.true_and]
  generalize (LeanRTL.eval (compile a).tag env).getLsbD i.val = atag
  generalize (LeanRTL.eval (compile a).data env).getLsbD i.val = adata
  generalize (LeanRTL.eval (compile b).tag env).getLsbD i.val = btag
  generalize (LeanRTL.eval (compile b).data env).getLsbD i.val = bdata
  cases atag <;> cases adata <;> cases btag <;> cases bdata <;> rfl

private theorem merge_decoded (atg adt btg bdt : Bool) :
    decodeBit (atg || (Bool.xor atg btg || Bool.xor adt bdt),
               adt && !(Bool.xor atg btg || Bool.xor adt bdt)) =
      (decodeBit (atg, adt)).merge (decodeBit (btg, bdt)) := by
  cases atg <;> cases adt <;> cases btg <;> cases bdt <;> rfl

theorem mux_step {w : Nat} (s : FourState.Expr 1) (a b : FourState.Expr w)
    (env : LeanRTL.Env) (i : Fin w) :
    den (compile (.mux s a b)) env i =
      FourState.mux (den (compile s) env ⟨0, by decide⟩) (den (compile a) env) (den (compile b) env) i := by
  rcases BitVec.eq_zero_or_eq_one (LeanRTL.eval (compile s).tag env) with ht | ht <;>
    rcases BitVec.eq_zero_or_eq_one (LeanRTL.eval (compile s).data env) with hd | hd
  all_goals
    simp [den, compile, choose, LeanRTL.eval, ht, hd, FourState.mux, decodeBit]
  all_goals try rfl
  all_goals
    simpa [decodeBit] using merge_decoded
      (LeanRTL.eval (compile a).tag env)[i.val]
      (LeanRTL.eval (compile a).data env)[i.val]
      (LeanRTL.eval (compile b).tag env)[i.val]
      (LeanRTL.eval (compile b).data env)[i.val]

end LeanRTL.FourState.Encoding
