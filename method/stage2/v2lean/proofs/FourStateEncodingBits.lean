import LeanRTL.Core.FourStateEncoding
import LeanRTL.Core.Semantics

/-! Exhaustive, kernel-checked one-bit compiler lemmas. These establish the actual
encoding compiler on these operators, not yet its arbitrary-width/module theorem. -/
namespace V2Lean.FourStateEncodingBits
open LeanRTL.FourState
open LeanRTL.FourState.Encoding

def sourceEnv (a b s : Bit) : Env := fun n _ =>
  if n == "a" then a else if n == "b" then b else if n == "s" then s else .x

def encodedEnv (a b s : Bit) : LeanRTL.Env := fun n =>
  if n == "t__a" then if (encodeBit a).1 then 1 else 0
  else if n == "d__a" then if (encodeBit a).2 then 1 else 0
  else if n == "t__b" then if (encodeBit b).1 then 1 else 0
  else if n == "d__b" then if (encodeBit b).2 then 1 else 0
  else if n == "t__s" then if (encodeBit s).1 then 1 else 0
  else if n == "d__s" then if (encodeBit s).2 then 1 else 0
  else 0

def agrees (expr : Expr 1) (a b s : Bit) : Prop :=
  let r := Encoding.compile expr
  decodeBit ((LeanRTL.eval r.tag (encodedEnv a b s)).getLsbD 0,
             (LeanRTL.eval r.data (encodedEnv a b s)).getLsbD 0) =
    getBit (LeanRTL.FourState.eval expr (sourceEnv a b s)) 0

theorem not_correct (a b s : Bit) : agrees (.not (.var "a" 1)) a b s := by cases a <;> cases b <;> cases s <;> rfl
theorem and_correct (a b s : Bit) : agrees (.and (.var "a" 1) (.var "b" 1)) a b s := by
  cases a <;> cases b <;> cases s <;> rfl
theorem or_correct (a b s : Bit) : agrees (.or (.var "a" 1) (.var "b" 1)) a b s := by
  cases a <;> cases b <;> cases s <;> rfl
theorem xor_correct (a b s : Bit) : agrees (.xor (.var "a" 1) (.var "b" 1)) a b s := by
  cases a <;> cases b <;> cases s <;> rfl
theorem eq_correct (a b s : Bit) : agrees (.eq (.var "a" 1) (.var "b" 1)) a b s := by
  cases a <;> cases b <;> cases s <;> rfl
theorem caseEq_correct (a b s : Bit) : agrees (.caseEq (.var "a" 1) (.var "b" 1)) a b s := by
  cases a <;> cases b <;> cases s <;> rfl
theorem mux_correct (a b s : Bit) : agrees (.mux (.var "s" 1) (.var "a" 1) (.var "b" 1)) a b s := by
  cases a <;> cases b <;> cases s <;> rfl

#print axioms not_correct
#print axioms and_correct
#print axioms or_correct
#print axioms xor_correct
#print axioms eq_correct
#print axioms caseEq_correct
#print axioms mux_correct
end V2Lean.FourStateEncodingBits
