import LeanRTL.Core.FourStateProcedural

/-! One activation of an untimed, nonblocking-only process. RHS expressions,
conditions and selected addresses observe a fixed pre-activation environment.
Pending updates compose in source order, including overlapping packed writes.
Clock detection, inter-process races and delayed NBA scheduling are separate. -/
namespace LeanRTL.FourState.NBA
open Source Encoding

def patchValue {w k : Nat} (old : Value w) (rhs : Value k) (lo : Nat) : Value w :=
  ⟨fun i => if lo ≤ i.val ∧ i.val < lo+k then getBit rhs (i.val-lo) else old i⟩

def patchBit {w k : Nat} (old : Expr w) (rhs : Expr k) (lo i : Nat) : Expr 1 :=
  if lo ≤ i ∧ i < lo+k then .extract (i-lo) rhs else .extract i old

def patchPrefix {w k : Nat} (old : Expr w) (rhs : Expr k) (lo : Nat) : (n : Nat) → Expr (n+1)
  | 0 => patchBit old rhs lo (w-1)
  | n+1 => .concat (patchPrefix old rhs lo n) (patchBit old rhs lo (w-(n+2)))

def patchExpr {w k : Nat} (old : Expr w) (rhs : Expr k) (lo : Nat) : Expr w :=
  if lo = 0 then
    if h : k = w then h ▸ rhs else match w with
      | 0 => .const 0
      | n+1 => patchPrefix old rhs lo n
  else match w with
    | 0 => .const 0
    | n+1 => patchPrefix old rhs lo n

theorem patch_bit_correct {w k : Nat} (old : Expr w) (rhs : Expr k) (lo i : Nat)
    (hi : i < w) (env : Env) :
    eval (patchBit old rhs lo i) env 0 = patchValue (eval old env) (eval rhs env) lo ⟨i,hi⟩ := by
  by_cases h : lo ≤ i ∧ i < lo+k <;> simp [patchBit, patchValue, eval, getBit, fill, hi, h]

theorem patch_prefix_correct {w k : Nat} (old : Expr w) (rhs : Expr k) (lo : Nat)
    (env : Env) (n : Nat) (hn : n+1 ≤ w) (i : Fin (n+1)) :
    eval (patchPrefix old rhs lo n) env i =
      getBit (patchValue (eval old env) (eval rhs env) lo) (w-(n+1)+i.val) := by
  induction n with
  | zero =>
    have hi : i = 0 := Fin.ext (by have := i.isLt; omega)
    subst i
    simpa [patchPrefix, getBit, show w-1 < w by omega] using
      patch_bit_correct old rhs lo (w-1) (by omega) env
  | succ n ih =>
    simp only [patchPrefix, eval]
    split
    · rename_i h
      have he : i.val = 0 := by omega
      simp [getBit, he, show w-(n+2) < w by omega,
        patch_bit_correct old rhs lo (w-(n+2)) (by omega) env]
    · rename_i h
      have hi : i.val-1 < n+1 := by omega
      have hj : w-(n+1)+(i.val-1) = w-(n+1+1)+i.val := by omega
      simpa [getBit, hi, hj] using ih (by omega) ⟨i.val-1,hi⟩

theorem patch_expr_correct {w k : Nat} (old : Expr w) (rhs : Expr k) (lo : Nat) (env : Env) :
    eval (patchExpr old rhs lo) env = patchValue (eval old env) (eval rhs env) lo := by
  unfold patchExpr
  split
  · rename_i hl
    split
    · rename_i hw
      subst lo; subst k
      apply value_ext; intro i
      simp [patchValue, getBit, i.isLt]
    · apply value_ext; intro i
      cases w with
      | zero => exact Fin.elim0 i
      | succ n => simpa [getBit, i.isLt] using patch_prefix_correct old rhs lo env n (by omega) i
  · apply value_ext; intro i
    cases w with
    | zero => exact Fin.elim0 i
    | succ n => simpa [getBit, i.isLt] using patch_prefix_correct old rhs lo env n (by omega) i


def resizeProof {a b : Nat} (h : a = b) (e : Expr a) : Expr b := h ▸ e

theorem eval_resizeProof {a b : Nat} (h : a = b) (e : Expr a) (env : Env) (i : Fin b) :
    eval (resizeProof h e) env i = eval e env ⟨i.val,by omega⟩ := by subst b; rfl

/-- Bounded static writes retain the old prefix/suffix as whole words. -/
def compactPatchExpr {w k : Nat} (old : Expr w) (rhs : Expr k) (lo : Nat) : Expr w :=
  if hk : k = 0 then old
  else if hb : lo+k ≤ w then
    if hl : lo = 0 then
      if hw : k = w then hw ▸ rhs
      else resizeProof (by omega) (.concat (.slice k (w-k) old) rhs)
    else if hh : lo+k = w then
      resizeProof (by omega) (.concat rhs (.slice 0 lo old))
    else resizeProof (by omega)
      (.concat (.slice (lo+k) (w-(lo+k)) old) (.concat rhs (.slice 0 lo old)))
  else patchExpr old rhs lo

theorem compact_patch_expr_correct {w k : Nat} (old : Expr w) (rhs : Expr k) (lo : Nat) (env : Env) :
    eval (compactPatchExpr old rhs lo) env = patchValue (eval old env) (eval rhs env) lo := by
  unfold compactPatchExpr
  split
  · rename_i hk
    subst k
    apply value_ext
    intro i
    simp only [patchValue,Nat.add_zero]
    split
    · rename_i h; omega
    · rfl
  · rename_i hk
    split
    · rename_i hb
      split
      · rename_i hl
        subst lo
        split
        · rename_i hw
          subst k
          apply value_ext
          intro i
          simp [patchValue,getBit]
        · apply value_ext
          intro i
          rw [eval_resizeProof]
          simp only [eval,patchValue]
          split
          · rename_i hi
            simp [getBit,hi,show 0 ≤ i.val ∧ i.val < 0+k by omega]
          · rename_i hi
            have hsub : i.val-k < w-k := by omega
            have hsum : k+(i.val-k)=i.val := by omega
            simp [getBit,hi,hsub,hsum,i.isLt]
      · rename_i hl
        split
        · rename_i hh
          apply value_ext
          intro i
          rw [eval_resizeProof]
          simp only [eval,patchValue]
          split
          · rename_i hi
            simp [getBit,hi,show ¬(lo ≤ i.val ∧ i.val < lo+k) by omega,i.isLt]
          · rename_i hi
            simp [getBit,show i.val-lo < k by omega,show lo ≤ i.val ∧ i.val < lo+k by omega]
        · rename_i hh
          apply value_ext
          intro i
          rw [eval_resizeProof]
          simp only [eval,patchValue]
          split
          · rename_i hi
            simp only [getBit,hi,↓reduceDIte]
            split
            · rename_i hlo
              simp [show ¬(lo ≤ i.val ∧ i.val < lo+k) by omega,i.isLt]
            · rename_i hlo
              simp [show i.val-lo < k by omega,show lo ≤ i.val ∧ i.val < lo+k by omega]
          · rename_i hi
            have hsub : i.val-(k+lo) < w-(lo+k) := by omega
            have hsum : lo+k+(i.val-(k+lo))=i.val := by omega
            simp [getBit,hsub,hsum,show ¬(lo ≤ i.val ∧ i.val < lo+k) by omega,i.isLt]
    · exact patch_expr_correct old rhs lo env

mutual
  inductive Stmt where
    | skip
    | write : {k : Nat} → String → Nat → Expr k → Stmt
    | seq : Stmt → Stmt → Stmt
    | ite : {k : Nat} → Expr k → Stmt → Stmt → Stmt
    | cases : {k : Nat} → Expr k → Arms k → Stmt
  inductive Arms : Nat → Type where
    | default : {k : Nat} → Stmt → Arms k
    | arm : {k : Nat} → List (Expr k) → Stmt → Arms k → Arms k
end

mutual
  def writeNames : Stmt → List String
    | .skip => []
    | .write name _ _ => [name]
    | .seq a b => writeNames a ++ writeNames b
    | .ite _ yes no => writeNames yes ++ writeNames no
    | .cases _ arms => armNames arms
  def armNames : {k : Nat} → Arms k → List String
    | _, .default stmt => writeNames stmt
    | _, .arm _ stmt rest => writeNames stmt ++ armNames rest
end

mutual
  def stmtValid (scope states : List (String × Nat)) : Stmt → Bool
    | .skip => true
    | @Stmt.write k name lo rhs =>
      rhs.valid scope && match states.lookup name with
        | some width => lo+k ≤ width
        | none => false
    | .seq a b => stmtValid scope states a && stmtValid scope states b
    | .ite condition yes no => condition.valid scope && stmtValid scope states yes && stmtValid scope states no
    | .cases selector arms => selector.valid scope && armsValid scope states arms
  def armsValid (scope states : List (String × Nat)) : {k : Nat} → Arms k → Bool
    | _, .default stmt => stmtValid scope states stmt
    | _, .arm labels stmt rest => labels.all (fun l => l.valid scope) &&
        stmtValid scope states stmt && armsValid scope states rest
end

mutual
  /-- Observe one destination after queued writes commit. `read` never changes. -/
  def execute (stmt : Stmt) (name : String) (read : Env) {w : Nat} (pending : Value w) : Value w :=
    match stmt with
    | .skip => pending
    | .write target lo rhs => if target = name then patchValue pending (eval rhs read) lo else pending
    | .seq a b => execute b name read (execute a name read pending)
    | .ite condition yes no => if truthy (eval condition read) then execute yes name read pending else execute no name read pending
    | .cases selector arms => executeArms selector arms name read pending
  def executeArms {k : Nat} (selector : Expr k) (arms : Arms k) (name : String) (read : Env)
      {w : Nat} (pending : Value w) : Value w :=
    match arms with
    | .default stmt => execute stmt name read pending
    | .arm labels stmt rest =>
      if labels.any (fun label => labelMatches selector label read) then execute stmt name read pending
      else executeArms selector rest name read pending
end

mutual
  def lower (stmt : Stmt) (name : String) {w : Nat} (pending : Expr w) : Expr w :=
    match stmt with
    | .skip => pending
    | .write target lo rhs => if target = name then compactPatchExpr pending rhs lo else pending
    | .seq a b => lower b name (lower a name pending)
    | .ite condition yes no => .mux (ifTest condition) (lower yes name pending) (lower no name pending)
    | .cases selector arms => lowerArms selector arms name pending
  def lowerArms {k : Nat} (selector : Expr k) (arms : Arms k) (name : String)
      {w : Nat} (pending : Expr w) : Expr w :=
    match arms with
    | .default stmt => lower stmt name pending
    | .arm labels stmt rest => .mux (caseTest selector labels) (lower stmt name pending) (lowerArms selector rest name pending)
end

mutual
  theorem lower_correct (stmt : Stmt) (name : String) {w : Nat} (pending : Expr w) (read : Env) :
      eval (lower stmt name pending) read = execute stmt name read (eval pending read) := by
    cases stmt with
    | skip => rfl
    | write target lo rhs => simp only [lower, execute]; split <;> simp [compact_patch_expr_correct]
    | seq a b =>
      change eval (lower b name (lower a name pending)) read = _
      rw [lower_correct b name, lower_correct a name]; rfl
    | ite condition yes no =>
      change eval (.mux (ifTest condition) _ _) read = _
      rw [eval_boolean_mux _ _ _ read _ (ifTest_correct condition read)]
      simp only [execute]
      split
      · exact lower_correct yes name pending read
      · exact lower_correct no name pending read
    | cases selector arms => exact lowerArms_correct selector arms name pending read
  termination_by sizeOf stmt
  theorem lowerArms_correct {k : Nat} (selector : Expr k) (arms : Arms k) (name : String)
      {w : Nat} (pending : Expr w) (read : Env) :
      eval (lowerArms selector arms name pending) read = executeArms selector arms name read (eval pending read) := by
    cases arms with
    | default stmt => exact lower_correct stmt name pending read
    | arm labels stmt rest =>
      change eval (.mux (caseTest selector labels) _ _) read = _
      rw [eval_boolean_mux _ _ _ read _ (caseTest_correct selector labels read)]
      simp only [executeArms]
      split
      · exact lower_correct stmt name pending read
      · exact lowerArms_correct selector rest name pending read
  termination_by sizeOf arms
end

end LeanRTL.FourState.NBA
