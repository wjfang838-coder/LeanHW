import LeanRTL.Core.Semantics
/-!
# Specification combinators

Shared vocabulary for stating "implementation satisfies specification" theorems.
Combinational correctness is functional equivalence of an output expression with a Lean
spec function; sequential correctness is an inductive invariant preserved by `Module.step`.
-/

namespace LeanRTL

/-- A register environment `r` (over the registers of `m`) satisfies invariant `inv` and the
    invariant is preserved by every step from every input/reset. -/
def Invariant (m : Module) (inv : Env → Prop) : Prop :=
  inv m.initRegs ∧
  ∀ (r inputs : Env) (rst : Bool), inv r → inv (m.step r inputs rst)

/-- Unfold a single combinational output against an input environment. -/
@[simp] def denote {w : Nat} (e : Expr w) (env : Env) : BitVec w := eval e env

end LeanRTL
