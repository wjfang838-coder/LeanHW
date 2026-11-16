import FrozenSpec
set_option autoImplicit false

namespace HandoffContract
/-- Unbounded, exact equivalence with the original Stage 1 trace relation.
No legality implication, finite diagnostic-universe restriction, or assumed law. -/
def Exact : Prop :=
  ∀ (xs : List (Bool × Bool × Bool)) (ys : List Bool),
    admits decidedSpec { steps := xs } { steps := ys } = true ↔
      ys = xs.map SpecIR.Gen.selected
end HandoffContract
