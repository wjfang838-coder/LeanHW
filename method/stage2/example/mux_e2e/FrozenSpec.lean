import DecidedSpec
import LeanSpec.Handoff
import SpecIR

/-! Fixed one-bit, stateless MUX profile. The executable output comes only from
Stage 1's frozen relation on singleton observations, not an authored mux function.
HandoffContract.Exact additionally requires equivalence for ALL finite traces. -/
namespace SpecIR.Gen
open SpecIR
structure In where
  a : Nat
  b : Nat
  sel : Nat
  deriving DecidableEq, Repr

def bits (i : In) : Bool × Bool × Bool :=
  (i.a % 2 == 1, i.b % 2 == 1, i.sel % 2 == 1)

def admitted (i : Bool × Bool × Bool) (o : Bool) : Bool :=
  admits decidedSpec { steps := [i] } { steps := [o] }

def selected (i : Bool × Bool × Bool) : Bool :=
  LeanSpec.Handoff.select admitted [false, true] false i

def renderIn (i : In) : List (String × Val) :=
  [("a", Val.mk 1 i.a), ("b", Val.mk 1 i.b), ("sel", Val.mk 1 i.sel)]

def suite : List (List In) := []

def spec : Design Unit In :=
  { name := "TopModule"
    renderIn := renderIn
    machine := { init := ()
                 step := fun _ _ => ()
                 out := fun _ i => [("out", .bits 1 (selected (bits i)).toNat)] } }
end SpecIR.Gen
