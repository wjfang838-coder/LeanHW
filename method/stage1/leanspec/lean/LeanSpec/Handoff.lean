import LeanSpec
import SpecIR.Machine

/-! A checked handoff for finite-observation, stateless specifications.
The executable reference is selected from the frozen relation itself. A caller
must prove totality over every input, not just the diagnostic sample. Stateful
contexts require a separate transition/trace bridge and are not covered here. -/
namespace LeanSpec.Handoff

def select {C O : Type} (adm : C → O → Bool) (observations : List O)
    (fallback : O) (c : C) : O :=
  (observations.find? (adm c)).getD fallback

theorem select_sound {C O : Type} (adm : C → O → Bool)
    (observations : List O) (fallback : O)
    (total : ∀ c, ∃ o ∈ observations, adm c o = true) (c : C) :
    adm c (select adm observations fallback c) = true := by
  unfold select
  cases h : observations.find? (adm c) with
  | none =>
    obtain ⟨o, ho, ha⟩ := total c
    exact False.elim ((List.find?_eq_none.mp h o ho) ha)
  | some o => exact List.find?_some h

/-- No independent output function is authored between diagnosis and proving. -/
def combinational {C O : Type} (name : String) (adm : C → O → Bool)
    (observations : List O) (fallback : O)
    (renderIn : C → List (String × SpecIR.Val))
    (renderOut : O → List (String × SpecIR.Val)) : SpecIR.Design Unit C :=
  { name := name
    renderIn := renderIn
    machine := { init := ()
                 step := fun _ _ => ()
                 out := fun _ c => renderOut (select adm observations fallback c) } }

/-- Functionalization preserves exactly a uniquely determined frozen relation. -/
theorem select_iff {C O : Type} (adm : C → O → Bool)
    (observations : List O) (fallback : O)
    (total : ∀ c, ∃ o ∈ observations, adm c o = true)
    (unique : ∀ c o p, adm c o = true → adm c p = true → o = p)
    (c : C) (o : O) :
    adm c o = true ↔ o = select adm observations fallback c := by
  constructor
  · intro h
    exact unique c o _ h (select_sound adm observations fallback total c)
  · intro h
    subst o
    exact select_sound adm observations fallback total c

end LeanSpec.Handoff
