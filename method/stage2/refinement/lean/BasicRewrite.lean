import FrozenRefinement

namespace BasicRewrite
open LeanRTL

def ExprEqual {w : Nat} (a b : Expr w) : Prop := ∀ e, eval a e = eval b e

theorem mux_same {w : Nat} (c : Expr 1) (a : Expr w) :
    ExprEqual (.mux c a a) a := by
  intro e
  simp [eval]

theorem mux_repeat {w : Nat} (c : Expr 1) (a b d : Expr w) :
    ExprEqual (.mux c a (.mux c b d)) (.mux c a d) := by
  intro e
  by_cases h : eval c e = 1#1 <;> simp [eval, h]

/-- Explicit scope projection, not an equivalence claim about asynchronous RTL. -/
def sampledReg (r : Reg) : Reg :=
  { r with
    emitInit := true
    init := if r.emitInit then r.init else 0
    asyncReset := none
    next := match r.asyncReset with
      | none => r.next
      | some (n, hi, v) =>
        .mux (.eq (.var n 1) (.const (if hi then 1 else 0))) (.const v) r.next }

def sampled (m : Symbolic.Module) : Symbolic.Module :=
  { m with core := { m.core with regs := m.core.regs.map sampledReg } }

def supported (m : Symbolic.Module) : Bool :=
  m.cycleValid && m.controlsSupported && m.core.regs.all (fun r => r.asyncLoad.isNone)

def model {σ ι : Type} (d : SpecIR.Design σ ι) (m : Symbolic.Module) :=
  FrozenRefinement.cycle d (sampled m)

open FrozenRefinement

def TraceEqual {ι : Type} (a b : Model ι) : Prop :=
  a.timebase = b.timebase ∧ ∀ initial choices stim,
    a.traceFrom (a.initial initial) choices 0 stim =
    b.traceFrom (b.initial initial) choices 0 stim

structure EqualCertificate {ι : Type} (a b : Model ι) where
  timebase : a.timebase = b.timebase
  relation : a.State → b.State → Prop
  init : ∀ o, relation (a.initial o) (b.initial o)
  step : ∀ s t i o, relation s t → relation (a.step s i o) (b.step t i o)
  observe : ∀ s t i o, relation s t → a.out s i o = b.out t i o

theorem EqualCertificate.traceEqual {ι : Type} {a b : Model ι}
    (c : EqualCertificate a b) : TraceEqual a b := by
  refine ⟨c.timebase, ?_⟩
  intro initial choices stim
  have go : ∀ xs s t n, c.relation s t →
      a.traceFrom s choices n xs = b.traceFrom t choices n xs := by
    intro xs
    induction xs with
    | nil => intros; rfl
    | cons i rest ih =>
      intro s t n h
      simp only [Model.traceFrom, c.observe s t i (choices n) h,
        ih _ _ _ (c.step s t i (choices n) h)]
  exact go stim _ _ 0 (c.init initial)

theorem transfer {σ ι : Type} {d : SpecIR.Design σ ι} {a b : Model ι}
    (spec_to_witness : Refines d b) (imported_to_witness : TraceEqual a b) :
    Refines d a := by
  refine ⟨spec_to_witness.1.trans imported_to_witness.1.symm, ?_⟩
  intro initial choices stim
  rw [imported_to_witness.2 initial choices stim]
  exact spec_to_witness.2 initial choices stim

end BasicRewrite
