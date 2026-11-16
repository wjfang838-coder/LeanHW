import SpecIR.Machine
import LeanRTL.Core.Semantics

/-!
# Frozen SpecIR / LeanRTL bridge

This optional module belongs to frozen-input workspaces. It is deliberately outside the
ordinary `LeanRTL` import tree: SpecIR remains a separately versioned specification dependency.

The input encoding, state transition, output widths and sampling time are fixed here; an
implementation author cannot choose an observation function or a latency to make the theorem
true. Equality includes every row, named output, width and `Val` constructor. In particular
`x`, `z` and unresolved values do not become arbitrary concrete bits. The cycle semantics
cannot establish event/subcycle behavior or a half-cycle interpretation: those need a distinct
bridge and are not certified by this proposition.
-/
namespace FrozenSpecBridge
open LeanRTL SpecIR

abbrev Registers := List (String × Nat)

/-- There are no implicit input-domain restrictions: every inhabitant of the frozen input
    type must render concrete bits before the two-state module can consume it. -/
def ConcreteInputs {σ ι : Type} (d : Design σ ι) : Prop :=
  ∀ i, ∀ p ∈ d.renderIn i, ∃ w n, p.2 = Val.bits w n

/-- Encoding is fixed by the frozen renderer, including its declared truncation. The fallback
    is unreachable under `ConcreteInputs`; it is not an interpretation of unknown inputs. -/
def inputValues {σ ι : Type} (d : Design σ ι) (i : ι) : Registers :=
  (d.renderIn i).map fun (n, v) => (n, v.nat?.getD 0)

def initial (m : Module) : Registers :=
  m.regs.map fun r => (r.name, r.init.toNat)

def environment (m : Module) (r : Registers) (i : Registers) : Env :=
  evalWires m.wires (cycleEnv (Env.ofList r) (Env.ofList i) (m.regs.map (·.name)))

def next (m : Module) (r : Registers) (i : Registers) : Registers :=
  let e := environment m r i
  let rst := match m.reset with | some n => Env.ofList i n != 0 | none => false
  m.regs.map fun reg =>
    (reg.name, if rst then reg.init.toNat else (eval reg.next e).toNat)

def outputs (m : Module) (r : Registers) (i : Registers) : List (String × Val) :=
  m.outputs.map fun o => (o.name, Val.bits o.width (eval o.expr (environment m r i)).toNat)

/-- The module's actual cycle transition and complete typed outputs, with the frozen inputs. -/
def design {σ ι : Type} (d : Design σ ι) (m : Module) : Design Registers ι where
  name := m.name
  timebase := .fullCycle
  machine := {
    init := initial m
    step := fun r i => next m r (inputValues d i)
    out := fun r i => outputs m r (inputValues d i) }
  renderIn := d.renderIn

/-- Strict, unbounded full-trace equivalence. No reset prefix, reachability sample bound,
    output mask, alternative parameter domain, or freely chosen latency is permitted. -/
def Equivalent {σ ι : Type} (d : Design σ ι) (m : Module) : Prop :=
  d.timebase = .fullCycle ∧ ConcreteInputs d ∧
  ∀ stim : List ι, d.trace stim = (design d m).trace stim

/-- The local induction obligations. Relations may contain invariants, but initialization
    and preservation must hold for *all* frozen inputs, and every output must agree. -/
structure Certificate {σ ι : Type} (d : Design σ ι) (m : Module) where
  fullCycle : d.timebase = .fullCycle
  concreteInputs : ConcreteInputs d
  relation : σ → Registers → Prop
  init : relation d.machine.init (initial m)
  step : ∀ s r i, relation s r →
    relation (d.machine.step s i) (next m r (inputValues d i))
  observe : ∀ s r i, relation s r →
    d.machine.out s i = outputs m r (inputValues d i)

private theorem trace_go_eq {σ τ ι : Type} (a : Design σ ι) (b : Design τ ι)
    (R : σ → τ → Prop) (hin : a.renderIn = b.renderIn)
    (hstep : ∀ s t i, R s t → R (a.machine.step s i) (b.machine.step t i))
    (hout : ∀ s t i, R s t → a.machine.out s i = b.machine.out t i)
    (xs : List ι) (s : σ) (t : τ) (h : R s t) (n : Nat) (acc : List Row) :
    Design.trace.go a s xs n acc = Design.trace.go b t xs n acc := by
  induction xs generalizing s t n acc with
  | nil => rfl
  | cons i is ih =>
    simp only [Design.trace.go]
    rw [hin, hout s t i h]
    exact ih _ _ (hstep s t i h) _ _

/-- Lift local state/observation correspondence to arbitrary finite traces. -/
theorem Certificate.equivalent {σ ι : Type} {d : Design σ ι} {m : Module}
    (c : Certificate d m) : Equivalent d m := by
  refine ⟨c.fullCycle, c.concreteInputs, ?_⟩
  intro stim
  exact trace_go_eq d (design d m) c.relation rfl c.step c.observe
    stim _ _ c.init 0 []

/-- Numeric projection used only to link the strict typed equality to the existing simulator.
    The main `Equivalent` theorem above does not erase constructors or widths. -/
def numericOutputs (xs : List (String × Val)) : Registers :=
  xs.map fun (n, v) => (n, v.nat?.getD 0)

@[simp] theorem numeric_outputs (m : Module) (r i : Registers) :
    numericOutputs (outputs m r i) = m.outputs?eval (Env.ofList r) (Env.ofList i) := by
  simp [numericOutputs, outputs, Module.outputs?eval, environment, Val.nat?, List.map_map]

/-- A structurally recursive presentation of the same module cycle runner. -/
def run (m : Module) (r : Registers) : List Registers → List Registers
  | [] => []
  | i :: is => m.outputs?eval (Env.ofList r) (Env.ofList i) :: run m (next m r i) is

private theorem run_fold (m : Module) (xs : List Registers) (r : Registers)
    (acc : List Registers) :
    (xs.foldl (fun st i => (next m st.1 i,
      st.2 ++ [m.outputs?eval (Env.ofList st.1) (Env.ofList i)])) (r, acc)).2 =
      acc ++ run m r xs := by
  induction xs generalizing r acc with
  | nil => simp [run]
  | cons i is ih =>
    simp only [List.foldl_cons]
    rw [ih]
    simp [run, List.append_assoc]

theorem run_eq_simulate (m : Module) (xs : List Registers) :
    run m (initial m) xs = m.simulate xs := by
  have h := run_fold m xs (initial m) []
  simpa [Module.simulate, next, environment, initial, Module.outputs?eval] using h.symm

private theorem trace_go_numeric {σ ι : Type} (d : Design σ ι) (m : Module)
    (xs : List ι) (r : Registers) (n : Nat) (acc : List Row) :
    (Design.trace.go (design d m) r xs n acc).map (fun row => numericOutputs row.outs) =
      (acc.reverse.map (fun row => numericOutputs row.outs)) ++
        run m r (xs.map (inputValues d)) := by
  induction xs generalizing r n acc with
  | nil => simp [Design.trace.go, run]
  | cons i is ih =>
    simp only [Design.trace.go]
    rw [ih]
    simp [design, run, List.append_assoc]

/-- The wrapped design is tied to the existing executable `Module.simulate`, not an
    independently authored behavioral implementation. -/
theorem design_trace_simulate {σ ι : Type} (d : Design σ ι) (m : Module)
    (stim : List ι) :
    ((design d m).trace stim).map (fun row => numericOutputs row.outs) =
      m.simulate (stim.map (inputValues d)) := by
  have h := trace_go_numeric d m stim (initial m) 0 []
  simpa [Design.trace, design, run_eq_simulate] using h

/-- Public corollary for linking an accepted strict theorem to the existing simulator. -/
theorem Equivalent.simulate {σ ι : Type} {d : Design σ ι} {m : Module}
    (h : Equivalent d m) (stim : List ι) :
    (d.trace stim).map (fun row => numericOutputs row.outs) =
      m.simulate (stim.map (inputValues d)) := by
  rw [h.2.2 stim]
  exact design_trace_simulate d m stim

/-- Strict equivalence already constrains the first observation, including traces that do
    not begin with reset. Useful for detecting an impossible two-state initial contract. -/
theorem Equivalent.initial_outputs {σ ι : Type} {d : Design σ ι} {m : Module}
    (h : Equivalent d m) (i : ι) :
    d.machine.out d.machine.init i = outputs m (initial m) (inputValues d i) := by
  have ht := congrArg (fun rows : List Row => rows.map (·.outs)) (h.2.2 [i])
  simpa [Design.trace, Design.trace.go, design] using ht

/-- Every output of the two-state module semantics is concrete; undefined and floating
    SpecIR values therefore cannot silently pass the equality proposition. -/
theorem outputs_concrete (m : Module) (r i : Registers) :
    ∀ p ∈ outputs m r i, ∃ w n, p.2 = Val.bits w n := by
  intro p hp
  obtain ⟨o, _, rfl⟩ := List.mem_map.mp hp
  exact ⟨o.width, _, rfl⟩

theorem Equivalent.initial_concrete {σ ι : Type} {d : Design σ ι} {m : Module}
    (h : Equivalent d m) (i : ι) :
    ∀ p ∈ d.machine.out d.machine.init i, ∃ w n, p.2 = Val.bits w n := by
  rw [h.initial_outputs i]
  exact outputs_concrete m _ _

end FrozenSpecBridge
