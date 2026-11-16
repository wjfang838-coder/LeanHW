import SpecIR.Machine
import LeanRTL.Core.Symbolic
import LeanRTL.Core.FourStateClocked
import LeanRTL.Core.FourStateSystem

/-! Version 3 refinement: every implementation choice must satisfy the frozen
specification. Only declared `.x` grants freedom. Missing specification values
never grant freedom. This is a distinct target from FrozenSpecBridge.Equivalent.
-/
namespace FrozenRefinement
open SpecIR
abbrev Oracle := String → Nat
abbrev Outputs := List (String × Val)

inductive All₂ {α β : Type} (R : α → β → Prop) : List α → List β → Prop where
  | nil : All₂ R [] []
  | cons {a b as bs} : R a b → All₂ R as bs → All₂ R (a::as) (b::bs)

@[simp] theorem all₂_nil {α β : Type} (R : α → β → Prop) : All₂ R [] [] := .nil
@[simp] theorem all₂_cons {α β : Type} {R : α → β → Prop} {a b as bs} :
    All₂ R (a::as) (b::bs) ↔ R a b ∧ All₂ R as bs := by
  constructor
  · intro h; cases h with | cons h t => exact ⟨h,t⟩
  · intro h; exact .cons h.1 h.2

def ValueRefines (spec actual : Val) : Prop :=
  match spec, actual with
  | .bits w n, .bits v k => w = v ∧ n = k
  | .x w, .bits v _ | .x w, .x v | .x w, .z v => w = v
  | .z w, .z v => w = v
  | _, _ => False

instance (s a : Val) : Decidable (ValueRefines s a) := by
  cases s <;> cases a <;> simp only [ValueRefines] <;> infer_instance

def OutputsRefine (spec actual : Outputs) : Prop :=
  All₂ (fun s a => s.1 = a.1 ∧ ValueRefines s.2 a.2) spec actual

structure Model (ι : Type) where
  State : Type
  timebase : Timebase
  initial : Oracle → State
  step : State → ι → Oracle → State
  out : State → ι → Oracle → Outputs

def Model.traceFrom {ι : Type} (m : Model ι) (s : m.State)
    (choices : Nat → Oracle) (n : Nat) : List ι → List Outputs
  | [] => []
  | i :: rest => m.out s i (choices n) ::
    m.traceFrom (m.step s i (choices n)) choices (n+1) rest

def specTrace {σ ι : Type} (d : Design σ ι) (s : σ) : List ι → List Outputs
  | [] => []
  | i :: rest => d.machine.out s i :: specTrace d (d.machine.step s i) rest

/-- Explicit physical-width normalization, separately bound in FrozenContract. -/
def normalize {σ ι : Type} (d : Design σ ι) (f : ι → ι) : Design σ ι :=
  {d with renderIn := fun i => d.renderIn (f i), machine := {
    init := d.machine.init
    step := fun s i => d.machine.step s (f i)
    out := fun s i => d.machine.out s (f i)}}

theorem normalize_trace {σ ι : Type} (d : Design σ ι) (f : ι → ι) (s : σ) (xs : List ι) :
    specTrace (normalize d f) s xs = specTrace d s (xs.map f) := by
  induction xs generalizing s with
  | nil => rfl
  | cons i rest ih =>
    change d.machine.out s (f i) :: specTrace (normalize d f) (d.machine.step s (f i)) rest =
      d.machine.out s (f i) :: specTrace d (d.machine.step s (f i)) (rest.map f)
    exact congrArg (List.cons _) (ih _)

/-- No bounded horizon, chosen initialization, reset prefix, or existential oracle. -/
def Refines {σ ι : Type} (d : Design σ ι) (m : Model ι) : Prop :=
  d.timebase = m.timebase ∧ ∀ (initial : Oracle) (choices : Nat → Oracle) (stim : List ι),
    All₂ OutputsRefine (specTrace d d.machine.init stim)
      (m.traceFrom (m.initial initial) choices 0 stim)

structure Certificate {σ ι : Type} (d : Design σ ι) (m : Model ι) where
  timebase : d.timebase = m.timebase
  relation : σ → m.State → Prop
  init : ∀ o, relation d.machine.init (m.initial o)
  step : ∀ s t i o, relation s t → relation (d.machine.step s i) (m.step t i o)
  observe : ∀ s t i o, relation s t → OutputsRefine (d.machine.out s i) (m.out t i o)

theorem Certificate.refines {σ ι : Type} {d : Design σ ι} {m : Model ι}
    (c : Certificate d m) : Refines d m := by
  refine ⟨c.timebase, ?_⟩
  intro initial choices stim
  have go : ∀ xs s t n, c.relation s t →
      All₂ OutputsRefine (specTrace d s xs) (m.traceFrom t choices n xs) := by
    intro xs
    induction xs with
    | nil => intros; exact .nil
    | cons i rest ih =>
      intro s t n h
      exact .cons (c.observe s t i (choices n) h)
        (ih _ _ _ (c.step s t i (choices n) h))
  exact go stim _ _ 0 (c.init initial)

/-- SpecIR.trace and the proof's recursion have identical complete observations. -/
theorem specTrace_eq_trace {σ ι : Type} (d : Design σ ι) (stim : List ι) :
    specTrace d d.machine.init stim = (d.trace stim).map (·.outs) := by
  have go : ∀ xs s n acc,
      (Design.trace.go d s xs n acc).map (·.outs) =
      acc.reverse.map (·.outs) ++ specTrace d s xs := by
    intro xs
    induction xs with
    | nil => intros; simp [Design.trace.go, specTrace]
    | cons i rest ih =>
      intro s n acc
      simpa [Design.trace.go, specTrace, List.append_assoc] using
        ih (d.machine.step s i) (n+1) ({cycle := n, ins := d.renderIn i, outs := d.machine.out s i}::acc)
  simpa [Design.trace] using (go stim d.machine.init 0 []).symm

def inputValues {σ ι : Type} (d : Design σ ι) (i : ι) : LeanRTL.Symbolic.Values :=
  (d.renderIn i).map fun (n,v) => (n, v.nat?.getD 0)

def symbolicOutputs (xs : List (String × Nat × Nat)) : Outputs :=
  xs.map fun (n,w,v) => (n, Val.bits w v)

/-- An omitted cycle clock is implicit in the declared sampling edge, not a
hidden constant-zero input. Explicitly rendered clock levels are retained. -/
def cycleInputs {σ ι : Type} (d : Design σ ι) (m : LeanRTL.Symbolic.Module) (i : ι) :
    LeanRTL.Symbolic.Values :=
  let values := inputValues d i
  match m.core.clock with
  | none => values
  | some name =>
    if (values.lookup name).isSome then values
    else values ++ [(name, if (m.core.regs.head?.map (·.negedge)).getD false then 0 else 1)]

def cycle {σ ι : Type} (d : Design σ ι) (m : LeanRTL.Symbolic.Module) : Model ι where
  State := LeanRTL.Symbolic.Values
  timebase := .fullCycle
  initial := m.initial
  step := fun s i o => m.next s (cycleInputs d m i) o
  out := fun s i o => symbolicOutputs (m.outputs s (cycleInputs d m i) o)

/-- A row observes the state before this row's edge-controlled transition,
matching SpecIR's documented pre-transition sampling convention. -/
def edges {σ ι : Type} (d : Design σ ι) (m : LeanRTL.Symbolic.Module) : Model ι where
  State := LeanRTL.Symbolic.Values × LeanRTL.Symbolic.Values
  timebase := .halfCycle
  initial := fun o => (m.initial o, m.inputs.map fun p => (p.name, 0))
  step := fun s i o => (m.edgeNext s.1 s.2 (inputValues d i) o, inputValues d i)
  out := fun s i o => symbolicOutputs (m.outputs s.1 (inputValues d i) o)

def fourEnv {σ ι : Type} (d : Design σ ι) (i : ι) : LeanRTL.FourState.Env :=
  fun n b => if (LeanRTL.Env.ofList (inputValues d i) n).testBit b then .one else .zero

def fourValue {w : Nat} (v : LeanRTL.FourState.Value w) : Val :=
  if LeanRTL.FourState.known v then .bits w (LeanRTL.FourState.toBitVec v).toNat
  else if (List.finRange w).all (fun i => v i == .z) then .z w else .x w

/-- Mixed unknown vectors conservatively abstract to X; a known spec output
still requires every bit known. Z remains distinct from binary data. -/
def fourOutputs (m : LeanRTL.FourState.Module) (e : LeanRTL.FourState.Env) : Outputs :=
  let env := LeanRTL.FourState.valuesEnv (m.wireValues e) e
  m.outputs.map fun p => (p.name, fourValue (LeanRTL.FourState.eval p.expr env))

def combinational {σ ι : Type} (d : Design σ ι) (m : LeanRTL.FourState.Module) : Model ι where
  State := Unit
  timebase := .fullCycle
  initial := fun _ => ()
  step := fun _ _ _ => ()
  out := fun _ i _ => fourOutputs m (fourEnv d i)

/-- Fixed-zero register initialization for the basic clocked proof scope.
This is an explicit proof boundary: power-up uncertainty and arbitrary
initial-state refinement are outside the claim. -/
def clockedInitial (m : LeanRTL.FourState.NBA.Clocked) (_ : LeanRTL.Symbolic.Oracle) :
    LeanRTL.FourState.NBA.Snapshot :=
  m.states.map fun p => (p.name, List.replicate p.width .zero)

def clocked {σ ι : Type} (d : Design σ ι) (clocks : List String)
    (m : LeanRTL.FourState.NBA.Clocked) : Model ι where
  State := LeanRTL.FourState.NBA.Snapshot × LeanRTL.FourState.Env
  timebase := .halfCycle
  initial := fun o => (clockedInitial m o, fun _ _ => .x)
  step := fun s i _ => (m.step s.1 s.2 (fourEnv d i), fourEnv d i)
  out := fun s i _ =>
    let asyncModel : LeanRTL.FourState.NBA.Clocked := {m with processes := m.processes.map fun p =>
      {p with events := p.events.filter fun e => !(e.name ∈ clocks)}}
    let settled := asyncModel.step s.1 s.2 (fourEnv d i)
    fourOutputs m.combinational (LeanRTL.FourState.valuesEnv settled (fourEnv d i))

/-- Full-cycle adapter for a design whose SpecIR row represents one positive
clock edge.  Outputs are observed after asynchronous controls settle and before
the row's clock edge; the step then performs exactly one low-to-high transition.
Physical clocks omitted from `renderIn` are supplied only by this adapter. -/
def clockedCycle {σ ι : Type} (d : Design σ ι) (clocks : List String)
    (m : LeanRTL.FourState.NBA.Clocked) : Model ι where
  State := LeanRTL.FourState.NBA.Snapshot
  timebase := .fullCycle
  initial := clockedInitial m
  step := fun s i _ =>
    let base := fourEnv d i
    let low : LeanRTL.FourState.Env := fun n b =>
      if n ∈ clocks ∧ b = 0 then .zero else base n b
    let high : LeanRTL.FourState.Env := fun n b =>
      if n ∈ clocks ∧ b = 0 then .one else base n b
    let asyncModel : LeanRTL.FourState.NBA.Clocked := {m with processes := m.processes.map fun p =>
      {p with events := p.events.filter fun e => !(e.name ∈ clocks)}}
    let settled := asyncModel.step s (fun _ _ => .x) low
    m.step settled low high
  out := fun s i _ =>
    let base := fourEnv d i
    let low : LeanRTL.FourState.Env := fun n b =>
      if n ∈ clocks ∧ b = 0 then .zero else base n b
    let asyncModel : LeanRTL.FourState.NBA.Clocked := {m with processes := m.processes.map fun p =>
      {p with events := p.events.filter fun e => !(e.name ∈ clocks)}}
    let settled := asyncModel.step s (fun _ _ => .x) low
    fourOutputs m.combinational (LeanRTL.FourState.valuesEnv settled low)

/-- Full-cycle adapter for a resolved hierarchical design. Top-level inout
ports have distinct external-driver names in the resolved network, so the
alias list maps each external-driver name to its SpecIR port name. The
transition and observation use the resolved System semantics directly. -/
def systemCycle {σ ι : Type} (d : Design σ ι) (clocks : List String)
    (inputAliases : List (String × String))
    (outputNames : List String)
    (m : LeanRTL.FourState.Resolved.System) : Model ι where
  State := LeanRTL.FourState.NBA.Snapshot
  timebase := .fullCycle
  initial := clockedInitial m.lower
  step := fun s i _ =>
    let raw := fourEnv d i
    let base : LeanRTL.FourState.Env := fun n b =>
      match inputAliases.lookup n with
      | some source => raw source b
      | none => raw n b
    let low : LeanRTL.FourState.Env := fun n b =>
      if n ∈ clocks ∧ b = 0 then .zero else base n b
    let high : LeanRTL.FourState.Env := fun n b =>
      if n ∈ clocks ∧ b = 0 then .one else base n b
    let asyncModel : LeanRTL.FourState.Resolved.System :=
      {m with processes := m.processes.map fun p =>
        {p with events := p.events.filter fun e => !(e.name ∈ clocks)}}
    let settled := asyncModel.step s (fun _ _ => .x) low
    m.step settled low high
  out := fun s i _ =>
    let raw := fourEnv d i
    let base : LeanRTL.FourState.Env := fun n b =>
      match inputAliases.lookup n with
      | some source => raw source b
      | none => raw n b
    let low : LeanRTL.FourState.Env := fun n b =>
      if n ∈ clocks ∧ b = 0 then .zero else base n b
    let asyncModel : LeanRTL.FourState.Resolved.System :=
      {m with processes := m.processes.map fun p =>
        {p with events := p.events.filter fun e => !(e.name ∈ clocks)}}
    let settled := asyncModel.step s (fun _ _ => .x) low
    let values := m.wireSnapshot settled low
    let read := LeanRTL.FourState.valuesEnv values low
    (m.network.outputWires.filter fun output => output.name ∈ outputNames).map fun output =>
      (output.name, fourValue (LeanRTL.FourState.eval output.expr read))

/-- Fixed physical sampling interval; the interval belongs to the frozen
contract, never to the implementation author. Time zero is retained. -/
def timed {ι : Type} (sampleFS : Nat) (m : LeanRTL.FourState.Timed.Signal) : Model ι where
  State := Nat
  timebase := .fullCycle
  initial := fun _ => 0
  step := fun t _ _ => t + sampleFS
  out := fun t _ _ => [(m.name, fourValue (w := m.width) ⟨fun i => (m.at t).getD i.val .x⟩)]

end FrozenRefinement
