import SpecIR.Val

/-!
# `SpecIR.Machine` — what a specification denotes.

A specification denotes a machine: an initial state, a total transition function, and a total
output function. "Total" is not an aspiration here — `step` and `out` are Lean functions, so a
case the generated design forgot is a compile error with a source location, which is obligation
**T3/T4** discharged by elaboration rather than by a reviewer noticing.

## The timebase

`timebase` records what one step *is*. Most designs step once per active clock edge. Designs that
use both edges — `freq_divbyodd`, `freq_divbyfrac` — are modelled at **half-cycle** granularity
with a phase bit in the state, because a single-edge Mealy machine simply cannot express "the
output falls 2.5 clock periods after reset is released". Choosing the timebase is a modelling
decision the IR is required to make explicitly rather than leave implied.
-/

namespace SpecIR

inductive Timebase where
  | fullCycle
  | halfCycle
deriving Repr, DecidableEq, Inhabited

/-- The denotation of a specification: a Moore/Mealy machine over `Val`-valued ports. -/
structure Machine (σ ι : Type) where
  init : σ
  step : σ → ι → σ
  out  : σ → ι → List (String × Val)

/-- Every observable in an output row has an explicit value. -/
def OutputsDetermined (outs : List (String × Val)) : Prop :=
  ∀ output ∈ outs, output.2.Determined

/-- Finite reachability from a machine's initial state. -/
inductive Reachable {σ ι : Type} (m : Machine σ ι) : σ → Prop where
  | init : Reachable m m.init
  | step {s : σ} : Reachable m s → (i : ι) → Reachable m (m.step s i)

/-- Level A completeness: outputs are determined over the entire state/input space. -/
def GlobalComplete {σ ι : Type} (m : Machine σ ι) : Prop :=
  ∀ s i, OutputsDetermined (m.out s i)

/-- Level B completeness: outputs are determined over every reachable state and legal input.

The current machine API has no separate legality predicate, so every inhabitant of `ι` is legal.
A later domain-specific input type can encode a narrower legal-input space without changing this
definition. -/
def ReachableComplete {σ ι : Type} (m : Machine σ ι) : Prop :=
  ∀ s, Reachable m s → ∀ i, OutputsDetermined (m.out s i)

theorem GlobalComplete.reachable {σ ι : Type} {m : Machine σ ι}
    (h : GlobalComplete m) : ReachableComplete m := by
  intro s _ i
  exact h s i

/-- A design pairs a machine with the ability to render its own stimulus, so a trace table can
name the inputs that produced each row. -/
structure Design (σ ι : Type) where
  name     : String
  timebase : Timebase := .fullCycle
  machine  : Machine σ ι
  renderIn : ι → List (String × Val)

structure Row where
  cycle : Nat
  ins   : List (String × Val)
  outs  : List (String × Val)
deriving Repr, Inhabited

namespace Design

variable {σ ι : Type}

/-- Run the machine over a stimulus, recording one row per step.

Outputs are sampled **before** the transition, so row `n` is what an observer sees during step
`n` — which is the reading that makes a combinational output and a registered output differ, and
therefore the reading `pulse_detect` turns on. -/
def trace (d : Design σ ι) (stim : List ι) : List Row :=
  let rec go (s : σ) (xs : List ι) (n : Nat) (acc : List Row) : List Row :=
    match xs with
    | []      => acc.reverse
    | i :: rest =>
      let row : Row := { cycle := n, ins := d.renderIn i, outs := d.machine.out s i }
      go (d.machine.step s i) rest (n + 1) (row :: acc)
  go d.machine.init stim 0 []

/-- Every open coordinate this stimulus reaches, as `(cycle, port, id, source)`. Empty means the
specification settled every output it was asked for — obligation **T5** on this stimulus.

"Open" is wider than "hole": a value the reading supplied from a mnemonic or from a paragraph
about internal structure is open too, because the document did not pay for it. That is the whole
difference between a question list of fourteen flag side-channels and one that contains `r`. -/
def openCells (d : Design σ ι) (stim : List ι)
    : List (Nat × String × String × Source × String) :=
  (d.trace stim).foldl (fun acc r =>
    acc ++ r.outs.filterMap (fun (p, v) =>
      match v.openId? with
      | some id => some (r.cycle, p, id, v.source, (v.proposed?).getD "")
      | none    => none)) []

@[inherit_doc openCells]
def holes (d : Design σ ι) (stim : List ι) : List (Nat × String × String) :=
  (d.openCells stim).map (fun (c, p, id, _, _) => (c, p, id))

def determined (d : Design σ ι) (stim : List ι) : Bool :=
  (d.openCells stim).isEmpty

end Design
end SpecIR
