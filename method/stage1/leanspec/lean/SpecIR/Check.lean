import SpecIR.Render

/-!
# `SpecIR.Check` — the obligations, and the bridge to the driver.

Obligations T3 and T4 (totality of `step` and `out`) are discharged by elaboration: a generated
design that forgets a case does not compile, and Lean names the line. This module is about the
ones that need evaluation:

  * **T5 Determined** — no stimulus in the suite reaches a `hole`. A failure carries the stimulus
    index, the cycle, the port and the hole's name, which is everything a question needs.
  * **T6 Property** — an asserted invariant is checked against the machine over the suite, and is
    reported as *entailed*, *violated* (with the first counterexample) or *vacuous* (never once
    exercised). Vacuity matters: a property no stimulus reaches is not evidence of anything, and
    counting it as passing is how a specification acquires guarantees it does not have.

`reportJson` is the only interface the Python driver uses. Findings cross the boundary as data,
never as parsed prose.
-/

namespace SpecIR

structure Finding where
  stimulus : Nat
  cycle    : Nat
  port     : String
  holeId   : String
  source   : Source := .hole
  /-- What the reading committed to, for `conv`/`stru`; empty for a genuine hole. -/
  value    : String := ""
deriving Repr, DecidableEq

/-- An invariant, stated over one row of the trace. `guard` says when the property is *about* this
row; `holds` says whether it is satisfied there. The pair is what makes vacuity detectable. -/
structure Property (σ ι : Type) where
  name  : String
  guard : σ → ι → Bool
  holds : σ → ι → Bool

/-- A provenance-carrying, unbounded functional property.

`Property` above is deliberately retained for bounded T6 evaluation.  `FormalProperty` is the
separate T11 layer: its statement is a proposition over the whole machine, and a generated theorem
must prove or disprove `Holds` rather than merely evaluate it on the stimulus suite. -/
structure FormalProperty (σ ι : Type) where
  id        : String
  className : String
  sources   : List String
  statement : Machine σ ι → Prop
  /-- A separately proved reachability/trigger condition.  Unconditional properties may retain
  the default; conditional properties should state that their antecedent is realizable. -/
  nonvacuous : Machine σ ι → Prop := fun _ => True

namespace FormalProperty

def Holds {σ ι : Type} (p : FormalProperty σ ι) (m : Machine σ ι) : Prop :=
  p.statement m

def Nonvacuous {σ ι : Type} (p : FormalProperty σ ι) (m : Machine σ ι) : Prop :=
  p.nonvacuous m

end FormalProperty

/-- Look up one named observable in an output row.  Formal properties use this helper instead of
depending on a generated list's positional representation. -/
def outputValue? (outs : List (String × Val)) (name : String) : Option Val :=
  (outs.find? fun output => output.1 == name).map Prod.snd

/-- Main-function templates. The caller supplies the actual requirement, not a sampled trace. -/
def TransitionLaw {σ ι : Type} (m : Machine σ ι)
    (guard : σ → ι → Prop) (relation : σ → ι → σ → Prop) : Prop :=
  ∀ s, Reachable m s → ∀ i, guard s i → relation s i (m.step s i)

def OutputLaw {σ ι : Type} (m : Machine σ ι)
    (guard : σ → ι → Prop) (relation : σ → ι → List (String × Val) → Prop) : Prop :=
  ∀ s, Reachable m s → ∀ i, guard s i → relation s i (m.out s i)

def HoldLaw {σ ι α : Type} (m : Machine σ ι)
    (guard : σ → ι → Prop) (projection : σ → α) : Prop :=
  TransitionLaw m guard (fun s _ next => projection next = projection s)

inductive PropVerdict where
  | entailed (witnessed : Nat)
  | violated (stimulus cycle : Nat)
  | vacuous
deriving Repr, DecidableEq

private def esc (s : String) : String :=
  s.foldl (fun acc c =>
    acc ++ (match c with
      | '"'  => "\\\""
      | '\\' => "\\\\"
      | '\n' => "\\n"
      | c    => String.singleton c)) ""

private def jstr (s : String) : String := "\"" ++ esc s ++ "\""

namespace Design

variable {σ ι : Type}

/-- **T5.** Every hole the suite reaches. Empty is the obligation discharged. -/
def scan (d : Design σ ι) (suite : List (List ι)) : List Finding :=
  suite.zipIdx.foldl (fun acc (stim, k) =>
    acc ++ (d.openCells stim).map (fun (c, p, h, src, val) =>
      { stimulus := k, cycle := c, port := p, holeId := h, source := src, value := val })) []

/-- The distinct hole names the suite reaches — the question list, deduplicated. -/
def openCoordinates (d : Design σ ι) (suite : List (List ι)) : List String :=
  (d.scan suite).foldl (fun acc f => if acc.contains f.holeId then acc else acc ++ [f.holeId]) []

/-- **T6.** Check one property over the suite, distinguishing violated from vacuous. -/
def checkProperty (d : Design σ ι) (suite : List (List ι)) (p : Property σ ι) : PropVerdict :=
  let rec go (s : σ) (xs : List ι) (k c seen : Nat) : PropVerdict × Nat :=
    match xs with
    | []        => (.entailed seen, seen)
    | i :: rest =>
      if p.guard s i then
        if p.holds s i then go (d.machine.step s i) rest k (c+1) (seen+1)
        else (.violated k c, seen)
      else go (d.machine.step s i) rest k (c+1) seen
  let rec outer (rem : List (List ι)) (k seen : Nat) : PropVerdict :=
    match rem with
    | []           => if seen == 0 then .vacuous else .entailed seen
    | stim :: rest =>
      match go d.machine.init stim k 0 seen with
      | (.violated a b, _) => .violated a b
      | (_, seen')         => outer rest (k+1) seen'
  outer suite 0 0

/-- One finding per distinct hole — the first stimulus that reaches it. A question needs a
separating input, not every input; emitting all of them turns a 23-coordinate report into a
6000-character wall the driver has to page through. -/
def firstPerHole (d : Design σ ι) (suite : List (List ι)) : List Finding :=
  (d.scan suite).foldl (fun acc f =>
    if acc.any (fun g => g.holeId == f.holeId) then acc else acc ++ [f]) []

/-- Every output cell the suite produces, as JSON: `[[{"port":…,"v":…,"hole":…}, …], …]`,
outer index stimulus, inner index cycle.

This is what makes *agreement between two readings of the same prose* computable. Two extractions
name their states differently and may not even use the same state type, so comparing IRs
syntactically is hopeless; comparing what they emit at the ports on a shared stimulus is not.
A coordinate where two readings disagree is a question whether or not either reading called it a
hole — which is the only way `alu`'s `LUI` is reachable, since there the prose is definite and
definite in the wrong direction. -/
def traceJson (d : Design σ ι) (suite : List (List ι)) : String :=
  "[" ++ String.intercalate "," (suite.map (fun stim =>
    "[" ++ String.intercalate "," ((d.trace stim).map (fun r =>
      "[" ++ String.intercalate "," (r.outs.map (fun (p, v) =>
        "{\"port\":" ++ jstr p ++ ",\"width\":" ++ toString v.width ++
        ",\"v\":" ++ jstr v.render ++
        ",\"bare\":" ++ jstr v.bare ++
        ",\"src\":" ++ jstr v.source.name ++
        ",\"hole\":" ++ (if v.isOpen then "true" else "false") ++ "}")) ++ "]")) ++ "]")) ++ "]"

/-- The runtime input name/order/width schema on every evaluated row.

`renderIn` is generated code and may compute a list after spelling a plausible tuple literal.  A
lexical schema alone can therefore certify `xs.reverse` or a `.map` that replaces an 8-bit value by a
1-bit one.  This trace is deliberately separate from `traceJson`: output agreement keeps its stable
wire format while T1 checks what `renderIn` actually returned. -/
def inputTraceJson (d : Design σ ι) (suite : List (List ι)) : String :=
  "[" ++ String.intercalate "," (suite.map (fun stim =>
    "[" ++ String.intercalate "," ((d.trace stim).map (fun r =>
      "[" ++ String.intercalate "," (r.ins.map (fun (p, v) =>
        "{\"port\":" ++ jstr p ++ ",\"width\":" ++ toString v.width ++ "}")) ++ "]")) ++ "]")) ++ "]"

/-- The whole obligation report, as JSON on one line. This is what the driver reads. -/
def reportJson (d : Design σ ι) (suite : List (List ι))
    (props : List (Property σ ι) := []) : String :=
  let fs := d.firstPerHole suite
  let findings := String.intercalate "," (fs.map (fun f =>
    "{\"stimulus\":" ++ toString f.stimulus ++
    ",\"cycle\":" ++ toString f.cycle ++
    ",\"port\":" ++ jstr f.port ++
    ",\"hole\":" ++ jstr f.holeId ++
    ",\"source\":" ++ jstr f.source.name ++
      ",\"value\":" ++ jstr f.value ++ "}"))
  let pv := String.intercalate "," (props.map (fun p =>
    let v := match d.checkProperty suite p with
      | .entailed n     => "{\"verdict\":\"entailed\",\"witnessed\":" ++ toString n ++ "}"
      | .violated a b   => "{\"verdict\":\"violated\",\"stimulus\":" ++ toString a ++
                           ",\"cycle\":" ++ toString b ++ "}"
      | .vacuous        => "{\"verdict\":\"vacuous\"}"
    "{\"name\":" ++ jstr p.name ++ ",\"result\":" ++ v ++ "}"))
  "{\"design\":" ++ jstr d.name ++
  ",\"timebase\":" ++ jstr (match d.timebase with | .fullCycle => "full" | .halfCycle => "half") ++
  ",\"determined\":" ++ (if fs.isEmpty then "true" else "false") ++
  ",\"open\":[" ++ String.intercalate "," ((d.openCoordinates suite).map jstr) ++ "]" ++
  ",\"findings\":[" ++ findings ++ "]" ++
  ",\"properties\":[" ++ pv ++ "]}"

end Design
end SpecIR
