import LeanSpec.Core

/-!
# Property checking — what the prose asserts, against what the prose defines.

`Core.lean` asks what the *definitions* leave open: ambiguity, incompleteness, contradiction,
redundancy.  This file asks a different question about the same partial specification, and the
distinction is the reason it is a separate stage rather than a fifth query.

A `choice` or a `hole` is a place the prose **declines to say** something.  A `property` is a
place the prose **says something without defining it** — a guarantee, an invariant, a protocol
obligation, a mutual exclusion, a bound:

    "valid is never high for more than one cycle"
    "ack follows req within two cycles"
    "exactly one of the outputs is asserted"

Such a clause is not a next-state law and it is not an open question.  It is a constraint the
specification places on itself, and it can be wrong in ways the four queries cannot see: it can
contradict the definitions while both remain individually satisfiable, or it can be true of
nothing at all.

## The same finite frame, on purpose

A property is a predicate over the *same* enumerated `Ctx` universe and the *same* finite `Obs`
as `admits`.  Nothing here introduces a temporal logic, a model checker, or a second notion of
what a trace is.  That is a deliberate restriction, not an omission: it means every question
below is closed by `decide` over a finite domain and carries a kernel-checked certificate,
exactly like the four queries.  Temporality lives where it already lived — inside `Ctx`, which
is a driven trace, so "within two cycles" is an ordinary predicate over a context.

A property that cannot be written this way is recorded by the driver as *inexpressible*, with
its reason.  It is never approximated.  An approximated property that passes is worse than no
property at all: it reports a guarantee as checked when what was checked was something else.

## The four checks

    Entailment      does every admitted observation satisfy it?
    Vacuity         is its antecedent reachable under any legal context?
    Pinning         does it eliminate readings?
    Independence    is it already entailed under every reading?

`Entailment` failure is the most serious finding the pipeline can produce.  `queryDeadness`
says a context admits nothing; an entailment failure says the definitions and the guarantees
are mutually inconsistent *while both remain individually satisfiable*.  It cannot be resolved
by choosing a reading — one of the two clauses is wrong — so the designer is asked which, with
the violating trace in hand.
-/

set_option autoImplicit false

namespace LeanSpec

/-! ## The representation

`ante` and `holds` are split rather than folded into one `C → O → Bool` because vacuity is a
question about the antecedent alone.  With `fun c o => !ante c || holds c o` as the only
representation, a property whose antecedent never fires is indistinguishable from one that is
genuinely satisfied everywhere, and that is precisely the confusion this stage exists to
prevent: such a property passes every check and constrains nothing. -/

structure Property (C O : Type) where
  /-- Reported verbatim in findings; the driver keys the prose clause off it. -/
  name  : String
  /-- Where the property has something to say.  `fun _ => true` for an unconditional invariant. -/
  ante  : C → Bool
  /-- What it then requires of the observation. -/
  holds : C → O → Bool

/-! ## Entailment -/

/-- The first admitted observation at `c` that the property forbids, if any.  `none` when the
    antecedent does not fire — a property is not violated where it says nothing. -/
def violationAt {C O : Type}
    (adm : C → O → Bool) (p : Property C O) (obs : List O) (c : C) : Option O :=
  if p.ante c then firstWhere (fun o => !p.holds c o) (admitSet adm obs c) else none

/-- **Entailment → cross-clause contradiction.**  The cheapest legal context, and an observation
    there, that the definitions permit and the guarantee forbids.  Cost-sorted `ctxs` makes this
    a cheapest counterexample rather than the first one the enumeration happened to reach — and
    it is a witness already, so stage 5 has nothing to synthesise for this finding. -/
def violation {C O : Type}
    (adm : C → O → Bool) (p : Property C O) (obs : List O) (ctxs : List C) (legal : C → Bool)
    : Option (C × O) :=
  match firstWhere (fun c => legal c && (violationAt adm p obs c).isSome) ctxs with
  | none   => none
  | some c => (violationAt adm p obs c).map (fun o => (c, o))

def entails {C O : Type}
    (adm : C → O → Bool) (p : Property C O) (obs : List O) (ctxs : List C) (legal : C → Bool)
    : Bool :=
  (violation adm p obs ctxs legal).isNone

/-- Every stated property entailed, everywhere in the domain.  This is the second half of a
    decided spec's acceptance criterion — the first being `determinedEverywhere` — and it is
    what the generated `decided_properties` theorem is stated about. -/
def allEntailed {C O : Type}
    (adm : C → O → Bool) (ps : List (Property C O)) (obs : List O) (ctxs : List C)
    (legal : C → Bool) : Bool :=
  ps.all (fun p => entails adm p obs ctxs legal)

/-! ## Vacuity -/

/-- The cheapest legal context where the antecedent fires: evidence the property is about
    something.  `none` means it is about nothing. -/
def anteReach {C O : Type}
    (p : Property C O) (ctxs : List C) (legal : C → Bool) : Option C :=
  firstWhere (fun c => legal c && p.ante c) ctxs

/-- **Vacuity.**  A property whose antecedent is unreachable is prose describing a situation
    that cannot arise.  It passes entailment, it survives every reading, and it constrains
    nothing — which is exactly why it has to be reported rather than counted as satisfied.

    Relative to the enumerated domain, like every other finding here: an antecedent unreachable
    in this projection may be reachable in a longer trace, so `emitDomain` is printed alongside
    and the driver reports the two together. -/
def vacuous {C O : Type}
    (p : Property C O) (ctxs : List C) (legal : C → Bool) : Bool :=
  (anteReach p ctxs legal).isNone

/-- Stronger than `vacuous`: the antecedent fires somewhere, but nowhere that the specification
    admits an observation for it to constrain.  Non-vacuous by the antecedent test and still
    inert.  Reported separately because the repair differs — the first is a missing scenario in
    the environment assumptions, the second a contradiction upstream in the definitions. -/
def inert {C O : Type}
    (adm : C → O → Bool) (p : Property C O) (obs : List O) (ctxs : List C) (legal : C → Bool)
    : Bool :=
  ctxs.all (fun c => !(legal c && p.ante c) || (admitSet adm obs c).isEmpty)

/-! ## Pinning and independence

A property is checked against the *candidate readings*, not only against one.  This is where
the stage pays for itself: if exactly one reading satisfies a guarantee the prose states, the
prose has answered its own question, and no designer is needed.

That is why this file runs before witness synthesis.  A question the prose already answers must
never reach the designer — asking it invites an answer that contradicts the specification's own
guarantee, and there is nothing downstream that would catch that. -/

/-- The readings that satisfy the property.  Labels come back, not predicates, so the driver can
    name them in the report and in the generated certificate. -/
def survivors {C O : Type}
    (cands : List (String × (C → O → Bool))) (p : Property C O)
    (obs : List O) (ctxs : List C) (legal : C → Bool) : List String :=
  (cands.filter (fun cd => entails cd.2 p obs ctxs legal)).map (·.1)

/-- How a property relates to the candidate space it was checked against.

    * `vacuousP`     — antecedent unreachable; it is about nothing
    * `violatedP`    — no reading satisfies it; the prose contradicts itself
    * `pinningP`     — exactly one reading survives; the prose decided this itself
    * `narrowingP`   — some but not all survive; fewer options to ask about
    * `independentP` — every reading survives; it restates the definitions, so merge, do not ask

    `vacuousP` is checked first: under a `vacuousP` property every reading trivially entails,
    which would otherwise be reported as `independentP` — a property about nothing, recorded as
    a property that agrees with everything. -/
inductive PropStatus where
  | vacuousP
  | violatedP
  | pinningP
  | narrowingP
  | independentP
  deriving DecidableEq, Repr

def statusName : PropStatus → String
  | .vacuousP     => "vacuous"
  | .violatedP    => "violated"
  | .pinningP     => "pinning"
  | .narrowingP   => "narrowing"
  | .independentP => "independent"

def classify {C O : Type}
    (cands : List (String × (C → O → Bool))) (p : Property C O)
    (obs : List O) (ctxs : List C) (legal : C → Bool) : PropStatus :=
  if vacuous p ctxs legal then .vacuousP
  else
    let s := survivors cands p obs ctxs legal
    if s.isEmpty then .violatedP
    else if s.length == cands.length then .independentP
    else if s.length == 1 then .pinningP
    else .narrowingP

/-! ## Emitters — one line of JSON per finding, for the Python driver -/

/-- Entailment under one named reading, with a cheapest counterexample when it fails.  The
    counterexample is printed both as simulator stimulus (`ctx`) and as a Lean term
    (`ctx_lean`), on the same terms as every other witness, so the trace the designer is shown
    and the term the certificate is stated about are the same context by construction. -/
def emitProperty {C O : Type} [DecidableEq O]
    (cs : Case C O) (cfgName : String) (p : Property C O) (adm : C → O → Bool) : IO Unit :=
  match violation adm p cs.obs cs.ctxs cs.legal with
  | none        => emit (jobj [("query", jstr "property"), ("property", jstr p.name),
                               ("cfg", jstr cfgName), ("entailed", jbool true)])
  | some (c, o) => emit (jobj [("query", jstr "property"), ("property", jstr p.name),
                               ("cfg", jstr cfgName), ("entailed", jbool false),
                               ("cost", jnat (cs.cost c)), ("ctx", cs.ctxJson c),
                               ("ctx_lean", jstr (cs.ctxLean c)),
                               ("observation", cs.obsJson o),
                               ("admits", jarr ((admitSet adm cs.obs c).map cs.obsJson))])

/-- Vacuity and inertness, with a reachability witness when the antecedent does fire. -/
def emitPropertyVacuity {C O : Type} [DecidableEq O]
    (cs : Case C O) (cfgName : String) (p : Property C O) (adm : C → O → Bool) : IO Unit :=
  match anteReach p cs.ctxs cs.legal with
  | none   => emit (jobj [("query", jstr "property_vacuity"), ("property", jstr p.name),
                          ("cfg", jstr cfgName), ("vacuous", jbool true), ("inert", jbool true)])
  | some c => emit (jobj [("query", jstr "property_vacuity"), ("property", jstr p.name),
                          ("cfg", jstr cfgName), ("vacuous", jbool false),
                          ("inert", jbool (inert adm p cs.obs cs.ctxs cs.legal)),
                          ("cost", jnat (cs.cost c)), ("ctx", cs.ctxJson c),
                          ("ctx_lean", jstr (cs.ctxLean c))])

/-- The property against the candidate space: which readings survive, and what that makes it.
    A `pinning` result is a question retired without spending an oracle query, and the driver
    turns it into a decision with the property clause as its basis. -/
def emitPropertyPin {C O : Type} [DecidableEq O]
    (cs : Case C O) (p : Property C O) (cands : List (String × (C → O → Bool))) : IO Unit :=
  let s := survivors cands p cs.obs cs.ctxs cs.legal
  emit (jobj [("query", jstr "property_pin"), ("property", jstr p.name),
              ("status", jstr (statusName (classify cands p cs.obs cs.ctxs cs.legal))),
              ("candidates", jarr (cands.map (fun cd => jstr cd.1))),
              ("survivors", jarr (s.map jstr)),
              ("n_candidates", jnat cands.length), ("n_survivors", jnat s.length)])

/-- Stage 6's stopping condition, property half: every stated property entailed under the
    decided reading.  Reported with the count so a run that extracted no properties at all is
    visible as such rather than as a clean pass — `allEntailed` over an empty list is `true`,
    and a specification from which nothing was extracted is a finding about the extraction. -/
def emitPropertiesDecided {C O : Type} [DecidableEq O]
    (cs : Case C O) (cfgName : String) (adm : C → O → Bool) (ps : List (Property C O)) : IO Unit :=
  emit (jobj [("query", jstr "properties_decided"), ("cfg", jstr cfgName),
              ("n_properties", jnat ps.length),
              ("all_entailed", jbool (allEntailed adm ps cs.obs cs.ctxs cs.legal)),
              ("violated", jarr ((ps.filter (fun p =>
                  !entails adm p cs.obs cs.ctxs cs.legal)).map (fun p => jstr p.name))),
              ("vacuous", jarr ((ps.filter (fun p =>
                  vacuous p cs.ctxs cs.legal)).map (fun p => jstr p.name)))])

end LeanSpec
