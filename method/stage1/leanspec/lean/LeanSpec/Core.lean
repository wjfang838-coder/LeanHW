/-!
# LeanSpec — the Lean side of the specification-checking pipeline.

Lean defines the authoritative semantics.  Everything else in this framework (the Python
drivers, the simulator oracle) either *feeds* this file or *reads what it printed*; nothing
else decides what a specification means.

## The one representation

A partial specification is a **relation**, not a function:

    admits : Cfg → Ctx → Obs → Bool

`Cfg` carries the undetermined points, `Ctx` is a legal input context (a driven trace,
projected onto the signals that matter), `Obs` is an observation (the outputs, projected the
same way).  `admits cfg c o` reads: *under the reading `cfg`, the specification permits
observing `o` in context `c`.*

A relation is used rather than a function because the four diagnoses are exactly the four
shapes the admitted set can take, and a function cannot express two of them:

    | admitSet c | = 0   the spec forbids every observation here      -> CONTRADICTION
    | admitSet c | = 1   the spec pins the observation                -> determined
    | admitSet c | > 1   the spec permits several                     -> INCOMPLETENESS
    admitSet differs between two readings at some c                   -> AMBIGUITY
    admitSet agrees at every c                                        -> REDUNDANCY (merge)

`Cfg` distinguishes the two kinds of undetermined point, and the naming is load-bearing —
the Python driver reads the field names:

  * `c_<name>` — a **candidate choice**: an inductive with one constructor per reading the
    prose supports.  The default constructor is the reading the text best supports.
  * `h_<name>` — a **semantic hole**: an `Option`, `none` meaning *no clause constrains this*.
    A hole makes `admits` permissive at that coordinate, which is what makes the freedom
    query see it.  Refinement replaces `none` with `some v` from the ground truth.

Nothing here fills a hole with a default.  A hole left alone shows up as a diagnosis; a hole
given an arbitrary value shows up as nothing at all, which is the failure this file exists to
prevent.

## What a case file must define

    inductive K<Name> ...            one per choice, `deriving DecidableEq, Repr`
    structure Cfg where ...          `c_*` / `h_*` fields, all with defaults
    structure Ctx / structure Obs    `deriving DecidableEq, Repr`
    def ctxUniverse : List Ctx       enumerated in NON-DECREASING `ctxCost` order
    def obsUniverse : List Obs       the projected observation domain
    def ctxCost : Ctx → Nat          trace length, or whatever "shorter witness" means here
    def legal : Ctx → Bool           the environment assumptions, made explicit
    def admits : Cfg → Ctx → Obs → Bool
    def ctxJson : Ctx → String       the witness as simulator stimulus (oracle input)
    def ctxLean : Ctx → String       the same context as a Lean term (certificate subject)
    def obsJson : Obs → String       an observation as JSON (oracle output, and predictions)
    def defaultCfg : Cfg := {}       every choice at the reading the prose best supports
    def case : Case Ctx Obs          the seven above, bundled

The universes are finite and small on purpose: stage 4 requires a witness projected onto the
signals relevant to the difference, so the domain a case enumerates *is* that projection.  A
`decide` over it is then cheap, and every finding below can carry a kernel-checked
certificate rather than a printed claim.

## Printed output is a report; a theorem is the machine's statement

`#eval` lines below print `LEANSPEC:{...}` JSON, which the Python driver parses.  That is a
report of what a search found.  The driver additionally requires, for every finding it keeps,
a `theorem` of the matching shape closed by `decide` plus its `#print axioms` line — see
`diagnose.py`.  A tactic that errors leaves the theorem admitted with a `sorryAx` body and no
`sorry` in the source, so the axiom line is read, not assumed.
-/

namespace LeanSpec

/-! ## A JSON emitter small enough to have no dependencies -/

def jesc (s : String) : String :=
  s.foldl (fun acc ch =>
    acc ++ (match ch with
            | '"'  => "\\\""
            | '\\' => "\\\\"
            | '\n' => "\\n"
            | '\t' => "\\t"
            | '\r' => "\\r"
            | c    => c.toString)) ""

/-- A string, quoted and escaped. -/
def jstr (s : String) : String := "\"" ++ jesc s ++ "\""

def jnat (n : Nat) : String := toString n

def jbool (b : Bool) : String := if b then "true" else "false"

/-- An array of already-rendered JSON fragments. -/
def jarr (xs : List String) : String := "[" ++ String.intercalate "," xs ++ "]"

/-- An object from `(key, already-rendered value)` pairs. -/
def jobj (kvs : List (String × String)) : String :=
  "{" ++ String.intercalate "," (kvs.map (fun kv => jstr kv.1 ++ ":" ++ kv.2)) ++ "}"

/-- The line shape the Python driver greps for.  One finding per line, never wrapped. -/
def emit (payload : String) : IO Unit := IO.println ("LEANSPEC:" ++ payload)

/-! ## The core: admitted sets -/

/-- Everything the reading `adm` permits to be observed in context `c`. -/
def admitSet {C O : Type} (adm : C → O → Bool) (obs : List O) (c : C) : List O :=
  obs.filter (adm c)

def firstWhere {C : Type} (p : C → Bool) : List C → Option C
  | []      => none
  | c :: cs => if p c then some c else firstWhere p cs

/-- `ctxUniverse` must be enumerated shortest-first, or "the shortest separating input"
    is only "the first one the enumeration happened to reach".  Checked, not trusted. -/
def sortedByCost {C : Type} (cost : C → Nat) : List C → Bool
  | []            => true
  | [_]           => true
  | a :: b :: cs  => cost a ≤ cost b && sortedByCost cost (b :: cs)

/-! ## The four queries

Each returns the *first* legal context exhibiting the property, which — given a cost-sorted
universe — is a cheapest witness. -/

/-- **Difference → ambiguity.**  A legal context where two readings admit different sets. -/
def queryDifference {C O : Type} [DecidableEq O]
    (admA admB : C → O → Bool) (obs : List O) (ctxs : List C) (legal : C → Bool) : Option C :=
  firstWhere (fun c => legal c && (admitSet admA obs c ≠ admitSet admB obs c)) ctxs

/-- **Equivalence → redundancy.**  Two readings that agree everywhere in the domain.
    The negation of a difference over the same universe, stated separately because a
    *merge* is an action and a difference is a question. -/
def queryEquivalence {C O : Type} [DecidableEq O]
    (admA admB : C → O → Bool) (obs : List O) (ctxs : List C) (legal : C → Bool) : Bool :=
  ctxs.all (fun c => !legal c || (admitSet admA obs c = admitSet admB obs c))

/-- **Freedom → incompleteness.**  A legal context admitting two distinct observations. -/
def queryFreedom {C O : Type} [DecidableEq O]
    (adm : C → O → Bool) (obs : List O) (ctxs : List C) (legal : C → Bool) : Option C :=
  firstWhere (fun c => legal c && (admitSet adm obs c).length > 1) ctxs

/-- **Deadness → contradiction.**  A legal context admitting nothing at all. -/
def queryDeadness {C O : Type} [DecidableEq O]
    (adm : C → O → Bool) (obs : List O) (ctxs : List C) (legal : C → Bool) : Option C :=
  firstWhere (fun c => legal c && (admitSet adm obs c).isEmpty) ctxs

/-- Two readings admit no observation in common at `c`. -/
def disjointAt {C O : Type} [DecidableEq O]
    (admA admB : C → O → Bool) (obs : List O) (c : C) : Bool :=
  (admitSet admA obs c).all (fun o => !admB c o)

/-- **Difference that an experiment can act on.**  Two readings differing at `c` is not the
    same as a query that can tell them apart.  If their admitted sets merely *differ* but
    overlap, the reference's actual observation may land in the intersection, consistent with
    both, and the query eliminates nothing -- which is what an open hole does to a fork, since
    it widens both sides until they share an observation.

    This finds the cheapest legal context where the two sets differ AND are disjoint: whatever
    the reference does there, at least one reading is refuted.  That is the witness worth
    spending a ground-truth query on, so `emitDifference` prefers it and falls back to a merely
    separating context -- saying which it found -- when no disjoint one exists in the domain. -/
def queryDiscriminating {C O : Type} [DecidableEq O]
    (admA admB : C → O → Bool) (obs : List O) (ctxs : List C) (legal : C → Bool) : Option C :=
  firstWhere (fun c => legal c
                       && (admitSet admA obs c ≠ admitSet admB obs c)
                       && disjointAt admA admB obs c) ctxs

def allPairs {α : Type} : List α → List (α × α)
  | []      => []
  | x :: xs => xs.map (fun y => (x, y)) ++ allPairs xs

/-- The same standard raised from two readings to `n`.  A hole is *pinned* by an experiment at
    `c` only if every one of its values predicts something there (a value predicting nothing is
    refuted by any observation at all, which is a modelling error, not evidence) and no two
    values predict a common observation.  Then whatever the reference shows, at most one value
    survives -- so one query answers the whole hole instead of narrowing it. -/
def pinningAt {C O : Type} [DecidableEq O]
    (pins : List (C → O → Bool)) (obs : List O) (c : C) : Bool :=
  pins.all (fun a => !(admitSet a obs c).isEmpty)
  && (allPairs pins).all (fun p => disjointAt p.1 p.2 obs c)

def queryPinning {C O : Type} [DecidableEq O]
    (pins : List (C → O → Bool)) (obs : List O) (ctxs : List C) (legal : C → Bool) : Option C :=
  firstWhere (fun c => legal c && pinningAt pins obs c) ctxs

/-- Every legal context is determined: exactly one observation admitted.  This is the
    property a *decided* spec has, and stage 5 stops when it holds. -/
def determinedEverywhere {C O : Type}
    (adm : C → O → Bool) (obs : List O) (ctxs : List C) (legal : C → Bool) : Bool :=
  ctxs.all (fun c => !legal c || (admitSet adm obs c).length == 1)

/-! ## Candidate-space splitting (stage 4: witnesses with high information gain) -/

/-- Group candidate tags by the set each admits at `c`: the partition a query at `c` induces
    on the candidate space.  Tags landing in the same group are indistinguishable there. -/
def partitionAt {C O : Type} [DecidableEq O]
    (cands : List (String × (C → O → Bool))) (obs : List O) (c : C) : List (List String) :=
  let step : List (List O × List String) → (String × (C → O → Bool)) → List (List O × List String) :=
    fun groups cand =>
      let s := admitSet cand.2 obs c
      if groups.any (fun g => g.1 = s) then
        groups.map (fun g => if g.1 = s then (g.1, g.2 ++ [cand.1]) else g)
      else groups ++ [(s, [cand.1])]
  (cands.foldl step []).map (·.2)

/-- Size of the largest group: how lopsided the split is.  `1` means every candidate is
    separated; `cands.length` means the query distinguishes nothing. -/
def splitWidth (groups : List (List String)) : Nat :=
  groups.foldl (fun m g => max m g.length) 0

/-- The context that divides the candidate space most evenly, cheapest first.  Ties go to the
    earlier (cheaper) context because `ctxs` is cost-sorted and `<` is strict. -/
def bestSplit {C O : Type} [DecidableEq O]
    (cands : List (String × (C → O → Bool))) (obs : List O) (ctxs : List C) (legal : C → Bool)
    : Option (C × List (List String)) :=
  ctxs.foldl (fun best c =>
    if !legal c then best else
    let g := partitionAt cands obs c
    if g.length ≤ 1 then best else
    match best with
    | none => some (c, g)
    | some (_, gb) => if splitWidth g < splitWidth gb then some (c, g) else best) none

/-! ## The case bundle

Everything a case supplies about its own domain, in one value, so an emitter takes one
argument instead of seven and a case file cannot pass `ctxCost` where `legal` was wanted.

`ctxLean` is the field that makes the certificates possible: a witness is printed *both* as
simulator stimulus (`ctxJson`, what the oracle is driven with) and as a Lean term
(`ctxLean`, what the generated theorem is stated about).  Two renderings of one context, so
the thing the kernel checks and the thing the simulator runs are the same context by
construction rather than by a reader's inspection. -/

structure Case (C O : Type) where
  ctxs    : List C
  obs     : List O
  legal   : C → Bool
  cost    : C → Nat
  ctxJson : C → String
  ctxLean : C → String
  obsJson : O → String

/-! ## Emitters — one line of JSON per finding, for the Python driver -/

/-- A reading that admits nothing at some legal context is not a rival reading, it is a broken
    one.  Reported alongside every difference so the driver can tell the two apart: a
    separation between two live readings is an **ambiguity** (the prose supports both and they
    disagree), while a separation involving a dead reading is a **repair** (the prose as
    written is unsatisfiable, and this is what dropping one clause buys).  Without this the
    contradiction gets counted a second time, once per rival it differs from. -/
def deadSomewhere {C O : Type} [DecidableEq O]
    (cs : Case C O) (adm : C → O → Bool) : Bool :=
  (queryDeadness adm cs.obs cs.ctxs cs.legal).isSome

def emitDifference {C O : Type} [DecidableEq O]
    (cs : Case C O) (name tagA tagB : String) (admA admB : C → O → Bool) : IO Unit :=
  let dA := deadSomewhere cs admA
  let dB := deadSomewhere cs admB
  let disc := queryDiscriminating admA admB cs.obs cs.ctxs cs.legal
  -- Prefer a context the oracle can act on; fall back to a merely separating one, and say so.
  match (match disc with | some c => some c | none => queryDifference admA admB cs.obs cs.ctxs cs.legal) with
  | none   => emit (jobj [("query", jstr "difference"), ("choice", jstr name),
                          ("a", jstr tagA), ("b", jstr tagB), ("separated", jbool false),
                          ("a_dead", jbool dA), ("b_dead", jbool dB)])
  | some c => emit (jobj [("query", jstr "difference"), ("choice", jstr name),
                          ("a", jstr tagA), ("b", jstr tagB), ("separated", jbool true),
                          ("a_dead", jbool dA), ("b_dead", jbool dB),
                          ("discriminating", jbool disc.isSome),
                          ("cost", jnat (cs.cost c)), ("ctx", cs.ctxJson c),
                          ("ctx_lean", jstr (cs.ctxLean c)),
                          ("a_admits", jarr ((admitSet admA cs.obs c).map cs.obsJson)),
                          ("b_admits", jarr ((admitSet admB cs.obs c).map cs.obsJson))])

def emitEquivalence {C O : Type} [DecidableEq O]
    (cs : Case C O) (name tagA tagB : String) (admA admB : C → O → Bool) : IO Unit :=
  emit (jobj [("query", jstr "equivalence"), ("choice", jstr name),
              ("a", jstr tagA), ("b", jstr tagB),
              ("equivalent", jbool (queryEquivalence admA admB cs.obs cs.ctxs cs.legal)),
              ("domain", jnat cs.ctxs.length)])

def emitFreedom {C O : Type} [DecidableEq O]
    (cs : Case C O) (name : String) (adm : C → O → Bool) : IO Unit :=
  match queryFreedom adm cs.obs cs.ctxs cs.legal with
  | none   => emit (jobj [("query", jstr "freedom"), ("cfg", jstr name), ("free", jbool false)])
  | some c => emit (jobj [("query", jstr "freedom"), ("cfg", jstr name), ("free", jbool true),
                          ("cost", jnat (cs.cost c)), ("ctx", cs.ctxJson c),
                          ("ctx_lean", jstr (cs.ctxLean c)),
                          ("admits", jarr ((admitSet adm cs.obs c).map cs.obsJson))])

/-- **A hole's own underconstraint trace.**  The global freedom query says *the spec is loose
    somewhere*; this says *this hole is what is loose here*, by exhibiting a legal context
    where the spec admits more than one observation AND pinning this one hole changes what is
    admitted.  Attribution by construction, rather than by a reader's guess about which of
    several holes caused a wide admitted set.

    The cheapest such context proves the hole is real but need not *answer* it: several of its
    values can predict the same thing there, and then one query only narrows the domain and a
    second round has to ask again.  So when the case supplies the hole's value domain, this
    prefers the cheapest context that is also **pinning** -- where the values are pairwise
    disjoint, so a single observation leaves at most one standing -- and reports which kind it
    found.  Higher information gain per query, at the cost of a longer trace, which is the
    trade `goal.md` asks to be made explicitly rather than silently. -/
def emitHole {C O : Type} [DecidableEq O]
    (cs : Case C O) (name : String) (admFree admPinned : C → O → Bool)
    (pins : List (String × (C → O → Bool)) := []) : IO Unit :=
  let free := fun c => cs.legal c
                       && (admitSet admFree cs.obs c).length > 1
                       && admitSet admFree cs.obs c ≠ admitSet admPinned cs.obs c
  let pinCtx := if pins.isEmpty then none
                else firstWhere (fun c => free c && pinningAt (pins.map Prod.snd) cs.obs c) cs.ctxs
  match (match pinCtx with | some c => some c | none => firstWhere free cs.ctxs) with
  | none   => emit (jobj [("query", jstr "hole"), ("hole", jstr name), ("free", jbool false)])
  | some c => emit (jobj [("query", jstr "hole"), ("hole", jstr name), ("free", jbool true),
                          ("pinning", jbool pinCtx.isSome),
                          ("cost", jnat (cs.cost c)), ("ctx", cs.ctxJson c),
                          ("ctx_lean", jstr (cs.ctxLean c)),
                          ("admits", jarr ((admitSet admFree cs.obs c).map cs.obsJson))])

def emitDeadness {C O : Type} [DecidableEq O]
    (cs : Case C O) (name : String) (adm : C → O → Bool) : IO Unit :=
  match queryDeadness adm cs.obs cs.ctxs cs.legal with
  | none   => emit (jobj [("query", jstr "deadness"), ("cfg", jstr name), ("dead", jbool false)])
  | some c => emit (jobj [("query", jstr "deadness"), ("cfg", jstr name), ("dead", jbool true),
                          ("cost", jnat (cs.cost c)), ("ctx", cs.ctxJson c),
                          ("ctx_lean", jstr (cs.ctxLean c))])

def emitSplit {C O : Type} [DecidableEq O]
    (cs : Case C O) (name : String) (cands : List (String × (C → O → Bool))) : IO Unit :=
  match bestSplit cands cs.obs cs.ctxs cs.legal with
  | none => emit (jobj [("query", jstr "split"), ("choice", jstr name), ("splits", jbool false)])
  | some (c, g) =>
      emit (jobj [("query", jstr "split"), ("choice", jstr name), ("splits", jbool true),
                  ("cost", jnat (cs.cost c)), ("ctx", cs.ctxJson c),
                  ("ctx_lean", jstr (cs.ctxLean c)),
                  ("groups", jarr (g.map (fun grp => jarr (grp.map jstr)))),
                  ("width", jnat (splitWidth g)), ("candidates", jnat cands.length)])

/-- The shape of the domain a diagnosis is relative to.  A finding is only as strong as the
    universe it was searched over, so the universe is reported with the findings, never
    left for a reader to guess. -/
def emitDomain {C O : Type} (cs : Case C O) : IO Unit :=
  emit (jobj [("query", jstr "domain"), ("ctx_total", jnat cs.ctxs.length),
              ("ctx_legal", jnat (cs.ctxs.filter cs.legal).length),
              ("obs_total", jnat cs.obs.length),
              ("cost_sorted", jbool (sortedByCost cs.cost cs.ctxs)),
              ("max_cost", jnat (cs.ctxs.foldl (fun m c => max m (cs.cost c)) 0))])

/-- Stage 5's stopping condition. -/
def emitDecided {C O : Type} [DecidableEq O]
    (cs : Case C O) (name : String) (adm : C → O → Bool) : IO Unit :=
  emit (jobj [("query", jstr "decided"), ("cfg", jstr name),
              ("determined", jbool (determinedEverywhere adm cs.obs cs.ctxs cs.legal)),
              ("free_at", jnat (cs.ctxs.filter (fun c =>
                  cs.legal c && (admitSet adm cs.obs c).length > 1)).length),
              ("dead_at", jnat (cs.ctxs.filter (fun c =>
                  cs.legal c && (admitSet adm cs.obs c).isEmpty)).length)])

/-- The prediction table the oracle is compared against: what each reading says the
    observation is at a context.  Printed for every witness so refinement is a comparison
    against a *recorded* prediction, not against one recomputed after the answer is known. -/
def emitPredict {C O : Type} [DecidableEq O]
    (cs : Case C O) (tag : String) (adm : C → O → Bool) (c : C) : IO Unit :=
  emit (jobj [("query", jstr "predict"), ("tag", jstr tag), ("ctx", cs.ctxJson c),
              ("ctx_lean", jstr (cs.ctxLean c)),
              ("admits", jarr ((admitSet adm cs.obs c).map cs.obsJson))])

/-- **What each value of a hole would look like.**  The freedom query says the spec is loose at
    this coordinate; that is a diagnosis, not yet a repair.  Filling the hole means learning
    *which* value the reference takes, and that is only possible if a prediction was recorded
    per candidate value before the question was asked.

    A case supplies `cfgPins_<hole> : List (String × Cfg)` -- the hole's value domain, labelled
    -- and this prints one prediction per value.  Where the labels' predictions differ, the
    observation pins the hole; where they coincide, the hole is unobservable in this projection
    and the report says so instead of inventing a value. -/
def emitPredictEach {C O : Type} [DecidableEq O]
    (cs : Case C O) (tagPrefix : String) (pins : List (String × (C → O → Bool)))
    (c : C) : IO Unit :=
  pins.forM (fun p => emitPredict cs (tagPrefix ++ "=" ++ p.1) p.2 c)

/-- **The specification extensionally: one line per legal context, with everything it admits
    there.**

    `emitDecided` gives the counts -- determined, free at N, dead at N -- and the counts are what
    a report quotes.  They are not enough to act on: `decided_determined` fails both when a
    context admits several observations and when it admits none, the two mean opposite things,
    and the failure itself does not say which.  Step 07 reads these lines to find a legal context
    whose `admits` is EMPTY, and re-emits the deliverable with `decided_admits_nothing` proved at
    exactly that context.  So the difference between "the prose is still loose here" and "the
    prose contradicts itself and no implementation can satisfy it" is carried by this emitter.

    Nothing here is compared against anything. The agreement sweep that once ran a decided spec
    against a reference implementation is gone and is not coming back -- it is an evaluation, it
    does not exist without an answer key, and this half's premise is that the prose alone is the
    world. This is an enumeration of the specification over its own frame. -/
def emitSweep {C O : Type} [DecidableEq O]
    (cs : Case C O) (adm : C → O → Bool) : IO Unit :=
  for c in cs.ctxs do
    if cs.legal c then
      emit (jobj [("query", jstr "sweep"), ("ctx", cs.ctxJson c),
                  ("ctx_lean", jstr (cs.ctxLean c)),
                  ("admits", jarr ((admitSet adm cs.obs c).map cs.obsJson))])

end LeanSpec
