#!/usr/bin/env python3
"""leanSpec — the driver.

    python3 -m leanspec.cli new       <name> --prose FILE [--why "..."]   stage the sandbox
    python3 -m leanspec.cli prompt    <name> --stage 1|2      what the agent is asked to write
    python3 -m leanspec.cli run       <name> [--round N] [--from N] [--to N]
    python3 -m leanspec.cli scaffold  <name> --round N        pre-fill authored/roundN/
    python3 -m leanspec.cli audit     <name> [--against DIR]  the wall, and (optionally) leaks
    python3 -m leanspec.cli ls                                the registry
    python3 -m leanspec.cli report                            one row per case

The single-stage commands are still here and still work, for the times when a step has to be
poked at on its own:

    extract  formalize  diagnose  properties  witness  resolve  verify  snapshot

`run` is the same work with a contract: ten numbered steps, each reading exactly one file (the
previous step's output) and writing exactly one, each declaring whether it may reach the
designer — and the declaration is enforced rather than documented, because a sealed step runs
with `oracle.ask_all` raising.  It ends in the deliverables the per-stage commands never produced: a
decided Lean specification with its proofs, and a decided natural-language one.

Stages 1 and 2 are the agent's; every other stage is the machine's.  The split is not cosmetic:
an agent that could also run the diagnosis could report a finding it did not find, and an agent
that could reach the oracle could answer its own question.

A case that needs more than one round runs the ten steps once per round, under `steps/roundN/`
and `authored/roundN/`.  Round N's step 00 reads round N−1's step 08 — sealed, and carrying the
accumulated questions — rather than its step 09, which is that round's terminal accounting and
has no reader downstream.  `out/` is rewritten by every round and is therefore the last one's.
"""
from __future__ import annotations

import argparse
import json
import os
import sys

if __package__ in (None, ""):                      # allow `python3 leanspec/cli.py ...`
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    __package__ = "leanspec"

from common import adapter, paths, variant
from . import cases, diagnose as diag_mod, leak, leanrun, oracle, patch, \
    pipeline as pipeline_mod, propcheck, refine, report as report_mod, schema, witness

#: What the shell in an authoring session is, stated to the agent because it cannot be inferred.
#: Both stages get the same text because both stages run under the same `Role`, and a note about
#: a grant that is written twice is a note that will eventually describe two different grants.
#:
#: This exists because its absence is expensive and silent.  `common/agent.refusals` reports six
#: refused calls in every one of stage 1's three attempts on `accu` — `python3 -c`, `jq`,
#: `python3 scratch/verify.py` — and stage 2 lost a whole session to the same thing.  An agent
#: cannot tell a wall from a mistake, so it works around the wall, and the working-around is what
#: the hour goes on.  Contains no `{}`, so it survives `.format()` on either prompt.
SHELL_NOTE = """\
The only interpreters this session may run are `lean` and `lake`.  There is no `python3`, no
`jq`, no `node`; a command leading with one is refused before it runs, and the refusal is not
about that particular command — the confinement reads the paths a command names, and an
interpreter names none, so no session here gets one.  Nor is there a way around it: a compound
command is split and each part judged separately.

Read JSON with the `Read` tool and write it with `Write`.  These documents are tens of kilobytes
and `Read` hands you a whole one at once.  Reaching for `python3 -c` to filter one, being
refused, and falling back to `head -c` slices costs you the structure that made it worth reading.
"""

STAGE1_PROMPT = """\
STAGE 1 — SEMANTIC EXTRACTION.  Read {spec} and write {out}.

You are reading a natural-language hardware specification.  You are NOT designing the
hardware, NOT writing Verilog, and NOT allowed to consult a reference implementation, a
testbench, or any other statement of what this design does.  The prose is the whole world.

Produce semantic clauses with provenance, be explicit about what the prose does not say, and
state what the prose claims about itself.

{{"design": "{name}",
  "source": "{spec}",
  "clauses": [
    {{"id": "C1",
      "kind": "interface|parameter|state|transition|timing|reset|priority|concurrency|"
              "protocol|assumption|corner",
      "text": "<the exact quoted text -- prose[span[0]:span[1]] must equal this>",
      "span": [<start>, <end>],
      "reading": "<what it means, one line>",
      "status": "fixed|choice|hole",
      "choice_id": "K1",      // when status is choice
      "hole_id": "H1"}} ],    // when status is hole
  "choices": [
    {{"id": "K1", "name": "<lowercase Lean-safe identifier>",
      "candidates": [{{"tag": "<short_tag>", "reading": "<one line>"}}, ...],
      "default": "<the tag the text best supports>",
      "basis": ["C3"]}} ],
  "holes": [
    {{"id": "H1", "name": "<lowercase Lean-safe identifier>",
      "missing": "<the behaviour no clause determines>",
      "why_required": "<why an implementation cannot avoid deciding it>",
      "candidates": [{{"tag": "<value or short_tag>", "reading": "<one line>"}}, ...],
      "domain": {{"size": <how many values this coordinate can take>,
                 "closed": <true if the candidates above ARE all of them>,
                 "why": "<how you know the size>"}}}} ],
  "properties": [
    {{"id": "P1", "name": "<lowercase Lean-safe identifier>",
      "kind": "invariant|guarantee|exclusion|bound|protocol|liveness",
      "statement": "<what the prose asserts holds of EVERY legal run, one line>",
      "expressible": true,
      "basis": ["C7", "C9"],
      "lean": "fun cfg c o => <a Bool over Cfg, Ctx, Obs>"}} ],
  "ports": [{{"name": "...", "dir": "in|out", "width": "8", "from_clause": "C1"}}]}}

Rules that the checker enforces, so read them as constraints and not as advice:

  * `span` is Python string (Unicode code-point) offsets into the decoded spec text and `prose[start:end]` must equal `text`
    EXACTLY.  Collapsed whitespace, a re-typed table row, a normalised dash -- all fail.
  * Every `choices` entry must be pointed at by some clause's `choice_id`; a fork with no
    clause behind it has no provenance and is rejected.
  * A `choice` is a fork only if the two readings can disagree on an OUTPUT the module has.
    A disagreement about a port's width, name, or existence is not a fork -- record it as a
    clause with `kind: interface`.
  * A `hole` is behaviour an implementation MUST decide and the prose never states.  Do not
    invent two candidate values for it and call it a fork: that is answering your own
    question.
  * A hole's `candidates` are the values the designer will be offered, and `domain` says what
    that list IS.  Every question this framework asks is multiple choice -- nobody is handed a
    blank -- so the option set decides what an answer is worth.  A list that is the whole domain
    (`closed: true`, and `size` must equal the number of candidates) can pin the coordinate: one
    survivor is the value.  A list that is a sample (`closed: false`) cannot: one survivor is one
    survivor among the values offered, and the designer may hold something that was never on the
    menu.  A sample is still worth listing -- two survivors prove the coordinate is FREE however
    the sample was drawn -- but a decision may not be taken on a pin that came out of one, and
    the checker refuses it.
  * So enumerate the domain when you can.  When you cannot -- a 32-bit reset value, say --
    do not guess a shortlist and hope: MEASURE.  Drive the context, read the port, put the
    observed value on the menu, and the pinning is then over a menu that contains the answer.
    Whichever you do, `domain.why` says how you know the size; leaving `domain` out entirely
    says only that you did not check, and the answer is carried with that caveat attached.
  * A `property` is not a reading to choose between.  It is a claim the prose makes about EVERY
    legal run -- "the output is never asserted while reset is held", "the counter never exceeds
    15" -- and it is checked against what the readings admit rather than resolved by asking.  It
    can come back violated, which is the sharpest result this framework produces: the same
    document both states a guarantee and admits a run that breaks it.  A property you cannot
    write over `Cfg`, `Ctx` and `Obs` is recorded with `expressible: false` and a `why`, not
    silently dropped and not approximated.
  * A property's provenance is its own `basis`, listing the clauses it rests on, and that is the
    whole of it.  Do not mark those clauses as anything other than what they are: a clause that
    states a guarantee is usually `fixed`, several properties commonly rest on the same clause,
    and `status` records what is UNDETERMINED about a clause rather than what it asserts.

Do not silently complete anything.  If the prose does not say it, it is a hole.

""" + SHELL_NOTE

STAGE2_PROMPT = """\
STAGE 2 — PARTIAL FORMALIZATION.  Write {out}.

`Partial.lean` is a Lean 4 file, `import LeanSpec` and nothing else (no Mathlib, no Std).
It carries the fixed semantics, the candidate choices and the holes, and it keeps them
distinguishable:

    inductive K<name> where | <tag> | <tag>       -- one per choices[] entry, tags verbatim
      deriving DecidableEq, Repr

    structure Cfg where
      c_<name> : K<name> := .<default tag>        -- one per choice
      h_<name> : Option <T> := none               -- one per hole; `none` means UNCONSTRAINED
      deriving DecidableEq, Repr

    structure Ctx where ... deriving DecidableEq, Repr    -- a driven context, projected onto
    structure Obs where ... deriving DecidableEq, Repr    -- the signals the forks can move

    def ctxUniverse : List Ctx      -- enumerated in NON-DECREASING ctxCost order
    def obsUniverse : List Obs      -- the observations the projection can take
    def ctxCost : Ctx -> Nat        -- what "shorter witness" means here (trace length)
    def legal : Ctx -> Bool         -- the environment assumptions, stated
    def admits : Cfg -> Ctx -> Obs -> Bool     -- THE PARTIAL SPEC, as a relation
    def ctxJson : Ctx -> String     -- {{"steps":[{{"<in>":<int>,...}}, ...]}}
    def ctxLean : Ctx -> String     -- the same context as a Lean term, e.g. "mk 3 5"
    def obsJson : Obs -> String     -- {{"steps":[{{"<out>":<int>,...}}, ...]}}
    def defaultCfg : Cfg := {{}}
    def cfgPin_<hole> : Cfg         -- one per hole: defaultCfg with THAT hole pinned to any
                                    --   in-range probe value, so freedom can be attributed
    def cfgPins_<hole> : List (String × Cfg)   -- the hole's option set, labelled, so a query
                                    --   can PIN it and not merely confirm it is free.
                                    --   The labels must be exactly the `candidates` tags
                                    --   stage 1 listed -- the checker cross-checks them, the
                                    --   way it cross-checks a choice against its inductive.
                                    --   A hole typed `Option K<name>` is closed for free: list
                                    --   every constructor.  A hole typed `Option Nat` is not:
                                    --   a `List Nat` shorter than the port's range is a
                                    --   SAMPLE, and stage 1 has to have said so, because a
                                    --   sample can prove freedom but cannot pin.
    def prop_<name> : Property Ctx Obs   -- one per expressible `properties[]` entry, named
                                    --   exactly as stage 1 named it.  NOT a `Cfg -> Ctx -> Obs
                                    --   -> Bool`: `Property` is a RECORD of `name`, `ante` and
                                    --   `holds`, and it takes no `Cfg` — the reading enters
                                    --   through `admits cfg`, which the checker applies itself.
                                    --   It says what the prose CLAIMS, not what the readings
                                    --   admit; the checker asks whether the second entails the
                                    --   first.
    def properties : List (Property Ctx Obs)   -- EVERY `prop_<name>` above, listed.  `allEntailed`
                                    --   folds over this list, so one left out is a guarantee
                                    --   that reads as checked and never was.
    def case : Case Ctx Obs := {{ ctxs := ctxUniverse, obs := obsUniverse, legal := legal,
                                cost := ctxCost, ctxJson := ctxJson, ctxLean := ctxLean,
                                obsJson := obsJson }}

`admits cfg c o` means: under reading `cfg`, the specification PERMITS observing `o` in
context `c`.  Write it as the conjunction of the clauses, so that

  * a hole left `none` constrains nothing at its coordinate -- several `o` stay admitted,
    which is what makes the freedom query see it;
  * two clauses that cannot both hold admit nothing, which is what makes the deadness query
    see it.

Never fill a hole with a plausible default.  A default here is a finding deleted.

Do not define `decidedCfg`.  It is derived from the decision record after the questions have
been answered, and a hand-written one is a value in the specification that no answer justified.

`probe.json` (in the case directory, not the sandbox) says how a Ctx becomes stimulus.  You do
not write it — it is derived from the extraction's port list before this session starts, and it
is at {out2} for you to READ:

    {{"clock": "clk" | null,
      "reset": {{"name": "rst", "active": 1, "cycles": 2}} | null,
      "inputs": ["..."], "outputs": ["..."],       // names as the PROSE gives them
      "sample": "after_edge"}}

Sampling convention, obeyed by both sides: clk toggles every 5 units from low, step n drives
at 10n and is sampled at 10n+9, i.e. after the edge that saw it.  `ctxJson`'s steps and
`obsJson`'s steps are on that same grid, one entry each, in order.

A `reset` of `null` does not mean the module has no reset.  It means the reset is DRIVEN — it is
a port like any other, it appears in `inputs` and in your `Ctx`, and the trace says when it is
asserted.  The `reset` field is for a preamble the trace does not contain, and holding a reset
both there and in the trace would drive it twice.

Verify with:  lean {out}

`LEAN_PATH` is already set in your environment to the build tree that `import LeanSpec`
resolves against, so run `lean` plainly — do not put an assignment in front of it and do not
name the binary by path.  Both forms are refused before they run.

""" + SHELL_NOTE + """
`LeanSpec` is 639 lines and you may READ it.  The source is:

    {lib}/LeanSpec.lean          what the library exports
    {lib}/LeanSpec/Core.lean     `Case`, the four queries, the emitters
    {lib}/LeanSpec/Property.lean the property checks

Read them rather than probing for the API with `#print`.  Everything the checker will ask of
this file is stated there, and reconstructing it one declaration at a time is the slow way to
learn something already written down.

A tactic that errors still leaves a declaration admitted with a `sorryAx` body and no `sorry`
in the source, so end anything you prove with `#print axioms` and read the output.
"""

# ---------------------------------------------------------------------------- stage 2, in passes
#
# The file above describes is six hundred lines of Lean, and for seven sessions it was asked for
# in one.  Every one of those sessions went the same way: the author read its inputs, entered a
# single turn of fifteen to eighteen thousand thinking tokens, and either came back with an `ls`
# or drew `api_retry`, `error: "unknown"` — which restarts the turn from the beginning and, once
# started, has never once recovered.  `Partial.lean` was a 51-byte stub at the end of all seven.
#
# The prompt used to end with a paragraph asking the author to build the file in passes and
# elaborate between them.  It is the right instruction and it did not happen, and there is a
# reason it could not: an author holding the whole task cannot decide to stop holding it.  So the
# passes moved out of the prose and into the driver, where each one is a separate session with a
# separate context and a `lean` run of its own between them (`leanspec/author.py:PASSES`).
#
# That changes nothing about the artifact or about who judges it.  `Partial.lean` is the same
# file, checked by the same steps 02..05, and no pass is shown anything the single-session author
# was not shown.  What changes is the size of the unit of work a fault can destroy — which is
# architecture, not method.
#
# The ORDER here is load-bearing, and writing it out as gated sessions has now found two places
# where the old paragraph had it wrong.  It put `case` in the same pass as the universes, but
# `Case` is built from `ctxJson`, `ctxLean` and `obsJson`, which came a pass later.  And it put
# `obsUniverse` before `admits`, which asks a session to guess the outputs of a declaration that
# does not exist yet — where guessing short is not a smaller list but a false contradiction,
# since `admitSet` only ever FILTERS `obsUniverse`.  `admits` needs the `Obs` type and nothing
# else from that pass, so it moves ahead of it and `obsUniverse` becomes a reading rather than a
# choice.  Written as prose, either inconsistency is a suggestion an author quietly reorders
# around; written as a sequence of gated sessions, one is a pass that does not elaborate and the
# other is a pass with no way to know it was wrong.
#
# SIX, and it was nine.  A pass costs a whole session — a fresh context, a re-read of the file so
# far, a `lean` run — and that overhead only buys something when the pass is a place a fault could
# have stopped.  Three of the nine were not:
#
#   * `cost` wrote `ctxCost` and `legal`, two total functions over the `Ctx` the previous pass had
#     just declared, needing nothing the previous pass did not already have in context.  235s of
#     session for about fifteen lines that the `types` author was better placed to write.  Merged
#     into `types`.
#   * `pins` wrote `defaultCfg` and the pin menus, whose labels come from the same extraction
#     entries `render`'s emitters are already reading.  Merged into `render`.
#   * `probe` wrote `probe.json`, which is not a judgement at all — see `emit.probe_document`,
#     which reproduces all twenty-one of the documents this method has ever produced from the
#     extraction's port list.  Deleted; the driver writes it.
#
# The other six are kept apart on purpose and merging any of them would be a different claim.
# `ctxs`, `admits`, `obs` and `properties` are each a place where a session decides something the
# prose does not settle, and `types` and `render` are each a shape every later pass is written
# against.  What was removed is session overhead, not gating.
STAGE2_PASSES = (
    ("types", """\
`Cfg`, `Ctx`, `Obs`, any `K<name>` inductives, and then `ctxCost` and `legal`.

`Ctx` is a driven context: a trace of inputs long enough for the fixed semantics to distinguish
the readings.  `Obs` is what the specification lets an observer see of it.  Choose their shapes
now, because every later pass is written against them; a shape chosen to make one clause easy
and the next impossible costs more than it saves.

One field per `choices[]` entry as `c_<name> : K<name>`, one per `holes[]` entry as
`h_<name> : Option <T> := none`, tags verbatim from the extraction.

`ctxCost` and `legal` close the pass.  Both are small total functions over the `Ctx` you have
just written and neither needs anything else, which is why they are here and not in a session of
their own.  `ctxCost` says what "a shorter witness" means here — trace length, ordinarily — and
the next pass's enumeration is ordered by it, so decide it now and state it in a comment.
`legal` states the environment assumptions: the port-width bounds, the reset protocol, anything
the prose assumes of whoever drives this module.  A context that violates them will still be
enumerated and then excluded, so `legal` is where an assumption becomes visible rather than
absent."""),

    ("ctxs", """\
`ctxUniverse` — the finite frame of driven contexts, in NON-DECREASING `ctxCost` order.

This is a CHOSEN frame, not an exhaustive one.  Every query in this method runs over it by
enumeration, and the properties are checked in it, so it has to be small enough to decide and
rich enough to ANSWER the readings the extraction found, not merely to tell them apart.

The test is DISJOINTNESS, and the difference between it and mere difference is the whole value
of the query:

  * two readings whose admitted sets DIFFER at a context can both survive the answer.  The
    oracle runs the design once, and the single observation it reports can land in the
    intersection, consistent with both.  The query is spent and nothing is eliminated.
  * two readings whose admitted sets are DISJOINT at a context cannot.  Whatever is observed
    refutes one of them.

So for each `choices[]` fork, look for a context where the two readings admit NO observation in
common.  For each `holes[]` coordinate, look for a context where the coordinate's values are
PAIRWISE disjoint — a hole is not a two-way fork, it is a domain, and one observation has to
leave at most one value of it standing.

A frame that only separates is not neutral at that coordinate, it is worse than silent: it
spends a query, records an answer, and closes nothing.  Measured across 45 designs, 26 of the 45
separated forks and 78 of the 100 free holes had no disjoint context anywhere in their frame,
and of the 120 hole questions actually put to an oracle, not one came back decided.

WHAT MAKES TWO SETS OVERLAP IS THE OTHER OPEN COORDINATES.  A hole left `none` constrains
nothing at its own coordinate, which widens every reading that quantifies over it — and that is
how two readings of a DIFFERENT coordinate come to share an observation.  The repair is a longer
or richer context: one where the coordinate under question reaches the output at a step the
others cannot.

The order is a claim, not a formatting rule: diagnosis reports the first DISJOINT context it
finds, and falls back to a merely separating one only when the frame holds no disjoint one at
all.  The cost order is what makes the context it asks at the cheapest one that answers.

Write the frame out as a literal list.  Every finding this frame produces is re-proved as a
theorem the KERNEL evaluates, once per finding, with no compilation — so the frame is paid for
dozens of times over, not once, and long traces cost more than numerous short ones because cost
is trace length and the queries fold over every step.

Spend that cost where it buys disjointness, and nowhere else.  A frame that separates every fork
DISJOINTLY at cost 9 is worth more than one that merely separates them all at cost 4: the
enumeration cost is paid once and is bounded, the unanswerable question is paid every round
forever.  The context to drop is the one no coordinate needs for disjointness."""),

    ("admits", """\
`admits : Cfg -> Ctx -> Obs -> Bool`, the declaration that carries the specification.

Write it as the conjunction of the clauses, ONE CLAUSE AT A TIME, and elaborate between them.
This is the most expensive declaration to find a type error in late and the only one where a
wrong turn is a wrong specification rather than a wrong encoding.

A hole left `none` must constrain nothing at its coordinate; two clauses that cannot both hold
must admit nothing.  Never fill a hole with a plausible default — a default here is a finding
deleted, and it is deleted invisibly."""),

    ("obs", """\
`obsUniverse` — the observations the queries range over.

This one is DERIVED, not invented.  Every query in `LeanSpec.Core` runs through

    admitSet adm obs c = obs.filter (adm c)

so `obsUniverse` is the entire search space, and an observation missing from it is not admitted
by anything.  A reading whose output is absent from this list is eliminated by an omission; a
context whose only admitted observations are absent is reported as a CONTRADICTION that the prose
does not contain.

So the rule is mechanical: READ THE `admits` YOU JUST WROTE, and for every `Cfg` reading and every
`c` in `ctxUniverse` with `legal c`, every `o` for which `admits cfg c o` is true must appear
here.  Then add nothing else — an observation no reading admits anywhere is dead weight in every
enumeration.  Finite, and on the same grid as `ctxUniverse`.

DERIVED describes how you FIND the entries, not how you write them down.  What goes in the file
is a literal list of `Obs` values.  Do not write a predictor and fold it over the readings and
the contexts; do not build the list by comprehension or by `List.map` over something else.  Run
that computation yourself, read off what it produced, and paste the answer.

The reason is the one thing about this pipeline that is invisible from inside this pass.  Every
finding is re-proved as a theorem discharged by `decide +kernel`, and the kernel evaluates what
the term says — with none of the compilation `#eval` gets.  A literal list is read.  A computed
one is RE-DERIVED FROM SCRATCH INSIDE EVERY CERTIFICATE, and there are dozens of them.  A file
that elaborates in seconds and diagnoses in under a minute can then fail to certify a single
theorem in forty, at which point nothing is proved, the run is rejected, and the message you get
back names theorems that were never reached.  It has happened, and the tell is exactly this: a
fast diagnosis and a certificate file killed at the wall clock.

If that set is too large to list, the `Obs` projection is too wide: say so in a comment and
narrow it to the signals the clauses actually constrain.  Too large to list is the signal to make
it smaller, never the signal to compute it."""),

    ("render", """\
`ctxJson`, `ctxLean`, `obsJson`, then `defaultCfg` and the pin menus.

The first three are the emitters a witness is written with, so they are prose about a value and
have to round-trip: `ctxLean` must produce a term that elaborates back to the context it was
given.

Do NOT write `case`.  The driver appends it when the passes are finished, because its seven
bindings have no second value they could take and writing them here is what made this pass wait
for `obsUniverse`.  Nothing you write in this pass may refer to `case`; nothing needs to.

Then `defaultCfg`, and `cfgPin_<hole>` and `cfgPins_<hole>` one hole at a time.
`cfgPins_<hole>`'s labels must be exactly the `candidates` tags the extraction listed; the
checker cross-checks them.  A hole typed `Option K<name>` is closed, so list every constructor;
a hole typed `Option Nat` may be a sample, and the extraction has to have said so."""),

    ("properties", """\
`prop_<name>`, one per expressible `properties[]` entry, named exactly as the extraction named
it, one at a time — and then `properties`, the list of all of them.

Each one is a `Property Ctx Obs`, which is a RECORD and not a predicate:

    def prop_<name> : Property Ctx Obs :=
      { name  := "<name>"          -- verbatim from the extraction; findings are keyed on it
      , ante  := fun c => ...      -- WHERE the property has something to say
      , holds := fun c o => ... }  -- what it then requires of the observation

    def properties : List (Property Ctx Obs) := [prop_<a>, prop_<b>, ...]

Two things about that shape are load-bearing and neither is guessable from the name.

`ante` and `holds` are SEPARATE, and folding them into `fun c o => !ante c || holds c o` is the
one rewrite that must not happen.  Vacuity is a question about the antecedent alone, and once it
is folded in, a property whose antecedent never fires is indistinguishable from one satisfied
everywhere — it passes every check and constrains nothing.  An unconditional invariant is
`ante := fun _ => true`, written out, not folded.

There is NO `Cfg` argument.  The reading enters through `admits cfg`, which the checker applies
itself: it asks `entails (admits defaultCfg) prop_<name> ...` and, for pinning, runs the same
property against each candidate `Cfg`.  A property that takes a `Cfg` cannot be put to either
question.

Nor can one that has a `Cfg` folded into it by a helper.  `properties` must hold the `prop_`
declarations THEMSELVES — bare identifiers, nothing applied to anything — and the checker
enforces it.  The rewrite this rules out is subtle enough to be worth naming, because it type-
checks and reads as careful:

    def asProperty (name) (ante) (p : Cfg -> Ctx -> Obs -> Bool) : Property Ctx Obs :=
      { name := name, ante := ante,
        holds := fun c o => candidates.any (fun cfg => p cfg c o) }   -- NO

`holds` now means "true under SOME reading".  Pinning then varies the readings against a claim
that already contains all of them, so every candidate survives whatever the prose said, and the
mechanism that retires a question WITHOUT asking the designer is silently switched off.

The reason that rewrite looks necessary is a conflation of two different emitters, so be clear
about which one you are worried about.  `emitProperty` asks whether ONE reading entails the
claim, and a failure there is the serious finding — the prose contradicting itself.
`emitPropertyPin` asks the claim against EVERY candidate and reports who survives, and a claim
that fails under one reading and holds under another is not a contradiction at all: it is the
best outcome available, because it eliminates a candidate and closes a question with no oracle
query at all.

So a property that discriminates between the readings is exactly what this section is for.
State the claim the way the prose states it, at whatever cycle and in whatever terms the prose
uses, and let the readings fall where they fall.  Do not soften it to survive every candidate,
and do not pick a candidate and state it there — the first makes pinning vacuous, the second
reports the other reading as violating a claim the prose never made.

`properties` must list every `prop_` you defined.  `allEntailed` folds over that list, so a
definition written and then left out is a guarantee that reads as checked and never was.

A property says what the prose CLAIMS.  It is not a restatement of `admits` and it is not
allowed to be true by construction: the checker asks whether the readings entail it, and a
property written out of `admits` makes that question answer itself.  An entry the extraction
marked `expressible: false` gets no definition here."""),
)

#: How a pass is asked for.  `{n}`/`{of}` are there so the session can tell how much of the file
#: is behind it, `{state}` is either the note that the file does not exist yet or the instruction
#: to read what the previous passes left, and `{out}` is the file every pass writes.
#:
#: The check that ends a pass used to be a `{verify}` slot with two fillings, because the ninth
#: pass wrote `probe.json` instead of Lean and had to be told to leave `Partial.lean` alone.  That
#: pass is gone — the driver derives the document — so there is one ending, written out here.
PASS_PROMPT = """\

PASS {n} OF {of}.  {state}

In this pass you add exactly this and nothing else:

{adds}

Then run `lean {out}` and read what it says.
A pass ends when the file elaborates with no error and no `sorryAx`; if it does not, fix what
Lean named before you stop, because the next pass is a different session and will inherit
whatever you leave.

Do not write declarations belonging to a later pass, and do not leave a stub for one.  An empty
`def` that elaborates is worse than a missing one: the pass that was supposed to write it will
find it already there.
"""


def _case(name: str) -> cases.Case:
    return cases.find(name)


# ------------------------------------------------------------------------------ commands

def cmd_new(a) -> int:
    """Create a case from a file of prose.

    The specification is *copied* into the sandbox and the copy is what every step reads.  The
    origin is recorded and never re-read: a run whose later steps went back to the source file
    would be a run against a document that can move underneath it, and its byte-exact clause
    spans would silently stop meaning anything.

    `--bench` decides which directory under `data/part1/` the case lands in.  Left unset it is
    inferred from the design name, because the datasets already know who owns which key and
    making the caller repeat it is how the two answers drift apart.  Inference is by the case's
    LEADING dotted component: this run is `accu.c5`, not `accu`, and the suffix is a note about
    which method version produced it rather than part of any design's name.
    """
    variant.require("a new case")
    if not os.path.isfile(a.prose):
        print(f"{a.prose}: no such file", file=sys.stderr)
        return 2
    with open(a.prose, errors="replace") as f:
        text = f.read()
    bench = a.bench or adapter.bench_for_key(a.name.split(".")[0])
    case = cases.register(cases.Case(name=a.name, source=os.path.abspath(a.prose), why=a.why,
                                     bench=bench))
    p = cases.stage_sandbox(case, text)
    print(f"{case.name}: sandbox at {os.path.relpath(case.sandbox)} "
          f"({os.path.getsize(p)} bytes of prose, and nothing else)")
    print(f"  bench  {case.bench or paths.LOCAL}"
          + ("" if case.bench else "   (no installed benchmark claims this name)"))
    print(f"  sha256 {cases.sha256(text)}")
    return 0


def cmd_prompt(a) -> int:
    """Print the prompt the driver would actually send, by asking the driver for it.

    This used to render `STAGE{1,2}_PROMPT` itself, with its own idea of where the outputs go —
    `sandbox/Partial.lean`, `case.path("probe.json")` — while `author.prompt_for` used
    `authored/round<N>/`.  So the prompt a reader inspected named different files from the one
    the agent received, which makes this subcommand worse than useless for the thing it exists
    for: checking that a prompt asks for something the run can actually provide.  That is the
    same drift as a grant and a prompt disagreeing (`docs/ARCHITECTURE.md`, "the third wall"),
    and it is closed the same way — there is now one renderer and this calls it.

    Imported here rather than at module scope: `author` imports this module for the prompt text.
    """
    from leanspec import author                                          # noqa: PLC0415
    case = _case(a.name)
    tag = "extraction" if a.stage == 1 else "formalization"
    ph = next(p for p in author.PHASES if p.tag == tag)
    if a.pss and not ph.passes:
        print(f"stage {a.stage} is written in one session; it has no passes", file=sys.stderr)
        return 2
    print(author.prompt_for(case, ph, a.round, pss=a.pss))
    return 0


def cmd_extract(a) -> int:
    case = _case(a.name)
    with open(case.path("extraction.json")) as f:
        doc = json.load(f)
    errs = schema.validate_extraction(doc, cases.prose(case))
    for e in errs:
        print("  " + e, file=sys.stderr)
    cases.log(case, "extract", ok=not errs, clauses=len(doc.get("clauses", [])),
              choices=len(doc.get("choices", [])), holes=len(doc.get("holes", [])),
              properties=len(doc.get("properties", [])))
    print(f"{case.name}: {len(doc['clauses'])} clause(s), {len(doc['choices'])} choice(s), "
          f"{len(doc['holes'])} hole(s), {len(doc.get('properties', []))} propert(ies), "
          f"{len(errs)} schema error(s)")
    return 1 if errs else 0


def cmd_formalize(a) -> int:
    case = _case(a.name)
    with open(case.path("extraction.json")) as f:
        ext = json.load(f)
    with open(case.path("sandbox", "Partial.lean"), errors="replace") as f:
        src = f.read()
    with open(case.path("probe.json")) as f:
        probe = json.load(f)
    errs = schema.check_partial(src, ext) + schema.validate_probe(probe, ext)
    res = leanrun.run(case.path("sandbox", "Partial.lean"), emit_olean=True)
    with open(case.path("formalize.log"), "w") as f:
        f.write(res["log"])
    for e in errs + res["errors"][:20]:
        print("  " + e, file=sys.stderr)
    if res["admitted"]:
        print(f"  ADMITTED (rests on sorryAx): {', '.join(res['admitted'])}", file=sys.stderr)
    ok = not errs and res["ok"]
    cases.log(case, "formalize", ok=ok, lean=leanrun.summarize(res))
    print(f"{case.name}: {leanrun.summarize(res)}  structural={len(errs)} error(s)")
    return 0 if ok else 1


def cmd_diagnose(a) -> int:
    out = diag_mod.diagnose(_case(a.name))
    print(json.dumps({k: v for k, v in out.items()
                      if k in ("ok", "counts", "lean", "structural_errors", "uncertified",
                               "errors", "warnings")}, indent=1))
    return 0 if out["ok"] else 1


def cmd_properties(a) -> int:
    out = propcheck.check(_case(a.name))
    for r in out["properties"]:
        print(f"  {r['name']:28} {r['status']:14} entailed={r['entailed']} "
              f"vacuous={r['vacuous']} survivors={r.get('survivors')}")
    for q in out.get("inexpressible", []):
        print(f"  {q['name']:28} inexpressible   {q.get('why', '')}")
    print(json.dumps(out["counts"], indent=1))
    return 0 if out["ok"] else 1


def cmd_witness(a) -> int:
    doc = witness.build(_case(a.name))
    for w in doc["witnesses"]:
        print(f"  {w['id']:38} cost={w['cost']} steps={w['complexity']['steps']} "
              f"signals={w['complexity']['signals']} cert={w['certificate']}")
    for s in doc.get("retired_by_property", []):
        print(f"  {s['id']:38} retired by `{s['retired_by_property']}` "
              f"-> {s['resolved_to']}")
    print(json.dumps(doc["totals"], indent=1))
    return 0


def _oracle_flag(s) -> None:
    """`--oracle`, on the two commands that can put a question.

    Default `designer`, which is guard 1: a run that does not name an authority gets the one the
    method is about, and the benchmark backend cannot be arrived at by omission.  It is a flag and
    not a config value or an environment variable for the same reason -- an answer key that could
    be switched on by something already in the shell would make "was this a designer run?" a
    question about the operator's environment rather than about the command that was run.

    `--oracle rtl` says: answer from the benchmark's own implementation of this design, by
    simulating it.  What comes out is an evaluation artifact -- a specification MEASURED against
    an implementation, not one decided by its author -- and `oracle.py`'s module docstring records
    what that costs, chiefly that a reference can never answer "any" and so pins coordinates a
    designer would have declared free.
    """
    s.add_argument("--oracle", choices=sorted(oracle.FLAG_KINDS), default="designer",
                   help="who answers the questions (default: designer).  `rtl` answers from the "
                        "benchmark's reference implementation by simulating it, and labels every "
                        "artifact of the run as measured rather than authored")


def _asking(a) -> str:
    """Set the process's oracle from `--oracle`, and say so on stderr when it is not the default.

    Printed rather than left in the artifacts alone.  The artifacts are guards 2 and 3 and they
    are for the reader afterwards; this is for the operator, now, before an hour of simulation --
    a `--oracle rtl` typed by habit into a run meant to be a real one is worth catching at the
    start of it.
    """
    kind = oracle.FLAG_KINDS[getattr(a, "oracle", "designer")]
    oracle.ask_with(kind)
    if kind != oracle.KIND_DESIGNER:
        print(f"oracle: {kind} -- this run's answers come from the benchmark's reference "
              f"implementation, and its specification is measured against that implementation "
              f"rather than decided by a designer", file=sys.stderr)
    return kind


def cmd_resolve(a) -> int:
    kind = _asking(a)
    doc = refine.resolve(_case(a.name), rnd=a.round, fresh=a.fresh, kind=kind)
    for r in doc["resolutions"]:
        print(f"  {r['witness']:38} {r['outcome']:12} kept={r.get('kept')} "
              f"eliminated={r.get('eliminated')}")
    print(f"{doc['oracle']} queries this run: {doc['queries']} "
          f"in {'1 sitting' if doc.get('sitting', {}).get('asked') else '0 sittings'} "
          f"({doc['distinct_questions']} distinct question(s))")
    if doc.get("reference"):
        print(f"answered from {', '.join(doc['reference'])}")
    return 0


def cmd_verify(a) -> int:
    case = _case(a.name)
    # The same list step 09 passes, read here from the case directory because a standalone
    # `verify` has no step chain to read it out of.  Omitting it would make this command the one
    # place a case with a violated property can be told it converged.
    out = refine.verify(case, [v["name"] for v in propcheck.violations(case)])
    print(json.dumps({k: out.get(k) for k in
                      ("converged", "blocked_by", "determinism_certificate", "decided",
                       "decided_unsatisfiable", "violated_properties", "designer_indifferent",
                       "rediagnosis")},
                     indent=1, default=str))
    return 0 if out["converged"] else 1


def cmd_snapshot(a) -> int:
    case = _case(a.name)
    d = refine.snapshot(case, a.round)
    print(f"{case.name}: round {a.round} frozen at {os.path.relpath(d)} "
          f"({len(os.listdir(d))} artifact(s))")
    return 0


def cmd_audit(a) -> int:
    """Two claims, checked separately, and only the first is always available.

    **Order.**  Did an answer from the designer reach the run before there was a witness to
    justify it?  That is `cases.audit`, it reads the append-only ledger, and it is the whole
    auditable claim of the method.  It needs nothing but the case.

    **Leaks.**  Did a name that could only have come from a reference implementation turn up in
    an artifact that was supposed to be derived from the prose alone?  leanSpec has no reference
    — the input is prose and the output is prose — so there is nothing in the repository to run
    this against.  It is here anyway, behind `--against`, because the claim it checks is about
    somebody *else's* checkout: an auditor who has a reference names it on the command line and
    the scanner reports what it finds.  It is a heuristic and says so; it cannot prove an agent
    did not look.
    """
    case = _case(a.name)
    aud = cases.audit(case)
    doc = {"case": case.name, "order": aud}
    ok = aud["clean"]

    if a.against:
        # The state the claim is about: the artifacts as they stood before any question was
        # answered.  The live files are a superset — step 06 records what a query returned, and
        # quoting the answer as the evidence for a decision is what the framework asks for.
        # Scanning those would report the framework working as a violation of itself.
        #
        # Where that state lives depends on how the case was run: the step chain for a case run
        # through `pipeline.py` (step 01's and step 02's outputs are that state by construction,
        # and nothing is frozen because nothing is overwritten), `rounds/round1/` for a case run
        # stage by stage, and the loose working files for one that never got that far.
        arts, scanned = {}, ""
        base = case.path("rounds", "round1")
        if pipeline_mod.n_steps(case):
            scanned = os.path.relpath(case.path(pipeline_mod.STEPS_DIR))
            for f in ("extraction.json", "probe.json", "Partial.lean"):
                t = pipeline_mod.undecided_text(case, f)
                if t is not None:
                    arts[f] = t
        elif os.path.isdir(base):
            scanned = os.path.relpath(base)
            for f in ("extraction.json", "probe.json", "Partial.lean"):
                p = os.path.join(base, f)
                if f == "Partial.lean" and not os.path.isfile(p):
                    p = case.path("sandbox", "Partial.lean")
                if os.path.isfile(p):
                    with open(p, errors="replace") as fh:
                        arts[f] = fh.read()
        else:
            scanned = os.path.relpath(case.dir)
            for f, p in (("extraction.json", case.path("extraction.json")),
                         ("probe.json", case.path("probe.json")),
                         ("Partial.lean", case.path("sandbox", "Partial.lean"))):
                if os.path.isfile(p):
                    with open(p, errors="replace") as fh:
                        arts[f] = fh.read()

        ref = _reference_files(a.against)
        reserved = leak.clause_ids(case.dir)
        scan = leak.leak_scan(cases.prose(case), ref, arts, a.toplevel, reserved)

        # And every sealed step document, of every round.
        #
        # The pass above scans the *artifacts* — the extraction, the partial semantics, the probe
        # — which is the claim about what the agent wrote.  This is the claim about what the
        # pipeline carried: a step document embeds its whole inherited chain, so scanning the
        # sealed steps of round N asks whether a reference's text reached any of them by any
        # route, including the seam where round N inherits round N−1.
        #
        # Every step is scanned, because every step is sealed except 06 — and 06 is excluded not
        # as an amnesty but because it is the step that talks to the designer, so its document
        # holds waveforms by design.  Values over ports the prose names are expected and are not
        # leaks; a private identifier is a different thing and is what is scanned for.
        sealed = {}
        for rnd in pipeline_mod.existing_rounds(case):
            for st in pipeline_mod.STEPS:
                if not st.sealed:
                    continue
                p = pipeline_mod.step_path(case, st, rnd)
                if os.path.isfile(p):
                    with open(p, errors="replace") as fh:
                        sealed[os.path.relpath(p, case.dir)] = fh.read()
        if sealed:
            # `reserved` is widened here and only here.  The artifact scan above is the claim
            # about what the *agent* wrote and stays as strict as it was; this pass is the claim
            # about what the *pipeline* carried, and a step document is generated — its schema
            # keys and the names of the files it materialises are written unconditionally.  The
            # rule, and what it costs, is in `leak.schema_vocabulary`.
            chain = leak.leak_scan(cases.prose(case), ref, sealed, a.toplevel,
                                   reserved | leak.schema_vocabulary(
                                       sealed, pipeline_mod.DELIVERABLES))
            scan = {"private_identifiers": scan["private_gt_identifiers"],
                    "hits": {**scan["hits"], **chain["hits"]},
                    "sealed_steps_scanned": len(sealed),
                    "clean": scan["clean"] and chain["clean"]}
        doc["leak_scan"] = scan
        doc["scanned"] = scanned
        doc["artifacts"] = sorted(arts)
        doc["reference"] = os.path.relpath(a.against)
        ok = ok and scan["clean"]
    else:
        doc["leak_scan"] = {
            "run": False,
            "why": "leanSpec carries no reference implementation, so there is nothing in this "
                   "repository to scan against.  Pass --against DIR to name one."}

    with open(case.path("audit.json"), "w") as f:
        json.dump(doc, f, indent=1)
    print(json.dumps(doc, indent=1))
    return 0 if ok else 1


def _reference_files(path: str) -> dict[str, str]:
    """Whatever `--against` names, keyed by filename, so the scanner can strip per syntax."""
    if os.path.isfile(path):
        with open(path, errors="replace") as f:
            return {os.path.basename(path): f.read()}
    out = {}
    for root, _, names in os.walk(path):
        for n in names:
            if n.endswith((".v", ".sv", ".vhd", ".py", ".vh", ".svh")):
                with open(os.path.join(root, n), errors="replace") as f:
                    out[n] = f.read()
    return out


def cmd_run(a) -> int:
    variant.require("a run")
    _asking(a)
    case = _case(a.name)
    if a.backup:
        d = pipeline_mod.backup(case, a.backup)
        print(f"{case.name}: "
              f"{'backed up to ' + os.path.relpath(d) if d else 'backup exists, kept'}")
    # `--round` defaults to the round already on disk, or 1.  Continuing the round that is there
    # is the common case — a step is re-run after its authored file was corrected — and starting
    # the *next* one silently would leave a half-built round behind and read its step 08 as a
    # handoff.  A new round is asked for by name.
    have = pipeline_mod.existing_rounds(case)
    rnd = a.round if a.round else (have[-1] if have else 1)
    if rnd > 1 and rnd - 1 not in have and a.start == 0:
        print(f"{case.name}: round {rnd} continues round {rnd - 1}, which has no steps/ "
              f"directory (rounds present: {have or 'none'})", file=sys.stderr)
        return 1
    docs = pipeline_mod.run(case, first=a.start, last=a.end, rnd=rnd)
    for d in docs:
        mark = "✓" if d["ok"] else "✗"
        lock = "  " if d["sealed"] else "??"
        print(f"  {mark} {lock} {d['step']:02d} {d['name']:<14} -> steps/round{rnd}/"
              f"{d['step']:02d}_{d['name']}.json")
        for p in d["problems"][:12]:
            print(f"        {p}", file=sys.stderr)
    print(f"\n{case.name}: steps/round{rnd}/INDEX.md, steps/INDEX.md")
    if docs and docs[-1]["step"] == pipeline_mod.LAST and docs[-1]["ok"]:
        print(f"{case.name}: converged.  Deliverables in {os.path.relpath(case.path('out'))}/")
    return 0 if docs and all(d["ok"] for d in docs) else 1


def cmd_scaffold(a) -> int:
    """Pre-fill `authored/roundN/` from the round the case already ran.

    Three of the four authored files are a copy: `rounds/roundN/` holds the extraction, the
    partial semantics and the probe exactly as that round used them.  The fourth is
    `decisions.json`, and this writes the half of it that is transcription — which witness was
    resolved, to what, against which `Cfg` field, quoting which bytes of the prose — leaving
    `evidence`, `consequence` and each hunk's `replacement` empty, because those are the reading
    and cannot be derived from the record.  It transcribes resolutions only: it cannot propose a
    reading the designer did not keep, and step 07 re-checks that independently of this command.
    """
    case = _case(a.name)
    made, existing = pipeline_mod.scaffold(case, a.round, force=a.force)
    for f in made:
        print(f"  + {f}")
    for f in existing:
        print(f"  = {f} (kept; --force to overwrite)")
    if not made and not existing:
        print(f"{case.name}: round {a.round} has no rounds/round{a.round}/ to scaffold from",
              file=sys.stderr)
        return 1
    return 0


def cmd_ls(a) -> int:
    reg = cases.registry()
    if not reg:
        print(f"no cases in {os.path.relpath(cases.REGISTRY)}")
        return 0
    for c in reg:
        rs = pipeline_mod.existing_rounds(c) if os.path.isdir(c.dir) else []
        out = os.path.join(c.dir, pipeline_mod.OUT_DIR, "REPORT.md")
        # `archived` is printed in the same column as `delivered`, and they are mutually
        # exclusive on purpose: an archived run may well have an `out/`, and showing both would
        # let a reader take the word they wanted.  Under `bak/` it is not a result.
        state = "archived" if c.bak else ("delivered" if os.path.isfile(out) else "")
        print(f"  {c.name:28} rounds={len(rs) or '-':<3} {state:<10} {c.why}")
    return 0


def cmd_archive(a) -> int:
    """Move a case under `<key>/bak/`, or back out.  See `cases.archive`."""
    c = cases.archive(a.name, on=not a.restore)
    where = "archived under" if c.bak else "restored to"
    print(f"{c.name}: {where} {os.path.relpath(c.dir, paths.REPO)}")
    return 0


def cmd_report(a) -> int:
    return report_mod.main(a)


def cmd_diff(a) -> int:
    """The decided prose against the original, as the deliverable has it.

    Convenience, and one guarantee: this recomputes the diff from the two files on disk rather
    than printing `out/spec.diff`, so a deliverable that was edited by hand after the fact shows
    up here as a diff that does not match the one shipped beside it.
    """
    case = _case(a.name)
    p = case.path(pipeline_mod.OUT_DIR, pipeline_mod.D_PROSE)
    if not os.path.isfile(p):
        print(f"{case.name}: no decided prose yet ({os.path.relpath(p)})", file=sys.stderr)
        return 1
    with open(p, errors="replace") as f:
        decided = f.read()
    print(patch.unified(cases.prose(case), decided), end="")
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="leanspec", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)

    def add(name, fn, **kw):
        s = sub.add_parser(name, **kw)
        s.set_defaults(fn=fn)
        return s

    s = add("new", cmd_new, help="create a case from a file of prose")
    s.add_argument("name")
    s.add_argument("--prose", required=True, help="the natural-language specification")
    s.add_argument("--why", default="", help="why this specification is worth running")
    s.add_argument("--bench", default="",
                   help="which corpus the prose came from; names the directory under "
                        "data/part1/.  Inferred from the design name when omitted, and "
                        "'local' when no installed benchmark claims it.")

    s = add("prompt", cmd_prompt, help="what the agent is asked to write")
    s.add_argument("name")
    s.add_argument("--stage", type=int, choices=(1, 2), default=1)
    s.add_argument("--round", type=int, default=1,
                   help="which round's prompt; the outputs are named per round")
    s.add_argument("--pass", type=int, default=0, dest="pss", metavar="N",
                   help="one pass of a staged phase (stage 2 has %d); 0 prints the whole brief"
                        % len(STAGE2_PASSES))

    for name, fn, h in (("extract", cmd_extract, "check stage 1"),
                        ("formalize", cmd_formalize, "check stage 2"),
                        ("diagnose", cmd_diagnose, "the four queries"),
                        ("properties", cmd_properties, "what the prose claims about itself"),
                        ("witness", cmd_witness, "the separating contexts"),
                        ("verify", cmd_verify, "re-diagnose the decided reading")):
        s = add(name, fn, help=h)
        s.add_argument("name")

    s = add("resolve", cmd_resolve, help="ask the designer, once per witness")
    s.add_argument("name")
    s.add_argument("--round", type=int, default=1)
    s.add_argument("--fresh", action="store_true",
                   help="re-ask questions whose answers are already on disk")
    _oracle_flag(s)

    s = add("snapshot", cmd_snapshot, help="freeze a round's artifacts")
    s.add_argument("name")
    s.add_argument("--round", type=int, required=True)

    s = add("audit", cmd_audit, help="the ordering claim, and optionally a leak scan")
    s.add_argument("name")
    s.add_argument("--against", default=None, metavar="DIR",
                   help="a reference implementation to scan against; leanSpec has none of its "
                        "own, so without this the leak scan does not run")
    s.add_argument("--toplevel", default="",
                   help="the module name the reference's harness instantiates, if any")

    s = add("run", cmd_run, help="the ten-step pipeline: one input and one output per step")
    s.add_argument("name")
    s.add_argument("--from", dest="start", type=int, default=0,
                   help="first step to run (default 0); earlier steps' outputs must exist")
    s.add_argument("--to", dest="end", type=int, default=pipeline_mod.LAST,
                   help=f"last step to run (default {pipeline_mod.LAST})")
    s.add_argument("--round", type=int, default=None,
                   help="which round to run (default: the highest round on disk, or 1)")
    s.add_argument("--backup", nargs="?", const=".bak", default=None,
                   help="copy the case directory aside first, e.g. --backup .bak")
    _oracle_flag(s)

    s = add("scaffold", cmd_scaffold,
            help="pre-fill authored/roundN/ from rounds/roundN/, leaving the reading to author")
    s.add_argument("name")
    s.add_argument("--round", type=int, required=True)
    s.add_argument("--force", action="store_true",
                   help="overwrite an authored file that already exists")

    add("ls", cmd_ls, help="the registry")

    s = add("archive", cmd_archive,
            help="move a case under <key>/bak/ — kept, but not a reported result")
    s.add_argument("name")
    s.add_argument("--restore", action="store_true", help="move it back out of bak/")

    s = add("report", cmd_report, help="one row per case")
    s.add_argument("--out", default=None)

    s = add("diff", cmd_diff, help="original prose vs. decided prose, recomputed")
    s.add_argument("name")

    a = p.parse_args(argv)
    return a.fn(a)


if __name__ == "__main__":
    raise SystemExit(main())
