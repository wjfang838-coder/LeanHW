#!/usr/bin/env python3
"""Drive the authoring agent through a case's three authored artifacts, round after round.

    python3 leanspec/author.py --case counter
    python3 leanspec/author.py --case counter --case adder --workers 2
    python3 leanspec/author.py --all
    python3 leanspec/author.py --audit                  # where did the authors reach

## What this is

`cli.py run` runs ten numbered steps, and three of them read a file the machine refuses to
write: `extraction.json` (step 01), `Partial.lean` + `probe.json` (step 02), and
`decisions.json` (step 07).  `common/steps.py` says why in the exception it raises — *"the
pipeline does not synthesise it, because a step that writes its own input decides its own
result."*  Those three are the agent's.

This is the human that used to sit in that loop, automated: for each case it runs the machine up
to the next authored artifact, launches an agent to write it, runs the machine again, and hands
any checker complaint back as a repair.  It is a **driver, not a step**.  It never writes into
`steps/`, never calls a step function, and never reaches the designer; everything it knows about
whether an artifact is good comes from the exit code of `cli.py run`.

## Where the queries are spent, and what the author may see when they are

The phases are cut so that no sealed artifact is ever authored by an agent that has seen an
answer.  Steps 01–05 — extraction, formalization, diagnosis, properties, witnesses — are all
sealed, so the first two phases run entirely before the designer is consulted.  Step 06 is the
open one, and it runs *between* the second phase and the third: the decisions author's whole job
is to say what those answers mean, so it is the one author that is supposed to have them.

That cut is why the formalization phase's machine range stops at 05 rather than running through
06.  A repair loop that re-ran resolution would hand the checker's stdout — including the
designer's verdicts — back to the agent writing `Partial.lean`, and the projection would then be
shaped around the answers it exists to earn.  The seal would still be enforced at the door and
would mean nothing.

## The prompts are the framework's, wherever the framework has one

Stages 1 and 2 ship prompts — `cli.STAGE1_PROMPT` and `cli.STAGE2_PROMPT` — and they are used
verbatim, with one substitution: `cmd_prompt` addresses the artifacts at `Case.path`, which
routes a bare filename into `state/`, and the pipeline reads `authored/roundN/`.  Pointing the
agent at `state/` would have it write where this driver does not look.  The substitution is the
output path and nothing else, and `AUTHOR.json` records both the template and the result.

Step 07 ships no prompt, so `DEC_PROMPT` below is written here.  It carries no engineering advice
about the design under test: every constraint in it is transcribed from the checker that will
judge the artifact — `step_decision`'s four numbered checks — so that what the agent is told and
what the machine enforces are the same sentences.  A prompt that added a hint the checker does
not check would be this file putting its thumb on the case.

## The wall

Every session runs through `common/agent.py`, which installs `common/confine.py` as a
`PreToolUse` hook and cannot be asked not to.  `--audit` then walks every tool call in every
transcript and reports each path argument that resolved outside the case directory, separating
the ones the wall refused from the ones that actually ran.  The two agree by construction: both
call `confine.offending`.

There is nothing here about a reference implementation, because leanSpec has none.  The old
version of this file also ran a leak scan against a benchmark's answer key after every case;
that scan is now `cli.py audit --against DIR`, run by an auditor who has a reference to name.
What survives here is the part that does not need one: did the agent stay inside the case.
"""
from __future__ import annotations

import argparse
import concurrent.futures
import fcntl
import hashlib
import json
import os
import shutil
import subprocess
import sys
import time

from common import agent_backend

if __package__ in (None, ""):
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
    __package__ = "leanspec"

from common import agent as agent_mod, confine                            # noqa: E402
from . import cases, cli, emit, leanrun, oracle, pipeline, schema         # noqa: E402

ROOT = cases.ROOT

# ---------------------------------------------------------------- the one prompt written here

DEC_PROMPT = """\
STAGE 7 INPUT — THE DECISIONS.  Read {res} and write {out}/decisions.json.

Step 06 has spent this round's queries.  Its output records, per witness, what the designer kept
and what the designer eliminated.  This document says what those answers MEAN for the
specification: which reading held, which coordinate of `Cfg` that fixes, which bytes of the prose
have to change, and which coordinates you are deliberately leaving open.

    {{"case": "{name}", "round": {rnd},
      "decisions": [
        {{"kind": "choice|hole|model|property|violation",
          "name": "<the question, as extraction.json spells it>",
          "round": {rnd},
          "witness": "<the witness id step 06 resolved>",
          "resolved_to": "<tag>", "rejected": ["<tag>", ...],
          "cfg_field": "c_<name>|h_<name>", "cfg_value": "<the Lean term>",
          "evidence": "<why the prose left this open, and what the answer returned>",
          "consequence": "<what an implementer must now do differently>",
          "patch": [{{"op": "replace", "clause": "C2", "span": [<start>, <end>],
                     "original": "<the exact bytes>", "replacement": "<the decided text>"}}]}} ],
      "remaining_open": [{{"name": "...", "cfg_field": "...", "why": "...",
                          "note_for_spec": "..."}}],
      "note": "<one line>"}}

Four checks, all mechanical, all run by step 07 — read them as constraints:

  * every decision names a witness step 06 actually resolved, and `resolved_to` must be what that
    witness KEPT.  A tag in `rejected` must have been eliminated by some answer this round
    received about the same question;
  * a witness that came back anything other than `decided`, `pinned` or `pinned_undeclared`
    decides nothing, and a decision taken on it is you answering your own question.  In
    particular `pinned_sampled` cannot pin: the option set was declared incomplete, so the value
    the designer holds need never have been offered;
  * every patch hunk quotes the prose byte for byte in `original` — `prose[span[0]:span[1]]` must
    equal it exactly — and must land inside a clause the decision's own question rests on;
  * every field of `Cfg` is either decided here or named in `remaining_open`.  A question the
    round could not close is named, not guessed.

`kind: "property"` is the one decision that costs no query.  Step 04 checks the properties the
prose states about itself against the projection, and a property that eliminates every reading of
a fork but one has answered that question already — the document constrained itself.  Such a
decision names the property in `evidence` and carries no `witness`, because none was spent.

`kind: "violation"` is the opposite finding and it is the strongest one this pipeline produces.
Step 04 proved that a guarantee the prose states is broken by the same prose's definitions: at a
legal context, the sentences that say what the design does admit a behaviour the guarantee says
must never happen.  There is no reading under which both sentences hold, so step 06 did not offer
a menu of behaviours — it showed the designer the two sentences and asked which one is wrong.
Such a decision is written like this:

  * `name` is the PROPERTY's name, not a fork's, and `witness` is `violation:<that name>`;
  * `resolved_to` is `definitions` (the behaviour is what was meant, so the guarantee sentence is
    wrong) or `property` (the guarantee is what was meant, so the definitions are too permissive)
    — whichever the resolution KEPT;
  * there is no `cfg_field` and no `cfg_value`.  An adjudication settles no coordinate of `Cfg`;
    it says which sentence the author disowned.  Do not invent one to fill the slot;
  * `patch` is the repair, and it is the whole point of the decision.  Rewrite the sentence the
    designer gave up so that the contradiction is gone from the prose;
  * `clauses` — a key no other decision kind has — lists every clause id your hunks touch.  For
    every other kind the extraction says which clause the question came from; here it knows only
    the clauses the GUARANTEE was read out of, and nothing records which clauses define the
    behaviour it forbids.  So when the designer disowns the definitions, you must name the
    clauses yourself.  Every id is checked against the extraction, and hunks outside the union of
    the property's own basis and the ids you list are refused.

Step 07 requires this: for every violation the designer adjudicated, there must be a decision.
An answered contradiction with no decision is a query spent for nothing, and the round will fail.
A round that found a violation does not converge either — the repair you write is a claim about
the NEXT round's prose, and only the next round's property check can confirm it.

Three reasons a coordinate stays open, and they are different findings asking for different
repairs.  The report above prints `separation certified` for each one; that field is how you
tell the first from the second, and you may not decide it by reading the answer.

  * `designer_indifferent` — separation **certified**, and the designer, shown that context,
    accepted every reading anyway.  The coordinate is a declared degree of freedom, and no
    further round closes it;
  * `unseparated` — separation **not certified**.  The readings differ somewhere in the frame
    but nowhere in it are they disjoint, so the one observation the oracle reported was
    consistent with all of them and the query eliminated nothing.  This is NOT a degree of
    freedom.  The design has a definite value here; this frame could not reach a context where
    that value shows.  What it asks for is a longer or richer `ctxUniverse` next round, and
    saying it is free would be recording our own reach as the designer's intent;
  * `unobservable_coordinate` — no legal context distinguishes the values at all, so the
    question cannot be put.  The prose can be narrowed to say so; it cannot be decided.

All three belong in `why`, spelled that way.  `note_for_spec` follows the label: for
`designer_indifferent` and `unobservable_coordinate` it names a choice the reader is free to
make, and for `unseparated` it does not — a reader told to choose freely at a coordinate the
design in fact fixes has been told something false.

`why` is for the record: why this round could not close the question.  `note_for_spec` is a
suggested wording for a reader, and it is printed in `out/QUESTIONS.md` — **not** in the decided
prose.  The decided prose carries the decisions and nothing else: no marker, no annotation, no
"this specification does not settle X".  An open coordinate is a fact about our run, and the
prose we hand on is a specification, not a report on our run.  Write `note_for_spec` as one
sentence naming what a reader must choose, in the specification's own words, WITHOUT hinting at
an answer.

A partial decision that does not say it is partial is the failure mode this exists to stop: a
design that shipped one correct decision beside two unresolved coordinates had its author
implement the decision faithfully and land FURTHER from what was wanted, because the rule that
got fixed and the rules that stayed wrong no longer cancelled.

`evidence` quotes what actually happened: which clauses left the question open, which witness was
shown, and what the designer said.  Quote the answer; do not improve it.

How a `replacement` should READ is not mechanical, and it decides more than it looks like it
does.  Three rules, each of them paid for:

  * say what this clause requires, and stop.  Do not explain how the decided rule relates to some
    other construct in the document.  One decided clause was once given a correct note whose
    second half observed that an operand priority list "is *not* the order of the multiplexer
    given further below".  Its implementer read that, went and looked at both multiplexers
    together, and unified a sub-term that had been left alone — the one term in the module that
    then went wrong.  Every decided clause was implemented correctly and the design still failed.
    A clarification relocates attention, so the risk it creates lands on the clauses next to the
    one it fixed;
  * write a standalone sentence next to the clause rather than a parenthetical spliced into a
    heading or a table row.  A long aside inside a heading changes the reading weight of the
    whole section it titles;
  * prefer the words the specification already uses for the thing.  A decision is not an
    invitation to re-name a signal or restate the design in better prose; the smallest edit that
    forecloses the wrong reading carries the least risk with it.

REPAIRING A SENTENCE AN EARLIER ROUND ALREADY REPAIRED.  This is allowed, it is one of the
reasons a second round exists, and it has a shape.  Every round's hunks are offsets into the same
original `sandbox/spec.txt`, so quote the ORIGINAL bytes in `original` and the ORIGINAL span in
`span` — the same ones the earlier round quoted — and write the sentence's whole new text in
`replacement`.  A hunk that rewrites exactly the span an earlier hunk rewrote supersedes it: what
you write is what the decided prose will say, and the earlier round's version is kept only as a
record of what it replaced.

So `replacement` must be complete.  It is not a delta against the earlier repair — whatever of
that repair you still want has to be in your text, or it is gone.  And the span must match
exactly: a hunk that covers part of an earlier round's span and part of some neighbouring text is
refused, because neither hunk quotes what the other left behind and there is no order in which
the two compose.  If the repair you want spans more text than the earlier one did, quote the
larger original span and rewrite the whole of it.
"""

HARD_RULE = """\

You are working in {dir}, which is the case directory, and it is your whole world.  The documents
your task names above are your inputs; the prose they were drawn from is `sandbox/spec.txt`.
There is no reference implementation, no testbench and no answer key anywhere — this case exists
to measure what the prose alone determines — so there is nothing outside this directory that
would help you, and reaching for something that looks like it would is how a run stops meaning
anything.

This is enforced, not requested: a hook refuses any tool call naming a path outside this
directory before it runs.  So put scratch work in `scratch/` here rather than `/tmp`, and address
files relative to the case.  The one exception is the Lean toolchain and the `LeanSpec` library
you compile against, which are allowed.
"""

CONTINUE = """\

THIS IS ROUND {rnd}, A CONTINUATION.  Round {prev} ran and did not converge.  Its extraction is at
`authored/round{prev}/extraction.json` and the decisions its queries earned are at
`authored/round{prev}/decisions.json`; both are your own earlier work and are safe to read.

This round's extraction is that document ADVANCED, not a fresh reading:

  * it must carry a `decisions` array holding **exactly** the decisions earlier rounds took —
    every one of them, and nothing else.  Step 01 checks both directions.  A decision dropped is a
    question that silently re-opens after it was already settled; a decision added is you
    answering your own question, which is the round-1 offence taken a round later;
  * a question earlier rounds closed is no longer a `choice` or a `hole`.  Its clause is now
    `fixed`, and its text is the decided text — `out/spec.decided.txt` is what round {prev}
    emitted and it is what this specification now SAYS;
  * but the bytes you quote are still `sandbox/spec.txt`'s.  Every round reads the same original
    file and every span is an offset into it, checked byte for byte against it; the decided prose
    is that file with one replacement per repair applied.  So read `spec.decided.txt` to know
    what the specification means, and address the original to say where.  A clause whose sentence
    an earlier round rewrote spans the ORIGINAL sentence, and its `text` is the original's;
  * what remains is what round {prev} left open, plus anything the decided text newly exposes.
    A round exists to ask what the previous one could not, so if you find nothing new to ask, say
    so in the extraction rather than manufacturing a fork.
"""

# Formalization's counterpart to `CONTINUE`, and it settles a question the earlier arrangement
# left implicit.  Every round got a fresh `authored/roundN/` and pass 1 was told the file did not
# exist yet, so `Partial.lean` was written from scratch each round — while the agent's confinement
# root is the whole case directory, so it could read the previous round's file and, measured on
# `accu`, did so constantly.  From scratch as a file, with hindsight as knowledge: an arrangement
# nobody chose, and one where what carried over was whatever the session happened to look at.
#
# So it is said out loud instead.  The previous round's file is named, it is an input, and what to
# do with it is stated per pass rather than left to taste.
INHERIT = """\

Round {p}'s `Partial.lean` is at `{prev}`.  It is your own earlier work on the same specification
and it is an input to this round, not a thing to avoid looking at.  Read it before you write.

You are still writing a new file.  Round {p}'s formalization was of round {p}'s extraction, and
this round's prose is not that prose — clauses that were forks are now decided text, and the
decided text says things the old file was written not to assume.  Every declaration you carry
over is one you are asserting is still right about a document that changed.
"""

# The frame specifically, because it is the one declaration where rebuilding from nothing has a
# measurable cost and where the failure of carrying over is quiet.  On `accu`, round 2 built 28
# contexts reaching cost 7 and round 3 built 19 reaching cost 8: the later frame was cheaper to
# decide and it was not the earlier frame refined, it was a different frame, and no reader can
# tell which of round 2's 28 contexts round 3 decided against keeping or simply never thought of.
#
# The rule is inherit-then-justify, and it is deliberately NOT monotone.  A frame that may only
# grow becomes bloated by construction — every round pays enumeration cost for every context any
# round ever wanted — and bloat is the thing that makes a frame too expensive to decide, which is
# the failure that ends a case.  Deleting is allowed; deleting silently is not.
INHERIT_CTXS = """\

START FROM ROUND {p}'S `ctxUniverse`, in `{prev}`.  It is the frame that produced this round's
questions, and a context in it is a context some earlier query needed.

  * Every one of round {p}'s contexts is either kept or dropped, and a comment says which and
    why.  You may drop as many as you like — this frame is not required to grow, and a frame that
    only ever grows is one that eventually costs more to enumerate than the questions it answers
    are worth.  What is not allowed is a context disappearing without anyone noticing.
  * RE-CHECK EVERY KEPT CONTEXT AGAINST THIS ROUND'S `legal`.  You wrote `legal` in the previous
    pass, against this round's prose, and the decided text may have tightened the environment
    assumptions since round {p}.  A context that was legal then and is not now is dead weight:
    it is enumerated by every query and excluded by every one of them.  Step 03 reports
    `ctx_total` and `ctx_legal` and the gap between them is visible.
  * Then add what this round needs.  The test is unchanged and it is DISJOINTNESS: for each
    `choices[]` fork and each `holes[]` coordinate still open, is there a context here where the
    readings admit NO observation in common — pairwise, across the whole value domain, for a
    hole?  A frame that merely separates a coordinate still spends a query on it and still
    closes nothing, because the one observation the oracle reports can be consistent with every
    candidate.  Last round's `diagnosis.json` says which coordinates that happened to:
    `discriminating: false` on a difference, `pinning: false` on a hole.  Those are the ones
    this frame has to reach further for, and a longer context is the thing that reaches.
  * Modify freely.  A kept context whose trace no longer means what it did — because a signal's
    decided timing changed — should be edited to mean what it was for, not preserved verbatim.
"""

# ------------------------------------------------------------------------------- the phases


class Phase:
    """One authored artifact, and the step ranges either side of writing it.

    `before` runs while the agent is not yet involved; `after` is the checker whose exit code is
    the only verdict on what the agent wrote.  The split exists for exactly one phase — the
    decisions author needs step 06 to have run, and nobody else may see it — but it is spelled
    generally rather than special-cased, because a special case here is a seal that holds by
    coincidence.

    `passes` splits the *writing* into several sessions with a cheap gate between them.  It is
    not a second seal and it changes nothing about what the phase produces or who judges it: the
    artifact is the same file and `after` is the same checker.  What it changes is how much work
    one fault can destroy, which is why only the formalization phase has one — a six-hundred-line
    Lean file was the only artifact here big enough for a single lost turn to cost a session.
    """

    def __init__(self, tag: str, writes: str, after: tuple[int, int],
                 before: tuple[int, int] | None = None,
                 passes: tuple[tuple[str, str], ...] = ()):
        self.tag, self.writes, self.after, self.before = tag, writes, after, before
        self.passes = passes


PHASES = [
    Phase("extraction", "extraction.json", after=(1, 1)),
    # 02..05: formalization, diagnosis, properties, witnesses.  All sealed, so a repair loop here
    # cannot show the author an answer.
    Phase("formalization", "Partial.lean (and the derived probe.json)", after=(2, 5),
          passes=cli.STAGE2_PASSES),
    # 06 first — the queries — then the author reads them, then 07..08 check and finish.
    #
    # 08 and not 09.  Step 09 is the round's accounting: it re-diagnoses and says whether the run
    # converged, and it exits nonzero when it did not — which is the ORDINARY outcome of a first
    # round and precisely the condition the round loop below exists to respond to.  Inside this
    # phase's span that verdict was read as a rejected artifact: the phase re-authored
    # `decisions.json` three times against a judgement no `decisions.json` could change, gave up,
    # and returned `rejected`, so `convergence()` and every round after the first were
    # unreachable code.  `accu` round 1 is the case that showed it — eight coordinates open,
    # nothing settled, three attempts spent — and until then `--max-rounds` had never once had an
    # effect.  The phase checks what the author wrote; the round decides whether to go again.
    Phase("decisions", "decisions.json", before=(6, 6), after=(7, 8)),
]

# The `blocked_by` verdicts no further round can move, named here rather than re-reasoned at the
# bottom of the round loop.  `refine.py` is where the distinction is drawn and argued; this is the
# scheduling consequence of it, and the two must not drift — a state added there and forgotten
# here costs rounds, and one added here in error skips them.
#
# `violated_property` is deliberately ABSENT.  It is the one blocked state that asks for another
# round: step 07 required the designer to adjudicate a guarantee against a definition, the
# decision rewrote one of the two sentences, and nothing in the round that made the rewrite can
# say whether it worked.  The check is the next round's stage 4 against the repaired prose.
#
# `unseparated` is ABSENT for the same reason and it is the more expensive omission, so it is
# stated rather than left to the reader of the set.  A coordinate whose readings the frame never
# made disjoint has not been answered, and the thing that would answer it — a longer context —
# is exactly what the next round's `ctxUniverse` pass is asked to add.  Filed as terminal it
# would stop the case at the round that proved its own frame too short.
TERMINAL = frozenset({"spec_contradiction", "designer_indifferent", "unobservable_coordinate"})

# `lake` and `lean` build and elaborate `Partial.lean`, which the stage 2 prompt tells the agent
# to do.  `Bash(python3:*)` is deliberately NOT granted, though `common/agent.py` offers it:
# the confinement hook reads the paths a command names, and `python3 -c '...'` names none, so an
# interpreter is a door in the wall.  That decision stands.  What did not stand is the sentence
# that used to follow it — "Nothing in the stage 1 or stage 2 instructions needs one" — which was
# a claim about what an agent would reach for, made without asking one.  Stage 2's main input is
# a 30 KB `01_extraction.json`; the formalization author's first move was `python3 -c` to pull
# the clause list out of it, got "This command requires approval", and fell back to reading a
# JSON document in `head -c 3000` / `tail -c 2500` byte slices.  It had `Read` the whole time.
#
# The mismatch is the same one twice below, and it can be closed from either side.  It is closed
# on the PROMPT side here, because the other side is a guarantee: stage 2 now states that `lean`
# and `lake` are the only interpreters and that step documents are read with `Read`.  An agent
# cannot infer what it was not granted, and a refusal it cannot explain is one it routes around.
#
# These patterns match on the head of the command, so the SHAPE the prompt asks for has to be a
# shape they match.  `LEAN_PATH=<build> ~/.elan/bin/lean Partial.lean` matches neither: it leads
# with an environment assignment and names the binary by path.  The stage 2 prompt asked for
# exactly that for one run, and every invocation came back "This command requires approval" —
# the agent spent forty minutes building its own lake package to route around a wall that was
# never meant to be there, and `Partial.lean` was still a stub when the hour was up.  Nothing
# reports this: the grant looks correct, the prompt looks correct, and they disagree.  So
# `LEAN_PATH` is set in the session environment by `run_agent` instead, and the prompt asks for
# a bare `lean Partial.lean` — which is what these patterns admit.
TOOLS = (*agent_mod.BASE_TOOLS, "Bash(lake:*)", "Bash(lean:*)")

# What lies outside the case and is still reachable.  `import LeanSpec` needs the library, and
# the build tree is what `LEAN_PATH` points at — set by `run_agent` in the session environment
# rather than typed by the agent, so an agent denied these would be told to compile against
# something it cannot open.  Nothing else is added: the framework's Python source is the checker,
# and the case directory is the world.  (`~/.elan` is added by `common/agent.py` for every role
# and is not repeated here.)
ALLOW_ROOTS = (leanrun.LEAN_DIR, leanrun.BUILD)

AUTHOR = agent_mod.Role(tag="spec-author", tools=TOOLS, allow=ALLOW_ROOTS,
                        timeout=int(os.environ.get("LEANSPEC_AUTHOR_TIMEOUT", "3600")))


def _authored_dir(case: cases.Case, rnd: int) -> str:
    d = case.path(pipeline.AUTHORED, f"round{rnd}")
    os.makedirs(d, exist_ok=True)
    return d


# --------------------------------------------------------------- the sealed artifacts, carried

#: The phases `carry_forward` writes, when it can.  Named here rather than spelled at the call
#: site so that a phase added to `PHASES` is not silently assumed to be authorable-or-carried.
CARRIED = ("extraction", "formalization")


def _produced(case: cases.Case, n: int, rnd: int) -> dict:
    """One step's `produced` block from a round that has already run, or `{}`."""
    p = pipeline.step_path(case, pipeline.BY_N[n], rnd)
    if not os.path.isfile(p):
        return {}
    try:
        with open(p, errors="replace") as f:
            return (json.load(f) or {}).get("produced") or {}
    except ValueError:
        return {}


def carried_documents(case: cases.Case, rnd: int) -> tuple[dict | None, dict | None, str]:
    """Round N ≥ 2's two sealed artifacts, derived from round N−1's record instead of re-authored.

    Returns `(files, record, why)` — the documents keyed by their authored name and a record of
    where each came from, or `None`s and a sentence saying why this round has to be authored after
    all.  Nothing is written here.  That is deliberate: it is what lets `rounds_test` re-derive
    `accu`'s recorded rounds and compare against them, rather than overwrite the one copy of the
    evidence this whole change is argued from.

    ## Why this is not a step writing its own input

    `common/steps.py` refuses to synthesise an authored file and says why: *"a step that writes
    its own input decides its own result."*  That still holds.  The caller is the round DRIVER,
    writing round N's inputs out of round N−1's recorded OUTPUTS — the same relation the agent had
    to the previous round's file, and the relation `_advance` already has to the extraction.  No
    step writes its own input, and every check that judged an authored artifact still judges this
    one: step 01 still tests the decision record in both directions, step 02 still runs
    `check_partial`, `validate_probe`, and the `decidedCfg` refusal, and the file still has to
    elaborate.  What changes is who typed it, not what it has to survive.

    ## What each piece is derived from

      * `extraction.json` is round N−1's step 07 `extraction_decided`.  Not a fresh reading of the
        decided prose — the same document, which `_advance` computed mechanically from the
        decision record precisely so that a hand edit "can close a question the designer did not
        answer, or leave one open that they did".  An agent re-deriving it by hand next round is
        that hand edit, taken one round later.
      * `Partial.lean` is ROUND ONE's file with `emit.decide_partial` applied to the accumulated
        assignments.  Round one's, not round N−1's, so that every round differs from the frame the
        first round's queries were asked in by exactly the decisions that were taken and by
        nothing else.  Measured on `accu`, re-authoring produced round 3's `obsUniverse` at 217
        entries against round 2's 106 — from an identical `Cfg`, for no recorded reason.
      * `probe.json` is `emit.probe_document` of that extraction, which is already where it comes
        from in an authored round.

    ## The decided field STAYS, and that reverses a decision

    Step 07 argues that `Cfg` is not cumulative: once a decision is in the prose, the next round's
    extraction marks the clause `fixed` and the next round's `Partial.lean` has no field for it.
    `decide_partial` pins the default instead and leaves the field in place, because dropping a
    field means rewriting every use of it — which is the cost this function exists to avoid.

    It is safe for one reason, and the reason is worth stating rather than trusting: `diagnose.py`
    enumerates forks from `ext["choices"]` and `ext["holes"]`, never from `Cfg`'s field list.  A
    coordinate the decisions closed is gone from the advanced extraction, so no query is generated
    for it whether or not `Cfg` still carries a pinned field.  The field costs its own line and
    its pin menu — two to six lines each on `accu` — and it buys the thing the prose round-trip
    was buying: somewhere durable the next round can read the answer.
    """
    ext = _produced(case, 7, rnd - 1).get("extraction_decided")
    if not ext:
        return None, None, (f"round {rnd - 1} step 07 recorded no `extraction_decided`, so there "
                            f"is no advanced extraction to carry")
    first = os.path.join(case.path(pipeline.AUTHORED, "round1"), "Partial.lean")
    if not os.path.isfile(first):
        return None, None, "round 1's Partial.lean is not on disk, so there is no frame to narrow"
    with open(first, errors="replace") as f:
        src = f.read()

    # The assignments are re-derived here rather than taken from step 07's `assignments`, and the
    # difference is the whole correctness of this function.  Step 07 filters its assignments to
    # the fields of the round it ran in, because `Cfg` was not cumulative: on `accu`, round 1
    # decided five coordinates, round 2's `Cfg` no longer had them, and round 2's recorded
    # `assignments` is therefore `{}`.  Carrying round 1's frame forward with THAT would pin
    # nothing and hand round 3 an undecided specification with a decided extraction -- the two
    # halves disagreeing about what is settled, which no checker downstream is looking for.
    #
    # So: the ACCUMULATED decision record, against ROUND ONE's field list, which is the frame
    # being narrowed.  Both are read from what the pipeline itself recorded rather than recomputed,
    # so a disagreement here is a disagreement with the run, not with a re-derivation of it.
    fields = _produced(case, 2, 1).get("cfg_fields")
    if not fields:
        return None, None, "round 1 step 02 recorded no `cfg_fields`, so there is no frame to pin"
    doc = _produced(case, 7, rnd - 1).get("decisions_doc") or {}
    assignments, _open, errs = emit.derive(fields, doc)
    if errs:
        return None, None, (f"the accumulated decision record does not derive against round 1's "
                            f"Cfg: {errs[0]}")

    pinned, done = emit.decide_partial(src, assignments)
    # An assignment naming a field round 1's `Cfg` does not have is not a thing to paper over: it
    # means the decision record and the frame disagree about what this case's coordinates ARE, and
    # carrying a file that silently ignored it would put that disagreement into every later round.
    # Authoring the round is the honest fallback -- an agent reading the decided prose can see
    # what this function cannot.
    if missing := sorted(set(assignments) - set(done)):
        return None, None, (f"round 1's Cfg has no field for {', '.join(missing)}, which the "
                            f"decision record assigns -- the frame and the record disagree, so "
                            f"this round is authored rather than carried")

    files = {"extraction.json": json.dumps(ext, indent=1),
             "Partial.lean": pinned,
             "probe.json": json.dumps(emit.probe_document(ext), indent=1)}
    return files, {"round": rnd, "how": "carried", "pinned": sorted(done),
                   "from": {"extraction.json": f"round {rnd - 1} step 07 extraction_decided",
                            "Partial.lean": "round 1, decide_partial(accumulated assignments)",
                            "probe.json": "emit.probe_document of that extraction"}}, ""


def carry_forward(case: cases.Case, rnd: int) -> tuple[dict | None, str]:
    """`carried_documents`, written into round N's authored directory."""
    files, rec, why = carried_documents(case, rnd)
    if files is None:
        return None, why
    out = _authored_dir(case, rnd)
    for name, content in files.items():
        with open(os.path.join(out, name), "w") as f:
            f.write(content)
    return rec, ""


def prompt_for(case: cases.Case, ph: Phase, rnd: int, pss: int = 0,
               target: str | None = None) -> str:
    """The ask for one phase, or for one pass of one.

    Stages 1–2 are the framework's text; 7 is the one above.  `pss` is 1-based and selects an
    entry of `ph.passes`; 0 means the whole phase, which is what `cli.py prompt` prints and what
    a phase without passes always gets.  The phase text is unchanged in either case — a pass is
    the same brief with a smaller ask bolted to the end, not a different brief, so nothing a pass
    session is told is something the whole-phase session was not.

    `target` names the file to write, and defaults to the artifact.  `_in_parallel` passes a
    working copy instead; it keeps the same basename, so every sentence of the brief that speaks
    of `Partial.lean` still speaks of the file the session is holding.
    """
    out = _authored_dir(case, rnd)
    if ph.tag == "extraction":
        body = cli.STAGE1_PROMPT.format(spec=os.path.join(case.sandbox, "spec.txt"),
                                        out=os.path.join(out, "extraction.json"),
                                        name=case.name)
        if rnd > 1:
            body += CONTINUE.format(rnd=rnd, prev=rnd - 1)
    elif ph.tag == "formalization":
        target = target or os.path.join(out, "Partial.lean")
        body = cli.STAGE2_PROMPT.format(out=target,
                                        out2=os.path.join(out, "probe.json"),
                                        lib=leanrun.LEAN_DIR)
        body += (f"\nRound {rnd}'s extraction is at {out}/extraction.json, and step 01 has "
                 f"validated it.  Formalize THAT document.\n")
        # Named only when it is actually there.  A prompt that points at a file the previous round
        # never wrote sends a session looking for it, and what it finds instead of giving up is
        # something else to read.
        prev = (case.path(pipeline.AUTHORED, f"round{rnd - 1}", "Partial.lean")
                if rnd > 1 else None)
        if prev and os.path.isfile(prev):
            body += INHERIT.format(prev=prev, p=rnd - 1)
        else:
            prev = None
        if pss:
            tag, adds = ph.passes[pss - 1]
            body += cli.PASS_PROMPT.format(
                n=pss, of=len(ph.passes), adds=adds, out=target,
                state=(f"`{os.path.basename(target)}` does not exist yet; this pass creates it."
                       if pss == 1 else
                       f"Passes 1..{pss - 1} are done and `{os.path.basename(target)}` "
                       f"elaborates.  READ IT FIRST — it was written by another session and what "
                       f"it named things is now binding on you."))
            if tag == "ctxs" and prev:
                body += INHERIT_CTXS.format(prev=prev, p=rnd - 1)
    else:
        st = pipeline.BY_NAME["resolution"]
        body = DEC_PROMPT.format(out=out, rnd=rnd, name=case.name,
                                 res=case.path(pipeline.STEPS_DIR, f"round{rnd}",
                                               st.stem + ".json"))
    profile_path = case.path("formalization-profile.json")
    if ph.tag == "formalization" and os.path.isfile(profile_path):
        with open(profile_path) as stream:
            profile = json.load(stream)
        if profile.get("name") != "stateless-bool-mux-traces-v1":
            raise ValueError("Unknown formalization profile")
        body += """\nRepresentation contract for this end-to-end profile (not a behavioral answer):
Declare Ctx with exactly `steps : List (Bool × Bool × Bool)`; tuple coordinates
are physical inputs a, b, sel in that order. Declare Obs with exactly
`steps : List Bool`, each Bool being the physical out sample. Cfg, admits,
properties, and diagnostic universes must still be derived from the NL extraction.
Do not restrict the Ctx type to the diagnostic sample: arbitrary finite traces,
including empty traces, must be representable. This profile covers only binary,
stateless combinational behavior, not analog delays or four-state X/Z behavior.
"""
    return body + HARD_RULE.format(dir=case.dir)


#: A requested ceiling on how much one turn may think, in tokens.  **It does not bind**, and it
#: is left here set because the request is free and the finding is worth keeping next to it.
#:
#: The reasoning that produced it: stage 2 never produced a `Partial.lean` across six sessions,
#: and the transcripts separate cleanly once you count thinking per TURN rather than per session.
#: Stage 1, which succeeds, runs 10 to 24 turns whose largest is 7,130 tokens and has never been
#: retried once.  Stage 2 runs four or five turns, opens with about a dozen orientation calls,
#: then enters a single turn of 15,000 to 18,000 tokens composing the whole file — and that turn
#: comes back `api_retry`, `error: "unknown"`, each attempt restarting the composition from the
#: beginning.  A plain `claude -p` against the same endpoint answers in under two seconds
#: throughout, so the endpoint is not down.
#:
#: So the theory was that the long turn is what fails, and 8,000 would force the pass-by-pass
#: shape the prompt asks for.  The next session then ran a turn of **18,144 tokens** with this
#: set to 8,000 and completed it with no retry at all.  Both halves of that are informative: the
#: variable is not honoured by this CLI, and a turn of that size is not deterministically fatal.
#: The failure is an intermittent fault that long requests are simply exposed to for longer, and
#: which costs the whole turn when it lands.  That is a worse problem than the one theorised —
#: it cannot be prompted around — but it is not the one this constant was set for, so nothing
#: here should be read as having fixed it.
MAX_THINKING = os.environ.get("LEANSPEC_MAX_THINKING", "8000")


def run_agent(case: cases.Case, ph: Phase, rnd: int, model: str, prompt: str,
              attempt: int, slug: str = "") -> dict:
    stem = f"round{rnd}.{ph.tag}{'.' + slug if slug else ''}.a{attempt}"
    t = case.path("logs", "authoring", f"{stem}.jsonl")
    role = agent_mod.Role(tag=AUTHOR.tag, tools=AUTHOR.tools, allow=AUTHOR.allow,
                          readonly=AUTHOR.allow, timeout=AUTHOR.timeout, model=model)
    if agent_backend.backend() == "codex":
        prompt = prompt.replace(cli.SHELL_NOTE, """This session uses Codex shell and apply_patch tools inside a filesystem namespace.
Use the shell to read the named inputs and apply_patch to write the named outputs.
Python may calculate and check exact Unicode string offsets with text.index(quote);
do not estimate spans by hand or use UTF-8 byte offsets. Only this case and the
explicitly granted language libraries are accessible. Do not read credentials.
""")
    r = agent_backend.run(role, case.dir, prompt, t, cwd=case.dir,
                          extra_env={"LEAN_PATH": leanrun.BUILD,
                                     "MAX_THINKING_TOKENS": MAX_THINKING})
    # Printed, not merely recorded.  A refused call means this prompt asked for something this
    # role was not given, and that is a defect in the harness rather than in the agent — but it
    # presents as an agent that went quiet, so it has to arrive while someone is still watching.
    summary = agent_mod.refusal_summary(r["refusals"])
    if summary:
        print(f"  {ph.tag} round {rnd} attempt {attempt}:\n{summary}", flush=True)
    cases.log(case, "author", phase=ph.tag, pss=slug or None, round=rnd, attempt=attempt,
              rc=r["rc"], how=r["how"], denied=r["denied"], refusals=r["refusals"],
              elapsed=r["elapsed"], transcript=os.path.relpath(r["transcript"], ROOT))
    return {"phase": ph.tag, "pass": slug or None, "round": rnd, "attempt": attempt,
            **{k: r[k] for k in ("rc", "how", "stderr", "elapsed", "session_error", "denied",
                                 "refusals")},
            "transcript": os.path.relpath(r["transcript"], ROOT)}


# ------------------------------------------------------------------------ writing in passes
#
# Only the formalization phase uses this, and `docs/design/SPECCHECK.md` ("Stage 2 is written in
# six sessions, not one") records why.  The short version: `Partial.lean` was asked for in one
# session seven times and was a 51-byte stub seven times, because the composition turn is long
# enough to be a target for an intermittent API fault that restarts it from the beginning and,
# having started, has never recovered.
#
# The pass state is a file rather than a variable because the point is to survive the process
# that failed.  It is keyed on the artifact's hash: if `Partial.lean` is not the file the record
# was written about, the record is about nothing and is discarded, and the passes start over from
# an empty file.  That is the conservative direction — it re-does work that may have been fine —
# and it is the right one, because the alternative is a pass told "passes 1..4 are done" about a
# file in which they are not.

PASS_STATE = ".passes.json"


def _sha(path: str) -> str:
    if not os.path.isfile(path):
        return ""
    h = hashlib.sha256()
    with open(path, "rb") as f:
        h.update(f.read())
    return h.hexdigest()


def _passes_done(out: str, target: str) -> list[str]:
    """Which passes a previous run finished, believed only if the artifact still matches."""
    p = os.path.join(out, PASS_STATE)
    if not os.path.isfile(p):
        return []
    try:
        with open(p, errors="replace") as f:
            d = json.load(f)
    except (OSError, ValueError):
        return []
    return list(d.get("done") or []) if d.get("sha") == _sha(target) else []


def _snapshot_dir(out: str) -> str:
    d = os.path.join(out, "passes")
    os.makedirs(d, exist_ok=True)
    return d


def _record_pass(out: str, target: str, done: list[str]) -> None:
    """Record the pass, and keep the file as it stood when the pass ended.

    The snapshot is what makes a *partial* rollback possible.  Without one there is exactly one
    move available when step 02 rejects the artifact — throw the whole record away and re-author
    every pass — because the only copy of the file on disk is the one the last pass left, and the
    state the file was in after the second-to-last pass no longer exists anywhere.  The first two
    `accu` sweeps were both rejected for something one pass wrote, and both re-authored about
    1,900 lines from nothing to fix it.

    Cheap: one copy per pass of a file that reaches ~140 KB, inside the case directory, alongside
    the record they belong to.
    """
    with open(os.path.join(out, PASS_STATE), "w") as f:
        json.dump({"done": done, "sha": _sha(target)}, f, indent=1)
    if os.path.isfile(target) and done:
        shutil.copy2(target, os.path.join(_snapshot_dir(out), f"{done[-1]}.lean"))


def _rewind_to(out: str, target: str, done: list[str], tag: str) -> bool:
    """Put the artifact and the record back to just before `tag` ran.  True if it worked.

    Only used when the rejection is attributable to one pass — see `do_case`.  It restores the
    snapshot taken when the pass *before* `tag` ended, so the passes that came before keep their
    work and `tag` and everything after it are re-authored.

    Returns False and changes nothing if the snapshot is not there, which is the case for any
    record written before snapshots existed.  Falling back to the full drop is always safe; a
    rewind onto a file that is not what the record describes would not be.
    """
    if tag not in done:
        return False
    i = done.index(tag)
    if i == 0:
        return False
    src = os.path.join(_snapshot_dir(out), f"{done[i - 1]}.lean")
    if not os.path.isfile(src):
        return False
    shutil.copy2(src, target)
    _record_pass(out, target, done[:i])
    return True


def _pass_gate(tag: str, target: str, ext: dict | None = None) -> tuple[bool, str]:
    """Whether a pass may end.  Cheap, local, and not the phase's verdict.

    Steps 02..05 remain the only judgement on `Partial.lean`.  This asks the one question that
    makes the *next* pass possible — does the file still elaborate — because a pass inherits what
    the last one left and a session cannot repair a file it was told was sound.

    `probe.json` used to be gated here too, for the ninth pass that wrote it, and the check could
    only ever ask `isfile` and `json.load` — neither of which distinguishes a document written by
    this attempt from one left behind by an abandoned one.  The driver derives the document now
    (`emit.probe_document`), so there is nothing here to gate: it is rewritten from the extraction
    on every entry to `in_passes` and cannot be stale.

    The properties pass gets one more question, about the section it just wrote and nothing else.
    That is a widening of this gate's remit and it is deliberate: a step 02 rejection drops the
    whole pass record, so a defect confined to one pass re-authors every pass, and the first
    `accu` run spent about a hundred minutes doing exactly that.  Asking the properties pass about
    its own output turns that into two repair attempts inside the pass.  Nothing else from
    `check_partial` is asked here — those sections belong to earlier passes, and asking about them
    would make this the verdict rather than a gate.
    """
    if not os.path.isfile(target):
        return False, f"{os.path.basename(target)} was not written"
    res = leanrun.run(target)
    if not res["ok"]:
        return False, "\n".join(res["errors"][:12]) or leanrun.summarize(res)
    if tag == "properties" and ext:
        with open(target, errors="replace") as f:
            problems = schema.property_problems(f.read(), ext)
        if problems:
            return False, "\n".join(problems)
    return True, ""


def in_passes(case: cases.Case, ph: Phase, rnd: int, model: str, repairs: int,
              log: list[dict], note: str = "") -> tuple[bool, str]:
    """Write this phase's artifact one pass at a time.  Returns (finished, last complaint).

    `note` is the checker's complaint from an earlier sweep, carried into every pass.  It has to
    reach all of them rather than only the last: step 02 rejects the artifact, and which pass
    wrote the part it is rejecting is not something this driver knows.
    """
    out = _authored_dir(case, rnd)
    target, probe = os.path.join(out, "Partial.lean"), os.path.join(out, "probe.json")
    # The properties gate needs to know which properties stage 1 declared expressible.  Read
    # here rather than per attempt, and tolerated missing: a phase that runs without an
    # extraction has larger problems, and step 01 is what reports them.
    ext: dict | None = None
    try:
        with open(os.path.join(out, "extraction.json")) as f:
            ext = json.load(f)
    except (OSError, ValueError):
        pass
    # `probe.json`, derived and rewritten unconditionally — before the first pass, on every entry,
    # including the entries that resume a half-finished record.  It was a pass of its own until
    # `emit.probe_document` showed it never carried a judgement, and writing it here is what makes
    # the stale-document hazard structural rather than checked:
    #
    # the record is keyed on the hash of the Lean file alone, so dropping it said nothing about
    # the probe and the probe survived a discarded attempt.  The gate for that pass could ask only
    # `isfile` and `json.load`, and a document written by the *previous* attempt answers both
    # perfectly well.  `probe.json` describes how a `Ctx` becomes stimulus, so a stale one is the
    # previous attempt's `Ctx` projected onto this one, silently, with step 04's witnesses built
    # through it.  A file recomputed from the extraction cannot be a previous attempt's.
    if ext is not None:
        with open(probe, "w") as f:
            json.dump(emit.probe_document(ext), f, indent=1)
    done = _passes_done(out, target)
    if not done and os.path.exists(target):
        # No usable record and a file on disk — a stub from a session that never got started, or
        # the tail of one that did.  Pass 1 is told the file does not exist, so make that true.
        os.replace(target, target + ".discarded")
        print(f"  formalization round {rnd}: discarded an unrecorded "
              f"{os.path.basename(target)}", flush=True)
    why = ""
    forked = False
    for i, (tag, _) in enumerate(ph.passes, 1):
        if tag in done:
            print(f"  formalization round {rnd}: pass {i}/{len(ph.passes)} {tag} — already done",
                  flush=True)
            continue
        # The fork.  Taken at the first undone pass whose whole remainder is independent, so a
        # resumed round that has `obs` already forks over the two that are left.  Once, though:
        # `forked` is what stops a fallback to sequence from being re-forked at the very next
        # pass, which would run the concurrent attempt again and fail it for the same reason.
        todo = [(k, t) for k, (t, _) in enumerate(ph.passes, 1) if t not in done]
        if PARALLEL and not forked and {t for _, t in todo} <= set(PARALLEL) and len(todo) > 1:
            forked = True
            status, why, entries = _in_parallel(case, ph, rnd, model, repairs, note, todo,
                                                out, target, ext, done)
            log.extend(entries)
            if status == "ok":
                break
            if status == "failed":
                return False, why
            print(f"  formalization round {rnd}: {why} — writing these "
                  f"{len(todo)} pass(es) in sequence instead", flush=True)
        ok, why, entries = _one_pass(case, ph, rnd, model, repairs, note, i, tag, target, ext)
        log.extend(entries)
        if not ok:
            return False, f"pass {i} ({tag}) was not completed in {repairs + 1} attempts:\n{why}"
        done.append(tag)
        _record_pass(out, target, done)
    _wire_case(out, target, done, rnd)
    return True, ""


def _one_pass(case: cases.Case, ph: Phase, rnd: int, model: str, repairs: int, note: str,
              i: int, tag: str, target: str, ext: dict | None,
              extra: str = "") -> tuple[bool, str, list[dict]]:
    """One pass, up to `repairs + 1` attempts, against `target`.  (finished, complaint, log rows).

    Records nothing and touches no pass state: `target` may be the artifact itself or one of
    `_in_parallel`'s working copies, and which of those it is decides what the result means.  That
    decision belongs to the caller.
    """
    ask = prompt_for(case, ph, rnd, pss=i, target=target) + note + extra
    entries, why = [], ""
    for attempt in range(1, repairs + 2):
        t0 = time.time()
        r = run_agent(case, ph, rnd, model, ask, attempt, slug=tag)
        ok, why = _pass_gate(tag, target, ext)
        r.update(**{"pass": tag, "pass_n": i, "pass_ok": ok, "gate": why[:800]})
        entries.append(r)
        print(f"  formalization round {rnd}: pass {i}/{len(ph.passes)} {tag} "
              f"attempt {attempt} — {'ok' if ok else 'rejected'} "
              f"({r['how']}, {round(time.time() - t0)}s)", flush=True)
        if ok:
            return True, "", entries
        # Lean's own diagnostic, handed back verbatim, exactly as the phase-level loop hands
        # back the checker's.  Nothing is added: if the message is not enough to repair from,
        # that is a fact about the message.
        ask = (prompt_for(case, ph, rnd, pss=i, target=target) + note + extra
               + f"\n\nA previous attempt at this pass left the file rejected:\n\n{why}\n\n"
                 f"Fix exactly what it names.  Do not delete a declaration to make the "
                 f"message go away, and do not move on to a later pass.\n")
    return False, why, entries


#: The passes that may be written at the same time, in the order they go into the file.
#:
#: They are independent because none of them reads a declaration another one writes.  That was not
#: true until the `case` record moved out of `render` and into the driver (`emit.case_stanza`):
#: `case` binds `obsUniverse`, so for as long as a session wrote it, `render` could not start until
#: `obs` had finished, and eight lines of wiring made two passes serial.
#:
#: Measured on `accu`, serially: obs 27.8 min, render 5.9, properties 16.8.  Concurrently the round
#: pays the slowest of the three instead of their sum.
#:
#: `LEANSPEC_SERIAL=1` turns it off, and that is not only a debugging switch: three `claude -p`
#: sessions at once is three times the request rate, and a machine or an account that cannot take
#: it should be able to say so without editing the module.
PARALLEL: tuple[str, ...] = (() if os.environ.get("LEANSPEC_SERIAL") else
                             ("obs", "render", "properties"))

#: What a parallel pass is told that a serial one is not.
#:
#: The first paragraph is there to correct the brief above it, not to add to it.  `PASS_PROMPT`
#: says "passes 1..N-1 are done and the file elaborates", which is true of the numbering and false
#: of the clock when the fork is taken: `render` is pass 5 and is written while pass 4 is still
#: running, so its copy does not contain `obsUniverse` and no amount of reading will find it.  A
#: session that believes the older sentence goes looking for a declaration that is not there.
_APPEND_ONLY = """

## You are one of several sessions writing this file at the same time

{others} being written right now, each in its own copy of `{f}`, at the same time as yours.  So
the line above about which passes are done describes the ORDER the sections go in, not what is in
the copy you are holding: those sections are not in it and will not appear while you work.  What
is in it is everything the passes before the concurrent group left, and that part is final.

When all of the concurrent sessions are finished the driver takes what each one ADDED and joins
the additions together, in the order the passes are numbered.  So:

* **Append.**  Add your section at the end of the file.  Everything above it was written by
  earlier passes and is binding on you exactly as it always was — read it, rely on it, do not
  edit it.
* Do not write a section that belongs to another pass.  You will not see its work and it will not
  see yours; two sessions writing the same declaration is two declarations in the joined file.
* If you find you MUST change something an earlier pass wrote — the projection is too wide, a type
  is wrong for what you have to say — then change it and say why in a comment.  The driver checks
  whether the part above your section is still what it handed you, and if it is not, it throws the
  concurrent attempt away and re-runs these passes one after another so that the later ones are
  written against your change.  That is the designed path, not a failure; it costs a re-run and it
  is much cheaper than a file whose sections disagree.
"""


def _in_parallel(case: cases.Case, ph: Phase, rnd: int, model: str, repairs: int, note: str,
                 todo: list[tuple[int, str]], out: str, target: str, ext: dict | None,
                 done: list[str]) -> tuple[str, str, list[dict]]:
    """Write the independent passes at the same time, then join what each one added.

    Returns `("ok" | "serial" | "failed", why, log rows)`.  `"serial"` means the concurrent attempt
    produced nothing usable and the caller should write these passes one after another; it is a
    decision, not an error, and the reason is printed.

    ## Why a copy each, and a join, rather than one file

    A pass is a `claude -p` session with `Write` on the artifact.  Three of them on one path is
    three sessions overwriting each other, and the loser's work is not merely lost -- it is lost
    *invisibly*, because the file still elaborates and the record still says the pass is done.  So
    each session gets the artifact as it stood when the last serial pass ended, in a directory of
    its own, and the driver reads back what each added.

    ## The join is refused unless it is a join

    Every copy must still START with the seed, byte for byte.  A session that edited the part
    above its own section did not write a section that can be joined -- it wrote a different file,
    and splicing another session's section onto it would produce an artifact that no session ever
    saw.  The `obs` pass is told, in as many words, that it may narrow `Obs` if the projection is
    too wide; that is exactly such an edit, and when it happens the whole concurrent attempt is
    discarded and the passes are re-run in sequence so that `render` and `properties` are written
    against the narrowed type.

    Then the joined file has to elaborate as a whole.  Each copy elaborating on its own is not that
    claim: two sections can each be sound and still collide on a name, and `_pass_gate` cannot see
    a collision it is not shown.

    ## What it costs when it does not work

    One concurrent attempt, thrown away.  That is the honest price and it is why the fallback is a
    fallback rather than a repair: a partial salvage -- keep the appends, re-run only the pass that
    edited the prefix -- would leave the kept sections written against a file that no longer exists.
    """
    # Only reachable once a serial pass has left a file — the first three passes are not in
    # `PARALLEL`, so the fork cannot be taken before `admits` has recorded one.  Checked anyway,
    # because the alternative to a fallback here is an exception out of the phase driver.
    if not os.path.isfile(target):
        return "serial", f"{os.path.basename(target)} is not there to fork from", []
    with open(target, errors="replace") as f:
        seed = f.read()
    base = os.path.basename(target)
    root = os.path.join(out, "parallel")
    shutil.rmtree(root, ignore_errors=True)
    copies = {}
    for i, tag in todo:
        d = os.path.join(root, tag)
        os.makedirs(d, exist_ok=True)
        copies[tag] = p = os.path.join(d, base)
        with open(p, "w") as f:
            f.write(seed)

    print(f"  formalization round {rnd}: {', '.join(t for _, t in todo)} at the same time",
          flush=True)
    with concurrent.futures.ThreadPoolExecutor(max_workers=len(todo)) as pool:
        futures = {}
        for i, tag in todo:
            rest = [f"`{t}`" for _, t in todo if t != tag]
            others = (f"The {' and '.join(rest)} pass is" if len(rest) == 1
                      else f"The {', '.join(rest[:-1])} and {rest[-1]} passes are")
            futures[pool.submit(_one_pass, case, ph, rnd, model, repairs, note, i, tag,
                                copies[tag], ext,
                                _APPEND_ONLY.format(f=base, others=others))] = (i, tag)
        got = {futures[f]: f.result() for f in concurrent.futures.as_completed(futures)}

    # In pass order, not completion order: the log is read as the story of how the file was
    # written, and three sessions finishing out of order do not make it a different story.
    entries = [r for k in todo for r in got[k][2]]
    for (i, tag) in todo:
        ok, why, _ = got[(i, tag)]
        if not ok:
            return "failed", (f"pass {i} ({tag}) was not completed in {repairs + 1} "
                              f"attempts:\n{why}"), entries

    joined, stages = seed, []
    for i, tag in todo:
        with open(copies[tag], errors="replace") as f:
            src = f.read()
        if not src.startswith(seed):
            return "serial", f"the {tag} pass changed what was above its own section", entries
        tail = src[len(seed):]
        joined += ("" if joined.endswith("\n") else "\n") + tail
        # The file as it WOULD have stood had this pass been the last serial one.  `_record_pass`
        # snapshots whatever `target` holds, and `_rewind_to` restores the snapshot belonging to
        # the pass before the one it is undoing — so recording all three against the finished join
        # would make every snapshot the same file, and a rewind to `properties` would restore a
        # copy that already contains the properties section while telling the next sweep to write
        # it again.  Staging the writes is what keeps the record and the snapshots meaning the
        # same thing they mean on the serial path.
        stages.append((tag, joined, tail))

    whole = os.path.join(root, base)
    with open(whole, "w") as f:
        f.write(joined)
    res = leanrun.run(whole)
    if not res["ok"]:
        return "serial", ("the joined file does not elaborate: "
                          + ("; ".join(res["errors"][:3]) or leanrun.summarize(res))), entries

    for tag, upto, _ in stages:
        with open(target, "w") as f:
            f.write(upto)
        done.append(tag)
        _record_pass(out, target, done)
    print(f"  formalization round {rnd}: joined {len(stages)} section(s) — "
          f"{sum(t.count(chr(10)) for _, _, t in stages)} lines", flush=True)
    return "ok", "", entries


def _wire_case(out: str, target: str, done: list[str], rnd: int) -> None:
    """Append the `case` record once the passes are finished, if none of them wrote one.

    The third thing the driver writes into an authored round, after `probe.json` and a carried
    round's whole artifact, and the argument is `emit.case_stanza`'s: seven bindings with no second
    way to write them.  Here rather than in a pass because appending is the only edit that cannot
    disturb what the sessions left, and after the loop rather than inside it because the record it
    wires up is not complete until the last pass has run.

    The re-record is the part that would be a bug if it were left out.  `_passes_done` believes the
    pass list only while the file still hashes to what the record says, so appending a byte after
    the final `_record_pass` would invalidate the record for every later entry — a resumed round
    would re-author six passes because the driver added eight lines to the file.
    """
    if not os.path.isfile(target):
        return
    with open(target, errors="replace") as f:
        src = f.read()
    stanza = emit.case_stanza(src)
    if stanza is None:
        return
    with open(target, "a") as f:
        f.write(("" if src.endswith("\n") else "\n") + "\n" + stanza)
    _record_pass(out, target, done)
    print(f"  formalization round {rnd}: wired `case` (generated, not authored)", flush=True)


def _drop_passes(out: str) -> None:
    """Forget which passes are done, so the next sweep re-authors the artifact from nothing."""
    p = os.path.join(out, PASS_STATE)
    if os.path.isfile(p):
        os.remove(p)


def _passes_done_raw(out: str) -> list[str]:
    """The recorded pass list without the hash check, for deciding what to rewind to."""
    try:
        with open(os.path.join(out, PASS_STATE), errors="replace") as f:
            return list(json.load(f).get("done") or [])
    except (OSError, ValueError):
        return []


def _owner_of(out: str) -> str:
    """The single pass a step 02 rejection is attributable to, or `""`.

    Attribution is by RECOMPUTING, never by reading the rejection's text.  A message is prose and
    matching it would tie this driver to wording that is free to change; the question asked here
    is the structural one directly — is every complaint step 02 would raise one that
    `property_problems` also raises?  If so the properties section is the whole of what is wrong,
    and that section is the `properties` pass's.

    The set has to be step 02's WHOLE verdict, and getting that wrong is how this function was
    first written.  `pipeline.step_formalization` rejects on four independent grounds — the
    structural check, the probe check, a literal search for a hand-written `decidedCfg`, and
    elaboration — and comparing against only the first said "properties" for the second `accu`
    sweep, which had a `decidedCfg` in it as well.  Rewinding on that verdict would have restored
    a snapshot still carrying the `decidedCfg` and called the properties pass the culprit.  So all
    four are recomputed here, and any drift between this list and that function reopens the same
    hole.

    `validate_probe` stays in that sum even though no pass writes `probe.json` any more.  It is
    derived from `extraction.json` now, so a complaint from it is a complaint about the
    extraction, which no rewind inside this phase can repair — and the honest answer to that is
    `""` and a dropped record, which is exactly what leaving it in the sum produces.

    Everything else returns `""` and the caller drops the record, which is the behaviour that was
    always there.  Only one pass has an owner function today; the rest of `check_partial` mixes
    obligations across passes — a missing `Cfg` field could come from the `types` pass or from a
    later pass deleting it — and a wrong attribution keeps work that should have been thrown away,
    which is a worse failure than repeating work that was fine.  Every uncertainty resolves
    to `""`.
    """
    src_p = os.path.join(out, "Partial.lean")
    ext_p = os.path.join(out, "extraction.json")
    probe_p = os.path.join(out, "probe.json")
    if not all(os.path.isfile(p) for p in (src_p, ext_p, probe_p)):
        return ""
    try:
        with open(src_p, errors="replace") as f:
            src = f.read()
        with open(ext_p) as f:
            ext = json.load(f)
        with open(probe_p) as f:
            probe = json.load(f)
        every = schema.check_partial(src, ext) + schema.validate_probe(probe, ext)
        if pipeline._DEFINES_DECIDED_CFG.search(src):
            every.append("decidedCfg")
        mine = schema.property_problems(src, ext)
        if every != mine:
            return ""
        # Elaboration last, because it is the only expensive one and the cheap checks have
        # already ruled out most rejections by the time it runs.
        if not leanrun.run(src_p)["ok"]:
            return ""
    except (OSError, ValueError, KeyError):
        return ""
    return "properties" if every else ""


def _complaint(ph: Phase, out: str) -> str:
    """The checker's complaint, handed back verbatim.

    Nothing is added to it: if the message is not enough to repair from, that is a fact about the
    message and belongs in the record rather than being patched over here.
    """
    return (f"\n\nA previous attempt wrote {ph.writes} and the checker rejected it:\n\n{out}\n\n"
            f"Fix exactly what it names.  Do not weaken the artifact to make the message go "
            f"away.\n")


def machine(case: cases.Case, span: tuple[int, int], rnd: int,
            oracle_kind: str = oracle.KIND_DESIGNER) -> tuple[int, str]:
    """Run the pipeline over a step range.  Its exit code is the only verdict here.

    `oracle_kind` is forwarded on the command line and not inherited, because `oracle._ASKING` is
    a module global in THIS process and every step below runs in a child.  A batch driver that
    set it here and did not pass it would answer all fifty designs from the designer while its
    own banner said `reference_rtl` -- the one failure mode the labelling in `oracle.py` exists
    to prevent, arriving through the label itself.

    Passed on every span rather than only on the one containing step 06.  Step 06 is the only
    reader, so the other spans are unaffected; making the flag conditional on a step NUMBER would
    put the guarantee at the mercy of the step table's ordering, and `_asking`'s banner is
    captured here rather than printed, so there is no noise to save.
    """
    p = subprocess.run([sys.executable, "-m", "leanspec.cli", "run", case.name,
                        "--from", str(span[0]), "--to", str(span[1]), "--round", str(rnd),
                        "--oracle", oracle_kind],
                       cwd=ROOT, capture_output=True, text=True)
    return p.returncode, (p.stdout + p.stderr)[-4000:]


def do_case(name: str, model: str, max_rounds: int, repairs: int,
            resume: bool = False, oracle_kind: str = oracle.KIND_DESIGNER) -> dict:
    log: list[dict] = []
    case = cases.find(name)

    rc, out = machine(case, (0, 0), 1, oracle_kind)
    if rc:
        return {"case": name, "status": "step00_failed", "detail": out[-800:], "log": log}

    for rnd in range(1, max_rounds + 1):
        carried: tuple[str, ...] = ()
        if rnd > 1:
            rc, out = machine(case, (0, 0), rnd, oracle_kind)
            if rc:
                return {"case": name, "status": "round_start_failed", "round": rnd,
                        "detail": out[-800:], "log": log}
            # The two sealed artifacts, derived from the last round's record rather than written
            # again.  A round that cannot be carried is authored exactly as it was before and says
            # which condition it failed: this is a scheduling change, and a case it does not fit
            # must not quietly become a case it half-fits.
            rec, why = carry_forward(case, rnd)
            if rec:
                carried = CARRIED
                log.append(rec)
                pins = ", ".join(rec["pinned"])
                print(f"  round {rnd}: carried {' and '.join(CARRIED)} forward"
                      f"{f' — pinned {pins}' if pins else ''}", flush=True)
            else:
                log.append({"round": rnd, "how": "not_carried", "why": why})
                print(f"  round {rnd}: authoring rather than carrying — {why}", flush=True)
        for ph in PHASES:
            # A carried artifact answers to the same checker an authored one does, and this is the
            # line that makes that true rather than claimed.  It does NOT fall back to authoring
            # on a rejection: the carry either produces something that passes or it is wrong, and
            # papering over it here would hide which of the two paths is at fault behind an
            # authoring session that looks ordinary.
            if ph.tag in carried:
                rc, out = machine(case, ph.after, rnd, oracle_kind)
                if rc:
                    return {"case": name, "status": "carried_rejected", "round": rnd,
                            "phase": ph.tag, "at": f"steps {ph.after[0]:02d}..{ph.after[1]:02d}",
                            "detail": out[-1500:], "log": log}
                log.append({"phase": ph.tag, "round": rnd, "how": "carried", "machine_rc": 0})
                continue
            if ph.before:
                rc, out = machine(case, ph.before, rnd, oracle_kind)
                if rc:
                    return {"case": name, "status": "blocked", "round": rnd, "phase": ph.tag,
                            "at": f"steps {ph.before[0]:02d}..{ph.before[1]:02d}",
                            "detail": out[-1500:], "log": log}
            # Under `--resume`, a phase whose artifact is already on disk and already passes the
            # machine is not re-authored.  The test is the same one that ends the repair loop, so
            # it cannot skip a phase that has not genuinely been done: on a case with nothing
            # written the steps fail for want of the file and authoring proceeds.  This exists
            # because a checker bug at step 07 used to cost every agent-hour before it, which
            # buys nothing and makes the bug expensive to look at twice.
            if resume:
                rc, out = machine(case, ph.after, rnd, oracle_kind)
                if rc == 0:
                    log.append({"phase": ph.tag, "round": rnd, "how": "resumed",
                                "note": f"{ph.writes} was already present and passed"})
                    continue
            ask, note = prompt_for(case, ph, rnd), ""
            for attempt in range(1, repairs + 2):
                if ph.passes:
                    # The passes write the artifact; this loop still owns the verdict.  A phase
                    # attempt is one full sweep of the passes, and a checker complaint is
                    # repaired the way it always was — by asking again, with the complaint in
                    # hand.  It goes to every pass rather than to one, because which pass wrote
                    # the part step 02 is rejecting is not something this driver knows.
                    okp, whyp = in_passes(case, ph, rnd, model, repairs, log, note)
                    if not okp:
                        return {"case": name, "status": "rejected", "round": rnd,
                                "phase": ph.tag, "detail": whyp[-1500:], "log": log}
                    rc, out = machine(case, ph.after, rnd, oracle_kind)
                    log.append({"phase": ph.tag, "round": rnd, "attempt": attempt,
                                "how": "passes", "machine_rc": rc})
                    if rc == 0:
                        break
                    # A rejection here is usually about the artifact rather than about one pass,
                    # so the record is dropped and the next sweep re-authors from an empty file.
                    # Keeping it would repair the last pass only, and step 02's complaints are
                    # routinely about the first.
                    #
                    # The exception is a rejection this driver can ATTRIBUTE.  `_owner_of` returns
                    # a pass only when every structural complaint step 02 could make is one that
                    # pass wrote — computed with the same function, not matched against the text
                    # of a message — and in that case the sweep rewinds to the snapshot from the
                    # pass before it instead.  The distinction is worth its lines: the second
                    # `accu` sweep was rejected for the shape of seven entries in `properties`,
                    # written by pass 8 of 9, and dropping the record cost the seventy-five
                    # minutes that passes 1 through 7 had taken.
                    outdir = _authored_dir(case, rnd)
                    owner = _owner_of(outdir)
                    if owner and _rewind_to(outdir, os.path.join(outdir, "Partial.lean"),
                                            _passes_done_raw(outdir), owner):
                        print(f"  formalization round {rnd}: rejection is pass `{owner}`'s alone "
                              f"— rewound to before it rather than dropping the sweep",
                              flush=True)
                    else:
                        _drop_passes(outdir)
                    note = _complaint(ph, out)
                    continue
                r = run_agent(case, ph, rnd, model, ask, attempt)
                rc, out = machine(case, ph.after, rnd, oracle_kind)
                r["machine_rc"] = rc
                log.append(r)
                if rc == 0:
                    break
                ask = prompt_for(case, ph, rnd) + _complaint(ph, out)
            else:
                return {"case": name, "status": "rejected", "round": rnd, "phase": ph.tag,
                        "detail": out[-1500:], "log": log}

        # The round's accounting, run here rather than as part of a phase, and its exit code is
        # deliberately ignored: "this round did not converge" is a verdict to act on, not a
        # failure to repair.  `convergence` reads the document either way, and reports the
        # missing-document case as unconverged, so a step 09 that genuinely broke still stops the
        # run — one round later, with the round's own artifacts on disk to look at.
        machine(case, (9, 9), rnd, oracle_kind)
        conv = convergence(case, rnd)
        if conv.get("converged"):
            return {"case": name, "status": "converged", "rounds": rnd, "log": log, **conv}
        # A round that cannot converge is not the same as a round that did not, and the
        # difference is already computed — `refine.py` sorts `blocked_by` into exactly this
        # distinction and says so in as many words: `designer_indifferent` "means further rounds
        # are pointless … only a change to the specification's intent can close it", and the same
        # holds of `spec_contradiction` (the decided reading admits nothing, and no re-authoring
        # of a document reverses a contradiction the designer adjudicated) and of
        # `unobservable_coordinate` (the values differ nowhere any port can see, so no query in
        # any round can separate them).  `violated_property` is the one blocked state that ASKS
        # for another round, because only the next round's stage 4 can check the rewrite.
        #
        # This loop used to read none of that.  It exited on `converged` or on `max_rounds`, so a
        # case the framework had already proved unclosable spent every remaining round re-deriving
        # the same verdict — on `verilogeval/Prob067_countslow` round 2 reached
        # `designer_indifferent` and round 3 began a fresh nine-pass formalization against it, an
        # hour and a quarter of authoring that could not have changed the answer.
        #
        # Nothing about a round changes here.  What changes is whether a round nothing can act on
        # is started, which is scheduling and not method: the rounds that DO run are the rounds
        # that ran before, byte for byte, and `--max-rounds` still bounds them.
        if (why := conv.get("blocked_by")) in TERMINAL:
            return {"case": name, "status": "blocked_terminal", "rounds": rnd, "log": log,
                    "note": f"{why} at round {rnd}: no further round can change it, so "
                            f"{max_rounds - rnd} of {max_rounds} were not run",
                    **conv}
        if rnd == max_rounds:
            return {"case": name, "status": "max_rounds", "rounds": rnd, "log": log, **conv}
    return {"case": name, "status": "no_rounds", "log": log}


def convergence(case: cases.Case, rnd: int) -> dict:
    """What the round's last step decided, read from its own document.

    The last step, not the handoff step: convergence is the round's terminal accounting and is
    where the re-diagnosis lives.  `blocked_by` is taken from the step's `produced` rather than
    from its `problems`, because `problems` is a checker's sentence and `blocked_by` is one of
    three named shapes the next round has to respond to.

    The coordinates left open come from the handoff step instead, because that is the step that
    computed them — step 09 re-diagnoses and does not re-derive the list.  Reported by name so a
    console line says *which* question is still open rather than only how many are.
    """
    def produced(n: int) -> dict:
        p = pipeline.step_path(case, pipeline.BY_N[n], rnd)
        if not os.path.isfile(p):
            return {}
        with open(p, errors="replace") as f:
            return (json.load(f) or {}).get("produced") or {}

    st = pipeline.BY_N[pipeline.LAST]
    p = pipeline.step_path(case, st, rnd)
    if not os.path.isfile(p):
        return {"converged": False, "blocked_by": f"step {st.n:02d} produced no document"}
    with open(p, errors="replace") as f:
        d = json.load(f)
    prod = d.get("produced") or {}
    return {"converged": bool(prod.get("converged")),
            "blocked_by": prod.get("blocked_by") or (d.get("problems") or [None])[0],
            "open": [o.get("name") or o.get("field")
                     for o in (produced(pipeline.HANDOFF).get("still_open") or [])]}


# ------------------------------------------------------------------------------- the audit
#
# What counts as "outside the case" is `confine.offending` and nothing else — the wall's own
# parser, not a second copy of it.  A copy lived here once and drifted: it anchored paths on `/`,
# so the agent's own `authored/round1/extraction.json` matched as `/round1/extraction.json`, read
# as absolute, resolved outside the case, and was reported as an escape.  The scan would have
# failed every confined run on its legitimate writes.  Sharing the function is what makes
# `_benign`'s claim — that the scan and the wall agree by construction — actually true.

_REFUSAL = "leansilicon confinement"


def _benign(hit: str) -> str:
    """Why an outside hit is not an escape — or `""` when it is one.

    The list is exactly what `common/agent.py` permits this role, so the scan and the wall agree
    by construction.  It deliberately does NOT excuse the framework's Python source, the sibling
    cases, or the user's memory directory, all three of which an unconfined pilot reached: the
    checker's implementation is not the agent's business, another case's `out/` holds decided
    text, and notes carried between cases are a channel between cases whatever they happen to
    say.
    """
    if hit.startswith("/dev/"):
        return "device file"
    p = os.path.realpath(os.path.expanduser(hit))
    for ok in (agent_mod.ELAN, *ALLOW_ROOTS):
        if p.startswith(os.path.realpath(ok)):
            return "lean toolchain, named by the stage 2 prompt"
    if not os.path.exists(os.path.expanduser(hit)):
        return "names no existing path"
    return ""


def _tool_blocks(path: str):
    """Yield every `tool_use` and `tool_result` block in one stream-json transcript."""
    for line in open(path, errors="replace"):
        try:
            row = json.loads(line)
        except ValueError:
            continue
        if not isinstance(row, dict):
            continue
        msg = row.get("message")
        # A `stream-json` line's `message.content` is a list of blocks, but some event kinds carry
        # it as a bare string.  Skipping those is not a gap: a string content holds no tool call,
        # and a tool call is the only thing this scan reads.
        if not isinstance(msg, dict) or not isinstance(msg.get("content"), list):
            continue
        for blk in msg["content"]:
            if isinstance(blk, dict) and blk.get("type") in ("tool_use", "tool_result"):
                yield blk


def transcript_escapes(case_dir: str) -> list[dict]:
    """Every path argument in one case's authoring transcripts that left the case directory.

    An escape is a call that **ran**, and the two are not the same thing.  A `tool_use` block is
    written to the transcript when the model asks, before anything is permitted, so a wall that is
    working produces a transcript full of outside paths — every one of them a request
    `confine.py` turned down.  Counting those as escapes reports the confinement as its own
    failure, which the first confined run duly did: six of them, two being the agent reaching for
    notes a previous case's agent had filed in the user's memory directory.  That is the
    cross-case channel closing, not opening.

    So a call is paired with its result and classified `blocked` when the result carries the
    hook's refusal.  What remains — outside the case, not an allowed root, and not refused — is an
    access that actually happened, and that is the only thing treated as fatal.

    The scan stays independent of the hook rather than trusting it: the two agree on which paths
    are outside (both call `confine.offending`) and disagree about nothing else, so a hook that
    silently stopped running shows up here as escapes with no refusals beside them.
    """
    tdir = os.path.join(case_dir, "logs", "authoring")
    base = os.path.realpath(case_dir)
    rows: list[dict] = []
    if not os.path.isdir(tdir):
        return rows
    for f in sorted(os.listdir(tdir)):
        if not f.endswith(".jsonl"):
            continue
        p = os.path.join(tdir, f)
        refused = {b.get("tool_use_id") for b in _tool_blocks(p)
                   if b.get("type") == "tool_result" and _REFUSAL in json.dumps(b.get("content"))}
        for blk in _tool_blocks(p):
            if blk.get("type") != "tool_use":
                continue
            inp = blk.get("input") or {}
            # `confine.offending` decides what is outside, so the scan and the wall cannot drift
            # apart: same fields, same regex, same `cd`-aware resolution.  A `Write` carries its
            # file text in `content`, which is not a path field and is not read here — a path
            # regex over Lean source flags `and/or` in a comment as a directory traversal.
            for hit in confine.offending(inp, base, [], [], base):
                blocked = blk.get("id") in refused
                why = "refused by the wall" if blocked else _benign(hit)
                rows.append({"transcript": f, "tool": blk.get("name"), "path": hit,
                             "why": why or None, "blocked": blocked, "escape": not why})
    return rows


def audit(names: list[str]) -> dict:
    rows, n, seen = [], 0, []
    for case in cases.registry():
        if names and case.name not in names:
            continue
        tdir = case.path("logs", "authoring")
        if not os.path.isdir(tdir):
            continue
        seen.append(case.name)
        n += len([f for f in os.listdir(tdir) if f.endswith(".jsonl")])
        for r in transcript_escapes(case.dir):
            rows.append({"case": case.name, **r})
    esc = [r for r in rows if r["escape"]]
    # `blocked` is reported rather than dropped: it is the wall's work, and a run with zero of
    # both is a different thing from a run where the agent tried repeatedly and was turned down.
    return {"cases": seen, "transcripts": n, "escapes": esc,
            "blocked": [r for r in rows if r.get("blocked")],
            "benign": [r for r in rows if not r["escape"] and not r.get("blocked")],
            "clean": not esc}


def order_check(name: str) -> dict:
    """The framework's own ordering claim, run after the case finishes.

    This is `cli.py audit` without `--against`: no leak scan, because there is nothing to scan
    against.  What it checks is the claim the method actually makes — that no answer from the
    designer entered the run before a witness justified asking for it — and that claim does not
    need a reference to be falsifiable.
    """
    p = subprocess.run([sys.executable, "-m", "leanspec.cli", "audit", name],
                       cwd=ROOT, capture_output=True, text=True)
    try:
        doc = json.loads(p.stdout)
    except ValueError:
        return {"verdict": "unreadable", "detail": (p.stdout + p.stderr)[-800:]}
    order = doc.get("order") or {}
    return {"verdict": "clean" if order.get("clean") else "failed",
            "violations": order.get("violations") or [],
            "queries": order.get("oracle_queries"),
            "replays": order.get("oracle_replays"),
            "reuses": order.get("oracle_reuses")}


def _ledger_write(led: str, row: dict, header: dict) -> list[dict]:
    """Merge one case's row into `AUTHOR.json` under a lock, and return the whole ledger.

    Read-modify-write on a file that several drivers write at once, so the READ has to happen
    inside the lock.  It used to happen once, at driver start, and every completed case pushed
    that start-of-run snapshot back over the file.  A driver that began before another batch
    existed therefore erased that batch's rows on its next write — on 2026-09-01 the verilogeval
    run lost all 13 of its rows that way.  The per-case artifacts survived on disk; what was lost
    was the one file that says what they were, which is the file every "which cases failed"
    question is answered from.

    `cases.py` has locked `CASES.json` against exactly this since it was written.  This ledger is
    the same shape of file with the same number of writers and had no lock at all.

    An unparseable ledger is moved aside rather than overwritten.  It should not happen now that
    the write is atomic, but a file left truncated by the old code is a real possibility, and
    "start fresh" and "start fresh, having silently deleted forty rows" are the same line of code
    unless the old bytes are kept.
    """
    with open(led + ".lock", "w") as lf:
        fcntl.flock(lf, fcntl.LOCK_EX)
        rows = []
        if os.path.isfile(led):
            try:
                with open(led, errors="replace") as f:
                    rows = json.load(f).get("cases", [])
            except ValueError:
                keep = led + f".unparseable.{int(time.time())}"
                os.replace(led, keep)
                print(f"  LEDGER: {led} did not parse — kept as {os.path.basename(keep)}, "
                      f"starting a new one", file=sys.stderr)
        rows = [x for x in rows if x.get("case") != row.get("case")] + [row]
        rows.sort(key=lambda x: x.get("case", ""))
        tmp = led + ".tmp"
        with open(tmp, "w") as f:
            json.dump({**header, "cases": rows}, f, indent=1)
            f.write("\n")
        os.replace(tmp, led)
    return rows


def _parser() -> argparse.ArgumentParser:
    """The batch driver's options, as an object, so a test can read them instead of restating them.

    Split out for one case in `oracle_test`: that every kind `--oracle` offers is one the child
    process can resolve.  Rebuilt by hand in the test, that assertion would pass against its own
    copy while this parser drifted.
    """
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--case", action="append", default=[], metavar="NAME",
                    help="a registered case; repeat for more than one")
    ap.add_argument("--all", action="store_true", help="every case in the registry")
    ap.add_argument("--model", default="opus")
    ap.add_argument("--workers", type=int, default=2)
    ap.add_argument("--max-rounds", type=int, default=3)
    ap.add_argument("--repairs", type=int, default=2, help="checker rejections per phase")
    ap.add_argument("--redo", action="store_true",
                    help="re-run cases that already produced a decided spec")
    ap.add_argument("--resume", action="store_true",
                    help="do not re-author a phase whose artifact is present and already passes")
    ap.add_argument("--audit", action="store_true", help="where did the authors reach")
    ap.add_argument("--oracle", default="designer", choices=sorted(oracle.FLAG_KINDS),
                    help="who answers this batch's questions (default: the designer)")
    return ap


def main() -> int:
    a = _parser().parse_args()

    if a.audit:
        r = audit(a.case)
        print(json.dumps({k: (len(v) if isinstance(v, list) and k != "cases" else v)
                          for k, v in r.items()}, indent=1))
        for row in r["escapes"] + r["benign"][:10]:
            print(f"  {row['case']:<28} {row['path']}  [{row['why'] or 'ESCAPE'}]")
        return 0 if r["clean"] else 1

    known = {c.name for c in cases.registry()}
    names = sorted(known) if a.all else a.case
    if not names:
        print("nothing to do: pass --case NAME or --all", file=sys.stderr)
        return 2
    if missing := [n for n in names if n not in known]:
        print(f"not registered: {', '.join(missing)}.  Create with `cli.py new NAME --prose F`.",
              file=sys.stderr)
        return 2
    todo = [n for n in names
            if a.redo or not os.path.isfile(cases.find(n).path("out", "spec.decided.txt"))]
    kind = oracle.FLAG_KINDS[a.oracle]
    print(f"{len(todo)}/{len(names)} to author, {a.workers} at a time, model={a.model}, "
          f"<={a.max_rounds} round(s), {a.repairs} repair(s) per phase")
    # Said once, at the top, before any of it runs.  Each case's own `asked.json` carries
    # `oracle_kind` and each report opens with `_measured_banner`, but those are for the reader
    # afterwards; a batch of fifty is exactly the run where the operator wants to know BEFORE the
    # hours are spent that the answers are coming from an answer key.
    if kind != oracle.KIND_DESIGNER:
        print(f"oracle: {kind} -- every one of these {len(todo)} specification(s) is MEASURED "
              f"against its benchmark's reference implementation, not decided by a designer.  A "
              f"reference cannot answer `any`, so the coordinates these runs pin are an upper "
              f"bound on what a designer would have pinned.", file=sys.stderr)

    led = os.path.join(cases.CASES_DIR, "AUTHOR.json")
    os.makedirs(os.path.dirname(led), exist_ok=True)
    # No pre-read.  `_ledger_write` re-reads inside its lock on every row, so this driver never
    # holds a snapshot of the file that other drivers can go on to invalidate.
    header = {"model": a.model, "allowed_tools": list(TOOLS),
              "prompts": {"decisions": DEC_PROMPT, "hard_rule": HARD_RULE,
                          "continue": CONTINUE, "inherit": INHERIT,
                          "inherit_ctxs": INHERIT_CTXS}}
    rows = []
    with concurrent.futures.ThreadPoolExecutor(max_workers=a.workers) as ex:
        futs = {ex.submit(do_case, n, a.model, a.max_rounds, a.repairs, a.resume, kind): n
                for n in todo}
        for fut in concurrent.futures.as_completed(futs):
            n = futs[fut]
            try:
                r = fut.result()
            except Exception as e:                                       # noqa: BLE001
                r = {"case": n, "status": "driver_error", "detail": f"{type(e).__name__}: {e}"}
            r["order"] = order_check(n)
            # Per row, not at the top of the file, because this ledger ACCUMULATES: every write
            # re-reads it and replaces only this case's row.  A case authored against the designer
            # in one run and re-authored against the reference in another would sit under
            # whichever label the later run wrote at the top, which is the one place a reader
            # would look and the one place it would be wrong.
            r["oracle_kind"] = kind
            r["isolation"] = {"escapes": [x["path"] for x in transcript_escapes(
                cases.find(n).dir) if x["escape"]][:20]}
            r["isolation"]["clean"] = not r["isolation"]["escapes"]
            print(f"  {n:<34} {r['status']:<16} rounds={r.get('rounds', '-')}  "
                  f"order={r['order']['verdict']}  "
                  f"escapes={len(r['isolation']['escapes'])}"
                  + (f"  open={r.get('open')}" if r.get("open") else ""))
            for e in r["isolation"]["escapes"][:6]:
                print(f"      ESCAPED: {e}")
            for v in r["order"].get("violations", [])[:4]:
                print(f"      ORDER: {v}")
            rows = _ledger_write(led, r, header)

    # `blocked_terminal` counts with `max_rounds` and not against it.  Both are cases that ran
    # every round there was any point in running and came out with a decided specification whose
    # open coordinates are declared; the only difference is that one stopped because the rounds
    # ran out and the other because the framework proved more of them could not help.  Reading
    # the second as a failure would make the early stop cost a case its result, which is the
    # opposite of what it is for.
    good = [r for r in rows if r.get("status") in ("converged", "max_rounds", "blocked_terminal")
            and (r.get("order") or {}).get("verdict") == "clean"
            and (r.get("isolation") or {}).get("clean")
            and r.get("case") in todo]
    print(f"\n{len(good)}/{len(todo)} produced a decided spec -> {os.path.relpath(led, ROOT)}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
