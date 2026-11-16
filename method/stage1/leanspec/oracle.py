#!/usr/bin/env python3
"""Stage 5's one door out: the designer.

Every other module in leanSpec derives its result from the prose.  This one asks a question, and
it is the only place in the half where a fact arrives that the document did not contain.  The
seal (`common/seal.py`) is what makes that sentence true rather than aspirational: `ask()` calls
`seal.check()` at the door, so a stage declared sealed that reaches for the designer *raises*
instead of getting an answer.

## Why there is no simulator here

The predecessor of this module had two backends, and both opened a *reference implementation*:
one compiled the witness into a testbench and drove the reference, the other ran a benchmark's
own checker against each reading emitted as RTL.  Neither exists here, and their absence is the
point rather than a gap.  A reference implementation is an answer key.  A method that needs one
to find out what a specification means can only be run where somebody has already built the
thing the specification describes -- which is to say, never, on the specification that matters.

The authority leanSpec appeals to is the **designer**: the person the prose belongs to.  A
specification is ambiguous when its author knows something the document does not say, and the
repair is to get that fact out of them and into the text.  So the question this module asks is
not "what does the implementation do", it is "which of these did you mean".

## And why there is one anyway, behind a flag

The paragraph above is about the method.  It is not about *measuring* the method, and those are
different activities that were previously served by the same code path and so could not be told
apart in a result.  A benchmark case ships a reference implementation; running the method over a
few hundred of them needs something that answers questions at three in the morning, and the
reference is the only thing available.  `KIND_REFERENCE` is that, and every guard on it exists to
keep the two activities distinguishable afterwards:

    it is never the default        `ask_all` answers with the designer unless a caller passes
                                   `kind=KIND_REFERENCE` in as many words
    `asked.json` records it        every stored answer says which authority produced it, so a
                                   sitting cannot be reinterpreted later as the other kind
    the sittings do not mix        `query_dir` puts them in different directories, so a designer
                                   answer is never replayed for a reference run or the reverse
    the report says it in words    a specification decided this way is labelled as measured
                                   against a reference, not as decided by its author

The last one is not hygiene.  On `accu` the decided arm passes five gates and a Lean determinism
proof and still fails RTLLM's own oracle -- `valid_out` a cycle early.  A certified specification
and the golden RTL already disagree about that design, so a report that did not say which of them
had answered the questions would be unreadable exactly where it mattered.

There is also a fidelity cost, and it is structural rather than a matter of care.  A reference
implementation does exactly one thing, so it can never answer **`any`**: a coordinate its author
would have declared free comes back as whichever value the RTL happens to implement, and the
specification records a decision where the truth was a degree of freedom.  It also cannot answer
`none` usefully -- it will always do *something*, and if that something is off the menu the honest
report is that the search space missed it, which is the one answer a mechanical oracle is good at.
`any` is the one it cannot give, and the count of coordinates a benchmark run pinned is therefore
an upper bound on what a designer would have pinned.

## What the designer is shown, and what they are not

    shown        the prose, the stimulus, and the distinct observable behaviours the prose
                 currently permits under it, drawn as waveforms and lettered
    not shown    the readings' names, the extraction, the diagnosis, the Lean, the pipeline's
                 own opinion of which answer is likely, or that it has one

That list is enforced twice.  The prompt is built here, from those inputs and nothing else, and
the session runs in a directory holding a copy of the prose and the question -- with
`common/confine.py` wired in as a `PreToolUse` hook, so a designer that goes looking for the case
directory is refused at the tool call rather than trusted not to try.

The behaviours are lettered and **shuffled**, deterministically, by a hash of the witness id.
`admits` enumerates readings in the order stage 1 wrote them down, and stage 1 writes the reading
it believes first often enough that presenting them in that order would be handing over a hint.
Deterministic, because a re-run that reorders the menu is a re-run that asked a different
question.

## Three answers, and all three are results

    chosen     one behaviour is what the designer meant.  It becomes the observation, and the
               elimination is mechanical: `refine.py` compares it against the predictions stage 4
               recorded BEFORE the question was asked.
    outside    none of them is.  The specification's variant space does not contain the answer --
               which is the finding a re-reading of the prose could not have produced.
    any        the designer does not care.  The coordinate is genuinely free, and saying so is an
               answer: it goes into the decided specification as a declared degree of freedom
               rather than being silently pinned to whichever reading happened to be first.

`any` is not "no answer".  A run that recorded it as one would report an open question where the
author had in fact closed it, in the direction that is hardest to notice.

## The question that is not a menu of behaviours

Stage 4 can prove that a specification's own guarantee forbids a behaviour its own definitions
admit.  That is not an ambiguity and no reading of the prose repairs it: two sentences contradict,
and one of them has to change.  It reaches this module as a `violation` witness and is put as a
choice between the two clauses -- here is the input, here is what your definitions admit under it,
here is the sentence saying that must never happen, which one is wrong.  `any` is refused for such
a question (`_verdict`), because "either sentence may stand" names no document.

## One sitting per round

Every question a round found is put to one designer at once, in `questions.md`, and answered in
one `answers.json`.  A fork can be invisible on its own and separable only jointly with another,
and a designer who never sees two questions together cannot be consistent across them.  The price
is that answers given together are correlated; `_PREAMBLE_LIST` records that trade rather than
arguing it away.

## The answers are kept

A sitting lives at `oracle/roundN/questions/`, with the prose it was asked against, the questions,
the answers, and the transcript of the session that gave them.  `asked.json` records the digest of
the document that was actually put, and a re-run replays the answers only if that digest still
matches -- logging `oracle_replay` instead of `oracle_query`, so re-running step 05 does not
re-ask an answered question and does not inflate the query count, which is one of the numbers this
method reports.  A digest that does not match is not a replay: the stored exchange moves to
`superseded-<n>/` and the questions are put again.  Nothing here overwrites an answer; `fresh=True`
archives it first, which is a thing a caller has to say out loud.
"""
from __future__ import annotations

import hashlib
import itertools
import json
import os
import re

from common import agent, seal
from common import agent_backend

from . import cases

# Read and Write, and nothing else.  No `Bash`, no `Glob`, no `Grep`: a designer answering a
# question about their own specification needs to read the two files in front of them and write
# one, and every other tool is a way to reach for the pipeline's working files.  The confinement
# hook would refuse those anyway; granting the tool and relying on the hook would make the wall
# load-bearing in a place it does not have to be.
DESIGNER = agent.Role(
    tag="designer",
    tools=("Read", "Write"),
    timeout=int(os.environ.get("LEANSPEC_ORACLE_TIMEOUT", "900")),
)

# ------------------------------------------------------- the other authority, named as one
#
# A simulator, which the designer is deliberately not given, because this role's whole job is to
# run one.  It is `agent.SIM_TOOLS` and not a bare `Bash`: the widening is three binaries, not a
# shell.  What those binaries may then NAME is the second wall -- `agent.run` sets
# `LEANSILICON_ROOT` to the sitting directory, `common/confine.py` is wired in as a `PreToolUse`
# hook from the settings file written into it, and a command naming anything outside is refused at
# the tool call.  The reference RTL is copied INTO that directory, so nothing about this role
# reaches further than the designer's role does -- it reaches the same room, which has one more
# file in it.
#
# What it must never reach is the authoring root.  It does not: an authoring session's root is the
# case sandbox and this directory is not under it, and no path here is added to any authoring
# role's `allow`.  That separation is the entire content of the claim that the method did not
# read the answer key, so it is stated here rather than left to be inferred from two call sites.
#
# The timeout is longer than the designer's because the work is different in kind.  A designer
# reads and decides; this role writes a testbench per question, compiles it, runs it, and reads a
# waveform back, which for a round of eight questions is eight build-run cycles.
REFERENCE = agent.Role(
    tag="reference",
    tools=("Read", "Write") + agent.SIM_TOOLS,
    timeout=int(os.environ.get("LEANSPEC_REFERENCE_TIMEOUT", "1800")),
)

#: The two authorities, as they are written into `asked.json`, the ledger and the report.  Values
#: rather than a boolean because a boolean would be recorded as `false` on every designer run and
#: read as "no information", where what is wanted is a positive statement of who answered.
KIND_DESIGNER = "designer"
KIND_REFERENCE = "reference_rtl"
KINDS = (KIND_DESIGNER, KIND_REFERENCE)

#: What a command line spells and what it means.  `rtl` is the short spelling the flag takes; the
#: long one is accepted too so that a value copied out of `asked.json` or a ledger row can be
#: pasted straight back into a command without a reader having to know they are the same thing.
FLAG_KINDS = {"designer": KIND_DESIGNER, "rtl": KIND_REFERENCE, KIND_REFERENCE: KIND_REFERENCE}

_ASKING = KIND_DESIGNER


def asking() -> str:
    """Who answers this process's questions.  The designer, unless something said otherwise."""
    return _ASKING


def ask_with(kind: str) -> str:
    """Name the authority for the rest of this process.  Returns what it was before.

    Process state, which is a thing to justify rather than reach for.  The alternative was a
    parameter threaded from the CLI through `pipeline.run` and `Chain.run_step` into the step
    function -- but `Chain` is `common/steps.py` and serves both halves of the framework, so that
    route puts a leanSpec oracle setting into the generic contract that runs stage 2's authoring
    steps as well.  A setting that has to be understood by code it does not apply to is worse than
    one place that holds it.

    What makes it safe is not that it is only set once.  It is that it cannot be set silently:
    `ask_all` records `oracle_kind` on the sitting, on every question, and in `asked.json`;
    `refine.resolve` puts it in `resolution.json`'s `oracle` field; `step_resolve` reads this
    function explicitly and writes what it read into its own step document.  A process whose
    authority was set wrongly produces a run that says so in five places, rather than a run that
    looks like a designer's.
    """
    global _ASKING
    if kind not in KINDS:
        raise ValueError(f"unknown oracle kind {kind!r}; expected one of {list(KINDS)}")
    was, _ASKING = _ASKING, kind
    return was


#: File extensions a reference implementation is written in.
_RTL = (".v", ".sv")


def reference_files(case: cases.Case) -> tuple[list[str], str | None]:
    """The benchmark's own implementation of this design, and why there isn't one if there isn't.

    Two shapes, because the two corpora on disk have two.  RTLLM gives each design a directory
    holding `design_description.txt` beside `verified_<name>.v`; VerilogEval and chipbench give a
    flat directory of `ProbNNN_<name>_prompt.txt` beside `ProbNNN_<name>_ref.sv`.  Both are found
    from `case.source`, which is the one field that records where the prose came from -- so a case
    registered from a loose file gets no reference and is told so, rather than being handed the
    reference of whatever else happens to sit in that directory.

    `LEANSPEC_REFERENCE` overrides, naming either a file or a directory of them.  It exists for
    the corpus this has not been taught yet, and it is an environment variable rather than a case
    field because pointing a case at a different answer key is a property of one measurement run
    and not of the case, which `cases.register` is right to refuse to let drift.

    **The testbench that ships beside the reference is deliberately not included.**  It answers a
    different question -- "does this design pass the benchmark's checks" -- and its expected-value
    tables would let this role answer from a table of outputs instead of from the design.  What is
    wanted is what the RTL does at the input sequence in the question, and only the RTL says that.

    Returns `(paths, why)`: a non-empty list and `None`, or an empty list and a sentence.  A
    missing reference is a reported reason and not an exception, because the caller's honest
    handling of it is to record that the round could not be answered -- the same shape as a
    designer who did not reply.
    """
    env = os.environ.get("LEANSPEC_REFERENCE", "").strip()
    if env:
        if os.path.isfile(env):
            return [env], None
        if os.path.isdir(env):
            got = sorted(os.path.join(env, f) for f in os.listdir(env)
                         if f.endswith(_RTL) and "test" not in f.lower())
            return (got, None) if got else ([], f"LEANSPEC_REFERENCE={env} holds no RTL file")
        return [], f"LEANSPEC_REFERENCE={env} is neither a file nor a directory"

    if not case.source:
        return [], (f"{case.name} records no `source`, so there is no benchmark directory to "
                    f"look in for a reference implementation")
    d = os.path.dirname(os.path.abspath(case.source))
    if not os.path.isdir(d):
        return [], f"the directory {case.source} came from no longer exists"

    # The flat-directory shape first, because its designs share a directory: `Prob067_countslow_
    # prompt.txt` sits beside 150 other designs' files, and taking every `.sv` in that directory
    # would hand this role the answer key to all of them.  The stem is what makes it one design.
    stem = os.path.basename(case.source)
    for suffix in ("_prompt.txt", ".txt"):
        if stem.endswith(suffix):
            stem = stem[:-len(suffix)]
            break
    sibs = [os.path.join(d, stem + "_ref" + e) for e in _RTL]
    got = [p for p in sibs if os.path.isfile(p)]
    if got:
        return got, None

    # The per-design-directory shape.  Everything in it that is RTL and is not a testbench: for
    # RTLLM that is `verified_accu.v` and not `testbench.v`.
    got = sorted(os.path.join(d, f) for f in os.listdir(d)
                 if f.endswith(_RTL) and "test" not in f.lower() and "_tb" not in f.lower())
    if got:
        return got, None
    return [], (f"no reference implementation found for {case.name}: neither {stem}_ref"
                f"{{{','.join(_RTL)}}} nor a non-testbench RTL file in {d}")


def _manifest(paths: list[str]) -> str:
    """A digest over the reference files' names and contents, as one string.

    Which answer key answered is part of who answered.  `question_sha256` binds a stored answer to
    the questions it was given for; this binds it to the implementation it was read out of, so a
    reference that was corrected between two runs supersedes the sitting instead of having its old
    verdicts replayed under the new file's name.
    """
    h = hashlib.sha256()
    for p in sorted(paths, key=os.path.basename):
        h.update(os.path.basename(p).encode())
        h.update(b"\0")
        with open(p, "rb") as f:
            h.update(hashlib.sha256(f.read()).hexdigest().encode())
        h.update(b"\n")
    return h.hexdigest()

ANSWERS = "answers.json"
QUESTIONS = "questions.md"
PROSE = "spec.txt"
# The one-question-per-designer form these two name is no longer asked; the names stay because
# `_supersede` still has to recognise and keep such an exchange when it finds one on disk from a
# run made before the sitting became the unit.  Archived evidence is not obsolete evidence.
ANSWER = "answer.json"
QUESTION = "question.md"
# Written beside the answer at the moment a question is actually put, and holding the digest of
# the question that was put.  It is what makes a replay checkable: `answer.json` records a
# LETTER, and a letter means nothing except against the option list the designer was shown.  The
# same witness id can carry a different list in a later round -- a coordinate that was three
# readings wide can narrow to two -- and replaying `B` across that boundary writes into the
# specification an observation the designer never chose, with the ledger showing an answer.
ASKED = "asked.json"

# Enough letters that no witness runs out; a fork with more readings than this is one whose menu
# the designer could not hold in their head anyway, and `bestSplit` exists to avoid it.  I and O
# are omitted: in a waveform they read as 1 and 0.
LETTERS = "ABCDEFGHJKLMNPQRSTUVWXYZ"


def _label(pos: int) -> str:
    """The `pos`-th menu label: `A`..`Z`, then `AA`, `AB`, ...

    The comment above is right about what a menu *should* be and was wrong about what one *was*.
    A witness's menu is the number of distinct behaviours, not the number of readings, and until
    `focus` existed that was the product of this question with every other open coordinate --
    so `LETTERS[pos]` raised `IndexError` on 8 of `accu`'s 10 witnesses, at the point of asking,
    after stages 1 through 4 had already been paid for.

    `focus` is the fix; this is the guarantee.  Bijective base-24 costs four lines and turns a
    class of crash into a page that is merely long, which is a thing a reader can see and judge.
    Truncating to 24 would have been the other option and is the one that must not be taken: the
    dropped behaviours would be invisible in the record, and an `outside` verdict would then be
    unfalsifiable.
    """
    n, out = pos, ""
    while True:
        out = LETTERS[n % len(LETTERS)] + out
        n = n // len(LETTERS) - 1
        if n < 0:
            return out


def _unlabel(a: str) -> int:
    """`_label`'s inverse, or `-1` for anything that is not a label."""
    if not a or any(c not in LETTERS for c in a):
        return -1
    n = 0
    for c in a:
        n = n * len(LETTERS) + LETTERS.index(c) + 1
    return n - 1


# ------------------------------------------------------------------------- the waveform

def _val(v) -> str:
    """One cell.  `x` survives as `x`; a `None` is a don't-care and is drawn as one.

    Values arrive as whatever the Lean emitters printed: a number for a number, the string `"x"`
    for an unknown.  A renderer that coerced `"x"` to `0` would be making, at the presentation
    layer, the same mistake a checker makes when it counts an X as a match.
    """
    if v is None:
        return "-"
    if isinstance(v, bool):
        return "1" if v else "0"
    return str(v)


def _table(rows: list[tuple[str, list]], n: int, indent: str = "  ") -> str:
    """A signal-per-row, step-per-column table, wide enough for its widest cell."""
    if not rows or not n:
        return indent + "(nothing)"
    cells = [[_val(v) for v in vals] for _, vals in rows]
    w = max([len(c) for row in cells for c in row] + [len(str(n - 1)), 1]) + 1
    label = max(len(name) for name, _ in rows) + 1
    out = [indent + "step".rjust(label) + " |" + "".join(str(i).rjust(w) for i in range(n)),
           indent + "-" * (label + 2 + w * n)]
    for (name, _), row in zip(rows, cells):
        out.append(indent + name.rjust(label) + " |" + "".join(c.rjust(w) for c in row))
    return "\n".join(out)


def _signals(seq: list[dict]) -> list[str]:
    """Every signal any step of a sequence mentions, in first-appearance order.

    Not sorted: the order the emitter printed them in is the order the specification declares
    them in, and a waveform whose rows are alphabetised is one whose reader has to reconstruct
    the interface to read it.
    """
    out: list[str] = []
    for st in seq or []:
        for k in (st or {}):
            if k not in out:
                out.append(k)
    return out


def _steps_of(trace) -> list[dict]:
    """A context or an observation as a list of per-step signal maps.

    `Ctx` and `Obs` serialise to `{"steps": [...]}`; a recorded observation is sometimes already
    the bare list.  Both arrive here, and until this existed the two callers below disagreed about
    which one they had: the stimulus unwrapped by hand and the option waveforms did not, so the
    first question ever put to an oracle raised `'str' object has no attribute 'get'` — iterating
    a dict yields its keys, and `"steps"` is a string.

    `emit._steps_of` and `refine._seq` are this same function.  Three copies is two too many, but
    both of those modules import this one, so the shared version cannot live here and moving it
    is a change to three call graphs to delete four lines.
    """
    if isinstance(trace, dict):
        return list(trace.get("steps") or [])
    return list(trace or [])


def waveform(seq, indent: str = "  ") -> str:
    seq = _steps_of(seq)
    rows = [(s, [(st or {}).get(s) for st in seq]) for s in _signals(seq)]
    return _table(rows, len(seq), indent)


def stimulus(ctx, indent: str = "  ") -> str:
    """A context as the oracle has to run it: its parameters, then its waveform.

    `ctxJson` serialises a `Ctx` as `{"params": {...}, "steps": [...]}` and `waveform` reads only
    the second, because a parameter is not a signal and has no column in a step table.  Dropping
    it is silent and it is not harmless: a parameter is part of the context the prediction was
    computed at, so an oracle that runs the design at a different value answers a different
    question, and the answer is recorded against this one.

    Measured on `freq_divbyodd`'s `num_div_one_in_scope`, which asks about NUM_DIV = 1 and whose
    own record says the reference was run "at the default NUM_DIV = 5 rather than at NUM_DIV = 1
    -- the question's waveform table names no parameter value".  The reading came back consistent
    with every candidate, which is what an answer to another question looks like from here.

    Rendered above the table rather than as a row in it: a row would put one value under step 0
    and blanks under the rest, which reads as a signal that is driven once and then released.
    """
    params = ctx.get("params") if isinstance(ctx, dict) else None
    wave = waveform(ctx, indent)
    if not params:
        return wave
    named = ", ".join(f"{k} = {_val(v)}" for k, v in params.items())
    return f"{indent}parameters: {named}\n\n{wave}"


# --------------------------------------------------------------- the menu, and its order

def _relevant(w: dict) -> list[str]:
    """The prediction tags this witness is about, and only those.

    Stage 3 evaluates *every* predicate at *every* context it emits, so a fork's witness carries
    the other coordinates' tags too -- a sibling fork's readings, a hole's values.  Those are
    answers to their own witnesses.  Putting them on this menu would offer behaviours this
    question cannot eliminate, and the designer choosing one would come back looking like an
    `outside`.

    The bare `hole:<n>` tag is dropped for the reason `refine.py` drops it from the count: it is
    the unconstrained reading, consistent with anything the hole could produce, so it contributes
    every behaviour and distinguishes none.
    """
    preds = w.get("predicted") or {}
    if w.get("kind") in ("ambiguity", "repair"):
        pre = str(w.get("choice")) + ":"
    else:
        pre = "hole:" + str(w.get("hole") or w["id"].split(":", 1)[-1]) + "="
    return [t for t in preds if t.startswith(pre)]


def _key(obs) -> str:
    return json.dumps(obs, sort_keys=True)


# A coordinate is one signal at one step: `("data_out", 3)`.  Searching subsets of them is
# exponential, so the search is bounded and gives up rather than hanging -- see `focus`.
_FOCUS_BUDGET = 20000


def _coords(preds: dict, tags: list[str]) -> list[tuple[str, int]]:
    """Every (signal, step) that any relevant prediction assigns a value to, sorted.

    Sorted rather than first-appearance because this feeds a subset search whose tie-breaks must
    be reproducible from the record; the *rendered* order is still `_signals`', which is the
    emitter's.
    """
    out = set()
    for t in tags:
        for obs in preds[t] or []:
            for i, st in enumerate(_steps_of(obs)):
                for k in (st or {}):
                    out.add((k, i))
    return sorted(out)


def _project(obs, foc: list[tuple[str, int]] | None) -> dict | list:
    """An observation with every coordinate outside `foc` erased.

    Erased, not defaulted: an omitted signal is a don't-care to `refine._matches` and draws as
    `-` in a waveform, so a projected option asserts exactly the coordinates it was reduced to
    and nothing else.  A step that keeps nothing becomes `None`, which is the same don't-care one
    level up.
    """
    if foc is None:
        return obs
    keep: dict[int, set] = {}
    for k, i in foc:
        keep.setdefault(i, set()).add(k)
    steps = _steps_of(obs)
    out = []
    for i in range(len(steps)):
        st = {k: v for k, v in (steps[i] or {}).items() if k in keep.get(i, ())}
        out.append(st or None)
    return {"steps": out}


def _refutable(sets: dict[str, set], tags: list[str]) -> frozenset:
    """The readings this menu can eliminate: those some option on it is inconsistent with.

    `refine` keeps a reading when *any* of its predictions matches the chosen behaviour, so a
    reading is refutable here exactly when the union of the others contains a behaviour it does
    not admit.  This is the quantity a projection may not lose.
    """
    return frozenset(t for t in tags
                     if set().union(*[sets[u] for u in tags if u != t]) - sets[t])


def focus(w: dict) -> list[tuple[str, int]] | None:
    """The coordinates this question is actually about, or `None` to keep the whole observation.

    ## Why a menu needs one

    `_relevant` already refuses to put a sibling coordinate's *readings* on this menu, because
    offering behaviours this question cannot eliminate makes a `chosen` answer look like it
    settled something it did not.  The same is true one axis over, and was not being done: the
    behaviours themselves differ in coordinates this question does not control.  An open hole
    widens both sides of a fork -- `witness.py` says so in as many words -- so the menu is the
    *product* of this question with every other still-open one.

    On `accu` that product was 596 waveforms for a single two-way fork about `valid_in_alignment`,
    of which the answer was scored on one bit.  A designer picking a letter there would be
    answering five questions at a context chosen to be minimal for a different one, and four of
    those five answers would be dropped on the floor.  It also overran the letter menu outright:
    `LETTERS` holds 24 because its author reasoned that a fork with more readings than that is
    unaskable anyway -- true, and the menu had stopped being the number of readings.

    ## What may not be lost

    Reducing a menu is dangerous in the direction the output does not show: drop the wrong
    behaviour and a `chosen` answer eliminates a reading it should not have, or an `outside`
    reports a hole in the variant space that was an artifact of the reduction.  So the subset is
    constrained, not chosen for size:

      * every reading the full menu could refute, the projected menu still refutes (`_refutable`);
      * every pair of readings that admitted *disjoint* behaviours here still does, so a witness
        where any answer refutes something keeps that property;
      * a menu with two or more behaviours stays that way -- a one-option question is not one.

    Subject to those, the smallest subset wins, then the smallest menu.  The result is a partition
    of the same behaviours rather than a truncation of them: each original behaviour still maps
    onto exactly one option, and an option carries the union of its members' tags, which can only
    make an answer *less* eliminating than the unprojected one.  Nothing is silently dropped.

    Correlation is why this searches subsets rather than testing coordinates one at a time.  On
    `accu`, `reset_partial_sum`'s readings agree on the value set of every single coordinate and
    differ only in which values occur *together*; per-coordinate filtering would have found
    nothing to keep and quietly turned a real question into a one-option page.  The pair
    `{data_out@1, valid_out@2}` separates them, and the size-1 pass simply fails to satisfy
    `_refutable` and moves on.

    `None` means no projection: the search found nothing admissible, or ran past `_FOCUS_BUDGET`.
    Then the menu is what it was before this function existed -- possibly huge, never wrong.
    """
    preds = w.get("predicted") or {}
    tags = _relevant(w)
    if len(tags) < 2:
        return None
    sets = {t: {_key(o) for o in (preds[t] or [])} for t in tags}
    whole = set().union(*sets.values())
    if len(whole) < 2:
        return None
    want = _refutable(sets, tags)
    disjoint = [(a, b) for a, b in itertools.combinations(tags, 2) if not (sets[a] & sets[b])]

    # Only coordinates that actually vary can carry information; a constant one enlarges the
    # search space by a factor of two and can never be the reason two behaviours differ.
    cs = [c for c in _coords(preds, tags)
          if len({_key(_project(o, [c])) for t in tags for o in (preds[t] or [])}) > 1]
    spent = 0
    for size in range(1, len(cs) + 1):
        best = None
        for sub in itertools.combinations(cs, size):
            spent += 1
            if spent > _FOCUS_BUDGET:
                return list(best[1]) if best else None
            P = {t: {_key(_project(o, sub)) for o in (preds[t] or [])} for t in tags}
            seen = set().union(*P.values())
            if len(seen) < 2 or _refutable(P, tags) != want:
                continue
            if any(P[a] & P[b] for a, b in disjoint):
                continue
            if best is None or (len(seen), sub) < (best[0], best[1]):
                best = (len(seen), sub)
        if best is not None:
            return list(best[1])
    return None


def options(w: dict) -> list[dict]:
    """The distinct behaviours the prose permits at this witness's stimulus.

    Deduplicated on the observation, not on the reading.  Two readings that predict the same
    trace are one behaviour, and offering it twice would ask the designer to tell apart things
    that are not distinguishable -- and would make a `chosen` answer look as though it eliminated
    a reading it cannot possibly eliminate.  The tags predicting each behaviour ride on the
    option and are NOT rendered: they are what the answer is scored against, afterwards.

    The observation is first projected onto `focus(w)`, which is the same argument applied to
    coordinates instead of readings; two behaviours that differ only outside the focus are one
    option here for exactly the reason two readings predicting one trace are.

    ## The one menu that is not made of behaviours

    A `violation` witness has no `predicted` and never will.  Stage 4 proved that the definitions
    admit an observation the stated guarantee forbids: the two sentences contradict, so there is
    no reading of the prose under which both hold and no *alternative behaviour* to offer -- the
    property says "not that" without saying what instead.  What the designer is choosing between
    is therefore the two clauses, and the menu is built out of them.

    Both options are put on the same page in the same form, and neither is marked as the likely
    one, for the same reason the behaviour menus are shuffled: the pipeline has an opinion about
    which sentence a specification usually gets wrong, and it is not evidence.  `order` shuffles
    this menu too, so which of the two comes first is a function of the question and not of the
    order they are written here.
    """
    if w.get("kind") == "violation":
        return [
            {"tags": ["definitions"], "obs": None,
             "text": "The behaviour above is what I meant. The sentence that states the "
                     "guarantee is wrong -- it does not hold in the case shown, and it has to "
                     "be corrected or dropped."},
            {"tags": ["property"], "obs": None,
             "text": "The guarantee above is what I meant. The behaviour is wrong -- the "
                     "sentences that define what the design does permit something they should "
                     "not, and they have to be tightened."},
        ]
    preds = w.get("predicted") or {}
    foc = focus(w)
    seen: dict[str, dict] = {}
    for tag in _relevant(w):
        for obs in preds[tag] or []:
            o = seen.setdefault(_key(_project(obs, foc)),
                                {"obs": _project(obs, foc), "tags": []})
            if tag not in o["tags"]:
                o["tags"].append(tag)
    return list(seen.values())


def _opt_key(o: dict) -> str:
    """What makes two options on a menu different options.

    The behaviour, when there is one; the clause text, when the menu is a clause menu.  Keying a
    clause menu by its absent `obs` would give every violation asked at the same context the same
    two-`null` menu -- so two different contradictions would hash to one `question_id`, and the
    second would silently replay the answer given to the first.
    """
    return "text:" + o["text"] if o.get("text") is not None else _key(o.get("obs"))


def question_id(w: dict) -> str:
    """What makes two askings the same asking: the stimulus, and the menu.

    Not the witness id.  A fork with three readings is diagnosed as pairwise comparisons, so it
    arrives here as several witnesses -- `ambiguity:q:a:b`, `ambiguity:q:a:c` -- and `_relevant`
    scopes every one of them to the same question, at the same context, with the same menu.  They
    are one question and must be asked once: `refine.resolve` caches on this, and putting the
    same page in front of the designer twice would inflate the query count this method reports
    while learning nothing.

    A clause menu needs a third component, and the reason is that its menu is a constant.  The two
    options a violation offers -- "the definitions are what I meant", "the guarantee is what I
    meant" -- are worded the same for every contradiction, because the sentences they refer to are
    printed in the body rather than in the options.  So two DIFFERENT broken guarantees, proved at
    the same context, would hash to the same question, and the second would silently replay the
    answer given to the first: one query spent, two contradictions recorded as adjudicated, and
    the second one's answer never asked for.  What tells them apart is the property, so the
    property is in the hash -- and only for that kind, so that every fork and hole asked before
    this existed still hashes to exactly the id it did.
    """
    key = {"ctx": (w.get("ctx") or {}), "menu": sorted(_opt_key(o) for o in options(w))}
    if w.get("kind") == "violation":
        key["property"] = w.get("property")
    return hashlib.sha256(json.dumps(key, sort_keys=True).encode()).hexdigest()[:16]



def order(qid: str, n: int) -> list[int]:
    """A deterministic permutation of `n` options, seeded by the question.

    Deterministic, so that re-asking is asking the same question; a permutation, so that the
    order stage 1 happened to write the readings in is not a recommendation.  Seeded by the
    question rather than the witness so that the *same* question drawn from two witnesses reads
    identically -- otherwise a cached answer's letter would name a different behaviour on the
    page the second witness would have produced.

    Fisher-Yates over a byte stream derived from the seed: no PRNG state, no dependence on the
    interpreter's hash randomisation, and reproducible from the id alone by anyone reading the
    record.
    """
    idx = list(range(n))
    stream = hashlib.sha256(qid.encode()).digest() * (n // 32 + 2)
    for i in range(n - 1, 0, -1):
        j = stream[n - i] % (i + 1)
        idx[i], idx[j] = idx[j], idx[i]
    return idx


# ---------------------------------------------------------------------------- the prompt

# There is one brief and it is the list form.  An earlier version put each fork to its own
# designer, one question and one `answer.json` per witness, and it is gone rather than kept
# alongside: two doors out of a sealed pipeline is one more than the seal can be argued about,
# and a path nothing calls is a path nothing tests.
#
# The reason for the list is a finding rather than a saving: a coordinate can be invisible on its
# own and separable only jointly with another, and a designer answering one question at a time
# cannot be consistent across two questions they never see together.  `accu` round 3 is the case
# that showed it -- `report_gated_by_reset` is observable only where a group completes with the
# reset low, which needs `reset_timing`'s other reading, so the two had to be put together or
# neither could move.
#
# What this costs is independence.  Answers given in one sitting are correlated: reading question
# 5 can change what you would have said to question 1.  That is a real loss and it is recorded
# here rather than argued away -- the trade was made deliberately, for consistency across a set
# of questions about ONE design, which is what a designer actually has.
_PREAMBLE_LIST = """\
You are the author of the specification in `spec.txt`. Read it.

A reader has gone through it and found {n} points where it does not determine what the design
does. They are not asking you to justify the text, to defend it, or to rewrite it. They are
asking what you meant, and every answer is a fact you know and the document does not say.

Each question below gives an input sequence and every output behaviour your specification
currently permits under it. All of them are consistent with what you wrote. One of them is
presumably what you had in mind.

Answer all {n}. They are about the same design, so your answers should be consistent with each
other -- if two questions turn out to be about the same underlying fact, say so in `why` and
answer both the same way. If a question only makes sense given how you answered another, say
that too.
"""

# Added to the brief only when the round found one, because a brief that describes a shape of
# question the round does not contain is a brief that has to be read past.
_PREAMBLE_VIOLATIONS = """\
**{n} of the questions below {isare} not of that kind**, and say so at the top of the question.
There the reader has not found something your specification leaves open -- they have proved that
it says two things that cannot both be true, and shown you the case where they come apart.
Neither of the two sentences can stay as it is. Such a question asks which one to change, and
"either is fine" is not an available answer to it.
"""

_HOWTO_LIST = """\
## Answers

Write a file called `answers.json` in this directory, and nothing else. One entry per question,
all {n} of them, keyed by the question number:

    {{"answers": [{{"q": 1, "answer": "<letter>", "why": "<one or two sentences>"}},
                  {{"q": 2, "answer": "<letter>", "why": "..."}}]}}

Three answers are possible for each question and all three are real:

  * a **letter** -- that behaviour is what you meant.
  * **"none"** -- none of them is what you meant. Say what the design does instead, in `why`.
    This is not a failure to answer: it means the reader's list of possibilities is missing the
    real one, which is worth more than any of the letters.
  * **"any"** -- you do not care. The design is free to do any of these and still be correct.
    Say so plainly if it is so; it will be written into the specification as a stated degree of
    freedom rather than guessed at. The one exception is a question that says at the top that it
    is about two sentences that contradict each other: there, "any" is not available, because
    whichever sentence you keep the other one is false.

Do not pick a letter you are unsure of in preference to "none" or "any". A wrong letter is
written into the specification as though you had stated it.

Answer every question. A question you leave out is recorded as unanswered, which is a worse
outcome than "none" -- "none" tells the reader their list was wrong, and silence tells them
nothing at all.
"""

# ------------------------------------------------- the same questions, put to the answer key
#
# A separate brief rather than a parameterised one, because almost every sentence of the
# designer's is false here.  "You are the author" is not true; "one of them is presumably what you
# had in mind" is not true; and "any" is offered there as a first-class answer and must not be
# offered here at all.  Editing four clauses of a shared string would have left a brief that reads
# as though a designer wrote it, which is the exact confusion the whole flag exists to prevent.
#
# It also has a side effect worth naming: the two briefs differ, so the two `questions.md` differ,
# so their `question_sha256` differ.  A designer's stored answer cannot be replayed for a
# reference run even if `query_dir` were ever collapsed back into one directory.  That is a second
# barrier and not the primary one -- `query_dir` splitting by kind is -- but two walls in front of
# "the ledger says a designer answered when a simulator did" is the right number.
_PREAMBLE_REFERENCE = """\
There is a reference implementation of a hardware design in this directory: {files}. It is the
authority on what this design does, and it is the only authority here.

There are {n} question(s) below. Each one is a point where the design's written specification does
not determine the behaviour, found by a reader going through it. Your job is to determine it, by
running the implementation.

Each question gives an input sequence and every output behaviour the specification currently
permits under it. Simulate the reference under that input sequence, read the outputs it actually
produces, and report which of the listed behaviours is the one it produced.

Do not pick the candidate that looks most plausible, most conventional, or most like what the
module's source appears to say. Run it. You have `iverilog` and `vvp`: write a testbench in this
directory, compile, run, and read the outputs off the simulation, one line per step in the same
order the question's waveform shows them.
"""

# The violation shape, restated for a simulator.  The designer is asked which of two sentences
# they meant to keep, which is a question about intent; a reference has no intent, so it is asked
# the one thing it can answer -- which of the two the implementation actually contradicts.
_PREAMBLE_VIOLATIONS_REFERENCE = """\
**{n} of the questions below {isare} not of that kind**, and say so at the top of the question.
There the reader has not found something the text leaves open -- they have proved that the
specification says two things that cannot both be true, and shown the case where they come apart.
Such a question shows a waveform the definitions admit, a sentence saying that waveform must never
happen, and asks which of the two to change.

Answer it by simulating the reference at that input sequence and seeing which of the two claims it
breaks. If the reference produces the waveform shown, the sentence forbidding it is the one that
is wrong about this design. If the reference satisfies that sentence, the definitions that admit
the waveform are. If it breaks both, or neither, answer "none" and say what it did.
"""

_HOWTO_REFERENCE = """\
## Answers

Write a file called `answers.json` in this directory. One entry per question, all {n} of them,
keyed by the question number:

    {{"answers": [{{"q": 1, "answer": "<letter>", "why": "<what you observed>"}},
                  {{"q": 2, "answer": "<letter>", "why": "..."}}]}}

Two answers are possible:

  * a **letter** -- the reference's outputs under that input sequence are the ones shown under
    that letter, step for step.
  * **"none"** -- the reference produced something that is not on the list. Put the waveform you
    observed in `why`, in the shape the question showed the candidates in. This is a useful
    answer and not a failure to answer: it says the reader's list of possibilities was missing the
    real behaviour, which is worth more than any of the letters.

**There is no "any".** A designer answering these questions may say the design is free to do any
of several things, and that is a real answer from them. It is not available to you: you are
reporting what one implementation did, and it did one thing. Two candidates that look equally
defensible are not a reason to say either is allowed -- simulate, and report the one it produced.

In `why`, say what you observed and how you observed it: the outputs you read off the simulation,
and enough about the testbench that someone re-running it would get the same answer. The letter
is the answer and `why` is the evidence for it, and both are kept.

Answer every question. A question you leave out is recorded as unanswered, which is a worse
outcome than "none".
"""

_TIMING = {
    "after_edge": "each step's outputs are read after the clock edge that consumed that step's "
                  "inputs",
    "before_edge": "each step's outputs are read while that step's inputs are applied, before "
                   "the clock edge consumes them",
}


# Whose specification it is.  The question bodies address the designer as its author -- "your
# specification", "every sentence you wrote" -- and to a simulator every one of those is false: it
# did not write the document, it is deliberately not given the document, and a question that
# claims otherwise is a question that reads as though the wrong brief was pasted in.
#
# So the possessive is a parameter and NOTHING else about a body is.  The stimulus, the timing
# note, the menu and the letters are the same bytes for either authority, which is what makes an
# answer from one comparable with an answer from the other -- if the two were shown different
# waveforms, a benchmark run would not be a measurement of this method but of a second method
# that happens to share its name.  The designer's strings are unchanged to the byte, so every
# sitting already recorded still matches its `question_sha256` and does not supersede.
_VOICE = {
    KIND_DESIGNER: {
        "ambiguity": "Two or more readings of your specification are possible here, and they "
                     "disagree about the outputs below.",
        "incompleteness": "Your specification does not pin down the outputs below: more than one "
                          "behaviour satisfies every sentence you wrote.",
        "permits": "The behaviours your specification permits",
        "does": "What your specification says the design does here",
        "never": "What your specification also says must never happen",
        "read_out_of": "That sentence was read out of {b} of your document.",
        "both": "Both claims are your specification's, so the document as written is not "
                "implementable: no design can do what the first part defines and still satisfy "
                "the second.",
    },
    KIND_REFERENCE: {
        "ambiguity": "Two or more readings of the design's specification are possible here, and "
                     "they disagree about the outputs below.",
        "incompleteness": "The design's specification does not pin down the outputs below: more "
                          "than one behaviour satisfies every sentence of it.",
        "permits": "The behaviours the specification permits",
        "does": "What the specification says the design does here",
        "never": "What the specification also says must never happen",
        "read_out_of": "That sentence was read out of {b} of the document.",
        "both": "Both claims are the specification's, so the document as written is not "
                "implementable: no design can do what the first part defines and still satisfy "
                "the second.",
    },
}


def _question_body(w: dict, opts: list[dict], perm: list[int],
                   probe: dict | None, depth: str = "##",
                   kind: str = KIND_DESIGNER) -> list[str]:
    """One question's stimulus and menu, without the brief or the answer instructions.

    Shared by the single-question and list forms so the two cannot drift: what a designer is
    shown about one fork is the same text whether it arrives alone or as item 4 of 7.  `depth`
    shifts the headings so the list form can nest them under a per-question heading.

    `kind` swaps the possessive and nothing else; see `_VOICE`.
    """
    v = _VOICE[kind]
    if w.get("kind") == "violation":
        return _violation_body(w, opts, perm, probe, depth, kind)

    L = []
    if w.get("kind") == "incompleteness":
        L += [v["incompleteness"], ""]
    else:
        L += [v["ambiguity"], ""]

    L += [f"{depth} The input sequence", "", "```", stimulus(w.get("ctx")), "```", ""]
    L += _timing(probe, depth)

    L += [f"{depth} {v['permits']}", ""]
    for pos, i in enumerate(perm):
        L += [f"{depth}# {_label(pos)}", "", "```", waveform(opts[i]["obs"]), "```", ""]
    return L


def _timing(probe: dict | None, depth: str) -> list[str]:
    """How to read the waveforms: which edge the outputs are sampled on, and the hidden reset.

    Factored out because both question shapes need it and neither may have a different answer to
    it -- a designer told the outputs are read after the edge in question 3 and before it in
    question 4 has been shown two different circuits.
    """
    if not probe:
        return []
    L = []
    note = _TIMING.get(probe.get("sample"))
    if note:
        L += [f"One step is one clock cycle, and {note}.", ""]
    r = probe.get("reset")
    if r:
        L += [f"`{r.get('name')}` is held active ({r.get('active')}) for {r.get('cycles')} "
              f"cycle(s) before step 0, and is not shown.", ""]
    return L


def _violation_body(w: dict, opts: list[dict], perm: list[int],
                    probe: dict | None, depth: str,
                    kind: str = KIND_DESIGNER) -> list[str]:
    """A contradiction, put as a choice between the two sentences that make it.

    Deliberately *not* the shape of the other questions, because it is not that kind of question.
    The others ask which of several behaviours your specification permits is the one you meant;
    this one has already established that your specification permits a behaviour it elsewhere
    forbids, so there is nothing to pick between and no answer that leaves the document as it is.
    Two clauses, one of them wrong, and only the author knows which.

    What is shown, in order: the input, the behaviour the definitions admit under it, and the
    sentence that says that behaviour must not happen.  In that order because the guarantee is
    the claim under test and a reader shown it first will read the waveform looking for the
    violation rather than reading what the waveform says.

    `any` is refused here rather than accepted and discounted later, and it is refused on the
    page as well as in `_verdict`: on a fork "I don't care" is a real answer -- the coordinate is
    free -- and a designer who has been told all their lives that it is an option will reach for
    it under a question that looks superficially like the others.  "Either sentence may stand" is
    not available when the two contradict.

    A reference is asked the same question with one clause changed, and it is the clause about
    knowing: "only you know which" is true of a designer and meaningless to a simulator, which is
    told instead to find out which of the two the implementation breaks.  That instruction is in
    `_PREAMBLE_VIOLATIONS_REFERENCE` rather than here, so the body stays what it is for both --
    the input, the admitted waveform, the guarantee, and the two sentences.
    """
    v = _VOICE[kind]
    ref = kind == KIND_REFERENCE
    prop = w.get("property", "?")
    L = ["**This question is not like the others.** The rest of them ask which of several "
         "behaviours you meant. This one is about two sentences in your specification that "
         "cannot both be true. One of them has to change, and only you know which.", ""]
    if ref:
        L = ["**This question is not like the others.** The rest of them ask which of several "
             "behaviours the reference produced. This one is about two sentences in the design's "
             "specification that cannot both be true. One of them has to change, and what the "
             "reference does decides which.", ""]

    L += [f"{depth} The input sequence", "", "```", stimulus(w.get("ctx")), "```", ""]
    L += _timing(probe, depth)

    L += [f"{depth} {v['does']}", "",
          "Reading the sentences that define the behaviour, this is admitted:", "",
          "```", waveform(w.get("admitted")), "```", ""]
    n_admits = len(w.get("admits") or [])
    if n_admits > 1:
        L += [f"({n_admits} behaviours are admitted at this input; the one above is the one the "
              f"guarantee below rejects.)", ""]

    L += [f"{depth} {v['never']}", "",
          f"> {w.get('statement', '')}", ""]
    if w.get("basis"):
        b = w["basis"] if isinstance(w["basis"], str) else ", ".join(w["basis"])
        L += [v["read_out_of"].format(b=b), ""]
    L += ["The waveform above breaks it. " + v["both"], ""]

    L += [f"{depth} Which one is wrong?", ""]
    for pos, i in enumerate(perm):
        L += [f"**{_label(pos)}.** {opts[i]['text']}", ""]
    L += ['There is no "any" for this question: whichever sentence you keep, the other one is '
          'false as written. If neither option is right -- if the real fault is somewhere else '
          'entirely -- answer "none" and say what it is.', ""]
    return L



def questions_markdown(prose_name: str, items: list[dict], probe: dict | None,
                       kind: str = KIND_DESIGNER, files: list[str] | None = None) -> str:
    """The whole of what the answering authority sees when the round's questions are put.

    Numbered `1..n` in the order given, and the caller orders them by a digest rather than by the
    diagnosis's own order: which questions the pipeline groups together, and in what sequence, is
    a statement about our reading of the specification and not something the designer is owed.
    Within a question the menu is shuffled exactly as it is in the single-question form.

    `kind` swaps the brief, the closing line, and the possessive in each question's framing
    sentence.  It does not swap the QUESTION: the input sequence, the timing note, the menu and
    its letters are the same bytes for either authority, which is what makes an answer from one
    comparable with an answer from the other.  If the reference and the designer were shown
    different waveforms, a run that used the reference would not be a measurement of the method;
    it would be a measurement of a second method that happens to share a name.  What `_VOICE`
    changes is who the document belongs to -- "your specification" is false addressed to a
    simulator, which did not write it and is deliberately not given it.

    The closing line differs because the two rooms differ.  A designer is given the prose and
    asked what they meant by it; a reference sitting has no `spec.txt` in it at all, because
    handing the implementation's operator the text would let them answer from the text -- which
    would make it a second and much worse designer, and would do it invisibly, since the answer
    format cannot distinguish "I simulated" from "I read the paragraph and guessed".
    """
    nv = sum(1 for it in items if it["witness"].get("kind") == "violation")
    ref = kind == KIND_REFERENCE
    names = ", ".join(f"`{os.path.basename(p)}`" for p in (files or []))
    L = [(_PREAMBLE_REFERENCE.format(n=len(items), files=names or "the RTL file(s) here") if ref
          else _PREAMBLE_LIST.format(n=len(items))), ""]
    if nv:
        # Said in the brief and again on each of those questions.  The preamble above tells the
        # designer that every question is a place the document does not *determine* something and
        # that all the offered behaviours are consistent with what they wrote, and for a violation
        # neither sentence is true: it is a place the document determines two incompatible things.
        # A designer who read only the brief would approach it as a preference.
        L += [(_PREAMBLE_VIOLATIONS_REFERENCE if ref else _PREAMBLE_VIOLATIONS).format(
            n=nv, isare="is" if nv == 1 else "are"), ""]
    for k, it in enumerate(items, 1):
        L += [f"## Question {k}", ""]
        L += _question_body(it["witness"], it["opts"], it["perm"], probe, "###", kind)
    L += ["", (_HOWTO_REFERENCE if ref else _HOWTO_LIST).format(n=len(items)), ""]
    if ref:
        L += [f"The reference implementation is {names or 'the RTL in this directory'}. The "
              f"specification these questions are about is deliberately NOT here: the question is "
              f"what the implementation does, and only the implementation says that."]
    else:
        L += [f"The specification is in `{prose_name}`, in this directory. It is the only other "
              f"file here."]
    return "\n".join(L)




# --------------------------------------------------------------------------- the answer

_NONE = ("NONE", "NEITHER", "NO", "OUTSIDE")
_ANY = ("ANY", "EITHER", "BOTH", "DONT CARE", "DON'T CARE", "FREE")


def _verdict(answer: str, opts: list[dict], perm: list[int], *, allow_any: bool = True) -> dict:
    """Turn what the designer wrote into the three-valued result the pipeline scores.

    Anything that is not a letter on the menu, `none` or `any` is `unparsed` -- not silently
    rounded to one of them.  A designer who wrote something else answered a different question,
    and the honest record of that is that this one is still open.

    `allow_any` is off for a clause menu.  "I don't care which" is a real answer about a fork --
    the coordinate is free and the specification says so -- and it is not an answer about a
    contradiction: whichever of the two sentences is kept, the other is false as written, so
    there is no document in which both stand.  Recorded as `any` it would come back through
    `refine` as a declared degree of freedom, which is the one reading of a contradiction that is
    certainly wrong.  It is recorded as `refused` instead: an answer was given, it was to a
    question that was not asked, and the contradiction is still there.

    It is off for the whole of a reference sitting as well, for a related reason with a different
    shape: there the answer is a report of what one implementation did, and "any" is not a report.
    An implementation does one thing at one input; the other candidates being untaken is not
    evidence that they are permitted, and only the design's author can say that they are.
    """
    a = (answer or "").strip().strip('."').upper()
    if a in _NONE:
        return {"verdict": "outside", "obs": None}
    if a in _ANY:
        return {"verdict": "any", "obs": None} if allow_any else {"verdict": "refused",
                                                                  "obs": None}
    pos = _unlabel(a)
    if 0 <= pos < len(perm):
        i = perm[pos]
        return {"verdict": "chosen", "letter": a, "obs": opts[i].get("obs"),
                "consistent_with": opts[i]["tags"]}
    return {"verdict": "unparsed", "obs": None}



# ------------------------------------------------------------------------- the front door

def query_dir(case: cases.Case, rnd: int, witness_id: str,
              kind: str = KIND_DESIGNER) -> str:
    """Where an exchange with an answering authority lives: the questions, the answers, the log.

    A subdirectory rather than the round directory itself, because the agent's confinement root is
    this path: whatever is beside it -- another round, another sitting, a superseded one -- is
    outside the room the designer is in, and that is enforced rather than assumed.

    A reference sitting gets its own name, so the two authorities never share a directory.  Not
    tidiness: `_replayable` decides whether to re-ask by looking for an `answers.json` where the
    sitting would be, and a shared directory would let a designer's answers be replayed under a
    reference run's ledger rows, or the reverse -- silently, since a replay writes no transcript
    of its own.  Different rooms make that structurally impossible instead of merely unlikely.
    The designer's name is unsuffixed so that every sitting recorded before this flag existed is
    still found where it was left.
    """
    safe = re.sub(r"[^A-Za-z0-9_.=-]+", "_", witness_id)
    if kind != KIND_DESIGNER:
        safe = f"{safe}.{kind}"
    return case.path("oracle", f"round{rnd}", safe)


def _supersede(d: str) -> str | None:
    """Move a stored answer that belongs to a different question out of the way, keeping it.

    Deleting it would be simpler and would destroy the record of a question that WAS put to a
    designer.  Leaving it in place would be worse: a stale `answers.json` sitting beside a new
    `questions.md` reads as though the designer had answered the questions now being asked.  So
    the whole exchange moves into `superseded-<n>/` and the directory is left empty for a real
    sitting, which is the only thing that can answer the questions now being asked.
    """
    live = [f for f in (PROSE, QUESTION, ANSWER, QUESTIONS, ANSWERS, ASKED,
                        "session.jsonl", "session.stderr")
            if os.path.exists(os.path.join(d, f))]
    if not os.path.isdir(d):
        return None
    # And whatever the sitting was given to work from or wrote while working: a reference sitting
    # holds the RTL it was answering out of and the testbench it built to answer with.  Those go
    # with the exchange rather than being left beside the next one, for the same reason the
    # answers do -- an `answers.json` archived away from the `verified_accu.v` it was read off is
    # an answer whose authority cannot be reconstructed, and the testbench is the `why`.
    live += sorted(f for f in os.listdir(d)
                   if f.endswith(_RTL + (".out", ".vcd", ".vvp")) and
                   os.path.isfile(os.path.join(d, f)))
    if not live:
        return None
    n = 1
    while os.path.exists(os.path.join(d, f"superseded-{n}")):
        n += 1
    dest = os.path.join(d, f"superseded-{n}")
    os.makedirs(dest)
    for f in live:
        os.rename(os.path.join(d, f), os.path.join(dest, f))
    return dest


def _replayable(d: str, qsha: str, answer: str = ANSWERS,
                refsha: str | None = None) -> tuple[bool, str | None]:
    """Whether the answer on disk answers THIS question, and if not, why not.

    Three outcomes.  No answer: nothing to replay, ask.  An answer whose `asked.json` carries
    this question's digest: replay it, and the round costs no query.  An answer that carries a
    different digest, or none at all: it was given to a different question, and the honest thing
    is to treat the question as unasked.  Absent an `asked.json` the pairing cannot be checked,
    and unverifiable is handled as mismatched -- the failure that direction costs one query, and
    the other direction writes a letter into the specification on the strength of a filename.

    `answer` is the file to look for, so the same guard covers one question and a whole list.  A
    list binds harder, not softer: its digest covers every question in it and their order, so a
    round that found one new fork re-asks all of them rather than replaying an answer given when
    the sitting had a different shape.

    `refsha` binds the second half of the same idea, and only a reference run passes one.  There,
    an answer is a fact about a specific implementation: a benchmark that corrects its reference
    between two runs has changed who answered, not just when, and replaying the old verdicts would
    put the old implementation's behaviour into a specification labelled as measured against the
    new one.  Passing `None` -- which every designer run does -- skips the check, because a
    designer sitting has no such file and a missing `reference_sha256` there means nothing.
    """
    if not os.path.isfile(os.path.join(d, answer)):
        return False, None
    p = os.path.join(d, ASKED)
    if not os.path.isfile(p):
        return False, "the stored answer has no record of the question it was given for"
    try:
        with open(p, errors="replace") as f:
            was = json.load(f)
    except ValueError:
        return False, f"{ASKED} is not readable JSON"
    if was.get("question_sha256") != qsha:
        # What the previous document held, in whichever unit it was written in.  A list records
        # `questions`, a single fork records `options`; naming the one that is there keeps the
        # message from reading "None option(s) then" and sending a reader to look for a bug.
        had = (f"{was['questions']} question(s) then" if "questions" in was else
               f"{was['options']} option(s) then" if "options" in was else
               "shape unrecorded")
        return False, (f"the stored answer was given to a different question "
                       f"({str(was.get('question_sha256'))[:12]} != {qsha[:12]}, {had})")
    if refsha is not None and was.get("reference_sha256") != refsha:
        return False, (f"the stored answer was read out of a different reference implementation "
                       f"({str(was.get('reference_sha256'))[:12]} != {refsha[:12]})")
    return True, None


def _read_answers(d: str, n: int) -> dict[int, dict]:
    """The designer's answers to a list, keyed by question number.

    Tolerant about the shape and strict about the content.  A designer who wrote a list, a map,
    or a bare letter per key has answered; a question absent from the file is absent from the
    result and its resolution records it unanswered, which is the honest reading of silence and
    is what `_HOWTO_LIST` warns is worse than "none".

    There is no transcript fallback.  A session that printed its JSON instead of writing it could
    be salvaged when there was one letter to find, but a list recovered from a transcript has to
    be re-associated with question numbers by a regex, and a mis-association writes an answer
    against the wrong fork -- the exact failure the `asked.json` digest exists to prevent.
    """
    out: dict[int, dict] = {}
    p = os.path.join(d, ANSWERS)
    if not os.path.isfile(p):
        return out
    try:
        with open(p, errors="replace") as f:
            doc = json.load(f)
    except ValueError:
        return out

    def put(q, ans, why):
        try:
            k = int(q)
        except (TypeError, ValueError):
            return
        if 1 <= k <= n and k not in out:
            out[k] = {"answer": str(ans), "why": str(why or ""), "via": ANSWERS}

    body = doc.get("answers") if isinstance(doc, dict) and "answers" in doc else doc
    if isinstance(body, list):
        for i, e in enumerate(body, 1):
            if isinstance(e, dict):
                put(e.get("q", e.get("question", i)), e.get("answer", ""), e.get("why"))
    elif isinstance(body, dict):
        for k, e in body.items():
            if isinstance(e, dict):
                put(k, e.get("answer", ""), e.get("why"))
            else:
                put(k, e, "")
    return out


def ask_all(case: cases.Case, items: list[dict], *, prose: str, probe: dict | None = None,
            rnd: int = 1, fresh: bool = False, kind: str = KIND_DESIGNER) -> dict:
    """Put every question this round found to one answering authority, in one sitting.

    `items` is one entry per DISTINCT question -- the caller has already collapsed witnesses that
    generate the same menu at the same context -- each `{"witness": <witness dict>, "purpose":
    <kind>, "id": <witness id>}`.  What comes back is keyed by witness id and carries the same
    fields per question that `ask` returns for one, so `refine` scores a list exactly as it
    scored a query.

    One session, N questions, and the ledger records both: an `oracle_session` event for the
    sitting and an `oracle_query` event per question, because "how many questions did this
    method have to put to a designer" and "how many times did it interrupt one" are different
    numbers and reporting either alone would overstate or understate the cost.

    `kind` defaults to the designer and has to be asked for by name to be anything else -- that
    default IS guard 1 of the four in the module docstring, and it is a parameter default rather
    than a module-level switch so that no code path can turn a benchmark run on for a caller that
    did not spell it.  What the other value changes: which role runs, which directory the sitting
    lives in, which brief is put, and what every row this writes says about who answered.  What it
    does not change: the questions.  A `kind` this does not know is refused rather than falling
    back to the designer, because a typo that silently produced a designer sitting would produce
    a *correct-looking* result -- the expensive kind of wrong.
    """
    if kind not in KINDS:
        raise ValueError(f"unknown oracle kind {kind!r}; expected one of {list(KINDS)}")
    ref = kind == KIND_REFERENCE
    seal.check("the designer oracle")

    # Resolved before anything is written, so a benchmark run with no answer key fails on the
    # question "which implementation?" rather than after the sitting directory exists and a role
    # has been launched into a room with nothing in it to read.  It is a result and not an
    # exception: `_score` turns the status into `oracle_no_reference` and the round reports that
    # its questions went unanswered, which is what happened.
    refs, no_ref = ([], None)
    if ref:
        refs, no_ref = reference_files(case)
        if not refs:
            cases.log(case, "oracle_session", backend=kind, oracle_kind=kind, round=rnd,
                      questions=len(items), answered=0, replayed=False, detail=no_ref)
            out = {it["id"]: {"id": it["id"], "status": "no_reference", "detail": no_ref}
                   for it in items}
            return {"status": "no_reference", "results": out, "skipped": list(out.values()),
                    "session": None, "questions": 0, "answered": 0, "replayed": False,
                    "dir": None, "oracle_kind": kind, "detail": no_ref}

    prepared, skipped = [], []

    for it in items:
        w = it["witness"]
        opts = options(w)
        if not opts:
            skipped.append({"id": it["id"], "status": "no_options", "detail":
                            "this witness's readings predict no observation at its context, so "
                            "there is nothing to put in front of the designer"})
            continue
        qid = question_id(w)
        prepared.append({"witness": w, "id": it["id"], "purpose": it.get("purpose"),
                         "qid": qid, "opts": opts, "perm": order(qid, len(opts))})
    if not prepared:
        return {"status": "no_options", "results": {s["id"]: s for s in skipped},
                "skipped": skipped, "session": None, "questions": 0, "answered": 0,
                "replayed": False, "dir": None}

    # Ordered by question id, not by the order the diagnosis produced them.  Which forks this
    # pipeline considers related, and in what sequence it found them, is our reading and not the
    # designer's business; a digest order is stable across re-runs without carrying it.
    prepared.sort(key=lambda p: p["qid"])

    d = query_dir(case, rnd, "questions", kind)
    q = questions_markdown(PROSE, prepared, probe, kind, refs)
    qsha = cases.sha256(q)
    refsha = _manifest(refs) if ref else None

    os.makedirs(d, exist_ok=True)
    if fresh:
        _supersede(d)
    replay, mismatch = _replayable(d, qsha, answer=ANSWERS, refsha=refsha)
    superseded = None
    if mismatch:
        superseded = _supersede(d)
        print(f"  oracle · round {rnd}: not replayed -- {mismatch}; the previous sitting is kept "
              f"in {os.path.basename(superseded or '')}/", flush=True)

    if not replay:
        # The prose goes in for a designer and does NOT for a reference.  The asymmetry is the
        # point and it is enforced here rather than trusted to the brief: `_PREAMBLE_REFERENCE`
        # tells that role to simulate rather than read, and a `spec.txt` sitting in the same
        # directory would make "read the paragraph and pick the plausible one" available to it,
        # indistinguishably from a real simulation in everything the answer format records.
        if not ref:
            with open(os.path.join(d, PROSE), "w") as f:
                f.write(prose)
        for p in refs:
            # Copied, not linked or read in place.  The role's confinement root is `d`, so a
            # symlink out of it is refused at the tool call and the sitting would be unanswerable;
            # and a copy is also the archive -- `_supersede` keeps it with the answers, so which
            # bytes were simulated stays recoverable after the benchmark's own file moves on.
            with open(p, "rb") as src, open(os.path.join(d, os.path.basename(p)), "wb") as dst:
                dst.write(src.read())
        with open(os.path.join(d, QUESTIONS), "w") as f:
            f.write(q)
    transcript = os.path.join(d, "session.jsonl")

    session = None
    if not replay:
        session = agent_backend.run(
            REFERENCE if ref else DESIGNER, root=d, cwd=d, transcript=transcript,
            prompt=f"Read `{QUESTIONS}` in this directory and follow it. Answer all "
                   f"{len(prepared)} questions it asks by writing `{ANSWERS}` in this directory.")
        with open(os.path.join(d, ASKED), "w") as f:
            json.dump({"question_sha256": qsha, "questions": len(prepared), "round": rnd,
                       # Guard 2.  Written for BOTH kinds, including the designer, so that a
                       # sitting with no `oracle_kind` is exactly one thing -- a run made before
                       # this flag existed -- rather than ambiguous between that and a reference
                       # run whose label failed to be written.
                       "oracle_kind": kind,
                       "reference_sha256": refsha,
                       "reference": [os.path.basename(p) for p in refs],
                       "order": [p["id"] for p in prepared]}, f, indent=1)

    answers = _read_answers(d, len(prepared))
    if session:
        summary = agent.refusal_summary(session["refusals"])
        if summary:
            print(f"  oracle · round {rnd}:\n{summary}", flush=True)

    logged_session = {"backend": kind, "oracle_kind": kind, "round": rnd,
                      "questions": len(prepared),
                      "answered": len(answers), "replayed": replay,
                      "question_sha256": qsha,
                      "reference_sha256": refsha,
                      "superseded": (os.path.relpath(superseded, case.dir)
                                     if superseded else None),
                      "superseded_why": mismatch,
                      "transcript": (os.path.relpath(transcript, case.dir)
                                     if os.path.isfile(transcript) else None)}
    if session:
        logged_session.update(rc=session["rc"], how=session["how"], elapsed=session["elapsed"],
                              denied=session["denied"], refusals=session["refusals"],
                              session_error=session["session_error"])
    cases.log(case, "oracle_session", **logged_session)

    who = "the reference" if ref else "the designer"
    results = {}
    for k, p in enumerate(prepared, 1):
        a = answers.get(k) or {"answer": "", "why": "", "via": "none"}
        wkind = p["witness"].get("kind")
        # `any` is refused for a reference on EVERY question, not only on a contradiction.  A
        # designer saying "I don't care" states a degree of freedom and the specification records
        # it as one; an implementation cannot state that, because it does exactly one thing at
        # this input and whatever it did is not evidence that the other candidates are allowed.
        # Accepted, it would enter `refine` as a declared freedom nobody declared.
        allow_any = wkind != "violation" and not ref
        menu = [_label(i) for i in range(len(p['perm']))] + (["'none'"] if ref else
                                                             ["'none'", "'any'"])
        res = {"status": "ok", "witness": p["id"], "question_id": p["qid"],
               "question_sha256": qsha, "options": len(p["opts"]), "question_number": k,
               "oracle_kind": kind,
               "letters": {_label(pos): p["opts"][i]["tags"] for pos, i in enumerate(p["perm"])},
               "why": a["why"], "answer_via": a["via"], "replayed": replay, "dir": d,
               **_verdict(a["answer"], p["opts"], p["perm"], allow_any=allow_any)}
        if res["verdict"] == "unparsed":
            res["status"] = "no_answer"
            res["detail"] = (
                f"question {k} was left unanswered" if a["via"] == "none" else
                f"{who}'s answer to question {k} was {a['answer']!r}, which is not one of {menu}")
        elif res["verdict"] == "refused":
            # Not `no_answer`: the authority did answer, and what they said is a fact about the
            # sitting worth keeping.  It settles nothing, and `refine` scores it as unadjudicated.
            res["detail"] = (
                f"{who} answered question {k} with {a['answer']!r}, and " + (
                    f"a reference implementation cannot say a coordinate is free -- it does one "
                    f"thing at this input, and what it did is not evidence that the other "
                    f"candidates are permitted" if ref and wkind != "violation" else
                    f"that question is a contradiction between two sentences -- there is no "
                    f"reading of the specification in which both stand, so 'any' names no "
                    f"document"))

        results[p["id"]] = res
        # Same event names as the single-question path, chosen by the same rule: a replay is not
        # a query.  `in_session` is what tells the two paths apart for anyone counting sittings,
        # and it is the only field here the one-at-a-time form does not also write.
        cases.log(case, "oracle_replay" if replay else "oracle_query",
                  backend=kind, oracle_kind=kind, purpose=p["purpose"],
                  witness=p["id"], verdict=res["verdict"], answer_via=a["via"],
                  question_id=p["qid"], question_sha256=qsha, options=len(p["opts"]),
                  question_number=k, in_session=True,
                  transcript=(os.path.relpath(transcript, case.dir)
                              if os.path.isfile(transcript) else None))
    for s in skipped:
        results[s["id"]] = s
    return {"status": "ok", "results": results, "skipped": skipped, "session": session,
            "dir": d, "questions": len(prepared), "answered": len(answers), "replayed": replay,
            "oracle_kind": kind, "reference": [os.path.basename(p) for p in refs]}
