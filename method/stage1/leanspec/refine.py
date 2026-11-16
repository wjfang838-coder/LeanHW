#!/usr/bin/env python3
"""Stage 5 — designer-guided refinement, and the check that the result is decided.

Two commands, deliberately separate:

    resolve   ask the designer at each witness; record which readings survive
    verify    re-diagnose the refined spec and certify that it is now determined

`resolve` is mechanical: it puts the witness in front of the designer, compares the answer
against the predictions stage 4 recorded *before* the query, and computes which candidates
remain.  It never edits the specification.

Editing is the agent's job -- pinning a surviving candidate, filling a hole with the answer,
revising the clause a contradiction implicates.  `verify` is what makes that safe: it does not
ask how the edit was chosen, it re-runs the four queries on the edited spec and asks the kernel
whether the result admits exactly one observation at every legal context.  An edit that pins a
reading the designer did not choose survives `resolve`'s bookkeeping and dies here.

## The three answers `resolve` can give a fork

    decided        exactly one reading matches the chosen behaviour -- the others are eliminated
    silent         the designer does not care; the fork is a real degree of freedom
    outside        the designer says none of the behaviours is right -- the variant space does
                   not contain the answer

`outside` is the interesting one and it is reported, never rounded to "inconclusive".  It says
the specification was misread in a way that re-reading the prose would not have caught, which is
precisely the case where a behavioural question earns its keep.

A hole is answered on the same scale, one level down: `pinned` when exactly one of the hole's
enumerated values survives, `silent` when *all* of them do (the coordinate is free and the
designer says so), `partial` when some but not all do, `outside` when none does, and `observed`
when the case never enumerated the values and the query could therefore only confirm the freedom.

`partial` is the one that is easy to leave out, and its absence is not harmless.  Two of three
values surviving filed as `silent` would assert that the question did not touch the coordinate --
when in fact it eliminated a third of the menu.  The distinction matters twice over: a narrowing
is evidence and silence is not, and a narrowing that stops at more than one value is the shape a
coordinate takes when part of it is settled and part of it is not.

## What a single survivor is worth, and when it is worth nothing

`pinned` says one option survived.  Whether that is an *answer* depends on where the options came
from, and the two cases are not close:

  * The menu is the whole domain -- an `inductive` with N constructors, all N offered.  Then one
    survivor is the value, because there was nothing else it could have been.
  * The menu is a sample of a larger domain -- three of the sixteen patterns a 4-bit register can
    hold.  Then one survivor means one survivor *among the values offered*, and the value the
    designer actually intends may never have been on the menu.

So `_classify` splits `pinned` by the domain status `schema.domain_of` reports:

    pinned              closed menu, one survivor -- an answer
    pinned_sampled      sampled menu, one survivor -- NOT an answer; step 06 refuses it
    pinned_undeclared   no declaration, one survivor -- carried with the caveat attached

Note what is *not* split.  `silent`, `partial` and `outside` are sound on a sample however it was
drawn: surviving values mean the coordinate is free among them whatever else is in the domain,
and no survivor means the answer is outside the menu, which a sample establishes as well as an
enumeration does.  A sample can prove freedom.  It cannot prove a pin.

## One question, asked once

Several findings routinely land on the same context -- a fork with three readings is diagnosed as
pairwise comparisons, and every one of them scopes to the same question, the same stimulus and
the same menu.  Asking the designer three times would inflate the query count this method reports
while learning nothing.  So resolutions are cached on `oracle.question_id`, which is exactly the
stimulus and the menu, and the reuse is logged so the ledger still shows what each finding was
answered with.
"""
from __future__ import annotations

import json
import os
import shutil

from . import cases, diagnose, leanrun, oracle, schema


def _matches(pred: dict, obs: list[dict]) -> bool:
    """Does a predicted observation agree with the behaviour the designer chose?

    The comparison is on the coordinates the prediction *projects onto*: a step given as `null`,
    and any signal a step omits, is a don't-care.  A projection is what stage 4's witnesses are
    built from, so comparing outside it would be comparing against detail the specification never
    claimed.
    """
    steps = pred.get("steps", []) if isinstance(pred, dict) else pred
    if steps is None:
        return True
    if len(steps) > len(obs):
        return False
    for i, st in enumerate(steps):
        if st is None:
            continue
        for k, v in st.items():
            # `obs[i]` may itself be `null` -- both sides of this comparison are projected onto the
            # same focus, so in practice they go blank together, but a prediction that asserts `k`
            # where the observation asserts nothing is a mismatch and not a crash: the reading
            # claims something the behaviour the designer picked does not show.
            if (obs[i] or {}).get(k) != v:
                return False
    return True


def _seq(obs) -> list[dict]:
    """An observation as a list of per-step dicts, however the emitter spelled it."""
    if obs is None:
        return []
    if isinstance(obs, dict):
        return obs.get("steps") or []
    return obs


def _hole_domains(case: cases.Case) -> dict:
    """Every hole's declared option set, keyed by hole name.

    Read here rather than threaded down from `resolve`'s caller because the same code path needs
    it for every hole and none of them carries an extraction.  A case with no extraction on disk
    -- which happens while a stage is being re-run -- yields an empty map, and every hole then
    classifies as `undeclared`, which is the truthful reading of "nobody wrote it down".
    """
    try:
        with open(case.path("extraction.json")) as f:
            ext = json.load(f)
    except (OSError, ValueError):
        return {}
    return {h["name"]: schema.domain_of(h) for h in ext.get("holes", [])}


def _pin_outcome(outcome: str, w: dict, doms: dict) -> tuple[str, dict]:
    """Qualify a `pinned` by where its options came from.  See the module docstring.

    Only `pinned` is touched.  `silent`, `outside` and `observed` say something a sample
    establishes as well as an enumeration does, so qualifying them would be noise.
    """
    dom = doms.get(w.get("hole") or w["id"].split(":", 1)[-1],
                   {"status": schema.UNDECLARED, "size": None, "offered": None, "why": ""})
    if outcome != "pinned":
        return outcome, dom
    return {schema.CLOSED: "pinned",
            schema.SAMPLED: "pinned_sampled",
            schema.UNDECLARED: "pinned_undeclared"}[dom["status"]], dom


def _mine(w: dict) -> str:
    """The prefix of the prediction tags that answer THIS witness.

    Stage 3 evaluates every predicate at every context it emits, so a fork's witness carries the
    other coordinates' tags too -- `hole:latency`, a sibling fork's readings -- and those are
    answers to their own witnesses.  Counting them made a cleanly decided fork read as `partial`,
    because a surviving hole value inflated the count past one; step 06 then refused the decision
    as "does not decide anything", and the question would have been re-posed in a second round
    with nothing new to measure.

    For a fork the scope is the whole fork and not the witness's own pair, because a fork with
    three readings is asked as pairwise comparisons at one shared context, and the pair that
    happens to be named can be the one where both sides die.  Read pairwise that comes back
    `outside` -- the answer is off the menu -- and that is false when the menu holds the answer
    and this very question found it.
    """
    if w.get("kind") in ("ambiguity", "repair"):
        return str(w.get("choice")) + ":"
    return "hole:" + str(w.get("hole") or w["id"].split(":", 1)[-1]) + "="


def _classify(w: dict, mine: dict[str, bool], doms: dict) -> tuple[str, dict | None]:
    """The outcome for one witness, from which of its own readings survived."""
    if w["kind"] in ("ambiguity", "repair"):
        return (("decided" if sum(mine.values()) == 1 else
                 "silent" if mine and all(mine.values()) else
                 "outside" if not any(mine.values()) else
                 "partial"), None)
    # A hole.  Bare `hole:<n>` is the unconstrained reading, consistent with anything the hole
    # could produce, so it is not evidence and `_mine` already excludes it.  `silent` means what
    # it says: EVERY value offered survived, so the question did not touch this coordinate.
    # Some-but-not-all is a different result -- the menu was narrowed and not emptied -- and
    # reporting it as silence would throw away the values the answer did rule out.
    outcome = ("observed" if not mine else
               "pinned" if sum(mine.values()) == 1 else
               "outside" if not any(mine.values()) else
               "silent" if all(mine.values()) else
               "partial")
    return _pin_outcome(outcome, w, doms)


def _score(case: cases.Case, w: dict, res: dict, doms: dict) -> dict:
    """What one witness's answer settled.

    Split from the asking so that a witness is scored the same way whether its question was put
    on its own or as item 4 of a list: this function never touches the oracle, and the whole of
    what it knows about the designer is `res`.
    """
    qid = oracle.question_id(w)
    if res.get("status") != "ok":
        return {"witness": w["id"], "kind": w["kind"], "outcome": "oracle_" + res["status"],
                "detail": {k: v for k, v in res.items()
                           if k not in ("dir", "obs", "session", "id")}}
    if w["kind"] == "violation":
        return _score_violation(w, res, qid)

    pre = _mine(w)

    tags = [t for t in (w.get("predicted") or {}) if t.startswith(pre)]
    verdict = res["verdict"]

    if verdict == "chosen":
        obs = _seq(res["obs"])
        # On the same coordinates the question was asked on.  `oracle.focus` reduces a menu to
        # the coordinates the readings disagree about, so the behaviour the designer picked
        # asserts those and leaves the rest don't-care.  The predictions have to be cut to the
        # same shape before comparing: a full prediction carries values for coordinates the
        # answer never claimed, and matching against those would eliminate readings on the
        # strength of detail nobody was asked about.  `_project` with a `None` focus is the
        # identity, so an unreduced menu still compares exactly as it did.
        foc = oracle.focus(w)
        consistent = {t: any(_matches(oracle._project(a, foc), obs)
                             for a in (w["predicted"][t] or []))
                      for t in (w.get("predicted") or {})}
    elif verdict == "any":
        # The designer says the coordinate is free.  Every reading on this menu is then correct,
        # which is a statement about all of them and not only about the ones this witness paired.
        obs, consistent = None, {t: True for t in tags}
    else:                                                            # outside
        # None of the offered behaviours is right.  The menu is exactly the union of what these
        # readings admit at this context, so every one of them is refuted -- which is what makes
        # `outside` a finding rather than a shrug.
        obs, consistent = None, {t: False for t in tags}

    mine = {t: ok for t, ok in consistent.items() if t.startswith(pre)}
    outcome, dom = _classify(w, mine, doms)
    return {"witness": w["id"], "kind": w["kind"], "outcome": outcome,
            "verdict": verdict, "question_id": qid,
            "discriminating": w.get("discriminating"), "domain": dom,
            "designer_said": res.get("why", ""),
            "reused_from": res.get("witness") if res.get("witness") != w["id"] else None,
            "pinned_to": ([t[len(pre):] for t, ok in mine.items() if ok]
                          if w["kind"] == "incompleteness" else None),
            "observed": obs, "consistent": consistent,
            "kept": [t for t, ok in consistent.items() if ok],
            "eliminated": [t for t, ok in consistent.items() if not ok]}


# The two sentences a violated property sets against each other, as the tags an answer is scored
# in.  `definitions` says the behaviour is what was meant and the guarantee sentence is wrong;
# `property` says the reverse.  They are qualified with the property's name when they reach a
# resolution, for the same reason every other tag is: `pipeline._tags` splits a `kept` entry on the
# question name, and an unqualified tag is attributed to every question in the round.
_CLAUSES = ("definitions", "property")

_UNADJUDICATED = (
    "the contradiction was put to the designer and no sentence was named, so both are still in "
    "the specification and both cannot hold -- this is an unanswered question, not a settled one")


def _score_violation(w: dict, res: dict, qid: str) -> dict:
    """What one adjudication of a contradiction settled.

    Nothing is scored against a prediction here, because there is none to score against.  The
    other three witness kinds carry `predicted` -- what each reading of the prose says will be
    observed, recorded before the question was put -- and the elimination is the mechanical
    comparison of the designer's waveform against those.  A violated property has no readings:
    stage 4 proved that the definitions and the guarantee disagree at a named legal context, and
    what the designer picks is a sentence.  So the elimination is the other sentence, directly,
    and there is no menu, no projection and no tag machinery in between.

    Four outcomes, and they are not the fork vocabulary:

        decided        one of the two sentences was named.  Step 07 has to read it -- see the
                       check there -- and the repair is a patch to the prose, not a coordinate
                       of `Cfg`: a contradiction is not a degree of freedom that a configuration
                       could take a value at.
        outside        neither sentence is the fault.  A real finding and the one no re-reading
                       could have produced, and it settles nothing here: what the designer says
                       is wrong instead is in `designer_said`, and no decision may be taken on it.
        unadjudicated  the question was put and came back "any", or came back nothing.  `any` is
                       an answer about a fork and not about a contradiction, and `oracle._verdict`
                       refuses it at the door rather than letting it arrive here looking like a
                       declared degree of freedom.
    """
    name = w["property"]
    verdict = res["verdict"]
    tag = (res.get("consistent_with") or [None])[0] if verdict == "chosen" else None
    outcome = ("decided" if tag in _CLAUSES else
               "outside" if verdict == "outside" else
               "unadjudicated")
    # On `outside` both sentences are refuted at once, and that is not a rhetorical flourish: the
    # menu is the whole of what the contradiction is between, so "neither" says the fault is a
    # third sentence nobody has named.  Nothing may be decided on it, and both tags are recorded
    # as eliminated so that a decision naming either one fails step 07's `gone` check.
    out = {"witness": w["id"], "kind": "violation", "outcome": outcome,
           "verdict": verdict, "question_id": qid, "property": name,
           "statement": w.get("statement", ""),
           "designer_said": res.get("why", ""),
           "reused_from": res.get("witness") if res.get("witness") != w["id"] else None,
           "observed": None, "pinned_to": None, "domain": None,
           "consistent": {f"{name}:{t}": (t == tag) for t in _CLAUSES},
           "kept": [f"{name}:{tag}"] if outcome == "decided" else [],
           "eliminated": ([f"{name}:{t}" for t in _CLAUSES if t != tag] if outcome == "decided"
                          else [f"{name}:{t}" for t in _CLAUSES] if outcome == "outside"
                          else [])}
    if outcome == "unadjudicated":
        out["detail"] = _UNADJUDICATED + (
            f" (the designer answered {res.get('verdict')!r}: {res.get('detail', '')})"
            if res.get("verdict") == "refused" else "")
    return out


# A contradiction has no menu.  Its finding is that the default reading admits NOTHING at a legal
# context, so there is no behaviour to offer and no letter the designer could pick: what has to
# change is a sentence, and which sentence is a reading of the prose that step 06 takes with the
# contradiction certificate in hand.  Spending a query here would be asking a question with a
# blank page and counting the answer.
_CONTRADICTION = (
    "the specification admits no observation at all at this context, so there is nothing to put "
    "in front of the designer -- the repair is a sentence, and the evidence for it is the "
    "emptiness certificate stage 3 already proved")


def _queries_this_run(case: cases.Case) -> int:
    """Queries this `resolve` invocation spent.

    The ledger is append-only, so its total also counts queries made by superseded stage-4
    witness sets and by re-runs.  The number that answers "how many designer queries did this
    case need" is the one attributable to the resolution actually on disk, so it is counted from
    the last stage boundary (`witness` or a previous `resolve`, whichever is later) and the ledger
    total is reported beside it rather than instead of it.
    """
    evs = cases.ledger(case)
    last = max((i for i, e in enumerate(evs) if e["event"] in ("witness", "resolve")), default=-1)
    return sum(1 for e in evs[last + 1:] if e["event"] == "oracle_query")


def resolve(case: cases.Case, rnd: int = 1, fresh: bool = False,
            kind: str = oracle.KIND_DESIGNER) -> dict:
    """Put this round's questions to the designer, once, and score every witness against them.

    The round's forks are collapsed to DISTINCT questions first -- two witnesses at the same
    context with the same menu are the same question however differently the diagnosis arrived at
    them -- and what remains is put in a single sitting.  One designer, one reading of the
    specification, one set of answers that are consistent with each other.

    The cost of that is recorded in `oracle.ask_all` and not hidden: answers given together are
    correlated, and a question late in the list is answered by someone who has already committed
    to a position on the earlier ones.  What it buys is that a fork which is invisible on its own
    -- separable only jointly with another -- can be seen, because both are on the same page.

    `kind` is who answers, and everything from here down is indifferent to it: the questions are
    the same questions and `_score` never touches the oracle, so a reference run is scored by the
    identical code that scores a designer run.  What it must NOT be is indifferent in the record,
    and `resolution.json`'s `oracle` field used to be the literal string `"designer"` -- true of
    every run there had ever been, and the field a reader consults to learn who answered.  It is
    the actual authority now, so that a benchmark-answered resolution says so where it is looked
    for rather than only in the ledger.
    """
    with open(case.path("witnesses.json")) as f:
        wit = json.load(f)
    with open(case.path("probe.json")) as f:
        probe = json.load(f)
    prose = cases.prose(case)
    doms = _hole_domains(case)

    # One representative per distinct question, in the order the witness search produced them, so
    # that which witness stands for a shared question is a property of the diagnosis and not of a
    # dict's iteration order.  The others are answered by their representative's answer and say so.
    askable = [w for w in wit["witnesses"] if w["kind"] != "contradiction"]
    rep: dict[str, dict] = {}
    for w in askable:
        rep.setdefault(oracle.question_id(w), w)
    got = oracle.ask_all(
        case, [{"witness": w, "id": w["id"], "purpose": w["kind"]} for w in rep.values()],
        prose=prose, probe=probe, rnd=rnd, fresh=fresh, kind=kind)

    out = []
    for w in wit["witnesses"]:
        if w["kind"] == "contradiction":
            out.append({"witness": w["id"], "kind": w["kind"], "outcome": "contradiction",
                        "detail": _CONTRADICTION})
            continue
        qid = oracle.question_id(w)
        res = got["results"].get(rep[qid]["id"]) or {
            "status": "no_answer",
            "detail": "the sitting produced no result for this question"}
        if rep[qid]["id"] != w["id"]:
            cases.log(case, "oracle_reuse", witness=w["id"], purpose=w["kind"], question_id=qid,
                      same_question_as=rep[qid]["id"], verdict=res.get("verdict"))
        out.append(_score(case, w, res, doms))

    doc = {"case": case.name, "oracle": kind, "round": rnd, "resolutions": out,
           "reference": got.get("reference") or [],
           "queries": _queries_this_run(case),
           "queries_ledger_total": sum(1 for e in cases.ledger(case)
                                       if e["event"] == "oracle_query"),
           "distinct_questions": len(rep),
           # One sitting per round, and whether it was a real one.  `queries` counts questions;
           # this counts interruptions, and the two are different costs.
           "sitting": {"asked": bool(got.get("questions")) and not got.get("replayed"),
                       "replayed": bool(got.get("replayed")),
                       "questions": got.get("questions", 0),
                       "answered": got.get("answered", 0),
                       "dir": (os.path.relpath(got["dir"], case.dir) if got.get("dir") else None)},
           "outcomes": {k: sum(1 for r in out if r["outcome"] == k)
                        for k in sorted({r["outcome"] for r in out})}}
    with open(case.path("resolution.json"), "w") as f:
        json.dump(doc, f, indent=1)
    cases.log(case, "resolve", round=rnd, oracle_kind=kind, **doc["outcomes"])
    return doc


# ------------------------------------------------------------------ verifying the result

# Two files, for the same reason stage 3 has two: measuring and proving are different jobs and
# they fail differently.
#
# `determinedEverywhere` is evaluated over the whole domain, and when the answer is `false` the
# evaluator still has to grind through every context to find that out.  On a large domain that
# reduction can exhaust the C stack, and when it does the Lean process ABORTS -- which, in a
# single file, takes the `#eval` output with it, buffered and unflushed.  The result was the worst
# possible reading of an honest negative: a spec that is legitimately not determined produced no
# measurement at all, and `verify` reported `decided: {}` and `checked: 0`, as if the sweep had
# never run.  A case whose only fault is an open hole would look like a case whose tooling broke.
#
# So the measurement runs alone and first, and it always survives.  The certificate is stated only
# when the measurement says there is something true to certify -- which is also the framework's
# own rule everywhere else: certify the finding, do not fish for one.
DECIDED_MEASURE = """\
-- GENERATED by leanspec/refine.py -- do not edit.
import Partial
open LeanSpec

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

#eval emitDecided case "decided" (admits decidedCfg)
#eval emitSweep case (admits decidedCfg)
"""

DECIDED_CERT = """\
-- GENERATED by leanspec/refine.py -- do not edit.
import Partial
open LeanSpec

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

-- The decided spec is determined and live at every legal context in the domain.
theorem decided_determined :
    determinedEverywhere (admits decidedCfg) obsUniverse ctxUniverse legal = true := by
  decide +kernel
#print axioms decided_determined
"""


ROUND_ARTIFACTS = ("extraction.json", "diagnosis.json", "witnesses.json", "resolution.json",
                   "properties.json", "probe.json", "diagnose.log", "certificates.log")


def snapshot(case: cases.Case, round_no: int) -> str:
    """Freeze one refinement round before the specification is edited.

    Stages 3-5 are repeated until convergence, and the *final* artifacts of a converged case say
    almost nothing: no ambiguity, no hole, no contradiction, because that is what convergence
    means.  What a round did is only legible if the round is kept.  So every round's extraction,
    partial spec, diagnosis, witnesses and resolution are copied under `rounds/roundN/` before the
    edit, and a reader goes to round 1 for *what was found* and to the last round for *what it
    became*.
    """
    d = case.path("rounds", f"round{round_no}")
    os.makedirs(d, exist_ok=True)
    src = case.path("sandbox", "Partial.lean")
    if os.path.isfile(src):
        shutil.copy(src, os.path.join(d, "Partial.lean"))
    for f in ROUND_ARTIFACTS:
        p = case.path(f)
        if os.path.isfile(p):
            shutil.copy(p, os.path.join(d, f))
    cases.log(case, "snapshot", round=round_no, files=sorted(os.listdir(d)))
    return d


def rounds(case: cases.Case) -> list[str]:
    d = case.path("rounds")
    return sorted(os.listdir(d), key=lambda n: int(n.replace("round", ""))) \
        if os.path.isdir(d) else []


def relabel(r: dict) -> dict:
    """A stored resolution's outcome, checked against the evidence stored beside it.

    Snapshots are frozen, and that is the point of them -- a round records what was found when it
    ran, and rewriting one to match a later rule would erase the history it exists to keep.  But
    an outcome is not an observation.  It is a *label derived* from the `consistent` map in the
    same record, so a frozen label can disagree with its own evidence: a round taken before
    `partial` existed calls a hole `silent` while listing the values the answer eliminated, which
    asserts "nothing was ruled out" directly above the thing that was.  Readers get the derived
    label re-derived; the evidence is untouched.

    Deliberately narrow.  Only `silent` is re-examined, because only `silent` makes a claim the
    stored evidence can refute on its own.  A frozen `pinned` is left alone: whether one survivor
    is an answer depends on the domain declared *at that round*, which is a different file, and
    the pin caveats are already carried by the live resolution.
    """
    consistent = r.get("consistent")
    if r.get("outcome") != "silent" or not consistent:
        return r
    if r.get("kind") == "incompleteness":
        mine = "hole:" + str(r.get("witness", "")).split(":", 1)[-1] + "="
        vals = {t: ok for t, ok in consistent.items() if t.startswith(mine)}
    else:
        vals = consistent
    if not vals or all(vals.values()):
        return r
    return dict(r, outcome="partial", relabelled_from="silent")


def _designer_indifferent(case: cases.Case) -> list[dict]:
    """Questions the designer was asked and declined to settle, with the proof that they are real
    questions.

    A `silent` resolution has two very different causes and they must not be reported as one.
    Either the projection was too weak -- the witness never actually forced the readings apart --
    or the readings *were* forced apart, in a way the kernel certified, and the designer said the
    design is free to do either.  The second is not a failure of the framework: it is the finding.
    It says the author of the specification, asked directly and shown a context where the readings
    provably diverge, does not care which happens -- so the coordinate is a genuine degree of
    freedom and no number of further rounds will close it.  What the decided specification owes
    such a coordinate is a sentence saying it is free, not a value.

    Only findings whose separation carries a certificate are listed, so the claim rests on the
    kernel rather than on a search that happened to come back empty.
    """
    rp, wp = case.path("resolution.json"), case.path("witnesses.json")
    if not (os.path.isfile(rp) and os.path.isfile(wp)):
        return []
    with open(wp) as f:
        wits = {w["id"]: w for w in json.load(f)["witnesses"]}
    with open(rp) as f:
        res = json.load(f)["resolutions"]
    out = []
    for r in res:
        if r["outcome"] != "silent":
            continue
        w = wits.get(r["witness"], {})
        cert = w.get("certificate", {})
        proved = bool(cert.get("pinning") if w.get("kind") == "incompleteness"
                      else cert.get("disjoint"))
        out.append({"witness": r["witness"], "kind": w.get("kind"),
                    "question": w.get("hole") or w.get("choice"),
                    "separation_certified": proved,
                    "accepted": r.get("kept", []),
                    "designer_said": r.get("designer_said", ""),
                    "cost": w.get("cost"), "stimulus": w.get("ctx"),
                    "why": ("the readings are provably distinguishable at this context and the "
                            "designer accepted every one of them, so the coordinate is free"
                            if proved else
                            "the readings were separated by search but no certificate closed, "
                            "so the silence may be the projection's rather than the designer's")})
    return out


def verify(case: cases.Case, violations: list[str] | tuple = ()) -> dict:
    """Re-diagnose the refined spec and certify that it is now determined.

    There is no reference to sweep against, and its absence is the reason this step is short.
    What can be checked is what the specification says about itself: that the four queries no
    longer find an ambiguity, a hole or a contradiction, and that the decided configuration admits
    exactly one observation at every legal context in the domain -- the second by the kernel, not
    by evaluation.  Whether the decided reading is the one the designer wanted is not a question
    this step can ask again; it was asked at stage 5 and the answer is in the record.

    `violations` is the list of properties stage 4 proved the definitions break, this round.  It
    is passed in rather than re-read because the four queries cannot find it: they ask whether the
    prose leaves something open, and a violated property is the prose closing something two ways.
    A round that found one does not converge whatever the re-diagnosis says -- the repair its
    decisions authored is a claim about the *next* round's prose, and the only thing that can
    check it is the next round's stage 4 finding nothing.  Reporting `converged` here would
    certify the specification on the strength of an edit nobody has re-run the kernel against.
    """
    redo = diagnose.diagnose(case)
    path = case.path("sandbox", "DecidedCheck.lean")
    with open(path, "w") as f:
        f.write(DECIDED_MEASURE)
    res = leanrun.run(path)
    log = res["log"]
    decided = next((f for f in res["findings"] if f["query"] == "decided"), {})

    # The certificate, asked for only when the measurement says there is one to be had.  A spec
    # that is not determined has nothing here to prove and the theorem would be false, so its
    # absence is a consequence of the measurement rather than a second, weaker verdict.
    cert = {"axioms": {}}
    if decided.get("determined"):
        cpath = case.path("sandbox", "DecidedCert.lean")
        with open(cpath, "w") as f:
            f.write(DECIDED_CERT)
        cert = leanrun.run(cpath)
        log += "\n" + cert["log"]
    with open(case.path("decided.log"), "w") as f:
        f.write(log)

    indiff = _designer_indifferent(case)
    counts = redo.get("counts", {})
    still_open = (counts.get("ambiguity", 1) != 0 or counts.get("incompleteness", 1) != 0
                  or counts.get("contradiction", 1) != 0)
    # A decided reading that admits nothing anywhere.  `determined` asks for exactly one admitted
    # observation per legal context, so an unsatisfiable configuration fails it in the same field
    # as a merely under-determined one, and the two must not be reported as one thing.  It happens
    # when the designer resolves a fork onto a reading the rest of the specification contradicts:
    # the question is answered, the answer is certified, and the specification still has no model.
    # No further round can help, because the block is not a missing answer -- it is two sentences
    # that cannot both hold.
    decided_unsat = bool(decided) and not decided.get("determined") \
        and decided.get("dead_at", 0) > 0
    out = {"case": case.name,
           "rediagnosis": {k: redo.get(k) for k in ("ok", "counts", "uncertified")},
           "decided": decided,
           "decided_unsatisfiable": decided_unsat,
           # Named, not counted.  A reader asking why a round did not converge needs to know which
           # guarantee the definitions broke, and the list is short by construction.
           "violated_properties": list(violations),
           "determinism_certificate": ("decided_determined" in cert["axioms"]
                                       and "sorryAx" not in cert["axioms"]["decided_determined"]),
           "lean": leanrun.summarize(res),
           "designer_indifferent": indiff,
           # Why a case that has not converged has not converged.  `spec_contradiction` is checked
           # first because it is the stronger statement: an unsatisfiable decided reading blocks
           # the case whatever the designer thinks of the remaining questions.
           # `designer_indifferent` means further rounds are pointless for a different reason --
           # the question is open, provably observable, and the author accepts either answer.
           # Either way only a change to the specification's intent can close it, which is the
           # recommendation the report carries for that case.
           #
           # `unobservable_coordinate` is the third, and it is the only one the projection settles
           # by itself: a hole shows freedom -- so it is a real gap -- and stage 3 finds no context
           # anywhere in the domain at which the values it can take are pairwise distinguishable.
           # A designer can narrow such a coordinate and can never be *asked* about it, because the
           # thing that would have to differ never reaches an output port.  It is separated from
           # `designer_indifferent` because the two ask for different repairs: an indifferent
           # question needs the specification to say the coordinate is free, an unobservable one
           # needs the projection widened or the coordinate declared internal.
           # `violated_property` is second, and it is the only one of the four that asks for
           # another round rather than for a change of intent.  Stage 4 proved that a guarantee
           # the prose states forbids a behaviour the same prose admits; step 07 required the
           # designer's adjudication to be answered by a decision, and that decision rewrote one
           # of the two sentences.  What no document in this round can say is whether the rewrite
           # worked -- the four queries walk straight past a property, so a re-diagnosis that
           # comes back clean is clean about something else.  The check is the next round's stage
           # 4, run against the repaired prose, and until it has run the honest verdict is that
           # this one is not finished.
           # `unseparated` sits between the two, and it is the one that must not be filed as
           # either.  The frame separated the readings somewhere but nowhere disjointly, so the
           # query ran, the oracle answered truthfully, and the observation was consistent with
           # every candidate.  Reported as `designer_indifferent` it claims the author declared a
           # freedom they were never asked about; reported as `unobservable_coordinate` it claims
           # the value cannot reach a port, when what happened is that this frame's contexts were
           # too short to carry it there.  The repair it asks for is a wider `ctxUniverse` and
           # another round, which is the one thing neither of the others is worth spending.
           "blocked_by": ("spec_contradiction" if decided_unsat else
                          "violated_property" if violations else
                          "designer_indifferent"
                          if still_open and any(i["separation_certified"] for i in indiff)
                          else "unseparated" if still_open and indiff
                          else "unobservable_coordinate"
                          if (still_open and counts.get("incompleteness")
                              and not counts.get("pinning"))
                          else None),
           "converged": bool(res["ok"] and decided.get("determined") and not still_open
                             and not violations)}
    with open(case.path("verification.json"), "w") as f:
        json.dump(out, f, indent=1)
    cases.log(case, "verify", converged=out["converged"], blocked_by=out["blocked_by"])
    return out
