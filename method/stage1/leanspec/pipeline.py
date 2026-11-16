#!/usr/bin/env python3
"""leanSpec as numbered steps, each with one input and one output.

The contract itself — one file in, one file out, the input carried verbatim under `inherited`,
the seal enforced at the door — lives in `common/steps.py` and is shared with `leanrtl`.  What is
here is the ten step *bodies* and the table that declares them.

    00 input          the natural-language specification this run is about, and its hash
    01 extraction     clauses with byte-exact provenance; where the prose is open   [authored]
    02 formalization  `admits : Cfg → Ctx → Obs → Bool`, elaborated                 [authored]
    03 diagnosis      the four queries, each finding re-proved as a theorem
    04 properties     what the prose claims about itself, checked in the same frame
    05 witnesses      the cheapest legal context that separates each pair of readings
    06 resolution     the designer, asked once per witness                              [open]
    07 decision       which reading held, what that fixes in `Cfg`, what to rewrite  [authored]
    08 output         the decided Lean spec, the decided prose, the question list
    09 convergence    re-diagnose the decided reading, and say whether it is settled

Three steps are marked `[authored]`.  Those are the model's work — reading prose, proposing
readings, writing semantics, choosing what a resolved question means for the text — and they are
read from `authored/roundN/` rather than produced here, because a step that both writes and
grades its own input is not a step.

One step is open, and it is the only one: **06**, where the designer is asked.  Every other step
runs inside `seal.sealed()`, where `oracle.ask_all` raises.  The seal says a step COULD NOT have
asked; the ledger says it DID NOT; `cases.audit` checks that no query preceded the witness that
justifies it.  All three are wanted.

## Two things this pipeline does not have

**No reference implementation, and so no agreement sweep.**  The only authority is the designer,
and the only claim made at the end is that every question the prose left open was found, put, and
either closed or declared open with a reason.  Step 09 re-diagnoses the *decided* reading and
asks whether it is now determined everywhere; that is a statement about the specification, proved
by the kernel, and it is the honest terminal claim.

**No annotation in the prose.**  `out/spec.decided.txt` is the original document with one
byte-exact replacement per decision and nothing else — no heading we wrote, no list of what is
still open, no marker saying a sentence was changed.  It is a drop-in replacement, and it has to
be one: an implementation author reads the original or decided prose, and a
reader of either must be reading a specification rather than a specification plus our commentary
about it. A proof runner additionally consumes the frozen formal artifacts through a checked
handoff. What is still open is not lost — it is in `out/QUESTIONS.md`, in `out/REPORT.md`, and
structurally in `out/HANDOFF.json` — but it is not in the document that gets handed over.  The
cost is real and is stated in the report: an implementer given only the decided prose cannot tell
a question that was answered from one that was never asked.  That is the price of a clean
interface, and it is paid deliberately rather than by omission.
"""
from __future__ import annotations

import json
import os
import re
import shutil

from common import paths, steps as steps_mod
from common.steps import get as _get, get_all as _get_all, numbered as _numbered   # noqa: F401
from . import cases, diagnose as diagnose_mod, emit, leanrun, oracle, patch, propcheck, refine, \
    schema, witness

AUTHORED = steps_mod.AUTHORED
STEPS_DIR = steps_mod.STEPS_DIR
OUT_DIR = "out"
HANDOFF = 8          # the step of round N-1 that round N reads; see `_chain` and `Chain`

# The deliverables, named once.  Step 08 writes seven of them and step 09 appends `REPORT.md`;
# the audit's leak scan subtracts their names from the step documents, because a filename the
# pipeline prints into its own record is not evidence about anything the agent wrote.
DELIVERABLES = ("DecidedSpec.lean", "DecidedSpec.standalone.lean", "spec.decided.txt",
                "spec.diff", "QUESTIONS.md", "PROPERTIES.md", "HANDOFF.json", "REPORT.md")
D_LEAN, D_STANDALONE, D_PROSE, D_DIFF, D_QUESTIONS, D_PROPERTIES, D_HANDOFF, D_REPORT \
    = DELIVERABLES


# ------------------------------------------------------------------------- the steps

def step_input(case: cases.Case, inp: dict | None, rnd: int) -> dict:
    """00 — the specification this run is about.

    The one step with no predecessor.  Its input is the prose staged into the sandbox when the
    case was created, and every later step that talks about "the spec" means the hash taken here.
    A clause whose span no longer quotes this text is a clause about a different document, and
    step 01 says so.

    Nothing is corrected here.  An earlier version of this pipeline repaired the port list
    against the interface a benchmark harness bound, on the argument that a decision taken
    against a document missing a port is a decision about the wrong module.  The argument was
    right and its premise is gone: there is no harness, no binding, and no source for a port list
    other than the prose itself.  So the interface is whatever the document says it is, the
    extraction records it, `probe.json` is checked against it — and if the prose omits a port,
    that is an incompleteness for the diagnosis to find and the designer to answer, not a defect
    for this step to silently patch.
    """
    prose = cases.prose(case)
    return {
        "ok": True, "problems": [],
        "prose": prose,
        "prose_sha256": cases.sha256(prose),
        "bytes": len(prose),
        "lines": prose.count("\n") + 1,
        "source": case.source or case.name,
        "note": "The input to the whole pipeline: natural language, and nothing else.  No "
                "reference implementation, no expected values, no interface bound from outside "
                "the document.  Everything downstream is derived from these bytes or from what "
                "the designer says when shown a waveform.",
    }


def step_extraction(case: cases.Case, inp: dict, rnd: int) -> dict:
    """01 — semantic extraction, validated against step 00's exact bytes."""
    prose = _get(inp, "prose")
    doc = json.loads(_chain(case).authored("extraction.json", rnd))
    doc.setdefault("decisions", [])
    problems = schema.validate_extraction(doc, prose)

    # What this round is allowed to have already answered.
    #
    # In round 1 the answer is nothing: step 01 is the state *before* any question is answered,
    # and a decision recorded there would be an answer the designer was never asked for.  From
    # round 2 on the extraction is a continuation — it is round N-1's step 07 output, advanced by
    # that round's decisions — so it not only may carry them, it *must*: an inherited decision
    # missing from the record is a question that silently re-opens, and one that appears without
    # having been inherited is exactly the round-1 offence, taken a round later.  Both directions
    # are checked, on (name, round), because a question can be re-posed under a new configuration
    # and the two askings are different decisions.
    inherited = _get(inp, "decisions_doc", None) or {}
    allowed = {(d.get("name"), d.get("round")) for d in inherited.get("decisions", [])}
    have = {(d.get("name"), d.get("round")) for d in doc["decisions"]}
    for name, r in sorted(have - allowed, key=lambda x: (x[1] or 0, x[0] or "")):
        problems.append(
            f"extraction.json records a decision on {name!r} (round {r}) that no earlier round "
            f"took.  A decision is an answer from the designer, and step 01 is sealed; the only "
            f"decisions this document may carry are the ones it inherits."
            if rnd > 1 else
            "extraction.json carries `decisions`: step 01 is the state *before* any question is "
            "answered, and a decision recorded here would be an answer the designer was never "
            "asked for.  Decisions belong to step 07.")
    for name, r in sorted(allowed - have, key=lambda x: (x[1] or 0, x[0] or "")):
        problems.append(
            f"round {r} decided {name!r}, and this round's extraction does not say so.  The "
            f"record accumulates: a question dropped from it is one a later round would be free "
            f"to answer differently, against a designer who has already fixed it.")
    _chain(case).materialise({"extraction.json": json.dumps(doc, indent=1)})
    cases.log(case, "extract", ok=not problems, clauses=len(doc.get("clauses", [])),
              choices=len(doc.get("choices", [])), holes=len(doc.get("holes", [])),
              properties=len(doc.get("properties", [])))
    return {
        "ok": not problems, "problems": problems,
        "extraction": doc,
        "clause_spans": {c["id"]: c["span"] for c in doc["clauses"]},
        "counts": {"clauses": len(doc["clauses"]), "choices": len(doc["choices"]),
                   "holes": len(doc["holes"]), "properties": len(doc["properties"]),
                   "deferred": len(doc.get("deferred", [])), "ports": len(doc["ports"])},
        "open_questions": ([{"kind": "choice", "name": k["name"], "basis": k["basis"],
                             "readings": [c["tag"] for c in k["candidates"]]}
                            for k in doc["choices"]]
                           + [{"kind": "hole", "name": h["name"], "missing": h["missing"]}
                              for h in doc["holes"]]),
        "claims": [{"name": p["name"], "kind": p["kind"], "statement": p["statement"],
                    "expressible": p["expressible"]} for p in doc["properties"]],
    }


def step_formalization(case: cases.Case, inp: dict, rnd: int) -> dict:
    """02 — the partial semantics, elaborated.

    The Lean source is carried *in the document*, not left on disk.  That is what lets step 03
    say which text it diagnosed: it writes the source out of its input before it runs, so an edit
    made to the sandbox between the two steps is overwritten rather than silently used.
    """
    ch = _chain(case)
    ext = _get(inp, "extraction")
    src = ch.authored("Partial.lean", rnd)
    probe = json.loads(ch.authored("probe.json", rnd))
    problems = schema.check_partial(src, ext) + schema.validate_probe(probe, ext)
    if _DEFINES_DECIDED_CFG.search(src):
        problems.append(
            "Partial.lean defines `decidedCfg`.  The decided configuration is derived from the "
            "decision record in step 08 and appended there; writing one by hand here puts a "
            "value into the specification that no query justified, at the exact coordinate this "
            "pipeline exists to keep honest.")
    fields = emit.cfg_fields(src, schema.cfg_field_names(src, ext))
    ch.materialise({"sandbox/Partial.lean": src, "probe.json": json.dumps(probe, indent=1)})
    res = leanrun.run(case.path("sandbox", "Partial.lean"), emit_olean=True)
    with open(case.path("formalize.log"), "w") as f:
        f.write(res["log"])
    ok = not problems and res["ok"]
    cases.log(case, "formalize", ok=ok, lean=leanrun.summarize(res))
    return {
        "ok": ok,
        "problems": problems + leanrun.why_failed(res, "Partial.lean"),
        "partial_lean": src,
        "partial_sha256": cases.sha256(src),
        "probe": probe,
        "cfg_fields": fields,
        "lean": leanrun.summarize(res),
    }


def step_diagnosis(case: cases.Case, inp: dict, rnd: int) -> dict:
    """03 — the four queries, with a kernel-checked certificate per finding."""
    _chain(case).materialise({
        "extraction.json": json.dumps(_get(inp, "extraction"), indent=1),
        "sandbox/Partial.lean": _get(inp, "partial_lean"),
    })
    out = diagnose_mod.diagnose(case)
    # When the certificate file was killed at the wall clock, every theorem in it is reported as
    # "not reached" and the list, read top to bottom, invites its reader to go debug the first
    # name on it -- a claim `lean` never got to, which may be perfectly true.  The cause is one
    # fact about the whole file, so it is stated once, first, ahead of the names.
    wall = ([f"the certificate file did not finish: {out['lean']['certificates']}.  Every "
             f"theorem below is 'not reached', which is a fact about the clock and not about "
             f"any of the claims -- `lean` was killed partway down the file, so the one named "
             f"first is no more at fault than the one named last.  What to change is the size "
             f"of the domain the kernel has to evaluate.  `decide +kernel` reduces `ctxUniverse` "
             f"and `obsUniverse` outright, with none of the compilation `#eval` gets: a universe "
             f"that is COMPUTED -- folded out of a predictor, built by a comprehension, derived "
             f"from the readings -- is re-derived from scratch inside every certificate, where an "
             f"enumerated one is merely read.  The diagnosis itself ran in "
             f"{out['lean']['diagnose']}, which is why the file elaborates and evaluates fine and "
             f"still cannot be certified.  Enumerate the universes, or make them smaller, or both."]
            if out.get("certificates_timed_out") else [])
    gen = {}
    for f in ("Diagnose.lean", "Certificates.lean"):
        p = case.path("sandbox", f)
        if os.path.isfile(p):
            with open(p, errors="replace") as fh:
                gen[f] = fh.read()
    return {
        "ok": bool(out.get("ok")),
        "problems": (out.get("structural_errors", []) + out.get("errors", []) + wall
                     + [f"{k}: {v}" for k, v in (out.get("uncertified") or {}).items()]),
        "diagnosis": out,
        "findings": out.get("findings", []),
        "counts": out.get("counts", {}),
        "domain": out.get("domain", {}),
        "certified": out.get("certified", {}),
        "uncertified": out.get("uncertified", {}),
        "generated_lean": gen,
    }


def step_properties(case: cases.Case, inp: dict, rnd: int) -> dict:
    """04 — what the prose claims about itself, checked against what it admits.

    A property is not a reading to choose between; it is a claim the specification makes about
    every legal run — an invariant, a guarantee, a bound.  Four questions are put to each one over
    the same finite frame the diagnosis uses, so `decide` closes all of them: is it entailed by
    the readings, is its antecedent ever satisfied, does it eliminate readings of an open fork,
    is it independent of every fork.

    This runs BEFORE witness synthesis, and the order is the point.  If exactly one reading of a
    fork satisfies a property the prose itself states, then the prose has already answered that
    question — and asking the designer anyway invites an answer the specification's own guarantee
    forbids, which would be recorded as `decided` with nothing downstream to catch it.  So step
    05 reads the pins from here and retires those forks without spending a query.

    A pin only retires a question when its certificate closed.  An uncertified pin is a search
    result, and closing a question on a search result is the shortcut this framework refuses
    everywhere else.
    """
    _chain(case).materialise({
        "extraction.json": json.dumps(_get(inp, "extraction"), indent=1),
        "sandbox/Partial.lean": _get(inp, "partial_lean"),
    })
    out = propcheck.check(case)
    return {
        "ok": bool(out.get("ok")),
        # A violated property is a FINDING, not a failed step: the prose states a guarantee and
        # the same prose admits a run that breaks it.  That is the sharpest thing this stage can
        # produce and it is reported, with its certified counterexample, rather than treated as
        # the checker having gone wrong.  What does fail the step is a certificate that would not
        # close — then the finding is unproved and must not be believed.
        "problems": [f"{k}: {v}" for k, v in (out.get("uncertified") or {}).items()],
        "properties": out,
        "property_findings": out.get("findings", []),
        "property_counts": out.get("counts", {}),
        "property_pins": out.get("pins", []),
        "violated_properties": [r["name"] for r in out.get("properties", [])
                                if r.get("entailed") is False],
    }


def step_witnesses(case: cases.Case, inp: dict, rnd: int) -> dict:
    """05 — the cheapest legal context that separates each pair of readings."""
    _chain(case).materialise({
        "extraction.json": json.dumps(_get(inp, "extraction"), indent=1),
        "probe.json": json.dumps(_get(inp, "probe"), indent=1),
        "diagnosis.json": json.dumps(_get(inp, "diagnosis"), indent=1),
        "properties.json": json.dumps(_get(inp, "properties"), indent=1),
    })
    doc = witness.build(case)
    return {
        "ok": True, "problems": [],
        "witnesses_doc": doc,
        "witnesses": doc["witnesses"],
        "retired_by_property": doc.get("retired_by_property", []),
        "totals": doc.get("totals", {}),
    }


def step_resolution(case: cases.Case, inp: dict, rnd: int) -> dict:
    """06 — the designer, asked this round's questions in one sitting.  The only open step.

    Everything before this point was derived from the prose.  This is the moment the questions
    leave the machine, and they leave it in one shape only: here is the input, here are the
    waveforms it could produce, which one is right — with the readings shuffled, lettered, and
    stripped of every name this pipeline uses for them.  The designer never sees a reading's tag,
    never sees the diagnosis, and is never asked which of *our* readings is meant.  Three answers
    come back per question and all three are results: this waveform, none of these, or any of them.

    All of the round's distinct questions go to one designer at once.  Two witnesses that ask the
    same thing are collapsed to one question first, so the number put is the number of genuinely
    different forks; the rest are answered by the same letter and the ledger says so.

    A prediction is recorded for every reading BEFORE the questions are put, in step 05, which is
    what makes the answers scorable rather than interpretable.  The ordering is enforced by the
    seal in front and checked by `cases.audit` behind.

    Who answers is `oracle.asking()`, read here rather than passed in, and written into this
    step's own document rather than only into the oracle's.  The default is the designer and the
    only thing that changes it is `--oracle` at the command line.  A benchmark run answers from
    the design's reference implementation, which is a different claim about the resulting
    specification -- measured against an implementation, not decided by an author -- and every
    artifact downstream of here is expected to carry the label rather than infer it.
    """
    _chain(case).materialise({
        "probe.json": json.dumps(_get(inp, "probe"), indent=1),
        "witnesses.json": json.dumps(_get(inp, "witnesses_doc"), indent=1),
    })
    kind = oracle.asking()
    doc = refine.resolve(case, rnd=rnd, kind=kind)
    return {
        "ok": True, "problems": [],
        "oracle_kind": kind,
        "reference": doc.get("reference") or [],
        "resolution": doc,
        "resolutions": doc["resolutions"],
        "outcomes": doc.get("outcomes", {}),
        "queries": doc.get("queries"),
        "sitting": doc.get("sitting"),
    }



def step_decision(case: cases.Case, inp: dict, rnd: int) -> dict:
    """07 — what the answers mean, checked against the answers.

    The authored document says which reading held, which coordinate of `Cfg` that fixes, which
    span of the prose has to change, and which coordinates are being left open on purpose.
    Four checks, all mechanical:

      * every decision names a witness step 06 actually resolved, and agrees with what it kept;
      * every patch hunk quotes the prose byte for byte and lands inside a clause the decision
        is based on;
      * every field of `Cfg` is decided or declared open;
      * the resulting extraction still validates — a fork recorded as answered may not still be
        listed as an open question.
    """
    ch = _chain(case)
    doc = json.loads(ch.authored("decisions.json", rnd))
    ext = json.loads(json.dumps(_get(inp, "extraction")))          # a copy, not the original
    prose, spans = _get(inp, "prose"), _get(inp, "clause_spans")
    fields = _get(inp, "cfg_fields")
    res = {r["witness"]: r for r in _get(inp, "resolutions")}
    problems: list[str] = []

    # 1 — a decision is a reading of an answer, so it has to name the answer.
    for i, d in enumerate(doc.get("decisions", [])):
        w = f"decision[{i}] ({d.get('name')!r})"
        for f in ("kind", "name", "resolved_to", "witness", "evidence", "round"):
            if f not in d:
                problems.append(f"{w}: missing {f!r}")
        wit = d.get("witness")
        if d.get("kind") == "model":
            continue
        if d.get("kind") == "property":
            # A fork the prose answered itself.  It has no witness because no query was spent on
            # it: step 04 proved that exactly one reading satisfies a guarantee the specification
            # states, and step 05 retired the question rather than putting it to the designer.
            # The check is against the certified pin, not against a resolution.
            pin = next((p for p in _get(inp, "property_pins", []) if p["name"] == d.get("name")),
                       None)
            if pin is None:
                problems.append(f"{w}: declared decided by a property, and step 04 certified no "
                                f"pin for {d.get('name')!r}")
            elif pin["resolved_to"] != d.get("resolved_to"):
                problems.append(f"{w}: the property pin fixes {d.get('name')!r} to "
                                f"{pin['resolved_to']!r}, not {d.get('resolved_to')!r}")
            continue
        if wit not in res:
            problems.append(f"{w}: witness {wit!r} is not one step 06 resolved ({sorted(res)})")
            continue
        r = res[wit]
        # `pinned_undeclared` is admitted, `pinned_sampled` is not, and the difference is what
        # stage 1 claimed rather than how confident anyone feels.  A sampled menu is an
        # affirmative statement that the option set is incomplete: one survivor out of it is one
        # survivor out of the values offered, and the value the designer holds may never have
        # been on the menu.  An undeclared menu makes no claim either way; the pin is carried
        # with the caveat attached and surfaces in the deliverables as one.
        if r["outcome"] == "pinned_sampled":
            dm = r.get("domain") or {}
            problems.append(f"{w}: witness {wit!r} pinned one of {dm.get('offered')} value(s) "
                            f"offered out of a domain of {dm.get('size')}, and a sampled option "
                            f"set cannot pin -- the value the designer holds need never have "
                            f"been offered. Enumerate the domain, or widen the menu")
            continue
        if r["outcome"] not in ("decided", "pinned", "pinned_undeclared"):
            problems.append(f"{w}: witness {wit!r} came back {r['outcome']!r}, which does not "
                            f"decide anything -- a decision taken on it would be the agent "
                            f"answering its own question")
            continue
        kept = _tags(r.get("kept"), d["name"]) or set(r.get("pinned_to") or [])
        # Kept, from the witness the decision names; eliminated, from every query this round put
        # about the same question.  A fork with three readings is asked as pairwise comparisons,
        # and each query can only eliminate the reading it was the comparison against.  Read out
        # of one of them alone, a decision could never record more than one rejection however
        # many the round actually made, and the deliverables would understate what the designer
        # ruled out.  What is kept stays tied to the named witness: that is the answer the
        # decision claims to be reading.
        #
        # `partial` counts here, and only here.  It is the outcome for a query that narrowed the
        # menu without emptying it, and its eliminations are exactly as sound as a decided
        # query's: the chosen waveform contradicted those readings' predictions.  What it may not
        # do is settle the answer, and it does not — `kept` above comes from the named witness
        # alone, which the check above has already required to have decided.  `silent` and
        # `observed` eliminate nothing; `outside` is excluded deliberately, because a sibling
        # query reporting the designer off the menu is a contradiction to surface rather than a
        # licence to reject.
        gone: set[str] = set()
        for other in res.values():
            if (_speaks_about(other, d["name"])
                    and other.get("outcome") in ("decided", "pinned", "pinned_undeclared",
                                                 "partial")):
                gone |= _tags(other.get("eliminated"), d["name"])
        if d.get("resolved_to") not in kept:
            problems.append(f"{w}: resolved_to {d.get('resolved_to')!r} is not what the designer "
                            f"kept ({sorted(kept)})")
        # ...and it must not be what another query THREW OUT.  `kept` above is scoped to the one
        # witness the decision cites, and `refine._resolve` scores each witness only against the
        # tags its own context predicted.  A reading the context never evaluated is therefore
        # absent from both lists there, so a fork asked pairwise can report `decided` on a value
        # a sibling context refutes.  Both queries are sound and neither is a contradiction to
        # surface; what is unsound is reading the answer out of the query that asked the smaller
        # question.  The union of eliminations is the right side to test against: an answer that
        # contradicted a reading's prediction contradicts it whichever witness carried it.
        elif d.get("resolved_to") in gone:
            culprits = sorted(o["witness"] for o in res.values()
                              if _speaks_about(o, d["name"])
                              and o.get("outcome") in ("decided", "pinned", "pinned_undeclared",
                                                       "partial")
                              and d["resolved_to"] in _tags(o.get("eliminated"), d["name"]))
            problems.append(f"{w}: resolved_to {d.get('resolved_to')!r} was kept by witness "
                            f"{wit!r} but eliminated by {culprits} -- the citing witness's "
                            f"context did not evaluate every reading of {d['name']!r}, so its "
                            f"`decided` is local. Cite a witness that survives the whole round")
        for tag in d.get("rejected", []):
            if tag not in gone:
                problems.append(f"{w}: {tag!r} is listed as rejected, but this round's queries "
                                f"about {d['name']!r} eliminated {sorted(gone)} -- a reading is "
                                f"only rejected if a query rejected it")

    # 1b — every contradiction the designer settled is answered by a decision.
    #
    # Without this the adjudication is optional.  Step 06 can put a violated property to the
    # designer, get back "the guarantee is wrong, drop it", and step 07 can then produce a
    # `decisions.json` that never mentions it -- and nothing downstream notices, because a
    # violation closes no fork and fixes no coordinate of `Cfg`, so neither `_advance` nor
    # `emit.derive` has anything to miss.  The query would be spent, the answer recorded in the
    # ledger, and the prose left saying both things.  The obligation is therefore stated here
    # directly: an answered contradiction is a repair owed.
    #
    # Only `decided` obliges.  `outside` is the designer saying neither sentence is the fault
    # and `unadjudicated` is no answer at all; there is nothing for a decision to read out of
    # either, and both are held by step 09 instead, which refuses to converge a round whose
    # contradictions are still open.
    named = {d.get("name") for d in doc.get("decisions", []) if d.get("kind") == "violation"}
    for r in res.values():
        if r.get("kind") == "violation" and r.get("outcome") == "decided":
            if r.get("property") not in named:
                stands = ", ".join(sorted(_tags(r.get("kept"), r.get("property") or ""))) or "one"
                problems.append(
                    f"the designer adjudicated the contradiction at property "
                    f"{r.get('property')!r} -- they said the {stands} sentence is the one that "
                    f"stands -- and no decision records it. A violated property is the strongest "
                    f"finding this pipeline produces; an answer to it that reaches no decision is "
                    f"a query spent for nothing. Write a decision with kind 'violation', name "
                    f"{r.get('property')!r}, witness {r['witness']!r}, and the patch that repairs "
                    f"the sentence the designer disowned")

    # 2 — the repairs, against the text they claim to be repairing.
    #
    # A hunk may only touch a clause the decision's own question rests on.  That means the
    # question has to exist: a decision naming none — a `model` decision, say, which revises the
    # projection rather than a reading of the prose — has no basis, and if `cid` were left as
    # `None` here it would match every `fixed` clause's absent `choice_id` and license a rewrite
    # of the entire spec.  So no question, no hunks.
    hunks, allowed = [], {}
    for d in doc.get("decisions", []):
        name = d.get("name")
        if d.get("kind") == "violation":
            # The one scope that is declared rather than derived, and the reason is a fact about
            # the finding.  A fork's repair rewrites the sentence the fork came from, and the
            # extraction says which sentence that is.  A violated property has two sides and the
            # extraction only knows one of them: `basis` records the clauses the guarantee was
            # read out of, and nothing records which clauses define the behaviour it forbids --
            # the behaviour comes out of `admits`, which is the whole formalization.  So when the
            # designer disowns the definitions, the clauses to repair cannot be looked up.
            #
            # They are therefore named by the decision, in `clauses`, and every name is checked
            # against the extraction.  That is weaker than a fork's scope and it is written down
            # as weaker: the guarantee here is that the repair lands on clauses that exist and
            # are listed, not that they are the only ones it could have touched.  What is not
            # weakened is `patch.validate` -- every hunk still quotes the prose byte for byte,
            # still may not overlap another, and still must fall inside one of these spans.
            declared = list(d.get("clauses") or [])
            known = {c["id"] for c in ext["clauses"]}
            unknown = [c for c in declared if c not in known]
            if unknown:
                problems.append(f"decision {name!r} claims to repair clause(s) {unknown} that "
                                f"the extraction does not contain")
                continue
            basis = _property_basis(inp, name) | set(declared)
            if d.get("patch") and not basis:
                problems.append(f"decision {name!r} carries {len(d['patch'])} patch hunk(s) and "
                                f"names no clause. A violation decision must list, in `clauses`, "
                                f"the clauses whose text it rewrites -- for this finding they "
                                f"cannot be derived, so an unnamed scope is an unbounded one")
                continue
            for h in d.get("patch", []):
                allowed[len(hunks)] = basis
                hunks.append(dict(h, decision=name))
            continue
        cid = _cid(ext, "choices", name) or _cid(ext, "holes", name)
        basis = {c["id"] for c in ext["clauses"]
                 if cid is not None and cid in (c.get("choice_id"), c.get("hole_id"))}
        if d.get("patch") and cid is None:
            problems.append(f"decision {name!r} carries {len(d['patch'])} patch hunk(s) but "
                            f"names no choice or hole in the extraction, so there is no clause "
                            f"it is entitled to rewrite")
            continue
        if d.get("patch") and not basis:
            problems.append(f"decision {name!r} names {cid!r}, but no clause is attributed to "
                            f"it -- a repair has to land on the text the question came from")
            continue
        for h in d.get("patch", []):
            allowed[len(hunks)] = basis
            hunks.append(dict(h, decision=name))
    problems += patch.validate(hunks, prose, {k: tuple(v) for k, v in spans.items()}, allowed)

    # 3 — every coordinate of `Cfg` accounted for.
    #
    # Across rounds, not within one.  A round's `decisions.json` records the decisions *that
    # round* took, because that is what its resolutions can be checked against; asking round 3's
    # document alone to account for round 1's would force every round to re-list every earlier
    # decision, which is a copy that can drift from what it copies.  `remaining_open`, in
    # contrast, is always the *current* list: what is still open after this round.
    prior = [d for ds in _get_all(inp, "decisions") for d in ds]
    acc = dict(doc, decisions=prior + list(doc.get("decisions", [])))
    seen: dict[str, str] = {}
    for d in acc["decisions"]:
        if d.get("kind") == "model" or not d.get("cfg_field"):
            continue
        if d["cfg_field"] in seen and seen[d["cfg_field"]] != d.get("name"):
            problems.append(f"`{d['cfg_field']}` is decided in more than one round, by "
                            f"{seen[d['cfg_field']]!r} and by {d.get('name')!r} -- a coordinate "
                            f"already fixed is not open to a second answer")
        seen[d["cfg_field"]] = d.get("name")

    # `Cfg` is not cumulative, and this used to assume it was.  A coordinate exists because the
    # prose left it undetermined; once a decision has been written into the prose, the next
    # round's extraction marks that clause `fixed`, the question is no longer a `choice` or a
    # `hole`, and the next round's `Partial.lean` has no field for it -- correctly, because a
    # decided coordinate is not a free parameter any more.  Handing the earlier decision to
    # `derive` anyway asks it to assign a field that does not exist, and it refuses the whole
    # decided spec with "`h_output_latency` is not a field of `Cfg`" -- naming the one thing that
    # went right.  Measured on `accu`, round 1 closed five coordinates and round 2 could not
    # produce a decided spec at all.
    #
    # So an earlier decision whose coordinate this round dropped is carried as history, the same
    # treatment `model` and `violation` decisions get, and for the same reason: it fixes nothing
    # in *this* `Cfg`.  What it fixed is in the prose.
    #
    # Which is exactly the thing to check, because it is the one way this can go wrong quietly.
    # `_advance` retires a question on the strength of the decision alone, whether or not the
    # decision carried a patch; a patchless one therefore drops the field from the next round's
    # `Cfg` while the prose still does not say what the designer chose, and the answer survives
    # nowhere.  A `property` decision is the exception and needs no patch -- the prose answered
    # that fork itself, so it already determines the coordinate.
    #
    # This fires only when a field is retired, which only happens when the round was AUTHORED.  A
    # round carried forward by `author.carried_documents` keeps round 1's field list, so `known`
    # holds every coordinate and this loop never runs.  The rule itself does not depend on the
    # schedule, so it also lives in step 08 as `_unwritten_answers`, stated as what it is about:
    # an answer that fixed a coordinate has to be in the decided prose.  Kept here as well because
    # on the authored path it fails the round one step earlier, and because `retired` is built in
    # the same pass.
    known = {f["field"] for f in fields}
    retired = []
    for d in prior:
        f = d.get("cfg_field")
        if not f or f in known:
            continue
        retired.append({"cfg_field": f, "name": d.get("name"), "round": d.get("round"),
                        "resolved_to": d.get("resolved_to")})
        if d.get("kind") != "property" and not d.get("patch"):
            problems.append(
                f"`{f}` was decided in round {d.get('round')} by {d.get('name')!r} and is no "
                f"longer a field of `Cfg`, but that decision carried no patch -- so the prose "
                f"never learned the answer and this round's formalization dropped the only other "
                f"place it was written down. A decision that retires a coordinate has to land in "
                f"the text")
    retired_fields = {r["cfg_field"] for r in retired}
    assignments, still_open, derr = emit.derive(
        fields, dict(acc, decisions=[d for d in acc["decisions"]
                                     if d.get("cfg_field") not in retired_fields]))
    problems += derr

    # 4 — the extraction, advanced by the decisions rather than edited by hand.
    ext = _advance(ext, acc)
    problems += [f"decided extraction: {e}" for e in schema.validate_extraction(ext, prose)]

    if not problems:
        ch.materialise({"extraction.json": json.dumps(ext, indent=1)})
    return {
        "ok": not problems, "problems": problems,
        "decisions_doc": dict(doc, decisions=acc["decisions"]),
        "decisions": doc.get("decisions", []),
        "patch_hunks": hunks,
        "assignments": assignments,
        "still_open": still_open,
        # The coordinates that stopped existing because their answer is now in the prose.  Not a
        # problem and not an omission, but the two look identical from `decidedCfg` alone -- the
        # field is simply absent -- so the reason is recorded where an audit can read it.
        "retired_coordinates": retired,
        "extraction_decided": ext,
    }


def _tags(entries: list[str] | None, name: str) -> set[str]:
    """The reading tags a resolution kept or eliminated, for one question.

    `refine.py` labels candidates for the *oracle*, where a label has to be unique across every
    question asked in one run: a fork's readings come back as `out_phase:same_edge`, a hole's
    values as `hole:dout_idle=accumulator`, and the bare `hole:dout_idle` that stands for the
    hole left open.  A decision names a reading the way the specification does — `same_edge`,
    `accumulator` — so the two vocabularies are joined here, once, instead of the decision record
    being asked to spell things in the oracle's dialect.

    There is one dialect now.  There used to be two, because there were two backends and one of
    them resolved a single question per query and returned its tags bare; with the designer as
    the only backend every list is qualified, and an unqualified entry is a bug rather than a
    second convention.  The tolerant branch is kept because it costs one line and because the
    failure it would produce — every tag silently attributed to every question — is exactly the
    kind that does not show up in an output.
    """
    entries = entries or []
    if not any(":" in e for e in entries):
        return set(entries)
    out = set()
    for e in entries:
        if e.startswith(f"{name}:"):
            out.add(e.split(":", 1)[1])
        elif e.startswith(f"hole:{name}="):
            out.add(e.split("=", 1)[1])
    return out


def _speaks_about(res: dict, name: str | None) -> bool:
    """Is this resolution an answer to the question `name`?

    By WITNESS ID, not by tag.  `_tags` is a translator and not a filter: asked whether a bare
    list mentions a question it answers yes for every question, and anything filtering on it
    would attribute one question's answer to all of them.

    Every witness id but `contradiction:default` carries its question at index 1 —
    `ambiguity:<q>:<a>:<b>`, `repair:<q>:<a>:<b>`, `incompleteness:<q>` — so the id is the
    reliable source.  The tag fallback is kept for the ids that name no question.
    """
    parts = (res.get("witness") or "").split(":")
    if len(parts) > 1:
        return parts[1] == name
    return bool(_tags(res.get("kept"), name or "") or _tags(res.get("eliminated"), name or ""))


def _property_basis(inp: dict, name: str | None) -> set[str]:
    """The clauses the property called `name` was read out of.

    Read from step 04's document rather than from the extraction, because that is the row the
    violation was proved against and the two can disagree by a round: a property dropped from a
    later extraction still has a certified counterexample in the chain, and a repair to it still
    has to land somewhere.  `basis` is a clause id or a list of them — `schema.validate_extraction`
    accepts both spellings — so both are normalised here.
    """
    for p in (_get(inp, "properties", {}) or {}).get("properties", []):
        if p.get("name") == name:
            b = p.get("basis") or []
            return {b} if isinstance(b, str) else set(b)
    return set()


def _cid(ext: dict, where: str, name: str | None) -> str | None:
    """The id of the choice or hole called `name`, or None.

    Clauses point at questions by id (`C8` claims `K1`), decisions name them by name
    (`out_phase`), and the two have to be joined somewhere.  Here, once.
    """
    for q in ext.get(where, []):
        if q.get("name") == name:
            return q.get("id")
    return None


def _advance(ext: dict, doc: dict) -> dict:
    """The extraction as the decisions leave it: answered questions closed, and recorded.

    Mechanical, and that is the point.  A hand edit at this coordinate can close a question the
    designer did not answer, or leave one open that they did.  Derived from the decision record
    instead, the two cannot drift.
    """
    answered = {(d["kind"], d["name"]) for d in doc.get("decisions", [])
                if d.get("kind") in ("choice", "hole")}
    # A property-pinned fork closes too: the prose answered it, which is a stronger authority
    # than a query, and leaving it in `choices` would re-pose it next round.
    answered |= {("choice", d["name"]) for d in doc.get("decisions", [])
                 if d.get("kind") == "property"}
    # `None` is dropped deliberately.  A decision taken in an earlier round names a question this
    # extraction no longer lists, so `_cid` returns None for it — and an unfiltered None in this
    # set matches every clause whose `choice_id` is absent, which would strip the `hole_id` off a
    # clause whose hole is still open and quietly mark it fixed.
    closed_ids = {_cid(ext, "choices" if k == "choice" else "holes", n)
                  for k, n in answered} - {None}
    ext["choices"] = [k for k in ext["choices"] if ("choice", k["name"]) not in answered]
    ext["holes"] = [h for h in ext["holes"] if ("hole", h["name"]) not in answered]
    for c in ext["clauses"]:
        if c.get("choice_id") in closed_ids or c.get("hole_id") in closed_ids:
            c["status"] = "fixed"
            c.pop("choice_id", None)
            c.pop("hole_id", None)
    ext["decisions"] = doc.get("decisions", [])
    return ext


def _unwritten_answers(ddoc: dict, hunks: list[dict]) -> list[str]:
    """Every decision that fixed a coordinate, and whether the prose ever learned its answer.

    This check used to live in step 07, phrased as a fact about retirement: a coordinate that was
    decided in an earlier round and is no longer a field of this round's `Cfg` must have carried a
    patch, because dropping the field removes the only other place the answer was written down.
    That phrasing was tied to a schedule where every round re-authored `Partial.lean` from the
    decided prose and so kept only the still-open coordinates.  A round carried forward by
    `author.carried_documents` narrows round 1's frame instead, so nothing is ever retired, and the
    step 07 check goes quiet -- not because the defect stopped being possible, but because its
    symptom did.  A patchless decision now leaves the answer pinned in `Cfg` and absent from the
    prose, and `spec.decided.txt` is the deliverable.

    So the rule is restated as what it was always about, at the step that produces the prose and
    can see every round's hunks at once: an answer that fixed a coordinate has to be in the text.
    `property` decisions are still exempt for the original reason -- the prose answered that fork
    itself, so there was nothing to rewrite -- and so are `model` decisions, which record what the
    run assumed rather than what the designer chose.

    `hunks` must be the list BEFORE `patch.supersede`.  A round-1 repair that round 2 rewrote is
    not an answer that never reached the prose; it is one whose sentence was written twice, and
    checking the surviving set would report the round-1 decision as unwritten on exactly the cases
    that took two rounds to get the sentence right.

    This is stricter than the check it replaces, deliberately.  The old one could only fire from
    round 2 onward, because a decision's field is always present in the round the decision is made
    -- so a patchless answer was tolerated for one round on the argument that `Cfg` still held it,
    and was caught later when the field went away.  Under the carry the field never goes away, so
    "later" never comes.  Asked of `accu`'s three recorded rounds this reports nothing: all six
    coordinate-fixing decisions there carry a hunk, which is to say the rule was already the
    practice and only the enforcement was schedule-dependent.
    """
    wrote = {h.get("decision") for h in hunks}
    out = []
    for d in ddoc.get("decisions", []):
        if d.get("kind") in ("property", "model") or not d.get("cfg_field"):
            continue
        if d.get("name") not in wrote:
            out.append(f"`{d['cfg_field']}` was decided in round {d.get('round')} by "
                       f"{d.get('name')!r} as {d.get('resolved_to')!r}, but no round's patch "
                       f"hunks carry that decision -- so the answer is in `Cfg` and nowhere in "
                       f"the decided prose. A decision that fixes a coordinate has to land in "
                       f"the text")
    return out


def step_output(case: cases.Case, inp: dict, rnd: int) -> dict:
    """08 — the deliverables, and the handoff.

    The decided Lean specification, with the proof that it is determined and one refutation per
    reading the designer ruled out; the decided prose, which is the original file with one
    byte-exact replacement per decision and *nothing else*; the question list, which is what the
    two of them are answers to; and `HANDOFF.json`, which is this half's own record of what it
    produced.

    `QUESTIONS.md` is written here, in a sealed step, and that is worth being explicit about
    rather than looking like a leak.  The answers in it are read out of step 06's recorded
    resolutions, which arrived in this step's input document like everything else in the chain.
    This step does not ask the designer anything; it reads what the step that was allowed to
    asked.

    This is also the handoff step: round N+1's step 00 continues from this document.  Step 09 is
    the round's terminal accounting — it re-diagnoses what was decided here — and nothing
    downstream reads it.
    """
    ch = _chain(case)
    partial = _get(inp, "partial_lean")
    assignments, still_open = _get(inp, "assignments"), _get(inp, "still_open")
    ddoc, findings = _get(inp, "decisions_doc"), _get(inp, "findings")
    prose = _get(inp, "prose")
    fields = _get(inp, "cfg_fields")
    props = _get(inp, "properties", None)
    # Every round's repairs, not this round's.  Each round's step 00 re-reads the same prose, so
    # a hunk's offsets mean the same thing in every round, and the decided prose is the original
    # with *all* of them applied — taking only this round's would silently drop the rewrite round
    # 1 authored and hand back a specification whose text still contains the sentence round 1 was
    # convened to fix.  Each round's set was checked against its own clause spans in step 07;
    # what no round could check is a pair that crosses a round boundary, and `patch.overlaps`
    # below does that.
    hunks_all = [dict(h, round=r) for r, hs in _numbered(inp, "patch_hunks") for h in hs]
    # ...except where a later round rewrote a sentence an earlier round had already rewritten,
    # which is not a collision to refuse but the thing a second round is convened to do.  See
    # `patch.supersede`: same span, later round wins, and what it replaced is kept as a record
    # because the decided prose cannot show it.
    hunks, superseded = patch.supersede(list(hunks_all))

    # Two derived edits to the authored semantics, both from the decision record and neither
    # written by hand.  `Cfg`'s defaults become the decided values, so `defaultCfg` — which is
    # what the diagnosis queries are asked about — is the decided configuration and step 09's
    # re-diagnosis measures the specification being shipped rather than the one step 02 posed.
    # And `decidedCfg` is appended, because every downstream consumer reads that name.  The
    # authored file on disk is untouched: it stays the undecided specification it was in step 02.
    partial_decided, rewritten = emit.decide_partial(partial, assignments)
    missing = sorted(set(assignments) - set(rewritten))
    partial_full = partial_decided.rstrip() + "\n" + _decided_trailer(assignments, still_open)

    decided_lean, ref_errs = emit.gen_lean(case.name, fields, assignments, still_open,
                                           ddoc, findings, partial)
    library_src = leanrun.library_source()
    standalone = emit.standalone(decided_lean, partial_full, library_src)
    el = emit.elaborate(case.sandbox, decided_lean, standalone, partial_full)

    # A second pass, on the failing paths only.  `decided_determined` fails both when the
    # specification admits too many observations and when it admits none, and which of the two
    # happened is not in the failure — it is in the sweep, which the same run already printed.
    # If some legal context admits nothing, the file is re-emitted with a theorem that says so at
    # that context and elaborated again.  The alternative was to emit the theorem always and let
    # it fail on every healthy case, which would put a red `decide` in the deliverable of every
    # case that is fine.
    unsat = next((s for s in (el.get("decided", {}) or {}).get("sweep", [])
                  if not s.get("admits") and s.get("ctx_lean")), None)
    dead_pins = {n for n in (el.get("admitted") or []) if n.startswith("determined_given_")}
    if not el["ok"] and (unsat or dead_pins):
        decided_lean, ref_errs = emit.gen_lean(case.name, fields, assignments, still_open,
                                               ddoc, findings, partial,
                                               unsat["ctx_lean"] if unsat else None, dead_pins)
        standalone = emit.standalone(decided_lean, partial_full, library_src)
        el = emit.elaborate(case.sandbox, decided_lean, standalone, partial_full)

    # The decided prose, and nothing appended to it.  An earlier version added a section naming
    # the questions this run could not settle, on the argument that a document answering three of
    # five questions reads exactly like one that had five answers all along — which is true, and
    # is why the same list is in `QUESTIONS.md`, in `REPORT.md` and in `HANDOFF.json`.  It is not
    # here because this file is the interface: `leanrtl` takes the original prose or this one, and
    # a heading we wrote inside it would make the two inputs different in kind rather than in
    # content.  See the module docstring for the cost.
    decided_prose, record = patch.apply(prose, hunks)
    diff = patch.unified(prose, decided_prose)
    cross_round = patch.overlaps(hunks)

    # The question list is the one deliverable that is about the *run* and not about the current
    # state of the specification, so it is built from the whole chain rather than from this
    # round.  `_advance` closes an answered question, which means round N's extraction no longer
    # contains the questions rounds 1..N-1 settled; asking only this round's document for them
    # produces a QUESTIONS.md whose questions are exactly the ones nobody managed to answer.
    ext_all = emit.merge_extractions(_get_all(inp, "extraction"))
    wits = [dict(w, round=r) for r, d in _numbered(inp, "witnesses_doc")
            for w in d.get("witnesses", [])]
    res = [dict(x, round=r) for r, d in _numbered(inp, "resolution")
           for x in d.get("resolutions", [])]
    questions = emit.questions_markdown(case.name, ext_all, wits, res)
    handoff = _handoff_doc(case, rnd, decided_prose, ddoc, still_open, ext_all, superseded,
                           _get_all(inp, "oracle_kind"))

    # `out/` is emptied first, so its contents are exactly what this run produced.  A deliverable
    # left behind by a previous run is the worst kind of stale file: it is in the directory a
    # reader is told to read, it looks generated because it is, and nothing about it says which
    # run it belongs to.  Step 09's report goes in the same directory and is written after this,
    # so a run stopped at 08 correctly has no report — there is nothing yet to report on.
    os.makedirs(case.path(OUT_DIR), exist_ok=True)
    for f in os.listdir(case.path(OUT_DIR)):
        if os.path.isfile(case.path(OUT_DIR, f)):
            os.remove(case.path(OUT_DIR, f))
    files = {
        f"{OUT_DIR}/{D_LEAN}": decided_lean,
        f"{OUT_DIR}/{D_STANDALONE}": standalone,
        f"{OUT_DIR}/{D_PROSE}": decided_prose,
        f"{OUT_DIR}/{D_DIFF}": diff,
        f"{OUT_DIR}/{D_QUESTIONS}": questions,
        f"{OUT_DIR}/{D_PROPERTIES}": emit.properties_markdown(case.name, props),
        f"{OUT_DIR}/{D_HANDOFF}": json.dumps(handoff, indent=1) + "\n",
    }
    ch.materialise(files)

    problems = list(ref_errs) + cross_round + _unwritten_answers(ddoc, hunks_all)
    if missing:
        problems.append("decided fields not found in the `Cfg` structure block: "
                        + ", ".join(missing))
    attributed = _attribute_indeterminacy(decided_lean, standalone, still_open, el)
    if not el["ok"] and not attributed:
        # Prepended, not substituted.  An elaboration failure is the loudest problem in this step
        # and belongs at the top of the list, but it is not the only one, and a cross-round patch
        # overlap that disappeared behind a Lean error would be a repair silently lost.
        head = ([f"DecidedSpec.lean: {e}" for e in el.get("decided", {}).get("errors", [])]
                + [f"standalone: {e}" for e in el.get("standalone", {}).get("errors", [])]
                + [f"ADMITTED: {a}" for a in el.get("admitted", [])])
        if el.get("where"):
            head.insert(0, f"{el['where']}: {el['lean']}")
        problems = head + problems
    return {
        "ok": (bool(el["ok"]) or bool(attributed)) and not problems,
        "problems": problems,
        # Not "the step failed": a finding ABOUT the specification, carrying which of the two
        # shapes it is in `kind`.  See `_attribute_indeterminacy`.
        "elaboration_finding": attributed,
        "decided_spec_lean": decided_lean,
        "decided_spec_standalone_bytes": len(standalone),
        "partial_with_decision": partial_full,
        "cfg_defaults_rewritten": sorted(rewritten),
        "elaboration": {k: el.get(k) for k in ("decided", "standalone", "admitted")},
        "theorems": (el.get("decided", {}).get("axioms") or {}),
        "decided_prose": decided_prose,
        "decided_prose_sha256": cases.sha256(decided_prose),
        "patch_record": record,
        # The repairs a later round wrote over.  Invisible in the decided prose by construction —
        # the sentence carries one rewrite and does not say a round wrote another one first — and
        # a round that revised its own earlier answer is exactly what a reader of a multi-round
        # case wants to know about.
        "superseded_patches": superseded,
        "handoff": handoff,
        "diff": diff,
        "still_open": still_open,
        "questions_md": questions,
        "files": sorted(files),
    }


def _handoff_doc(case: cases.Case, rnd: int, decided_prose: str, ddoc: dict,
                 still_open: list[dict], ext_all: dict,
                 superseded: list[dict] | None = None,
                 oracle_kinds: list[str] | None = None) -> dict:
    """`out/HANDOFF.json` — leanSpec's record of what it produced, in machine-readable form.

    It is not an input contract.  `leanrtl` takes exactly two possible inputs — the original
    prose, or `spec.decided.txt` — and reads neither this file nor anything else in `out/`.  The
    two halves are independent: either runs alone, neither imports the other, and the only thing
    that crosses between them is a natural-language specification.

    So what is this for?  The same thing `REPORT.md` is for, minus the prose: a reader (or a
    later script of ours, or a table in a paper) asking what a run decided, on what basis, and
    what it left open should not have to parse markdown to find out.  `still_open` is the entry
    that matters most and is the one that would otherwise be invisible — the decided prose
    deliberately carries no note about it.

    `oracle_kinds` is guard 3 in the machine-readable half, and it lands on each ruling's
    `authority` rather than only in a header.  A ruling is the unit a script reads and a table
    quotes; a header a query does not select is a label that will eventually be dropped somewhere
    downstream, and the field it would have qualified says "the designer" in as many words.  Per
    round, because a run whose rounds had different authorities has rulings with different
    authorities, and one document-level string could only lie about that.
    """
    # By round, so a ruling gets the authority that answered ITS round.  Positional: `oracle_kinds`
    # is oldest-first as `_get_all` returns it, and round N is the Nth entry.  Absent -- every run
    # made before the flag existed -- it is the designer, which is what those runs were.
    by_round = {i: k for i, k in enumerate(oracle_kinds or [], 1)}
    said = {"designer": "the designer",
            "reference_rtl": "the benchmark's reference implementation, by simulation"}

    rulings = []
    # A ruling a later round overturned stays in the list and says so.  Dropping it would make
    # this document disagree with `QUESTIONS.md`, which records every query the run spent; leaving
    # it unmarked is worse, because the two rulings then read as concurrent and the reader has no
    # way to tell which one the prose next to them implements.  On `accu`, round 1's `grouping`
    # and round 2's `valid_out_single_cycle` rule opposite ways on the same sentence.
    #
    # Keyed by name and round together, because a name is not unique across a run: a violated
    # property that survives its own repair comes back under the same name in the next round, and
    # keyed by name alone the round that superseded reports itself as superseded.
    over = {(s.get("decision"), s.get("round")): s for s in (superseded or [])}
    for d in ddoc.get("decisions", []):
        if d.get("kind") == "model":
            continue
        q = (next((k for k in ext_all.get("choices", []) if k.get("name") == d.get("name")), None)
             or next((h for h in ext_all.get("holes", []) if h.get("name") == d.get("name")),
                     None) or {})
        spans = [c["span"] for c in ext_all.get("clauses", [])
                 if q.get("id") in (c.get("choice_id"), c.get("hole_id"))]
        s = over.get((d.get("name"), d.get("round")))
        rulings.append({"question": d.get("name"),
                        "kind": d.get("kind"),
                        "decision": d.get("resolved_to"),
                        "rejected": d.get("rejected", []),
                        "round": d.get("round"),
                        "in_force": s is None,
                        "overturned_by": (None if s is None else
                                          {"round": s.get("by_round"),
                                           "decision": s.get("by_decision")}),
                        "authority": ("the prose's own guarantee" if d.get("kind") == "property"
                                      else said.get(by_round.get(d.get("round")), "the designer")),
                        "why": d.get("evidence", ""),
                        "basis_clause_spans": spans})
    return {
        "decided_prose": D_PROSE,
        "decided_lean": D_LEAN,
        "standalone_lean": D_STANDALONE,
        "decided_prose_sha256": cases.sha256(decided_prose),
        "original_prose_sha256": cases.sha256(cases.prose(case)),
        "rulings": rulings,
        "still_open": [{"coordinate": o["field"], "name": o.get("name", o["field"]),
                        "why": o.get("why", ""), "note_for_spec": o.get("note_for_spec", "")}
                       for o in still_open],
        "source": {"case": case.name, "rounds": rnd,
                   "oracle": sorted(set(oracle_kinds or ["designer"])),
                   "oracle_by_round": by_round or {r: "designer" for r in range(1, rnd + 1)}},
        "note": "LeanSpec records the decided prose and relational Lean artifacts. A Stage 2 "
                "adapter must bind its executable reference to that relation with a checked "
                "handoff theorem; the MUX e2e profile does so for every finite trace. An entry "
                "under `still_open` is a coordinate the decided prose genuinely does not "
                "determine: an implementation has to choose, and the choice is an assumption "
                "rather than a reading of the specification.",
    }


def _theorem_span(src: str, name: str) -> tuple[int, int] | None:
    """The 1-based line range a theorem's failure can legitimately be reported in.

    A `decide` failure is reported at the *tactic* line, not at the `theorem` line, so a check
    that only looked at where the theorem is declared would attribute nothing.  The span runs
    from the declaration to the `#print axioms` that closes it, which is the block `gen_lean`
    emits as a unit.
    """
    start = end = None
    for i, line in enumerate(src.splitlines(), 1):
        if start is None and line.startswith(f"theorem {name} "):
            start = i
        elif start is not None and line.strip() == f"#print axioms {name}":
            end = i
            break
    return (start, end) if start and end else None


def _err_line(e: str) -> int | None:
    m = re.match(r"[^\s:]+:(\d+):\d+:", e.strip())
    return int(m.group(1)) if m else None


#: `gen_lean` writes this when the open coordinates have more combinations than it will write
#: determinacy theorems for.  Matched rather than re-derived, so the file and the finding cannot
#: disagree about how many there were: the emitter knows the product, this does not.  Its ABSENCE
#: is meaningful too — pinnings can also be missing because a coordinate has no enumerable axis,
#: and that is a different finding, so the marker is written only for the size decline.
_PINNINGS_DECLINED = re.compile(r"(?m)^-- PINNINGS-DECLINED: (\d+) > MAX_PINNINGS=(\d+)$")


def _attribute_indeterminacy(decided_lean: str, standalone: str, still_open: list[dict],
                             el: dict) -> dict | None:
    """Is this elaboration failure a finding about the specification, or a broken emission?

    `decided_determined` asks the decided specification to admit exactly one observation at every
    legal context.  It fails in two opposite ways, and neither of them is the emission breaking:

      * **too many.**  A coordinate is genuinely open — open because the designer could not or
        would not settle it, which the record is required to state with a reason.  The
        specification then admits more than one observation somewhere, and should.
      * **too few.**  Some legal context admits nothing at all, because the prose contradicts
        itself and the designer answered in favour of one side.  No implementation conforms, and
        no further round can change that until a sentence is amended.

    Reporting either as a failed step would say the emission broke when what actually happened is
    that the emission worked and reported a defect in the document — which is this framework's
    own headline result.

    So the failure is downgraded to a finding, but only on evidence, and the evidence is the
    theorems `gen_lean` writes beside `decided_determined` for exactly this purpose.  Every
    condition has to hold:

      * something is declared open, with a reason (too many), or the second pass found a legal
        context with an empty admit set (too few);
      * the corroborating theorems were emitted and every one of them PROVED — if the
        specification is undetermined even with the open coordinates pinned, the indeterminacy is
        somewhere else and this is a real fault;
      * `decided_determined` is the only theorem resting on `sorryAx`;
      * every Lean error, in both files, lies inside `decided_determined`'s own block.

    The last one is what stops this from becoming a blanket amnesty.  Without it a syntax error
    anywhere in the file would be waved through by a case that happens to have an open hole, and
    the step would report a specification it never successfully elaborated.

    The second condition has an exception, and it is a downgrade rather than a loosening: when
    the open coordinates have too many combinations for `gen_lean` to write a theorem per
    combination, there are no corroborating theorems to check and the finding says outright that
    nothing located the indeterminacy.  The other three conditions are untouched.  See the
    `undetermined_open_unattributed` branch.
    """
    if el.get("where"):
        return None                                  # Partial.lean itself failed: not this.
    axioms = (el.get("decided", {}) or {}).get("axioms") or {}
    admitted = set(el.get("admitted") or [])
    if admitted != {"decided_determined"}:
        return None
    pinned = re.findall(r"(?m)^#print axioms ((?:determined_given|never_ambiguous_given|"
                        r"dead_somewhere_given)_\w+)$", decided_lean)
    unsat = ["decided_admits_nothing", "decided_admits_nothing_legal"]
    if all(n in axioms for n in unsat):
        kind, must, extra = "no_model", unsat + pinned, {
            "why": ("`decided_determined` is admitted, not proved, and the sweep says why: there "
                    "is a legal context at which the decided specification admits NO observation. "
                    "`decided_admits_nothing` proves it at that context and "
                    "`decided_admits_nothing_legal` proves the context is legal. The prose "
                    "contradicts itself, and no implementation can satisfy it as written -- which "
                    "is a result about the specification, not a failure to finish the run."),
            # The two unsatisfiability theorems are what the report cites here, and only those:
            # a file emitted with an unsatisfiable context carries no pinning theorems today, and
            # if it ever did they would not be the evidence for THIS claim.
            "pinned_theorems": unsat,
        }
    elif still_open and pinned:
        dead = sorted(n[len("dead_somewhere_given_"):] for n in pinned
                      if n.startswith("dead_somewhere_given_"))
        live = [n for n in pinned if n.startswith("determined_given_")]
        # Which coordinates the pinnings could not enumerate, read out of the marker `gen_lean`
        # writes rather than re-derived here: one statement of the caveat, in one place, and the
        # file and the finding cannot drift apart about which coordinate it applies to.
        sampled = re.findall(r"(?m)^-- SAMPLED-PINNING: (\w+)$", decided_lean)
        kind, must = "undetermined_by_open_coordinate", pinned
        extra = {"why": (
            "`decided_determined` is admitted, not proved: the specification does not admit "
            "exactly one observation at every legal context, because a coordinate is declared "
            "open. Pinning the open coordinate(s) settles it at every point of their product, so "
            "the indeterminacy is located at those coordinates and nowhere else. The reason each "
            "one is open is in `out/REPORT.md`."
            + (f" {len(dead)} of the {len(live) + len(dead)} pinnings report the opposite failure "
               "rather than ambiguity: at those values the specification admits NOTHING at some "
               "legal context, so they are values the rest of the prose contradicts."
               if dead else "")
            + ((" One qualification, and it is not small: "
                + ", ".join(f"`{f}`" for f in sampled)
                + (" has" if len(sampled) == 1 else " have")
                + " a type with no finite enumeration, so the pinnings for it were taken from "
                  "the menu offered the designer rather than from its domain. Each theorem is "
                  "exactly true at the value it names, but together they cover the menu and not "
                  "the domain -- so the indeterminacy is located at that coordinate only as far "
                  "as the menu reaches, and a value never offered is one nothing here rules on.")
               if sampled else "")),
            "dead_pinnings": dead, "sampled_coordinates": sampled}
    elif still_open and (m := _PINNINGS_DECLINED.search(decided_lean)):
        # Open coordinates, and too many combinations of them to write a theorem per combination.
        # `accu` round 1 is the case that forced this: eight coordinates, 3072 pinnings, against
        # `MAX_PINNINGS=12` -- and with no pinning there was no evidence, so the branch above
        # declined, so the step FAILED, so `author.py` reported the phase rejected and never ran
        # round 2.  A round that settles little is the ordinary state of round 1; it is what
        # rounds 2 and 3 exist for.  Reporting it as a broken emission makes the multi-round loop
        # unreachable exactly when it is needed, which is the opposite of what the numbers mean.
        #
        # So the failure is downgraded here too -- but the CLAIM is downgraded with it, and that
        # is the whole of the difference from the branch above.  There, the location of the
        # indeterminacy is proved: pin the open coordinates and everything else is determined.
        # Here nothing of the kind was checked, and the finding says so in as many words.  What
        # is still true is the disjunction the file elaborated: `decided_determined` is the only
        # admitted theorem and every error is inside it, so the specification is undetermined
        # somewhere, and the record declares which coordinates are open and why.  Where it is
        # undetermined is asserted by the decision record and not by a theorem.
        #
        # The four structural conditions are unchanged and still checked below, so this is not
        # the blanket amnesty the docstring warns about: a syntax error anywhere else in the file,
        # or a second admitted theorem, still fails the step.
        kind, must = "undetermined_open_unattributed", []
        extra = {"why": (
            "`decided_determined` is admitted, not proved: the specification does not admit "
            "exactly one observation at every legal context, and the decision record declares "
            f"{len(still_open)} coordinate(s) open with a reason for each. Unlike the attributed "
            f"case, that is where the argument stops. Pinning the open coordinates would take "
            f"{m.group(1)} combinations, more than the {m.group(2)} this emitter will write "
            "theorems for, so NO theorem here locates the indeterminacy at those coordinates. "
            "That they are the only undetermined ones is the record's claim, not a checked one. "
            "A later round that closes some of them brings the product back under the limit and "
            "the claim back within reach."),
            "pinnings_declined": int(m.group(1)), "pinnings_limit": int(m.group(2))}
    else:
        return None
    if any(n not in axioms or n in admitted for n in must):
        return None
    for src, key in ((decided_lean, "decided"), (standalone, "standalone")):
        span = _theorem_span(src, "decided_determined")
        if not span:
            return None
        for e in (el.get(key, {}) or {}).get("errors", []):
            ln = _err_line(e)
            if ln is None or not (span[0] <= ln <= span[1]):
                return None
    return {"kind": kind, "open_fields": [o["field"] for o in still_open],
            "pinned_theorems": must, **extra}


def _decided_trailer(assignments: dict, still_open: list[dict]) -> str:
    L = ["",
         "-- ------------------------------------------------------------------ GENERATED",
         "-- Appended by leanspec/pipeline.py step 08 from the decision record.  Do not",
         "-- edit: every assignment below is a coordinate that was settled, and every field",
         "-- NOT listed is declared open in `authored/decisions.json` with a reason, which is",
         "-- quoted in `out/REPORT.md` rather than here.",
         ""]
    for o in still_open:
        L.append(f"--   open: {o['field']}")
    if still_open:
        L.append("")
    L.append("def decidedCfg : Cfg := " + emit._one_line_record("defaultCfg", assignments))
    return "\n".join(L) + "\n"


def _version_space(ext: dict, findings: list[dict], pins: list[dict],
                   decided: set[str]) -> dict:
    """How many readings of this specification are still standing, counted four ways.

    The four queries have always *reported* what they eliminated -- an equivalence that merged two
    readings, a fork whose reading admits nothing, a property that pins one. What nobody could
    read off the record is the number those eliminations are eliminations from, and that is the
    number which says whether a round made progress. Two rounds that each close one question look
    identical in the change log and are not the same result if the first went 48 -> 12 and the
    second went 4 -> 3.

    It matters more under the carried schedule than it did before. Re-formalizing against the
    decided prose gave the agent an incidental chance to notice a fork nobody asked about, so the
    space could grow between rounds without anything recording that it had; carrying round 1's
    frame forward means new coordinates enter only when someone puts them there. That is the
    intended trade -- it is what makes the loop cheap -- but a space that can now only shrink is a
    space whose size is the honest measure of what is left, and it should be written down rather
    than inferred from the fact that questions stopped being generated.

    Four numbers, because three of the transitions are different KINDS of elimination and
    conflating them would hide which one is doing the work:

        before          the product of every open coordinate's declared readings
        after_formal    less dead readings, merged equivalents, and property-pinned forks --
                        everything Lean settled without spending a question
        after_feedback  less what this round's answers closed
        quotient        `|V/≈|`, further collapsing coordinates no legal context can observe

    `quotient` is the plan document's §12 condition, and it is reported rather than enforced. It
    reaches 1 on a settled case, but it also reaches 1 on a case blocked by
    `unobservable_coordinate` -- the coordinate is collapsed *because* nothing distinguishes its
    values -- and those two are not the same outcome. `blocked_by` remains the termination rule;
    this is the size of the thing it is terminating on.

    A hole whose menu stage 1 could not enumerate has no factor to contribute and is not silently
    counted as 1: it is returned in `undeclared`, because a product that quietly omits a
    coordinate reads exactly like a product over a smaller space.
    """
    dead: set[tuple[str, str]] = set()
    merged: dict[str, set[str]] = {}
    unobservable: set[str] = set()
    for f in findings:
        if f.get("query") == "difference":
            for side in ("a", "b"):
                if f.get(f"{side}_dead"):
                    dead.add((f["choice"], f[side]))
        elif f.get("query") == "equivalence" and f.get("equivalent"):
            # `b` folds into `a`; counting both ends would remove the pair rather than the
            # duplicate, and a three-way equivalence would then take the fork below one reading.
            merged.setdefault(f["choice"], set()).add(f["b"])
        elif f.get("query") == "hole" and f.get("free") is False:
            unobservable.add(f["hole"])
    pinned = {p["name"] for p in pins if p.get("kind") == "choice"}

    coords, undeclared = [], []
    for k in ext.get("choices", []):
        tags = [c["tag"] for c in k.get("candidates", [])]
        after = [t for t in tags
                 if (k["name"], t) not in dead and t not in merged.get(k["name"], ())]
        coords.append({"coordinate": f"c_{k['name']}", "kind": "choice", "declared": len(tags),
                       "after_formal": 1 if k["name"] in pinned else max(1, len(after)),
                       "decided": f"c_{k['name']}" in pinned or f"c_{k['name']}" in decided,
                       "observable": True})
    for h in ext.get("holes", []):
        tags = [c["tag"] for c in h.get("candidates", [])]
        if not tags:
            undeclared.append(f"h_{h['name']}")
            continue
        coords.append({"coordinate": f"h_{h['name']}", "kind": "hole", "declared": len(tags),
                       "after_formal": len(tags),
                       "decided": f"h_{h['name']}" in decided,
                       "observable": h["name"] not in unobservable})

    def prod(vals) -> int:
        n = 1
        for v in vals:
            n *= v
        return n

    return {
        "before": prod(c["declared"] for c in coords),
        "after_formal": prod(c["after_formal"] for c in coords),
        "after_feedback": prod(1 if c["decided"] else c["after_formal"] for c in coords),
        "quotient": prod(1 if c["decided"] or not c["observable"] else c["after_formal"]
                         for c in coords),
        "coordinates": coords,
        # Named, not counted.  See the docstring: an unenumerated menu is an unknown factor, and
        # folding it in as 1 would report a space smaller than the one the run is searching.
        "undeclared": undeclared,
    }


def step_convergence(case: cases.Case, inp: dict, rnd: int) -> dict:
    """09 — re-diagnose what was decided, and say whether it is settled.

    The round's terminal accounting.  Everything before it produced a specification; this asks
    the specification the same four questions step 03 asked, over the decided configuration, and
    then asks the one question that only makes sense at the end: does `admits decidedCfg` admit
    *exactly one* observation at every legal context, proved by `decide +kernel` with the axioms
    read rather than the exit code.

    There is no agreement sweep here and there is no reference quoted at the end.  There is no
    reference.  The claim this pipeline makes is not "the decided specification matches an
    implementation someone else wrote" — that would be a measurement of a benchmark — it is
    "every place this document was open was found, put to its author, and closed or declared
    open with a reason, and what came out is determined".  That claim is checked here.

    When it does not hold, `blocked_by` says which of four shapes the case is in, and each asks
    for a different repair:

        spec_contradiction        two sentences disagree; the decided reading has no model
        violated_property         the prose states a guarantee its own definitions break; the
                                  designer said which sentence was wrong and step 07 wrote the
                                  repair, and only the next round's stage 4 can confirm it
        designer_indifferent      the question is real, observable, and the author accepts both
        unobservable_coordinate   the coordinate is free and nothing at any legal context can
                                  distinguish its values, so it can be narrowed but never asked

    `REPORT.md` is written here rather than in step 08 because its summary quotes this verdict.
    """
    _chain(case).materialise({
        "extraction.json": json.dumps(_get(inp, "extraction_decided"), indent=1),
        "sandbox/Partial.lean": _get(inp, "partial_with_decision"),
        "probe.json": json.dumps(_get(inp, "probe"), indent=1),
    })
    # Read out of step 04's record rather than re-derived here.  `refine.verify` re-runs the four
    # queries and none of them is a property check, so a violation is invisible to it; passing the
    # list is what stops a round that found one from reporting itself converged.
    ver = refine.verify(case, _get(inp, "violated_properties", []))
    # Every round's resolutions, tagged, for the same reason step 08 accumulates: the report's
    # change log covers every decision the run took, and a decision taken in round 1 has to be
    # able to find the answer round 1 got.  Read out of this round's document alone, an early
    # decision would match no resolution and would be reported without the caveat its option set
    # earned.
    res = [dict(x, round=r) for r, d in _numbered(inp, "resolution")
           for x in d.get("resolutions", [])]
    # The size of the space the verdict above is a verdict about.  Built from this round's own
    # documents -- the extraction it posed, the findings Lean returned, the forks a property
    # retired, the coordinates the answers closed -- so it measures this round rather than
    # re-deriving anything.
    vspace = _version_space(_get(inp, "extraction"), _get(inp, "findings", []),
                            _get(inp, "property_pins", []),
                            {d["cfg_field"] for d in _get(inp, "decisions_doc").get("decisions", [])
                             if d.get("cfg_field")})
    # Who answered, over the WHOLE run and not this round.  `_get` would return the latest, and a
    # case whose round 1 was put to a designer and whose round 2 was answered from the reference
    # is a case whose specification is part-authored and part-measured -- the one shape where a
    # single label is a lie, and the shape a `_get` would have printed.  `_get_all` collects every
    # round's, and `_measured_banner` fires if any of them was not the designer.
    kinds = sorted(set(_get_all(inp, "oracle_kind")) or {oracle.KIND_DESIGNER})
    ora = {"kind": (kinds[0] if len(kinds) == 1 else "mixed"), "kinds": kinds,
           "reference": sorted({f for r in _get_all(inp, "reference") for f in (r or [])})}
    md = emit.report_markdown(case.name, _get(inp, "decisions_doc"), _get(inp, "patch_record"),
                              _get(inp, "still_open"), _get(inp, "diff"), ver, res,
                              _get(inp, "elaboration_finding", None),
                              _get(inp, "properties", None),
                              _get(inp, "superseded_patches", None), vspace, ora)
    _chain(case).materialise({f"{OUT_DIR}/{D_REPORT}": md})
    return {
        "ok": bool(ver.get("converged")),
        "problems": ([] if ver.get("converged")
                     else [f"not converged: {ver.get('blocked_by') or 'open questions remain'}"]),
        "verification": ver,
        "converged": ver.get("converged"),
        "blocked_by": ver.get("blocked_by"),
        "version_space": vspace,
        "oracle": ora,
        "determinism_certificate": ver.get("determinism_certificate"),
        "designer_indifferent": ver.get("designer_indifferent", []),
        "report_md": md,
    }



# --------------------------------------------------------------------------- the runner

STEPS: list[steps_mod.Step] = [
    steps_mod.Step(0, "input", "The natural-language specification this run is about",
                   step_input),
    steps_mod.Step(1, "extraction", "Semantic extraction, with byte-exact provenance",
                   step_extraction, authored=("extraction.json",)),
    steps_mod.Step(2, "formalization", "The partial semantics, elaborated",
                   step_formalization, authored=("Partial.lean", "probe.json")),
    steps_mod.Step(3, "diagnosis", "The four queries, with certificates", step_diagnosis),
    steps_mod.Step(4, "properties", "What the prose claims about itself, checked",
                   step_properties),
    steps_mod.Step(5, "witnesses", "The cheapest separating context per finding", step_witnesses),
    steps_mod.Step(6, "resolution", "The designer, asked once per witness", step_resolution,
                   sealed=False,
                   why_open="this is the step that spends the queries; a witness and a recorded "
                            "prediction exist for every one of them, and nothing before it may "
                            "reach the designer"),
    steps_mod.Step(7, "decision", "What the answers fix, and what they leave open", step_decision,
                   authored=("decisions.json",)),
    steps_mod.Step(8, "output", "The decided Lean specification, the decided prose, the questions",
                   step_output),
    steps_mod.Step(9, "convergence", "Re-diagnosis of the decided reading, and the report",
                   step_convergence),
]

BY_NAME = {s.name: s for s in STEPS}
BY_N = {s.n: s for s in STEPS}
LAST = max(BY_N)


def _chain(case: cases.Case) -> steps_mod.Chain:
    """This case's chain.  Cheap to build, so it is built where it is needed rather than passed
    through every step signature: a `Chain` is a table plus four paths, and holding one in a
    module global would make two cases in one process share a directory."""
    return steps_mod.Chain(ctx=case, dir=case.dir, name=case.name, steps=STEPS,
                           handoff=HANDOFF, root=paths.DATA)


def step_path(case: cases.Case, st: steps_mod.Step, rnd: int) -> str:
    return _chain(case).step_path(st, rnd)


def existing_rounds(case: cases.Case) -> list[int]:
    return _chain(case).existing_rounds()


def run_step(case: cases.Case, st: steps_mod.Step, rnd: int = 1) -> dict:
    return _chain(case).run_step(st, rnd)


def run(case: cases.Case, first: int = 0, last: int = LAST, rnd: int = 1,
        say=lambda _: None) -> list[dict]:
    """Steps `first`..`last` of round `rnd`, stopping at the first that does not succeed.

    The round is snapshotted into `rounds/roundN/` on the way through, and *when* matters.
    `refine.snapshot` copies the live working files, and step 07 overwrites the live extraction
    with the decided one — so a snapshot taken at the end of the run would record the state the
    round produced, where what every other reader wants is the state the round *worked on*:
    `rounds/round1/` is what the case looked like before any question was answered.  So it is
    taken after step 06, which is the last step before the decisions land, and a run that starts
    at step 07 does not take one at all — there is nothing left of that round to freeze that step
    07 has not already changed.
    """
    ch = _chain(case)
    done, snapped = [], False
    for st in sorted(STEPS, key=lambda s: s.n):
        if not (first <= st.n <= last):
            continue
        doc = ch.run_step(st, rnd)
        done.append(doc)
        mark = "ok" if doc["ok"] else "FAILED"
        say(f"  {st.stem:<22} {mark}"
            + ("" if doc["ok"] else "  " + "; ".join(map(str, doc["problems"][:3]))))
        if st.n == 6:
            refine.snapshot(case, rnd)
            snapped = True
        if not doc["ok"]:
            break
    if not snapped and first <= 6:
        refine.snapshot(case, rnd)
    index(case, rnd)
    rounds_index(case)
    return done


def index(case: cases.Case, rnd: int) -> str:
    """`steps/roundN/INDEX.md` — the chain, as one table, regenerated from the files themselves."""
    ch = _chain(case)
    L = [f"# {case.name} — round {rnd}, step by step", "",
         "Each step reads exactly one file (the previous step's output) and writes exactly one "
         "(its own). A step's output contains its input verbatim under `inherited`, so the last "
         "file is the whole run and any file is the whole run up to that point.", ""]
    if rnd > 1:
        L += [f"This round continues round {rnd - 1}: step 00 reads that round's step "
              f"{HANDOFF:02d}, so the chain here reaches back through every earlier round. It "
              f"reads step {HANDOFF:02d} and not step {LAST:02d} because step {LAST:02d} is that "
              f"round's terminal accounting — it re-diagnoses what step {HANDOFF:02d} produced, "
              f"and nothing downstream needs its verdict except the decision to run this round "
              f"at all.", ""]
    L += ["| step | output | reads | seal | ok | authored input |",
          "|---|---|---|---|---|---|"]
    rel = ch.round_dir(STEPS_DIR, rnd)
    for st in STEPS:
        p = ch.step_path(st, rnd)
        if not os.path.isfile(p):
            L.append(f"| {st.n:02d} {st.name} | *(not run)* | | | | |")
            continue
        with open(p) as f:
            d = json.load(f)
        reads = (d.get("input") or {}).get("file", "—")
        auth = [f"`{a}`" for a in st.authored]
        n_glob = len(d.get("authored_inputs") or {}) - len(st.authored)
        auth += [f"{n_glob} × `{pat}`" for pat in st.authored_glob if n_glob > 0]
        L.append(f"| {st.n:02d} {st.name} | `{rel}/{st.stem}.json` | `{reads}` | "
                 f"{'sealed' if st.sealed else '**open**'} | "
                 f"{'✓' if d.get('ok') else '✗'} | "
                 f"{', '.join(auth) or '—'} |")
    L += ["", "## What each step is", ""]
    for st in STEPS:
        L.append(f"* **{st.n:02d} {st.name}** — {st.title}."
                 + ("" if st.sealed else f"  Open: {st.why_open}."))
    L += ["", "## Deliverables", "",
          f"Written by step {HANDOFF:02d} of every round into `{OUT_DIR}/`, which therefore holds "
          f"the *latest* round's. The rounds before it are not lost — each one's step documents "
          f"are here, and `rounds/` keeps its artifacts.", "",
          f"* `{OUT_DIR}/{D_PROSE}` — the decided natural-language specification: the original "
          f"with one byte-exact replacement per decision and nothing else. This is the file the "
          f"implementation half takes, and it carries no annotation of ours.",
          f"* `{OUT_DIR}/{D_DIFF}` — unified diff, original → decided.",
          f"* `{OUT_DIR}/{D_LEAN}` — the decided formal specification, with the proof that it is "
          f"determined and one refutation per reading that was ruled out. No evidence and no "
          f"narration: it is the specification and its proofs.",
          f"* `{OUT_DIR}/{D_STANDALONE}` — the same, with the library and the case's "
          f"`Partial.lean` spliced in, so it elaborates with no import path.",
          f"* `{OUT_DIR}/{D_QUESTIONS}` — every question the prose left open, across every round: "
          f"where it comes from, the readings, the cheapest input that tells them apart drawn as "
          f"a waveform, and what the designer answered.",
          f"* `{OUT_DIR}/{D_PROPERTIES}` — every claim the prose makes about itself, and what "
          f"checking it returned: entailed or violated, vacuous or live, and whether it pins a "
          f"reading the designer therefore never had to be asked about.",
          f"* `{OUT_DIR}/{D_HANDOFF}` — the same run in machine-readable form: every ruling with "
          f"its basis, and every coordinate left open. Not read by the implementation half.",
          f"* `{OUT_DIR}/{D_REPORT}` — the argument: what changed and on whose authority, what "
          f"the prose claims about itself, what is still unspecified and why. Written by step "
          f"{LAST:02d}.", ""]
    md = "\n".join(L)
    with open(case.path(rel, "INDEX.md"), "w") as f:
        f.write(md)
    return md


def rounds_index(case: cases.Case) -> str:
    """`steps/INDEX.md` — one row per round, and where the deliverables came from."""
    ch = _chain(case)
    rs = ch.existing_rounds()
    n = len(STEPS)
    L = [f"# {case.name} — the run, round by round", "",
         f"A round is one pass of the {n} steps. Round N's step 00 reads round N−1's step "
         f"{HANDOFF:02d}, so the last document of the last round is the whole run: every question "
         f"ever asked is reachable from it through `inherited`.", "",
         "| round | steps run | converged | blocked by | index |",
         "|---|---|---|---|---|"]
    for r in rs:
        n_ok = sum(1 for st in STEPS if os.path.isfile(ch.step_path(st, r)))
        conv, blocked = "—", ""
        p = ch.step_path(BY_N[LAST], r)
        if os.path.isfile(p):
            with open(p) as f:
                d = json.load(f)
            conv = "✓" if (d.get("produced") or {}).get("converged") else "✗"
            blocked = (d.get("produced") or {}).get("blocked_by") or ""
        L.append(f"| {r} | {n_ok}/{n} | {conv} | {'`' + blocked + '`' if blocked else '—'} | "
                 f"[`round{r}/INDEX.md`](round{r}/INDEX.md) |")
    L += ["", f"The deliverables in `{OUT_DIR}/` are round {rs[-1] if rs else '—'}'s.", ""]
    md = "\n".join(L)
    with open(case.path(STEPS_DIR, "INDEX.md"), "w") as f:
        f.write(md)
    return md


def backup(case: cases.Case, suffix: str = ".bak") -> str | None:
    """Copy the case directory aside before a re-run.  Returns the path, or None if it exists."""
    dst = case.dir + suffix
    if os.path.exists(dst):
        return None
    shutil.copytree(case.dir, dst)
    return dst


# ------------------------------------------------------------------------- the scaffold

# What "defines `decidedCfg`" means, for the step 02 gate and for `_strip_decided_cfg` below.
#
# It was a bare `"decidedCfg" in src` until the second `accu` sweep, which did exactly the right
# thing — wrote no `decidedCfg`, and said so in a doc comment: "`decidedCfg` is *not* written here
# in any pass".  The substring matched the sentence and the gate answered "Partial.lean defines
# `decidedCfg`", which was false.  There is no way for an author to act on that: the artifact was
# already correct, the message named a declaration that was not there, and the only edit that
# satisfies it is deleting the comment that proves the author understood the rule.
#
# A mention is not a definition.  The two are told apart the way every other reader here tells
# them apart — by anchoring at the start of a line — which is also what `_strip_decided_cfg` was
# already doing, so the gate and the stripper now ask the same question rather than two.
_DEFINES_DECIDED_CFG = re.compile(r"(?m)^\s*(?:noncomputable\s+)?(?:def|abbrev)\s+decidedCfg\b")


def _strip_decided_cfg(src: str) -> str:
    """Drop a hand-written `decidedCfg`, which step 02 forbids.

    The pipeline derives `decidedCfg` in step 08 from the decision record, and step 02 rejects a
    `Partial.lean` that already defines one: a hand-written one is a value in the specification
    that no query justified, at the exact coordinate the whole arrangement exists to keep honest.

    Dropping it is only safe because the definition is dead — nothing else in an authored
    `Partial.lean` may refer to it, since it is written last.  When something does — a file whose
    author wrote a theorem ABOUT the decided configuration — the definition is left in place and
    step 02 raises it, because deleting a definition that has a use site would turn a rejection
    into an elaboration error several steps later.
    """
    lines = src.splitlines(keepends=True)
    start = next((i for i, ln in enumerate(lines) if ln.startswith("def decidedCfg")), None)
    if start is None:
        return src
    end = start + 1
    while end < len(lines) and (not lines[end].strip() or lines[end][:1].isspace()):
        end += 1                                     # the definition's continuation lines
    while end > start + 1 and not lines[end - 1].strip():
        end -= 1                                     # ... but not the blank line after it
    # The doc comment immediately above goes too, or the file keeps a `/-- ... -/` attached to
    # nothing, which does not elaborate.
    if start and lines[start - 1].rstrip().endswith("-/"):
        opener = next((i for i in range(start - 1, -1, -1) if lines[i].lstrip().startswith("/--")),
                      None)
        if opener is not None:
            start = opener
    rest = "".join(lines[:start] + lines[end:])
    if re.search(r"\bdecidedCfg\b", rest):
        return src                                   # it has a use site: not this command's call
    return re.sub(r"\n\n\n+", "\n\n", rest)


def scaffold(case: cases.Case, rnd: int, force: bool = False) -> tuple[list[str], list[str]]:
    """Pre-fill `authored/round{rnd}/` from what the case already ran.

    Everything but `decisions.json` is a copy of what `rounds/round{rnd}/` holds, which is what
    makes re-running a round a transcription rather than a re-authoring: the round runs again
    against the same inputs.

    `decisions.json` is written half-empty on purpose.  What can be derived is derived — which
    witness was resolved, to what, which readings were eliminated, which coordinate of `Cfg` the
    question names, and the byte-exact quote of every clause the question rests on.  What cannot
    be is left blank: `evidence` is the argument that the prose was open and what the designer
    showed, `consequence` is what the answer settles, and `replacement` is the sentence that says
    it.  Those are readings, and a scaffold that guessed them would be the agent answering its
    own question in the one file the agent is supposed to write.

    It transcribes resolutions and nothing else.  A reading the designer did not keep cannot
    appear here, because the only source for `resolved_to` is the resolution's own `kept` list —
    and step 07 re-derives that check from the step chain, independently of this command, so a
    scaffold that got it wrong is caught rather than trusted.
    """
    ch = _chain(case)
    made, kept = [], []
    src = case.path("rounds", f"round{rnd}")
    if not os.path.isdir(src):
        return [], []
    dst = case.path(ch.round_dir(AUTHORED, rnd))
    os.makedirs(dst, exist_ok=True)

    for name in ("extraction.json", "Partial.lean", "probe.json"):
        s, d = os.path.join(src, name), os.path.join(dst, name)
        if not os.path.isfile(s):
            continue
        if os.path.exists(d) and not force:
            kept.append(os.path.relpath(d, case.dir))
            continue
        with open(s, errors="replace") as f:
            body = f.read()
        if name == "Partial.lean":
            body = _strip_decided_cfg(body)
        with open(d, "w") as f:
            f.write(body)
        made.append(os.path.relpath(d, case.dir))

    d = os.path.join(dst, "decisions.json")
    if os.path.exists(d) and not force:
        kept.append(os.path.relpath(d, case.dir))
        return made, kept

    step6 = ch.step_path(BY_N[6], rnd)
    if os.path.isfile(step6):
        with open(step6, errors="replace") as f:
            res = (_get(json.load(f), "resolution") or {})
    else:
        with open(os.path.join(src, "resolution.json"), errors="replace") as f:
            res = json.load(f)
    with open(os.path.join(dst, "extraction.json"), errors="replace") as f:
        ext = json.load(f)
    with open(os.path.join(dst, "Partial.lean"), errors="replace") as f:
        partial = f.read()
    fields = emit.cfg_fields(partial, schema.cfg_field_names(partial, ext))
    with open(d, "w") as f:
        json.dump(_skeleton(case, rnd, res.get("resolutions", []), ext, fields,
                            cases.prose(case)), f, indent=1)
    made.append(os.path.relpath(d, case.dir))
    return made, kept


def _skeleton(case: cases.Case, rnd: int, resolutions: list[dict], ext: dict,
              fields: list[dict], prose: str) -> dict:
    """The derivable half of a `decisions.json`."""
    known = {f["field"]: f for f in fields}
    questions = ([("choice", k) for k in ext.get("choices", [])]
                 + [("hole", h) for h in ext.get("holes", [])])
    decided = {d.get("cfg_field") for d in ext.get("decisions", []) if d.get("cfg_field")}

    decisions, open_fields = [], []
    for kind, q in questions:
        name = q["name"]
        field = ("c_" if kind == "choice" else "h_") + name
        # Every resolution that speaks about this question, decisive first: one question can be
        # posed by several witnesses (a three-reading fork is three pairwise comparisons), and
        # they do not all have to come back decisive.  `_speaks_about` says why attribution is by
        # witness id and not by tag.
        mine = [r for r in resolutions if _speaks_about(r, name)]
        firm = [r for r in mine
                if r.get("outcome") in ("decided", "pinned", "pinned_undeclared")]
        if not firm:
            open_fields.append({
                "cfg_field": field if field in known else "",
                "name": name,
                "why": "",
                "note_for_spec": "",
            })
            continue
        r = firm[0]
        kept = sorted(set().union(*[_tags(x.get("kept"), name) for x in firm])
                      or set(r.get("pinned_to") or []))
        gone = sorted(set().union(*[_tags(x.get("eliminated"), name) for x in firm]))
        tag = kept[0] if len(kept) == 1 else ""
        decisions.append({
            "kind": kind,
            "name": name,
            "round": rnd,
            "witness": r.get("witness"),
            "resolved_to": tag,
            "rejected": gone,
            "cfg_field": field if field in known else "",
            "cfg_value": _cfg_value(known.get(field), tag),
            "evidence": "",
            "consequence": "",
            "patch": [{"op": "replace", "clause": c["id"], "span": list(c["span"]),
                       "original": prose[c["span"][0]:c["span"][1]], "replacement": ""}
                      for c in ext.get("clauses", [])
                      if q.get("id") in (c.get("choice_id"), c.get("hole_id"))],
        })

    # A coordinate this round neither decides nor found a question for is one an earlier round
    # already settled — it is listed in the extraction's decision record — or one nobody has
    # accounted for yet, and the second is the case worth flagging in the file rather than in a
    # comment nobody reads.
    for f in fields:
        if f["field"] in decided or f["field"] in {d["cfg_field"] for d in decisions}:
            continue
        if any(o["cfg_field"] == f["field"] for o in open_fields):
            continue
        open_fields.append({"cfg_field": f["field"], "name": f["field"].split("_", 1)[-1],
                            "why": "", "note_for_spec": ""})

    return {
        "case": case.name,
        "round": rnd,
        "note": (f"Step 07, round {rnd}.  Scaffolded: every field below except `evidence`, "
                 f"`consequence` and each hunk's `replacement` was transcribed from "
                 f"steps/round{rnd}/06_resolution.json and the round's extraction.  Those three "
                 f"are the reading and are written by hand.  A `remaining_open` entry with an "
                 f"empty `why` is a refusal, not a placeholder: step 07 rejects it."),
        "decisions": decisions,
        "remaining_open": open_fields,
    }


def _cfg_value(field: dict | None, tag: str) -> str:
    """A guess at the Lean term for `tag` in `field`, or "" when there is nothing to guess from.

    The designer's vocabulary and Lean's are not the same one.  A hole over `Option Bool` comes
    back pinned to `"0"`, and the term is `some false`; a fork over `Kout_phase` comes back as
    `same_edge` and the term is `Kout_phase.same_edge`.  Both mappings are mechanical, and both
    are still checked: step 08 elaborates what is written here, so a wrong guess is a Lean error
    rather than a wrong specification.

    The mapping is `emit._lean_reading`'s, called rather than restated, because step 08 uses that
    one to write the *refutation* of each rejected reading.  Two copies of it would let the
    scaffold suggest a spelling the emitter would not have chosen, and the disagreement would
    surface as a Lean error in a file neither of them wrote.
    """
    if not field or not tag:
        return ""
    value, err = emit._lean_reading(field["type"], tag)
    return "" if err else value


# ------------------------------------------------- the pre-decision state, for other readers
#
# `report.py` and the audit both need the artifacts as they stood *before* any question was
# answered, and both find them in `rounds/round1/`.  A pipeline case has those too — `run`
# snapshots every round — but it also has the step chain, which is the more exact record: the
# state those two readers want is simply the output of the step that produced it, in round 1.
# Without this they would read the live files instead — which, after step 09, are the *decided*
# ones — and a converged case would report that it found nothing (because convergence is what
# "finds nothing" means) and the leak scan would report the framework working as a violation of
# itself, since a decision quotes the designer's answer as its evidence.

STEP_ARTIFACTS: dict[str, tuple[int, str]] = {
    "extraction.json": (1, "extraction"),
    "probe.json":      (2, "probe"),
    "Partial.lean":    (2, "partial_lean"),
    "diagnosis.json":  (3, "diagnosis"),
    "properties.json": (4, "properties"),
    "witnesses.json":  (5, "witnesses_doc"),
    "resolution.json": (6, "resolution"),
}


def undecided(case: cases.Case, name: str):
    """The named artifact as the step that produced it left it, or None if this is not a
    pipeline case.

    Round 1, always: "before any question was answered" is a statement about the whole run, not
    about the latest round.  A four-round case's round 4 extraction has three answered questions
    already removed from it, and reading that one here would report those three as never found.
    """
    if name not in STEP_ARTIFACTS:
        return None
    n, key = STEP_ARTIFACTS[name]
    p = step_path(case, BY_N[n], 1)
    if not os.path.isfile(p):
        return None
    with open(p) as f:
        doc = json.load(f)
    return (doc.get("produced") or {}).get(key)


def undecided_text(case: cases.Case, name: str) -> str | None:
    v = undecided(case, name)
    if v is None:
        return None
    return v if isinstance(v, str) else json.dumps(v, indent=1)


def n_steps(case: cases.Case) -> int:
    """Step documents written across every round."""
    ch = _chain(case)
    return sum(len([f for f in os.listdir(case.path(ch.round_dir(STEPS_DIR, r)))
                    if f.endswith(".json")])
               for r in ch.existing_rounds())
