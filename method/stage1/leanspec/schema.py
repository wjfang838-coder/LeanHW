#!/usr/bin/env python3
"""Stage 1 and 2 artifacts, and the checks that make them more than prose in JSON.

## `extraction.json` (stage 1)

Semantic clauses with **provenance as byte offsets**, not as a re-typed quotation.  Every
clause carries `span: [start, end]` and `text`, and the validator requires

    prose[start:end] == text

byte for byte.  A quote that has been silently normalised -- whitespace collapsed, a Unicode
minus turned into ASCII, a table cell reflowed -- fails here, where it is one line to fix,
rather than downstream where it becomes an argument about what the specification said.

Clause `status` is one of:

    fixed     the prose determines this
    choice    the prose supports more than one reading; `choice_id` names the fork
    hole      required behaviour the prose never states; `hole_id` names it

A property is not a fourth value.  `choice` and `hole` are places the specification declines to
say something, and `status` records exactly that: what is undetermined about the clause.  A
property is a place the document says something *without defining it* -- "ack follows req within
two cycles", "exactly one output is asserted" -- and the clause stating it is usually perfectly
determinate, so `fixed` is the truth about its status.  Folding the property itself into the
clause list would lose the one thing that makes it interesting: it can contradict the definitions
while both halves remain individually satisfiable, and neither the difference query nor the
deadness query can see that.  So `properties` carries them as their own list, `propcheck` asks the
four questions of `LeanSpec.Property` about each, and a property's provenance runs property ->
clauses through `basis`.  That direction is many-to-many and it is the only one that fits; see the
note on `STATUSES` for what it cost to learn.

`ports` is the interface as the *prose* gives it.  It is recorded separately because an
interface disagreement has no common port to compare on and so can never be a trace question
-- the same tier `harness/clarify.py` calls INTERFACE.  Here it becomes a checkable claim:
`oracle.py` reports a probe whose port names are absent from the reference as
`port_missing`, which is an interface-conformance finding rather than a silent zero.

An optional `decisions` list is stage 5's record: which fork or hole was closed, to what, on
the strength of which witness and which observed behaviour.  A fork may not appear in both
`choices` and `decisions` -- open and answered at once -- and a decision without a witness is
rejected, because that is the agent answering its own question from its own reading.

An optional `deferred` list is the coverage the projection gives up: a question stage 1 raised
that stage 2 chose not to model, with the reason.  It is reported separately from the findings
and never counted as one.

### A hole's option set, and whether it is the whole domain

Every question this framework asks is multiple choice: the oracle is handed N pinned
configurations and reports which ones the reference's observation is consistent with.  It is
never handed a blank.  For a fork the options come from `candidates`, and `check_partial`
cross-checks them against the constructors of `inductive K<name>`, so the option set is closed
by construction -- there is no third constructor to be surprised by.

A hole's options live in `cfgPins_<name>` in `Partial.lean`, and for an inductively-typed hole
the same argument applies.  For a numerically-typed one -- `h_reset_data : Option Nat` over a
4-bit register -- the list is whatever stage 2 chose to write, and *that is not the same claim*.
Two survivors out of a sample still prove the coordinate is free: whatever else is in the
domain, these two are, and they disagree.  One survivor out of a sample proves nothing, because
the value the reference actually holds may never have been offered.

    A sampled option set can prove FREEDOM.  It cannot prove a PIN.

So a hole may declare, optionally:

    "candidates": [{"tag": "0000", "reading": "..."}, ...]   the options, as a fork carries them
    "domain": {"size": 16, "closed": true, "why": "..."}     how many values the coordinate has

`closed` must equal `size == len(candidates)`, and `check_partial` cross-checks the tags against
`cfgPins_<name>`.  When a hole declares nothing the domain is *undeclared* rather than assumed
either way, and a pin taken on it is carried forward with that caveat attached rather than
silently trusted.  When it declares a sample, `refine._classify` returns `pinned_sampled` and
step 6 refuses to close the question on it.

When a domain is too large to enumerate, the honest fallback is not a smaller menu: it is to
*measure*.  Drive the context, read the port, put the observed value on the menu, and then run
the ordinary pinning against it.  Nothing in the corpus needs that yet, so it is the documented
rule and not a code path.

## `probe.json` (stage 2)

How a context becomes stimulus: the clock, the reset discipline, the driven inputs and the
watched outputs, in the names the *prose* uses.  It is the specification's commitment about
its own interface, written before the reference is opened.
"""
from __future__ import annotations

import hashlib
import json
import os
import re
import shutil
import tempfile

CLAUSE_KINDS = ("interface", "parameter", "state", "transition", "timing", "reset",
                "priority", "concurrency", "protocol", "assumption", "corner")

# `status` answers one question about a clause: what is UNDETERMINED about it.  Fixed, or forked,
# or silent.  A property is not an answer to that question -- a clause that states a guarantee is
# usually perfectly determinate -- so `property` is deliberately not a fourth value here.  It was,
# for one iteration, and the round-trip that came with it (every property claimed by some clause's
# `property_id`, by analogy with choices and holes) could not be satisfied by a correct document:
# a clause routinely underwrites several properties and `property_id` holds one.  Three authoring
# attempts in a row wrote the right thing and were rejected for it.  A property's provenance is
# its own `basis`, which points at the clauses, and that direction is the only one that fits.
STATUSES = ("fixed", "choice", "hole")

# What a stated guarantee is *about*.  Recorded for the report and for nothing else -- no check
# branches on it -- because a reader scanning a case wants to know whether the specification
# constrains its outputs, its protocol or its timing, and the four checks give the same answer
# whichever it is.
PROPERTY_KINDS = ("invariant", "guarantee", "exclusion", "bound", "protocol", "liveness")


def _err(errs: list, where: str, msg: str) -> None:
    errs.append(f"{where}: {msg}")


UNDECLARED = "undeclared"
CLOSED = "closed"
SAMPLED = "sampled"


def domain_of(hole: dict) -> dict:
    """What a hole's option set claims to be: the whole domain, a sample of it, or unstated.

    Returned for every hole, declared or not, so that callers branch on one shape.  `size` is the
    number of values the coordinate can take and `offered` the number on the menu; for an
    undeclared hole both may be `None`, and the only honest thing to say downstream is that
    nobody wrote it down.

    The distinction is not bookkeeping.  `status == SAMPLED` is the case where exactly one
    survivor is *not* an answer, because the value the reference holds may never have been
    offered -- see the module docstring.
    """
    cands = hole.get("candidates") or []
    dom = hole.get("domain") or {}
    size, offered = dom.get("size"), (len(cands) or None)
    if not dom:
        return {"status": UNDECLARED, "size": None, "offered": offered, "why": ""}
    closed = bool(dom.get("closed"))
    return {"status": CLOSED if closed else SAMPLED, "size": size, "offered": offered,
            "why": dom.get("why", "")}


def _check_domain(hole: dict) -> list[str]:
    """The declaration, against itself.  Absent is fine; inconsistent is not."""
    dom, cands = hole.get("domain"), hole.get("candidates") or []
    errs = []
    if hole.get("candidates") is not None:
        if not isinstance(cands, list) or not cands:
            return ["`candidates` must be a non-empty list when present"]
        tags = [c.get("tag") for c in cands]
        if any(not isinstance(t, str) or not t for t in tags):
            errs.append("every candidate needs a non-empty string `tag`")
        if len(set(tags)) != len(tags):
            errs.append(f"duplicate candidate tags {sorted(t for t in set(tags) if tags.count(t) > 1)}")
    if dom is None:
        return errs
    if not isinstance(dom, dict) or "size" not in dom or "closed" not in dom:
        return errs + ["`domain` needs `size` and `closed`"]
    size = dom["size"]
    if not isinstance(size, int) or size < 1:
        return errs + [f"domain size {size!r} must be a positive integer"]
    if not cands:
        errs.append("`domain` is declared but no `candidates` are listed, so there is nothing "
                    "for the size to be a claim about")
    elif bool(dom["closed"]) != (size == len(cands)):
        # The one inconsistency worth rejecting: a menu that calls itself the whole domain while
        # its own declared size says otherwise.  Either number may be the mistake, and which one
        # it is decides whether a pin taken here is sound, so it is not guessable.
        errs.append(f"`closed` is {bool(dom['closed'])} but {len(cands)} candidate(s) are listed "
                    f"against a domain of {size}")
    return errs


def validate_extraction(doc: dict, prose: str) -> list[str]:
    errs: list[str] = []
    # `source` rather than a benchmark name and a key.  A case is one specification, named by
    # whoever started the run; where the prose came from is a string for a reader, not an index
    # into a dataset this repository does not have.
    for k in ("design", "source", "clauses", "choices", "holes", "properties", "ports"):
        if k not in doc:
            _err(errs, "extraction", f"missing top-level key {k!r}")
    if errs:
        return errs

    ids = set()
    for i, c in enumerate(doc["clauses"]):
        w = f"clause[{i}]"
        for k in ("id", "kind", "text", "span", "reading", "status"):
            if k not in c:
                _err(errs, w, f"missing {k!r}")
        if errs and w in errs[-1]:
            continue
        if c["id"] in ids:
            _err(errs, w, f"duplicate id {c['id']!r}")
        ids.add(c["id"])
        if c["kind"] not in CLAUSE_KINDS:
            _err(errs, w, f"kind {c['kind']!r} not in {CLAUSE_KINDS}")
        if c["status"] not in STATUSES:
            _err(errs, w, f"status {c['status']!r} not in {STATUSES}")
        s, e = c["span"]
        if not (0 <= s < e <= len(prose)):
            _err(errs, w, f"span {c['span']} outside the spec (0..{len(prose)})")
        elif prose[s:e] != c["text"]:
            _err(errs, w, "span does not quote the spec byte for byte; "
                          f"prose[{s}:{e}]={prose[s:e]!r} but text={c['text'][:80]!r}")
        if c["status"] == "choice" and not c.get("choice_id"):
            _err(errs, w, "status 'choice' needs a choice_id")
        if c["status"] == "hole" and not c.get("hole_id"):
            _err(errs, w, "status 'hole' needs a hole_id")

    seen_choice = set()
    for i, k in enumerate(doc["choices"]):
        w = f"choice[{i}]"
        for f in ("id", "name", "candidates", "default", "basis"):
            if f not in k:
                _err(errs, w, f"missing {f!r}")
        if any(w in e for e in errs[-1:]):
            continue
        if k["id"] in seen_choice:
            _err(errs, w, f"duplicate choice id {k['id']!r}")
        seen_choice.add(k["id"])
        if not re.fullmatch(r"[a-z][A-Za-z0-9_]*", k["name"]):
            _err(errs, w, f"name {k['name']!r} must be a lowercase Lean-safe identifier")
        tags = [c["tag"] for c in k["candidates"]]
        if len(tags) < 2:
            _err(errs, w, "a fork has at least two candidate readings")
        if len(set(tags)) != len(tags):
            _err(errs, w, f"duplicate candidate tags {tags}")
        if k["default"] not in tags:
            _err(errs, w, f"default {k['default']!r} is not one of {tags}")
        for c in k["candidates"]:
            if not c.get("reading"):
                _err(errs, w, f"candidate {c.get('tag')!r} has no reading")
        for b in ([k["basis"]] if isinstance(k["basis"], str) else k["basis"]):
            if b not in ids:
                _err(errs, w, f"basis {b!r} is not a clause id")

    seen_hole = set()
    for i, h in enumerate(doc["holes"]):
        w = f"hole[{i}]"
        for f in ("id", "name", "missing", "why_required"):
            if f not in h:
                _err(errs, w, f"missing {f!r}")
        if any(w in e for e in errs[-1:]):
            continue
        if h["id"] in seen_hole:
            _err(errs, w, f"duplicate hole id {h['id']!r}")
        seen_hole.add(h["id"])
        if not re.fullmatch(r"[a-z][A-Za-z0-9_]*", h["name"]):
            _err(errs, w, f"name {h['name']!r} must be a lowercase Lean-safe identifier")
        errs += [f"{w}: {e}" for e in _check_domain(h)]

    # A stated guarantee.  Two fields carry the whole weight of this section.
    #
    # `expressible` is the one that must never be quietly true.  A property is checked as an
    # ordinary predicate over the enumerated `Ctx`/`Obs` frame, and a clause that does not fit
    # that frame -- one quantifying over unbounded time, one about a signal outside the
    # projection -- has to be recorded as inexpressible WITH ITS REASON rather than approximated
    # into something that does fit.  An approximation that passes reports a guarantee as checked
    # when what was checked was a different claim, and nothing downstream can tell the two apart.
    #
    # `basis` is the ordinary provenance requirement: a property nobody wrote is a property this
    # pipeline invented, and inventing guarantees is the failure mode the whole method is built
    # against.  It points property -> clauses, many to many, and that is the ONLY direction
    # checked.  See the note on `STATUSES` for the version that also demanded the reverse.
    seen_prop = set()
    for i, p in enumerate(doc["properties"]):
        w = f"property[{i}]"
        for f in ("id", "name", "statement", "kind", "basis", "expressible"):
            if f not in p:
                _err(errs, w, f"missing {f!r}")
        if any(w in e for e in errs[-1:]):
            continue
        if p["id"] in seen_prop:
            _err(errs, w, f"duplicate property id {p['id']!r}")
        seen_prop.add(p["id"])
        if not re.fullmatch(r"[a-z][A-Za-z0-9_]*", p["name"]):
            _err(errs, w, f"name {p['name']!r} must be a lowercase Lean-safe identifier")
        if p["kind"] not in PROPERTY_KINDS:
            _err(errs, w, f"kind {p['kind']!r} not in {PROPERTY_KINDS}")
        # Either spelling.  The prompt asks for `why`; `why_inexpressible` is what an earlier
        # version of this check demanded, and a document that says why in either field has said
        # why.  Rejecting the prompt's own spelling is the checker disagreeing with the ask.
        if not p["expressible"] and not (p.get("why") or p.get("why_inexpressible")):
            _err(errs, w, "a property declared inexpressible must say why -- an unexplained "
                          "omission is indistinguishable from a property nobody got to")
        for b in ([p["basis"]] if isinstance(p["basis"], str) else p["basis"]):
            if b not in ids:
                _err(errs, w, f"basis {b!r} is not a clause id")

    # Every fork and hole a clause points at must exist, and vice versa: a `choice_id` with no
    # entry is a question that will never be asked, and an entry no clause points at is a
    # question with no provenance.
    used_c = {c["choice_id"] for c in doc["clauses"] if c.get("choice_id")}
    used_h = {c["hole_id"] for c in doc["clauses"] if c.get("hole_id")}
    for m in sorted(used_c - seen_choice):
        _err(errs, "clauses", f"choice_id {m!r} has no entry in `choices`")
    for m in sorted(seen_choice - used_c):
        _err(errs, "choices", f"{m!r} is claimed by no clause -- it has no provenance")
    for m in sorted(used_h - seen_hole):
        _err(errs, "clauses", f"hole_id {m!r} has no entry in `holes`")
    for m in sorted(seen_hole - used_h):
        _err(errs, "holes", f"{m!r} is claimed by no clause -- it has no provenance")

    for i, p in enumerate(doc["ports"]):
        for f in ("name", "dir", "width"):
            if f not in p:
                _err(errs, f"port[{i}]", f"missing {f!r}")
        if p.get("dir") not in ("in", "out"):
            _err(errs, f"port[{i}]", f"dir {p.get('dir')!r} is not in|out")

    # `decisions` is stage 5's record, and it is optional only because round 1 has none.  What
    # it must not be is a place to write down an answer while the question is still open: a
    # decided fork that is still listed in `choices` would keep being re-asked, and a decision
    # with no witness is the agent filling a hole from its own reading -- the exact move this
    # framework exists to prevent.
    #
    # `model` is the third kind, and it records the round in which a query came back `outside`
    # -- the reference did something the projection could not express -- together with what was
    # changed about the projection in response.  A widened domain that is not recorded reads,
    # one round later, as a question answered on the first try; recording it is what keeps the
    # query count honest.  It is not a resolution, so it does not have to name an open fork.
    #
    # `property` is the fourth and the only one that costs no query: step 04 proved that exactly
    # one reading of a fork satisfies a guarantee the prose states about itself, so the document
    # answered its own question and step 05 retired it instead of asking.  It was missing from
    # this list, which made it a kind the author is instructed to write and the checker refuses
    # -- `author.py` names it, `pipeline.py`'s step 07 validates it against the certified pin,
    # and only the decided extraction had never heard of it.  A run that earned a property pin
    # would have produced a decision no edit could make acceptable: dropping it loses a settled
    # fork, keeping it fails here.  It closes a `choice`, so it carries the same obligation as
    # one -- a fork recorded as decided and still listed in `choices` gets asked again next
    # round, with a query, having already been answered for free.
    for i, d in enumerate(doc.get("decisions", [])):
        w = f"decision[{i}]"
        for f in ("kind", "name", "resolved_to", "witness", "evidence", "round"):
            if f not in d:
                _err(errs, w, f"missing {f!r}")
        # `violation` is the fifth and it closes nothing.  The others say which reading of an open
        # question was chosen; this one says which of two sentences the author disowned, after
        # stage 4 proved they cannot both hold.  Its `name` is the property's, not a fork's, so it
        # is deliberately absent from the two "decided and still open" checks below -- a property
        # is not an entry in `choices` or `holes`, and looking for it in either would be looking in
        # the wrong document.  What holds it to account is step 07, which requires a decision here
        # for every violation the designer adjudicated, and step 09, which refuses to converge a
        # round that found one.
        if d.get("kind") not in ("choice", "hole", "model", "property", "violation"):
            _err(errs, w, f"kind {d.get('kind')!r} is not choice|hole|model|property|violation")
        if (d.get("kind") in ("choice", "property")
                and d.get("name") in {k["name"] for k in doc["choices"]}):
            _err(errs, w, f"{d['name']!r} is recorded as decided and still open in `choices`")
        if d.get("kind") == "hole" and d.get("name") in {h["name"] for h in doc["holes"]}:
            _err(errs, w, f"{d['name']!r} is recorded as decided and still open in `holes`")

    # `deferred` is the other half of "the agent must not silently invent missing behaviour":
    # it must not silently *drop* a question either.  A projection is a choice about what to
    # look at, and every projection excludes something -- here, the questions stage 1 raised
    # that stage 2 decided not to model, each with the reason.  They are not counted as
    # detected, which is the point: a deferred question is a known gap in the coverage, and one
    # that is written down can be argued with.
    for i, d in enumerate(doc.get("deferred", [])):
        w = f"deferred[{i}]"
        for f in ("name", "from_clauses", "question", "why_deferred"):
            if f not in d:
                _err(errs, w, f"missing {f!r}")
        if any(w in e for e in errs[-1:]):
            continue
        if d["name"] in {k["name"] for k in doc["choices"]} | {h["name"] for h in doc["holes"]}:
            _err(errs, w, f"{d['name']!r} is deferred and also modelled -- it is one or "
                          "the other")
        for b in d["from_clauses"]:
            if b not in ids:
                _err(errs, w, f"from_clauses {b!r} is not a clause id")
    return errs


def validate_probe(probe: dict, extraction: dict) -> list[str]:
    errs: list[str] = []
    for f in ("clock", "reset", "inputs", "outputs", "sample"):
        if f not in probe:
            _err(errs, "probe", f"missing {f!r}")
    if errs:
        return errs
    if probe["sample"] not in ("after_edge", "before_edge"):
        _err(errs, "probe", "the defined sampling conventions are 'after_edge' and "
                            "'before_edge' (see oracle.py: inputs are driven a half period "
                            "before the edge, and outputs are read after it or before it)")
    names = {p["name"]: p for p in extraction["ports"]}
    for s in probe["inputs"]:
        if s not in names:
            _err(errs, "probe", f"driven signal {s!r} is not a port in extraction.json")
        elif names[s]["dir"] != "in":
            _err(errs, "probe", f"driven signal {s!r} is declared an output")
    for s in probe["outputs"]:
        if s not in names:
            _err(errs, "probe", f"watched signal {s!r} is not a port in extraction.json")
        elif names[s]["dir"] != "out":
            _err(errs, "probe", f"watched signal {s!r} is declared an input")
    if probe["clock"] and probe["clock"] not in names:
        _err(errs, "probe", f"clock {probe['clock']!r} is not a port in extraction.json")
    r = probe["reset"]
    if r and (r.get("name") not in names or "active" not in r or "cycles" not in r):
        _err(errs, "probe", "reset needs {name, active, cycles} and a name that is a port")
    return errs


#: Every declaration a case file owes, with the type it owes it at.
#:
#: The type is half of the obligation and for a long time only the *name* was checked.  What
#: that cost is recorded in `docs/design/SPECCHECK.md`: seven properties written as
#: `Cfg → Ctx → Obs → Bool` passed a check whose error message names `Property Ctx Obs`, because
#: the regex matched `def prop_<name>` and stopped there.  Tightening that regex to also read the
#: type would have been a worse version of the elaborator, so the elaborator does it instead —
#: `example : <type> := <name>` is exactly the question, asked of the thing that can answer it.
#:
#: `Case` and `Property` are written qualified so an obligation does not depend on the case file
#: having `open LeanSpec` still in scope where the obligations are appended.
REQUIRED_DEFS: list[tuple[str, str]] = [
    ("Cfg", "Type"),
    ("Ctx", "Type"),
    ("Obs", "Type"),
    ("ctxUniverse", "List Ctx"),
    ("obsUniverse", "List Obs"),
    ("ctxCost", "Ctx → Nat"),
    ("legal", "Ctx → Bool"),
    ("admits", "Cfg → Ctx → Obs → Bool"),
    ("ctxJson", "Ctx → String"),
    ("ctxLean", "Ctx → String"),
    ("obsJson", "Obs → String"),
    ("defaultCfg", "Cfg"),
    ("case", "LeanSpec.Case Ctx Obs"),
]


def lean_obligations(extraction: dict) -> dict:
    """What `Partial.lean` must contain, derived from stage 1 rather than restated by hand."""
    return {
        "cfg_fields": ([f"c_{k['name']}" for k in extraction["choices"]]
                       + [f"h_{h['name']}" for h in extraction["holes"]]),
        # Fields that MAY be present without being required: the coordinates this run has already
        # decided.  Two shapes are legal for a decided coordinate and the difference is who wrote
        # the round.  An authored round re-reads the decided prose, finds the clause `fixed`, and
        # writes no field at all.  A round carried forward by `author.carried_documents` narrows
        # round 1's frame instead, so the field survives with its answer pinned as the default.
        #
        # Neither is the defect the reverse check below is looking for.  That check's own sentence
        # says what the defect is -- "an assignment no query justified at a coordinate no answer
        # names" -- and a field the decision record names is a coordinate an answer names, by
        # construction.  What is still refused is a `c_`/`h_` field that is neither declared open
        # nor recorded as decided, which is the invented coordinate.
        "decided_fields": [d["cfg_field"] for d in extraction.get("decisions", [])
                           if d.get("cfg_field")],
        "choice_enums": {f"K{k['name']}": [c["tag"] for c in k["candidates"]]
                         for k in extraction["choices"]},
        # Only the holes that declared an option set.  A hole that declared none imposes no
        # obligation here -- the omission is reported downstream as `undeclared`, not as a
        # missing declaration, because stage 1 is allowed not to know the domain.
        "hole_pins": {h["name"]: [c["tag"] for c in h["candidates"]]
                      for h in extraction["holes"] if h.get("candidates")},
        # Only the expressible ones.  A property recorded as inexpressible is a declared gap in
        # the coverage, and demanding a Lean definition for it would push stage 2 into writing
        # the approximation the declaration exists to refuse.
        "properties": [p["name"] for p in extraction.get("properties", []) if p["expressible"]],
        "defs": [d for d, _ in REQUIRED_DEFS],
    }


# ------------------------------------------------------- asking Lean what the file declares
#
# Three questions a regex cannot answer and the environment answers exactly: which fields a
# structure has, which constructors an inductive has, and which constants a definition's *value*
# mentions.  All three are set comparisons, and the direction that used to be missing is the one
# that matters most -- a regex can see that a declared field is absent, but not that an
# UNDECLARED one is present, and an undeclared coordinate is the defect `emit.cfg_fields` drew a
# phantom `domain` from.
#
# Printed with `IO.println` rather than `logInfo` so the line arrives at column zero and
# `common/leanrun.py`'s finding parser reads it the same way it reads every emitter in
# `LeanSpec/Core.lean`.  A `logInfo` would arrive as `<file>:<line>:<col>: info: LEANSPEC:{...}`
# and be silently dropped.
_INTROSPECT = '''
/-! ### leanSpec obligations.  Generated by `leanspec/schema.py`; not part of `Partial.lean`. -/

namespace LeanSpecCheck
open Lean

def line (q of : String) (names : List String) : String :=
  "LEANSPEC:" ++ (Json.mkObj [("query", Json.str q), ("of", Json.str of),
                              ("names", toJson names)]).compress

open Lean Elab Command in
elab "#leanspec_fields " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  IO.println (line "fields" n.toString
    ((getStructureFields (← getEnv) n).toList.map (·.toString)))

open Lean Elab Command in
elab "#leanspec_ctors " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let ci ← liftCoreM <| getConstInfoInduct n
  IO.println (line "ctors" n.toString
    (ci.ctors.map (fun c => (c.replacePrefix n Name.anonymous).toString)))

open Lean Elab Command in
elab "#leanspec_refs " id:ident : command => do
  let n ← liftCoreM <| realizeGlobalConstNoOverload id
  let some ci := (← getEnv).find? n | throwError "no such constant"
  IO.println (line "refs" n.toString
    ((ci.value?.getD (mkConst n)).getUsedConstants.toList.map (·.toString)))

end LeanSpecCheck
'''

#: Lean's own diagnostics, in the shape `common/leanrun.py` insists on: `<file>:<line>:<col>:`.
#: Matched here rather than reused from there because this needs the line number and the body,
#: and a diagnostic's body runs to the start of the next one.  The optional `(...)` is Lean
#: 4.29's message tag — `error(lean.unknownIdentifier):` — and a pattern without it sees a file
#: whose every failure is tagged as a file with no failures.
_DIAG = re.compile(r"(?m)^[^\s:]*:(\d+):\d+: (error|warning|information)(?:\([^)\n]*\))?: ")

#: An error whose cause is that the name is not there at all, as opposed to being there at the
#: wrong type.  The distinction is the difference between two error messages a stage-2 author has
#: to act on differently: write the declaration, or fix the one you wrote.  Matched against the
#: lower-cased diagnostic, so both Lean's tag (`lean.unknownIdentifier`) and its prose
#: (`Unknown identifier`) count.
_ABSENT = ("unknownidentifier", "unknownconstant", "unknown identifier", "unknown constant",
           "unknown declaration", "unknown namespace", "no such constant")


def _errors_by_line(log: str) -> list[tuple[int, str]]:
    """`(line, whole diagnostic)` for every error in a Lean log, in order.

    A diagnostic's body runs to the next diagnostic, and the findings the obligations print
    arrive on stdout in between — so they are dropped here rather than becoming the tail of
    whatever error happened to precede them.
    """
    out, hits = [], list(_DIAG.finditer(log))
    for i, m in enumerate(hits):
        if m.group(2) != "error":
            continue
        end = hits[i + 1].start() if i + 1 < len(hits) else len(log)
        body = [l for l in log[m.start():end].splitlines() if not l.startswith("LEANSPEC:")]
        out.append((int(m.group(1)), "\n".join(body).strip()))
    return out


def _obligation_blocks(ob: dict) -> list[dict]:
    """One Lean fragment per obligation, in the order `check_partial` has always reported them.

    `section` is the half of `check_partial`'s verdict the fragment belongs to: `"struct"` for
    everything an early pass owns, `"props"` for what pass 8 writes.  That split is what lets
    `property_problems` be a real subset of `check_partial` rather than a second implementation
    of it, which is the invariant `author._owner_of` compares on.
    """
    blocks: list[dict] = []

    for name, ty in REQUIRED_DEFS:
        blocks.append({"lean": f"example : {ty} := {name}", "section": "struct",
                       "absent": f"Partial.lean: no declaration of `{name}`",
                       "wrong": f"Partial.lean: `{name}` is not `{ty}`"})

    # The field set, both directions.  `Cfg` missing is already reported above, so an error here
    # is not reported twice -- `skip` says the fragment's own failure is somebody else's finding.
    blocks.append({"lean": "#leanspec_fields Cfg", "section": "struct", "skip": True})

    for enum in ob["choice_enums"]:
        blocks.append({"lean": f"#leanspec_ctors {enum}", "section": "struct",
                       "absent": f"Partial.lean: no `inductive {enum}` for that choice",
                       "wrong": f"Partial.lean: `{enum}` is not an inductive type"})

    # A hole that declared an option set gets the same treatment: the menu the oracle will be
    # offered is `cfgPins_<name>`, and if it disagrees with the one stage 1 wrote down then the
    # question rendered in QUESTIONS.md is not the question that was asked.  A hole with no
    # `cfgPins_` at all is skipped, exactly as it was when this was a regex -- and unlike the
    # regex, a menu built by `.map` over a value list is now read rather than skipped, because
    # `#eval` runs it instead of looking at it.
    for name in ob["hole_pins"]:
        blocks.append({"lean": f"#eval IO.println (LeanSpecCheck.line \"pins\" \"{name}\" "
                               f"((cfgPins_{name}).map (·.1)))",
                       "section": "struct", "skip": True})

    # Each expressible property needs a `Property Ctx Obs` to be checked as, and the list has to
    # hold all of them.  The second half matters as much as the first: `allEntailed` over a list
    # that quietly omits a property returns `true` for it, so a definition written and then left
    # out of `properties` is a guarantee that reads as checked and never was.
    for name in ob["properties"]:
        blocks.append({"lean": f"example : LeanSpec.Property Ctx Obs := prop_{name}",
                       "section": "props",
                       "absent": f"Partial.lean: no `def prop_{name} : Property Ctx Obs` for "
                                 f"that property",
                       "wrong": f"Partial.lean: `prop_{name}` is not a `Property Ctx Obs`"})
    if ob["properties"]:
        blocks.append({
            "lean": "example : List (LeanSpec.Property Ctx Obs) := properties",
            "section": "props",
            "absent": "Partial.lean: no `def properties : List (Property Ctx Obs)`",
            "wrong": "Partial.lean: `properties` is not a `List (Property Ctx Obs)`"})
        blocks.append({"lean": "#leanspec_refs properties", "section": "props", "skip": True})
    return blocks


def _assemble(src: str, ob: dict) -> tuple[str, list[dict]]:
    """The case file plus its obligations, and where each obligation starts.

    `import Lean` is prepended rather than spliced in beside `import LeanSpec`, so the case file
    is carried through byte for byte and every line of it moves by exactly one.  Stripping its
    import block instead would mean a regex deciding which lines of a Lean file are imports,
    which is the job this function exists to stop doing.
    """
    text = "import Lean\n" + src
    if not text.endswith("\n"):
        text += "\n"
    text += "\n" + _INTROSPECT
    out = []
    for b in _obligation_blocks(ob):
        start = text.count("\n") + 1
        text += "\n" + b["lean"].rstrip() + "\n"
        out.append(dict(b, start=start, end=text.count("\n")))
    return text, out


def _elaborate(text: str) -> dict:
    """Elaborate the assembled file in a directory of its own, and take nothing away but the log.

    A temporary directory rather than the case's: this is a question about a string, several of
    its callers hold no case at all, and a file left in a case directory is a file some later
    step can read.
    """
    from leanspec import leanrun                       # local: `leanrun` refuses without a build
    d = tempfile.mkdtemp(prefix="leanspec-obligations-")
    try:
        p = os.path.join(d, "Obligations.lean")
        with open(p, "w") as f:
            f.write(text)
        return leanrun.run(p, cwd=d)
    finally:
        shutil.rmtree(d, ignore_errors=True)


#: The last few reports, keyed on the file and the obligations.  `author._owner_of` asks for
#: `check_partial` and `property_problems` over the same bytes one line apart, and step 02 asks
#: for the first of them over bytes `_pass_gate` has already elaborated; without this each of
#: those is a separate `lean` process.
_CACHE: dict[tuple[str, str], dict] = {}
_CACHE_KEEP = 8


def _report(src: str, extraction: dict) -> dict:
    """Every obligation's verdict, from one elaboration.

    Returns `{"struct", "props", "broken", "fields"}`.  `broken` is non-empty when the case file
    itself did not elaborate, in which case the obligations were asked of an environment with
    holes in it and the answer is reported as an answer about the file, not about an obligation.
    """
    ob = lean_obligations(extraction)
    key = (hashlib.sha256(src.encode()).hexdigest(),
           hashlib.sha256(json.dumps(ob, sort_keys=True).encode()).hexdigest())
    if key in _CACHE:
        return _CACHE[key]

    text, blocks = _assemble(src, ob)
    res = _elaborate(text)
    found = {(f.get("query"), f.get("of")): f.get("names", []) for f in res["findings"]}
    diags = _errors_by_line(res["log"])
    first = blocks[0]["start"] if blocks else text.count("\n") + 1

    struct: list[str] = []
    props: list[str] = []
    # An error above the first obligation is the case file's own, reported with the line number
    # it has in `Partial.lean` -- one less than in the file that was elaborated.
    broken = [" ".join(_DIAG.sub(lambda m: f"Partial.lean:{int(m.group(1)) - 1}: error: ",
                                 d, count=1).split())[:300] for ln, d in diags if ln < first]

    for b in blocks:
        hit = [d for ln, d in diags if b["start"] <= ln <= b["end"]]
        if not hit or b.get("skip"):
            continue
        # The location is dropped: it points into the assembled file, which is a temporary
        # nobody has and whose line numbers mean nothing to the author being asked to repair.
        why = " ".join(_DIAG.sub("", hit[0], count=1).split())
        msg = (b["absent"] if any(w in hit[0].lower() for w in _ABSENT)
               else f"{b['wrong']} — {why[:240]}")
        (props if b["section"] == "props" else struct).append(msg)

    fields = found.get(("fields", "Cfg"), [])
    for f in ob["cfg_fields"]:
        if f not in fields:
            struct.append(f"Partial.lean: `Cfg` has no field `{f}`")
    # The other direction, which no regex ever asked: a `c_` or `h_` field stage 1 never
    # declared is a fork or a hole that stage 2 invented, and `decidedCfg` has to be total over
    # it -- so it would be an assignment no query justified at a coordinate no answer names.
    # A field the decision record names is exempt: see `decided_fields` in `lean_obligations`.
    allowed = set(ob["cfg_fields"]) | set(ob.get("decided_fields") or ())
    for f in fields:
        if f.startswith(("c_", "h_")) and f not in allowed:
            struct.append(f"Partial.lean: `Cfg` has a field `{f}` that extraction.json does not "
                          f"declare, so no decision could ever name it")
    # And the gap between the two readers.  `emit.cfg_fields` needs each coordinate's type and
    # default *as written*, which only the source has, so it stays a parser -- but a coordinate
    # it cannot read is one `derive` would then never assign, and a decided specification with a
    # silently-open coordinate in it is the failure this whole check exists upstream of.
    from leanspec import emit                                  # local: `emit` imports `schema`
    read = {f["field"] for f in emit.cfg_fields(src)}
    for f in fields:
        if f not in read:
            struct.append(f"Partial.lean: `Cfg`'s field `{f}` cannot be read back from the "
                          f"source — its declaration is not `<name> : <type> := <default>` on a "
                          f"line of its own, so `decidedCfg` could not be made total over it")

    for enum, tags in ob["choice_enums"].items():
        ctors = found.get(("ctors", enum))
        if ctors is not None and sorted(ctors) != sorted(tags):
            struct.append(f"Partial.lean: `{enum}` has {ctors}, extraction.json says {tags}")

    for name, tags in ob["hole_pins"].items():
        labels = found.get(("pins", name))
        if labels is not None and sorted(labels) != sorted(tags):
            struct.append(f"Partial.lean: `cfgPins_{name}` offers {labels}, extraction.json "
                          f"lists {tags}")

    if ob["properties"]:
        refs = found.get(("refs", "properties"))
        if refs is not None:
            for miss in sorted(n for n in ob["properties"] if f"prop_{n}" not in refs):
                props.append(f"Partial.lean: `prop_{miss}` is defined but not in `properties`, "
                             f"so nothing would ever check it")
        props.extend(_bare_entries_of(src))

    out = {"struct": struct, "props": props, "broken": broken, "fields": fields}
    if len(_CACHE) >= _CACHE_KEEP:
        _CACHE.pop(next(iter(_CACHE)))
    _CACHE[key] = out
    return out


def check_partial(src: str, extraction: dict) -> list[str]:
    """Structural check of the agent's `Partial.lean` against the obligations above.

    Not syntactic any more, and that is the whole change.  This used to be five regexes reading a
    generated Lean file back, which is a parser for Lean written in Python and kept honest by
    nobody; `docs/design/SPECCHECK.md` lists what leaked through it.  Now the obligations are
    *appended to the file as Lean* and the elaborator decides — so "the field is missing" and
    "the field is there at the wrong type" are the same question asked once, and the answer is
    the one the queries in stage 3 will act on rather than a second opinion about it.

    It still does not judge whether the semantics are right; the four queries do that.  It
    catches the failure where a choice recorded in stage 1 quietly has no field in stage 2, which
    would make the fork *vanish* rather than be answered — and now also the reverse, a
    coordinate stage 2 invented that stage 1 never declared.
    """
    r = _report(src, extraction)
    # The elaboration failure goes only in this half, never in `property_problems`.  That is what
    # makes `author._owner_of` refuse to attribute a rejection to pass 8 when the file does not
    # elaborate: the two lists differ, so it drops the whole record, which is the conservative
    # answer it says every uncertainty resolves to.
    return r["struct"] + r["props"] + [
        f"Partial.lean does not elaborate, so its obligations were checked against an "
        f"environment with holes in it: {b}" for b in r["broken"][:4]]


def property_problems(src: str, extraction: dict) -> list[str]:
    """The `properties` obligations on their own.

    Split out of `check_partial` so that the one pass which writes this section can be asked
    about it *while it is still the pass in progress*.  Step 02 remains the verdict on
    `Partial.lean` — that is not moved here — but a defect confined to pass 8 does not need to
    cost the other eight: a step 02 rejection drops the whole pass record on purpose, and
    re-authoring a 1,900-line file from nothing takes about a hundred minutes.

    Only what pass 8 itself writes is asked.  Everything else in `check_partial` is about a
    section some earlier pass owns, and asking those here would turn a pass gate into the
    phase's judgement, which is exactly the thing `_pass_gate`'s docstring says it is not.
    """
    return _report(src, extraction)["props"]


def cfg_field_names(src: str, extraction: dict) -> list[str]:
    """`Cfg`'s fields in declaration order, as the elaborated environment has them.

    The authority for `emit.cfg_fields`, which needs each field's *type and default* as written
    and so has to read the source however carefully.  What it must not do is invent a field, and
    this is the list that stops it.
    """
    return list(_report(src, extraction)["fields"])


#: The body of `def properties`, for the one obligation the elaborator cannot be asked.
_PROPERTIES_BODY = re.compile(r"(?ms)^\s*def\s+properties\b.*?:=(.*?)(?=^\S|\Z)")


def _bare_entries_of(src: str) -> list[str]:
    """The shape check on `properties`, which stays syntactic because it is about syntax.

    Everything else in this module moved to the elaborator, and this did not move with it for a
    reason worth stating rather than leaving as an omission: `asProperty "p" ante prop_p` and
    `prop_p` have the *same type*, so there is no Lean question whose answer distinguishes them.
    What is wrong with the first is a fact about the term that was written, and the term is what
    a regex can see.  See `_bare_entries` for what it cost to find that out.
    """
    m = _PROPERTIES_BODY.search(src)
    return _bare_entries(m.group(1)) if m else []


def _list_body(body: str) -> str | None:
    """The text between the outermost `[` and its match, or `None` if there is no list."""
    i = body.find("[")
    if i < 0:
        return None
    depth = 0
    for j in range(i, len(body)):
        if body[j] == "[":
            depth += 1
        elif body[j] == "]":
            depth -= 1
            if depth == 0:
                return body[i + 1:j]
    return None


#: An entry of `properties` that is not one of the `prop_` declarations.
_BARE = re.compile(r"^prop_\w+$")


def _bare_entries(body: str) -> list[str]:
    """Every entry of `properties` must be a `prop_<name>` and nothing else.

    The list is what `emitPropertyPin` ranges over, and its whole premise is stated in
    `Property.lean`: the claim is held FIXED while the reading varies, so `survivors` measures the
    readings rather than the claim.  `Property.holds` is `Ctx → Obs → Bool` with no `Cfg` for
    exactly that reason.

    An entry that is an *application* rather than an identifier is how that premise gets broken
    without breaking the type.  The first complete `accu` run wrote

        def asProperty (name : String) (ante : Ctx → Bool) (p : Cfg → Ctx → Obs → Bool) :=
          { name := name, ante := ante,
            holds := fun c o => propReadings.any (fun cfg => p cfg c o) }

    and listed seven `asProperty "..." (fun ...) prop_<name>` entries.  Every earlier check passes:
    each `def prop_<name>` exists, each name appears in the list, and the result really is a
    `Property Ctx Obs`.  What it does is close the fork inside the claim — `holds` becomes "true
    under SOME candidate reading" — so when `emitPropertyPin` then varies the candidates, it is
    comparing them against a claim that already contains all of them.  The reasoning offered for it
    was sound about the axis it considered (an existential closure can lose a violation but never
    invent one, so no contradiction is manufactured) and silent about the axis it damaged: property
    pinning, which is the mechanism that retires a question WITHOUT spending an oracle query.

    So the shape is required rather than the type, because the shape is what carries the meaning
    and it is exactly checkable.  The escape the author was reaching for was not needed: it feared
    manufacturing an entailment failure, which `Property.lean` rightly calls the most serious
    finding the pipeline can produce — but that is `emitProperty`, one reading at a time.
    `emitPropertyPin` is a different query, and a claim that fails under one candidate and holds
    under another is its best possible result: the candidate is eliminated and the question closes
    without an oracle query.  A property that discriminates between readings is the point.
    """
    inner = _list_body(body)
    if inner is None:
        return []
    bad = [e for e in (" ".join(raw.split()) for raw in inner.split(","))
           if e and not _BARE.match(e)]
    if not bad:
        return []
    # One error for the list, not one per entry.  The complaint is carried into the prompt of
    # every pass in the next sweep, and seven copies of the same paragraph would crowd out the
    # other findings it travels with.
    shown = ", ".join(f"`{e[:44]}`" for e in bad[:3]) + (" …" if len(bad) > 3 else "")
    return [f"Partial.lean: {len(bad)} of the entries in `properties` are not `prop_` "
            f"declarations — {shown}.  Every entry must be a bare `prop_<name>`: "
            f"`Property.holds` takes no `Cfg` so that `emitPropertyPin` can vary the reading "
            f"while the claim stays fixed, and an entry that wraps a `Cfg`-taking function closes "
            f"that coordinate inside the claim instead — which leaves `survivors` comparing the "
            f"candidates against something that already contains them.  A claim that fails under "
            f"one reading and holds under another is not a contradiction and does not need "
            f"softening: `emitProperty` is the query where a failure is serious, and "
            f"`emitPropertyPin` is a different one, whose whole purpose is to eliminate the "
            f"candidate and close the question with no oracle query at all."]


def main(argv: list[str]) -> int:
    """`python3 -m leanspec.schema <prose.txt> <extraction.json>`.

    Both arguments are paths, because the prose is a file in the case's sandbox and there is no
    dataset to look it up in.  Checking an extraction against prose it did not come from is the
    one way this validator can lie, so the caller names the file rather than a key.
    """
    import sys                                                # pragma: no cover - CLI helper
    with open(argv[1], errors="replace") as f:
        prose = f.read()
    with open(argv[2]) as f:
        doc = json.load(f)
    errs = validate_extraction(doc, prose)
    for e in errs:
        print(e, file=sys.stderr)
    return 1 if errs else 0
