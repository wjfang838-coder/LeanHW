#!/usr/bin/env python3
"""Does a violated property survive the whole way from stage 4 to a decision?

    python3 -m leanspec.violation_test

A violated property is the strongest finding this pipeline produces and, until change 5, the only
one nobody was asked about: it was written into `PROPERTIES.md` and stopped there.  Making it a
question touched six modules, and none of the existing tests reaches any of that path -- the four
queries cannot produce a `violation` finding, so no fixture in the corpus has one.  This builds
one and walks it through.

What is checked, in the order a run does it:

    witness      `propcheck.violations` becomes a witness with a context and a certificate
    oracle       the menu is the two CLAUSES, and two contradictions do not share a question_id
    oracle       `any` is refused on such a menu, and the refusal says why
    refine       an answer scores as `decided` with the tags step 07's `_tags` expects
    pipeline     `_speaks_about` and `_tags` accept the witness id and the tag scheme
    schema       `violation` is an accepted decision kind, and it closes no fork
    emit         `derive` does not demand a `cfg_field`, and the section renders

The last one matters more than it looks: a violation decision fixes no coordinate of `Cfg`, and
`emit.derive` errors on any decision that names none.  That check is the reason the deliverables
cannot contain an invented assignment, so the exemption has to be tested rather than assumed.
"""
from __future__ import annotations

import json
import os
import shutil
import sys
import tempfile

if __package__ in (None, ""):
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from leanspec import cases, emit, oracle, pipeline, refine, schema, witness   # noqa: E402

CTX = {"steps": [{"clk": 1, "rst": 0, "din": 3}, {"clk": 1, "rst": 0, "din": 4}]}
# The shape `Property.lean`'s `obsJson` actually prints — `{"steps": [...]}`, not a per-signal
# map.  Written out longhand rather than sketched, because two of the checks below are that the
# waveform renders, and a fixture in the wrong shape renders as `(nothing)` and passes anyway.
OBS = {"steps": [{"dout": 0}, {"dout": 7}]}
OBS2 = {"steps": [{"dout": 0}, {"dout": 3}]}


def _properties(names) -> dict:
    """A stage-4 document with one violated row per name, certificates closed."""
    return {"properties": [
        {"name": n, "statement": f"The accumulator never outputs a value smaller than {i}.",
         "kind": "safety", "basis": [f"C{i + 1}"], "entailed": False,
         "certificate": {"entailment": True, "witness": True,
                         "axioms": {f"prop_violated_{i}": "propext"}},
         "counterexample": {"ctx": CTX, "ctx_lean": f"ctx{i}", "observation": OBS,
                            "admits": [OBS, OBS2], "cost": 2}}
        for i, n in enumerate(names)]}


def _case(tmp: str, names) -> cases.Case:
    c = cases.Case(name="vio")
    os.makedirs(c.dir, exist_ok=True)
    with open(c.path("diagnosis.json"), "w") as f:
        json.dump({"findings": [], "predictions": [], "domain": {"cost_sorted": True},
                   "certified": {}}, f)
    with open(c.path("properties.json"), "w") as f:
        json.dump(_properties(names), f)
    return c


def main() -> int:
    bad: list[str] = []

    def ck(name: str, cond) -> None:
        print(f"  {'ok ' if cond else 'BAD'}  {name}")
        if not cond:
            bad.append(name)

    tmp = tempfile.mkdtemp(prefix="vio-test-")
    old = cases.CASES_DIR
    cases.CASES_DIR = tmp
    try:
        c = _case(tmp, ["no_shrink", "no_grow"])
        doc = witness.build(c)
        ws = [w for w in doc["witnesses"] if w["kind"] == "violation"]

        # --- stage 4 -> a witness
        ck("both violations become witnesses", len(ws) == 2)
        ck("the totals count them apart", doc["totals"]["violations"] == 2)
        w = ws[0]
        ck("the id names the property", w["id"] == "violation:no_shrink")
        ck("the context comes across", w["ctx"] == CTX and w["ctx_lean"] == "ctx0")
        ck("the admitted observation comes across", w["admitted"] == OBS)
        ck("the whole admit set travels with it", w["admits"] == [OBS, OBS2])
        ck("the certificate claims only what the row carries",
           w["certificate"] == {"violation": True, "witness": True})

        # --- the oracle: a menu of clauses, not of behaviours
        opts = oracle.options(w)
        ck("the menu has two options", len(opts) == 2)
        ck("neither option is a behaviour", all(o["obs"] is None for o in opts))
        ck("the two options are the two clauses",
           {t for o in opts for t in o["tags"]} == {"definitions", "property"})
        # Two DIFFERENT contradictions at the SAME context.  Keyed on the absent `obs` these
        # would hash to one question, and step 06 would replay the first answer for the second.
        ck("two contradictions are two questions",
           oracle.question_id(ws[0]) != oracle.question_id(ws[1]))
        ck("the same contradiction is the same question",
           oracle.question_id(ws[0]) == oracle.question_id(dict(ws[0])))

        perm = list(range(len(opts)))
        body = "\n".join(oracle._question_body(w, opts, perm, None, "####"))
        ck("the question says it is not like the others", "not like the others" in body)
        ck("the question quotes the guarantee", "never outputs a value smaller than 0" in body)
        ck("the question offers no 'any'", 'There is no "any" for this question' in body)
        # The stimulus and the admitted behaviour, both drawn.  A witness whose observation is in
        # the wrong shape renders as `(nothing)` and every other check on this page still passes,
        # so the rows are named here rather than the section being checked for existence.
        ck("the stimulus is drawn", "din |" in body)
        ck("the admitted behaviour is drawn", "dout |" in body)
        ck("...and it is the one the guarantee rejects", "(nothing)" not in body)

        # --- the verdicts
        v_any = oracle._verdict("any", opts, perm, allow_any=False)
        ck("`any` is refused, not accepted", v_any["verdict"] == "refused")
        v_ok = oracle._verdict("A", opts, perm, allow_any=False)
        ck("a letter still resolves", v_ok["verdict"] == "chosen")
        ck("...to a clause, with no waveform", v_ok["obs"] is None)
        ck("`any` is still an answer on an ordinary menu",
           oracle._verdict("any", opts, perm)["verdict"] == "any")

        # --- refine: what the adjudication settles
        chosen = {"status": "ok", "verdict": "chosen", "consistent_with": ["definitions"],
                  "why": "the guarantee sentence is the wrong one", "witness": w["id"]}
        r = refine._score(c, w, chosen, {})
        ck("an adjudication is `decided`", r["outcome"] == "decided")
        ck("...and keeps the clause the designer named", r["kept"] == ["no_shrink:definitions"])
        ck("...and eliminates the other", r["eliminated"] == ["no_shrink:property"])
        ck("...and fixes no coordinate", r["pinned_to"] is None and r["observed"] is None)

        refused = {"status": "ok", "verdict": "refused", "obs": None, "why": "",
                   "detail": "'any' names no document", "witness": w["id"]}
        rr = refine._score(c, w, refused, {})
        ck("a refusal is `unadjudicated`", rr["outcome"] == "unadjudicated")
        ck("...and settles nothing", rr["kept"] == [] and rr["eliminated"] == [])
        ck("...and says so in `detail`", "unanswered question" in rr.get("detail", ""))

        outside = {"status": "ok", "verdict": "outside", "obs": None, "why": "both are wrong",
                   "witness": w["id"]}
        ro = refine._score(c, w, outside, {})
        ck("`outside` refutes both sentences at once",
           ro["outcome"] == "outside"
           and set(ro["eliminated"]) == {"no_shrink:definitions", "no_shrink:property"})

        # --- step 07's existing machinery, unchanged, must accept all of that
        ck("step 07 attributes the resolution to the property",
           pipeline._speaks_about(r, "no_shrink") and not pipeline._speaks_about(r, "no_grow"))
        ck("step 07 reads the kept tag",
           pipeline._tags(r["kept"], "no_shrink") == {"definitions"})
        ck("step 07 reads the eliminated tag",
           pipeline._tags(r["eliminated"], "no_shrink") == {"property"})

        # --- schema and emit
        ext = {"case": "vio", "design": "vio", "source": "test", "ports": [],
               "clauses": [], "choices": [], "holes": [], "properties": [], "deferred": [],
               "decisions": [{"kind": "violation", "name": "no_shrink",
                              "resolved_to": "definitions", "witness": w["id"],
                              "evidence": "e", "round": 1, "clauses": ["C1"]}]}
        errs = [e for e in schema.validate_extraction(ext, "") if "decision[0]" in e]
        ck("`violation` is an accepted decision kind", not errs)
        ext_bad = json.loads(json.dumps(ext))
        ext_bad["decisions"][0]["kind"] = "adjudication"
        ck("an invented kind is still refused",
           any("decision[0]" in e for e in schema.validate_extraction(ext_bad, "")))

        _, _, derr = emit.derive([], {"decisions": ext["decisions"]})
        ck("`derive` does not demand a coordinate of it", not derr)
        _, _, derr2 = emit.derive([], {"decisions": [dict(ext["decisions"][0], kind="choice")]})
        ck("...and still demands one of a fork", bool(derr2))

        md = emit.questions_markdown("vio", ext, [dict(x, round=1) for x in ws],
                                     [dict(r, round=1)])
        ck("the section renders", "Where the prose forbids what it defines" in md)
        ck("...under its own heading, not the deadness one",
           "Where the prose contradicts itself" not in md)
        ck("...with the guarantee quoted", "> The accumulator never outputs" in md)
        ck("...with the waveform drawn", "dout" in md and "din" in md)
        ck("...captioned as a disagreement, not as an emptiness",
           "your definitions and your guarantee disagree" in md
           and "admits nothing" not in md)
        ck("...with the adjudication", "the definitions stand" in md)
        ck("...and the unadjudicated one named as unanswered", "unadjudicated" in
           emit.questions_markdown("vio", ext, [dict(ws[1], round=1)],
                                   [dict(refine._score(c, ws[1], refused, {}), round=1)]))
    finally:
        cases.CASES_DIR = old
        shutil.rmtree(tmp, ignore_errors=True)

    if bad:
        print(f"\n{len(bad)} case(s) wrong:")
        for n in bad:
            print(f"  {n}")
        return 1
    print("\nviolation: a broken guarantee reaches the designer as a question, comes back as a "
          "decision, and closes no coordinate on the way")
    return 0


if __name__ == "__main__":
    sys.exit(main())
