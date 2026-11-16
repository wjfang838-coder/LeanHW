#!/usr/bin/env python3
"""What a round does to the round before it.

    python3 -m leanspec.rounds_test

Three rules that only exist across rounds, so no single-round fixture reaches any of them, and the
first two were found by a real `accu` run rather than by reading the code.

`Cfg` IS NOT CUMULATIVE -- WHEN THE ROUND IS AUTHORED.  A coordinate exists because the prose left
it undetermined.  Once a decision is written into the prose, the next round's extraction marks that
clause `fixed`, the question is no longer a `choice` or a `hole`, and the next round's
`Partial.lean` has no field for it.  Step 07 used to hand every earlier round's decision to
`emit.derive` anyway, which refused the whole decided spec with "`h_output_latency` is not a field
of `Cfg`" -- naming the one thing that went right.  On `accu`, round 1 closed five coordinates and
round 2 could then produce no decided spec at all.

    retire       an earlier decision whose coordinate this round dropped is history, not an error
    retire       ...unless it carried no patch, because then the answer is nowhere
    retire       ...and a `property` decision needs no patch: the prose answered that fork itself
    retire       a decision naming a coordinate no `Cfg` ever had is still refused

ONE SENTENCE CAN BE REPAIRED TWICE.  Every round reads the same original prose, so every round's
spans mean the same thing and the decided prose is the original with all of them applied.  That
was written for rounds repairing different sentences and cannot express the case a second round
exists to produce: a repair the next round's evidence shows was wrong.  On `accu`, round 1
adjudicated a contradiction by rewriting a sentence to say the accumulated values are "the 4 most
recently received"; round 2's property check then proved that reading breaks
`valid_out_single_cycle`, and round 2 rewrote the same sentence.

    supersede    same span, later round wins, and what it replaced is returned rather than lost
    supersede    a partial cross is still refused -- no order of application composes it
    supersede    one round's two hunks on one span are not a supersession
    apply        the surviving hunks compose into the prose the later round wrote

A CARRIED ROUND KEEPS THE FIELD AND PINS IT.  `author.carried_documents` derives round N ≥ 2's two
sealed artifacts from round N−1's record instead of re-authoring them, and it narrows round 1's
frame with `emit.decide_partial` rather than dropping the decided fields -- because dropping a
field means rewriting every use of it, which is the cost the carry exists to avoid.  So both
shapes are legal for a decided coordinate, and which one occurs says who wrote the round.

`schema.lean_obligations` is where the two meet.  Its reverse check refuses "a `c_` or `h_` field
that extraction.json does not declare", and the carried frame has five of them on `accu`.  The
exemption is not a hole in that check but its own sentence read exactly: the defect is "an
assignment no query justified at a coordinate no answer names", and a field the decision record
names is a coordinate an answer names.

Which leaves step 07's other cross-round check with nothing to fire on.  "A decision that retires a
coordinate has to land in the text" is stated as a fact about retirement, and a carried round
retires nothing -- so the defect stays possible while its symptom disappears.  The rule moved to
`pipeline._unwritten_answers` in step 08, restated as what it was always about: an answer that
fixed a coordinate has to be in the decided prose, which is the deliverable.  It is asked of the
hunks BEFORE `patch.supersede`, and the round-1-overturned-by-round-2 case above is why.

    unwritten    an answer that fixed a coordinate has to be in the decided prose
    unwritten    ...and `property` and `violation` decisions still owe none
    unwritten    a superseded repair is in the text, in the form the later round gave it
    obligations  a decided coordinate is PERMITTED, and is still not REQUIRED
    obligations  a field neither declared open nor decided is still an invented coordinate
    obligations  a decision naming no `cfg_field` exempts nothing
    chain        `accu`'s recorded rounds 2 and 3, re-derived, pass the checker they were judged by

A ROUND IS MEASURED BY WHAT IT REMOVED, NOT BY WHAT IT DECIDED.  `pipeline._version_space` counts
the readings still standing at each stage of a round, which is the number every other count in
`REPORT.md` is a count *of*.  It matters more now than it did: re-formalizing against the decided
prose let the agent notice a fork nobody asked about, so the space could grow between rounds
without anything recording that it had, and a carried round cannot do that.  The trade is
deliberate -- it is what makes the loop cheap -- and a space that can now only shrink is one whose
size is the honest measure of what is left.

On `accu` it separates two rounds the change log cannot: round 1 went 36864 -> 576, and round 2
took two decisions and went 192 -> 192, because both were `violation` decisions that repaired a
sentence rather than closing a coordinate.

    space        pruning, merging and pinning each remove readings, and merging removes one side
    space        an unobservable coordinate is open, and collapses only in `|V/≈|`
    space        a hole with no menu is named, not counted as one
    space        `accu`'s three rounds, re-counted, and the one that closed nothing
"""
from __future__ import annotations

import json
import os
import sys

if __package__ in (None, ""):
    sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from leanspec import emit, patch, schema   # noqa: E402


def _ob(choices=(), holes=(), decisions=()):
    """`lean_obligations` of a minimal extraction, for the two directions of the field check."""
    return schema.lean_obligations({
        "choices": [{"name": c, "candidates": [{"tag": "a"}, {"tag": "b"}]} for c in choices],
        "holes": [{"name": h, "candidates": []} for h in holes],
        "decisions": list(decisions),
        "properties": []})


def _verdict(ob, fields):
    """`schema._report`'s two field directions, as it runs them on lines 690-701.

    Copied rather than called for the reason `_retire` below is: the original needs an elaborated
    Lean environment to learn what `Cfg` declares, so calling it means a Lean toolchain and a
    well-formed case file for what is a four-line set comparison.  The real one is exercised --
    with the real elaborator, on the real frame -- by `carried_chain`; this covers the rule when
    the dataset is not installed, and drifting from the original makes that check fail loudly.
    """
    allowed = set(ob["cfg_fields"]) | set(ob.get("decided_fields") or ())
    missing = [f"no field `{f}`" for f in ob["cfg_fields"] if f not in fields]
    invented = [f"invented `{f}`" for f in fields
                if f.startswith(("c_", "h_")) and f not in allowed]
    return missing + invented


def carried_chain(ck) -> None:
    """`accu`'s recorded rounds, re-derived by the carry and put to the checker that judged them.

    The chain matters, not one round in isolation.  Round 3's carried extraction has to be round
    2's CARRIED one advanced -- not the one an agent re-authored from decided prose -- because an
    authored extraction also narrows hole menus and rewrites the property list, and round 1's Lean
    was never going to match those.  Testing round 3 against round 2's authored record instead
    reports five problems that no real carried run would produce, which is how this function came
    to simulate the whole chain rather than each round against what happened to be on disk.

    Nothing is written.  `author.carried_documents` is pure for exactly this reason: the recorded
    rounds are the evidence the carry is argued from, and a test that overwrote them would destroy
    the thing it was checking.
    """
    import copy
    from leanspec import author, cases, pipeline

    try:
        case = cases.find("accu.c5")
    except Exception:
        print("  ..   accu.c5 is not installed, so the recorded chain was not re-derived")
        return
    if not os.path.isfile(pipeline.step_path(case, pipeline.BY_N[7], 2)):
        print("  ..   accu.c5 has no round 2 on disk, so the recorded chain was not re-derived")
        return

    def produced(n, r):
        with open(pipeline.step_path(case, pipeline.BY_N[n], r)) as f:
            return (json.load(f) or {}).get("produced") or {}

    files2, _rec, why = author.carried_documents(case, 2)
    ck(f"accu round 2 can be carried at all ({why})", files2 is not None)
    if files2 is None:
        return
    ext2 = json.loads(files2["extraction.json"])

    want = produced(7, 1)["extraction_decided"]
    ck("...and its extraction is round 1's step 07 output, not a re-reading of the prose",
       [c["name"] for c in ext2["choices"]] == [c["name"] for c in want["choices"]]
       and [h["name"] for h in ext2["holes"]] == [h["name"] for h in want["holes"]])

    probs2 = schema.check_partial(files2["Partial.lean"], ext2)
    ck(f"...and it passes step 02's own checker ({len(probs2)} problem(s): {probs2[:1]})",
       not probs2)

    # Round 3, from round 2's CARRIED extraction advanced by round 2's accumulated decisions.
    doc2 = produced(7, 2)["decisions_doc"]
    ext3 = pipeline._advance(copy.deepcopy(ext2), doc2)
    assigns, _open, errs = emit.derive(produced(2, 1)["cfg_fields"], doc2)
    ck(f"the accumulated record derives against round 1's frame ({errs[:1]})", not errs)
    with open(case.path(pipeline.AUTHORED, "round1", "Partial.lean"), errors="replace") as f:
        src1 = f.read()
    p3, done = emit.decide_partial(src1, assigns)
    ck("...pinning every coordinate the earlier rounds closed, not only the last round's",
       set(done) == set(assigns) and len(done) == 5)
    probs3 = schema.check_partial(p3, ext3)
    ck(f"...and round 3 carried passes the checker too ({len(probs3)} problem(s): {probs3[:1]})",
       not probs3)

FIELDS = [{"field": "c_sum_scope", "type": "KsumScope", "default": "", "kind": "choice"},
          {"field": "h_reset_kind", "type": "Option KresetKind", "default": "", "kind": "hole"}]

PROSE = ("The module accumulates four inputs and pulses valid_out. "
         "The four are the most recently received. "
         "There is no output before four arrive.")
S1 = (PROSE.index("The four"), PROSE.index("There is no"))
S2 = (PROSE.index("There is no"), len(PROSE))


def _dec(name, field, *, kind="hole", patched=True, rnd=1):
    d = {"kind": kind, "name": name, "round": rnd, "witness": f"w:{name}",
         "resolved_to": "x", "evidence": "e", "cfg_field": field, "cfg_value": "some x"}
    if patched:
        d["patch"] = [{"op": "replace", "clause": "C1", "span": [0, 4],
                       "original": PROSE[:4], "replacement": "This"}]
    return d


def _hunk(rnd, decision, span, replacement):
    return {"op": "replace", "round": rnd, "decision": decision, "clause": "C1",
            "span": list(span), "original": PROSE[span[0]:span[1]], "replacement": replacement}


def _retire(prior, doc_decisions):
    """Step 07's check 3, as `pipeline.step_decision` runs it.

    Duplicated here rather than imported because the check is eight lines inside a function that
    wants a case directory, a chain of step documents and a resolution record.  What is under test
    is the rule, and a copy that drifts from the original fails loudly the next time this runs
    against a real `07_decision.json` -- which is how the rule got here.
    """
    known = {f["field"] for f in FIELDS}
    problems, retired = [], []
    for d in prior:
        f = d.get("cfg_field")
        if not f or f in known:
            continue
        retired.append(f)
        if d.get("kind") != "property" and not d.get("patch"):
            problems.append(f"`{f}` retired with no patch")
    acc = {"decisions": prior + doc_decisions,
           "remaining_open": [{"name": f["field"], "cfg_field": f["field"], "why": "open"}
                              for f in FIELDS]}
    _, _, derr = emit.derive(FIELDS, dict(acc, decisions=[
        d for d in acc["decisions"] if d.get("cfg_field") not in set(retired)]))
    return problems + derr, retired


def version_space_chain(ck) -> None:
    """`accu`'s three recorded rounds, sized -- and the one that closed nothing.

    The change log says round 2 took two decisions, and a reader stopping there would score it as
    a productive round.  Both were `violation` decisions: they repaired a sentence the definitions
    broke, which is real work and is not a coordinate closed, so the space went 192 -> 192.  That
    is the fact this number exists to make visible, and it is drawn from the run rather than from
    a fixture because a fixture would only show that the arithmetic works.
    """
    from leanspec import cases, pipeline

    try:
        case = cases.find("accu.c5")
    except Exception:
        print("  ..   accu.c5 is not installed, so the recorded space was not re-counted")
        return
    sizes = {}
    for r in (1, 2, 3):
        p = pipeline.step_path(case, pipeline.BY_N[8], r)
        if not os.path.isfile(p):
            continue
        with open(p) as f:
            inp = json.load(f)
        sizes[r] = pipeline._version_space(
            pipeline._get(inp, "extraction"), pipeline._get(inp, "findings", []),
            pipeline._get(inp, "property_pins", []),
            {d["cfg_field"] for d in pipeline._get(inp, "decisions_doc").get("decisions", [])
             if d.get("cfg_field")})
    if not sizes:
        print("  ..   accu.c5 has no step 08 on disk, so the recorded space was not re-counted")
        return
    for r, v in sorted(sizes.items()):
        print(f"  ..   round {r}: |V| {v['before']} -> formal {v['after_formal']} -> feedback "
              f"{v['after_feedback']}, |V/≈| {v['quotient']}")
    if 1 in sizes:
        ck("round 1 searched a space its five answers cut by a factor of 32",
           sizes[1]["before"] == 36864 and sizes[1]["after_feedback"] == 576)
    if 2 in sizes:
        ck("round 2 took two decisions and closed no coordinate, and the size says so",
           sizes[2]["after_formal"] == sizes[2]["after_feedback"])
    if 3 in sizes:
        ck("round 3 closed two, and the space is still 8 readings wide up to observation",
           sizes[3]["after_feedback"] == 96 and sizes[3]["quotient"] == 8)
        ck("...so `|V/≈| = 1` would not have called this case converged either",
           sizes[3]["quotient"] != 1)


def main() -> int:
    from leanspec import pipeline
    bad: list[str] = []

    def ck(what: str, cond: bool):
        print(f"  {'ok  ' if cond else 'WRONG'} {what}")
        if not cond:
            bad.append(what)

    print("\nCfg is not cumulative")
    errs, ret = _retire([_dec("output_latency", "h_output_latency")], [])
    ck("an earlier round's dropped coordinate is history, not an error", not errs)
    ck("...and it is named, because the decided spec cannot show it",
       ret == ["h_output_latency"])

    errs, _ = _retire([_dec("output_latency", "h_output_latency", patched=False)], [])
    ck("...unless the decision carried no patch: the answer is then written down nowhere",
       any("retired with no patch" in e for e in errs))

    errs, _ = _retire([_dec("grouping", "c_grouping", kind="property", patched=False)], [])
    ck("...but a `property` decision needs none -- the prose answered that fork itself", not errs)

    errs, _ = _retire([], [_dec("invented", "h_never_existed", rnd=2)])
    ck("this round naming a coordinate no `Cfg` has is still refused",
       any("is not a field of `Cfg`" in e for e in errs))

    errs, _ = _retire([], [])
    ck("and every field of this round's `Cfg` is still accounted for", not errs)

    print("\none sentence, repaired twice")
    r1 = _hunk(1, "grouping", S1, "The four are the most recently received. ")
    r2 = _hunk(2, "valid_out_single_cycle", S1, "The four are those since the last output. ")
    keep, sup = patch.supersede([r1, r2])
    ck("same span, later round wins", keep == [r2])
    ck("...and what it replaced is returned rather than dropped",
       len(sup) == 1 and sup[0]["round"] == 1 and sup[0]["by_round"] == 2
       and sup[0]["by_decision"] == "valid_out_single_cycle")
    ck("...so the surviving hunks no longer overlap", not patch.overlaps(keep))

    cross = _hunk(2, "wide", (S1[0], S2[1]), "Everything at once.")
    keep2, sup2 = patch.supersede([r1, cross])
    ck("a partial cross is not a supersession", not sup2 and len(keep2) == 2)
    ck("...and is still refused", any("overlapping" in e for e in patch.overlaps(keep2)))

    same = _hunk(1, "other", S1, "Something else. ")
    keep3, sup3 = patch.supersede([r1, same])
    ck("one round's two hunks on one span supersede nothing new",
       len(keep3) == 1 and sup3[0]["round"] == 1 and sup3[0]["by_round"] == 1)

    r3 = _hunk(1, "before_four", S2, "No output arrives before the fourth input.")
    out, _ = patch.apply(PROSE, patch.supersede([r1, r2, r3])[0])
    ck("the decided prose is what the later round wrote",
       "those since the last output" in out and "most recently received" not in out)
    ck("...with the other round's untouched repair still in it",
       "before the fourth input" in out)

    print("\nand the report says which answer is in force")
    keep, sup = patch.supersede([r1, r2, r3])
    _, rec = patch.apply(PROSE, keep)
    doc = {"decisions": [
        {"kind": "choice", "name": "grouping", "round": 1, "resolved_to": "sliding_window",
         "witness": "w:g", "evidence": "e",
         "consequence": "An implementer must not clear the word counter on a pulse."},
        {"kind": "violation", "name": "valid_out_single_cycle", "round": 2,
         "resolved_to": "property", "witness": "violation:valid_out_single_cycle",
         "evidence": "e", "consequence": "The counter restarts after every output."},
        {"kind": "hole", "name": "quiet", "round": 1, "resolved_to": "zero", "witness": "w:q",
         "evidence": "e", "consequence": "Written into Cfg, no sentence was wrong."}]}
    ver = {"converged": False, "blocked_by": "unobservable_coordinate"}
    md = emit.report_markdown("t", doc, rec, [], "", ver, [], None, None, sup)
    ck("an overturned decision is not reported as one that changed no prose",
       "overturned in round 2 by `valid_out_single_cycle`" in md)
    ck("...and is named as superseded rather than as a live ruling",
       "the later answer is the one in force" in md)
    ck("...while a decision that genuinely wrote no hunk still reads that way",
       "closed without the prose changing" in md and "**`quiet`**" in md)
    ck("...and the two are not in the same list",
       md.index("**`quiet`**") < md.index("**`grouping`**"))
    ck("without a supersession record the section is absent",
       "the later answer is the one in force"
       not in emit.report_markdown("t", doc, rec, [], "", ver, [], None, None, None))

    # The case the real run produced: a violated property survives its own repair and is
    # adjudicated again in the next round under the SAME name.  Keyed by name alone, round 2
    # reports itself as having overturned itself and round 1 vanishes from both lists.
    p1 = _hunk(1, "pulse_count_bounded", S2, "No output before four. ")
    p2 = _hunk(2, "pulse_count_bounded", S2, "No output before four, counting from the last. ")
    keep4, sup4 = patch.supersede([p1, p2])
    _, rec4 = patch.apply(PROSE, keep4)
    doc4 = {"decisions": [
        {"kind": "violation", "name": "pulse_count_bounded", "round": 1,
         "resolved_to": "property", "witness": "v:p", "evidence": "e",
         "consequence": "The round 1 wording."},
        {"kind": "violation", "name": "pulse_count_bounded", "round": 2,
         "resolved_to": "property", "witness": "v:p", "evidence": "e",
         "consequence": "The round 2 wording."}]}
    md4 = emit.report_markdown("t", doc4, rec4, [], "", ver, [], None, None, sup4)
    ck("one name, two rounds: the earlier is reported overturned",
       "*(round 1, overturned in round 2 by `pulse_count_bounded`)*" in md4)
    ck("...and the later is not reported as overturning itself",
       "round 2, overturned" not in md4)
    ck("...nor demoted to a decision that changed no prose",
       "closed without the prose changing" not in md4)

    print("\nand the report says how big the space was that this round searched")
    ext = {"choices": [{"name": "timing", "candidates": [{"tag": "same"}, {"tag": "next"},
                                                         {"tag": "late"}]}],
           "holes": [{"name": "quiet", "candidates": [{"tag": "zero"}, {"tag": "hold"}]},
                     {"name": "edge", "candidates": [{"tag": "pos"}, {"tag": "neg"}]}],
           "properties": []}
    v = pipeline._version_space(ext, [], [], set())
    ck("with nothing pruned the space is the product of the declared menus", v["before"] == 12)
    ck("...and no stage has shrunk it",
       (v["after_formal"], v["after_feedback"], v["quotient"]) == (12, 12, 12))

    dead = [{"query": "difference", "choice": "timing", "a": "same", "b": "next",
             "a_dead": False, "b_dead": True}]
    ck("a reading that admits nothing at any legal context is gone",
       pipeline._version_space(ext, dead, [], set())["after_formal"] == 8)

    # `b` folds into `a`.  Counting both ends removes the pair rather than the duplicate, which on
    # a two-reading fork takes it to zero -- a space with no readings in it, reported for a fork
    # whose two readings turned out to be one.
    eq = [{"query": "equivalence", "choice": "timing", "a": "same", "b": "next",
           "equivalent": True}]
    ck("observationally equal readings merge to one, not to none",
       pipeline._version_space(ext, eq, [], set())["after_formal"] == 8)

    pin = [{"kind": "choice", "name": "timing", "resolved_to": "same"}]
    ck("a fork a certified property answers is down to one reading before any query",
       pipeline._version_space(ext, [], pin, set())["after_formal"] == 4)

    free = [{"query": "hole", "hole": "edge", "free": False}]
    vf = pipeline._version_space(ext, free, [], set())
    ck("a coordinate no legal context can observe still counts as open...",
       vf["after_feedback"] == 12)
    ck("...and is collapsed only in the quotient, which is why that is not the stopping rule",
       vf["quotient"] == 6)

    vd = pipeline._version_space(ext, [], [], {"h_quiet"})
    ck("an answered coordinate is closed by the feedback, not by the formal pass",
       (vd["after_formal"], vd["after_feedback"]) == (12, 6))

    nomenu = {"choices": ext["choices"], "properties": [],
              "holes": ext["holes"] + [{"name": "latency", "candidates": []}]}
    vn = pipeline._version_space(nomenu, [], [], set())
    ck("a hole stage 1 could not enumerate is named rather than counted as one",
       vn["before"] == 12 and vn["undeclared"] == ["h_latency"])

    print("\ntwo rounds that each closed one question are not the same result")
    version_space_chain(ck)

    print("\nand an answer that fixed a coordinate is in the text, whoever wrote the round")
    d_hole = {"kind": "hole", "name": "output_latency", "round": 1,
              "cfg_field": "h_output_latency", "resolved_to": "same_cycle"}
    d_prop = {"kind": "property", "name": "grouping", "round": 1, "cfg_field": "c_grouping",
              "resolved_to": "sliding_window"}
    d_viol = {"kind": "violation", "name": "no_pulse_before_four", "round": 1,
              "cfg_field": None, "resolved_to": "property"}
    h_lat = _hunk(1, "output_latency", S1, "It asserts in the same cycle. ")
    ck("a decision that fixed a coordinate and wrote a hunk is fine",
       not pipeline._unwritten_answers({"decisions": [d_hole]}, [h_lat]))
    ck("...and the same decision with no hunk anywhere is the answer written down nowhere",
       any("has to land in the text" in p for p in
           pipeline._unwritten_answers({"decisions": [d_hole]}, [])))
    ck("a `property` decision still needs none, and a `violation` names no coordinate",
       not pipeline._unwritten_answers({"decisions": [d_prop, d_viol]}, []))

    # The reason this is asked of the pre-supersede list.  Round 2 rewrote round 1's sentence, so
    # `patch.supersede` drops round 1's hunk -- and round 1's answer is in the text, in the form
    # round 2 gave it.  Checking the survivors reports it unwritten on exactly the multi-round
    # cases the second round exists to serve.
    d2 = dict(d_hole, name="valid_out_single_cycle", round=2, cfg_field="h_valid_out")
    h2 = _hunk(2, "valid_out_single_cycle", S1, "It asserts one cycle later. ")
    kept, _ = patch.supersede([h_lat, h2])
    ck("a superseded repair is not an answer that never reached the prose",
       not pipeline._unwritten_answers({"decisions": [d_hole, d2]}, [h_lat, h2]))
    ck("...which checking only the surviving hunks would have got wrong",
       any("output_latency" in p for p in
           pipeline._unwritten_answers({"decisions": [d_hole, d2]}, kept)))

    print("\na carried round keeps the field and pins it")
    #                       round 1 asked about `timing` and `reset_kind` and closed `timing`;
    #                       round 2 carried, so round 1's field is still there with a default.
    ob = _ob(holes=["reset_kind"], decisions=[{"name": "timing", "cfg_field": "c_timing"}])
    ck("a decided coordinate is permitted where an authored round would have dropped it",
       not _verdict(ob, ["c_timing", "h_reset_kind"]))
    ck("...and is still not required, because the authored shape drops it",
       not _verdict(ob, ["h_reset_kind"]))
    ck("a field neither declared open nor decided is still an invented coordinate",
       _verdict(ob, ["h_reset_kind", "c_overflow"]) == ["invented `c_overflow`"])
    ck("...and a coordinate the extraction declares is still required to be there",
       _verdict(ob, ["c_timing"]) == ["no field `h_reset_kind`"])

    # A `property` decision adjudicates a fork the prose answered itself and names no coordinate.
    # Read loosely -- "there is a decision, so let the field through" -- it would exempt every
    # invented field on any case that ever decided anything, which is most of them by round 2.
    prop = _ob(holes=["reset_kind"], decisions=[{"name": "valid_out_single_cycle"}])
    ck("a decision naming no `cfg_field` exempts nothing",
       _verdict(prop, ["h_reset_kind", "c_timing"]) == ["invented `c_timing`"])

    print("\n...and the recorded chain still passes the checker that judged it")
    carried_chain(ck)

    if bad:
        print(f"\n{len(bad)} case(s) wrong:")
        for n in bad:
            print(f"  {n}")
        return 1
    print("\nrounds: a coordinate an earlier round closed stops existing without stopping the "
          "run, or survives pinned when the round was carried, and a sentence repaired twice "
          "carries the later repair")
    return 0


if __name__ == "__main__":
    sys.exit(main())
