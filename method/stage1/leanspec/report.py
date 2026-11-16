#!/usr/bin/env python3
"""Aggregation — one row per case, read out of the artifacts and never recomputed from a log.

    detection      how many forks and holes the diagnosis confirmed, out of what stage 1 proposed
    validity       what fraction of confirmed findings carry a kernel-checked certificate
    properties     what the prose claims about itself, and whether it keeps its own claims
    witnesses      trace length and driven-signal count, and whether each is cheapest-in-domain
    queries        questions actually put to the designer, counted from the ledger
    convergence    whether the decided reading is determined everywhere, and if not, what blocks
    runtime        wall clock, from the ledger's own timestamps

Three figures are deliberately absent rather than estimated:

  * **agreement with a reference.**  There is no reference.  This half of leanSilicon takes prose
    and returns prose, and the claim it makes is about the decision procedure — every question
    the prose left open was found, put, and closed or declared open with a reason — not about
    matching an implementation somebody else wrote.  A column here comparing the decided spec to
    an answer key would be reporting a different experiment from the one that ran.
  * **token cost.**  The agent stages run in a conversation this process cannot see.  What is
    recorded instead is artifact size and round count, labelled as a proxy.  A token number
    invented here would be indistinguishable from a measured one in the report, which is the
    whole problem.
  * **detection *accuracy*** in the sense of precision against a labelled truth set.  There is no
    per-specification list of "the real ambiguities in this document".  What is reported is the
    confirmed/proposed ratio and, separately, what the designer said about each confirmed
    finding — which is a measurement, where an accuracy figure would be a claim about a set
    nobody has enumerated.
"""
from __future__ import annotations

import datetime
import json
import os

from common import paths

from . import cases, emit, pipeline, refine, schema

RESULTS = paths.data("runs", "leanspec")


def _load(case: cases.Case, name: str) -> dict:
    p = case.path(name)
    if not os.path.isfile(p):
        return {}
    with open(p, errors="replace") as f:
        return json.load(f)


def _tree_bytes(root: str) -> int:
    return sum(os.path.getsize(os.path.join(d, f))
               for d, _, fs in os.walk(root) for f in fs
               if os.path.isfile(os.path.join(d, f)))


def _first_round(case: cases.Case, name: str) -> dict:
    """The artifact as it stood before any question was answered.

    A converged case's live `diagnosis.json` reports nothing — no ambiguity, no hole, no
    contradiction — because that is what convergence *is*.  Reading the live file would turn
    every successful case into a case that found nothing.

    The step chain is asked first and `rounds/round1/` second, and they are not equally good: a
    round directory is a snapshot of the working files, taken while the round is running, whereas
    a step document is the output of the step that produced it and cannot have been advanced by
    anything downstream.
    """
    step = pipeline.undecided(case, name)
    if isinstance(step, dict):
        return step
    rs = refine.rounds(case)
    if rs:
        p = case.path("rounds", rs[0], name)
        if os.path.isfile(p):
            with open(p, errors="replace") as f:
                return json.load(f)
    return _load(case, name)


def _final(case: cases.Case) -> dict:
    """The last round's step 09, which carries the convergence verdict and the re-diagnosis.

    Read from the step chain rather than from a `verification.json` on disk, because the chain is
    the record: a loose file is whatever the last command to write it left behind, and a case run
    to step 06 and then abandoned would still have one from an earlier attempt.
    """
    rs = pipeline.existing_rounds(case)
    if not rs:
        return _load(case, "verification.json")
    p = pipeline.step_path(case, pipeline.BY_N[pipeline.LAST], rs[-1])
    if not os.path.isfile(p):
        return _load(case, "verification.json")
    with open(p, errors="replace") as f:
        return (json.load(f).get("produced") or {}).get("verification") or {}


# The events that *advance* a case, as opposed to re-checking one.  `extract`, `formalize` and
# `audit` are idempotent and get re-run — while iterating on the schema, while regenerating this
# report — and each re-run stamps a fresh timestamp into the ledger.  Taking the span from the
# first event to the last one therefore measures *when the report was last regenerated*, not how
# long the case took: run the audit over every case and they all report the same elapsed time, to
# the second.  That happened, which is why the definition below is anchored to the last event
# that moved the case forward.
_ADVANCING = ("oracle_query", "verify", "snapshot", "resolve", "witness", "diagnose",
              "properties")


def _t(row: dict) -> float | None:
    try:
        return datetime.datetime.fromisoformat(row["ts"]).timestamp()
    except (KeyError, TypeError, ValueError):
        return None


def _elapsed(led: list[dict]) -> float | None:
    """Seconds from the first ledger event to the last one that advanced the case.

    Still an upper bound on compute rather than a measurement of it — the gaps between stages are
    an agent thinking in a conversation this process cannot see — and it is labelled that way
    wherever it is reported.  What it is not is a number that changes every time somebody re-runs
    the audit.
    """
    starts = [t for t in map(_t, led) if t is not None]
    ends = [t for t in (_t(e) for e in led if e.get("event") in _ADVANCING) if t is not None]
    if not starts or not ends:
        return None
    return round(max(ends) - min(starts), 1)


def _options_census(ext: dict, live: dict) -> dict:
    """How many of this case's questions were asked out of a complete option set.

    `closed` counts questions whose options are the whole domain, `sampled` those whose options
    were declared to be a subset of it, and `undeclared` those where stage 1 recorded nothing
    either way.  The distinction is not bookkeeping: only a closed set can turn one survivor into
    an answer, so this is the count that says how much of a corpus's pinning rests on a menu
    somebody checked.

    Two extractions, because a hole's roster and its declaration come from different moments.
    The roster is round 1's — a hole answered in round 1 is gone from the live file, and a
    question that was asked still counts.  The declaration is the *latest* one, because a later
    round may enumerate a domain the first round left unstated, and then the question it asked
    was asked out of the enumerated menu; reporting round 1's silence would describe a menu
    nobody used.

    That rule is `emit.merge_extractions`, and it is called rather than restated: step 08 needs
    the same union to build `QUESTIONS.md`, and a census that counted a question the question
    list did not print would be two answers to one question about the same run.
    """
    merged = emit.merge_extractions([ext, live])
    n = {schema.CLOSED: len(merged["choices"]), schema.SAMPLED: 0, schema.UNDECLARED: 0}
    for h in merged["holes"]:
        n[schema.domain_of(h)["status"]] += 1
    return {"closed": n[schema.CLOSED], "sampled": n[schema.SAMPLED],
            "undeclared": n[schema.UNDECLARED]}


def row(case: cases.Case) -> dict:
    ext = _first_round(case, "extraction.json")
    diag = _first_round(case, "diagnosis.json")
    props = _first_round(case, "properties.json")
    wit = _first_round(case, "witnesses.json")
    res = _first_round(case, "resolution.json")
    ver = _final(case)
    aud = _load(case, "audit.json")
    led = cases.ledger(case)
    rs = refine.rounds(case)
    final = _load(case, "diagnosis.json")

    counts = diag.get("counts", {})
    certified, uncertified = diag.get("certified", {}), diag.get("uncertified", {})
    ws = wit.get("witnesses", [])
    # The tally is recounted from the round's own resolutions rather than read off the `outcomes`
    # field beside them, so that a label the stored evidence contradicts is corrected here too —
    # see `refine.relabel`.  Falls back to the stored tally for a round with no per-resolution
    # detail to recount from.
    labels = [refine.relabel(x).get("outcome") for x in res.get("resolutions", [])]
    outcomes = ({o: labels.count(o) for o in dict.fromkeys(labels) if o}
                or res.get("outcomes", {}))
    # Decisions are read from the *live* extraction, not round 1's: round 1 is by construction
    # the state before any of them were taken.  They are counted by kind because the four kinds
    # cost different things — a `model` decision fixes the projection and teaches nothing about
    # the specification, a `choice` closes a fork and a `hole` fills a gap (both at the price of
    # a query), and a `property` closes a fork for free, because the prose answered it.
    live_ext = _load(case, "extraction.json")
    dec = live_ext.get("decisions", [])
    pcounts = props.get("counts", {})
    return {
        "case": case.name,
        "source": case.source,
        "why_selected": case.why,
        "proposed": {"clauses": len(ext.get("clauses", [])),
                     "choices": len(ext.get("choices", [])),
                     "holes": len(ext.get("holes", [])),
                     "properties": len(ext.get("properties", [])),
                     "deferred": len(ext.get("deferred", []))},
        "diagnosed": counts,
        "domain": {k: diag.get("domain", {}).get(k)
                   for k in ("ctx_total", "ctx_legal", "obs_total", "cost_sorted", "max_cost")},
        "certificates": {"certified": len(certified), "uncertified": len(uncertified),
                         "names": sorted(certified)},
        # What the prose claims about itself.  `violated` is the sharpest single number this
        # framework produces: the same document states a guarantee and admits a run that breaks
        # it, with a certified counterexample.  `pinning` is the second — a claim that answers
        # one of the document's own open questions, so the fork retires without a query.
        "properties": {"stated": pcounts.get("stated", 0),
                       "expressible": pcounts.get("expressible", 0),
                       "inexpressible": pcounts.get("inexpressible", 0),
                       "violated": pcounts.get("violated", 0),
                       "vacuous": pcounts.get("vacuous", 0),
                       "inert": pcounts.get("inert", 0),
                       "pinning": pcounts.get("pinning", 0),
                       "narrowing": pcounts.get("narrowing", 0),
                       "independent": pcounts.get("independent", 0),
                       "uncertified": len(props.get("uncertified") or {})},
        "witnesses": {"n": len(ws),
                      "retired_by_property": len(wit.get("retired_by_property") or []),
                      "mean_steps": wit.get("totals", {}).get("mean_steps"),
                      "mean_signals": wit.get("totals", {}).get("mean_signals"),
                      "all_minimal_in_domain": wit.get("totals", {}).get("all_minimal")},
        "resolution": outcomes,
        # What the questions were asked *out of*.  Every question this framework asks is multiple
        # choice, so the option set is half of it, and the two halves are not equally
        # trustworthy: a closed set makes one survivor the answer, a sampled one makes it one
        # survivor among the values offered.  A choice is closed by construction — its options
        # are the constructors of an inductive, cross-checked against the extraction — so only
        # the holes can land anywhere else.
        "options": _options_census(ext, live_ext),
        "decisions": {"total": len(dec),
                      "model": sum(1 for d in dec if d.get("kind") == "model"),
                      "choice": sum(1 for d in dec if d.get("kind") == "choice"),
                      "hole": sum(1 for d in dec if d.get("kind") == "hole"),
                      "property": sum(1 for d in dec if d.get("kind") == "property")},
        # A query is a question PUT TO A DESIGNER.  A replay (step 06 re-run over an answer
        # already on disk) and a reuse (two witnesses that turned out to be the same question)
        # are counted apart, because the number this method reports is the first one and adding
        # the other two to it would inflate the cost every time a run was resumed.
        "queries": {"asked": sum(1 for e in led if e.get("event") == "oracle_query"),
                    "replayed": sum(1 for e in led if e.get("event") == "oracle_replay"),
                    "reused": sum(1 for e in led if e.get("event") == "oracle_reuse"),
                    # Sittings, not questions: one per round in which anything was asked.
                    "sittings": sum(1 for e in led if e.get("event") == "oracle_session"
                                    and not e.get("replayed"))},
        "converged": ver.get("converged"),
        "blocked_by": ver.get("blocked_by"),
        "decided_unsatisfiable": bool(ver.get("decided_unsatisfiable")),
        # Questions the projection proved answerable and the designer then declined to answer.
        # Counted separately from `blocked_by` because a case can be blocked on something else
        # and still carry them — and because it is a different kind of fact from the rest of this
        # row: a certified separation the designer accepts on both sides is not a defect in the
        # specification but a declared degree of freedom in it, and no amount of further querying
        # closes the question.
        "designer_indifferent": {
            "n": len(ver.get("designer_indifferent") or []),
            "certified": sum(1 for i in (ver.get("designer_indifferent") or [])
                             if i.get("separation_certified")),
            "questions": [i.get("question") for i in (ver.get("designer_indifferent") or [])],
        },
        "rounds": len(rs),
        "pipeline_steps": pipeline.n_steps(case),
        "final_counts": final.get("counts", {}),
        "determinism_certificate": ver.get("determinism_certificate"),
        "audit": {"order_clean": aud.get("order", {}).get("clean"),
                  "leak_scan_run": bool(aud.get("leak_scan", {}).get("run", True)),
                  "leak_clean": aud.get("leak_scan", {}).get("clean"),
                  "private_identifiers": aud.get("leak_scan", {}).get("private_identifiers")},
        "wall_clock_s": _elapsed(led),
        "artifact_bytes": _tree_bytes(case.dir) if os.path.isdir(case.dir) else 0,
    }


def aggregate(rows: list[dict]) -> dict:
    def s(path: list[str]) -> int:
        tot = 0
        for r in rows:
            v = r
            for k in path:
                v = (v or {}).get(k) if isinstance(v, dict) else None
            tot += v or 0
        return tot

    blocked: dict[str, int] = {}
    for r in rows:
        if r.get("blocked_by"):
            blocked[r["blocked_by"]] = blocked.get(r["blocked_by"], 0) + 1
    return {
        "cases": len(rows),
        "blocked_by": blocked,
        "totals": {
            "clauses": s(["proposed", "clauses"]),
            "choices_proposed": s(["proposed", "choices"]),
            "holes_proposed": s(["proposed", "holes"]),
            "properties_proposed": s(["proposed", "properties"]),
            "deferred": s(["proposed", "deferred"]),
            "ambiguity": s(["diagnosed", "ambiguity"]),
            "repair_options": s(["diagnosed", "repair_options"]),
            "inert_forks": s(["diagnosed", "inert_forks"]),
            "discriminating": s(["diagnosed", "discriminating"]),
            "pinning": s(["diagnosed", "pinning"]),
            "redundancy": s(["diagnosed", "redundancy"]),
            "incompleteness": s(["diagnosed", "incompleteness"]),
            "contradiction": s(["diagnosed", "contradiction"]),
            "certified": s(["certificates", "certified"]),
            "uncertified": s(["certificates", "uncertified"]),
            "prop_stated": s(["properties", "stated"]),
            "prop_expressible": s(["properties", "expressible"]),
            "prop_inexpressible": s(["properties", "inexpressible"]),
            "prop_violated": s(["properties", "violated"]),
            "prop_vacuous": s(["properties", "vacuous"]),
            "prop_inert": s(["properties", "inert"]),
            "prop_pinning": s(["properties", "pinning"]),
            "prop_narrowing": s(["properties", "narrowing"]),
            "prop_uncertified": s(["properties", "uncertified"]),
            "options_closed": s(["options", "closed"]),
            "options_sampled": s(["options", "sampled"]),
            "options_undeclared": s(["options", "undeclared"]),
            "witnesses": s(["witnesses", "n"]),
            "retired_by_property": s(["witnesses", "retired_by_property"]),
            "queries_asked": s(["queries", "asked"]),
            "queries_replayed": s(["queries", "replayed"]),
            "queries_reused": s(["queries", "reused"]),
            "decisions": s(["decisions", "total"]),
            "decisions_model": s(["decisions", "model"]),
            "decisions_choice": s(["decisions", "choice"]),
            "decisions_hole": s(["decisions", "hole"]),
            "decisions_property": s(["decisions", "property"]),
            "converged": sum(1 for r in rows if r["converged"]),
            "rounds": s(["rounds"]),
            "order_clean": sum(1 for r in rows if r["audit"]["order_clean"]),
            "leak_scans_run": sum(1 for r in rows if r["audit"]["leak_scan_run"]),
            "leak_clean": sum(1 for r in rows if r["audit"]["leak_clean"]),
            "designer_indifferent": s(["designer_indifferent", "certified"]),
            "designer_indifferent_cases": sum(1 for r in rows
                                              if r["designer_indifferent"]["certified"]),
        },
    }


def markdown(rows: list[dict], agg: dict) -> str:
    L = ["# leanSpec — results", "",
         f"{agg['cases']} specification(s).", "",
         "## Per case", "",
         "Findings are counted as *separations*, not as questions: a fork with three readings "
         "contributes three pairwise comparisons, so the finding columns can exceed the proposed "
         "columns beside them. `free`/`dead` are the hole and contradiction verdicts; `disc`/"
         "`pin` are the witnesses that separate two readings and the witnesses that pin one hole "
         "value against the rest. `props` is stated/violated — a violated property is the "
         "document contradicting a guarantee it makes about itself, with a certified "
         "counterexample.", "",
         "| case | forks | holes | defer | ambig | repair | inert | disc | pin | free | dead | "
         "certs | props | witnesses | queries | history | decisions (m/c/h/p) | indiff | "
         "outcome |",
         "|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|"]
    for r in rows:
        d, c, dec, p = r["diagnosed"], r["certificates"], r["decisions"], r["properties"]
        out = "converged" if r["converged"] else (r.get("blocked_by") or "open")
        hist = (f"{r['rounds']} round{'s' if r['rounds'] != 1 else ''}"
                + (f", {r['pipeline_steps']} steps" if r.get("pipeline_steps") else "")
                if r["rounds"]
                else (f"{r['pipeline_steps']} steps" if r.get("pipeline_steps") else "—"))
        q = (f"{r['queries']['asked']}"
             + (f" (+{r['queries']['reused']} reused)" if r["queries"]["reused"] else ""))
        L.append(f"| `{r['case']}` | {r['proposed']['choices']} | {r['proposed']['holes']} | "
                 f"{r['proposed']['deferred']} | {d.get('ambiguity', 0)} | "
                 f"{d.get('repair_options', 0)} | {d.get('inert_forks', 0)} | "
                 f"{d.get('discriminating', 0)} | {d.get('pinning', 0)} | "
                 f"{d.get('incompleteness', 0)} | {d.get('contradiction', 0)} | "
                 f"{c['certified']}✓/{c['uncertified']}✗ | "
                 f"{p['stated']}/{p['violated']} | {r['witnesses']['n']} | {q} | "
                 f"{hist} | {dec['model']}/{dec['choice']}/{dec['hole']}/{dec['property']} | "
                 f"{r['designer_indifferent']['certified'] or '—'} | {out} |")
    t = agg["totals"]
    L += ["", "## Totals", "",
          f"- **{t['clauses']}** clauses extracted, carrying **{t['choices_proposed']}** forks, "
          f"**{t['holes_proposed']}** holes and **{t['properties_proposed']}** stated properties "
          f"into diagnosis, with **{t['deferred']}** questions recorded as deferred — visible in "
          f"the prose, outside the projection, and named rather than silently dropped.",
          f"- fork separations: **{t['ambiguity']}** real ambiguities (a legal context separates "
          f"two readings the prose can both satisfy), **{t['inert_forks']}** inert (the readings "
          f"are observationally equal, so the prose is imprecise but not ambiguous), and "
          f"**{t['repair_options']}** repair options — separations between readings of a clause "
          f"set that contradicts itself, where choosing a reading is choosing what to fix.",
          f"- **{t['redundancy']}** pairs proved observationally equivalent and were merged.",
          f"- hole separations: **{t['incompleteness']}** holes show observable freedom, "
          f"**{t['pinning']}** witnesses pin a value against the rest.",
          f"- contradictions found by Deadness: **{t['contradiction']}**.",
          f"- certificates: **{t['certified']}** kernel-checked, **{t['uncertified']}** not.",
          f"- properties: **{t['prop_stated']}** claims the prose makes about itself, of which "
          f"**{t['prop_expressible']}** could be written over the projection and "
          f"**{t['prop_inexpressible']}** could not and are named as such. "
          f"**{t['prop_violated']}** are *violated* — the same document states the guarantee and "
          f"admits a run that breaks it, with a certified counterexample. "
          f"**{t['prop_vacuous']}** never have their antecedent satisfied at any legal context "
          f"and **{t['prop_inert']}** hold at every one, so neither constrains anything; "
          f"**{t['prop_narrowing']}** eliminate at least one reading of an open fork and "
          f"**{t['prop_pinning']}** eliminate all but one, which retires the question without a "
          f"query. **{t['prop_uncertified']}** property findings did not close a certificate and "
          f"are therefore reported as searches rather than believed.",
          f"- option sets: every question is multiple choice — the designer is shown N waveforms "
          f"and picks one, or rejects all of them, or declares the choice free. "
          f"**{t['options_closed']}** of those option sets are the coordinate's whole domain, so "
          f"one survivor is the answer; **{t['options_sampled']}** are a declared sample, which "
          f"can prove a coordinate free but may not pin it; **{t['options_undeclared']}** declare "
          f"no domain size, and a pin taken on one is carried with that caveat printed beside it "
          f"rather than as a proven value.",
          f"- designer queries: **{t['queries_asked']}** questions put, "
          f"**{t['queries_reused']}** answered by an identical question asked earlier in the same "
          f"run, **{t['queries_replayed']}** re-read from disk on a re-run. Only the first is a "
          f"cost. **{t['retired_by_property']}** further question(s) never reached the designer "
          f"at all, because a property the prose itself states had already answered them.",
          f"- decisions taken: **{t['decisions']}** — **{t['decisions_model']}** fixing the "
          f"projection (interface facts, which teach nothing about the specification), "
          f"**{t['decisions_choice']}** closing a fork, **{t['decisions_hole']}** filling a hole, "
          f"**{t['decisions_property']}** closed by the document's own guarantee.",
          f"- converged: **{t['converged']}/{agg['cases']}**, over **{t['rounds']}** refinement "
          f"round(s) in total."
          + ("  Not converged: "
             + ", ".join(f"**{n}** {k}" for k, n in sorted(agg["blocked_by"].items()))
             + "." if agg["blocked_by"] else ""),
          f"- designer-indifferent questions: **{t['designer_indifferent']}** across "
          f"**{t['designer_indifferent_cases']}** case(s) — a reading pair the projection proves "
          f"distinguishable at a legal context, where the designer then accepted both. The "
          f"specification is under-determined there *by decision*, so no amount of further "
          f"querying closes the question, and the coordinate is carried into the deliverables as "
          f"a declared degree of freedom rather than as an unanswered question.",
          f"- audit: ledger order clean on **{t['order_clean']}/{agg['cases']}**. The leak scan "
          f"ran on **{t['leak_scans_run']}/{agg['cases']}** — it needs a reference implementation "
          f"named on the command line, and leanSpec has none of its own, so a case without one is "
          f"not a case that passed.", "",
          "## What is not here", "",
          "There is no agreement column. This half of leanSilicon has no reference "
          "implementation and does not want one: what it claims is that every question the prose "
          "left open was found, put to its author, and closed or declared open with a reason — "
          "and that the result is determined everywhere, proved by the kernel. Comparing the "
          "decided specification to an implementation somebody else wrote would answer a "
          "different question, and putting the two numbers in one table would invite reading the "
          "second as evidence for the first.", ""]
    return "\n".join(L)


def main(a=None) -> int:
    rows = [row(c) for c in cases.registry()]
    agg = aggregate(rows)
    out = getattr(a, "out", None) or RESULTS
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, "RESULTS.json"), "w") as f:
        json.dump({"rows": rows, "aggregate": agg}, f, indent=1, default=str)
    md = markdown(rows, agg)
    with open(os.path.join(out, "SUMMARY.md"), "w") as f:
        f.write(md)
    print(md)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
