#!/usr/bin/env python3
"""Stage 4 — turning a diagnosis into evidence a designer (or an oracle) can be shown.

A finding says *the specification is ambiguous here*.  A witness says *drive this, watch
that, and the two readings disagree* -- and it is the second that can be handed to a
simulator.  This module takes what stage 3 found and produces, per finding:

    the stimulus            the context as `{"steps": [{signal: value}, ...]}`
    the predictions         what each reading says will be observed, recorded BEFORE asking
    the complexity          trace length, driven signals, active signals
    the split               how evenly the query divides the candidate space
    the certificate status  whether the kernel confirmed the finding this witness serves

`goal.md` asks witnesses to be optimised for high information gain, short traces, and few
relevant signals.  What this module can *prove* about that, and what it can only *measure*,
are kept apart:

  * **short** — proved, conditionally.  `ctxUniverse` is enumerated in non-decreasing
    `ctxCost` order and the search returns the first hit, so the witness is a cheapest one in
    the domain.  `cost_sorted` is checked in Lean, not assumed; if it comes back false the
    witness is marked `minimal_in_domain: false` and the claim is withdrawn rather than
    restated.
  * **few signals** — measured, not proved.  The `Ctx` type *is* the projection: a case
    enumerates only the signals its fork can turn on.  The count reported here is the count
    of signals in the stimulus, and it is a property of that modelling choice.
  * **information gain** — computed, and bounded below.  A context where two readings admit
    *different* sets is not automatically a query worth asking: if the sets differ but overlap
    -- which is what an open hole does, widening both sides until they share an observation --
    the reference's answer can land in the intersection and eliminate nothing.  Stage 3 there-
    fore searches first for a context where the two sets are **disjoint**, and a witness marked
    `discriminating` is one where any observation refutes a reading.  When the domain contains
    no such context the merely-separating one is kept, marked `discriminating: false`, and its
    `silent` outcome at stage 5 is the honest result rather than a surprise.  For a wider fork
    `bestSplit` picks the context whose induced partition has the smallest largest group, which
    is the even division `goal.md` asks for.

Nothing here re-runs a search: every number comes from the JSON stage 3 printed.

## The fourth kind

Three of the four kinds below are questions about what the prose leaves *open* -- an ambiguity, a
repair, an incompleteness.  The fourth, `violation`, is not: stage 4 proved that the prose's own
guarantee forbids an observation the prose's own definitions admit, at a context both call legal.
There is no reading under which both sentences hold, so there is no menu of behaviours and no
choice of reading that repairs it -- what has to change is one of the two sentences, and which one
is a fact only the author has.  It becomes a witness for exactly that reason: it is a question, and
the machinery for putting a question to the author is here.  `oracle.options` builds its menu out
of the two clauses instead of out of two waveforms.
"""
from __future__ import annotations

import json

from . import cases, propcheck


def _stimulus(ctx: dict) -> dict:
    return ctx if isinstance(ctx, dict) else json.loads(ctx)


def _obs(x) -> dict:
    """`ctxJson`/`obsJson` emit raw JSON, so an emitter's array already holds objects; a
    quoted rendering would arrive as a string.  Accept either rather than depend on which."""
    return x if isinstance(x, dict) else json.loads(x)


def _complexity(stim: dict) -> dict:
    steps = stim.get("steps", [])
    driven, active = set(), set()
    for st in steps:
        for k, v in st.items():
            driven.add(k)
            if v not in (0, "0", False):
                active.add(k)
    return {"steps": len(steps), "signals": len(driven), "active_signals": len(active),
            "signal_names": sorted(driven)}


def build(case: cases.Case) -> dict:
    diag = json.load(open(case.path("diagnosis.json")))
    findings = diag["findings"]
    # A fork a certified property already pins is not a question.  Dropping it here rather than
    # letting stage 5 ask and stage 6 reconcile is not an optimisation: the designer, shown a
    # menu that includes readings the specification's own guarantee forbids, can pick one -- and
    # the answer would be recorded as `decided`, the fork closed on it, and the property left
    # violated by the decided spec with nothing downstream to notice.  See `propcheck`.
    retired = propcheck.retired(case)
    preds = {}
    for p in diag.get("predictions", []):
        preds.setdefault(p["ctx_lean"], {})[p["tag"]] = [_obs(a) for a in p["admits"]]
    cost_sorted = diag.get("domain", {}).get("cost_sorted", False)
    certified = diag.get("certified", {})

    splits = {f["choice"]: f for f in findings if f["query"] == "split" and f.get("splits")}
    out, skipped = [], []
    for f in findings:
        q = f["query"]
        if q == "difference" and f.get("separated"):
            n, a, b = f["choice"], f["a"], f["b"]
            if n in retired:
                skipped.append({"id": f"ambiguity:{n}:{a}:{b}", "choice": n,
                                "retired_by_property": retired[n]["property"],
                                "resolved_to": retired[n]["resolved_to"],
                                "why": retired[n]["why"]})
                continue
            stim = _stimulus(f["ctx"])
            # A separation against a reading that is dead somewhere is not evidence of an
            # ambiguity -- it is the price of one repair of a contradiction.  Same witness,
            # same oracle question, different claim, so it is labelled differently.
            kind = "repair" if (f.get("a_dead") or f.get("b_dead")) else "ambiguity"
            w = {"id": f"{kind}:{n}:{a}:{b}", "kind": kind, "choice": n,
                 "candidates": [a, b], "ctx": stim, "ctx_lean": f["ctx_lean"],
                 "dead_side": [t for t, d in ((a, f.get("a_dead")), (b, f.get("b_dead"))) if d],
                 "discriminating": bool(f.get("discriminating")),
                 "cost": f["cost"], "minimal_in_domain": bool(cost_sorted),
                 "complexity": _complexity(stim),
                 "predicted": preds.get(f["ctx_lean"], {}),
                 "certificate": {"legal": f"legal_{n}_{a}_{b}" in certified,
                                 "separation": f"diff_{n}_{a}_{b}" in certified,
                                 "disjoint": f"disj_{n}_{a}_{b}" in certified}}

            if n in splits:
                w["split"] = {"groups": splits[n]["groups"], "width": splits[n]["width"],
                              "candidates": splits[n]["candidates"]}
            else:
                w["split"] = {"groups": [[a], [b]], "width": 1, "candidates": 2}
            out.append(w)
        elif q == "hole" and f.get("free"):
            n = f["hole"]
            stim = _stimulus(f["ctx"])
            out.append({"id": f"incompleteness:{n}", "kind": "incompleteness", "hole": n,
                        "ctx": stim, "ctx_lean": f["ctx_lean"], "cost": f["cost"],
                        "minimal_in_domain": bool(cost_sorted),
                        "complexity": _complexity(stim),
                        "admits": [_obs(a) for a in f["admits"]],
                        "pinning": bool(f.get("pinning")),
                        "predicted": preds.get(f["ctx_lean"], {}),
                        "certificate": {"legal": f"legal_hole_{n}" in certified,
                                        "freedom": f"free_{n}" in certified,
                                        "attribution": f"attrib_{n}" in certified,
                                        **({"pinning": f"pin_{n}" in certified}
                                           if f.get("pinning") else {})}})
        elif q == "deadness" and f.get("dead"):
            stim = _stimulus(f["ctx"])
            out.append({"id": "contradiction:default", "kind": "contradiction",
                        "ctx": stim, "ctx_lean": f["ctx_lean"], "cost": f["cost"],
                        "minimal_in_domain": bool(cost_sorted),
                        "complexity": _complexity(stim),
                        "certificate": {"legal": "legal_dead" in certified,
                                        "emptiness": "dead_default" in certified}})

    # A guarantee the definitions break.  Stage 4 proved it at a named context and, until this
    # existed, wrote it into `PROPERTIES.md` and stopped: the strongest finding this pipeline can
    # produce was the only one nobody was asked about.  A run could then converge with the
    # contradiction intact -- the four queries walk straight past a property, so the re-diagnosis
    # finds nothing, `decided_determined` closes, and the deliverables report a clean case whose
    # own prose forbids the behaviour its own prose defines.
    #
    # It is a witness because it has everything a witness is: a legal context, a certified claim
    # about that context, and a question only the author can answer.  What it does not have is a
    # menu of behaviours -- the property says "not that" without saying what instead, so there is
    # no second waveform to offer and no reading of the prose under which both sentences hold.
    # What is put to the designer is therefore the pair of sentences, and the question is which
    # one is wrong.  See `oracle.options` for the shape of that menu.
    for v in propcheck.violations(case):
        ce = v.get("counterexample") or {}
        stim = _stimulus(ce.get("ctx") or {"steps": []})
        out.append({"id": f"violation:{v['name']}", "kind": "violation",
                    "property": v["name"], "statement": v.get("statement", ""),
                    "property_kind": v.get("kind"), "basis": v.get("basis"),
                    "ctx": stim, "ctx_lean": ce.get("ctx_lean"), "cost": ce.get("cost"),
                    "minimal_in_domain": bool(cost_sorted),
                    "complexity": _complexity(stim),
                    # The observation the definitions admit and the property rejects, and the
                    # whole admit set it was drawn from.  Both travel with the witness because
                    # the designer is shown the first and a reader checking the finding by hand
                    # needs the second: a property broken by one of five admitted behaviours is
                    # a different repair from one broken by the only behaviour there is.
                    "admitted": _obs(ce["observation"]) if ce.get("observation") else None,
                    "admits": [_obs(a) for a in ce.get("admits", [])],
                    # What stage 4's kernel actually closed, named the way a fork's is: `violation`
                    # is `entails ... = false` over the whole frame, `witness` is that the context
                    # printed above is one where it fails.  `prop_legal_<n>` is proved too and is
                    # not claimed here, because the row this is read from does not carry it and a
                    # certificate flag nobody can trace to a theorem is worse than an absent one.
                    "certificate": {
                        "violation": bool((v.get("certificate") or {}).get("entailment")),
                        "witness": bool((v.get("certificate") or {}).get("witness"))}})

    doc = {"case": case.name, "witnesses": out,
           # Questions retired without a query, so the count of questions asked can be read
           # against the count of questions found rather than silently shrinking.
           "retired_by_property": skipped,
           "merged": [{"choice": f["choice"], "a": f["a"], "b": f["b"]}
                      for f in findings
                      if f["query"] == "equivalence" and f.get("equivalent")],
           "inert": [{"choice": f["choice"], "a": f["a"], "b": f["b"]}
                     for f in findings
                     if f["query"] == "difference" and not f.get("separated")],
           "totals": {"witnesses": len(out),
                      "retired_by_property": len(skipped),
                      # Counted apart from the rest, because it is not the same kind of number:
                      # the others are questions about what the prose leaves open, and this is
                      # the count of places it closes two ways at once.
                      "violations": sum(1 for w in out if w["kind"] == "violation"),
                      "discriminating": sum(1 for w in out if w.get("discriminating")),
                      "pinning": sum(1 for w in out if w.get("pinning")),
                      "mean_steps": (round(sum(w["complexity"]["steps"] for w in out) / len(out), 2)
                                     if out else 0),
                      "mean_signals": (round(sum(w["complexity"]["signals"] for w in out) / len(out), 2)
                                       if out else 0),
                      "all_minimal": all(w["minimal_in_domain"] for w in out) if out else True}}
    json.dump(doc, open(case.path("witnesses.json"), "w"), indent=1)
    cases.log(case, "witness", n=len(out), **doc["totals"])
    return doc
