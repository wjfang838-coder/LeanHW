#!/usr/bin/env python3
"""An authoring aid: fill each clause's `span` from its `text`.

Provenance is a byte range into the spec file, and a byte range typed by hand is a byte range
typed wrong.  This tool computes it -- but it computes it *from* the `text` the agent wrote,
by searching for that text verbatim.  So it cannot manufacture provenance for a quote that was
paraphrased, re-typed with collapsed whitespace, or invented: those simply do not occur in the
file and are reported as `not found`.

`schema.validate_extraction` re-checks `prose[start:end] == text` independently and is what the
`extract` stage actually gates on.  This is convenience; that is the check.

    python3 -m leanspec.spans <case> [--check]

`--check` reports without writing, which is what you want once an extraction is final.
"""
from __future__ import annotations

import json
import sys

from . import cases


def fill(doc: dict, prose: str) -> tuple[dict, list[str]]:
    notes: list[str] = []
    used: list[tuple[int, int]] = []
    for cl in doc.get("clauses", []):
        t = cl.get("text", "")
        if not t:
            notes.append(f"{cl.get('id')}: empty text")
            continue
        n = prose.count(t)
        if n == 0:
            notes.append(f"{cl.get('id')}: not found verbatim -- {t[:60]!r}")
            continue
        # Several clauses may quote the same repeated sentence; hand each the next occurrence
        # rather than all of them the first, so two clauses never claim one span.
        start = -1
        pos = 0
        while True:
            i = prose.find(t, pos)
            if i < 0:
                break
            if (i, i + len(t)) not in used:
                start = i
                break
            pos = i + 1
        if start < 0:
            notes.append(f"{cl.get('id')}: every occurrence already claimed -- {t[:40]!r}")
            continue
        used.append((start, start + len(t)))
        cl["span"] = [start, start + len(t)]
        if n > 1:
            notes.append(f"{cl.get('id')}: text occurs {n}x; took the occurrence at {start}")
    return doc, notes


def main(argv: list[str] | None = None) -> int:
    argv = list(sys.argv[1:] if argv is None else argv)
    check = "--check" in argv
    argv = [a for a in argv if a != "--check"]
    case = cases.find(argv[0])
    p = case.path("extraction.json")
    doc = json.load(open(p))
    prose = open(case.path("sandbox", "spec.txt")).read()
    doc, notes = fill(doc, prose)
    bad = [n for n in notes if "not found" in n or "already claimed" in n or "empty" in n]
    if not check and not bad:
        json.dump(doc, open(p, "w"), indent=1)
    for n in notes:
        print(("  " if n in bad else "  note: ") + n, file=sys.stderr)
    print(f"{case.name}: {len(doc.get('clauses', []))} clause(s), {len(bad)} unresolved")
    return 1 if bad else 0


if __name__ == "__main__":
    if __package__ in (None, ""):
        import os
        sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.dirname(os.path.abspath(__file__)))))
        __package__ = "leanspec"
    raise SystemExit(main())
