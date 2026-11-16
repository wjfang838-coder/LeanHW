"""`probe.json` is derived, and the derivation reproduces every one an agent ever wrote.

`python3 -m leanspec.probe_test`

`emit.probe_document` replaced a whole authoring pass — the ninth of stage 2, one `claude -p`
session per round whose entire output was this document.  Deleting a pass is a claim that the pass
was not deciding anything, and a claim like that is worth checking against the record rather than
asserting from the shape of the code.

So the corpus half of this test is the evidence, not a smoke test: every `probe.json` under
`data/part1/` is loaded with the `extraction.json` of the round that produced it, and the derived
document must equal it EXACTLY — same fields, same values, same order within `inputs` and
`outputs`.  A single mismatch means some session made a choice this function does not make, and
the pass was carrying a judgement after all.

The corpus is two designs, so it pins the rules it happens to exercise and no others.  The unit
half below states the three rules that could have gone another way and that the corpus agrees with
only by coincidence of its contents:

  * a port named `reset` is a DRIVEN input, not the `reset` field.  `Prob067_countslow` has one
    and every document it produced left `reset` null, which is the rule and not an oversight — the
    field is for a preamble the trace does not contain, and a reset held by both would be driven
    twice.
  * the clock is matched on a closed list of whole names.  `clk_div` on a clock-dividing design is
    an ordinary input the specification constrains, and a substring rule would take it out of the
    stimulus entirely.
  * a design with no clock port at all yields `clock: null` and loses no input.

`schema.validate_probe` is then run over every derived document, because the pipeline still checks
this file at step 02 and a generator that writes something its own validator rejects is a worse
failure than the pass it replaced.
"""
from __future__ import annotations

import glob
import json
import os
import sys

from common import paths
from . import emit, schema


def _extraction_for(probe_path: str) -> dict | None:
    """The `extraction.json` governing this probe: its own directory, then upwards.

    A round's authored directory holds both.  The copies under `rounds/` and `state/` are
    materialised by the pipeline from the authored pair, so their extraction is a level or two up.
    """
    d = os.path.dirname(probe_path)
    for _ in range(4):
        p = os.path.join(d, "extraction.json")
        if os.path.isfile(p):
            try:
                with open(p) as f:
                    return json.load(f)
            except ValueError:
                return None
        d = os.path.dirname(d)
    return None


def corpus() -> tuple[int, list[str]]:
    """Every recorded `probe.json`, re-derived.  Returns (checked, complaints)."""
    bad: list[str] = []
    n = 0
    root = paths.data(paths.PART1)
    for p in sorted(glob.glob(os.path.join(root, "**", "probe.json"), recursive=True)):
        rel = os.path.relpath(p, root)
        ext = _extraction_for(p)
        if ext is None:
            bad.append(f"{rel}: no extraction.json above it")
            continue
        with open(p) as f:
            want = json.load(f)
        got = emit.probe_document(ext)
        n += 1
        if got != want:
            bad.append(f"{rel}:\n      agent wrote {json.dumps(want)}\n      derived    "
                       f"{json.dumps(got)}")
        for e in schema.validate_probe(got, ext):
            bad.append(f"{rel}: the derived document fails validate_probe — {e}")
    return n, bad


def _ports(*spec: tuple[str, str]) -> dict:
    return {"ports": [{"name": n, "dir": d, "width": "1"} for n, d in spec]}


#: (what it is, the extraction, the document it must produce).
UNITS: list[tuple[str, dict, dict]] = [
    ("a reset PORT stays a driven input and `reset` stays null",
     _ports(("clk", "in"), ("reset", "in"), ("q", "out")),
     {"clock": "clk", "reset": None, "inputs": ["reset"], "outputs": ["q"],
      "sample": "after_edge"}),

    ("`rst_n` is an input like any other",
     _ports(("clk", "in"), ("rst_n", "in"), ("d", "in"), ("q", "out")),
     {"clock": "clk", "reset": None, "inputs": ["rst_n", "d"], "outputs": ["q"],
      "sample": "after_edge"}),

    ("`clk_div` is NOT the clock — a divided clock is a signal the prose constrains",
     _ports(("clk", "in"), ("clk_div", "in"), ("q", "out")),
     {"clock": "clk", "reset": None, "inputs": ["clk_div"], "outputs": ["q"],
      "sample": "after_edge"}),

    ("no clock port: `clock` is null and nothing is dropped",
     _ports(("a", "in"), ("b", "in"), ("y", "out")),
     {"clock": None, "reset": None, "inputs": ["a", "b"], "outputs": ["y"],
      "sample": "after_edge"}),

    ("the clock need not come first, and case does not matter",
     _ports(("d", "in"), ("CLK", "in"), ("q", "out")),
     {"clock": "CLK", "reset": None, "inputs": ["d"], "outputs": ["q"],
      "sample": "after_edge"}),

    ("port order is extraction order, not sorted",
     _ports(("clk", "in"), ("z", "in"), ("a", "in"), ("y2", "out"), ("y1", "out")),
     {"clock": "clk", "reset": None, "inputs": ["z", "a"], "outputs": ["y2", "y1"],
      "sample": "after_edge"}),

    ("an extraction with no ports is a document, not a crash",
     {"ports": []},
     {"clock": None, "reset": None, "inputs": [], "outputs": [], "sample": "after_edge"}),
]


def main() -> int:
    fail = 0
    for what, ext, want in UNITS:
        got = emit.probe_document(ext)
        ok = got == want
        fail += not ok
        print(f"  {'ok  ' if ok else 'BAD '} {what}")
        if not ok:
            print(f"         want {json.dumps(want)}")
            print(f"         got  {json.dumps(got)}")

    n, bad = corpus()
    if not n:
        print("\n  BAD  no probe.json found under data/part1 — the corpus check saw nothing")
        fail += 1
    else:
        print(f"\n  {'BAD ' if bad else 'ok  '} {n} recorded probe.json re-derived from "
              f"extraction.json")
        for b in bad:
            print(f"    {b}")
        fail += len(bad)

    print()
    if fail:
        print(f"probe: {fail} failure(s)")
        return 1
    print(f"probe: all {len(UNITS)} rules and all {n} recorded documents agree")
    return 0


if __name__ == "__main__":
    sys.exit(main())
