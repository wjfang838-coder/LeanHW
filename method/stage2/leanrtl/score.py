#!/usr/bin/env python3
"""Push an arm's emitted Verilog through the benchmark's own oracle and write down what it said.

    python3 -m leanrtl.score --key accu --all
    python3 -m leanrtl.score --key Prob067_countslow --arm decided
    python3 -m leanrtl.score --key accu --all --preproof     # …and the pre-proof artifact too

## Why this is a separate file, and not part of `launch`

`launch` runs arms and refuses to score them, on purpose — its own docstring says so: an
orchestrator that also scores is an orchestrator with an experimental design baked into it, and
the two then cannot be separated.  This is that scoring step, kept apart under the same rule as
`compare.py`: it is experiment code, and **nothing under `leanrtl/` may import it.**

Which leaves a gap that had gone unnoticed until a second benchmark arrived.  `Adapter.score`
existed, every adapter implemented it, and *nothing in the repository called it*.  The one design
that had been run end to end was judged by hand.  So the benchmark socket's scoring channel was in
exactly the state its defect channel was in — written, documented, and never once exercised — and
"the framework produces a benchmark verdict" was an assertion about code that had never run.

## What it does not do

It does not aggregate, does not compare arms, and does not compute a pass rate.  One workspace in,
one verdict out, one file written beside the artifact it judges.  Aggregation across arms or
designs is a claim about an experiment, and it belongs to whoever is running one.

It also does not decide whether a failure is the method's fault.  A `func_fail` here is the
oracle's report, not a verdict on the author; a design the benchmark itself cannot grade is what
`known_defects()` is for, and if the key appears there it is printed alongside rather than folded
into the status.

## The verdict is written next to the artifact, and names what it judged

`out/<key>.verdict.json` for the certified Verilog, `out/<key>.preproof.verdict.json` for the one
emitted before the proof phase.  Two files, never one, because they are answers to different
questions — "does the certified design pass" and "did it already pass before it was proved" — and
a single file would silently become whichever was written last.

Each records the oracle, the adapter's `dataset_id()` fingerprint and the artifact's own sha256.
A verdict that does not say which simulator, which dataset bytes and which file produced it is a
claim that cannot be checked later, and this repository has already been bitten once by a stored
result whose oracle was implicit.

## Finding the workspaces

This addresses `data/part2/<bench>/<key>/` directly and lists the arms in it, rather than walking
every benchmark the way `compare.discover` does.  That is not an oversight and the two are not
redundant: `compare` takes a key with no adapter in hand and must tolerate a workspace filed under
the wrong benchmark, so it looks everywhere and lets `out/<key>.v` be the evidence.  Scoring
cannot do that even in principle — it needs an adapter to judge with, so it must already have
committed to a benchmark, and a workspace filed under a different one is a workspace this file
would be judging with the wrong oracle.  Narrower is correct here, not lazier.
"""
from __future__ import annotations

import argparse
import dataclasses
import datetime
import hashlib
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

from common import adapter, paths                                          # noqa: E402
from leanrtl import preproof                                               # noqa: E402


def arms_for(bench: str, key: str) -> list[str]:
    """Arm directories under `data/part2/<bench>/<key>/`, in a stable order.

    `bak/` is skipped by name — see `paths.BAK`; everything that is not a reported arm lives in
    there.  An arm with no emitted Verilog is still returned, because "this arm emitted nothing"
    is a result the table should be able to show rather than a row that quietly disappears.
    """
    d = paths.part2(bench, key)
    if not os.path.isdir(d):
        return []
    return [os.path.join(d, a) for a in sorted(os.listdir(d))
            if a != paths.BAK and os.path.isdir(os.path.join(d, a))]


def _sha(p: str) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 16), b""):
            h.update(b)
    return h.hexdigest()


def score_one(ad, design, ws: str, key: str, artifact: str = "final") -> dict:
    """Judge one artifact of one workspace and write its verdict beside it.

    Returns the record that was written.  The artifact is named in the record and in the filename,
    so a pre-proof verdict can never be read as the certified one — the failure mode `compare.py`
    guards against on its own table, in the direction that flatters.
    """
    pre = artifact == preproof.TAG
    name = f"{key}.{preproof.TAG}.v" if pre else f"{key}.v"
    vpath = os.path.join(ws, "out", name)
    v = ad.score(design, vpath)
    rec = dataclasses.asdict(v)
    rec.update({
        "artifact": preproof.TAG if pre else "final",
        "verilog": os.path.join(os.path.basename(ws), "out", name),
        "verilog_sha256": _sha(vpath) if os.path.isfile(vpath) else None,
        "bench": design.bench,
        "toplevel": design.toplevel,
        "arm": os.path.basename(ws),
        "dataset_id": ad.dataset_id(),
        "adapter": os.path.relpath(ad._module_file(), paths.REPO),
        "scored_at": datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
    })
    # The per-design hash table is the useful half of `dataset_id` here and the bulky half is
    # not: 156 entries of somebody else's designs in every verdict file is noise that makes the
    # one line a reader wants harder to find.  The design's own entry is kept.
    per = (rec["dataset_id"] or {}).pop("per_design", {}) or {}
    if design.key in per:
        rec["dataset_id"]["this_design"] = per[design.key]
    out = os.path.join(ws, "out",
                       f"{key}.{preproof.TAG}.verdict.json" if pre else f"{key}.verdict.json")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    with open(out, "w") as f:
        json.dump(rec, f, indent=1, default=str)
    rec["_path"] = out
    return rec


def line(rec: dict) -> str:
    e = rec.get("extra") or {}
    bits = []
    if "mismatches" in e:
        bits.append(f"{e['mismatches']}/{e.get('samples', '?')} mismatched")
    if rec.get("bridges"):
        bits.append("bridges: " + ",".join(rec["bridges"]))
    if e.get("subset"):
        bits.append(e["subset"])
    return (f"  {rec['arm']:<10} {rec['artifact']:<9} {rec['status']:<14} "
            f"oracle={rec['oracle']:<8} " + ("· " + " · ".join(bits) if bits else ""))


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--key", required=True)
    ap.add_argument("--bench", default="", help="inferred from --key when omitted")
    ap.add_argument("--all", action="store_true", help="every arm of this design")
    ap.add_argument("--arm", default="", help="one arm, by directory name")
    ap.add_argument("--preproof", action="store_true",
                    help="also judge the Verilog emitted BEFORE the proof phase, and write its "
                         "verdict to a separate file")
    a = ap.parse_args(argv)

    bench = a.bench or adapter.bench_for_key(a.key)
    if not bench:
        # Without a benchmark there is no oracle, and there is no sensible default: judging with
        # some other corpus's testbench would produce a verdict-shaped object that means nothing.
        print(f"score: no installed benchmark claims the key {a.key!r}, so there is no oracle to "
              f"judge it with.  Pass --bench if you know which one it is.\n"
              f"       installed: {', '.join(adapter.installed()) or '—'}", file=sys.stderr)
        return 2
    try:
        ad = adapter.load(bench)
    except Exception as e:                                              # noqa: BLE001
        print(f"score: could not load {bench}'s adapter: {type(e).__name__}: {e}", file=sys.stderr)
        return 2
    design = ad.design_map().get(a.key)
    if design is None:
        print(f"score: {bench} has no design named {a.key!r}", file=sys.stderr)
        return 2

    wss = arms_for(bench, a.key)
    if a.arm:
        wss = [w for w in wss if os.path.basename(w) == a.arm]
    elif not a.all:
        print("score: name an arm with --arm, or pass --all", file=sys.stderr)
        return 2
    if not wss:
        print(f"score: no workspace under {os.path.relpath(paths.part2(bench, a.key), paths.REPO)}"
              + (f" named {a.arm!r}" if a.arm else ""), file=sys.stderr)
        return 2

    defect = ad.known_defects().get(a.key)
    print(f"score: {a.key} · {bench} · oracle {ad.oracle} · toplevel {design.toplevel} · "
          f"{len(wss)} arm(s)")
    if defect:
        # Printed, never folded into the status.  A benchmark defect is a fact about the
        # BENCHMARK, and silently rewriting a `func_fail` into `unwinnable` would hide the one
        # thing a reader needs to weigh for themselves.
        print(f"  KNOWN DEFECT ({defect.kind}, unwinnable={defect.unwinnable}, "
              f"judged under {defect.oracle or '?'}): {defect.summary}")

    recs = []
    for ws in wss:
        for art in ((preproof.TAG,) if a.preproof else ()) + ("final",):
            rec = score_one(ad, design, ws, a.key, art)
            recs.append(rec)
            print(line(rec))
            if rec.get("detail") and rec["status"] not in ("func_pass",):
                print("      " + rec["detail"].strip().replace("\n", "\n      ")[:600])
    for rec in recs:
        print(f"  written: {os.path.relpath(rec['_path'], paths.REPO)}")
    # Non-zero when any CERTIFIED artifact did not pass.  A pre-proof row that fails is a finding,
    # not an error: an implementation that only became correct during the proof phase is exactly
    # what the pre-proof artifact exists to make visible.
    return 0 if all(r["func_pass"] for r in recs if r["artifact"] == "final") else 3


if __name__ == "__main__":
    sys.exit(main())
