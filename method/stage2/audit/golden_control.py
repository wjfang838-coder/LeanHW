#!/usr/bin/env python3
"""The golden control: push every design's OWN reference through its OWN checker.

    python3 audit/golden_control.py --bench verilogeval
    python3 audit/golden_control.py --bench verilogeval --write

`Adapter.golden_source` renames `RefModule` to `TopModule` in a copy of the benchmark's reference
so the benchmark's own answer can occupy the candidate slot.  The verilogeval adapter has carried
that method, and the docstring explaining why it makes `known_defects()` "falsifiable rather than
folklore", since it was written -- and nothing has ever called it.  That is the same state
`Adapter.score` was in before `leanrtl/score.py`: a channel that exists, is documented, and has
never once produced a number.  So "the benchmark can grade this design" was an assumption, not a
measurement, on all 156 of them.

## What a failing golden run does and does not establish

A reference compared against itself is a tautology *on the comparison* -- of course the two agree
-- but it is not a tautology on elaboration, on the stimulus generator, or on the testbench's own
timeout.  Those are exactly where the failures turn out to be:

  * `Prob099_m2014_q6c` -- the checker connects `.Y2()` and `.Y4()` to both slots.  The prompt
    asks for `Y1`/`Y3` and the reference implements `Y1`/`Y3`.  The testbench is the one from a
    different variant of the problem, and *nothing* compiles against it, the reference included.
  * `Prob082_lfsr32`, `Prob141_count_clock`, `Prob156_review2015_fancytimer` -- the testbench
    carries `initial #1000000 $display("TIMEOUT"); $finish;` and its own stimulus loop runs past
    that wall.  `TIMEOUT` therefore fires for every candidate ever submitted, the reference
    included, and `_read` -- correctly, and for good reasons written down beside it -- refuses to
    read a truncated sample as a pass.  The refusal is right; what was missing is the control that
    says the truncation is the benchmark's and not the candidate's.

So this control separates "we got it wrong" from "nobody can get it right", and it does so with a
reproducible command rather than with a reading of the prompt.

## What it deliberately does NOT establish

`spec-contradicts-reference` -- a prompt whose text disagrees with the reference it is graded
against -- is invisible here, because the reference always agrees with itself.  Those entries can
only be earned by reading both and demonstrating the disagreement, so this driver never writes
one, and `--write` preserves any that a human put in the file.  Four are known on verilogeval
today and none of them is in this control's output:

  * `Prob031_dff`        -- the interface block declares `- input q`; `q` is the output.
  * `Prob062_bugs_mux2`  -- the quoted buggy module's only stated defect is the width of `out`,
                            and the reference also flips the mux polarity (`sel ? a : b` against
                            the prompt's `(~sel & a) | (sel & b)`, which is `sel ? b : a`).
                            Width-only repair scores 85/114.
  * `Prob093_ece241_2014_q3` -- the reference disagrees with the K-map printed in its own prompt
                            at (cd=11, ab=10): the map says 1, `mux_in[2] = ~d` gives 0.
                            A K-map-literal implementation scores 11/60.
  * `Prob149_ece241_2013_q4` -- the prose opens the supplemental valve when "the previous level
                            was lower than the current level" (a rise); the reference asserts
                            `dfr` in `B2`/`C2`, which are reachable only by falling.

These are `unwinnable=False` on purpose: a candidate CAN pass them, by guessing against the prose.
They stay in the denominator.  Only what this control establishes comes out of it.
"""
from __future__ import annotations

import argparse
import json
import os
import sys
import tempfile

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))
from common import adapter as adapter_mod          # noqa: E402

#: Statuses that mean the golden reference did not clear its own checker.  `no_verdict` is here
#: because a checker that reaches its verdict line having sampled nothing has graded nothing.
BAD = ("compile_fail", "func_fail", "timeout", "no_verdict", "sim_error", "harness_error")

#: What the control saw -> the `Defect.kind` it earns.  A reference that does not compile means
#: the testbench cannot instantiate what the dataset ships; anything else means the reference ran
#: and still did not pass.
KIND = {"compile_fail": "broken-testbench"}
DEFAULT_KIND = "reference-fails-own-testbench"

#: Kinds this control cannot establish.  `--write` carries existing entries of these kinds
#: through untouched rather than dropping them -- see the module docstring.
NOT_OURS = ("spec-contradicts-reference", "oracle-artifact")


def run_one(ad, d) -> tuple[str, object]:
    """Score the design's own reference in the candidate slot.  Returns (status, Verdict|None)."""
    src = ad.golden_source(d)
    if src is None:
        return "declined", None
    with tempfile.TemporaryDirectory(prefix=f"golden-{d.key}-") as wd:
        p = os.path.join(wd, "golden.sv")
        open(p, "w").write(src)
        v = ad.score(d, p)
    return v.status, v


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("--bench", required=True)
    ap.add_argument("--only", help="comma-separated keys")
    ap.add_argument("--write", action="store_true",
                    help="write KNOWN_DEFECTS.json beside the adapter from what this run found")
    a = ap.parse_args(argv)

    ad = adapter_mod.load(a.bench)
    designs = ad.designs()
    if a.only:
        want = set(a.only.split(","))
        designs = [d for d in designs if d.key in want]

    rows, failed = [], []
    for i, d in enumerate(designs, 1):
        st, v = run_one(ad, d)
        rows.append((d.key, st))
        mark = "ok " if st == "func_pass" else "BAD"
        print(f"[{i:3}/{len(designs)}] {mark} {d.key:32} {st}")
        if st in BAD:
            failed.append((d, st, v))

    print(f"\ngolden control · {a.bench} · oracle {ad.oracle}")
    print(f"  designs        {len(designs)}")
    print(f"  reference passes its own checker   {sum(1 for _, s in rows if s == 'func_pass')}")
    print(f"  reference FAILS its own checker    {len(failed)}")
    for d, st, _ in failed:
        print(f"      {d.key:34} {st}")

    if not a.write:
        if failed:
            print("\n  --write to record these in KNOWN_DEFECTS.json")
        return 0

    path = os.path.join(os.path.dirname(ad._module_file()), "KNOWN_DEFECTS.json")
    old = {}
    if os.path.isfile(path):
        old = {x["key"]: x for x in json.load(open(path))["defects"]}
    # Entries this control cannot speak to survive verbatim; entries it CAN speak to are rewritten
    # from what it just measured, so a stale `unwinnable` cannot outlive the measurement that set
    # it.  A key it no longer finds bad, and whose old entry was ours, is dropped -- silently
    # keeping it would be inheriting a conclusion instead of re-earning it.
    kept = {k: x for k, x in old.items() if x.get("kind") in NOT_OURS}
    dropped = [k for k, x in old.items()
               if x.get("kind") not in NOT_OURS
               and k not in {d.key for d, _, _ in failed}]
    out = dict(kept)
    for d, st, v in failed:
        ev = (f"python3 audit/golden_control.py --bench {a.bench} --only {d.key} "
              f"-> {st}. The benchmark's own reference, renamed into the candidate slot by "
              f"Adapter.golden_source, scored `{st}` against the benchmark's own testbench.")
        detail = (getattr(v, "detail", "") or "").strip()
        if detail:
            ev += "  Checker said: " + " ".join(detail.split())[:300]
        out[d.key] = {
            "key": d.key,
            "kind": KIND.get(st, DEFAULT_KIND),
            "summary": f"the reference scores `{st}` against this design's own testbench",
            "evidence": ev,
            "unwinnable": True,
            "arms_affected": "both",
            "oracle": ad.oracle,
            "reaudit": "",
        }
    body = {
        "bench": a.bench,
        "dataset_id": ad.dataset_id(),
        "note": ("Written by audit/golden_control.py.  Entries of kind "
                 + "/".join(NOT_OURS) + " are hand-authored and are preserved, not produced, "
                 "by that driver -- see its module docstring."),
        "defects": [out[k] for k in sorted(out)],
    }
    json.dump(body, open(path, "w"), indent=1)
    print(f"\n  wrote {path}  ({len(out)} entries: {len(failed)} from this control, "
          f"{len(kept)} preserved)")
    if dropped:
        print(f"  DROPPED (this control no longer finds them bad): {', '.join(sorted(dropped))}")
    return 0


if __name__ == "__main__":
    sys.exit(main())
