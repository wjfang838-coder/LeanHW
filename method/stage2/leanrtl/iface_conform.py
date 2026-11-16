#!/usr/bin/env python3
"""Interface conformance: does the emitted module header match the interface the PROSE declares?

    python3 -m leanrtl.iface_conform --ws ../data/part2/rtllm/accu/decided [--key K] [--json OUT]

A design can die before a single vector is applied, with the simulator raising
`AttributeError: <top> contains no child object named X` — the testbench reached for a port or a
parameter the emitted module does not have.  Every one of those names is declared in the design's
own prose.  Nothing about that failure needs a simulator to find: it is a set difference between
two lists we already hold.  On one benchmark round it was seven of twenty-two failures.

This check reads ONLY the prose and our own emitted Verilog.  It never opens the testbench.  That
matters — on a benchmark with no reference RTL the testbench is the entire ground truth, so a
check that consulted it would be scoring against the answer key, and any repair it motivated
would be untraceable to the specification.  Everything reported here is derivable from the task
statement alone, which is exactly what the authoring agent was given.

## Where a declared interface hides in prose

Four shapes, in descending order of authority:

  1. a fenced ```verilog / ```SystemVerilog block holding a `module ... (...);` header --
     the spec writing the interface out as code;
  2. a markdown table with a direction column (`| clk | 1 bit | input | System clock |`);
  3. bulleted declarations under an Interface/Inputs/Outputs/Ports/Signals heading
     (`- **`awaddr_i`**: Address for write operations.`, possibly carrying a `[W-1:0]` prefix);
  4. a Parameters section naming SCREAMING_CASE identifiers.

A design may use several, and when they DISAGREE that is itself a finding.  One real case named
its slave-ready pin one thing in the signal table and another eleven lines later in the module
skeleton; both arms followed the skeleton, and the testbench followed the table.  A checker that
silently picked one would have hidden the defect, so the disagreement is reported as
`prose_self_conflict` and neither reading is called wrong.

That case is also the cleanest argument for the half of leanSilicon that reads prose: the
contradiction is in the document, it is mechanically findable, and nobody had to run anything to
know that one of the two readings was going to lose.

## What a finding does and does not mean

`missing_port` / `missing_param` says the prose declares a name the emitted header does not
carry.  Where a harness probes by name that is very close to fatal, but the check is a
*predictor*, not a verdict.  `extra_port` is much weaker evidence, since prose routinely omits a
clock it mentions only in passing, and it is reported separately so it cannot inflate the
headline.

## A parameter can be present and still be a lie: `inert_param`

`missing_param` asks whether the name is DECLARED.  That is the wrong question on its own, and
answering only it hid the larger defect for a whole round.

The extraction route emits every module in the NON-ANSI style — a bare port list, then
`parameter DATA_WIDTH = 16;` after the `);`.  The header regex only ever read the ANSI `#(...)`
form, so `emitted_params` came back EMPTY for all 78 designs of that arm while the direct-Verilog
control, which writes ANSI headers, parsed clean.  Every `missing_param` reported against the
first arm was therefore a parser artifact, and the 12-vs-0 arm split it produced was written up
as a property of the extraction route.  It was a property of this file.

The real defect is worse, and it is what the split was standing in front of.  A design declares
`DATA_WIDTH = 16` and `NUM_TAPS = 8`, and then writes `input [127:0] data_in` — the product, as a
literal.  The parameter is a decoration: elaborate the module with `NUM_TAPS = 10` and it still
expects 128 bits.  Seventeen designs carried at least one such parameter.

So `inert_param` reports a parameter the module declares and never reads.  Three things make it
worth more than `missing_param`:

  * it is a property of ONE file — our own emitted Verilog.  It needs no prose, no testbench and
    no reference, so no repair it motivates can be fitting to the answer key;
  * a declared-but-inert parameter is invisible to every other gate.  It elaborates, it
    synthesises, it has no undriven net, and a proof about the fixed-width module is perfectly
    true of the fixed-width module.  Nothing else in the pipeline is looking at it;
  * it predicts the failure that actually happened.  Of the 17, the 11 whose harness elaborates
    at a width other than the baked-in one all failed; of the 3 whose harness sets no parameter
    at all, 2 passed.  The defect fires exactly when it is exercised.

A reference inside another parameter's initialiser counts as a use.  That over-approximates
"used" — `parameter A = 1; parameter B = A;` calls A live even when B is itself inert — and
over-approximating is the safe direction for a predictor whose whole value is that a flag means
something.
"""
from __future__ import annotations

import argparse
import json
import os
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

# The extraction lives in `leanrtl/authoring/iface_gate.py` rather than here, because `bb.py emit` runs
# the SAME check during authoring, where a mismatch is still cheap to fix.  Two copies would
# drift, and this file's findings carry a published hit rate, so the authoring loop imports the
# post-hoc implementation rather than getting a second one of its own.
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "authoring"))
from iface_gate import prose_iface, emitted_iface                            # noqa: E402


def check(ws: str, key: str) -> dict:
    spec = os.path.join(ws, "specs", key + ".spec.txt")
    vpath = os.path.join(ws, "out", key + ".v")
    if not (os.path.isfile(spec) and os.path.isfile(vpath)):
        return {"key": key, "skipped": "no spec or no emitted verilog"}
    e = emitted_iface(vpath)
    p = prose_iface(open(spec, errors="replace").read(), e["module"])
    missing_port = sorted(p["ports"] - e["ports"])
    missing_param = sorted(p["params"] - e["params"])
    extra_port = sorted(e["ports"] - p["ports"])
    return {"key": key, "module": e["module"],
            "missing_port": missing_port, "missing_param": missing_param,
            "extra_port": extra_port, "prose_self_conflict": p["self_conflict"],
            "flag": bool(missing_port or missing_param),
            # A `flag: false` from a prose the believed sources yielded NOTHING from is not this
            # check passing -- it is this check having had nothing to compare against.  The two
            # look identical in the output, and the second one is the common case on a benchmark
            # whose specs declare their pins as an indented list under a plain `Input ports:` line
            # rather than as a code header or a direction table.  Every RTLLM design reads that
            # way, so `flag` is false for all of them for a reason that is about this parser.
            #
            # Reported as its own field rather than folded into `flag`, for the same reason
            # `flag_inert` is: `flag` is the presence question and has a published hit rate, and a
            # number that silently changes meaning is worse than one that is narrow.
            "vacuous": not (p["ports"] or p["params"]),
            "inert_param": sorted(e["inert_params"]),
            "flag_inert": bool(e["inert_params"]),
            "prose_ports": sorted(p["ports"]), "prose_params": sorted(p["params"]),
            "emitted_ports": sorted(e["ports"]), "emitted_params": sorted(e["params"]),
            "by_source": p["by_source"]}


def report(r: dict) -> str:
    if "skipped" in r:
        return f"iface_conform: {r['key']} — {r['skipped']}"
    L = [f"interface conformance · {r['key']} · module `{r['module']}`"]
    if r.get("vacuous"):
        L.append("  NOTHING COMPARED — the believed sources (a code header, a direction table, a "
                 "direction-led\n    declaration list) found no interface in this prose, so every "
                 "name below is `extra` by\n    default and no absence could have been detected.  "
                 "This is not a pass.")
        # The unflagged reading is not evidence of the same kind and never sets `flag`, but
        # where it is the ONLY reading available, saying nothing about it reports less than is
        # known.  It is printed as what it is: a weaker source, named, with its verdict spelled
        # out rather than folded into the headline.
        bul = (r.get("by_source") or {}).get("bullet_unflagged") or []
        if bul:
            miss = sorted(set(bul) - set(r["emitted_ports"]))
            L.append("    The unflagged reading (an indented or bulleted declaration list) does "
                     "name " + ", ".join(bul) + ".")
            L.append("    Against the emitted header that is "
                     + ("an exact match" if not miss and
                        set(bul) == set(r["emitted_ports"]) else
                        ("a MISS on " + ", ".join(miss)) if miss else "a subset, with no absence")
                     + " — weaker evidence, and not counted in `flag`.")
    if r["missing_port"]:
        L.append("  MISSING PORT   " + ", ".join(r["missing_port"]))
    if r["missing_param"]:
        L.append("  MISSING PARAM  " + ", ".join(r["missing_param"]))
    if r["extra_port"]:
        L.append("  extra port     " + ", ".join(r["extra_port"])
                 + "   (weak: prose routinely omits a clock it mentions in passing)")
    if r["prose_self_conflict"]:
        L.append("  PROSE CONTRADICTS ITSELF (table vs code header): "
                 + ", ".join(r["prose_self_conflict"])
                 + "\n    Neither reading is called wrong here.  This is a defect in the "
                   "document, not in the module.")
    if r["inert_param"]:
        L.append("  INERT PARAM    " + ", ".join(r["inert_param"])
                 + "\n    Declared by the module and never read: elaborating it at another "
                   "value changes nothing.")
    if len(L) == 1:
        L.append("  clean — every name the prose declares is on the emitted header, and every "
                 "declared parameter is read")
    return "\n".join(L)


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ws", required=True)
    ap.add_argument("--key", help="default: the key in the workspace's provenance stamp")
    ap.add_argument("--json")
    ap.add_argument("--strict", action="store_true",
                    help="exit 3 when a declared port or parameter is missing")
    a = ap.parse_args(argv)
    ws = os.path.abspath(os.path.expanduser(a.ws))

    key = a.key
    if not key:
        from common import provenance                                        # noqa: E402
        key = (provenance.read(ws) or {}).get("key")
        if not key:
            sys.exit("iface_conform: no --key, and this workspace has no provenance stamp to "
                     "take one from")

    r = check(ws, key)
    print(report(r))

    dest = a.json or os.path.join(ws, "out", "iface_conform.json")
    os.makedirs(os.path.dirname(os.path.abspath(dest)), exist_ok=True)
    json.dump(r, open(dest, "w"), indent=1)
    print(f"wrote {dest}")
    return 3 if (a.strict and r.get("flag")) else 0


if __name__ == "__main__":
    sys.exit(main())
