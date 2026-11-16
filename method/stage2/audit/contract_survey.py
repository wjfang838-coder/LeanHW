#!/usr/bin/env python3
"""Survey: what port table does `contract.derive` read out of every design's prose?

    audit/contract_survey.py [--bench NAME]... [--key K] [--strict]
                             [--baseline [F]] [--write-baseline] [--quiet]
                             [--against-reference]

## Why

`contracts/<key>.json` is BINDING.  The two authors of a design are aligned through those port
names and widths and through nothing else, and the emitted module header is built from them.  A
port table that is wrong is not a degraded run, it is a void one — and it does not announce
itself: the design goes on to spend a full authoring session, and the failure surfaces at the
oracle as `compile_fail` or `func_fail`, which reads as a bad design rather than as "the method
never understood the spec".

`contract.derive` is a pure function of `(prose, key, toplevel)`, so the whole port table can be
recomputed for every installed design in a few seconds without staging a workspace, spending an
authoring session, or writing anything.  That is what this does.  It is the feedback loop for
editing the readers in `leanrtl/contract.py` and `leanrtl/authoring/iface_gate.py`: snapshot
before, edit, snapshot after, read the diff.

## `leanrtl/` MUST NOT IMPORT THIS FILE

Sharper here than the ordinary rule that keeps experiment code out of the method.  This file
imports `common.adapter` and reads dataset directories.  If `contract.py` could import it, the
one module whose entire doctrine is *the prose alone* would acquire a live import path to the
answer key.  The dependency runs one way: audit reads the method, never the reverse.

## Why losing a port fails and gaining one does not

`--strict` exits 3 for a design that lost a port against the baseline, or for a NEW design that
reads zero ports.  It does not fail on gains.  That asymmetry is `_is_other_head`'s error-direction
argument expressed as an exit code: mistaking a heading for a port adds one bogus entry that the
caller can see and argue with, while mistaking a port for a heading silently drops it and every
port after it.  A reader edit that only adds names is safe to land and read afterwards; one that
drops a name has to be justified name by name.

Zero installed benchmarks exits **2**, not 0 — a survey that reports success having looked at
nothing is the failure mode this directory exists to prevent.
"""
import argparse, json, os, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

DEFAULT_BASELINE = os.path.join(ROOT, "audit", "CONTRACT_BASELINE.json")

#: A design's spec file, with this replaced by `_ref.sv`, is the golden implementation — for the
#: two benchmarks that store them side by side.  Used ONLY by `--against-reference`.
_SPEC_SUFFIXES = ("_prompt.txt", ".spec.txt", ".txt")


def survey(designs):
    """`{bench/key: {module, ports, undetermined, conflicts}}`, derived from the prose alone."""
    from leanrtl import contract
    out = {}
    for d in designs:
        ident = f"{d.bench}/{d.key}"
        try:
            prose = open(d.spec_path, encoding="utf-8", errors="replace").read()
        except OSError as e:
            out[ident] = {"error": f"unreadable spec: {e}"}
            continue
        try:
            c = contract.derive(prose, d.key, d.toplevel)
        except Exception as e:                                   # a parse crash is a finding
            out[ident] = {"error": f"{type(e).__name__}: {e}"}
            continue
        out[ident] = {
            "module": c.get("module"),
            "ports": [{"name": p.get("name"), "dir": p.get("dir"), "width": p.get("width")}
                      for p in (c.get("ports") or [])],
            "undetermined": [f"{u.get('name')}:{u.get('what')}" for u in (c.get("undetermined") or [])],
            "conflicts": sorted(c.get("conflicts") or []),
        }
    return out


def diff(before, after):
    """Per-design GAIN/LOST/MODULE changes.  Returns `(changes, lost_any, new_zero)`."""
    changes, lost_any, new_zero = {}, [], []
    for ident in sorted(set(before) | set(after)):
        b, a = before.get(ident), after.get(ident)
        if b is None:
            if a and not a.get("error") and not a.get("ports"):
                new_zero.append(ident)
            continue
        if a is None:
            continue
        bn = [p["name"] for p in b.get("ports", [])]
        an = [p["name"] for p in a.get("ports", [])]
        lost, gained = [n for n in bn if n not in an], [n for n in an if n not in bn]
        mod = (b.get("module"), a.get("module"))
        if not (lost or gained) and mod[0] == mod[1]:
            continue
        changes[ident] = {"lost": lost, "gained": gained,
                          "module": None if mod[0] == mod[1] else mod}
        if lost:
            lost_any.append(ident)
        if bn and not an:
            new_zero.append(ident)
    return changes, lost_any, new_zero


def against_reference(designs, rows):
    """DEVELOPER DIAGNOSTIC ONLY — compares the derived table to the golden `_ref.sv` header.

    This reads the answer key.  It exists because it is by far the fastest way to see WHICH port a
    reader edit is still getting wrong, and it is fenced so that it can never influence anything
    but a human's next edit:

      * it lives in `audit/`, which no code path reachable from `pipeline.py` imports;
      * `contract.derive` takes no argument through which a reference could reach it;
      * it is an explicit command-line flag with no config-file or environment equivalent, so
        "did this run look at the answer key" is answerable from the shell history alone;
      * it prints, and returns nothing — it writes no contract, touches no workspace, and does
        not contribute to the exit code.

    The `how` line every contract carries — "no testbench, reference implementation or dataset
    file was read" — stays literally true of `derive`, which is the thing that never sees this.
    """
    from leanrtl.authoring import iface_gate
    print("\n--- against reference (DEVELOPER DIAGNOSTIC — this reads the answer key) ---")
    for d in designs:
        ident = f"{d.bench}/{d.key}"
        ref = None
        for suf in _SPEC_SUFFIXES:
            if d.spec_path.endswith(suf):
                cand = d.spec_path[: -len(suf)] + "_ref.sv"
                if os.path.isfile(cand):
                    ref = cand
                break
        if not ref:
            print(f"  {ident}: no reference located beside the spec")
            continue
        try:
            # `emitted_iface` reports ports as bare names, `derive` as dicts — normalise both.
            gold = {p["name"] if isinstance(p, dict) else p
                    for p in (iface_gate.emitted_iface(ref).get("ports") or ())}
        except Exception as e:
            print(f"  {ident}: reference unreadable ({type(e).__name__}: {e})")
            continue
        got = {p["name"] for p in rows.get(ident, {}).get("ports", [])}
        missing, extra = sorted(gold - got), sorted(got - gold)
        if not missing and not extra:
            print(f"  {ident}: OK ({len(got)})")
        else:
            print(f"  {ident}: MISSING {missing or '-'}  EXTRA {extra or '-'}")


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bench", action="append", metavar="NAME",
                    help="repeatable; default is every benchmark under the dataset root")
    ap.add_argument("--key", help="survey one design only")
    ap.add_argument("--strict", action="store_true",
                    help="exit 3 if any design LOST a port against the baseline, or newly "
                         "reads zero ports.  Gains never fail.")
    ap.add_argument("--baseline", nargs="?", const=DEFAULT_BASELINE,
                    help="compare against this snapshot (default: %s)"
                         % os.path.relpath(DEFAULT_BASELINE, ROOT))
    ap.add_argument("--write-baseline", action="store_true",
                    help="rewrite the snapshot from what is derived now")
    ap.add_argument("--quiet", action="store_true", help="totals and diff only, no per-design lines")
    ap.add_argument("--against-reference", action="store_true",
                    help="DEVELOPER DIAGNOSTIC: also print the derived table against the golden "
                         "_ref.sv header.  Reads the answer key; prints only; never affects the "
                         "exit code or any written file.")
    a = ap.parse_args()

    from common import adapter
    names = a.bench or adapter.installed()
    designs = []
    for b in names:
        try:
            designs.extend(adapter.load(b).designs())
        except Exception as e:
            print(f"contract_survey: cannot load benchmark {b!r}: {e}", file=sys.stderr)
    if a.key:
        designs = [d for d in designs if d.key == a.key]
    if not designs:
        print(f"contract_survey: nothing to survey under {adapter.BENCH_DIR} "
              f"(this is NOT a pass)")
        return 2

    rows = survey(designs)

    if a.write_baseline:
        p = a.baseline or DEFAULT_BASELINE
        json.dump({"_note": "Port tables derived from prose by leanrtl/contract.py, snapshotted "
                            "by audit/contract_survey.py. A commit that REMOVES a port name here "
                            "has to justify it name by name — that is the review signal.",
                   "designs": rows}, open(p, "w"), indent=1, sort_keys=True)
        print(f"contract_survey: wrote {len(rows)} designs to {os.path.relpath(p, ROOT)}")
        return 0

    by_bench = {}
    for ident, r in sorted(rows.items()):
        b = ident.split("/", 1)[0]
        t = by_bench.setdefault(b, {"n": 0, "zero": 0, "undet": 0, "confl": 0, "err": 0})
        t["n"] += 1
        if r.get("error"):
            t["err"] += 1
            if not a.quiet:
                print(f"  {ident}: ERROR {r['error']}")
            continue
        ports = r["ports"]
        if not ports:
            t["zero"] += 1
        if r["undetermined"]:
            t["undet"] += 1
        if r["conflicts"]:
            t["confl"] += 1
        if not a.quiet:
            tags = ""
            if r["undetermined"]:
                tags += f"  [UNDET {len(r['undetermined'])}]"
            if r["conflicts"]:
                tags += f"  [CONFLICT {len(r['conflicts'])}]"
            mark = "ZERO " if not ports else "     "
            print(f"  {mark}{ident}  module={r['module']}  n={len(ports)}{tags}\n"
                  f"        {', '.join(p['name'] for p in ports)}")

    print()
    for b, t in sorted(by_bench.items()):
        print(f"contract_survey: {b:<14} designs={t['n']:>4}  zero-port={t['zero']:>3}  "
              f"undetermined={t['undet']:>3}  conflicts={t['confl']:>3}  errors={t['err']:>3}")

    rc = 0
    if a.baseline and os.path.exists(a.baseline):
        before = json.load(open(a.baseline))["designs"]
        changes, lost_any, new_zero = diff(before, rows)
        n_lost = sum(len(c["lost"]) for c in changes.values())
        n_gain = sum(len(c["gained"]) for c in changes.values())
        print(f"\n  baseline {os.path.relpath(a.baseline, ROOT)}: "
              f"{len(changes)} design(s) changed · {n_lost} name(s) LOST · {n_gain} gained")
        for ident, c in sorted(changes.items()):
            if c["module"]:
                print(f"  MODULE {ident}: {c['module'][0]} -> {c['module'][1]}")
            if c["lost"]:
                print(f"  LOST   {ident}: {', '.join(c['lost'])}")
            if c["gained"]:
                print(f"  GAIN   {ident}: {', '.join(c['gained'])}")
        for ident in new_zero:
            print(f"  NEW ZERO-PORT  {ident}")
        if a.strict and (lost_any or new_zero):
            rc = 3
    elif a.baseline:
        print(f"\n  baseline {os.path.relpath(a.baseline, ROOT)} does not exist "
              f"— run --write-baseline first")

    if a.against_reference:
        against_reference(designs, rows)
    return rc


if __name__ == "__main__":
    sys.exit(main())
