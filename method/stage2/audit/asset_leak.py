#!/usr/bin/env python3
"""Gate: no benchmark design name may appear in the assets a workspace receives.

    audit/asset_leak.py [--assets DIR | --ws DIR] [--strict] [--baseline F] [--write-baseline]

## Why

Accumulated assets get GROWN FROM the benchmarks one tests on, so a lemma's docstring naturally
says "this one came from design X" — and sometimes says more than the name: a register count, a
modulus, a state encoding.  A sanitiser existed but was written against one benchmark's design
list, so a second benchmark's names survived untouched for months.

Two leakage levels, both flagged, severity distinguished:
  * NAME   — the design is named.  Tells an author the design exists and roughly what proof
             shape it needed.
  * ANSWER — the name appears next to a number or an encoding.  That is the thing the spec was
             supposed to be tested on.

## Two modes, because a shared asset tree can already be contaminated

Sanitisation happens at stage time, so a mention in `assets/` today is not a build break.  What
must never happen is a *new* one.

  * over `assets/`, with `--baseline` — fails only on names not already recorded.  Prose written
    *about* a leak is not exempt: twice in one day the leak was introduced by someone
    documenting why the rule exists.
  * over a staged `data/part2/<bench>/<key>/<arm>`, with no baseline — any hit is a failure.  A workspace has
    been sanitised; there is nothing left to grandfather.

`--write-baseline` is for *removing* leaks, never for making a new one go away.  The baseline
diff is the review: a commit that adds a line to it is a commit that added a leak.

Keys come from `common/adapter.all_design_keys()`, which is the same call the sanitiser
makes, so the gate cannot be narrower than the sanitiser.  It was: checking only the one
benchmark with an adapter, it saw 43 keys where the sanitiser saw 335.

With no benchmark installed there are no keys, and this exits **2** — "nothing checked".  That
is deliberately not 0.  A gate that reports success when it had nothing to look at is the
failure mode this whole file exists to prevent, one level up.
"""
import argparse, json, os, re, sys, collections

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

# NOT under assets/: the baseline lists design names by construction, so a baseline
# stored inside the scanned tree reports itself as a leak and grows on every rerun.
DEFAULT_BASELINE = os.path.join(ROOT, "audit", "LEAK_BASELINE.json")

# The parts of a staged slot an author can read.  Scanning only `assets/` is what let a shared
# proof library name three designs and still report a clean workspace: the library had been
# copied into `LeanRTL/Lib/` by then, which is a different path with the same bytes.
WS_ROOTS = ("assets", "LeanRTL", "docs", "scripts", "given", "instructions")
WS_SKIP = ("specs", "frags", "out", "log", "notes", "scratch", "emits", "simdiff", "snapshot")

ANSWERY = re.compile(r"""(?:\b(?:n|N|DW|AW|width|depth|mod|modulus|cycles?|states?|regs?|
                          registers?|bits?|period)\s*[=:]\s*\d+
                        |\bn\s*=\s*\d+
                        |\b\d+\s*(?:registers?|states?|cycles?|bits?)\b)""", re.X)


def scan(assets_dir, keys, skip=(), rel_to=None):
    """Every occurrence of every key under `assets_dir`, with 90 bytes of context either side.

    `rel_to` is what the reported paths are relative to — the workspace when scanning a slot, the
    repository otherwise. A path printed relative to the wrong base sends a reader to a file that
    does not exist, and the baseline keys on these strings, so getting it wrong also silently
    invalidates every grandfathered entry.
    """
    base = rel_to or ROOT
    hits = collections.defaultdict(list)
    for root, dirs, files in os.walk(assets_dir):
        dirs[:] = [d for d in dirs if d not in ("__pycache__", ".lake", ".git")]
        if any(os.sep + s + os.sep in root + os.sep or root.endswith(os.sep + s)
               for s in skip):
            dirs[:] = []
            continue
        for fn in files:
            p = os.path.join(root, fn)
            try:
                text = open(p, errors="replace").read()
            except OSError:
                continue
            for k in keys:
                # Short keys are ordinary English (`pe` in "type", `alu` in "value"), so a
                # word-boundary scan for them is pure noise.  They leak in their code-quoted
                # form, which is what the sanitiser redacts -- scan for that.
                pat = (r"`" + re.escape(k) + r"`") if len(k) <= 5 \
                    else r"\b" + re.escape(k) + r"\b"
                for m in re.finditer(pat, text):
                    ctx = text[max(0, m.start() - 90): m.end() + 90].replace("\n", " ")
                    level = "ANSWER" if ANSWERY.search(ctx) else "NAME"
                    hits[os.path.relpath(p, base)].append((k, level, ctx.strip()[:150]))
    return hits


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--assets", default=os.path.join(ROOT, "assets"))
    ap.add_argument("--ws", help="scan a STAGED workspace's whole readable surface instead — "
                                "assets/, LeanRTL/, docs/, scripts/ and given/.  Scanning only "
                                "assets/ is what let a shared proof library name three designs "
                                "and still report a clean workspace.")
    ap.add_argument("--strict", action="store_true", help="exit 3 on any non-baselined hit")
    ap.add_argument("--key", help="the design this workspace is FOR.  Its own name is not a "
                                 "leak — an author is supposed to know what it is writing — and "
                                 "a key that is a substring of no other is removed from the "
                                 "probe list rather than reported against itself.")
    ap.add_argument("--baseline", nargs="?", const=DEFAULT_BASELINE,
                    help="grandfather these file/key pairs (default: %s)"
                         % os.path.relpath(DEFAULT_BASELINE, ROOT))
    ap.add_argument("--write-baseline", action="store_true",
                    help="rewrite the baseline from what is present now — only when REMOVING")
    a = ap.parse_args()

    from common.adapter import all_design_keys, BENCH_DIR   # one key source, shared with the stager
    keys, sources = all_design_keys()
    if a.key:
        keys = {k for k in keys if k != a.key}
        sources.append(f"−own:{a.key}")
    if not keys:
        print(f"asset_leak: no design keys found under {BENCH_DIR} — nothing checked "
              f"(this is NOT a pass)")
        return 2

    if a.ws:
        ws = os.path.abspath(os.path.expanduser(a.ws))
        hits = collections.defaultdict(list)
        for top in WS_ROOTS:
            d = os.path.join(ws, top)
            if not os.path.isdir(d):
                continue
            for f, v in scan(d, keys, skip=WS_SKIP, rel_to=ws).items():
                hits[f].extend(v)
    else:
        hits = scan(a.assets, keys)
    flat = {f"{f}::{k}" for f, v in hits.items() for k, _, _ in v}

    if a.write_baseline:
        p = a.baseline or DEFAULT_BASELINE
        json.dump({"_note": "Known asset leaks, grandfathered by audit/asset_leak.py. "
                            "Sanitisation removes these at stage time. A commit that ADDS a "
                            "line here added a leak — that is the review signal.",
                   "leaks": sorted(flat)}, open(p, "w"), indent=1)
        print(f"asset_leak: wrote {len(flat)} entries to {os.path.relpath(p, ROOT)}")
        return 0

    base = set()
    if a.baseline and os.path.exists(a.baseline):
        base = set(json.load(open(a.baseline))["leaks"])
    new = sorted(flat - base)
    stale = sorted(base - flat)

    n_ans = sum(1 for v in hits.values() for _, lvl, _ in v if lvl == "ANSWER")
    for f, v in sorted(hits.items()):
        for k, lvl, ctx in v[:3]:
            mark = "NEW " if f"{f}::{k}" in (flat - base) else "    "
            print(f"  {mark}[{lvl:6}] {f}: {k}\n              …{ctx}")
    print(f"\nasset_leak: {len(hits)} file(s), {sum(len(v) for v in hits.values())} hit(s), "
          f"{n_ans} answer-level, over {len(keys)} keys from [{', '.join(sources)}]")
    if base:
        print(f"  baseline: {len(base)} grandfathered · {len(new)} NEW · "
              f"{len(stale)} since removed")
        if stale:
            print("  (removed leaks still in the baseline — rerun with --write-baseline)")
    for n in new:
        print(f"  NEW LEAK  {n}")
    return 3 if (new and a.strict) else 0


if __name__ == "__main__":
    sys.exit(main())
