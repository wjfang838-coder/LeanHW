#!/usr/bin/env python3
"""Which method variant produced this results tree.

`$LEANSILICON_DATA` reroutes every path in the repository — `common/paths.py:38` is the only
place it is read, so a run pointed at another root writes its whole tree there and can see
nothing of the default one.  That is what makes a baseline or an ablation cheap: it is not a
prefix inside `data/`, it is a second `data/`.

    leansilicon/
      data/                 the method's own results
      baselines/<name>/     a DIFFERENT method, run for comparison
      ablations/<name>/     this method with one component removed
      studies/<name>/       the tables across those trees — the actual findings

    LEANSILICON_DATA=../ablations/wo-lean python3 -m leanspec.cli run accu

## Why this file has to exist

Those trees are byte-for-byte the same SHAPE.  `part1/<bench>/<case>/`, `part2/<bench>/<key>/<arm>/`,
the same step documents, the same `summary.json`.  Nothing inside one says which variant made
it, so from the inside `data/` and `ablations/wo-lean/` are indistinguishable, and the only
thing carrying the answer is a directory name — which is a label somebody typed, revocable by
`mv`, and verified by nothing.

That failure has already happened here once, in what is now
`data/part2/rtllm/accu/bak/decided.r1prose`.  Its suffix was applied by hand after the run;
its `run.json` still says `arm: decided`, and its staged prose is byte-identical to the
ORIGINAL arm's.  Two labels on one directory, disagreeing, and neither one checked.  A whole
results tree is the same mistake, larger.

So a non-default root must carry `VARIANT.json` at its top before anything may write into it,
and `name` in that file must equal the directory's own basename — a tree that has been renamed
stops being writable rather than silently becoming a different experiment.

## `data/` is exempt, deliberately

The default root needs no manifest.  Requiring one would mean a fresh clone cannot run until
somebody writes a file describing the absence of a variation, and "the method itself" is what
this repository is; the file exists to describe DEPARTURES from it.  `kind` for `data/` is
reported as `method` without anything on disk saying so.

## Waivers

An ablation does not merely produce different numbers.  It can remove the thing an invariant is
about.  `wo-lean` — spec check with the formalization, diagnosis and witness steps taken out —
has no step 05, so no `witness` event ever reaches the ledger, so `leanspec/cases.audit`'s
ordering check finds every `oracle_query` unjustified and reports the run as a violation.

That reading is wrong in both available directions.  Reported as a violation it says the run was
illegal, when having no witnesses IS the arm's definition; suppressed, it turns off the one
check that makes leanSpec's claim auditable and prints `clean: true` over the top.

`waives` is the third answer: the tree states in advance which invariant it cannot satisfy and
why, `audit` moves those findings to a `waived` list that names the tree, and `clean` describes
only what was left.  A reader who sees `waived` non-empty cannot mistake the row for a method
run, and a waiver nobody declared still fails.
"""
from __future__ import annotations

import json
import os
import sys

from . import paths, provenance

NAME = "VARIANT.json"

#: What a tree can be.  `method` is the default root and is not written down anywhere; the other
#: two are the reason this file exists.
#:
#: The distinction is not cosmetic.  A BASELINE is a different method — `profiles/bare.yaml` is
#: one author, no proof library, no skill notes — and its result is evidence about that method.
#: An ABLATION is this method with a part taken out, and its result is evidence about the part.
#: Reporting one as the other is how "our method beats the baseline" gets written under a table
#: where the comparison was actually against our own method with a flag flipped.
KINDS = ("method", "baseline", "ablation")

#: Invariants a tree may declare it cannot satisfy.  Closed, not free text: a waiver whose name
#: is a sentence is a waiver no checker can look up, and the whole point is that the checker
#: consults this list rather than a human remembering to.
WAIVABLE = {
    "witness_before_answer":
        "leanspec/cases.audit — no designer answer may enter the run before a witness "
        "justifies it.  Waivable only by an arm that has no witness step at all.",
    "lean_convergence":
        "leanspec step 09 — convergence is `determinedEverywhere (admits decidedCfg)`, which "
        "is a Lean query.  An arm without the Lean layer needs another stopping rule and must "
        "say so, because 'both arms converged' is otherwise a sentence about two different "
        "words.",
}


def tree() -> str:
    """The results root this process is writing to."""
    return paths.DATA


def is_default(t: str = "") -> bool:
    """Is this the repository's own `data/`?  The one root that needs no manifest."""
    return os.path.realpath(t or tree()) == os.path.realpath(os.path.join(paths.REPO, "data"))


def path(t: str = "") -> str:
    return os.path.join(t or tree(), NAME)


def method_digest() -> str:
    """A fingerprint of the method that is about to run.

    `framework/` and the two halves' Python, through the same `provenance` functions a workspace
    stamp uses.  Not a git commit: this repository is not a checkout on the machine it runs on,
    and a field that says `unknown` on every row is worse than one that says what was hashed.
    """
    roots = [paths.method(r) for r in ("framework", "common", "leanspec", "leanrtl", "profiles")]
    roots = [r for r in roots if os.path.exists(r)]
    return provenance.digest(provenance.walk(*roots), paths.CODEBASE)


def read(t: str = "") -> dict:
    """The manifest, or `{}`.  Never raises — `require` is what refuses."""
    p = path(t)
    if not os.path.isfile(p):
        return {}
    try:
        with open(p) as f:
            d = json.load(f)
        return d if isinstance(d, dict) else {}
    except (OSError, ValueError):
        return {}


def describe(t: str = "") -> dict:
    """What this tree is, whether or not it says so.  `data/` answers `method`."""
    t = t or tree()
    if is_default(t):
        return {"kind": "method", "name": "data", "tree": t,
                "what": "the method's own results", "waives": []}
    d = dict(read(t))
    d.setdefault("kind", "unknown")
    d.setdefault("name", os.path.basename(os.path.realpath(t)))
    d.setdefault("waives", [])
    d["tree"] = t
    return d


def problems(t: str = "") -> list[str]:
    """Everything wrong with this tree's manifest.  Empty for `data/`."""
    t = t or tree()
    if is_default(t):
        return []
    p = path(t)
    if not os.path.isfile(p):
        return [f"{p} does not exist"]
    d = read(t)
    if not d:
        return [f"{p} is not a readable JSON object"]
    out = []
    if d.get("kind") not in KINDS:
        out.append(f"kind is {d.get('kind')!r}; expected one of {', '.join(KINDS)}")
    # The directory's own name has to match.  This is the check that makes `mv` visible: a tree
    # renamed to look like a different experiment stops being writable instead of quietly
    # becoming one.
    base = os.path.basename(os.path.realpath(t))
    if d.get("name") != base:
        out.append(f"name is {d.get('name')!r} but the directory is {base!r} — one of them has "
                   f"moved, and a results tree may not be renamed into a different experiment")
    for k in ("what", "control"):
        if not d.get(k):
            out.append(f"{k} is empty")
    ctl = d.get("control")
    if ctl and not os.path.isdir(os.path.join(t, ctl) if not os.path.isabs(ctl) else ctl):
        out.append(f"control {ctl!r} does not resolve to a directory — a variant with no tree "
                   f"to be compared against is a number with no denominator")
    for w in d.get("waives", []):
        nm = w.get("invariant") if isinstance(w, dict) else w
        if nm not in WAIVABLE:
            out.append(f"waives an unknown invariant {nm!r}; known: {', '.join(WAIVABLE)}")
        elif not (isinstance(w, dict) and w.get("why")):
            out.append(f"waives {nm!r} with no reason — a waiver with no argument is a "
                       f"suppression")
    return out


def waived(invariant: str, t: str = "") -> str:
    """Why this tree is allowed to break `invariant`, or `""` if it is not allowed to.

    Returns the reason rather than a bool so that whoever reports the waiver has to print the
    argument for it beside the result.  A waiver that shows up in output as `true` is one nobody
    reading the table can evaluate.
    """
    for w in describe(t).get("waives", []):
        if isinstance(w, dict) and w.get("invariant") == invariant:
            return w.get("why") or "declared with no reason"
    return ""


def require(why: str = "") -> dict:
    """Refuse to start a run in an undeclared results tree.  Called by the writers only.

    Readers — `ls`, `audit`, `compare` — do not call this.  A tree that is already on disk can
    be read whatever state its manifest is in; the refusal is about not ADDING to a tree whose
    identity nobody has written down, because that is the moment the ambiguity is created and
    the only moment it is cheap to fix.
    """
    probs = problems()
    if not probs:
        return describe()
    t = tree()
    sys.exit(
        f"variant: {t} is not this repository's `data/`, so it is a baseline or an ablation, and "
        f"it must say which before {why or 'a run'} may write into it.\n\n  "
        + "\n  ".join(probs)
        + f"\n\nWrite {path()} — `python3 -m common.variant --init "
        f"--kind ablation --what '...' --control ../../data` — or unset $LEANSILICON_DATA to "
        f"run against the method's own tree.\n\nEvery one of these trees has the same shape, so "
        f"nothing inside one says which variant produced it.  A directory name is a label "
        f"somebody typed; this file is the record.")


def init(t: str, kind: str, what: str, control: str, differs: list[str],
         waives: list[dict]) -> dict:
    """Write a manifest.  Overwrites, because a variant redefined mid-study is worth one loud
    rewrite rather than a second file that disagrees with the first."""
    os.makedirs(t, exist_ok=True)
    d = {"kind": kind,
         "name": os.path.basename(os.path.realpath(t)),
         "what": what,
         "differs": differs,
         "control": control,
         "waives": waives,
         # What the method looked like when this tree was declared.  Not re-checked on every
         # run: a tree accumulates runs across method edits and pinning it would make the third
         # run fail for a reason that has nothing to do with the third run.  It is here so a
         # study can report that two trees were declared against different methods, which is a
         # fact about the comparison rather than an error in either tree.
         "method_digest_at_init": method_digest()}
    with open(os.path.join(t, NAME), "w") as f:
        json.dump(d, f, indent=1)
    return d


def main(argv: list[str] | None = None) -> int:
    import argparse
    ap = argparse.ArgumentParser(prog="variant", description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--tree", default="", help="default: $LEANSILICON_DATA")
    ap.add_argument("--init", action="store_true", help="write VARIANT.json")
    ap.add_argument("--kind", choices=[k for k in KINDS if k != "method"])
    ap.add_argument("--what", default="", help="one line: what this tree is")
    ap.add_argument("--control", default="", help="the tree this is compared against")
    ap.add_argument("--differs", action="append", default=[],
                    help="one component that differs from the method arm; repeatable")
    ap.add_argument("--waive", action="append", default=[], metavar="INVARIANT=WHY",
                    help=f"an invariant this arm cannot satisfy.  known: {', '.join(WAIVABLE)}")
    a = ap.parse_args(argv)
    t = os.path.abspath(a.tree) if a.tree else tree()

    if a.init:
        if not a.kind:
            return _die("--init needs --kind")
        ws = []
        for s in a.waive:
            k, _, v = s.partition("=")
            if k not in WAIVABLE:
                return _die(f"unknown invariant {k!r}.  known:\n  "
                            + "\n  ".join(f"{n}\n    {d}" for n, d in WAIVABLE.items()))
            if not v:
                return _die(f"--waive {k} needs a reason: --waive '{k}=because ...'")
            ws.append({"invariant": k, "why": v})
        init(t, a.kind, a.what, a.control or "../../data", a.differs, ws)

    print(json.dumps(describe(t), indent=1))
    probs = problems(t)
    if probs:
        print("\nproblems:\n  " + "\n  ".join(probs), file=sys.stderr)
        return 1
    print("\nok — this tree says what it is", file=sys.stderr)
    return 0


def _die(msg: str) -> int:
    print(f"variant: {msg}", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
