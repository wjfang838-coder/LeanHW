#!/usr/bin/env python3
"""One command per design: stage a workspace, run the chain, ride out the challenge rounds.

    python3 -m leanrtl.launch --profile two-author --key accu --spec prose.txt
    python3 -m leanrtl.launch --profile two-author --key accu \\
            --original original.txt --decided decided.txt

`launch` is the thin layer.  It owns exactly three decisions — which workspace, which arm, and
how many rounds — and every other decision belongs to `stage.py` (what a workspace contains),
`pipeline.py` (what the steps are) or `two_author.py` (what the authors are told).  A launcher
that also decided any of those would be a second place they could be decided, and the two would
drift in the direction nobody was watching.

Two things it fills in are lookups rather than decisions: `--bench` and `--toplevel` both name
facts the dataset already states, and both are read from the adapter when omitted rather than
required from a caller who could contradict them.  Both are printed with their source, because a
default that is silently right on one corpus and silently wrong on another is worse than no
default — see `resolve_toplevel`.

## Two arms, two workspaces, never one

With `--original` and `--decided` this stages TWO workspaces and runs the chain in each.  They
are separate directories with separate provenance stamps and separate git repositories, and
neither can see the other.  Sharing one workspace between arms would be cheaper by exactly one
`lake build`, and would make every arm-to-arm comparison worthless: the second arm would start
with the first arm's `.lake`, its `LeanRTL/Blind/<Camel>.lean`, its committed fragments and its
`scratch/asm`, and an author that found a working implementation sitting on disk would not have
to write one.

The two arms are the same design, the same profile, the same framework and the same gates.  The
ONLY difference is which prose file `specs/<key>.spec.txt` was copied from.  That is what makes
the comparison mean something, and it is why the arm is a property of the workspace rather than
a flag on a shared one.

### They do not have to run at the same time

`--decided Q` alone runs the second arm against an original arm that already finished.  This is
not a loosening of the rule above; it is what the rule requires once the two arms are separated
in time, which they are by construction.  The decided prose is produced by the OTHER half of this
pipeline, and that half takes as long as it takes — so by the time it exists, the original arm
has usually been done for hours.  Passing `--original` again then does not add a second piece of
evidence.  It re-runs a finished workspace and overwrites the first.

What makes the single-arm form safe is that the pairing is checked rather than asserted:
`original_arm_ran` loads the sibling workspace's own provenance stamp and requires it to say
`arm: original` for this key and this profile.  A caller cannot supply that from the command
line, which is the property the two-flag form was protecting.

## Rounds

A round ends in one of three ways.  It converges — every step green through `certify`.  It
fails — some step returned problems, and the run stops with them.  Or D challenges the frozen
specification, which is a RESULT and not an error: `pipeline` exits 4, and this starts round N+1,
where S rewrites the specification with the challenge as a directive.

`max_spec_versions` in the profile bounds it.  The bound exists because the challenge loop has no
natural fixed point — S and D can disagree about the same clause indefinitely, each round costing
two full authoring sessions — and a loop with no bound eventually spends a night on one design.
Hitting the bound is reported as `unresolved`, which is a real outcome and not a failure of
either author: two competent readers could not converge on what the document says, which is
information about the document.

## What this does not do

It does not score anything.  There is no arm table, no aggregate, no comparison of the two arms'
verdicts — those belong to whoever is running an experiment, and baking them in here is how a
method acquires an experimental design it then cannot be separated from.  What comes out is one
`summary.json` per workspace and the ledger.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import sys
import time

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

from common import adapter, ledger, paths, profiles, provenance, variant            # noqa: E402
from leanrtl import pipeline, stage, two_author                              # noqa: E402


def ws_for(a, arm: str) -> str:
    """Where this arm's workspace goes.  See `common/paths.ws2` for the layout and why."""
    return os.path.abspath(os.path.expanduser(paths.ws2(a.bench, a.key, arm)))


def already_staged(ws: str, a, arm: str, prose: str) -> bool:
    """Is this directory a workspace for exactly the run we are about to start?

    `stage.main` refuses an existing directory, which is right — a workspace silently reused
    across arms would carry the first arm's `.lake`, its committed fragments and, worst, its
    author's working implementation, and every arm-to-arm comparison after that is worthless.
    But applied to the workspace `--stage-only` JUST built, that refusal makes the two commands
    unable to compose: staging ahead of time produces a directory `launch` will not run in.

    So the question is not "does it exist" but "is it the same run".  Key, profile and arm must
    match, and `specs/<key>.spec.txt` must be byte-identical to the prose we were handed — the
    file the author actually reads, rather than the path it was copied from, because a path that
    still resolves says nothing about what is at the end of it now.  Anything else is a different
    run wearing this one's directory, and the caller is told to pass `--force` and mean it.
    """
    if not os.path.isdir(ws) or a.force:
        return False
    try:
        prev = pipeline.Run.load(ws)
    except (FileNotFoundError, TypeError, ValueError):
        return False
    if (prev.key, prev.profile, prev.arm) != (a.key, a.profile, arm):
        return False
    staged = os.path.join(ws, "specs", f"{a.key}.spec.txt")
    if not os.path.isfile(staged):
        return False
    return _sha(staged) == _sha(prose)


def _sha(p: str) -> str:
    h = hashlib.sha256()
    with open(p, "rb") as f:
        for b in iter(lambda: f.read(1 << 16), b""):
            h.update(b)
    return h.hexdigest()


def stage_arm(a, arm: str, prose: str) -> str:
    """Stage one workspace for one arm and record what it is a workspace for."""
    ws = os.path.abspath(os.path.expanduser(a.ws)) if a.ws else ws_for(a, arm)
    if already_staged(ws, a, arm, prose):
        print(f"launch: reusing the staged workspace at {ws}")
        return ws
    argv = ["--profile", a.profile, "--key", a.key, "--spec", prose, "--ws", ws]
    if a.toplevel:
        argv += ["--toplevel", a.toplevel]
    if a.force:
        argv.append("--force")
    if a.destroy:
        argv += ["--destroy"]
    rc = stage.main(argv)
    if rc != 0:
        sys.exit(f"launch: staging {arm} failed")
    pipeline.Run(ws=ws, key=a.key, profile=a.profile,
                 toplevel=a.toplevel or a.key,
                 prose=os.path.abspath(os.path.expanduser(prose)), arm=arm,
                 mutation=not a.no_mutation).save()
    return ws


def resolve_toplevel(a, say=print) -> None:
    """Fill in `--toplevel` from the benchmark, and say where the answer came from.

    The module name the oracle instantiates is a fact the dataset already states, and the caller
    should not have to repeat a fact they can contradict — the same reasoning `--bench` is
    inferred under.  What makes this one urgent rather than tidy is the shape of the failure when
    it is wrong.

    `stage.resolve_spec` defaults the toplevel to the KEY on the `--spec` path, and `stage_arm`
    always takes the `--spec` path.  On RTLLM that default is correct on all 50 designs — key and
    toplevel are the same string — so it has never once been exercised.  On VerilogEval and
    ChipBench every one of the 201 designs is named `TopModule`, and the key never is.  An omitted
    `--toplevel` there emits a module called `Prob067_countslow`, the checker instantiates
    `TopModule`, finds nothing, and the run scores `compile_fail` — which reads as a design that
    does not elaborate, and is in fact a design nobody looked for.  That is a wrong answer wearing
    a plausible failure's clothes, and the cost of it is a full authoring session.

    So it is resolved once, here, before either arm is staged, from the same adapter that will do
    the scoring.  An explicit `--toplevel` still wins: a caller running prose no benchmark claims
    has no adapter to ask.  When nothing can answer, the key stands as before — but it is printed
    rather than assumed, because that default is silently right on one corpus and silently wrong
    on two.
    """
    if a.toplevel:
        say(f"launch: toplevel `{a.toplevel}` (given on the command line)")
        return
    if a.bench and a.bench != paths.LOCAL:
        try:
            d = adapter.load(a.bench).design_map().get(a.key)
        except Exception as e:                                    # noqa: BLE001
            # An unreadable adapter must not silently become the key-shaped default.  Say what
            # broke; the caller can pass --toplevel and proceed.
            say(f"launch: could not ask {a.bench}'s adapter for a toplevel "
                f"({type(e).__name__}: {e})")
            d = None
        if d and d.toplevel:
            a.toplevel = d.toplevel
            say(f"launch: toplevel `{a.toplevel}` (from {a.bench}'s adapter)")
            return
    say(f"launch: toplevel `{a.key}` (no adapter named one; defaulting to the key)")


def rounds_allowed(prof: dict) -> int:
    """How many specification versions this profile permits, as a round count.

    `max_spec_versions: 0` means "there is nobody to challenge" — the control arm has one author
    — and it still gets ONE round: zero versions would be zero runs.  The number bounds
    REWRITES, not attempts.
    """
    return max(1, int(prof.get("max_spec_versions") or 0))


def run_arm(ws: str, max_rounds: int, say=print) -> dict:
    """The chain, once per round, until it converges, fails, or runs out of rounds."""
    run = pipeline.Run.load(ws)
    ch = pipeline.chain(run)
    t0 = time.time()
    history = []

    for rnd in range(1, max_rounds + 1):
        say(f"\n── {run.key} · arm `{run.arm}` · round {rnd}/{max_rounds} "
            + "─" * max(0, 40 - len(run.key) - len(run.arm)))
        try:
            docs = ch.run(0, pipeline.LAST, rnd, say=say)
        except Exception as e:                                   # noqa: BLE001
            # A step raising is not the same as a step failing, and the distinction has to
            # survive into the record: a failed step is a finding about the work, an exception is
            # a finding about this code.  Recording both as "round failed" is how a broken
            # pipeline gets written up as a hard benchmark.
            history.append({"round": rnd, "outcome": "error", "error": f"{type(e).__name__}: {e}"})
            say(f"  ERROR in the pipeline itself: {type(e).__name__}: {e}")
            break

        last = docs[-1] if docs else None
        if last and last["ok"] and last["step"] == pipeline.LAST:
            history.append({"round": rnd, "outcome": "converged"})
            break
        chl = ((last or {}).get("produced") or {}).get("challenge")
        if chl:
            history.append({"round": rnd, "outcome": "challenged",
                            "quote": chl.get("quote", "")[:300],
                            "why": chl.get("why", "")[:300]})
            say(f"  D challenged the specification: {chl.get('why', '')[:120]}")
            if rnd == max_rounds:
                say("  and this is the last round the profile allows")
            continue
        history.append({"round": rnd, "outcome": "failed",
                        "step": (last or {}).get("name"),
                        "problems": (last or {}).get("problems", [])})
        break

    outcome = history[-1]["outcome"] if history else "nothing ran"
    if outcome == "challenged":
        # Ran out of rounds mid-argument.  Named as its own outcome rather than folded into
        # "failed": nobody's work was wrong, the two authors could not agree on what the document
        # says, and that is information about the document.
        outcome = "unresolved"

    fz = two_author.freeze_intact(ws, run.key)
    vp = os.path.join(ws, "verify.json")
    summary = {
        "key": run.key, "arm": run.arm, "profile": run.profile, "ws": ws,
        "outcome": outcome, "rounds": history, "elapsed_s": round(time.time() - t0, 1),
        "spec_versions": fz.get("version"),
        "freeze_intact": fz.get("intact"),
        "verify": (json.load(open(vp)) if os.path.isfile(vp) else None),
        "simdiff": (json.load(open(os.path.join(ws, "simdiff", run.key + ".json")))
                    if os.path.isfile(os.path.join(ws, "simdiff", run.key + ".json")) else None),
        "provenance": provenance.read(ws),
    }
    with open(os.path.join(ws, "summary.json"), "w") as f:
        json.dump(summary, f, indent=1, default=str)
    ledger.log(paths.DATA, "arm_done", ws=os.path.basename(ws), key=run.key, arm=run.arm,
               outcome=outcome, rounds=len(history), elapsed=summary["elapsed_s"])
    return summary


def report(s: dict) -> str:
    v = ((s.get("verify") or {}).get("design") or {})
    L = [f"{s['key']} · {s['arm']:<9} {s['outcome'].upper():<11} "
         f"{s['elapsed_s']}s  spec v{s.get('spec_versions') or '—'}"]
    if s.get("freeze_intact") is False:
        L.append("    FREEZE BROKEN — every proof here is about a document that no longer "
                 "exists; this run is void, not weaker")
    if s.get("simdiff"):
        L.append(f"    simdiff  {s['simdiff']['verdict']} · {s['simdiff']['checked']} checked")
    if v:
        marks = " ".join(f"{k}={'ok' if x.get('pass') else 'FAIL'}"
                         for k, x in v.items() if isinstance(x, dict) and "pass" in x)
        L.append(f"    gates    {marks or '(none ran)'}")
    for r in s["rounds"]:
        if r["outcome"] == "challenged":
            L.append(f"    round {r['round']}: challenged — {r['why'][:90]}")
        elif r["outcome"] == "failed":
            L.append(f"    round {r['round']}: failed at {r.get('step')} — "
                     + "; ".join(map(str, r.get("problems", [])[:2])))
        elif r["outcome"] == "error":
            L.append(f"    round {r['round']}: PIPELINE ERROR — {r['error']}")
    L.append(f"    {s['ws']}")
    return "\n".join(L)


def original_arm_ran(a) -> str:
    """The completed original-arm workspace for this key and profile, or `""`.

    `--decided` alone is refused below because a run with nothing to be decided *relative to*
    has only its own label as evidence that it was decided prose.  That reasoning is right and
    it has a hole: it assumes the two arms are always run together.  They are not.  The original
    arm takes the better part of an hour, and the decided prose does not exist until the other
    half of this pipeline converges — which can be a day later.  Running them together then means
    re-running the original arm on top of its own finished workspace, which does not produce a
    second piece of evidence.  It overwrites the first.

    So the question this asks is the one the guard actually wants answered: does the evidence
    exist?  Not "was the flag passed" but "is there a workspace on disk whose own provenance says
    it ran the original prose for this key under this profile".  That is `pipeline.Run.load`
    reading a stamp `stage.py` wrote, which is the same thing `already_staged` trusts one function
    up, and it is not something a caller can assert from the command line.
    """
    ws = ws_for(a, "original")
    try:
        prev = pipeline.Run.load(ws)
    except (FileNotFoundError, TypeError, ValueError):
        return ""
    return ws if (prev.key, prev.profile, prev.arm) == (a.key, a.profile, "original") else ""


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--profile", required=True)
    ap.add_argument("--key", required=True)
    # `--spec` and `--original` remain mutually exclusive — they are two different claims about
    # what the single prose file is — but the group is no longer `required`, because `--decided`
    # alone is a legitimate third form (see `original_arm_ran`).  The obligation to name SOME
    # prose is checked below instead, where it can say which forms exist.
    src = ap.add_mutually_exclusive_group()
    src.add_argument("--spec", help="one prose file; the arm is called `original`")
    src.add_argument("--original", help="the original prose (pairs with --decided)")
    ap.add_argument("--decided", help="the decided prose, from the other half; alone, only when "
                                      "the original arm already ran")
    ap.add_argument("--toplevel")
    ap.add_argument("--ws", help="only meaningful with --spec; two arms need two directories")
    # Which directory under `data/part2/` the workspaces land in.  Inferred from `--key`, because
    # the datasets already record who owns which name and a caller made to repeat it is a caller
    # who can contradict it: `--key accu --bench cvdp` would stage rtllm's prose in cvdp's
    # directory, and nothing downstream reads the prose closely enough to notice.  Explicit is
    # still allowed for prose that came from a file no benchmark claims.
    ap.add_argument("--bench", default="",
                    help="which corpus this design is from; names the directory under "
                         "data/part2/.  Inferred from --key when omitted.")
    ap.add_argument("--rounds", type=int,
                    help="override the profile's max_spec_versions")
    ap.add_argument("--force", action="store_true")
    ap.add_argument("--destroy", action="store_true")
    ap.add_argument("--stage-only", action="store_true",
                    help="build the workspaces and stop, without spending an authoring session")
    ap.add_argument("--no-mutation", action="store_true",
                    help="skip proof mutation in certify.  It is a measurement, not a gate: the "
                         "same gates decide the same outcome, and the run writes no "
                         "out/proof_mutation.json, so the report shows `—` rather than a score")
    a = ap.parse_args(argv)
    variant.require("a launch")
    a.bench = a.bench or adapter.bench_for_key(a.key) or paths.LOCAL

    if not (a.spec or a.original or a.decided):
        sys.exit("launch: name some prose.  `--spec P` runs one arm called `original`; "
                 "`--original P --decided Q` runs both; `--decided Q` runs the second arm alone "
                 "when the first is already on disk.")
    if a.original and not a.decided:
        sys.exit("launch: --original without --decided stages one arm and calls it two.  Use "
                 "--spec for a single arm, so the record says which one it was.")
    sibling = ""
    if a.decided and not a.original:
        sibling = original_arm_ran(a)
        if not sibling:
            sys.exit("launch: --decided needs --original, or an original arm already on disk.  A "
                     "decided-prose run alone has nothing to be decided relative to, and the arm "
                     f"label would be the only evidence it was.  Looked for a workspace at "
                     f"{os.path.relpath(ws_for(a, 'original'), paths.REPO)} whose own stamp says "
                     f"it ran the original prose; there is none.")

    prof = profiles.load(a.profile)
    max_rounds = a.rounds or rounds_allowed(prof)
    arms = ([("original", a.spec)] if a.spec else
            [("decided", a.decided)] if sibling else
            [("original", a.original), ("decided", a.decided)])
    if len(arms) > 1 and a.ws:
        sys.exit("launch: --ws names one directory and this is a two-arm run.  Two arms sharing "
                 "a workspace share the first arm's build, fragments and assembled design, which "
                 "is the whole of what the second arm was supposed to produce.")
    if sibling:
        print(f"launch: the original arm is already on disk at {os.path.relpath(sibling, ROOT)} "
              f"and is not re-run — running it again would overwrite the evidence this arm is "
              f"paired with, not add to it.")

    print(f"launch: {a.key} · profile {a.profile} ({prof['_sha']}) · "
          f"{len(arms)} arm(s) · up to {max_rounds} round(s)")
    resolve_toplevel(a)
    for arm, prose in arms:
        if not os.path.isfile(os.path.expanduser(prose)):
            sys.exit(f"launch: no prose at {prose}")

    staged = [(arm, stage_arm(a, arm, prose)) for arm, prose in arms]
    if a.stage_only:
        for arm, ws in staged:
            print(f"  staged {arm}: {ws}")
        return 0

    summaries = []
    for arm, ws in staged:
        summaries.append(run_arm(ws, max_rounds))

    print("\n" + "=" * 78)
    for s in summaries:
        print(report(s))
    if len(summaries) > 1:
        print("\nBoth arms ran the same profile, framework and gates; the only difference "
              "between\nthem is which prose file was staged.  No comparison is drawn here — "
              "that is the\nexperiment's job, not the method's.")
    return 0 if all(s["outcome"] == "converged" for s in summaries) else 3


if __name__ == "__main__":
    sys.exit(main())
