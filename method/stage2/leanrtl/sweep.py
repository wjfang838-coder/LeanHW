#!/usr/bin/env python3
"""Run one benchmark's designs through `launch` N at a time, and write down what happened.

    python3 -m leanrtl.sweep --bench rtllm --profile two-author --jobs 8 --stage-only
    python3 -m leanrtl.sweep --bench rtllm --profile two-author --jobs 8
    python3 -m leanrtl.sweep --bench rtllm --report

## Why this is a separate file

`launch` is one command per design and says so in its own docstring: it owns which workspace,
which arm and how many rounds, and nothing else.  A sweep is not a fourth decision of the same
kind — it is an experimental design, "run these designs, this many at once, and tabulate them" —
so it lives out here under the same rule as `score.py` and `compare.py`: **nothing under
`leanrtl/` may import this file.**

It also does not import `pipeline`, `stage` or `two_author`.  It shells out to
`python3 -u -m leanrtl.launch`, one subprocess per design.  That is not timidity about imports:

  * A design that dies — a Lean segfault, an OOM, an author session that wedges — takes its own
    process down and nothing else.  In-process, one design's crash ends the sweep.
  * `pipeline` chdirs, writes files relative to a workspace and spawns authoring sessions with a
    `PreToolUse` hook bound to a root.  Eight of those sharing one interpreter share one cwd and
    one set of module globals, and the first collision between two designs would be silent.
  * The subprocess boundary is the same boundary a human running `launch` by hand would have, so
    a design that fails here fails the same way when re-run alone.  A sweep whose failures cannot
    be reproduced one at a time is not evidence.

## The original arm only

`--spec P` is the launch form that names an arm `original`, and it is the only form this file
uses.  The decided arm cannot be swept: its prose is a Part 1 deliverable (`out/spec.decided.txt`)
that exists for a design or does not, and a sweep that skipped the designs Part 1 has not reached
yet would be a table whose row set silently encoded Part 1's progress rather than Part 2's.  Run
those with `launch --decided` as they become available.

`--report` will read whatever arms are on disk, so it takes `--arm`.

## What "already done" means, and why it is not a state file

A design is skipped when `out/<key>.v` exists.  That is the same evidence `compare.discover` uses
to decide a directory is a reported arm, and using anything else here — a manifest, a done-list,
a `.sweep_state` — would create a second answer to "did this design produce an artifact" that can
disagree with the first.  It also makes the sweep resumable by construction: interrupt it, run the
same command again, and it picks up the designs that have no artifact.

`--force` is deliberately NOT passed through.  A sweep that can overwrite a finished, verified
workspace is a sweep that can destroy the result it was run to extend, and the recovery is
another authoring session.  Re-run one design deliberately with `launch --force` instead.

## No retries

A design that fails is recorded and left.  Retrying inside a sweep means the table's rows are no
longer one run each, and "converged" starts to mean "converged on some attempt, count unstated".
The challenge loop is already a bounded retry that `launch` owns (`max_spec_versions`), and it is
the one that belongs to the method.
"""
from __future__ import annotations

import argparse
import contextlib
import datetime
import fcntl
import json
import os
import signal
import subprocess
import sys
import threading
import time
from concurrent.futures import ThreadPoolExecutor, as_completed

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

from common import adapter, paths                                          # noqa: E402

#: The only arm a sweep can produce.  See the module docstring.
ARM = "original"

#: Per-design wall clock.  `accu` — the acceptance design, the simplest in RTLLM, converged in one
#: round — recorded `elapsed_s: 2977.9`.  Four hours is about five times that, which leaves room
#: for a design that needs both challenge rounds without leaving a wedged session running until
#: somebody notices.  `bak/decided.killed` is what the alternative looks like.
DEFAULT_TIMEOUT = 4 * 60 * 60

#: How long a killed process group gets to exit before it is killed harder.
GRACE = 30

GATES = ("builds", "proves_impl", "zero_sorry", "axiom_clean", "undriven_nets",
         "asset_leak", "simdiff")


def log_dir(bench: str, arm: str) -> str:
    """Where this sweep's per-design logs and its progress journal go.

    Under `data/logs/` rather than in the workspaces, because a design that dies before `stage`
    finishes has no workspace to hold its own log, and that is exactly the design whose log is
    worth reading.
    """
    return paths.data("logs", "sweep", f"{bench}-{arm}")


def _read_json(p: str) -> dict:
    try:
        with open(p) as f:
            return json.load(f)
    except (OSError, ValueError):
        return {}


def attempted(bench: str, key: str, arm: str = ARM) -> bool:
    """Has this design been RUN?  `summary.json` is `launch`'s own journal of a finished run.

    This, and not the artifact, is what decides whether a sweep skips a design.  Staging does not
    write it — after Phase A all 49 workspaces existed and none had one — so it separates "the
    directory is ready" from "the run happened", which is the distinction the skip needs.  A run
    that finished and failed is attempted: the agreed policy is to record and never retry, and
    re-running it here would quietly violate that.
    """
    return os.path.isfile(os.path.join(paths.ws2(bench, key, arm), "summary.json"))


def certified(bench: str, key: str, arm: str = ARM) -> bool:
    """Did the PIPELINE emit and certify an artifact here — as opposed to something leaving a file?

    Not `out/<key>.v` alone, which is what this used to test and what `compare.discover` still
    tests.  `compare` may be that loose because it takes a key with no adapter in hand and lets
    any artifact be evidence; a sweep may not, because it hands the file to `score`, and `score`
    writes the verdict out labelled `final`.

    `alu` is the case that found this.  It failed at `06_proof`, so `07_emit` never ran: no
    `07_emit.json`, no `iface_conform.json`, no `verify.json`, `outcome: failed`.  It nonetheless
    has a 37 KB `out/alu.v`, timestamped minutes BEFORE its proof transcript closed — D holds the
    emit tooling inside its own authoring session and had run it to look at its work.  Reading
    that as "done" skips the design on the next sweep and offers D's scratch to the oracle as the
    certified artifact.  Both errors point the same way, the flattering one.

    `verify.json` is written by `08 certify` and by nothing else, so requiring it alongside the
    artifact asks the question actually meant: did this design come out of the pipeline.
    """
    ws = paths.ws2(bench, key, arm)
    return (os.path.isfile(os.path.join(ws, "out", f"{key}.v"))
            and os.path.isfile(os.path.join(ws, "verify.json")))


def append(path: str, rec: dict) -> None:
    """One JSON object per line, under an exclusive `flock`, flushed and fsynced.

    The same discipline as `common/ledger.py` and for the same reason: eight workers append here,
    and two interleaved writes produce a line that no reader can parse and no writer will notice.
    """
    os.makedirs(os.path.dirname(path), exist_ok=True)
    with open(path, "a") as f:
        fcntl.flock(f.fileno(), fcntl.LOCK_EX)
        try:
            f.write(json.dumps(rec, default=str) + "\n")
            f.flush()
            os.fsync(f.fileno())
        finally:
            fcntl.flock(f.fileno(), fcntl.LOCK_UN)


class Fleet:
    """The set of subprocesses currently running, so a Ctrl-C can take them all down.

    Without this, interrupting a sweep leaves eight `launch` processes — and their authoring
    sessions and `lake` builds — orphaned and still spending money, with nothing left holding
    their pids.
    """

    def __init__(self) -> None:
        self._procs: set[subprocess.Popen] = set()
        self._lock = threading.Lock()
        self.stopping = False

    def add(self, p: subprocess.Popen) -> None:
        with self._lock:
            self._procs.add(p)

    def drop(self, p: subprocess.Popen) -> None:
        with self._lock:
            self._procs.discard(p)

    def stop_all(self) -> None:
        self.stopping = True
        with self._lock:
            procs = list(self._procs)
        for p in procs:
            kill_group(p)


def kill_group(p: subprocess.Popen) -> None:
    """Kill a launch and everything it started.

    Every child is spawned with `start_new_session=True`, so its pid is its own process group
    leader and one `killpg` reaches the authoring sessions and `lake` beneath it.  Signalling the
    pid alone would leave a `claude -p` running with no parent to wait on it.
    """
    for sig in (signal.SIGTERM, signal.SIGKILL):
        if p.poll() is not None:
            return
        with contextlib.suppress(ProcessLookupError, PermissionError):
            os.killpg(p.pid, sig)
        with contextlib.suppress(subprocess.TimeoutExpired):
            p.wait(timeout=GRACE if sig == signal.SIGTERM else 5)


def launch_cmd(key: str, spec: str, profile: str, bench: str, stage_only: bool,
               no_mutation: bool = False) -> list[str]:
    cmd = [sys.executable, "-u", "-m", "leanrtl.launch",
           "--profile", profile, "--key", key, "--bench", bench, "--spec", spec]
    if stage_only:
        cmd.append("--stage-only")
    if no_mutation:
        cmd.append("--no-mutation")
    return cmd


def run_one(key: str, spec: str, a, fleet: Fleet) -> dict:
    """Run one design to completion, or to the wall clock, and return its record.

    `rc` is `launch`'s own: 0 every arm converged, 3 it ran and did not, 1 it refused the
    arguments.  `launch` absorbs `pipeline`'s exit 4 internally — a challenge starts round N+1,
    bounded by the profile's `max_spec_versions` — so there is no exit 4 to see here and a sweep
    that special-cased one would be describing a control flow that does not exist.
    """
    d = log_dir(a.bench, ARM)
    os.makedirs(d, exist_ok=True)
    logp = os.path.join(d, f"{key}.log")
    cmd = launch_cmd(key, spec, a.profile, a.bench, a.stage_only, a.no_mutation)
    t0 = time.time()
    rc, timed_out = None, False
    with open(logp, "a") as lf:
        lf.write(f"\n{'=' * 78}\n# sweep {datetime.datetime.now().astimezone().isoformat()}\n"
                 f"# {' '.join(cmd)}\n{'=' * 78}\n")
        lf.flush()
        p = subprocess.Popen(cmd, cwd=paths.METHOD, stdout=lf, stderr=subprocess.STDOUT,
                             stdin=subprocess.DEVNULL, start_new_session=True)
        fleet.add(p)
        try:
            rc = p.wait(timeout=a.timeout)
        except subprocess.TimeoutExpired:
            timed_out = True
            lf.write(f"\n# sweep: wall clock {a.timeout}s reached; killing the process group\n")
            lf.flush()
            kill_group(p)
            rc = p.poll()
        finally:
            fleet.drop(p)

    ws = paths.ws2(a.bench, key, ARM)
    s = _read_json(os.path.join(ws, "summary.json"))
    # A directory with no `run.json` is a workspace `stage` died inside — the shape
    # `bak/decided.crashed-stage` has.  It matters because it is not self-healing: `launch`'s
    # `already_staged` cannot load a run record, so `stage.main` refuses the existing directory
    # and every later attempt exits 1 for a reason that looks nothing like the original failure.
    # Saying so here is the whole of the fix; clearing it is a deliberate act with `--force`, and
    # a sweep that deleted workspaces to unstick itself is a sweep that can delete a good one.
    half_staged = os.path.isdir(ws) and not os.path.isfile(os.path.join(ws, "run.json"))
    return {
        "key": key,
        "bench": a.bench,
        "arm": ARM,
        "profile": a.profile,
        "rc": rc,
        "timed_out": timed_out,
        "half_staged": half_staged,
        "stage_only": a.stage_only,
        # `outcome` is launch's word for it — converged / unresolved / failed.  Absent when the
        # run died before writing a summary, which is a different thing from failing one and is
        # recorded as such rather than flattened into "failed".
        "outcome": s.get("outcome"),
        "rounds": len(s.get("rounds") or []) or None,
        "spec_versions": s.get("spec_versions"),
        "freeze_intact": s.get("freeze_intact"),
        "verify_ok": (s.get("verify") or {}).get("design", {}).get("all_pass"),
        "elapsed_s": round(time.time() - t0, 1),
        "reported_elapsed_s": s.get("elapsed_s"),
        "emitted": certified(a.bench, key, ARM),
        "log": os.path.relpath(logp, paths.REPO),
        "at": datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
    }


def status_line(rec: dict) -> str:
    if rec["timed_out"]:
        tag = "TIMEOUT"
    elif rec["stage_only"]:
        tag = "staged" if rec["rc"] == 0 else "STAGE-FAIL"
    elif rec["outcome"] == "converged" and rec["verify_ok"]:
        tag = "converged"
    elif rec["outcome"]:
        tag = rec["outcome"]
    else:
        tag = f"died(rc={rec['rc']})"
    return (f"  {rec['key']:<22} {tag:<12} "
            f"{rec['elapsed_s'] / 60:6.1f} min"
            + (f"  rounds={rec['rounds']}" if rec["rounds"] else "")
            + ("  artifact" if rec["emitted"] else "")
            + ("  HALF-STAGED (re-run needs --force)" if rec.get("half_staged") else ""))


def do_run(a, designs: dict) -> int:
    keys = plan_keys(a, designs)
    if not keys:
        print("sweep: nothing to do — every design already has an artifact.  "
              "Pass --all to include them, or --only to name some.")
        return 0

    d = log_dir(a.bench, ARM)
    progress = os.path.join(d, "progress.jsonl")
    what = "stage" if a.stage_only else "run"
    print(f"sweep: {what} {len(keys)} design(s) of {a.bench} · arm {ARM} · profile {a.profile} · "
          f"{a.jobs} at a time · {a.timeout}s each")
    print(f"       logs {os.path.relpath(d, paths.REPO)}")
    if a.dry_run:
        for k in keys:
            print(f"  {k:<22} -> {os.path.relpath(paths.ws2(a.bench, k, ARM), paths.REPO)}")
            print(f"      {' '.join(launch_cmd(k, designs[k].spec_path, a.profile, a.bench, a.stage_only, a.no_mutation))}")
        return 0

    fleet = Fleet()
    prev = signal.getsignal(signal.SIGINT)

    def on_sigint(sig, frm):                                               # noqa: ANN001, ARG001
        print("\nsweep: interrupted — killing running designs", file=sys.stderr)
        fleet.stop_all()
        signal.signal(signal.SIGINT, prev)

    signal.signal(signal.SIGINT, on_sigint)
    recs = []
    try:
        with ThreadPoolExecutor(max_workers=a.jobs) as pool:
            futs = [pool.submit(run_one, k, designs[k].spec_path, a, fleet) for k in keys]
            # As they finish, not in submission order: a 40-minute design should not hold back
            # the record of eight that already landed, and the journal is what a second terminal
            # is tailing to see where the sweep is.
            for f in as_completed(futs):
                rec = f.result()
                append(progress, rec)
                recs.append(rec)
                print(status_line(rec) + f"   [{len(recs)}/{len(keys)}]", flush=True)
    finally:
        signal.signal(signal.SIGINT, prev)

    ok = sum(1 for r in recs if (r["rc"] == 0 if r["stage_only"] else
                                 r["outcome"] == "converged" and r["verify_ok"]))
    print(f"\nsweep: {ok}/{len(recs)} {'staged' if a.stage_only else 'converged'} · "
          f"journal {os.path.relpath(progress, paths.REPO)}")
    if not a.stage_only:
        print("       `python3 -m leanrtl.sweep --bench %s --report` to score and tabulate."
              % a.bench)
    return 0 if ok == len(recs) else 3


def plan_keys(a, designs: dict) -> list[str]:
    keys = sorted(designs)
    if a.only:
        want = [k.strip() for k in a.only.split(",") if k.strip()]
        missing = [k for k in want if k not in designs]
        if missing:
            sys.exit(f"sweep: {a.bench} has no design named {', '.join(missing)}")
        keys = want
    if not a.all:
        keys = [k for k in keys if not attempted(a.bench, k, ARM)]
    return keys


# --------------------------------------------------------------------------------------------
# report


def score_one(key: str, bench: str, arm: str) -> int:
    """Shell out to `score`.  A workspace whose artifact will not compile is a row, not a stop."""
    p = subprocess.run([sys.executable, "-m", "leanrtl.score", "--key", key,
                        "--bench", bench, "--arm", arm],
                       cwd=paths.METHOD, capture_output=True, text=True)
    return p.returncode


def index_one(key: str, bench: str) -> int:
    """Regenerate this design's own `RESULTS.md`, the way `accu`'s was made."""
    p = subprocess.run([sys.executable, "-m", "leanrtl.compare", "--key", key, "--all", "--index"],
                       cwd=paths.METHOD, capture_output=True, text=True)
    return p.returncode


def collect(bench: str, key: str, arm: str) -> dict:
    """Everything the tables need about one workspace, read from what the run itself wrote.

    No gate is recomputed here.  `verify.json` is the gate report; a second implementation of
    "did this pass" that lived in a reporting script would be the one that eventually disagreed,
    and it would disagree in a table rather than in a run, where nobody would catch it.
    """
    ws = paths.ws2(bench, key, arm)
    s = _read_json(os.path.join(ws, "summary.json"))
    v = (s.get("verify") or {}) or _read_json(os.path.join(ws, "verify.json"))
    verdict = _read_json(os.path.join(ws, "out", f"{key}.verdict.json"))
    mut = _read_json(os.path.join(ws, "out", "proof_mutation.json"))
    gates = v.get("gates") or {}
    scope = ((v.get("design") or {}).get("proof_scope") or {}).get("scope") or {}
    return {
        "key": key,
        "exists": os.path.isdir(ws),
        "emitted": os.path.isfile(os.path.join(ws, "out", f"{key}.v")),
        "outcome": s.get("outcome"),
        "rounds": len(s.get("rounds") or []) or None,
        "elapsed_s": s.get("elapsed_s"),
        "gates": gates,
        "n_gates_pass": sum(1 for g in GATES if gates.get(g)),
        "n_gates": sum(1 for g in GATES if g in gates),
        "failed_gates": [g for g in GATES if g in gates and not gates[g]],
        "scope": scope,
        # `proof_mutation.json` calls it `mutation_score` and spells it "10/10 (100%)".  `killed`
        # and `survived` are that same fact as integers; `mutants` is NOT — it counts what was
        # ATTEMPTED, and the two differ by whatever `excluded` holds.  All four are kept so the
        # table can say which of them it means.
        "mutation_killed": mut.get("killed"),
        "mutation_survived": mut.get("survived"),
        "mutation_attempted": mut.get("mutants"),
        "mutation_excluded": sum(v for k, v in (mut.get("excluded") or {}).items()
                                 if isinstance(v, int)),
        "mutation_score": mut.get("mutation_score"),
        "verdict": verdict.get("status"),
    }


def _mutation_cell(r: dict) -> str:
    """The mutation column: killed over ADMISSIBLE, never killed over attempted.

    `proof_mutation.json` excludes a mutant that does not elaborate, on the stated ground that it
    is evidence about the mutation operator rather than about the proof.  So `mutants` counts what
    was tried and `killed + survived` counts what could be judged, and the two part company
    exactly when an operator produced Lean that will not build.

    Dividing by the attempted count there prints `0/9` for a design whose file says
    `"0/0 — undefined"` — it turns "no mutant was admissible" into "the proof caught none of nine",
    which is the opposite claim, is the one a reader would quote out of a results table, and is
    indistinguishable in the column from a genuinely vacuous proof.  `Prob141_count_clock` is the
    case that showed it: all nine mutants `impl_broken`, a `trace/pins/any` proof, and a column
    that read as worthless.

    A run with `--no-mutation` wrote no file at all, so every field is None and the cell is `—`:
    not measured and measured-as-nothing are different facts and get different marks.
    """
    killed, survived = r["mutation_killed"], r["mutation_survived"]
    if killed is None or survived is None:
        return "—"
    admissible = killed + survived
    if not admissible:
        return f"undef ({r['mutation_excluded']} excl)"
    cell = f"{killed}/{admissible}"
    return cell + (f" ({r['mutation_excluded']} excl)" if r["mutation_excluded"] else "")


def summary_md(bench: str, arm: str, rows: list[dict]) -> str:
    n = len(rows)
    conv = sum(1 for r in rows if r["outcome"] == "converged")
    emit = sum(1 for r in rows if r["emitted"])
    green = sum(1 for r in rows if r["n_gates"] and r["n_gates_pass"] == r["n_gates"])
    passed = sum(1 for r in rows if r["verdict"] == "func_pass")
    now = datetime.datetime.now().astimezone().isoformat(timespec="seconds")

    def pct(x: int) -> str:
        return f"{x}/{n}" + (f" ({100 * x / n:.0f}%)" if n else "")

    out = [
        f"# leanRTL sweep — {bench}, arm `{arm}`",
        "",
        f"Generated {now} by `python3 -m leanrtl.sweep --bench {bench} --arm {arm} --report`.",
        "Every number is read from what a run wrote — `summary.json`, `verify.json`,",
        "`out/<key>.verdict.json`, `out/proof_mutation.json`. Nothing is recomputed here.",
        "",
        "| | |",
        "|---|---|",
        f"| designs with a workspace | {n} |",
        f"| converged | {pct(conv)} |",
        f"| emitted Verilog | {pct(emit)} |",
        f"| all gates green | {pct(green)} |",
        f"| benchmark `func_pass` | {pct(passed)} |",
        "",
        "`outcome` is `launch`'s: **converged** every step green through certify · "
        "**unresolved** S and D could not agree within the profile's challenge bound · "
        "**failed** a step returned problems. A blank means the run wrote no summary.",
        "",
        "| design | outcome | rounds | gates | scope | mutation | verdict | min |",
        "|---|---|---:|---|---|---:|---|---:|",
    ]
    for r in sorted(rows, key=lambda r: r["key"]):
        g = (f"{r['n_gates_pass']}/{r['n_gates']}" if r["n_gates"] else "—")
        if r["failed_gates"]:
            g += " ✗" + ",".join(r["failed_gates"])
        sc = r["scope"]
        scope = (f"{sc.get('time', '?')}/{sc.get('observed', '?')}/{sc.get('reset', '?')}"
                 if sc else "—")
        mut = _mutation_cell(r)
        mins = f"{r['elapsed_s'] / 60:.0f}" if r["elapsed_s"] else "—"
        out.append(f"| `{r['key']}` | {r['outcome'] or '—'} | {r['rounds'] or '—'} | {g} "
                   f"| {scope} | {mut} | {r['verdict'] or '—'} | {mins} |")
    out += [
        "",
        "`scope` is `time/observed/reset` from `verify.design.proof_scope` — what the proof",
        "actually covers. `trace/pins/any` is the strong form: every cycle of every legal input",
        "stream, at the pins, under an arbitrary reset stream.",
        "",
        "`mutation` is killed over **admissible** mutants. `n excl` counts mutants dropped for",
        "not elaborating — those say something about the mutation operator and nothing about the",
        "proof, so they are never a denominator. `undef` means none was admissible, which is not",
        "a score of zero. `—` means the run was launched with `--no-mutation` and never asked.",
        "",
        f"Per-design logs: `data/logs/sweep/{bench}-{arm}/<key>.log`; "
        f"one JSON line per run in `progress.jsonl`.",
        "",
    ]
    return "\n".join(out)


def do_report(a, designs: dict) -> int:
    keys = sorted(designs)
    if a.only:
        keys = [k.strip() for k in a.only.split(",") if k.strip()]
    keys = [k for k in keys if os.path.isdir(paths.ws2(a.bench, k, a.arm))]
    if not keys:
        print(f"sweep: no workspace under {os.path.relpath(paths.part2(a.bench), paths.REPO)} "
              f"for arm {a.arm!r} — nothing to report.", file=sys.stderr)
        return 2

    # `certified`, not "has a .v": handing an uncertified artifact to `score` produces a verdict
    # file labelled `final` for a design the pipeline never emitted.  See `certified`.
    scorable = [k for k in keys if certified(a.bench, k, a.arm)]
    print(f"sweep: reporting {len(keys)} workspace(s) · "
          + (f"scoring {len(scorable)} artifact(s)" if not a.no_score
             else "not scoring (--no-score): reading what is already on disk"))
    if not a.no_score:
        with ThreadPoolExecutor(max_workers=a.jobs) as pool:
            list(pool.map(lambda k: score_one(k, a.bench, a.arm), scorable))
        with ThreadPoolExecutor(max_workers=a.jobs) as pool:
            list(pool.map(lambda k: index_one(k, a.bench), scorable))

    rows = [collect(a.bench, k, a.arm) for k in keys]
    md = summary_md(a.bench, a.arm, rows)
    d = log_dir(a.bench, a.arm)
    os.makedirs(d, exist_ok=True)
    out = os.path.join(d, "SUMMARY.md")
    with open(out, "w") as f:
        f.write(md)
    with open(os.path.join(d, "SUMMARY.json"), "w") as f:
        json.dump({"bench": a.bench, "arm": a.arm, "rows": rows,
                   "at": datetime.datetime.now().astimezone().isoformat(timespec="seconds")},
                  f, indent=1, default=str)
    print(md)
    print(f"sweep: written {os.path.relpath(out, paths.REPO)}")
    return 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--bench", required=True,
                    help="which corpus to sweep.  Required: it decides the row set, and a "
                         "default that was right once would be silently wrong on the next one.")
    ap.add_argument("--profile", default="two-author")
    ap.add_argument("--arm", default=ARM,
                    help=f"report only; a sweep can produce {ARM!r} and nothing else")
    ap.add_argument("--jobs", type=int, default=8)
    ap.add_argument("--only", default="", help="comma-separated keys, instead of the whole corpus")
    ap.add_argument("--all", action="store_true",
                    help="include designs that already emitted Verilog (they are re-run in place; "
                         "launch still refuses to overwrite without --force, which is not passed)")
    ap.add_argument("--timeout", type=int, default=DEFAULT_TIMEOUT,
                    help=f"per-design wall clock, seconds (default {DEFAULT_TIMEOUT})")
    ap.add_argument("--stage-only", action="store_true",
                    help="build the workspaces and stop, without spending an authoring session")
    ap.add_argument("--no-mutation", action="store_true",
                    help="pass --no-mutation to every launch: certify runs the same gates and "
                         "skips the mutation measurement, leaving that column empty")
    ap.add_argument("--dry-run", action="store_true",
                    help="print the commands and the workspaces they would write, and stop")
    ap.add_argument("--report", action="store_true",
                    help="score the artifacts on disk and write SUMMARY.md; runs nothing")
    ap.add_argument("--no-score", action="store_true",
                    help="with --report, tabulate what is already on disk without re-scoring")
    a = ap.parse_args(argv)

    if a.jobs < 1:
        sys.exit("sweep: --jobs must be at least 1")
    if not a.report and a.arm != ARM:
        sys.exit(f"sweep: a sweep produces the {ARM!r} arm and nothing else — the decided arm's "
                 f"prose is a Part 1 deliverable that exists per design or not at all.  Run those "
                 f"with `launch --decided`.  (--arm is for --report.)")
    try:
        ad = adapter.load(a.bench)
    except Exception as e:                                                 # noqa: BLE001
        sys.exit(f"sweep: could not load {a.bench}'s adapter: {type(e).__name__}: {e}\n"
                 f"       installed: {', '.join(adapter.installed()) or '—'}")
    designs = ad.design_map()

    if a.report:
        return do_report(a, designs)
    return do_run(a, designs)


if __name__ == "__main__":
    sys.exit(main())
