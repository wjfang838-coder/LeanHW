#!/usr/bin/env python3
"""Running Lean, and reading what it actually said.

Three things this module refuses to get wrong, each because getting it wrong has a recorded
cost in the tree this method comes from:

  * **What counts as an error.**  Not "the output contains the substring `error`" — a
    specification that prints `error_flag=1` from an `#eval` is not a failed elaboration.
    Lean's own diagnostics are `<file>:<line>:<col>: error: ...`, and that is what is matched.

  * **What counts as proved.**  A tactic that *errors* still leaves the declaration in the
    environment with a `sorryAx` body and no `sorry` anywhere in the source.  So every generated
    certificate is followed by `#print axioms`, and the axiom line is parsed: anything resting on
    `sorryAx` is reported as **admitted**, never as proved.

  * **Where Lean runs.**  Bare `lean` with `LEAN_PATH` naming exactly the oleans the caller
    chose, with the run directory as the working directory.  Not `lake env lean` from the
    repository root: the root is where everything else in this repository lives, and pointing a
    stage that must derive its result from one prose file at the directory holding the other half
    of the pipeline is the kind of thing that stays true only as long as nobody tests it.

Both halves of leanSilicon run Lean and neither knows about the other, so nothing here names a
library, a prelude or a finding vocabulary.  The caller passes its own.
"""
from __future__ import annotations

import json
import os
import re
import resource
import subprocess
import time

LEAN = os.path.expanduser("~/.elan/bin/lean")

# Lean's per-task thread stack, in Kb.  Many of the claims this framework makes are closed by
# `decide` or read off an `#eval`, and both evaluate a whole finite domain by recursion on the C
# stack: `determinedEverywhere` over a few hundred observations and a couple of hundred
# configurations is deep enough to exhaust Lean's 8 Mb default, and the failure mode is the worst
# kind — the process aborts with "Stack overflow detected", so the file produces no finding line
# and no `#print axioms` line, and a caller reading only the output cannot distinguish "the claim
# is false" from "the evaluator ran out of room".  64 Mb is not a licence to state bigger claims;
# it is what stops the size of the domain from deciding whether a true claim can be checked.
TSTACK_KB = 65536

# How long one elaboration may take.  A wall-clock cap and nothing else — it does not bound the
# size of any claim, and a file that exceeds it comes back as `exit=124`, which is why
# `why_failed` below goes out of its way to keep that distinguishable from a false claim.  Raise
# it with `LEANSILICON_LEAN_TIMEOUT` when a case is genuinely large or the machine is loaded; do
# not raise it to make a slow proof look like a fast one, because the elapsed time is recorded
# beside the result in every step document.
DEFAULT_TIMEOUT = int(os.environ.get("LEANSILICON_LEAN_TIMEOUT", "900"))

# Lean's own diagnostics.  The optional `(...)` is the message tag Lean 4.29 attaches to the
# diagnostics it has classified -- `error(lean.unknownIdentifier):` rather than `error:` -- and
# leaving it out of this pattern does not merely lose a line of context.  `run` reports
# `errors: []` for a file whose every failure is tagged, `why_failed` then falls back to the
# summary, and a stage-2 pass gate hands the author back `exit=1  2.4s  0 finding(s)` in place of
# the sentence naming the identifier that does not exist.
ERROR_RE = re.compile(r"(?m)^(?:\S*?):\d+:\d+: error(?:\([^)\n]*\))?:")
AXIOM_RE = re.compile(r"(?m)^'([^']+)' depends on axioms: \[([^\]]*)\]")
NOAXIOM_RE = re.compile(r"(?m)^'([^']+)' does not depend on any axioms")


def _unlimited_stack() -> None:
    """Raise the child's own stack limit to the hard maximum before `exec`.

    `--tstack` sizes the threads Lean spawns for elaboration tasks, and for a long time that was
    the only stack this framework had to worry about.  It is not the only one.  Writing an olean
    walks the finished environment on the *calling* thread, which is the process's main stack and
    is governed by `RLIMIT_STACK` instead — so a file that elaborates in 46s with a 64 Mb task
    stack can abort with "Stack overflow detected" the moment the same run is asked for
    `-o Partial.olean`, and raising `--tstack` to a gigabyte does not move it at all.  One case
    failed its output step exactly this way while its formalization step had passed on the same
    bytes: `decide +kernel` over that case's configuration space leaves proof terms deep enough
    that the serialiser, not the evaluator, is what runs out of room.

    The failure is worth removing rather than working around, because it is silent in the way
    that matters: exit -6 arrives with an empty error list and zero findings, so a caller reading
    the parsed result sees a step that produced nothing and cannot tell that from a step whose
    claims were false.
    """
    try:
        soft, hard = resource.getrlimit(resource.RLIMIT_STACK)
        if soft != hard:
            resource.setrlimit(resource.RLIMIT_STACK, (hard, hard))
    except (ValueError, OSError):
        pass


def build_olean(src: str, out: str, force: bool = False) -> str:
    """Compile one Lean file to an olean, once.  Returns the olean path.

    Stale-checked by mtime rather than by content, which is the opposite of what
    `common/provenance.py` does and is right here for a different reason: this compiles a file
    this repository owns, in place, and the question is "has the source been edited since",
    which is exactly what an mtime answers.  Provenance asks "is this tree a copy of that tree",
    which an mtime cannot answer at all.
    """
    os.makedirs(os.path.dirname(os.path.abspath(out)), exist_ok=True)
    if not force and os.path.isfile(out) and os.path.getmtime(out) >= os.path.getmtime(src):
        return out
    r = subprocess.run([LEAN, f"--tstack={TSTACK_KB}", "-o", out, src],
                       preexec_fn=_unlimited_stack, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"{src} does not compile:\n{r.stdout}{r.stderr}")
    return out


def run(path: str, cwd: str | None = None, lean_path: list[str] | None = None,
        timeout: int | None = None, emit_olean: bool = False,
        prefix: str = "LEANSPEC:") -> dict:
    """Elaborate one file.  Returns everything a caller could want to check, parsed.

    `LEAN_PATH` is what `lean_path` names *plus the working directory*, so a run's generated
    files can import each other — the run's own semantics — while still seeing nothing else.
    `emit_olean` additionally writes `<stem>.olean` beside the source, which is how one generated
    file becomes importable by the next.

    `prefix` is the marker the Lean side prints its structured findings behind, one JSON object
    per line.  A line that carries the prefix and does not parse is recorded as an *unparseable
    finding* rather than dropped: a finding the Lean side meant to emit and the Python side could
    not read is a fact about the run, and silently skipping it turns a broken emitter into a
    clean result.
    """
    timeout = DEFAULT_TIMEOUT if timeout is None else timeout
    cwd = cwd or os.path.dirname(os.path.abspath(path))
    env = dict(os.environ,
               LEAN_PATH=os.pathsep.join([*(lean_path or []), os.path.abspath(cwd)]))
    base = os.path.basename(path)
    cmd = [LEAN, f"--tstack={TSTACK_KB}"]
    if emit_olean:
        cmd += ["-o", os.path.splitext(base)[0] + ".olean"]
    cmd.append(base)
    t0 = time.time()
    try:
        r = subprocess.run(cmd, cwd=cwd, env=env, preexec_fn=_unlimited_stack,
                           capture_output=True, text=True, timeout=timeout)
        out, code = r.stdout + r.stderr, r.returncode
    except subprocess.TimeoutExpired as e:
        out = (e.stdout or b"").decode("utf-8", "replace") + \
              (e.stderr or b"").decode("utf-8", "replace") + \
              f"\nleansilicon: lean exceeded {timeout}s"
        code = 124
    dt = time.time() - t0

    findings = []
    for line in out.splitlines():
        line = line.strip()
        if line.startswith(prefix):
            try:
                findings.append(json.loads(line[len(prefix):]))
            except ValueError as e:
                findings.append({"query": "unparseable", "raw": line[:400], "why": str(e)})

    axioms: dict[str, list[str]] = {}
    for m in AXIOM_RE.finditer(out):
        axioms[m.group(1)] = [a.strip() for a in m.group(2).split(",") if a.strip()]
    for m in NOAXIOM_RE.finditer(out):
        axioms[m.group(1)] = []

    errors = [l for l in out.splitlines() if ERROR_RE.match(l.strip()) or ERROR_RE.match(l)]
    admitted = sorted(k for k, v in axioms.items() if "sorryAx" in v)
    return {"path": path, "exit": code, "seconds": round(dt, 2), "log": out,
            "findings": findings, "axioms": axioms, "errors": errors, "admitted": admitted,
            "ok": code == 0 and not errors and not admitted}


def summarize(res: dict) -> str:
    bits = [f"exit={res['exit']}", f"{res['seconds']}s", f"{len(res['findings'])} finding(s)"]
    if res["errors"]:
        bits.append(f"{len(res['errors'])} lean error(s)")
    if res["admitted"]:
        bits.append(f"ADMITTED: {', '.join(res['admitted'])}")
    return "  ".join(bits)


def why_failed(res: dict, what: str = "") -> list[str]:
    """The problem strings a failed run should contribute, never an empty list.

    `errors` holds Lean's own `file:line:col: error:` diagnostics, and for the ordinary failure —
    a `decide` that does not close, a name that does not resolve — that is the whole story.  The
    two failures that are not ordinary produce none of them.  A timeout is killed before it
    prints anything and comes back as exit 124; a stack overflow aborts and comes back as exit -6
    with the abort message on a line no diagnostic regex matches.  A caller that reports `errors`
    alone then writes `ok: false` beside `problems: []`, which is how one case recorded a
    2401-second timeout as a step that failed for no stated reason.

    So: the diagnostics when there are any, and otherwise the summary line, which carries the
    exit code and the elapsed seconds and is enough to tell the two apart.
    """
    if res["ok"]:
        return []
    prefix = f"{what}: " if what else ""
    out = list(res["errors"][:20])
    out += [f"{prefix}ADMITTED (rests on sorryAx): {a}" for a in res["admitted"]]
    if not out:
        out.append(prefix + summarize(res))
    return out
