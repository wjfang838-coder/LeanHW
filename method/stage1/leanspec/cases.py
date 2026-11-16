#!/usr/bin/env python3
"""Cases: one prose specification, one directory, one ledger.

A case is the unit leanSpec works on.  It is created from a natural-language specification and a
name, and it owns everything the run produces.  It knows nothing about a benchmark, a reference
implementation or a testbench, because leanSpec has none of those: the input is prose and the
output is prose, and everything in between is derived from the input.

## The sandbox

Stages 1–4 run against `<case>/sandbox/`, which holds the prose and the Lean working tree the
agent writes.  Nothing else is in it.  The confinement hook in `common/confine.py` makes that a
wall rather than a description — an agent launched here can reach this directory and the
toolchain, and denies everything else.

## The ledger

Every step boundary and every designer query appends one line to `<case>/logs/ledger.jsonl`.
Two things are then checkable rather than promised:

  * **order** — no `oracle_query` event may precede the witness it belongs to, and none may
    precede diagnosis.  `audit()` reports a violation as a hard failure.
  * **cost** — "number of designer queries required" is a count of lines, not an estimate.

An append-only log is used rather than a summary because a summary is written by the same process
that would have to admit the violation.  The ledger is the audit; `common/seal.py` is the
enforcement, and both are wanted:

    the seal   says a stage COULD NOT have asked
    the ledger says a stage DID NOT ask
"""
from __future__ import annotations

import dataclasses
import fcntl
import json
import os

from common import ledger as _ledger, paths, provenance, variant as _variant

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = paths.STAGE1
CASES_DIR = paths.data(paths.PART1)
REGISTRY = os.path.join(CASES_DIR, "CASES.json")

# ------------------------------------------------------------------ the case directory layout
#
# A case directory holds directories only.  A loose file there carries no label saying which step
# owns it, or whether it is an input, an output or scratch, and after nine steps there were a
# dozen of them sitting beside each other with no way to tell.  So:
#
#   authored/   the model's work, and only that
#   sandbox/    the prose and the Lean working tree
#   steps/      the pipeline chain, one file per step
#   out/        the deliverables
#   logs/       raw stdout from Lean, the transcripts, and the append-only ledger
#   state/      the flat artifacts a step materialises before it runs
#
# `state/` is the one that needs saying out loud: those files are a *cache*.  A step materialises
# its inputs there before running, so the previous step's output document is the channel and the
# flat file is only what a tool on disk needs to see.
LOGS_DIR = "logs"
STATE_DIR = "state"
_LOG_SUFFIXES = (".log", ".jsonl", ".txt.log")
_STATE_SUFFIXES = (".json", ".sv")

sha256 = provenance.sha256


def bucket(name: str) -> str:
    """The subdirectory a loose artifact belongs in, or `""` for one that is already placed."""
    if name.endswith(_LOG_SUFFIXES):
        return LOGS_DIR
    if name.endswith(_STATE_SUFFIXES):
        return STATE_DIR
    return ""


@dataclasses.dataclass
class Case:
    """One specification under examination.

    `source` records where the prose came from and is never read back to fetch it: the prose the
    run works on is the copy in the sandbox, hashed at step 00, and a later step that re-read the
    origin could be reading a file that has moved underneath it.

    `bench` names the corpus the prose came from, and is what keeps two datasets' identically
    named designs in two directories.  It defaults to empty and resolves to `paths.LOCAL`, which
    is the honest answer for prose handed over as a file: it came from no benchmark, and saying
    so is better than filing it under one.  The registry stays single — one `CASES.json` listing
    every case with its `bench` — because a per-benchmark registry makes `ls` of all runs a walk
    instead of a read, and the lock that serialises writes to it would become several locks.

    `bak` says this run is kept but is not a reported result: an attempt that never produced an
    `out/`, a superseded round, a directory renamed by hand.  It is a registry field rather than a
    suffix on the name because `dir` is computed from it — a case whose entry and location
    disagree is a case `find()` cannot open — and `archive()` is the only thing that sets it,
    moving the directory in the same locked section.

    The NAME is untouched by any of this.  `accu.c5` stays `accu.c5` in every one of that run's
    173 ledger lines and in each of its step documents; `dir` splits it on the first dot to place
    it under `accu/c5/`.  Renaming the cases to match the new directories would have edited the
    past in order to tidy the present, and the ledger is the audit.
    """
    name: str
    source: str = ""
    why: str = ""
    bench: str = ""
    bak: bool = False

    @property
    def key(self) -> str:
        """The design this case is about: everything before the first dot."""
        return self.name.partition(".")[0]

    @property
    def label(self) -> str:
        """Which run of that design: everything after it, or `base` for an unsuffixed name."""
        return self.name.partition(".")[2] or paths.BASE

    @property
    def dir(self) -> str:
        return paths.case1(self.bench, self.key, self.label, bak=self.bak)

    @property
    def sandbox(self) -> str:
        return os.path.join(self.dir, "sandbox")

    def path(self, *parts: str) -> str:
        """Where an artifact lives.  A bare filename is routed into its bucket."""
        if len(parts) == 1 and (b := bucket(parts[0])):
            os.makedirs(os.path.join(self.dir, b), exist_ok=True)
            return os.path.join(self.dir, b, parts[0])
        return os.path.join(self.dir, *parts)


def registry() -> list[Case]:
    if not os.path.isfile(REGISTRY):
        return []
    with open(REGISTRY) as f:
        return [Case(**c) for c in json.load(f)["cases"]]


def find(name: str) -> Case:
    for c in registry():
        if c.name == name:
            return c
    raise KeyError(f"{name} is not in {os.path.relpath(REGISTRY, ROOT)}")


def register(case: Case) -> Case:
    """Add a case, or update its metadata if it is already there.

    Refuses to change `source` on an existing case.  A case is a run against one specification,
    and repointing it at a different file mid-run leaves a directory whose steps were derived
    from prose that is no longer named anywhere — the chain would still verify internally and
    would describe a document nobody can produce again.

    Read-modify-write on the one file every case reads, so it is locked and the publish is a
    rename.  It used to be three unsynchronised calls — `json.load`, a membership test,
    `json.dump` into `open(..., "w")` — and concurrency is the normal case: a sweep creates
    several cases at once, and more than one sweep can be running.  `"w"` truncates, so a slow
    writer left its tail sitting after a faster writer's complete document and the file became
    one valid JSON object followed by a fragment.  Every reader then died on it, including agents
    mid-run in other sweeps, who were handed the decode error as though it were the checker
    rejecting their work.  A corrupt registry is not a local failure.
    """
    os.makedirs(CASES_DIR, exist_ok=True)
    with open(REGISTRY + ".lock", "w") as lf:
        fcntl.flock(lf, fcntl.LOCK_EX)
        cases = registry()
        for i, c in enumerate(cases):
            if c.name == case.name:
                if case.source and c.source and os.path.realpath(case.source) != \
                        os.path.realpath(c.source):
                    raise ValueError(
                        f"{case.name} already exists and was created from {c.source}.  Pointing "
                        f"it at {case.source} would leave its finished steps describing prose "
                        f"that is no longer named anywhere.  Use a new name.")
                cases[i] = dataclasses.replace(c, source=case.source or c.source,
                                               why=case.why or c.why)
                break
        else:
            cases.append(case)
        tmp = REGISTRY + f".tmp.{os.getpid()}"
        with open(tmp, "w") as f:
            json.dump({"cases": [dataclasses.asdict(c)
                                 for c in sorted(cases, key=lambda c: c.name)]}, f, indent=1)
            f.flush()
            os.fsync(f.fileno())
        os.replace(tmp, REGISTRY)
    return find(case.name)


def archive(name: str, on: bool = True) -> Case:
    """Move a case into `<key>/bak/`, or back out.  Directory and registry, or neither.

    `bak` is not a label somebody applies to a directory afterwards — that is exactly the failure
    this layout was reorganised to stop, and `data/part2/rtllm/accu/bak/decided.r1prose` is the
    directory that proves it: a suffix added by hand, a `run.json` still saying something else,
    and nothing that ever compared them.  Here the flag and the location are one operation.

    The order is rename-then-write, with the rename undone if the write fails.  It cannot be made
    atomic across a directory and a JSON file, so the question is only which inconsistency is
    survivable: a registry that still points at the old location leaves `find()` working and the
    move simply not to have happened, while a registry updated ahead of a rename that then failed
    leaves every subsequent command looking in a directory that does not exist.
    """
    with open(REGISTRY + ".lock", "w") as lf:
        fcntl.flock(lf, fcntl.LOCK_EX)
        cases = registry()
        i, case = next(((i, c) for i, c in enumerate(cases) if c.name == name), (None, None))
        if case is None:
            raise KeyError(f"{name} is not in {os.path.relpath(REGISTRY, ROOT)}")
        if case.bak == on:
            return case
        src, dst = case.dir, dataclasses.replace(case, bak=on).dir
        moved = False
        if os.path.isdir(src):
            if os.path.exists(dst):
                raise FileExistsError(
                    f"{dst} already exists.  Two directories claiming to be {name} is the "
                    f"ambiguity this move is supposed to remove, so it is refused rather than "
                    f"merged.")
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            os.rename(src, dst)
            moved = True
        try:
            cases[i] = dataclasses.replace(case, bak=on)
            tmp = REGISTRY + f".tmp.{os.getpid()}"
            with open(tmp, "w") as f:
                json.dump({"cases": [dataclasses.asdict(c)
                                     for c in sorted(cases, key=lambda c: c.name)]}, f, indent=1)
                f.flush()
                os.fsync(f.fileno())
            os.replace(tmp, REGISTRY)
        except Exception:
            if moved:
                os.rename(dst, src)
            raise
    return find(name)


def prose(case: Case) -> str:
    """The specification this run is about: the sandbox copy, not the origin."""
    p = os.path.join(case.sandbox, "spec.txt")
    if not os.path.isfile(p):
        raise FileNotFoundError(
            f"{case.name} has no prose in its sandbox.  A case is created from a specification; "
            f"run `new` before running a step.")
    with open(p, errors="replace") as f:
        return f.read()


def stage_sandbox(case: Case, text: str) -> str:
    """Put the prose, and only the prose, where the agent will work."""
    os.makedirs(case.sandbox, exist_ok=True)
    p = os.path.join(case.sandbox, "spec.txt")
    with open(p, "w") as f:
        f.write(text)
    log(case, "sandbox", spec_sha256=sha256(text), bytes=len(text))
    return p


# ------------------------------------------------------------------------------- ledger

def log(case: Case, event: str, **fields) -> dict:
    """One ledger line, in the case's own log.  See `common/ledger.py` for why it is a `flock`."""
    return _ledger.log(case.dir, event, case=case.name, **fields)


def ledger(case: Case) -> list[dict]:
    return _ledger.read(case.dir)


# Every way an answer from the designer can enter the run.  All three are checked for order,
# and the reason is that only the first of them is a *cost*:
#
#   oracle_query   the designer was asked, and answered.  This is the number the method reports.
#   oracle_replay  step 06 ran again over an answer already on disk.  No question was put.
#   oracle_reuse   two witnesses turned out to be the same question -- same context, same menu --
#                  so the second reads the first's answer.  No question was put.
#   oracle_session one sitting in which a whole round's questions were put at once.  It carries no
#                  verdict of its own -- the per-question events do -- but it is the moment the
#                  designer's answers entered the run, so the ordering check has to see it.  A
#                  sitting is not a fourth way to be answered; it is the container for the first.
#
# A replay and a reuse spend nothing, and if the ordering check only looked at `oracle_query` a
# run whose answers were all already cached would pass it while having consulted the designer's
# verdicts before the diagnosis that is supposed to justify them.  The claim is about when an
# answer became available to the run, not about who paid for it.
_ANSWERS = ("oracle_query", "oracle_replay", "oracle_reuse", "oracle_session")


def audit(case: Case) -> dict:
    """Did any answer from the designer reach the run before there was a witness to justify it?

    This is the whole auditable claim of leanSpec's method: a question is asked of the designer
    only when the formal diagnosis has produced a finding and the witness search has produced a
    concrete separating context for it.  An answer with no witness before it is a question that
    was not earned, and it does not matter how good the answer was.

    Timestamps are ISO strings and compare lexicographically because they carry a fixed-width
    offset, so ordering is a string comparison and does not need parsing.
    """
    evs = ledger(case)
    first_a = next((e for e in evs if e.get("event") in _ANSWERS), None)
    first_w = next((e for e in evs if e.get("event") == "witness"), None)
    diag = next((e for e in evs if e.get("event") == "diagnose"), None)
    viol = []
    if first_a:
        what = first_a["event"]
        if first_w is None:
            viol.append(f"a designer answer entered the run ({what}) and no witness event "
                        f"precedes it")
        elif first_a["ts"] < first_w["ts"]:
            viol.append(f"{what} at {first_a['ts']} precedes the first witness "
                        f"at {first_w['ts']}")
        if diag and first_a["ts"] < diag["ts"]:
            viol.append(f"{what} at {first_a['ts']} precedes diagnosis at {diag['ts']}")
    corrupt = [e for e in evs if e.get("event") == "corrupt"]
    if corrupt:
        viol.append(f"{len(corrupt)} unreadable line(s) in an append-only log")
    # An ablation can remove the thing an invariant is ABOUT.  An arm with no formalization has
    # no step 05, so no witness event ever exists, so every query above is unjustified — and
    # both obvious readings are wrong: reported as a violation it says the run was illegal, when
    # having no witnesses is that arm's definition; suppressed, it turns off the only check that
    # makes this half's claim auditable and prints `clean: true` over the top.
    #
    # So the tree declares it in `VARIANT.json` and the findings move to `waived`, carrying the
    # stated reason.  `clean` then describes what was left, and a reader who sees `waived`
    # non-empty cannot read the row as a method run.  `data/` waives nothing and cannot: the
    # default root has no manifest, so `waived()` returns `""` there for every invariant.
    excuse = _variant.waived("witness_before_answer")
    waived: list[str] = []
    if excuse and viol:
        waived, viol = [f"{v}   [waived: {excuse}]" for v in viol], []
    return {"case": case.name,
            "events": len(evs),
            # Reported apart, because they mean different things: the first is what the method
            # cost, the other two are what re-running it did not cost.
            "oracle_queries": sum(1 for e in evs if e.get("event") == "oracle_query"),
            "oracle_replays": sum(1 for e in evs if e.get("event") == "oracle_replay"),
            "oracle_reuses": sum(1 for e in evs if e.get("event") == "oracle_reuse"),
            # How many times a designer was sat down, as against how many questions they were
            # asked.  Both are costs and neither substitutes for the other: a method that asks
            # twenty questions in one sitting has interrupted a designer once and used twenty of
            # their judgements, and quoting either number alone flatters it.
            "oracle_sittings": sum(1 for e in evs if e.get("event") == "oracle_session"
                                   and not e.get("replayed")),
            "seal_violations": sum(1 for e in evs if e.get("event") == "seal_violation"),
            "variant": _variant.describe()["name"],
            "violations": viol,
            "waived": waived,
            "clean": not viol}
