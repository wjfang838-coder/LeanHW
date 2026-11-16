#!/usr/bin/env python3
"""RTLLM: 50 designs, each shipping a prose description, a testbench and a reference RTL.

Installed data, not method — this file lives under `benchmarks/`, which is gitignored, and the
dataset itself is a symlink to a checkout outside both.  Nothing here may look at how the
Verilog it grades was produced.

## The oracle

Two are available and neither is implicit.  Which one ran is stamped into every verdict, because
a verdict that does not name its simulator reads as a fact about the design and gets carried
across a toolchain change that invalidates it.

`RTLLM_ORACLE=icarus` (the default) is Icarus Verilog, locally: open, reproducible, no license,
no network.  It is the one CI can run.

`RTLLM_ORACLE=vcs` is Synopsys VCS on the remote server named by `VCS_REMOTE`.  **This is the
oracle RTLLM itself uses** — every makefile in the dataset invokes `vcs`, and the published RTLLM
numbers come from it.  The two simulators do not agree about this benchmark: several of these
testbenches use constructs Icarus cannot elaborate (`ring_counter`'s testbench initialises a
whole array in its declaration and Icarus answers `sorry:`), and a design recorded as unpassable
under Icarus may elaborate and pass under VCS.  So an Icarus number here is not comparable with a
published RTLLM number and a VCS number is.

The remote backend was deliberately absent from an earlier version of this file, on the grounds
that it introduces an `oracle_unavailable` state that is not a property of any design.  That
objection is answered rather than dismissed: `oracle_unavailable` is a first-class status in
`Verdict`, held apart from every failure status, and this adapter returns it — never
`compile_fail` — when the host is unreachable, the license is refused or VCS is missing.  A run
that could not be measured says so.  What is NOT ported from that earlier version is the repair
overlay and the two dataset bridges: those change what is being graded, and the reasons below
still stand.

## The harness is the testbench AND the files it reads

Five of the fifty testbenches call `$readmemh`/`$fopen` on a relative path: `signal_generator`
reads `tri_gen.txt`, `multi_booth_8bit` reads `test_data.dat`, `alu` reads `reference.dat`,
`calendar` reads `reference.txt`, and `asyn_fifo` reads `wfull.txt`, `rempty.txt` and
`tdata.txt`.  **All seven files ship**, in the design's own dataset directory, beside the
testbench that names them.

An earlier draft of this docstring said the last three did not ship and that the designs reading
them were therefore unwinnable.  That was wrong, and the way it was wrong is worth keeping: those
designs were failing because this adapter compiled in a scratch directory containing only the
candidate, so `$readmemh` resolved against a cwd where the file was absent.  "The simulator
cannot open it" was read as "the dataset does not have it", and a harness bug was written down as
a property of the benchmark — the exact substitution `_rundir` now exists to prevent.
`signal_generator` printed `$readmemh: Unable to open` and scored `func_fail` on the same
mechanism.  `calendar` scores `func_pass` once the file is staged, which is what settled it.

So every file the testbench reads is staged next to the candidate, because it is part of the
harness in exactly the way the testbench is.  `makefile` and `verified_<key>.v` are never staged:
the first is dead weight and the second is the answer key.

## Passing is what the testbench says passing is

Each testbench ends by printing `===========Your Design Passed===========`,
`===========Error===========`, or `===========Failed===========`.  This adapter reads that line
and nothing else.  It does not
count mismatches, does not diff waveforms, and does not consult the reference implementation —
`verified_<key>.v` is present in the dataset and is never opened, because a candidate scored
against the reference rather than against the testbench is scored against an answer key that the
prose does not contain.

The fifty testbenches do not agree on how to space that line — 28 write it closed up and 22 put
spaces around the words — so the comparison ignores the `=` padding and the whitespace inside it.
Only 13 of the fifty carry an `Error` line at all.  Several use `Failed`, and 29 print a tally
(`=========== Test completed with 3/20 failures ===========`), and for five designs that tally is
the only mark a failing run leaves.  All verdict dialects are read; see `PASS_RE`, `FAIL_RE` and
`TALLY_RE`, and note that a nonzero tally outranks a `Passed` line.

A run that prints none of these is `no_verdict`, which is kept apart from `func_fail` on
purpose.
A testbench that ran off the end of its stimulus, or that `$finish`ed from the wrong initial
block, produces no line at all — and reading silence as failure attributes the harness's problem
to the design.

## What this adapter deliberately does not have

The version of this adapter in the previous repository carried a *repair overlay* (a corrected
prose or testbench per design, selectable with an environment variable) and two *dataset bridges*
that retried compilation after declaring a missing parameter or renaming the module.  Both are
experiment, not benchmark: the overlay changes what is being graded and the bridges change what
counts as a compile failure.

They are omitted rather than ported.  What that costs is worth stating: several of these 50
designs have a prose description that contradicts their own testbench — a module name spelled
one way in the text and another in the instantiation, a testbench that parameter-overrides a
module whose description never mentions parameters, a testbench that instantiates the design
*positionally* in an order the prose does not give (`LFSR DUT(out, clk, rst)`) — and against
those, a correct reading of the prose scores `compile_fail`.  That is a real property of this
dataset, and reporting it as one is more useful than quietly repairing it: a benchmark whose
defects have been patched out cannot be used to argue that reading the prose carefully is what
helped.  Switching the oracle to VCS does not repair any of them; it removes a different and
unrelated set of failures, the ones that were Icarus's.
"""
from __future__ import annotations

import glob
import hashlib
import os
import re
import shutil
import subprocess
import tempfile
import uuid

HERE = os.path.dirname(os.path.abspath(__file__))
DATASET = os.path.join(HERE, "dataset")

try:
    from _adapter import Adapter, Design, Verdict
except ModuleNotFoundError:                    # direct execution, e.g. the self-check at the foot
    # `common.adapter.load` binds itself as `_adapter` before running this file, so the import
    # above is the normal path and this one only fires when nobody called `load` — running this
    # file as a script with `method/` on PYTHONPATH.  It resolves to the SAME module object, not
    # a copy, so the classes are the ones every other adapter implements.
    #
    # What stood here was `sys.path.insert(0, <repo>/adapters)` followed by the bare import.  The
    # directory consolidation deleted `adapters/`, so the insert has been adding a nonexistent
    # path for as long as this file has been here and the foot of it has never once run.
    from common.adapter import Adapter, Design, Verdict          # noqa: E402

PASS = "===========Your Design Passed==========="
FAIL = "===========Error==========="

# The same two lines, read as what they mean rather than as how they were typed.  RTLLM's fifty
# testbenches are fifty separately-written files and they do not agree on the spacing: 28 print
# `===========Your Design Passed===========` and 22 print
# `=========== Your Design Passed ===========`.  Matching the literal caught only the first
# spelling, so twenty-two designs could never be scored `func_pass` whatever they emitted — they
# came out `no_verdict`, and a whole-corpus sweep read eighteen genuine passes as unreadable runs.
# Note that collapsing runs of whitespace does NOT fix this: the difference is whether there is a
# space between `===========` and `Your` at all, not how many.  The `=` padding is decoration and
# is treated as such.
PASS_RE = re.compile(r"=+\s*Your\s+Design\s+Passed\s*=+")
FAIL_RE = re.compile(r"=+\s*(?:Error|Failed)\s*=+", re.I)

# A third dialect, and the one that matters most.  29 of the fifty testbenches also print a tally
# — `=========== Test completed with 3/20 failures ===========`, in eight different spacings, with
# or without the `=` padding, with or without a denominator, and once saying `errors.` instead of
# `failures` — and for five designs that tally is the ONLY thing they print when the design is
# wrong: they carry no `Error` line, so a failing run left no line either reader recognised and
# came out `no_verdict`.  A testbench that counted its own failures reached a verdict.  Reading
# that as silence attributes the design's failure to the harness, which is the one direction of
# error this adapter is built to avoid making.
TALLY_RE = re.compile(r"Test\s+completed\s+with\s+(\d+)\s*(?:/\s*\d+)?\s*(?:failures|errors)",
                      re.I)


def camel_of(key: str) -> str:
    return "".join(p[0].upper() + p[1:] for p in re.split(r"[_\-.]", key) if p)


class RTLLM(Adapter):
    name = "rtllm"
    oracle = "icarus"

    def designs(self) -> list[Design]:
        out = []
        for p in sorted(glob.glob(os.path.join(DATASET, "*", "*", "*",
                                               "design_description.txt"))):
            d = os.path.dirname(p)
            key = os.path.basename(d)
            out.append(Design(
                key=key, bench=self.name, spec_path=p,
                # The directory name IS the module name for all 50; where a testbench disagrees
                # that is a defect of the dataset and shows up as `compile_fail`, which is what
                # it is.  Guessing the name out of the testbench instead would be reading the
                # answer key.
                toplevel=key, camel=camel_of(key),
                meta={"dir": d,
                      "category": os.path.relpath(os.path.dirname(os.path.dirname(d)), DATASET),
                      "testbench": os.path.join(d, "testbench.v")}))
        return out

    def stage(self, design: Design, ws: str) -> None:
        """The prose, and only the prose.

        Not the testbench, not the reference, not the makefile.  Everything in that directory
        except `design_description.txt` is the answer, and the whole claim of this method is
        about what can be built from the description alone.
        """
        dest = os.path.join(ws, "specs", design.key + ".spec.txt")
        os.makedirs(os.path.dirname(dest), exist_ok=True)
        shutil.copyfile(design.spec_path, dest)

    # ---- shared by every oracle -----------------------------------------------------------

    def _harness(self, design: Design) -> list[str]:
        """The data files the testbench reads, alongside the testbench itself.

        Everything in the design's directory that is not Verilog, not the prose and not the
        makefile.  Seven files qualify across the fifty — `tri_gen.txt`, `test_data.dat`,
        `reference.dat`, `reference.txt`, `wfull.txt`, `rempty.txt`, `tdata.txt` — and every one
        is read by a `$readmemh`/`$fopen` on a bare relative name, so they only resolve if they
        sit in the simulator's cwd.  The `not Verilog` half of the rule is what keeps
        `verified_<key>.v` out, and it is a rule rather than a name list so that a reference
        added under a different name later is still excluded.
        """
        d = design.meta["dir"]
        keep = []
        for f in sorted(os.listdir(d)):
            p = os.path.join(d, f)
            if not os.path.isfile(p):
                continue
            if f.endswith((".v", ".sv")) or f == "design_description.txt" or f == "makefile":
                continue
            keep.append(p)
        return keep

    def _rundir(self, design: Design, vpath: str, td: str,
                verdict: Verdict | None = None) -> str:
        """Lay the candidate, the testbench and the harness data out in one scratch directory.

        The candidate is COPIED rather than compiled where it lies, and the testbench is copied
        in beside it rather than read from the dataset in place: compiling in the dataset
        directory would leave build droppings beside somebody else's data and would let a
        wildcard pick up `verified_<key>.v`.  Copying the testbench in — rather than pointing the
        compiler at it — is what lets its `$readmemh` find the data file, since the simulator's
        cwd is this directory.
        """
        shutil.copyfile(vpath, os.path.join(td, design.key + ".v"))
        assets = [("checker/testbench.v", design.meta["testbench"], "testbench.v")]
        assets += [("harness/" + os.path.basename(path), path, os.path.basename(path))
                   for path in self._harness(design)]
        dataset_inputs, score_inputs = [], []
        for logical, source, name in assets:
            # One read feeds both the content hash and the scratch file consumed by the simulator.
            # A dataset edit between two arms therefore changes row evidence even if restored later.
            data = open(source, "rb").read()
            open(os.path.join(td, name), "wb").write(data)
            digest = hashlib.sha256(data).hexdigest()
            dataset_inputs.append({"name": logical, "sha256": digest})
            score_inputs.append({"name": name, "sha256": digest})
        if verdict is not None:
            verdict.extra["dataset_inputs"] = dataset_inputs
            verdict.extra["score_inputs"] = score_inputs
        return td

    def _read(self, v: Verdict, out: str) -> Verdict:
        """Turn what the testbench printed into a status.  Identical for every simulator.

        The tally is read first and a nonzero one is decisive, because a testbench that counted
        failures counted them whatever else it went on to print.  A design that both fails the
        count and reaches the `Passed` line is a contradictory testbench, and the failure is the
        safe reading; `disagreed` records it rather than hiding it.
        """
        tally = TALLY_RE.search(out)
        failures = int(tally.group(1)) if tally else None
        if failures:
            v.status = "func_fail"
        elif PASS_RE.search(out):
            v.status, v.func_pass = "func_pass", True
        elif FAIL_RE.search(out):
            v.status = "func_fail"
        elif failures == 0:
            # The tally is the whole verdict on the five designs that print no `Passed` line.
            v.status, v.func_pass = "func_pass", True
        else:
            # No line of any of the three dialects.  NOT a failure: the testbench did not reach
            # its own verdict, which is a statement about the run and not about the design.
            v.status = "no_verdict"
        v.detail = out[-700:]
        v.extra.update({"tail": out.strip().splitlines()[-3:], "failures": failures,
                        "said_passed": bool(PASS_RE.search(out)),
                        "disagreed": bool(failures and PASS_RE.search(out))})
        return v

    def _refusal(self, design: Design, vpath: str) -> Verdict | None:
        """The two things that stop a scoring run before any simulator is involved."""
        v = Verdict(key=design.key, oracle=self.oracle)
        if not os.path.isfile(vpath):
            v.status = "not_emitted"
            v.detail = f"no {vpath}"
            return v
        if not os.path.isfile(design.meta["testbench"]):
            v.status = "harness_error"
            v.detail = f"this design ships no testbench at {design.meta['testbench']}"
            return v
        return None

    def score(self, design: Design, vpath: str) -> Verdict:
        refused = self._refusal(design, vpath)
        if refused:
            return refused
        v = Verdict(key=design.key, oracle=self.oracle)

        with tempfile.TemporaryDirectory(prefix=f"rtllm-{design.key}-") as td:
            self._rundir(design, vpath, td, v)
            sim = os.path.join(td, "a.out")
            c = subprocess.run(["iverilog", "-g2012", "-o", sim,
                                design.key + ".v", "testbench.v"],
                               cwd=td, capture_output=True, text=True, timeout=300)
            if c.returncode != 0:
                v.status = "compile_fail"
                v.detail = (c.stderr or c.stdout)[-700:]
                return v
            v.syntax_pass = True
            try:
                r = subprocess.run(["vvp", sim], cwd=td,
                                   capture_output=True, text=True, timeout=300)
            except subprocess.TimeoutExpired:
                v.status = "timeout"
                v.detail = "the simulation did not terminate in 300s"
                return v
            out = r.stdout + r.stderr

        return self._read(v, out)

    def dataset_id(self) -> dict:
        """Hash every byte that can affect reading, answering, replay or benchmark scoring.

        Logical names are part of the digest because `$readmemh("reference.dat")` depends on the
        filename.  Absolute mount paths and the selected simulator are not: identical dataset bytes
        moved elsewhere remain the same dataset, and simulator identity is frozen separately.
        """
        overall = hashlib.sha256()
        per = {}
        designs = self.designs()
        for design in designs:
            directory = design.meta["dir"]
            references = [os.path.join(directory, name) for name in sorted(os.listdir(directory))
                          if name.startswith("verified_") and name.endswith((".v", ".sv"))]
            sources = [("prompt/design_description.txt", design.spec_path),
                       ("checker/testbench.v", design.meta["testbench"])]
            sources += [("reference/" + os.path.basename(path), path) for path in references]
            sources += [("harness/" + os.path.basename(path), path)
                        for path in self._harness(design)]
            digest = hashlib.sha256()
            files = []
            for logical, path in sources:
                data = open(path, "rb").read() if os.path.isfile(path) else None
                file_sha = hashlib.sha256(data).hexdigest() if data is not None else None
                digest.update(logical.encode())
                digest.update(b"\0")
                digest.update(data if data is not None else b"<missing>")
                digest.update(b"\0")
                files.append({"name": logical, "sha256": file_sha})
            per[design.key] = {
                "sha256": digest.hexdigest(), "files": files,
                "scorer_files": [logical for logical, _path in sources
                                 if logical.startswith(("checker/", "harness/"))],
            }
            overall.update(design.key.encode())
            overall.update(b"\0")
            overall.update(digest.digest())
        return {"bench": self.name, "designs": len(designs),
                "files_hashed": sum(len(item["files"]) for item in per.values()),
                "sha256": overall.hexdigest(), "per_design": per}

    ORACLE_NOTE = ("graded under Icarus; published RTLLM numbers are from VCS and are not "
                   "comparable with these")


class RTLLM_VCS(RTLLM):
    """The same benchmark, the same reading of what the testbench printed, a different simulator.

    Only `score` differs, and inside `score` only the two lines that invoke a compiler.  Staging,
    the harness-file rule and `_read` are inherited verbatim on purpose: if VCS and Icarus
    disagreed about a design because they were being asked different questions, the comparison
    between them would be worthless.  They are asked the same question.

    ## Why remote

    There is no VCS on this machine.  There is one on `VCS_REMOTE` (default below), where it is
    `T-2022.06_Full64` under a floating license.  Each design is rsynced over as a directory of
    three or four small files, built and run there, and the combined output is read back.  Nothing
    persists between designs except the directory, which is overwritten.

    ## `oracle_unavailable` is not a failure

    Reaching a simulator is a property of the network, not of the design under test.  Every way
    this can go wrong that is NOT the candidate's fault — ssh refused, rsync failed, `vcs` not on
    the remote PATH, the license server said no — returns `oracle_unavailable`, which `Verdict`
    holds apart from every failure status.  A run once counted three remote timeouts as
    non-passes and two of the three were on the arm the run was about.

    The license check is by pattern rather than by exit code because VCS exits nonzero for a
    refused license and for a syntax error alike, and calling the first one `compile_fail` would
    charge the design for the license server's mood.
    """

    oracle = "vcs"
    ORACLE_NOTE = ("graded under Synopsys VCS, the simulator RTLLM's own makefiles invoke; "
                   "comparable with published RTLLM numbers")

    # `-full64` because VCS_HOME on the remote points at the 32-bit tree and the compiler is only
    # in `linux64`; `-sverilog` because five of these testbenches are SystemVerilog in all but the
    # extension; the timescale because eleven testbenches declare none and VCS, unlike Icarus,
    # refuses to elaborate a design where some modules have one and others do not.
    VCS_FLAGS = ["-full64", "-sverilog", "-timescale=1ns/1ps", "-q", "-notice", "+lint=none"]
    RDIR = "leansilicon-vcs"
    COMPILE_TIMEOUT = 900
    RUN_TIMEOUT = 300

    # `LogLevel=ERROR` because ssh writes `Warning: Permanently added … to the list of known
    # hosts` to stderr on first contact, and that line lands in the middle of the compile log this
    # adapter then pattern-matches for license failures.
    SSH_OPTS = ["-o", "BatchMode=yes", "-o", "ConnectTimeout=15", "-o", "LogLevel=ERROR"]

    # Not the candidate's fault.  Matched against the compile output before its exit code is
    # believed — but only once `VCS_DIAG_RE` has ruled out that the compiler ran at all.
    UNAVAILABLE_RE = re.compile(
        r"Cannot find VCS compiler|VCS_HOME is|License|Licensing|FLEXlm|FLEXnet|"
        r"cannot check ?out|vcs: command not found|Permission denied|Connection (refused|closed)",
        re.I)

    # VCS prefixes every diagnostic of its own with `Error-[CODE]` or `Warning-[CODE]`.  Seeing
    # one means the compiler started, read the sources and reached an opinion about them — so the
    # failure belongs to the design, whatever else the log also says.  This is the discriminator
    # because the naive one is wrong in the flattering direction: a first cut called a run
    # unavailable when its output lacked the string `simv`, and VCS does not print `simv` when it
    # fails, so three designs with genuine port-mismatch errors (`LFSR`, `radix2_div`,
    # `sequence_detector`) were recorded as unmeasured instead of as failures.
    VCS_DIAG_RE = re.compile(r"(?:Error|Warning)-\[")

    def host(self) -> str:
        return os.environ.get("VCS_REMOTE", "usr@usr")

    def _ssh(self, script: str, timeout: int) -> subprocess.CompletedProcess:
        """Run bash on the remote over stdin.

        Over stdin and not as an argument because the remote login shell at this site is tcsh:
        `ssh host 'source env.sh'` is parsed by tcsh and dies on `Illegal variable name` before
        bash is ever reached.  `/bin/bash -s` makes the interpreter explicit.
        """
        return subprocess.run(["ssh", *self.SSH_OPTS, self.host(), "/bin/bash", "-s"],
                              input=f"source ~/{self.RDIR}/env.sh 2>/dev/null\n{script}\n",
                              capture_output=True, text=True, timeout=timeout)

    def score(self, design: Design, vpath: str) -> Verdict:
        refused = self._refusal(design, vpath)
        if refused:
            return refused
        v = Verdict(key=design.key, oracle=self.oracle)
        token = "%s-%s" % (design.key, uuid.uuid4().hex)
        remote_rel = "%s/score/%s" % (self.RDIR, token)
        rd = "~/" + remote_rel
        v.extra["remote_workspace_sha256"] = hashlib.sha256(remote_rel.encode()).hexdigest()
        try:
            return self._score_remote(design, vpath, v, remote_rel, rd)
        finally:
            # Each arm and process has its own remote build tree.  Cleanup is best-effort and must
            # never overwrite the score that was already measured if the connection has gone away.
            try:
                self._ssh("rm -rf -- %s" % rd, 60)
            except (OSError, subprocess.TimeoutExpired):
                pass

    def _score_remote(self, design: Design, vpath: str, v: Verdict,
                      remote_rel: str, rd: str) -> Verdict:
        key = design.key
        try:
            with tempfile.TemporaryDirectory(prefix=f"rtllm-{key}-") as td:
                self._rundir(design, vpath, td, v)
                push = subprocess.run(
                    ["rsync", "-az", "--delete", "-e", "ssh " + " ".join(self.SSH_OPTS),
                     td + "/", f"{self.host()}:{remote_rel}/"],
                    capture_output=True, text=True, timeout=180)
            if push.returncode != 0:
                v.status = "oracle_unavailable"
                v.detail = f"rsync to {self.host()} failed: {(push.stderr or '')[-400:]}"
                return v

            flags = " ".join(self.VCS_FLAGS)
            c = self._ssh(f"cd {rd} && vcs {flags} -o simv {key}.v testbench.v 2>&1",
                          self.COMPILE_TIMEOUT)
        except subprocess.TimeoutExpired:
            v.status = "oracle_unavailable"
            v.detail = f"the remote build did not answer in {self.COMPILE_TIMEOUT}s"
            return v
        except OSError as e:                       # no ssh/rsync binary at all
            v.status = "oracle_unavailable"
            v.detail = f"cannot reach {self.host()}: {e}"
            return v

        cout = c.stdout + c.stderr
        if c.returncode != 0:
            # The order matters: an unreachable simulator must not be recorded as a broken design,
            # and a broken design must not be recorded as an unreachable simulator.  A VCS
            # diagnostic settles it in favour of the design; only its absence lets the transport
            # be blamed.
            if not self.VCS_DIAG_RE.search(cout) and (self.UNAVAILABLE_RE.search(cout)
                                                      or not cout.strip()):
                v.status = "oracle_unavailable"
                v.detail = f"VCS on {self.host()} did not run: {cout[-700:]}"
            else:
                v.status = "compile_fail"
                v.detail = cout[-700:]
            return v
        v.syntax_pass = True

        try:
            r = self._ssh(f"cd {rd} && ./simv -q 2>&1", self.RUN_TIMEOUT + 60)
        except subprocess.TimeoutExpired:
            v.status = "timeout"
            v.detail = f"the simulation did not terminate in {self.RUN_TIMEOUT}s"
            return v
        out = r.stdout + r.stderr
        v = self._read(v, out)
        v.extra["compile_tail"] = cout.strip().splitlines()[-2:]
        return v


ORACLES = {"icarus": RTLLM, "vcs": RTLLM_VCS}


def adapter() -> Adapter:
    """`RTLLM_ORACLE` picks the simulator; Icarus is the default.

    An unknown value is an error rather than a fallback.  Silently grading under Icarus because
    somebody typed `RTLLM_ORACLE=VCS-2022` would produce a table of numbers labelled `vcs` by the
    person who ran it and `icarus` by every verdict file in it, and the label a reader trusts is
    the one in the paper.
    """
    name = os.environ.get("RTLLM_ORACLE", "icarus").strip().lower()
    if name not in ORACLES:
        raise SystemExit(f"rtllm: RTLLM_ORACLE={name!r} is not one of "
                         f"{', '.join(sorted(ORACLES))}")
    return ORACLES[name]()


if __name__ == "__main__":
    a = adapter()
    ds = a.designs()
    print(f"rtllm: {len(ds)} designs, oracle {a.oracle}")
    print("  " + a.dataset_id()["sha256"])
    for d in ds:
        print(f"  {d.key:26} {d.toplevel:26} {d.camel:26} {d.meta['category']}")
