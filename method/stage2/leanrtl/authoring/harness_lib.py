#!/usr/bin/env python3
"""Shared benchmark-harness library (P0.4 + P1.6).

ONE home for the things the six benchmark runners used to copy-paste and let drift:

  * Benchmark data roots — env-var overridable, defaulting to <repo>/bench_data/ (gitignored,
    fetched by scripts/fetch_benchmarks.sh):
        RTLLM_ROOT  (default bench_data/RTLLM)
        VEVAL_ROOT  (default bench_data/VerilogEval/dataset_spec-to-rtl)
        CVDP_JSONL  (default bench_data/CVDP_data/cvdp_v1.1.0_nonagentic_code_generation
                     _no_commercial.jsonl)
    Resolution is repo-relative (derived from __file__), never a hardcoded /home or /tmp path.

  * ONE canonical pass/fail parser per benchmark (parse_rtllm / parse_veval / parse_cocotb) —
    previously benchmarks/rtllm/run.py, benchmarks/rtllm/sweep.py and benchmarks/baseline/run_rtllm.py each had a
    slightly different RTLLM heuristic, which could pollute differential comparisons.

  * run_vvp(sim, cwd) — vvp always with an explicit cwd so testbench-relative $readmemh
    (RTLLM alu/calendar-style oracle loads) resolves against the design's own directory.

  * extract_verilog(key, top, wd, f9=...) — leanrtl extract -> RTLIL JSON -> (optional
    miter-anchored F9 procedural emission) -> yosys write_verilog.

  * run_cocotb(record, verilog_path, top) — the CVDP cocotb harness staging + pytest run that
    was copied in benchmarks/cvdp/run.py, benchmarks/baseline/run_cvdp.py and benchmarks/cvdp/param_check.py, now with a bounded
    retry (default 2 attempts, pass on first success) and an `attempts` field in the result.

Consumers: benchmarks/rtllm/run.py, benchmarks/rtllm/sweep.py, benchmarks/rtllm/ss_measure.py, benchmarks/verilogeval/run.py,
benchmarks/cvdp/run.py, benchmarks/cvdp/param_check.py, benchmarks/baseline/run_{rtllm,veval,cvdp}.py, scripts/measure_all.py.
"""
import os
import re
import sys
import json
import tempfile
import subprocess

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEANHDL = os.path.join(REPO, ".lake", "build", "bin", "leanrtl")
BENCH_DATA = os.path.join(REPO, "bench_data")


# ---------------------------------------------------------------------------
# benchmark data roots (env-var overridable, repo-relative defaults)
# ---------------------------------------------------------------------------
def rtllm_root():
    return os.environ.get("RTLLM_ROOT", os.path.join(BENCH_DATA, "RTLLM"))


def veval_root():
    return os.environ.get("VEVAL_ROOT",
                          os.path.join(BENCH_DATA, "VerilogEval", "dataset_spec-to-rtl"))


def cvdp_jsonl():
    return os.environ.get("CVDP_JSONL",
                          os.path.join(BENCH_DATA, "CVDP_data",
                                       "cvdp_v1.1.0_nonagentic_code_generation_no_commercial.jsonl"))


_cvdp_records = None


def cvdp_record(pid, jsonl=None):
    """Look up one CVDP problem record by id (whole file cached on first call)."""
    global _cvdp_records
    if _cvdp_records is None:
        path = jsonl or cvdp_jsonl()
        if not os.path.isfile(path):
            raise FileNotFoundError(
                f"CVDP jsonl not found: {path}\n"
                "Set CVDP_JSONL or fetch it (see scripts/fetch_benchmarks.sh).")
        _cvdp_records = {json.loads(l)["id"]: json.loads(l) for l in open(path)}
    return _cvdp_records.get(pid)


# ---------------------------------------------------------------------------
# subprocess helpers
# ---------------------------------------------------------------------------
def sh(cmd, timeout=90, cwd=None, env=None):
    return subprocess.run(cmd, capture_output=True, text=True,
                          timeout=timeout, cwd=cwd, env=env)


def run_vvp(sim, cwd, timeout=60):
    """Run a compiled iverilog sim.  `cwd` is REQUIRED (pass the design dir): RTLLM
    testbenches $readmemh relative oracle files, which resolve against the cwd.
    Raises subprocess.TimeoutExpired on hang."""
    return sh(["vvp", sim], timeout=timeout, cwd=cwd)


# ---------------------------------------------------------------------------
# canonical pass/fail parsers (ONE heuristic per benchmark)
# ---------------------------------------------------------------------------
def parse_rtllm(out):
    """Canonical RTLLM testbench verdict.  Priority order:
      1. explicit failure/error count  ("Test completed with N [/M] failures|errors") -> N == 0
      2. explicit pass banner          ("Your Design Passed")
      3. explicit fail/error marker    -> fail
      4. bare "pass"/"passed" with no fail/error marker -> pass
      5. default fail (silent testbench = no evidence of passing)."""
    low = out.lower()
    m = re.search(r"with\s+(\d+)\s*/?\s*\d*\s*(?:failures?|errors?)", low)
    if m:
        return int(m.group(1)) == 0
    if "your design passed" in low:
        return True
    if re.search(r"\bfail(?:ed|ure|ures)?\b", low) or re.search(r"\berrors?\b", low):
        return False
    return bool(re.search(r"\bpass(?:ed)?\b", low))


def parse_veval(out):
    """Canonical VerilogEval v2 verdict (its testbenches print mismatch counts)."""
    low = out.lower()
    m = re.search(r"mismatches:\s*(\d+)", low)
    if m:
        return int(m.group(1)) == 0
    m = re.search(r"total mismatched samples is\s*(\d+)", low)
    if m:
        return int(m.group(1)) == 0
    if "all tests passed" in low:
        return True
    return ("passed" in low) and ("fail" not in low)


def parse_cocotb(out):
    """Canonical cocotb/pytest verdict -> {tests, passed, failed, func_pass} or None.
    Prefers cocotb's own summary line (TESTS=n PASS=n FAIL=n); falls back to the pytest
    "N passed / N failed" summary (what benchmarks/cvdp/param_check.py used to parse)."""
    m = re.search(r"TESTS=(\d+)\s+PASS=(\d+)\s+FAIL=(\d+)", out)
    if m:
        t, p, f = (int(g) for g in m.groups())
        return {"tests": t, "passed": p, "failed": f,
                "func_pass": f == 0 and p == t and t > 0}
    mp = re.search(r"(\d+) passed", out)
    mf = re.search(r"(\d+) failed", out)
    if mp or mf:
        p = int(mp.group(1)) if mp else 0
        f = int(mf.group(1)) if mf else 0
        return {"tests": p + f, "passed": p, "failed": f,
                "func_pass": f == 0 and p > 0}
    return None


# ---------------------------------------------------------------------------
# LeanRTL -> Verilog extraction (verified RTLIL path, optional F9 emission)
# ---------------------------------------------------------------------------
def extract_verilog(key, top, wd, f9=False, timeout=90):
    """leanrtl extract <key> -> RTLIL JSON -> yosys write_verilog as module <top>.
    With f9=True, first try the F9 procedural next-state emission, used ONLY when a Yosys
    miter proves it equivalent to the verified RTLIL (falls back to write_verilog).
    Returns (verilog_path, err, emit_kind) with emit_kind in {"f9", "write_verilog", None}."""
    rj = os.path.join(wd, top + ".json")
    vv = os.path.join(wd, top + ".v")
    r = sh([LEANHDL, "extract", key, "-o", rj], timeout=timeout)
    if r.returncode != 0:
        return None, "extract: " + (r.stderr + r.stdout)[-300:], None
    if f9:
        sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
        from f9_emit import f9_or_none
        p, _ = f9_or_none(LEANHDL, key, top, rj, wd)
        if p is not None:
            return p, None, "f9"
    r = sh(["yosys", "-q", "-p",
            f"read_json {rj}; hierarchy -top {top}; proc; opt; write_verilog {vv}"],
           timeout=timeout)
    if r.returncode != 0:
        return None, "yosys: " + r.stderr[-300:], None
    return vv, None, "write_verilog"


# ---------------------------------------------------------------------------
# CVDP cocotb harness (staging + bounded-retry run)
# ---------------------------------------------------------------------------
def stage_cvdp_harness(record, verilog_text, wd):
    """Write the record's harness files + the DUT Verilog into `wd`.
    Returns (dut_path, cocotb_module_name)."""
    files = record["harness"]["files"]
    for path, content in files.items():
        fp = os.path.join(wd, path)
        os.makedirs(os.path.dirname(fp), exist_ok=True)
        open(fp, "w").write(content)
    ctx = record.get("output", {}).get("context", {})
    if ctx:                                   # place the DUT where the record says the RTL lives
        rel = list(ctx.keys())[0]
    else:                                     # fall back to the harness env's VERILOG_SOURCES
        src = re.search(r"VERILOG_SOURCES\s*=\s*(\S+)", files["src/.env"]).group(1)
        rel = src.lstrip("/")
        if rel.startswith("code/"):
            rel = rel[len("code/"):]
    dut = os.path.join(wd, rel)
    os.makedirs(os.path.dirname(dut), exist_ok=True)
    open(dut, "w").write(verilog_text)
    module = re.search(r"MODULE\s*=\s*(\S+)", files["src/.env"]).group(1)
    return dut, module


def run_cocotb(record, verilog_path, top, timeout=260, retries=2):
    """Run the record's cocotb harness against the Verilog at `verilog_path` with TOPLEVEL=top.
    Bounded retry: up to `retries` attempts, returning on the first success (icarus/cocotb runs
    can be flaky: VPI races, transient timeouts).  Result always carries `attempts`.
    Returns {status, func_pass, attempts, [tests, pass, fail], [detail]}."""
    res = {"attempts": 0, "func_pass": False, "status": "not_run"}
    text = open(verilog_path).read()
    for attempt in range(1, max(1, retries) + 1):
        res["attempts"] = attempt
        with tempfile.TemporaryDirectory() as wd:
            dut, module = stage_cvdp_harness(record, text, wd)
            runner = os.path.join(wd, "src", "test_runner.py")
            if not os.path.isfile(runner):
                res.update(status="no_runner", func_pass=False)
                return res                    # structural — retrying cannot help
            env = dict(os.environ, SIM="icarus", TOPLEVEL_LANG="verilog",
                       VERILOG_SOURCES=dut, TOPLEVEL=top, MODULE=module,
                       PYTHONPATH=os.path.join(wd, "src"))
            try:
                v = subprocess.run(["python3", "-m", "pytest", "-s", "-q", runner],
                                   capture_output=True, text=True,
                                   timeout=timeout, env=env, cwd=wd)
            except subprocess.TimeoutExpired:
                res.update(status="timeout", func_pass=False)
                continue
            out = v.stdout + v.stderr
            p = parse_cocotb(out)
            if p is None:
                res.update(status="sim_err", func_pass=False, detail=out[-250:])
                continue
            res.update(tests=p["tests"], func_pass=p["func_pass"],
                       status="func_pass" if p["func_pass"] else "func_fail")
            res["pass"], res["fail"] = p["passed"], p["failed"]
            if p["func_pass"]:
                return res
    return res


def run_pytest_cocotb(runner_py, env, cwd, timeout=300, retries=2):
    """Generic pytest-driven cocotb invocation with bounded retry (flake mitigation).
    Returns (combined_output, attempts). Caller parses with parse_cocotb()."""
    out, attempts = "", 0
    for attempts in range(1, retries + 1):
        v = subprocess.run(["python3", "-m", "pytest", "-s", "-q", runner_py],
                           capture_output=True, text=True, env=env, cwd=cwd, timeout=timeout)
        out = v.stdout + v.stderr
        verdict = parse_cocotb(out)
        if verdict and verdict["func_pass"]:
            break
    return out, attempts
