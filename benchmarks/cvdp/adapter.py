#!/usr/bin/env python3
"""CVDP `cid003`: 78 spec-to-RTL problems, judged by their own cocotb harness under Icarus.

Installed data, not method — this file lives under `benchmarks/`, which is gitignored, and the two
datasets it reads are symlinks to checkouts outside both.  Nothing here may look at how the Verilog
it grades was produced.

## The population is one category of one file, and the rest of CVDP is a different experiment

`cvdp_v1.0.2_nonagentic_code_generation_no_commercial.jsonl` holds 302 rows across five categories:

    cid002  94    cid003  78    cid004  55    cid007  40    cid016  35

Only `cid003` is spec-to-RTL — a prose specification and nothing else, with the module to be
written from scratch.  Every other category either hands the author the existing RTL it wants
modified (so the prose is not the whole task statement), ships no harness at all, or needs Xcelium,
which is not on this machine and is not free.  `CATEGORY` is therefore a constant and not a filter
argument: enlarging a population is a decision, not a discovery, and a lane that quietly grew from
78 to 302 would change every denominator on it without changing a line of any report.

`categories` is `["cid003", "easy"|"medium"]` — 41 easy, 37 medium.  The difficulty is carried in
`meta` and in every `Verdict.extra`, because those two are not one population either.

## The record, and the one shape that has already cost sixteen designs

    id               globally unique across all 772 rows of all five files — this is `Design.key`
    input.prompt     the prose spec; the ONLY thing an author may read
    input.context    {path: content}; EMPTY on 77 of the 78 — see below for the exception
    output.response  "" on all 78
    output.context   {path: ""} on all 78 — one key, and its value is the empty string
    harness.files    {relpath: content} — the entire oracle

Note the extra `files` nesting on `harness`.  A reader that treats `row["harness"]` as
`{path: content}` sees exactly one key, whose value is a dict rather than a string, and concludes
the harness is empty.  That mistake was made here and it reported sixteen designs with complete,
runnable harnesses as unscorable.  `_harness_files()` is the one place that unwraps it.

**There is no official reference solution anywhere in this dataset.**  `output.response` is empty on all 78
and every value in `output.context` is the empty string — the paths are there, the contents are
not.  Three consequences, and none of them is optional:

  * Without a separately constructed synthetic reference, `golden_source()` returns `None`.
  * A reference-construction run may freeze RTL that passed this exact harness.  Such a source is
    labelled synthetic and harness-derived everywhere; it is not presented as an upstream answer.
  * `known_defects()` ships empty, and `KNOWN_DEFECTS.json` is deliberately absent, because the
    control that would establish an `unwinnable` entry cannot be run.  See the section on blind
    harnesses below for what is shipped instead, and why it is shipped as data rather than as an
    exclusion.

### The one design with `input.context`

`cvdp_copilot_serial_in_parallel_out_0004` ships `docs/Documentation.md`, 2252 bytes, and it is
part of the task statement rather than a hint: it carries the port table and the shift direction.
Staging the prompt alone would pose a strictly smaller problem than the benchmark's on that design
and then report the result under the benchmark's name.

So it is staged, twice over, and the duplication is on purpose.  It is written verbatim to
`<ws>/specs/<key>.context/docs/Documentation.md`, so a prompt that names the relative path has
something to resolve; and it is APPENDED to `<key>.spec.txt` under a marked header, because
`leanrtl/stage.py:resolve_spec` reads exactly one file — `Design.spec_path` — and a document
sitting beside it is a document nobody opens.  This is the only transformation this adapter
performs on any prompt, it fires on 1 of 78 designs, and `meta["spec_includes_context"]` says so
per design so that a spec whose bytes differ from `input.prompt` can never be mistaken for one
that does not.

## The oracle: cocotb + pytest + Icarus, run locally, without the container

Every one of the 78 `.env`s says `SIM = icarus`.  Upstream's flow is a per-problem
`docker-compose.yml` that runs pytest inside `nvidia/cvdp-sim:v1.0.0`.  That image is not public,
so it is not what happened here.  What happened here is that this machine already carries Icarus,
cocotb and pytest, and a real harness was driven end to end with no container at all — a true PASS
on a hand-written correct DUT and a true FAIL on a deliberately wrong one, same design, same
harness.  So `score()` runs the harness locally and `oracle = "icarus"` is stamped on every
verdict.

Exactly which parts of the official image are reproduced, and which are not:

    reproduced          cocotb 2.0.1                   (image: cocotb 2.0.1)
    NOT reproduced      Icarus Verilog 12.0 (v12_0)    (image: v13_0)
    NOT reproduced      pytest 7.4.0                   (image: pytest 8.3.2)

A verdict that does not name its simulator reads as a fact about the design and gets carried across
a toolchain change that invalidates it, so the live versions are probed and stamped into
`dataset_id()["toolchain"]` and into `Verdict.extra["toolchain"]` on every row.  No number from
this adapter is comparable with a published CVDP number, which came from that image.

One further deviation, and it is a superset rather than a subset.  19 of the 78
`docker-compose.yml` files drive the harness with `python3 /src/test_runner.py` rather than with
pytest.  This adapter runs pytest on all 78.  That is safe here and was checked rather than
assumed: all 78 `test_runner.py` define at least one function whose name begins with `test`, so
pytest collects and runs the simulation on every one of them, including all 19.  What pytest does
NOT run is the body of a `__main__` guard (32 of the 78 have one), and on all 32 that body only
calls the same `test_runner()` pytest has already collected.  The service name in the compose file
is never read — they vary (`direct`, `01-new-tb`, `test`, `auto`, `pytest`, `07-new-tb`, `3-`,
`1-new-tb`) and hardcoding one would silently skip 45 designs.

What this adapter must NOT do is bypass `test_runner.py` and invoke cocotb itself, which would be
the tidier-looking route.  `test_runner.py` is where per-design run state is set up: on
`fsm_seq_detector_0001` it does `os.environ["TEST_SEQUENCE"] = json.dumps(...)` before calling the
runner, and the testbench reads that variable at module import with a bare
`json.loads(os.getenv("TEST_SEQUENCE"))`.  Skip the runner script and the testbench dies on
`NoneType.split` before a single cycle is simulated.

## Graded with v1.1.0's harness, posed with v1.0.2's prompt

v1.0.2's harnesses were written against cocotb 1.x and seven of them cannot run under the cocotb
2.0.1 installed here.  The count was measured, not read off a grep, because the obvious greps are
wrong in both directions:

    6 of 78   pytest cannot even collect `src/test_runner.py`: `from cocotb.runner import
              get_runner`, which 2.x moved to `cocotb_tools.runner` — apb_gpio_0001,
              decode_firstbit_0001, hill_cipher_0001, packet_controller_0001, perf_counters_0001,
              perfect_squares_0001.  Under v1.1.0's harnesses the same probe finds 0 of 78.
    1 of 78   collects but dies when the testbench module loads: clock_divider_0003's
              `harness_library.py:2` does `from cocotb.sim_time_utils import get_sim_time`.
              A collect-only probe misses this one, so both probes are needed.

Two greps that look like breakages are not.  `palindrome_3b_0002` contains the string
`from cocotb.runner import get_runner` on a **commented-out** line — its live import on the next
line is already `cocotb_tools.runner` — so a grep for `cocotb.runner` reports 7 collect failures
where there are 6.  And `units=` (77 designs) and `signal._type` (31) are *not* breakages at all:
cocotb 2.0.1 still accepts both, `Timer.__init__` retaining `units: None = None` alongside the new
`unit`.  Verified live — the priority encoder passes under `CVDP_HARNESS_SOURCE=self`.

Grading those seven with their own harness produces seven import errors, and an import error
scored as a design failure is the benchmark measuring its own age.

A v1.1.0 copy of the same benchmark sits outside this repository with all 78 harnesses ported to
cocotb 2.x.  The prompts across the two versions were compared byte for byte before anything was
built on them: **all 78 `input.prompt` strings and all 78 `input.context` dicts are identical**,
the two id sets are equal, and `SIM`, `TOPLEVEL`, `MODULE` and `VERILOG_SOURCES` agree on every
design.  All 78 harnesses differ, which is the point.

So the default is: **pose the v1.0.2 prompt, grade with the v1.1.0 harness, matched by `id`.**
It is switchable (`CVDP_HARNESS_SOURCE=self` grades with v1.0.2's own harness), it is recorded in
`dataset_id()` and in `Verdict.extra["harness_from"]`, and a missing or incomplete overlay is a
hard failure out of `designs()` rather than a silent fallback — falling back would grade seven
designs as design failures and report 78/78 attempted.

## Scoring runs in a private temp tree

cocotb's runner writes `sim_build/`, `sim.log`, `build.log`, `.cache/` and `*.fst` into its cwd, so
two designs scored at once in a shared directory collide on all of them.  Each `score()` builds:

    <tmp>/rtl/<basename of VERILOG_SOURCES>   the candidate.  NOT `<toplevel>.v`: on 8 designs the
                                              two differ, e.g. TOPLEVEL=priority_encoder_8x3 with
                                              VERILOG_SOURCES=/code/rtl/priority_encoder.v, and 63
                                              of 78 use a `.sv` extension.  Icarus is told the
                                              filename, so the filename is what must match.
    <tmp>/src/...                             every `harness.files` key starting `src/`
    <tmp>/rundir/                             the cwd of the run

`src/.env` is parsed as `KEY = value` with the whitespace padding it ships with (51 of 78 have no
trailing newline).  `VERILOG_SOURCES` is rewritten to the temp path and `PYTHONPATH` to
`<tmp>/src`; `SIM`, `TOPLEVEL`, `MODULE`, `TOPLEVEL_LANG`, `WAVE` and `HASH` are passed verbatim.
Then, from `<tmp>/rundir`, pytest is run over `<tmp>/src/test_runner.py` with a 300 s timeout —
150 s covered all 78 when this was measured, and expiry is `timeout`, never a failure.

The run is its own process group and a timeout kills the group.  `subprocess.run(timeout=...)`
kills only the direct child and then waits on the pipe, and `vvp` inherits that pipe: a hung
simulator would leave the scorer blocked forever on a call that had already timed out.

## The verdict rule

Primary is pytest's **last** `in <n>s` summary line — `10 passed in 3.62s`,
`9 failed, 1 passed in 3.81s`.  The last, not the first, because a collection error prints one
summary and the run prints another.

The cocotb `** TESTS=1 PASS=1 FAIL=0 SKIP=0 **` tables are a cross-check, and **all** of them are
read, not the first.  Eight designs fan out with `@pytest.mark.parametrize` and print one table per
case; `low_pass_filter_0001` prints 54.  A reader that stopped at the first table would adjudicate
a 54-case sweep on case 1.

    func_pass  requires  failed == 0 and errors == 0 and passed > 0 and sum(cocotb FAIL) == 0

`failed == 0` rather than "something passed" is load-bearing and has a name:
`static_branch_predict_0001`'s `test_runner.py` defines a second pytest function whose entire body
is a `print`.  It always passes.  A rule that accepted a run because some item passed would accept
that design unconditionally.

Where the two readers disagree the failure wins and the disagreement is recorded in
`Verdict.extra["reader_disagreement"]`, so a row can never be quoted without it being visible that
the two halves of the oracle did not agree about it.

pytest is run with `-s`.  Without it pytest's fd-level capture swallows the simulator's stdout on
every passing test — cocotb's tables are printed by `vvp`, a grandchild of pytest — and the
cross-check has nothing to read on exactly the runs it is supposed to confirm.

Statuses: `func_pass | func_fail | no_verdict | timeout | not_emitted | harness_error`.  There is
no `compile_fail`: under this oracle an elaboration failure arrives as a pytest error inside
`runner.build()` and is indistinguishable, at the status level, from any other error.  It is not
lost — `extra["build_failed"]` and `extra["compile_errors"]` carry the simulator's own words, so
"did not elaborate" can be separated from "elaborated and mismatched" without inventing a status
whose meaning differs from the same word on the other three lanes.

A run that prints no summary line at all is `no_verdict`, never `func_fail`.  Silence is a
statement about the run, not about the design.

## Harnesses that cannot fail, shipped as data

Some of these harnesses cannot report a failure.  Two distinct mechanisms, and both are here:

  * assertions wrapped in `try/except AssertionError` whose handler only appends to a list —
    `ethernet_packet_parser_0001` (`field_extract`);
  * a cocotb test with no `assert`, no `raise` and no `pytest.fail` anywhere in it, which compares
    against a Python reference model and then *prints* the answer — `complex_multiplier_0001`,
    `dbi_0001`, `factorial_0001`, `perceptron_0001`, `unpacker_one_hot_0001`,
    `vga_controller_0001`.

The second mechanism is the more common one and is not what the earlier hand probe described; that
probe called them "assertions wrapped in try/except", which is true of exactly one of the seven.

`BLIND_PROBED` below is the hand-measured list, kept verbatim with its provenance because it is
evidence and evidence is not edited to agree with a later theory.  `_blindness()` is the static
scan, recomputed from the bytes of whichever harness is actually being graded, so it cannot go
stale against a dataset switch the way a hardcoded list would.  Both are reported, per design, in
`meta` and in `Verdict.extra`.

Neither is ever an exclusion.  A design is not dropped, not marked `unwinnable`, not removed from
any denominator — the flag rides along on the verdict and the report decides.  `unwinnable` would
require the golden control, and the golden control cannot be run here.

Note also what the static scan does NOT catch: a harness that asserts, but asserts something too
weak to distinguish a wrong design.  The hand probe listed `comparator_0001`
(`signed_unsigned_comparator`) as blind; its v1.1.0 testbench contains 30 live assertions and the
scan therefore does not flag it.  One of those two observations is about a weak testbench rather
than a blind one, and only re-probing that design decides which — which is precisely why the hand
list is preserved rather than overwritten.

## Every single-run number on this lane is a sample

55 of the 78 harnesses call `random.*`, and 8 of them randomise the **elaborated circuit** through
an unseeded `runner.build(parameters=...)`: `16qam_mapper_0001`, `16qam_mapper_0006`,
`cascaded_adder_0001`, `configurable_digital_low_pass_filter_0001` / `_0004` / `_0014`,
`data_bus_controller_0001`, `matrix_multiplier_0001`.  On those, two runs of the same candidate
against the same harness are two different problems.  Only 5 harnesses call `random.seed` at all.

`meta["randomised"]` and `meta["param_randomised"]` carry this, `Verdict.extra` repeats it, and
`Verdict.extra["cocotb_seeds"]` records the seeds cocotb printed for the run that produced the row.
That does not make the number reproducible — the pytest-side draw that picks the parameters happens
before cocotb is seeded and is not printed anywhere — but it makes the row honest about being a
draw rather than a measurement.

## `toplevel` comes from the `.env`, never from the prose

On 14 of the 78 the module name does not appear in the prompt at all, and on
`sync_serial_communication_0001` the source filename says `..._top` while `TOPLEVEL` is
`..._tx_rx`.  The name is therefore read out of the harness and handed to the author through
`Design.toplevel`, which every stager already reads.  Inferring it from the prose would emit a
module the harness cannot find, which arrives as an elaboration error and reads as a hardware
mistake.  `TOPLEVEL` is not unique across the whole 302-row file (83 collisions); it is unique
within cid003, which is asserted in `designs()` rather than assumed.

## The prompts are materialised to disk, because the socket reads a path

`Design.spec_path` is a filename and `leanrtl/stage.py` opens it directly.  These prompts live
inside a JSONL, so `designs()` writes them to `<HERE>/specs/` — under `benchmarks/`, which is
gitignored.  The write is content-compared first, so a second call is a no-op and the leak gate,
which calls `designs()` on every installed benchmark, does not churn the tree.
"""
from __future__ import annotations

import concurrent.futures
import hashlib
import json
import os
import re
import signal
import subprocess
import tempfile

try:
    from _adapter import Adapter, Design, Verdict
except ModuleNotFoundError:                    # direct execution, e.g. the self-check at the foot
    # `common.adapter.load` binds itself as `_adapter` before running this file, so the import
    # above is the normal path and this one only fires when nobody called `load` — running this
    # file as a script with `method/` on PYTHONPATH.  It resolves to the SAME module object, not
    # a copy, so the classes are the ones every other adapter implements.
    from common.adapter import Adapter, Design, Verdict          # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))

#: The prompts.  Symlink to the v1.0.2 non-agentic, non-commercial code-generation JSONL.
DATASET = os.environ.get("CVDP_DATASET", os.path.join(HERE, "dataset"))

#: The oracle.  Symlink to the v1.1.0 copy of the same benchmark, whose harnesses are cocotb 2.x.
HARNESS = os.environ.get("CVDP_HARNESS", os.path.join(HERE, "harness"))

#: `overlay` grades with `HARNESS`; `self` grades with the harness shipped beside the prompt.
#: `self` is the honest v1.0.2 reading and loses 8 designs to cocotb 1.x/2.x drift; it exists so
#: that claim can be re-measured rather than believed.
HARNESS_SOURCE = os.environ.get("CVDP_HARNESS_SOURCE", "overlay")

#: Where `input.prompt` is materialised so that `Design.spec_path` is a real path.
SPEC_CACHE = os.environ.get("CVDP_SPEC_CACHE", os.path.join(HERE, "specs"))

#: Harness-derived references created by ``python -m specir.bootstrap``.  They live with run data,
#: not beside the benchmark source, and are accepted only through their bound manifest.
SYNTHETIC_GOLDEN_ROOT = os.environ.get(
    "CVDP_SYNTHETIC_GOLDEN_ROOT",
    os.path.abspath(os.path.join(HERE, "..", "..", "specir", "runs", "experiments",
                                 "cvdp-synthetic")))

#: The one spec-to-RTL category.  A constant, not an argument — see the module docstring.
CATEGORY = "cid003"

#: Seconds for one harness.  150 s covered all 78 when this was measured; the margin is for the
#: parametrised fan-outs, and expiry is `timeout` rather than a failure.
TIMEOUT = 300

#: Designs a hand probe found could not report a failure — a deliberately wrong DUT still passed.
#: PROVENANCE: 11 of the 78 were probed, by hand, on this machine, against the v1.1.0 harnesses.
#: This is a LOWER BOUND and nothing may present it as the complete list.  The names are the
#: `TOPLEVEL`s the probe recorded, mapped here to keys.  `_blindness()` recomputes a static
#: over-approximation from the graded bytes; the two disagree, and the docstring says how.
BLIND_PROBED = {
    "cvdp_copilot_complex_multiplier_0001":     "complex_multiplier",
    "cvdp_copilot_dbi_0001":                    "dbi_enc",
    "cvdp_copilot_factorial_0001":              "factorial",
    "cvdp_copilot_ethernet_packet_parser_0001": "field_extract",
    "cvdp_copilot_comparator_0001":             "signed_unsigned_comparator",
    "cvdp_copilot_unpacker_one_hot_0001":       "unpack_one_hot",
}

#: Designs whose `test_runner.py` randomises the ELABORATED CIRCUIT through an unseeded
#: `runner.build(parameters=...)`.  Two runs of one candidate are two different problems.
#: Hand-verified against the v1.1.0 harnesses; a regex over `parameters=` alone reports 9, the
#: ninth being `8x3_priority_encoder_0001`, where the line is commented out.
PARAM_RANDOMISED = (
    "cvdp_copilot_16qam_mapper_0001",
    "cvdp_copilot_16qam_mapper_0006",
    "cvdp_copilot_cascaded_adder_0001",
    "cvdp_copilot_configurable_digital_low_pass_filter_0001",
    "cvdp_copilot_configurable_digital_low_pass_filter_0004",
    "cvdp_copilot_configurable_digital_low_pass_filter_0014",
    "cvdp_copilot_data_bus_controller_0001",
    "cvdp_copilot_matrix_multiplier_0001",
)

# ------------------------------------------------------------------------------------- readers

# pytest's own last line: `10 passed in 3.62s`, `9 failed, 1 passed in 3.81s`, `1 error in 0.3s`,
# `no tests ran in 0.01s`, and the same with `=` decorations when not run under `-q`.  Matched
# loosely and then confirmed by `_COUNT` below, because `-s` interleaves the simulator's entire
# stdout into this stream and a stricter anchor on a stream that noisy is a guess either way.
_SUMMARY_LINE = re.compile(r"^(?P<body>[^\n]*?)\s+in\s+(?P<secs>\d+(?:\.\d+)?)s\s*=*\s*$", re.M)
_COUNT = re.compile(r"(\d+)\s+(passed|failed|errors?|skipped|xfailed|xpassed|deselected"
                    r"|warnings?|reruns?)\b", re.I)
_NO_TESTS = re.compile(r"no tests ran", re.I)

# cocotb's own tally, one per simulator invocation:
#   ** TESTS=1 PASS=1 FAIL=0 SKIP=0            10.00       0.00     2665.42 **
_COCOTB_TALLY = re.compile(r"TESTS=(\d+)\s+PASS=(\d+)\s+FAIL=(\d+)\s+SKIP=(\d+)")

# `0.00ns INFO cocotb  Seeding Python random module with 1788112063` — the only part of the draw
# the run prints.  It does NOT cover the pytest-side draw that picks build parameters.
_COCOTB_SEED = re.compile(r"Seeding Python random module with\s+(\d+)")

# Icarus speaks two dialects of failure and cocotb's runner re-raises the second.
_IVERILOG_ERR = re.compile(r"^.*?:\d+:\s*(?:syntax )?error.*$|^.*\berror:.*$", re.M | re.I)
_BUILD_FAILED = re.compile(r"returned non-zero exit status|iverilog.*non-zero|I give up", re.I)

# Anything that can raise out of a cocotb test.  Absence of all of them in every module the
# harness loads means the harness cannot report a failure, whatever the DUT does.
_FAILERS = re.compile(r"^\s*(?:assert\b|raise\b)|\bpytest\.fail\b|\bTestFailure\b"
                      r"|\bcocotb\.result\b", re.M)
_CATCHES_ASSERT = re.compile(r"except\s+AssertionError")

_ENV_LINE = re.compile(r"^\s*([A-Za-z_][A-Za-z_0-9]*)\s*=\s*(.*?)\s*$")

_TOOLCHAIN: dict | None = None


def _camel(key: str) -> str:
    return "".join(w[:1].upper() + w[1:] for w in re.split(r"[_\-.]", key) if w)


def toolchain() -> dict:
    """The three versions that decide what a verdict on this lane means, probed once.

    Probed rather than declared.  The official image pins Icarus v13_0 and pytest 8.3.2 and this
    machine has neither; a constant in this file would say what the container has and be wrong
    about what ran.
    """
    global _TOOLCHAIN
    if _TOOLCHAIN is None:
        iv = ""
        try:
            r = subprocess.run(["iverilog", "-V"], capture_output=True, text=True, timeout=30)
            iv = (r.stdout + r.stderr).strip().splitlines()[0] if (r.stdout or r.stderr) else ""
        except Exception:                                        # noqa: BLE001
            iv = "unavailable"
        def _ver(mod: str) -> str:
            try:
                return __import__(mod).__version__
            except Exception:                                    # noqa: BLE001
                return "unavailable"
        _TOOLCHAIN = {"iverilog": iv, "cocotb": _ver("cocotb"), "pytest": _ver("pytest"),
                      "official_image": "nvidia/cvdp-sim:v1.0.0 "
                                        "(iverilog v13_0, cocotb 2.0.1, pytest 8.3.2) — NOT USED"}
    return _TOOLCHAIN


def _harness_files(row: dict) -> dict[str, str]:
    """`{relpath: content}` out of a record's harness, through the `files` nesting.

    `row["harness"]` has exactly one key, `files`, whose value is the dict.  Treating the outer
    dict as the file map yields one entry whose value is not a string, which reads as an empty
    harness — sixteen designs with complete harnesses were reported unscorable that way.

    Entries whose content is empty or whitespace are dropped.  There are none in cid003 today;
    materialising one would create a file the harness could import and get nothing from.
    """
    files = row.get("harness", {}).get("files", {})
    if not isinstance(files, dict):
        return {}
    return {k: v for k, v in files.items() if isinstance(v, str) and v.strip()}


def _parse_env(text: str) -> dict[str, str]:
    """`src/.env` as a dict.  `KEY = value`, whitespace-padded; 51 of 78 have no trailing newline,
    which is why this splits lines rather than reading up to one."""
    out = {}
    for line in text.splitlines():
        if not line.strip() or line.lstrip().startswith("#"):
            continue
        m = _ENV_LINE.match(line)
        if m:
            out[m.group(1)] = m.group(2)
    return out


def _blindness(files: dict[str, str], module: str) -> dict:
    """Can this harness report a failure at all?  Computed from the bytes being graded.

    The modules cocotb loads are every `.py` under `src/` except `test_runner.py`, which is the
    pytest driver and not a testbench.  `harness_library.py` is included: some designs put their
    only assertion in it.
    """
    mods = {k: v for k, v in files.items()
            if k.startswith("src/") and k.endswith(".py") and k != "src/test_runner.py"}
    failers = sum(len(_FAILERS.findall(v)) for v in mods.values())
    return {"assert_free": failers == 0,
            "catches_assertionerror": any(_CATCHES_ASSERT.search(v) for v in mods.values()),
            "failing_constructs": failers,
            "cocotb_modules": sorted(mods),
            "module": module}


def _build_logs(rundir: str, cap: int = 40000) -> str:
    """The simulator's own log files, with the scratch path stripped out.

    cocotb's runner is given `log_file="sim.log"` or `"build.log"` by these harnesses, and Icarus
    writes its diagnostics there rather than to the caller's pipe.  So a candidate that will not
    elaborate leaves `priority_encoder.v:8: syntax error` / `I give up.` in the run directory while
    the pytest stream carries only `subprocess.CalledProcessError`.  Without this, the detail on
    every non-elaborating candidate names a Python exception — which reads as the harness having
    broken rather than the design.

    The name is globbed, not assumed: `log_file=` differs across the 78 and a hardcoded `sim.log`
    would find nothing on the ones that say `build.log`.  Read at most `cap` bytes per file, since
    a chatty simulation can produce a very large log and none of this decides a verdict.
    """
    parts = []
    for root, dirs, names in os.walk(rundir):
        # `sim_build/` holds the compiled object and `cmds.f`; the logs are beside it or in it.
        # Depth is bounded by not descending into anything else the harness may have created.
        dirs[:] = [d for d in dirs if d in ("sim_build", "harness", "logs")]
        for n in sorted(names):
            if not n.endswith(".log"):
                continue
            p = os.path.join(root, n)
            try:
                with open(p, errors="replace") as f:
                    parts.append(f"----- {n} -----\n" + f.read(cap))
            except OSError:
                continue
    text = "\n".join(parts)
    # The temp path is an artefact of this scorer, not of the design.  Stripping it keeps a
    # diagnostic comparable between two runs of the same candidate.
    return text.replace(rundir, "<rundir>").replace(os.path.dirname(rundir), "<tmp>")


def _run(cmd: list[str], cwd: str, env: dict, timeout: int) -> tuple[int | None, str, bool]:
    """`(returncode, combined output, timed_out)`, with the whole process group killed on expiry.

    Not `subprocess.run(timeout=...)`.  That kills the direct child and then blocks in
    `communicate()` until the pipe closes — and `vvp` is a grandchild holding that same pipe, so a
    hung simulator would block the scorer forever inside a call that had already timed out.  A new
    session plus `killpg` takes the simulator down with the runner.
    """
    p = subprocess.Popen(cmd, cwd=cwd, env=env, stdout=subprocess.PIPE,
                         stderr=subprocess.STDOUT, text=True, errors="replace",
                         start_new_session=True)
    try:
        out, _ = p.communicate(timeout=timeout)
        return p.returncode, out or "", False
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError, OSError):
            p.kill()
        try:
            out, _ = p.communicate(timeout=30)
        except subprocess.TimeoutExpired:                        # nothing left to do but say so
            out = ""
        return None, out or "", True


class CVDP(Adapter):
    name = "cvdp"
    oracle = "icarus"

    def __init__(self) -> None:
        self._prompts: dict[str, dict] | None = None
        self._harness: dict[str, dict] | None = None
        self._designs: list[Design] | None = None
        self._synthetic_cache: dict[str, dict | None] = {}

    def _synthetic_golden(self, key: str) -> dict | None:
        """Load and authenticate a harness-passing answer key exactly once per adapter."""
        if key in self._synthetic_cache:
            return self._synthetic_cache[key]
        root = os.path.join(SYNTHETIC_GOLDEN_ROOT, key, "out")
        source = os.path.join(root, "golden.sv")
        manifest = os.path.join(root, "manifest.json")
        try:
            source_bytes = open(source, "rb").read()
            manifest_bytes = open(manifest, "rb").read()
            meta = json.loads(manifest_bytes)
            digest = hashlib.sha256(source_bytes).hexdigest()
        except (OSError, ValueError, TypeError):
            self._synthetic_cache[key] = None
            return None
        attempts = meta.get("attempts") if isinstance(meta.get("attempts"), list) else []
        accepted_attempt = meta.get("accepted_attempt")
        accepted = [item for item in attempts if isinstance(item, dict) and
                    item.get("attempt") == accepted_attempt]
        confirmations = meta.get("confirmation_scores")
        _prompts, harness = self._load()
        files = _harness_files(harness.get(key, {}))
        expected_inputs = [
            {"name": "harness/" + relative,
             "sha256": hashlib.sha256(content.encode()).hexdigest()}
            for relative, content in sorted(files.items()) if relative.startswith("src/")
        ]
        current_toolchain = toolchain()
        if (meta.get("schema_version") != 1 or meta.get("bench") != "cvdp" or
                meta.get("key") != key or meta.get("status") != "func_pass" or
                meta.get("source_sha256") != digest or
                not isinstance(accepted_attempt, int) or len(accepted) != 1 or
                accepted[0].get("candidate_sha256") != digest or
                not isinstance(meta.get("bootstrap_run_id"), str) or
                not meta.get("bootstrap_run_id")):
            self._synthetic_cache[key] = None
            return None
        if (not isinstance(confirmations, list) or not confirmations or
                confirmations != accepted[0].get("confirmation_scores") or
                any(not isinstance(item, dict) or item.get("status") != "func_pass" or
                    item.get("source_sha256") != digest or
                    item.get("dataset_inputs") != expected_inputs or
                    item.get("score_inputs") != expected_inputs or
                    item.get("toolchain") != current_toolchain
                    for item in confirmations)):
            self._synthetic_cache[key] = None
            return None
        value = {"path": source, "source": source_bytes.decode(errors="replace"),
                 "source_bytes": source_bytes, "manifest_bytes": manifest_bytes,
                 "manifest": meta}
        self._synthetic_cache[key] = value
        return value

    def synthetic_golden_path(self, key: str) -> str | None:
        value = self._synthetic_golden(key)
        return value["path"] if value else None

    @staticmethod
    def _synthetic_answer_metadata(design: Design, synthetic: dict) -> str:
        """Tell Answer which declaration the harness instantiates in a multi-module source."""
        return json.dumps({
            "schema_version": 1,
            "answer_key_kind": "synthetic_harness_pass",
            "benchmark": "cvdp",
            "design_key": design.key,
            "benchmark_toplevel": design.toplevel,
            "source_sha256": hashlib.sha256(synthetic["source_bytes"]).hexdigest(),
            "bootstrap_run_id": synthetic["manifest"]["bootstrap_run_id"],
        }, indent=2, sort_keys=True) + "\n"

    # -- the two datasets --------------------------------------------------------

    @staticmethod
    def _read_jsonl(path: str, what: str) -> dict[str, dict]:
        """Every `cid003` row of one JSONL, keyed by `id`.

        An absent dataset raises rather than returning nothing — the trap RTLLM fell into, where a
        fresh clone scored 0/0 and exited 0.
        """
        if not os.path.isfile(path):
            raise FileNotFoundError(
                f"cvdp: {what} not found at {path}.\n"
                f"  The benchmark is external data and is not vendored.\n"
                f"  Point CVDP_DATASET / CVDP_HARNESS at the JSONL files, or fix the\n"
                f"  `dataset` and `harness` symlinks beside this file.\n"
                f"  Expected: a CVDP non-agentic code-generation JSONL, one record per line.")
        rows = {}
        with open(path, errors="replace") as f:
            for n, line in enumerate(f, 1):
                if not line.strip():
                    continue
                try:
                    r = json.loads(line)
                except json.JSONDecodeError as e:
                    raise ValueError(f"cvdp: {path} line {n} is not JSON: {e}") from e
                cats = r.get("categories") or []
                if not cats or cats[0] != CATEGORY:
                    continue
                rows[r["id"]] = r
        if not rows:
            raise ValueError(
                f"cvdp: {path} holds no {CATEGORY} rows.  That file is a CVDP JSONL of some "
                f"other split — the spec-to-RTL population lives in the non-agentic "
                f"code-generation file — and a lane with no designs is not a lane.")
        return rows

    def _load(self) -> tuple[dict[str, dict], dict[str, dict]]:
        """`(prompt rows, harness rows)`, matched by id, with the overlay checked before use."""
        if self._prompts is None:
            self._prompts = self._read_jsonl(DATASET, "prompt dataset")
            if HARNESS_SOURCE == "self":
                self._harness = self._prompts
            elif HARNESS_SOURCE == "overlay":
                # Loud, not silent.  Falling back to v1.0.2's own harnesses here would score the
                # 8 cocotb-1.x designs as design failures and report a full 78-design sweep.
                h = self._read_jsonl(HARNESS, "harness overlay (v1.1.0)")
                missing = sorted(set(self._prompts) - set(h))
                if missing:
                    raise ValueError(
                        f"cvdp: the harness overlay at {HARNESS} is missing "
                        f"{len(missing)} of {len(self._prompts)} {CATEGORY} ids, e.g. "
                        f"{missing[:3]}.  Grading those with the v1.0.2 harness would score "
                        f"cocotb-1.x import errors as design failures.  Fix the overlay, or "
                        f"set CVDP_HARNESS_SOURCE=self and say so in the report.")
                self._harness = h
            else:
                raise ValueError(
                    f"cvdp: CVDP_HARNESS_SOURCE={HARNESS_SOURCE!r} is not 'overlay' or 'self'.")
        return self._prompts, self._harness            # type: ignore[return-value]

    # -- the design set ----------------------------------------------------------

    @staticmethod
    def _spec_text(row: dict) -> tuple[str, list[str]]:
        """`(prose, context relpaths)` — the prompt, plus any `input.context` appended.

        The append fires on 1 of 78 designs.  See the module docstring: `resolve_spec` reads one
        file, so a context document staged beside it is a document nobody opens, and posing the
        prompt alone there would pose a smaller problem than the benchmark's.
        """
        prose = row.get("input", {}).get("prompt", "") or ""
        ctx = row.get("input", {}).get("context") or {}
        rels = sorted(k for k, v in ctx.items() if isinstance(v, str) and v.strip())
        for rel in rels:
            prose = (prose.rstrip("\n") + "\n\n"
                     + f"----- input.context: {rel} -----\n\n"
                     + ctx[rel].rstrip("\n") + "\n")
        return prose, rels

    @staticmethod
    def _materialise(path: str, text: str) -> None:
        """Write `text` to `path` only if it is not already there.

        Content-compared because `designs()` is called by the leak gate on every installed
        benchmark, and a spec cache that rewrote 78 files on every gate run would churn mtimes
        under whatever is reading them.  Written through a temp file and `os.replace` so a
        concurrent reader never sees half a prompt.
        """
        if os.path.isfile(path):
            try:
                if open(path, errors="replace").read() == text:
                    return
            except OSError:
                pass
        os.makedirs(os.path.dirname(path), exist_ok=True)
        fd, tmp = tempfile.mkstemp(dir=os.path.dirname(path), prefix=".spec-")
        try:
            with os.fdopen(fd, "w") as f:
                f.write(text)
            os.replace(tmp, path)
        except BaseException:
            if os.path.exists(tmp):
                os.unlink(tmp)
            raise

    def designs(self) -> list[Design]:
        if self._designs is not None:
            return self._designs
        prompts, harness = self._load()
        out, tops = [], {}
        for key in sorted(prompts):
            prow, hrow = prompts[key], harness[key]
            files = _harness_files(hrow)
            env = _parse_env(files.get("src/.env", ""))
            top = env.get("TOPLEVEL", "")
            if not top:
                # Without a TOPLEVEL there is nothing to tell the author to call the module and
                # nothing for Icarus to elaborate.  Every cid003 row has one; say so if that ends.
                raise ValueError(
                    f"cvdp: {key} has no TOPLEVEL in src/.env.  The module name is read from the "
                    f"harness because 14 of 78 prompts never mention it; a design with neither "
                    f"cannot be posed.")
            # Unique within cid003 today.  `TOPLEVEL` is NOT unique across the whole 302-row file
            # (83 collisions), so this is asserted rather than assumed: two designs sharing a
            # module name would still key apart, but every report row that quoted the toplevel
            # instead of the key would silently merge them.
            if top in tops:
                raise ValueError(
                    f"cvdp: TOPLEVEL {top!r} is shared by {tops[top]} and {key}.  Reports that "
                    f"quote the module name would merge two designs into one row — namespace "
                    f"the toplevel before running anything.")
            tops[top] = key
            prose, ctx_rels = self._spec_text(prow)
            spec_path = os.path.join(SPEC_CACHE, f"{key}.spec.txt")
            self._materialise(spec_path, prose)
            src = env.get("VERILOG_SOURCES", "")
            blind = _blindness(files, env.get("MODULE", ""))
            cats = prow.get("categories") or []
            out.append(Design(
                key=key, bench=self.name, spec_path=spec_path,
                # From the `.env`, never from the prose.  On 14 of 78 the prose does not contain
                # this string at all, and on `sync_serial_communication_0001` the source filename
                # says `..._top` while the module is `..._tx_rx`.
                toplevel=top, camel=_camel(key),
                meta={
                    "difficulty": cats[1] if len(cats) > 1 else "",
                    "module": env.get("MODULE", ""),
                    "sim": env.get("SIM", ""),
                    "toplevel_lang": env.get("TOPLEVEL_LANG", ""),
                    # The filename Icarus is handed.  NOT `<toplevel>.v`: 63 of 78 are `.sv` and
                    # on 8 the stem differs from the module name outright.
                    "source_name": os.path.basename(src),
                    "source_path_in_container": src,
                    "harness_from": HARNESS_SOURCE,
                    "harness_files": len(files),
                    "has_harness": bool(files.get("src/test_runner.py")),
                    "context_files": ctx_rels,
                    "spec_includes_context": bool(ctx_rels),
                    "randomised": any(re.search(r"\brandom\.", v)
                                      for k, v in files.items() if k.startswith("src/")),
                    "param_randomised": key in PARAM_RANDOMISED,
                    "blind_probed": key in BLIND_PROBED,
                    "blind_static": blind["assert_free"] or blind["catches_assertionerror"],
                    "blindness": blind,
                    # This is an Answer-only key, not a T8/T9 benchmark reference.  In particular
                    # it must never be staged under ``ws/ref`` by the generic runner.
                    "synthetic_answer_key": self.synthetic_golden_path(key),
                    "answer_key_kind": ("synthetic_harness_pass" if
                                        self.synthetic_golden_path(key) else "harness"),
                }))
        self._designs = out
        return out

    def dataset_id(self) -> dict:
        """Hash the exact bytes being graded: the prompt, its context, and the harness that judges
        it — per design and overall.

        Both halves, because this lane poses one dataset and grades with another and a fingerprint
        of either alone would call two different experiments the same name.  Neither the path nor
        the version string is the identity: three byte-identical copies of one dataset sat on a
        disk and different scripts read different ones.
        """
        prompts, harness = self._load()
        h = hashlib.sha256()
        per = {}
        for d in self.designs():
            dh = hashlib.sha256()
            prow, hrow = prompts[d.key], harness[d.key]
            sources = [("prompt/prompt.txt",
                        (prow.get("input", {}).get("prompt", "") or "").encode())]
            for k, v in sorted((prow.get("input", {}).get("context") or {}).items()):
                sources.append(("context/" + k, (v or "").encode()))
            for k, v in sorted(_harness_files(hrow).items()):
                sources.append(("harness/" + k, v.encode()))
            synthetic = self._synthetic_golden(d.key)
            if synthetic:
                sources.append(("synthetic-reference/golden.sv", synthetic["source_bytes"]))
                sources.append(("synthetic-reference/manifest.json",
                                synthetic["manifest_bytes"]))
                sources.append(("synthetic-reference/answer-metadata.json",
                                self._synthetic_answer_metadata(d, synthetic).encode()))
            files = []
            for logical, data in sources:
                digest = hashlib.sha256(data).hexdigest()
                dh.update(logical.encode())
                dh.update(b"\0")
                dh.update(data)
                dh.update(b"\0")
                files.append({"name": logical, "sha256": digest})
            per[d.key] = {
                "sha256": dh.hexdigest(), "files": files,
                "scorer_files": [logical for logical, _data in sources
                                 if logical.startswith("harness/src/")],
                "reference_available": False,
                "answer_key_kind": "synthetic_harness_pass" if synthetic else "harness",
            }
            h.update(d.key.encode())
            h.update(b"\0")
            h.update(dh.digest())
        return {"bench": self.name, "category": CATEGORY, "designs": len(per),
                "sha256": h.hexdigest(), "oracle": self.oracle,
                # This is an explicit capability bit, not an inference from a missing path.
                # All 78 output.response values and output.context contents are empty.
                "reference_available": False,
                "prompts_from": os.path.realpath(DATASET),
                "harness_from": os.path.realpath(HARNESS) if HARNESS_SOURCE == "overlay"
                                else os.path.realpath(DATASET),
                "harness_source": HARNESS_SOURCE,
                "toolchain": toolchain(),
                "note": "prompts posed from v1.0.2, graded with the v1.1.0 harness (cocotb 2.x); "
                        "all 78 prompts are byte-identical between the two.  Run locally, NOT in "
                        "nvidia/cvdp-sim — published CVDP numbers are not comparable with these.",
                "per_design": per}

    def stage(self, design: Design, ws: str) -> None:
        """The prose, and only the prose.

        Not the harness — it ships in the same record as the prompt and it IS the oracle: every
        assertion, every stimulus vector and the module name itself.  One record holds both, which
        is why this copies a named file rather than anything derived from the record.

        The one design carrying `input.context` also gets that document written under its own
        relative path, in addition to the copy already appended to the spec.
        """
        dst = os.path.join(ws, "specs", f"{design.key}.spec.txt")
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(design.spec_path, errors="replace") as f:
            open(dst, "w").write(f.read())
        rels = design.meta.get("context_files") or []
        if rels:
            prompts, _ = self._load()
            ctx = prompts[design.key].get("input", {}).get("context") or {}
            for rel in rels:
                # `normpath` under a fixed root: a context key is dataset-supplied and a `..` in
                # one would write outside the workspace.
                p = os.path.normpath(os.path.join(ws, "specs", f"{design.key}.context", rel))
                root = os.path.join(ws, "specs", f"{design.key}.context")
                if not p.startswith(root + os.sep):
                    continue
                os.makedirs(os.path.dirname(p), exist_ok=True)
                open(p, "w").write(ctx[rel])

    def answer_materials(self, design: Design) -> dict[str, str]:
        """Return the case-local oracle material for the isolated Answer role.

        CVDP ships no reference RTL.  Before bootstrap its only answer key is the cocotb harness;
        after bootstrap this mapping contains only the accepted synthetic RTL.  The SpecIR driver
        freezes questions before requesting either mapping and mounts it only in Answer.
        """
        # The synthetic source intentionally stays in ``answer-key/``.  Putting it in ``ref/``
        # would turn on post-freeze T8/T9 reference replay, while this experiment is specifically
        # measuring question discovery + answering without that repair/validation channel.
        synthetic = self._synthetic_golden(design.key)
        if synthetic:
            metadata = json.loads(self._synthetic_answer_metadata(design, synthetic))
            # Interface names only: no stimuli, assertions or expected values leave this wall.
            names = set()
            for name, body in self.bootstrap_materials(design).items():
                if name.endswith(".py"):
                    names.update(re.findall(r"\bdut\.([A-Za-z_][A-Za-z0-9_]*)", body))
            metadata["verification_visible_names"] = sorted(
                n for n in names if not n.startswith("_") and
                re.search(r"\b" + re.escape(n) + r"\b", synthetic["source"]))
            return {
                "synthetic-golden.sv": synthetic["source"],
                "synthetic-metadata.json": json.dumps(metadata, indent=2, sort_keys=True) + "\n",
            }
        return self.bootstrap_materials(design)

    def bootstrap_materials(self, design: Design) -> dict[str, str]:
        """The full oracle granted only to the synthetic-reference construction role."""
        _prompts, harness = self._load()
        return dict(_harness_files(harness[design.key]))

    # -- the golden control ------------------------------------------------------

    def golden_source(self, design: Design) -> str | None:
        """CVDP still has no benchmark reference for a golden-control/T8/T9 arm.

        `output.response` is `""` on all 78 records and every value in `output.context` is the
        empty string; the paths a solution would occupy are present and their contents are not.
        A manifest-authenticated synthetic source is available through ``answer_materials`` only;
        it is deliberately not promoted into the stronger benchmark-reference capability.
        """
        del design
        return None

    def known_defects(self) -> dict:
        """Empty, and `KNOWN_DEFECTS.json` is deliberately absent.

        A defect entry must carry the control that established it.  The control for
        "no candidate can pass this design" is the golden one, and this dataset ships no golden
        source (see `golden_source`), so no entry here could be falsifiable and every one would be
        folklore with a schema around it.

        The harnesses that cannot report a failure are NOT recorded here for the same reason.
        `unwinnable` is the opposite claim — nobody can pass — and a blind harness is a design
        nobody can FAIL.  Marking either as a defect would remove it from a denominator on the
        strength of an argument, not a measurement.  They ride along on the verdict instead:
        `extra["blind_probed"]` and `extra["blind_static"]`, on every row, for the report to weigh.

        Still delegates to the socket, so a file written later — after a control that can be run
        here has been run — is honoured without editing this method.
        """
        return super().known_defects()

    # -- scoring -----------------------------------------------------------------

    def score(self, design: Design, vpath: str) -> Verdict:
        v = Verdict(key=design.key, oracle=self.oracle)
        v.extra.update({
            "difficulty": design.meta.get("difficulty", ""),
            "harness_from": design.meta.get("harness_from", HARNESS_SOURCE),
            "toplevel": design.toplevel,
            "module": design.meta.get("module", ""),
            # Carried on every row, never used to exclude one.  A `func_pass` on a design flagged
            # here is a pass the harness could not have withheld.
            "blind_probed": design.meta.get("blind_probed", False),
            "blind_static": design.meta.get("blind_static", False),
            # 55 of 78 randomise and 8 randomise the elaborated circuit.  Every number from this
            # lane is a sample; a row that does not say so invites being read as a measurement.
            "randomised": design.meta.get("randomised", False),
            "param_randomised": design.meta.get("param_randomised", False),
            "toolchain": toolchain(),
        })
        try:
            return self._score(design, vpath, v)
        except Exception as e:                                   # score must be total
            v.status, v.detail = "harness_error", f"{type(e).__name__}: {e}"
            return v

    def _score(self, design: Design, vpath: str, v: Verdict) -> Verdict:
        _, harness = self._load()
        files = _harness_files(harness[design.key])
        # Docker metadata is part of the frozen dataset identity, but the local scorer below
        # executes only `src/`.  Record and execute the exact same in-memory harness bytes so
        # every measured arm can prove which checker it actually used.
        scorer_inputs = [
            {"name": "harness/" + rel,
             "sha256": hashlib.sha256(content.encode()).hexdigest()}
            for rel, content in sorted(files.items()) if rel.startswith("src/")
        ]
        v.extra["dataset_inputs"] = list(scorer_inputs)
        v.extra["score_inputs"] = list(scorer_inputs)
        if not files.get("src/test_runner.py") or "src/.env" not in files:
            v.status, v.detail = "harness_error", "this record ships no src/test_runner.py or .env"
            return v
        if not os.path.isfile(vpath):
            v.status, v.detail = "not_emitted", f"no {vpath}"
            return v
        env_file = _parse_env(files["src/.env"])
        src_name = os.path.basename(env_file.get("VERILOG_SOURCES", "")) or f"{design.toplevel}.v"

        with tempfile.TemporaryDirectory(prefix=f"cvdp-{design.key}-") as wd:
            rtl, src, rundir = (os.path.join(wd, d) for d in ("rtl", "src", "rundir"))
            for d in (rtl, src, rundir):
                os.makedirs(d, exist_ok=True)
            # The candidate takes the harness's OWN filename, not `<toplevel>.v`.  On 8 designs
            # the two differ and on 63 the extension is `.sv`; Icarus is handed the path from
            # VERILOG_SOURCES, so that path is what has to exist.
            with open(vpath, errors="replace") as f:
                open(os.path.join(rtl, src_name), "w").write(f.read())
            for rel, content in files.items():
                if not rel.startswith("src/"):
                    continue                     # docker-compose.yml / Dockerfile are not ours
                p = os.path.normpath(os.path.join(wd, rel))
                if not p.startswith(src + os.sep):
                    continue                     # a `..` in a dataset-supplied key
                os.makedirs(os.path.dirname(p), exist_ok=True)
                open(p, "w").write(content)

            env = {k: v2 for k, v2 in os.environ.items()
                   # A caller's pytest configuration must not reach a benchmark run: addopts that
                   # add a plugin, change the summary format or reorder tests would be silently
                   # scoring somebody else's preferences.
                   if k not in ("PYTEST_ADDOPTS", "PYTEST_PLUGINS", "PYTHONPATH",
                                "COCOTB_RESULTS_FILE", "VERILOG_SOURCES", "TOPLEVEL", "MODULE")}
            env.update(env_file)                 # SIM / TOPLEVEL / MODULE / TOPLEVEL_LANG / WAVE
            env["VERILOG_SOURCES"] = os.path.join(rtl, src_name)
            env["PYTHONPATH"] = src              # where `harness_library` and the testbench live
            env["PYTHONDONTWRITEBYTECODE"] = "1"

            cmd = ["python3", "-m", "pytest", "-q", "-s", "--color=no",
                   "-o", f"cache_dir={os.path.join(wd, '.cache')}",
                   os.path.join(src, "test_runner.py")]
            # `-s` is load-bearing, not verbosity.  cocotb's tally is printed by `vvp`, a
            # grandchild of pytest, and pytest's fd capture swallows it on every PASSING test —
            # so without `-s` the cross-check reads nothing on exactly the runs it confirms.
            rc, out, expired = _run(cmd, rundir, env, TIMEOUT)
            simulator_built = os.path.isfile(os.path.join(rundir, "sim_build", "sim.vvp"))
            v.extra["pytest_rc"] = rc
            v.extra["cmd"] = "python3 -m pytest -q -s <tmp>/src/test_runner.py"
            # Read the simulator's own log BEFORE the tree is deleted.  Icarus does not write its
            # diagnostics to our pipe: every harness passes `log_file=` to `runner.build`, so a
            # candidate that will not elaborate produces `sim.log: syntax error / I give up.` in
            # the run directory and nothing but `subprocess.CalledProcessError` on stdout.  A
            # verdict whose detail is the name of a Python exception says the harness broke; the
            # log says the design did.
            logs = _build_logs(rundir)

        if expired:
            v.syntax_pass = simulator_built
            v.status = "timeout" if simulator_built else "harness_error"
            prefix = (f"the harness did not return within {TIMEOUT} s" if simulator_built else
                      f"the harness timed out before producing a simulator image in {TIMEOUT} s")
            v.detail = prefix + "\n" + out.strip()[-500:]
            v.extra["cocotb_seeds"] = [int(s) for s in _COCOTB_SEED.findall(out)]
            return v
        return self._read(out, v, logs)

    @staticmethod
    def _read(out: str, v: Verdict, logs: str = "") -> Verdict:
        """Adjudicate from pytest's summary, cross-checked against every cocotb tally.

        Primary is the LAST `in <n>s` line, because a collection error prints one summary and the
        run prints another and the first is not the one that describes the run.

        The cross-check reads ALL the tallies.  8 designs fan out with `@pytest.mark.parametrize`
        and print one per case — `low_pass_filter_0001` prints 54 — and adjudicating a 54-case
        sweep on case 1 is adjudicating 2% of it.

        `failed == 0` rather than "something passed": `static_branch_predict_0001` defines a second
        pytest function whose whole body is a `print`, so on that design "something passed" is true
        of every candidate ever written.

        `logs` is the simulator's own log files, which are NOT on the pytest stream — see `_score`.
        They decide nothing; they are read only to say WHY a failing run failed.
        """
        seeds = [int(s) for s in _COCOTB_SEED.findall(out)]
        tallies = [{"tests": int(a), "pass": int(b), "fail": int(c), "skip": int(d)}
                   for a, b, c, d in _COCOTB_TALLY.findall(out)]
        cocotb_fail = sum(t["fail"] for t in tallies)
        cocotb_ran = sum(t["tests"] for t in tallies)
        v.extra.update({"cocotb_seeds": seeds, "cocotb_tallies": len(tallies),
                        "cocotb_tests": cocotb_ran, "cocotb_fail": cocotb_fail})
        if _BUILD_FAILED.search(out) or _BUILD_FAILED.search(logs):
            # Not a status of its own: under this oracle an elaboration failure is a pytest error
            # inside `runner.build()`.  Recorded so "did not elaborate" stays separable from
            # "elaborated and mismatched" without a fifth word that means something else on the
            # other three lanes.
            v.extra["build_failed"] = True
            # Only here, and not on every run.  `\berror:` is common in a passing simulation's
            # own chatter, and a `compile_errors` list populated on a functional mismatch would
            # send a reader looking for a syntax problem that is not there.
            errs = [ln.strip() for ln in _IVERILOG_ERR.findall(logs) if ln.strip()]
            if errs:
                v.extra["compile_errors"] = errs[:5]
            v.status = "compile_fail"
            v.syntax_pass = False
            v.detail = (("\n".join(v.extra.get("compile_errors", [])) + "\n---\n") if
                        v.extra.get("compile_errors") else "") + (logs or out).strip()[-700:]
            return v

        summary = None
        for m in _SUMMARY_LINE.finditer(out):
            body = m.group("body").strip().strip("=").strip()
            if _COUNT.search(body) or _NO_TESTS.search(body):
                summary = (body, float(m.group("secs")))
        if summary is None:
            # Silence is a statement about the run, not about the design.  NEVER `func_fail`.
            v.status = "no_verdict"
            v.detail = ("pytest printed no summary line\n" + out.strip()[-700:])
            return v

        body, secs = summary
        # pytest says `1 error` and `2 errors`, `1 warning` and `2 warnings`.  Folded to one key
        # each: a run whose plural form was counted under a second key reports `errors == 0` while
        # holding an error, and `errors == 0` is half of the pass rule.
        _PLURAL = {"errors": "error", "warnings": "warning", "reruns": "rerun"}
        counts: dict[str, int] = {}
        for n, word in _COUNT.findall(body):
            w = word.lower()
            w = _PLURAL.get(w, w)
            counts[w] = counts.get(w, 0) + int(n)
        passed = counts.get("passed", 0)
        failed = counts.get("failed", 0)
        errors = counts.get("error", 0)
        v.extra.update({"pytest_summary": body, "pytest_seconds": secs,
                        "passed": passed, "failed": failed, "errors": errors,
                        "skipped": counts.get("skipped", 0)})
        # The nearest thing this lane has to what the other three call `syntax_pass`, and it is
        # derived from the RUN rather than from a separate compile step: cocotb printed a tally,
        # so `iverilog` elaborated the candidate and `vvp` started it.  Deliberately not inferred
        # from "pytest collected something" — a collected test that died in `runner.build()` is
        # exactly the case this flag must not claim.
        v.syntax_pass = cocotb_ran > 0 and not v.extra.get("build_failed", False)

        # The head of the failure a reader wants is the simulator's line, not the tail of pytest's
        # `FAILED ...` roll-call, which on a non-elaborating candidate is ten identical copies of
        # `subprocess.CalledProcessEr...` and says nothing about the Verilog.
        head = ""
        if v.extra.get("compile_errors"):
            head = "\n".join(v.extra["compile_errors"]) + "\n---\n"

        if failed or errors:
            v.status, v.func_pass = "func_fail", False
            v.detail = head + out.strip()[-700:]
        elif passed > 0 and cocotb_fail == 0:
            v.status, v.func_pass = "func_pass", True
        elif passed > 0 and cocotb_fail:
            # The readers disagree.  The failure wins, and the disagreement is on the row: a
            # cocotb test that failed while pytest reported a clean run means the harness swallowed
            # something, and a pass recorded here without that note is a pass nobody could audit.
            v.status, v.func_pass = "func_fail", False
            v.detail = head + out.strip()[-700:]
        else:
            # A summary that counted nothing — `no tests ran`, or only warnings.  The harness
            # collected nothing to run, which is not the design's failure.
            v.status = "no_verdict"
            v.detail = head + out.strip()[-700:]

        agree = (v.status == "func_pass") == (cocotb_fail == 0 and cocotb_ran > 0)
        if not agree:
            v.extra["reader_disagreement"] = {
                "pytest": {"passed": passed, "failed": failed, "errors": errors},
                "cocotb": {"tallies": len(tallies), "tests": cocotb_ran, "fail": cocotb_fail},
                "resolved_as": v.status,
                "rule": "the failure wins; absent cocotb tallies are absence of evidence, not "
                        "evidence of a pass",
            }
        v.mismatch_outputs = [t for t in tallies if t["fail"]]
        return v

    def score_all(self, items, workers: int = 1) -> dict:
        """Judge many designs.  Each runs in its own temporary directory and touches nothing
        outside it, so they are independent; 78 local cocotb runs are worth overlapping.

        Note what overlapping does NOT fix: 8 of these harnesses randomise the elaborated circuit
        unseeded, so two workers scoring the same design are running two different problems.  That
        is a property of the dataset and is recorded per row, not repaired here.
        """
        if workers <= 1 or len(items) <= 1:
            return {d.key: self.score(d, p) for d, p in items}
        out = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
            futs = {ex.submit(self.score, d, p): d.key for d, p in items}
            for f in concurrent.futures.as_completed(futs):
                out[futs[f]] = f.result()
        return out


def adapter() -> Adapter:
    return CVDP()


if __name__ == "__main__":
    import sys
    a = adapter()
    ds = a.designs()
    ident = a.dataset_id()
    tc = ident["toolchain"]
    n_diff: dict[str, int] = {}
    for d in ds:
        n_diff[d.meta["difficulty"]] = n_diff.get(d.meta["difficulty"], 0) + 1
    blind = [d.key for d in ds if d.meta["blind_static"] or d.meta["blind_probed"]]
    print(f"cvdp: {len(ds)} designs ({CATEGORY}), oracle {a.oracle}")
    print(f"  {ident['sha256']}  {ident['prompts_from']}")
    print(f"  harness [{ident['harness_source']}]  {ident['harness_from']}")
    print(f"  {', '.join(f'{k}={v}' for k, v in sorted(n_diff.items()))}"
          f"   randomised={sum(1 for d in ds if d.meta['randomised'])}"
          f"   param-randomised={sum(1 for d in ds if d.meta['param_randomised'])}")
    print(f"  blind (probed or static): {len(blind)} — {', '.join(sorted(blind))}")
    print(f"  toolchain: {tc['iverilog']} | cocotb {tc['cocotb']} | pytest {tc['pytest']}")
    print(f"  specs cached at {SPEC_CACHE}")
    print(f"  known_defects: {len(a.known_defects())}   golden control: none (dataset ships no "
          f"reference)")
    if "-v" in sys.argv:
        for d in ds:
            flags = "".join((" NO-HARNESS" if not d.meta["has_harness"] else "",
                             " BLIND" if d.meta["blind_static"] else "",
                             " BLIND?" if d.meta["blind_probed"]
                             and not d.meta["blind_static"] else "",
                             " PARAM-RAND" if d.meta["param_randomised"] else "",
                             " +CONTEXT" if d.meta["spec_includes_context"] else ""))
            print(f"  {d.key:56} {d.toplevel:44} {d.meta['difficulty']:7}"
                  f" {d.meta['source_name']:38}{flags}")
