#!/usr/bin/env python3
"""The benchmark interface, and the one place design names come from.

leanSilicon ships **no benchmark**. This file is the socket a benchmark plugs into, plus the
key-source both the sanitiser and the leak gate read, and nothing else. A dataset lives outside
the repository — under `$LEANSILICON_BENCH`, or `benchmarks/` if that is unset, which is
gitignored — because a benchmark is experimental data and this repository holds method.

## Why the socket exists at all

Each benchmark used to have *two* runners: a full one used by the proof arm (carrying that
benchmark's dataset bridges — parameter shims, module-name aliases, retry passes) and a bare
one used by the control. The control's scorer even documented itself as using "the SAME
benchmark bridges the proof-carrying arms use". It did not. The effect was measured: a design
whose emitted header was missing a parameter the testbench overrides failed for the control and
passed for the method, from the *same* defect, and nothing in either report recorded the
asymmetry because the bridge fields were not copied out.

An adapter therefore owns its bridges, and there is one code path for every arm. A profile
chooses *who writes the Verilog*; it can never choose *how the Verilog is judged*.

## What an adapter must provide

    designs()            -> [Design]        the design set, from the dataset, in a stable order
    stage(design, ws)    -> None            put the prose spec (and only that) into a workspace
    score(design, vpath) -> Verdict         judge one emitted .v through the benchmark's oracle
    known_defects()      -> {key: Defect}   designs this benchmark cannot fairly grade

`score` must be total: a crash is a verdict (`status="harness_error"`), never an exception that
aborts a run.

## Known defects are data, not folklore

Every benchmark examined so far ships designs no candidate can pass — testbenches that will not
elaborate on the configured simulator, reference implementations that fail their own testbench,
oracles that compare buses on cycles the protocol leaves undefined. Recording them as data lets
a verdict be marked `unwinnable` instead of silently counted as a method failure, and lets a
report state its denominator honestly.

A defect entry must carry the evidence that established it, because "this design is unfair" is
exactly the kind of claim that rots into an excuse if it is not falsifiable.

## The key source

`all_design_keys()` is here, and not in the stager, because the *sanitiser* and the *leak gate*
must not be able to disagree about what a design name is. They did: the gate checked the one
benchmark that had an adapter and saw 43 keys where the sanitiser saw 335, so 292 names were
redacted at stage time by a function whose work no gate ever confirmed. One import, one answer.

It returns keys from **every** installed benchmark, not the one being staged. Redacting only the
staged benchmark's names is the original bug in a new place: the assets are shared, so a
workspace staged for one dataset still carries lemma docstrings naming designs from another.
"""
from __future__ import annotations

import dataclasses
import importlib.util
import json
import os
import sys
from typing import Any

from . import paths

# Outside the repository by default is the point, not a convenience.  `benchmarks/` sits
# beside `method/` rather than inside it, and is gitignored; `$LEANSILICON_BENCH` lets the
# dataset live anywhere, including read-only.
BENCH_DIR = os.path.expanduser(paths.BENCH)


@dataclasses.dataclass
class Design:
    """One benchmark problem."""
    key: str                     # stable id; names the workspace file and the report row
    bench: str                   # adapter name
    spec_path: str               # the prose spec — the ONLY thing an authoring agent may read
    toplevel: str                # module name the oracle instantiates
    camel: str                   # Lean module name for the design file
    meta: dict[str, Any] = dataclasses.field(default_factory=dict)


@dataclasses.dataclass
class Verdict:
    """The result of judging one emitted design."""
    key: str
    status: str = "unscored"     # func_pass | func_fail | compile_fail | iverilog_fail
                                 # | timeout | no_verdict | not_emitted | harness_error
                                 # | unwinnable | oracle_unavailable
                                 # `oracle_unavailable` means the design was NOT MEASURED — the
                                 # simulator host could not be reached.  It is kept apart from
                                 # every failure status on purpose: a run once counted three
                                 # remote timeouts as non-passes, and two of the three were on
                                 # the arm the run was about.
    syntax_pass: bool = False
    func_pass: bool = False
    detail: str = ""             # human-readable head of the failure
    mismatch_outputs: list = dataclasses.field(default_factory=list)
    # `detail` is capped for readability.  Any statistic about *how many* outputs failed must
    # be derived from `mismatch_outputs`, never by counting matches in `detail`: the cap once
    # truncated exactly the hardest-failing designs and a per-output accuracy figure computed
    # from it was wrong by 30 points.
    bridges: dict = dataclasses.field(default_factory=dict)   # param_shim / module_alias / ...
    oracle: str = ""             # icarus | verilator | vcs | jaspergold — never left implicit
    extra: dict = dataclasses.field(default_factory=dict)


@dataclasses.dataclass
class Defect:
    """A design this benchmark cannot fairly grade."""
    key: str
    kind: str                    # broken-testbench | reference-fails-own-testbench
                                 # | spec-contradicts-reference | oracle-artifact
    summary: str
    evidence: str                # the control that established it — must be reproducible
    unwinnable: bool             # True = no candidate can pass; exclude from the denominator
    arms_affected: str = "both"
    oracle: str = ""             # the simulator this entry was JUDGED under, not the one in use
    reaudit: str = ""            # a later re-measurement: when, under what, and what it found

    # `oracle` is here because `unwinnable` is not a property of a design, it is a property of a
    # design under a simulator, and one such list's entries were all established under iverilog.
    # Two of them — a free-running oscillator and a ring counter — are unwinnable there for the
    # specific reason that iverilog cannot elaborate them, and both elaborate and pass under VCS.
    # An entry that does not say which oracle judged it reads as a fact about the design, and
    # gets carried across a simulator change that invalidates it.
    #
    # `reaudit` is one field rather than one per run.  It was written as `vcs_2026_08_13`, which
    # puts the date in the SCHEMA: the next re-measurement adds `vcs_2026_11_02` and every reader
    # has to know all of them, while a dataclass that lists neither silently drops both.  The
    # date belongs in the value.


class Adapter:
    """Subclass per benchmark.  Nothing here may depend on which arm produced the Verilog."""

    name: str = ""
    oracle: str = ""             # the simulator/prover this adapter judges with

    def designs(self) -> list[Design]:
        raise NotImplementedError

    def stage(self, design: Design, ws: str) -> None:
        raise NotImplementedError

    def score(self, design: Design, vpath: str) -> Verdict:
        raise NotImplementedError

    def score_all(self, items: list, workers: int = 1) -> dict[str, Verdict]:
        """Judge many designs.  `items` is [(Design, vpath)]; returns {key: Verdict}.

        The default is the obvious serial loop, so an adapter that does not override this
        behaves exactly as the simple case does.  An adapter whose oracle is a remote round-trip
        overrides it to overlap them — the judgement of one design must not depend on another's,
        which is why this returns a plain map and not an accumulated state.
        """
        return {d.key: self.score(d, p) for d, p in items}

    def dataset_id(self) -> dict[str, Any] | None:
        """Fingerprint of the exact bytes this adapter is grading, for provenance.

        `None` when the adapter cannot identify its data.  An adapter that CAN should hash the
        files it actually resolves — including any repair overlay — rather than the checkout
        directory: three byte-identical copies of one dataset sat on a disk and different scripts
        read different ones, so a path is not an identity and a copy is not a version.
        """
        return None

    # -- shared ------------------------------------------------------------------

    def known_defects(self) -> dict[str, Defect]:
        p = os.path.join(os.path.dirname(self._module_file()), "KNOWN_DEFECTS.json")
        if not os.path.exists(p):
            return {}
        return {d["key"]: Defect(**d) for d in json.load(open(p))["defects"]}

    def _module_file(self) -> str:
        import inspect
        return inspect.getfile(type(self))

    def design_map(self) -> dict[str, Design]:
        return {d.key: d for d in self.designs()}


# -------------------------------------------------------------------- loading and keys

def installed() -> list[str]:
    """Benchmark names present under `BENCH_DIR`, in a stable order."""
    if not os.path.isdir(BENCH_DIR):
        return []
    return sorted(n for n in os.listdir(BENCH_DIR)
                  if os.path.isdir(os.path.join(BENCH_DIR, n)) and not n.startswith((".", "_")))


def load(name: str) -> Adapter:
    """Import `<BENCH_DIR>/<name>/adapter.py` and return its `adapter()`.

    Loaded by path rather than by package name.  The dataset directory is not on `sys.path` and
    must not be put there: a benchmark that shadows a repository module — an `emit.py`, a
    `schema.py` — would be imported in preference to the method's own, and the failure would
    look like a bug in the method.

    Which leaves the one import a benchmark adapter genuinely needs.  Every one of them opens
    `from _adapter import Adapter, Design, Verdict` — that is the interface they implement — and
    the interface is THIS module.  `$LEANSILICON_BENCH` may point anywhere, including outside this
    repository entirely, so an adapter cannot be expected to compute a path back to the method
    tree; asking it to is how the wiring broke.  This module binds itself under the bare name
    instead, which grants exactly that one name and shadows nothing else.

    Itself, and not a copy.  The interface was a separate `_adapter.py` in the tree this came
    from and is merged into the loader here, so a second file carrying a second `Design` would
    hand every adapter classes that are not the ones `load`'s own annotations name — two types
    with one name, agreeing until the day one of them gains a field.

    The failure this repairs was silent by design in the wrong direction.  `adapters/_adapter.py`
    was the planned home; the directory consolidation folded sixteen top-level directories into
    four and dropped that one, so every adapter raised `ModuleNotFoundError` on import.
    `all_design_keys` catches that, records the benchmark as `UNREADABLE` and returns no keys —
    and a leak gate with no keys checks nothing.  The gate reports `checked: false, pass: false`
    rather than a pass, which is the only reason this surfaced at all instead of certifying a
    workspace nobody had scanned.

    The loaded module is registered in `sys.modules` before it is executed, which is the
    documented way to load by path and is load-bearing here rather than tidy.  Without it
    `inspect.getfile(type(adapter))` cannot find the class's source — `inspect` resolves a class
    to a file through `sys.modules[cls.__module__]`, and an unregistered module leaves it with
    nothing to resolve, so it reports the class as a *built-in* and raises.  That is the one
    lookup `known_defects()` performs, so every benchmark shipping a `KNOWN_DEFECTS.json` would
    have raised `TypeError` on the first call.  rtllm ships none, which is the only reason this
    survived: the socket's defect channel had never once been read.
    """
    sys.modules.setdefault("_adapter", sys.modules[__name__])
    p = os.path.join(BENCH_DIR, name, "adapter.py")
    if not os.path.isfile(p):
        raise FileNotFoundError(f"no adapter at {p}")
    spec = importlib.util.spec_from_file_location(f"_leansilicon_bench_{name}", p)
    if spec is None or spec.loader is None:
        raise ImportError(f"could not load {p}")
    mod = importlib.util.module_from_spec(spec)
    sys.modules[spec.name] = mod
    spec.loader.exec_module(mod)
    return mod.adapter()


def bench_for_key(key: str) -> str:
    """Which installed benchmark owns `key`, or `""` if none does or more than one does.

    Runs land in `data/part<N>/<bench>/`, and the caller naming the run should not have to repeat
    a fact the datasets already state.  So this answers it from the same source `all_design_keys`
    reads, and every caller treats `""` the same way: fall back to `paths.LOCAL`, or to whatever
    `--bench` said.

    Ambiguity returns `""` rather than picking.  Two corpora using one name for different designs
    is the reason the benchmark layer exists at all, and a function that resolved it by sort order
    would put the collision back one level down while appearing to have handled it.
    """
    if not key:
        return ""
    owners = []
    for name in installed():
        man = os.path.join(BENCH_DIR, name, "DESIGNS.json")
        got: set[str] = set()
        if os.path.isfile(man):
            got = {r["key"] if isinstance(r, dict) else r for r in json.load(open(man))}
        elif os.path.isfile(os.path.join(BENCH_DIR, name, "adapter.py")):
            try:
                got = {d.key for d in load(name).designs()}
            except Exception:                                   # noqa: BLE001
                continue
        if key in got:
            owners.append(name)
    return owners[0] if len(owners) == 1 else ""


def all_design_keys() -> tuple[set[str], list[str]]:
    """Every design name in every installed benchmark, and where each batch came from.

    A benchmark contributes through `DESIGNS.json` (a list of keys, or of records with a `key`)
    if it has one, and otherwise through its adapter's `designs()`. `_extra_keys.json` at the
    dataset root adds names that no adapter enumerates — a dataset whose loader is not written
    yet still has designs whose names must not leak.

    An adapter that raises is recorded as `UNREADABLE` and contributes nothing. It is not
    silently skipped: a key source that quietly shrinks disarms the sanitiser, and the caller
    prints the sources so a shrunken list is visible in the run's own output.

    Every key, including the short ones. A `len(k) > 5` filter used to live on this line, and it
    silently disarmed the sanitiser's own short-key rule: that function redacts `pe` / `alu` /
    `fsm` / `RAM` / `accu` in their code-quoted form, but the short keys never reached it, so the
    branch had nothing to act on. The floor was removed in the place it was noticed and left in
    the place it took effect. Length policy belongs to whoever redacts or scans, not here.
    """
    keys: set[str] = set()
    sources: list[str] = []
    for name in installed():
        got: set[str] = set()
        man = os.path.join(BENCH_DIR, name, "DESIGNS.json")
        if os.path.isfile(man):
            got = {r["key"] if isinstance(r, dict) else r for r in json.load(open(man))}
        elif os.path.isfile(os.path.join(BENCH_DIR, name, "adapter.py")):
            try:
                got = {d.key for d in load(name).designs()}
            except Exception:
                sources.append(f"{name}:UNREADABLE")
                continue
        if got:
            keys |= got
            sources.append(f"{name}:{len(got)}")
    extra = os.path.join(BENCH_DIR, "_extra_keys.json")
    if os.path.isfile(extra):
        for bench, ks in json.load(open(extra)).items():
            if bench.startswith("_"):
                continue
            keys |= set(ks)
            sources.append(f"{bench}*:{len(ks)}")
    return keys, sources


if __name__ == "__main__":
    ks, srcs = all_design_keys()
    print(f"bench dir: {BENCH_DIR}"
          + ("" if os.path.isdir(BENCH_DIR) else "   (does not exist)"))
    print(f"installed: {', '.join(installed()) or '—'}")
    print(f"{len(ks)} design key(s) from [{', '.join(srcs) or '—'}]")
