#!/usr/bin/env python3
"""Build a workspace from a profile and one prose specification.  The only way one is created.

    python3 -m leanrtl.stage --profile two-author --key accu --spec path/to/accu.txt
    python3 -m leanrtl.stage --profile two-author --key accu --bench rtllm

A workspace is disposable: everything in it is derived from `profiles/<name>.yaml`,
`assets/MANIFEST.yaml`, `framework/` and one prose file.  If you find yourself editing one by
hand, change the profile instead — hand-edits are how thirteen undocumented workspaces
accumulated in a home directory, each subtly different, none reproducible.

## One design per workspace

A slot holds exactly one design (`common/workspace.py` says why at length).  So there is no
manifest, no `--only`, and no design set: `--key` names the design, `--spec` is its prose, and
everything in the tree is about that one thing.  This is the single biggest simplification over
the tree this method comes from, where a workspace held fifty designs and the isolation argument
had to be re-made for every file that could see across them.

## Isolation is physical

The workspace gets the prose specification and nothing else.  Testbenches, reference RTL and
dataset files live beside the spec in the checkout and must never follow it in.  The workspace
is its own git repository with history starting from empty, so a deleted asset cannot be
recovered with `git show`, and `harness_lib.py` resolves benchmark roots relative to the
workspace — so inside one they resolve to a directory that does not exist and every path to a
testbench is dead.  Isolation is a missing directory, not a rule the agent is asked to follow.

## The two inputs, and why either is accepted

`--spec <path>` takes a prose file directly.  That is the interface: this half consumes prose,
and the prose may be a benchmark's original text or the decided text `leanspec` produced.  It
cannot tell which, deliberately — if it could, "the decided prose is better" would be a claim
about a code path rather than about the prose.

`--bench <name>` is a convenience that reads the prose out of an installed adapter and then does
exactly the same thing.  It exists so that running a benchmark does not require copying files by
hand; it grants this half no knowledge it does not have with `--spec`.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

from common import adapter, paths, profiles, provenance, variant   # noqa: E402

# `lean-toolchain` is the one file a workspace takes from ABOVE the method tree.  Lake wants a
# package at the top of the repository, so the toolchain pin lives there and `framework/` does not
# carry a second copy — one toolchain, no drift.  Named here rather than reached for as
# `paths.REPO` at the point of use because two functions below bind a local list called `paths`,
# and the module would be shadowed exactly where it is needed.  The reorganisation that split the
# tree into `method/` and `data/` moved this file out from under `ROOT` and left both uses behind;
# they failed at staging with a `FileNotFoundError` naming `method/lean-toolchain`.
TOOLCHAIN = os.path.join(paths.REPO, "lean-toolchain")

# The authoring toolbox is `leanrtl`'s own, and sits beside this file rather than at the
# top of the tree: it is what gets copied into `<ws>/scripts/`, and nothing in the other
# half has any business importing it.
AUTHORING = os.path.join(os.path.dirname(os.path.abspath(__file__)), "authoring")
LAKE = os.path.expanduser("~/.elan/bin/lake")


# ------------------------------------------------------------------------ assets

def asset_sets() -> dict:
    import yaml
    return yaml.safe_load(open(os.path.join(ROOT, "assets", "MANIFEST.yaml")))["sets"]


def copy_assets(profile: dict, ws: str) -> list[str]:
    sets, copied = asset_sets(), []
    for name in profile.get("assets", []):
        if name not in sets:
            sys.exit(f"stage: profile '{profile['name']}' wants unknown asset set '{name}'")
        for rel in sets[name].get("paths", []):
            src = os.path.join(ROOT, "assets", rel.rstrip("/"))
            if not os.path.exists(src):
                continue
            dst = os.path.join(ws, "assets", rel.rstrip("/"))
            os.makedirs(os.path.dirname(dst), exist_ok=True)
            if os.path.isdir(src):
                # `dirs_exist_ok` because `refresh` calls this on a workspace that already holds
                # a sanitised — and possibly stale — copy.  Overwrite in place; `sanitize` runs
                # afterwards and redacts the fresh bytes.  A file DELETED from the repository is
                # not removed from the workspace by this, which is the one asymmetry with a full
                # stage; the digest hashes path names so the staleness is at least visible.
                shutil.copytree(src, dst, dirs_exist_ok=True)
            else:
                shutil.copy(src, dst)
            copied.append(rel)
    for doc in profile.get("rules", []):
        src = os.path.join(ROOT, "assets", "instructions", doc)
        if os.path.exists(src):
            os.makedirs(os.path.join(ws, "assets", "instructions"), exist_ok=True)
            shutil.copy(src, os.path.join(ws, "assets", "instructions", doc))
            copied.append(f"instructions/{doc}")
    return copied


# ------------------------------------------------------------------- sanitisation

# Every accumulated skill and lemma cites its provenance as a path into a design tree —
# `LeanRTL/Designs/VEval/Prob046Dff8p.lean:88`.  The basename is the design name in CamelCase,
# which matches NO key-derived pattern when the key is snake_case: `\bProb046\b` does not match
# inside `Prob046Dff8p`, and the substring residual check misses it too when the key carries a
# suffix the camel form drops.  Verified: a key-only sanitiser reported `residual: 0` on a
# workspace that still named a design three times on one line.  Redact the path shape directly.
#
# The rule is by ROOT, not by an enumerated list of design directories: `LeanRTL/Core/` is the
# framework and its filenames are legitimate references an author needs, everything else under
# `LeanRTL/` is design-tree and its basenames are design names.  An enumerated list missed
# `LeanRTL/WholeDesign/UpDownCounterTrace.lean` — the same "written against the directories I
# happened to think of" failure, one level down.
FRAMEWORK_ROOTS = ("Core", "Backend", "Frontend", "Lib")
DESIGN_PATH = re.compile(r"(LeanRTL/)((?!(?:" + "|".join(FRAMEWORK_ROOTS) + r")/)"
                         r"(?:\w+/)*)([A-Za-z0-9_]+)(\.lean)")


def variants(key: str) -> set[str]:
    """A key leaks under several spellings; redact all of them."""
    camel = "".join(w[:1].upper() + w[1:] for w in re.split(r"[_\-]", key))
    return {key, camel, key.replace("_", ""), key.replace("_", "-")}


# Everything an author can read.  `assets/` alone was NOT enough -- and that was not a near-miss,
# it was most of the surface:
#
#   * a shared `Lift.lean` named one design and gave its output shape while eliding its two
#     neighbours, handing that author two of its own recorded ambiguities.
#   * a shared `Semantic/Accum.lean` described one design's state as "a `(cnt, acc, …)` tuple
#     that clears `acc` every 4 beats" and called another an "un-gated MAC / running-sum" -- the
#     core behavioural reading of both, in the library both authors are told to use.
#   * `scripts/*.py` picked up design names from comments.
#
# `specs/`, `contracts/` and `notes/` are this design's own and legitimately named -- an author is
# given its own -- and `LeanRTL/Blind/` holds the authored file itself.  Everything else is shared
# and must be name-free.
SANITIZE_ROOTS = ("assets", "LeanRTL", "docs", "scripts")
SANITIZE_SKIP = ("LeanRTL/Blind", "specs", "contracts", "notes", "out", "log", "scratch",
                 "frags", "given", "simdiff", "emits", "snapshot")

# `SANITIZE_SKIP` is a DIRECTORY rule -- it is matched against `rel_root`.  These two are files
# sitting directly in `LeanRTL/`, so the walk reaches them and redacts them, and redacting them is
# not merely pointless but destructive.
#
# Pointless, because both are machine-generated by `bb.py` from whatever `LeanRTL/Blind/` already
# holds.  They cannot name a design the workspace does not have -- which is exactly why
# `LeanRTL/Blind` is in `SANITIZE_SKIP` in the first place.  The registry is a table of contents
# for a directory we have already agreed not to redact.
#
# Destructive, because the name appears inside an import PATH: `import LeanRTL.Blind.SyncLifo`
# becomes `import LeanRTL.Blind.(design name elided)`, which is not a module reference at all.
# `lake build` then fails on the whole library, so a refresh dies at its own build step and never
# reaches the stamp -- leaving a workspace that has in fact taken the new framework but still
# reports the old fingerprint, i.e. permanently stale to every reader.
SANITIZE_SKIP_FILES = ("LeanRTL/BlindRegistry.lean", "LeanRTL/BlindParamRegistry.lean")


def sanitize(ws: str, keys: set[str]) -> dict:
    """Redact other designs' names out of everything this workspace's author can read."""
    # No length floor.  A `len(v) > 5` test exempted `fsm`, `pe`, `alu`, `RAM`, `ROM`, `accu`
    # outright -- six of fifty keys, and two of the three worst leaks found.  Short keys are
    # ordinary English (`pe`, `RAM`), so for those redact only the code-quoted form, which is how
    # a leak is actually written.  Long keys keep the word-boundary rule.
    #
    # `\b` is NOT that rule, though it was.  `_` and `-` are word characters to `re`, so
    # `\brightshifter\b` does not match in `rightshifter_reads` -- and a design name suffixed
    # with `_reads` / `_observe` / `_trace` is not an edge case, it is how a design name appears
    # in Lean, i.e. the single most leak-prone form there is.  Verified: a staged workspace's
    # `assets/skills/patterns/fixed-latency-delay-law.md` carried another design's entire
    # whole-trace theorem -- statement, 8-bit width, port `d`, register `q`, exact latency -- as
    # a worked example, past a sanitiser reporting 47 files redacted.  Only the residual scan saw
    # it, and the residual scan is advisory.  Boundary on alphanumerics instead, so that `_` and
    # `-` terminate a name the way a space does.
    spellings = {v for k in keys for v in variants(k)}
    changed, residual = [], []

    def walkable():
        for top in SANITIZE_ROOTS:
            for root, dirs, files in os.walk(os.path.join(ws, top)):
                dirs[:] = [d for d in dirs if d not in ("__pycache__", ".lake", ".git")]
                rel_root = os.path.relpath(root, ws)
                if any(rel_root == s or rel_root.startswith(s + os.sep) for s in SANITIZE_SKIP):
                    dirs[:] = []
                    continue
                for fn in files:
                    p = os.path.join(root, fn)
                    if os.path.relpath(p, ws).replace(os.sep, "/") in SANITIZE_SKIP_FILES:
                        continue
                    yield p

    # Compile once: the spelling set exceeds Python's regex cache, so compiling inside
    # the per-file loop reparses every expression for every staged source file.
    redactions = [(k, re.compile((r"`" + re.escape(k) + r"`") if len(k) <= 5
                  else r"(?<![A-Za-z0-9])" + re.escape(k) + r"(?![A-Za-z0-9])"))
                  for k in sorted(spellings, key=len, reverse=True)]

    for p in walkable():
        try:
            text = open(p, errors="replace").read()
        except OSError:
            continue
        new, hits = text, []
        if DESIGN_PATH.search(new):
            hits.append("<design-path>")
            new = DESIGN_PATH.sub(r"\1\2(elided)\4", new)
        for k, pat in redactions:   # longest first, identical substitution order
            if pat.search(new):
                hits.append(k)
                new = pat.sub("(design name elided)", new)
        if hits:
            open(p, "w").write(new)
            changed.append({"file": os.path.relpath(p, ws), "keys": sorted(hits)})

    # A name can survive redaction inside a LARGER identifier (`UpDownCounterM6`) or inside an
    # ordinary English word (`edge-detection` contains the key `edge-detect`).  The first is a
    # real leak, the second is noise, and only a human reading the context can tell them apart —
    # so report with context and never auto-redact here.  Silently rewriting the second kind
    # would corrupt prose the authoring agent depends on.
    #
    # Scan the SAME roots the redaction covered.  Scanning only `assets/` while redacting more
    # would report `residual: 0` about a workspace nobody had looked at -- which is how the
    # library leaks survived: the scan was clean because it was pointed at the wrong tree.
    for p in walkable():
        try:
            t = open(p, errors="replace").read()
        except OSError:
            continue
        for k in spellings:
            # A SUBSTRING scan is the point here -- it is what catches a name surviving inside a
            # larger identifier.  But for a short key it degenerates: `pe` matches "type" and
            # "specEnv", `alu` matches "value", `accu` matches "accumulator".  Reporting 229 of
            # those trains the reader to skip the field, which is worse than not having it.
            # Short keys are redacted in their code-quoted form above and excluded here by design.
            if len(k) <= 5:
                continue
            i = t.find(k)
            if i >= 0:
                residual.append({"file": os.path.relpath(p, ws), "key": k,
                                 "context": t[max(0, i - 60):i + len(k) + 60]
                                             .replace("\n", " ").strip()})
    return {"redacted": changed, "residual": residual,
            "n_keys": len(keys), "n_spellings": len(spellings)}


# ------------------------------------------------------------------- the Lean project

# The scaffold a single author replaces.  Deliberately a design that COMPILES and is obviously
# not the assignment: an author that leaves any of it behind has left something visible, whereas
# an empty section would look like work in progress.  `verify.is_scaffold` keys on the section-1
# sentence below, so it must not be reworded without changing that constant too.
#
# `name` is the design's TOPLEVEL, not its key.  On some benchmarks the two are the same string
# for every design, which is why this once read `{key}` and why the difference could not show up
# as a test failure.  It is not general: one benchmark's 156 designs all have toplevel
# `TopModule`, because its checker instantiates one fixed module name.  A scaffold that pre-fills
# the key there is a trap with no floor under it — the author that keeps the placeholder's name
# emits the wrong module and the row reads `compile_fail`, indistinguishable in a report from a
# design that got the hardware wrong.
SINGLE_SCAFFOLD = """
/-! ## 1. impl -/

/-- REPLACE ME.  A 4-bit counter, here only so the scaffold compiles. -/
def impl : Module :=
  {{ name := "{toplevel}"
   , inputs  := [ {{ name := "clk", width := 1 }} ]
   , outputs := [ {{ name := "q", width := 4, expr := .var "q" 4 }} ]
   , regs    := [ {{ name := "q", width := 4, next := .add (.var "q" 4) (.const 1), init := 0 }} ]
   , clock   := some "clk" }}

/-! ## 2. spec -/

-- REPLACE ME.  The untyped adapters the tools call; give them a typed oracle to wrap.
def specInit : List (String × Nat) := []
def specStep (_regs _ins : List (String × Nat)) : List (String × Nat) := []
def specOuts (_regs _ins : List (String × Nat)) : List (String × Nat) := []

/-! ## 3. L1 -/

-- REPLACE ME.  A next-state law per register and an output law per port, over all inputs.

/-! ## 4. whole-trace -/

-- REPLACE ME.  For a sequential design climb to SimRefines and then the full Refines, whose
-- `obs` obligation is what makes the claim about the pins.  For a combinational design say so
-- explicitly rather than leaving this empty.
"""

# The two AUTO-GENERATED registries, in the state a workspace starts in.  They are constants
# rather than literals at their point of use because there are TWO points of use: staging writes
# them when a workspace is built, and the slot reset rewrites them between designs — `bb.py`
# fills them in as an author builds, so a slot that kept the last design's registry would hand
# the next author the last design's key.  Two copies of a fact drift; one cannot.  (It did: a
# reset that was not updated when the second registry arrived cost 64 of 78 designs on one run,
# because the leak gate then refused every design the slot was handed after the first.)
BLIND_REGISTRY_EMPTY = (
    "import LeanRTL.Core.Syntax\n"
    "/-! # Workspace module registry (AUTO-GENERATED by scripts/bb.py). -/\n"
    "namespace LeanRTL\n\n"
    "def blindRegistry : List (String × Module) := []\n\n"
    "def blindParentRegistry : List (String × Parent) := []\n\n"
    "end LeanRTL\n")

BLIND_PARAM_REGISTRY_EMPTY = (
    "import LeanRTL.Core.ParamBackend\n"
    "/-! # Workspace ParamModule registry (AUTO-GENERATED by scripts/bb.py). -/\n"
    "namespace LeanRTL.Designs.Param\n\n"
    "def paramRegistry : List ParamMeta := []\n\n"
    "def findParamMeta? (key : String) : Option ParamMeta :=\n"
    "  paramRegistry.find? (·.key == key)\n\n"
    "end LeanRTL.Designs.Param\n")

# Framework files that exist in the repository and must NOT reach an author's workspace.  Kept as
# one list because two places consume it — the `copytree` that installs `LeanRTL/Core` and the
# fingerprint — and a workspace whose fingerprint covered a file it does not contain would be
# permanently, silently stale.
#
# `ParamTemplates.lean` is the case the exclusion was built for, and the reason it was split out
# of `ParamBackend.lean`: it holds hand-written PER-DESIGN parametric emitters, and the sanitiser
# redacts design *names* only — never implementations.  An author who opened it would find, under
# a redacted name, a complete answer to a benchmark design: its exact port list, its width
# formulas, its reset polarity.  What ships instead is the GENERIC emitter, which derives all of
# that from the author's own `gen` by fitting and then verifying it.  Keep this a list of file
# NAMES: an `ignore` predicate over contents would be a second, weaker sanitiser, and there is
# already one.
FRAMEWORK_NOT_SHIPPED = ("ParamTemplates.lean",)

SCAFFOLD_FILES = ("lakefile.toml", "Main.lean", "LeanRTL.lean", "dsl-reference.md", "AGENT.md")


def framework_inputs() -> list[str]:
    """Every repository file `install_framework` copies into a workspace, absolute and sorted.

    This is the definition of "the framework a workspace is holding".  It is derived by walking
    the same trees `install_framework` walks rather than listed by hand, so a file added to
    `framework/LeanRTL/Core/` or to `authoring/` is fingerprinted the day it is added.
    """
    paths = [TOOLCHAIN]
    paths += [os.path.join(AUTHORING, "scaffold", n) for n in SCAFFOLD_FILES]
    paths += provenance.walk(os.path.join(ROOT, "framework", "LeanRTL", "Core"),
                             exclude=FRAMEWORK_NOT_SHIPPED)
    paths += [os.path.join(AUTHORING, f) for f in os.listdir(AUTHORING) if f.endswith(".py")]
    return sorted(p for p in paths if os.path.isfile(p))


def framework_fingerprint() -> str:
    """A digest of the framework as it stands in the repository RIGHT NOW.

    Stamped into `provenance.json` at staging time and re-checked before the workspace is used
    again.  The bug this exists to kill: a workspace is re-staged only when its directory is
    ABSENT, so a run repeated after the framework moved keeps the framework it was first staged
    with — while author slots, copied fresh from the warm template, get the new one.  The two
    then disagree, and the disagreement surfaces as the collection workspace failing to elaborate
    designs that built green in the slot they were written in.  A whole 17-design gate column
    once read `0/17 — does not elaborate` for exactly this reason.  A wrong number, not an error.
    """
    return provenance.digest(framework_inputs(), ROOT)


def asset_inputs(profile: dict) -> list[str]:
    """Every repository file `copy_assets` copies into a workspace, absolute and sorted.

    `framework_inputs` one layer out, and it exists because the gap it covers cost a round.  The
    workspace holds a COPY of `assets/` — the instructions, the skill library, the role cards —
    and that copy is what an author actually reads.  A framework-only refresh reinstalls
    `framework/` and `authoring/` and NOTHING ELSE, so a round launched after the instructions
    were rewritten ran authors against the instructions of the day the workspace was staged.
    Measured: the backend half of an async-reset change landed (framework) and the documentation
    half did not (assets), and the round was reported as "the authors did not follow the new
    instructions" when the new instructions were never on disk.
    """
    sets, paths = asset_sets(), []
    for name in profile.get("assets", []):
        for rel in sets.get(name, {}).get("paths", []):
            src = os.path.join(ROOT, "assets", rel.rstrip("/"))
            if os.path.isdir(src):
                paths += provenance.walk(src)
            elif os.path.isfile(src):
                paths.append(src)
    for doc in profile.get("rules", []):
        p = os.path.join(ROOT, "assets", "instructions", doc)
        if os.path.isfile(p):
            paths.append(p)
    return sorted(set(paths))


def assets_fingerprint(profile: dict) -> str:
    return provenance.digest(asset_inputs(profile), ROOT)


def install_framework(ws: str) -> None:
    """Copy in every file `framework_inputs` names — and nothing else.

    Split out of `install_project` so that refreshing a workspace's framework is *the same code*
    as installing it.  A separate "refresh" routine that copied a subset is how a workspace ends
    up half-migrated, which is worse than being wholly stale: wholly stale fails on the first
    import, half-migrated fails somewhere in the middle of a proof.

    Touches nothing an author or a run produced.  `LeanRTL/Blind/`, `notes/`, `out/`, `log/`,
    `frags/`, `scratch/`, `specs/`, `contracts/` and the two auto-generated registries are all
    outside this function by construction, because none of them is in `framework_inputs`.
    """
    # lean-toolchain comes from the repository root (one toolchain, no drift).  lakefile /
    # LeanRTL.lean / Main.lean come from the SCAFFOLD, not the framework: the repository's
    # versions declare four libraries and import an accumulated Lib, neither of which exists in a
    # workspace.  Copying the repository's here is a recorded incident — the build failed on a
    # missing registry and the "fix" was to hand-patch the workspace, which is how workspaces
    # stop being reproducible.
    shutil.copy(TOOLCHAIN, os.path.join(ws, "lean-toolchain"))
    for name in ("lakefile.toml", "Main.lean", "LeanRTL.lean"):
        shutil.copy(os.path.join(AUTHORING, "scaffold", name), os.path.join(ws, name))
    # `dirs_exist_ok` because this runs on refresh as well as on staging.  A file DELETED from the
    # framework therefore survives in a refreshed workspace; that is deliberate and is the safe
    # direction, since a stale extra module is inert unless something imports it, whereas pruning
    # would let this function delete an author's file the day someone puts one under `Core/`.
    shutil.copytree(os.path.join(ROOT, "framework", "LeanRTL", "Core"),
                    os.path.join(ws, "LeanRTL", "Core"), dirs_exist_ok=True,
                    ignore=shutil.ignore_patterns(*FRAMEWORK_NOT_SHIPPED))
    os.makedirs(os.path.join(ws, "scripts"), exist_ok=True)
    for f in sorted(os.listdir(AUTHORING)):
        if f.endswith(".py"):
            shutil.copy(os.path.join(AUTHORING, f), os.path.join(ws, "scripts", f))
    os.makedirs(os.path.join(ws, "docs"), exist_ok=True)
    shutil.copy(os.path.join(AUTHORING, "scaffold", "dsl-reference.md"),
                os.path.join(ws, "docs", "dsl-reference.md"))
    shutil.copy(os.path.join(AUTHORING, "scaffold", "AGENT.md"), os.path.join(ws, "AGENT.md"))


def install_lib(ws: str) -> None:
    """Install the accumulated library and append its imports to the workspace's `LeanRTL.lean`.

    The accumulated library is an ASSET, not framework: install it only when the profile selected
    it, and install the SANITISED copy that already landed under `<ws>/assets/` — copying from
    the repository here would route it around the redaction step entirely.  `assets/lib` is laid
    out as `LeanRTL/Lib/…` so the repository's Lake package can serve it to an editor; the staged
    copy keeps the same shape.

    Split out alongside `install_framework` because the two are coupled through one file:
    `install_framework` restores `LeanRTL.lean` from the pristine scaffold, which drops the
    import block this function appends.  Anything that calls one must call the other, in this
    order.
    """
    src_lib = os.path.join(ws, "assets", "lib", "LeanRTL", "Lib")
    if not os.path.isdir(src_lib):
        return
    shutil.copytree(src_lib, os.path.join(ws, "LeanRTL", "Lib"), dirs_exist_ok=True)
    mods = []
    for r_, _, fs in os.walk(src_lib):
        for f_ in sorted(fs):
            if f_.endswith(".lean"):
                rel = os.path.relpath(os.path.join(r_, f_), src_lib)
                mods.append("LeanRTL.Lib." + os.path.splitext(rel)[0].replace(os.sep, "."))
    mods.sort()
    with open(os.path.join(ws, "LeanRTL.lean"), "a") as fh:
        fh.write("\n-- accumulated library, installed by leanrtl/stage.py from the profile's "
                 "`lib` asset set\n")
        fh.write("\n".join(f"import {m}" for m in mods) + "\n")


def camel_of(key: str) -> str:
    """The Lean module name for a key.

    Split on `-` and `.` as well as `_`.  The result names a MODULE — the file is written as
    `LeanRTL/Blind/<camel>.lean` and closed with `end LeanRTL.Blind.<camel>` — and a hyphen there
    does not survive: `lake` quotes the component as `«Prob000Four-to-one…»` while the `end`
    clause does not, and the module fails to build.  Seven of one benchmark's 45 designs failed
    this way, taking the whole workspace's `lake build` down with them.

    Identical to `authoring/asm_f.py`'s, and must stay identical: the two name the same file, and
    the day they disagree the assembler writes one path and every gate reads another.
    """
    return "".join(p[0].upper() + p[1:] for p in re.split(r"[_\-.]", key) if p)


def install_project(ws: str, profile: dict, key: str, toplevel: str) -> None:
    """The Lean package an author works in.

    The workspace becomes self-contained: `framework/` is copied in as `LeanRTL/Core/`, and
    `authoring/*.py` becomes `<ws>/scripts/`.  Those scripts are the author's ONLY build entry
    point, which is what keeps `lake` and `yosys` invocations attributed and logged.
    """
    install_framework(ws)
    os.makedirs(os.path.join(ws, "LeanRTL", "Blind"), exist_ok=True)
    open(os.path.join(ws, "LeanRTL", "BlindRegistry.lean"), "w").write(BLIND_REGISTRY_EMPTY)
    # The parametric registry, written for EVERY arm and empty here.  `Main.lean` imports it
    # unconditionally, so a workspace whose design has no parameters still needs the file to
    # exist or the CLI does not build.  Writing it always is what keeps the parametric route
    # additive: `bb.py` gates it on the DESIGN declaring a `paramMeta`, not on this file.
    open(os.path.join(ws, "LeanRTL", "BlindParamRegistry.lean"), "w").write(
        BLIND_PARAM_REGISTRY_EMPTY)

    src_roles = os.path.join(ws, "assets", "roles")
    if os.path.isdir(src_roles):
        for f in sorted(os.listdir(src_roles)):
            shutil.copy(os.path.join(src_roles, f), os.path.join(ws, f))

    install_lib(ws)

    if profile["authoring"] == "single":
        # One author writes the design file itself; there is no fragment assembly.  Give it the
        # same header the assembler would have produced, so the arms differ in WHO writes the
        # sections and in nothing else -- same imports, same namespace, same section markers, so
        # the gates read both the same way.
        sys.path.insert(0, os.path.join(ws, "scripts"))
        import importlib
        asm = importlib.import_module("asm_f")
        importlib.reload(asm)
        camel = asm.camel_of(key)
        body = asm.HEADER.format(lib_imports=asm.lib_imports(), key=key, camel=camel)
        open(os.path.join(ws, "LeanRTL", "Blind", camel + ".lean"), "w").write(
            body + SINGLE_SCAFFOLD.format(toplevel=toplevel)
            + f"\nend LeanRTL.Blind.{camel}\n")
    else:
        os.makedirs(os.path.join(ws, "frags", key), exist_ok=True)


# ------------------------------------------------------------------------ the prose

def resolve_spec(a) -> tuple[str, str, str]:
    """`(prose, toplevel, source)` — from `--spec`, or from an installed adapter.

    The toplevel defaults to the key and says so.  That default is right on datasets where the
    module name and the key coincide and silently wrong where they do not, so it is printed
    rather than assumed: a run that emitted the wrong module name would fail at the oracle with
    `compile_fail`, which reads as a hardware error.
    """
    if a.spec:
        p = os.path.abspath(os.path.expanduser(a.spec))
        if not os.path.isfile(p):
            sys.exit(f"stage: no prose specification at {p}")
        return open(p, errors="replace").read(), (a.toplevel or a.key), p
    from common.adapter import load
    ad = load(a.bench)
    d = ad.design_map().get(a.key)
    if d is None:
        sys.exit(f"stage: {a.bench} has no design {a.key!r}")
    return (open(d.spec_path, errors="replace").read(), a.toplevel or d.toplevel, d.spec_path)


def has_work(ws: str) -> list[str]:
    """Traces that somebody has worked in this directory.  `--force` refuses over these."""
    traces = []
    for d, why in (("log", "commands have been run (log/)"),
                   ("notes", "an author's notes exist (notes/)")):
        p = os.path.join(ws, d)
        if os.path.isdir(p) and os.listdir(p):
            traces.append(why)
    fr = os.path.join(ws, "frags")
    if os.path.isdir(fr) and any(os.listdir(os.path.join(fr, k)) for k in os.listdir(fr)
                                 if os.path.isdir(os.path.join(fr, k))):
        traces.append("fragments have been written (frags/)")
    bd = os.path.join(ws, "LeanRTL", "Blind")
    if os.path.isdir(bd):
        for f in os.listdir(bd):
            if f.endswith(".lean") and "REPLACE ME" not in open(
                    os.path.join(bd, f), errors="replace").read():
                traces.append(f"a design file has been authored ({f})")
                break
    return traces


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--profile", required=True)
    ap.add_argument("--key", required=True, help="the design's name; names every file about it")
    src = ap.add_mutually_exclusive_group(required=True)
    src.add_argument("--spec", help="path to the prose specification — original or decided")
    src.add_argument("--bench", help="read the prose from an installed adapter instead")
    ap.add_argument("--toplevel", help="the module name the oracle instantiates "
                                      "(default: the key, or the adapter's)")
    ap.add_argument("--ws")
    # Which arm of the design this workspace is, and so which directory it gets under
    # `data/part2/<bench>/<key>/`.  `launch` passes `original` / `decided` (via `--ws`, since it
    # computes the path itself); a workspace staged by hand is part of no pair, and `solo` says
    # that rather than borrowing an arm name it would then sit beside in a comparison table.
    ap.add_argument("--arm", default="solo",
                    help="the arm this workspace is: names the directory under "
                         "data/part2/<bench>/<key>/  (default: solo)")
    ap.add_argument("--force", action="store_true", help="rebuild an IDLE workspace")
    ap.add_argument("--destroy", action="store_true",
                    help="with --force, delete a workspace that contains work")
    ap.add_argument("--no-build", action="store_true",
                    help="skip the workspace build (faster; leaves it cold)")
    a = ap.parse_args(argv)
    variant.require("staging a workspace")

    profile = profiles.load(a.profile)
    profile.setdefault("authoring", "two-author")
    prose, toplevel, spec_src = resolve_spec(a)
    # `--bench` says which corpus the PROSE came from and is mutually exclusive with `--spec`, so
    # under `--spec` it is None and the directory layer has to be inferred from the key.  Both
    # answers come out of `common/adapter.py`, which is the only thing that knows what a design
    # name is; a second opinion here is how the sanitiser and the leak gate once disagreed.
    bench = a.bench or adapter.bench_for_key(a.key)
    ws = os.path.abspath(os.path.expanduser(
        a.ws or paths.ws2(bench, a.key, a.arm)))

    if os.path.exists(ws):
        if not a.force:
            sys.exit(f"stage: {ws} exists (pass --force to rebuild)")
        # `--force` deletes the workspace.  Refuse when there is work in it: `rmtree` has run
        # under two agents that were writing into one, and their output went with it.  `--force`
        # alone should mean "rebuild a workspace I have finished with", never "destroy whatever
        # is in flight".
        traces = has_work(ws)
        if traces and not a.destroy:
            sys.exit(f"stage: {ws} contains work — " + "; ".join(traces) + ".\n"
                     f"  --force rebuilds an idle workspace.  To delete work, pass --destroy as "
                     f"well, and make sure nothing is running in it: an agent writing here will "
                     f"lose everything and will not be told why.")
        shutil.rmtree(ws)

    for d in ("specs", "contracts", "notes", "out", "log", "scratch", "frags", "given",
              "assets", "simdiff", "emits", "snapshot"):
        os.makedirs(os.path.join(ws, d), exist_ok=True)

    # The prose, and only the prose.  Written under the key's own name so the isolation scan can
    # exempt this one file by path (`common/workspace.isolation`) — a design's own specification
    # legitimately says "synchronizer" when that is what it is about, and redacting a common
    # hardware noun out of the one file the author is supposed to read would corrupt the task.
    with open(os.path.join(ws, "specs", f"{a.key}.spec.txt"), "w") as f:
        f.write(prose)

    copied = copy_assets(profile, ws)
    if profile["authoring"] != "direct-verilog":
        install_project(ws, profile, a.key, toplevel)

    # Sanitise LAST, after every tree it scans exists.  This call used to sit above the project
    # install, and `SANITIZE_ROOTS` was widened to catch leaks that its comment names one by one
    # — while three of those four roots were still EMPTY at this point in staging.  The widening
    # was inert and the scan reported a clean tree because it was pointed at nothing.  Verified:
    # a staged workspace's `scripts/simlib.py` named three designs and `scripts/cosim.py` named a
    # fourth and quoted its prose's reset polarity, past a report claiming 47 files redacted.
    # Anything installed after this line is unsanitised by construction.
    from common.adapter import all_design_keys
    all_keys, key_sources = all_design_keys()
    # This design's own name is not redacted out of its own workspace.  It is in `specs/`, in the
    # module name, in the registry — an author is told which design it is writing, and a
    # sanitiser that elided it would produce a workspace that cannot build.
    others = {k for k in all_keys if k != a.key}
    rep = sanitize(ws, others)
    rep.update(profile=profile["name"], key=a.key, assets=copied, key_sources=key_sources,
               own_key_exempt=a.key)
    json.dump(rep, open(os.path.join(ws, "sanitize_report.json"), "w"), indent=1)

    if profile["authoring"] != "direct-verilog" and not a.no_build:
        # Hand over a WARM workspace.  `bb.py build` runs `lake env lean`, which does not build
        # dependencies, so on a cold workspace the author's FIRST command -- the one its role
        # card tells it to run -- fails on unresolved `import LeanRTL.Core.*`.
        print("  building the workspace library (once, ~30s) …", flush=True)
        b = subprocess.run([LAKE, "build"], cwd=ws, capture_output=True, text=True, timeout=3600)
        if b.returncode != 0:
            sys.exit("stage: the staged workspace does not build — refusing to hand it to an "
                     "author\n" + (b.stdout + b.stderr)[-1500:])

    # Stamped LAST, after the build has confirmed the framework compiles here.  Stamping before
    # it means a staging run that dies half-way leaves the workspace claiming to hold the new
    # framework while holding a mixture — and the next launch, reading a fingerprint that
    # matches, would skip the re-stage that would have repaired it.  A crashed stage must look
    # stale.
    provenance.stamp(ws,
                     profile=profile["name"], profile_sha=profile["_sha"],
                     key=a.key, toplevel=toplevel,
                     spec_source=spec_src,
                     spec_sha=provenance.sha256(prose),
                     bench=a.bench,
                     framework=framework_fingerprint(),
                     assets_digest=assets_fingerprint(profile),
                     authoring=profile["authoring"], assets=profile.get("assets", []))

    # Its own git repository, history starting from empty, so a deleted asset cannot be recovered
    # with `git show`.
    subprocess.run(["git", "init", "-q"], cwd=ws)

    print(f"stage: {ws}")
    print(f"  profile={profile['name']}  authoring={profile['authoring']}  "
          f"assets={profile.get('assets') or 'none (bare)'}")
    print(f"  design={a.key}  toplevel={toplevel}"
          + ("" if (a.toplevel or a.bench) else "  (defaulted to the key — check the prose)"))
    print(f"  prose from {spec_src} ({len(prose)} bytes, sha {provenance.sha256(prose)})")
    print(f"  asset paths copied: {len(copied)}")
    print(f"  sanitised against {len(others)} other key(s) from [{', '.join(key_sources) or '—'}]"
          f": {len(rep['redacted'])} file(s) redacted, {len(rep['residual'])} residual mention(s)")
    if not others:
        print("  NOTE: no benchmark is installed, so no other design name could be redacted. "
              "That is not the same as a clean workspace — nothing was checked.")
    if rep["residual"]:
        print("  NOTE: residual mentions are recorded in sanitize_report.json — review before "
              "quoting this run's numbers")
    return 0


if __name__ == "__main__":
    sys.exit(main())
