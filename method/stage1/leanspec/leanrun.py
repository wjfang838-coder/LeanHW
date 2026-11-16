#!/usr/bin/env python3
"""Running Lean against leanSpec's own library.

`common/leanrun.py` knows how to start Lean and how to read what it said; it deliberately knows
nothing about which library, which prelude or which finding vocabulary.  This is where leanSpec
supplies those, once, so that no step body has to.

The prelude is the `LeanSpec` library as `lake` built it.  Built by `lake` rather than compiled
here by hand because `LeanSpec` is three modules with an import graph, and hand-rolling oleans
for a dependency graph is a build system.  What this adds is the refusal: a run that would use a
prelude nobody has built is stopped with a sentence saying which command builds it, rather than
failing several frames later on `unknown package 'LeanSpec'`.

`import LeanSpec` and nothing else.  No Mathlib, no Std beyond the core, and — the point of the
whole arrangement — no `LeanRTL`.  A case's generated file that reached for the implementation
half's DSL would be deriving a specification's meaning from an implementation, which is the one
direction this method exists to rule out.
"""
from __future__ import annotations

import os
import re

from common import leanrun as _leanrun, paths

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = paths.STAGE1
LEAN_DIR = os.path.join(HERE, "lean")
# `.lake/` is at the REPOSITORY root, not the method root: the lakefile has to sit at the top
# of the tree so an editor opening the repository gets one package rather than a thousand red
# files, and Lake puts its build tree beside its lakefile.
BUILD = os.path.join(paths.REPO, ".lake", "build", "lib", "lean")

PREFIX = "LEANSPEC:"

summarize = _leanrun.summarize
why_failed = _leanrun.why_failed


def prelude() -> str:
    """The directory holding `LeanSpec.olean`, or a refusal naming the command that makes it."""
    if not os.path.isfile(os.path.join(BUILD, "LeanSpec.olean")):
        raise RuntimeError(
            f"{os.path.relpath(BUILD, paths.REPO)}/LeanSpec.olean does not exist, so nothing here "
            f"can `import LeanSpec`.  Run `lake build LeanSpec` at {paths.REPO} first.")
    return BUILD


def run(path: str, cwd: str | None = None, timeout: int | None = None,
        emit_olean: bool = False) -> dict:
    """Elaborate one file against the LeanSpec prelude and its own working directory."""
    return _leanrun.run(path, cwd=cwd, lean_path=[prelude()], timeout=timeout,
                        emit_olean=emit_olean, prefix=PREFIX)


# The library's sources, in dependency order.  `LeanSpec.lean` itself is only imports and a
# docstring, so it is not in the list — splicing it into a standalone file would splice in
# `import LeanSpec.Core`, which is the line the standalone exists to remove.
MODULES = ("LeanSpec/Core.lean", "LeanSpec/Property.lean")


def library_source() -> str:
    """The whole `LeanSpec` library as one string, for the standalone deliverable.

    A standalone file is a file someone else can check without this repository: one `lean`
    invocation, no `LEAN_PATH`, no build tree.  That only works if the library travels with it,
    which means concatenating it — and it is worth being explicit that the concatenation is
    *evidence*, not the thing that runs.  What the pipeline elaborates is the modular version
    against the built prelude; the standalone is emitted beside it and checked, so a divergence
    between the two is caught here rather than by the reader who trusted it.
    """
    out = []
    for rel in MODULES:
        with open(os.path.join(LEAN_DIR, rel), errors="replace") as f:
            src = f.read()
        # `import LeanSpec.Core` is exactly what a standalone file must not contain, and it is
        # dropped here rather than by the emitter's own stripper: that one matches `import \w+`
        # and a dotted module name is not `\w+`, so a line left for it to remove would survive
        # into the deliverable and break the one property the deliverable has.
        out.append(re.sub(r"(?m)^\s*import\s+[\w.]+\s*$\n?", "", src).rstrip())
    return "\n\n".join(out) + "\n"
