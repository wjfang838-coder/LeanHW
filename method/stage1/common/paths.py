#!/usr/bin/env python3
"""Where the method is, and where the runs go.

Until the tree was reorganised these were one directory and so one constant: every module
computed `ROOT` two `dirname`s up from itself, and `ROOT` meant both "the code" and "the
place results land".  That conflation is what this module exists to end.

  * `METHOD` is the code — `framework/`, `assets/`, `audit/`, `profiles/`, the two halves.
    It is versioned, it is small, and a run only ever *reads* from it.

  * `DATA` is what runs produce — both halves' runs, evidence, the top-level ledger.  It is
    gitignored, it is gigabytes, and nothing under `METHOD` should ever be written by a run.

Keeping the two apart is not tidiness.  A results directory *inside* the method directory is a
tree where "what did we do" and "what happened when we did it" have the same parent, and the
first audit that walks the method to hash it walks a moving target.  `provenance.walk` hashes
`framework/` — if a run wrote into that subtree, every later run would be staged against a
different framework than the one before it, and the stamp that is supposed to catch exactly
that would be computing the drift rather than reporting it.

Both are overridable by environment, because the alternative to an override is a copy of the
tree, and a copy of the method is a second method that nobody remembers to update.
"""
from __future__ import annotations

import os

HERE = os.path.dirname(os.path.abspath(__file__))

#: The method tree: `method/`.  Read-only as far as a run is concerned.
STAGE1 = os.path.dirname(HERE)
CODEBASE = os.path.dirname(STAGE1)
STAGE2 = os.path.join(CODEBASE, "stage2")
# Legacy resource-root API used by the Stage 2 stager.
METHOD = STAGE2

#: The repository root.  Holds `lakefile.toml` — Lake needs a package at the top of the tree,
#: not one buried a level down, so this is the directory `lake build` runs in.
REPO = os.path.dirname(CODEBASE)

#: Everything a run produces.  `part1/ part2/ runs/ logs/` live here and nowhere else.
DATA = os.path.abspath(os.environ.get("LEANSILICON_DATA", os.path.join(REPO, "data")))

#: Design corpora.  Outside the repository by default is the point, not a convenience — see
#: `common/adapter.py`, which is the only thing that should be reading it.
BENCH = os.path.abspath(os.environ.get("LEANSILICON_BENCH", os.path.join(REPO, "benchmarks")))

# ------------------------------------------------------------------ where each half's runs land
#
# `data/part<N>/<bench>/<key>/<run>`.  Layers, and each earns its place.
#
# The FIRST layer is the half.  These directories were `cases/` and `workspaces/` — two different
# nouns for the same thing, one run of one half, and nothing in either name said which half or
# which came first.  Reading the tree required already knowing that `leanspec` writes cases and
# `leanrtl` writes workspaces.  The module names stay as they are; the directories say `part1`
# and `part2` so the order is legible from the filesystem alone.
#
# The SECOND layer is the benchmark.  Without it, `accu` from one corpus and `accu` from another
# collide on one directory name, and the loser is whichever ran second.  Design keys are chosen
# by dataset authors who never coordinated, and `adapter.all_design_keys()` already merges fifty
# of them from every installed benchmark into one namespace for the leak gate to scan — that
# merge is safe because it is a *set of names to redact*.  A directory is not.
#
# The THIRD is the design key, with the run inside it — `case1` and `ws2` below.  It was flat, and
# a flat layer put one design's runs in sort order among unrelated designs: eight directories in a
# row under `rtllm/`, two of them results and six of them not, distinguishable only by suffixes a
# reader had to already know.  Grouping them means the question "what happened to this design"
# is answered by one `ls`, and `bak/` can hold the answer to "and what else did we try".
PART1 = "part1"
PART2 = "part2"

#: Prose that came from a file rather than an installed benchmark still needs a home.  Named
#: rather than left blank so that `data/part1//accu` never appears: an empty path component
#: collapses silently on `os.path.join` and puts the run one level up, where it sits beside the
#: benchmark directories looking like one of them.
LOCAL = "local"


def part1(bench: str = "", *parts: str) -> str:
    """A path under `data/part1/<bench>/` — one leanSpec run and everything it produced."""
    return data(PART1, bench or LOCAL, *parts)


def part2(bench: str = "", *parts: str) -> str:
    """A path under `data/part2/<bench>/` — one leanRTL workspace."""
    return data(PART2, bench or LOCAL, *parts)


#: Everything under a design that is not a reported result.  Dead ends, crashed stages, runs that
#: never produced an `out/`, hand-renamed copies, a workspace whose assets were never redacted —
#: kept, because deleting the record of how a result was reached is how a result stops being
#: checkable, but kept somewhere a reader cannot mistake for the result.
#:
#: A directory rather than a naming convention, on purpose.  On the Part 2 side it used to be a
#: suffix list (`.abandoned`, `.crashed-stage`, `.killed`, `.unsanitised`) that `compare.discover`
#: matched against, which meant every consumer had to know the vocabulary and a suffix nobody had
#: thought of yet was included by default — `.unsanitised` DID emit Verilog, so only its name kept
#: it out of a table read as if every row had been staged the same way.  A directory inverts the
#: default: a run is reported only if somebody put it beside the others.
#:
#: The two halves reach that conclusion differently, and both are right.  Part 2 has no registry,
#: so `compare.discover` walks the tree and skips this name.  Part 1 does have one, so the flag
#: lives in `CASES.json` and `cases.archive()` moves the directory and sets it together — a case
#: whose registry entry and location disagree is a case `find()` cannot open.
BAK = "bak"

#: The label for a case whose name carries no suffix.  `data/part1/rtllm/accu/base/` rather than
#: `data/part1/rtllm/accu/` holding both a run and its siblings' directories, which would make
#: `accu/` simultaneously a run and a container and give `ls` no way to say which.
BASE = "base"


def case1(bench: str, key: str, label: str, *parts: str, bak: bool = False) -> str:
    """One leanSpec case: `data/part1/<bench>/<key>/<label>/`, or under `<key>/bak/` if archived.

    The design key is the directory and the run label sits inside it, matching `ws2` on the other
    half.  Case NAMES keep their dotted form — `accu.c5` is the identity recorded in all 173 of
    that run's ledger lines, in `CASES.json`, and in every step document — and only the layout
    changed; `cases.Case.dir` splits the name on the first dot to place it.  Renaming the cases to
    match the directories would have edited the past to tidy the present.
    """
    head = (key, BAK, label) if bak else (key, label)
    return part1(bench, *head, *parts)


def ws2(bench: str, key: str, arm: str) -> str:
    """One leanRTL workspace: `data/part2/<bench>/<key>/<arm>/`.

    The only spelling of this path.  It is computed in three places that must agree — `stage.main`
    builds it, `launch.stage_arm` builds it, and `launch.original_arm_ran` looks for the sibling —
    and the last one returning the wrong path is indistinguishable from "the original arm never
    ran", so a paired run would silently stage a third workspace beside the two already on disk.

    The design key is the directory and the arm sits inside it, because the arms of one design are
    the thing being compared and a flat layer scattered them into sort order among unrelated
    designs.  The profile is NOT in the path: `data/` holds one method by construction now that a
    baseline is a separate tree, and `launch.already_staged` compares `(key, profile, arm)`
    against the run record, so a profile change at this path is caught as a different run rather
    than quietly reusing the first one's directory.
    """
    return part2(bench, key, arm)


def data(*parts: str) -> str:
    """A path under `DATA`.  Creates nothing: the caller that writes there makes it."""
    return os.path.join(DATA, *parts)


def method(*parts: str) -> str:
    """A path under `METHOD` — assets, framework sources, audit scripts."""
    root = STAGE1 if parts and parts[0] in ("common", "leanspec") else STAGE2
    return os.path.join(root, *parts)
