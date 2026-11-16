#!/usr/bin/env python3
"""What a working directory is holding, written down where the work happens.

A run produces artifacts, and an artifact is a result *of something*: of a framework, of a set
of instructions, of one reading of one prose file.  When that something is not recorded beside
the artifact, the artifact silently becomes a measurement of whatever happens to be on disk the
next time anybody looks.

Two failures make the case, and both are recorded in the tree this method comes from.

  * A workspace is re-staged only when its directory is **absent**, so an arm re-run after the
    framework moved kept the framework it was first staged with — while the author slots, copied
    fresh from the template, got the new one.  Seventeen designs then failed to elaborate in the
    collection workspace on `Unknown constant`, having built and emitted cleanly in the slots
    they were written in.  The column read `0/17`.  That is not a proof result; it is a
    measurement of the wrong tree, and nothing on disk said the two disagreed.

  * The same shape one layer out.  A refresh that reinstalled the framework and nothing else ran
    authors against the *previous* round's instructions, and the round was reported as "the
    authors did not follow the new instructions" when the new instructions were never on disk.

So: a stamp, and a comparison against it before the directory is used again.

**Content-addressed, not mtime-based.**  `cp -a` preserves timestamps, so mtimes compare equal
across a copy of a genuinely different tree, and `git checkout` moves mtimes on files whose
content did not change.  Path names are hashed alongside content, so adding or removing a file
moves the digest even when no surviving file changed.

**Generic on purpose.**  This module does not know what a framework is or what an asset is.  It
hashes a list of files and reads and writes a JSON object; each half of leanSilicon supplies its
own list and its own field names.  The alternative — one module that knows both halves' layouts
— is a dependency between two halves that are supposed to be decoupled.
"""
from __future__ import annotations

import hashlib
import json
import os

NAME = "provenance.json"


class Mismatch(RuntimeError):
    """A directory is stamped as holding something other than what it is about to be used as."""


def sha256(s: str | bytes) -> str:
    """The content identity of one blob, twelve hex characters.

    Here rather than in each caller because a hash written into a step document, a hash written
    onto a ledger row and a hash a later step compares against have to be the same function.  Two
    spellings of "the sha of this file" is how a chain that looks verified stops being one.
    """
    return hashlib.sha256(s.encode() if isinstance(s, str) else s).hexdigest()[:12]


def digest(paths: list[str], base: str) -> str:
    """A content digest of `paths`, with their names relative to `base` hashed in.

    Sixteen hex characters.  This is an identity, not a security boundary: it exists so that two
    trees which differ compare unequal, and truncating keeps it readable in a log line.
    """
    h = hashlib.sha256()
    for p in sorted(paths):
        h.update(os.path.relpath(p, base).encode())
        h.update(b"\0")
        with open(p, "rb") as f:
            h.update(f.read())
        h.update(b"\0")
    return h.hexdigest()[:16]


def walk(*roots: str, skip: tuple[str, ...] = (".lake", ".git", "__pycache__"),
         exclude: tuple[str, ...] = ()) -> list[str]:
    """Every file under `roots`, sorted.  Files whose basename is in `exclude` are left out.

    `exclude` is for files that exist in the repository and deliberately do **not** ship into a
    workspace.  Fingerprinting a file the workspace does not contain makes the workspace
    permanently, silently stale, so the list of what is copied and the list of what is hashed
    have to be the same list — which is why callers derive both from one call to this.
    """
    out = []
    for r in roots:
        if os.path.isfile(r):
            if os.path.basename(r) not in exclude:
                out.append(os.path.abspath(r))
            continue
        for dirpath, dirs, files in os.walk(r):
            dirs[:] = [d for d in dirs if d not in skip]
            out.extend(os.path.join(dirpath, f) for f in files if f not in exclude)
    return sorted(set(out))


def path(ws: str) -> str:
    return os.path.join(ws, NAME)


def stamp(ws: str, **fields) -> dict:
    """Write the stamp.  Returns what was written."""
    os.makedirs(ws, exist_ok=True)
    with open(path(ws), "w") as f:
        json.dump(fields, f, indent=1, sort_keys=True, default=str)
    return fields


def read(ws: str) -> dict:
    """The stamp, or `{}` when absent or unreadable.

    Never raises.  A missing stamp means "unknown", and the callers distinguish the two cases
    themselves: `stale` treats unknown as stale (the conservative reading), while a ledger row
    recording which framework a run used should record that it did not know rather than refuse
    over a field nothing depends on.
    """
    try:
        with open(path(ws)) as f:
            v = json.load(f)
        return v if isinstance(v, dict) else {}
    except (OSError, ValueError):
        return {}


def stale(ws: str, want: dict) -> dict:
    """Which stamped fields disagree with `want`, as `field -> (have, want)`.

    An absent field counts as disagreeing.  A workspace staged before a field existed carries no
    opinion about it, and treating silence as agreement is how a stale tree passes a freshness
    check — the whole point of which is to catch the tree nobody remembered to update.
    """
    have = read(ws)
    return {k: (have.get(k), v) for k, v in want.items() if have.get(k) != v}


def require(ws: str, want: dict, why: str = "") -> None:
    """Refuse to proceed when the stamp and the intended use disagree.

    Raising rather than refreshing, because this module cannot know how to build the thing that
    is wrong.  The caller that knows how to re-stage catches this and re-stages; the caller that
    only wants to *score* a directory has no business quietly rewriting it, and for that caller
    stopping is the correct outcome.
    """
    bad = stale(ws, want)
    if not bad:
        return
    lines = [f"  {k}: holds {have or 'nothing'}, this run needs {w}" for k, (have, w) in
             sorted(bad.items())]
    raise Mismatch(
        f"{ws} is stamped as something else than what it is about to be used as"
        + (f" ({why})" if why else "") + ":\n" + "\n".join(lines)
        + "\nA directory used under a stamp it does not carry produces artifacts that are "
          "results of a tree nobody can name afterwards.")
