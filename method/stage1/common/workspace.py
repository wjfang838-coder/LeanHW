#!/usr/bin/env python3
"""Slots: a working directory that holds exactly one design.

An author is told it is alone with one specification.  That sentence is either true of the
directory it opens or it is a claim about the author's discipline, and the whole point of this
method is that it is the former.  So a slot holds **one** design, and everything about the last
one is gone before the next one arrives.

Four things here, each of which exists because its absence cost a round in the tree this method
comes from:

  * **`make` copies from a warm template.**  Staging from scratch ends in a `lake build` — two
    minutes of compiling the same library to byte-identical output.  Fifty of those is two hours
    of rebuilding the same thing.

  * **`reset` sweeps against the template's own listing**, not against a list of names to
    delete.  A list of names is a list of the strays somebody thought of.  `.bb_out.txt` was not
    on one: an author redirected a build command into it, the file survived the reset at the slot
    root, and the leak gate then refused 22 designs for naming the design that had been in that
    slot before them.  The gate was right and the reset was incomplete.

  * **`squatters` runs before the slots are made.**  `rmtree` unlinks a directory; it does not
    stop anything inside it.  A killed sweep leaves its agent children running, reparented to
    init, each holding its workspace as an absolute path — so recreating the slot puts a new
    design underneath a survivor that is still writing the old one's files.

  * **`isolation` scans in Python, not with grep**, because the boundary rule matters more than
    the speed.  `_` and `-` are word characters, so a `\\b`-anchored search does not see
    `right_shifter` inside `rightshifter_reads` — which is exactly how one design's whole-trace
    theorem sat in a shared document past a sanitiser reporting 47 files redacted.

Nothing here knows what a design *is*.  A slot is a directory, a key is a string, and the caller
supplies the template and the other keys.  Both halves of leanSilicon can use it and neither has
to tell the other that it did.
"""
from __future__ import annotations

import os
import re
import shutil
import subprocess

# Per-design state, recreated empty on every reset.  Recreating a directory cannot leave a file
# behind; blanking what you remember can, and did — a previous clone left a complete solution in
# `scratch/` in a workspace it reported clean.
DESIGN_DIRS = ("specs", "contracts", "notes", "out", "log", "scratch", "frags", "given",
               "snapshot", "emits", "simdiff")


def slot_path(pool: str, name: str) -> str:
    return os.path.join(pool, name)


def make(pool: str, name: str, template: str) -> str:
    """One slot, copied from the warm template.  Any previous slot of that name is removed."""
    slot = slot_path(pool, name)
    os.makedirs(pool, exist_ok=True)
    if os.path.isdir(slot):
        shutil.rmtree(slot)
    subprocess.run(["cp", "-a", template, slot], check=True)
    return slot


def reset(slot: str, template: str, dirs: tuple[str, ...] = DESIGN_DIRS) -> None:
    """Remove every trace of the last design from a slot, leaving the template's tree behind.

    Two passes, because they cover different ground.  The first recreates the per-design
    directories, which cannot leave a file behind *inside them*.  The second sweeps the slot
    ROOT, which the first cannot reach and where an author writes whatever it likes: whatever the
    template does not have is this design's or the last one's, and neither belongs to an author
    about to be told it is alone with one design.
    """
    for d in dirs:
        p = os.path.join(slot, d)
        shutil.rmtree(p, ignore_errors=True)
        os.makedirs(p)

    keep = set(os.listdir(template)) if os.path.isdir(template) else set()
    keep |= set(dirs) | {"provenance.json", "manifest.json"}
    for name in os.listdir(slot):
        if name in keep:
            continue
        p = os.path.join(slot, name)
        try:
            if os.path.isdir(p) and not os.path.islink(p):
                shutil.rmtree(p, ignore_errors=True)
            else:
                os.remove(p)
        except OSError:
            pass


def squatters(slots: list[str]) -> list[tuple[int, str, str]]:
    """Processes still holding any of `slots`, from a run that is already over.

    Detected by `/proc/<pid>/cwd` **and** by the command line, because either alone misses a
    case: a survivor whose directory was already unlinked reports `<path> (deleted)` and would
    slip a plain string match, and a process that has chdir'd elsewhere still holds the absolute
    path it was told to write to.

    Linux-only.  A platform without `/proc` gets an empty list rather than an error — a check
    that cannot run is not a licence to refuse a launch, and saying so here is better than a
    caller inferring "clean" from a crash it caught.
    """
    found: list[tuple[int, str, str]] = []
    if not os.path.isdir("/proc"):
        return found
    want = {os.path.abspath(s) for s in slots}
    me = os.getpid()
    for ent in os.listdir("/proc"):
        if not ent.isdigit() or int(ent) == me:
            continue
        try:
            cwd = os.readlink(f"/proc/{ent}/cwd")
            with open(f"/proc/{ent}/cmdline", "rb") as f:
                cmd = f.read().decode("utf-8", "replace")
        except OSError:
            continue                     # gone, or another user's — neither is ours to report
        cwd = cwd[:-len(" (deleted)")] if cwd.endswith(" (deleted)") else cwd
        for full in sorted(want):
            if cwd == full or full in cmd:
                found.append((int(ent), full, cmd[:160].replace("\x00", " ")))
                break
    return found


def _spellings(key: str) -> set[str]:
    """The forms one key is actually written in: raw, camel, squashed, hyphenated."""
    return {key,
            "".join(w[:1].upper() + w[1:] for w in re.split(r"[_\-]", key)),
            key.replace("_", ""),
            key.replace("_", "-")}


def isolation(slot: str, key: str, other_keys: set[str],
              own_prefix: str = "specs") -> tuple[list[str], dict]:
    """No design but this one may be nameable inside the slot an author is about to open.

    Boundaries are alphanumeric, so an underscore ends a name the way a space does.  Keys of five
    characters or fewer (`pe`, `alu`, `fsm`, `RAM`, `accu`) are ordinary English and are matched
    only in their code-quoted form; scanning them as bare words reports every occurrence of
    "type" and "value" and trains the reader to ignore the gate.

    The design's OWN specification is exempt, and only its own.  An asynchronous FIFO's prose says
    "synchronizer", which is another design's key, because that is what such prose talks about.
    That file is the one thing the author is supposed to read, and redacting a common hardware
    noun out of it would corrupt the task being measured.  Any OTHER file under `specs/` is still
    reported: one specification per slot is the invariant, and a second one appearing there is
    the failure this gate exists to catch.

    Alphanumeric boundaries are also what lets one key be found inside another.
    `binary_to_one_hot_decoder` and `binary_to_one_hot_decoder_sequential` are both real keys, so
    the slot staged for the second contains its own name in its own manifest, its own provenance
    and its own module, and every one of those reads as a mention of the first — the gate refused
    the design for being itself.  So this design's own name is masked out, in all four spellings,
    before any other key is probed for.  That is not a weakening: an occurrence that exists only
    as a substring of THIS key is not a reference to another design.  The masked span becomes
    NULs of the same length so that no two neighbours are joined into a name that was never
    there.

    Returns the hits AND how much was looked at.  A ledger row that records only failures cannot
    distinguish "the gate ran and found nothing" from "the gate did not run"; the counts go on
    the row so the row itself is the evidence.
    """
    own = os.path.join(own_prefix, key + ".")
    own_pats = [re.compile(re.escape(v))
                for v in sorted(_spellings(key), key=len, reverse=True)]
    pats = []
    for k in sorted(other_keys):
        for v in _spellings(k):
            pats.append((k, re.compile(re.escape(f"`{v}`") if len(v) <= 5 else
                                       rf"(?<![A-Za-z0-9]){re.escape(v)}(?![A-Za-z0-9])")))
    hits, n_files = [], 0
    for root, dirs, files in os.walk(slot):
        dirs[:] = [d for d in dirs if d not in (".lake", ".git", "__pycache__")]
        for fn in files:
            p = os.path.join(root, fn)
            if os.path.relpath(p, slot).startswith(own):
                continue
            try:
                with open(p, errors="replace") as f:
                    text = f.read()
            except OSError:
                continue
            n_files += 1
            for op in own_pats:
                text = op.sub(lambda m: "\0" * len(m.group(0)), text)
            named = sorted({k for k, pat in pats if pat.search(text)})
            if named:
                hits.append(f"{os.path.relpath(p, slot)}: {', '.join(named[:5])}")
    return hits, {"keys_probed": len(other_keys), "patterns": len(pats), "files": n_files}
