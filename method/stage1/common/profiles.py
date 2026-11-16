#!/usr/bin/env python3
"""Profiles: the run's configuration, in a file, named.

A profile answers "what is this run?" — who authors, what they are given, which gates decide
whether the result counts. It is the whole of the run's configuration that is not the design.

## Why the configuration is a file and not a flag set

Flags live in shell history. A run configured by flags cannot be re-run except by whoever
still has the terminal it was launched from, and cannot be *compared* to another run at all,
because there is nothing to diff. Every claim of the form "arm A beats arm B" is a claim about
two profiles, and if the profiles are not on disk the claim is unfalsifiable.

## Why a profile is never edited

`stamp` writes the profile's name and its content hash into the workspace, and `require`
refuses a workspace whose stamp contradicts the profile it is being run under. That refusal is
the point. Editing a profile in place leaves every artifact of the previous round stamped with
a name that has come to mean something else — a silent change to the meaning of data already
collected. A new arm is a new file.

## What is deliberately NOT here

No arm table, no lane list, no per-round map. The tree this method comes from had ~40 profiles
and a launcher holding a hard-coded `ARMS` dict alongside them, so the launcher had to be
edited to add an arm and the two lists drifted. Here the launcher takes `--profile <name>` and
the set of arms is exactly the set of files in `profiles/`.
"""
from __future__ import annotations

import hashlib
import json
import os
import sys

from . import paths
ROOT = paths.STAGE2
DIR = os.environ.get("LEANSILICON_PROFILES", os.path.join(ROOT, "profiles"))

# Fields every profile must carry.  Checked on load rather than at the point of use, so a typo
# in a gate name is an error at launch and not a gate that silently never ran.  A profile that
# declares a gate nothing enforces is a claim in a config file that a reader will believe.
REQUIRED = ("name", "description")


def path(name: str) -> str:
    return os.path.join(DIR, f"{name}.yaml")


def available() -> list[str]:
    if not os.path.isdir(DIR):
        return []
    return sorted(f[:-5] for f in os.listdir(DIR) if f.endswith(".yaml")
                  and not f.startswith("_"))


def load(name: str) -> dict:
    """The profile, plus `_sha` and `_path`.

    `_sha` is of the bytes on disk, not of the parsed object: a comment in a profile is part of
    the argument for why the arm is what it is, and a run that carries a hash blind to comments
    would report two arms as identical when one had been re-justified.
    """
    import yaml
    p = path(name)
    if not os.path.isfile(p):
        have = ", ".join(available()) or "none"
        sys.exit(f"profile: no such profile {name!r} in {DIR} (have: {have})")
    raw = open(p, "rb").read()
    prof = yaml.safe_load(raw.decode()) or {}
    missing = [k for k in REQUIRED if not prof.get(k)]
    if missing:
        sys.exit(f"profile {name!r}: missing required field(s) {', '.join(missing)}")
    if prof["name"] != name:
        # The name inside the file is what gets stamped into workspaces and printed in reports.
        # A file whose internal name disagrees with its filename means one of the two is what a
        # reader will cite, and there is no way to tell which.
        sys.exit(f"profile {name!r}: declares name {prof['name']!r} — the file name and the "
                 f"`name:` field must agree, because both are cited as the arm's identity")
    prof["_sha"] = hashlib.sha256(raw).hexdigest()[:12]
    prof["_path"] = p
    return prof


def gates(prof: dict) -> dict:
    return prof.get("gates", {}) or {}


def summary(prof: dict) -> str:
    g = [k for k, v in gates(prof).items() if v]
    return (f"{prof['name']} ({prof['_sha']}): {prof.get('authoring', '?')} authoring, "
            f"assets {'+'.join(prof.get('assets') or []) or '—'}, "
            f"gates {' '.join(sorted(g)) or '—'}")


if __name__ == "__main__":
    if len(sys.argv) > 1:
        print(json.dumps(load(sys.argv[1]), indent=1, sort_keys=True))
    else:
        for n in available():
            print(summary(load(n)))
