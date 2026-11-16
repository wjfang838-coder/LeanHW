#!/usr/bin/env python3
"""An append-only event log, one per run.

Two properties, and they are the whole point:

  * **Append-only.**  Opened `"a"`, one JSON object per line, flushed and `fsync`ed.  Nothing
    here rewrites a row.  A record that can be edited answers "what does this run claim
    happened", and the question worth answering is "what happened".

  * **Ordered under concurrency.**  Several designs run in parallel against one ledger, so the
    write takes an exclusive `flock` for the duration of the line.  Without it, two 4 KB writes
    interleave and the file has a corrupt row in the middle — which is discovered later, by the
    audit that was supposed to be reading it.

`ts` is wall-clock and is what the ordering audit reads: the seal says a stage could not have
looked, and the ledger says in what order things actually happened.  They answer different
questions and both are wanted.
"""
from __future__ import annotations

import datetime
import fcntl
import json
import os

NAME = "ledger.jsonl"


def path(root: str) -> str:
    return os.path.join(root, "logs", NAME)


def log(root: str, event: str, **fields) -> dict:
    """Append one event.  Returns the row, so a caller can put it in a step document."""
    row = {"ts": datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
           "event": event, **fields}
    p = path(root)
    os.makedirs(os.path.dirname(p), exist_ok=True)
    line = json.dumps(row, sort_keys=True, default=str) + "\n"
    with open(p, "a") as f:
        fcntl.flock(f.fileno(), fcntl.LOCK_EX)
        try:
            f.write(line)
            f.flush()
            os.fsync(f.fileno())
        finally:
            fcntl.flock(f.fileno(), fcntl.LOCK_UN)
    return row


def read(root: str) -> list[dict]:
    """Every row, in order.  Unparseable lines come back as `{"event": "corrupt", ...}` rather
    than being skipped: a hole in an append-only log is a finding about the log."""
    p = path(root)
    if not os.path.isfile(p):
        return []
    out = []
    for i, line in enumerate(open(p, errors="replace"), 1):
        line = line.strip()
        if not line:
            continue
        try:
            out.append(json.loads(line))
        except ValueError as e:                                          # noqa: BLE001
            out.append({"event": "corrupt", "line": i, "raw": line[:400], "why": str(e)})
    return out


def events(root: str, name: str) -> list[dict]:
    return [r for r in read(root) if r.get("event") == name]
