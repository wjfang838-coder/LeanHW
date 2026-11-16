#!/usr/bin/env python3
"""The runtime both halves of leanSilicon share, and the only thing they share.

`leanspec/` and `leanrtl/` do not import each other, do not read each other's directories and
do not know that the other exists.  What they have in common is *how a run is conducted* — how an
agent is started, what confines it, what a step document is, what gets written down — and that
lives here.

  * `agent`       the one place an agent session is started; the wall is not optional
  * `confine`     the `PreToolUse` hook that is that wall
  * `ledger`      an append-only event log, ordered under concurrency
  * `leanrun`     running Lean, and reading what it actually said
  * `provenance`  what a directory is holding, written down where the work happens
  * `seal`        making a wall a property of the call graph rather than of a convention
  * `steps`       one input file, one output file, nothing else between steps
  * `workspace`   a working directory that holds exactly one design

Sharing a runtime is not a coupling between the halves.  Each imports these; neither imports the
other; deleting either half leaves this package and the other half working.
"""
