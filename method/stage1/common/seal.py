#!/usr/bin/env python3
"""The seal: making a wall a property of the call graph rather than of a convention.

An earlier generation of this method described its wall as two auditable mechanisms — an
append-only ledger and a leak scan — and both are *post hoc*.  They report a violation after it
has happened, which is the right thing to have and the wrong thing to rely on: nothing in the
process stopped a stage from opening what it was declared not to see, and a stage that did would
be caught only if the thing it opened left fingerprints in its output.

This closes that.  Every stage of leanSpec except resolution must derive its result from the
prose alone, and the designer oracle is the single door out.  `oracle.ask_all()` checks the seal, so
a sealed stage that reaches for the designer *raises* instead of getting an answer.  The audit
stays exactly as it was, because the two answer different questions:

    the seal   says this run COULD NOT have looked
    the ledger says this run DID NOT look

Nested seals keep the outermost reason, so a step that seals itself inside an already-sealed
region cannot widen its own permissions by accident.
"""
from __future__ import annotations

import contextlib

DEFAULT_REASON = "this stage must derive its result from the prose alone"


class Sealed(RuntimeError):
    """A sealed stage reached for something the seal covers."""


_SEALED: str = ""


@contextlib.contextmanager
def sealed(reason: str = DEFAULT_REASON):
    """Make the sealed doors raise for the duration.  Nested seals keep the outermost reason."""
    global _SEALED
    prev = _SEALED
    _SEALED = prev or reason
    try:
        yield
    finally:
        _SEALED = prev


@contextlib.contextmanager
def unsealed():
    """Explicitly open the wall.  Written at the call site, so a reader can grep for every place
    in the framework where it is opened on purpose."""
    global _SEALED
    prev = _SEALED
    _SEALED = ""
    try:
        yield
    finally:
        _SEALED = prev


def is_sealed() -> str:
    """The reason, or `""` when open.  Truthy means sealed."""
    return _SEALED


def check(what: str) -> None:
    """Raise if sealed.  Called at the door, not by the caller of the door — a check the caller
    performs is a check the caller can forget."""
    if _SEALED:
        raise Sealed(
            f"{what} was reached from a sealed stage.  {_SEALED}.  A stage that must derive its "
            f"result from the prose alone cannot ask the designer what the answer is; if this "
            f"stage genuinely needs it, change its declaration where the steps are listed, so "
            f"the change is on the record rather than in a call."
        )
