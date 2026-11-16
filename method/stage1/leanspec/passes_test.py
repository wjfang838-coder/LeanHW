#!/usr/bin/env python3
"""Stage 2's six passes: what the driver writes, and what three sessions at once are allowed to do.

    python3 -m leanspec.passes_test

Two changes to the formalization phase are under test here, and they are one change: the second is
only possible because of the first.

THE `case` RECORD IS WIRING, SO THE DRIVER WRITES IT.  `case : Case Ctx Obs` binds seven
declarations and invents nothing -- 23 of the 24 recorded `Partial.lean` files declare it and all
23 declare it identically.  While a session wrote it, the `render` pass could not begin until `obs`
had finished, because `case` names `obsUniverse`.  Eight lines of wiring were the whole reason two
passes were ordered.  `emit.case_stanza` generates it and `author._wire_case` appends it after the
last pass has run.

    stanza     a file with no `case` gets one, and it declares all seven fields
    stanza     a file that declares `case` is left alone -- a session that wrote one keeps it
    stanza     `def caseSplit :` is not a `case` declaration
    wire       appending re-records the pass hash, or a resumed round re-authors six passes
    wire       a file that has one is not given a second
    wire       nothing to append to is not an error

THREE SESSIONS, THREE COPIES, ONE JOIN.  `obs`, `render` and `properties` read no declaration each
other writes, so they run at once.  Not on one path: three `claude -p` sessions with `Write` on one
file is three sessions overwriting each other, and the loser's work is lost *invisibly* -- the file
still elaborates and the record still says the pass is done.  Each gets the artifact as the last
serial pass left it, in a directory of its own, and the driver reads back what each ADDED.

The join is refused unless it is a join.  Both refusals fall back to writing the passes in
sequence, which is a decision and not an error; a partial salvage would leave the kept sections
written against a file that no longer exists.

    join       the sections land in pass order, not in the order the sessions finished
    join       ...and so does the log, which is read as the story of how the file was written
    join       a pass that edited what was above its own section sends the group back to sequence
    join       a join that does not elaborate does too -- two sound sections can collide on a name
    join       a pass that never finished is the phase failing, not a fallback
    join       every refusal leaves the artifact and the pass record exactly as it found them

    stage      the snapshots are staged, so `_rewind_to` still means what it means serially
    rewind     ...which is what makes undoing one pass of a joined group possible at all

WHEN THE FORK IS TAKEN.  At the first undone pass whose whole remainder is independent -- so a
round resumed with `obs` already done forks over the two that are left -- and at most once, because
a group that fell back to sequence must not be re-forked at the very next pass.

    fork       a fresh round writes `types`, `ctxs`, `admits` one at a time
    fork       ...then forks over the three that are left
    fork       a resumed round forks over the remainder
    fork       one pass left is not a fork
    fork       a fallback to sequence is not re-forked
    fork       `LEANSPEC_SERIAL` writes all six in sequence
"""

from __future__ import annotations

import json
import os
import shutil
import sys
import tempfile
import time

sys.path.insert(0, os.path.dirname(os.path.dirname(os.path.abspath(__file__))))

from leanspec import author, cases, emit                                   # noqa: E402

SEED = """\
import LeanSpec

structure Ctx where
  n : Nat

structure Obs where
  v : Nat
"""

#: The three that may be written at once, as `in_passes` numbers them.
GROUP = [(4, "obs"), (5, "render"), (6, "properties")]


def _tail(tag: str) -> str:
    return f"\n-- section written by {tag}\ndef {tag}Universe : List Nat := [0]\n"


class _Fixture:
    """A round directory with a target file and a pass record, and the stubs put back after."""

    def __init__(self, done: list[str], seed: str = SEED, write_target: bool = True):
        self.dir = tempfile.mkdtemp(prefix="passes_test.")
        self.target = os.path.join(self.dir, "Partial.lean")
        if write_target:
            with open(self.target, "w") as f:
                f.write(seed)
        self.done = list(done)
        if self.done:
            author._record_pass(self.dir, self.target, self.done)
        self.saved = {"_one_pass": author._one_pass, "_in_parallel": author._in_parallel,
                      "_authored_dir": author._authored_dir, "run": author.leanrun.run,
                      "PARALLEL": author.PARALLEL}
        author._authored_dir = lambda case, rnd: self.dir
        author.leanrun.run = lambda p, **kw: {"ok": True, "errors": [], "out": ""}

    def close(self):
        for k, v in self.saved.items():
            if k == "run":
                author.leanrun.run = v
            else:
                setattr(author, k, v)
        shutil.rmtree(self.dir, ignore_errors=True)

    def read(self) -> str:
        with open(self.target, errors="replace") as f:
            return f.read()

    def snapshot(self, tag: str) -> str:
        p = os.path.join(self.dir, "passes", f"{tag}.lean")
        if not os.path.isfile(p):
            return ""
        with open(p, errors="replace") as f:
            return f.read()

    def record(self) -> dict:
        with open(os.path.join(self.dir, author.PASS_STATE)) as f:
            return json.load(f)


def _appender(behaviour=None, delay=None):
    """A stub `_one_pass` that writes what a session would have written.

    `behaviour[tag]` may be `"prefix"` (edit what was above its own section, which is what the
    `obs` pass is explicitly permitted to do) or `"fail"` (never finish).  `delay[tag]` makes the
    sessions complete out of order, which is the ordinary case and the one the log has to survive.
    """
    behaviour, delay, seen = behaviour or {}, delay or {}, []

    def stub(case, ph, rnd, model, repairs, note, i, tag, target, ext, extra=""):
        time.sleep(delay.get(tag, 0))
        seen.append((tag, extra))
        if behaviour.get(tag) == "fail":
            return False, f"{tag} never elaborated", [{"pass": tag, "pass_ok": False}]
        with open(target, errors="replace") as f:
            src = f.read()
        if behaviour.get(tag) == "prefix":
            src = src.replace("structure Obs where", "-- narrowed\nstructure Obs where")
        with open(target, "w") as f:
            f.write(src + _tail(tag))
        return True, "", [{"pass": tag, "pass_ok": True}]

    stub.seen = seen
    return stub


def _joined(*tags: str) -> str:
    return SEED + "".join(_tail(t) for t in tags)


def main() -> int:
    bad: list[str] = []
    n = 0

    def ck(what: str, cond: bool):
        nonlocal n
        n += 1
        print(f"  {'ok  ' if cond else 'WRONG'} {what}")
        if not cond:
            bad.append(what)

    print("\nthe `case` record is wiring, so the driver writes it")
    stanza = emit.case_stanza(SEED)
    ck("a file with no `case` gets one",
       stanza is not None and "def case : Case Ctx Obs" in stanza)
    ck("...and it declares all seven fields",
       all(f"{k} " in stanza for k in ("ctxs", "obs", "legal", "cost", "ctxJson", "ctxLean",
                                       "obsJson")))
    ck("a file that declares `case` is left alone",
       emit.case_stanza(SEED + "\ndef case : Case Ctx Obs := { }\n") is None)
    ck("`def caseSplit :` is not a `case` declaration",
       emit.case_stanza(SEED + "\ndef caseSplit : Nat := 0\n") is not None)

    fx = _Fixture(["types", "ctxs", "admits"])
    try:
        before = fx.record()["sha"]
        author._wire_case(fx.dir, fx.target, fx.done, 1)
        ck("the stanza is appended", "def case : Case Ctx Obs" in fx.read())
        ck("...and the pass hash is re-recorded, or a resumed round re-authors six passes",
           fx.record()["sha"] != before
           and author._passes_done(fx.dir, fx.target) == ["types", "ctxs", "admits"])
        was = fx.read()
        author._wire_case(fx.dir, fx.target, fx.done, 1)
        ck("a file that has one is not given a second", fx.read() == was)
    finally:
        fx.close()

    fx = _Fixture([], write_target=False)
    try:
        author._wire_case(fx.dir, fx.target, [], 1)
        ck("nothing to append to is not an error", not os.path.exists(fx.target))
    finally:
        fx.close()

    print("\nthree sessions, three copies, one join")
    fx = _Fixture(["types", "ctxs", "admits"])
    try:
        author._one_pass = _appender(delay={"obs": 0.09, "render": 0.045})
        status, why, entries = author._in_parallel(None, None, 1, "m", 1, "", GROUP, fx.dir,
                                                   fx.target, None, fx.done)
        ck("the sections land in pass order, not in the order the sessions finished",
           status == "ok" and fx.read() == _joined("obs", "render", "properties"))
        ck("...and the sessions did finish out of order, so that meant something",
           [t for t, _ in author._one_pass.seen] == ["properties", "render", "obs"])
        ck("...and so does the log",
           [e["pass"] for e in entries] == ["obs", "render", "properties"])
        ck("the pass record names all six, in order",
           fx.done == ["types", "ctxs", "admits", "obs", "render", "properties"]
           and author._passes_done(fx.dir, fx.target) == fx.done)
        ck("each session was told which others were writing at the same time",
           all(f"`{o}`" in x for t, x in author._one_pass.seen
               for o in ("obs", "render", "properties") if o != t))
        ck("...and none was told it was writing alongside itself",
           all(f"The `{t}`" not in x for t, x in author._one_pass.seen))

        ck("the snapshots are staged, so a rewind means what it means serially",
           fx.snapshot("obs") == _joined("obs")
           and fx.snapshot("render") == _joined("obs", "render")
           and fx.snapshot("properties") == _joined("obs", "render", "properties"))
        ck("...which is what makes undoing one pass of a joined group possible at all",
           author._rewind_to(fx.dir, fx.target, list(fx.done), "properties")
           and fx.read() == _joined("obs", "render")
           and author._passes_done(fx.dir, fx.target) == ["types", "ctxs", "admits", "obs",
                                                          "render"])
    finally:
        fx.close()

    for name, kw, expect in (
            ("a pass that edited what was above its own section sends the group back to sequence",
             {"behaviour": {"obs": "prefix"}}, ("serial", "changed what was above")),
            ("a pass that never finished is the phase failing, not a fallback",
             {"behaviour": {"render": "fail"}}, ("failed", "was not completed"))):
        fx = _Fixture(["types", "ctxs", "admits"])
        try:
            author._one_pass = _appender(**kw)
            status, why, _ = author._in_parallel(None, None, 1, "m", 1, "", GROUP, fx.dir,
                                                 fx.target, None, fx.done)
            ck(name, status == expect[0] and expect[1] in why)
            ck(f"...and it left the artifact and the record as it found them ({expect[0]})",
               fx.read() == SEED and fx.done == ["types", "ctxs", "admits"]
               and author._passes_done(fx.dir, fx.target) == fx.done)
        finally:
            fx.close()

    fx = _Fixture(["types", "ctxs", "admits"])
    try:
        author._one_pass = _appender()
        author.leanrun.run = lambda p, **kw: {"ok": False, "errors": ["`obsUniverse` twice"],
                                              "out": ""}
        status, why, _ = author._in_parallel(None, None, 1, "m", 1, "", GROUP, fx.dir,
                                             fx.target, None, fx.done)
        ck("a join that does not elaborate goes back to sequence too",
           status == "serial" and "does not elaborate" in why and "obsUniverse" in why)
        ck("...and it left the artifact and the record as it found them (join)",
           fx.read() == SEED and fx.done == ["types", "ctxs", "admits"])
    finally:
        fx.close()

    print("\nwhen the fork is taken")
    ph = [p for p in author.PHASES if p.tag == "formalization"][0]
    ck("the six passes are the ones this is about",
       [t for t, _ in ph.passes] == ["types", "ctxs", "admits", "obs", "render", "properties"])

    def _fork_run(done: list[str], parallel=None, status: str = "ok"):
        """Run `in_passes` with both writers stubbed.  Returns (serial tags, forked todos)."""
        fx = _Fixture(done, write_target=bool(done))
        try:
            if parallel is not None:
                author.PARALLEL = parallel
            serial, forks = [], []

            def one(case, ph_, rnd, model, repairs, note, i, tag, target, ext, extra=""):
                serial.append(tag)
                return True, "", []

            def par(case, ph_, rnd, model, repairs, note, todo, out, target, ext, done_):
                forks.append([t for _, t in todo])
                if status == "ok":
                    done_.extend(t for _, t in todo)
                return status, "stubbed", []

            author._one_pass, author._in_parallel = one, par
            ok, why = author.in_passes(cases.Case(name="passes.probe"), ph, 1, "m", 1, [])
            assert ok, why
            return serial, forks
        finally:
            fx.close()

    serial, forks = _fork_run([])
    ck("a fresh round writes `types`, `ctxs`, `admits` one at a time",
       serial[:3] == ["types", "ctxs", "admits"])
    ck("...then forks over the three that are left", forks == [["obs", "render", "properties"]]
       and serial == ["types", "ctxs", "admits"])

    serial, forks = _fork_run(["types", "ctxs", "admits", "obs"])
    ck("a resumed round forks over the remainder",
       forks == [["render", "properties"]] and serial == [])

    serial, forks = _fork_run(["types", "ctxs", "admits", "obs", "render"])
    ck("one pass left is not a fork", forks == [] and serial == ["properties"])

    serial, forks = _fork_run(["types", "ctxs", "admits"], status="serial")
    ck("a fallback to sequence is not re-forked",
       len(forks) == 1 and serial == ["obs", "render", "properties"])

    serial, forks = _fork_run([], parallel=())
    ck("`LEANSPEC_SERIAL` writes all six in sequence",
       forks == [] and serial == [t for t, _ in ph.passes])

    if bad:
        print(f"\n{len(bad)} case(s) wrong:")
        for n in bad:
            print(f"  {n}")
        return 1
    print(f"\npasses: all {n} cases hold — the driver writes the wiring, three sessions write "
          f"three sections into three copies, and a join that is not a join is written in "
          f"sequence instead")
    return 0


if __name__ == "__main__":
    sys.exit(main())
