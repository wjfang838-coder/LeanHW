#!/usr/bin/env python3
"""The step-document chain: one input file, one output file, nothing else between steps.

Both halves of leanSilicon are pipelines, and a pipeline without a seam between its stages is a
directory that every stage reads and writes at will.  Nothing is *wrong* with the results that
come out of such a directory, and everything is wrong with the shape: you cannot point at a file
and say "this is what step 3 produced", you cannot re-run step 4 without trusting that steps
1–3's leftovers are still the ones it was written against, and a reader asking "what did the
diagnosis actually see" has to reconstruct it from timestamps.

So there is a contract, and it is the narrowest one that still lets the steps do their work:

    step N reads exactly one file — `steps/roundR/(N-1)_*.json`, the previous step's output —
    and writes exactly one file — `steps/roundR/NN_<name>.json`.

Everything a step needs, it takes from that one document; everything it learns, it puts in its
own.  A step's output *contains* its input verbatim, under `inherited`, so the last document in
the chain is the whole run and any document in the middle is the whole run up to that point.
The chain is a chain of values, not a chain of side effects.

The flat working files a step's internals still read and write have not gone away; they have
changed status.  They are a **materialisation**: a step writes the ones it needs out of its
input document before it runs, so what a step reads is what its input *says*, not what happened
to survive from an earlier invocation.  That is the real decoupling.  Re-running step 4 on step
3's output gives the same answer whatever else has happened in that directory in the meantime,
because step 4 begins by overwriting the directory with its input.

## The seal

Each step declares whether it may reach through the doors `common/seal.py` guards, and the
runner **enforces the declaration** rather than documenting it: a step declared sealed runs
inside `seal.sealed()`, where those doors raise.  The declaration lives in the steps table, so
changing what a step may reach is a diff in the table rather than a call somewhere in a step
body.  The ledger is still the audit, and both are wanted:

    the seal   says this step COULD NOT have looked
    the ledger says this step DID NOT look

## Authored inputs

Some steps' inputs are written by an agent rather than computed here, and those are read from
`authored/roundR/` and hashed onto the step document.  A step that both writes and grades its
own input is not a step.

## What this module does not know

It does not know what a case is, what a design is, how many steps there are, or what any of them
does.  It takes a list of `Step`s and a context object it never inspects, and it enforces the
contract.  The two halves of leanSilicon each supply their own steps table and neither has to
know that the other exists.
"""
from __future__ import annotations

import dataclasses
import glob
import json
import os
import typing

from . import ledger, provenance, seal

STEPS_DIR = "steps"
AUTHORED = "authored"

_MISSING = object()


@dataclasses.dataclass(frozen=True)
class Step:
    """One step's declaration.  The table of these *is* the pipeline's specification."""
    n: int
    name: str
    title: str
    fn: typing.Callable
    # Declared, and then enforced by `Chain.run_step`.  Sealed is the default because the
    # interesting property of this method is what a stage could not see, and a default that has
    # to be opted out of is one a new step cannot acquire by being forgotten about.
    sealed: bool = True
    why_open: str = ""
    authored: tuple[str, ...] = ()
    authored_glob: tuple[str, ...] = ()

    @property
    def stem(self) -> str:
        return f"{self.n:02d}_{self.name}"

    def __post_init__(self):
        if not self.sealed and not self.why_open:
            raise ValueError(
                f"step {self.stem} is declared open and says nothing about why.  An open step is "
                f"a hole in the seal; the reason it exists goes on every document it writes, so "
                f"a reader of the record does not have to come back to this table to find it.")


# ------------------------------------------------------------------ reading the chain

def get(doc: dict | None, key: str, default=_MISSING):
    """A value produced by this step or by any step before it.

    The lookup walks `inherited`, which is what makes "a later step's output contains the earlier
    ones" load-bearing rather than decorative: a late step reads what an early one printed by
    asking its own input document for it, not by opening that step's file.

    The chain spans rounds as well as steps — round N's step 00 inherits round N-1's handoff — so
    this returns the *latest* value for a key several rounds produced.  That is right for
    anything describing the current state and wrong for anything the whole run accumulates;
    `get_all` is for the latter.

    Absence raises, because for almost every caller a key the chain never produced means the
    chain is broken and the useful outcome is a traceback naming the key.  `default` is for the
    one shape where absence is the expected state rather than a fault: a key only a LATER round
    can have produced, read from round 1.  Passing it is how a caller says so out loud — the
    alternative, softening the default to `None` for everyone, would turn every real chain break
    into an `AttributeError` several frames further on.
    """
    while doc:
        if key in (doc.get("produced") or {}):
            return doc["produced"][key]
        doc = doc.get("inherited")
    if default is not _MISSING:
        return default
    raise KeyError(f"no step in this chain produced {key!r}")


def get_all(doc: dict | None, key: str) -> list:
    """Every value under `key` in the chain, oldest first.

    `get` shadows: with four rounds in one chain it returns round 4's answers and round 1's are
    still in the document, unread.  For a question list that is exactly wrong — a question
    answered in round 1 is *gone* from round 4's extraction, because closing it is what the round
    did — so reading only the latest round produces a deliverable with the answered questions
    missing.  The union is what the file is supposed to be.
    """
    out = []
    while doc:
        if key in (doc.get("produced") or {}):
            out.append(doc["produced"][key])
        doc = doc.get("inherited")
    out.reverse()
    return out


def numbered(doc: dict | None, key: str) -> list[tuple[int | None, typing.Any]]:
    """`get_all`, with each value paired with the round that produced it.

    A question asked in two rounds has two witnesses with the same `id` and two answers naming
    it, and they are not interchangeable — the second asking was posed against a different option
    set, which is usually why there was a second asking.  Carrying the round alongside is what
    lets a deliverable match an answer to the asking it belongs to.
    """
    out = []
    while doc:
        if key in (doc.get("produced") or {}):
            out.append((doc.get("round"), doc["produced"][key]))
        doc = doc.get("inherited")
    out.reverse()
    return out


def has(doc: dict | None, key: str) -> bool:
    try:
        get(doc, key)
        return True
    except KeyError:
        return False


# --------------------------------------------------------------------------- the chain

@dataclasses.dataclass
class Chain:
    """A run's steps, its directory, and the enforcement of the contract between them.

    `ctx` is handed to every step function and is never inspected here — it is whatever the half
    in question calls a run (a case, a workspace).  `root` is where the ledger lives, which is
    the repository rather than the run: one log per invocation, not one per directory.
    """
    ctx: typing.Any
    dir: str
    name: str
    steps: list[Step]
    handoff: int
    root: str

    def __post_init__(self):
        self.by_n = {s.n: s for s in self.steps}
        self.by_name = {s.name: s for s in self.steps}
        if len(self.by_n) != len(self.steps):
            raise ValueError(f"{self.name}: two steps share a number")
        if self.handoff not in self.by_n:
            raise ValueError(f"{self.name}: handoff step {self.handoff} is not in the table")

    # --------------------------------------------------------------------- paths

    def path(self, *parts: str) -> str:
        return os.path.join(self.dir, *parts)

    def round_dir(self, base: str, rnd: int) -> str:
        return os.path.join(base, f"round{rnd}")

    def step_path(self, st: Step, rnd: int) -> str:
        return self.path(self.round_dir(STEPS_DIR, rnd), st.stem + ".json")

    def handoff_path(self, rnd: int) -> str:
        """Where round `rnd + 1` reads its predecessor.

        A round does not hand off from its LAST step, it hands off from the last *sealed* step
        that carries the accumulated state.  Where those differ, inheriting the last step would
        drag whatever made it open into the `inherited` blob of every sealed step of the next
        round — the seal would still be enforced at the door and would mean nothing, because the
        answer would already be in the room.  So the chain forks at the end of a round: the
        handoff step feeds the next round, and anything after it is that round's terminal
        accounting, read by nothing downstream.
        """
        return self.step_path(self.by_n[self.handoff], rnd)

    def existing_rounds(self) -> list[int]:
        d = self.path(STEPS_DIR)
        if not os.path.isdir(d):
            return []
        return sorted(int(f[5:]) for f in os.listdir(d)
                      if f.startswith("round") and f[5:].isdigit()
                      and os.path.isdir(os.path.join(d, f)))

    # ---------------------------------------------------------- authored inputs

    def authored(self, name: str, rnd: int) -> str:
        p = self.path(self.round_dir(AUTHORED, rnd), name)
        if not os.path.isfile(p):
            raise FileNotFoundError(
                f"{self.name}: {os.path.relpath(p)} is missing.  This step's input is written by "
                f"the agent, from what it was given and from the previous step's output; the "
                f"pipeline does not synthesise it, because a step that writes its own input "
                f"decides its own result.")
        with open(p, errors="replace") as f:
            return f.read()

    def authored_glob(self, pattern: str, rnd: int) -> dict[str, str]:
        """The round's authored inputs whose names the agent chooses rather than the framework.

        A file with one fixed name can be named in `Step.authored`.  A *set* whose size depends
        on what the agent found — one candidate per reading of one question — is discovered
        rather than declared, which is why it lands here.
        """
        d = self.path(self.round_dir(AUTHORED, rnd))
        out = {}
        for p in sorted(glob.glob(os.path.join(d, pattern))):
            with open(p, errors="replace") as f:
                out[os.path.basename(p)] = f.read()
        return out

    def materialise(self, files: dict[str, str]) -> list[str]:
        """Write a step's working files out of its document and into the run directory.

        Paths are relative to the run directory.  This is the line that makes a step a function
        of its input rather than of the directory's history: it overwrites, unconditionally,
        before the step runs.

        Where a name lands is the CONTEXT's decision, not this function's.  `leanspec` routes a
        bare `foo.json` into `state/` and leaves any path with a separator alone, so a step that
        materialises `"extraction.json"` and a module that reads `case.path("extraction.json")`
        have to agree — and until this asked the context, they did not.  Every step wrote
        `<case>/extraction.json` and every reader looked in `<case>/state/extraction.json`, so
        step 03 raised `FileNotFoundError` on a file its own step had just written.  It survived
        because steps 03 through 08 had never run: steps 00-02 materialise `sandbox/Partial.lean`,
        which has a separator in it and is therefore placed identically either way.

        A context without a `path` of its own keeps the plain join, which is what `leanrtl` uses.
        """
        place = getattr(self.ctx, "path", None)
        if not callable(place):
            place = self.path
        written = []
        for rel, content in files.items():
            p = place(*rel.split("/"))
            os.makedirs(os.path.dirname(p), exist_ok=True)
            with open(p, "w") as f:
                f.write(content)
            written.append(rel)
        return sorted(written)

    # ------------------------------------------------------------------ running

    def _input(self, st: Step, rnd: int) -> tuple[dict | None, dict | None]:
        """The one document this step reads, and the reference that names it."""
        if st.n > 0:
            prev = self.by_n[st.n - 1]
            p = self.step_path(prev, rnd)
            if not os.path.isfile(p):
                raise FileNotFoundError(
                    f"{self.name}: round {rnd} step {st.n:02d} needs step {prev.n:02d}'s output "
                    f"at {os.path.relpath(p)}, which does not exist.  Steps read one file and it "
                    f"is the previous one's; there is no other channel between them.")
            with open(p, errors="replace") as f:
                raw = f.read()
            inp = json.loads(raw)
            ref = {"file": os.path.relpath(p, self.dir), "sha256": provenance.sha256(raw),
                   "step": prev.stem, "round": rnd}
            if not inp.get("ok", True):
                raise RuntimeError(
                    f"{self.name}: round {rnd} step {prev.n:02d} ({prev.name}) did not succeed, "
                    f"so step {st.n:02d} has nothing sound to read.  Its problems: "
                    f"{inp.get('problems')}")
            return inp, ref

        if rnd > 1:
            # The seam between rounds, and it is deliberately *not* gated on the handoff
            # document's `ok`.  A round exists because the previous one did not converge, and
            # `ok=False` at the end of a round is the ordinary way that shows up; refusing to
            # continue on it would make the round loop unreachable through the very condition
            # that calls for another round.  A handoff that failed to *emit* is a different
            # matter, and it is caught downstream: this round's first real step revalidates what
            # it inherits.
            hs = self.by_n[self.handoff]
            p = self.handoff_path(rnd - 1)
            if not os.path.isfile(p):
                raise FileNotFoundError(
                    f"{self.name}: round {rnd} needs round {rnd - 1}'s step {self.handoff:02d} "
                    f"output at {os.path.relpath(p)}, which does not exist.  A round is a "
                    f"continuation of the one before it, not a fresh start.")
            with open(p, errors="replace") as f:
                raw = f.read()
            return json.loads(raw), {
                "file": os.path.relpath(p, self.dir), "sha256": provenance.sha256(raw),
                "step": hs.stem, "round": rnd - 1,
                "why": f"round {rnd - 1} did not converge; its step {self.handoff:02d} is sealed "
                       f"and carries the accumulated state, so it is what this round continues "
                       f"from."}

        return None, None

    def run_step(self, st: Step, rnd: int = 1) -> dict:
        """One step of round `rnd`: read one file, run under the declared seal, write one file."""
        os.makedirs(self.path(self.round_dir(STEPS_DIR, rnd)), exist_ok=True)
        inp, inp_ref = self._input(st, rnd)

        guard = (seal.sealed(f"step {st.stem} is declared sealed") if st.sealed
                 else seal.unsealed())
        with guard:
            produced = st.fn(self.ctx, inp, rnd)

        doc = {
            "step": st.n,
            "name": st.name,
            "title": st.title,
            "run": self.name,
            "round": rnd,
            "sealed": st.sealed,
            "seal": ("sealed: the guarded doors raise for the duration of this step"
                     if st.sealed else "open — " + st.why_open),
            "input": inp_ref,
            "authored_inputs": {
                **{a: provenance.sha256(self.authored(a, rnd)) for a in st.authored},
                **{n: provenance.sha256(s) for p in st.authored_glob
                   for n, s in self.authored_glob(p, rnd).items()}},
            "ok": bool(produced.get("ok", True)),
            "problems": produced.get("problems", []),
            "produced": {k: v for k, v in produced.items() if k not in ("ok", "problems")},
            "inherited": inp,
        }
        out = self.step_path(st, rnd)
        with open(out, "w") as f:
            json.dump(doc, f, indent=1, default=str)
        ledger.log(self.root, "pipeline_step", run=self.name, step=st.n, name=st.name,
                   ok=doc["ok"], round=rnd, sealed=st.sealed,
                   output=os.path.relpath(out, self.dir))
        return doc

    def run(self, first: int = 0, last: int | None = None, rnd: int = 1,
            say=lambda _: None) -> list[dict]:
        """Steps `first`..`last` of round `rnd`, stopping at the first that does not succeed.

        Stopping rather than continuing, because a step reads exactly one file and it is the
        previous step's: running on past a failure means running on the last document that
        happened to be written, which is a different run than the one being asked for.
        """
        last = max(self.by_n) if last is None else last
        docs = []
        for st in sorted(self.steps, key=lambda s: s.n):
            if not (first <= st.n <= last):
                continue
            doc = self.run_step(st, rnd)
            docs.append(doc)
            mark = "ok" if doc["ok"] else "FAILED"
            say(f"  {st.stem:<22} {mark}"
                + ("" if doc["ok"] else "  " + "; ".join(map(str, doc["problems"][:3]))))
            if not doc["ok"]:
                break
        return docs
