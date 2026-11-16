#!/usr/bin/env python3
"""leanRTL's step chain: prose in, a certified Verilog module out, one document per step.

    python3 -m leanrtl.pipeline --ws <workspace> [--first 0] [--last 8] [--round 1]

Nine steps on the same contract `common/steps.py` enforces for leanSpec: each reads exactly one
file and it is the previous step's, each writes exactly one, and each carries the document it
read in an `inherited` envelope so a reader can reconstruct what the step saw without trusting
that the directory has not moved since.

    00 input       the prose this run is about, and which arm it came from
    01 contract    the interface, DERIVED from the prose rather than transcribed
    02 spec        S writes frags/<key>/spec.lean                       [open: spawns an author]
    03 freeze      sha recorded, mode 0444, path onto the read-only list
    04 impl        D writes frags/<key>/impl.lean                       [open: spawns an author]
    05 simdiff     160 cycles of the executable spec against the implementation
    06 proof       D writes frags/<key>/proof.lean                      [open: spawns an author]
    07 emit        RTLIL -> Verilog, then the interface gate
    08 certify     every gate the profile declares, plus proof mutation

## Two Verilog modules, not one

    out/<key>.preproof.v    the implementation as D first wrote it, emitted with no proof
    out/<key>.v             the same implementation after the proof phase

The second is what the gates certify and what a report quotes.  The first exists so that "the
proof changed the design" is a claim somebody can check rather than one this repository asserts
about itself.  It is taken at the tail of step 04 and NOT as a step of its own: it spawns no
author, it decides nothing, and it cannot fail a run — a measurement wired into the pass/fail
chain is a measurement that quietly selects which runs get measured.  `leanrtl/preproof.py` has
the rest, including why the pair has to come out of one session instead of two arms.

## The numbering is the architecture

`emit` is before `certify` because `undriven_nets` reads the emitted Verilog: a gate about an
artifact cannot run before the artifact exists.  `freeze` is its own step rather than the tail of
`spec` because the freeze is the thing a later reader most needs a timestamp and a hash for, and
a fact recorded inside the step that could have prevented it is a weaker record.  `simdiff` sits
between `impl` and `proof` because it is the cheap check: an implementation the specification's
own executable form disagrees with is not worth an hour of proof, and the same information comes
out of the proof attempt much later and much more expensively.

## What this half is given, and what it is deliberately not given

Exactly one file: a natural-language specification.  Either the original prose or a decided
version of it — the `--arm` label says which, and NOTHING else differs between the two runs.

The plan this repository was built from had this step reading a `HANDOFF.json` alongside the
prose, carrying the questions the other half answered and the coordinates it left open.  That was
dropped on instruction, and the reason is worth stating because the cost is real.  A handoff file
tells the implementer which parts of the document were argued over.  That is a hint no ordinary
specification carries, and an arm that gets it is not being asked the same question as an arm
that does not.  Removing it makes the comparison between the two arms clean: both halves see a
document and nothing about how it came to be.

What it costs: an implementer handed a partially-decided document cannot tell a question that was
answered from one that was never asked.  A coordinate the other half left open reads exactly like
a coordinate nobody noticed, and D will resolve it by assumption and record the assumption — which
is the right behaviour, but it means the two arms' assumption lists are not directly comparable.
That is stated here and in `leanspec/pipeline.py`, and it is the price of the decoupling.

This half also never reads the other half's directory.  Not by convention: `data/part1/` is on the
confinement hook's deny list for every session this pipeline starts.

## Sealed and open

`sealed` means the same thing in both halves — this step could not reach the one door out — and
the door is different because the halves are.  leanSpec's door is the designer oracle.  This
half has no designer; its door is the model that writes code, and `_author()` calls `seal.check`
before spawning one.  So steps 02, 04 and 06 are declared open and the other six are sealed, and
that declaration is enforced rather than described: a sealed step that tried to spawn an author
would raise.

Six of nine steps being unable to call a model is the substantive claim here.  The contract, the
freeze, the vector diff, the emission and every gate are deterministic functions of files on
disk, and can be re-run against the same inputs to the same answer.
"""
from __future__ import annotations

import argparse
import dataclasses
import json
import os
import shutil
import subprocess
import sys
from collections.abc import Callable

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

from common import ledger, paths, profiles, provenance, seal                        # noqa: E402
from common import steps as steps_mod                                        # noqa: E402
from leanrtl import contract, preproof, two_author, verify as verify_mod    # noqa: E402

STEPS_DIR = steps_mod.STEPS_DIR
AUTHORED = steps_mod.AUTHORED

# Round N reads round N-1's step 04.  A round of this half exists for exactly one reason — the
# implementer challenged the frozen specification — and step 04 is where a challenge is written.
# Pointing the handoff at the last step instead would say a round is a continuation of a finished
# run, which is not what a challenged round is: steps 05..08 of a challenged round never ran.
HANDOFF = 4

ARMS = ("original", "decided")


@dataclasses.dataclass
class Run:
    """One design, one workspace, one arm.  Persisted so a resumed run cannot drift from the
    one it is resuming."""
    ws: str
    key: str
    profile: str
    toplevel: str
    prose: str          # absolute path to the natural-language specification
    arm: str
    # Whether `certify` asks the mutation question at all.  It is a field of the run rather than
    # a profile key because the profile decides what a design must PASS, and this decides what
    # was MEASURED about a passing one — turning it off must not move `profile_sha`, or every
    # run made without it becomes incomparable with the verdicts already on disk.  Defaulted
    # True and read through `Run(**d)`, so a `run.json` written before this field loads as one
    # that mutated, which is what those runs did.
    mutation: bool = True

    @property
    def gates(self) -> dict:
        return profiles.gates(profiles.load(self.profile))

    def path(self, *p: str) -> str:
        return os.path.join(self.ws, *p)

    def save(self) -> None:
        with open(self.path("run.json"), "w") as f:
            json.dump(dataclasses.asdict(self), f, indent=1)

    @staticmethod
    def load(ws: str) -> "Run":
        p = os.path.join(ws, "run.json")
        if not os.path.isfile(p):
            raise FileNotFoundError(
                f"pipeline: {p} does not exist.  A workspace records which design, which arm and "
                f"which prose file it is for, because a run resumed against a different one of "
                f"those is a different run wearing the first one's directory.")
        with open(p) as f:
            d = json.load(f)
        # `ws` is resolved from where the file was FOUND, not from what it says.  The recorded
        # value is a record of where this ran, and a workspace that has since been moved -- the
        # tree reorganised, the directory copied to another machine -- is still that workspace.
        # Trusting the stored string instead makes every path derived from it point at a
        # directory that no longer exists, and the failure surfaces several calls later as a
        # missing fragment rather than as "this record is stale".
        d["ws"] = os.path.abspath(ws)
        return Run(**d)


# ------------------------------------------------------------------- spawning an author

#: How many times an author is asked for the same artifact before the step gives up on it.
#:
#: A session can exit `rc=0`, `how="ok"`, `is_error=false` — the CLI's own report of a clean
#: finish — having never written the file the step exists to obtain.  Four of them did, across
#: the 50-design rtllm sweep: `calendar` spec stopped after 220 s on "Now I have what I need.
#: Let me write my notes as I go, then the spec.", `adder_pipe_64bit` spec after 639 s,
#: `instr_reg` spec after 395 s with `spec.lean` on disk and no `S.committed` beside it, and
#: `adder_8bit` impl after 329 s on "Now let me write the implementation."  All four announced
#: the write and ended the turn instead of performing it.
#:
#: None of `agent._supervise`'s rules can see this.  `STALL` watches for a transcript that stops
#: growing and this one stopped growing by exiting; `STORM` counts API retries and there were
#: none; the timeout is an hour away.  Those rules answer "is this session still working"; this
#: one answers "did the session do the thing", and only the caller knows what the thing was.
#:
#: So the predicate comes from the step, and the retry is a fresh session rather than a nudge
#: down the same one — sessions run `--no-session-persistence`, so there is nothing to resume.
#: What carries over is the workspace: an author that wrote a draft and stopped short sees its
#: own draft on disk next time, which is why `instr_reg`'s uncommitted `spec.lean` is worth
#: re-entering rather than starting from nothing.
#:
#: A session that ended `ok` is retried.  So is one that ended badly *but left the artifact on
#: disk* — see `made` in `_author`.  Everything else is not: `timeout`, `stalled` and `api-storm`
#: on an empty workspace mean the session never got a turn through, and re-sending the same long
#: request into the same fault is precisely what `_supervise` was written to stop paying for.
#:
#: The exception is not a softening of that rule, it is the case the rule was never about.  Cost
#: is the whole argument for refusing to retry a timeout, and when the artifact already exists the
#: retry is not the hour-long request again — it is a short session that reads its own finished
#: file and signs it.  Measured: `cvdp_copilot_16qam_mapper_0006` spent 3603 s on `impl`, of which
#: 1.0 min was in the 39 Lean builds it ran; its errors converged to zero, its last three messages
#: were "Every gate is green", "One wording fix", "Now the notes, then commit", and the wall
#: arrived during the sign-off.  `impl.lean` was on disk, complete; `D.committed` was not, and the
#: whole hour was discarded over the marker.  `sync_serial_communication_0001` lost `spec` the
#: same way at `stalled`.
#:
#: Nothing is laundered by this.  Committing is a sign-off, not a gate: steps 05 through 08 re-run
#: every gate against whatever was committed, so a retry that only signs off cannot move a bad
#: artifact past anything it would not otherwise have to pass.
AUTHOR_ATTEMPTS = int(os.environ.get("LEANSILICON_AUTHOR_ATTEMPTS", "3"))

#: Prefixed to the unchanged prompt on a retry.  Deliberately thin: it names what is missing and
#: says the previous session ended without it, and it changes nothing about the task.  A retry
#: prompt that re-explains the job is a different prompt, and then the artifact that comes back
#: is not the one the first prompt was asking for.
RESUME_NOTE = """\
NOTE — this is attempt {n} of {total} at this step.  A previous session for this exact task ended
without producing what the step requires:

{missing}

Nothing else about the task has changed; the full instructions follow unaltered.  Anything you
already wrote is still on disk in this workspace — read it first and continue from there rather
than starting over.  Finish by actually writing and committing the artifact, in this session.

----------------------------------------------------------------------

"""


def _author(run: Run, phase: str, rnd: int, ch: dict | None = None,
            done: Callable[[], list[str]] | None = None,
            made: Callable[[], bool] | None = None) -> dict:
    """Run one authoring session, through the one door this half has.

    `seal.check` first, so a step that forgot to declare itself open fails here rather than
    quietly producing a model-written artifact inside a region the record says was deterministic.

    `done` returns what is still missing, empty when the session did its job.  It is the step's
    own acceptance test rather than a rule here, because "the artifact" is different in each of
    the three phases and one of them — `impl` — has two acceptable answers.  When it comes back
    non-empty and the session ended cleanly, the author is asked again; see `AUTHOR_ATTEMPTS`.

    `made` answers a narrower question: is the expensive artifact — the `.lean` file itself, not
    the sign-off beside it — already on disk?  When it is, a session that ended `timeout` or
    `stalled` is retried too, because the next attempt is then a short one that reads its own
    finished file rather than a repeat of the request that ran out of clock.  A step whose
    acceptance test is the file alone has no use for it: `made()` true would leave `done()` empty
    and the loop breaks on that first.  `step_proof` passes nothing for exactly that reason, and
    would need to start passing it if `_missing_proof` ever grew a marker of its own.

    The returned record is the last attempt's, with `attempts` and `attempt_log` added.  Every
    attempt gets its own transcript, its own prompt file and its own ledger row: a retried step
    that overwrote the first session's transcript would erase the only evidence of the failure
    mode that made the retry necessary.
    """
    seal.check("an authoring session")
    role_of = {"spec": two_author.role_S, "impl": two_author.role_D, "proof": two_author.role_D}
    role = role_of[phase](run.ws, run.key)
    # `data/part1/` is the other half's directory.  Denying it is what makes "the two halves are
    # decoupled" a property of the run rather than a sentence in a README: the hook checks deny
    # before allow and exits 2, so an author that reaches for it gets a refusal, not a file.
    role = dataclasses.replace(role, deny=(*role.deny, paths.data(paths.PART1)))
    from common import agent
    base = two_author.prompt(run.ws, run.key, phase, ch=ch)
    os.makedirs(run.path("logs"), exist_ok=True)

    attempts, log, missing = 0, [], []
    for n in range(1, AUTHOR_ATTEMPTS + 1):
        attempts = n
        stem = f"{run.key}.{phase}.r{rnd}" + (f".a{n}" if n > 1 else "")
        text = base if n == 1 else RESUME_NOTE.format(
            n=n, total=AUTHOR_ATTEMPTS,
            missing="\n".join("  - " + m for m in missing)) + base
        with open(run.path("logs", stem + ".prompt.txt"), "w") as f:
            f.write(text)
        res = agent.run(role, run.ws, text, run.path("logs", stem + ".jsonl"), cwd=run.ws)
        # See `common/agent.refusals`.  A refused call is a prompt asking for something this role
        # was not granted; it presents as an author that went quiet, so it is printed as it
        # happens.
        summary = agent.refusal_summary(res["refusals"])
        if summary:
            print(f"  {run.key} · {phase} · round {rnd}:\n{summary}", flush=True)
        ledger.log(paths.DATA, "author", ws=os.path.basename(run.ws), key=run.key, phase=phase,
                   round=rnd, attempt=n, refusals=res["refusals"],
                   **{k: res[k] for k in ("role", "rc", "how", "elapsed", "denied")})
        missing = list(done()) if done else []
        log.append({"attempt": n, "how": res["how"], "rc": res["rc"],
                    "elapsed": res["elapsed"], "missing": missing})
        # A session is asked again if it ended cleanly, or if it ended badly having nonetheless
        # written the artifact — the second is the sign-off rescue, and it is cheap precisely
        # because the work it would otherwise repeat is already on disk.
        rescue = res["how"] != "ok" and made is not None and made()
        if not missing or not (res["how"] == "ok" or rescue) or n == AUTHOR_ATTEMPTS:
            break
        why = (f"session ended {res['how']} with the artifact written but not signed off"
               if rescue else "session ended ok without " + "; ".join(missing))
        print(f"  {run.key} · {phase} · round {rnd}: {why} — "
              f"asking again (attempt {n + 1}/{AUTHOR_ATTEMPTS})", flush=True)

    return {**res, "attempts": attempts, "attempt_log": log}


def _missing_spec(run: Run) -> list[str]:
    """What step 02 still needs from S.  Mirrors that step's own `problems`, on purpose.

    The retry note quotes this back to the author, so a wording that drifted from the step's
    would tell S to produce one thing and then fail it for another.
    """
    out = []
    if not os.path.isfile(two_author.frag(run.ws, run.key, "spec")):
        out.append("frags/%s/spec.lean" % run.key)
    if not two_author.committed(run.ws, run.key, "S"):
        out.append("frags/%s/S.committed — the specification is still a draft" % run.key)
    return out


def _missing_impl(run: Run) -> list[str]:
    """What step 04 still needs from D — and nothing, when D challenged instead.

    A challenge is a legitimate terminal state for the impl phase, so an author that raised one
    has finished its turn.  Retrying it would be asking D to withdraw an objection by attrition,
    which is the opposite of what the challenge mechanism is for.
    """
    ch = two_author.challenge(run.ws, run.key)
    if ch and not ch.get("malformed") and not ch.get("incomplete"):
        return []
    out = []
    if not os.path.isfile(two_author.frag(run.ws, run.key, "impl")):
        out.append("frags/%s/impl.lean" % run.key)
    if not two_author.committed(run.ws, run.key, "D"):
        out.append("frags/%s/D.committed" % run.key)
    return out


def _missing_proof(run: Run) -> list[str]:
    """What step 06 still needs from D.

    The file only — whether the proof it contains actually closes is step 06's business and the
    gates' after it, and a predicate that asked for a *green* proof would turn this retry into an
    unbounded "try until it works" loop over the hardest phase in the pipeline.  Not the same
    question: this one is about a session that stopped before writing, not one that wrote
    something insufficient.
    """
    if not os.path.isfile(two_author.frag(run.ws, run.key, "proof")):
        return ["frags/%s/proof.lean" % run.key]
    return []


def _bytes_sha(path: str) -> str:
    with open(path, "rb") as f:
        return provenance.sha256(f.read())


def _snapshot(run: Run, rnd: int, phase: str, *frags: str) -> list[str]:
    """Copy what the author just wrote into `authored/round<R>/`.

    The step document hashes what is in there, so this is what makes "the agent wrote exactly
    this" a checkable claim per round rather than a statement about whatever is on disk now.  A
    second round overwrites `frags/`; it does not overwrite round 1's snapshot.

    Nor does a later PHASE overwrite an earlier one's.  Both the implementation and the proof
    phase snapshot `impl.lean`, because D is permitted to re-encode the implementation in order
    to close a proof — so the second copy used to land on the first and the implementation as it
    stood before the proof was gone, which is exactly the artifact `leanrtl/preproof.py` exists
    to keep.  A phase that writes a DIFFERENT `impl.lean` now gets `impl.<phase>.lean` beside it.
    A phase that writes the identical bytes gets nothing, because a second filename would imply a
    correction that did not happen.
    """
    d = run.path(AUTHORED, f"round{rnd}")
    os.makedirs(d, exist_ok=True)
    got = []
    for f in frags:
        src = run.path("frags", run.key, f + ".lean")
        if not os.path.isfile(src):
            continue
        dst = os.path.join(d, f + ".lean")
        if os.path.isfile(dst):
            if _bytes_sha(dst) == _bytes_sha(src):
                got.append(f + ".lean")
                continue
            dst = os.path.join(d, f"{f}.{phase}.lean")
        shutil.copy2(src, dst)
        got.append(os.path.basename(dst))
    role = "S" if phase == "spec" else "D"
    src = run.path("notes", f"{run.key}.{role}.{phase}.json")
    if os.path.isfile(src):
        shutil.copy2(src, os.path.join(d, f"{role}.{phase}.json"))
        got.append(f"{role}.{phase}.json")
    return got


def _notes(run: Run, phase: str) -> dict | None:
    role = "S" if phase == "spec" else "D"
    p = run.path("notes", f"{run.key}.{role}.{phase}.json")
    if not os.path.isfile(p):
        return None
    try:
        with open(p, errors="replace") as f:
            return json.load(f)
    except ValueError:
        # Reported as malformed rather than dropped.  An author's closing block is the only place
        # a declared assumption is written down, and a run that silently reports zero assumptions
        # because the JSON had a trailing comma is worse than one that says the file is broken.
        return {"malformed": True, "raw_head": open(p, errors="replace").read()[:400]}


def _bbf(run: Run, *argv: str) -> tuple[int, str]:
    r = subprocess.run([sys.executable, run.path("scripts", "bbf.py"), run.key, *argv],
                       cwd=run.ws, capture_output=True, text=True)
    return r.returncode, (r.stdout + r.stderr)[-4000:]


# ----------------------------------------------------------------------------- the steps

def step_input(run: Run, inp: dict | None, rnd: int) -> dict:
    """The prose, hashed, and copied to where every downstream reader looks for it.

    Copied rather than referenced: the file this run was about must still be readable, byte for
    byte, after whatever produced it has moved on.  A pipeline whose input is a path is a
    pipeline whose record can be invalidated from outside it.
    """
    if not os.path.isfile(run.prose):
        return {"ok": False, "problems": [f"no prose at {run.prose}"]}
    with open(run.prose, errors="replace") as f:
        text = f.read()
    dest = run.path("specs", run.key + ".spec.txt")
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    with open(dest, "w") as f:
        f.write(text)

    ch = None
    if rnd > 1:
        # The only thing carried across a round boundary.  The prose is identical — a challenge
        # is a claim about the SPECIFICATION, never about the document, and a round that also
        # changed the prose would confound the two.
        ch = steps_mod.get(inp, "challenge", None)

    return {"ok": True,
            "arm": run.arm,
            "prose": os.path.relpath(dest, run.ws),
            "prose_sha256": provenance.sha256(text),
            "bytes": len(text.encode()),
            "source": run.prose,
            "challenge": ch,
            "note": ("this half is given a natural-language specification and nothing else; the "
                     "arm label records which document it was, and no other input differs "
                     "between arms")}


def step_contract(run: Run, inp: dict, rnd: int) -> dict:
    """The interface, derived.

    An earlier shape had an agent transcribe the module header out of the prose into a JSON
    contract that both authors then built against.  A contract with one port name mistyped
    produces a specification and an implementation that agree with each other perfectly and mean
    nothing about the design — and nothing downstream can see it, because every downstream check
    compares the two halves through the contract's own names.

    So it is computed.  A contradiction in the document is a refusal, because a contract that
    guesses hands both authors the same guess — and so is a width the document names and never
    fixes, because a port nothing can drive is a port no gate downstream is actually testing.
    An undetermined DIRECTION is still only reported: it costs nothing to stimulate.
    """
    text = open(run.path(steps_mod.get(inp, "prose")), errors="replace").read()
    c = contract.derive(text, run.key, run.toplevel)
    dest = run.path("contracts", run.key + ".json")
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    with open(dest, "w") as f:
        json.dump(c, f, indent=1)

    problems = []
    if c["conflicts"]:
        problems.append("the prose contradicts itself about its own interface: "
                        + ", ".join(sorted(c["conflicts"])))
    if not c["ports"]:
        problems.append("no ports could be read out of the prose — a parse failure, not a "
                        "portless design")
    # A port count is not a usable interface.  Everything downstream that stimulates the design
    # reads `width` out of the contract JSON written just above and shifts by it — `simdiff`'s
    # vector generator does `1 << w` — so a port whose width is not a positive integer cannot be
    # driven, on any bench, and the run reaches `05_simdiff` only to compare nothing and report
    # `vacuous`.  That is not a hypothesis about a lane: it is the one code path, and it is why
    # this check belongs here rather than in a profile.  Measured on the workspaces that exist:
    # 8 designs across cvdp and rtllm carried an unresolved width, 0 converged, and every one
    # that got as far as simdiff came back `vacuous` — each after roughly 40 minutes of authoring.
    # `contract.main()` has refused this since it grew `--allow-undetermined`; the pipeline did
    # not, which made the automated path strictly more permissive than the hand one.
    open_w = [p for p in c["ports"] if not isinstance(p["width"], int) or p["width"] < 1]
    if open_w:
        problems.append(
            "the prose names a width for %d of %d port(s) and never fixes it, so nothing "
            "downstream can drive them: %s"
            % (len(open_w), len(c["ports"]),
               ", ".join("%s[%s]" % (p["name"], p.get("width_expr") or "?")
                         for p in sorted(open_w, key=lambda p: p["name"]))))
    return {"ok": not problems, "problems": problems,
            "contract": os.path.relpath(dest, run.ws),
            "module": c["module"], "n_ports": len(c["ports"]), "n_params": len(c["params"]),
            "ports": c["ports"], "params": c["params"],
            "clock": c["clock"], "reset": c["reset"],
            "undetermined": c["undetermined"], "derived_from": c["derived_from"]}


def step_spec(run: Run, inp: dict, rnd: int) -> dict:
    """S turns the prose into an executable, typed specification."""
    thawed = None
    ch = None
    if rnd > 1:
        # The one legitimate unfreeze.  S is being asked to rewrite the document in answer to a
        # challenge, and a document that cannot be rewritten cannot be revised.  It goes through
        # `unfreeze` rather than a `chmod` here so that the ledger carries who opened it and why:
        # everything after step 03 is a claim about a specific document, and "when did this stop
        # being that document" has to be answerable from the record alone.
        ch = steps_mod.get(inp, "challenge", None)
        thawed = two_author.unfreeze(
            run.ws, run.key,
            why=f"round {rnd}: D challenged version {rnd - 1} — "
                + (ch or {}).get("why", "(challenge text unavailable)")[:200])
        for m in ("S.committed", "D.committed"):
            p = run.path("frags", run.key, m)
            if os.path.isfile(p):
                os.remove(p)
        p = run.path("notes", f"{run.key}.challenge.json")
        if os.path.isfile(p):
            # Moved, not deleted.  It is round N-1's evidence and stays readable; leaving it in
            # place would make round N look challenged from the moment it started, and the round
            # that ANSWERS a challenge must not be indistinguishable from one that raised it.
            os.replace(p, run.path("notes", f"{run.key}.challenge.r{rnd - 1}.json"))

    res = _author(run, "spec", rnd, ch=ch, done=lambda: _missing_spec(run),
                  made=lambda: os.path.isfile(two_author.frag(run.ws, run.key, "spec")))
    got = _snapshot(run, rnd, "spec", "spec")
    notes = _notes(run, "spec")
    committed = two_author.committed(run.ws, run.key, "S")
    problems = []
    if not got:
        problems.append("S wrote no frags/%s/spec.lean" % run.key)
    if not committed:
        problems.append("S did not commit — the specification is still a draft, and freezing a "
                        "draft records a version nobody signed off on")
    return {"ok": not problems, "problems": problems, "session": res,
            "committed": committed, "authored": got, "unfroze": thawed,
            "ambiguities": (notes or {}).get("ambiguities", []),
            "notes": notes}


def step_freeze(run: Run, inp: dict, rnd: int) -> dict:
    """Record the hash, make it read-only, and say plainly what that does and does not buy.

    This is the load-bearing step of the whole half.  Everything after it is a claim about a
    document, and the claim is only worth what the guarantee that the document did not move is
    worth.
    """
    rec = two_author.freeze(run.ws, run.key, version=rnd)
    ledger.log(paths.DATA, "spec_frozen", ws=os.path.basename(run.ws), key=run.key,
               sha256=rec["sha256"], version=rec["version"], round=rnd)
    return {"ok": True, "freeze": rec, "version": rec["version"],
            "enforced": ["sha256 recorded in frags/<key>/spec.frozen.json",
                         "file mode 0444",
                         "path on LEANSILICON_READONLY for every D session; common/confine.py "
                         "checks deny before allow, so the file is unreachable rather than "
                         "merely protected"],
            "limits": ("chmod and a hook are circumventable in principle; the hash is what "
                       "says whether they were circumvented in fact.  It is re-checked at every "
                       "step boundary from here on, and a run whose specification moved is void "
                       "rather than degraded.")}


def step_impl(run: Run, inp: dict, rnd: int) -> dict:
    """D writes an implementation against the frozen specification, or challenges it."""
    res = _author(run, "impl", rnd, done=lambda: _missing_impl(run),
                  made=lambda: os.path.isfile(two_author.frag(run.ws, run.key, "impl")))
    got = _snapshot(run, rnd, "impl", "impl")
    ch = two_author.challenge(run.ws, run.key)
    fz = two_author.freeze_intact(run.ws, run.key)
    notes = _notes(run, "impl")

    if ch and not ch.get("malformed") and not ch.get("incomplete"):
        # A challenge is a legitimate terminal state for this round, and it is `ok=False` on
        # purpose: `Chain.run` stops at the first step that does not succeed, which is exactly
        # what should happen — steps 05..08 of a challenged round are about an implementation
        # that is being thrown away.  The round seam reads this document anyway; `_input` does
        # not gate the handoff on `ok`, for this case.
        return {"ok": False, "problems": ["D challenged the frozen specification"],
                "session": res, "authored": got, "challenge": ch, "notes": notes,
                "next": "round %d: S rewrites the specification with this challenge as a "
                        "directive, and D's work here is discarded" % (rnd + 1)}

    problems = []
    if not fz["intact"]:
        problems.append("FREEZE BROKEN — " + fz["why"])
    if not got:
        problems.append("D wrote no frags/%s/impl.lean" % run.key)
    if not two_author.committed(run.ws, run.key, "D"):
        problems.append("D did not commit the implementation")
    if ch:
        problems.append("a challenge file exists but is not usable: "
                        + (ch.get("malformed") or "missing " + ", ".join(ch["incomplete"])))

    # The first of the two artifacts this half produces, taken here because here is the only
    # moment it exists: `frags/<key>/proof.lean` is not written until step 06, so the ordinary
    # full assembly is proof-free right now and will never be again.  See `leanrtl/preproof.py`.
    #
    # Its result is reported and gates nothing — not `ok`, not `problems`.  A measurement that
    # can fail the thing it measures is a measurement that selects the runs it likes, and the
    # whole point of this pair is that the earlier artifact may be the worse one.
    pre = preproof.capture(run.ws, run.key) if got else None

    return {"ok": not problems, "problems": problems, "session": res, "authored": got,
            "freeze": fz, "challenge": None, "notes": notes,
            "preproof": pre,
            "preproof_note": ("the implementation emitted with no proof in the file.  Paired "
                              "with `out/<key>.v` from step 07, which is the same implementation "
                              "after the proof phase was allowed to re-encode it; the pair is "
                              "what makes 'the proof changed the design' a checkable claim "
                              "instead of a story told about a single artifact"),
            "assumptions": (notes or {}).get("assumptions", [])}


def step_simdiff(run: Run, inp: dict, rnd: int) -> dict:
    """The cheap check, before the expensive one."""
    r = two_author.simdiff(run.ws, run.key)
    ledger.log(paths.DATA, "simdiff", ws=os.path.basename(run.ws), key=run.key, round=rnd, **r)
    means = {
        "agree": "the implementation matches the frozen specification on every checked vector",
        "diverge": "they disagree.  D read the specification, so this is the implementation's "
                   "bug — which makes it a cheap finding, not evidence about the prose",
        "build_error": "the comparison ran and agreed on every checked vector, but the fragments "
                       "do not elaborate.  A failure, but not a disagreement: the defect is in "
                       "whatever stopped compiling, and `head` names it",
        "ungateable": "out of scope for this gate, not a verdict on either fragment: the design "
                      "carries a memory or a latch and `Module.simulateFast` represents neither "
                      "(no array; and a cycle environment built from `regs` and the inputs only, "
                      "so a latch's Q net reads 0 every cycle).  The run CONTINUES — see "
                      "`two_author.PASSABLE` — because scoring the cycle model's own artifact as "
                      "the implementation's bug is worse than not scoring it.  Validate the "
                      "memory or latch path against the emitted Verilog instead of chasing a "
                      "driver bug that is not there",
        "vacuous": "NOTHING WAS COMPARED.  Not agreement.  A large design once came back at "
                   "`0 checked` because the driver overflowed the stack at runtime and printed "
                   "no verdict line at all",
    }[r["verdict"]]
    ok = r["verdict"] in two_author.PASSABLE
    return {"ok": ok, "problems": [] if ok else [f"simdiff: {r['verdict']}"],
            "verdict": r["verdict"], "checked": r["checked"], "mismatches": r["mismatches"],
            "means": means}


def step_proof(run: Run, inp: dict, rnd: int) -> dict:
    """D proves the implementation refines the frozen specification.

    D may re-encode the implementation to make a proof close — that is a legitimate correction,
    and it is why simdiff is re-run here rather than trusted from step 05.  D may not touch the
    specification, and the freeze check below is what says so about this run rather than about
    the mechanism in general.
    """
    res = _author(run, "proof", rnd, done=lambda: _missing_proof(run))
    got = _snapshot(run, rnd, "proof", "impl", "proof")
    fz = two_author.freeze_intact(run.ws, run.key)
    notes = _notes(run, "proof")

    problems = []
    if not fz["intact"]:
        problems.append("FREEZE BROKEN — " + fz["why"])
    if "proof.lean" not in got:
        problems.append("D wrote no frags/%s/proof.lean" % run.key)

    # Re-run the vector diff unconditionally.  D is permitted to re-encode the implementation
    # here, and an implementation that changed after the gate passed has not been through it.
    again = two_author.simdiff(run.ws, run.key)
    if again["verdict"] == "build_error":
        # Named separately because the sentence below is a claim about the IMPLEMENTATION, and
        # here the implementation is not what broke: the comparison agreed on every vector and
        # the driver still exited non-zero.  Attaching the re-encoding story to this case is how
        # `alu` came to report a spec disagreement it did not have.
        problems.append(f"simdiff after the proof phase: build_error — the comparison agreed on "
                        f"all {again['checked']} checked vectors, but the fragments no longer "
                        f"elaborate.  Read `simdiff_after.head`, not the implementation")
    elif again["verdict"] not in two_author.PASSABLE:
        problems.append(f"simdiff after the proof phase: {again['verdict']} — the implementation "
                        f"was re-encoded into something the frozen specification no longer "
                        f"agrees with")
    return {"ok": not problems, "problems": problems, "session": res, "authored": got,
            "freeze": fz, "simdiff_after": again, "notes": notes,
            "scope_claimed": (notes or {}).get("scope_claimed"),
            "corrections": (notes or {}).get("corrections", []),
            "assumptions": (notes or {}).get("assumptions", [])}


def step_emit(run: Run, inp: dict, rnd: int) -> dict:
    """RTLIL through yosys to Verilog, then the interface gate on what came out.

    Before the gates rather than after, because `undriven_nets` is a check on the emitted file:
    a gate about an artifact cannot run before the artifact exists, and running it anyway
    produces a green row about a design that was never emitted.
    """
    rc, out = _bbf(run, "emit", "--role", "D")
    v = run.path("out", run.key + ".v")
    got = os.path.isfile(v)
    os.makedirs(run.path("scratch"), exist_ok=True)
    with open(run.path("scratch", f"{run.key}.emit.txt"), "w") as f:
        f.write(out)

    iface = None
    if got:
        from leanrtl import iface_conform
        iface = iface_conform.check(run.ws, run.key)
        with open(run.path("out", "iface_conform.json"), "w") as f:
            json.dump(iface, f, indent=1)

    problems = []
    if rc != 0:
        problems.append(f"emit exited {rc}")
    if not got:
        problems.append("no out/%s.v" % run.key)
    return {"ok": not problems, "problems": problems, "rc": rc,
            "verilog": os.path.relpath(v, run.ws) if got else None,
            "bytes": os.path.getsize(v) if got else 0,
            "iface_conform": iface,
            "iface_note": ("the interface check reads the prose and our own Verilog and never "
                           "the testbench: a check that consulted the harness would be scoring "
                           "against the answer key"),
            # This is the SECOND of the two artifacts.  Step 04 emitted the first, before any
            # proof existed; `delta` reads `log/<key>.jsonl` and says whether the implementation
            # section moved in between, which is the difference between "the proof corrected the
            # design" and "the proof was closed against the design as written".  Reported here
            # rather than left to be inferred from two Verilog files, because two files that
            # differ do not say WHY, and two that agree do not say the proof was idle.
            "preproof_pair": {"earlier": f"out/{run.key}.{preproof.TAG}.v",
                              "later": f"out/{run.key}.v",
                              "correction": preproof.delta(run.ws, run.key)},
            "tail": out[-1500:] if problems else ""}


def step_certify(run: Run, inp: dict, rnd: int) -> dict:
    """Every gate the profile declares, and then the question the gates cannot ask.

    The gates say the proof is sound.  `proof_mutation` asks whether it is about anything: a
    theorem that holds no matter what the implementation says is a true theorem and an empty
    one, and nothing else in this pipeline is looking for that.

    `run.mutation` turns that second question off.  It is a measurement, not a gate — nothing
    downstream reads it and no `ok` depends on it — so a sweep that only wants the artifacts can
    skip it and keep the certification unchanged.  Skipping writes no `out/proof_mutation.json`,
    which is what makes the omission legible: the report's mutation column reads the file, and a
    missing file is `—` rather than a zero that would look like a proof that caught nothing.
    """
    if not verify_mod.reassemble(run.ws, run.key):
        return {"ok": False, "problems": ["could not assemble from the current fragments"]}
    gates = run.gates
    rec = verify_mod.verify(run.ws, run.key, gates)
    with open(run.path("verify.json"), "w") as f:
        json.dump({"profile": run.profile, "gates": gates, "key": run.key, "design": rec},
                  f, indent=1)
    ledger.log(paths.DATA, "certify", ws=os.path.basename(run.ws), key=run.key, round=rnd,
               all_pass=bool(rec.get("all_pass")),
               failed=[k for k, v in rec.items()
                       if isinstance(v, dict) and v.get("pass") is False])

    mut = None
    if rec.get("all_pass") and run.mutation:
        from leanrtl import proof_mutation
        mut = proof_mutation.mutate(run.ws, run.key)
        with open(run.path("out", "proof_mutation.json"), "w") as f:
            json.dump(mut, f, indent=1)

    fz = two_author.freeze_intact(run.ws, run.key)
    problems = [] if rec.get("all_pass") else [
        "gate failed: " + k for k, v in rec.items()
        if isinstance(v, dict) and v.get("pass") is False] or [rec.get("detail", "not all gates "
                                                                      "passed")]
    if not fz["intact"]:
        problems.insert(0, "FREEZE BROKEN — " + fz["why"])
    return {"ok": not problems, "problems": problems,
            "verdict": rec, "line": verify_mod.line(rec),
            "proof_mutation": mut, "freeze": fz,
            "scope": ("`proof_scope` is descriptive, not a gate.  It lists what the proof does "
                      "not reach, and an L1-only design is a smaller claim rather than a "
                      "failure — reading it as a verdict is how a narrow proof gets read as a "
                      "broad one.")}


STEPS: list[steps_mod.Step] = [
    steps_mod.Step(0, "input", "The natural-language specification this run is about",
                   step_input),
    steps_mod.Step(1, "contract", "The interface, derived from the prose", step_contract),
    steps_mod.Step(2, "spec", "S writes the executable specification", step_spec,
                   sealed=False,
                   why_open="this step spawns an authoring session, which is the one door out "
                            "of this half; everything else here is a deterministic function of "
                            "files on disk",
                   authored=("spec.lean",)),
    steps_mod.Step(3, "freeze", "The specification is frozen", step_freeze),
    steps_mod.Step(4, "impl", "D writes the implementation, or challenges the specification",
                   step_impl, sealed=False,
                   why_open="this step spawns an authoring session",
                   # Declared as a glob rather than in `authored` so that an ABSENT `impl.lean` is
                   # not an error.  This step has two legal endings and only one of them writes a
                   # file: on the challenge route D writes `notes/<key>.challenge.json` and stops,
                   # and `authored()` raises `FileNotFoundError` on a missing name, which would
                   # turn the challenge into a crash in the one step that is supposed to produce
                   # it.  `authored_glob` returns `{}` instead.
                   authored_glob=("impl.lean",)),
    steps_mod.Step(5, "simdiff", "The executable specification against the implementation",
                   step_simdiff),
    steps_mod.Step(6, "proof", "D proves the implementation refines the specification",
                   step_proof, sealed=False,
                   why_open="this step spawns an authoring session",
                   authored=("proof.lean",),
                   # And again here, because proof is allowed to CORRECT the implementation: step
                   # 06's `corrections` field exists for exactly that, and the bytes the proof is
                   # about are therefore not always the bytes step 04 left behind.  Hashing it in
                   # both places is what makes a correction visible as a change of hash rather
                   # than as a silent overwrite.
                   authored_glob=("impl.lean",)),
    steps_mod.Step(7, "emit", "RTLIL to Verilog, and the interface gate", step_emit),
    steps_mod.Step(8, "certify", "Every gate this profile declares, and proof mutation",
                   step_certify),
]

BY_N = {s.n: s for s in STEPS}
LAST = max(BY_N)


def chain(run: Run) -> steps_mod.Chain:
    return steps_mod.Chain(ctx=run, dir=run.ws, name=f"{run.profile}/{run.key}/{run.arm}",
                           steps=STEPS, handoff=HANDOFF, root=paths.DATA)


# ------------------------------------------------------------------------------- the CLI

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ws", required=True)
    ap.add_argument("--first", type=int, default=0)
    ap.add_argument("--last", type=int, default=LAST)
    ap.add_argument("--round", type=int, default=1)
    a = ap.parse_args(argv)
    ws = os.path.abspath(os.path.expanduser(a.ws))
    run = Run.load(ws)

    print(f"{run.profile}/{run.key} · arm `{run.arm}` · round {a.round}")
    docs = chain(run).run(a.first, a.last, a.round, say=print)
    if not docs:
        print("  (no steps in that range)")
        return 0
    last = docs[-1]
    if last["ok"]:
        return 0
    ch = (last.get("produced") or {}).get("challenge")
    if ch:
        print(f"\nround {a.round} ends in a CHALLENGE, which is a result and not an error.\n"
              f"  quote: {ch.get('quote', '')[:160]}\n"
              f"  why:   {ch.get('why', '')[:160]}\n"
              f"Run round {a.round + 1} to rewrite the specification against it.")
        return 4
    return 3


if __name__ == "__main__":
    sys.exit(main())
