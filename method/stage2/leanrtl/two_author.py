#!/usr/bin/env python3
"""The two-author state machine: who runs next, what they are told, and what freezes between them.

    python3 -m leanrtl.two_author --ws <workspace> --key <design> status
    python3 -m leanrtl.two_author --ws <workspace> --key <design> prompt spec|impl|proof
    python3 -m leanrtl.two_author --ws <workspace> --key <design> freeze
    python3 -m leanrtl.two_author --ws <workspace> --key <design> gate
    python3 -m leanrtl.two_author --ws <workspace> --key <design> challenge

This module does not spawn agents.  It owns the part that must not drift between runs — the
order, the prompts, and the freeze — and hands the prompt to whatever is orchestrating.  Keeping
the prompts here rather than in the orchestrator is deliberate: a run whose role prompts were
improvised is not the same experiment as the last one, and the difference is invisible in the
results.

## The pipeline

    contract  ->  S writes spec  ->  [FREEZE]  ->  D writes impl  ->  simdiff  ->  D proves
                       ^                                                             |
                       +------------------- challenge.json --------------------------+

The contract is derived (`leanrtl/contract.py`), not authored.  S reads the prose and writes an
executable `BitVec` specification.  It is then frozen — `chmod 0444`, its hash recorded, and its
path put on the confinement hook's read-only list — and D writes an implementation against it and
proves the implementation refines it.

## Why serial, and what that gave up

The shape this replaces ran the specification author and the implementation author CONCURRENTLY
and blind to each other, so that a disagreement between their artifacts was evidence about the
*prose* rather than about either of them.  That was a good instrument when the prose arrived
unexamined.  leanSpec answers the ambiguity question upstream now, on the document itself, with a
separating stimulus attached to each finding — which is strictly more than "two readers read it
differently and one of them is wrong somewhere".

What was given up is real and worth naming: the blind pair produced ONE signal a serial pair
cannot, and simdiff was its detector.  Here simdiff still runs and still writes the same four
verdicts, but it means something weaker — a cheap deterministic self-check before an expensive
proof.  D read the specification, so a divergence is D's bug and not the document's.

The other thing given up is that the prover no longer writes only against two formal artifacts.
When R and P were separate, P never read the prose, so P could not resolve a spec/impl
disagreement by deciding what the design *ought* to do.  D can.  Nothing here catches that; what
catches it is that D cannot touch the specification, so the only thing D can bend is the
implementation — and bending the implementation to make a proof close is a legitimate move that
simdiff re-checks.

## What the freeze is, exactly

Three things, and the third is the one that matters:

  1. the file's sha256 is recorded in `frags/<key>/spec.frozen.json`;
  2. the file is made read-only;
  3. its path goes on `LEANSILICON_READONLY`, which `common/confine.py` refuses every write to
     while leaving every read through — D implements against this file, so it must be readable.

(1) and (2) are detection and friction.  An agent can `chmod` a file back, and a hash is only
read by whoever thinks to read it.  (3) is the wall: it runs before the tool call, so a file
inside the directory the agent otherwise owns becomes one it can open and cannot save.

The wall is a WRITE wall and not a read wall, and that is the single substantive difference from
the blind-parallel mode this replaced.  There, the same file was unreachable, because the
implementer was not supposed to have seen the specification at all.  Here the implementer's task
is defined against it.  Carrying the old list over unchanged — which is what happened the first
time — hands D a target it cannot read and a phase it cannot start.

## The challenge route

D may not edit the specification.  If D believes it is wrong, D writes
`notes/<key>.challenge.json` — a quote, a reason, and a counterexample trace — and stops.  The
orchestrator sends the specification back to S with the challenge as a directive, the version
advances, and D's work is discarded.  There is no adjudicator: adjudication answered "which of
two blind readings does the prose support", and there are no longer two blind readings.

The decided prose is treated as unconditionally authoritative.  A challenge never re-opens the
specification-checking half — that half ran on the document, alone, and this half is not allowed
to know it exists.
"""
from __future__ import annotations

import argparse
import datetime
import json
import os
import re
import stat
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

from common import agent, ledger, paths                                             # noqa: E402

FROZEN = "spec.frozen.json"


# --------------------------------------------------------------------------------- the roles

def role_S(ws: str, key: str) -> agent.Role:
    """S may write anywhere in the workspace it is told to; nothing is denied.

    In particular the prose is READ by S and is not on any deny list.  S is the only author whose
    job is to read English.
    """
    return agent.Role(tag="S", tools=(*agent.BASE_TOOLS, *agent.LEAN_TOOLS))


def role_D(ws: str, key: str) -> agent.Role:
    """D gets the simulator binaries, and gets the specification to read but not to change.

    The two lists are doing different jobs.  `readonly` carries the frozen fragment: D's task in
    both phases is defined against that file — implement it, then prove the implementation
    refines it — so it has to be readable, and the freeze is that it cannot be written.  This is
    the one place the serial mode differs from the blind-parallel mode it replaced, where the
    same file was on `deny` because the implementer was not supposed to have seen it at all.

    `deny` carries the freeze RECORD, which stays unreadable.  It holds the hash, and an agent
    that can read the hash can check whether an edit was noticed.  That is not a threat model
    about a dishonest agent so much as about a persistent one — a loop that can see whether a
    change registered will eventually find the change that does not.
    """
    return agent.Role(
        tag="D",
        tools=(*agent.BASE_TOOLS, *agent.LEAN_TOOLS, *agent.SIM_TOOLS),
        readonly=(os.path.join(ws, "frags", key, "spec.lean"),),
        deny=(os.path.join(ws, "frags", key, FROZEN),))


# ------------------------------------------------------------------------------ the prompts

COMMON = """You are author {role} on design `{key}` in the workspace {ws}.

Read your role card `{ws}/ROLE_{role}.md` first and follow it exactly; it defines what you may
read, what you may write, and the JSON block you must end with.  `{ws}/AGENT.md` is the
workspace manual and `{ws}/docs/dsl-reference.md` is the language reference.  Accumulated
lemmas and patterns are under `{ws}/assets/` — the design names in them have been redacted,
which is expected.

Hard rules, which override anything else you infer:
{rules}

Two traps in this toolchain, which cost earlier runs a round each.  They apply to any Lean you
write, specification or implementation or proof:

  * **`bv_decide` is not kernel-checked here.**  It emits a per-theorem axiom
    (`<thm>._native.bv_decide.ax_N_M`) that the kernel trusts rather than verifies, and it
    propagates to everything that uses the lemma.  `bb.py audit` stays green and there is no
    `sorry` in the source — only `#print axioms` sees it, and the `axiom_clean` gate fails the
    whole design over it, including the other author's work.  For a small finite enumeration use
    `revert x; decide`, which is kernel-checked.  `decide` needs a CLOSED goal: `by decide` under
    a free variable errors, and an ignored error there silently yields `sorryAx`.
  * **`simp` renormalises BitVec literals** — `(0 : BitVec 1)` becomes `0#1` — so a
    `by_cases h : x = 0` hypothesis silently stops matching afterwards.  Enumerate the value
    instead of case-splitting on the proposition.

This workspace has no dependencies at all, so Mathlib tactics are absent: `interval_cases` and
friends do not exist.  Use an explicit `match`, `omega`, or `decide`.

Also write your closing JSON block verbatim to `{ws}/notes/{key}.{role}.{phase}.json` — the same
object, nothing added.  A report cannot count what only exists in a chat reply.  D writes twice,
once per phase, and the two files are kept apart because the implementation phase's assumptions
are not the proof phase's and a single file would silently keep only the later ones.

Everything you need is inside {ws}.  Do not read, list, or search anything outside it — not
this repository, not other workspaces, not the network.  If you believe you need something
outside, say so in your notes and stop; a run that reaches outside is void and gets thrown
away, which costs more than an honest incomplete answer.
"""

RULES = """  * Argue from the prose you were given.  If it does not determine something, record the
    reading you took in your notes and pick the one the text best supports — do not import what a
    reference implementation would "obviously" do.
  * A property the prose states about the whole design is an obligation, not a comment.
  * `contracts/{key}.json` is fixed.  It was derived from the prose mechanically, not written by
    anyone, and every port name and width in it is binding: the two halves of this design are
    compared through those names and nothing else."""

PHASES = {
    "spec": ("S", "the formal specification",
             "Write `frags/{key}/spec.lean` per your role card.  Check it with\n"
             "`python3 scripts/bbf.py {key} build --frag spec --role S`, then commit with\n"
             "`python3 scripts/bbf.py {key} commit --role S`.\n\n"
             "What you write is FROZEN the moment you commit it.  An implementation is then built\n"
             "against it and proved correct with respect to it, and neither step can revise it.\n"
             "So it has to be the specification you would defend, not a first draft: state the\n"
             "behaviour the prose gives, choose explicitly where the prose leaves a choice, and\n"
             "write down which choice you made."),
    "impl": ("D", "the implementation",
             "Write `frags/{key}/impl.lean` per your role card, against the prose and against\n"
             "`frags/{key}/spec.lean`, which is frozen and read-only.  Check it with\n"
             "`python3 scripts/bbf.py {key} build --frag impl --role D`, self-simulate with\n"
             "`python3 scripts/bbf.py {key} sim --role D`, then commit with\n"
             "`python3 scripts/bbf.py {key} commit --role D`.\n\n"
             "If you conclude the specification contradicts the prose, do not work around it:\n"
             "write `notes/{key}.challenge.json` with a quote, a reason and a concrete\n"
             "counterexample trace, and stop."),
    "proof": ("D", "the proofs",
              "Write `frags/{key}/proof.lean` per your role card: L1 laws per register and per\n"
              "output, then the whole-trace climb for a sequential design.  Zero `sorry`.\n"
              "`python3 scripts/bbf.py {key} build --role D` after every edit; finish with\n"
              "`python3 scripts/bbf.py {key} emit --role D`, which must succeed.\n\n"
              "You may re-encode `frags/{key}/impl.lean` when a proof needs it; after ANY such\n"
              "edit run `python3 scripts/bbf.py {key} simdiff --role D` and it must stay green.\n"
              "`SIMDIFF-UNGATEABLE` is not red: this design carries a memory or a latch, which\n"
              "the whole-design cycle model does not represent, so the gate declines to run\n"
              "rather than failing you.  Do not reshape the implementation to make it score --\n"
              "a latch rewritten as a self-holding register scores green and emits a flip-flop\n"
              "whose clock is a constant.  Prove the per-element law instead.\n"
              "You may not edit the specification — the file is read-only and denied to you at\n"
              "the tool layer, so an attempt fails rather than silently succeeding.{evidence}"),
}

REDO = """

--- THIS IS A RE-RUN.  The specification you were given last time was CHALLENGED. ---

{challenge}

The specification has been rewritten and its version is now {version}.  Your previous work on
this design has been discarded; start from the specification as it stands now, and do not assume
any part of what you wrote before is still valid against it.
"""


# ---------------------------------------------------------------------------------- the freeze

def frag(ws: str, key: str, name: str) -> str:
    return os.path.join(ws, "frags", key, name + ".lean")


def committed(ws: str, key: str, role: str) -> bool:
    return os.path.isfile(os.path.join(ws, "frags", key, role + ".committed"))


def freeze_path(ws: str, key: str) -> str:
    return os.path.join(ws, "frags", key, FROZEN)


def sha_of(path: str) -> str:
    import hashlib
    return hashlib.sha256(open(path, "rb").read()).hexdigest()


def freeze(ws: str, key: str, version: int | None = None) -> dict:
    """Record the hash, make the file read-only, and return the record.

    The deny list is not written here — it is passed per session by `common/agent.py`, from
    `role_D`.  Two mechanisms for one rule would be one mechanism and one comment about it.
    """
    p = frag(ws, key, "spec")
    if not os.path.isfile(p):
        raise FileNotFoundError(f"two_author: nothing to freeze — {os.path.relpath(p, ws)} does "
                                f"not exist.  S has not committed.")
    prev = read_freeze(ws, key)
    rec = {"path": os.path.relpath(p, ws),
           "sha256": sha_of(p),
           "version": version if version is not None else ((prev or {}).get("version", 0) + 1),
           "at": datetime.datetime.now().astimezone().isoformat(timespec="seconds"),
           "bytes": os.path.getsize(p),
           "supersedes": (prev or {}).get("sha256"),
           "enforced_by": "chmod 0444, plus this path on LEANSILICON_READONLY for every D session; "
                          "common/confine.py refuses every write to it and lets every read "
                          "through, because D implements against this file.  Only the sha256 "
                          "above DETECTS a change; the other two layers obstruct one"}
    os.chmod(p, stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
    fp = freeze_path(ws, key)
    if os.path.isfile(fp):
        os.chmod(fp, stat.S_IRUSR | stat.S_IWUSR)
    with open(fp, "w") as f:
        json.dump(rec, f, indent=1)
    os.chmod(fp, stat.S_IRUSR | stat.S_IRGRP | stat.S_IROTH)
    return rec


def unfreeze(ws: str, key: str, why: str) -> dict:
    """Make the specification writable again, on the record.

    The ONE legitimate caller is a new round after a challenge: S is being asked to rewrite the
    document, and a document that cannot be rewritten cannot be revised.  It is a function with a
    mandatory reason and a ledger row rather than a `chmod` in a step body, because the freeze is
    what every claim after it rests on and "who unfroze it and why" has to be answerable from the
    record alone.

    The previous record is kept as `supersedes` on the next freeze, so a two-version run shows
    both hashes and neither is silently replaced.
    """
    p = frag(ws, key, "spec")
    prev = read_freeze(ws, key)
    if os.path.isfile(p):
        os.chmod(p, stat.S_IRUSR | stat.S_IWUSR | stat.S_IRGRP | stat.S_IROTH)
    ledger.log(paths.DATA, "spec_unfrozen", ws=os.path.basename(ws), key=key, why=why,
               was=(prev or {}).get("sha256"), version=(prev or {}).get("version"))
    return {"unfroze": (prev or {}).get("sha256"), "why": why,
            "version_was": (prev or {}).get("version")}


def read_freeze(ws: str, key: str) -> dict | None:
    p = freeze_path(ws, key)
    if not os.path.isfile(p):
        return None
    try:
        return json.load(open(p))
    except ValueError:
        return None


def freeze_intact(ws: str, key: str) -> dict:
    """Whether the frozen specification is still the one that was frozen.

    Checked at every phase boundary and again at certification.  A `chmod` and a hook are both
    circumventable in principle — the hash is what says whether they were circumvented in
    fact, and a run whose specification changed under it is void, not degraded.
    """
    rec = read_freeze(ws, key)
    if rec is None:
        return {"frozen": False, "intact": None, "why": "no freeze record"}
    p = frag(ws, key, "spec")
    if not os.path.isfile(p):
        return {"frozen": True, "intact": False, "version": rec["version"],
                "why": "the frozen file has been DELETED"}
    now = sha_of(p)
    mode = stat.S_IMODE(os.stat(p).st_mode)
    return {"frozen": True, "intact": now == rec["sha256"], "version": rec["version"],
            "sha256": rec["sha256"], "now": now,
            "writable": bool(mode & (stat.S_IWUSR | stat.S_IWGRP | stat.S_IWOTH)),
            "why": "" if now == rec["sha256"] else
                   "the specification has been MODIFIED since it was frozen.  Every proof in this "
                   "workspace is about a document that no longer exists, and the run is void — "
                   "not weaker, void.  Re-freeze deliberately and restart D, or restore the file."}


# ----------------------------------------------------------------------------- the state machine

def challenge(ws: str, key: str) -> dict | None:
    p = os.path.join(ws, "notes", f"{key}.challenge.json")
    if not os.path.isfile(p):
        return None
    try:
        c = json.load(open(p))
    except ValueError as e:
        return {"malformed": str(e), "path": os.path.relpath(p, ws)}
    missing = [k for k in ("quote", "why", "counterexample_trace") if not c.get(k)]
    if missing:
        # Reported rather than rejected.  A challenge is expensive — it costs S a rewrite and D
        # its whole run — so an incomplete one should come back to its author, not be silently
        # honoured or silently dropped.
        c["incomplete"] = missing
    return c


#: The simdiff verdicts a run may continue past.  `agree` is the gate passing.  `ungateable` is
#: the gate declining to run at all, which is a different thing from either passing or failing it
#: and has to be treated as a third case rather than folded into one of the two.
#:
#: Folding it into failure is what this constant exists to undo.  Every non-`agree` verdict used
#: to stop the run, so a design whose only defect was being outside the cycle model was reported
#: with the same words as one whose implementation contradicts its specification.
#: `verilogeval/Prob028_m2014_q4a` is the measured cost: a transparent latch, `SIMDIFF-FAIL
#: mismatches=80 checked=160` produced entirely by `Module.simulateFast` reading the latch's Q
#: net as 0, and an emitted `always @* if (ena) q = d;` that is the reference circuit and scores
#: `func_pass` with 0 mismatches on 100 samples.  See `authoring/simdiff_f.py`'s latch guard.
#:
#: This is a REAL WEAKENING and is not hidden.  There is no `simdiff` key in `verify.verify()` --
#: the six gates it computes are unchanged and every one of them still has to pass -- so nothing
#: here turns a gate green; what it does is let a design reach those gates without the cheap
#: dynamic pre-check.  The verdict is written to `simdiff/<key>.json` and printed in the run
#: summary either way, so "this design was never vector-checked" is on the face of the record.
#: What pins a latch instead is `Latch.den` in the proof, which `proves_impl` / `zero_sorry` /
#: `axiom_clean` do still gate.  `bb cosim` cannot stand in for it: the whole-design co-simulator
#: compares against `Module.simulate`, which is the same Moore model, and `Core/Syntax.lean:262`
#: says so ("`bb cosim` therefore CANNOT validate a latch-carrying design").
PASSABLE = ("agree", "ungateable")


def simdiff(ws: str, key: str) -> dict:
    """The deterministic gate: the specification's executable form against the implementation.

    160 cycles of seeded pseudo-random stimulus through both.  Five verdicts, and the three that
    are not pass/fail are the point of it:

      agree       they match on every checked vector
      diverge     they do not.  With serial authoring this is the implementation's bug — D read
                  the specification — so it is a cheap finding, not evidence about the prose.
      build_error the comparison RAN and agreed, but the driver exited non-zero because something
                  in the fragments no longer elaborates.  Still a failure — nothing may certify on
                  fragments that do not compile — but it is not a disagreement, and calling it one
                  sends the reader after a bug that is not there.  `alu` failed exactly this way:
                  `SIMDIFF-OK checked=960 mismatches=0`, `impl.lean` byte-identical to the one that
                  had just passed at step 05, and the actual defect two unsolved goals in a helper
                  lemma D wrote in `proof.lean`.  It was reported as "the implementation was
                  re-encoded into something the frozen specification no longer agrees with".
      ungateable  the driver is working and this design is outside what it can represent -- a
                  non-empty `mems` (`Module.simulateFast` carries no array) or a non-empty
                  `latches` (it builds its cycle environment from `regs` and the inputs, so a
                  latch's Q net reads 0 every cycle).  Telling the operator to "fix the driver"
                  here sends them after a bug that is not present.
      vacuous     NOTHING was compared.  Not agreement.  A large design once came back as "0
                  checked" because the driver overflowed the stack at runtime, printing no verdict
                  line at all; the only reason it was caught is that this refuses to read an
                  empty comparison as a pass.

    The ordering matters: `build_error` is tested only after `agree`, so a clean run is still a
    clean run, and only the non-zero-exit case is split off the old `else` branch.  Every verdict
    other than `agree` keeps `head`, which is where the elaboration errors are legible.
    """
    r = subprocess.run([sys.executable, os.path.join(ws, "scripts", "bbf.py"),
                        key, "simdiff", "--role", "H"],
                       cwd=ws, capture_output=True, text=True)
    out = r.stdout + r.stderr
    os.makedirs(os.path.join(ws, "scratch"), exist_ok=True)
    open(os.path.join(ws, "scratch", f"{key}.simdiff.txt"), "w").write(out)

    checked = int((re.search(r"checked=(\d+)", out) or [0, 0])[1] or 0)
    mism = int((re.search(r"mismatches=(\d+)", out) or [0, 0])[1] or 0)
    if "SIMDIFF-UNGATEABLE" in out:
        verdict = "ungateable"
    elif "SIMDIFF-VACUOUS" in out or (checked == 0 and "SIMDIFF-OK" not in out):
        verdict = "vacuous"
    elif "SIMDIFF-OK" in out and r.returncode == 0:
        verdict = "agree"
    elif "SIMDIFF-OK" in out:
        verdict = "build_error"
    else:
        verdict = "diverge"
    res = {"verdict": verdict, "checked": checked, "mismatches": mism,
           "head": out.strip()[-400:] if verdict != "agree" else ""}
    os.makedirs(os.path.join(ws, "simdiff"), exist_ok=True)
    json.dump(res, open(os.path.join(ws, "simdiff", f"{key}.json"), "w"), indent=1)
    return res


def state(ws: str, key: str) -> dict:
    fz = freeze_intact(ws, key)
    sd = os.path.join(ws, "simdiff", key + ".json")
    return {
        "contract": os.path.isfile(os.path.join(ws, "contracts", key + ".json")),
        "spec": os.path.isfile(frag(ws, key, "spec")),
        "S_committed": committed(ws, key, "S"),
        "frozen": fz["frozen"], "freeze_intact": fz["intact"],
        "spec_version": fz.get("version"),
        "impl": os.path.isfile(frag(ws, key, "impl")),
        "D_committed": committed(ws, key, "D"),
        "simdiff": (json.load(open(sd)).get("verdict") if os.path.isfile(sd) else None),
        "proof": os.path.isfile(frag(ws, key, "proof")),
        "challenged": challenge(ws, key) is not None,
        "emitted": os.path.isfile(os.path.join(ws, "out", key + ".v")),
    }


def next_phase(st: dict) -> str:
    if st["frozen"] and st["freeze_intact"] is False:
        return "VOID — the frozen specification has changed"
    if not st["contract"]:
        return "contract (python3 -m leanrtl.contract)"
    if not (st["spec"] and st["S_committed"]):
        return "spec (S)"
    if not st["frozen"]:
        return "freeze"
    if st["challenged"]:
        return "spec (S) — re-run: D challenged the specification"
    if not st["impl"]:
        return "impl (D)"
    if st["simdiff"] is None:
        return "gate"
    if st["simdiff"] != "agree":
        if st["simdiff"] in PASSABLE:
            # Not D's move.  The gate declined; the design goes on to the proof, which is the
            # only thing that pins it.
            return "proof (D)" if not st["proof"] else (
                "done" if st["emitted"] else "proof (D) — emit outstanding")
        return f"impl (D) — simdiff came back `{st['simdiff']}`"
    if not st["proof"]:
        return "proof (D)"
    return "done" if st["emitted"] else "proof (D) — emit outstanding"


def prompt(ws: str, key: str, phase: str, ch: dict | None = None) -> str:
    """The prompt for one phase.  `ch` overrides the challenge read from disk.

    The override exists because the caller archives `notes/<key>.challenge.json` before starting
    the round that answers it — leaving it in place would make the new round read as challenged
    from the moment it began — and the prompt still has to carry it.
    """
    role, what, task = PHASES[phase]
    ev = ""
    if phase == "proof":
        p = os.path.join(ws, "scratch", f"{key}.simdiff.txt")
        if os.path.isfile(p):
            ev = ("\n\nThe deterministic self-check has already run on your implementation; its "
                  "output is\nin `scratch/" + key + ".simdiff.txt`.")
    body = (COMMON.format(role=role, key=key, ws=ws, phase=phase, rules=RULES.format(key=key))
            + f"\nYour task ({what}):\n" + task.format(key=key, evidence=ev) + "\n")
    ch = ch if ch is not None else challenge(ws, key)
    if phase == "spec" and ch and not ch.get("malformed"):
        body += REDO.format(challenge=json.dumps(ch, indent=1),
                            version=(read_freeze(ws, key) or {}).get("version", 0) + 1)
    return body


# ------------------------------------------------------------------------------------- the CLI

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ws", required=True)
    ap.add_argument("--key", required=True)
    ap.add_argument("action", choices=["status", "prompt", "freeze", "check-freeze", "gate",
                                       "challenge"])
    ap.add_argument("phase", nargs="?", choices=list(PHASES))
    a = ap.parse_args(argv)
    ws = os.path.abspath(os.path.expanduser(a.ws))

    if a.action == "status":
        st = state(ws, a.key)
        for k, v in st.items():
            print(f"  {k:16} {'—' if v is None else v}")
        print(f"  {'next':16} {next_phase(st)}")
        return 0

    if a.action == "prompt":
        if not a.phase:
            sys.exit("two_author: prompt needs a phase (spec|impl|proof)")
        st = state(ws, a.key)
        if not st["contract"]:
            sys.exit("two_author: derive the contract first — both authors are compared through "
                     "its port names, so neither can start without it")
        if a.phase in ("impl", "proof") and not st["frozen"]:
            sys.exit("two_author: the specification is not frozen.  D runs against a frozen "
                     "specification or not at all; an unfrozen one is a document D can edit, and "
                     "then the proof is about whatever the two converged on rather than about "
                     "the design.")
        if st["frozen"] and st["freeze_intact"] is False:
            sys.exit("two_author: " + freeze_intact(ws, a.key)["why"])
        if a.phase == "proof" and st["simdiff"] not in PASSABLE:
            sys.exit(f"two_author: simdiff is `{st['simdiff']}` — proving an implementation that "
                     f"the specification's own executable form disagrees with is an hour spent "
                     f"discovering the same thing more expensively")
        print(prompt(ws, a.key, a.phase))
        return 0

    if a.action == "freeze":
        rec = freeze(ws, a.key)
        ledger.log(paths.DATA, "spec_frozen", ws=os.path.basename(ws), key=a.key,
                   sha256=rec["sha256"], version=rec["version"])
        print(f"two_author: frozen `{rec['path']}` at version {rec['version']}\n"
              f"  sha256 {rec['sha256']}\n"
              f"  {rec['bytes']} bytes, mode 0444\n"
              f"  {rec['enforced_by']}")
        return 0

    if a.action == "check-freeze":
        r = freeze_intact(ws, a.key)
        if not r["frozen"]:
            print("two_author: not frozen")
            return 1
        if r["intact"]:
            print(f"two_author: freeze intact — version {r['version']}, sha {r['sha256']}"
                  + ("  (WARNING: the file is writable again — the hash still matches, so "
                     "nothing has been lost, but the friction is gone)" if r["writable"] else ""))
            return 0
        print("two_author: FREEZE BROKEN\n  " + r["why"])
        ledger.log(paths.DATA, "freeze_broken", ws=os.path.basename(ws), key=a.key,
                   was=r.get("sha256"), now=r.get("now"))
        return 3

    if a.action == "gate":
        r = simdiff(ws, a.key)
        print(open(os.path.join(ws, "scratch", f"{a.key}.simdiff.txt")).read()[-1200:])
        print(f"\nsimdiff: {r['verdict']} · {r['checked']} checked"
              + (f" · {r['mismatches']} mismatches" if r["mismatches"] else ""))
        print({"agree": "  the implementation matches the frozen specification on every checked "
                        "vector — D may start proving",
               "diverge": "  they disagree.  D read the specification, so this is the "
                          "implementation's bug; fix the implementation, never the specification",
               "build_error": "  the comparison agreed on every vector — the fragments do not "
                              "COMPILE.  Fix the elaboration errors above; the implementation is "
                              "not the suspect.",
               "ungateable": "  OUT OF SCOPE for this gate, not a verdict on either fragment.  "
                             "Validate the memory path against the emitted Verilog instead.",
               "vacuous": "  NOTHING WAS COMPARED.  Not agreement — fix the driver before "
                          "reading anything into this design"}[r["verdict"]])
        ledger.log(paths.DATA, "simdiff", ws=os.path.basename(ws), key=a.key, **r)
        return 0 if r["verdict"] == "agree" else 1

    c = challenge(ws, a.key)
    if c is None:
        print("two_author: no challenge")
        return 1
    print(json.dumps(c, indent=1))
    if c.get("malformed"):
        print("\ntwo_author: the challenge file is not valid JSON.  It is not honoured and it is "
              "not discarded — send it back to D.")
        return 2
    if c.get("incomplete"):
        print(f"\ntwo_author: this challenge is missing {', '.join(c['incomplete'])}.  A challenge "
              f"costs S a rewrite and costs D its whole run, so an incomplete one goes back to D "
              f"rather than through.")
        return 2
    print(f"\ntwo_author: valid.  Re-run S with this as a directive; the specification version "
          f"becomes {(read_freeze(ws, a.key) or {}).get('version', 0) + 1} and D restarts.")
    return 0


if __name__ == "__main__":
    sys.exit(main())
