#!/usr/bin/env python3
"""The one place this framework starts an agent.

There used to be four.  `launch.py` ran the design authors, `three_role.py` shaped their
prompts, the spec-check driver ran the spec authors, and a rerun tool ran a fourth variant —
each with its own `subprocess.run(["claude", "-p", ...])`, its own timeout, its own idea of
where a transcript goes, and its own answer to whether the confinement hook was installed.
Three of the four did not install it.  That is not a thing to fix in three places.

So: one call site, and the wall is not optional.  `run()` always writes a settings file wiring
`common/confine.py` in as a `PreToolUse` hook and always sets the environment the hook reads.
There is no parameter that turns it off; an unconfined session is produced by editing this
file, which is a diff someone reviews.

## What a caller supplies and what it does not

A caller says *who* is running (a `Role`), *where* (a directory), and *what* to ask.  It does
not choose the output format, the permission mode, session persistence, or whether the hook is
installed, because those are properties of how this framework runs agents rather than of any
one role.

## The transcript is the record

Every session writes `stream-json` to a file, and the path comes back on the result.  The
ledger row points at it.  A session whose transcript is missing is reported, never silently
counted as having happened.
"""
from __future__ import annotations

import contextlib
import dataclasses
import json
import os
import subprocess
import sys
import tempfile
import time

HERE = os.path.dirname(os.path.abspath(__file__))
CONFINE = os.path.join(HERE, "confine.py")

# The elan toolchain, which every role needs to run Lean, and nothing else from outside the run.
ELAN = os.path.expanduser("~/.elan")

DEFAULT_TIMEOUT = int(os.environ.get("LEANSILICON_AGENT_TIMEOUT", "3600"))

# Read, search, write, and a shell scoped to the toolchain.  `Bash` is granted per-binary rather
# than wholesale: the confinement hook covers the paths a command names, and this covers which
# commands can name them.  Two walls, because either alone has a hole the other closes — a
# scoped binary can still be pointed outside, and an unscoped shell inside the run can still
# fetch from the network.
#
# A role that can express a path only through a structured file tool can be confined by the hook:
# the complete path is present in the tool input before anything executes.  A shell or interpreter
# is categorically different.  ``echo $(...)`` can launch another command, Python can assemble a
# path a byte at a time, and Lean can execute arbitrary ``IO`` through ``--run``; no regex over the
# literal command can make those safe.  SpecIR therefore uses FILE_TOOLS and performs all Lean and
# simulator execution in its driver, after the model session has ended.
FILE_TOOLS = ("Read", "Glob", "Grep", "Write", "Edit")

# Kept for older methods whose evidence predates the stronger SpecIR boundary.  New roles must opt
# into FILE_TOOLS or a narrowly justified executable set, rather than inheriting these by habit.
BASE_TOOLS = (*FILE_TOOLS, "TodoWrite", "Bash(echo:*)")
LEAN_TOOLS = ("Bash(lake:*)", "Bash(lean:*)", "Bash(python3:*)")
SIM_TOOLS = ("Bash(iverilog:*)", "Bash(vvp:*)", "Bash(yosys:*)")


@dataclasses.dataclass(frozen=True)
class Role:
    """Who is running, and what that permits.

    `tag` names the role in transcripts, ledger rows and step documents — one string, so a
    reader grepping for a role finds every trace of it.

    `deny` and `readonly` are two different walls and the difference matters.  `deny` puts a path
    out of reach in both directions; it is what keeps one half of the pipeline out of the other.
    `readonly` leaves a path readable and refuses writes to it; it is what makes a freeze a
    freeze.  Putting the frozen specification on `deny` instead — which is what the blind-parallel
    mode did, correctly, because there the implementer was not supposed to see it — leaves a
    serial implementer with nothing to implement against.
    """
    tag: str
    tools: tuple[str, ...]
    allow: tuple[str, ...] = ()
    deny: tuple[str, ...] = ()
    readonly: tuple[str, ...] = ()
    # The exact files whose bytes constitute this session's input.  ``readonly`` is an enforcement
    # policy and may include shared library directories; ``inputs`` is the smaller evidentiary set
    # snapshotted before and after the session.  Keeping them separate avoids pretending that a
    # permission list is itself proof that the bytes did not change.
    inputs: tuple[str, ...] = ()
    timeout: int = DEFAULT_TIMEOUT
    # An alias, not a pinned identifier.  Which model a run used is recorded on the ledger row
    # from what the CLI reports, so pinning here would only add a second place to disagree.
    model: str = "opus"


def settings_file(root: str) -> str:
    """A settings file wiring the confinement in, written into the run it governs.

    Beside the transcripts it governed, on purpose: a run whose wall cannot be reconstructed is
    a run whose isolation is a claim.

    Written to a temporary name and renamed, because two sessions sharing a root now start at the
    same moment -- `author.in_parallel` runs three of them -- and `open(p, "w")` truncates before
    it writes.  A session that started in that window would be handed a settings file that is
    zero bytes or half a document, and a settings file the CLI cannot parse is a session with no
    `PreToolUse` hook: the confinement would be off, and nothing in the transcript would say so.
    The content is the same every time, so the rename is between two identical documents; it is
    the truncation that had to go, not a disagreement.
    """
    doc = {"hooks": {"PreToolUse": [{"matcher": "*", "hooks": [
        {"type": "command", "command": f"{sys.executable} {CONFINE}"}]}]}}
    p = os.path.join(root, "logs", "confine.settings.json")
    os.makedirs(os.path.dirname(p), exist_ok=True)
    fd, tmp = tempfile.mkstemp(dir=os.path.dirname(p), prefix=".confine.", suffix=".json")
    try:
        with os.fdopen(fd, "w") as f:
            json.dump(doc, f, indent=1)
        os.replace(tmp, p)
    except BaseException:
        with contextlib.suppress(OSError):
            os.unlink(tmp)
        raise
    return p


def run(role: Role, root: str, prompt: str, transcript: str,
        cwd: str | None = None, extra_env: dict | None = None) -> dict:
    """One agent session.  Returns what happened; never raises for the agent's own failure.

    An agent that fails is a result, not an exception: the pipeline records the rc, the tail of
    stderr and the transcript, and the step that reads its output decides what a missing
    artifact means.  Raising here would lose the transcript of the session that failed, which is
    the only thing that explains why.
    """
    os.makedirs(os.path.dirname(os.path.abspath(transcript)), exist_ok=True)
    _keep(transcript)
    cmd = ["claude", "-p", prompt,
           "--model", role.model,
           "--permission-mode", "acceptEdits",
           "--allowedTools", *role.tools,
           # `allow` has to be granted TWICE, because two independent walls stand in front of it.
           # `LEANSILICON_ALLOW` opens ours; `--add-dir` opens the CLI's own working-directory
           # restriction, which refuses a Read or an `ls` outside the session cwd and reports it
           # in its own words ("may only list files in the allowed working directories").  Grant
           # one and not the other and the path is named by the prompt, permitted by the hook,
           # and still unreachable — which is how the stage 2 author came to spend a session
           # reconstructing an API it was entitled to read.  A role's `allow` is the list of
           # places it was decided the role may reach, so both walls are opened from it and
           # neither can drift from the other.
           *[a for d in role.allow for a in ("--add-dir", d)],
           "--settings", settings_file(root),
           "--output-format", "stream-json", "--verbose",
           "--no-session-persistence"]
    env = dict(os.environ,
               LEANSILICON_ROOT=os.path.realpath(root),
               LEANSILICON_ALLOW=os.pathsep.join([ELAN, *role.allow]),
               LEANSILICON_DENY=os.pathsep.join(role.deny),
               LEANSILICON_READONLY=os.pathsep.join(role.readonly),
               **(extra_env or {}))
    t0 = time.time()
    errfile = os.path.splitext(transcript)[0] + ".stderr"
    try:
        with open(transcript, "w") as tf, open(errfile, "w") as ef:
            p = subprocess.Popen(cmd, cwd=cwd or root, stdout=tf, stderr=ef, text=True, env=env)
            rc, how = _supervise(p, transcript, role.timeout, t0)
    except FileNotFoundError:
        rc, how = -2, "no-cli"
    err = _tail(errfile) if how != "no-cli" else "the `claude` CLI is not on PATH"
    return {"role": role.tag, "rc": rc, "how": how, "stderr": err,
            "elapsed": round(time.time() - t0, 1),
            "transcript": os.path.abspath(transcript),
            "session_error": session_error(transcript),
            "denied": denied_calls(transcript),
            "refusals": refusals(transcript)}


#: How many consecutive `api_retry` events, with no work in between, before a session is declared
#: dead.  The CLI retries with exponential backoff, so by the fourth the waits are in the tens of
#: seconds and each one is re-sending the same long request into the same fault.  Four is where
#: the evidence says recovery has stopped happening; below that, sessions do come back.
STORM = int(os.environ.get("LEANSILICON_STORM", "4"))

#: How long a transcript may stop growing before the session is declared dead, in seconds.
#:
#: This is the rule that catches the failure the retry counter misses.  A session in trouble emits
#: `api_retry` two or three times and then stops emitting ANYTHING — no further retry, no error,
#: no exit — and sits there until its timeout.  Counting retries never reaches four, so the count
#: alone would have watched an hour of silence and called it a session.
#:
#: Silence is a better signal than retries because a working session is never silent for long: a
#: turn in progress ticks `thinking_tokens` every few seconds, and the only real gap is between a
#: tool call and its result.  Seven minutes is far longer than anything this framework asks an
#: agent to run — `lean` on a six-hundred-line file is seconds — and is deliberately generous, so
#: that a slow tool is never mistaken for a dead session.
STALL = int(os.environ.get("LEANSILICON_STALL", "420"))

#: How often the supervisor looks at the transcript, in seconds.
POLL = 10.0


def _supervise(p: subprocess.Popen, transcript: str, timeout: int, t0: float) -> tuple[int, str]:
    """Wait for a session, ending it early when it has stopped working.

    A session that starts retrying does not come back.  Across the sessions that brought this
    repository up, `api_retry` climbed to attempt 3, 4 and 5 and never once produced another tool
    call afterwards — the composition turn is long, the fault is intermittent, and every retry
    re-sends the whole turn into it.  What made that expensive was not the failure but the
    waiting: the session held its full hour before the driver was allowed its next repair, so
    three attempts cost three hours to learn the same thing three times.

    Two rules end it, and both are needed.  `STORM` consecutive retries with no intervening event
    is the loud version.  `STALL` seconds without the transcript growing at all is the quiet one,
    and it is the one that matters more: the observed failure emits two retries and then goes
    silent, which a retry counter watches forever.

    `how` comes back `api-storm` or `stalled`, deliberately neither of them `timeout`: a timeout
    means the agent worked and ran out of time, these mean it never got a turn through, and a
    driver deciding whether to repair is asking exactly that question.
    """
    retries, seen, mark, last = 0, 0, _size(transcript), time.time()
    while True:
        try:
            p.wait(timeout=POLL)
            return p.returncode, ("ok" if p.returncode == 0 else "exit")
        except subprocess.TimeoutExpired:
            pass
        now = time.time()
        if timeout and (now - t0) > timeout:
            return _end(p, -1, "timeout")
        size = _size(transcript)
        if size != mark:
            mark, last = size, now
        elif now - last > STALL:
            return _end(p, -4, "stalled")
        retries, seen = _storm_state(transcript, seen, retries)
        if retries >= STORM:
            return _end(p, -3, "api-storm")


def _size(path: str) -> int:
    """How much a session has written so far, or -1 while it has not started writing."""
    try:
        return os.path.getsize(path)
    except OSError:
        return -1


def _end(p: subprocess.Popen, rc: int, how: str) -> tuple[int, str]:
    """Stop a session and report the reason we stopped it, not the reason it stopped.

    `terminate` first, so the CLI gets to flush what it has written; `kill` if it does not take
    the hint.  The returned `rc` is ours — the process's own exit status after a signal says
    nothing about why the signal was sent, and why is the whole content of this result.
    """
    p.terminate()
    try:
        p.wait(timeout=10)
    except subprocess.TimeoutExpired:
        p.kill()
        p.wait()
    return rc, how


def _storm_state(transcript: str, seen: int, retries: int) -> tuple[int, int]:
    """Consecutive trailing transport-retry events, and accounted-for line count.

    Claude reports these as ``api_retry`` subtypes.  Current Codex JSONL instead emits top-level
    ``error`` events whose message begins ``Reconnecting...``.  Both mean the same thing to the
    supervisor: the same request is being retried without intervening model work.

    Reads only what is new since the last look, so the cost of polling a growing transcript does
    not grow with it.  A partially-written final line parses as nothing and is simply not counted
    yet; it will be a complete line by the next poll.
    """
    if not os.path.isfile(transcript):
        return retries, seen
    n = 0
    try:
        with open(transcript, errors="replace") as f:
            for line in f:
                n += 1
                if n <= seen:
                    continue
                line = line.strip()
                if not line:
                    n -= 1                       # not an event; do not consume it from the count
                    continue
                try:
                    ev = json.loads(line)
                except ValueError:
                    n -= 1                       # truncated tail — re-read it next time round
                    continue
                reconnecting = (
                    ev.get("type") == "error"
                    and isinstance(ev.get("message"), str)
                    and ev["message"].startswith("Reconnecting...")
                )
                retries = retries + 1 if (ev.get("subtype") == "api_retry"
                                          or reconnecting) else 0
    except OSError:
        return retries, seen
    return retries, n


def _keep(transcript: str) -> None:
    """Move an existing transcript aside rather than overwriting it.

    Transcript names are `<round>.<phase>.<pass>.a<attempt>`, and `attempt` counts from 1 within
    one driver invocation.  So a driver restarted after a failure writes `a1` again and, without
    this, the record of the failure that caused the restart is gone — destroyed by the run that
    exists because of it.  That is the exact thing the module docstring above says does not
    happen here, and it happened: a stalled session's transcript was overwritten by its own
    replacement within the hour.

    The old one becomes `<stem>.prev<N>.jsonl`, N counting up, so the sequence is readable.
    Nothing is ever removed.
    """
    if not os.path.isfile(transcript) or os.path.getsize(transcript) == 0:
        return
    stem, ext = os.path.splitext(transcript)
    n = 1
    while os.path.exists(f"{stem}.prev{n}{ext}"):
        n += 1
    os.replace(transcript, f"{stem}.prev{n}{ext}")


def _tail(path: str, n: int = 800) -> str:
    """The last `n` characters of a file, or "" if there is nothing to read."""
    try:
        with open(path, errors="replace") as f:
            return f.read()[-n:]
    except OSError:
        return ""


#: What a refused tool call looks like, per wall.  Ours announces itself; the CLI's two do not,
#: so they are recognised by the words they use.  If a future CLI reworks that wording this
#: table goes stale — which is a real weakness, and the reason `refusals()` reports the tool
#: call it refused rather than only a count: a table that stops matching shows up as silence in
#: a place a reader is looking, instead of as a number that was never printed.
_REFUSED = (
    ("confinement", "leansilicon confinement:"),
    ("command-not-granted", "requires approval"),
    ("outside-working-dir", "allowed working directories"),
)


def refusals(path: str) -> list[dict]:
    """Every tool call refused by any of the three walls, with what was refused.

    `denied_calls` counted one wall.  The CLI brings two more — the `--allowedTools` patterns,
    which match on the head of a command, and the working-directory restriction — and across the
    runs that built this repository they refused two and a half times as often as ours did, while
    reporting nothing anywhere.  Three separate bring-up sessions were lost to that gap: a
    verification command whose shape the grant did not admit, a library the role was granted and
    the CLI would not open, and an interpreter the prompt never thought to say was absent.  Each
    looked from the outside like an agent that had simply stalled.

    The count alone would not have shortened any of them, so this returns the offending call.  A
    refusal is a disagreement between what a prompt asks for and what a role was given, and the
    only thing that identifies which disagreement is the text of the call itself.
    """
    if not os.path.isfile(path):
        return []
    out: list[dict] = []
    try:
        for line in open(path, errors="replace"):
            line = line.strip()
            if not line:
                continue
            try:
                ev = json.loads(line)
            except ValueError:
                continue
            msg = ev.get("message")
            if not isinstance(msg, dict) or not isinstance(msg.get("content"), list):
                continue
            for b in msg["content"]:
                if not isinstance(b, dict) or b.get("type") != "tool_result":
                    continue
                text = b.get("content")
                if isinstance(text, list):
                    text = "".join(x.get("text", "") for x in text if isinstance(x, dict))
                text = str(text or "")
                for wall, mark in _REFUSED:
                    if mark in text:
                        out.append({"wall": wall, "detail": text.strip()[:200]})
                        break
    except OSError:
        return out
    return out


def refusal_summary(rs: list[dict]) -> str:
    """One line per distinct refusal, for a driver log.  Empty when there were none."""
    if not rs:
        return ""
    seen: dict[tuple, int] = {}
    for r in rs:
        k = (r["wall"], r["detail"])
        seen[k] = seen.get(k, 0) + 1
    L = [f"  {len(rs)} tool call(s) refused — a prompt and a grant disagree:"]
    for (wall, detail), n in sorted(seen.items(), key=lambda kv: -kv[1]):
        L.append(f"    [{wall}] x{n}  {detail.splitlines()[0][:120]}")
    return "\n".join(L)


def session_error(path: str) -> str:
    """The API-level failure a `stream-json` transcript ends on, if any.

    A session can exit 0 having done nothing — the CLI reports an overload or a refusal as a
    result and returns cleanly — so `rc` alone does not separate "the agent tried and failed"
    from "the agent never ran".  Those need different responses, so they are told apart here.
    """
    if not os.path.isfile(path):
        return "transcript missing"
    last = ""
    try:
        for line in open(path, errors="replace"):
            line = line.strip()
            if not line:
                continue
            try:
                ev = json.loads(line)
            except ValueError:
                continue
            if ev.get("type") == "result" and ev.get("is_error"):
                last = str(ev.get("result") or ev.get("subtype") or "error")[:300]
            if ev.get("type") == "error":
                last = str(ev.get("error") or ev)[:300]
    except OSError as e:                                                 # noqa: BLE001
        return f"transcript unreadable: {e}"
    return last


def denied_calls(path: str) -> int:
    """How many tool calls **our** confinement refused.

    Kept as its own number because it means something specific: a role bouncing off `confine.py`
    is a role reaching for another run, the other half of the pipeline, or the dataset — which is
    a different fact from a role whose command shape the CLI did not admit.  Conflating them
    would make a wall that guards isolation share a counter with one that guards nothing.

    It is *not* the number of refusals a session saw; see `refusals()`, which sees all three
    walls.  Reading this one as the total is what let three bring-up sessions fail silently.
    """
    if not os.path.isfile(path):
        return 0
    n = 0
    try:
        for line in open(path, errors="replace"):
            if "leansilicon confinement:" in line:
                n += 1
    except OSError:
        return 0
    return n
