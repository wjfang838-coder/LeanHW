#!/usr/bin/env python3
"""A `PreToolUse` hook that confines an authoring agent to one run directory.

Isolation used to be measured after the fact: walk the transcripts, report every path argument
that left the run.  The first pilot of that approach showed why it is not enough.  Rescanned
with a corrected parser it found 20 such calls across 16 distinct paths, and they partitioned
three ways: the project's accumulated agent memory (and three of six calls were *writes* — the
agent filing lessons of its own), a listing of the directory holding every other case, and
several reads of the checker's own Python source.

Nothing in that list was a reference.  The agent did not open one.  The door was open.

So this is the wall, and it runs before the call rather than after the run:

    ALLOW  the run directory, in full
    ALLOW  whatever the prompt explicitly told the agent to compile against
    DENY   everything else — the other runs, the benchmark, the framework's Python source,
           the other half of the pipeline, and the user's memory

Exit 2 blocks the call and shows the message to the agent, so a refusal is something it can read
and route around rather than a silent failure.

## Two walls, not one

`DENY` makes a path unreachable: the agent may neither read nor write it.  That is the wall
around the other half of the pipeline, and around every other run.

`READONLY` makes a path readable and unwritable.  That is a *different* wall and it was worth
separating, because conflating the two broke the method the first time this ran.  The frozen
specification is on it: the implementer's whole task is to build against that file, so denying
it outright leaves the implementer with nothing to implement — but the implementer must not be
able to edit it, or the freeze means nothing.  Under the earlier blind-parallel mode the same
file was genuinely unreadable, and the list was carried over unchanged into serial authoring,
where it is exactly wrong.

`READONLY` is enforced hard for the file-writing tools, which are how an agent actually edits.
For `Bash` it is enforced on the commands that visibly modify — a redirection into the path,
`chmod`, `mv`, `rm`, `sed -i`, `tee`, `truncate`, `cp` onto it — and not on the rest, because
reading is the point.  That check is a heuristic and is not the guarantee.  The guarantee is
layered: the file is `chmod 0444` on disk, `chmod` itself is refused here, and the recorded
sha256 is re-checked afterwards.  Only the last of those *detects*; the first two only obstruct.

`LEANSILICON_ROOT` carries the run directory, `LEANSILICON_ALLOW` the extra roots,
`LEANSILICON_DENY` the unreachable paths and `LEANSILICON_READONLY` the unwritable ones; all are
set per subprocess by `common/agent.py`.  **With no root set the hook denies everything**,
because a confinement that fails open is not one.
"""
from __future__ import annotations

import json
import os
import re
import sys

# A path claim is any run of name characters containing a separator.  The leading segment is
# optional-but-greedy on purpose: an earlier version anchored on `~`, `.` or `/`, so a plain
# relative path like `sandbox/spec.txt` matched only from its slash, arrived here as `/spec.txt`,
# resolved as absolute and was denied — the agent's own input, and every relative write it makes.
#
# A claim also has to START where a shell word starts, which is what the lookbehind buys.  Without
# it the scanner is free to begin INSIDE a word it could not span, and that is not a hypothetical:
# `jq '{a:(.a//null)}'` has a `//` the leading segment cannot cross, so matching restarted at the
# second slash and the decisions author was refused for naming `/null` — a directory it had not
# mentioned, in a program that touches no files.  `(.name//.choice//.hole//"")` gave `/.choice/`
# and `/.hole/` the same way.  The rule generalises past `jq`: any `x//y` operator was readable as
# an absolute path, and always as one whose first component was the operand rather than the root.
#
# The slash-run in the middle (`/+`, not `/`) is what keeps that from being a way out.  A doubled
# slash is legal POSIX and `realpath` collapses it, so `cat //etc/passwd` must still be caught —
# with the lookbehind alone it would match nowhere, because the only position that can span it is
# the one the lookbehind rejects.  Absorbing the run makes the whole of `//etc/passwd` the token,
# which resolves exactly where the single-slash spelling does and is refused exactly as it was.
#
# What this does NOT fix, deliberately: a regex literal that opens at a word boundary, such as
# awk's `'/.choice/,/.hole/'`.  That is `_INERT`'s family — the wall reads shell words and cannot
# know which of them the command means as a pattern — and the only edit that would cover it is
# exempting quoted arguments, which is where real path arguments live too.
_PATHY = re.compile(r"(?<![\w.\-~])/*[\w.\-~]*(?:/+[\w.\-]+)+/*")

# ...and `-` being a name character means `/-` matches, which is how the formalization author got
# refused for typing Lean's block-comment opener into a `grep`.  A token built from nothing but
# slashes and dashes addresses nothing: it has no name to resolve, no `.` or `..` to climb with,
# and no `~` to expand.  Exempting exactly that shape closes the false positive without widening
# anything — `/.`, `../..` and `/-x` all still arrive at `allowed()` as before.
#
# Worth being precise about why this is a bug and not a judgement call.  The wall failed CLOSED,
# so nothing was reachable that should not have been; the cost was a turn, and the ARCHITECTURE
# note on the third wall says what a turn spent on an unexplainable refusal actually buys — the
# agent routes around it.  This one did, and succeeded.  A wall that cries wolf is still teaching.
_INERT = re.compile(r"^[/\-]+$")

# Sinks, not sources.  `2>/dev/null` is the ordinary way to run a simulator quietly; denying it
# costs a turn and teaches nothing, and nothing can be read back out of it.
_SINKS = ("/dev/null", "/dev/stdout", "/dev/stderr", "/dev/tty")

# Path-valued fields across the tools the grant allows.  `command` is included because `Bash` is
# scoped to a handful of binaries and those take file arguments: a scoped binary pointed at
# another run's directory reads it just as well as `Read` would.  A Glob ``pattern`` is handled
# separately below: unlike every other field it is relative to the tool's ``path`` and can spell
# components with ``*``, ``?`` and character classes that a literal-path scanner cannot see.
_FIELDS = ("file_path", "path", "notebook_path", "command", "pattern")

# Claude Code 2.1.233 implements Glob with ripgrep 14.1.1 / globset 0.4.15.  Braces are valid in
# that dialect, but their alternatives can move the static search root in ways this small hook must
# not guess at, so they are conservatively refused.  Treating an escaped metacharacter as magic is
# also conservative: it can only move the checked root upward, never hide a reachable path.
_GLOB_PREFIX_MAGIC = re.compile(r"[*?[{]")
_GLOB_UNSUPPORTED = re.compile(r"[{}]")

# ECMAScript String.prototype.trim WhiteSpace + LineTerminator code points.  Python's default
# ``strip`` differs in both directions (notably FEFF is JS whitespace and U+0085 is not), which can
# make the hook and Claude choose different relative search directories.
_JS_TRIM = "".join(chr(code) for code in (9, 10, 11, 12, 13, 32, 160, 5760, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287, 12288, 65279))

ROOT_ENV = "LEANSILICON_ROOT"
ALLOW_ENV = "LEANSILICON_ALLOW"
DENY_ENV = "LEANSILICON_DENY"
RDONLY_ENV = "LEANSILICON_READONLY"

#: Tools whose whole purpose is to change a file.  Naming a read-only path in one of these is a
#: write attempt with no reading interpretation available.
_WRITE_TOOLS = ("Write", "Edit", "MultiEdit", "NotebookEdit")

#: Shell commands that modify the path they name.  Deliberately over- rather than under-broad:
#: a false refusal costs the agent one turn and says why, while a miss lets the freeze be edited.
#: `chmod` is here because it is the move that would defeat the 0444 on disk.
_MUTATES = re.compile(
    r"(?:^|[\s;&|])(?:chmod|chown|mv|rm|cp|ln|touch|truncate|tee|dd|install|patch|shred)\b"
    r"|>\s*['\"]?(?=[\w.~/])"
    r"|\bsed\b[^|;&]*\s-[a-zA-Z]*i"
    r"|\bpython3?\b[^|;&]*\bopen\([^)]*['\"][wa]", re.I)


def roots() -> tuple[str, list[str], list[str], list[str]]:
    root = os.environ.get(ROOT_ENV, "")
    real = lambda env: [os.path.realpath(p)                                     # noqa: E731
                        for p in os.environ.get(env, "").split(os.pathsep) if p]
    return (os.path.realpath(root) if root else ""), \
        real(ALLOW_ENV), real(DENY_ENV), real(RDONLY_ENV)


def under(p: str, roots_: list[str]) -> bool:
    return any(p == r or p.startswith(r + os.sep) for r in roots_ if r)


def allowed(hit: str, root: str, extra: list[str], deny: list[str], cwd: str) -> bool:
    if hit in _SINKS:
        return True
    hit = os.path.expanduser(hit)
    # One base, not two.  Trying cwd *and* the run dir and accepting either lets a relative path
    # that escapes through cwd be laundered by the run: with the agent launched at the repository
    # root, `part1/other` misses under cwd but lands harmlessly under `<run>/part1/other`, and the
    # escape is waved through.  A relative path has exactly one meaning — the one the tool will
    # give it — and the agent is launched with `cwd=<run>`, so that meaning is the run.
    p = os.path.realpath(hit if os.path.isabs(hit) else os.path.join(cwd, hit))
    # Deny wins over allow.  This is what puts a path inside a directory the agent otherwise owns
    # out of reach entirely: it lives in the run, so `root` admits it, and only an explicit denial
    # takes it back.  Ordering the checks the other way round would make it a request, not a wall.
    if under(p, deny):
        return False
    return under(p, [root, *extra])


def effective_cwd(command: str, cwd: str, root: str) -> str:
    """The directory a `Bash` command's relative paths are actually resolved against.

    `cd scratch && iverilog ../authored/round1/cand.sv` is an ordinary way to build, and both of
    its paths stay inside the run — but only if the `cd` is honoured.  Resolved against the
    session cwd instead, the `..` climbs out and the build is refused; the first confined run
    lost a turn to exactly that.

    Only a leading `cd` counts, and only when it lands inside the run: a command that begins by
    leaving is not made safe by what it does next.
    """
    m = re.match(r"\s*cd\s+([^\s;&|]+)\s*(?:&&|;)", command)
    if not m:
        return cwd
    target = os.path.expanduser(m.group(1).strip("'\""))
    p = os.path.realpath(target if os.path.isabs(target) else os.path.join(cwd, target))
    return p if p == root or p.startswith(root + os.sep) else cwd


def _has_denied_descendant(base: str, deny: list[str]) -> bool:
    """Whether traversing ``base`` can reach an explicitly denied path."""
    return any(base == hidden or base == os.sep or hidden.startswith(base + os.sep)
               for hidden in deny if hidden)


def _structured_search_path(raw, cwd: str) -> str:
    """Resolve a structured search ``path`` exactly as Claude Code 2.1.233 does.

    Its normalizer trims the field, defaults an empty result to cwd, and expands only exact ``~``
    and ``~/...``.  Python ``expanduser`` additionally expands ``~user``; using it here can make the
    hook inspect one tree while Grep/Glob inspect a different literal directory below cwd.
    """
    value = raw.strip(_JS_TRIM) if isinstance(raw, str) else ""
    if not value:
        value = cwd
    elif value == "~":
        value = os.path.expanduser("~")
    elif value.startswith("~/"):
        value = os.path.join(os.path.expanduser("~"), value[2:])
    return value if os.path.isabs(value) else os.path.join(cwd, value)


def _recursive_search_offence(inp: dict, tool: str, root: str, extra: list[str],
                              deny: list[str], cwd: str) -> list[str]:
    """Reject recursive searches whose traversal tree can enter a denied descendant.

    Grep uses ``cwd`` when ``path`` is omitted.  Checking only the literal tool input lets such a
    call traverse the whole session root without ever naming a denied child, so its whole base tree
    must be clean.  Glob has a separate check because an absolute pattern can replace its declared
    path with a different search root, while relative, slashless, and empty patterns all recurse.
    """
    if tool != "Grep":
        return []
    raw = inp.get("path")
    base = os.path.realpath(_structured_search_path(raw, cwd))
    if not allowed(base, root, extra, deny, cwd):
        return [str(raw)]
    if _has_denied_descendant(base, deny):
        return [str(raw)]
    return []


def _glob_pattern_offence(inp: dict, root: str, extra: list[str], deny: list[str],
                           cwd: str) -> list[str]:
    """Reject a Glob whose actual ripgrep traversal root is not wholly clean.

    Claude Code 2.1.233 does not implement this tool with Python glob semantics.  A relative pattern
    is a ripgrep/globset filter over the literal ``path`` search directory; a slashless pattern and
    even the empty pattern recurse through that whole directory.  An absolute pattern instead picks
    its own search root: the static directory before its first glob metacharacter (or the containing
    directory for an exact path), and the separate ``path`` no longer bounds it.

    Confinement therefore validates roots, not guessed matches.  The selected search root must be
    allowed and have no denied descendant.  Ripgrep does not follow symlinks found during traversal,
    while an explicit symlink search root *is* traversed, so realpath of that root is the complete
    symlink boundary needed here.  Parent components and brace alternatives are refused rather than
    emulated across a different glob dialect.
    """
    raw_pattern = inp.get("pattern")
    if not isinstance(raw_pattern, str):
        return ["<missing Glob pattern>"]
    pattern = raw_pattern
    if _GLOB_UNSUPPORTED.search(pattern) or "\x00" in pattern:
        return [pattern]

    raw_base = inp.get("path")
    base = os.path.realpath(_structured_search_path(raw_base, cwd))
    if not allowed(base, root, extra, deny, cwd):
        return [pattern]

    # Patterns are passed verbatim to Claude's absolute-pattern detector and ripgrep.  In
    # particular, ``~`` is ordinary relative pattern text here; expanding it would validate the
    # wrong tree.
    expanded = pattern
    if any(component == os.pardir for component in expanded.split(os.sep)):
        return [pattern]
    absolute = os.path.isabs(expanded)
    if not absolute:
        # ``path`` limits traversal but does not consistently re-root slash-containing filters;
        # either way every candidate comes from this same search tree.  Empty is also recursive.
        search_root = base
    else:
        magic = _GLOB_PREFIX_MAGIC.search(expanded)
        if magic:
            split = expanded.rfind(os.sep, 0, magic.start())
            search_root = expanded[:split] if split > 0 else os.sep
        else:
            # Node's path.dirname drops trailing separators before taking the parent; Python keeps
            # the final component for `/dir/`.  Claude uses the Node result as its search root.
            trimmed = expanded.rstrip(os.sep)
            search_root = os.path.dirname(trimmed) if trimmed else os.sep
            search_root = search_root or os.sep
        search_root = os.path.realpath(search_root)

    if (not allowed(search_root, root, extra, deny, cwd)
            or _has_denied_descendant(search_root, deny)):
        return [pattern]
    return []


def offending(inp: dict, root: str, extra: list[str], deny: list[str], cwd: str,
              tool: str = "") -> list[str]:
    """The path arguments in one tool call that name somewhere out of reach.

    Shared by the hook and by the transcript scan, so the wall and the measurement of the wall
    cannot drift apart on what counts as outside.
    """
    bad = _recursive_search_offence(inp, tool, root, extra, deny, cwd)
    if tool == "Glob":
        bad.extend(_glob_pattern_offence(inp, root, extra, deny, cwd))
    for f in _FIELDS:
        v = inp.get(f)
        if not isinstance(v, str):
            continue
        # Recursive search paths use Claude's trim-and-limited-tilde normalizer, while shell paths
        # use shell expansion; their dedicated checks above must not be reinterpreted here.  Glob
        # patterns additionally use ripgrep/globset syntax and may choose an independent root.
        if tool in ("Grep", "Glob") and f == "path":
            continue
        if tool == "Glob" and f == "pattern":
            continue
        here = effective_cwd(v, cwd, root) if f == "command" else cwd
        for hit in _PATHY.findall(v):
            # A bare word is not a path claim.  `_PATHY` needs a separator, so what reaches here
            # is `foo/bar`, `/abs`, `../up` — each of which addresses a location.  `/-` does not,
            # and is the one shape excluded.  The explicit trio is checked first so that adding
            # the exemption cannot quietly take `/` off the deny list.
            if hit in ("/", "./", "../"):
                bad.append(hit)
            elif _INERT.match(hit):
                continue
            elif not allowed(hit, root, extra, deny, here):
                bad.append(hit)
    return bad


def clobbering(inp: dict, tool: str, rdonly: list[str], root: str, cwd: str) -> list[str]:
    """The read-only paths this call would WRITE.

    Reading them is the point — the implementer builds against the frozen specification — so a
    mention alone is not an offence.  What is checked is the tool: a file-writing tool naming one
    has no reading interpretation, and a shell command naming one is judged by whether it looks
    like it modifies.
    """
    if not rdonly:
        return []
    bad = []
    for f in _FIELDS:
        v = inp.get(f)
        if not isinstance(v, str):
            continue
        if tool not in _WRITE_TOOLS and not (f == "command" and _MUTATES.search(v)):
            continue
        here = effective_cwd(v, cwd, root) if f == "command" else cwd
        for hit in _PATHY.findall(v):
            p = os.path.expanduser(hit)
            p = os.path.realpath(p if os.path.isabs(p) else os.path.join(here, p))
            if under(p, rdonly):
                bad.append(hit)
    return bad


def main() -> int:
    try:
        ev = json.load(sys.stdin)
    except Exception:                                                    # noqa: BLE001
        print("leansilicon confinement: unreadable hook event; denying", file=sys.stderr)
        return 2
    root, extra, deny, rdonly = roots()
    if not root:
        print(f"leansilicon confinement: {ROOT_ENV} is unset, so nothing is allowed",
              file=sys.stderr)
        return 2
    inp, tool = (ev.get("tool_input") or {}), (ev.get("tool_name") or "?")
    cwd = ev.get("cwd") or root

    frozen = clobbering(inp, tool, rdonly, root, cwd)
    if frozen:
        print(f"leansilicon confinement: {tool} would write {', '.join(sorted(set(frozen))[:4])},"
              f" which is frozen.\nYou may READ it — that is what it is for — and you may not "
              f"change it.  If you believe it is wrong, that is a challenge, and your role card "
              f"says how to file one.  An implementation quietly fitted to an edited "
              f"specification is not a result anyone can check.", file=sys.stderr)
        return 2

    bad = offending(inp, root, extra, deny, cwd, tool)
    if not bad:
        return 0
    print(f"leansilicon confinement: {tool} names "
          f"{', '.join(sorted(set(bad))[:4])}, which is outside this run.\n"
          f"You may read and write {root} and what the prompt named, and nothing else.  The "
          f"prose you were given is the whole task statement; the benchmark's dataset, any "
          f"reference implementation, any testbench, the other half of this pipeline and every "
          f"other run are deliberately out of reach.", file=sys.stderr)
    return 2


if __name__ == "__main__":
    raise SystemExit(main())
