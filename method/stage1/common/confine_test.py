#!/usr/bin/env python3
"""Does the wall hold, and does it let through what it is supposed to let through?

    python3 common/confine_test.py

Both halves matter and only one of them is usually tested.  A confinement that denies everything
passes every test that asks "is X blocked", and the first thing it blocks is the work.  That is
not hypothetical here: the frozen specification spent one iteration on the DENY list, carried
over unchanged from the blind-parallel mode where the implementer genuinely was not supposed to
see it.  Under serial authoring the implementer's whole task is defined against that file, so the
wall as written handed D a target it could not open.  Nothing would have reported that except a
wasted authoring session.

So the cases below come in pairs: for every path, what must be refused AND what must go through.
"""
from __future__ import annotations

import json
import os
import subprocess
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.dirname(HERE)
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

from common import paths                                                    # noqa: E402
CONFINE = os.path.join(HERE, "confine.py")


def cases(ws: str, spec: str, rec: str, impl: str) -> list[tuple]:
    """(name, tool, tool_input, expected rc).  0 is allowed, 2 is refused."""
    bom = chr(0xfeff)
    next_line = chr(0x85)
    unicode_dirty = next_line + "safe" + next_line
    return [
        # The frozen specification: readable by every route, writable by none.
        ("read the frozen spec", "Read", {"file_path": spec}, 0),
        ("grep inside the frozen spec", "Grep", {"path": spec, "pattern": "specStep"}, 0),
        # Recursive tools traverse below their effective base.  Omitting ``path`` means cwd, and
        # naming the allowed workspace still crosses the denied freeze record; both must fail before
        # the tool runs.  A clean, narrower subtree remains searchable.
        ("grep with omitted path", "Grep", {"pattern": "specStep"}, 2),
        ("grep from allowed parent", "Grep", {"path": ws, "pattern": "specStep"}, 2),
        ("glob with omitted path", "Glob", {"pattern": "**/*.lean"}, 2),
        ("glob from allowed parent", "Glob", {"path": ws, "pattern": "**/*.lean"}, 2),
        ("grep a clean subtree", "Grep",
         {"path": os.path.join(ws, "clean"), "pattern": "specStep"}, 0),
        ("glob a clean subtree", "Glob",
         {"path": os.path.join(ws, "clean"), "pattern": "*.lean"}, 0),
        # Relative and slashless patterns are ripgrep filters over the whole declared search tree;
        # they do not make a broad parent safe.  An absolute pattern selects its own static root.
        ("relative glob cannot narrow parent", "Glob",
         {"path": ws, "pattern": "clean/*.lean"}, 2),
        ("absolute glob narrows its parent", "Glob",
         {"path": ws, "pattern": os.path.join(ws, "clean", "*.lean")}, 0),
        ("absolute exact trailing slash uses parent", "Glob",
         {"path": os.path.join(ws, "clean"),
          "pattern": os.path.join(ws, "clean") + os.sep}, 2),
        ("glob path metachar is literal", "Glob",
         {"path": os.path.join(ws, "clean", "[safe]"), "pattern": "*.lean"}, 0),
        # Parent components are refused even though the current ripgrep traversal is path-bounded;
        # character classes and wildcard bytes must never make a future root rewrite ambiguous.
        # Absolute patterns ignore a clean declared base and select their own static search root.
        ("glob class cannot hide a deny", "Glob",
         {"path": os.path.join(ws, "clean"),
          "pattern": "../fr[a]gs/accu/spec.frozen.json"}, 2),
        ("glob question mark cannot hide it", "Glob",
         {"path": os.path.join(ws, "clean"),
          "pattern": "../fr?gs/accu/spec.frozen.json"}, 2),
        ("glob star cannot cross to a deny", "Glob",
         {"path": os.path.join(ws, "clean"), "pattern": "../*/**"}, 2),
        ("absolute glob class cannot hide it", "Glob",
         {"path": os.path.join(ws, "clean"),
          "pattern": os.path.join(ws, "fr[a]gs", "accu", "spec.frozen.json")}, 2),
        ("glob class inside clean subtree", "Glob",
         {"path": os.path.join(ws, "clean"), "pattern": "nested/[a]llowed/*.lean"}, 0),
        ("glob parent component fails closed", "Glob",
         {"path": os.path.join(ws, "clean"), "pattern": "../clean/[a]llowed/*.lean"}, 2),
        ("empty glob recurses over parent", "Glob", {"path": ws, "pattern": ""}, 2),
        ("empty glob on clean subtree", "Glob",
         {"path": os.path.join(ws, "clean"), "pattern": ""}, 0),
        ("whitespace glob path means cwd", "Glob", {"path": "   ", "pattern": "*.lean"}, 2),
        ("U+FEFF glob path means cwd", "Glob", {"path": bom, "pattern": "*.lean"}, 2),
        ("U+0085 glob path stays literal", "Glob",
         {"path": unicode_dirty, "pattern": "*.lean"}, 2),
        ("tilde glob pattern stays relative", "Glob", {"path": ws,
                                                        "pattern": "~/clean/*.lean"}, 2),
        ("cat the frozen spec", "Bash", {"command": f"cat {spec}"}, 0),
        ("diff against the frozen spec", "Bash", {"command": f"diff {spec} {impl}"}, 0),
        ("Edit the frozen spec", "Edit", {"file_path": spec}, 2),
        ("Write over the frozen spec", "Write", {"file_path": spec}, 2),
        ("redirect into the frozen spec", "Bash", {"command": f"echo x > {spec}"}, 2),
        ("append to the frozen spec", "Bash", {"command": f"echo x >> {spec}"}, 2),
        ("tee into the frozen spec", "Bash", {"command": f"echo x | tee {spec}"}, 2),
        # `chmod` is the move that would defeat the 0444, so the hook refuses it by name.
        ("chmod the frozen spec", "Bash", {"command": f"chmod 644 {spec}"}, 2),
        ("sed -i the frozen spec", "Bash", {"command": f"sed -i s/a/b/ {spec}"}, 2),
        ("rm the frozen spec", "Bash", {"command": f"rm -f {spec}"}, 2),
        ("mv over the frozen spec", "Bash", {"command": f"mv {impl} {spec}"}, 2),
        ("cp over the frozen spec", "Bash", {"command": f"cp {impl} {spec}"}, 2),

        # The freeze record stays unreadable: an agent that can read the hash can find out
        # whether an edit was noticed.
        ("read the freeze record", "Read", {"file_path": rec}, 2),
        ("grep the freeze record", "Bash", {"command": f"grep sha {rec}"}, 2),

        # The other half of the pipeline, and everything outside the run.  Written relative,
        # because that is how an author would reach for it: the workspace is four levels down
        # (`data/part2/<bench>/<key>/<arm>`) and `../../../../part1` is the other half from
        # inside it.
        ("read the other half", "Read",
         {"file_path": "../../../../part1/rtllm/accu/c5/out/HANDOFF.json"}, 2),
        ("list the other half", "Bash", {"command": "ls ../../../../part1/"}, 2),
        ("read the dataset", "Read", {"file_path": "/home/x/datasets/RTLLM/a/testbench.v"}, 2),

        # And the ordinary work, which must not be collateral damage.
        ("write the impl fragment", "Write", {"file_path": impl}, 0),
        ("edit the impl fragment", "Edit", {"file_path": impl}, 0),
        ("build through bbf", "Bash", {"command": "python3 scripts/bbf.py accu build --role D"}, 0),
        ("emit and redirect elsewhere", "Bash",
         {"command": "python3 scripts/bbf.py accu emit --role D > scratch/accu.D/emit.log"}, 0),
        ("run a sim quietly", "Bash", {"command": "vvp scratch/accu.D/a.out 2>/dev/null"}, 0),
        ("cd then build", "Bash", {"command": "cd scratch/accu.D && iverilog -o a.out ../../out/accu.v"}, 0),
        ("read the prose", "Read", {"file_path": "specs/accu.spec.txt"}, 0),
        ("read Core", "Read", {"file_path": "LeanRTL/Core/Refine.lean"}, 0),

        # `-` is a name character, so `/-` — Lean's block-comment opener — used to match `_PATHY`
        # and be denied as a path outside the run.  It addresses nothing, and the four cases
        # under it are the ones that must NOT come along with the exemption.
        ("grep a Lean comment opener", "Bash", {"command": "grep -n /- frags/accu/impl.lean"}, 0),
        ("the exemption does not cover a dot", "Bash", {"command": "ls /."}, 2),
        ("the exemption does not cover ..", "Bash",
         {"command": "ls ../../../../part1/rtllm/accu/c5"}, 2),
        ("the exemption does not cover /-x", "Bash", {"command": "cat /-x/secrets"}, 2),
        ("a dash path with a name is still a path", "Bash", {"command": "cat /-/etc/passwd"}, 2),

        # `//` is an operator in `jq`, and the leading segment of `_PATHY` cannot cross it, so
        # matching used to restart at the second slash: `(.a//null)` was refused for naming
        # `/null`, and `(.name//.choice//.hole//"")` for naming `/.choice/` and `/.hole/`.  Both
        # cost the decisions author a turn on a program that opens no file at all.  A path claim
        # now has to begin where a shell word begins, and the three cases under these are what
        # that must not cost: a doubled slash is legal POSIX, `realpath` collapses it, and the
        # only position that can span `//etc/passwd` is the one the lookbehind rejects — so the
        # slash-run is absorbed into the token rather than skipped past.
        ("jq's alternative operator is not a path", "Bash",
         {"command": "jq -c '{a:(.a//null)}' steps/round1/03_diagnosis.json"}, 0),
        ("...nor is a chain of them", "Bash",
         {"command": "jq -r 'select((.name//.choice//.hole//\"\") | tostring)' state/d.json"}, 0),
        ("...and the spaced spelling was never one", "Bash",
         {"command": "jq -c '.pair // .fork // null' state/d.json"}, 0),
        ("a doubled slash is not a way out", "Bash", {"command": "cat //etc/passwd"}, 2),
        ("...nor one past a deny entry", "Bash",
         {"command": "cat /" + paths.case1("rtllm", "accu", "c5", "out", "spec.decided.txt")}, 2),
        ("...and an interior one still resolves", "Bash",
         {"command": "cat frags//accu//impl.lean"}, 0),
    ]


def main() -> int:
    ws = paths.ws2("local", "confine-test", "solo")
    spec = os.path.join(ws, "frags", "accu", "spec.lean")
    rec = os.path.join(ws, "frags", "accu", "spec.frozen.json")
    impl = os.path.join(ws, "frags", "accu", "impl.lean")
    # The paths need not exist: the hook decides from the path, before the tool runs, which is
    # the only point at which it could decide anything.
    env = dict(os.environ,
               LEANSILICON_ROOT=ws,
               LEANSILICON_ALLOW=os.path.expanduser("~/.elan"),
               LEANSILICON_DENY=os.pathsep.join([
                   rec,
                   paths.data(paths.PART1),
                   os.path.join(ws, chr(0x85) + "safe" + chr(0x85), "ref"),
               ]),
               LEANSILICON_READONLY=spec)

    bad, n = [], 0
    for name, tool, inp, want in cases(ws, spec, rec, impl):
        n += 1
        ev = json.dumps({"tool_name": tool, "tool_input": inp, "cwd": ws})
        r = subprocess.run([sys.executable, CONFINE], input=ev, text=True,
                           capture_output=True, env=env)
        ok = r.returncode == want
        if not ok:
            bad.append((name, r.returncode, want, (r.stderr or "").strip()[:200]))
        print(f"  {'ok ' if ok else 'BAD'}  {name:34} rc={r.returncode} (want {want})")

    # With no root set, nothing is allowed.  A confinement that fails open is not one, and this
    # is the case that a refactor is most likely to break silently.
    r = subprocess.run([sys.executable, CONFINE],
                       input=json.dumps({"tool_name": "Read",
                                         "tool_input": {"file_path": spec}, "cwd": ws}),
                       text=True, capture_output=True,
                       env={k: v for k, v in env.items() if k != "LEANSILICON_ROOT"})
    ok = r.returncode == 2
    if not ok:
        bad.append(("unset root denies everything", r.returncode, 2, ""))
    print(f"  {'ok ' if ok else 'BAD'}  {'unset root denies everything':34} rc={r.returncode} "
          f"(want 2)")

    if bad:
        print(f"\n{len(bad)} case(s) wrong:")
        for name, got, want, err in bad:
            print(f"  {name}: got {got}, want {want}  {err}")
        return 1
    print(f"\nconfine: all {n + 1} cases hold — the frozen spec reads and does not write, "
          f"the record and the other half are unreachable, and ordinary work is untouched")
    return 0


if __name__ == "__main__":
    sys.exit(main())
