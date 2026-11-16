#!/usr/bin/env python3
"""bbf — role wrapper: assembles the design from role fragments, then delegates to `bb`.

    python3 scripts/bbf.py <key> <cmd> --role S|D|H [--frag spec|impl|proof]

cmds:
    build    assemble (full, or --frag scoped) then bb build (type-check)
    commit   record this role's fragment sha
    simdiff  assemble full + run the spec-vs-impl vector diff gate
    check | sim | cosim | emit | audit    assemble full + bb <cmd>

S owns `frags/<key>/spec.lean`.  D owns `impl.lean` and `proof.lean`.  The assembled
`LeanRTL/Blind/<Camel>.lean` is harness-generated and belongs to neither.

## What changed with serial authoring, and what it cost

This wrapper was written for a BLIND PARALLEL pair — a specification author S and an
implementation author R running at the same time, neither able to see the other's fragment,
so that a disagreement between the two was evidence about the prose rather than about either
of them.  Enforcing that was most of this file: until both had committed, a role-attributed
command assembled with ONLY the caller's fragment and stubbed the rest.

That guard existed because the earlier form assembled the FULL design and ran `lake env lean`
on it, so when the other author's fragment was mid-edit and red, THEIR identifiers, simp sets
and rendered proof goals were printed to this author's stdout.  Role R found it and reported it
rather than reading on; the log confirmed the committed implementation sha predated the first
exposure, so that run survived — but only by the luck of the timing.

Serial authoring removes the condition the guard was protecting: S commits, the specification is
frozen, and only then does D start, having READ it.  Keeping the stub-out would now be actively
wrong — D's implementation would type-check against a stubbed specification and then be handed
to a proof step that sees the real one, which is a build that goes green on a file nobody will
ever assemble.

So the wall moved rather than disappearing.  It used to be that D could not READ the
specification; now D cannot WRITE it — `frags/<key>/spec.lean` is mode 0444 and on the tool
layer's deny list.  This file enforces the ordering half of that: it refuses to run as D at all
until S has committed, because a D that starts early is building against a document that is
still moving.
"""
import os, sys, json, time, hashlib, subprocess, fcntl

WS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(WS, "scripts"))
import bb        # noqa: E402
import asm_f     # noqa: E402

# The fragment a role commits when it does not say which.  D owns two, and `impl` is the one it
# writes first; the proof phase passes `--frag proof` explicitly.
ROLE_FRAG = {"S": "spec", "D": "impl"}
OWNS = {"S": ("spec",), "D": ("impl", "proof"), "H": ()}
# The assembly scope a fragment-scoped build gets.  `impl` for D resolves to `impl+spec` because
# under serial authoring the implementation is written against the frozen specification and has
# to compile against the real one.
SCOPE = {("S", "spec"): "spec", ("D", "impl"): "impl+spec", ("D", "proof"): None}
# NOT `.bb.lock`: that one belongs to bb.py, and sharing it deadlocks parent on child.
ASM_LOCK = os.path.join(WS, ".bbf-assemble.lock")



def committed(key, role):
    return os.path.isfile(os.path.join(WS, "frags", key, role + ".committed"))


def frag_sha(key, frag):
    p = os.path.join(WS, "frags", key, frag + ".lean")
    return hashlib.sha256(open(p, "rb").read()).hexdigest()[:12] if os.path.isfile(p) else None


def log_role(key, cmd, role, rc, extra=None):
    e = {"ts": round(time.time(), 3), "iso": time.strftime("%Y-%m-%dT%H:%M:%S"),
         "key": key, "cmd": "f_" + cmd, "role": role, "rc": rc,
         "frag_sha": {f: frag_sha(key, f) for f in ("impl", "spec", "proof")},
         "sec_sha": {}, "file_sha": "", "err_class": "green" if rc == 0 else "fail",
         "err_head": "", "wall_s": 0}
    if extra:
        e.update(extra)
    bb.log(key, e)


def passthrough(argv):
    """Everything after the command that is not this wrapper's own flag.

    `--N 2,2` belongs to `bb.py` and is how an author exercises a parameterised design at a
    vector other than the default — which the manual calls the failure mode that costs the most
    designs, because the default vector is the one instance that cannot reveal it.  Swallowing it
    here would have made every `--N` in this workspace silently run the defaults and report
    green, which is worse than not offering the flag.
    """
    out, i = [], 3
    while i < len(argv):
        if argv[i] in ("--role", "--frag"):
            i += 2
            continue
        out.append(argv[i])
        i += 1
    return out


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    key, cmd = sys.argv[1], sys.argv[2]
    role = sys.argv[sys.argv.index("--role") + 1] if "--role" in sys.argv else "?"
    frag = sys.argv[sys.argv.index("--frag") + 1] if "--frag" in sys.argv else None
    rest = passthrough(sys.argv)

    if frag and role in OWNS and frag not in OWNS[role]:
        print(f"bbf: role {role} does not own `{frag}`.  S owns the specification; D owns the "
              f"implementation and the proofs.", file=sys.stderr)
        return 2

    # The ordering half of the freeze.  D writes against a specification that is supposed to be
    # settled, and one that has not been committed is still moving: an implementation built
    # against a draft compiles today and is about a different document tomorrow, with nothing in
    # the record saying which one it was written for.
    if role == "D" and not committed(key, "S"):
        print(f"bbf: refusing to run as D — S has not committed `frags/{key}/spec.lean`.  "
              f"An implementation written against an uncommitted specification is written "
              f"against a draft, and no later artifact records which draft.", file=sys.stderr)
        return 2

    if cmd == "commit":
        f = frag or ROLE_FRAG.get(role)
        if not f or frag_sha(key, f) is None:
            print(f"bbf: nothing to commit for role {role}"
                  + (f" (no frags/{key}/{f}.lean)" if f else ""))
            return 1
        open(os.path.join(WS, "frags", key, role + ".committed"), "w").write(
            frag_sha(key, f) + "\n")
        log_role(key, "commit", role, 0, {"frag_scope": f})
        print(f"bbf: committed {role} fragment {f} {frag_sha(key, f)}")
        return 0

    if cmd == "simdiff":
        import simdiff_f
        rc = simdiff_f.run(key)
        log_role(key, "simdiff", role, rc)
        return rc

    if cmd == "build":
        if frag:
            if frag_sha(key, frag) is None:
                # Without this, `build --frag spec` assembles the STUB in that slot, type-checks
                # it, and reports rc=0 — a green build of a file the author has not written.  A
                # tool that says yes before there is anything to say yes about teaches its user
                # to stop reading its output.
                print(f"bbf: there is no frags/{key}/{frag}.lean to build.  Write it first; "
                      f"building now would type-check the placeholder and call it green.",
                      file=sys.stderr)
                return 2
            # Per-role PRIVATE assembly: a fragment-scoped check never touches the canonical
            # assembled file, so a build that fails leaves the last good full assembly alone.
            scope = SCOPE.get((role, frag), frag)
            camel = asm_f.camel_of(key)
            priv = os.path.join(WS, "scratch", "asm", role, camel + ".lean")
            asm_f.assemble(key, scope, out_path=priv)
            r = subprocess.run([os.path.expanduser("~/.elan/bin/lake"), "env", "lean",
                                os.path.relpath(priv, WS)], cwd=WS)
            log_role(key, "build", role, r.returncode, {"frag_scope": scope or "full"})
            return r.returncode
        asm_f.assemble(key)
        r = subprocess.run([sys.executable, os.path.join(WS, "scripts", "bb.py"),
                            key, "build"] + rest)
        log_role(key, "build", role, r.returncode, {"frag_scope": "full"})
        return r.returncode

    if cmd in ("check", "sim", "cosim", "emit", "audit"):
        # Full assembly, held under a lock of its own.  Nothing is stubbed out by role any more
        # — see the module docstring — but the lock stays: `launch.py` may have several designs
        # in flight in one workspace, and two of them assembling at once still race on the
        # canonical file.  A separate lock file keeps it from ever aliasing bb.py's, which
        # deadlocked parent on child the one time they were shared.
        stdin = sys.stdin.read() if cmd == "sim" else None
        with open(ASM_LOCK, "a") as lk:
            fcntl.flock(lk, fcntl.LOCK_EX)
            asm_f.assemble(key)
            fcntl.flock(lk, fcntl.LOCK_UN)
        r = subprocess.run([sys.executable, os.path.join(WS, "scripts", "bb.py"),
                            key, cmd] + rest, input=stdin, text=True)
        log_role(key, cmd, role, r.returncode, {"frag_scope": "full"})
        return r.returncode

    print(__doc__)
    return 2


if __name__ == "__main__":
    sys.exit(main())
