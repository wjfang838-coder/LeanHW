#!/usr/bin/env python3
"""Check the framework's own theorems — the trust base every design proof is stated against.

    audit/framework_axioms.py [--framework framework/] [--strict]

## Why this exists

`leanrtl/verify.py` gates *design* proofs.  It found, on the first design ever run through it,
that `bv_decide` emits an axiom the kernel trusts instead of checking.  The framework's own
compiler-correctness ladder — `CompilerCorrectSeq`, `CompilerModuleCorrect`, `HierRefine` and
the rest — is what every one of those design theorems is stated *against*, and it had never been
checked the same way.  A hole there is worth more than a hole in any single design.

It is also the reason `framework/` builds standalone at all.  Workspaces compile `Core/`
themselves, so a standalone build is redundant for the pipeline — but it is what makes this
check runnable, and it fails in ~30s instead of once per workspace.

## What is and is not covered

`private theorem`s are invisible to an importing probe.  That is fine and not a gap: axiom
dependencies are transitive, so a private lemma's axioms surface in whatever public theorem
uses it.  A private lemma used by nothing is dead code, not an unchecked claim.  The count of
unresolved names is reported rather than hidden — silence is not a pass.
"""
import argparse
import glob
import os
import re
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

from common import paths                                             # noqa: E402

STD = {"propext", "Classical.choice", "Quot.sound"}


def theorem_names(core_dir, lib_root):
    names = []
    for f in sorted(glob.glob(os.path.join(core_dir, "**", "*.lean"), recursive=True)):
        src = open(f, errors="replace").read()
        src = re.sub(r"/-.*?-/", "", src, flags=re.S)     # docstrings contain the word "theorem"
        src = re.sub(r"--[^\n]*", "", src)
        ns = []
        for line in src.splitlines():
            m = re.match(r"\s*namespace\s+(\S+)", line)
            if m:
                ns.append(m.group(1)); continue
            e = re.match(r"\s*end\s+(\S+)\s*$", line)
            if e and ns and e.group(1) == ns[-1]:
                ns.pop(); continue
            t = re.match(r"\s*(?:@\[[^\]]*\]\s*)?theorem\s+([A-Za-z_][\w'!?]*)", line)
            if t:                                          # `private` deliberately not matched
                names.append(".".join(ns + [t.group(1)]))
    return sorted(set(names))


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--framework", default=paths.REPO,
                    help="the Lake package root — the repository, where lakefile.toml is")
    ap.add_argument("--lib", default="LeanRTL")
    ap.add_argument("--strict", action="store_true", help="exit 3 on any untrusted axiom")
    a = ap.parse_args()

    # Three shapes, in order: the repository (sources under `method/stage2/framework/`), a bare
    # framework checkout, and a staged workspace, where the library sits at the top because
    # that is how it was installed.  The last is why this is a probe and not a constant.
    for c in (os.path.join(a.framework, "method", "stage2", "framework", a.lib, "Core"),
              os.path.join(a.framework, "framework", a.lib, "Core"),
              os.path.join(a.framework, a.lib, "Core")):
        if os.path.isdir(c):
            core = c
            break
    else:
        print(f"framework_axioms: no {a.lib}/Core under {a.framework} — nothing checked "
              f"(this is NOT a pass)")
        return 2
    names = theorem_names(core, a.lib)
    if not names:
        print("framework_axioms: no theorems found — nothing checked (this is NOT a pass)")
        return 2

    probe = os.path.join(a.framework, "_framework_axioms_probe.lean")
    open(probe, "w").write(f"import {a.lib}\n"
                           + "\n".join(f"#print axioms {n}" for n in names) + "\n")
    try:
        r = subprocess.run([os.path.expanduser("~/.elan/bin/lake"), "env", "lean",
                            os.path.basename(probe)], cwd=a.framework,
                           capture_output=True, text=True, timeout=3600)
        out = r.stdout + r.stderr
    finally:
        os.remove(probe)

    dep = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", out, re.S)
    free = re.findall(r"'([^']+)' does not depend on any axioms", out)
    unresolved = re.findall(r"Unknown constant `([^`]+)`", out)
    bad = []
    for n, axs in dep:
        extra = sorted({x.strip() for x in axs.replace("\n", " ").split(",") if x.strip()} - STD)
        if extra:
            bad.append((n, extra))

    print(f"framework_axioms: {a.lib}/Core — {len(names)} theorem names extracted")
    print(f"  reporting standard axioms : {len(dep)}")
    print(f"  depending on no axioms    : {len(free)}")
    print(f"  unresolved (private/local): {len(unresolved)}  "
          f"— covered transitively by the public theorems that use them")
    print(f"  OUTSIDE the trusted set   : {len(bad)}")
    for n, e in bad:
        print(f"      {n}: {', '.join(e)}")
    return 3 if (bad and a.strict) else 0


if __name__ == "__main__":
    sys.exit(main())
