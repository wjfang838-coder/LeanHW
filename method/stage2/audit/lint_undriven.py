#!/usr/bin/env python3
"""Undriven-net probe: is the Verilog being scored the circuit that was proved?

    audit/lint_undriven.py <file.v|dir> [...] [--strict]

## Why

`Compiler.compileExpr` had a path where `.var n w` with an unresolved name fell through to
`fresh w` and **silently allocated a floating net** — the latch's name was not in the env that
`compileModuleM` built.  Every command stayed green: `build`, `check`, `sim` and `emit` all
passed, and the emitted netlist read an input that nothing drove.  Three authors located it
independently on different designs before it was believed.

The proof is about the Lean `Module`.  This scans the *artifact*.  It says nothing about
whether the design is correct — only whether the thing handed to the oracle is still the thing
the theorem was about.

Driver sources must be enumerated exhaustively or every wire looks undriven:

    assign x = ...          single target
    assign {a,b,c} = ...    concatenated lvalue (Yosys emits adder carries this way)
    x <= ... / x = ...      procedural assignment, including concatenated lvalues
    .PORT(net)              driven by a cell or instance
    input ...               input port

Paths are arguments.  The original version of this file carried a hard-coded list of
workspaces in a home directory as its default target, so running it with no arguments audited
somebody else's old run and reported a pass for work it had never looked at.
"""
import argparse
import glob
import os
import re
import sys

IDS = lambda s: set(re.findall(r"\b([A-Za-z_]\w*)\b", s))          # noqa: E731


def scan(path):
    src = open(path, errors="replace").read()
    src = re.sub(r"/\*.*?\*/", "", src, flags=re.S)
    src = re.sub(r"//[^\n]*", "", src)
    decl = set(re.findall(r"^\s*wire\s+(?:\[[^\]]*\]\s*)?(\w+)\s*;", src, re.M))
    driven = set()
    for m in re.finditer(r"(?:^|\bassign\b)([^;=<>!]*?)(?:<=|=(?!=))", src, re.M):
        driven |= IDS(m.group(1))                                  # any lvalue, incl. {a,b}
    for m in re.findall(r"\.\w+\s*\(\s*([^()]*?)\s*\)", src):
        driven |= IDS(m)                                           # cell / instance ports
    driven |= set(re.findall(r"^\s*input\s+(?:\[[^\]]*\]\s*)?(\w+)", src, re.M))
    return sorted(decl - driven)


def targets(paths):
    for p in paths:
        p = os.path.expanduser(p)
        if os.path.isdir(p):
            yield from sorted(glob.glob(os.path.join(p, "**", "*.v"), recursive=True))
        elif os.path.isfile(p):
            yield p
        else:
            print(f"lint_undriven: no such path: {p}", file=sys.stderr)


def main():
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("paths", nargs="+", help="Verilog files or directories to scan")
    ap.add_argument("--strict", action="store_true", help="exit 3 if any net is undriven")
    a = ap.parse_args()

    files = list(targets(a.paths))
    if not files:
        print("lint_undriven: nothing to scan (this is NOT a pass)")
        return 2
    bad = 0
    for p in files:
        u = scan(p)
        if u:
            bad += 1
            print(f"  {os.path.basename(p)[:-2]:30} {len(u)} undriven: {', '.join(u[:8])}")
    print(f"lint_undriven: {bad}/{len(files)} artifact(s) contain an undriven net")
    return 3 if (bad and a.strict) else 0


if __name__ == "__main__":
    sys.exit(main())
