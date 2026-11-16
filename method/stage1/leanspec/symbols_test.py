"""Every `LeanSpec` symbol the pipeline writes into a `.lean` file must exist.

`python3 -m leanspec.symbols_test`

Four stages of this half generate Lean and hand it to the elaborator: `diagnose` writes the query
harness, `propcheck` the property harness, `witness` the split search, and `emit` the deliverable
`DecidedSpec.lean`. None of that source is type-checked when it is *written*; it is a Python
string until something runs `lean` on it.

So a call to a declaration the library does not have is invisible until a case gets that far —
and `emit.gen_lean` had one. `#eval emitSweep case (admits decidedSpec)` was emitted into the step
07 deliverable, `emitSweep` had been dropped in the port (it is the last declaration before
`end SpecCheck` upstream, which is how a tail goes missing), and no case had ever reached step 07
to find out.

This checks the relation rather than either side: both the Python and the Lean read perfectly well
on their own, which is exactly why nothing was watching. It is the same shape as the third wall in
`docs/ARCHITECTURE.md` — a prompt and a grant that each look right — one layer down.

Only `#eval` heads are checked, because those are unambiguous. Theorem *statements* mention the
same library functions, but they are assembled from f-strings mixed with prose and there is no
honest way to tell an identifier from an English word without parsing Lean, which would be a worse
copy of the elaborator. `KNOWN_UNCHECKED` says so rather than leaving the limit implied.
"""
from __future__ import annotations

import glob
import re
import sys

#: What a case's own `Partial.lean` and the generated `DecidedSpec.lean` bring, as opposed to
#: what `LeanSpec` exports.  A generator may name these freely.
CASE_LOCAL = {
    "case", "admits", "legal", "ctxUniverse", "obsUniverse", "ctxCost",
    "ctxJson", "ctxLean", "obsJson", "defaultCfg", "decidedSpec",
    "Cfg", "Ctx", "Obs", "properties",
}

#: Generators, in the order a run reaches them.
GENERATORS = ("leanspec/diagnose.py", "leanspec/propcheck.py", "leanspec/witness.py",
              "leanspec/emit.py", "leanspec/pipeline.py", "leanspec/refine.py")

KNOWN_UNCHECKED = ("theorem statements — assembled from prose and f-strings, so telling an "
                   "identifier from an English word needs a Lean parser")

_DECL = re.compile(r"(?m)^\s*(?:def|abbrev|structure|inductive|instance|theorem)\s+"
                   r"([A-Za-z_][\w'!?]*)")
#: `#eval <head>` inside a Python string, plus the per-property/per-hole prefixed forms.
_EVAL = re.compile(r"#eval\s+([A-Za-z_]\w*)")


def exports() -> set[str]:
    """Everything `LeanSpec` declares, across the library's modules."""
    out: set[str] = set()
    for f in sorted(glob.glob("leanspec/lean/LeanSpec/*.lean")) + ["leanspec/lean/LeanSpec.lean"]:
        try:
            src = open(f).read()
        except FileNotFoundError:
            continue
        out |= {m.group(1) for m in _DECL.finditer(src)}
    return out


def emitted() -> dict[str, set[str]]:
    """`{symbol: {generator, ...}}` for every `#eval` head the pipeline writes."""
    out: dict[str, set[str]] = {}
    for f in GENERATORS:
        try:
            src = open(f).read()
        except FileNotFoundError:
            continue
        for m in _EVAL.finditer(src):
            out.setdefault(m.group(1), set()).add(f.split("/")[-1])
    return out


def main() -> int:
    have, used = exports(), emitted()
    if not have:
        print("BAD  no LeanSpec declarations found — run from the repository root")
        return 1
    if not used:
        print("BAD  no `#eval` found in any generator — the scan is looking at nothing")
        return 1

    missing = {k: v for k, v in used.items() if k not in have and k not in CASE_LOCAL}
    for name in sorted(used):
        where = ", ".join(sorted(used[name]))
        if name in missing:
            print(f"  BAD  {name:22} emitted by {where} — NOT DECLARED by LeanSpec")
        else:
            print(f"  ok   {name:22} {where}")

    print(f"\nnot checked: {KNOWN_UNCHECKED}")
    if missing:
        print(f"\n{len(missing)} symbol(s) would be an unknown identifier at elaboration:")
        for name in sorted(missing):
            print(f"  {name}")
        return 1
    print(f"symbols: all {len(used)} emitted symbols exist in the {len(have)} LeanSpec declares")
    return 0


if __name__ == "__main__":
    sys.exit(main())
