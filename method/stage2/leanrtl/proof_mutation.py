#!/usr/bin/env python3
"""Mutation testing for the PROOFS: can the proof system reject an incorrect implementation?

    python3 -m leanrtl.proof_mutation --ws ../data/part2/rtllm/accu/decided --key accu \
        [--rounds 2] [--workers 4] [--json OUT]

A design that builds green with `zero_sorry` and `axiom_clean` has proved SOMETHING about its
implementation.  Whether that something constrains the implementation is a different question,
and it has an experiment: break the implementation and see whether the proofs stop closing.

    KILLED     the mutated implementation type-checks, and a theorem below it fails.
               The proof was about the implementation, and it noticed.
    SURVIVED   everything still builds.  Either the mutation was semantically inert, or the
               proofs do not pin down the behaviour the mutation changed.

    mutation score = killed / (killed + survived)

## Why the mutations are constructor swaps and nothing cleverer

The implementation is a `LeanRTL.Expr` tree — `.add`, `.mux`, `.eq`, `.var "cnt" 2` — and `Expr`
is indexed by bit width, so most textual edits to it do not type-check.  A mutant that fails to
ELABORATE is not evidence that a proof rejected it; it is evidence that the edit was invalid, and
counting it as a kill would let a mutation operator that produces nothing but syntax errors score
100%.

So every operator here swaps one constructor for another with the IDENTICAL signature, taken from
`framework/LeanRTL/Core/Syntax.lean`:

    add sub mul udiv umod    {w} -> Expr w -> Expr w -> Expr w
    and or xor               {w} -> Expr w -> Expr w -> Expr w
    shl shr sshr             {w k} -> Expr w -> Expr k -> Expr w
    eq ult slt               {w} -> Expr w -> Expr w -> Expr 1
    zext sext                {w} -> (k : Nat) -> Expr w -> Expr (w + k)

plus two literal edits that cannot change a type at all: a `.const n` becomes `.const (n+1)`, and
a register's `init := 0` becomes `init := 1`.  The result is a mutant that is a DIFFERENT CIRCUIT
of the same shape, which is exactly what the proofs are supposed to notice.

Mutants that fail to elaborate anyway are reported as `impl_broken` and excluded from the score
rather than dropped, because "how often did the operator produce an invalid edit" is a fact about
this instrument that a reader should be able to see.

## Comments and string literals are masked, and that is not a detail

`.var "add" 8` names a wire.  Rewriting the four letters inside those quotes produces a file that
still builds and still proves everything, and it would be counted as a survivor — evidence that
the proofs are weak, drawn from an edit that changed nothing but a name.  The same goes for the
word `add` inside a docstring.  The Verilog version of this mistake is on record: two "survivors"
that turned out to be edits to comment text.  So a mask over comments (`--`, `/- -/`, `/-- -/`,
nested) and string literals is computed first, and no site inside one is ever a mutation site.

## The verdict comes from WHERE the errors land

`scripts/bb.py`'s four scaffold markers divide the file into `impl`, `spec`, `l1` and
`whole-trace`.  Lean reports every error with a line number, so the verdict is read off the line
numbers, in this order:

  * any error inside the `impl` section  ->  `impl_broken`, excluded.  The mutated definition did
    not elaborate; every error below it is a cascade off a definition that does not exist, so the
    proofs never ran and nothing was rejected.  This is decided FIRST and wins even when errors
    also appear further down, because the alternative lets an operator that produces nothing but
    ill-typed edits score 100%.
  * any error inside the `spec` section  ->  `spec_broken`, reported on its own.  A mutation to
    the implementation should not be able to break the specification, and one that does says
    something about how entangled the two are.  Under two-author authoring it says more: the
    specification was written first, by someone who never saw this implementation, so an
    implementation edit reaching it means the freeze did not buy what it was supposed to.
  * any error below                      ->  `killed_by_proof`.
  * no error located at all, rc != 0     ->  `unattributable`, excluded.

A file whose markers are missing or out of order cannot be read this way; it is reported under
`unattributable` and not scored.

## Nothing in the workspace is touched

Each mutant is written to `<ws>/.mutants/` and built with `lake env lean` from the workspace root,
which sets `LEAN_PATH` and does not care where the file sits.  `LeanRTL/Blind/*.lean` — the
evidence this round reports — is opened read-only and never written.
"""
from __future__ import annotations

import argparse
import collections
import concurrent.futures as cf
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAKE = os.path.expanduser("~/.elan/bin/lake")

# The same four markers `scripts/bb.py` hashes the file by.
MARKERS = [("impl", "/-! ## 1. impl"), ("spec", "/-! ## 2. spec"),
           ("l1", "/-! ## 3. L1"), ("wt", "/-! ## 4. whole-trace")]
BLIND_HDR = re.compile(r"^--\s*@blind\s+(\S+)", re.M)
ERR = re.compile(r"^(?P<file>[^:\n]+):(?P<line>\d+):(?P<col>\d+):\s*error:", re.M)

# Signature-identical swaps.  `(from, to)` — applied one site at a time.
SWAPS = [("add", "sub"), ("sub", "add"), ("mul", "add"), ("udiv", "umod"), ("umod", "udiv"),
         ("and", "or"), ("or", "and"), ("xor", "and"),
         ("shl", "shr"), ("shr", "shl"), ("sshr", "shr"),
         ("eq", "ult"), ("ult", "eq"), ("slt", "ult"),
         ("zext", "sext"), ("sext", "zext")]
# A constructor reference: `.add`, `Expr.add`, `.add ` — matched with the leading dot so that a
# field named `add` on some other structure is not a site.
CTOR = "(?<![\\w.])\\.{name}(?![\\w'])"
CONST = re.compile(r"(?<![\w.])\.const\s+(\d+)(?![\w'.])")
INIT0 = re.compile(r"(?<![\w])init\s*:=\s*0(?![\w'.])")


def mask(src: str) -> list[bool]:
    """True at every index that is INSIDE a comment or a string literal.

    Lean block comments nest, so the depth is counted rather than searched for a closing token;
    `/-- doc -/` is a block comment as far as this is concerned.  A `--` inside a string is not a
    line comment, and a `"` inside a comment does not open a string, so the three states are
    tracked in one pass instead of three.
    """
    out = [False] * len(src)
    i, depth, in_line, in_str = 0, 0, False, False
    while i < len(src):
        c = src[i]
        if in_line:
            out[i] = True
            if c == "\n":
                in_line = False
            i += 1
            continue
        if in_str:
            out[i] = True
            if c == "\\":
                if i + 1 < len(src):
                    out[i + 1] = True
                i += 2
                continue
            if c == '"':
                in_str = False
            i += 1
            continue
        if depth:
            out[i] = True
            if src.startswith("/-", i):
                depth += 1
                out[i + 1] = True
                i += 2
                continue
            if src.startswith("-/", i):
                depth -= 1
                out[i + 1] = True
                i += 2
                continue
            i += 1
            continue
        if src.startswith("/-", i):
            depth = 1
            out[i] = out[i + 1] = True
            i += 2
            continue
        if src.startswith("--", i):
            in_line = True
            out[i] = True
            i += 1
            continue
        if c == '"':
            in_str = True
            out[i] = True
            i += 1
            continue
        i += 1
    return out


def sections(src: str) -> dict[str, tuple[int, int]] | None:
    """section -> (first line, last line), 1-based inclusive, or None when the markers degrade."""
    pos = []
    for name, m in MARKERS:
        mt = re.search(r"(?m)^" + re.escape(m), src)
        pos.append((name, mt.start() if mt else -1))
    if any(i < 0 for _, i in pos) or [i for _, i in pos] != sorted(i for _, i in pos):
        return None
    out, n = {}, len(src)
    for k, (name, start) in enumerate(pos):
        end = pos[k + 1][1] if k + 1 < len(pos) else n
        out[name] = (src.count("\n", 0, start) + 1, src.count("\n", 0, end) + 1)
    return out


def sites(src: str, lo: int, hi: int) -> list[dict]:
    """Every mutation site inside `src[lo:hi]`, outside comments and strings."""
    m = mask(src)
    found = []
    for frm, to in SWAPS:
        for mt in re.finditer(CTOR.format(name=re.escape(frm)), src):
            if lo <= mt.start() < hi and not m[mt.start()]:
                found.append({"kind": f"{frm}->{to}", "at": mt.start(), "end": mt.end(),
                              "text": f".{to}"})
    for mt in CONST.finditer(src):
        if lo <= mt.start() < hi and not m[mt.start()]:
            found.append({"kind": "const+1", "at": mt.start(), "end": mt.end(),
                          "text": f".const {int(mt.group(1)) + 1}"})
    for mt in INIT0.finditer(src):
        if lo <= mt.start() < hi and not m[mt.start()]:
            found.append({"kind": "init0->1", "at": mt.start(), "end": mt.end(),
                          "text": "init := 1"})
    found.sort(key=lambda s: s["at"])
    return found


def pick(found: list[dict], rounds: int) -> list[dict]:
    """Round k takes the k-th site of every KIND, so one prolific operator cannot crowd out the
    rest — a design with forty `.add`s and one `.eq` would otherwise be scored almost entirely on
    whether its adder is pinned down."""
    by = collections.defaultdict(list)
    for s in found:
        by[s["kind"]].append(s)
    out = []
    for r in range(rounds):
        for kind in sorted(by):
            if r < len(by[kind]):
                out.append(by[kind][r])
    return out


def build(ws: str, rel: str, timeout: int) -> tuple[int, str, bool]:
    try:
        p = subprocess.run([LAKE, "env", "lean", rel], cwd=ws, capture_output=True, text=True,
                           timeout=timeout)
        return p.returncode, (p.stdout or "") + (p.stderr or ""), False
    except subprocess.TimeoutExpired:
        return -1, "", True


def run_one(ws: str, key: str, path: str, s: dict, i: int, timeout: int) -> dict:
    src = open(path, errors="replace").read()
    mutant = src[: s["at"]] + s["text"] + src[s["end"]:]
    name = f"{key}.{i}.lean"
    rel = os.path.join(".mutants", name)
    open(os.path.join(ws, rel), "w").write(mutant)
    rc, log, to = build(ws, rel, timeout)
    sec = sections(mutant)
    lines = sorted({int(m.group("line")) for m in ERR.finditer(log)
                    if os.path.basename(m.group("file")) == name})
    row = {"key": key, "kind": s["kind"], "mutant": i,
           "original": src[s["at"]: s["end"]], "replacement": s["text"],
           "line": src.count("\n", 0, s["at"]) + 1,
           "rc": rc, "n_errors": len(lines), "error_lines": lines[:8],
           "first_error": (ERR.search(log).group(0) if ERR.search(log) else "")}
    if to:
        row["verdict"] = "timeout"
    elif rc == 0:
        row["verdict"] = "survived"
    elif sec is None:
        row["verdict"] = "unattributable"
    else:
        impl_lo, impl_hi = sec["impl"]
        spec_lo, spec_hi = sec["spec"]
        l1_lo = sec["l1"][0]
        in_impl = [l for l in lines if impl_lo <= l < impl_hi]
        in_spec = [l for l in lines if spec_lo <= l < spec_hi]
        below = [l for l in lines if l >= l1_lo]
        # Order matters, and this is the ordering the score depends on.  An error inside the
        # `impl` section means the mutated definition did not elaborate; every error below it is
        # then a cascade off a definition that does not exist, so the file's proofs never ran and
        # nothing was rejected.  Counting that as a kill would let an operator that only produces
        # ill-typed edits score 100%.  So `impl_broken` is decided FIRST and wins even when there
        # are errors further down.
        if in_impl:
            row["verdict"] = "impl_broken"
        elif in_spec:
            row["verdict"] = "spec_broken"
        elif below:
            row["verdict"] = "killed_by_proof"
        elif lines:
            row["verdict"] = "killed_by_proof"        # errors, but between spec and L1
        else:
            row["verdict"] = "unattributable"          # rc != 0 with no located error
    try:
        os.remove(os.path.join(ws, rel))
    except OSError:
        pass
    return row


def blind_file(ws: str, key: str) -> str | None:
    """The assembled file whose `-- @blind` header names `key`.

    By header rather than by filename: `camel_of` is the only thing that knows how a key becomes a
    module name, and a second place that thinks it knows is a second place that can be wrong.
    """
    bdir = os.path.join(ws, "LeanRTL", "Blind")
    if not os.path.isdir(bdir):
        return None
    for fn in sorted(os.listdir(bdir)):
        if not fn.endswith(".lean"):
            continue
        p = os.path.join(bdir, fn)
        m = BLIND_HDR.search(open(p, errors="replace").read())
        if m and m.group(1) == key:
            return p
    return None


def mutate(ws: str, key: str, rounds: int = 2, workers: int = 4, timeout: int = 1200) -> dict:
    """The whole measurement, as a function, so `pipeline.py` does not shell out to its own CLI."""
    path = blind_file(ws, key)
    if path is None:
        return {"key": key, "error": "no `-- @blind` file for this key under LeanRTL/Blind/",
                "mutants": 0, "killed": 0, "survived": 0, "mutation_score": "— undefined"}

    src = open(path, errors="replace").read()
    if sections(src) is None:
        # Not scored, and named rather than dropped.  A design whose markers degraded is a design
        # this instrument cannot read, which is a different fact from a design whose proofs are
        # weak, and reporting the two the same way is how a weak instrument passes for a strong
        # result.
        return {"key": key, "markers": "degraded", "mutants": 0, "killed": 0, "survived": 0,
                "mutation_score": "— undefined",
                "why": "the four scaffold section markers are missing or out of order, so an "
                       "error's line number cannot be attributed to a section and a kill cannot "
                       "be told from a mutant that simply did not elaborate"}

    lo = src.find(MARKERS[0][1])
    hi = src.find(MARKERS[1][1])
    found = sites(src, lo, hi)
    chosen = pick(found, rounds)

    mdir = os.path.join(ws, ".mutants")
    os.makedirs(mdir, exist_ok=True)
    rows = []
    try:
        with cf.ThreadPoolExecutor(max_workers=workers) as ex:
            futs = [ex.submit(run_one, ws, key, path, s, i, timeout)
                    for i, s in enumerate(chosen)]
            for n, f in enumerate(cf.as_completed(futs), 1):
                r = f.result()
                rows.append(r)
                print(f"  [{n}/{len(chosen)}] {r['kind']:12} line {r['line']:<5} {r['verdict']}",
                      flush=True)
    finally:
        shutil.rmtree(mdir, ignore_errors=True)

    tally = collections.Counter(r["verdict"] for r in rows)
    killed, survived = tally["killed_by_proof"], tally["survived"]
    scored = killed + survived
    return {
        "key": key, "markers": "ok", "file": os.path.relpath(path, ws),
        "rounds": rounds, "sites": len(found), "mutants": len(rows),
        "verdicts": dict(tally),
        "mutation_score": (f"{killed}/{scored} ({100 * killed / scored:.0f}%)" if scored
                           else "0/0 — undefined"),
        "killed": killed, "survived": survived,
        "excluded": {"impl_broken": tally["impl_broken"], "timeout": tally["timeout"],
                     "unattributable": tally["unattributable"],
                     "why": "a mutant that does not elaborate is evidence about the mutation "
                            "operator, not about the proofs, so it is named and excluded rather "
                            "than counted as a kill"},
        "spec_broken": tally["spec_broken"],
        "spec_broken_note": "a mutation to the implementation broke the SPECIFICATION section. "
                            "The two are supposed to be independent statements about the design; "
                            "where they are not, the refinement theorem has less to say than its "
                            "name suggests. Under two-author authoring it is stronger than that: "
                            "the specification was frozen before this implementation existed, so "
                            "an implementation edit that reaches it means the two are entangled "
                            "through something the freeze does not cover.",
        "by_kind": {k: dict(collections.Counter(r["verdict"] for r in rows if r["kind"] == k))
                    for k in sorted({r["kind"] for r in rows})},
        "mutants_detail": rows,
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ws", required=True)
    ap.add_argument("--key", required=True)
    ap.add_argument("--rounds", type=int, default=2)
    ap.add_argument("--workers", type=int, default=4)
    ap.add_argument("--timeout", type=int, default=1200)
    ap.add_argument("--json")
    ap.add_argument("--force", action="store_true",
                    help="measure even when the certification gates are not green")
    a = ap.parse_args(argv)

    ws = os.path.abspath(os.path.expanduser(a.ws))
    # Mutating a design whose proofs already fail measures nothing about the proofs: every mutant
    # comes back red because the file was red to begin with, and the score reads 100%.  The
    # workspace's own `verify.json` is the check, and `--force` is the escape hatch for looking at
    # a design deliberately.
    vp = os.path.join(ws, "verify.json")
    if not a.force:
        if not os.path.isfile(vp):
            sys.exit("proof_mutation: no verify.json in this workspace — run "
                     "`python3 -m leanrtl.verify` first, or pass --force.  A mutation score over "
                     "proofs that do not close is not a fact about the proofs.")
        v = json.load(open(vp))
        if not (v.get("design") or {}).get("all_pass"):
            sys.exit("proof_mutation: this workspace's gates are not green — "
                     f"{(v.get('design') or {}).get('summary', 'see verify.json')}.  Pass --force "
                     "to measure anyway, and say so wherever the number is quoted.")

    out = mutate(ws, a.key, a.rounds, a.workers, a.timeout)
    print(f"\nmutation score {out['mutation_score']}   "
          f"(killed {out['killed']}, survived {out['survived']}"
          + (f"; excluded: {out['excluded']['impl_broken']} did not elaborate, "
             f"{out['excluded']['timeout']} timed out, "
             f"{out['excluded']['unattributable']} unattributable)" if "excluded" in out else ")"))
    if out.get("spec_broken"):
        print(f"  {out['spec_broken']} mutant(s) broke the SPEC section — see spec_broken_note")
    if out.get("markers") == "ok" and out["killed"] == 0 and out["survived"]:
        print("  this design killed no mutant at all — its proofs do not constrain the "
              "behaviour these operators change")

    dest = a.json or os.path.join(ws, "out", "proof_mutation.json")
    os.makedirs(os.path.dirname(os.path.abspath(dest)), exist_ok=True)
    json.dump(out, open(dest, "w"), indent=1)
    print(f"wrote {dest}")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
