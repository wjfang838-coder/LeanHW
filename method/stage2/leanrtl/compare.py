#!/usr/bin/env python3
"""Do two arms of the same design behave differently, and is the difference one the specification
left free?

    python3 -m leanrtl.compare --key accu <ws> <ws> [<ws> ...]
    python3 -m leanrtl.compare --key accu --all          # every finished workspace for that key
    python3 -m leanrtl.compare --key accu --all --preproof   # …and each one's pre-proof Verilog

## Why this is not in `launch.py`

`launch` runs arms and refuses to compare them, on purpose: an orchestrator that also scores is
an orchestrator with an experimental design baked into it, and the two then cannot be separated.
This file is that experimental design, kept apart so it can be wrong without the pipeline being
wrong.  Nothing in `leanrtl/` may import it.

## Two questions, one table

The arms differ in ONE input: which prose the specification author read.  One arm got the
original description, another the prose after `leanSpec` adjudicated its ambiguities.  If the
decided prose closed a real ambiguity, the two implementations should disagree about it — and if
they agree everywhere, the ambiguity was either not real or not reachable, which is equally worth
knowing and is the finding nobody reports because no one looks.

`--preproof` adds a second, orthogonal question to the same table.  Each workspace produces two
Verilog modules — the implementation emitted before the proof phase and the same implementation
after it (see `leanrtl/preproof.py`) — and comparing those two asks whether PROVING changed the
circuit, with prose, author and session all held fixed.  With both flags the rows factor: across
workspaces the variable is the specification, within a workspace it is the proof.  The pair
verdict below says which of the two it is looking at, because the same divergence count means
completely different things in the two directions.

## What is actually being asked

So the comparison is behavioural, not textual.  Emitted Verilog differs in wire numbering and
register count for reasons that have nothing to do with meaning; the same three arms here carry
27, 8 and 19 registers and could still implement the same function.  Every arm is driven with
BYTE-IDENTICAL stimulus and the output traces are diffed.

## Three regimes, because not every difference is a defect

`leanSpec` finishes with a list of coordinates it deliberately left open — on `accu`:
`h_data_out_between_pulses`, `h_reset_kind`, `h_reset_data_out`, `h_reset_partial_sum`,
`h_clock_edge`.  Those are undetermined ON PURPOSE: the designer was asked and was indifferent,
or the coordinate is unobservable.  Two arms may differ there and both be correct.

A single trace diff cannot tell those apart from a real disagreement, so the stimulus is split
to separate them:

    pulsed   outputs sampled ONLY on cycles where valid_out is high, no reset after init.
             This is the accumulate-and-group semantics — what round 1 and round 2 actually
             adjudicated.  A divergence here is a REAL disagreement about the decided reading.

    quiet    every cycle sampled, still no reset.  Adds what `data_out` shows BETWEEN pulses,
             which is `h_data_out_between_pulses` and is open.  A divergence that appears here
             but not in `pulsed` is explained by the specification, not by an author.

    reset    resets injected mid-stream.  Adds the three reset coordinates, all open.  Same
             reading: new divergence here is licensed.

The regimes nest, so the classification is a subtraction and not a judgement call.

## What it does not do

It does not say which arm is right.  There is no reference implementation in this repository —
`leanSpec` never had one, that is the point of it — so a divergence is reported as a divergence,
with the cycle and the stimulus that produced it, for a human to read.
"""
from __future__ import annotations

import argparse
import json
import os
import random
import re
import shutil
import subprocess
import sys
import tempfile

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

from common import paths   # noqa: E402
from leanrtl import preproof   # noqa: E402

CYCLES = 400
SEED = 20260830


# --------------------------------------------------------------------------- stimulus

def stimulus(regime: str) -> list[tuple[int, int, int]]:
    """`(rst_n, valid_in, data_in)` per cycle, identical for every arm in a regime.

    Drawn from `random.Random(SEED)` rather than an LFSR in the testbench so that the vectors are
    a Python object this file can print next to a divergence.  A stimulus you cannot quote is one
    you cannot argue about.

    `valid_in` is high 60% of the time.  Not 50%, because the interesting cycles are the ones
    that COMPLETE a group of four, and a stream that idles half the time reaches fewer of them in
    a fixed budget.  Not 100%, because a gap between valid inputs is exactly where an
    implementation that counts cycles instead of counting valid inputs gives itself away.
    """
    rng = random.Random(SEED)
    out = []
    for c in range(CYCLES):
        # Cycles 0-3 hold reset for every regime: an arm that starts mid-air is not being
        # compared, it is being guessed at.
        if c < 4:
            out.append((0, 0, 0))
            continue
        rst = 1
        if regime == "reset":
            # Sparse and aperiodic.  A reset every N cycles would land on the same phase of the
            # group counter every time and could miss the case the reset coordinates are about:
            # a reset arriving with a partial sum already accumulated.
            if c in (97, 98, 211, 305, 306, 307):
                rst = 0
        out.append((rst, 1 if rng.random() < 0.6 else 0, rng.randrange(256)))
    return out


TB = """\
`timescale 1ns/1ps
module tb;
  reg clk = 0, rst_n = 0, valid_in = 0;
  reg [7:0] data_in = 0;
  wire valid_out;
  wire [9:0] data_out;
  reg [9:0] rst_v [0:{n}];
  reg [9:0] vin_v [0:{n}];
  reg [9:0] din_v [0:{n}];
  integer c;
  accu dut(.clk(clk), .rst_n(rst_n), .data_in(data_in), .valid_in(valid_in),
           .valid_out(valid_out), .data_out(data_out));
  always #5 clk = ~clk;
  initial begin
    $readmemh("rst.hex", rst_v);
    $readmemh("vin.hex", vin_v);
    $readmemh("din.hex", din_v);
    for (c = 0; c < {n}; c = c + 1) begin
      @(negedge clk);
      rst_n    = rst_v[c][0];
      valid_in = vin_v[c][0];
      data_in  = din_v[c][7:0];
      #4 $display("%0d %b %0d", c, valid_out, data_out);
      @(posedge clk);
    end
    $finish;
  end
endmodule
"""


def trace(vpath: str, vec: list[tuple[int, int, int]], work: str) -> list[tuple[int, int, int]]:
    """Simulate one arm's Verilog on `vec`; return `(cycle, valid_out, data_out)` per cycle.

    Driven on the falling edge and sampled 4 ns later — one nanosecond BEFORE the rising edge that
    ends the cycle.  That probe point is the whole reason this function has a comment.

    The first version sampled `#1` AFTER the rising edge, which is the one instant that reads a
    Mealy design wrong: the registers have advanced to the next state but the inputs are still the
    previous cycle's.  `accu` was emitted both ways by different arms — `original` registers its
    outputs (`assign valid_out = vout;` with `vout <= …` in the clocked block), `.r2prose` drives
    them combinationally (`assign valid_out = rst_n & valid_in & (cnt == 2'd3)`) — and against the
    post-edge probe the combinational arms appeared to pulse a cycle early carrying a sum that
    double-counted the current input.  Neither was true.  `acc` had absorbed `data_in` at the edge
    and the combinational `acc + data_in` then added it a second time, purely because the probe
    stood between the two.

    Sampling before the rising edge is correct for both styles and is what a real testbench does:
    a registered output shows the value its last edge established, a combinational one shows the
    value its current inputs imply, and a consumer clocking on that same edge captures exactly
    what is sampled here.
    """
    os.makedirs(work, exist_ok=True)
    shutil.copy(vpath, os.path.join(work, "dut.v"))
    with open(os.path.join(work, "tb.v"), "w") as f:
        f.write(TB.format(n=len(vec)))
    for name, i in (("rst", 0), ("vin", 1), ("din", 2)):
        with open(os.path.join(work, f"{name}.hex"), "w") as f:
            f.write("\n".join(f"{v[i]:03x}" for v in vec) + "\n")
    exe = os.path.join(work, "a.out")
    r = subprocess.run(["iverilog", "-g2012", "-o", exe, "tb.v", "dut.v"],
                       cwd=work, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError(f"iverilog failed on {vpath}:\n{r.stderr[:600]}")
    r = subprocess.run(["vvp", exe], cwd=work, capture_output=True, text=True, timeout=300)
    if r.returncode != 0:
        raise RuntimeError(f"vvp failed on {vpath}:\n{r.stderr[:600]}")
    out = []
    for line in r.stdout.splitlines():
        m = re.match(r"^(\d+) ([01x]) (\d+)$", line.strip())
        if m:
            out.append((int(m.group(1)), -1 if m.group(2) == "x" else int(m.group(2)),
                        int(m.group(3))))
    return out


# --------------------------------------------------------------------------- diffing

def diverge(a: list, b: list, vec: list, *, pulsed: bool) -> list[dict]:
    """Cycles where two traces disagree.

    `pulsed` compares `data_out` only on cycles where BOTH arms raise `valid_out`, and compares
    `valid_out` always.  That is the split the regimes rest on: `valid_out` timing is decided
    (round 2 adjudicated `valid_out_single_cycle` explicitly), while `data_out` between pulses is
    an open coordinate, so including it unconditionally would report every arm as disagreeing
    about something the specification declines to fix.
    """
    out = []
    for i in range(min(len(a), len(b))):
        ca, cb = a[i], b[i]
        vdiff = ca[1] != cb[1]
        ddiff = ca[2] != cb[2]
        if pulsed:
            ddiff = ddiff and ca[1] == 1 and cb[1] == 1
        if vdiff or ddiff:
            out.append({"cycle": ca[0], "valid_out": [ca[1], cb[1]], "data_out": [ca[2], cb[2]],
                        "differs": ("valid_out" if vdiff else "") + ("+" if vdiff and ddiff else "")
                                   + ("data_out" if ddiff else ""),
                        "stim": {"rst_n": vec[i][0], "valid_in": vec[i][1], "data_in": vec[i][2]}})
    return out


def best_shift(a: list, b: list, vec: list, span: int = 4) -> tuple[int, int]:
    """The output delay `k` that best aligns `b` to `a`, and the divergences left at it.

    Two arms can compute the same function and present it on different cycles.  A registered
    output and a combinational one differ by exactly one cycle of latency, and against a fixed
    reference every single pulse then counts as a disagreement — 110 of them here, which reads as
    two authors who understood the design differently and is instead two authors who understood
    it identically and pipelined it differently.

    So the number to report is not "do the traces match" but "do they match after a shift, and
    what shift".  A residual at the best shift is a real disagreement about the function.  A
    residual of zero at `k = 1` is a real disagreement about latency — still a difference, still
    worth naming, but not the same finding and not one that makes either arm wrong unless the
    prose fixed the timing.

    Searched over a small window on purpose.  A design that needs a shift of eight to line up is
    not a latency variant, it is a different circuit, and a wide enough search will always find
    some alignment that happens to score well on a finite trace.
    """
    best = (0, len(diverge(a, b, vec, pulsed=True)))
    for k in range(-span, span + 1):
        if k == 0:
            continue
        if k > 0:
            x, y, v = a[:len(a) - k], b[k:], vec[:len(vec) - k]
        else:
            x, y, v = a[-k:], b[:len(b) + k], vec[-k:]
        n = len(diverge(x, y, v, pulsed=True))
        if n < best[1]:
            best = (k, n)
    return best


# --------------------------------------------------------------------------- reading a workspace

def read_arm(ws: str, key: str, artifact: str = "final") -> dict:
    """Everything this file reports about one finished workspace, for one of its two artifacts.

    Missing pieces are recorded as `None` rather than raising.  A half-finished arm is a thing
    the table should be able to SHOW — an arm that failed at certify is evidence about the arm —
    and a comparison that refuses to run because one row is incomplete reports nothing at all.

    `artifact` selects between the Verilog emitted before the proof phase and the one emitted
    after it (see `leanrtl/preproof.py`).  On the pre-proof row every proof-derived column is
    forced to `None`: the theorem count, the mutation score and the gate list all describe the
    certification of the LATER artifact, and carrying them across would print a proof's numbers
    beside the file that was emitted without one — the single most flattering error this table
    could make, and the one a reader is least able to catch.
    """
    def load(*p):
        f = os.path.join(ws, *p)
        try:
            return json.load(open(f))
        except (OSError, ValueError):
            return None

    pre = artifact == preproof.TAG
    s = load("summary.json") or {}
    run = load("run.json") or {}
    ver = s.get("verify") or load("verify.json") or {}
    des = ver.get("design") or {}
    mut = load("out", "proof_mutation.json") or {}
    spec = os.path.join(ws, "specs", f"{key}.spec.txt")
    prose = open(spec, "rb").read() if os.path.isfile(spec) else b""
    import hashlib
    v = os.path.join(ws, "out", f"{key}.{preproof.TAG}.v" if pre else f"{key}.v")
    prec = load("out", f"{key}.{preproof.TAG}.json") or {}
    return {
        "ws": os.path.basename(ws) + (f":{preproof.TAG}" if pre else ""),
        "workspace": os.path.basename(ws),
        "artifact": preproof.TAG if pre else "final",
        "arm": run.get("arm"),
        "prose_bytes": len(prose),
        "prose_sha": hashlib.sha256(prose).hexdigest()[:12] if prose else None,
        "prose_from": run.get("prose"),
        "outcome": (("preproof" if prec.get("ok") else "preproof?") if pre
                    else s.get("outcome")),
        "elapsed_s": None if pre else s.get("elapsed_s"),
        "spec_versions": s.get("spec_versions"),
        "freeze_intact": s.get("freeze_intact"),
        "gates": {} if pre else (ver.get("gates") or {}),
        "n_theorems": None if pre else (des.get("axiom_clean") or {}).get("n_theorems"),
        "n_about_impl": None if pre else (des.get("proves_impl") or {}).get("n_about_impl"),
        "mutation": None if pre else mut.get("mutation_score"),
        "preproof": prec if pre else None,
        "verilog": v if os.path.isfile(v) else None,
        "n_regs": (sum(1 for L in open(v) if L.lstrip().startswith("reg "))
                   if os.path.isfile(v) else None),
    }


def discover(key: str) -> list[str]:
    """Finished workspaces for `key`, in a stable order.

    A workspace counts as finished when it has an emitted `out/<key>.v`.  Everything that is not a
    reported arm lives under `<key>/bak/` and is skipped by that one name — see `paths.BAK` for
    why it is a directory and no longer a list of suffixes to recognise.

    Every benchmark under `data/part2/`, not just the one that owns this key.  A key is passed on
    the command line and the benchmark layer is inferred, so a workspace staged before the
    inference existed — or under an explicit `--bench` that disagreed — sits under a directory
    this function would never think to look in, and `--all` would silently compare a subset.  The
    fix is to look everywhere and let `out/<key>.v` be the filter, which is what it already was.
    That is also why this walks every design directory rather than going straight to `<key>/`: the
    directory a workspace sits in is a claim about which design it is, and `out/<key>.v` is the
    evidence.  Where they disagree the evidence wins, and a misfiled workspace is still compared.
    """
    root = paths.data(paths.PART2)
    if not os.path.isdir(root):
        return []
    out = []
    for bench in sorted(os.listdir(root)):
        bdir = os.path.join(root, bench)
        if not os.path.isdir(bdir):
            continue
        for design in sorted(os.listdir(bdir)):
            ddir = os.path.join(bdir, design)
            if not os.path.isdir(ddir):
                continue
            for arm in sorted(os.listdir(ddir)):
                if arm == paths.BAK:
                    continue
                ws = os.path.join(ddir, arm)
                if os.path.isfile(os.path.join(ws, "out", f"{key}.v")):
                    out.append(ws)
    return out


def index(key: str, wss: list[str]) -> str:
    """Write `<key>/RESULTS.md` — what this design produced, at the level somebody looks first.

    The deliverables sit four directories down, in `<arm>/out/`, and a design's results are then
    something you have to already know the layout to find.  That is how `out/<key>.preproof.v`
    could be written to both arms and reported as done while the person who asked for it looked
    at `data/part2/rtllm/accu/` and saw two directories.

    Generated, never hand-written, and it says when from what.  A hand-maintained index is a
    second claim about the same files that drifts from them silently — which is the failure the
    `bak/` reorganisation was about, one layer up.

    Hashes are full sha256 of the artifact bytes, so the table answers "are these two the same
    file" without anybody having to run a diff, and answers it for a reader who has the table and
    not the tree.
    """
    import hashlib
    if not wss:
        return ""
    root = os.path.dirname(os.path.abspath(wss[0]))
    lines = [f"# `{key}` — what this design produced", "",
             "Generated by `python3 -m leanrtl.compare --key %s --all --index`.  Do not edit: it "
             "is rewritten\nfrom the files it describes, and a hand-kept index is a second claim "
             "that drifts from them." % key, "",
             "Each arm emits TWO Verilog modules from ONE authoring session — the implementation "
             "before\nthe proof phase, and the same implementation after it.  The second is what "
             "the gates certify;\nthe first exists so that \"the proof changed the design\" is "
             "checkable.  See `method/stage2/leanrtl/preproof.py`.", "",
             "| arm | artifact | file | bytes | sha256 |", "|---|---|---|---:|---|"]
    body = []
    for ws in wss:
        arm = os.path.basename(ws)
        for label, name in (("pre-proof", f"{key}.{preproof.TAG}.v"), ("certified", f"{key}.v")):
            p = os.path.join(ws, "out", name)
            if not os.path.isfile(p):
                lines.append(f"| `{arm}` | {label} | — | | *not emitted* |")
                continue
            b = open(p, "rb").read()
            lines.append(f"| `{arm}` | {label} | `{arm}/out/{name}` | {len(b)} | "
                         f"`{hashlib.sha256(b).hexdigest()[:16]}` |")
        rec = {}
        try:
            rec = json.load(open(os.path.join(ws, "out", f"{key}.{preproof.TAG}.json")))
        except (OSError, ValueError):
            pass
        d = rec.get("delta") or preproof.delta(ws, key)
        same = None
        pa, pb = os.path.join(ws, "out", f"{key}.{preproof.TAG}.v"), os.path.join(ws, "out",
                                                                                 f"{key}.v")
        if os.path.isfile(pa) and os.path.isfile(pb):
            same = open(pa, "rb").read() == open(pb, "rb").read()
        body.append((arm, d, same, rec))

    lines += ["", "## Did the proof change the circuit?", ""]
    for arm, d, same, rec in body:
        moved = d.get("changed")
        lines.append(f"**`{arm}`** — implementation section "
                     + ("MOVED during the session" if moved else "never moved")
                     + f" ({d.get('n_distinct')} distinct hash"
                     + ("es" if (d.get("n_distinct") or 0) != 1 else "") + ")."
                     + ("  The two Verilog files are **byte-identical**."
                        if same else "  The two Verilog files **differ**."
                        if same is False else ""))
        if rec.get("stashed"):
            lines.append(f"  Captured after the fact (`--stash-proof`); "
                         f"faithful: **{rec.get('faithful')}** — {rec.get('faithful_why', '')}")
        lines.append("")
    lines += ["A design where the section never moved is one where the author closed the proof "
              "against the\nimplementation as first written.  The proof then bought certification "
              "rather than a different\ncircuit — a real result, and one that is only visible "
              "because both files were kept.", ""]

    # The benchmark's own verdict, when one has been taken.  Read from disk rather than computed:
    # `leanrtl.score` owns the oracle, this file owns the index, and an index that ran a simulator
    # would be a second place a verdict could come from.
    #
    # It is here at all because the gates and the verdict are not the same claim and reading only
    # the first is how "the method certified this design" gets said about a design that fails its
    # own testbench.  `rtllm/accu` is the case: six green gates, a closed Lean proof, and a
    # `func_fail` on the decided arm.  A results index that showed the hashes and stopped is what
    # let that sit unnoticed until somebody thought to call the adapter.
    lines += ["## What the benchmark said", ""]
    verdicts = []
    for ws in wss:
        arm = os.path.basename(ws)
        for label, name in (("pre-proof", f"{key}.{preproof.TAG}.verdict.json"),
                            ("certified", f"{key}.verdict.json")):
            try:
                v = json.load(open(os.path.join(ws, "out", name)))
            except (OSError, ValueError):
                continue
            verdicts.append((arm, label, v))
    if not verdicts:
        lines += ["No verdict has been taken.  This is not a pass: nothing here has been run "
                  "against the\nbenchmark's own testbench, and the gates above are a claim about "
                  "the proof, not about the\ndesign.  Run `python3 -m leanrtl.score --key "
                  f"{key} --all --preproof`.", ""]
    else:
        lines += ["| arm | artifact | status | oracle | detail | scored |",
                  "|---|---|---|---|---|---|"]
        for arm, label, v in verdicts:
            x = v.get("extra") or {}
            # RTLLM's adapter has no sample count and puts the testbench's own tail in `detail`,
            # newlines and all.  A raw newline ends a markdown table row, so the four accu
            # verdicts rendered as eight half-rows and the table stopped being one.
            det = (f"{x['mismatches']}/{x['samples']} mismatched"
                   if x.get("samples") is not None
                   else " ".join((v.get("detail") or "").split())[:60].replace("|", "\\|"))
            lines.append(f"| `{arm}` | {label} | **{v.get('status')}** | {v.get('oracle')} | "
                         f"{det} | {(v.get('scored_at') or '')[:19]} |")
        lines += ["", "The oracle is named in every row because it is not a property of the "
                  "design: RTLLM's own\nmakefiles target VCS and this column may say `icarus`, "
                  "and a verdict carried across that\nchange is a verdict about a different "
                  "run.", ""]

    out = os.path.join(root, "RESULTS.md")
    with open(out, "w") as f:
        f.write("\n".join(lines))
    return out


# --------------------------------------------------------------------------- report

def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("ws", nargs="*", help="workspaces to compare")
    ap.add_argument("--key", required=True)
    ap.add_argument("--all", action="store_true", help="every finished workspace for this key")
    ap.add_argument("--preproof", action="store_true",
                    help="also compare each workspace's pre-proof Verilog — the implementation "
                         "as it was emitted before the proof phase.  Doubles the rows and asks "
                         "whether proving changed the circuit")
    ap.add_argument("--index", action="store_true",
                    help="write <key>/RESULTS.md listing every artifact this design produced, "
                         "and stop.  Simulates nothing")
    ap.add_argument("--json", help="write the full result here")
    ap.add_argument("--max-show", type=int, default=6, help="divergences printed per pair")
    a = ap.parse_args(argv)

    wss = [os.path.abspath(w) for w in a.ws] or (discover(a.key) if a.all else [])
    if a.index:
        if not wss:
            print(f"compare: no finished workspace for {a.key}", file=sys.stderr)
            return 2
        p = index(a.key, wss)
        print(p)
        return 0
    if len(wss) < 2 and not (a.preproof and wss):
        print("compare: name at least two workspaces, or pass --all", file=sys.stderr)
        return 2

    # Pre-proof first within each workspace, so the table reads in the order the artifacts were
    # produced rather than in the order that flatters them.
    arms = []
    for w in wss:
        if a.preproof:
            m = read_arm(w, a.key, preproof.TAG)
            if m["verilog"]:
                arms.append(m)
            else:
                print(f"compare: {os.path.basename(w)} has no out/{a.key}.{preproof.TAG}.v — run "
                      f"`python3 -m leanrtl.preproof --ws {w} --key {a.key} --stash-proof` to "
                      f"reconstruct it", file=sys.stderr)
        arms.append(read_arm(w, a.key))

    print(f"\n{'arm':<38} {'prose':>7} {'sha':<13} {'outcome':<11} {'regs':>5} {'thm':>4} "
          f"{'mutation':>10}")
    print("-" * 96)
    for m in arms:
        print(f"{m['ws']:<38} {m['prose_bytes'] or 0:>7} {m['prose_sha'] or '-':<13} "
              f"{(m['outcome'] or '-'):<11} {str(m['n_regs'] or '-'):>5} "
              f"{str(m['n_theorems'] if m['n_theorems'] is not None else '-'):>4} "
              f"{str(m['mutation'] if m['mutation'] is not None else '-'):>10}")
    if a.preproof:
        print("\n  `thm` and `mutation` are blank on every :preproof row on purpose: those "
              "numbers\n  certify the artifact emitted AFTER the proof, and this row is the one "
              "emitted before it.")
        for w in wss:
            d = preproof.delta(w, a.key)
            print(f"  {os.path.basename(w):<24} implementation section: "
                  f"{'MOVED during the session' if d['changed'] else 'never moved'} "
                  f"({d['n_distinct']} distinct)")

    # Arms whose prose is byte-identical are not two readings of one design; they are one reading
    # run twice.  Said out loud because it happened: a workspace named `.r1prose` carried exactly
    # the original arm's bytes, and a table that does not check this reports the difference
    # between two authoring sessions as the effect of specification checking.
    #
    # Grouped by WORKSPACE, not by row: with `--preproof` every workspace contributes two rows
    # with the same prose by construction, and firing this note on them would say that a
    # pre-proof/final pair differs "by authoring session", which is the one thing it does not.
    by_sha: dict = {}
    for m in arms:
        by_sha.setdefault(m["prose_sha"], set()).add(m["workspace"])
    for sha, names in by_sha.items():
        if len(names) > 1:
            print(f"\n  NOTE  same prose ({sha}) in {len(names)} workspaces: "
                  f"{', '.join(sorted(names))}"
                  f"\n        these differ only by authoring session, not by specification")

    runnable = [m for m in arms if m["verilog"]]
    if len(runnable) < 2:
        print("\ncompare: fewer than two arms emitted Verilog; nothing to simulate")
        return 0

    result = {"key": a.key, "cycles": CYCLES, "seed": SEED, "arms": arms, "pairs": []}
    work = tempfile.mkdtemp(prefix="leanrtl-compare-")
    try:
        traces = {}
        for regime in ("pulsed", "quiet", "reset"):
            vec = stimulus("reset" if regime == "reset" else "clean")
            for m in runnable:
                k = (regime, m["ws"])
                try:
                    traces[k] = trace(m["verilog"], vec,
                                      os.path.join(work, regime, m["ws"]))
                except Exception as e:                          # noqa: BLE001
                    print(f"\n  SIM FAILED  {regime}/{m['ws']}: {e}")
                    traces[k] = None

        for i in range(len(runnable)):
            for j in range(i + 1, len(runnable)):
                x, y = runnable[i], runnable[j]
                print(f"\n{'=' * 96}\n{x['ws']}\n  vs  {y['ws']}")
                pair = {"a": x["ws"], "b": y["ws"], "regimes": {}}
                if x["workspace"] == y["workspace"]:
                    print("  (one session's two artifacts — any divergence below is the PROOF "
                          "PHASE, not prose and not authoring variance)")
                elif x["prose_sha"] == y["prose_sha"]:
                    print("  (same prose — any divergence below is authoring variance, not "
                          "specification)")
                for regime in ("pulsed", "quiet", "reset"):
                    vec = stimulus("reset" if regime == "reset" else "clean")
                    ta, tb = traces[(regime, x["ws"])], traces[(regime, y["ws"])]
                    if ta is None or tb is None:
                        print(f"  {regime:<7} — not simulated")
                        continue
                    d = diverge(ta, tb, vec, pulsed=(regime == "pulsed"))
                    ent = {"n": len(d), "first": d[:a.max_show]}
                    if regime == "pulsed":
                        k, resid = best_shift(ta, tb, vec)
                        ent["shift"], ent["n_at_shift"] = k, resid
                    pair["regimes"][regime] = ent
                    verdict = "identical" if not d else f"{len(d)} cycle(s) differ"
                    if regime == "pulsed" and ent.get("shift"):
                        verdict += (f"  ·  {ent['n_at_shift']} after aligning "
                                    f"{ent['shift']:+d} cycle(s)")
                    print(f"  {regime:<7} {verdict}")
                    for e in d[:a.max_show]:
                        print(f"      c{e['cycle']:<4} {e['differs']:<20} "
                              f"valid_out {e['valid_out'][0]}/{e['valid_out'][1]}  "
                              f"data_out {e['data_out'][0]}/{e['data_out'][1]}"
                              f"   (rst_n={e['stim']['rst_n']} valid_in={e['stim']['valid_in']} "
                              f"data_in={e['stim']['data_in']})")
                    if len(d) > a.max_show:
                        print(f"      … {len(d) - a.max_show} more")

                # The subtraction the regimes exist for.  Reported per pair rather than once,
                # because two arms can agree on the decided reading and disagree on an open
                # coordinate, which is the expected outcome and reads as a failure without this.
                p, q, r = (pair["regimes"].get(k, {}).get("n") for k in ("pulsed", "quiet", "reset"))
                sh = pair["regimes"].get("pulsed", {})
                k, resid = sh.get("shift", 0), sh.get("n_at_shift")
                if p is not None:
                    if p and k and resid == 0:
                        print(f"\n  → the same function, presented {abs(k)} cycle(s) "
                              f"{'later' if k > 0 else 'earlier'} by "
                              f"{y['ws'] if k > 0 else x['ws']}.  All {p} raw divergences vanish "
                              f"under that shift, so the arms agree on accumulate-and-group and "
                              f"differ only in output latency — one registers its outputs, the "
                              f"other drives them combinationally.  A real difference a consumer "
                              f"can see, but not a disagreement about what the prose said, unless "
                              f"the prose fixed the timing.")
                    elif p and k:
                        print(f"\n  → {p} raw divergence(s), {resid} still there after aligning "
                              f"{abs(k)} cycle(s).  Part latency, part genuine: these arms "
                              f"disagree about the DECIDED reading on {resid} cycle(s).")
                    elif p:
                        print(f"\n  → {p} divergence(s) in `pulsed` at every shift in ±4: these "
                              f"arms disagree about the DECIDED reading — accumulate-and-group "
                              f"and valid_out timing. Specification checking did not close this, "
                              f"or the two authors read the closed text differently.")
                    else:
                        print("\n  → no divergence in `pulsed`: the arms agree cycle-for-cycle "
                              "wherever the specification commits.")
                    if q is not None and q > p:
                        print(f"  → {q - p} further in `quiet`: what `data_out` shows between "
                              f"pulses.  `HANDOFF.json` lists `h_data_out_between_pulses` as "
                              f"still_open, so by the handoff's own account both arms are within "
                              f"the specification — but the round-3 prose carries "
                              f"`data_out_stable_between_pulses` as a ruling and the sentence "
                              f"\"On every cycle where valid_out is 0, data_out holds its previous "
                              f"value\".  A coordinate can be open in the `Cfg` and pinned in the "
                              f"prose at the same time, and the arms follow the prose.  Read this "
                              f"number against which prose the arm was authored from, not against "
                              f"the open-list alone.")
                    if r is not None and q is not None and r > q:
                        print(f"  → {r - q} further under `reset`: reset behaviour. "
                              f"`h_reset_kind` / `h_reset_data_out` / `h_reset_partial_sum` are "
                              f"OPEN — licensed difference, not a defect.")
                result["pairs"].append(pair)
    finally:
        shutil.rmtree(work, ignore_errors=True)

    if a.json:
        with open(a.json, "w") as f:
            json.dump(result, f, indent=1)
        print(f"\nwritten: {a.json}")
    print()
    return 0


if __name__ == "__main__":
    sys.exit(main())
