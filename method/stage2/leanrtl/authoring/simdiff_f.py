#!/usr/bin/env python3
"""F-arm sim-diff gate (plan v1.2 §2 step 3): run S's executable spec adapters against
R's impl simulation on deterministic pseudorandom stimulus, BEFORE any proving.

    python3 scripts/simdiff_f.py <key>

Reads contracts/<key>.json for input ports, assembles the design, generates a #eval
driver, runs `lake env lean` on it, prints and logs the verdict:
    SIMDIFF-OK checked=N | SIMDIFF-FAIL mismatches=K (+ first mismatches) | SIMDIFF-VACUOUS
"""
import os, re, sys, json, random, subprocess, time

WS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
sys.path.insert(0, os.path.join(WS, "scripts"))
import bb            # noqa: E402  (workspace bb: resolve/log/camel helpers)
import asm_f         # noqa: E402

LAKE = os.path.expanduser("~/.elan/bin/lake")
CYCLES = 160
RESETTISH = ("reset", "rst", "rst_n", "reset_n", "areset", "resetn", "arst_n")

# The `mems` / `latches` field of a `Module` literal, wherever it is written.  Whether the list is
# EMPTY is decided below in code, not in the pattern; `harness/simdiff_blind.py` carries the same
# pair and the reason, and this file cannot import it (it runs from `<ws>/scripts/`, where
# `harness/` is not on the path), so the test is duplicated rather than shared.
MEMS_FIELD = re.compile(r"(?m)^\s*,?\s*mems\s*:=")
LATCHES_FIELD = re.compile(r"(?m)^\s*,?\s*latches\s*:=")
_BLANK = re.compile(r"(?:\s|--[^\n]*\n)*")


def _field_nonempty(body, field):
    """Does this module carry anything in `field`?  Anything that is not literally the empty list,
    including a value this cannot read -- abstaining from a comparison that would be meaningless
    is the safe direction, running one that reads every backed output as 0 is not."""
    for m in field.finditer(body):
        rest = body[m.end():]
        rest = rest[_BLANK.match(rest).end():]
        for empty in ("#[]", "[]"):
            if rest.startswith(empty):
                tail = rest[len(empty):].lstrip(" \t")
                if tail[:1] in ("", "\n", ",", "}", ")", "-"):
                    break
        else:
            return True
    return False


def _mems_nonempty(body):
    return _field_nonempty(body, MEMS_FIELD)


def _latches_nonempty(body):
    return _field_nonempty(body, LATCHES_FIELD)


def is_resettish(p):
    """A 1-bit input whose name CONTAINS a reset token, not just one that equals one.

    The exact-name list missed every prefixed or suffixed reset port in this benchmark --
    `wb_rst_i`, `RST_PAD_I`, `dtcm_rst_n` -- so the gate drove them as ordinary random inputs
    instead of an initial pulse.  A design then spends the run being reset at random, which
    makes the comparison harsher than intended and tangles with the documented asyncReset gap.
    Width-guarded to 1 bit so a wide bus with `rst` in its name cannot be caught.
    """
    if p.get("width", 1) != 1:
        return False
    n = p["name"].lower()
    return n in RESETTISH or any(
        t in n.replace("-", "_").split("_") for t in ("rst", "reset", "resetn", "rstn"))


def gen_vectors(inputs, seed):
    """Full-width randoms (v1.3 M47 hardening: no 2^30 cap — the alu negative-operand
    gap) + a deterministic signed-boundary sweep on cycles 8..11 (0 / all-ones /
    sign-bit / max-positive per data port)."""
    rng = random.Random(seed)
    resets = [p for p in inputs if is_resettish(p)]
    others = [p for p in inputs if p not in resets]
    vecs = []
    for t in range(CYCLES):
        cyc = []
        for p in resets:
            low_active = p["name"].lower().endswith("_n") or p["name"].lower().startswith("n")
            asserted = t < 2 or t in (60, 61)
            v = (0 if asserted else 1) if low_active else (1 if asserted else 0)
            cyc.append((p["name"], v))
        for p in others:
            w = p["width"]
            if 8 <= t <= 11 and w > 1:
                v = [0, (1 << w) - 1, 1 << (w - 1), (1 << (w - 1)) - 1][t - 8]
            else:
                v = rng.randrange(0, 1 << w)
            cyc.append((p["name"], v))
        vecs.append(cyc)
    return vecs


def driver_lean(key, camel, vecs, is_parent, design_body, out_ports):
    rows = ",\n    ".join(
        "[" + ", ".join(f'("{n}", {v})' for n, v in cyc) + "]" for cyc in vecs)
    simcall = "impl.simulateSeq vecs" if is_parent else "impl.simulateFast vecs"
    outs = "[" + ", ".join(f'"{n}"' for n in out_ports) + "]"
    # The driver elaborates the WHOLE design plus a literal vector table, which on a large
    # design (44 in / 46 out) blew Lean's default recursion limit.  The elaboration errors then
    # cascaded into `noncomputable` failures on `vecs` and `main`, and the run reported
    # `vacuous - 0 checked`.  The gate is right to refuse to call that agreement, but the cause
    # is the driver, not the two fragments, so raise the limit here rather than in asm_f.py
    # (which every role's build goes through).
    return f"""{design_body}
set_option maxRecDepth 100000
open LeanRTL LeanRTL.Blind.{camel}

/-- contract output ports: specOuts must cover EVERY one (v1.3 M47: a spec that omits
    a port must FAIL the gate, not silently skip it). -/
def contractOuts : List String := {outs}

def vecs : List (List (String × Nat)) :=
  [ {rows} ]

def main : IO Unit := do
  let sims := {simcall}
  let n := min vecs.length sims.length
  let mut regs := specInit
  let mut mism := 0
  let mut checked := 0
  for i in [0:n] do
    let ins := vecs[i]!
    let simOut := sims[i]!
    let sOut := specOuts regs ins
    for name in contractOuts do
      checked := checked + 1
      match sOut.lookup name, simOut.lookup name with
      | some sv, some v' =>
          if sv ≠ v' then
            if mism < 5 then
              IO.println s!"SIMDIFF-MISMATCH cycle={{i}} sig={{name}} spec={{sv}} impl={{v'}}"
            mism := mism + 1
      | none, _ =>
          if mism < 5 then IO.println s!"SIMDIFF-SPEC-OMITS sig={{name}}"
          mism := mism + 1
      | _, none =>
          if mism < 5 then IO.println s!"SIMDIFF-MISSING sig={{name}}"
          mism := mism + 1
    regs := specStep regs ins
  if checked == 0 then IO.println "SIMDIFF-VACUOUS"
  else if mism == 0 then IO.println s!"SIMDIFF-OK checked={{checked}}"
  else IO.println s!"SIMDIFF-FAIL mismatches={{mism}} checked={{checked}}"

#eval main
"""


def run(key):
    camel = asm_f.camel_of(key)
    # self-contained driver: inline the assembled design (no .olean needed, no build lock)
    design_body = open(asm_f.assemble(key)).read()

    # A design with a non-empty `mems` cannot be gated by this driver.  `Module.simulateFast`
    # builds its environment from registers and inputs only, so every memory read resolves
    # through `Env.ofList`'s `getD 0` and the impl side reads 0 on every memory-backed output
    # for every cycle.  Against any spec that models the array, that is a guaranteed
    # "divergence" of exactly the wrong kind: an artifact of the cycle model, reported with the
    # same words as a real disagreement between two readings.  `leanhdl check` already knows
    # (semanticCoverage per-access, reason memShape); the gate has to refuse rather than score.
    # The emptiness test is `harness/simdiff_blind.py`'s, duplicated at the top of this file
    # rather than imported (this runs from `<ws>/scripts/`).  The pattern that used to be here --
    # `^\s*mems\s*:=\s*(?!\[\s*\])` -- matched `mems := []` too: `\s*` in front of a negative
    # lookahead backtracks to zero width, the lookahead is then tested against ` []` instead of
    # `[]`, `\[` does not match a space, and the negative lookahead succeeds.  Every design that
    # wrote its EMPTY `mems` field out was refused by a driver whose refusal is about memories.
    # On the VerilogEval lane that was 45 designs across five arms and not one had a memory.
    if _mems_nonempty(design_body):
        print("SIMDIFF-UNGATEABLE mems")
        print("  This design has a non-empty `mems`.  Module.simulateFast carries no array, so "
              "every memory-backed output reads 0 and any comparison is meaningless.  "
              "NOT agreement, NOT divergence -- ungateable by this driver.")
        return 3
    # The same argument, for the same reason, about `latches`.  `Module.simulate` /
    # `simulateFast` build their cycle environment from `regs` and the input vector only
    # (`Core/Semantics.lean:209-210`, `470-481`), so a latch's Q net resolves through neither and
    # reads 0 on every cycle -- a guaranteed "divergence" that is an artifact of the Moore cycle
    # model rather than a disagreement between the two fragments.  The framework says so itself,
    # in three places, and said so before this guard existed: `Core/Syntax.lean:256-263` ("latches
    # are **not** modelled by the whole-design cycle simulator ... `bb cosim` therefore CANNOT
    # validate a latch-carrying design -- its `fail` there is expected, not a design bug"),
    # `Core/Coverage.lean:116` (`CoverageReason.latch`), and `Coverage.lean:51-53` ("pinned by
    # `Latch.den` + co-simulation").
    #
    # Only `mems` was guarded, so the gate ran anyway and scored the artifact of its own model as
    # the implementation's bug.  `verilogeval/Prob028_m2014_q4a` is the observed case and cost a
    # whole design: `SIMDIFF-FAIL mismatches=80 checked=160`, and the Verilog it emitted --
    # `always @* if (ena) q = d;` -- is the reference circuit and scores `func_pass` with 0
    # mismatches on 100 samples.  Worse than losing it: D had predicted this exactly, wrote it
    # down in `impl.lean`, and chose the honest model anyway, noting that a self-holding `Reg`
    # "denotes the same next-value function under the cycle model, and would therefore be green
    # on `sim`/`simdiff` by construction" while emitting a flip-flop whose CLK is tied to a
    # constant and which freezes at its `init` forever.  Ungated, this gate rewards that.
    if _latches_nonempty(design_body):
        print("SIMDIFF-UNGATEABLE latch")
        print("  This design has a non-empty `latches`.  Module.simulateFast builds its cycle "
              "environment from `regs` and the inputs only, so a latch's Q net reads 0 on every "
              "cycle and any comparison is meaningless.  NOT agreement, NOT divergence -- "
              "ungateable by this driver.  A latch's behaviour is pinned by `Latch.den` "
              "(`q' = enable ? d : q`) in the proof and by co-simulation of the emitted "
              "`$dlatch`, which is where it lives in this framework.")
        return 3
    contract = json.load(open(os.path.join(WS, "contracts", key + ".json")))
    inputs = [p for p in contract["ports"]
              if p["dir"] == "in" and p["name"].lower() not in ("clk", "clock")]
    out_ports = [p["name"] for p in contract["ports"] if p["dir"] == "out"]
    import zlib
    vecs = gen_vectors(inputs, seed=zlib.crc32(key.encode()) & 0xffff)
    impl_frag = open(os.path.join(WS, "frags", key, "impl.lean")).read() \
        if os.path.isfile(os.path.join(WS, "frags", key, "impl.lean")) else ""
    is_parent = "def impl : Parent" in impl_frag
    d = os.path.join(WS, "scratch", "simdiff")
    os.makedirs(d, exist_ok=True)
    drv = os.path.join(d, f"SimDiff{camel}.lean")
    open(drv, "w").write(driver_lean(key, camel, vecs, is_parent, design_body, out_ports))
    t0 = time.time()
    # Run under a raised stack limit.  e203_biu (57 in / 66 out, 159 cycles) aborted with
    # "Stack overflow detected" at RUNTIME -- the driver compiled fine and then died, so no
    # SIMDIFF-* line was printed and the harness fell back to `vacuous`.  Twice now a large
    # design has come back as "0 checked" for a reason that had nothing to do with the two
    # fragments; both times the gate refused to call it agreement, which is the only reason
    # it was caught.
    r = subprocess.run(["bash", "-c",
                        "ulimit -s 262144 2>/dev/null; exec \"$@\"", "_",
                        LAKE, "env", "lean", "--tstack=262144",
                        os.path.relpath(drv, WS)], cwd=WS,
                       capture_output=True, text=True, timeout=900)
    out = r.stdout + r.stderr
    # v1.3 M47: OK requires BOTH the marker and a clean rc — a driver with elaboration
    # errors elsewhere must not pass the gate on a printed OK alone
    if "SIMDIFF-OK" in out and r.returncode == 0:
        verdict = "simdiff_ok"
    elif "SIMDIFF-FAIL" in out or "SIMDIFF-MISSING" in out:
        verdict = "simdiff_fail"
    elif "SIMDIFF-VACUOUS" in out:
        verdict = "simdiff_vacuous"
    else:
        verdict = "simdiff_error"
    print(out[-1500:])
    bb.log(key, {"ts": round(t0, 3), "iso": time.strftime("%Y-%m-%dT%H:%M:%S"),
                 "key": key, "cmd": "simdiff", "rc": r.returncode,
                 "wall_s": round(time.time() - t0, 1), "err_class": verdict,
                 "err_head": out[-400:] if verdict != "simdiff_ok" else "",
                 "sec_sha": {}, "file_sha": ""})
    return 0 if verdict == "simdiff_ok" else 1


if __name__ == "__main__":
    sys.exit(run(sys.argv[1]))
