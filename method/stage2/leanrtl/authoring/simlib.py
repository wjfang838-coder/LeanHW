"""Shared helpers for LeanRTL verification: interface parsing, vector generation,
Verilog simulation (iverilog) and Lean reference simulation."""
import json, subprocess, os, itertools, random, re

CLOCK_NAMES = {"clk", "clock"}
RESET_NAMES = {"rst", "reset", "rst_n", "resetn", "rstn", "nrst",
               "areset", "arst", "arst_n", "reset_n"}
# active-LOW reset names: asserted = 0, deasserted = 1 (previously these were listed in
# RESET_NAMES but driven with active-high polarity, holding the design in reset forever)
ACTIVE_LOW_RESET_NAMES = {"rst_n", "resetn", "rstn", "nrst", "arst_n", "reset_n"}

NO_INPUT_CYCLES = 64   # a module with no input ports still needs a run length
IVERILOG_TIMEOUT = 120   # seconds; a hung compile/sim should fail loudly, not stall the bench
VVP_TIMEOUT = 600

REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LEANRTL_BIN = os.path.join(REPO, ".lake", "build", "bin", "leanrtl")


def load_interface(rtlil_json_path):
    """Return (top_name, inputs, outputs) where inputs/outputs are [(name, width)]."""
    with open(rtlil_json_path) as f:
        d = json.load(f)
    mods = d["modules"]
    name = next(iter(mods))
    m = mods[name]
    inputs, outputs = [], []
    for pname, p in m["ports"].items():
        w = len(p["bits"])
        if p["direction"] == "input":
            inputs.append((pname, w))
        elif p["direction"] == "output":
            outputs.append((pname, w))
    return name, inputs, outputs


def is_clock(n):
    return n.lower() in CLOCK_NAMES


def is_reset(n):
    return n.lower() in RESET_NAMES


def is_active_low_reset(n):
    return n.lower() in ACTIVE_LOW_RESET_NAMES


def _run(cmd, timeout, what, **kw):
    """subprocess.run with timeout + exit-status check (a crashed vvp used to be
    silently treated as a short-but-valid trace)."""
    try:
        r = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout, **kw)
    except subprocess.TimeoutExpired:
        raise RuntimeError(f"{what} timed out after {timeout}s: {' '.join(cmd)}")
    if r.returncode != 0:
        raise RuntimeError(f"{what} failed (exit {r.returncode}):\n" + r.stderr + r.stdout)
    return r


def data_inputs(inputs, clock=None):
    """Inputs that carry data (exclude clock and reset).

    `clock` is the name the DESIGN declares.  Without it this fell back to the {clk, clock}
    whitelist, so a clock named `wclk` was classified as data, driven from the vector file, and
    also declared as the testbench's clock register -- two declarations of one identifier.
    """
    return [(n, w) for (n, w) in inputs
            if n != clock and not is_clock(n) and not is_reset(n)]


_KNOWN = re.compile(r"^-?\d+$")
_UNKNOWN = re.compile(r"^[0-9xXzZ_?]+$")


def _parse_samples(stdout: str, out_names: list) -> list:
    """Turn vvp's stdout into one sample per data line, skipping simulator chatter.

    This used to be `line.split()` plus two loose tests, and it produced a NON-DETERMINISTIC
    result.  vvp prints `$finish called at 512000 (1ps)` prefixed by the testbench path; on a
    6-output design that message tokenises to exactly 6 fields, so it passed the arity filter,
    and then `any("x" in v)` matched -- because the token was a path through a *random* temp
    directory, `/tmp/tmpc66xqpbi/tb.v:22:`, whose name happens to contain an `x`.  The message
    was recorded as an unknown SAMPLE, the run came back 513 samples for 512 vectors, and the
    length check reported `truncated simulation` against a design that had just agreed on all
    512.  Whether a design passed therefore depended on the letters `tempfile` happened to draw.

    So: a data line is one where EVERY token is a bare integer, or every token is a bit pattern
    over 0/1/x/z.  A path, a time, or a parenthesised unit fails both.
    """
    res = []
    for line in stdout.strip().split("\n"):
        vals = line.split()
        if len(vals) != len(out_names):
            continue
        if all(_KNOWN.match(v) for v in vals):
            res.append({on: int(v) for on, v in zip(out_names, vals)})
        elif all(_UNKNOWN.match(v) for v in vals):
            res.append(None)        # unknown sample — placeholder keeps vector alignment
        # anything else is simulator chatter: skip without a placeholder
    return res


def _fresh(taken, base):
    """A Verilog identifier not in `taken`.

    The generated testbench used hardcoded locals (`integer fd, r;` and the instance name
    `dut`).  Verilog puts nets, variables and instance names in ONE module-scope namespace, so a
    design with an output port named `r` -- `alu` has one -- made iverilog fail with "'r' has
    already been declared in this scope", and the run was logged as a co-simulation FAILURE of
    the design.  That is the harness marking its own defect against the candidate, which is the
    one error class that must never be silent.
    """
    n = base
    while n in taken:
        n += "_"
    return n


def _corner_values(w):
    """Directed corner values for a w-bit input: 0, 1, all-ones, MSB, MSB-1 boundary."""
    top = 2 ** w
    cs = {0, 1, top - 1, top >> 1, (top >> 1) - 1, 2, top - 2}
    return sorted(v % top for v in cs if 0 <= v)


def gen_vectors(inputs, max_exhaustive_bits=16, n_random=512, seed=0):
    """Generate combinational input vectors as a list of {name: value} dicts.
    Exhaustive for small input spaces; otherwise directed corners (0 / 1 / all-ones /
    sign boundaries — previously never hit for wide designs) + seeded randoms."""
    di = data_inputs(inputs)
    total = sum(w for _, w in di)
    rng = random.Random(seed)
    vecs = []
    if total <= max_exhaustive_bits:
        for combo in itertools.product(*[range(2 ** w) for _, w in di]):
            vecs.append(dict(zip([n for n, _ in di], combo)))
    else:
        seen = set()
        # all inputs pinned to a shared corner, plus one-hot corner sweeps
        shared = set()
        for _, w in di:
            shared.update(_corner_values(w))
        for v in sorted(shared):
            vec = {n: v % (2 ** w) for n, w in di}
            key = tuple(sorted(vec.items()))
            if key not in seen:
                seen.add(key)
                vecs.append(vec)
        for n0, w0 in di:
            for v in _corner_values(w0):
                vec = {n: (v if n == n0 else rng.randrange(2 ** w)) for n, w in di}
                key = tuple(sorted(vec.items()))
                if key not in seen:
                    seen.add(key)
                    vecs.append(vec)
        while len(vecs) < n_random:
            vecs.append({n: rng.randrange(2 ** w) for n, w in di})
    return vecs


def gen_seq_vectors(inputs, cycles=64, seed=0, reset_name=None, active_low=None, clock=None):
    """Generate a clock sequence: a list of per-cycle {name: value} dicts.
    Cycle 0 asserts reset (if present); reset is deasserted afterwards.

    `reset_name` overrides autodetection (e.g. a manifest-declared reset outside
    RESET_NAMES).  `active_low=None` auto-detects polarity from the name (rst_n/… are
    asserted LOW) — right for external reference Verilog.  Pass `active_low=False` for
    LeanRTL-authored modules: `Module.reset` semantics is active-high (nonzero = reset)
    regardless of the port's name, and the vectors must match the semantics, not the
    naming convention."""
    di = data_inputs(inputs, clock)
    if reset_name is None:
        reset_name = next((n for n, _ in inputs if is_reset(n)), None)
    di = [(n, w) for (n, w) in di if n != reset_name]
    if active_low is None:
        active_low = reset_name is not None and is_active_low_reset(reset_name)
    rng = random.Random(seed)
    seq = []
    # HOLD each data input for a run of cycles instead of redrawing it every cycle.
    #
    # Redrawing every cycle silently fails to exercise any design whose behaviour depends on an
    # input being STABLE.  `square_wave` counts to `freq - 1`: with `freq` redrawn each cycle the
    # comparison fires with probability ~1/256 per cycle and never fired in 64, so the run was
    # correctly reported `vacuous` -- correctly, because nothing WAS compared, but the cause was
    # the stimulus, not the design.  The same blindness hits every enable/threshold/mode input.
    #
    # Run lengths are drawn per input so the phases interleave rather than all changing together,
    # and a length-1 run is still possible, so per-cycle variation is not lost -- only made
    # non-exclusive.  Seeded, so the vectors stay reproducible.
    def draw(w: int) -> int:
        """A value this run length can actually exercise, half the time.

        A uniform draw over a wide input is almost always LARGE, and a design that counts up to
        that input cannot reach it inside a 64-cycle trace: `square_wave` counting to `freq - 1`
        with `freq` uniform on 0..255 needs ~128 cycles on average to toggle once.  So half the
        draws come from a small/corner set that a short trace can reach, and half stay uniform so
        the wide range is still covered.
        """
        top = 2 ** w
        if w <= 3 or rng.random() < 0.5:
            return rng.randrange(top)
        return rng.choice(sorted({0, 1, 2, 3, 4, 5, 7, 8,
                                  min(top - 1, cycles // 4), top - 1, top >> 1}))

    hold = {n: 0 for n, _ in di}
    val = {n: 0 for n, _ in di}
    for i in range(cycles):
        for n, w in di:
            if hold[n] == 0:
                v = draw(w)
                val[n] = v
                if w == 1:
                    # A 1-bit input is exactly the thing that must be free to change every
                    # cycle: it carries the enables, the serial data and the pulses that
                    # sequence detectors key on.  A random per-cycle stream still contains runs,
                    # so the held-enable case is covered without holding deliberately.
                    hold[n] = 1
                elif w == 2:
                    # NARROW inputs must be free to change EVERY cycle.  Holding them 2..8
                    # cycles -- which the wide-input rule below did -- gave 7 runs over 64
                    # cycles on a 1-bit port and made the patterns sequence detectors wait for
                    # (`010`, `1001`) literally unreachable: `fsm`, `pulse_detect`,
                    # `sequence_detector` and `RAM` all came back `vacuous`.  Mostly length 1,
                    # sometimes longer so a held enable is still exercised.
                    hold[n] = 1 if rng.random() < 0.6 else rng.randint(2, 4)
                else:
                    # Hold a SMALL value long enough for a counter to walk up to it.  A fixed
                    # 1..8 was not enough: a free-running counter passes the small thresholds
                    # while a large value is held, and then never returns until it wraps.
                    hold[n] = max(rng.randint(1, 8), v + 2) if v + 2 <= cycles // 2 \
                        else rng.randint(1, 8)
            hold[n] -= 1
        cyc = dict(val)
        if reset_name is not None:
            asserted = (i == 0)
            cyc[reset_name] = (0 if asserted else 1) if active_low else (1 if asserted else 0)
        seq.append(cyc)
    return seq, reset_name


# ---------------------------------------------------------------------------
# Verilog simulation via iverilog
# ---------------------------------------------------------------------------

def _tb_comb(top, di, outputs, vecpath):
    decl = "\n".join(f"  reg [{w-1}:0] {n};" for n, w in di)
    odecl = "\n".join(f"  wire [{w-1}:0] {n};" for n, w in outputs)
    conns = ", ".join(f".{n}({n})" for n, _ in (di + outputs))
    in_names = [n for n, _ in di]
    out_names = [n for n, _ in outputs]
    taken = set(in_names) | set(out_names)
    fd, rc, dut = _fresh(taken, "fd"), _fresh(taken, "r"), _fresh(taken, "dut")
    scanfmt = " ".join("%d" for _ in in_names)
    scanargs = (", " + ", ".join(in_names)) if in_names else ""
    dispfmt = " ".join("%0d" for _ in out_names)
    dispargs = (", " + ", ".join(out_names)) if out_names else ""
    if not in_names:
        # A module with NO driven inputs has nothing to scan, and `$fscanf(fd, "")` is a
        # compile error -- `clkgenerator` (a free-running oscillator, zero input ports) died
        # with "$fscanf requires at least three argument" and was logged against the design.
        # Emit a fixed-length loop instead.
        return f"""`timescale 1ns/1ps
module tb;
{decl}
{odecl}
  {top} {dut}({conns});
  integer {rc};
  initial begin
    for ({rc} = 0; {rc} < {NO_INPUT_CYCLES}; {rc} = {rc} + 1) begin
      #1;
      $display("{dispfmt}"{dispargs});
    end
    $finish;
  end
endmodule
"""
    return f"""`timescale 1ns/1ps
module tb;
{decl}
{odecl}
  {top} {dut}({conns});
  integer {fd}, {rc};
  initial begin
    {fd} = $fopen("{vecpath}", "r");
    {rc} = $fscanf({fd}, "{scanfmt}"{scanargs});
    while ({rc} == {len(in_names)}) begin
      #1;
      $display("{dispfmt}"{dispargs});
      {rc} = $fscanf({fd}, "{scanfmt}"{scanargs});
    end
    $finish;
  end
endmodule
"""


def simulate_comb_verilog(verilog_path, top, inputs, outputs, vectors, workdir):
    """Simulate a combinational design; returns list of {out_name: value}."""
    di = [(n, w) for (n, w) in inputs if not is_clock(n)]
    in_names = [n for n, _ in di]
    out_names = [n for n, _ in outputs]
    vecpath = os.path.join(workdir, "vec.txt")
    with open(vecpath, "w") as f:
        for v in vectors:
            f.write(" ".join(str(v.get(n, 0)) for n in in_names) + "\n")
    tb = _tb_comb(top, di, outputs, vecpath)
    tbpath = os.path.join(workdir, "tb.v")
    open(tbpath, "w").write(tb)
    simbin = os.path.join(workdir, "sim.out")
    _run(["iverilog", "-g2012", "-o", simbin, tbpath, verilog_path],
         IVERILOG_TIMEOUT, "iverilog")
    r = _run(["vvp", simbin], VVP_TIMEOUT, "vvp")
    return _parse_samples(r.stdout, out_names)


def _tb_seq(top, inputs, outputs, vecpath, clock, reset):
    di = data_inputs(inputs, clock)
    ctrl = [(n, w) for (n, w) in inputs if is_reset(n)]
    drv = di + ctrl                       # all driven (non-clock) inputs
    decl = "\n".join(f"  reg [{w-1}:0] {n};" for n, w in drv)
    odecl = "\n".join(f"  wire [{w-1}:0] {n};" for n, w in outputs)
    conns_list = [f".{clock}({clock})"] + [f".{n}({n})" for n, _ in (drv + outputs)]
    conns = ", ".join(conns_list)
    in_names = [n for n, _ in drv]
    out_names = [n for n, _ in outputs]
    taken = set(in_names) | set(out_names) | {clock}
    fd, rc, dut = _fresh(taken, "fd"), _fresh(taken, "r"), _fresh(taken, "dut")
    scanfmt = " ".join("%d" for _ in in_names)
    scanargs = (", " + ", ".join(in_names)) if in_names else ""
    dispfmt = " ".join("%0d" for _ in out_names)
    dispargs = (", " + ", ".join(out_names)) if out_names else ""
    if not in_names:
        # See `_tb_comb`: nothing to scan, and `$fscanf(fd, "")` will not compile.
        return f"""`timescale 1ns/1ps
module tb;
  reg {clock};
{odecl}
  {top} {dut}({conns});
  integer {rc};
  initial begin
    {clock} = 0;
    for ({rc} = 0; {rc} < {NO_INPUT_CYCLES}; {rc} = {rc} + 1) begin
      #1;
      $display("{dispfmt}"{dispargs});
      {clock} = 1; #1;
      {clock} = 0; #1;
    end
    $finish;
  end
endmodule
"""
    return f"""`timescale 1ns/1ps
module tb;
  reg {clock};
{decl}
{odecl}
  {top} {dut}({conns});
  integer {fd}, {rc};
  initial begin
    {clock} = 0;
    {fd} = $fopen("{vecpath}", "r");
    {rc} = $fscanf({fd}, "{scanfmt}"{scanargs});
    while ({rc} == {len(in_names)}) begin
      #1;
      $display("{dispfmt}"{dispargs});   // sample outputs from current register state
      {clock} = 1; #1;                    // rising edge: registers update
      {clock} = 0; #1;
      {rc} = $fscanf({fd}, "{scanfmt}"{scanargs});
    end
    $finish;
  end
endmodule
"""


def simulate_seq_verilog(verilog_path, top, inputs, outputs, seq, clock, reset, workdir):
    """Simulate a sequential design over a clock sequence; returns list of
    {out_name: value}, one per cycle, sampled before each rising edge."""
    di = data_inputs(inputs, clock)
    ctrl = [(n, w) for (n, w) in inputs if is_reset(n)]
    in_names = [n for n, _ in (di + ctrl)]
    out_names = [n for n, _ in outputs]
    vecpath = os.path.join(workdir, "seq.txt")
    with open(vecpath, "w") as f:
        for v in seq:
            f.write(" ".join(str(v.get(n, 0)) for n in in_names) + "\n")
    tb = _tb_seq(top, inputs, outputs, vecpath, clock, reset)
    tbpath = os.path.join(workdir, "tb.v")
    open(tbpath, "w").write(tb)
    simbin = os.path.join(workdir, "sim.out")
    _run(["iverilog", "-g2012", "-o", simbin, tbpath, verilog_path],
         IVERILOG_TIMEOUT, "iverilog")
    r = _run(["vvp", simbin], VVP_TIMEOUT, "vvp")
    return _parse_samples(r.stdout, out_names)


# ---------------------------------------------------------------------------
# Lean reference simulation
# ---------------------------------------------------------------------------

def lean_sim(top, inputs, cycles, leanrtl_bin=None, nvec=None):
    """Run the Lean denotational reference over input cycles (list of {name: value}).
    Returns list of {out_name: value}.

    `nvec` is a comma-separated parameter vector: when given, the reference is the design's
    generator applied to THAT vector rather than to its declared defaults.  The caller is
    responsible for having built the other side of the comparison at the same vector."""
    leanrtl_bin = leanrtl_bin or LEANRTL_BIN
    all_in = [n for n, _ in inputs]
    lines = []
    for v in cycles:
        lines.append(" ".join(f"{n}={v.get(n, 0)}" for n in all_in))
    inp = "\n".join(lines) + "\n"
    cmd = [leanrtl_bin, "sim", top] + (["--N", nvec] if nvec else [])
    r = subprocess.run(cmd, input=inp, capture_output=True, text=True)
    if r.returncode != 0:
        raise RuntimeError("leanrtl sim failed:\n" + r.stderr)
    res = []
    for line in r.stdout.strip().split("\n"):
        if not line.strip():
            continue
        d = {}
        for tok in line.split():
            k, val = tok.split("=")
            d[k] = int(val)
        res.append(d)
    return res
