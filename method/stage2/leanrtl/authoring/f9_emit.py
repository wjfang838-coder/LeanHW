#!/usr/bin/env python3
"""
F9 procedural-Verilog emission with a per-design equivalence anchor.

`f9_or_none` emits `leanrtl vverilog <key>` (procedural next-state SystemVerilog: register
next-state computed inside the clocked always block, mux decision-trees lowered to `if/else`
statements) and PROVES it logically equivalent to the *verified* RTLIL (`gold_json`, produced by
`leanrtl extract` on the machine-checked compiler) via a Yosys `equiv_induct` miter.

It returns the path to the F9 Verilog **only if** the miter proves equivalence; otherwise `None`,
so the caller falls back to the standard `write_verilog` path.  This preserves the proof-carrying
guarantee: the emitted Verilog is used only when certified to compute the same logic as the verified
netlist.  In 2-state SAT `if/else` and `$mux` are identical, so the miter certifies the *logic* is
the proven logic while the procedural *rendering* recovers faithful blocking-assignment scheduling
and 4-state `if(x)`-as-false behavior that the continuous-assign `$dff` netlist mis-simulates.
"""
import os, subprocess, re, json, time

_MITER = """
read_json {gold}
hierarchy -top {top}
proc; opt; clean
rename {top} gold
design -stash gold
read_verilog -sv {gate}
hierarchy -top {top}
proc; opt; clean
rename {top} gate
design -stash gate
design -copy-from gold -as gold gold
design -copy-from gate -as gate gate
equiv_make gold gate equiv
hierarchy -top equiv
async2sync
opt -full
equiv_simple
equiv_induct
equiv_status -assert
"""


def _sh(cmd, t=180):
    return subprocess.run(cmd, capture_output=True, text=True, timeout=t)


def f9_or_none(leanrtl, key, top, gold_json, wd, port_order=None):
    """Return (path_to_F9_verilog | None, detail).  None => caller falls back to write_verilog.

    `port_order`, when given, is the header port order the design's own contract declares.  The
    emitted header is non-ANSI — directions and widths are declared by name on their own lines —
    so this reorders the parenthesis list and nothing else, and the miter below (which matches
    ports by NAME) is unaffected either way.  It exists because a benchmark testbench may bind by
    POSITION, which no name-based check in this pipeline can see.  If the emitter rejects the
    order as not a permutation of the module's ports, the emission is retried without it and the
    disagreement is recorded in the returned detail rather than silently applied or silently lost.
    """
    if os.environ.get("F9_DISABLE"):            # baseline / regression-comparison escape hatch
        return None, "f9_disabled"
    gate = os.path.join(wd, f"{top}_f9.v")
    order_note = ""
    v = None
    argv = ["vverilog", key]
    if port_order:
        v = _sh([leanrtl] + argv + ["--port-order", ",".join(port_order)])
        if v.returncode != 0:
            order_note = "|port_order_rejected:" + (v.stderr or "")[-80:].strip()
            v = None
        else:
            argv += ["--port-order", ",".join(port_order)]
    if v is None:
        v = _sh([leanrtl] + argv)
    if v.returncode != 0 or not v.stdout.strip().startswith("module"):
        return None, "vverilog_unsupported:" + (v.stderr or v.stdout)[-120:].strip() + order_note

    # A delay-driven step timebase (`Module.stepDelay`) is invisible to Yosys, so it gets its own
    # anchor rather than the plain miter.  Checked BEFORE the combinational guard below: `always #n`
    # carries no posedge, and falling back to `write_verilog` here would silently discard the delay
    # and re-emit the very $dff-on-a-constant-clock netlist stepDelay exists to replace.
    if any(_ALWAYS_DELAY.match(l) for l in v.stdout.splitlines()):
        open(gate, "w").write(v.stdout)
        p, d = _timed_or_none(leanrtl, key, top, gold_json, wd, argv, gate, v.stdout)
        return p, d + order_note

    # F9 only helps SEQUENTIAL modules: its win is procedural next-state inside a clocked
    # always block. A purely-combinational module has no `always @(posedge …)`; forcing its
    # outputs through a clocked/procedural rendering can break combinational simulation even
    # though the miter proves 2-state logical equivalence. Fall back to write_verilog.
    if not any(s in v.stdout for s in
               ("always @(posedge", "always @ (posedge", "always @(negedge", "always @ (negedge")):
        return None, "combinational_no_f9" + order_note
    open(gate, "w").write(v.stdout)
    ys = os.path.join(wd, "f9_miter.ys")
    open(ys, "w").write(_MITER.format(gold=gold_json, gate=gate, top=top))
    try:
        y = _sh(["yosys", ys])
    except subprocess.TimeoutExpired:
        return None, "miter_timeout" + order_note
    blob = y.stdout + y.stderr
    if "Equivalence successfully proven!" in blob:
        return gate, "miter_proven" + order_note
    m = re.search(r"(Found \d+ unproven.*|.*proof did fail.*|ERROR:.*)", blob)
    return None, "miter_fail:" + (m.group(1)[:120] if m else "unknown") + order_note


_ALWAYS_DELAY = re.compile(r"^\s*always\s+#\d+\s+begin\s*$")
_ALWAYS_EDGE = re.compile(r"^\s*always\s+@\((posedge|negedge)\s+\S+\)\s+begin\s*$")


def _timed_or_none(leanrtl, key, top, gold_json, wd, argv, gate, timed_text):
    """Certify a delay-driven (`Module.stepDelay`) emission, or return None.

    Yosys cannot read `always #n begin … end`, so the miter that anchors every other emission
    cannot run on this file at all.  Rather than ship it unproven, emit the SAME module a second
    time with `--clocked` — which changes the sensitivity line and nothing else — prove THAT
    against the verified RTLIL, and then require the two files to differ on exactly one line,
    which must be an `always` header on both sides.  What that buys is precise and worth stating
    precisely: the port list, the declarations, the reset branch and every next-state statement
    are certified equal to the proven netlist; the choice of what advances a step is not, and
    cannot be, because RTLIL has no delay.  That residue is what `CoverageReason.timedStep`
    records, and it is why this route never reports plain `miter_proven`.
    """
    twin = os.path.join(wd, f"{top}_f9_clocked.v")
    c = _sh([leanrtl] + argv + ["--clocked"])
    if c.returncode != 0 or not c.stdout.strip().startswith("module"):
        return None, "timed_step:clocked_twin_failed"
    open(twin, "w").write(c.stdout)
    ys = os.path.join(wd, "f9_timed_miter.ys")
    open(ys, "w").write(_MITER.format(gold=gold_json, gate=twin, top=top))
    try:
        y = _sh(["yosys", ys])
    except subprocess.TimeoutExpired:
        return None, "timed_step:miter_timeout"
    blob = y.stdout + y.stderr
    if "Equivalence successfully proven!" not in blob:
        m = re.search(r"(Found \d+ unproven.*|.*proof did fail.*|ERROR:.*)", blob)
        return None, "timed_step:miter_fail:" + (m.group(1)[:100] if m else "unknown")

    a, b = timed_text.splitlines(), c.stdout.splitlines()
    if len(a) != len(b):
        return None, f"timed_step:delta_len:{len(a)}vs{len(b)}"
    diff = [i for i, (x, y_) in enumerate(zip(a, b)) if x != y_]
    if len(diff) != 1:
        return None, "timed_step:delta_lines:" + ",".join(str(i + 1) for i in diff[:8])
    i = diff[0]
    if not (_ALWAYS_DELAY.match(a[i]) and _ALWAYS_EDGE.match(b[i])):
        return None, f"timed_step:delta_not_sensitivity:{a[i].strip()[:40]!r}"
    return gate, f"timed_step:clocked_twin_proven,delta=1line@{i + 1}:{a[i].strip()}"


def module_params(leanrtl, key):
    """The module's declared Verilog parameters as [(name, value)], or [] if it declares none."""
    r = _sh([leanrtl, "params", key], t=60)
    if r.returncode != 0:
        return []
    out = []
    for line in r.stdout.splitlines():
        if "=" in line:
            n, _, v = line.partition("=")
            if n.strip() and v.strip().isdigit():
                out.append((n.strip(), int(v.strip())))
    return out


_PARAM_DECL = re.compile(r"\bparameter\b(?!\s*\btype\b)([^;]*);", re.S)
_NAME_EQ = re.compile(r"([A-Za-z_]\w*)\s*=")
_PARAM_KW = {"signed", "unsigned", "integer", "reg", "wire", "logic", "bit", "int", "localparam"}


def inert_params(src):
    """The parameters the module DECLARES and its body never READS — the ones it is lying about.

    A `parameter` that occurs in exactly one place, its own declaration, cannot change anything
    about the circuit.  Overriding it at elaboration — `dut #(.DATA_WIDTH(12)) u (…)`, which is
    precisely what a CVDP `param_draw` testbench does — therefore yields the SAME fixed-width
    module, and the design fails for a reason no other check in this pipeline can see: it
    elaborates, it synthesises, it has no undriven net, its Lean theorem is true of it, and the
    `_MITER` below proves it equivalent to the gold RTLIL.  That last proof is where the blind spot
    lives: the miter reads the gate with `read_verilog -sv` and no `-chparam`, so it only ever
    builds the DEFAULT instance.  "Equivalence successfully proven!" is true and says nothing at
    all about any other width.

    So the question has to be asked separately, and asked of the emitted TEXT rather than of the
    RTLIL, because RTLIL has no parameters to ask about.  A mention inside another parameter's
    initialiser counts as a use: over-approximating "used" keeps this from crying wolf, which is
    the safe direction for a check whose whole value is that a hit is worth acting on.
    """
    end = src.find("endmodule")
    body = src[:end if end != -1 else len(src)]
    decl_at, names = {}, []
    for d in _PARAM_DECL.finditer(body):
        for nm in _NAME_EQ.finditer(d.group(1)):
            if nm.group(1).lower() in _PARAM_KW:
                continue
            names.append(nm.group(1))
            decl_at.setdefault(nm.group(1), set()).add(
                (d.start(1) + nm.start(1), d.start(1) + nm.end(1)))
    out = []
    for nm in names:
        spans = decl_at.get(nm, set())
        uses = [u for u in re.finditer(r"\b%s\b" % re.escape(nm), body) if u.span() not in spans]
        if not uses:
            out.append(nm)
    return out


def inject_params(vpath, params, gold_json, top, wd):
    """Add `parameter` declarations to a `write_verilog`-route netlist, then RE-PROVE it.

    The F9 emitter renders parameters itself.  The fallback route does not and cannot: its Verilog
    is produced by Yosys from RTLIL, and RTLIL has no representation for a Verilog parameter.  So a
    combinational design whose spec declares parameters — and whose testbench therefore instantiates
    it as `dut #(.N(32)) u (…)` — cannot elaborate on that route no matter how correct its logic is.

    The edit is textual and deliberately narrow: insert `parameter NAME = VALUE;` after the module
    header, and rewrite a PORT declaration's range to `[NAME-1:0]` when its width matches a declared
    parameter.  Textual edits to generated Verilog are exactly the kind of thing that silently
    breaks, so the result is handed back to the same `equiv_induct` miter that certifies the F9
    route: the rewrite is applied only if it is proven to compute the same logic as the verified
    RTLIL.  Returns (ok, detail); on failure the file is left untouched.
    """
    if not params:
        return True, "no_params"
    src = open(vpath).read()
    m = re.search(r"^(module\s+\S+\s*\([^)]*\)\s*;)\s*$", src, re.M)
    if not m:
        return False, "params_inject:no_module_header"
    by_width = {}
    for n, v in params:
        by_width.setdefault(v, n)
    decls = "\n".join(f"  parameter {n} = {v};" for n, v in params)
    out = src[:m.end(1)] + "\n" + decls + src[m.end(1):]

    def _port(mo):
        kw, hi, lo, rest = mo.group(1), int(mo.group(2)), mo.group(3), mo.group(4)
        name = by_width.get(hi + 1)
        return f"  {kw} [{name}-1:{lo}] {rest}" if (name and lo == "0") else mo.group(0)

    out = re.sub(r"^  (input|output|inout) \[(\d+):(\d+)\] (\S+;)$", _port, out, flags=re.M)

    cand = os.path.join(wd, "params_" + os.path.basename(vpath))
    open(cand, "w").write(out)
    ys = os.path.join(wd, "params_miter.ys")
    open(ys, "w").write(_MITER.format(gold=gold_json, gate=cand, top=top))
    try:
        y = _sh(["yosys", ys])
    except subprocess.TimeoutExpired:
        return False, "params_inject:miter_timeout"
    blob = y.stdout + y.stderr
    if "Equivalence successfully proven!" not in blob:
        mm = re.search(r"(Found \d+ unproven.*|.*proof did fail.*|ERROR:.*)", blob)
        return False, "params_inject:miter_fail:" + (mm.group(1)[:100] if mm else "unknown")
    open(vpath, "w").write(out)
    # The miter above proved the DEFAULT instance equivalent.  Whether the parameter it just
    # inserted does any work at any other width is a different question, and on this route the
    # answer is usually no: `_port` rewrites a port RANGE when its width happens to match a
    # declared value, and nothing rewrites the body, which Yosys emitted at fixed width.  Say so
    # rather than returning a bare "params_injected", because a decorative parameter is not a
    # cosmetic defect -- it is the whole difference between passing and failing a `param_draw`
    # testbench, and it is invisible to every other gate.  Recorded, not fatal: refusing the emit
    # would turn a design that fails one testbench into a design that shipped nothing, which
    # destroys the evidence instead of reporting it.
    dead = inert_params(out)
    detail = "params_injected:" + ",".join(f"{n}={v}" for n, v in params)
    return True, detail + ("|inert:" + ",".join(dead) if dead else "|all_read")


_PARAM_MITER = """
read_json {gold}
hierarchy -top {top}
proc; opt; clean
rename {top} gold
design -stash gold
read_verilog -sv {gate}
hierarchy -top {top}{chparam}
proc; opt; clean
rename {top} gate
design -stash gate
design -copy-from gold -as gold gold
design -copy-from gate -as gate gate
equiv_make gold gate equiv
hierarchy -top equiv
async2sync
opt -full
equiv_simple
# Deeper than the default 4.  `equiv_make` cuts the induction at wires the two designs NAME the
# same, and a parametric register array cannot be named the way the compiler names it: the
# elaborated module has `s_0 … s_4`, and no Verilog declares N separately-named regs when N is a
# parameter, so the emitted text says `reg s [0:N-1]` and the FFs go unmatched.  The cone then runs
# back through the whole shift chain, and the induction needs as many time frames as the chain is
# long.  A 5-deep chain fails at the default and passes here; 32 is chosen to cover any pipeline
# depth these designs plausibly have, and it costs only unproven cells -- a proven one never
# reaches the deeper frames.
equiv_induct -seq 32
equiv_status -assert
"""


# The bounded fallback's ceiling and its wall-clock budget.
#
# `-maxsteps` is a CEILING, not a target.  Yosys proves the base case at length 1, then 2, then 3
# — `-initsteps` speeds up only the induction half, so there is no way to jump straight to N — and
# each solve is bigger than the last.  What actually stops the run is the clock, so the frame count
# is set high enough not to be the binding constraint and the depth reached is READ OFF the log
# rather than assumed.  That is the honest reading anyway: the certificate is "they agree for the
# first K cycles from reset", and K is a measurement.
_BOUNDED_FRAMES = 64
# Measured, on a 16-entry queue miter at DATA_WIDTH=8: frames 1..19 all proven inside 360 s, and
# then frame 20 alone ran past 180 s without finishing.  The cost per frame is not flat, it climbs,
# so the budget past this point buys single frames at minutes apiece — and `emit` is a step an
# authoring agent sits and waits on, out of a fixed wall-clock budget for the whole design.  A
# deeper number in the detail string is not worth the minutes it costs the author.
_BOUNDED_SECONDS = 360
# Below this the bounded claim is not worth reporting: a handful of cycles from reset is inside the
# stretch where most designs are still holding their reset values and nothing has been exercised.
_BOUNDED_MIN = 8
# A CEILING on the whole anchoring step, across every vector and both miters.
#
# There was none, and the per-miter caps multiply: three vectors at 600 s of induction plus two at
# `_BOUNDED_SECONDS` of bounded work is 42 minutes, inside a step an author calls once and waits
# on, out of a fixed budget for the entire design.  That is not hypothetical -- a design whose four
# proof sections were all green was killed at its budget with the log reading "Emit is running" and
# shipped NOTHING, because `emit` alone could outlast what it had left.
#
# The floor below is what makes the deadline safe to enforce: anchoring stops at a vector boundary
# and reports what it established, so running out of clock costs evidence, never the artifact.
_ANCHOR_BUDGET = 1200
# Starting a miter with less than this left buys nothing -- it cannot reach `_BOUNDED_MIN` frames
# and its only possible outcome is to burn the remainder and be reported as a timeout.
_ANCHOR_MIN_SLICE = 90

_PARAM_MITER_BOUNDED = """
read_json {gold}
hierarchy -top {top}
proc; opt; clean
rename {top} gold
design -stash gold
read_verilog -sv {gate}
hierarchy -top {top}{chparam}
proc; opt; clean
rename {top} gate
design -stash gate
design -copy-from gold -as gold gold
design -copy-from gate -as gate gate
miter -equiv -flatten -make_assert gold gate miter
hierarchy -top miter
async2sync
opt -full
# `-tempinduct-baseonly -maxsteps N`, NOT `-seq N`.  Yosys's own help: "The following additional
# options can be used to set up a proof.  If also -seq is passed, a temporal induction proof is
# performed."  So `sat -prove-asserts -seq N` is an INDUCTION, starting from a free state, which is
# the very thing `equiv_induct` already failed at -- a holding FIFO would fail it again for exactly
# the same reason and this fallback would prove nothing it did not already know.  The base case of
# temporal induction IS the bounded check from the power-on state, and `-tempinduct-baseonly` runs
# that half alone.
sat -prove-asserts -tempinduct-baseonly -maxsteps {frames} -verify
"""


def _bounded_failed(blob):
    """Did the bounded miter find a counterexample?

    Kept apart from "did it prove anything", because the two are not complements here: a run
    stopped by the clock has neither proven its ceiling nor failed, and calling that a failure
    would throw away every frame it did prove."""
    return ("FAIL!" in blob or "Assert failed" in blob
            or "Temporal induction failed" in blob or "Induction failed" in blob)


def _bounded_depth(blob):
    """The deepest frame count whose base case was proven, or 0.

    Read from the log rather than inferred from the exit status, so that a run the clock stopped
    still reports what it established.  Yosys prints one such line per length."""
    ks = re.findall(r"Base case for induction length (\d+) proven", blob)
    return max((int(k) for k in ks), default=0)


def param_vectors(defaults):
    """The parameter vectors the parametric emission is anchored at: the declared defaults, then
    one off-default value of each parameter in turn (the rest held at their defaults).

    One-at-a-time, not a full grid, and that is the point.  The defect this whole route exists to
    kill is a parameter the body never reads, and a parameter is inert exactly when moving it
    ALONE changes nothing.  A vector that moves everything at once would still catch it, but it
    would not say WHICH parameter was decorative; moving one at a time names it.

    Halving is the off-default value because it preserves the properties a design is entitled to
    assume of a width — a power of two stays a power of two, an even width stays even — while
    still being small enough to keep the SAT instance cheap.  Floor of 2, because a 1-bit or 0-bit
    version of a datapath is degenerate in ways the spec never claimed.
    """
    base = list(defaults)
    vecs = [base]
    for i, v in enumerate(base):
        alt = max(2, v // 2) if v >= 4 else v + 1
        if alt != v:
            vecs.append(base[:i] + [alt] + base[i + 1:])
    return vecs


def param_anchor(leanrtl, key, top, names, defaults, vpath, wd):
    """Prove PARAMETRIC SystemVerilog equivalent to the verified compiler, at more than one vector.

    This is the parametric route's half of the proof-carrying invariant, and without it the route
    has none.  `leanrtl pverilog` derives its widths and constants by fitting the design's own
    `gen` over a grid and re-checking the fit at held-out vectors -- but that is a statement about
    the FORMULAS, not about the Verilog: it says the fitted `DATA_WIDTH*NUM_TAPS` reproduces what
    `gen` returns, and says nothing about whether the module text built around it computes the
    logic the machine-checked compiler proved.  So each vector here is anchored the same way F9 is:
    `leanrtl extract <key> --N <vector>` runs the PROVEN compiler at that vector to get the gold
    netlist, and the same `equiv_induct` miter proves the parametric module -- elaborated at that
    vector via `hierarchy -chparam` -- against it.

    `-chparam` is the whole difference from `_MITER`.  `_MITER` reads the gate with plain
    `read_verilog -sv`, so it only ever builds the DEFAULT instance; that blind spot is why a
    module could declare a parameter, never read it, and still be certified.  Overriding the
    parameter here is what makes the certificate say something about the family.

    A vector whose gold cannot be produced is SKIPPED and named, not failed: `gen` may legitimately
    be ill-formed away from its defaults (a width the spec requires to be a multiple of something),
    and a design is not wrong for that.  A vector that produces a gold and then fails BOTH miters IS
    fatal -- that is the emitted module disagreeing with the proven one.

    ## Two miters, and why the second one is not a weakening of the first

    `equiv_induct` proves equivalence by temporal induction from a FREE initial state: it shows that
    if the two designs agree for k frames they agree at k+1, for every state they could conceivably
    be in.  That is unbounded and it is the certificate we want.  It is also *impossible* for a
    design with HOLDING storage.  A queue idle-holds its contents, so its output is a function of
    inputs arbitrarily far in the past; no finite k makes the state a function of the last k inputs,
    and `equiv_make` cannot bridge the gap by matching register names because a parametric array is
    declared `reg [W-1:0] s [0:N-1]` while the compiler's netlist names the same flops `s_0 … s_4`.
    Raising `-seq` does not help and cannot: the two designs genuinely differ at some unreachable
    state, and induction quantifies over unreachable states.  Three designs in the parameter subset
    are queues, and all three failed here, fell all the way back to a non-parametric Yosys netlist,
    and shipped with no parameter at all.

    So when induction fails, this retries from the COMMON POWER-ON STATE for a bounded number of
    frames.  That is only sound because both sides now HAVE a power-on state and it is the same one:
    the compiler's netlist carries `init` attributes, and `emitPVerilog` emits an `initial` block for
    every register whose `init` is a literal (which it now refuses to emit without), and Yosys `proc`
    turns that block into the same `init` attributes.  Before that fix the gate powered up at `x` and
    this fallback would have been unsound rather than merely weaker.

    It IS weaker, and the detail string says which vectors got which, so no design can quietly be
    reported as carrying the unbounded certificate when it carries the bounded one.  What the bounded
    proof states: from reset, for the K cycles the detail string reports, the emitted module and the
    machine-checked
    compiler's netlist agree on every output for EVERY input sequence.  That is a real proof over all
    inputs -- it is bounded in time, not sampled.
    """
    vecs = param_vectors(defaults)
    proven, bounded, skipped, inconclusive, deferred, reasons = [], [], [], [], [], []
    t0 = time.monotonic()
    def _left():
        return _ANCHOR_BUDGET - (time.monotonic() - t0)
    for vec in vecs:
        tag = ",".join(str(v) for v in vec)
        if _left() < _ANCHOR_MIN_SLICE:
            # Out of clock, at a vector boundary.  Everything already appended to `proven` and
            # `bounded` was established by a miter that ran to a verdict, so stopping here does not
            # weaken a single claim -- it only stops making new ones.  The rest are named.
            deferred.append(tag)
            continue
        gold = os.path.join(wd, f"pgold_{key}_{tag.replace(',', '_')}.json")
        g = _sh([leanrtl, "extract", key, "--N", tag, "-o", gold])
        if g.returncode != 0 or not os.path.exists(gold):
            if vec == list(defaults):
                # The defaults are what the spec itself states, so `gen` failing there is not a
                # parameter being out of range -- it is the design.
                return False, f"param_anchor:gold_failed_at_defaults:{tag}"
            skipped.append(tag)
            continue
        chparam = "".join(f" -chparam {n} {v}" for n, v in zip(names, vec))
        ys = os.path.join(wd, f"pminer_{key}_{tag.replace(',', '_')}.ys")
        open(ys, "w").write(_PARAM_MITER.format(gold=gold, gate=vpath, top=top,
                                                chparam=chparam))
        try:
            y = _sh(["yosys", ys], t=max(_ANCHOR_MIN_SLICE, min(600, _left())))
            blob = y.stdout + y.stderr
        except subprocess.TimeoutExpired:
            blob = ""
        if "Equivalence successfully proven!" in blob:
            proven.append(tag)
            continue
        # Induction did not close.  Retry bounded from the common power-on state before calling it
        # a failure -- see the docstring.  A vector that fails BOTH is reported with the INDUCTION
        # miter's message, because that is the stronger claim and its failure is the informative one.
        #
        # Unless the verdict is already settled.  The bounded miter is the expensive step here by a
        # wide margin -- `equiv_induct` fails in well under a minute on the designs that fail it,
        # while the bounded run is budgeted minutes and reliably spends all of them -- and once two
        # vectors are anchored, a third can only lengthen the detail string.  It cannot change the
        # verdict: `refuted` is the only other outcome and it is reachable only THROUGH this run.
        # So the vector is named as deferred rather than run, and rather than silently dropped: a
        # reader must be able to see that the module carries no certificate at it.
        if len(proven) + len(bounded) >= 2:
            deferred.append(tag)
            continue
        ysb = os.path.join(wd, f"pminerb_{key}_{tag.replace(',', '_')}.ys")
        blog = os.path.join(wd, f"pminerb_{key}_{tag.replace(',', '_')}.log")
        open(ysb, "w").write(_PARAM_MITER_BOUNDED.format(gold=gold, gate=vpath, top=top,
                                                         chparam=chparam,
                                                         frames=_BOUNDED_FRAMES))
        # `-l` rather than the pipe, so the depth reached survives the clock stopping the run.
        # On a TimeoutExpired the child is killed and its buffered stdout is not something to
        # depend on; the log file is already on disk.
        try:
            _sh(["yosys", "-l", blog, ysb],
                t=max(_ANCHOR_MIN_SLICE, min(_BOUNDED_SECONDS, _left())))
        except subprocess.TimeoutExpired:
            pass
        bblob = open(blog).read() if os.path.exists(blog) else ""
        depth = _bounded_depth(bblob)
        if _bounded_failed(bblob):
            # A COUNTEREXAMPLE, not a proof that ran out of room: the bounded miter drove both
            # sides from the same power-on state and they disagreed on an output at a finite
            # cycle.  That is the emitted module contradicting the machine-checked compiler, and
            # nothing further in this loop can make it not so.  Stop here and say which vector.
            wit = re.search(r"(Assert failed.*|.*Temporal induction failed.*)", bblob)
            return False, (f"param_anchor:refuted@{tag}:"
                           + (wit.group(1)[:120] if wit else "counterexample"))
        if depth >= _BOUNDED_MIN:
            bounded.append(f"{tag}:{depth}")
            continue
        # Neither miter reached a verdict at this vector: the induction left cells unproven and the
        # bounded run did not get deep enough to be worth reporting.  That is INCONCLUSIVE, and it
        # is not the same thing as the two designs differing.  Record it and keep going -- one
        # expensive vector must not knock a design off the parametric route when the others close,
        # which is what returning here used to do.
        mm = re.search(r"(Found \d+ unproven.*|.*proof did fail.*|ERROR:.*)", blob)
        inconclusive.append(f"{tag}:{depth}" if depth else tag)
        note = "timeout" if not blob else (mm.group(1)[:80] if mm else "unknown")
        reasons.append(f"{tag}={note}")
    if len(proven) + len(bounded) < 2:
        # One proven vector is exactly the guarantee the old route already had, and it is the one
        # a decorative parameter survives.  Refuse rather than report a parametric certificate
        # that covers a single instance.
        return False, ("param_anchor:too_few_vectors_anchored"
                       + (":inconclusive=" + ";".join(reasons) if reasons else "")
                       + (":skipped=" + ";".join(skipped) if skipped else ""))
    detail = "param_anchor:proven@" + ";".join(proven) if proven else "param_anchor:proven@none"
    if bounded:
        # `<vector>:<frames>` — the depth is per vector and is a measurement, so it is reported per
        # vector.  A reader must be able to tell a 40-cycle certificate from a 9-cycle one.
        detail += "|bounded@" + ";".join(bounded)
    if inconclusive:
        # Named, not dropped.  These vectors carry NO certificate: the module ships because other
        # vectors anchored it, and a reader must be able to see which instances that claim does
        # not cover.
        detail += "|inconclusive@" + ";".join(inconclusive)
    if deferred:
        # Same status as `inconclusive` -- no certificate at these vectors -- but a different
        # reason, and the distinction is worth the extra word.  `inconclusive` means both miters ran
        # and neither reached a verdict; `deferred` means the bounded miter was never given the
        # minutes because the verdict was already settled by two other vectors.
        detail += "|deferred@" + ";".join(deferred)
    return True, detail + ("|skipped=" + ";".join(skipped) if skipped else "")


def contract_port_order(contract_path):
    """The header order a design's contract declares, or None if it declares none.

    The contract is the author's record of the interface the SPEC states, written before any
    Verilog exists; `ports` is a list of `{name, dir, width}` in the order the spec gives them.
    Returning it here is what lets the emitter honour a declared order the `Module` literal (which
    carries inputs and outputs as two separate lists) cannot itself express.
    """
    try:
        with open(contract_path) as f:
            c = json.load(f)
    except Exception:
        return None
    ports = c.get("ports")
    if not isinstance(ports, list):
        return None
    names = [p.get("name") for p in ports if isinstance(p, dict) and p.get("name")]
    return names or None



if __name__ == "__main__":
    import sys, tempfile
    REPO = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
    LEANHDL = os.path.join(REPO, ".lake", "build", "bin", "leanrtl")
    key, top = sys.argv[1], (sys.argv[2] if len(sys.argv) > 2 else sys.argv[1])
    with tempfile.TemporaryDirectory() as wd:
        gold = os.path.join(wd, "gold.json")
        e = _sh([LEANHDL, "extract", key, "-o", gold])
        if e.returncode != 0:
            print("extract failed:", (e.stderr + e.stdout)[-200:]); sys.exit(1)
        path, detail = f9_or_none(LEANHDL, key, top, gold, wd)
        print(f"{key}: {'F9 USED' if path else 'FALLBACK'}  ({detail})")
