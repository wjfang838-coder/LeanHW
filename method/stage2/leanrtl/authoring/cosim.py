#!/usr/bin/env python3
"""Layer 7: differential co-simulation of the LeanRTL *semantics* against the
LeanRTL-*generated* Verilog.  Confirms the (trusted) compiler preserves behaviour.

  cosim.py <design.rtlil.json> <generated.v> [--seq] [--cycles N] [--key <name>] [--N <v1,v2,…>]

--key: `leanrtl sim` lookup name when it differs from the Verilog module name
(VerilogEval designs are all named TopModule but registered under Prob0NN_* keys).

--N: the parameter vector the two artifacts were built at.  Passed straight through to
`leanrtl sim`, so that both sides of the comparison are the same instance.

--strict-observations: require one complete known output row from both simulators for
EVERY supplied vector. Frozen equivalence runs use this mode; no x/z prefix is skipped.

Exit 0 iff the applicable sample-coverage checks pass and every compared vector / cycle agrees.  Prints a JSON summary on the last line."""
import sys, os, json, tempfile
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import simlib


def main(argv):
    rtlil = argv[0]
    verilog = argv[1]
    seq = "--seq" in argv
    cycles = 64
    if "--cycles" in argv:
        idx = argv.index("--cycles") + 1
        if idx >= len(argv) or not argv[idx].isdigit():
            print("cosim: --cycles needs a numeric argument", file=sys.stderr)
            return 2
        cycles = int(argv[idx])
    sim_key = argv[argv.index("--key") + 1] if "--key" in argv else None

    top, inputs, outputs = simlib.load_interface(rtlil)
    lean_key = sim_key or top

    try:
        return _compare(argv, rtlil, verilog, seq, cycles, top, inputs, outputs, lean_key)
    except RuntimeError as e:
        # iverilog/vvp/leanrtl failed to RUN.  That is a statement about this harness or the
        # toolchain, not about the candidate, and it must not be reported in the same field as a
        # semantic disagreement -- `alu` was logged as cosim_fail because the generated testbench
        # declared `integer fd, r;` against a design with an output port named `r`.
        # See docs/findings/HARNESS_SELF_ATTRIBUTION.md.
        print(json.dumps({"module": top, "kind": "seq" if seq else "comb",
                          "status": "harness_error", "err_class": "harness_error",
                          "error": str(e)[:2000]}))
        return 3


def _is_vacuous(hw) -> bool:
    """Sequential stimulus heuristic: did any known output vary?

    A constant sequential run may have remained in reset, so the driver can retry a reset
    polarity. Constant combinational functions are valid and are checked by direct comparisons.
    """
    known = [x for x in hw if x is not None]
    return len({repr(x) for x in known}) <= 1


def _drive(simlib, inputs, outputs, cycles, active_low, clock, reset, verilog, top, lean_key,
           nvec=None):
    vectors, _ = simlib.gen_seq_vectors(inputs, cycles=cycles, active_low=active_low,
                                        clock=clock)
    with tempfile.TemporaryDirectory() as wd:
        hw = simlib.simulate_seq_verilog(verilog, top, inputs, outputs, vectors,
                                         clock, reset, wd)
    return vectors, hw, simlib.lean_sim(lean_key, inputs, vectors, nvec=nvec)


def _compare(argv, rtlil, verilog, seq, cycles, top, inputs, outputs, lean_key):
    # `--N <v1,v2,…>`: compare the design at a NON-default parameter vector.  The netlist and the
    # Verilog handed to this script were both built at that vector by the caller, so the Lean side
    # must be too -- run it at the defaults and every width would disagree for a reason that is
    # this harness's, not the design's.
    nvec = argv[argv.index("--N") + 1] if "--N" in argv else None
    polarity = None
    if seq:
        # The design's declared clock wins over the {clk, clock} name whitelist: a two-clock
        # design names neither port `clk`, and inferring from the name reported the harness's
        # blind spot as a failure of the design.
        named = argv[argv.index("--clock") + 1] if "--clock" in argv else None
        clock = (named if named and any(n == named for n, _ in inputs)
                 else next((n for n, _ in inputs if simlib.is_clock(n)), None))
        reset = next((n for n, _ in inputs if simlib.is_reset(n)), None)
        if clock is None:
            raise RuntimeError(
                "--seq but no clock input found: the design declares a clock but this harness "
                f"could not identify it among {[n for n, _ in inputs]}"
                + (f" (declared name {named!r} is not an input port)" if named else
                   "; pass --clock <name>"))
        # Polarity must follow how the DESIGN treats the port, not a blanket assumption.
        # `Module.reset` is active-high, so `active_low=False` is right for a design that uses
        # that channel -- but a design that folds an active-low reset IN-BAND (Module.reset :=
        # none, `rst_n` an ordinary input tested against 0) is then driven with rst_n=1 on cycle
        # 0 and rst_n=0 for the other 63, i.e. held in reset for the whole run.  Both sides
        # output zeros, the run "passes" 64/64, and nothing was compared.  Found by an author
        # who wrote its own testbench because it did not believe the result.
        #
        # In-band is the common case here precisely because Module.reset cannot express rst_n.
        # So: auto-detect from the name unless the module declares the reset channel.
        active_low = None
        if reset is not None and "--reset-active-high" in argv:
            active_low = False
        # A design whose registers carry per-register `clockNet` is genuinely multi-clock, and
        # `Module.simulate` -- the Lean side of this comparison -- edges ONE clock per cycle.
        # Comparing against it would be comparing the design to a semantics that does not model
        # it.  Say so, rather than driving the second clock from the vector file and reporting
        # the resulting disagreement as the design's.
        if "--multiclock" in argv:
            raise RuntimeError(
                "design declares per-register clockNet (multi-clock); Module.simulate models a "
                "single clock, so co-simulation cannot compare these two on equal terms.  "
                "`leanrtl check` reports the same thing as CoverageReason.clockNet.")
        # If the chosen polarity holds the design in reset for the whole run, nothing is
        # compared and the verdict is `vacuous` -- a statement about the STIMULUS, not the
        # design.  The port name carries no polarity information (`rst` is conventionally
        # active-high, but `instr_reg`'s prose says "if the reset (rst) signal is low"), and an
        # in-band reset is invisible to `Module.reset`, so there is nothing left to infer from.
        #
        # But both sides are driven by the SAME stimulus, so the polarity cannot bias the
        # comparison -- it only decides whether anything interesting happens.  So try the other
        # one and keep whichever run actually exercised the design.  The polarity used is
        # reported, because a run that needed the flip is evidence about the design's reading.
        polarity = "declared" if active_low is not None else "auto"
        vectors, hw, lean = _drive(simlib, inputs, outputs, cycles, active_low, clock, reset,
                                   verilog, top, lean_key, nvec)
        if _is_vacuous(hw):
            alt = (not active_low) if active_low is not None else True
            v2, hw2, lean2 = _drive(simlib, inputs, outputs, cycles, alt, clock, reset,
                                    verilog, top, lean_key, nvec)
            if not _is_vacuous(hw2):
                vectors, hw, lean = v2, hw2, lean2
                polarity = f"flipped (active_low={alt})"
    else:
        vectors = simlib.gen_vectors(inputs)
        with tempfile.TemporaryDirectory() as wd:
            hw = simlib.simulate_comb_verilog(verilog, top, inputs, outputs, vectors, wd)
        lean = simlib.lean_sim(lean_key, inputs, vectors, nvec=nvec)

    summary = _summarize(vectors, hw, lean, outputs, top=top, seq=seq,
                         strict="--strict-observations" in argv, polarity=polarity)
    print(json.dumps(summary))
    return 0 if summary["status"] == "pass" else 1


def _summarize(vectors, hw, lean, outputs, *, top, seq, strict=False, polarity=None):
    """Assess every requested row before classifying observed behavior.

    A prefix comparison is diagnostic only: unequal trace lengths always fail. Strict mode
    additionally requires every declared output in every row and no skipped unknown values.
    Neither identical constants nor two empirical passes are a full equivalence theorem.
    """
    n = min(len(hw), len(lean), len(vectors))
    names = {name for name, _ in outputs}
    mism = []
    compared = 0
    skipped = 0
    malformed = []
    for i in range(n):
        if hw[i] is None or lean[i] is None:
            skipped += 1
            continue
        if (not isinstance(hw[i], dict) or not isinstance(lean[i], dict)
                or set(hw[i]) != names or set(lean[i]) != names):
            malformed.append(i)
        compared += 1
        if hw[i] != lean[i]:
            mism.append({"vector": vectors[i], "lean": lean[i], "verilog": hw[i]})

    known = [sample for sample in hw[:n] if sample is not None]
    constant_trace = bool(known) and len({repr(sample) for sample in known}) == 1
    lengths_match = len(hw) == len(lean) == len(vectors)
    summary = {
        "module": top, "kind": "seq" if seq else "comb",
        "vectors": len(vectors), "compared": compared, "skipped_xz": skipped,
        "sample_counts": {"requested": len(vectors), "verilog": len(hw), "lean": len(lean)},
        "mismatches": len(mism), "constant_trace": constant_trace,
        "strict_observations": strict,
        "complete_observation_coverage": bool(names) and bool(vectors) and lengths_match
            and compared == len(vectors) and not skipped and not malformed,
        "status": "pass",
    }
    if polarity:
        summary["reset_polarity"] = polarity
    if mism:
        summary["first_mismatch"] = mism[0]
    # Coverage errors take precedence over the sequential stimulus heuristic: a constant
    # prefix must never conceal missing rows, unknown samples, or a real disagreement.
    if not vectors or not names or compared == 0:
        summary.update(status="fail", err_class="no_comparisons",
                       error="no comparable samples, no requested vectors, or no observable outputs")
    elif not lengths_match:
        summary.update(status="fail", err_class="sample_count_mismatch",
                       error=f"unequal simulation lengths: verilog {len(hw)}/{len(vectors)} samples, "
                             f"lean {len(lean)}/{len(vectors)}")
    elif strict and skipped:
        summary.update(status="fail", err_class="unknown_observations",
                       error=f"strict observations forbid skipped x/z samples: {skipped}/{len(vectors)}")
    elif strict and malformed:
        summary.update(status="fail", err_class="output_coverage",
                       error=f"declared output coverage missing or malformed at sample {malformed[0]}")
    elif mism:
        summary.update(status="fail", err_class="mismatch")
    elif skipped > n // 2:
        summary.update(status="fail", err_class="unknown_observations",
                       error=f"majority of samples unknown (x/z): {skipped}/{n}")
    elif seq and constant_trace:
        summary.update(status="vacuous", err_class="vacuous",
                       error="sequential outputs remained constant; the stimulus may not have exercised "
                             "state transitions after reset (both reset polarities were tried)")
    return summary


if __name__ == "__main__":
    if len(sys.argv) < 3:
        print(__doc__, file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1:]))
