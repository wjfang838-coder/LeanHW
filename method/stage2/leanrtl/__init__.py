#!/usr/bin/env python3
"""leanRTL — from a prose specification to a proof-carrying implementation, and to Verilog.

Part two of leanSilicon, and it runs alone.  Nothing here imports `leanspec`, reads a case
directory, or knows that a specification half exists.  Its input is **one prose specification**
and an interface contract; that prose may be a benchmark's original text or the decided text
part one produced, and this half cannot tell which — deliberately, because if it could, "the
decided prose is better" would be a claim about a code path rather than about the prose.

The method is: two authors, serial, with a machine-enforced freeze between them.

    contract   the module name, its ports and their widths — derived, not asked for
    spec       S writes an executable `BitVec` specification.  Frozen: hashed, made read-only,
               and added to the confinement hook's READONLY list.
    impl       D writes the implementation against the frozen specification
    simdiff    a cheap deterministic self-check before anything expensive: 160 cycles of
               pseudo-random stimulus through both.  agree / diverge / ungateable / vacuous.
    proof      D proves the implementation refines the specification.  Correction may change
               the implementation and never the specification; a changed implementation re-runs
               simdiff.
    emit       RTLIL → Verilog through yosys, with the interface gate in the loop
    certify    the gates in `verify`, plus proof mutation and the scope audit

D may not edit the specification.  If D believes it is wrong, D writes `challenge.json` — a
quote, a reason and a counterexample trace — and stops; the specification goes back to S, its
version advances, and D's work is discarded.  There is no adjudicator: with serial authoring
there is no second reading to adjudicate between.

  * `stage`           build a workspace from a profile, and stamp what it holds
  * `two_author`      the S → freeze → D state machine and its two role cards
  * `pipeline`        the eight steps, on the shared step-document contract
  * `verify`          the certification gates
  * `proof_mutation`  whether the proofs actually constrain the design
  * `iface_conform`   after the fact: does the emitted module match the prose's interface
  * `launch`          the orchestrator
"""
