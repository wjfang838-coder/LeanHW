# MUX: a fresh two-stage end-to-end run

This executable smoke profile starts with the clarified VerilogEval `Prob022_mux2to1`
NL specification. It generates a new relational LeanSpec and new Verilog, imports
that exact Verilog through Yosys, and asks the prover to close two fixed targets.
It does not load a historical implementation or proof.

From the repository root, with the Lean/Yosys tools and an authorized agent backend:

```bash
source env.sh
export LEANSILICON_AGENT_BACKEND=codex
lake build
python3 -u -m leanrtl.e2e_mux --case mux_fresh
```

Choose a new case name for each run. Results go to ignored `data/part1/local/<case>/`
and `data/part2/local/<case>/`; source files and benchmarks stay separate. External
agent calls use the selected backend's credentials, which are not part of this repo.
`--reuse-stage1` resumes from an already converged Stage 1 case. Generated artifacts,
failures, compiler feedback and transcripts are retained.

The profile is deliberately explicit: three Boolean inputs in the order `(a,b,sel)`,
one Boolean output, stateless combinational behavior, and arbitrary finite traces.
The driver gives Stage 1 this representation contract, **not an output function**.
An incompatible representation or an unclosed proof fails the run. This profile is
not a generic adapter for stateful CPU, memory, arbitrary port widths, or X/Z timing.

## What is checked

1. Stage 1 extracts clauses with exact Unicode string spans, formalizes `admits`,
   runs diagnosis/property/witness checks, and performs resolution/revision and
   convergence. A clarified MUX needs no designer answer when there is no open
   choice or hole; the driver must not report a simulated answer as human input.
2. `FrozenSpec.lean` computes its output by selecting a Boolean observation admitted
   by the **actual frozen Stage 1 relation** on a singleton input trace. There is no
   separately authored mux reference function between the stages.
3. `HandoffContract.Exact` requires, for **all** finite Boolean traces `xs` and `ys`,

   ```text
   admits decidedSpec {steps := xs} {steps := ys} = true
     ↔ ys = xs.map selected
   ```

   This excludes both an always-true relation and an empty relation. It also checks
   empty traces and arbitrary lengths beyond the finite diagnostic universe. A
   fallback in the executable selector cannot pass if it selects forbidden behavior.
4. The implementation author writes `candidate.v`. `v2lean.import_refinement`
   creates `Imported.lean` from that exact RTL and records source/importer hashes.
   Physical port names, widths and order are checked by the frozen contract.
5. The prover supplies a term of the unchanged target

   ```lean
   FrozenRefinement.Refines FrozenContract.spec
     (FrozenContract.model V2LeanImported.impl)
   ```

   This quantifies over every initial oracle, every sequence of implementation
   choices and every finite input trace. Nat inputs are normalized to their physical
   one-bit values. The specification renders every output as concrete bits, so the
   refinement target enforces equality of the complete output interface. Even a
   state relation `True` must discharge the universal output obligation.
6. The checker rebuilds the certificate in a fresh source-only workspace, compiles
   both fixed targets, and audits their axiom dependencies. The MUX acceptance path
   uses kernel checking and standard Lean axioms, not `sorry` or `native_decide`.
7. Negative controls import an incorrect constant-zero RTL and substitute a trivial
   handoff proof. Both must fail for proof reasons; an infrastructure failure does
   not count as a successful negative control.

`end-to-end.json` is written only after all these gates pass. The cold certificate
includes a `replay.py` entry point and hashes for both its sources and replay tools.
`Partial.lean`, `DecidedSpec.lean`, the fixed handoff target, the original RTL and
its import report are included in the source manifest.

The mathematical guarantee begins at the frozen Lean relation. Translating NL into
that relation remains the reviewed formalization boundary. The Verilog frontend
and supported RTLIL importer remain part of the translation trust base; this run
is not a theorem about all SystemVerilog or analog propagation delay.

## Where the implementation lives

- `leanrtl/e2e_mux.py`: orchestration, isolated agent sessions, source binding and
  negative controls.
- `stage1/leanspec/lean/LeanSpec/Handoff.lean`: finite relational selection and its
  generic soundness/exactness lemmas.
- `FrozenSpec.lean` and `HandoffContract.lean` here: deterministic profile templates.
- `refinement/refinement_checks.py`: fixed-target checking, optional relational
  handoff gate, source-only replay and axiom audit.

The experiment outputs are generated into `data/`, rather than shipped as method
source or benchmark results.
