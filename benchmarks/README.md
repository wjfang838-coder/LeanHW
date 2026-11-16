# Clarified benchmarks

329 cases: VerilogEval 156, RTLLM 50, CVDP 78, and ChipBench 45.

`<suite>/clarified/<design>/spec.clarified.txt` is the final natural-language specification in this package; `interface.json` identifies the public module interface. These files come from the complete corrected/clarified snapshot dated 2026-10-05. All 329 specifications were checked for byte-for-byte agreement across that date's three model-run directories. `corrections.json` retains input revision notes, not model scores.

The datasets, CVDP harnesses, testbenches, reference RTL, and test data are evaluation inputs, not model outputs. CVDP's `dataset` and `harness` are JSONL files. The official data usually has no reference RTL; separately constructed answer supplements remain in their original directories.

For generation or Stage 1 analysis, explicitly read files under `clarified/`. The adapters retain the original benchmark reading/evaluation interfaces; their `stage()` methods do not automatically substitute clarified NL. Evaluation references and private testbenches must not be supplied to the author as specification inputs.

The old frozen LeanSpec set from `data_v2lean/part1` is not included: it has only 328 complete inputs and predates these clarified revisions. It must not be claimed to correspond to the final NL here. The Stage 1 framework can formalize these NL specifications afresh.

Runs, scores, model candidates, waveforms, simulation executables, and build caches are excluded. Original sources and hashes are recorded in the [method migration manifest](../method/MIGRATION.json).
