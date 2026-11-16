---
id: spec-is-the-oracle
layer: principle
applies_to: what "correct" means in the benchmark
lib: LeanRTL/Core/Refine.lean (Refines / Alpha); docs/instructions/CORE.md §5
maturity: principle
---
# The spec is the oracle, not the golden RTL

Matching a golden Verilog reference is not correctness: the golden may itself be buggy on inputs its testbench never exercises, and a dev testbench can have its own edge-race artifacts. The only oracle that closes both the "is the impl right" gap and the "is the golden right" gap is a **proof against a formal spec** — a differential experiment where impl and spec are two independent layers bridged by a proven refinement (`α` + `Refines`). When the dev-TB, the golden RTL, and the spec disagree, trust the spec and the hidden scorer, not the artifact you were handed (CORE §5, dev-tb-not-oracle).
