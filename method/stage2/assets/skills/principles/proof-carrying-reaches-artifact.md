---
id: proof-carrying-reaches-artifact
layer: principle
applies_to: every emitted Verilog deliverable
lib: benchmarks/cvdp/param_check.py; scripts/f9_emit.py (equiv_induct miter)
maturity: principle
---
# Correctness must reach the emitted artifact

A theorem about a Lean `Module` is worthless if the Verilog that ships is a different circuit. Two — and only two — bridges are allowed to close that gap: (a) the Verilog is **produced by a proven transform** (`leanrtl extract` / `pverilog` off the machine-checked compiler), or (b) the Verilog is **verified against the proven reference** by a Yosys miter (`equiv_induct` in `f9_emit.f9_or_none`; per-N `equiv_induct` in `param_check.py`). A hand-written template is trustworthy only once a miter anchors it to the verified netlist. Never let a hand-edit slip in downstream of the last proof.
