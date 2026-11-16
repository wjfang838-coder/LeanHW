---
id: no-peek-boundary
layer: process
applies_to: single-shot (SS) generation runs
lib: "—"
maturity: promoted
---
# The no-peek boundary

Single-shot generation must not read the testbench, the reference/golden Verilog, any `_ref` file, the harness internals, or a hidden `.jsonl` — reading them voids the measurement. Author from the spec + port interface only. (The subagent `leanrtl-module-author` is explicitly forbidden the reference RTL and the hand-written dataset impls for this reason.) Debugging is allowed against your OWN DUT instrumentation (`$monitor`/`$display` in a kept workspace), not against the hidden checker's source. If you cannot tell whether a file is inside the boundary, treat it as inside.
