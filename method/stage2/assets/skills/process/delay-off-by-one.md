---
id: delay-off-by-one
layer: process
applies_to: registered outputs and done pulses
lib: docs/instructions/CORE.md §2.4
maturity: promoted
---
# Pin the exact latency (delay off-by-one)

A registered output reads one cycle LATE in cocotb (updated only after the posedge sample). Pin the exact latency: a `done` pulse fires on the LAST working cycle (same cycle as the result), not the next one — sorting and gcd both lost runs to an extra cycle. When unsure how many cycles the checker waits, count the `RisingEdge`s in the golden testbench. Registered-vs-combinational output is a one-word difference in the spec ("asserted when…" vs "…on the next cycle", see Mealy/Moore) that changes the latency by one; get it exact or the fixed-latency-delay-law corollary is false.
