---
id: internal-signal-names
layer: process
applies_to: designs scored by cocotb (probes internal regs)
lib: docs/instructions/CORE.md §2.1
maturity: promoted
---
# Match internal signal names to the spec

cocotb/CVDP testbenches probe INTERNAL registers by name (`dut.shift_reg`, `dut.clock`), not just ports. Name every register with the spec's exact word: `shift_reg` not `sr`, `clock` not `clk` when the spec says `clock`. A name mismatch is a functional failure even if the logic is bit-perfect — each of `sr→shift_reg` and `clk→clock` cost a run. Read the spec for the internal field names as carefully as for the port list.
