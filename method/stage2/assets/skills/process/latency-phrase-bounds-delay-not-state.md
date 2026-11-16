---
id: latency-phrase-bounds-delay-not-state
layer: process
applies_to: any spec whose clarification names a register-stage count or forbids "extra buffering"
lib: —
example: ChipBench Prob010_integer_multiple_data_bit_width_conversion_8to16
maturity: sediment
---
# "One register stage / no extra buffering" bounds the DELAY, not the STATE

A clarification like

> *…asserted on the clock edge immediately following receipt of the second input (exactly one
> register stage / one cycle of latency), with no additional buffering or pipeline stage.*

is a statement about **when** the output appears — one cycle after the last input, not two. It is
**not** a budget on how many registers the design may contain. A holding register that captures an
earlier input and is read combinationally on the deciding cycle adds **zero** latency; it is not a
"pipeline stage" and not "additional buffering". Deleting it does not satisfy the clarification —
it changes a different, unrelated thing.

## What deleting it costs

The failure mode is specific: with the holding register gone, the only place to park a partial
result is the OUTPUT register itself, so the output starts changing on cycles where the spec says
it holds. ChipBench Prob010 accumulates two 8-bit inputs into one 16-bit output. The reference
keeps `data_r`, leaves `data_out` untouched on the first input, and writes `{data_r, data_in}` on
the second. An author who read "no additional buffering" as forbidding `data_r` wrote the high half
straight into `data_out` on the first input and the low half on the second. **The final value is
identical every time** — and the testbench samples every cycle, so it caught `data_out` moving one
cycle early: **70 of 141 samples**, with `valid_out` clean throughout. Restoring `data_r`: 0/141.

Note what made this hard to see. The design was internally consistent, the whole-trace theorem was
proved, all proof gates were green, and the two readings **agree on every cycle the output is
valid**. Only the hold-cycles separate them, and only the spec sentence *"If only one data input is
received, the module waits for the second input before producing any output"* decides it.

## How to apply

1. Read a latency phrase as a constraint on the **output's timing** and nothing else. Count the
   edges between the last input and the output; that is the whole claim.
2. Before removing an internal register to satisfy such a phrase, check the latency **with** it. If
   the register is read combinationally on the deciding cycle, removing it changes no latency and
   the phrase never asked for it.
3. Ask what the output does on the cycles the spec does *not* describe. A spec that says "waits
   for the second input before producing any output", or that names a hold/idle behaviour, is
   constraining the output on hold cycles too — and a testbench that samples every cycle will
   check exactly those.

See also `delay-off-by-one` (the same counting done wrong in the other direction).
