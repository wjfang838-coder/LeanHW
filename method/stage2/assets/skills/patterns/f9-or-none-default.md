---
id: f9-or-none-default
layer: pattern
applies_to: emission of self-authored netlists under cocotb
principle: proof-carrying-reaches-artifact
tactics: []
lib: scripts/f9_emit.py (f9_or_none)
example: axis_to_uart (LeanRTL/Designs/CvdpAgentic/AxisToUartTx.lean, UartRxToAxis.lean)
maturity: promoted
strike: 3
---
# Default to `f9_or_none`, not structural write_verilog

`scripts/f9_emit.f9_or_none` emits procedural next-state SV (`leanrtl vverilog`) and gates it behind a Yosys `equiv_induct` miter against the verified netlist, returning `None` if unsupported. Prefer it over Yosys `write_verilog`: a structural `$mux`-tree netlist permanently **absorbs an uninitialized cocotb input's X** into FSM state registers (tready/TX go X and stay X), whereas behavioural if/else takes the `else` branch on X and survives (F11 four-state hazard, wave-Y2 three-strike; UART designs were 0/1 structural, 1/1 after F9). Gotcha: pure stateless datapaths (no feedback, sync reset) are safe structural — `cic` passed single-shot; the X-absorption bites *stateful* structural netlists specifically.

## Worked example

```python
def f9_or_none(leanrtl, key, top, gold_json, wd):
    """Return (path_to_F9_verilog | None, detail).  None => caller falls back to write_verilog."""
    …
    v = _sh([leanrtl, "vverilog", key])          # procedural next-state SV
    …
    y = _sh(["yosys", ys])                        # equiv_induct miter vs verified netlist
    if "Equivalence successfully proven!" in blob:
        return gate, "miter_proven"
    return None, "miter_fail:" + …
```
> Source: scripts/f9_emit.py:46
