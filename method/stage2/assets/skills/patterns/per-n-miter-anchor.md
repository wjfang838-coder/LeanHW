---
id: per-n-miter-anchor
layer: pattern
applies_to: parametric (F2) / procedural (F9) emission
principle: proof-carrying-reaches-artifact
tactics: []
lib: benchmarks/cvdp/param_check.py (Yosys equiv_induct); scripts/f9_emit.py
example: cascaded_adder / signed_comparator (LeanRTL/Designs/Param/)
maturity: promoted
---
# Per-N miter anchor

A ∀N Lean theorem proves the family; a Yosys miter proves the *emitted SystemVerilog* is that family. `param_check.py` instantiates the parametric emission at concrete N and runs `equiv_induct` against `compile(impl N)` (the verified-compiler netlist) — so `pverilog` output is anchored back to verified RTLIL at each checked N. `f9_emit.f9_or_none` does the same for procedural next-state emission. This is the artifact-reaching half of a parametric proof (see proof-carrying-reaches-artifact). Gotcha: the miter checks specific N values, not ∀N structurally — pick N that exercise every generate-branch (0/1/boundary), and the Lean ∀N theorem carries the rest.

## Worked example

```
MITER = """
read_json {gold}                 # verified-compiler netlist (gold)
…
read_verilog -sv {gate}          # emitted parametric SystemVerilog
chparam -set {param} {n} {top}   # instantiate the family at concrete N
…
equiv_make gold gate equiv
async2sync
equiv_simple
equiv_induct
equiv_status -assert
"""
```
> Source: benchmarks/cvdp/param_check.py:32
