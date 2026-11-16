# Native-array execution profile

`NativeMemory.lean` adds a separate whole-design semantics for register logic with
native memories. It does not change the meaning or memory exclusion of the legacy
`Module.step` / register-only compiler correctness theorem.

A `Program` combines a checked pure logic module, unique named full-depth arrays,
old-state asynchronous read descriptors, and at most one masked write per array.
`Program.comb` binds read ports from the old arrays before evaluating the wire DAG.
`Program.step` calculates all register inputs and memory writes on the same edge.
RAM read data is therefore not a free environmental input to the complete program.
Reads are read-first. Reset is ordinary explicit logic in the imported CPU; there
is no implicit array reset or initial zero assumption.

`Program.checked` is the executable profile gate. Read addresses in this first
profile may use registers and physical inputs, but not synthetic read names or
intermediate combinational wires. Registers and writes share a positive edge.
Distinct memories have distinct names; write masks have one bit per data bit.
`read_write_same`, `read_write_other` and `write_disabled` have ordinary Lean proofs.

The matching importer is `v2lean/native_memory.py`. Unsupported native RAM modes
are rejected. This profile currently supplies execution/import semantics; a new
generic native-memory SystemVerilog emission correctness theorem is not provided.
The memory CPU demonstration has a complete circuit-to-cycle-to-ISA refinement
for its declared RV32 subset. The proof, physical handshake/retirement connection,
and source-bound replay evidence are documented in `case_cpu/memory/README.md`.
