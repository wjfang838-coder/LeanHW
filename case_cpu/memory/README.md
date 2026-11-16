# Native-memory CPU case (method 2)

Method walkthrough: the [self-contained HTML case study](method.html) follows ADD from ISA to RTL equivalence. It compares actual LeanSpec, LeanRTL, and proof code, developing ALU, decode, forwarding, packet, retirement, and trace proofs, with memory as an extension. Appendices A–E include complete NL specification, Verilog, LeanSpec, LeanRTL, proof sources, and shared Lean dependencies for offline reading.

**Both refinement levels are closed: actual RTL / native RAM → cycle LeanSpec → transaction ISA.** Unified replay is recorded in `evidence/replay-latest.json`; source binding, tests, and PDR results are in `evidence/latest.json`. The original case without memory remains in the parent directory.

| Component | Implementation |
|---|---|
| RTL | `rtl/cpu.sv`, 999 lines, generated deterministically by `scripts/build_rtl.py` |
| Pipeline | IF / ID / EX / MEM / WB; five independent stalls; WB/MEM forwarding |
| ISA | 29 RV32 arithmetic instructions + LB/LH/LW/LBU/LHU/SB/SH/SW/FENCE, totaling 38 |
| Data RAM | 256 × 32 bits, 1 KiB; three asynchronous read ports and one synchronous write port |
| Memory access | Little endian; signed/unsigned loads; masked byte/halfword/word stores |
| Faults | Four load/store alignment/range faults; precise halt and younger-instruction flush; reset preserves RAM |
| Latency | MUL: 3 EX cycles; DIV/REM: 34; MEM delay 0..15, sampled on entry to MEM |
| Native import | 730 word nodes, 27 register groups; 2,044 scalar bits + 8,192 RAM bits |

Input is a ready/valid instruction stream. This RV32 subset excludes instruction RAM, branches/jumps, CSR, and cache. Multiplication/division use a combinational ALU; countdowns represent completion latency. Loads/stores/FENCE serialize the backend; arithmetic can overlap, and IF/ID can buffer younger instructions. Twelve performance counters are diagnostic state, excluded from the ISA architectural projection and checked by cycle-by-cycle simulation.

## Closed proofs

| Connection / property | Lean entry point |
|---|---|
| Actual imported circuit preserves the register-form model relation each cycle | `MemCircuitRefinement.circuit_cycle_refinement` |
| Register-form model → cycle LeanSpec | `MemRawBridge.project_cycle` |
| Cycle LeanSpec → transaction ISA, including arbitrary subsequent resets | `MemRefinement.reset_refinement` |
| Actual RF, PC, all RAM words, and fault → ISA | `MemCircuitRefinement.rtl_isa_refinement` |
| Full trace with ISA driven by physical `retire_valid/retire_insn` | `MemPortRefinement.rtl_to_transaction_isa` |
| Physical input handshake / retirement → model events | `MemAcceptRefinement.accepted_port_refinement`, `MemPortRefinement.retired_port_refinement` |
| Physical drain yields ISA execution of the actual accepted program | `MemTraceRefinement.rtl_accepted_program_refinement` |
| Reachable retirement PC, RD, and result come from the current ISA effect | `MemOutputRefinement.reachable_retirement_payload` |
| Store output byte lanes agree with the ISA store effect | `MemOutputRefinement.retirement_store_lanes` |
| FIFO conservation with explicit reset/trap abort accounting | `MemEvents.trace_conservation` |

The relation covers instruction, operation, destination, PC, value, fault, and memory address/data for valid packets. Decoder, all 29 ALU operations, forwarding, immediates, memory faults, countdowns, and five-stage control connect to the actual AST. Irrelevant payloads of invalid packets are unconstrained. Initial RAM, reset seeds, inputs, stalls, delays, and undefined-value choices are universally quantified. Neither full one-step equivalence nor internal invariants are assumed.

Trace safety allows permanent stalls. The accepted-program theorem requires no subsequent reset and a physically drained pipeline at the end. Faults may flush younger instructions; ISA steps after halt are identities. There is no fairness assumption or claim that every environment eventually drains the pipeline.

## Specification, diagnosis, and correction

`spec/original.txt` contains deliberately ambiguous, incomplete, and conflicting requirements. `spec/decisions.json` records revision decisions; `spec/revised.txt` is the implementation contract. `MemoryDiagnosis.lean` uses LeanSpec queries/admitted sets for eight local scenarios and proves determinacy of the revised finite projection. This is not an NL→Lean equivalence proof.

Closing the circuit bridge exposed an actual interface bug: a faulting load leaked its decoded RD, although R10 requires `retire_rd = 0` on traps. RTL output gating was corrected, along with the same mistake in the independent Python reference. `MemPortRefinement.trap_rd_zero` proves the repaired property. `evidence/correction.json` records the original expression, repair, and reproducible witness.

Five private RTL mutants cover the original trap-RD bug, zero-extending LB, SB overwriting a whole word, stores during WB stall, and resampling MEM delay. The same independent reference detects all five. Mutation detection uses differential simulation; the corrected complete CPU is validated by replaying Lean refinement proofs.

## Method 2 and trust boundaries

`method/stage2/framework/LeanRTL/Core/NativeMemory.lean` represents state as a register environment plus memory functions: asynchronous reads bind to the old array, and register D inputs and array writes are computed on the same edge. `method/stage2/v2lean/native_memory.py` preserves actual `$mem_v2` nodes. In the complete `Program`, RAM read data comes from the actual array, not an environment oracle.

Lean import uses `proc -norom; memory_collect`, without `memory_map`. Supported RAMs are full-depth, with arbitrary initial contents, asynchronous read ports without enable/reset, and at most one direct common positive-edge write port per memory. Read addresses depend on old registers and physical inputs. `scripts/check_import.py` checks accepted cases and eight rejection boundaries. This does not extend the old register-only compiler theorem or establish a general native-RAM SV compiler-correctness theorem.

The trust base includes SystemVerilog/Yosys lowering, the Python importer, the Lean kernel and standard axioms, native LRAT checking for `bv_decide`, and native evaluation of checker/topology facts. Dependencies are listed in `evidence/Audit.log`; there is no `sorryAx` or unproved circuit-bridge assumption. Simulation and PDR are not premises of Lean theorems.

## Validation evidence

- Independent byte-addressed Python reference versus RTL: 14,381 edges, 583 retirements, 38 instructions, 32 stall masks, and four fault classes. Retirement/debug/occupancy/counters are checked every cycle; all RAM is scanned after drain.
- All five mutants are detected against the corrected baseline, including a concrete counterexample for the original trap-RD bug.
- Yosys-bundled ABC `pdr`: full timed out at 60 s; sanity timed out at 30 s. Full AIG: 21,984 latches, 464,712 ANDs, 74 bad outputs. Sanity: 12,550 latches, 221,766 ANDs, 58 bad outputs. Both entered PDR and produced neither a proof nor a counterexample.
- The PDR reference has its own RF/RAM and accepted FIFO. Only first-reset and initial-RAM correspondence constraints are assumed, not pipeline invariants or fairness. `fold; strash; orpos; pdr` checks all bad outputs together. Only this AIG baseline expands RAM; Lean proofs retain native RAM.

A single timeout establishes neither inherent PDR complexity nor a fair speed comparison with Lean.

## Reproduction

From the repository root:

```bash
python3 case_cpu/memory/scripts/replay.py
python3 case_cpu/memory/scripts/simulate.py
python3 case_cpu/memory/scripts/mutants.py
python3 case_cpu/memory/scripts/pdr.py --task full --seconds 60 --synthesis-seconds 240
python3 case_cpu/memory/scripts/pdr.py --task sanity --seconds 30 --synthesis-seconds 240
python3 case_cpu/memory/scripts/report.py
```

Default replay resynthesizes the actual RTL, checks the AST, and recompiles every proof module. Fresh checking of the 730-node shallow certificate took about 922 s in the recorded run; `evidence/shallow-latest.json` binds its source, object, and log hashes. The recorded unified replay used `--reuse-shallow`, strictly checking those hashes before reusing the just-completed certificate and recompiling every other module from source. Reuse is explicitly recorded. Incremental replay time is not the time for a complete fresh proof.

`report.py` publishes `closed_rtl_to_isa: true` only when all top-level proof replays pass, the axiom audit finds no `sorryAx`, and RTL/AST/simulation/mutant/PDR hashes agree. Earlier failure logs are development records; current conclusions are determined by `latest.json` and its corresponding replay/task records.
