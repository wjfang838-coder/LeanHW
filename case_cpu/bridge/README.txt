LeanRTL -> LeanSpec cycle -> transaction ISA
==========================================

Run from the repository root:
    python3 case_cpu/scripts/bridge.py

This command reimports rtl/cpu.sv through Yosys and v2lean.symbolic, requires
an exact text match with ImportedData.lean, regenerates the shallow functions
and proof equations, compiles all modules, and prints the final theorem types
and axiom dependencies. Evidence is written to a new evidence/bridge/<time>/
directory; evidence/bridge-latest.json is updated only after a successful run.
The original rtl/cpu.sv, lean/ISA.lean and lean/Pipeline.lean are unchanged.

Actual source binding
---------------------
The frontend uses proc, flatten, memory_map -keepdc, pmuxtree, opt -nodffe
-nosdff, wreduce, and a final opt. It does not bit-blast arithmetic. The imported
module has 341 combinational nodes and 19 groups of state registers (1419 bits).
Yosys's don't-care and undefined-division outputs become five arbitrary choice
ports: 82 packed bits and four 32-bit values. Every theorem quantifies over the
entire choice environment, rather than choosing constants for those ports.
Reset is an in-band synchronous input, not an extra assumed initial state.

Lower-level proof
-----------------
ImportedData: actual LeanRTL AST, taken verbatim from the frontend output.
ImportCertificate: width/shape checks; positive-edge registers, no latches or
                   implicit initialized state.
Circuit/Shallow: shallow functions for the actual AST, with every node equation
                 checked and a generic topological evaluator correspondence.
WordMath/StorageCircuit: packed register file, write masking and reset, signed
                         division/remainder, and signed/unsigned high products.
DecodeSpec/DecoderTable/DecoderCircuit/DecodeFields: independent RTL decoder,
                    frozen Option-valued ISA decoder, immediate and register fields.
ALUCircuit: all 29 actual RTL operations equal the frozen ISA calculate function.
ControlCircuit/Forwarding/DispatchCircuit/AcceptCircuit: each procedural phase
                    agrees with a register-shaped semantic state and five stalls.
NetlistStep: core.step updates all 19 state groups exactly as the actual netlist.
RawCPU: this register-shaped state projects to the frozen Pipeline.cycle model.
SourceRefinement: compose the real netlist step, phase proofs, projection and
                  the already proved cycle-to-ISA refinement.

Final statements (all universal over finite traces, with no cycle bound)
-----------------------------------------------------------------------
rtl_step_refines: imported core.step -> rawCycle; Legal requires only that live
                 instruction slots contain supported encodings. This invariant
                 is established by reset and preserved for every subsequent input.
rtl_cycle_refinement: arbitrary pre-reset state + one reset edge + arbitrary
                      subsequent inputs -> the frozen cycle model.
rtl_isa_refinement: the above states' complete architecture equals ISA reference;
                    subsequent resets restart the ISA state.

Physical interface and conservation
-----------------------------------
Events.outputPort reads the real core.outputs?eval result. rtlReference consumes
physical retire_valid and retire_insn ports. rtl_isa_physical_events proves the
resulting architectural reference equality. Physical ready/valid acceptance and
retirement events match the cycle spec. rtl_conservation proves retired plus
pending equals initially pending plus accepted within a no-reset epoch.
rtl_drained_refinement executes exactly all physically accepted instructions once
empty; it cannot hide a dropped instruction by selecting only retirements.
PacketPC proves correct stored instruction PCs by induction; retirement_pc and
retirement_value connect the corresponding output ports to architecture/ISA.
port_debug and port_arch_pc connect the actual architectural observation ports.

Trust boundary and limits
-------------------------
There is no sorry/admit, no behavioral axiom, no assumed one-step equivalence,
no fixed seed/program/choice assignment, and no bounded simulation in the proof.
However, this is explicitly NOT a native-axiom-free proof:
* SystemVerilog -> Yosys RTLIL -> symbolic importer is a frontend trust boundary.
  Exact regeneration binds the proved AST to the recorded source and tool version;
  Lean does not prove the SystemVerilog frontend correct.
* bv_decide uses native LRAT checking for finite combinational equalities.
* native_decide evaluates the finite topology and complete decoder table; import
  width/check metadata have additional native finite checks.
* The final Audit.log lists every standard and native certificate axiom. The
  runner rejects sorryAx. The old upper-level proof remains standard-axiom-only.

Arbitrary permanent stalls are allowed. These are safety/conservation theorems,
not liveness/fairness proofs. No elapsed proof replay time measures development
cost. These Lean results do not change the earlier ABC PDR result: full PDR was
inconclusive at its 60-second budget, while sanity and order were proved.
