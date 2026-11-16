# LeanRTL benchmark authoring — CORE (single source of truth)

> Initial version: 2026-07-06, after v0.9. **Updated 2026-07-31:** section 3 adds two
> proof-acceleration resources consolidated in v1.3 M47 (`Lib/StepSimp` and
> `Lib/BvBridge`) and the 61-entry `docs/skills/` collection. These were previously
> absent from the author's reading sequence (plan v1.4 M53 P1). All benchmark
> instructions (RTLLM / VerilogEval / CVDP, SS + ITER) read this document first,
> followed by their small benchmark-specific deltas. **This matrix is authoritative
> for capability questions.** Old skip lists and "framework unsupported" examples
> in other instructions are superseded. Update this single copy as capabilities evolve.

## 1. Capability matrix — use this table to decide expressibility

### 1.1 NOW EXPRESSIBLE — do not skip these previously unsupported features

| Capability | DSL form | Lowering | Proof coverage / notes |
|---|---|---|---|
| **Negedge registers** (F1) | `Reg.negedge := true` | `$dff` CLK_POLARITY=0 → `always @(negedge clk)` | Uniform negedge designs are covered by the whole-design theorem (`WholeDesign/Negedge.lean`, Stage 0). Mixed posedge/negedge designs use per-register proofs + cosimulation; `semanticCoverage` reports `.negedgeMix`. |
| **Level-sensitive latches** (F8) | `Module.latches : List Latch` | `$dlatch` | Per-latch law `Latch.den`; level-sensitive behavior is outside `Module.simulate`, and `semanticCoverage` reports `.latch`. **Wires, outputs, and register next-state expressions may refer to latch Q by name**, just like registers. The compiler preallocates Q nets using `seedLatchNets`. Do not declare another wire with the same name: `checkErrors` rejects duplicates. `bb cosim` necessarily fails on latch designs because its Lean side has no latch model; that is not a design bug. A posedge flip-flop is not a latch replacement: enable changes have different behavior. A negedge flip-flop is equivalent only under the `clk & Q` clock-gating pattern. |
| **Dynamic asynchronous load** (F6) | `Reg.asyncLoad := some (net, activeHi, expr)` | `$aldff` | Per-register `Reg.aldffDen` plus Stage-2 full-trace value theorem (`WholeDesign/AsyncLoad.lean`). Do not combine with asyncReset (section 1.3). `semanticCoverage` reports `.asyncLoad`. |
| **Asynchronous reset** (F4) | `Reg.asyncReset := some (net, activeHi, val)` **and** fold the same reset in-band into `next` (both are required; section 2.2) | `$adff`, with `ARST_POLARITY` from `activeHi` | The whole-design simulate theorem still applies (`Module.eraseArst_simulate` + `coveredModuloArst_moduleChecks`). When folded (`Module.arstFoldedb = true`), reset-active edges are covered without restricting the reset scope (`Reg.arstFolded_arstDen`); only between-edge response remains outside the cycle model. A declaration without folding restricts the theorem to reset-inactive intervals: use per-register `Reg.arstDen` and the Stage-2 value theorem, pattern `asyncreset-value-trace`. Supply the reset port itself and its polarity, not an inverted net. This authoring guide defaults to asynchronous reset when the specification does not distinguish synchronous/asynchronous behavior (section 2.2). `semanticCoverage` still reports `.asyncReset`; `coveredModuloArstb` enables the whole-design theorem, and `arstFoldedb` removes its reset-inactive restriction. |
| **Power-up initialization without reset** (F7) | `Reg.init` + `reset := none` | RTLIL `\init` attribute → `initial q = <v>` | Eliminates the first-edge-X failure class seen in VerilogEval Prob034/053/074/104. |
| **Multiple / gated / derived clocks** | `Reg.clockNet := some (expr : Expr 1)` | That register uses this clock net | Per-register characterization + cosimulation, outside whole-design simulate (section 1.3). `semanticCoverage` reports `.clockNet`. |
| **Addressed memory** | `Module.mems : List MemBlock` (clocked write + asynchronous reads) | One `$mem_v2` | Stage-1 shapes (module-clock writes + asynchronous reads) have a whole-design read-after-write theorem (`WholeDesign/Memory.lean`). Other shapes use per-access characterization + cosimulation; `semanticCoverage` reports `.memShape`. |
| **Module parameters / parameterized widths** (F2) | `ParamModule`: `impl : Nat → Module` + parameterized emitter (see `LeanRTL/Designs/Param/`) | `leanrtl pverilog <key>` emits parameterized SV; `leanrtl extract <key> --N k` extracts an instance | A ∀N Lean proof plus per-N Yosys miters binds pverilog to verified RTLIL (`benchmarks/cvdp/param_check.py`). Covered subclasses include width-uniform/affine, generate loops, memory depth, filo, signed MAC FIR, bit permutations, packed parameterized ports, and value-dependent generate. A testbench's `-P` parameter sweep is not automatically a framework gap: check the templates first. |
| **Sequential multi-module hierarchy** (F10) | `Parent` with combinational or sequential children | `compileParent` flattens it | `HierSeqCorrect.flattenParentSeq`. |
| **Multi-cycle end-to-end proofs** | `LeanRTL/Lib/MultiCycle` (`iterate_to_terminal`, LTL) | — | Example: `MultiCycle/GcdIter.lean`. |
| **Protocol refinement** | `Refine.Refines` / `RefinesInband` / `StutterRefines` + α | — | Examples: `LeanRTL/Designs/Protocol/` (AxiRegister, Wb2Ahb). Alpha-pattern catalog: `docs/skills/patterns/alpha-shape-catalog.md`. |
| **Procedural next-state emission** (F9, including F11) | No author action: the harness automatically uses `leanrtl vverilog` after a successful equivalence miter | Clocked always block with if/else | Automatically handles delta-cycle races and X-as-0 four-state issues; agents need no workaround. |

### 1.2 Genuine limits — only these justify skip / framework_gap

- **real / float types** for behavioral real-number arithmetic.
- **Tri-state z** buses.
- **SystemVerilog interfaces / structs / enums** as port types.
- **Both edges on the same FF (DDR)**. A combination of two opposite-polarity registers is supported (F1).
- **Metastability / genuinely asynchronous CDC behavior**, including synchronizer timing semantics.
- Declared out of scope: a free-running oscillator whose clock is itself an output (`clkgenerator`, not synthesizable), and positional instantiation with output-first port order (`LFSR`, user ruling).

### 1.3 Combination gaps — boundaries when supported features interact

> **Machine-checked classification (M32).** These boundaries between the language and
> reference semantics are not just prose conventions. `leanrtl check <name>` prints
> `Module.semanticCoverage`: `full` (the whole-design simulate theorem applies) or
> `per-register`, with a `CoverageReason` list. The theorem
> `semanticCoverage_full_moduleChecks` in `LeanRTL/Core/Coverage.lean` proves that
> full coverage and well-formed widths imply `moduleChecksb = true`, making the
> whole-design simulate theorems applicable directly. Each boundary below has a
> corresponding `CoverageReason`.

> **`asyncReset` is a special case.** `Module.step` / `Module.simulate` never read
> `Reg.asyncReset`; `Module.eraseArst_simulate` proves
> `m.simulate = m.eraseArst.simulate`. When asynchronous reset is the only construct
> outside the model (`Module.coveredModuloArstb`), the whole-design simulate theorem
> still applies over reset-inactive intervals. `coveredModuloArst_moduleChecks`
> derives `moduleChecksb m.eraseArst` from two `by decide` facts about `m` itself.
> Coverage still reports `.asyncReset`: between-edge reset behavior is outside the
> cycle model and is covered per register by `Reg.arstDen`. Do not change reset to
> synchronous merely to regain a theorem; that change is unnecessary and can break
> the testbench (sections 2.2 and 2.3).

- **`asyncReset` + `asyncLoad` on one register is forbidden.** The compiler's conflicting lowering would emit `$adff` and silently lose async-load behavior. Never combine these fields. The historical guard work is represented by `checkErrors` rejecting emission; `semanticCoverage` reports both `.asyncReset` and `.asyncLoad`.
- **Designs with `clockNet` or `mems` generally lack a whole-design simulate theorem.** Use per-register/per-access characterization + cosimulation. Exceptions are the Stage 0–2 classes in `WholeDesign/`: uniform negedge, module-clock writes with asynchronous memory reads, asyncLoad value theorems, and asyncReset value theorems over reset-inactive intervals. Coverage reports `.clockNet` / `.memShape` when whole-design simulate does not apply.
- **Two edges implemented as two opposite-polarity registers are supported** with per-register proofs. Same-FF DDR is a genuine limitation (section 1.2). Mixed posedge/negedge registers produce `.negedgeMix`; uniform negedge remains within the model.

## 2. Authoring lessons — observed failure modes

### 2.1 Internal signal names matter to cocotb

Cocotb/CVDP testbenches probe internal registers by name, such as `dut.shift_reg` and
`dut.clock`. Preserve the specification's names: do not abbreviate `shift_reg` to
`sr` or change `clock` to `clk`. A wrong name causes func_fail even when the logic is correct.

### 2.2 Reset family and asynchronous-reset convention (F5)

For a sequential design with a clock port, use `regs` and next-state `Expr`,
`clock := some "<clk>"`, and `reset := none`. Fold reset in-band into each register's
next state according to polarity:

- Active-low `rst_n` / `reset_n`: `.mux (.eq (.var "rst_n" 1) (.const 0)) <resetVal> <normal>`.
- Active-high `reset` / `rst`: `.mux (.eq (.var "reset" 1) (.const 1)) <resetVal> <normal>`.

**Asynchronous reset requires both in-band folding and the `asyncReset` declaration.**
In addition to the fold, add
`asyncReset := some ("<rstPort>", <activeHi>, <resetVal>)` to each register.
Use the reset port itself and its polarity: active-low `rst_n` is
`some ("rst_n", false, 0)`; active-high `rst` is `some ("rst", true, 0)`.
Port name, polarity, and reset value must match the in-band fold exactly.

The two parts serve distinct purposes:

- **In-band folding covers reset-active edges in the theorem.** The cycle model
  computes reset values on those edges. `Reg.arstFolded_arstDen` proves
  `arstDen e = eval next e`: the `$adff` denotation agrees with ordinary next state.
- **The `asyncReset` declaration provides the Verilog sensitivity list.** The emitter
  uses its polarity for `always @(posedge clk or negedge rst_n)` and `if (!rst_n)`.
  Without it, only `@(posedge clk)` remains, and a reset deasserted in the same time
  step can fail to take effect (section 2.3).

Folding alone can fail the testbench; declaring alone restricts the theorem to
reset-inactive intervals. Use both. `leanrtl check` distinguishes these cases:
when `Module.arstFoldedb` is true, it reports no reset-scope restriction; otherwise,
it identifies the missing fold.

**This guide defaults to asynchronous reset when the specification is silent.**
This was a frequent benchmark failure mode: prose often says only "reset is active
low" or lists `rst_n` without "asynchronous". Reading that as synchronous risks
mismatching reference RTL, which commonly uses
`always @(posedge clk or negedge rst_n)`. Testbenches often deassert reset in the
same time step as a clock edge (section 2.3), leaving a synchronous implementation
one cycle late or entirely X. Under ordinary stimulus that holds reset across at
least one edge, asynchronous and synchronous reset agree at sampled cycles; a
between-edge reset pulse distinguishes them.

**Choosing asynchronous reset need not sacrifice the cycle theorem if reset is also
folded in-band.** `Module.eraseArst_simulate` proves the equality with the synchronous
twin's simulation. The same whole-design theorem applies to `m`; folding includes
reset-active edges, leaving only between-edge response outside the cycle model.
`coveredModuloArst_moduleChecks` supplies M6's `moduleChecksb` from two `by decide`
facts. `.asyncReset` remains an honest coverage report because `Reg.arstDen` handles
between-edge behavior separately. Do not change reset to synchronous solely to
obtain the whole-design theorem.

Do not introduce an inverted net (`nrst = ~rst_n`) and declare an active-high reset.
That continuous assignment adds a delta delay between the port and flip-flop,
which can lose a race against a testbench deasserting reset at a clock edge and
shift the entire trace by one cycle. This single change has been observed to turn
an otherwise failing design into a passing one. Only when the specification
explicitly requires synchronous reset should the implementation stop at in-band
folding without `asyncReset`. A synchronous design whose testbench deasserts reset
at the first clock edge may never initialize its registers, leaving them X.

Widths live in types — a mismatch is a compile error.

### 2.3 X initialization and the first edge

F7 emits `initial q = <init>` from `Reg.init` even with `reset := none`, avoiding
uninitialized reset-free registers. A testbench may pulse reset before any clock
edge; synchronous reset cannot take effect then. If NL specifies asynchronous
reset, use `asyncReset` as described in section 2.2.

### 2.4 Latency and off-by-one conventions

A registered output is readable one cycle later from cocotb's perspective: it
updates after posedge sampling. The done-pulse convention is to assert it during
the final working cycle, alongside the result, not on the following cycle. If
uncertain, count the `RisingEdge` events awaited by the reference testbench.

### 2.5 Mealy vs Moore

Whether an output reads current inputs combinationally (Mealy) or is registered
(Moore) may depend on a single word in NL: "output is asserted when..." versus
"...on the next cycle". In SS mode, read carefully and choose conservatively.
In ITER mode, the testbench's sampling instant determines the required correction.

### 2.6 $readmemh and data files

Testbenches using `$readmemh` expect execution in the design directory. The harness
sets `cwd=design_dir`; the agent need not manage paths or copy data files.

### 2.7 Delta cycles and X propagation are handled automatically

The harness's procedural emitter handles continuous-netlist delta-cycle races with
cocotb VPI / blocking-assignment testbenches and the X-as-0 four-state behavior
(F9/F11), after an equivalence miter passes. Do not introduce manual workarounds
such as a single named wire, or classify these symptoms as framework_gap.

### 2.8 F9 protects only cones inlined into register next state: agentic sequential controllers must be wire-free

This rule was promoted after three observed failures in July 2026. F9's
`leanrtl vverilog` recomputes the register next-state cone using blocking temporaries
inside the clocked block and lowers decision muxes to if/else. Named `Wire` values
still become module-level continuous assignments. Referencing them in next state
can delay same-cycle inputs by a delta and miss a write, or turn floating z inputs
into X through continuous ternaries and corrupt storage. Both occurred in
`cache_controller`; the handwritten `door_lock` template has the same pattern.

In agentic sequential designs, use **`wires := []`**. Inline conditions and data
selection into register next-state and output expressions. A mux whose select may
be z/x must be in a decision position that lowers to if/else, not a continuous
ternary. For small storage (at most 32 entries) with an adversarial four-state
testbench, use named registers with a readSel chain rather than MemBlock: memories
disable F9 and `$mem` powers up X. To debug a hidden testbench, instrument your own
DUT with `$monitor` / `$display` and run the scoring harness once in the retained
workspace to inspect its stimulus timing.

## 3. Allowed libraries and verification

**Author-readable library files** that do not invalidate the measurement:

- `LeanRTL/Core/Syntax.lean`, `Semantics.lean`, `DSL.lean`, and `Lib/Lift.lean`.
  HWLib has been merged, with its namespace retained.
- For refinement: `LeanRTL/Core/Refine.lean`; see the alpha-pattern catalog at
  `docs/skills/patterns/alpha-shape-catalog.md`. The former `Lib/Refine.lean` and
  `Lib/Refine/Alpha.lean` moved to Core and the techniques collection, respectively.
- For parameterization (F2): `LeanRTL/Core/ParamBackend.lean`, formerly Param/Emit,
  plus one template such as `Param/CascadedAdder.lean`.
- **Proof-acceleration resources consolidated in v1.3 M47**: read their docstrings
  first. Observed reductions were 53% in proof rounds and 66% in elapsed time.
  - **`LeanRTL/Lib/StepSimp.lean`**: unfolding lemmas for `Module.step`, `cycleEnv`,
    `List.find?`, and `evalWires`, plus `step_simp`. Avoid spending four to six rounds
    rediscovering simp combinations; sequential `step_α`/`obs` obligations often
    close in one line. Source: 86 repeated discoveries across 206 blind-test notes.
  - **`LeanRTL/Lib/BvBridge.lean`**: `bv_decide` boundary support, including
    `ofNat`/`toNat` roundtrip simplification, `slt` to `ult` + MSB rewrites, mod-2,
    and Nat arithmetic bridges. Check here first for spurious counterexamples or
    stalls, often caused by opaque conversions; 67 cases were recorded in those notes.
- Style templates, not benchmark reference answers: `LeanRTL/Designs/Rtllm/*.lean`,
  `LeanRTL/Designs/Rtllm/Counter12.lean`, and `LeanRTL/Designs/Rtllm/Adder8bit.lean`.

**Technique collection `docs/skills/`**: consult `docs/skills/INDEX.md` before
starting. Its 61 entries are grouped into `tactics/` (such as `hstep-simp-macro` and
`ofnat-tonat-ofnat-simp`), `patterns/` (alpha shapes, per-N miter binding, L3→L4
output observation, fold induction for ∀N, and memory RAW laws), `principles/`, and
`process/`. Entries were promoted after recurring problems; search the index when
a proof shape looks familiar.

**Run verification at the end of every file:**

```
~/.elan/bin/lake env lean <your-file>.lean    # must exit 0
```

No `sorry`; `#print axioms <your_theorem>` must contain neither `sorryAx` nor `ofReduceBool`.

## 4. Unified root-cause JSON schema for all three benchmarks

At the end of ITER, write `<bench>/iter/<key>.json`. Use the benchmark's canonical
key: RTLLM → `<design>` (NL filename), VerilogEval → `<stem>`, CVDP → `<manifest id>`
(with `top` also recorded).

```json
{
  "benchmark": "rtllm | veval | cvdp",
  "key": "<canonical key, as above>",
  "toplevel": "<module actually instantiated by the harness>",
  "single_shot_status": "func_fail | iverilog_fail | gen_fail | sim_timeout | sim_err",
  "root_cause": "<one enum value below>",
  "detail": "One paragraph identifying the signal, cycle, or line, with concrete evidence",
  "iter_fixed": true,
  "framework_gap": null
}
```

The unified `root_cause` enum replaces framework_single_clock,
framework_module_params, framework_limit, and framework_other:

- `nl_ambiguity`: the specification is underdetermined (shift direction, output
  timing, Mealy/Moore, rounding, etc.) and the testbench fixes the choice.
- `nl_contradiction`: the specification contradicts itself.
- `nl_tb_inconsistency`: specification and testbench disagree, such as reset_n vs rst_n.
- `tb_broken`: the testbench is broken, uses VCS-only constructs, or fails its own reference.
- `gen_error`: the specification is clear and the single-shot implementation is wrong.
- `framework_gap`: check section 1 first; use only for a genuine limitation in 1.2
  or a combination gap in 1.3. Name the precise missing feature in `framework_gap`,
  including an F number when applicable; otherwise use `null`.

Do not rewrite historical records using older schemas. New records use this schema.

## 5. Friction hook — input to M28's two-strike ledger, required for every ITER run

Benchmark iteration is the largest source of friction observations, but root-cause
JSON previously did not contribute to the two-strike counts in
`benchmarks/_archive/eval_v3/friction_summary.json`. At the end of every ITER run,
write `<bench>/iter/<key>.friction.json` beside the root-cause record, using the
schema of historical `benchmarks/_archive/eval_v3/*/friction.json` examples:

```json
{
  "id": "<key>",
  "batch": "<current batch name, such as v0.9-iter>",
  "date": "YYYY-MM-DD",
  "repair_rounds": 2,
  "frictions": [
    { "kind": "spec | framework-gap | proof | tooling",
      "what": "Where manual work or a blocker occurred",
      "resolution": "How it was resolved, or why it remains unresolved",
      "sediment": "Candidate model, law, or alpha pattern for promotion into the library; record a strike" }
  ],
  "spec_changed": false
}
```

Write a record even with `"frictions": []`; zero friction is itself fitness data.
Entries with `kind: "framework-gap"` feed the two-strike count: the second
occurrence of the same gap triggers a promotion review (plan v0.8 M28).

### Agentic mode: the development testbench is not the oracle

Promoted after two observed cases in July 2026. In CVDP agentic mode, the visible
`verif/` development testbench is not the scorer; the hidden cocotb scorer is.

1. **Configuration comes from environment-default parameters, not the development
   instantiation.** The hidden harness uses test_runner's env-default `-P` bindings,
   matching the specification/documentation defaults rather than development-TB
   overrides. A three-input registered implementation based on the development TB
   can fail against the default four-input combinational configuration. Use the
   documented defaults.
2. **Development-TB edge races can mislead.** Driving and sampling on the same
   Verilog edge can make a structural DUT appear to require negedge or a cycle
   offset. A clean cocotb scorer lacks that race. If the specification says posedge,
   use posedge; follow the specification and scorer, not the development-TB artifact.

Use the development TB for compilation and rough checks. Final correctness rests
on specification semantics, the proof, and the hidden scorer.

## 6. Five design-file rules (plan v1.0 M33, finalized 2026-07-17)

1. **Keep a design and all its proofs in one file**, ordered
   `impl → spec → L1 → full trace (L3/L4/L5)`. There is no separate WholeDesign
   promotion layer.
2. **Promote shared lemmas into `LeanRTL/Lib/`.** They must not live in a design file.
   Designs may import Core/Lib but not other designs, except structural submodule
   composition through `*.Impl`. Lint with `scripts/check_design_imports.py`.
3. **The old prohibition on editing design files is retired.** It was a temporary
   benchmark-measurement rule. Measurements are snapshotted; git provides provenance.
4. **Read proof levels directly from the design's own theorems** (`*_correct`,
   `_trace`, `_refines_full`, `_reads`). `scripts/proof_level.py` no longer infers
   levels across files.
5. **Prove new designs directly to the highest meaningful level in that file.**
   Combinational designs stop at L1-complete; sequential designs need L1 + L3 + L4,
   plus L5 when semantics are clear. State genuine boundaries reported by
   `Module.semanticCoverage` honestly. "L1 now, higher levels later" is a migration
   strategy for existing designs only. The `leanrtl-full-temporal` skill is
   correspondingly a tool for existing designs.
