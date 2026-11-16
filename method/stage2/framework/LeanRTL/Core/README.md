# LeanRTL/Core/ — the engine

Everything here answers one question: **"is what you wrote real, meaningful, and faithfully
carried to actual Verilog?"** Users and agents never edit these files and rarely need to read
them — the language surface is documented in [`docs/dsl-reference.md`](../../docs/dsl-reference.md),
the rationale in [`docs/ARCHITECTURE.md`](../../docs/ARCHITECTURE.md).

Membership test (first principles): *delete it — does a **guarantee** weaken, or only a
convenience?* Guarantees live here; conveniences (proof combinators) live in `LeanRTL/Lib/`.

## The object language — what you can say

| File | Role |
|---|---|
| `Syntax.lean` | The deep-embedded AST: `Expr` (23 constructors, width-indexed types), `Reg` (next/init/asyncReset/asyncLoad/negedge/clockNet), `Wire`, `Module`, `Latch`, `MemBlock`, `Inst`/`Parent`. Hardware **is a Lean value** of these types. |
| `DSL.lean` | Smart constructors (`caseE`, `fsmNext`, `ifE`, `arraySelect`, `rotate*E`, `regFile`) — each desugars to the core AST and ships a **proven `eval`-law**, so sugar costs zero trust. |

## The reference semantics — what it means

| File | Role |
|---|---|
| `Semantics.lean` | The single authority on meaning: `eval` (expression → value), `Module.step` (one clock edge: combinational settle via `evalWires`, then simultaneous register latch), `simulate`. **This is the one part of the system that cannot be proven, only audited** — which is why it is kept small enough to read. |
| `MemSemantics.lean` | Per-access memory semantics (read-after-write laws for `MemBlock`). |
| `Coverage.lean` | `Module.semanticCoverage` — the machine judgment of the *language ≤ semantics* boundary: `.full` (whole-design simulate theorems apply) vs `.perRegister [reasons]` (asyncReset / asyncLoad / clockNet / memShape / latch / negedgeMix). Surfaced by `leanrtl check`/`status`. |

## The promise — what a certificate claims

| File | Role |
|---|---|
| `Refine.lean` | The obligation vocabulary: `SimRefines` (L3 lockstep forward simulation), `Refines` (L4: + reset streams, `LegalInputs`, output-port observation — the anti-cheat form), `StutterRefines` (non-lockstep protocols), `specTrace`/`specTraceR`, and the once-proven `.trace`/`.observe` induction. The *definitions* of what we promise live here; the *tools that discharge them* live in `Lib/`. |
| `Spec.lean`, `Spec/Model.lean` | Minimal spec-side vocabulary (`Invariant`) and implementation-agnostic abstract models (Queue/Mem) — the two-layer "wall": the spec side deliberately cannot import the impl side. |

## The bridge to the real artifact — proven compilation

| File | Role |
|---|---|
| `Compiler.lean` | The lowering: `Module`/`Parent` → Yosys RTLIL cells (`$dff`, `$adff`, `$aldff`, `$mem_v2`, `$dlatch`, …). Two-pass instance compilation (forward references / instance feedback supported). |
| `Backend.lean` | The RTLIL-JSON data model + renderer. |
| `BackendSem.lean` | Denotational semantics **of RTLIL** — the reference the correctness proofs compare against. |
| `CompilerCorrect.lean` | Proof stage 1: combinational faithfulness `⟦e⟧ = ⟦compile e⟧` (largest file; single-purpose). |
| `CompilerCorrectSeq.lean` | Proof stage 2: sequential faithfulness; also home of `regTrace` (the register-trace definition every whole-trace theorem quantifies over) and `simulateFast`. |
| `CompilerDeterministic.lean` | Proof stage 3: the ∀σ direction — the emitted netlist is deterministic over **all** valuations. |
| `CompilerModuleCorrect.lean` | Proof stage 4: whole-module fold lemmas (the M6 class gate `moduleChecksb` that `Coverage` builds on). |
| `Optimize.lean` | Netlist optimization, with meaning-preservation proofs. |
| `ProcVerilog.lean` | F9 procedural emitter (`always @(posedge) q <= next` shape) — used when the structural render mis-simulates under cocotb; anchored back to the proven RTLIL by a Yosys miter. |
| `ParamBackend.lean` | The parametric (`#(parameter …)`) Verilog emitter for ∀N designs (`Designs/Param/`) — an *unproven template* emitter, which is exactly why every parametric design is re-anchored per-N by `benchmarks/cvdp/param_check.py`'s equivalence miters. |

## Hierarchy — guarantees across module boundaries

| File | Role |
|---|---|
| `HierCorrect.lean` | Combinational `Parent` flattening + faithfulness. |
| `HierSeqCorrect.lean` | Sequential hierarchy (F10): `flattenParentSeq` turns a `Parent` into a register-shaped flat `Module`; per-instance faithfulness (`flatNext_eq_childStep`, `flatOut_eq_childOut`). |
| `HierRefine.lean` | `Parent.regTrace` + the whole-trace refinement bridges for hierarchical designs (thin defeq layer over `SimRefines.trace`). |
| `HierSeqBridge.lean` | The flat-trace ↔ hierarchical-`simulateSeq` state equality: wire-free children (`WFParentSeq`) and the generalized wire-carrying form (`WFParentSeq'` → `Parent.regTrace_eq_hierRegTrace'`). |

## Admission & self-evidence

| File | Role |
|---|---|
| `Check.lean` | Legality lint (`Module.checkErrors` / `Parent.checkErrors`) — defines the class of designs the theorems quantify over. |
| `CheckWidth.lean` | Executable width checkers, with proofs. |
| `NetTrace.lean` | The netlist-level trust chain (M29): leaf theorems with **zero importers by design** — they exist to be audited, not called, and are gated in `scripts/check_axioms.sh` `CORE_PAIRS` and force-built by the lakefile glob. |

## Trust statuses at a glance

```
proven   : Compiler* / Hier* / Optimize / CheckWidth / NetTrace theorems (kernel-checked, whitelisted axioms)
audited  : Syntax + Semantics definitions (small on purpose — read them)
anchored : ProcVerilog & ParamBackend output (unproven emitters ≡-checked against proven RTLIL by Yosys miters)
trusted  : Yosys write_verilog rendering of RTLIL
```
