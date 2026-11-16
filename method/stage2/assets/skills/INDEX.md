# LeanRTL proof-skill library

A layered index of the crystallized proof know-how for LeanRTL — the moves that turn a hardware
spec into a machine-checked, artifact-reaching correctness proof.

## How the layers relate

The library has a **spine** and an **axis**:

- **Spine (L0 → L1 → L2).** An **L0 principle** is a load-bearing idea ("why"); an **L1 pattern**
  is a reusable proof shape for a class of designs ("what to do"), each linking *up* to a principle;
  an **L2 tactic** is a concrete Lean move ("how"), which patterns link *down* to. Read a pattern,
  follow its `principle:` up for the rationale and its `tactics:` down for the mechanics.
- **Process axis.** Operational discipline that keeps the spine honest end-to-end — no-peek
  boundaries, disk discipline, audits, the friction hook, cocotb-facing authoring conventions.

Each entry carries a `maturity`: **sediment** (a still-forming lesson), **promoted** (crystallized
into `LeanRTL/Lib/`, `CORE.md`, or a tactic macro), or **principle** (an L0 invariant). Where the
friction ledger records recurrences, a `strike` count is shown. The raw
`benchmarks/cvdp_agentic/friction/*.json` ledger (~76 files) remains the **sediment pool** feeding
this library: recurring pain there is counted (2-strike rule, plan v0.8 M28) and promoted here.

Every `lib:` / `example:` pointer in these files points at a declaration or design that actually
exists in the repo (grep-verified).

---

## Principles (L0)

| Skill | One-liner | Maturity |
|---|---|---|
| [Commuting square + generic induction](principles/commuting-square-and-generic-induction.md) | Prove the ∀t induction once (`SimRefines.trace`); designs supply only the single-step square. | principle |
| [The leaf is a decision, not an induction](principles/leaf-is-decision-not-induction.md) | Induction tames time; the leaf is closed by bv_decide/simp/rfl/omega, never more induction. | principle |
| [Correctness must reach the artifact](principles/proof-carrying-reaches-artifact.md) | The shipped Verilog is proven only via a proven transform OR a Yosys miter to the verified reference. | principle |
| [Friction → promotion](principles/friction-to-promotion.md) | Recurring proof pain is counted (2-strike) and promoted into Lib/ or CORE.md; marginal cost falls. | principle |
| [Two orthogonal axes](principles/two-orthogonal-axes.md) | Proof strength = vertical L0–L5 × horizontal 📐∀N; level is the max reached, the ∀N badge is orthogonal. | principle |
| [The spec is the oracle](principles/spec-is-the-oracle.md) | Matching golden RTL ≠ correct; only proof against a formal spec closes both gaps. | principle |

## Patterns (L1) — the spine

| Skill | One-liner | Maturity |
|---|---|---|
| [Single-step → L3 lift](patterns/single-step-to-l3-lift.md) | Bundle per-register lemmas into a `SimRefines`, read off `.trace` for the whole run. | promoted |
| [L3 → L4 observation](patterns/l3-to-l4-observation.md) | Add reset streams + LegalInputs + output-port obs via `refines_single_moore/_out`. | promoted |
| [Counter decode to `t mod N`](patterns/counter-decode-mod.md) | Decode state, induct on t; only one wrap state — split it, off it the `%` vanishes. | promoted |
| [Running-sum accumulator](patterns/running-sum-accumulator.md) | `acc(t) = Σ gated inputs`; keep the enable gate inside the spec fold. | promoted |
| [Partial-product invariant](patterns/partial-product-invariant.md) | Restate `yout=(a mod 2^k)·b`, peel one bit via `Nat.mod_mul`; never SAT the whole product. | promoted |
| [Well-founded termination (∃K)](patterns/well-founded-termination.md) | Strictly-decreasing measure + `loop_latch` gives an end-to-end halting theorem. | promoted |
| [Fold induction for ∀N](patterns/fold-induction-forall-n.md) | `eval` commutes with `.foldl` by list induction — one ∀N theorem, no per-N SAT. | promoted |
| [Width cast via `sextTo`](patterns/width-cast-sextto.md) | Discharge the signed-widen cast once with `eval_sextTo`, then work at uniform width. | sediment · s1 |
| [Parent flatten to a Module](patterns/parent-flatten.md) | `flattenParentSeq` → plain Module → `Parent.regTrace`; irreducible instance cycles stay split. | promoted · s3 |
| [Computed-wire congruence](patterns/computed-wire-congruence.md) | Prove base wire-env agreement once (`deq_hcones`), reuse N× via `evalWires_specEnv_round`. | promoted |
| [Per-N miter anchor](patterns/per-n-miter-anchor.md) | Yosys `equiv_induct` proves emitted@N ≡ compile(impl N); ∀N Lean carries the rest. | promoted |
| [F9 emission must be wire-free](patterns/f9-wire-free-emission.md) | Agentic sequential controllers `wires := []`; no input-fed continuous ternaries. | promoted · s3 |
| [Default to `f9_or_none`](patterns/f9-or-none-default.md) | Procedural next-state (vverilog) survives cocotb's X where structural netlists absorb it. | promoted · s3 |
| [State-decode invariant](patterns/state-decode-invariant.md) | Prove the FSM transition table equals a clean `stateSpec` + scenario star theorems. | promoted · s3 |
| [Memory raw laws](patterns/memory-raw-laws.md) | Per-access read-after-write laws over an honest free-input trace for `$mem` designs. | promoted |
| [clockNet honest single-tick](patterns/clocknet-honest-single-tick.md) | Multi-clock: prove per-domain single-tick cones + cosim; no whole-design trace across clocks. | promoted |
| [Register-bank list induction](patterns/register-bank-list-induction.md) | N named registers + one k-parameterized select lemma × N instantiations (avoids `$mem`). | sediment · s1 |
| [Cummings Gray CDC FIFO](patterns/cummings-gray-cdc-fifo.md) | Gray-pointer async FIFO with the exact two-bit-inverted full / empty-init-1 flag laws. | sediment · s1 |
| [Genuine parametric emission](patterns/genuine-parametric-emission.md) | When dev-TB config ≠ spec default, emit a real `ParamModule` and let the scorer pick N. | promoted · s2 |
| [Multi-cycle iterate bridge](patterns/multi-cycle-iterate-bridge.md) | `iterate_stepClosed_eq_regTrace` bridges abstract `iterate` to real `regTrace`. | promoted |
| [Fixed-latency delay law](patterns/fixed-latency-delay-law.md) | Delay line whole-trace law in three lines: L3 trace + `specTrace_succ`, exact latency. | promoted |
| [Rule-30 iterate compose](patterns/rule30-iterate-compose.md) | Free-run generator: prove the per-step CA rule, compose `state(t)=iterate rule t seed`. | sediment · s1 |
| [CRC step law + KAT](patterns/crc-step-law-plus-kat.md) | Per-step LFSR law (`crcStepE_eval`) + decide-checked known-answer tests pin bit-order. | sediment · s1 |
| [Stutter-refines protocol](patterns/stutter-refines-protocol.md) | Handshake advances spec only on `commit`; `StutterRefines.trace` over `committedTrace`. | promoted |
| [Dual edge = two registers](patterns/dual-edge-two-registers.md) | Single-edge negedge is inside M6; mixed posedge+negedge = two opposite-polarity regs. | promoted |
| [Async-load value trace](patterns/asyncload-value-trace.md) | `$aldff` gets a value-level whole-trace theorem via `stepAld`/`regTraceAld` (`aldffDen`). | promoted |
| [Async-reset value trace](patterns/asyncreset-value-trace.md) | Declaring `asyncReset` does NOT cost the whole-design theorem — `Module.eraseArst_simulate` proves `simulate` ignores it, `coveredModuloArstb` is the verdict. Route 2 adds the reset-active cycles via `stepArst`/`regTraceArst` (`arstDen`). Reset EDGE stays unproved, pinned structurally. | provisional |

## Tactics (L2)

| Skill | One-liner | Maturity |
|---|---|---|
| [`simp only`, not full `simp`](tactics/simp-only-not-full-simp.md) | Full simp normalizes literals like `% 64` and breaks lemma matching — keep the set explicit. | promoted |
| [Trailing `rfl` for Decidable](tactics/trailing-rfl-decidable.md) | ite/OfNat instance mismatch: append a bare `rfl` after the `simp only`. | promoted · s2 |
| [`bv_decide` for fixed width](tactics/bv-decide-for-fixed-width.md) | SAT + LRAT certificate for finite BitVec goals, inside the audited axiom whitelist. | promoted |
| [Restate to dodge SAT blow-up](tactics/restate-to-avoid-sat-blowup.md) | If `bv_decide` hangs, the fix is a better statement (an invariant), not a bigger timeout. | promoted |
| [`apply … _ _` to infer envs](tactics/apply-infer-envs.md) | Let unification place `cycleEnv`/`specEnv`; explicit envs whnf-timeout the elaborator. | sediment |
| [Base agreement by `simp only [forall_mem_*]`](tactics/elaborator-base-agreement.md) | Precomputed `rfl` lists, not `decide`/`fin_cases`, on wide wire sets. | sediment |
| [Local maxRecDepth/heartbeat bump](tactics/maxrecdepth-heartbeat-local-bump.md) | `set_option … in` on the one proof that needs it, never file-wide. | sediment |
| [`ofNat_toNat_ofNat` normalizer](tactics/ofnat-tonat-ofnat-simp.md) | The `@[simp]` reg-value round-trip that kills bespoke `ofNat_mod<2^w>` lemmas. | promoted · s2 |
| [`hstep_simp` macro](tactics/hstep-simp-macro.md) | The bundled simp set for the single-step obligation; append design lemmas only. | promoted |
| [Wide zero init not `rfl`](tactics/bitvec-ofnat-zero-not-rfl.md) | `BitVec.ofNat_zero`/simp for wide inits, so Lean never computes `2^512`. | sediment |
| [`Nat.mod_eq_of_lt` to drop `%`](tactics/nat-mod-eq-of-lt.md) | All quantities `< 2^w` ⇒ the modulus is a no-op; then `omega`. | promoted |
| [`omega` for bounds](tactics/omega-for-bounds.md) | Linear Nat/Int side goals; feed it the non-linear facts as hypotheses. | promoted |
| [`decide` for finite checks](tactics/decide-for-finite.md) | Small concrete cases (the one wrap state, a KAT row) close by kernel reduction. | promoted |
| [Bounded Nat case-split](tactics/bounded-nat-case-split.md) | `rcases (by omega : k=0∨…)` — core-Lean substitute for Mathlib `interval_cases`. | sediment |
| [Case-split + transport](tactics/nat-case-split-transport.md) | N-way `rcases` + `ofNat_toNat_ofNat` for the addressed-word select. | sediment · s1 |
| [Repack the spec env](tactics/specenv-repack.md) | Project-and-unfold the record state; `funext` env-bridge is unsound on raw `r`. | sediment · s2 |

## Process

| Skill | One-liner | Maturity |
|---|---|---|
| [Write to disk, fill one sorry at a time](process/write-to-disk-discipline.md) | Skeleton + sorry + import first, build+save each; the disk is truth, chat buffers stall. | promoted |
| [Audit after reorg](process/audit-after-reorg.md) | Run `check_axioms` + `proof_level`, not just `lake build`; a PKG_DIRS miss dropped 2881→46. | promoted |
| [The dev-TB is not the oracle](process/dev-tb-not-oracle.md) | Scored config = spec DEFAULT params; the dev TB has its own bugs and edge races. | promoted · s2 |
| [Log a friction JSON every run](process/friction-hook.md) | Root-cause + sediment per run — this is the strike-counting input to promotion. | promoted |
| [Verify generated files by regenerate + diff](process/verify-by-regenerate-diff.md) | For a generated registry, regenerate and `git diff` must be empty; edit the generator. | sediment |
| [The no-peek boundary](process/no-peek-boundary.md) | Single-shot must not read testbench/reference/_ref/harness/hidden jsonl. | promoted |
| [Match internal signal names](process/internal-signal-names.md) | cocotb probes internal registers by name — `clk→clock`, `sr→shift_reg`. | promoted |
| [Reset family convention](process/reset-family-convention.md) | NL says async ⇒ fold the reset in-band **and** declare `Reg.asyncReset` on the reset PORT with its polarity (never an inverter wire); don't bet a sync reset catches the first posedge. | promoted |
| [Pin the exact latency](process/delay-off-by-one.md) | Registered output reads one cycle late; done pulse on the last working cycle, not the next. | promoted |
| [Latency phrase ≠ state budget](process/latency-phrase-bounds-delay-not-state.md) | "one register stage / no additional buffering" bounds WHEN the output appears, not how many registers you may hold; deleting the staging reg makes the output move on hold cycles. | sediment |
| [Namespace vs. path independence](process/namespace-vs-path-independence.md) | Moving a `.lean` changes its import path, not its namespace; open/qualified refs survive. | sediment |
| [Registry shadowing](process/registry-shadowing.md) | The toplevel key can be shadowed across registries; grep-verify which impl is served. | sediment |

---

## By design type — which pattern for which circuit

A cross-index into the same pattern cards, keyed by what you are building (from each card's
`applies_to`). Start from your circuit's row; the pattern's `principle:` explains why and its
`tactics:` explain how. See [`../spec-guide.md`](../spec-guide.md) for the matching spec shape.

| Design class | Patterns |
|---|---|
| **Counters** (free-running / modulo) | [counter-decode-mod](patterns/counter-decode-mod.md) (L5 `t mod N` headline) · [rule30-iterate-compose](patterns/rule30-iterate-compose.md) (free-running generators) |
| **FSMs & pattern detectors** | [state-decode-invariant](patterns/state-decode-invariant.md) (transition table = clean `stateSpec` + scenario stars) |
| **Accumulators & MACs** | [running-sum-accumulator](patterns/running-sum-accumulator.md) (gated `Σ`) · [partial-product-invariant](patterns/partial-product-invariant.md) (shift-add) |
| **Shift & delay lines** | [fixed-latency-delay-law](patterns/fixed-latency-delay-law.md) (pipeline delay) · [crc-step-law-plus-kat](patterns/crc-step-law-plus-kat.md) (LFSR / CRC) |
| **Iterative datapaths** (mul / div / gcd) | [multi-cycle-iterate-bridge](patterns/multi-cycle-iterate-bridge.md) · [well-founded-termination](patterns/well-founded-termination.md) (∃K halting) · [partial-product-invariant](patterns/partial-product-invariant.md) |
| **Memories** | [memory-raw-laws](patterns/memory-raw-laws.md) (addressed `$mem`) · [register-bank-list-induction](patterns/register-bank-list-induction.md) (N-entry banks, avoids `$mem`) |
| **Multi-clock & CDC** | [clocknet-honest-single-tick](patterns/clocknet-honest-single-tick.md) (per-domain tick + cosim) · [cummings-gray-cdc-fifo](patterns/cummings-gray-cdc-fifo.md) (async FIFO) |
| **Hierarchical** (`Parent`) | [parent-flatten](patterns/parent-flatten.md) (`flattenParentSeq` → plain Module → `regTrace`) |
| **Protocol handshake** | [stutter-refines-protocol](patterns/stutter-refines-protocol.md) (ready-valid, spec advances on commit) |
| **Parametric ∀N** | [fold-induction-forall-n](patterns/fold-induction-forall-n.md) (reducers) · [width-cast-sextto](patterns/width-cast-sextto.md) (signed widen) · [genuine-parametric-emission](patterns/genuine-parametric-emission.md) (config ≠ spec default) · [per-n-miter-anchor](patterns/per-n-miter-anchor.md) (Yosys anchor) |
| **Combinational** (L1-complete) | no dedicated L1 pattern — `eval = spec` closes by [`bv_decide`](tactics/bv-decide-for-fixed-width.md); for signed heterogeneous widths [width-cast-sextto](patterns/width-cast-sextto.md), for ∀N reducers [fold-induction-forall-n](patterns/fold-induction-forall-n.md) |

**Cross-cutting (every sequential class).** The L1→L3→L4 spine is design-independent:
[single-step-to-l3-lift](patterns/single-step-to-l3-lift.md) (bundle per-register lemmas into a
`SimRefines`), [l3-to-l4-observation](patterns/l3-to-l4-observation.md) (add reset streams +
`LegalInputs` + output-port obs), [alpha-shape-catalog](patterns/alpha-shape-catalog.md) (choose the
abstraction `α`), and [computed-wire-congruence](patterns/computed-wire-congruence.md) (when the
next-state reads computed wires).

**Special register / clock features (orthogonal to design class).**
[dual-edge-two-registers](patterns/dual-edge-two-registers.md) (mixed posedge+negedge = two
opposite-polarity regs) · [asyncload-value-trace](patterns/asyncload-value-trace.md) (`$aldff`
dynamic-load registers) · [asyncreset-value-trace](patterns/asyncreset-value-trace.md) (`$adff`
async-reset registers; default to async when the spec is silent, name the reset PORT with its
polarity, never an inverter wire — it costs no theorem).

**Emission & RTL-carry (agentic self-authored netlists).**
[f9-or-none-default](patterns/f9-or-none-default.md) (procedural next-state survives cocotb's X) ·
[f9-wire-free-emission](patterns/f9-wire-free-emission.md) (`wires := []` for sequential controllers).
