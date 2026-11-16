import LeanRTL.Core.CompilerCorrectSeq
import LeanRTL.Core.Refine
/-!
# `Lift` — a reusable proof-lifting library: per-cycle `*_correct` ⟶ whole-trace `SimRefines`

Most sequential designs in this repo prove **per-register next-state** lemmas
(`<reg>_correct : eval <reg>Next (env …) = spec<reg> …`), which relate cycle `t` to `t+1`
only.  Lifting one to a genuine *whole-trace* theorem via the `SimRefines` forward-simulation
bridge (`LeanRTL/Refine.lean`) is a fixed, mechanical dance:

1. bridge the design's own `env` helper to the `cycleEnv` that `Module.step` actually evaluates
   under (the `show cycleEnv … = … from rfl` boilerplate);
2. unfold `Module.step` on the design's register shape to expose `eval <reg>Next (cycleEnv …)`;
3. package the four `SimRefines` obligations (`init_inv`/`init_α`/`step_inv`/`step_α`), where for a
   design that needs no gluing invariant three of the four are `trivial`.

This file makes each of those steps a named, design-agnostic lemma so a caller only supplies the
design's `next_correct` lemma and the register shape.  It is the foundation for a batch lift of the
corpus, so the API is kept small and every lemma is `rfl`/`by decide`-dischargeable from the caller.

The API in one glance:

| shape                              | combinator                                   |
| ---------------------------------- | -------------------------------------------- |
| 1 reg, default record, no wires    | `simRefines_single`                          |
| 1 reg, ANY record (async/negedge…) | `simRefines_single_rec`                      |
| 2 regs                             | `simRefines_pair`                            |
| 3 regs                             | `simRefines_triple`                          |
| n>3 regs                           | `simRefines_triv` + `multi_step_reg` (see §5)|

Nothing here is design-specific; the two seed lifts live in
`LeanRTL/WholeDesign/UpDownCounterTrace.lean` and `LeanRTL/WholeDesign/Dff8Trace.lean`; four batch
waves (RTLLM + VerilogEval, ~40 designs) live in the sibling `*Trace.lean`/`BcdClock.lean` files.
-/

namespace LeanRTL.Designs.WholeDesign.Lift
open LeanRTL LeanRTL.CompilerCorrectSeq LeanRTL.Refine

/-! ## 1. `cycleEnv` projection lemmas

`Module.step` evaluates every next-state expression under `cycleEnv regVals inputs regNames`, which
reads register names from `regVals` and everything else from `inputs`.  A design's `next_correct`
lemma is stated over its own `env` helper; these two lemmas are the bridge, replacing the
per-signal `show cycleEnv … = … from rfl` boilerplate.  The membership side-conditions are concrete
list-membership facts the caller discharges with `by decide`. -/

/-- A signal that IS a register name reads from the register file. -/
@[simp] theorem cycleEnv_reg (rv i : Env) (names : List String) (n : String)
    (h : names.contains n = true) : cycleEnv rv i names n = rv n := by
  simp only [cycleEnv, h]; rfl

/-- A signal that is NOT a register name reads from the inputs. -/
@[simp] theorem cycleEnv_input (rv i : Env) (names : List String) (n : String)
    (h : names.contains n = false) : cycleEnv rv i names n = i n := by
  simp only [cycleEnv, h]; rfl

/-! ## 2. `BitVec.ofNat`-mod normalisation + the standard env↔cycleEnv bridge incantation

### The `.toNat` round-trip

A register materialised through `env` appears on the spec side as `BitVec.ofNat w ((BitVec.ofNat w
n).toNat)` (the design's `env` binds each register to `<bv>.toNat`).  Collapsing that round-trip
back to `BitVec.ofNat w n` is what closes the bridge.  The **robust** way to do it is the pair
`BitVec.ofNat_toNat` (`BitVec.ofNat m x.toNat = x.setWidth m`, for *any* `x`) then `BitVec.setWidth_eq`
(`x.setWidth n = x`), applied under **`simp only`**.  Under `simp only` no modulus ever appears, so no
per-width bookkeeping is needed — this is why every wave-A/C/D bridge is mod-lemma-free.

`ofNat_toNat_ofNat` below packages that same round-trip as a single named lemma.  **Do not reach for
full `simp`** in a bridge: full `simp` carries the global lemma `BitVec.toNat_ofNat`
(`(BitVec.ofNat w n).toNat = n % 2^w`), which fires *first* (bottom-up), rewriting the round-trip to
`BitVec.ofNat w (n % 2^w)` and then reducing `2^w` to a literal (`% 64`, `% 256`, …).  At that point
the round-trip is gone and neither `ofNat_toNat_ofNat` nor the old symbolic `ofNat_mod_pow` (over
`2^w`) can fold it back — which is exactly why `ofNat_mod_pow` was dead and why BcdClock + wave-B
re-derived bespoke per-width `ofNat_mod2/4/…` literals.  Staying in `simp only` sidesteps all of it.

### The standard bridge tail

Every single- and multi-register bridge closes with the *verbatim identical* invariant tail

    [String.reduceEq, if_pos, ite_false, BitVec.ofNat_toNat, BitVec.setWidth_eq]

(the `hstep_simp [ … ]` macro below appends exactly this to the caller's design-specific unfolds).
Pairing rule: `String.reduceEq` MUST travel with `if_pos, ite_false` — `String.reduceEq` rewrites a
string comparison `"a" == "b"` to `True`/`False`, and `if_pos`/`ite_false` are what then collapse the
resulting `if True/False` in the reset/mux chain; drop them and the env `if`-chain stalls.

### Gotcha: a `def sp := spec …` shorthand does NOT auto-unfold

If a bridge abbreviates the spec as `private def sp (r i) := spec …` and projects `(sp r i).1`, then
`rw [← next_correct …]` fails ("did not find pattern") because the goal still shows `(sp r i).1`, not
`(spec …).1`.  Insert `simp only [sp]` (or `simp only [specStep]`) to unfold the shorthand BEFORE the
`rw [← …]`. -/

/-- The `.toNat` round-trip killer as one named `@[simp]` lemma: truncating `BitVec.ofNat w n` to a
    `Nat` and back is the identity.  Equivalent to `BitVec.ofNat_toNat` + `BitVec.setWidth_eq` on this
    particular shape; usable in a `simp only` list where you'd otherwise write that pair.  (Prefer the
    pair when the `.toNat` wraps a non-`ofNat` term such as a whole `if`; this lemma is intentionally
    the narrow, self-documenting case.)  Replaces the dead `ofNat_mod_pow` (which never fired once
    full `simp` had reduced `2^w` to a literal modulus). -/
@[simp] theorem ofNat_toNat_ofNat (w n : Nat) :
    BitVec.ofNat w ((BitVec.ofNat w n).toNat) = BitVec.ofNat w n := by
  apply BitVec.eq_of_toNat_eq; simp [BitVec.toNat_ofNat]

open Lean.Parser.Tactic in
/-- **The standard bridge closer.**  `hstep_simp [a, b, …]` is `simp only [a, b, …, String.reduceEq,
    if_pos, ite_false, BitVec.ofNat_toNat, BitVec.setWidth_eq]`: the caller lists only the
    design-specific unfolds (`<reg>Next`, `eval`, `Env.lookup`, the design's `env`, and the
    `show cycleEnv … = … from rfl` / `cycleEnv_reg` / `cycleEnv_input` projections), and the macro
    appends the invariant tail.  See §2 for the pairing rule and the `def sp` gotcha. -/
macro "hstep_simp" "[" args:simpLemma,* "]" : tactic =>
  `(tactic| simp only [$args,*, String.reduceEq, if_pos, ite_false,
                       BitVec.ofNat_toNat, BitVec.setWidth_eq])

/-! ═══════════════════════════════════════════════════════════════════════════
    § L3 combinators (`SimRefines`) — §3–§6: reset-free, output-blind lockstep lifts.
    ═══════════════════════════════════════════════════════════════════════════ -/

/-! ## 3. Invariant-free packaging

For a design that needs no gluing invariant (`inv := fun _ => True` — the registers are always
well-defined), three of the four `SimRefines` obligations are `trivial`.  Supply only `init_α`
(`α m.initRegs = s0`) and the commuting square `step_α` (`α (m.step r i false) = specStep (α r) i`). -/
theorem simRefines_triv (m : Module) {S : Type _} (α : Env → S) (specStep : S → Env → S) (s0 : S)
    (hinit : α m.initRegs = s0)
    (hstep : ∀ r i : Env, α (m.step r i false) = specStep (α r) i) :
    SimRefines m α specStep s0 (fun _ => True) where
  init_inv := trivial
  init_α   := hinit
  step_inv := fun _ _ _ => trivial
  step_α   := fun r i _ => hstep r i

/-! ## 4. The single-register combinator (the common case)

dff / counter / one-shot / single-register FSM: one register, no wires.  On such a module
`Module.step r i false` reduces (on the register's own name) to `(eval rnNext (cycleEnv r i [rn])).toNat`,
which `single_step` proves once and for all; `simRefines_single` then packages the whole `SimRefines`
from just the design's `next_correct` (as `hstep`) and the register shape (`hshape`, dischargeable by
`⟨rfl, rfl⟩`).

**Register-record generality.**  `simRefines_single` fixes the register to the *default* record shape
`{name, width, next, init}` (`asyncReset := none`), so `hshape := ⟨rfl, rfl⟩`.  A register carrying a
non-default field — `asyncReset` (`$adff`), `negedge`, `asyncLoad` (`$aldff`), `clockNet` — fails that
exact-record equality.  But `Module.step _ _ false` reads a register through *only* `find? (·.name = rn)`
and `eval reg.next`; the structural fields are invisible to the reset-free cycle.  So the generalised
`single_step_rec` / `simRefines_single_rec` (parameterised over the whole `Reg` record) lift **any**
single-register design reset-free, and `simRefines_single` is just their `{name,width,next,init}`
instance.  (Whole-design *resetful*/multi-domain semantics for async/`clockNet` regs remain out of the
cycle model — see the honesty notes in `Semantics.lean` — so these are honest non-reset-cone traces.) -/

/-- Reduce a single-register, wire-free module's step, on the register's own name, to the bare
    next-state evaluation under `cycleEnv`.  Fixed to the default `{name,width,next,init}` record;
    for a non-default record use `single_step_rec`.  This is the load-bearing `Module.step`
    unfolding. -/
theorem single_step {m : Module} {rn : String} {w : Nat} {rnNext : Expr w} {i0 : BitVec w}
    (hregs : m.regs = [{ name := rn, width := w, next := rnNext, init := i0 }])
    (hwires : m.wires = []) (r i : Env) :
    (m.step r i false) rn = (eval rnNext (cycleEnv r i [rn])).toNat := by
  have hfind : m.regs.find? (·.name = rn)
      = some { name := rn, width := w, next := rnNext, init := i0 } := by
    rw [hregs]; simp
  have hmap : m.regs.map (·.name) = [rn] := by rw [hregs]; simp
  simp only [Module.step, hwires, evalWires, List.foldl_nil, hfind, hmap]
  rfl

/-- `single_step` generalised over the **full** register record: on a single-register, wire-free
    module `Module.step r i false` reduces (on the register's own name) to the bare next-state
    evaluation, regardless of the register's structural fields (`asyncReset`/`negedge`/…).  The proof
    is byte-identical to `single_step` with the literal record replaced by the abstract `reg`. -/
theorem single_step_rec {m : Module} {reg : Reg}
    (hregs : m.regs = [reg]) (hwires : m.wires = []) (r i : Env) :
    (m.step r i false) reg.name = (eval reg.next (cycleEnv r i [reg.name])).toNat := by
  have hfind : m.regs.find? (·.name = reg.name) = some reg := by rw [hregs]; simp
  have hmap : m.regs.map (·.name) = [reg.name] := by rw [hregs]; simp
  simp only [Module.step, hwires, evalWires, List.foldl_nil, hfind, hmap]
  rfl

/-- **The single-register lift, over the full `Reg` record.**  For a module `m` whose only register
    is `reg` (any record — sync, async-reset, negedge, aldff, clockNet) and that has no wires,
    forward-simulate the abstraction `α r = BitVec.ofNat reg.width (r reg.name)` against `specN`.
    Callers supply:

    * `hshape` : `m.regs = [reg] ∧ m.wires = []` — discharged by `⟨rfl, rfl⟩`;
    * `hstep`  : the design's `next_correct`, re-aimed at `cycleEnv r i [reg.name]`;
    * `hinit`  : `BitVec.ofNat reg.width (m.initRegs reg.name) = s0` — discharged by `rfl`/`by decide`.

    Returns a full (invariant-free) `SimRefines`.  `simRefines_single` is the `asyncReset := none`
    special case. -/
theorem simRefines_single_rec (m : Module) (reg : Reg)
    (specN : BitVec reg.width → Env → BitVec reg.width) (s0 : BitVec reg.width)
    (hshape : m.regs = [reg] ∧ m.wires = [])
    (hstep : ∀ r i : Env,
        eval reg.next (cycleEnv r i [reg.name]) = specN (BitVec.ofNat reg.width (r reg.name)) i)
    (hinit : BitVec.ofNat reg.width (m.initRegs reg.name) = s0) :
    SimRefines m (fun r => BitVec.ofNat reg.width (r reg.name)) specN s0 (fun _ => True) := by
  refine simRefines_triv m (fun r => BitVec.ofNat reg.width (r reg.name)) specN s0 hinit ?_
  intro r i
  show BitVec.ofNat reg.width ((m.step r i false) reg.name)
      = specN (BitVec.ofNat reg.width (r reg.name)) i
  rw [single_step_rec hshape.1 hshape.2 r i]
  simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
  exact hstep r i

/-- **The single-register lift** (default record shape).  For a module `m` whose only register is
    `{name := rn, width := w, next := rnNext, init := i0}` and that has no wires, forward-simulate
    the abstraction `α r = BitVec.ofNat w (r rn)` against `specN`.  Callers supply:

    * `hshape`  : `m.regs = [{…}] ∧ m.wires = []` — discharged by `⟨rfl, rfl⟩`;
    * `hstep`   : the design's `next_correct`, re-aimed at `cycleEnv r i [rn]` (bridge the design's
                  `env` with `cycleEnv_reg`/`cycleEnv_input`);
    * `hinit`   : `BitVec.ofNat w (m.initRegs rn) = s0` — discharged by `rfl`/`by decide`.

    Returns a full `SimRefines` (invariant-free), whose `.trace` (via `regTrace_through_α`) is the
    whole-trace theorem.  Implemented as the default-record instance of `simRefines_single_rec`. -/
theorem simRefines_single (m : Module) (rn : String) (w : Nat) (rnNext : Expr w) (i0 : BitVec w)
    (specN : BitVec w → Env → BitVec w) (s0 : BitVec w)
    (hshape : m.regs = [{ name := rn, width := w, next := rnNext, init := i0 }] ∧ m.wires = [])
    (hstep : ∀ r i : Env, eval rnNext (cycleEnv r i [rn]) = specN (BitVec.ofNat w (r rn)) i)
    (hinit : BitVec.ofNat w (m.initRegs rn) = s0) :
    SimRefines m (fun r => BitVec.ofNat w (r rn)) specN s0 (fun _ => True) :=
  simRefines_single_rec m { name := rn, width := w, next := rnNext, init := i0 } specN s0
    hshape hstep hinit

/-! ## 5. The multi-register combinators (tuple lifts)

Cascade counters, edge detectors, FSM datapaths: several registers, whose abstract state is a tuple
`(BitVec w₁ × BitVec w₂ × …)`.  The friction here was fivefold — every multi-register design
re-rolled the same `refine simRefines_triv …; intro r i; show <explicit tuple>; simp only [specStep,
Prod.mk.injEq]; exact ⟨…⟩` closing dance.  `simRefines_pair`/`simRefines_triple` absorb that dance:
the caller supplies only the per-register bridges (each `BitVec.ofNat wₖ ((m.step r i false) rnₖ) =
<the kᵗʰ spec>`, proved exactly as before) and the combinator assembles the `SimRefines`.

Two conveniences make them drop-in:

* **The per-register bridges may be stated in their natural form** — RHS `= <raw spec function>`,
  NOT `= (specStep (α r) i).k`.  As long as `specStep` is a literal `Prod.mk` tuple of those spec
  functions, `(specStep (α r) i).k` is *definitionally* the kᵗʰ spec, so Lean accepts the natural
  bridge where the projection form is expected.  This covers BOTH lemma shapes: separate
  `<reg>_correct` per register (calendar/traffic) and a single conjunction projected `.1/.2.1/.2.2`
  (edge_detect) — the combinator only sees the finished per-register bridge either way.
* **`α` is built by the combinator** as `fun r => (BitVec.ofNat w₁ (r rn₁), …)`; the caller's own `α`
  def must be that same tuple (it is, by convention) so the final `_trace` theorem typechecks by defeq.

For **n > 3** registers (BcdClock n=6, synchronizer n=5, traffic_light n=8) there is no fixed-arity
combinator; use `simRefines_triv` directly with the tuple `α`/`specStep` and close with
`simp only [specStep, Prod.mk.injEq]; exact ⟨sα_1 r i, …, sα_n r i⟩`, where each `sα_k` is proved via
`multi_step_reg` (or the `show … = (eval rnₖNext (evalWires m.wires (cycleEnv …))).toNat` defeq) +
`hstep_simp`.  The N-tuple `refine`/`intro`/`show`/`simp only [specStep, Prod.mk.injEq]`/`exact` shape
is the direct n>3 template; `simRefines_pair`/`_triple` are just its n=2/3 packagings. -/

/-- **Per-register `Module.step` projection** (the multi-register analogue of `single_step`, with NO
    singleton-regs and NO `m.wires = []` restriction).  Given `find?` on a register name, project that
    one register's next value.  `hfind` is discharged by `rfl` (the reg list is a literal, so `find?`
    computes); it is robust where the raw `show … from rfl` defeq is fragile.  Wire-carrying modules
    keep the `evalWires m.wires (cycleEnv …)` environment (e.g. `width_8to16`'s `not_rst_n` net).

    TEMPLATE — no current in-tree caller (the 2–3-register corpus is covered by `simRefines_pair` /
    `simRefines_triple`).  Kept as the documented **n>3** template referenced by §2's routing table and
    §5 (and by `docs/plan/proof-levels.md`): `simRefines_triv` + one `multi_step_reg` per register. -/
theorem multi_step_reg {m : Module} {rn : String} {reg : Reg}
    (hfind : m.regs.find? (·.name = rn) = some reg) (r i : Env) :
    (m.step r i false) rn
      = (eval reg.next (evalWires m.wires (cycleEnv r i (m.regs.map (·.name))))).toNat := by
  simp only [Module.step, hfind, if_neg Bool.false_ne_true]

/-- **The two-register lift.**  `α r = (BitVec.ofNat w₁ (r rn₁), BitVec.ofNat w₂ (r rn₂))`; supply the
    two per-register bridges (`h1`, `h2`) and `hinit`.  Prev/cur register pairs (registered edge/change
    detectors, sample-and-compare, delay-line + combinational output) are all this shape. -/
theorem simRefines_pair (m : Module) (rn1 rn2 : String) (w1 w2 : Nat)
    (specStep : (BitVec w1 × BitVec w2) → Env → BitVec w1 × BitVec w2)
    (s0 : BitVec w1 × BitVec w2)
    (hinit : (BitVec.ofNat w1 (m.initRegs rn1), BitVec.ofNat w2 (m.initRegs rn2)) = s0)
    (h1 : ∀ r i : Env, BitVec.ofNat w1 ((m.step r i false) rn1)
        = (specStep (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2)) i).1)
    (h2 : ∀ r i : Env, BitVec.ofNat w2 ((m.step r i false) rn2)
        = (specStep (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2)) i).2) :
    SimRefines m (fun r => (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2))) specStep s0
      (fun _ => True) := by
  refine simRefines_triv m _ specStep s0 hinit ?_
  intro r i
  show (BitVec.ofNat w1 ((m.step r i false) rn1), BitVec.ofNat w2 ((m.step r i false) rn2)) = _
  rw [h1 r i, h2 r i]

/-- **The three-register lift.**  `α r = (BitVec.ofNat w₁ (r rn₁), BitVec.ofNat w₂ (r rn₂),
    BitVec.ofNat w₃ (r rn₃))`; supply the three per-register bridges and `hinit`.  Covers 3-register
    edge detectors (`edge_detect`), 3-digit ripple counters (`calendar`), etc. -/
theorem simRefines_triple (m : Module) (rn1 rn2 rn3 : String) (w1 w2 w3 : Nat)
    (specStep : (BitVec w1 × BitVec w2 × BitVec w3) → Env → BitVec w1 × BitVec w2 × BitVec w3)
    (s0 : BitVec w1 × BitVec w2 × BitVec w3)
    (hinit : (BitVec.ofNat w1 (m.initRegs rn1), BitVec.ofNat w2 (m.initRegs rn2),
              BitVec.ofNat w3 (m.initRegs rn3)) = s0)
    (h1 : ∀ r i : Env, BitVec.ofNat w1 ((m.step r i false) rn1)
        = (specStep (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2), BitVec.ofNat w3 (r rn3)) i).1)
    (h2 : ∀ r i : Env, BitVec.ofNat w2 ((m.step r i false) rn2)
        = (specStep (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2), BitVec.ofNat w3 (r rn3)) i).2.1)
    (h3 : ∀ r i : Env, BitVec.ofNat w3 ((m.step r i false) rn3)
        = (specStep (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2), BitVec.ofNat w3 (r rn3)) i).2.2) :
    SimRefines m
      (fun r => (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2), BitVec.ofNat w3 (r rn3)))
      specStep s0 (fun _ => True) := by
  refine simRefines_triv m _ specStep s0 hinit ?_
  intro r i
  show (BitVec.ofNat w1 ((m.step r i false) rn1), BitVec.ofNat w2 ((m.step r i false) rn2),
        BitVec.ofNat w3 ((m.step r i false) rn3)) = _
  rw [h1 r i, h2 r i, h3 r i]

/-! ## 6. One-step trace corollary

Hand a caller the whole-trace equation directly, without threading `.trace … |>.2` by hand. -/

/-- **Whole-trace, through `α`.**  Given any `SimRefines`, at every cycle `t` of a reset-free run the
    abstracted register state equals the `t`-fold `specStep` from `s0`.  This is the payoff form:
    `α (regTrace m inputs (fun _=>false) t) = specTrace specStep s0 inputs t`. -/
theorem regTrace_through_α {m : Module} {S : Type _} {α : Env → S} {specStep : S → Env → S} {s0 inv}
    (h : SimRefines m α specStep s0 inv) (inputs : Nat → Env) (t : Nat) :
    α (regTrace m inputs (fun _ => false) t) = specTrace specStep s0 inputs t :=
  (h.trace inputs t).2

/-! ═══════════════════════════════════════════════════════════════════════════
    § L4 combinators (`Refines`) — §7–§10: add reset streams + legality + output observation.
    ═══════════════════════════════════════════════════════════════════════════ -/

/-! ## 7. The single-register **L4** combinator (`Refines`, full refinement)

`simRefines_single` (§4) lifts a design to `SimRefines` — the reset-free, output-blind L3 bridge.
The L4 target `Refines` (`LeanRTL/Refine.lean`) adds three obligations on top of the lockstep square:

* **`reset_α`** — the *framework* synchronous-reset step re-establishes the initial abstract state
  `s0`, so `Refines.trace` quantifies over ALL reset streams, not just the never-reset one;
* **`obs`** — the impl's REAL output PORTS denote the spec's outputs on the abstracted state
  (anti-cheat gate #3: a vacuous `α` that ignores the wires no longer "refines");
* boundary legality — `step_α`/`obs` MAY assume `Module.LegalInputs`.

The pleasant discovery for the single-register shape is that **two of the three are free**:

* `reset_α` is *derivable from `init_α`*.  `Module.step r i true` forces the register to its
  `init` (regardless of `Module.reset`/async fields — see `reset_step_rec`), and `m.initRegs`
  reads back that same `init` (`initRegs_single_rec`); so `α (m.step r i true) = α m.initRegs = s0`
  is exactly the `hinit` the L3 lift already supplies.  No new `hreset` obligation is needed.
  (This is precisely the task's "framework sync-reset path re-establishes `init`" note: these
  designs carry their *real* reset IN-BAND on the `rst` input, handled inside `step_α`; the
  `Refines.reset_α` covers the *framework* out-of-band sync-reset path, which merely reloads `init`.)
* `obs` is near-`rfl` for the **Moore** shape where the sole output port IS the register
  (`outputs := [{name := out, expr := .var rn w}]`) — `moore_obs` discharges it mechanically, so
  `refines_single_moore` asks the caller for *nothing* beyond the L3 `hstep`/`hinit` plus the two
  shape equalities (`houts`, all `rfl`).

So an L3→L4 promotion of a Moore-output single-register design costs exactly the same proof effort
as the L3 lift did (the `next_correct` re-aim) — the L4 obligations are all mechanical.  These are
kept `LegalInputs`-free (unconditional `hstep`/output shape) to match the counters we validate on;
a design that genuinely needs `LegalInputs` in `step_α` threads it in the `hstep` it supplies. -/

/-- **Reset-cycle step reduction** (full `Reg` record).  On a *reset* cycle `Module.step r i true`
    forces the single register to its `init`, regardless of the register's structural fields
    (`asyncReset`/`negedge`/…) — the sync-reset path reads only `r.init`.  The `true`-branch analogue
    of `single_step_rec`. -/
theorem reset_step_rec {m : Module} {reg : Reg}
    (hregs : m.regs = [reg]) (r i : Env) :
    (m.step r i true) reg.name = reg.init.toNat := by
  have hfind : m.regs.find? (·.name = reg.name) = some reg := by rw [hregs]; simp
  simp only [Module.step, hfind, if_true]

/-- The single register's `init` value read back through `Module.initRegs`.  Pairs with
    `reset_step_rec` to make `reset_α` = `init_α`. -/
theorem initRegs_single_rec {m : Module} {reg : Reg} (hregs : m.regs = [reg]) :
    m.initRegs reg.name = reg.init.toNat := by
  have hfind : m.regs.find? (·.name = reg.name) = some reg := by rw [hregs]; simp
  simp only [Module.initRegs, hfind]

/-- **The Moore observation lemma** (output port IS the register).  For a wire-free module whose
    sole output port is `{name := out, expr := .var rn w}` and whose register list names `rn`, the
    real output map denotes exactly the register value — so the `Refines.obs` obligation against
    `specOut s _ := [(out, s.toNat)]` is mechanical.  `hnames` is discharged by `rfl` (the reg list
    is a literal). -/
theorem moore_obs {m : Module} {rn out : String} {w : Nat}
    (houts : m.outputs = [{ name := out, width := w, expr := .var rn w }])
    (hwires : m.wires = [])
    (hnames : m.regs.map (·.name) = [rn]) (r i : Env) :
    m.outputs?eval r i = [(out, (BitVec.ofNat w (r rn)).toNat)] := by
  simp only [Module.outputs?eval, houts, hwires, hnames, evalWires, List.foldl_nil,
             List.map_cons, List.map_nil, eval, Env.lookup]
  rw [cycleEnv_reg r i [rn] rn (by simp)]

/-- **The single-register L4 lift, over the full `Reg` record.**  Promote a single-register,
    wire-free module `m` to the *full* `Refines` (reset streams + legality + output observation),
    supplying only the L3 data plus one output-observation bridge:

    * `hshape` : `m.regs = [reg] ∧ m.wires = []` — `⟨rfl, rfl⟩`;
    * `hstep`  : the design's `next_correct`, re-aimed at `cycleEnv r i [reg.name]` (as in L3);
    * `hinit`  : `BitVec.ofNat reg.width (m.initRegs reg.name) = s0` — `rfl`/`by decide`;
    * `hobs`   : `m.outputs?eval r i = specOut (α r) i` — `moore_obs` for the Moore-output shape.

    `reset_inv`/`reset_α` are discharged internally (`reset_α` from `hinit`), so there is no separate
    reset obligation.  The abstraction is the same `α r = BitVec.ofNat reg.width (r reg.name)` as L3;
    invariant-free (`fun _ => True`). -/
theorem refines_single_rec (m : Module) (reg : Reg)
    (specN : BitVec reg.width → Env → BitVec reg.width)
    (specOut : BitVec reg.width → Env → List (String × Nat))
    (s0 : BitVec reg.width)
    (hshape : m.regs = [reg] ∧ m.wires = [])
    (hstep : ∀ r i : Env,
        eval reg.next (cycleEnv r i [reg.name]) = specN (BitVec.ofNat reg.width (r reg.name)) i)
    (hinit : BitVec.ofNat reg.width (m.initRegs reg.name) = s0)
    (hobs : ∀ r i : Env,
        m.outputs?eval r i = specOut (BitVec.ofNat reg.width (r reg.name)) i) :
    Refines m (fun r => BitVec.ofNat reg.width (r reg.name)) specN specOut s0 (fun _ => True) where
  init_inv  := trivial
  init_α    := hinit
  step_inv  := fun _ _ _ _ => trivial
  step_α    := by
    intro r i _ _
    show BitVec.ofNat reg.width ((m.step r i false) reg.name)
        = specN (BitVec.ofNat reg.width (r reg.name)) i
    rw [single_step_rec hshape.1 hshape.2 r i]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    exact hstep r i
  reset_inv := fun _ _ _ => trivial
  reset_α   := by
    intro r i _
    show BitVec.ofNat reg.width ((m.step r i true) reg.name) = s0
    rw [reset_step_rec hshape.1 r i, ← initRegs_single_rec hshape.1]
    exact hinit
  obs       := fun r i _ _ => hobs r i

/-- **The single-register L4 lift** (default `{name,width,next,init}` record).  Instance of
    `refines_single_rec`; the analogue of `simRefines_single`, additionally taking `hobs`
    (the output-observation bridge — `moore_obs` for the Moore shape).  `reset` is free. -/
theorem refines_single (m : Module) (rn : String) (w : Nat) (rnNext : Expr w) (i0 : BitVec w)
    (specN : BitVec w → Env → BitVec w)
    (specOut : BitVec w → Env → List (String × Nat)) (s0 : BitVec w)
    (hshape : m.regs = [{ name := rn, width := w, next := rnNext, init := i0 }] ∧ m.wires = [])
    (hstep : ∀ r i : Env, eval rnNext (cycleEnv r i [rn]) = specN (BitVec.ofNat w (r rn)) i)
    (hinit : BitVec.ofNat w (m.initRegs rn) = s0)
    (hobs : ∀ r i : Env, m.outputs?eval r i = specOut (BitVec.ofNat w (r rn)) i) :
    Refines m (fun r => BitVec.ofNat w (r rn)) specN specOut s0 (fun _ => True) :=
  refines_single_rec m { name := rn, width := w, next := rnNext, init := i0 } specN specOut s0
    hshape hstep hinit hobs

/-- **The single-register Moore L4 lift** — the batch-friendly form.  For the common counter/dff/
    shift shape where the sole output port IS the register (`outputs := [{name := out,
    expr := .var rn w}]`), `specOut` is fixed to `[(out, s.toNat)]` and the `obs` obligation is
    discharged internally via `moore_obs`.  The caller supplies EXACTLY the L3 data plus the output
    shape equality `houts` (`rfl`): an L3→L4 promotion at zero extra proof cost. -/
theorem refines_single_moore (m : Module) (rn out : String) (w : Nat) (rnNext : Expr w)
    (i0 : BitVec w) (specN : BitVec w → Env → BitVec w) (s0 : BitVec w)
    (hshape : m.regs = [{ name := rn, width := w, next := rnNext, init := i0 }] ∧ m.wires = [])
    (houts : m.outputs = [{ name := out, width := w, expr := .var rn w }])
    (hstep : ∀ r i : Env, eval rnNext (cycleEnv r i [rn]) = specN (BitVec.ofNat w (r rn)) i)
    (hinit : BitVec.ofNat w (m.initRegs rn) = s0) :
    Refines m (fun r => BitVec.ofNat w (r rn)) specN (fun s _ => [(out, s.toNat)]) s0
      (fun _ => True) :=
  refines_single m rn w rnNext i0 specN (fun s _ => [(out, s.toNat)]) s0 hshape hstep hinit
    (fun r i => moore_obs houts hshape.2
      (by rw [hshape.1]; rfl) r i)

/-! ## 7b. The single-register **L4** combinator with a GENERAL (Mealy/combinational) output

`refines_single_moore` (§7) discharges the `Refines.obs` obligation only for the **Moore
output=register** shape (`outputs := [{name := out, expr := .var rn w}]`).  A Mealy or
combinational-output FSM — `fsm` (`MATCH = f(state,IN,RST)`), `pulse_detect` (reset-gated Mealy),
`sequence_detector` (`sequence_detected = (state==S4)`) — has a *combinational* output PORT whose
expression is NOT the bare register variable, yet it carries an `output_correct`/`out_correct` lemma
(`eval outExpr env = specOut …`) proved with the *same* shape as `next_correct`.  This section makes
the L3→L4 promotion just as mechanical for that shape: the caller reuses `output_correct` to close one
extra bridge `hout` — the **output analogue of `hstep`**, discharged by the SAME `cycleEnv`→`env`
incantation — and the combinator assembles the full `Refines`.

`single_out_obs` is the general analogue of `moore_obs`: it reduces `Module.outputs?eval` for a
single-output, wire-free module to the bare `eval outExpr (cycleEnv r i [rn])`, leaving the caller's
`hout` to finish (whereas `moore_obs` bakes in the `.var rn w` register read).  `refines_single_out`
(and its `_rec` full-record variant) fold `single_out_obs` in, so the produced spec output is the
single port `fun s i => [(out, (outVal s i).toNat)]`.  `refines_single_moore` stays the
output=register special case; `refines_single`/`refines_single_rec` remain the fully general escape
hatch taking an arbitrary `specOut`/`hobs`. -/

/-- **The general single-output observation reduction** (analogue of `moore_obs`).  For a wire-free
    module whose sole output port is `{name := out, width := wo, expr := outExpr}` and whose register
    list names `rn`, `Module.outputs?eval` reduces to that one output evaluated under `cycleEnv r i
    [rn]` — no assumption on the *shape* of `outExpr` (Moore, Mealy, combinational; any width `wo`).
    The caller finishes with its design's `output_correct` (bridged `cycleEnv`→`env` as in `hstep`).
    `hnames` is `rfl` (the reg list is a literal). -/
theorem single_out_obs {m : Module} {rn out : String} {wo : Nat} {outExpr : Expr wo}
    (houts : m.outputs = [{ name := out, width := wo, expr := outExpr }])
    (hwires : m.wires = [])
    (hnames : m.regs.map (·.name) = [rn]) (r i : Env) :
    m.outputs?eval r i = [(out, (eval outExpr (cycleEnv r i [rn])).toNat)] := by
  simp only [Module.outputs?eval, houts, hwires, hnames, evalWires, List.foldl_nil,
             List.map_cons, List.map_nil]

/-- **The single-register L4 lift with a general (Mealy/combinational) output**, over the full `Reg`
    record.  Like `refines_single_rec`, but the caller does NOT hand-build `hobs`: they supply the
    output port shape `houts`, the abstract output value `outVal : S → Env → BitVec wo`, and the output
    bridge `hout` — the design's `output_correct` re-aimed at `cycleEnv r i [reg.name]`, i.e. the exact
    `hstep` incantation applied to the output expression.  The produced spec output is the single port
    `fun s i => [(out, (outVal s i).toNat)]`, and `hobs` is discharged internally via `single_out_obs`.
    Reset (`reset_α`) is free from `hinit` as in `refines_single_rec`; async/negedge records are fine
    (the register record is abstract). -/
theorem refines_single_out_rec (m : Module) (reg : Reg) (out : String) (wo : Nat) (outExpr : Expr wo)
    (specN : BitVec reg.width → Env → BitVec reg.width)
    (outVal : BitVec reg.width → Env → BitVec wo) (s0 : BitVec reg.width)
    (hshape : m.regs = [reg] ∧ m.wires = [])
    (houts : m.outputs = [{ name := out, width := wo, expr := outExpr }])
    (hstep : ∀ r i : Env,
        eval reg.next (cycleEnv r i [reg.name]) = specN (BitVec.ofNat reg.width (r reg.name)) i)
    (hinit : BitVec.ofNat reg.width (m.initRegs reg.name) = s0)
    (hout : ∀ r i : Env,
        eval outExpr (cycleEnv r i [reg.name]) = outVal (BitVec.ofNat reg.width (r reg.name)) i) :
    Refines m (fun r => BitVec.ofNat reg.width (r reg.name)) specN
      (fun s i => [(out, (outVal s i).toNat)]) s0 (fun _ => True) :=
  refines_single_rec m reg specN (fun s i => [(out, (outVal s i).toNat)]) s0 hshape hstep hinit
    (fun r i => by
      rw [single_out_obs (rn := reg.name) houts hshape.2 (by rw [hshape.1]; rfl) r i, hout r i])

/-- **The single-register L4 lift with a general output** (default `{name,width,next,init}` record).
    Instance of `refines_single_out_rec`; the combinational/Mealy-output analogue of
    `refines_single_moore`.  Caller supplies the L3 data (`hshape`/`hstep`/`hinit`) plus the output
    port shape `houts` and the output bridge `hout` (reusing the design's `output_correct`). -/
theorem refines_single_out (m : Module) (rn out : String) (w wo : Nat) (rnNext : Expr w)
    (outExpr : Expr wo) (i0 : BitVec w) (specN : BitVec w → Env → BitVec w)
    (outVal : BitVec w → Env → BitVec wo) (s0 : BitVec w)
    (hshape : m.regs = [{ name := rn, width := w, next := rnNext, init := i0 }] ∧ m.wires = [])
    (houts : m.outputs = [{ name := out, width := wo, expr := outExpr }])
    (hstep : ∀ r i : Env, eval rnNext (cycleEnv r i [rn]) = specN (BitVec.ofNat w (r rn)) i)
    (hinit : BitVec.ofNat w (m.initRegs rn) = s0)
    (hout : ∀ r i : Env, eval outExpr (cycleEnv r i [rn]) = outVal (BitVec.ofNat w (r rn)) i) :
    Refines m (fun r => BitVec.ofNat w (r rn)) specN (fun s i => [(out, (outVal s i).toNat)]) s0
      (fun _ => True) :=
  refines_single_out_rec m { name := rn, width := w, next := rnNext, init := i0 } out wo outExpr
    specN outVal s0 hshape houts hstep hinit hout

/-! ## 8. L4 whole-trace / observable corollaries (resetful)

The `Refines` payoffs, handed to a caller without threading `.trace … |>.2` / `.observe` by hand.
Both quantify over arbitrary input AND reset streams (of legal inputs). -/

/-- **Resetful whole-trace, through `α`.**  Given any `Refines`, at every cycle `t` of a run under
    arbitrary legal inputs and an arbitrary reset stream, the abstracted register state equals the
    resetful abstract trace `specTraceR`. -/
theorem refinesTrace_through_α {m : Module} {S : Type _} {α : Env → S} {specStep specOut s0 inv}
    (h : Refines m α specStep specOut s0 inv) (inputs : Nat → Env) (reset : Nat → Bool)
    (hleg : ∀ t, m.LegalInputs (inputs t)) (t : Nat) :
    α (regTrace m inputs reset t) = specTraceR specStep s0 inputs reset t :=
  (h.trace inputs reset hleg t).2

/-- **Resetful observable correctness.**  The impl's real output ports match the spec's outputs on
    the resetful abstract trace — every cycle, all legal input streams, all reset streams. -/
theorem observe_through_α {m : Module} {S : Type _} {α : Env → S} {specStep specOut s0 inv}
    (h : Refines m α specStep specOut s0 inv) (inputs : Nat → Env) (reset : Nat → Bool)
    (hleg : ∀ t, m.LegalInputs (inputs t)) (t : Nat) :
    m.outputs?eval (regTrace m inputs reset t) (inputs t)
      = specOut (specTraceR specStep s0 inputs reset t) (inputs t) :=
  h.observe inputs reset hleg t

/-! ## 9. The multi-register **L4** combinators (`refines_pair` / `refines_triple`)

`simRefines_pair`/`simRefines_triple` (§5) lift a multi-register design to the reset-free,
output-blind L3 `SimRefines`.  `refines_pair`/`refines_triple` are their **L4 `Refines`** analogues
— the multi-register counterparts of `refines_single`/`refines_single_moore` (§7).  They take the
SAME per-register step bridges `h1`/`h2`[/`h3`] that `simRefines_pair`/`simRefines_triple` take, and
add exactly the three L4 obligations, all *free* from data the L3 lift already produced:

* **reset** — the per-register reductions `hrst1`/`hrst2`[/`hrst3`], each
  `(m.step r i true) rnₖ = m.initRegs rnₖ`, discharged by `fun _ _ => rfl` (a reset cycle loads every
  register's `init`, which is exactly what `m.initRegs` reads back — `step_reset_initRegs`).  With
  `hinit` these make `reset_α` free, so `Refines.trace` quantifies over ALL reset streams, not just
  the never-reset one;
* **observation** — the bridge `hobs` (`∀ r i, m.outputs?eval r i = specOut (α r) i`): the impl's real
  output PORTS denote the spec outputs on the abstracted tuple.  Use `moore_obs_mem` when the sole
  output IS one of the registers; a direct `Module.outputs?eval` reduction (or the design's
  `output_correct`) for multi-output / combinational-slice ports;
* **legality** — available but unused, since the L3 bridges are unconditional (matching the counters
  the whole batch validates on).

`step_α` reuses `h1`/`h2`[/`h3`] verbatim, exactly as `simRefines_pair`/`simRefines_triple` do (the
natural `= <raw spec>` bridge is accepted where `(specStep (α r) i).k` is expected — `specStep` is a
literal `Prod.mk`).  For a design whose only *public* L3 artifact is the aggregate
`SimRefines`/tuple-`hstep`, project the per-register bridges with `congrArg (·.1) (h.step_α r i trivial)`
etc. (the tuple `α`'s projections are the register bridges by defeq).  n > 3 registers stay on the
`simRefines_triv` + tuple template (§5); these two packagings cover the 2–3 register corpus. -/

/-- **Reset-cycle per-register reduction to `initRegs`** (the multi-register analogue of
    `reset_step_rec`, keyed on `find?` rather than a singleton reg list).  On a reset cycle
    `Module.step r i true` loads register `rn` to `r.init`, which is exactly what `m.initRegs rn`
    reads back; `hfind` (`rfl` on a literal reg list) drives it.  This is what makes
    `refines_pair`/`refines_triple`'s `reset_α` free — though the caller-facing obligation is stated
    directly as `(m.step r i true) rn = m.initRegs rn`, itself dischargeable by a bare `rfl`.

    TEMPLATE — no current in-tree caller (callers discharge the reset obligation by a bare `rfl`, as
    the §7/§8 prose notes).  Kept as the named multi-register reset reduction referenced by that
    prose. -/
theorem step_reset_initRegs {m : Module} {rn : String} {reg : Reg}
    (hfind : m.regs.find? (·.name = rn) = some reg) (r i : Env) :
    (m.step r i true) rn = m.initRegs rn := by
  simp only [Module.step, Module.initRegs, hfind, if_true]

/-- **Moore observation, over a MULTI-register module** (the `find?`-free generalisation of
    `moore_obs`).  For a wire-free module whose sole output port is `{name := out, expr := .var rn w}`
    and whose register list *contains* `rn` (need not be a singleton), the real output map denotes the
    register value.  `hmem` — `(m.regs.map (·.name)).contains rn = true` — is discharged by `by decide`
    (the reg list is a literal).  Lets a 2–3 register design whose single output IS one of the
    registers (`Prob054`/`Prob045`/`Prob066` edge detectors) discharge `hobs` mechanically. -/
theorem moore_obs_mem {m : Module} {rn out : String} {w : Nat}
    (houts : m.outputs = [{ name := out, width := w, expr := .var rn w }])
    (hwires : m.wires = [])
    (hmem : (m.regs.map (·.name)).contains rn = true) (r i : Env) :
    m.outputs?eval r i = [(out, (BitVec.ofNat w (r rn)).toNat)] := by
  simp only [Module.outputs?eval, houts, hwires, evalWires, List.foldl_nil,
             List.map_cons, List.map_nil, eval, Env.lookup,
             cycleEnv_reg r i (m.regs.map (·.name)) rn hmem]

/-- **The two-register L4 lift.**  `α r = (BitVec.ofNat w₁ (r rn₁), BitVec.ofNat w₂ (r rn₂))`; the L4
    `Refines` analogue of `simRefines_pair`.  Caller supplies the two per-register step bridges
    (`h1`/`h2`, exactly as for `simRefines_pair`), `hinit`, the two reset reductions (`hrst1`/`hrst2`,
    `fun _ _ => rfl`), and the observation bridge `hobs`.  `reset_α` is derived from `hinit`;
    invariant-free. -/
theorem refines_pair (m : Module) (rn1 rn2 : String) (w1 w2 : Nat)
    (specStep : (BitVec w1 × BitVec w2) → Env → BitVec w1 × BitVec w2)
    (specOut : (BitVec w1 × BitVec w2) → Env → List (String × Nat))
    (s0 : BitVec w1 × BitVec w2)
    (hinit : (BitVec.ofNat w1 (m.initRegs rn1), BitVec.ofNat w2 (m.initRegs rn2)) = s0)
    (h1 : ∀ r i : Env, BitVec.ofNat w1 ((m.step r i false) rn1)
        = (specStep (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2)) i).1)
    (h2 : ∀ r i : Env, BitVec.ofNat w2 ((m.step r i false) rn2)
        = (specStep (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2)) i).2)
    (hrst1 : ∀ r i : Env, (m.step r i true) rn1 = m.initRegs rn1)
    (hrst2 : ∀ r i : Env, (m.step r i true) rn2 = m.initRegs rn2)
    (hobs : ∀ r i : Env,
        m.outputs?eval r i = specOut (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2)) i) :
    Refines m (fun r => (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2))) specStep specOut s0
      (fun _ => True) where
  init_inv  := trivial
  init_α    := hinit
  step_inv  := fun _ _ _ _ => trivial
  step_α    := by
    intro r i _ _
    show (BitVec.ofNat w1 ((m.step r i false) rn1), BitVec.ofNat w2 ((m.step r i false) rn2)) = _
    rw [h1 r i, h2 r i]
  reset_inv := fun _ _ _ => trivial
  reset_α   := by
    intro r i _
    show (BitVec.ofNat w1 ((m.step r i true) rn1), BitVec.ofNat w2 ((m.step r i true) rn2)) = s0
    rw [hrst1 r i, hrst2 r i]; exact hinit
  obs       := fun r i _ _ => hobs r i

/-- **The three-register L4 lift.**  `α r = (BitVec.ofNat w₁ (r rn₁), BitVec.ofNat w₂ (r rn₂),
    BitVec.ofNat w₃ (r rn₃))`; the L4 `Refines` analogue of `simRefines_triple`.  Same shape as
    `refines_pair` with a third register (`h3`/`hrst3`).  Covers 3-register edge detectors
    (`edge_detect`), 3-digit ripple counters (`calendar`), etc. -/
theorem refines_triple (m : Module) (rn1 rn2 rn3 : String) (w1 w2 w3 : Nat)
    (specStep : (BitVec w1 × BitVec w2 × BitVec w3) → Env → BitVec w1 × BitVec w2 × BitVec w3)
    (specOut : (BitVec w1 × BitVec w2 × BitVec w3) → Env → List (String × Nat))
    (s0 : BitVec w1 × BitVec w2 × BitVec w3)
    (hinit : (BitVec.ofNat w1 (m.initRegs rn1), BitVec.ofNat w2 (m.initRegs rn2),
              BitVec.ofNat w3 (m.initRegs rn3)) = s0)
    (h1 : ∀ r i : Env, BitVec.ofNat w1 ((m.step r i false) rn1)
        = (specStep (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2), BitVec.ofNat w3 (r rn3)) i).1)
    (h2 : ∀ r i : Env, BitVec.ofNat w2 ((m.step r i false) rn2)
        = (specStep (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2), BitVec.ofNat w3 (r rn3)) i).2.1)
    (h3 : ∀ r i : Env, BitVec.ofNat w3 ((m.step r i false) rn3)
        = (specStep (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2), BitVec.ofNat w3 (r rn3)) i).2.2)
    (hrst1 : ∀ r i : Env, (m.step r i true) rn1 = m.initRegs rn1)
    (hrst2 : ∀ r i : Env, (m.step r i true) rn2 = m.initRegs rn2)
    (hrst3 : ∀ r i : Env, (m.step r i true) rn3 = m.initRegs rn3)
    (hobs : ∀ r i : Env, m.outputs?eval r i
        = specOut (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2), BitVec.ofNat w3 (r rn3)) i) :
    Refines m
      (fun r => (BitVec.ofNat w1 (r rn1), BitVec.ofNat w2 (r rn2), BitVec.ofNat w3 (r rn3)))
      specStep specOut s0 (fun _ => True) where
  init_inv  := trivial
  init_α    := hinit
  step_inv  := fun _ _ _ _ => trivial
  step_α    := by
    intro r i _ _
    show (BitVec.ofNat w1 ((m.step r i false) rn1), BitVec.ofNat w2 ((m.step r i false) rn2),
          BitVec.ofNat w3 ((m.step r i false) rn3)) = _
    rw [h1 r i, h2 r i, h3 r i]
  reset_inv := fun _ _ _ => trivial
  reset_α   := by
    intro r i _
    show (BitVec.ofNat w1 ((m.step r i true) rn1), BitVec.ofNat w2 ((m.step r i true) rn2),
          BitVec.ofNat w3 ((m.step r i true) rn3)) = s0
    rw [hrst1 r i, hrst2 r i, hrst3 r i]; exact hinit
  obs       := fun r i _ _ => hobs r i

/-! ## 10. The invariant-free N-tuple **L4** combinator (`refines_triv`)

`simRefines_triv` (§3) is the invariant-free N-tuple *L3* packaging: for a design that needs no
gluing invariant it turns `init_α` + the commuting square `step_α` into a `SimRefines`.  `refines_triv`
is its **L4 twin** — the invariant-free N-tuple analogue of `refines_pair`/`refines_triple` (§9) for
ANY register arity (4, 5, 6, 8, …), where there is no fixed-arity combinator.  It promotes a design
straight to the full `Refines` (reset streams + boundary-legality + output observation) from four
pieces the design already has or gets for free:

* **`hinit`** — `α m.initRegs = s0` (the L3 `init_α`, `rfl`/`by decide`);
* **`hstep`** — `∀ r i, α (m.step r i false) = specStep (α r) i`: the L3 commuting square VERBATIM.
  A design whose `*Trace.lean` already proves `refines : SimRefines m α specStep s0 (fun _=>True)`
  hands this over as `fun r i => refines.step_α r i trivial` — no re-derivation of the big tuple
  bridge, the whole point of this combinator on 5- and 8-tuples;
* **`hreset`** — `∀ r i, α (m.step r i true) = s0`: FREE.  A framework sync-reset step reloads every
  register's `init` (`Module.step _ _ true` takes the `r.init` branch — see `reset_step_rec`/
  `step_reset_initRegs`), which is exactly what `m.initRegs` reads back, so `α (m.step r i true)` is
  defeq `α m.initRegs = s0`; the caller discharges it with `fun _ _ => rfl`.  (These designs carry
  their *real* reset in-band on an `rst`/`rst_n`/`reset` input, handled inside `hstep`; `hreset`
  covers the framework's out-of-band sync-reset path, which merely reloads `init`.)
* **`hobs`** — `∀ r i, m.outputs?eval r i = specObs (α r) i`: the impl's real output PORTS denote the
  spec's outputs on the abstracted tuple (anti-cheat gate #3).  Moore ports (`.var rn w`) reduce by a
  direct `Module.outputs?eval` unfold with `cycleEnv_reg`; combinational-slice/mux ports unfold over
  their expressions; the design's own `output_correct` closes a Mealy port.

All three L4-specific obligations beyond `hstep` are thus mechanical.  `refines_pair`/`refines_triple`
remain the 2- and 3-tuple packagings that additionally *build* `α`; `refines_triv` takes the design's own
tuple `α` and is arity-agnostic — the batch tool for the 4-to-8-register wave. -/
theorem refines_triv (m : Module) {S : Type _} (α : Env → S) (specStep : S → Env → S)
    (specObs : S → Env → List (String × Nat)) (s0 : S)
    (hinit : α m.initRegs = s0)
    (hstep : ∀ r i : Env, α (m.step r i false) = specStep (α r) i)
    (hreset : ∀ r i : Env, α (m.step r i true) = s0)
    (hobs : ∀ r i : Env, m.outputs?eval r i = specObs (α r) i) :
    Refines m α specStep specObs s0 (fun _ => True) where
  init_inv  := trivial
  init_α    := hinit
  step_inv  := fun _ _ _ _ => trivial
  step_α    := fun r i _ _ => hstep r i
  reset_inv := fun _ _ _ => trivial
  reset_α   := fun r i _ => hreset r i
  obs       := fun r i _ _ => hobs r i

end LeanRTL.Designs.WholeDesign.Lift

/-! ## Folded from HWLib (M31f) — wire-free single-step reductions.
    Kept under the original `LeanRTL.HWLib` namespace so existing qualified refs survive. -/
namespace LeanRTL.HWLib
open LeanRTL

/-! ## Pattern: per-step register reduction (the most-reused proof step)

Every sequential design's per-step proof reduces `(m.step …) regName` to "evaluate the register's
`next` expression in this cycle's environment".  Proven once here for wire-free modules, so designs
stop hand-rolling it.

NOTE (2026-07-16 prune): `regStepWF` / `regResetWF` have no *current* in-tree caller (the α-readout
wrappers that used them were pruned with `Lib/Refine/Alpha.lean`), but they are the documented
per-step plumbing cited by `docs/AGENT_GUIDE.md` and the α-shape catalog skill, so they stay here as
the canonical wire-free step/reset laws for the next sequential design to reuse. -/

/-- For a **wire-free** module, one non-reset step of register `rg` is exactly its `next` expression
    evaluated in the current cycle's environment. -/
theorem regStepWF (m : Module) (hw : m.wires = []) (regVals inputs : Env) (rg : Reg)
    (hfind : m.regs.find? (fun r => r.name = rg.name) = some rg) :
    (m.step regVals inputs false) rg.name
      = (eval rg.next (cycleEnv regVals inputs (m.regs.map (·.name)))).toNat := by
  simp [Module.step, hw, evalWires, hfind]

/-- For a wire-free module, a reset step puts register `rg` at its `init`. -/
theorem regResetWF (m : Module) (regVals inputs : Env) (rg : Reg)
    (hfind : m.regs.find? (fun r => r.name = rg.name) = some rg) :
    (m.step regVals inputs true) rg.name = rg.init.toNat := by
  simp [Module.step, hfind]

end LeanRTL.HWLib

