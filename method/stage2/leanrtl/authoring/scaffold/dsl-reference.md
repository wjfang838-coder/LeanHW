# LeanRTL DSL Reference

The standalone reference for **how a LeanRTL design is written** — the abstract syntax you
author, field by field. This is the language reference that complements the *capability
matrix* in [`docs/instructions/CORE.md`](instructions/CORE.md) (which tells you *which* feature
maps to *which* field) and the proof skills in [`docs/skills/`](skills/INDEX.md) (which tell you
how to *prove* what you wrote).

Everything here is quoted from the two authoritative sources:

* [`LeanRTL/Core/Syntax.lean`](../LeanRTL/Core/Syntax.lean) — the AST (the grammar).
* [`LeanRTL/Core/DSL.lean`](../LeanRTL/Core/DSL.lean) — the surface sugar / smart constructors and
  their proven `eval`-laws.

Every field name, constructor, and `example:` path below was grep-verified against the repo.

---

## 1. Orientation

LeanRTL is a **deep-embedded HDL**: a piece of hardware is not text to be parsed — it is a Lean
**data value**. You build a `Module` (a plain Lean structure literal), and that value *is* the
circuit. Three things then act on it:

* **Meaning.** [`LeanRTL/Core/Semantics.lean`](../LeanRTL/Core/Semantics.lean) gives the AST a
  denotational reading over `BitVec`: `eval : Expr w → Env → BitVec w` interprets a combinational
  expression, `Module.step` advances every register one clock, `Module.simulate` runs a whole trace.
  This is what your spec and proofs talk about.
* **Compilation.** [`LeanRTL/Core/Compiler.lean`](../LeanRTL/Core/Compiler.lean) lowers the *same*
  AST to RTLIL cells (`compile : Module → Backend.Design`), and this lowering is itself proven
  correct (the `compile_correct` family). Yosys then turns RTLIL into Verilog.
* **Widths are types.** `Expr` is indexed by its bit width (`Expr : Nat → Type`), so a width
  mismatch is a Lean *type error* caught at the very first verification layer — before any theorem.

The authoring loop is therefore: **author a `Module` → state a spec → prove it → lower it to
RTLIL → emit Verilog.** You never write Verilog by hand; the proven compiler (or a miter-anchored
emitter) produces it.

---

## 2. The core types

All types live in `namespace LeanRTL` in `Core/Syntax.lean`. Open it with `open LeanRTL`.

### 2.1 `Expr : Nat → Type` — combinational, word-level expressions

An `Expr w` is a fixed-width combinational value. Its width `w : Nat` is part of its Lean type.
The full constructor list is in §3; the two you touch constantly are:

```lean
def wire (name : String) (w : Nat) : Expr w := .var name w   -- reference a signal by name
def bit (b : Bool) : Expr 1 := .const (if b then 1 else 0)   -- 1-bit literal
```

`.var "count" 4` reads the 4-bit signal named `count`; `.const (2 : BitVec 4)` is a literal.
References are **by name** — a register, input, or wire is reached by writing its name, which is
why signal names are load-bearing (see CORE.md §2.1).

### 2.2 `InPort` / `OutPort` — ports

```lean
structure InPort where
  name  : String
  width : Nat

structure OutPort where
  name  : String
  width : Nat
  expr  : Expr width      -- the combinational driver of this output
```

An output carries its own **driving expression** `expr`. This is the combinational-vs-sequential
seam: a *pure combinational* module puts all its logic in `OutPort.expr` and has no registers
(`example:` [`LeanRTL/Designs/Rtllm/Adder8bit.lean`](../LeanRTL/Designs/Rtllm/Adder8bit.lean) —
`sum`/`cout` are just `expr`s of the inputs, `regs = []`, `clock = none`).

### 2.3 `Reg` — a clocked register (sequential state)

```lean
structure Reg where
  name       : String
  width      : Nat
  next       : Expr width                              -- the D-input (next-state) cone
  init       : BitVec width                            -- power-on / synchronous-reset value
  asyncReset : Option (String × BitVec width) := none  -- F4  → $adff
  negedge    : Bool                            := false -- F1  → $dff CLK_POLARITY=0
  asyncLoad  : Option (String × Bool × Expr width) := none -- F6 → $aldff
  clockNet   : Option (Expr 1)                 := none  -- F11 → per-register clock
```

A register is the unit of sequential state: on each active clock edge it latches `eval next`.
`next` may reference inputs, wires, and *other registers* (including itself, for hold/feedback) by
name; `init` is both the power-on value and, for a synchronous reset, the value the reset folds to.
The four `Option`/`Bool` fields default so that a plain `{ name, width, next, init }` literal is an
ordinary posedge `$dff` — every advanced flavour is opt-in (§4).

```lean
-- example: LeanRTL/Designs/Examples/Counter/Impl.lean
def nextCount : Expr 4 := .add (.var "count" 4) (.const 2)
regs := [{ name := "count", width := 4, next := nextCount, init := 0 }]
```

### 2.4 `Wire` — an internal combinational signal

```lean
structure Wire where
  name  : String
  width : Nat
  expr  : Expr width
```

A wire binds `name` to `eval expr`. Wires give a module a **word-level RTL shape**: each coarse
cell becomes one named, shared signal instead of a duplicated expression tree — essential for large
or imported designs. The `wires` list must be **topologically ordered**: each `expr` may reference
only inputs, registers, and *earlier* wires.

```lean
-- example: LeanRTL/Designs/Cvdp/CvdpSetBitCalculator0001.lean
wires := [{ name := "not_rst_n", width := 1, expr := .not (.var "i_rst_n" 1) }]
```

> Authoring note: for **agentic sequential** designs, keep `wires := []` and inline the cones into
> each register's `next` (CORE.md §2.8) — the procedural emitter's X-safety only covers next-state
> cones, not module-level continuous assigns.

### 2.5 `Module` — the unit you author

```lean
structure Module where
  name    : String
  inputs  : List InPort
  outputs : List OutPort
  wires   : List Wire     := []
  regs    : List Reg      := []
  latches : List Latch    := []
  mems    : List MemBlock := []
  clock   : Option String := none    -- clock input name; present ⇔ sequential
  reset   : Option String := none    -- optional synchronous active-high reset input
```

A **combinational** module leaves `regs = []` and `clock = none` (all logic in `OutPort.expr`).
A **sequential** module sets `clock := some "<clkname>"` and populates `regs`. `reset := some "..."`
opts into the framework's synchronous reset path; `reset := none` with a non-zero `init` is the
power-on-init / async-reset style (§4, F7/F4).

```lean
-- example: LeanRTL/Designs/Examples/Counter/Impl.lean
def impl : Module :=
  { name    := "Counter"
    inputs  := [{ name := "clk", width := 1 }, { name := "rst", width := 1 }]
    outputs := [{ name := "q", width := 4, expr := .var "count" 4 }]
    regs    := [{ name := "count", width := 4, next := nextCount, init := 0 }]
    clock   := some "clk"
    reset   := some "rst" }
```

### 2.6 `Latch` — a level-sensitive transparent latch (F8)

```lean
structure Latch where
  name   : String
  width  : Nat
  enable : Expr 1        -- transparent (q follows d) while high, holds while low
  d      : Expr width
```

Unlike a `Reg`, a latch has **no clock edge**: its next-value law is `q' = if enable then d else q`
(pinned by `Latch.den` in `Core/Semantics.lean`). Lowers to a Yosys `$dlatch`.

```lean
-- example: LeanRTL/Designs/VEval/Prob028M2014Q4a.lean
def latchQ : Latch := { name := "q", width := 1, enable := .var "ena" 1, d := .var "d" 1 }
-- placed in the module as:  latches := [ latchQ ]
```

### 2.7 `MemBlock` — an addressed memory array (SRAM/RAM)

```lean
structure MemWrite (aw dw : Nat) where
  clock : Expr 1         -- the memory samples writes on this net's positive edge
  en    : Expr 1
  addr  : Expr aw
  data  : Expr dw

structure MemRead (aw : Nat) where
  addr : Expr aw
  out  : String          -- fresh net name driven by mem[addr]; referenced via .var out dw

structure MemBlock where
  name      : String
  addrWidth : Nat
  dataWidth : Nat
  writes    : List (MemWrite addrWidth dataWidth) := []
  reads     : List (MemRead addrWidth)            := []
```

A `MemBlock` models a real `reg [dw-1:0] mem [0:2^aw-1]` array — one `$mem_v2` cell, not thousands
of `$dff`s — with synchronous `writes` and asynchronous (combinational) `reads`. A read port
drives a fresh net `out` that the rest of the module reads as `.var out dataWidth`. Its behaviour
is pinned per-access by `MemBlock.read_after_write` in `Core/MemSemantics.lean`.

```lean
-- example: LeanRTL/Designs/WholeDesign/RamExample.lean
def wr0 : MemWrite 4 8 :=
  { clock := .var "clk" 1, en := .var "we" 1, addr := .var "waddr" 4, data := .var "wdata" 8 }
def rd0 : MemRead 4 := { addr := .var "raddr" 4, out := "rout" }
def ram : MemBlock := { name := "ram", addrWidth := 4, dataWidth := 8, writes := [wr0], reads := [rd0] }
-- module:  mems := [ ram ] ,  and an output  { name := "rdata", width := 8, expr := .var "rout" 8 }
```

### 2.8 `Parent` / `Inst` — one level of hierarchy (F10)

```lean
structure Inst where
  instName : String
  child    : Module
  ins      : List (String × AnyExpr)   -- child input port ↦ parent-side expression

structure Parent where
  name    : String
  inputs  : List InPort
  insts   : List Inst
  outputs : List OutPort               -- may reference "<inst>.<port>" as var
  clock   : Option String := none      -- present ⇔ sequential hierarchy
  reset   : Option String := none
```

A `Parent` instantiates leaf `Module`s. Each `Inst` maps the child's input ports to parent-side
expressions (`ins`), and the child's outputs become parent signals named `"<instName>.<portName>"`
(read them with `.var "u_ctrl.run" 1`). Children may be combinational or **sequential**: a clocked
child's `clk`/`rst` are ordinary parent inputs threaded in through `ins` (e.g.
`("clk", anyExpr (.var "clk" 1))`), and `Parent.clock`/`Parent.reset` name the parent's own
clock/reset for the sequential flattening. `anyExpr` packs an `Expr w` into the width-erased
`AnyExpr := Σ w, Expr w` the port map needs.

```lean
-- example: LeanRTL/Designs/Examples/SeqHierTest/Impl.lean
{ instName := "u_cnt", child := counter,
  ins := [("clk", anyExpr (.var "clk" 1)),
          ("rst", anyExpr (.var "rst" 1)),
          ("en",  anyExpr (.var "u_ctrl.run" 1))] }   -- cross-instance wiring
```

---

## 3. Expression constructors

### 3.1 Core `Expr` cases (from `Core/Syntax.lean`)

All widths are checked by Lean's type-checker. `w`, `k`, `a`, `b` are `Nat` width parameters.

| Constructor | Signature | Meaning |
|---|---|---|
| `.const v` | `BitVec w → Expr w` | literal bit-vector |
| `.var n w` | `String → (w:Nat) → Expr w` | reference a signal by name |
| `.not a` | `Expr w → Expr w` | bitwise NOT |
| `.and a b` / `.or a b` / `.xor a b` | `Expr w → Expr w → Expr w` | bitwise AND / OR / XOR |
| `.add a b` / `.sub a b` | `Expr w → Expr w → Expr w` | add / subtract (mod 2ʷ) |
| `.mul a b` | `Expr w → Expr w → Expr w` | multiply, truncated to `w` |
| `.shl a b` / `.shr a b` | `Expr w → Expr k → Expr w` | logical left / (zero-fill) right shift by unsigned count |
| `.sshr a b` | `Expr w → Expr k → Expr w` | arithmetic (sign-extending) right shift |
| `.udiv a b` / `.umod a b` | `Expr w → Expr w → Expr w` | unsigned division / remainder |
| `.eq a b` | `Expr w → Expr w → Expr 1` | unsigned equality (1 bit) |
| `.ult a b` | `Expr w → Expr w → Expr 1` | unsigned less-than |
| `.slt a b` | `Expr w → Expr w → Expr 1` | **signed** (two's-complement) less-than |
| `.mux s a b` | `Expr 1 → Expr w → Expr w → Expr w` | `if s = 1 then a else b` |
| `.concat hi lo` | `Expr a → Expr b → Expr (a+b)` | concatenate (`hi` in high bits) |
| `.zext k a` | `(k:Nat) → Expr w → Expr (w+k)` | zero-extend by `k` bits |
| `.sext k a` | `(k:Nat) → Expr w → Expr (w+k)` | sign-extend by `k` bits |
| `.extract i a` | `(i:Nat) → Expr w → Expr 1` | single bit at index `i` (LSB = 0) |
| `.slice lo len a` | `(lo len:Nat) → Expr w → Expr len` | contiguous field of `len` bits from bit `lo` |

Note the two `.mux` idioms for control: a raw `.mux cond t e`, and the in-band reset fold
`.mux (.eq (.var "rst_n" 1) (.const 0)) <resetVal> <normal>` (CORE.md §2.2).

### 3.2 DSL sugar (from `Core/DSL.lean`) — smart constructors with proven `eval`-laws

Each of these **desugars to the proven core** (`.mux`/`.or`/`.shr`/…), so it inherits
`compile_correct` for free *and* ships a packaged `eval`-law you cite in your proof instead of
re-deriving the mux reasoning.

| Constructor | Expands to | `eval`-law | Typical use |
|---|---|---|---|
| `ifE c t e` | `.mux c t e` | `ifE_eval` | if-then-else |
| `caseE branches dflt` | right-nested `.mux` chain (first match wins) | `caseE_eval` | priority case / FSM decode |
| `arraySelect idx elems dflt` | address-`mux` over the element list | `arraySelect_eval` | ROM / LUT / S-box lookup |
| `fsmNext stateVar table` | `caseE` over the current state | `fsmNext_eval` | Moore FSM next-state |
| `rotateRightE e n` / `rotateLeftE e n` | `.or (.shr…) (.shl…)` | `rotrE_eval` / `rotlE_eval` (+ `rotCount_exact`) | SHA/AES/cipher rotates |
| `regFile name depth width awidth we waddr wdata readPorts` | ordinary `Reg`s + read-`Wire`s | (via `arraySelect_eval`) | register file / small RAM |

Real usages:

* `caseE` — `example:` [`LeanRTL/Designs/Cvdp/CvdpVendingMachine0001.lean`](../LeanRTL/Designs/Cvdp/CvdpVendingMachine0001.lean)
* `arraySelect` — `example:` [`LeanRTL/Designs/Rtllm/ROM.lean`](../LeanRTL/Designs/Rtllm/ROM.lean)
* `rotateLeftE` (with `rotlE_eval`/`rotCount_exact`) — `example:` [`LeanRTL/Designs/CvdpAgentic/Cipher.lean`](../LeanRTL/Designs/CvdpAgentic/Cipher.lean)
* `regFile` — `example:` [`LeanRTL/Designs/Examples/Scratchpad/Impl.lean`](../LeanRTL/Designs/Examples/Scratchpad/Impl.lean)

`fsmNext` is defined in `Core/DSL.lean` and re-exported through `LeanRTL/Lib/HWLib.lean`; use it
with its `fsmNext_eval` law. `regFile` returns `(regs, readWires)` to splice into a module's
`regs`/`wires`, and its auto-param `depth ≤ 2^awidth` rejects aliasing address shapes at
elaboration.

---

## 4. How to express each hardware feature

This mirrors the capability matrix in CORE.md §1, but as a *language* reference: feature → the exact
field to set → what it lowers to → a real design. The default `{ name, width, next, init }` register
is a **posedge `$dff`**; every row below is an opt-in field.

| Feature | DSL field you set | Lowers to | Example design |
|---|---|---|---|
| **Combinational output** | `OutPort.expr` (no `regs`, `clock := none`) | continuous assign | [`Rtllm/Adder8bit.lean`](../LeanRTL/Designs/Rtllm/Adder8bit.lean) |
| **Posedge register** | `Reg { next, init }` (defaults) + `Module.clock := some c` | `$dff` `always @(posedge c)` | [`Examples/Counter/Impl.lean`](../LeanRTL/Designs/Examples/Counter/Impl.lean) |
| **Negedge register** (F1) | `Reg.negedge := true` | `$dff` `CLK_POLARITY = 0` → `always @(negedge clk)` | [`VEval/Prob046Dff8p.lean`](../LeanRTL/Designs/VEval/Prob046Dff8p.lean) |
| **Synchronous reset (in-band)** | fold `.mux (reset cond) <rstVal> <normal>` into `next`; `Module.reset` may be `some`/`none` | `$dff` + mux | [`Rtllm/Counter12.lean`](../LeanRTL/Designs/Rtllm/Counter12.lean) (active-low, `reset := none`) |
| **Asynchronous reset** (F4) | `Reg.asyncReset := some (net, val)` (add a wire `net = ~rst_n` if active-low) | `$adff` `always @(posedge clk, negedge rst_n)` | [`Cvdp/CvdpSetBitCalculator0001.lean`](../LeanRTL/Designs/Cvdp/CvdpSetBitCalculator0001.lean) |
| **Async load of a dynamic value** (F6) | `Reg.asyncLoad := some (net, activeHi, expr)` | `$aldff` (`CLK`+`ALOAD`+async data) | [`Cvdp/CvdpLfsr8bit0001.lean`](../LeanRTL/Designs/Cvdp/CvdpLfsr8bit0001.lean) |
| **Power-on init, no reset** (F7) | `Reg.init := <v>` + `Module.reset := none` | RTLIL `\init` → `initial q = <v>` | [`VEval/Prob107Fsm1s.lean`](../LeanRTL/Designs/VEval/Prob107Fsm1s.lean) |
| **Gated / second / derived clock** (F11) | `Reg.clockNet := some (expr : Expr 1)` | that `$dff`/`$adff` clocked off `eval expr` | [`Cvdp/CvdpApbHistoryShiftRegister0001.lean`](../LeanRTL/Designs/Cvdp/CvdpApbHistoryShiftRegister0001.lean) |
| **Transparent latch** (F8) | `Module.latches := [ Latch {enable, d} ]` | `$dlatch` `always @(*) if (en) q = d;` | [`VEval/Prob028M2014Q4a.lean`](../LeanRTL/Designs/VEval/Prob028M2014Q4a.lean) |
| **Addressed memory (SRAM/RAM)** | `Module.mems := [ MemBlock {writes, reads} ]` | one `$mem_v2` cell | [`WholeDesign/RamExample.lean`](../LeanRTL/Designs/WholeDesign/RamExample.lean) |
| **Parametric width / constant** (F2) | a `def implGen (…) : Module` family + `def paramMeta : ParamMeta` | parametric SystemVerilog (`leanrtl pverilog`) | §6.1 below; `AGENT.md` for when to reach for it |
| **Sequential multi-module hierarchy** (F10) | `Parent { insts, ins, clock, reset }` | `compileParent` → real module instantiations | [`Examples/SeqHierTest/Impl.lean`](../LeanRTL/Designs/Examples/SeqHierTest/Impl.lean) |

Concrete field snippets (all verbatim from the cited files):

```lean
-- F1 negedge  (VEval/Prob046Dff8p.lean)
regs := [ { name := "q", width := 8, next := qNext, init := 0x34, negedge := true } ]

-- F4 async reset  (Cvdp/CvdpSetBitCalculator0001.lean)
wires := [ { name := "not_rst_n", width := 1, expr := .not (.var "i_rst_n" 1) } ]
regs  := [ { name := "o_set_bit_count", width := 8, next := countNext, init := 0,
             asyncReset := some ("not_rst_n", (0 : BitVec 8)) } ]

-- F6 async load of a dynamic value  (Cvdp/CvdpLfsr8bit0001.lean)
asyncLoad := some ("reset", false, .var "lfsr_seed" 8)

-- F11 gated / derived clock  (Cvdp/CvdpApbHistoryShiftRegister0001.lean)
clockNet := some (.and (.var "pclk" 1) (.not (.var "clk_gate_en" 1)))   -- gated clock
clockNet := some (.var "history_shift_valid" 1)                          -- data signal as clock
```

**Combination limits** (CORE.md §1.3): `asyncReset` + `asyncLoad` on the *same* register is
forbidden. Registers carrying `clockNet`, `asyncLoad`, or a module with non-empty `mems` are
excluded from the whole-design cycle theorems (`moduleChecksb` returns `false`) and instead pinned
per-register/per-access + co-simulation — this is by design, not a gap.

---

## 5. A complete minimal worked module

The 4-bit "even counter" — the smallest end-to-end sequential design — quoted verbatim from
`example:` [`LeanRTL/Designs/Examples/Counter/`](../LeanRTL/Designs/Examples/Counter/)
(`Impl.lean` + `Spec.lean` + `Proof.lean`).

**Implementation** (`Impl.lean`): one 4-bit register that increments by 2 each clock, sync-reset.

```lean
def nextCount : Expr 4 := .add (.var "count" 4) (.const 2)

def impl : Module :=
  { name    := "Counter"
    inputs  := [{ name := "clk", width := 1 }, { name := "rst", width := 1 }]
    outputs := [{ name := "q", width := 4, expr := .var "count" 4 }]
    regs    := [{ name := "count", width := 4, next := nextCount, init := 0 }]
    clock   := some "clk"
    reset   := some "rst" }
```

**Spec** (`Spec.lean`): the intended next-state function and an environment binding the register.

```lean
def step (c : BitVec 4) : BitVec 4 := c + 2
def env (c : BitVec 4) : Env := fun n => if n = "count" then c.toNat else 0
```

**Correctness** (`Proof.lean`): the AST's next-state expression denotes the spec — one line.

```lean
theorem next_correct (c : BitVec 4) :
    eval nextCount (env c) = step (env c |>.lookup "count" 4) := by
  simp only [nextCount, step, eval, Env.lookup, env,
             BitVec.ofNat_toNat, BitVec.setWidth_eq, if_true]
```

That is the whole shape of a proof-carrying design: `eval <the register's next cone> = <the spec
function>`. (This example additionally proves the `Even4` invariant is preserved for all time; for
lifting per-cycle facts to a whole-trace theorem, see the `leanrtl-full-temporal` skill.)

---

## 6. What it lowers to & how to emit

The `Module` you authored is lowered by the **proven** compiler (`compile : Module →
Backend.Design`, `Core/Compiler.lean`) to RTLIL cells, and Yosys turns RTLIL into Verilog via
`write_verilog`. Three CLI entry points produce the artifact (all resolve a design by its **registry
key**):

* `leanrtl extract <key>` — run the machine-checked compiler to RTLIL (`out/<key>.rtlil.json`);
  Yosys then emits structural Verilog. This is the default proven path (`docs/plan/history/plan.v0.1.md`).
* `leanrtl vverilog <key>` (F9) — emit **procedural** next-state SystemVerilog (register cones
  recomputed with blocking temps inside the clocked block, decisions lowered to `if/else`). It is
  gated behind a Yosys `equiv_induct` miter against the verified netlist before use (see
  [`scripts/f9_emit.py`](../scripts/f9_emit.py) — `f9_or_none`), which is why it is trustworthy
  despite being a hand-shaped emitter.
* `leanrtl pverilog <key>` (F2) — emit genuinely **parametric** SystemVerilog for a
  `List Nat → Module` family declared by a `paramMeta : ParamMeta`;
  `leanrtl extract <key> --N k1,k2,…` pins a concrete instance (the vector is in `paramMeta.params`
  declaration order). Like F9 it is miter-anchored before use, but at **several** parameter vectors
  rather than one: `scripts/f9_emit.py::param_anchor` runs the proven compiler at each vector for
  the gold netlist and elaborates the parametric module at that same vector with
  `hierarchy -chparam`. See §6.1.

The proof-carrying invariant: the shipped Verilog is trusted **only** because it is either produced
by the proven transform *or* miter-anchored to the verified reference — never a naked hand-edit
(see `docs/skills/principles/proof-carrying-reaches-artifact.md`). The end-to-end wiring lives in
[`scripts/export_emitted.py`](../scripts/export_emitted.py).

---

## 6.1 F2 — parametric designs (`paramMeta`)

Use this when your spec's interface declares Verilog `parameter`s. Modelling such a design as a
fixed `impl : Module` at the default value produces Verilog that *declares* the parameter and never
reads it, so an override at elaboration changes nothing — see `AGENT.md` for why that is a real
failure and not a cosmetic one.

**The structure** (`LeanRTL/Core/ParamBackend.lean`):

```lean
structure ParamMeta where
  key    : String                 -- the registry key, exactly as `bb.py` is invoked with
  params : List (String × Nat)    -- Verilog parameter name × default, in DECLARATION order
  gen    : List Nat → Module      -- the family, applied to a vector in `params` order
  sym    : Option PModule := none -- the family written SYMBOLICALLY; see §6.2
```

Both `ParamMeta` and `clog2 : Nat → Nat` (the Lean mirror of Verilog's `$clog2`) are already
opened in your file's header. Declare it in the design file, with the type annotation written
literally — `bb.py` selects the route by matching the text `def paramMeta : ParamMeta`:

```lean
def implGen (width nStages : Nat) : Module :=
  { name := "…"
  , inputs  := [⟨"clk", 1⟩, ⟨"rst", 1⟩, ⟨"din", width⟩]
  , outputs := [⟨"dout", width + 1, .var "acc" (width + 1)⟩]
  , regs    := [{ name := "acc", width := width + 1, next := .zext 1 (.var "din" width)
                , init := 0, asyncReset := some ("rst", 0) }
               ,{ name := "cnt", width := clog2 nStages, next := …, init := 0 }]
  , clock   := some "clk" }

def paramMeta : ParamMeta :=
  { key := "…", params := [("WIDTH", 8), ("N_STAGES", 4)]
  , gen := fun v => implGen v[0]! v[1]! }

/-- Definitionally the instance the harness registers, so `check`/`sim`/`cosim` and every L1
    theorem can go on naming one concrete module. -/
def impl : Module := implGen 8 4
```

The two registries then differ: `blindRegistry` gets `paramMeta.gen paramMeta.defaults` (the
default instance) while `paramRegistry` gets the family, which is what `pverilog` and `extract --N`
serve.

**Running your design off-default.** `sim`, `cosim` and `extract` build the default instance unless
told otherwise, and `check` sweeps a grid of vectors and reports which ones `gen` builds a
well-formed module at. To pin one instance, pass `--N <v1,v2,…>` — values in the order
`paramMeta.params` declares them:

```
python3 scripts/bb.py <key> check --N 2,8
python3 scripts/bb.py <key> sim   --N 2,8
python3 scripts/bb.py <key> cosim --N 2,8
leanrtl check <Name> --N 2,8        # the same thing, one layer down
leanrtl sim   <Name> --N 2,8
leanrtl extract <Name> --N 2,8 -o gold.json
```

Use it. A grading testbench instantiates your module at widths and depths it chooses, not the ones
your spec states as defaults; a generator that is correct at the defaults and wrong anywhere else
is green on every other command here. The default vector is the one instance that cannot show you
that.

**How the emitter derives the widths, and what it will not do.** It has no access to your Lean
source — it builds `gen` at a grid of parameter vectors and compares the resulting `Module`s. Each
width, constant and reset value is fitted as a multilinear form in the parameters plus `$clog2`
terms, and the fit is then **re-evaluated at vectors it was not fitted on**. A fitted formula that
does not reproduce there is discarded and the design is refused with the reason — the emitter will
not ship a width it has not checked. It therefore expresses:

| Fits | Refused |
|---|---|
| a constant; `WIDTH`; `2*WIDTH+1`; `A_W+B_W` | `WIDTH*WIDTH`, `2^WIDTH-1`, `WIDTH/2` — not multilinear |
| products: `A_W*B_W`, `X*Y*Z` | `WIDTH*$clog2(N)` — `$clog2` may only appear linearly |
| `$clog2(N)`; `A_W+B_W+$clog2(N)` | a parameter that changes the **number** of registers |

That last row is the structural limit and is deliberate: `gen` at two vectors must produce the same
register list, port list and expression *shape*, differing only in widths and constants. A depth or
array-length parameter changes the shape, and the emitter names it rather than silently dropping
registers. **It is also no longer the end of the road** — set `sym` and the shape stops mattering;
see §6.2.

A refusal is **not** an emit failure. `bb.py <key> emit` prints the reason, falls back to the
ordinary f9 / `write_verilog` route, still writes `out/<key>.v`, and records the route as
`pverilog_refused->f9`.

**It is then miter-anchored, at more than one vector.** Fitting-and-verifying is a statement about
the *formulas*, not about the Verilog — it says the fitted width reproduces what `gen` returns, and
says nothing about whether the module built around it computes the proven logic. So the emitted
module is proved against the machine-checked compiler's own netlist the same way F9 is, except at
each of several parameter vectors: the declared defaults, then one off-default value of each
parameter in turn. The gold at a vector comes from `leanrtl extract <key> --N <vector>`, and the
gate is elaborated at that same vector with `hierarchy -chparam`.

That last part is the whole difference from the F9 miter, which reads the gate with a plain
`read_verilog -sv` and therefore only ever builds the **default** instance. A module can declare a
parameter, never read it, and sail through *that* miter — which is precisely how a decorative
parameter used to reach a testbench. Overriding the parameter in the miter is what makes the
certificate say something about the family rather than about one instance, and a module that fails
to be anchored at two or more vectors does not ship on this route.

**Two miters, and what each one certifies.** The first is `equiv_induct`, which proves the two
agree *forever*. It reasons from a FREE initial state — "if they agree for k frames then they agree
at k+1, whatever state they are in" — and that is more than a design with holding storage can
support: a queue's output depends on inputs from arbitrarily long ago, so from an arbitrary state
the two can disagree at once and no depth repairs it. Raising `-seq` does not help, and neither
does name-matching the storage, because the compiler's netlist names a parametric array's flops
`s_0 … s_4` and no Verilog can write that when the count is a parameter.

So a vector that fails the induction is retried BOUNDED, from the common power-on state — sound
only because every register gets its `init` on both sides. What that proves: *from reset, for the
first K cycles, the two agree on every output for every input sequence.* That is a proof over all
inputs, bounded in time and not sampled, and K is reported per vector in the `emit` line
(`bounded@8,16:19` — nineteen cycles at that vector). It is weaker than the induction and the route
says which vectors got which, so a design can never be read as carrying the unbounded certificate
when it carries the bounded one.

A vector where the BOUNDED miter finds a counterexample is different again, and it is fatal: the
two were driven from the same power-on state and disagreed at a finite cycle, so the emitted module
contradicts the machine-checked compiler. The route refuses (`param_anchor:refuted@…`). A vector
where neither miter reaches a verdict is `inconclusive@…`, is named in the detail, and does not by
itself knock the design off the route — the two-vector floor still has to be met by vectors that
did anchor.


## 6.2 F2 symbolic — when a parameter is a COUNT (`sym`)

§6.1's emitter never reads your Lean source. It builds `gen` at a grid of vectors and recovers the
module from the numbers, which works exactly as far as the module's *shape* is constant. A tap
count, a number of stages, a matrix dimension or a queue depth changes how many registers and how
many operators the design has, and no amount of better fitting reaches it: the emitter observes
points, and a point does not carry a loop.

Setting `sym` hands it the loop instead of asking it to infer one.

**The structure** (`LeanRTL/Core/PModule.lean`, opened in your header alongside `ParamMeta`):

```lean
structure PModule where
  name    : String
  params  : List (String × Nat)      -- same meaning and same order as `ParamMeta.params`
  inputs  : List (String × NatE)
  outputs : List POut                -- { name, width : NatE, expr : PExpr }
  wires   : List PWire := []         -- { name, width : NatE, expr : PExpr }
  regs    : List PReg  := []
  clock   : Option String := none
  derived : List (String × NatE) := []   -- parameters whose DEFAULT is a formula; see below

structure PReg where
  name  : String
  width : NatE
  next  : PExpr
  init  : PExpr
  count : Option NatE := none        -- `some n` ⇒ an ARRAY of n registers
  asyncReset : Option String := none
```

Every width is a **`NatE`**: an elaboration-time expression over the parameter vector, which is
exactly what a Verilog `parameter` expression may contain.

### Parameters that are *derived* from other parameters — `derived`

Read the spec's parameter table before you write `params`, and ask of each entry: **is this one
the spec calls primary, or one it says is calculated from the others?**  Phrases that mean derived:
"should be calculated to handle overflow", "wide enough to hold", "derived from", "= 2×… ", or a
width given as a formula rather than a number.

A grader instantiates your module by overriding the parameters it treats as primary and leaving
every derived one alone, expecting it to follow.  If you declare a derived parameter independently,
at a literal, it *keeps that literal* while the primary ones move — so the module elaborates,
simulates, and computes the right function at the wrong width.  Nothing warns you: at your declared
defaults everything agrees, and your own `sim`/`cosim`/`param_anchor` all run at the defaults.

Say it instead:

```lean
params  := [("N", 8), ("IN_W", 8), ("ACC_W", 19)]
derived := [("ACC_W", .add (.mul 2 (.param 1)) (.clog2 (.param 0)))]   -- 2*IN_W + $clog2(N)
```

emits

```verilog
module m #(parameter N = 8, parameter IN_W = 8,
           parameter ACC_W = ((2 * IN_W) + ($clog2(N)))) ( … );
```

The numeric default stays, and stays load-bearing: it is the vector `gen`, `elabAt` and every
`param_anchor` proof see.  The emitter checks that the formula evaluates to exactly that number at
the declared defaults and **refuses** if it does not, so the two can never disagree.  A formula may
only name parameters declared *before* it, as in Verilog.

Use `--N` to check the derived one really follows: `bb.py <key> sim --N …` at a vector where the
primary parameters differ from their defaults is the test this feature exists for.

| `NatE` | means |
|---|---|
| `.lit n` | the literal `n` (numerals also work: `4` elaborates via `OfNat`) |
| `.param i` | the `i`-th declared parameter, in `params` order |
| `.idx k` | the `k`-th enclosing loop index, **innermost first** |
| `.add` `.sub` `.mul` `.div` | arithmetic; `.sub` is truncated, as on `Nat` |
| `.pow2 a` | `2**(a)` |
| `.clog2 a` | `$clog2(a)` |

`PExpr` is the ordinary expression set — `.const w v`, `.var n w`, `.not`, `.bin`, `.cmp`, `.mux`,
`.shl`/`.shr`/`.sshr`, `.zext k`, `.sext k`, `.slice lo len`, `.concat` — plus the nodes that
make a count expressible:

| node | means |
|---|---|
| `.sel arr elemW i` | element `i` of register array `arr`; `i` is a `NatE`, so it is a parameter/loop expression, not a runtime net |
| `.fold op count width seed body` | reduce `body` over `i = 0 .. count-1` with `op`, from `seed`, at `width` bits; inside `body`, `.idx 0` is `i` |
| `.foldA count width seed body` | the same loop, but `body` computes the **new accumulator** outright instead of a value to be combined with a fixed operator |
| `.acc width` | inside a `.foldA` body, the running accumulator — its value after element `i-1` |
| `.ifEq a b t f` | pick a branch by comparing two **elaboration-time** naturals — how element 0 of a shift register takes the new sample and the rest take their predecessor |

A runtime-indexed array is not `.sel`; it is a `MemBlock` and belongs on the memory path.

**`.fold` vs `.foldA`.** `.fold` reduces with a `PBin` (`+ - * & | ^ / %`), and a great many real
reductions are not one. A combinational maximum over a parametric number of elements — "start with
the first sample, then for each remaining one, if it is larger the peak becomes it" — has no
operator to name. `.foldA` gives the body the running value instead:

```lean
-- max over `.param 1` elements of the array `s`, each `.param 0` bits wide
.foldA (.sub (.param 1) 1) (.param 0) (.sel "s" (.param 0) 0)          -- seed: element 0
  (.mux (.cmp .ult (.acc (.param 0)) (.sel "s" (.param 0) (.add (.idx 0) 1)))
        (.sel "s" (.param 0) (.add (.idx 0) 1))
        (.acc (.param 0)))
```

Minimum, saturating add, a running index-of-max, a priority encoder and a compare-and-swap pass are
all this shape. `.fold op` is kept because it reads better where it fits, and is exactly `.foldA`
with `body = .bin op (.acc w) elem`. The accumulator is scoped to the **innermost** enclosing
`.foldA`; an `.acc` with no enclosing `.foldA` fails to elaborate rather than defaulting to
anything.

**A register's `init` must be a literal.** `Reg.init` is a `BitVec`, not an expression, so `init`
has to be a `.const` — or an `.ifEq` between constants, when element 0 of an array needs a
different power-on value from the rest. Anything else is refused by name. The emitted module gives
every register that value in an `initial` block, whether or not it has an `asyncReset`, so a
reset-less design powers up where the compiler's netlist powers up rather than at `x`.

**Wiring it up.** Three fields, one family:

```lean
def famP : PModule := { name := "…", params := [("DATA_WIDTH", 8), ("N_STAGES", 4)], … }

def paramMeta : ParamMeta :=
  { key := "…", params := famP.params, gen := famP.genOf, sym := some famP }

def impl : Module := famP.genOf [8, 4]
```

`PModule.genOf` is the family at a concrete vector, as an ordinary `Module` — a `PReg` with
`count := some n` unfolds to `n` ordinary registers named `nm_0 … nm_{n-1}`, and every `.fold`
unfolds to a chain. **Nothing downstream changes**: the compiler, the semantics, `Refines` and
every L1 theorem still consume a monomorphic `Module`, because that is still what they get.

If you would rather write the default instance out by hand, do — and then state the equation, which
holds definitionally when the two agree:

```lean
theorem famP_default : famP.elabAt [8, 4] = some impl := by rfl
```

**`sym` is checked first and unconditionally.** Nothing is fitted, so §6.1's table of refusals does
not apply; if you set it, a structure refusal cannot happen. What the symbolic route still refuses
is narrow, and each refusal names itself:

- a width that mentions a loop index — every element of an array shares one declared width, and a
  fold's accumulator is declared outside its own loop;
- a bit- or part-select of a value whose width mentions a loop index;
- a parameter that adds, removes or renames a **port** (the port list is fixed), or that changes
  how many read/write ports a memory has.

**The certificate is unchanged.** `gen` is still what `leanrtl extract <key> --N <vector>` runs the
*verified compiler* on, and the emitted text is still proved equivalent to that netlist at the
defaults plus one off-default value of each parameter (§6.1's last two paragraphs, verbatim).
Writing the loops down does not buy a weaker check — it buys a module the check can be run on at
all. What the miter catches on this route is `emitPVerilog` and `elabAt` disagreeing: two
independent renderings of one `PModule`, which is where an emitter bug would live.

---

## 7. Pointers

* **How to PROVE what you wrote** → [`docs/skills/INDEX.md`](skills/INDEX.md) — the layered proof
  library (principles → patterns → tactics), including per-feature proof shapes
  (`patterns/asyncload-value-trace.md`, `patterns/memory-raw-laws.md`,
  `patterns/dual-edge-two-registers.md`, `patterns/parent-flatten.md`, …).
* **The authoring playbook + hard-won lessons** →
  [`docs/instructions/CORE.md`](instructions/CORE.md) — the single-source capability matrix
  (§1), the reset/signal-name/latency conventions (§2), and the root-cause schema (§4). When in
  doubt about *whether a feature is expressible*, that matrix is the authority; this file is the
  authority on *how the field is spelled*.
* **Lifting per-cycle proofs to whole-trace correctness** → the `leanrtl-full-temporal` skill
  (SimRefines forward-simulation bridge).

---

### Appendix: fields not surfaced in the CORE.md §1 capability matrix

For completeness — grammar in `Core/Syntax.lean` that the feature matrix (§1.1, which enumerates
*sequential/structural* features) does not list as a row:

* **`Module.wires` / the `Wire` type** — internal combinational signals for word-level RTL sharing.
  Foundational to every non-trivial and every imported design, but the matrix only cautions *against*
  wires for agentic sequential designs (§2.8) rather than presenting them as a feature.
* **The full combinational `Expr` palette** — `.mul`, `.sub`, `.udiv`, `.umod`, the *signed*
  operators `.slt` and `.sshr`, and `.slice`/`.extract`/`.concat`/`.zext`/`.sext` bus reshaping are
  not in the matrix (which is about clocking/state, not the datapath algebra).
* **`MemWrite.clock`** — each memory *write port* carries its own clock net (may be the module
  clock, a second clock, or a data-signal-as-clock strobe), i.e. `clockNet`-for-memory; only
  implied by the single "addressed memory" matrix row.
* **`Parent.clock` / `Parent.reset`** — the parent-side clock/reset used by the sequential
  flattening; the matrix lists F10 hierarchy but not these fields.
* **"ParamModule" is not a Lean type.** The matrix writes F2 as `ParamModule: impl : Nat → Module`.
  There is no `structure ParamModule`: what exists is `structure ParamMeta`
  (`LeanRTL/Core/ParamBackend.lean`), and F2 is the pair of an ordinary generator
  `def implGen (…) : Module` and a `def paramMeta : ParamMeta` that registers it. See §6.1.

### Field completeness note (machine-checked)

For lint completeness (`scripts/check_dsl_reference.py`), the remaining structural fields:
`Reg` also carries `width` (bit width) and `negedge` (falling-edge clocking, F1).
`Module` carries `inputs` / `outputs` (the port lists), `latches` (level-sensitive `Latch` list, F8),
`clock` / `reset` (the module clock/reset net names).
`MemBlock` carries `addrWidth` / `dataWidth`. `Latch` carries `width`, `enable` (gate net), `d` (data expr).
`Wire` carries `width`.
