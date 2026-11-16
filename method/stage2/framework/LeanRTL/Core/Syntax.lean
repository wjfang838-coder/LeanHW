/-!
# LeanRTL abstract syntax (the deep embedding)

A LeanRTL design is a Lean *data value*: an `Expr` for combinational logic and a
`Module` bundling typed ports, internal `wires`, and (optionally) registers.  Widths live
in the types, so width mismatches are Lean type errors caught at the very first verification
layer.  Internal `wires` give a module a *word-level RTL* shape — each coarse cell is a
named, shared signal — which is what lets large designs (and imported RTLIL) be represented
without blowing up into duplicated expression trees.

The same `Expr` is given two interpretations elsewhere:
* `LeanRTL.eval`    — denotational semantics over `BitVec` (for specs & proofs);
* `LeanRTL.compile` — lowering to RTLIL JSON cells (for Yosys).
-/

namespace LeanRTL

/-- Combinational, word-level expressions of a fixed bit width. -/
inductive Expr : Nat → Type where
  /-- A literal bit-vector constant. -/
  | const  : {w : Nat} → BitVec w → Expr w
  /-- Reference to a port / register / wire by name; `w` is its width. -/
  | var    : String → (w : Nat) → Expr w
  | not    : {w : Nat} → Expr w → Expr w
  | and    : {w : Nat} → Expr w → Expr w → Expr w
  | or     : {w : Nat} → Expr w → Expr w → Expr w
  | xor    : {w : Nat} → Expr w → Expr w → Expr w
  | add    : {w : Nat} → Expr w → Expr w → Expr w
  | sub    : {w : Nat} → Expr w → Expr w → Expr w
  /-- Multiplication, truncated to the operand width (matches `BitVec` `*`). -/
  | mul    : {w : Nat} → Expr w → Expr w → Expr w
  /-- Logical left shift; `b` is an unsigned, possibly different-width, shift count. -/
  | shl    : {w k : Nat} → Expr w → Expr k → Expr w
  /-- Logical (zero-fill) right shift by an unsigned count. -/
  | shr    : {w k : Nat} → Expr w → Expr k → Expr w
  /-- Arithmetic (sign-extending) right shift by an unsigned count. -/
  | sshr   : {w k : Nat} → Expr w → Expr k → Expr w
  /-- Unsigned division (truncating). -/
  | udiv   : {w : Nat} → Expr w → Expr w → Expr w
  /-- Unsigned remainder. -/
  | umod   : {w : Nat} → Expr w → Expr w → Expr w
  /-- Unsigned equality, producing one bit. -/
  | eq     : {w : Nat} → Expr w → Expr w → Expr 1
  /-- Unsigned less-than, producing one bit. -/
  | ult    : {w : Nat} → Expr w → Expr w → Expr 1
  /-- Signed less-than (two's-complement), producing one bit. -/
  | slt    : {w : Nat} → Expr w → Expr w → Expr 1
  /-- `mux s a b = if s = 1 then a else b`. -/
  | mux    : {w : Nat} → Expr 1 → Expr w → Expr w → Expr w
  /-- Concatenation: `concat hi lo` places `hi` in the high bits, `lo` below it
      (matching `BitVec.append`). -/
  | concat : {a b : Nat} → Expr a → Expr b → Expr (a + b)
  /-- Zero-extend by `k` bits. -/
  | zext   : {w : Nat} → (k : Nat) → Expr w → Expr (w + k)
  /-- Sign-extend by `k` bits (replicate the MSB). -/
  | sext   : {w : Nat} → (k : Nat) → Expr w → Expr (w + k)
  /-- Extract a single bit at index `i` (LSB = 0). -/
  | extract : {w : Nat} → (i : Nat) → Expr w → Expr 1
  /-- Extract a contiguous field of `len` bits starting at bit `lo`. -/
  | slice   : {w : Nat} → (lo len : Nat) → Expr w → Expr len

/-! Convenience constructors / notation. -/

/-- A named input/wire reference. -/
def wire (name : String) (w : Nat) : Expr w := .var name w

/-- One-bit constant. -/
def bit (b : Bool) : Expr 1 := .const (if b then 1 else 0)

/-! ## Modules -/

/-- External packed-vector declaration. Expr indices remain LSB-relative BitVec
    indices; this metadata records the HDL port's signedness and index labels. -/
structure PortLayout where
  name : String
  signed : Bool := false
  offset : Int := 0
  upto : Bool := false
  deriving Repr, Inhabited

structure InPort where
  name  : String
  width : Nat
  deriving Repr, Inhabited

structure OutPort where
  name  : String
  width : Nat
  expr  : Expr width

/-- An expression of some (existentially packed) width, used for instance port maps. -/
abbrev AnyExpr := Σ w, Expr w

def anyExpr {w : Nat} (e : Expr w) : AnyExpr := ⟨w, e⟩

/-- A clocked register.  `next` is the D-input expression (may reference inputs, internal
    wires, and other registers by name); `init` is the synchronous-reset value.

    `asyncReset` (F4) is an optional *asynchronous* reset: `some (rstNet, activeHi, rstVal)` means
    the register is held at the constant `rstVal` whenever the 1-bit input net `rstNet` is at its
    active level (`activeHi = true` ⇒ held while `rstNet` is high; `false` ⇒ active-LOW, held while
    `rstNet` is low), *independently of the clock* (an `$adff`).  An async reset cannot be lowered to
    a synchronous `$dff`+mux (it fires between clock edges), so it compiles to a real `$adff` cell
    with `ARST_POLARITY = if activeHi then 1 else 0`; `write_verilog` renders the active-low case as
    `always @(posedge clk or negedge rstNet) if (!rstNet) q <= rstVal;`.  Default `none` keeps every
    existing register literal and module unchanged.

    The polarity field is not decoration.  Without it an active-low `rst_n` can only reach an
    `$adff` through an inverter net (`nrst = ~rst_n`, `asyncReset := some ("nrst", 0)`), and the
    emitted `always @(posedge clk or posedge nrst) if (nrst)` then samples a net that settles one
    delta *after* `rst_n` moves.  A testbench that deasserts reset in the same timestep as a clock
    edge — `rst_n = 0; repeat(10) @(posedge clk); rst_n = 1;` is the common idiom — loses that race
    and the whole output trace shifts by one cycle.  Naming the port and its polarity directly is
    what removes the extra delta.

    `negedge` (F1) selects the clock edge the flip-flop samples on: `false` (default) = the
    **positive** edge (`$dff`/`$adff` `CLK_POLARITY = 1`, `always @(posedge clk)`); `true` = the
    **negative** edge (`CLK_POLARITY = 0`, `always @(negedge clk)`).  Default `false` keeps every
    existing register literal unchanged.

    `asyncLoad` (F6) is an optional *asynchronous load of a **dynamic** value*: `some (net, activeHi,
    val)` means that whenever the 1-bit input `net` is at its active level (`activeHi = true` ⇒ load
    while `net` is high; `false` ⇒ active-LOW, load while `net` is low), the register is *asynchronously*
    forced to `eval val` — the value of an arbitrary `Expr width` (typically an input port such as
    `.var "lfsr_seed" 8`), **not** a compile-time constant — independently of the clock; otherwise it
    clocks in `next` on the active clock edge.  This is exactly Yosys `$aldff` semantics
    (`CLK` + `ALOAD` + async data `AD` + normal data `D` + `Q`); `write_verilog` renders it as
    `always @(posedge clk or negedge net) if (!net) q <= val; else q <= next;`.  It is the one thing
    `asyncReset` (constant `ARST_VALUE`) cannot express — a runtime data load.  Default `none` keeps
    every existing register literal unchanged.

    *Cycle-semantics note (like F1/F8).*  An async load fires *between* clock edges, so — exactly as
    for `asyncReset` and `negedge` — it is **not** modelled by the one-active-edge-per-cycle
    `Module.simulate`.  Its behaviour is pinned by the per-register characterization `Reg.aldffDen`
    (`q' = active ? val : next`, proved per instance in the design file) and validated end-to-end by
    co-simulation of the emitted `$aldff`.  A register carrying `asyncLoad` is excluded from the
    whole-design compiler-correctness theorems (`moduleChecksb` returns `false`, exactly as it does
    for `asyncReset`), and the `$aldff` is emitted by a lowering *post-pass* over the (M6-proven)
    `compileModuleM` output — so no compiler-correctness theorem is disturbed.

    *Cycle-semantics note.*  `Module.simulate`/`Module.step` are a **one-active-edge-per-cycle**
    model: each register advances once per simulate cycle from its `next` cone.  A *single-edge*
    register (whether posedge or negedge) samples exactly once per active edge = once per cycle, so
    a negedge-only design has the *same* cycle-level trace as the posedge version and `negedge` does
    not change `Module.simulate` — its whole behavioural effect is the emitted flip-flop's clock
    polarity, which `write_verilog` lowers to `always @(negedge clk)`.  When posedge and negedge
    registers **coexist** in one module (a dual-edge design), the two edges interleave *within* a
    clock period; the cycle model advances both on the same cycle and therefore does NOT faithfully
    model that sub-cycle interleaving (see the F1b honesty note in the dual-edge VEval files).  The
    per-register next-state proofs remain valid; the compiler still emits one correctly-polarised
    `$dff` per register, which is the accepted two-flop dual-edge idiom Yosys/iverilog realise. -/
structure Reg where
  name  : String
  width : Nat
  next  : Expr width
  init  : BitVec width
  /-- Emit an explicit power-on value. False preserves an uninitialized Verilog
      register: `init` remains the synchronous-reset/simulator seed, but imposes
      no hardware initial-state constraint. Use step theorems from an arbitrary
      corresponding state for such a register, rather than a fixed-seed trace. -/
  emitInit : Bool := true
  /-- F4 asynchronous reset: `some (rstNet, activeHi, rstVal)` holds `q` at the constant `rstVal`
      while the 1-bit net `rstNet` is at its active level (`activeHi = true` ⇒ active-high,
      `false` ⇒ active-low).  Lowers to a Yosys `$adff`.  Default `none`. -/
  asyncReset : Option (String × Bool × BitVec width) := none
  negedge : Bool := false
  /-- F6 asynchronous load of a *dynamic* value: `some (net, activeHi, val)` forces `q ← eval val`
      asynchronously while the 1-bit input `net` is at its active level (`activeHi = true` ⇒
      active-high, `false` ⇒ active-low).  Lowers to a Yosys `$aldff`.  Default `none`. -/
  asyncLoad : Option (String × Bool × Expr width) := none
  /-- F11 **per-register clock net** (multi-clock / gated clock).  `some clkExpr` clocks this
      flip-flop off the 1-bit *derived* net `clkExpr` — an arbitrary combinational `Expr 1` — rather
      than the module clock (`Module.clock`).  `clkExpr` may be:
      * another **clock input** (`.var "clk2" 1`) — a second clock domain (e.g. a glitch-free mux);
      * a **gated clock** (`.and (.var "pclk" 1) (.not (.var "clk_gate_en" 1))`) — clock gating;
      * a **data signal used as a clock** (`.var "history_shift_valid" 1`) — a signal whose rising
        edge advances the register.
      The compiled `$dff`/`$adff`/`$aldff` takes its `CLK` from `eval clkExpr` (a lowering *post-pass*
      over the M6-proven `compileModuleM`, exactly like the F6 `$aldff` rewrite): `write_verilog`
      renders `always @(posedge <clkExpr>)`.  Default `none` = the module clock, keeping every existing
      register literal unchanged.

      *Cycle-semantics honesty note (like F1/F6/F8).*  `Module.simulate` is a **single-clock,
      one-active-edge-per-cycle** model: it advances *every* register on the same tick and therefore
      **cannot** model two (or more) *independent* clock domains that edge at unrelated times, nor a
      gated clock that skips edges.  A register carrying `clockNet` is therefore **excluded** from the
      whole-design cycle theorems (`moduleChecksb` returns `false`, exactly as for `asyncReset`/
      `asyncLoad`).  Its behaviour is pinned by the per-register next-state characterization proved in
      the design file (`eval r.next = spec`, valid on *its* clock's edge) plus the honest boundary that
      the multi-domain *interleaving* is out of `Module.simulate`'s reach, and it is validated
      end-to-end by co-simulation of the emitted multi-clock netlist. -/
  clockNet : Option (Expr 1) := none

/-! ### Back-compatibility for the two pre-polarity `asyncReset` spellings

`Reg.asyncReset` has carried three different types.  It began as `Option String` (a net name, with
the reset value taken to be zero), became `Option (String × BitVec width)` (an explicit value), and
is now `Option (String × Bool × BitVec width)` (an explicit polarity, added so that an active-low
reset need not be reached through an inverter net).  Neither widening was accompanied by a
coercion, so each one silently invalidated every design already written against the older spelling
— which is not a hypothetical: of the 78 CVDP designs in `workspaces/_cvdp2/cvOursParam2`, four
were authored with the bare-`String` form and two with the pair form, and refreshing that
workspace's framework broke all six at once.  Three of them had been *passing*.

That is a framework defect rather than an authoring one.  A blind author writes against the DSL
they were handed; a field type that moves underneath them turns finished, scored work into a
compile error with no diagnostic pointing at the cause.  So the older spellings are supported
here, permanently, rather than migrated away.

Both legacy forms mean **active-high**, and they mean it exactly: the compiler of the pair era
hardcoded `("ARST_POLARITY", binStr32 1)` with no way to say otherwise, so `activeHi := true` is
not a chosen default but a transcription of what those designs actually compiled to.  An
active-low reset was expressed the only way it could be — through an inverter net
(`nrst = ~rst_n`, `asyncReset := some ("nrst", 0)`) — and `ProcVerilog.asyncNet?` still rewrites
that idiom back to the input port with the polarity flipped, so the legacy encoding keeps working
on top of these coercions rather than competing with them.

The bare-`String` form takes value `0` for the same reason: the era that accepted it had no place
to put a value.
-/

instance {w : Nat} : CoeTail String (String × Bool × BitVec w) :=
  ⟨fun net => (net, true, 0)⟩

instance {w : Nat} : CoeTail (String × BitVec w) (String × Bool × BitVec w) :=
  ⟨fun p => (p.1, true, p.2)⟩

/-- The pair spelling needs this as well as the coercion above, because a coercion never gets the
chance to fire on it.  Against the expected type `String × (Bool × BitVec w)` the elaborator sees a
tuple *literal* and destructures it structurally — `Prod.mk` against `Prod` — so the reset value
`0` is pushed into `Bool × BitVec w` and fails there, before any `CoeTail` on the pair as a whole
is ever considered.  The coercion still covers the case where the pair arrives as an opaque term
rather than a literal, so both are kept.

`true` is again a transcription rather than a default: the compiler that accepted this spelling
emitted `("ARST_POLARITY", binStr32 1)` unconditionally. -/
instance {w n : Nat} [OfNat (BitVec w) n] : OfNat (Bool × BitVec w) n :=
  ⟨(true, OfNat.ofNat n)⟩

/-- And this is where the elaborator actually lands once it has destructured the pair: the reset
value, whatever its form, is elaborated against `Bool × BitVec w`.  The `OfNat` instance above
covers that position only for a numeric literal; a computed value — `BitVec.ofNat (cwOf n) n`, a
width derived from a parameter — is an ordinary term and needs a coercion instead. -/
instance {w : Nat} : CoeTail (BitVec w) (Bool × BitVec w) :=
  ⟨fun v => (true, v)⟩

/-- A level-sensitive **transparent latch** (F8).  Unlike a `Reg` (edge-triggered flip-flop), a
    latch has no clock edge: while `enable` is high the latch is *transparent* — its output `q`
    follows `d` combinationally — and while `enable` is low it *holds* its last value.  Its
    next-value law is therefore `q' = if enable then d else q` (a level-sensitive stateful
    feedback that is neither a pure-combinational acyclic wire nor an edge-clocked register).

    It lowers to a Yosys `$dlatch` cell (`EN` + `D` + `Q`, `EN_POLARITY = 1`), which
    `write_verilog` renders as the canonical `always @(*) if (en) q = d;` latch idiom.

    **Referencing a latch's `Q`.**  A latch is an ordinary named signal: wires, outputs and
    register next-states may read `.var name width` exactly as they read a register.  The
    compiler pre-allocates each latch's Q net *before* the module body (`seedLatchNets`), so the
    reference resolves to the very net the `$dlatch` drives.  No wire/output of the same name is
    needed — and declaring one is in fact **rejected** by `Module.checkErrors` as a duplicate
    signal name.  (Before 2026-08-05 that seeding did not exist and such a reference silently
    compiled to a *floating* net, after which `opt_clean` deleted the `$dlatch` as dead while
    `build`/`check`/`emit` all reported success.  Four RealBench authors hit it independently;
    see `docs/plan/friction.v1.5.md` STRIKE-4.)

    **A flip-flop is not a substitute.**  A `posedge` `Reg` differs from a low-transparent latch
    on every cycle whose enable changes.  A `negedge` `Reg` *is* waveform-identical for the
    `clk & Q` clock-gate idiom specifically.

    *Cycle-semantics honesty note (like F1's dual-edge).*  `Module.simulate` is a
    one-value-per-cycle Moore model; it does not capture a latch's *intra-cycle transparency*
    (when `enable` is high, a same-cycle read of `q` sees the new `d`, not the held value).  So —
    exactly as `negedge` does not change `Module.simulate` — latches are **not** modelled by the
    whole-design cycle simulator.  Their behaviour is instead pinned by the per-latch next-state
    characterization `Latch.den` (`q' = enable ? d : q`, proved in the VEval files) and validated
    end-to-end by co-simulation of the emitted `$dlatch`.  `bb cosim` therefore CANNOT validate a
    latch-carrying design — its `fail` there is expected, not a design bug. -/
structure Latch where
  name   : String
  width  : Nat
  /-- 1-bit level-sensitive enable: transparent (output follows `d`) while high, holds while low. -/
  enable : Expr 1
  /-- Data input captured while `enable` is high. -/
  d      : Expr width

/-- An internal combinational signal: `name` is bound to the value of `expr`.  Wires give the
    module a *word-level RTL* shape — each coarse cell becomes one wire — so common
    sub-expressions are named and shared instead of duplicated, which is essential for large
    designs (and for round-tripping an imported RTLIL design).  `expr` may reference inputs,
    registers, and *earlier* wires by name; the `wires` list must be topologically ordered. -/
structure Wire where
  name  : String
  width : Nat
  expr  : Expr width

/-! ## Addressed memory (SRAM / RAM array)

A `MemBlock` models a real synchronous memory array — a `reg [dataWidth-1:0] mem [0:size-1]`
— rather than an array of individually-named registers.  This is what unblocks kilobyte-scale
storage (a 1 KB SRAM = 1024×8 or 256×32): the register-array pattern (`RAM.lean`, `sync_lifo`)
would explode into thousands of `$dff` cells and an intractable compile/proof, whereas one memory
array is a single cell.

A `MemBlock` lowers (via a compiler *post-pass*, exactly like the F8 `$dlatch` / F6 `$aldff` / F11
per-register-clock elements) to a single Yosys `$mem_v2` cell, which `write_verilog` renders as the
canonical array idiom:
`reg [DW-1:0] mem [0:2^AW-1]; always @(posedge wclk) if (we) mem[waddr] <= wdata;
 assign rout = mem[raddr];`.

*Cycle-semantics honesty note (like F8/F6/F11).*  The whole-design `Module.simulate` is a
register-file Moore model and carries **no** memory array, so a module with a non-empty `mems` is
**excluded** from the whole-design cycle theorems (`moduleChecksb` returns `false`, exactly as for
`asyncReset`/`asyncLoad`/`clockNet`).  A memory's behaviour is instead pinned by the per-access
*addressed characterization* (`MemBlock.read_after_write` / `read_after_write_ne` in
`MemSemantics.lean`, proved per instance in the design file — reading address A returns the last
value written to A) and validated end-to-end by co-simulation of the emitted `$mem_v2` cell. -/

/-- One synchronous **write port** of a `MemBlock` (`aw`-bit address, `dw`-bit data).  On each
    active (posedge) edge of the 1-bit derived net `clock` — which may be the module clock, a second
    clock, or a *data signal used as a clock* (e.g. an SRAM `valid` strobe) — the word `data` is
    stored at `addr` whenever `en` is high.  Lowers to a `$mem_v2` write port
    (`WR_CLK = clock`, `WR_EN = replicate en`, `WR_ADDR = addr`, `WR_DATA = data`,
    `WR_CLK_ENABLE = 1`, `WR_CLK_POLARITY = 1`). -/
structure MemWrite (aw dw : Nat) where
  /-- 1-bit write clock; the memory samples on its **positive** edge. -/
  clock : Expr 1
  /-- 1-bit write enable: the word is stored only when this is high on the clock edge. -/
  en    : Expr 1
  addr  : Expr aw
  data  : Expr dw

/-- One **asynchronous (combinational) read port** of a `MemBlock`: the net named `out` is driven
    combinationally by `mem[addr]` (`assign out = mem[addr];`; a `$mem_v2` read port with
    `RD_CLK_ENABLE = 0`).  `out` should be a **fresh internal net name** referenced by the rest of
    the module (an output's expression, a wire, or a register's next-state cone); the compiler
    pre-binds it so those references connect to this read port.  (Registered/synchronous reads —
    `RD_CLK_ENABLE = 1` — are a natural extension left as future work; the current targets need only
    asynchronous reads.) -/
structure MemRead (aw : Nat) where
  addr : Expr aw
  /-- Name of the net this read port drives with `mem[addr]`; referenced elsewhere by `var out dw`. -/
  out  : String

/-- An addressed memory array: `size` words (default `2^addrWidth`) of `dataWidth` bits, with synchronous `writes`
    and asynchronous `reads`.  Lowers to a single `$mem_v2` cell.  A module's `mems` default to `[]`
    (keeping every existing module literal unchanged); a non-empty `mems` puts the module on the
    per-access proof + co-simulation path (`moduleChecksb` returns `false`). -/
structure MemBlock where
  name      : String
  addrWidth : Nat
  dataWidth : Nat
  /-- Number of physical words. Addresses at or above size are out of bounds.
      The default retains the full address-space behavior of existing modules. -/
  size      : Nat := 2 ^ addrWidth
  /-- Optional complete initial image, in ascending address order. `none` leaves
      contents unconstrained; a present image must contain exactly `size`
      words (checked by `Module.checkErrors`). -/
  init      : Option (List (BitVec dataWidth)) := none
  writes    : List (MemWrite addrWidth dataWidth) := []
  reads     : List (MemRead addrWidth) := []

/-- A hardware module.  Combinational modules leave `regs = []` and `clock = none`. -/
structure Module where
  name    : String
  inputs  : List InPort
  outputs : List OutPort
  /-- Internal combinational signals, topologically ordered (each references only inputs,
      registers, and earlier wires).  Outputs and register next-state may reference them. -/
  wires   : List Wire     := []
  regs    : List Reg      := []
  /-- Level-sensitive transparent latches (F8), each `q' = if enable then d else q`.  Default `[]`
      keeps every existing module literal unchanged; a latch lowers to a `$dlatch` cell. -/
  latches : List Latch    := []
  /-- Addressed memory arrays (SRAM/RAM), each lowering to one `$mem_v2` cell via a compiler
      post-pass.  Default `[]` keeps every existing module literal unchanged; a non-empty `mems`
      excludes the module from the whole-design cycle theorems (`moduleChecksb` is `false`), whose
      behaviour is instead pinned per-access + validated by co-simulation. -/
  mems    : List MemBlock := []
  /-- Name of the clock input (1-bit), present iff the module is sequential. -/
  clock   : Option String := none
  /-- Name of an optional synchronous active-high reset input (1-bit). -/
  reset   : Option String := none
  /-- Declared header port order, when the specification fixes one.  The emitters render a
      *non-ANSI* header — names in the parenthesis list, directions and widths declared on their own
      lines below — so this reorders the parenthesis list only and carries no semantic content for
      any name-based consumer (Yosys `equiv_make` matches ports by name).  It exists because a
      testbench may bind by *position*, which no name-based check can see.  Default `[]` keeps every
      existing module literal unchanged and means inputs-then-outputs, the previous behaviour.  A
      non-empty value that is not a permutation of `inputs ++ outputs` is rejected by the emitter
      rather than silently ignored. -/
  portOrder : List String := []
  /-- Nondefault signedness/index labels of external ports, preserved by RTLIL.
      These do not change Expr semantics: signed operations are explicit nodes. -/
  portLayouts : List PortLayout := []
  /-- Verilog `parameter` declarations, each `(name, default value)`, in declaration order.

      A `Module` is always ONE member of a design family — the Lean design may be a family over a
      width (`implGen (M : Nat)`), but the netlist that gets emitted is monomorphic, so every width
      here is a literal `Nat`.  What this field adds is the *declaration* of which member: the
      emitted header carries `parameter N = 32;`, and a port whose width equals a declared
      parameter's value is rendered `[N-1:0]` rather than `[31:0]`.

      That is exactly what a benchmark testbench needs to elaborate `dut #(.N(32)) u (…)`, which is
      otherwise a hard elaboration error no amount of correct logic can survive.  It is NOT a claim
      that the emitted body is generic: overriding a parameter to a value other than its default
      gives a module whose header and body disagree, and nothing here or in the proofs covers that.
      The proof is about the family; this field records which member the netlist is.

      Default `[]` keeps every existing module literal unchanged. -/
  params : List (String × Nat) := []
  /-- Drive the ambient step timebase from a `#N` delay instead of a clock edge.

      `Module.step` / `Module.simulate` / `regTrace` are cycle-indexed and never ask what *causes*
      a cycle — a step is a step.  Emission does ask, and until now had exactly one answer: a
      posedge on `clock`.  A design whose prose names no clock input (a free-running generator
      driven by `initial` + `always #(PERIOD/2)`) therefore had nowhere to land: it compiled to a
      `$dff` with a constant clock net, which never fires, so a design whose Lean semantics were
      right emitted Verilog that does nothing.

      `stepDelay = some n` says "one step is `n` time units", and the emitter renders the register
      block as `always #n begin … end`.  Nothing about the *semantics* changes — this selects the
      driver of a step, not what a step does — so every theorem about `step`, `simulate` and
      `regTrace` carries over untouched.  What it costs is the equivalence miter: Yosys cannot
      read a delay-driven `always`, so the certified artifact is the clocked rendering of the same
      module and the shipped file must be checked to differ from it by exactly that one line. -/
  stepDelay : Option Nat := none

/-! ## Hierarchy

A `Parent` instantiates leaf `Module`s.  Each instance maps the child's input ports to parent-side
expressions; the child's outputs become parent signals named `"<instName>.<portName>"`.  Children
are plain `Module`s (no further instances), giving one level of hierarchy — Yosys flattens deeper
structure on demand.

Children may be **combinational** (`Parent.combOut` / `Parent.simulate`) *or* **sequential** (F10):
a clocked child's clock and reset are ordinary 1-bit parent inputs threaded into the child through
`ins` (e.g. `("clk", anyExpr (.var "clk" 1))`), and its registers persist across cycles under
`Parent.simulateSeq`.  The compiler needs no special case — `compileParent` lowers each child through
the M6-proven `compileModule` and `compileInst` wires every mapped port — so `write_verilog` emits a
real sequential module instantiation.  See `HierSeqCorrect.lean` for the proof-carrying story. -/

structure Inst where
  instName : String
  child    : Module
  /-- child input port ↦ parent-side expression (includes a clock/reset for a sequential child) -/
  ins      : List (String × AnyExpr)

structure Parent where
  name    : String
  inputs  : List InPort
  insts   : List Inst
  /-- output expressions, which may reference instance outputs as `var "<inst>.<port>" w` -/
  outputs : List OutPort
  /-- Name of the parent clock input (1-bit), present iff the hierarchy is sequential.  It is the
      clock the sequential flattening (`HierSeqCorrect.flattenParentSeq`) gives the flat module; the
      compiler instead threads it into each child through `ins`.  Default `none` (combinational). -/
  clock   : Option String := none
  /-- Name of an optional parent synchronous reset input (1-bit) for the sequential flattening. -/
  reset   : Option String := none

end LeanRTL
