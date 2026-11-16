import LeanRTL.Core.Syntax
import LeanRTL.Core.Backend
import LeanRTL.Core.Check
/-!
# The compiler (AST → RTLIL lowering)

`compile : Module → Backend.Design` walks the deep-embedded AST and emits coarse Yosys
cells (`$and`, `$add`, `$mux`, `$dff`, …).  It is kept deliberately structural: every
operator maps to exactly one cell with full-width buses, and `concat`/`zext` are pure
bus reassembly.  Net ids are allocated monotonically starting at 2.
-/

namespace LeanRTL
open Backend

/-- Compiler state: fresh-id counter, accumulated cells (reversed), a cell-name counter,
    and the name→bus environment for inputs and registers. -/
structure CState where
  nextId : Nat               := 2
  cells  : List Cell         := []
  count  : Nat               := 0
  env    : List (String × Bus) := []

abbrev CM := StateM CState

/-- Allocate `w` fresh net ids as an LSB-first bus. -/
def fresh (w : Nat) : CM Bus := do
  let s ← get
  let bus := (List.range w).map (fun i => Bit.net (s.nextId + i))
  set { s with nextId := s.nextId + w }
  return bus

def emit (type : String) (params : List (String × String))
    (portDirs : List (String × Dir)) (conns : List (String × Bus)) : CM Unit :=
  modify fun s =>
    { s with
      cells := { name := s!"$auto{s.count}", type := type, parameters := params,
                 portDirections := portDirs, connections := conns, hideName := true } :: s.cells,
      count := s.count + 1 }

/-- The constant bits (LSB first) of a literal bit-vector. -/
def constBits {w : Nat} (v : BitVec w) : Bus :=
  (List.range w).map (fun i => if v.getLsbD i then Bit.one else Bit.zero)

/-- Render a bit-vector as an RTLIL value parameter: a `w`-bit binary string, **MSB first**
    (the format Yosys writes for cell value params such as `$adff`'s `ARST_VALUE`). -/
def bitvecParam {w : Nat} (v : BitVec w) : String :=
  String.ofList (((List.range w).reverse).map (fun i => if v.getLsbD i then '1' else '0'))

/-- Standard params for a width-preserving unsigned binary op. -/
def binParams (w : Nat) : List (String × String) :=
  [("A_SIGNED", binStr32 0), ("B_SIGNED", binStr32 0),
   ("A_WIDTH", binStr32 w), ("B_WIDTH", binStr32 w), ("Y_WIDTH", binStr32 w)]

/-- Emit a width-`w` binary op cell over pre-compiled operand buses. -/
def emitBin (type : String) (w : Nat) (ba bb : Bus) : CM Bus := do
  let y ← fresh w
  emit type (binParams w)
    [("A", .input), ("B", .input), ("Y", .output)]
    [("A", ba), ("B", bb), ("Y", y)]
  return y

/-- Emit a comparison cell (operand width `w`, 1-bit result) over pre-compiled buses. -/
def emitCmp (type : String) (w : Nat) (ba bb : Bus) : CM Bus := do
  let y ← fresh 1
  emit type [("A_SIGNED", binStr32 0), ("B_SIGNED", binStr32 0),
             ("A_WIDTH", binStr32 w), ("B_WIDTH", binStr32 w), ("Y_WIDTH", binStr32 1)]
    [("A", .input), ("B", .input), ("Y", .output)]
    [("A", ba), ("B", bb), ("Y", y)]
  return y

/-- Emit a signed comparison cell (operand width `w`, 1-bit result). -/
def emitCmpSigned (type : String) (w : Nat) (ba bb : Bus) : CM Bus := do
  let y ← fresh 1
  emit type [("A_SIGNED", binStr32 1), ("B_SIGNED", binStr32 1),
             ("A_WIDTH", binStr32 w), ("B_WIDTH", binStr32 w), ("Y_WIDTH", binStr32 1)]
    [("A", .input), ("B", .input), ("Y", .output)]
    [("A", ba), ("B", bb), ("Y", y)]
  return y

/-- Emit a variable-shift cell: `A` (width `w`, signedness `aSigned`) shifted by unsigned
    `B` (width `k`), result width `w`. -/
def emitShift (type : String) (aSigned w k : Nat) (ba bb : Bus) : CM Bus := do
  let y ← fresh w
  emit type [("A_SIGNED", binStr32 aSigned), ("B_SIGNED", binStr32 0),
             ("A_WIDTH", binStr32 w), ("B_WIDTH", binStr32 k), ("Y_WIDTH", binStr32 w)]
    [("A", .input), ("B", .input), ("Y", .output)]
    [("A", ba), ("B", bb), ("Y", y)]
  return y

/-- Lower an expression to its result bus, allocating nets and emitting cells. -/
def compileExpr : {w : Nat} → Expr w → CM Bus
  | _, .const v => return constBits v
  | _, .var n w => do
      match (← get).env.lookup n with
      | some bus => return bus
      | none     => fresh w
  | w, .not a => do
      let ba ← compileExpr a
      let y ← fresh w
      emit "$not" [("A_SIGNED", binStr32 0), ("A_WIDTH", binStr32 w), ("Y_WIDTH", binStr32 w)]
        [("A", .input), ("Y", .output)] [("A", ba), ("Y", y)]
      return y
  | w, .and a b => do let ba ← compileExpr a; let bb ← compileExpr b; emitBin "$and" w ba bb
  | w, .or a b  => do let ba ← compileExpr a; let bb ← compileExpr b; emitBin "$or"  w ba bb
  | w, .xor a b => do let ba ← compileExpr a; let bb ← compileExpr b; emitBin "$xor" w ba bb
  | w, .add a b => do let ba ← compileExpr a; let bb ← compileExpr b; emitBin "$add" w ba bb
  | w, .sub a b => do let ba ← compileExpr a; let bb ← compileExpr b; emitBin "$sub" w ba bb
  | w, .mul a b => do let ba ← compileExpr a; let bb ← compileExpr b; emitBin "$mul" w ba bb
  | _, @Expr.shl w k a b => do
      let ba ← compileExpr a; let bb ← compileExpr b; emitShift "$shl" 0 w k ba bb
  | _, @Expr.shr w k a b => do
      let ba ← compileExpr a; let bb ← compileExpr b; emitShift "$shr" 0 w k ba bb
  | _, @Expr.sshr w k a b => do
      let ba ← compileExpr a; let bb ← compileExpr b; emitShift "$sshr" 1 w k ba bb
  | w, .udiv a b => do let ba ← compileExpr a; let bb ← compileExpr b; emitBin "$div" w ba bb
  | w, .umod a b => do let ba ← compileExpr a; let bb ← compileExpr b; emitBin "$mod" w ba bb
  | _, @Expr.eq w a b => do
      let ba ← compileExpr a; let bb ← compileExpr b; emitCmp "$eq" w ba bb
  | _, @Expr.ult w a b => do
      let ba ← compileExpr a; let bb ← compileExpr b; emitCmp "$lt" w ba bb
  | _, @Expr.slt w a b => do
      let ba ← compileExpr a; let bb ← compileExpr b; emitCmpSigned "$lt" w ba bb
  | w, .mux s a b => do
      let bs ← compileExpr s
      let ba ← compileExpr a    -- s = 1 branch
      let bb ← compileExpr b    -- s = 0 branch
      let y ← fresh w
      -- Yosys `$mux`: Y = S ? B : A.  Our `mux s a b = s ? a : b`  ⇒  B := ba, A := bb.
      emit "$mux" [("WIDTH", binStr32 w)]
        [("A", .input), ("B", .input), ("S", .input), ("Y", .output)]
        [("A", bb), ("B", ba), ("S", bs), ("Y", y)]
      return y
  | _, @Expr.concat a b ea eb => do
      let bhi ← compileExpr ea    -- width a, high bits
      let blo ← compileExpr eb    -- width b, low bits
      return blo ++ bhi           -- LSB-first: low bus then high bus
  | _, @Expr.zext w k a => do
      let ba ← compileExpr a
      return ba ++ List.replicate k Bit.zero
  | _, @Expr.sext _w k a => do
      let ba ← compileExpr a
      return ba ++ List.replicate k (ba.getLastD Bit.zero)
  | _, @Expr.extract _w i a => do
      let ba ← compileExpr a
      return [ba.getD i Bit.zero]   -- the i-th bit (LSB = 0)
  | _, @Expr.slice _w lo len a => do
      let ba ← compileExpr a
      let s := (ba.drop lo).take len
      return s ++ List.replicate (len - s.length) Bit.zero

/-! ## Module lowering, in explicit `foldlM`/`forM` phases.

The five phases below are written as folds (rather than `let mut`/`for`) so that each is amenable
to compositional reasoning in `CompilerCorrectSeq.lean` (M6b).  They emit exactly the same nets and
cells, in the same order, as the previous imperative formulation — the round-trip corpus is the
behavioural guard. -/

/-- Allocate a fresh net for one input port and bind it in the environment. -/
def compileInput (acc : List Port × List NetName) (p : InPort) : CM (List Port × List NetName) := do
  let bus ← fresh p.width
  modify fun s => { s with env := (p.name, bus) :: s.env }
  return (acc.1 ++ [{ name := p.name, dir := .input, bits := bus }],
          acc.2 ++ [{ name := p.name, bits := bus }])

/-- Allocate a fresh `Q` net for one register and bind it (before its next-state logic).

    The Q net carries an RTLIL `init` attribute set to the register's power-on value `r.init`
    (a width-bit MSB-first binary string) when `r.emitInit` is true. This default is independent
    of reset; imported registers without a power-on constraint set `emitInit := false`, so
    `yosys write_verilog` lowers it to an `initial` statement (F7).  It is orthogonal to the
    synchronous-reset mux in `compileDffSync`, which handles the reset-input behaviour. -/
def compileReg (acc : List (String × Bus) × List NetName) (r : Reg) :
    CM (List (String × Bus) × List NetName) := do
  let bus ← fresh r.width
  modify fun s => { s with env := (r.name, bus) :: s.env }
  return (acc.1 ++ [(r.name, bus)],
          acc.2 ++ [{ name := r.name, bits := bus,
                      attrs := if r.emitInit then [("init", bitvecParam r.init)] else [] }])

/-- Compile one internal wire's cone and bind the result net by name. -/
def compileWire (acc : List NetName) (w : Wire) : CM (List NetName) := do
  let bus ← compileExpr w.expr
  modify fun s => { s with env := (w.name, bus) :: s.env }
  return acc ++ [{ name := w.name, bits := bus }]

/-- Emit the next-state cone (with optional synchronous-reset mux) and the `$dff` for one
    *synchronous* register.  This is the original (M6-proven) flip-flop emission; `compileDff`
    delegates to it whenever the register has no asynchronous reset (`r.asyncReset = none`). -/
def compileDffSync (regBuses : List (String × Bus)) (reset clock : Option String) (r : Reg) :
    CM Bus := do
  let qbus := (regBuses.lookup r.name).getD []
  let dbus ← compileExpr r.next
  let dbus2 ← (do
    match reset with
    | some rstName =>
        let sbus := ((← get).env.lookup rstName).getD [Bit.zero]
        let y ← fresh r.width
        -- D' = reset ? init : D   (Yosys $mux Y = S?B:A)
        emit "$mux" [("WIDTH", binStr32 r.width)]
          [("A", .input), ("B", .input), ("S", .input), ("Y", .output)]
          [("A", dbus), ("B", constBits r.init), ("S", sbus), ("Y", y)]
        pure y
    | none => pure dbus : CM Bus)
  let s ← get
  let clkBus := match clock with
    | some c => (s.env.lookup c).getD [Bit.zero]
    | none   => [Bit.zero]
  -- F1: CLK_POLARITY = 0 for a negedge register (`always @(negedge clk)`), 1 for posedge.
  emit "$dff" [("CLK_POLARITY", binStr32 (if r.negedge then 0 else 1)), ("WIDTH", binStr32 r.width)]
    [("CLK", .input), ("D", .input), ("Q", .output)]
    [("CLK", clkBus), ("D", dbus2), ("Q", qbus)]
  return dbus2

/-- Emit the next-state cone and an `$adff` cell for one *asynchronous-reset* register.  An
    async reset fires between clock edges, so (unlike a synchronous reset) it cannot be lowered
    to a `$dff` + reset mux; it needs a real `$adff` cell (`Q ← rstVal` while `arstNet` is at its
    active level, else `Q ← D` on the clock edge).  `ARST_POLARITY` carries the register's declared
    reset polarity, so an active-low `rst_n` reaches the cell as the port itself rather than through
    an inverter net — `write_verilog` then renders `always @(posedge clk or negedge rst_n)` and the
    reset does not lag the port by a delta.  Clock polarity is `r.negedge` as usual. -/
def compileDffAsync (regBuses : List (String × Bus)) (clock : Option String) (r : Reg)
    (arstName : String) (arstActiveHi : Bool) (arstVal : BitVec r.width) : CM Bus := do
  let qbus := (regBuses.lookup r.name).getD []
  let dbus2 ← compileExpr r.next
  let s ← get
  let clkBus := match clock with
    | some c => (s.env.lookup c).getD [Bit.zero]
    | none   => [Bit.zero]
  let arstBus := (s.env.lookup arstName).getD [Bit.zero]
  emit "$adff"
    [("ARST_POLARITY", binStr32 (if arstActiveHi then 1 else 0)), ("ARST_VALUE", bitvecParam arstVal),
     ("CLK_POLARITY", binStr32 (if r.negedge then 0 else 1)), ("WIDTH", binStr32 r.width)]
    [("ARST", .input), ("CLK", .input), ("D", .input), ("Q", .output)]
    [("ARST", arstBus), ("CLK", clkBus), ("D", dbus2), ("Q", qbus)]
  return dbus2

/-- Emit the flip-flop for one register, branching on its (optional) asynchronous reset.  With
    `r.asyncReset = none` this is *definitionally* the synchronous `compileDffSync` body (so the
    M6 proofs reduce with a single `r.asyncReset = none` rewrite); with `some (arst, val)` it
    emits an `$adff` instead. -/
def compileDff (regBuses : List (String × Bus)) (reset clock : Option String) (r : Reg) :
    CM Bus :=
  match r.asyncReset with
  | none => compileDffSync regBuses reset clock r
  | some (arstName, arstActiveHi, arstVal) =>
      compileDffAsync regBuses clock r arstName arstActiveHi arstVal

/-- Compile every register's next-state logic + flip-flop, returning each register's D-bus (the
    value clocked in next cycle).  Cell emission is identical to running `compileDff` per register;
    the returned buses are for reasoning (M6b). -/
def compileDffs (regBuses : List (String × Bus)) (reset clock : Option String) (regs : List Reg) :
    CM (List Bus) :=
  regs.foldlM (fun acc r => do let d ← compileDff regBuses reset clock r; pure (acc ++ [d])) []

/-- Compile one output port's cone. -/
def compileOutput (acc : List Port × List NetName) (o : OutPort) :
    CM (List Port × List NetName) := do
  let bus ← compileExpr o.expr
  return (acc.1 ++ [{ name := o.name, dir := .output, bits := bus }],
          acc.2 ++ [{ name := o.name, bits := bus }])

/-- Share attributes across `NetName`s that carry the same name.  The common Verilog idiom
    `output reg q` makes a register and an output port name the *one* physical wire, so both
    `compileReg` and `compileOutput` emit a `NetName` for it; the RTLIL-JSON object then holds
    that key twice and Yosys keeps the last one, which would drop the register's `init` attribute
    carried on the earlier (register) entry.  Giving *every* occurrence of a name the union of
    that name's attributes makes `init` survive onto whichever entry wins — without touching bit
    assignments (the entries share the same bus, so this only moves attributes). -/
def propagateNetAttrs (nets : List NetName) : List NetName :=
  nets.map fun n => { n with attrs := (nets.filter (·.name == n.name)).flatMap (·.attrs) }

/-- Lower a whole module to an RTLIL module. -/
def compileModuleM (m : Module) : CM Backend.Module := do
  let (inPorts, inNets) ← m.inputs.foldlM compileInput ([], [])
  let (regBuses, regNets) ← m.regs.foldlM compileReg ([], [])
  let wireNets ← m.wires.foldlM compileWire []
  let _ ← compileDffs regBuses m.reset m.clock m.regs
  let (outPorts, outNets) ← m.outputs.foldlM compileOutput ([], [])
  return { name := m.name, ports := inPorts ++ outPorts,
           cells := (← get).cells.reverse,
           netnames := propagateNetAttrs (inNets ++ regNets ++ wireNets ++ outNets) }

/-! ## Transparent-latch lowering (F8)

A `$dlatch` cell realizes the level-sensitive law `Q = EN ? D : (held Q)` (`EN_POLARITY = 1`), which
`write_verilog` renders as `always @(*) if (en) q = d;`.  A latch's `Q` net is **shared** with
whatever the compiled module already bound to the latch's name — the `output reg q` idiom makes the
module output (or an internal wire) and the latch one physical net — or a fresh net if the name is
otherwise undeclared.

Latch lowering is a *post-pass* over the (M6-proven) `compileModuleM` output: the input/register/
wire/dff/output lowering is exactly `compileModuleM`, so every compiler-correctness theorem (all
stated about `compileModuleM`) applies verbatim, and the `$dlatch` cells are appended afterwards. -/

/-- Emit one `$dlatch` cell driving `qbus` from `l.enable` (EN) and `l.d` (D). -/
def compileLatchCell (qbus : Bus) (l : Latch) : CM Unit := do
  let enBus ← compileExpr l.enable
  let dBus  ← compileExpr l.d
  emit "$dlatch" [("EN_POLARITY", binStr32 1), ("WIDTH", binStr32 l.width)]
    [("EN", .input), ("D", .input), ("Q", .output)]
    [("EN", enBus), ("D", dBus), ("Q", qbus)]

/-- The physical net a latch shares: the bus the compiled module already gave the latch's name (an
    output port or internal wire), else `none` (the latch needs a fresh net + netname). -/
def latchQBus (bm : Backend.Module) (name : String) : Option Bus :=
  match bm.ports.find? (·.name == name) with
  | some p => some p.bits
  | none   => (bm.netnames.find? (·.name == name)).map (·.bits)

/-- Lower every latch to a `$dlatch`, returning the *new* netnames (only for latches whose net was
    not already declared by an output/wire; a shared-net latch adds no netname). -/
def compileLatches (seed : List (String × Bus)) (bm : Backend.Module) (latches : List Latch) :
    CM (List NetName) :=
  latches.foldlM (fun acc l => do
    -- The SEEDED net is the one the module body compiled its `.var l.name` references against
    -- (`seedLatchNets` bound it in the env before `compileModuleM` ran), so it is the net the
    -- `$dlatch` must drive.  Allocating a different one here is exactly the STRIKE-4 bug: the
    -- body would read an undriven net while the latch drove an unread one, and `opt_clean` would
    -- then delete the `$dlatch` as dead.  Fall back to the old port/netname sharing only when
    -- there is no seed (i.e. a caller that did not seed).
    match seed.lookup l.name with
    | some qbus => do
        compileLatchCell qbus l
        -- A port or wire already declaring this name carries the net; otherwise declare it.
        pure (if (latchQBus bm l.name).isSome then acc
              else acc ++ [{ name := l.name, bits := qbus }])
    | none =>
      match latchQBus bm l.name with
      | some qbus => do compileLatchCell qbus l; pure acc
      | none      => do
          let qbus ← fresh l.width
          compileLatchCell qbus l
          pure (acc ++ [{ name := l.name, bits := qbus }])) []

/-! ## Async-load lowering (F6 — `$aldff`)

An `$aldff` cell realizes `Q ← AD` *asynchronously* while `ALOAD` is at its active level (per
`ALOAD_POLARITY`), and `Q ← D` on the active clock edge otherwise — i.e. an asynchronous load of the
*dynamic* data bus `AD` (an arbitrary compiled `Expr`, typically an input port), which the constant
`$adff`/`asyncReset` path cannot express.  `write_verilog` renders it as
`always @(posedge clk or negedge net) if (!net) q <= AD; else q <= D;` (active-low shown).

Like the F8 `$dlatch` post-pass, this is a lowering pass over the (M6-proven) `compileModuleM`
output, carrying **no** compiler-correctness theorem: an `asyncLoad` register is excluded from the
whole-design theorems (`moduleChecksb` returns `false` for it, exactly as for `asyncReset`), its
behaviour is characterized per-instance by `Reg.aldffDen`, and the emitted `$aldff` is validated by
co-simulation.  Unlike the latch pass (which only *appends* `$dlatch` cells), each `asyncLoad`
register already had a `$dff` emitted by `compileDff`; this pass *rewrites that one cell in place*
into a `$aldff` — identified unambiguously by its `Q` bus — adding the `ALOAD` (the async net) and
`AD` (the compiled load value) connections. -/

/-- A pending async-load rewrite: `(qbus, aloadBus, adBus, activeHi)` — rewrite the `$dff` whose `Q`
    connection is `qbus` into a `$aldff` with `ALOAD := aloadBus`, `AD := adBus`, and
    `ALOAD_POLARITY := if activeHi then 1 else 0`. -/
abbrev AldffRewrite := Bus × Bus × Bus × Bool

/-- Rewrite a single `$dff` cell into a `$aldff` when its `Q` bus matches a pending async-load
    rewrite; every other cell (including `$dlatch`es and non-matching `$dff`s) passes through. -/
def applyAldff (rewrites : List AldffRewrite) (c : Cell) : Cell :=
  if c.type = "$dff" then
    match rewrites.find? (fun (q, _, _, _) => decide (c.connections.lookup "Q" = some q)) with
    | some (_, aloadBus, adBus, activeHi) =>
        { c with
          type := "$aldff",
          parameters := c.parameters ++ [("ALOAD_POLARITY", binStr32 (if activeHi then 1 else 0))],
          portDirections := c.portDirections ++ [("ALOAD", .input), ("AD", .input)],
          connections := c.connections ++ [("ALOAD", aloadBus), ("AD", adBus)] }
    | none => c
  else c

/-- Collect the async-load rewrites for a module's registers, compiling each load value's `AD` cone
    (this emits its cells into the state) and looking up the async net's `ALOAD` bus and the
    register's `Q` bus from the post-`compileModuleM` environment. -/
def collectAldffRewrites (regs : List Reg) : CM (List AldffRewrite) :=
  regs.foldlM (fun acc r => do
    match r.asyncLoad with
    | none => pure acc
    | some (net, activeHi, val) => do
        let qbus    := ((← get).env.lookup r.name).getD []
        let aloadBus := ((← get).env.lookup net).getD [Bit.zero]
        let adBus ← compileExpr val
        pure (acc ++ [(qbus, aloadBus, adBus, activeHi)])) []

/-! ## Multi-clock / gated-clock lowering (F11 — per-register clock net)

`compileModuleM` emits every register's flip-flop with `CLK` driven by the *module* clock.  A register
carrying `Reg.clockNet = some clkExpr` must instead be clocked off the *derived* net `eval clkExpr` —
a second clock domain (`.var "clk2" 1`), a gated clock (`.and clk (.not gate)`), or a data signal used
as a clock.  Exactly like the F6 `$aldff` rewrite, this is a lowering *post-pass* over the M6-proven
`compileModuleM` output that carries **no** compiler-correctness theorem: a `clockNet` register is
excluded from the whole-design cycle theorems (`moduleChecksb` returns `false`, as for `asyncReset`),
its next-state is characterized per-instance in the design file, and the emitted netlist is validated
by co-simulation.

The rewrite compiles `clkExpr`'s cone (so a gated clock's `$and`/`$not` cells are emitted) and replaces
the `CLK` connection of the register's flip-flop — identified unambiguously by its `Q` bus — with the
compiled clock bus.  It applies to whichever flip-flop kind `compileModuleM`/the `$aldff` pass produced
(`$dff`, `$adff`, or `$aldff`); every other cell passes through unchanged. -/

/-- A pending per-register clock rewrite: `(qbus, clkBus)` — drive the flip-flop whose `Q` connection
    is `qbus` from `CLK := clkBus` (the compiled derived/gated clock), replacing the module-clock
    `CLK` that `compileModuleM` emitted. -/
abbrev ClockRewrite := Bus × Bus

/-- Rewrite the `CLK` connection of a flip-flop cell (`$dff`/`$adff`/`$aldff`) whose `Q` bus matches a
    pending clock rewrite; every other cell (and non-matching flip-flop) passes through. -/
def applyClock (rewrites : List ClockRewrite) (c : Cell) : Cell :=
  if c.type = "$dff" || c.type = "$adff" || c.type = "$aldff" then
    match rewrites.find? (fun (q, _) => decide (c.connections.lookup "Q" = some q)) with
    | some (_, clkBus) =>
        { c with connections := c.connections.map
                   (fun (k, b) => if k = "CLK" then (k, clkBus) else (k, b)) }
    | none => c
  else c

/-- Collect the per-register clock rewrites, compiling each derived clock's cone (this emits its
    `$and`/`$not`/… cells into the state) and looking up the register's `Q` bus from the
    post-`compileModuleM` environment. -/
def collectClockRewrites (regs : List Reg) : CM (List ClockRewrite) :=
  regs.foldlM (fun acc r => do
    match r.clockNet with
    | none => pure acc
    | some clkExpr => do
        let qbus    := ((← get).env.lookup r.name).getD []
        let clkBus ← compileExpr clkExpr
        pure (acc ++ [(qbus, clkBus)])) []

/-! ## Addressed-memory lowering (`$mem_v2`)

A `MemBlock` lowers to a single Yosys `$mem_v2` cell — the array-level memory primitive — which
`write_verilog` renders as `reg [DW-1:0] mem [0:2^AW-1]; always @(posedge wclk) if (we) mem[waddr]
<= wdata; assign rout = mem[raddr];`.  This is what lets a 1 KB SRAM be one cell instead of
thousands of `$dff`s.

Like the F8/F6/F11 post-passes, memory lowering is a pass over the (M6-proven) `compileModuleM`
output carrying **no** compiler-correctness theorem: a module with `mems ≠ []` is excluded from the
whole-design theorems (`moduleChecksb` returns `false`), its memory is characterized per-access
(`MemBlock.read_after_write`), and the emitted `$mem_v2` is validated by co-simulation.

Read-port outputs are handled like the F8 latch's shared net, but *pre-seeded*: `seedMemReadNets`
allocates one fresh bus per read port's `out` name and binds it in the environment **before**
`compileModuleM` runs, so any downstream reference (`var out dw` in an output/wire/register cone)
compiles to that same bus — which the `$mem_v2` read port then drives.  For a mem-free module
(`mems = []`) `seedMemReadNets` is a no-op, so `compileModuleFull` is byte-identical to before. -/

/-- `n` copies of char `c` as a String — an RTLIL bit-string at a uniform logic level (`'0'`/`'1'`/`'x'`). -/
def repChar (c : Char) (n : Nat) : String := String.ofList (List.replicate n c)

/-- Pre-allocate one fresh `dataWidth`-bit bus per memory read port's `out` name and bind it in the
    environment (so downstream references connect to it), returning the `(out, bus)` seed map.  Runs
    *before* `compileModuleM`; a no-op when there are no memories. -/
def seedMemReadNets (mems : List MemBlock) : CM (List (String × Bus)) :=
  mems.foldlM (fun acc mem =>
    mem.reads.foldlM (fun acc2 rd => do
      let bus ← fresh mem.dataWidth
      modify fun s => { s with env := (rd.out, bus) :: s.env }
      pure (acc2 ++ [(rd.out, bus)])) acc) []

/-- Pre-allocate one fresh `width`-bit bus per latch `name` and bind it in the environment, so a
    wire / output / register cone that reads the latch's `Q` resolves to the latch's own net rather
    than to a fresh floating one.  Runs *before* `compileModuleM`; a no-op when there are no
    latches.  Mirrors `seedMemReadNets` exactly. -/
def seedLatchNets (latches : List Latch) : CM (List (String × Bus)) :=
  latches.foldlM (fun acc l => do
    let bus ← fresh l.width
    modify fun s => { s with env := (l.name, bus) :: s.env }
    pure (acc ++ [(l.name, bus)])) []

/-- Compile one `MemBlock` to a `$mem_v2` cell.  Each write/read port's cones are emitted into the
    compiler state (via `compileExpr`, so a data-signal write clock or an addressed cone lands as
    ordinary cells); the read-port output buses are the ones `seedMemReadNets` pre-allocated (looked
    up in `readSeed`).  Port arrays are the per-port buses concatenated LSB-first, matching Yosys'
    `$mem_v2` layout. -/
def compileMemCell (readSeed : List (String × Bus)) (mem : MemBlock) : CM Cell := do
  let dw := mem.dataWidth
  let aw := mem.addrWidth
  let mut wrClk : Bus := []; let mut wrEn : Bus := []
  let mut wrAddr : Bus := []; let mut wrData : Bus := []
  for w in mem.writes do
    let cb ← compileExpr w.clock
    let eb ← compileExpr w.en
    let ab ← compileExpr w.addr
    let db ← compileExpr w.data
    wrClk  := wrClk  ++ cb
    wrEn   := wrEn   ++ List.replicate dw (eb.getD 0 Bit.zero)   -- $mem_v2 WR_EN is per-bit
    wrAddr := wrAddr ++ ab
    wrData := wrData ++ db
  let mut rdAddr : Bus := []; let mut rdData : Bus := []
  for r in mem.reads do
    let ab ← compileExpr r.addr
    let db := (readSeed.lookup r.out).getD (List.replicate dw Bit.zero)
    rdAddr := rdAddr ++ ab
    rdData := rdData ++ db
  let rp := mem.reads.length
  let wp := mem.writes.length
  let params : List (String × String) :=
    [ ("MEMID", "\\" ++ mem.name),
      ("ABITS", binStr32 aw), ("WIDTH", binStr32 dw),
      ("SIZE", binStr32 mem.size), ("OFFSET", binStr32 0),
      ("INIT", match mem.init with
        | none => repChar 'x' (mem.size * dw)
        | some words => String.join (words.reverse.map bitvecParam)),
      ("RD_PORTS", binStr32 rp), ("WR_PORTS", binStr32 wp),
      ("RD_CLK_ENABLE", repChar '0' rp), ("RD_CLK_POLARITY", repChar '0' rp),
      ("RD_WIDE_CONTINUATION", repChar '0' rp), ("RD_CE_OVER_SRST", repChar '0' rp),
      ("RD_TRANSPARENCY_MASK", repChar '0' (rp * wp)),
      ("RD_COLLISION_X_MASK", repChar '0' (rp * wp)),
      ("RD_ARST_VALUE", repChar 'x' (rp * dw)),
      ("RD_SRST_VALUE", repChar 'x' (rp * dw)),
      ("RD_INIT_VALUE", repChar 'x' (rp * dw)),
      ("WR_CLK_ENABLE", repChar '1' wp), ("WR_CLK_POLARITY", repChar '1' wp),
      ("WR_PRIORITY_MASK", repChar '0' (wp * wp)),
      ("WR_WIDE_CONTINUATION", repChar '0' wp) ]
  let portDirs : List (String × Dir) :=
    [ ("RD_ADDR", .input), ("RD_ARST", .input), ("RD_CLK", .input), ("RD_DATA", .output),
      ("RD_EN", .input), ("RD_SRST", .input),
      ("WR_ADDR", .input), ("WR_CLK", .input), ("WR_DATA", .input), ("WR_EN", .input) ]
  let conns : List (String × Bus) :=
    [ ("RD_ADDR", rdAddr), ("RD_ARST", List.replicate rp Bit.zero),
      ("RD_CLK", List.replicate rp Bit.x), ("RD_DATA", rdData),
      ("RD_EN", List.replicate rp Bit.one), ("RD_SRST", List.replicate rp Bit.zero),
      ("WR_ADDR", wrAddr), ("WR_CLK", wrClk), ("WR_DATA", wrData), ("WR_EN", wrEn) ]
  pure { name := "$mem$" ++ mem.name, type := "$mem_v2",
         parameters := params, portDirections := portDirs, connections := conns, hideName := true }

/-- `compileModuleM` extended with the F8 transparent-latch, F6 async-load (`$aldff`), F11
    per-register clock (multi-clock / gated-clock), and addressed-memory (`$mem_v2`) post-passes.

    **Post-pass pipeline contract (ordering rationale).**  Each rewrite pass identifies its target
    flip-flop by the register's *unique* `Q` bus, so a rewrite can never hit the wrong cell.  Running
    `applyAldff` before `applyClock` is safe because the two touch **disjoint connection keys**:
    `applyAldff` retypes `$dff → $aldff` and *adds* `ALOAD`/`AD` (never touching `CLK`), while
    `applyClock` *replaces* only `CLK` — and it matches all of `$dff`/`$adff`/`$aldff`, so a register
    carrying both rewrites is still found after its retype.  The `$mem_v2` cells are **appended
    outside the rewrite scan** (`allCells ++ memCells`), so they are never rewrite targets; the port
    cones `compileMemCell` emits into the state are ordinary combinational cells that pass through
    the scan unmatched (no flip-flop kind, no matching `Q`). -/
def compileModuleFull (m : Module) : CM Backend.Module := do
  let readSeed ← seedMemReadNets m.mems
  -- F8 latches must be seeded for the SAME reason memory read-port outputs are: `compileLatches`
  -- runs AFTER the module body, so a wire/output cone that references a latch's Q would compile
  -- against a name the env does not yet know, and `compileExpr`'s `| none => fresh w` fallback
  -- would silently allocate a FLOATING net — the `$dlatch` then gets dead-code-eliminated and
  -- `build`/`check`/`emit` all report success on a netlist that is not the proven circuit.
  -- Four RealBench authors hit this independently; see docs/plan/friction.v1.5.md (STRIKE-4).
  let latchSeed ← seedLatchNets m.latches
  let bm ← compileModuleM m
  let latchNets ← compileLatches latchSeed bm m.latches
  let rewrites ← collectAldffRewrites m.regs
  let clockRewrites ← collectClockRewrites m.regs
  let memCells ← m.mems.mapM (compileMemCell readSeed)   -- emits port cones into state, returns $mem_v2 cells
  let allCells := (((← get).cells.reverse).map (applyAldff rewrites)).map (applyClock clockRewrites)
  let readNetNames := readSeed.map (fun p => ({ name := p.1, bits := p.2 } : NetName))
  let ports := if m.portOrder.isEmpty || m.portOrder.length != bm.ports.length ||
      !bm.ports.all (fun p => m.portOrder.contains p.name) then bm.ports else
    m.portOrder.filterMap (fun name => bm.ports.find? (fun p => p.name == name))
  return { bm with cells := allCells ++ memCells, ports := ports, portLayouts := m.portLayouts,
                   netnames := bm.netnames ++ latchNets ++ readNetNames }

def compileModule (m : Module) : Backend.Module := (compileModuleFull m).run' {}

/-- Compile a (currently flat) module into an RTLIL design. -/
def compile (m : Module) : Backend.Design := { modules := [compileModule m] }

/-- Render a module straight to RTLIL JSON text. -/
def Module.toRtlilJson (m : Module) : String := (compile m).render

/-- Yosys write_verilog deliberately emits unsigned declarations. Keep signed
    external ports in a wiring-only wrapper, with a canonical unsigned core. -/
def Module.interfaceCoreName (m : Module) : String := m.name ++ "__v2lean_core"

def Module.interfaceInstanceName (m : Module) : String :=
  let used := m.inputs.map (·.name) ++ m.outputs.map (·.name)
  ((List.range (used.length + 1)).map (fun n => "__v2lean_core_" ++ toString n)).find?
    (fun n => !used.contains n) |>.getD "__v2lean_core_fallback"

def Module.interfaceCore (m : Module) : Module :=
  if m.portLayouts.isEmpty then m else { m with name := m.interfaceCoreName, portLayouts := [] }

private def interfaceIdent (name : String) : String :=
  if name.all (fun c => c.isAlphanum || c == '_' || c == '$') then name else "\\" ++ name ++ " "

/-- Generated entirely from the Module's checked interface metadata. Connections
    are whole, equal-width words; internal Expr indices remain LSB-relative. -/
def Module.interfaceWrapper (m : Module) : String :=
  if m.portLayouts.isEmpty then "" else Id.run do
    let names := m.inputs.map (·.name) ++ m.outputs.map (·.name)
    let order := if m.portOrder.isEmpty then names else m.portOrder
    let decl := fun (dir name : String) (width : Nat) =>
      let p := (m.portLayouts.find? (fun p => p.name == name)).getD { name := name }
      let hi := p.offset + Int.ofNat (width - 1)
      let range := if width == 1 && p.offset == 0 then "" else
        if p.upto then s!"[{p.offset}:{hi}] " else s!"[{hi}:{p.offset}] "
      s!"  {dir} {if p.signed then "signed " else ""}{range}{interfaceIdent name};"
    let dirs := m.inputs.map (fun p => decl "input" p.name p.width) ++
                m.outputs.map (fun p => decl "output" p.name p.width)
    let connections := names.map (fun n => s!".{interfaceIdent n}({interfaceIdent n})")
    return "module " ++ interfaceIdent m.name ++ "(" ++ String.intercalate ", " (order.map interfaceIdent) ++ ");\n" ++
      String.intercalate "\n" dirs ++ "\n  " ++ interfaceIdent m.interfaceCoreName ++ " " ++
      m.interfaceInstanceName ++ "(" ++ String.intercalate ", " connections ++ ");\nendmodule\n"

/-! ## Hierarchy lowering

A child instance is lowered structurally, so **sequential** children work with no special case (F10):
each child is compiled by the M6-proven `compileModule` (which handles registers, clock, reset), and
`compileInst` wires *every* mapped port — a sequential child's clock/reset are ordinary parent inputs
threaded through `inst.ins` (e.g. `("clk", anyExpr (.var "clk" 1))`).  The emitted RTLIL is a real
sequential module instantiation cell that `yosys write_verilog` renders as `child inst (.clk(clk),
…);`.  The semantic model of the sequential composition and its proof-carrying flattening live in
`Semantics.Parent.simulateSeq` / `HierSeqCorrect.lean`. -/

/-- Build one instance cell: connect the child's input ports to compiled parent
    expressions, allocate fresh buses for the child's outputs, and register those output
    wires in the env under `"<instName>.<port>"`.  Works uniformly for combinational and
    sequential children (a sequential child's clock/reset arrive as ordinary mapped ports). -/
def compileInst (inst : Inst) : CM Cell := do
  let inConns ← inst.ins.mapM (fun (port, ae) => do
    let b ← compileExpr ae.2
    pure (port, b))
  let mut outConns : List (String × Bus) := []
  for o in inst.child.outputs do
    let b ← fresh o.width
    modify fun s => { s with env := (inst.instName ++ "." ++ o.name, b) :: s.env }
    outConns := outConns ++ [(o.name, b)]
  let portDirs := inst.child.inputs.map (fun p => (p.name, Dir.input))
                    ++ inst.child.outputs.map (fun o => (o.name, Dir.output))
  pure { name := inst.instName, type := inst.child.name,
         portDirections := portDirs, connections := inConns ++ outConns, hideName := false }

/-- **Pass 1 of the two-pass parent lowering.**  Pre-register one instance's output nets: allocate a
    fresh bus per output and bind it in the env under `"<instName>.<port>"`, returning the
    `(port, bus)` output-connection list so `compileInstBody` reuses those very nets.  Running this
    over *every* instance before any `ins` cone is compiled is what makes instance-level feedback
    (a forward `.var "<inst>.<port>"`) resolve to a real net instead of a dangling fresh one. -/
def preRegisterInstOuts (inst : Inst) : CM (List (String × Bus)) := do
  let mut outConns : List (String × Bus) := []
  for o in inst.child.outputs do
    let b ← fresh o.width
    modify fun s => { s with env := (inst.instName ++ "." ++ o.name, b) :: s.env }
    outConns := outConns ++ [(o.name, b)]
  pure outConns

/-- **Pass 2 of the two-pass parent lowering.**  Compile one instance's body against the complete
    net table: its input-connection cones (which now see *every* instance's pre-registered outputs,
    so forward/feedback references resolve to real nets) plus the pre-registered output connections
    (`outConns`, allocated in pass 1 — never re-allocated here).  Structurally identical to
    `compileInst` except the outputs are supplied rather than freshly allocated. -/
def compileInstBody (inst : Inst) (outConns : List (String × Bus)) : CM Cell := do
  let inConns ← inst.ins.mapM (fun (port, ae) => do
    let b ← compileExpr ae.2
    pure (port, b))
  let portDirs := inst.child.inputs.map (fun p => (p.name, Dir.input))
                    ++ inst.child.outputs.map (fun o => (o.name, Dir.output))
  pure { name := inst.instName, type := inst.child.name,
         portDirections := portDirs, connections := inConns ++ outConns, hideName := false }

def dedupModules (ms : List Module) : List Module :=
  ms.foldl (fun acc m => if acc.any (·.name == m.name) then acc else acc ++ [m]) []

/-- Lower a hierarchical parent's top module.

    **Two-pass, byte-identity preserving.**  When the parent is declaration-order-resolvable
    (`p.hasForwardInstRef = false` — every `ins` reference to an instance output points at an
    *earlier* instance, which is the entire pre-M34a corpus), the SINGLE-pass lowering runs: each
    instance is compiled by `compileInst` in declaration order, allocating its `ins` cones then its
    output nets.  This is bit-for-bit the pre-M34a code path, so extracted RTLIL is byte-identical.

    When the parent has a self/forward instance reference (legal instance-level feedback, e.g. a
    CDC pointer pair or an LMS loop), the TWO-pass lowering runs: pass 1 (`preRegisterInstOuts`)
    pre-registers *every* instance's output nets, then pass 2 (`compileInstBody`) compiles the
    `ins` cones against the now-complete net table.  A forward `.var "<inst>.<port>"` therefore
    resolves to the real pre-registered net instead of a dangling fresh one (closing the
    friction-ledger strike-2/3 Parent forward-reference gap).  Combinational-loop freedom (that the
    feedback actually crosses a register) is not proven here — a true bit-level comb loop is caught
    downstream by Yosys `hierarchy -check` / co-simulation, as with any flat netlist. -/
def compileParentM (p : Parent) : CM Backend.Module := do
  let mut inPorts : List Port := []
  let mut nets : List NetName := []
  for pt in p.inputs do
    let bus ← fresh pt.width
    modify fun s => { s with env := (pt.name, bus) :: s.env }
    inPorts := inPorts ++ [{ name := pt.name, dir := .input, bits := bus }]
    nets := nets ++ [{ name := pt.name, bits := bus }]
  let mut instCells : List Cell := []
  if p.hasForwardInstRef then
    -- Two-pass: pre-register all instance outputs (pass 1), then compile bodies (pass 2).
    let outMaps ← p.insts.mapM preRegisterInstOuts
    for (inst, outConns) in p.insts.zip outMaps do
      let c ← compileInstBody inst outConns
      instCells := instCells ++ [c]
  else
    -- Single-pass (byte-identical to the pre-M34a path for forward-only parents).
    for inst in p.insts do
      let c ← compileInst inst
      instCells := instCells ++ [c]
  let mut outPorts : List Port := []
  for o in p.outputs do
    let bus ← compileExpr o.expr
    outPorts := outPorts ++ [{ name := o.name, dir := .output, bits := bus }]
    nets := nets ++ [{ name := o.name, bits := bus }]
  return { name := p.name, ports := inPorts ++ outPorts,
           cells := (← get).cells.reverse ++ instCells, netnames := nets }

/-- Compile a hierarchical parent: the top module plus every distinct child module, so
    Yosys `hierarchy -check` resolves all instances. -/
def compileParent (p : Parent) : Backend.Design :=
  let top := (compileParentM p).run' {}
  let children := (dedupModules (p.insts.map (·.child))).map compileModule
  { modules := top :: children }

def Parent.toRtlilJson (p : Parent) : String := (compileParent p).render

end LeanRTL
