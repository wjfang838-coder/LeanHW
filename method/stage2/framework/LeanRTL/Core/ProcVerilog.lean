import LeanRTL.Core.Syntax
import LeanRTL.Core.Semantics
/-!
# F9 — procedural next-state Verilog emitter.

`emitProcVerilog` renders a monomorphic `Module` as **procedural** SystemVerilog in which every
register's next-state is computed *inside* the clocked `always` block, with the register's mux
decision-tree lowered to `if / else` **statements** (not a continuous-assign `$mux` cone feeding the
flip-flop).  Two cosim-fidelity properties follow, and they are exactly what the RTLIL→`write_verilog`
netlist path (`assign nxt = f(inputs); always @(posedge) q <= nxt;`) fails to provide:

1. **No delta-cycle race.**  The clocked block reads the module's inputs *directly* (via
   blocking-assigned temporaries computed at block-execution time), so a testbench that drives an
   input with a *blocking* assignment at the clock edge (VerilogEval `Prob066`) is observed by this
   DUT with the same scheduling as a procedural behavioral reference — instead of the flip-flop
   sampling a stale continuous-assign wire one delta behind.

2. **4-state `if(X)` = false through a mux select.**  A mux whose select is an undriven (`x`/`z`)
   input is rendered `if (sel) … else …`; Verilog takes the `else` for an `x` select, so the register
   *holds* / *falls through* exactly as a behavioral `if(sel)` reference does — whereas a 2-state
   synthesized `$mux` propagates `x` into the register and never recovers (CVDP `apb_controller`,
   `packet_controller`, `vending_machine`).

This emitter is **not trusted**: it carries no Lean proof.  Its output is anchored to the verified
compiler by a per-design Yosys `equiv_induct` miter (`scripts/f9_miter.py`) proving it logically
equivalent to `compile m` (the machine-checked RTLIL).  The miter sees only 2-state logic, in which
`if/else` and `$mux` are identical — so it certifies the *logic* is the proven logic, while the
*rendering* recovers the procedural scheduling / 4-state behavior.  The consumer (`veval/run.py`,
`cvdp/run.py`) uses this Verilog **only** when the miter passes, else falls back to `write_verilog`.

Width-explicit SSA (each `Expr` node → its own sized net) avoids Verilog's self- and context-
determined width truncation (the classic `sum==0` over 8-bit adds silently widened to 32-bit) — the
same discipline as the F2 parametric emitter.
-/
namespace LeanRTL.ProcVerilog
open LeanRTL

/-- The result bit-width of an `Expr` (its type index). -/
def ewidth {w : Nat} (_ : Expr w) : Nat := w

/-- A `[w-1:0]` range for a bus, empty for a 1-bit scalar. -/
def rangeC (w : Nat) : String := if w == 1 then "" else s!"[{w - 1}:0] "

/-- Escape a name as a Verilog identifier.  Plain identifiers (`[A-Za-z_][A-Za-z0-9_$]*`) pass
    through; anything else (e.g. per-entry register names like `RAM[3]`) becomes a Verilog
    **escaped identifier** `\name ` — backslash prefix and the standard-mandated trailing space.
    (VCS rejects the unescaped form as a zero-size array declaration; iverilog silently
    misparses it.  Caught by the VCS second-oracle sweep, 2026-07-17.) -/
def escV (n : String) : String :=
  let plainHead := n.length > 0 && (n.front.isAlpha || n.front == '_')
  let plainBody := n.all (fun c => c.isAlphanum || c == '_' || c == '$')
  if plainHead && plainBody then n else "\\" ++ n ++ " "

/-- Is `s` a bare Verilog identifier (safe to bit-select / replicate)? -/
def isIdent (s : String) : Bool :=
  s.length > 0 && !(s.get 0).isDigit && s.all (fun c => c.isAlphanum || c == '_')

/-- SSA emitter state: fresh-net counter and accumulated bindings `(name, width, rhs)` (reversed). -/
abbrev SM := StateM (Nat × List (String × Nat × String))

/-- Bind `rhs` to a fresh net of width `w` (prefix `pfx`); return its name. -/
def fresh (pfx : String) (w : Nat) (rhs : String) : SM String := do
  let (n, binds) ← get
  let nm := s!"{pfx}{n}"
  set (n + 1, (nm, w, rhs) :: binds)
  return nm

/-- Force `s` (width `w`) to be a bare identifier — materialize a net if it is a compound
    expression — so it can be bit-selected or replicated. -/
def ensureNet (pfx : String) (w : Nat) (s : String) : SM String :=
  if isIdent s then return s else fresh pfx w s

/-- Emit an `Expr` as width-explicit SSA; returns the net/leaf holding its value.  Muxes here (a
    *datapath* mux, e.g. an arithmetic result select) render as a ternary `?:`; the register's
    top-level decision muxes are instead lowered to `if/else` by `emitDecision`. -/
partial def emitCore (pfx : String) : {w : Nat} → Expr w → SM String
  | w, e =>
    match e with
    | .const v      => return s!"{w}'d{v.toNat}"
    | .var n _      => return escV n
    | .not a        => do let x ← emitCore pfx a; fresh pfx w s!"(~ {x})"
    | .and a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} & {y})"
    | .or a b       => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} | {y})"
    | .xor a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} ^ {y})"
    | .add a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} + {y})"
    | .sub a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} - {y})"
    | .mul a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} * {y})"
    | .shl a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} << {y})"
    | .shr a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} >> {y})"
    | .sshr a b     => do let x ← emitCore pfx a; let y ← emitCore pfx b
                          fresh pfx w s!"($signed({x}) >>> {y})"
    | .udiv a b     => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} / {y})"
    | .umod a b     => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx w s!"({x} % {y})"
    | .eq a b       => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx 1 s!"({x} == {y})"
    | .ult a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b; fresh pfx 1 s!"({x} < {y})"
    | .slt a b      => do let x ← emitCore pfx a; let y ← emitCore pfx b
                          fresh pfx 1 s!"($signed({x}) < $signed({y}))"
    | .mux s a b    => do let sN ← emitCore pfx s; let x ← emitCore pfx a; let y ← emitCore pfx b
                          fresh pfx w s!"({sN} ? {x} : {y})"
    | .concat a b   => do let x ← emitCore pfx a; let y ← emitCore pfx b
                          fresh pfx w ("{" ++ x ++ ", " ++ y ++ "}")
    | .zext k a     => do let x ← ensureNet pfx (ewidth a) (← emitCore pfx a)
                          fresh pfx w ("{ {" ++ toString k ++ "{1'b0}}, " ++ x ++ " }")
    | .sext k a     => do let wa := ewidth a
                          let x ← ensureNet pfx wa (← emitCore pfx a)
                          fresh pfx w ("{ {" ++ toString k ++ "{" ++ x ++ "[" ++ toString (wa - 1)
                                       ++ "]}}, " ++ x ++ " }")
    | .extract i a  => do let x ← ensureNet pfx (ewidth a) (← emitCore pfx a)
                          fresh pfx 1 s!"{x}[{i}]"
    | .slice lo len a => do let x ← ensureNet pfx (ewidth a) (← emitCore pfx a)
                            fresh pfx w s!"{x}[{lo + len - 1}:{lo}]"

/-- Run `emitCore` once from counter `start`; return `(net, orderedBindings, nextCounter)`. -/
def runCore (pfx : String) (start : Nat) {w : Nat} (e : Expr w) :
    String × List (String × Nat × String) × Nat :=
  let (net, (n, binds)) := (emitCore pfx e).run (start, [])
  (net, binds.reverse, n)

/-- The non-blocking-assignment operator this emitter uses for register updates.

    A vendor/industrial flip-flop library writes `q <= #1 d`: a one-time-unit intra-assignment
    delay that models clk-to-Q and, crucially, decides who wins when a *testbench* drives its
    stimulus with blocking assignments **at the same clock edge** the DUT samples.  With `#1` the
    flop captures the pre-edge input (real hardware); without it the simulator may hand the flop
    the post-edge value, putting the design one cycle out of phase for the rest of the run.

    Plain `q <= d` is the synthesizable-textbook form and stays the DEFAULT, because adding a delay
    changes nothing for a well-written testbench and every existing benchmark lane was measured
    with it.  `LEANRTL_NBA_DELAY=1` opts into the library form; see `docs/plan/friction.v1.5.md`
    (RealBench e203: every reference module is built from `sirv_gnrl_dffs.v`'s `qout_r <= #1 dnxt`
    while its stimulus generator assigns on the posedge — deleting that `#1` from the *reference
    itself* makes it fail its own harness 202/222, so the lane grades flop-delay style). -/
def nbaOp (delay : Bool) : String := if delay then " <= #1 " else " <= "

/-- Lower a register's next-state `Expr` to procedural statements assigning `lhs <= …`, with the
    mux decision-tree rendered as `if/else` **statements** (so an `x` select falls to `else`), and
    all datapath sub-expressions collected as blocking temporaries (`_t…`).  Returns
    `(stmtLines, tempBindings, nextCounter)`. -/
partial def emitDecision (delay : Bool) (lhs indent : String) : {w : Nat} → Expr w → Nat →
    (List String × List (String × Nat × String) × Nat)
  | _, .mux s a b, ctr =>
      let (sNet, sB, c1) := runCore "_t" ctr s
      let (aL, aB, c2) := emitDecision delay lhs (indent ++ "  ") a c1
      let (bL, bB, c3) := emitDecision delay lhs (indent ++ "  ") b c2
      let lines := [indent ++ "if (" ++ sNet ++ ") begin"] ++ aL
                 ++ [indent ++ "end else begin"] ++ bL ++ [indent ++ "end"]
      (lines, sB ++ aB ++ bB, c3)
  | _, e, ctr =>
      let (net, b, c1) := runCore "_t" ctr e
      ([indent ++ lhs ++ nbaOp delay ++ net ++ ";"], b, c1)

/-- `some p` when `e` is exactly `~p` for some signal name `p`.  Matching `.var p _` rather than
    `.var p 1` keeps the width opaque, so this elaborates against an `Expr w` for any `w`. -/
def invOf? {w : Nat} (e : Expr w) : Option String :=
  match e with
  | .not e' => match e' with
               | .var p _ => some p
               | _        => none
  | _ => none

/-- The single async-reset net shared by the registers, paired with its active level, if any.

    A reset that reaches the `$adff` through an **inverter net** — the `nrst = ~rst_n` +
    `asyncReset := some ("nrst", true, 0)` idiom this repository's own instructions used to mandate
    — is collapsed here to name the input port and the opposite polarity instead.  The two describe
    the same function of the same signal at every clock edge, so no cycle-level fact changes; they
    differ only in Verilog's event schedule, where the inverter net settles one delta *after* the
    port moves.  A testbench that deasserts reset in the same timestep as a clock edge (`rst_n = 0;
    repeat(10) @(posedge clk); rst_n = 1;` — the common idiom) loses that race and the whole output
    trace shifts by a cycle, so the indirection is never what a design wants.  Restricted to INPUT
    PORTS: a port has no delta of its own, whereas an intermediate wire would only move the problem
    one level up. -/
def asyncNet? (m : Module) : Option (String × Bool) :=
  (m.regs.findSome? (fun r => r.asyncReset.map (fun ar => (ar.1, ar.2.1)))).map fun (net, hi) =>
    match m.wires.find? (·.name == net) with
    | some w =>
        match invOf? w.expr with
        | some p => if m.inputs.any (·.name == p) then (p, !hi) else (net, hi)
        | none   => (net, hi)
    | none => (net, hi)

/-- Format ordered SSA bindings as continuous-assign wire declarations. -/
def wireLines (binds : List (String × Nat × String)) : List String :=
  binds.map (fun (nm, w, rhs) => s!"  wire {rangeC w}{nm} = {rhs};")

/-- Emit procedural SystemVerilog for a monomorphic `Module`.  Returns `none` if the module mixes
    async-reset and non-async-reset registers (unsupported shape — the caller falls back).

    `delay` selects the register-update operator: `false` (default) emits the synthesizable-textbook
    `q <= d`; `true` emits the vendor-library `q <= #1 d`.  See `nbaOp`.

    `forceClocked` renders a `stepDelay` module as though it were clocked.  It exists for exactly one
    caller: the equivalence miter, which runs on a netlist Yosys can read and therefore cannot see a
    delay-driven `always`.  Emitting both forms from this one function is the point — the two differ
    only in the sensitivity line, so certifying the clocked form and diffing the pair certifies
    everything the shipped file says except which event advances a step. -/
def emitProcVerilog (m : Module) (delay : Bool := false) (forceClocked : Bool := false) :
    Option String := Id.run do
  -- Expr uses unsigned, LSB-relative internal references. Until this emitter
  -- inserts canonical internal aliases for signed/ranged ports, use RTLIL.
  if !m.portLayouts.isEmpty then return none
  -- F8: this emitter renders only registers/wires/outputs; it has no procedural form for a
  -- level-sensitive `$dlatch`.  A module with latches returns none so the caller falls back to
  -- `write_verilog`, which emits each `$dlatch` as the `always @(*) if (en) q = d;` latch idiom.
  if !m.latches.isEmpty then return none
  -- F9: this emitter has no procedural form for an addressed memory (`$mem_v2`) — it would emit
  -- Verilog that *references* the mem read-port output nets without ever declaring or driving them.
  -- A module with memories returns none so the caller falls back to `write_verilog`, which renders
  -- the `$mem_v2` as the `reg [DW-1:0] mem [0:2^AW-1]; always @(posedge wclk) …` memory idiom.
  if !m.mems.isEmpty then return none
  -- F6: this emitter has no procedural form for an asynchronous *load* of a dynamic value
  -- (`$aldff`).  A module with any `asyncLoad` register returns none so the caller falls back to
  -- `write_verilog`, which renders the `$aldff` as `always @(posedge clk or negedge net)
  -- if (!net) q <= val; else q <= next;` (the trusted RTLIL path).
  if m.regs.any (·.asyncLoad.isSome) then return none
  -- F11: this emitter renders every register in ONE clocked `always` block off the *single* module
  -- clock (`clk`), so it cannot express a per-register clock net (a second clock domain, a gated
  -- clock, or a data signal used as a clock).  A module with any `clockNet` register returns none so
  -- the caller falls back to `write_verilog`, which clocks each flip-flop off its own derived net.
  if m.regs.any (·.clockNet.isSome) then return none
  let arst? := asyncNet? m
  let numAsync := (m.regs.filter (fun r => r.asyncReset.isSome)).length
  -- Reject mixed reset styles: either all regs async-reset (shared net) or none.
  if arst?.isSome && numAsync ≠ m.regs.length then return none
  -- F1: registers are grouped by clock edge and each group gets its own `always` block.  A module
  -- whose registers share one edge emits exactly ONE block — byte-for-byte what this emitter has
  -- always produced — and a negedge-*only* module renders with a `negedge` sensitivity.  A DUAL-edge
  -- module (posedge and negedge registers mixed) emits two blocks, posedge first.  It used to return
  -- none here and fall back to `write_verilog`, and that cost the design the race against a
  -- testbench that releases reset in the same timestep as a clock edge: Yosys lifts the reset test
  -- onto continuous-assign wires (`_09_ = ~rst; _08_ = _09_ | …`) whose two deltas land AFTER the
  -- edge, so the flop samples the pre-release value and the whole trace runs one cycle late.  This
  -- emitter computes the same test with a blocking assignment INSIDE the block, which is post-edge —
  -- the property F9 exists for.  (Measured on ChipBench Prob016, an odd-divisor clock divider whose
  -- 50% duty cycle no single-edge design can reach: 172/621 mismatches on the fallback, 0/621 here.)
  let allNeg := !m.regs.isEmpty && m.regs.all (·.negedge)
  let anyNeg := m.regs.any (·.negedge)
  let regGroups : List (String × List Reg) :=
    if !anyNeg then [("posedge", m.regs)]
    else if allNeg then [("negedge", m.regs)]
    else [("posedge", m.regs.filter (fun r => !r.negedge)), ("negedge", m.regs.filter (·.negedge))]
  let clk := m.clock.getD "clk"
  -- F13: `stepDelay` drives the ambient step from a `#n` delay instead of a clock edge (see
  -- `Module.stepDelay`).  It answers to the same `Module.step`, so the block's BODY is byte-for-byte
  -- what the clocked rendering produces — only the sensitivity line differs, which is what lets the
  -- harness certify the clocked form and ship this one.  Two shapes are refused rather than guessed:
  -- a module that names both a clock and a delay has two candidate drivers and no rule picks one,
  -- and an async reset is an edge-sensitivity construct with no meaning in a delay-driven block.
  if m.stepDelay.isSome && m.clock.isSome then return none
  if m.stepDelay.isSome && arst?.isSome then return none
  let sensOf := fun (edge : String) => match m.stepDelay with
    | some n => if forceClocked then s!"@({edge} {clk})" else s!"#{n}"
    | none   => s!"@({edge} {clk})"
  let regNames := m.regs.map (·.name)
  let isReg := fun (nm : String) => regNames.contains nm
  -- Port direction declarations (non-ANSI: names in the header, directions below).
  -- `portOrder`, when set, fixes the header's parenthesis list.  The header is the only place it is
  -- consulted; directions/widths are declared below by name, so this changes nothing a name-based
  -- consumer sees.  It matters only for a testbench that binds by position.  A non-empty order that
  -- is not a permutation of the declared ports returns none (the caller falls back) rather than
  -- emitting a header that drops or duplicates a port.
  let declPorts := (m.inputs.map (·.name)) ++ (m.outputs.map (·.name))
  if !m.portOrder.isEmpty then
    if m.portOrder.length ≠ declPorts.length then return none
    if !declPorts.all (fun p => m.portOrder.contains p) then return none
  let portNames := if m.portOrder.isEmpty then declPorts else m.portOrder
  -- Verilog `parameter` declarations (see `Module.params`).  A PORT whose width equals a declared
  -- parameter's value is rendered `[N-1:0]` — that is the width the spec writes and the width a
  -- testbench's `#(.N(32))` override names.  Internal regs/wires stay concrete: they are not part
  -- of the interface, and rendering them symbolically would suggest a genericity the body of this
  -- monomorphic netlist does not have.
  let paramDecls := m.params.map (fun (n, v) => s!"  parameter {n} = {v};")
  let rangeP := fun (w : Nat) =>
    match m.params.find? (fun (_, v) => v == w) with
    | some (n, _) => if w == 1 then "" else s!"[{n}-1:0] "
    | none        => rangeC w
  let inDirs  := m.inputs.map  (fun p => s!"  input  {rangeP p.width}{p.name};")
  let outDirs := m.outputs.map (fun o => s!"  output {rangeP o.width}{o.name};")
  -- Register storage (a reg-backed output shares its physical `reg`); carry the power-on init (F7).
  let regDecls := m.regs.map (fun r =>
    let initial := if r.emitInit then s!" = {r.width}'d{r.init.toNat}" else ""
    s!"  reg {rangeC r.width}{escV r.name}{initial};")
  -- Internal wires (m.wires) as continuous assigns, plus their SSA temps (`_w` namespace).
  let mut wctr : Nat := 0
  let mut wireDecls : List String := []
  for w in m.wires do
    let (net, binds, c) := runCore "_w" wctr w.expr
    wctr := c
    wireDecls := wireDecls ++ wireLines binds ++ [s!"  wire {rangeC w.width}{escV w.name} = {net};"]
  -- Combinational (non-register-backed) outputs as continuous assigns.
  let mut combOuts : List String := []
  for o in m.outputs do
    if !(isReg o.name) then
      let (net, binds, c) := runCore "_w" wctr o.expr
      wctr := c
      -- A design wire may share the output's name (the wire decl already drives the port
      -- net); emitting `assign x = x;` would double-drive it and X-poison 4-state sim.
      if net == escV o.name then
        combOuts := combOuts ++ wireLines binds
      else
        combOuts := combOuts ++ wireLines binds ++ [s!"  assign {escV o.name} = {net};"]
  -- Sequential process: per-register decision trees + shared blocking datapath temps.
  -- One pass per edge group (see F1 above); `tctr` runs across groups so temp names stay unique.
  let mut tctr : Nat := 0
  let mut tempBinds : List (String × Nat × String) := []
  let mut groupBodies : List (String × List Reg × List (String × Nat × String) × List String) := []
  for (edge, regs) in regGroups do
    let mut gBinds : List (String × Nat × String) := []
    let mut gStmts : List String := []
    for r in regs do
      let (lines, binds, c) := emitDecision delay (escV r.name) "      " r.next tctr
      tctr := c
      gBinds := gBinds ++ binds
      gStmts := gStmts ++ lines
    tempBinds := tempBinds ++ gBinds
    groupBodies := groupBodies ++ [(edge, regs, gBinds, gStmts)]
  -- Where the datapath temporaries live decides WHICH stimulus edge the flop samples.
  -- Inside the clocked block (blocking `_t = …`, the default) the block reads the module's inputs
  -- at block-execution time, i.e. the POST-edge values — that is F9's whole point (VerilogEval
  -- Prob066's blocking-assignment testbench, CVDP's 4-state `if(x)`).  A vendor flip-flop library
  -- instead computes its `dnxt` on a continuous-assign wire OUTSIDE the block, so the flop samples
  -- the PRE-edge values.  `delay` selects the library form: temporaries become wires AND the NBA
  -- carries `#1`.  Measured on RealBench `e203_ifu_litebpu`: neither half alone changes anything
  -- (201/3022 either way); together they give 0/3022.
  let tempDecls := if delay then tempBinds.map (fun (nm, w, rhs) => s!"  wire {rangeC w}{nm} = {rhs};")
                   else tempBinds.map (fun (nm, w, _) => s!"  reg {rangeC w}{nm};")
  -- Reset-branch assignments, restricted to the group's own registers.
  let resetAsgnOf := fun (regs : List Reg) => regs.map (fun r =>
    let v := match r.asyncReset with | some (_, _, rv) => rv.toNat | none => r.init.toNat
    s!"      {escV r.name}{nbaOp delay}{r.width}'d{v};")
  let mut proc : List String := []
  if !m.regs.isEmpty then
    for (edge, gRegs, gBinds, gStmts) in groupBodies do
      let tempAsgn := if delay then ([] : List String)
                      else gBinds.map (fun (nm, _, rhs) => s!"      {nm} = {rhs};")
      let normalBody := tempAsgn ++ gStmts
      let resetAsgn := resetAsgnOf gRegs
      let block : List String :=
        match arst?, m.reset with
        | some (a, activeHi), _ =>
            -- The reset's declared polarity picks BOTH the sensitivity edge and the branch test.
            -- Emitting `posedge`/`if (a)` unconditionally is what forced an active-low `rst_n`
            -- through an inverter net and cost the design a delta against the testbench.
            let redge := if activeHi then "posedge" else "negedge"
            let test := if activeHi then a else s!"!{a}"
            [s!"  always @({edge} {clk} or {redge} {a}) begin",
             s!"    if ({test}) begin"] ++ resetAsgn ++ ["    end else begin"] ++ normalBody ++ ["    end", "  end"]
        | none, some rst =>
            [s!"  always {sensOf edge} begin",
             s!"    if ({rst}) begin"] ++ resetAsgn ++ ["    end else begin"] ++ normalBody ++ ["    end", "  end"]
        | none, none =>
            [s!"  always {sensOf edge} begin"] ++ normalBody ++ ["  end"]
      proc := proc ++ block
  let header := s!"module {m.name}(" ++ String.intercalate ", " portNames ++ ");"
  let lines :=
    [header] ++ paramDecls ++ inDirs ++ outDirs ++ regDecls ++ wireDecls ++ combOuts
      ++ tempDecls ++ proc ++ ["endmodule", ""]
  return some (String.intercalate "\n" lines)

end LeanRTL.ProcVerilog
