import LeanRTL.Core.Syntax
/-!
# Denotational semantics

`eval` interprets an `Expr` as a function over `BitVec`, given an environment that maps
signal names to values.  To keep proofs free of dependent width-casts, an environment is
just `String → Nat` (a stored natural per name); `Env.lookup` reconstructs a `BitVec` of
the width demanded by the AST.  Because every `var n w` we ever build is fed an env whose
stored value is `< 2^w`, the round-trip `BitVec.ofNat w v.toNat = v` makes specs reduce to
pure `BitVec` identities that `bv_decide` discharges.
-/

namespace LeanRTL

abbrev Env := String → Nat

def Env.lookup (e : Env) (name : String) (w : Nat) : BitVec w := BitVec.ofNat w (e name)

/-- Build an environment from a name ↦ value association list. -/
def Env.ofList (vals : List (String × Nat)) : Env := fun n => (vals.lookup n).getD 0

def eval : {w : Nat} → Expr w → Env → BitVec w
  | _, .const v,    _ => v
  | _, .var n w,    e => e.lookup n w
  | _, .not a,      e => ~~~ eval a e
  | _, .and a b,    e => eval a e &&& eval b e
  | _, .or a b,     e => eval a e ||| eval b e
  | _, .xor a b,    e => eval a e ^^^ eval b e
  | _, .add a b,    e => eval a e + eval b e
  | _, .sub a b,    e => eval a e - eval b e
  | _, .mul a b,    e => eval a e * eval b e
  | _, .shl a b,    e => BitVec.shiftLeft (eval a e) (eval b e).toNat
  | _, .shr a b,    e => BitVec.ushiftRight (eval a e) (eval b e).toNat
  | _, .sshr a b,   e => BitVec.sshiftRight (eval a e) (eval b e).toNat
  | _, .udiv a b,   e => eval a e / eval b e
  | _, .umod a b,   e => eval a e % eval b e
  | _, .eq a b,     e => if eval a e = eval b e then 1 else 0
  | _, .ult a b,    e => if (eval a e) < (eval b e) then 1 else 0
  | _, .slt a b,    e => if (eval a e).toInt < (eval b e).toInt then 1 else 0
  | _, .mux s a b,  e => if eval s e = 1 then eval a e else eval b e
  | _, .concat a b, e => eval a e ++ eval b e
  | _, .zext k a,   e => (eval a e).setWidth _
  | _, .sext k a,   e => (eval a e).signExtend _
  | _, .extract i a, e => if (eval a e).getLsbD i then 1 else 0
  | _, .slice lo len a, e => ((eval a e) >>> lo).setWidth len

/-! ## Latch semantics (F8)

A transparent latch is a level-sensitive state element: `q' = if enable then d else q`.  `Latch.den`
gives its next value against a cycle environment `e` — when `enable` is high the latch is transparent
(the value is `eval l.d e`), when low it holds its current value (looked up by name).  This is the
per-latch characterization the compiled `$dlatch` realizes; it is *proved per instance* in the VEval
latch files.  It deliberately lives outside `Module.simulate`: the cycle simulator is a Moore
one-value-per-cycle model and does not represent a latch's intra-cycle transparency (see the honesty
note on `Latch`). -/

/-- Next value of a transparent latch under cycle environment `e`: `enable ? d : (held q)`. -/
def Latch.den (l : Latch) (e : Env) : BitVec l.width :=
  if eval l.enable e = 1 then eval l.d e else e.lookup l.name l.width

/-! ## Async-load register semantics (F6)

An `$aldff` register with `asyncLoad = some (net, activeHi, val)` is *asynchronously* forced to
`eval val` while `net` is at its active level, and otherwise clocks in `next`.  `Reg.aldffDen` gives
its resulting value against a cycle environment `e`: when the async load net is active the value is
`eval val e` (the dynamic loaded value), otherwise it is `eval r.next e` (the normal next-state).
For a register with `asyncLoad = none` this is exactly `eval r.next e`, so it is a conservative
extension of the ordinary next-state.

Like `Latch.den` (and for the same sub-cycle reason as `negedge`/`asyncReset`), this characterization
lives *outside* `Module.simulate`: the one-active-edge-per-cycle model does not represent an async
load firing between clock edges.  It is the per-register fact the compiled `$aldff` realizes, proved
per instance in the design file and validated by co-simulation. -/

/-- Value of an async-load (`$aldff`) register under cycle environment `e`: `active ? val : next`,
    where `active` is the async-load net at its declared polarity (`activeHi ? net=1 : net=0`). -/
def Reg.aldffDen (r : Reg) (e : Env) : BitVec r.width :=
  match r.asyncLoad with
  | some (net, activeHi, val) =>
      if (if activeHi then e.lookup net 1 = 1 else e.lookup net 1 = 0)
      then eval val e else eval r.next e
  | none => eval r.next e

/-! ## Async-reset register semantics (F4)

An `$adff` register with `asyncReset = some (net, activeHi, val)` is *asynchronously* held at the
constant `val` while `net` is at its active level, and otherwise clocks in `next`.  `Reg.arstDen`
gives its resulting value against a cycle environment `e`.  For a register with `asyncReset = none`
this is exactly `eval r.next e`, so — like `Reg.aldffDen` — it is a conservative extension of the
ordinary next-state.

Like `Latch.den` and `Reg.aldffDen`, this characterization lives *outside* `Module.simulate`: the
one-active-edge-per-cycle model does not represent a reset firing between clock edges, and
`Module.semanticCoverage` keeps reporting `.asyncReset` for such a design.  What it gives the author
is the Stage-2 route `asyncLoad` already had: compose this per-register law over a trace on which the
reset is inactive and the rest of the design is back inside a whole-trace theorem, without ever
claiming the sub-cycle reset itself was proved.  See `assets/skills/patterns/asyncreset-value-trace.md`.

Note it is stated on the DECLARED net and polarity.  `ProcVerilog.asyncNet?` may render a reset that
was declared through an inverter net (`nrst = ~rst_n`) as `negedge rst_n` instead; that rewrite is
polarity-preserving by construction (`nrst = 1 ⟺ rst_n = 0`), so it changes no value this definition
assigns. -/

/-- Value of an async-reset (`$adff`) register under cycle environment `e`: `active ? rstVal : next`,
    where `active` is the reset net at its declared polarity (`activeHi ? net=1 : net=0`).  `rstVal`
    is a compile-time constant (`ARST_VALUE`), so unlike `aldffDen` it is not `eval`'d. -/
def Reg.arstDen (r : Reg) (e : Env) : BitVec r.width :=
  match r.asyncReset with
  | some (net, activeHi, val) =>
      if (if activeHi then e.lookup net 1 = 1 else e.lookup net 1 = 0)
      then val else eval r.next e
  | none => eval r.next e

/-! ### The asynchronous reset folded in-band (F4, the case that is *not* scoped)

`arstDen` is stated as a per-register law precisely because the `$adff` responds to `net` *between*
clock edges, which the one-active-edge-per-cycle model cannot express.  That is the entire content
of the "scoped to the reset-inactive segment" caveat: on a reset-active edge the `$adff` presents
`val` while `Module.step` clocks in `eval r.next e`, and in general those two differ.

They do **not** differ when the author has *also* folded the reset in-band — written `next` as
`mux (net == activeLevel) val …`, which is exactly what the synchronous spelling of the same reset
looks like.  Then the cycle model already computes `val` on precisely the edges the `$adff` holds
it, and `arstDen` collapses into the ordinary next-state (`Reg.arstFolded_arstDen` below).

So declaring `asyncReset` **on top of** an in-band fold costs nothing at any clock edge: the
whole-design `simulate` theorem (unconditional already, by `Module.eraseArst_simulate`) covers
reset-active cycles too, and the only thing left out of model is the sub-cycle response.  The two
spellings are complements, not alternatives, and the pair is what the emitter needs — the fold
gives the theorem its reset-active edges, the declaration gives the Verilog the `negedge rst_n` in
its sensitivity list that a testbench deasserting reset *on* a clock edge requires.

`arstFoldedb` is decidable by inspection of the syntax tree, so `leanrtl check` can tell the two
cases apart and stop quoting the scoping caveat at designs that do not incur it. -/

/-- The head of an in-band reset fold: `some (net, lvl, val)` when the expression is syntactically
    `mux (net == lvl) val _` over a 1-bit net.  `none` for every other shape. -/
def Expr.inBandResetHead : {w : Nat} → Expr w → Option (String × BitVec 1 × BitVec w)
  | _, .mux (.eq (.var n 1) (.const lvl)) (.const v) _ => some (n, lvl, v)
  | _, _ => none

/-- Reading the fold back out: on any environment that puts the net at the folded level, the
    expression evaluates to the folded value, whatever the fold's `else` branch is. -/
theorem Expr.inBandResetHead_eval {w : Nat} (x : Expr w) (n : String) (lvl : BitVec 1)
    (v : BitVec w) (h : x.inBandResetHead = some (n, lvl, v)) (e : Env)
    (hact : e.lookup n 1 = lvl) : eval x e = v := by
  unfold Expr.inBandResetHead at h
  split at h
  · next n' lvl' v' _ =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl, rfl⟩ := h
      simp [eval, hact]
  · exact absurd h (by simp)

/-- The register's asynchronous reset is *folded in-band*: `next` already selects the declared reset
    value under the declared net's active-level test.  Vacuously true of a register that declares no
    asynchronous reset. -/
def Reg.arstFoldedb (r : Reg) : Bool :=
  match r.asyncReset with
  | none => true
  | some (net, activeHi, val) =>
      match r.next.inBandResetHead with
      | some (n, lvl, v) => n == net && lvl == (if activeHi then 1 else 0) && v == val
      | none => false

/-- **The `$adff` costs nothing at a clock edge when the reset is folded in-band.**  Its denotation
    is then the plain next-state, on *every* environment — reset-active ones included.  Composed
    with `Module.eraseArst_simulate` this says the whole-design cycle theorem of such a design is
    unscoped: it is only the reset's response *between* edges that stays out of model. -/
theorem Reg.arstFolded_arstDen (r : Reg) (h : r.arstFoldedb = true) (e : Env) :
    r.arstDen e = eval r.next e := by
  unfold Reg.arstFoldedb at h
  unfold Reg.arstDen
  cases harst : r.asyncReset with
  | none => rfl
  | some a =>
      obtain ⟨net, activeHi, val⟩ := a
      rw [harst] at h
      cases hhead : r.next.inBandResetHead with
      | none => rw [hhead] at h; exact absurd h (by simp)
      | some t =>
          obtain ⟨n, lvl, v⟩ := t
          rw [hhead] at h
          simp only [Bool.and_eq_true, beq_iff_eq] at h
          obtain ⟨⟨rfl, hlvl⟩, rfl⟩ := h
          dsimp only
          by_cases hc : (if activeHi then e.lookup n 1 = 1 else e.lookup n 1 = 0)
          · rw [if_pos hc]
            refine (Expr.inBandResetHead_eval r.next n lvl v hhead e ?_).symm
            subst hlvl; cases activeHi <;> simpa using hc
          · rw [if_neg hc]

/-- Every register's asynchronous reset is folded in-band. -/
def Module.arstFoldedb (m : Module) : Bool := m.regs.all (·.arstFoldedb)

/-- The module-level reading of `Reg.arstFolded_arstDen`. -/
theorem Module.arstFolded_arstDen (m : Module) (h : m.arstFoldedb = true)
    (r : Reg) (hr : r ∈ m.regs) (e : Env) : r.arstDen e = eval r.next e :=
  Reg.arstFolded_arstDen r (List.all_eq_true.mp h r hr) e

/-! ## Module-level semantics

For sequential modules, the register file is an `Env` over the register names.  One clock
step updates every register from its `next` expression evaluated against the *current*
registers and the cycle's inputs (with synchronous reset to `init`). -/

/-- The combined environment seen by combinational expressions in one cycle: register
    values overlaid by the current input values. -/
def cycleEnv (regVals inputs : Env) (regNames : List String) : Env :=
  fun n => if regNames.contains n then regVals n else inputs n

/-- Extend an environment with a module's internal wires, evaluated in declaration order.
    The `wires` list must be topologically ordered: each wire's `expr` sees inputs,
    registers, and the wires before it.  With no wires this is the identity. -/
def evalWires (wires : List Wire) (e : Env) : Env :=
  wires.foldl (fun env w => fun n => if n = w.name then (eval w.expr env).toNat else env n) e

/-- Evaluate all outputs of a module in one cycle. -/
def Module.outputs?eval (m : Module) (regVals inputs : Env) : List (String × Nat) :=
  let e := evalWires m.wires (cycleEnv regVals inputs (m.regs.map (·.name)))
  m.outputs.map (fun o => (o.name, (eval o.expr e).toNat))

/-- One synchronous step: produce the next register environment. -/
def Module.step (m : Module) (regVals inputs : Env) (resetActive : Bool) : Env :=
  let e := evalWires m.wires (cycleEnv regVals inputs (m.regs.map (·.name)))
  fun n =>
    match m.regs.find? (·.name = n) with
    | some r => if resetActive then r.init.toNat else (eval r.next e).toNat
    | none   => regVals n

/-- Initial register environment (all registers at their `init`). -/
def Module.initRegs (m : Module) : Env :=
  fun n => match m.regs.find? (·.name = n) with
           | some r => r.init.toNat
           | none   => 0

/-- Run a module over a list of input cycles (each cycle a name→value map).  Returns the
    per-cycle output maps.  Combinational modules ignore registers; sequential modules tick
    one clock per cycle and treat a nonzero value on the `reset` input as a synchronous
    reset.  Output of cycle `i` is sampled from the register state *before* that cycle's
    clock edge (Moore/Mealy convention).

    Register values are materialised to concrete `Nat`s each cycle (not kept as lazy
    closures) so each signal lookup is O(1) — essential when `next` references a register
    more than once, which would otherwise re-evaluate the whole past trace exponentially. -/
def Module.simulate (m : Module) (cycles : List (List (String × Nat))) :
    List (List (String × Nat)) :=
  let regNames := m.regs.map (·.name)
  let init : List (String × Nat) := m.regs.map (fun r => (r.name, r.init.toNat))
  (cycles.foldl
    (fun (st : List (String × Nat) × List (List (String × Nat))) inpL =>
      let inp := Env.ofList inpL
      let e := evalWires m.wires (cycleEnv (Env.ofList st.1) inp regNames)
      let outs := m.outputs.map (fun o => (o.name, (eval o.expr e).toNat))
      let rst := match m.reset with | some r => (inp r != 0) | none => false
      let regs' := m.regs.map (fun r =>
        (r.name, if rst then r.init.toNat else (eval r.next e).toNat))
      (regs', st.2 ++ [outs]))
    (init, [])).2

/-! ## Erasing the asynchronous reset (F4): the design the cycle model actually describes

`Module.step` / `Module.simulate` never read `Reg.asyncReset` — look at the two definitions
above: the register update is `if resetActive then r.init else eval r.next e`, with
`resetActive` coming from the *module-level synchronous* `Module.reset`.  So the cycle
semantics of a design carrying async resets is, verbatim and by construction, the cycle
semantics of the same design with those resets erased.

`Module.eraseArst` names that erasure and the four theorems below prove the identification.
Their point is an *incentive*, not new expressive power.  Before them, an author whose spec
left the reset style open had a reason to read it as synchronous even when the reference RTL
was `always @(posedge clk or negedge rst_n)`: declaring `asyncReset` dropped the design out of
`Module.fullyCoveredb`, and the whole-design `simulate` theorem was believed to go with it.
It does not.  `eraseArst_simulate` says the whole-design theorem an author would have written
for the synchronous twin is *literally the same theorem* about `m` — so the async reading costs
nothing at the `simulate` level and the emitted Verilog gets the reset the reference has.

What the erasure does *not* do — and what keeps `semanticCoverage` reporting `.asyncReset`
unchanged — is model the reset firing between clock edges.  Every theorem here is scoped to
the reset-inactive segment: on a trace where no declared reset net is ever at its active level,
the emitted `$adff` steps exactly as the `$dff` of `m.eraseArst`, and these equalities transport
the whole-design result onto the shipped design.  A trace containing an assertion of the reset
between edges is outside all of it; `Reg.arstDen` above is the per-register law that covers the
reset value itself.  See `Module.coveredModuloArstb` in `Core/Coverage.lean` for the decidable
verdict and `assets/skills/patterns/asyncreset-value-trace.md` for the authoring shape. -/

/-- The design the cycle semantics actually describes: every register's asynchronous reset
    erased, everything else untouched. -/
def Module.eraseArst (m : Module) : Module :=
  { m with regs := m.regs.map (fun r => { r with asyncReset := none }) }

/-- Erasure preserves every register's name, so it preserves the register *name set* that
    `cycleEnv` uses to decide register-vs-input. -/
theorem Module.eraseArst_regNames (m : Module) :
    m.eraseArst.regs.map (·.name) = m.regs.map (·.name) := by
  simp [Module.eraseArst, List.map_map, Function.comp]

/-- Erasure commutes with the `find?` that `Module.step` / `Module.initRegs` use to look a
    register up by name. -/
theorem Module.find?_eraseArst (regs : List Reg) (n : String) :
    (regs.map (fun r => { r with asyncReset := none })).find? (fun r => r.name = n)
      = (regs.find? (fun r => r.name = n)).map (fun r => { r with asyncReset := none }) := by
  induction regs with
  | nil => rfl
  | cons r rs ih =>
      by_cases h : r.name = n
      · simp [List.find?, h]
      · simp [List.find?, h, ih]

/-- **One step is blind to the async reset.**  `Module.step` reads only `name` / `init` / `next`,
    all preserved by the erasure. -/
theorem Module.eraseArst_step (m : Module) (regVals inputs : Env) (resetActive : Bool) :
    m.eraseArst.step regVals inputs resetActive = m.step regVals inputs resetActive := by
  funext n
  simp only [Module.step, Module.eraseArst, Module.find?_eraseArst, List.map_map,
    Function.comp_def]
  cases regs_eq : m.regs.find? (fun r => r.name = n) with
  | none => rfl
  | some r => rfl

/-- Initial register state is blind to the async reset (it reads `init` only). -/
theorem Module.eraseArst_initRegs (m : Module) : m.eraseArst.initRegs = m.initRegs := by
  funext n
  simp only [Module.initRegs, Module.eraseArst, Module.find?_eraseArst]
  cases m.regs.find? (fun r => r.name = n) with
  | none => rfl
  | some r => rfl

/-- Outputs in one cycle are blind to the async reset. -/
theorem Module.eraseArst_outputs?eval (m : Module) (regVals inputs : Env) :
    m.eraseArst.outputs?eval regVals inputs = m.outputs?eval regVals inputs := by
  simp only [Module.outputs?eval, Module.eraseArst, List.map_map, Function.comp_def]

/-- **The whole-design trace is blind to the async reset.**  This is the theorem that makes the
    async reading free: whatever an author proves about `m.eraseArst.simulate` — the synchronous
    twin, which *is* `fullyCoveredb` whenever the rest of the design is in model — holds verbatim
    of `m.simulate`, on the segment where the reset stays inactive. -/
theorem Module.eraseArst_simulate (m : Module) (cycles : List (List (String × Nat))) :
    m.eraseArst.simulate cycles = m.simulate cycles := by
  simp only [Module.simulate, Module.eraseArst, List.map_map, Function.comp_def]

/-! ## Hierarchy semantics (combinational children) -/

/-- Combinational output map of a (leaf, combinational) module. -/
def Module.combOut (m : Module) (inputs : List (String × Nat)) : List (String × Nat) :=
  let e := evalWires m.wires (Env.ofList inputs)
  m.outputs.map (fun o => (o.name, (eval o.expr e).toNat))

/-- Combinational output map of a hierarchical parent.  Instances are evaluated in order so
    that a later instance may consume an earlier instance's outputs (e.g. a carry chain). -/
def Parent.combOut (p : Parent) (inputs : List (String × Nat)) : List (String × Nat) :=
  let envF := p.insts.foldl (fun acc inst =>
      let e := Env.ofList acc
      let childIns := inst.ins.map (fun (port, ae) => (port, (eval ae.2 e).toNat))
      let outs := (inst.child.combOut childIns).map
                    (fun (pn, v) => (inst.instName ++ "." ++ pn, v))
      acc ++ outs)
    inputs
  let e := Env.ofList envF
  p.outputs.map (fun o => (o.name, (eval o.expr e).toNat))

/-- Run a combinational parent over independent input cycles. -/
def Parent.simulate (p : Parent) (cycles : List (List (String × Nat))) :
    List (List (String × Nat)) :=
  cycles.map p.combOut

/-! ## Sequential hierarchy semantics (F10)

`Parent.combOut`/`Parent.simulate` model a parent whose instances are *combinational* leaves: every
cycle is independent.  A parent may instead instantiate *sequential* (clocked) `Module` children,
whose registers persist across cycles.  `Parent.simulateSeq` is the **stateful** hierarchical
simulator: it carries every child instance's register file across cycles, keyed by the flattened
name `"<inst>.<reg>"`.  Each cycle, in instance-declaration order, a child's outputs are computed
from its *current* registers and its instance-mapped inputs (Moore), threaded to later instances and
the parent outputs; then every child advances its registers by one `Module.step`, its own `reset`
input — mapped through `ins` — driving the synchronous reset.  A combinational child (`regs = []`)
contributes no state and its `Module.outputs?eval` reduces to `Module.combOut`, so `simulateSeq`
conservatively extends the combinational model.

The compiler needs **no** change for this shape: `compileParent` already lowers each child via the
M6-proven `compileModule` (registers, clock, reset all handled) and `compileInst` wires each child
port — including a clock/reset threaded through `ins` — to the parent net, so `write_verilog` emits a
real sequential module instantiation.  The proof-carrying story is in `HierSeqCorrect.lean`. -/

/-- The input environment a child instance sees this cycle: each declared input port bound to the
    value of its parent-side instance expression, evaluated in the parent env. -/
def Inst.childIn (inst : Inst) (parentEnv : Env) : Env :=
  Env.ofList (inst.ins.map (fun pe => (pe.1, (eval pe.2.2 parentEnv).toNat)))

/-- A child instance's current register environment, projected out of the flat hierarchical state
    (whose keys are `"<inst>.<reg>"`). -/
def Inst.regVals (inst : Inst) (flat : Env) : Env :=
  fun rn => flat (inst.instName ++ "." ++ rn)

/-- Whether a child instance's synchronous reset fires this cycle: its `reset` input, mapped through
    `ins`, is nonzero. -/
def Inst.resetActive (inst : Inst) (parentEnv : Env) : Bool :=
  match inst.child.reset with
  | some r => (inst.childIn parentEnv) r != 0
  | none   => false

/-- Fold the instances (in order) to build one cycle's parent environment: start from the cycle
    inputs and append each instance's outputs (renamed `"<inst>.<port>"`), computed from the child's
    *current* registers and its mapped inputs.  Later instances see earlier ones' outputs. -/
def Parent.cycleEnvList (p : Parent) (flat : Env) (inputs : List (String × Nat)) :
    List (String × Nat) :=
  p.insts.foldl (fun acc inst =>
      let pe := Env.ofList acc
      let outs := (inst.child.outputs?eval (inst.regVals flat) (inst.childIn pe)).map
                    (fun pv => (inst.instName ++ "." ++ pv.1, pv.2))
      acc ++ outs)
    inputs

/-- Initial hierarchical register state: every child register at its `init`, keyed `"<inst>.<reg>"`. -/
def Parent.initFlat (p : Parent) : List (String × Nat) :=
  p.insts.flatMap (fun inst =>
    inst.child.regs.map (fun r => (inst.instName ++ "." ++ r.name, r.init.toNat)))

/-- Advance the whole hierarchical register state by one cycle: every child steps its own registers
    (from its current registers, mapped inputs, and mapped reset), the results re-keyed
    `"<inst>.<reg>"`. -/
def Parent.nextFlat (p : Parent) (flat : Env) (inputs : List (String × Nat)) :
    List (String × Nat) :=
  let pe := Env.ofList (p.cycleEnvList flat inputs)
  p.insts.flatMap (fun inst =>
    let stepped := inst.child.step (inst.regVals flat) (inst.childIn pe) (inst.resetActive pe)
    inst.child.regs.map (fun r => (inst.instName ++ "." ++ r.name, stepped r.name)))

/-- One cycle's parent outputs, sampled from the *current* registers (Moore): the parent output
    expressions evaluated in this cycle's parent environment. -/
def Parent.outCycle (p : Parent) (flat : Env) (inputs : List (String × Nat)) :
    List (String × Nat) :=
  let e := Env.ofList (p.cycleEnvList flat inputs)
  p.outputs.map (fun o => (o.name, (eval o.expr e).toNat))

/-- **Stateful hierarchical simulator (F10).**  Run a parent with (possibly) sequential children over
    a list of input cycles, threading every child instance's register file across cycles.  Output of
    cycle `i` is sampled from the register state *before* that cycle's clock edge (Moore). -/
def Parent.simulateSeq (p : Parent) (cycles : List (List (String × Nat))) :
    List (List (String × Nat)) :=
  ((cycles.foldl
      (fun (st : List (String × Nat) × List (List (String × Nat))) inpL =>
        let flat := Env.ofList st.1
        (p.nextFlat flat inpL, p.outCycle flat inpL :: st.2))
      (p.initFlat, [])).2).reverse

/-! ## Executable fast path (CLI)

`evalWires` binds each wire as a *closure re-evaluating its expression on every lookup* —
fine for proofs, but executing it re-computes whole cones per reference (potentially
exponential with fanout).  `evalWiresFast` materialises each wire's value ONCE at bind time;
its equality to the reference is proved by fold induction, so no semantic assumption is added.  `Module.simulateFast` is the
CLI-facing simulator built on it (and a reversed accumulator instead of quadratic append);
`CompilerCorrectSeq.simulateFast_eq` proves it computes exactly `Module.simulate`. -/

/-- Explicit value table, with the incoming environment as a fallback. Keeping values
    in a data structure prevents closure/let optimizations from recomputing shared cones. -/
def wireValuesEnv (values : List (String × Nat)) (base : Env) : Env :=
  fun n => match values.lookup n with
    | some v => v
    | none => base n

def evalWireMemoStep (base : Env) (values : List (String × Nat)) (w : Wire) : List (String × Nat) :=
  (w.name, (eval w.expr (wireValuesEnv values base)).toNat) :: values

private theorem evalWireMemoFold_eq (wires : List Wire) (values : List (String × Nat)) (base : Env) :
    wireValuesEnv (wires.foldl (evalWireMemoStep base) values) base = evalWires wires (wireValuesEnv values base) := by
  induction wires generalizing values with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.foldl_cons, evalWires] at *
    rw [ih]
    congr 1
    funext n
    by_cases h : n = w.name
    · simp [evalWireMemoStep, wireValuesEnv, h]
    · have hb : (n == w.name) = false := by simp [h]
      simp [evalWireMemoStep, wireValuesEnv, List.lookup_cons, h, hb]

def evalWiresFast (wires : List Wire) (base : Env) : Env :=
  wireValuesEnv (wires.foldl (evalWireMemoStep base) []) base

theorem evalWiresFast_eq (wires : List Wire) (base : Env) :
    evalWiresFast wires base = evalWires wires base :=
  evalWireMemoFold_eq wires [] base

/-- Executable simulator: semantics of `Module.simulate`, engineering of a linear-time loop
    (materialised wires, reversed output accumulator). -/
def Module.simulateFast (m : Module) (cycles : List (List (String × Nat))) :
    List (List (String × Nat)) :=
  let regNames := m.regs.map (·.name)
  let init : List (String × Nat) := m.regs.map (fun r => (r.name, r.init.toNat))
  ((cycles.foldl
    (fun (st : List (String × Nat) × List (List (String × Nat))) inpL =>
      let inp := Env.ofList inpL
      let e := evalWiresFast m.wires (cycleEnv (Env.ofList st.1) inp regNames)
      let outs := m.outputs.map (fun o => (o.name, (eval o.expr e).toNat))
      let rst := match m.reset with | some r => (inp r != 0) | none => false
      let regs' := m.regs.map (fun r =>
        (r.name, if rst then r.init.toNat else (eval r.next e).toNat))
      (regs', outs :: st.2))
    (init, [])).2).reverse

end LeanRTL
