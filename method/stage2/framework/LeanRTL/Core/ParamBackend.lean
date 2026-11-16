import LeanRTL.Core.Syntax
import LeanRTL.Core.Semantics
import LeanRTL.Core.PModule
/-!
# Parametric-Verilog emitter for the F2 class.

`emitParamVerilog` turns a **ParamModule** (`gen : List Nat → Module`, one entry per declared
Verilog parameter) into genuinely parametric SystemVerilog:

```verilog
module M #(parameter DATA_WIDTH = 16, parameter NUM_TAPS = 8)
  (input [DATA_WIDTH*NUM_TAPS-1:0] a, ...); ... endmodule
```

Nothing here is written per design.  Three facts make it work:

1. **Widths and constants are *fitted*, then *verified*.**  `gen` is instantiated at a designed
   grid of parameter vectors, and every `Nat` the emitted text must contain — a port width, an
   internal `Expr` node's width, a literal's *value*, a `zext`/`sext` amount, a bit index, a slice
   origin — is fitted by `fitNat` as a multilinear form in the parameters plus `$clog2` terms.  The
   fitted form is then evaluated at *every* sample point, including the ones the fit did not use.
   A single mismatch and the fit is `none`, and the emit **refuses with a reason** rather than
   shipping a formula it has not checked.  This is the one property the whole file rests on: the
   emitter is allowed to guess, and is not allowed to guess silently.

2. **The body is emitted width-explicitly (SSA).**  Every `Expr` node becomes its own
   explicitly-sized net — `wire [W-1:0] _tK = <op of operand nets>;` — exactly as the LeanRTL RTLIL
   compiler allocates one bus per cell.  Because each operand is a full-width net, Verilog's
   context- or self-determined-width rules can never silently truncate an intermediate (the trap a
   naive `$signed(a*b)>>>1` falls into: `$signed`'s argument is self-determined, shrinking the
   product).  Sign-extension is real bit replication `{ {k{ a[hi] }}, a }`; arithmetic shift is
   `$signed(a) >>> k` on a full-width net.

3. **The samples are walked in lockstep.**  `peel` turns each sample of a node into a constructor
   tag plus its children, so one flat recursion covers all of `Expr`'s cases at every sample at
   once.  Samples that disagree on the *shape* of a node are a structural difference across
   parameter values, which is exactly the thing this emitter cannot express — so it refuses.

The emission is validated per-vector by a Yosys equivalence miter against the design's *verified*
RTLIL path (`compile (gen v)`), so any emitter bug is caught rather than trusted.

## What it refuses, and why that is the interesting part

A parameter that changes the **number of registers** — a memory depth, a sort-array length, a
matrix row count — makes `gen v` a structurally *different* module at different `v`, and this
emitter is a lockstep walk over structurally identical samples.  It says so by name.  The previous
emitter zipped two samples with `List.zip`, which truncates: a design whose register count moved
lost registers silently and shipped.  Refusing loudly is strictly better than that, and it is why
`emitParamVerilog` returns `Except String String`.

Also refused, for the same reason and by the same mechanism: any width or constant that is not
multilinear-plus-`$clog2` in the parameters — a `2^N-1` mask, a `N/2` floor division, a
`DW*$clog2(NT)` product.  These reach verification and fail it.

The archived per-design templates that used to live in this file are in
`LeanRTL.Core.ParamTemplates`, which `harness/stage.py` deliberately does **not** copy into an
author's workspace.
-/
namespace LeanRTL.Designs.Param
open LeanRTL

/-! ## Parameter metadata -/

/-- Metadata pairing a registry key with the design's Verilog parameters and its generator. -/
structure ParamMeta where
  /-- Registry key = emitted Verilog module name (`gen defaults |>.name`). -/
  key    : String
  /-- The Verilog parameters in **declaration order**, each with its default value.  The order is
      load-bearing: it is the order `gen` expects its argument vector in, and the order the
      `#(parameter …)` header is emitted in. -/
  params : List (String × Nat)
  /-- The generator, applied to a vector in `params` order. -/
  gen    : List Nat → Module
  /-- The **symbolic** form of the same family, when the author wrote one.

      Everything else in this file recovers a parametric module by *sampling* `gen`, and sampling
      has a hard limit: a parameter that moves the module's SHAPE — a filter's tap count, an adder
      tree's input count, a matrix dimension — makes `shapeMismatch` refuse, because the emitter
      observes points and a point does not carry a loop.  A `PModule` carries the loop, so when
      this field is present `emitParamVerilog` renders it directly and never fits anything.

      `gen` stays required and stays the gold: `leanrtl extract --N` runs the **verified compiler**
      on `gen v`, and `param_anchor` proves the emitted text against that netlist at several
      vectors.  What ties the two together is the author's own obligation, `sym.elabAt v =
      some (gen v)`, which is `rfl` when it holds.  So a wrong `sym` cannot slip through: it would
      have to agree with the compiler's netlist at every anchored vector. -/
  sym    : Option PModule := none

/-- The parameter names, in declaration order. -/
def ParamMeta.names (pm : ParamMeta) : List String := pm.params.map (·.1)

/-- The declared default vector — the instance every non-parametric gate in the pipeline sees. -/
def ParamMeta.defaults (pm : ParamMeta) : List Nat := pm.params.map (·.2)

/-! ## Fitted forms

A `WForm` is a `Nat`-valued function of the parameter vector, in the only shape this emitter can
render: a multilinear polynomial (degree ≤ 1 in each parameter, so products of *distinct*
parameters are in and squares are out) plus a linear combination of `$clog2` of single parameters.

That is not an arbitrary choice; it is the shape RTL width arithmetic actually takes.  `DATA_WIDTH`,
`2*WIDTH+1`, `DATA_WIDTH+COEFF_WIDTH`, `DATA_WIDTH*NUM_TAPS`, `ROWS*COLS`, `$clog2(DEPTH)` and
`DATA_WIDTH+COEFF_WIDTH+$clog2(NUM_TAPS)` are all in it.  Everything outside it is refused. -/

/-- Ceiling log base 2, matching Verilog's `$clog2`: the number of bits needed to index `n` items. -/
def clog2 (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- A fitted `Nat`-valued function of the parameter vector. -/
structure WForm where
  /-- The constant term. -/
  konst : Int := 0
  /-- Multilinear terms: a coefficient and the set of parameter indices multiplied together.  The
      index list is always non-empty and ascending. -/
  terms : List (Int × List Nat) := []
  /-- `$clog2` terms: a coefficient and the parameter index it is taken of. -/
  logs  : List (Int × Nat) := []
  deriving Inhabited

/-- Evaluate a fitted form at a concrete parameter vector. -/
def WForm.eval (f : WForm) (xs : List Nat) : Int :=
  let mono := f.terms.foldl
    (fun acc t => acc + t.1 * t.2.foldl (fun p i => p * (xs.getD i 1 : Int)) 1) 0
  let lg := f.logs.foldl (fun acc t => acc + t.1 * (clog2 (xs.getD t.2 1) : Int)) 0
  f.konst + mono + lg

/-- Is this form the literal `1`?  (A 1-bit net takes no `[hi:lo]` range in Verilog.) -/
def WForm.isOne (f : WForm) : Bool :=
  f.terms.isEmpty && f.logs.isEmpty && f.konst == 1

/-- Is this form a plain constant, and if so which? -/
def WForm.asConst? (f : WForm) : Option Int :=
  if f.terms.isEmpty && f.logs.isEmpty then some f.konst else none

/-- One signed piece of a rendered form: `("+", "2*DATA_WIDTH")`. -/
private def renderPiece (c : Int) (body : String) : String × String :=
  let sgn := if c < 0 then "-" else "+"
  let mag := c.natAbs
  if body.isEmpty then (sgn, toString mag)
  else if mag == 1 then (sgn, body)
  else (sgn, s!"{mag}*{body}")

/-- Render a fitted form as a SystemVerilog elaboration-time expression, e.g.
    `DATA_WIDTH+COEFF_WIDTH+$clog2(NUM_TAPS)`.  Parameters are elaboration-time constants, so the
    result is legal anywhere a constant expression is (a port range, a part-select, a replication
    count). -/
def WForm.render (f : WForm) (names : List String) : String :=
  let nameOf := fun (i : Nat) => names.getD i s!"P{i}"
  let monoPieces := f.terms.map (fun t =>
    renderPiece t.1 (String.intercalate "*" (t.2.map nameOf)))
  let logPieces := f.logs.map (fun t => renderPiece t.1 s!"$clog2({nameOf t.2})")
  let others := monoPieces ++ logPieces
  let pieces := if f.konst == 0 && !others.isEmpty then others
                else others ++ [renderPiece f.konst ""]
  match pieces with
  | [] => "0"
  | (s0, b0) :: rest =>
      let head := if s0 == "-" then "-" ++ b0 else b0
      rest.foldl (fun acc p => acc ++ p.1 ++ p.2) head

/-- A port/wire range `[width-1:0]`, or empty for a 1-bit scalar. -/
def rangeOfW (f : WForm) (names : List String) : String :=
  if f.isOne then "" else s!"[{f.render names}-1:0] "

/-! ## The sample grid

The grid is designed, not random, and it is designed around one hazard: `$clog2` is a step
function, so a fit taken across a power-of-two boundary attributes the step to whichever parameter
happens to be moving.  So the multilinear fit is taken inside a box where every `$clog2` is
*constant* (two adjacent values in the same octave), and `$clog2` is measured separately by one
probe per parameter that crosses exactly one boundary.

The probe values are small — 5, 6, 9 at the first octave — because a sample is a whole elaborated
`Module` and there are `2^k` of them.  A six-parameter matrix design is sampled as a 6×6 instance,
not a 65×65 one.  If verification fails at the first octave the whole thing is retried one octave
up, which is what catches a design that special-cases a small parameter value. -/

/-- Probe values for one parameter at octave `e`: two points with the same `$clog2` and one that
    crosses into the next octave.  For `e = 2` this is `(5, 6, 9)`. -/
def probeTriple (e : Nat) : Nat × Nat × Nat := (2 ^ e + 1, 2 ^ e + 2, 2 ^ (e + 1) + 1)

/-- The sample grid for one octave, and the bookkeeping `fitNat` needs to read it. -/
structure FitCtx where
  /-- Parameter names, in declaration order. -/
  names : List String
  /-- Number of parameters. -/
  k     : Nat
  /-- Per-parameter low corner value (same `$clog2` as `hi`). -/
  lo    : List Nat
  /-- Per-parameter next-octave probe value. -/
  up    : List Nat
  /-- Every sample vector, in order: `2^k` corners (in bitmask order), then `k` `$clog2` probes,
      then the held-out verification points. -/
  pts   : List (List Nat)
  /-- `2^k` — where the corners end and the `$clog2` probes begin. -/
  nFit  : Nat

/-- The parameter indices set in bitmask `m`, ascending. -/
def bitsOf (k m : Nat) : List Nat :=
  (List.range k).filter (fun i => ((m >>> i) &&& 1) == 1)

/-- Number of set bits in `m`, below index `k`. -/
def popcount (k m : Nat) : Nat :=
  (List.range k).foldl (fun acc i => acc + ((m >>> i) &&& 1)) 0

/-- Build the sample grid for `params` at octave `e`. -/
def mkCtx (params : List (String × Nat)) (e : Nat) : FitCtx :=
  let k := params.length
  let names := params.map (·.1)
  let tri := probeTriple e
  let lo := List.replicate k tri.1
  let hi := List.replicate k tri.2.1
  let up := List.replicate k tri.2.2
  let nFit := 2 ^ k
  let corners := (List.range nFit).map (fun m =>
    (List.range k).map (fun i => if ((m >>> i) &&& 1) == 1 then hi.getD i 1 else lo.getD i 1))
  let probes := (List.range k).map (fun i =>
    (List.range k).map (fun j => if j == i then up.getD j 1 else lo.getD j 1))
  -- Held-out points.  The defaults are in there because they are the instance every other gate in
  -- the pipeline actually elaborates; a fit that is right on the grid and wrong at the default
  -- would ship a module whose default instance disagrees with its own proof.
  let defaults := params.map (·.2)
  let vHigh := (List.range k).map (fun i => 2 ^ (e + 2) + 1 + i)
  let vMixed := (List.range k).map (fun i => if i % 2 == 0 then 2 ^ e + 1 else 2 ^ (e + 1) + 2)
  { names, k, lo, up, nFit, pts := corners ++ probes ++ [defaults, vHigh, vMixed] }

/-- Fit a `Nat`-valued observation over the grid as a `WForm`, or refuse.

    Three steps, and the third is the one that matters.  (1) Multilinear coefficients from the
    `2^k` corners by inclusion–exclusion, converted from the Newton basis to the monomial basis.
    (2) One `$clog2` coefficient per parameter, read off as the residual at that parameter's
    octave-crossing probe — inside the corner box every `$clog2` is constant, so it was absorbed
    into the fitted constant term, and the residual at a probe that moves `$clog2` by exactly one
    *is* the coefficient.  (3) Evaluate the result at **every** point in the grid, including the
    held-out ones, and return `none` on any mismatch.  Step 3 is what makes steps 1 and 2 safe to
    do at all. -/
def fitNat (ctx : FitCtx) (ys : List Nat) : Option WForm := Id.run do
  if ys.length ≠ ctx.pts.length then return none
  if ctx.k == 0 then return none
  -- Fast path.  The overwhelmingly common observation is a value that does not move with the
  -- parameters at all — a 1-bit net, a literal `0` reset, a fixed bit index.  Skip the O(4^k) fit.
  match ys with
  | [] => return none
  | y0 :: _ => if ys.all (· == y0) then return some { konst := (y0 : Int) }
  let nc := ctx.nFit
  let y := fun (i : Nat) => (ys.getD i 0 : Int)
  -- (1a) Newton coefficients over the corner box: d_S = Σ_{T ⊆ S} (-1)^{|S \ T|} · y(corner T).
  let mut d : Array Int := (List.replicate nc (0 : Int)).toArray
  for s in [0:nc] do
    let mut acc : Int := 0
    for t in [0:nc] do
      if (t &&& s) == t then
        acc := acc + (if popcount ctx.k (s ^^^ t) % 2 == 0 then y t else -(y t))
    d := d.set! s acc
  -- (1b) Newton → monomial: a_U = Σ_{S ⊇ U} d_S · Π_{i ∈ S \ U} (-lo_i).
  let mut a : Array Int := (List.replicate nc (0 : Int)).toArray
  for u in [0:nc] do
    let mut acc : Int := 0
    for s in [0:nc] do
      if (u &&& s) == u then
        let mut p : Int := 1
        for i in [0:ctx.k] do
          if ((s >>> i) &&& 1) == 1 && ((u >>> i) &&& 1) == 0 then
            p := p * (-(ctx.lo.getD i 1 : Int))
        acc := acc + d[s]! * p
    a := a.set! u acc
  let ml : WForm :=
    { konst := a[0]!
    , terms := (List.range nc).filterMap (fun u =>
        if u ≠ 0 && a[u]! ≠ 0 then some (a[u]!, bitsOf ctx.k u) else none)
    , logs  := [] }
  -- (2) `$clog2` coefficients, one octave-crossing probe per parameter.
  let mut gammas : List (Int × Nat) := []
  let mut absorbed : Int := 0
  for i in [0:ctx.k] do
    let pt := ctx.pts.getD (nc + i) []
    let g := y (nc + i) - ml.eval pt
    if g ≠ 0 then
      gammas := gammas ++ [(g, i)]
      absorbed := absorbed + g * (clog2 (ctx.lo.getD i 1) : Int)
  let f : WForm := { ml with konst := ml.konst - absorbed, logs := gammas }
  -- (3) Verify everywhere, and refuse rather than ship an unverified formula.
  for pt in ctx.pts, yv in ys do
    if f.eval pt ≠ (yv : Int) then return none
  return some f

/-! ## Lockstep expression emission -/

/-- One sample of an expression: its width and the expression itself.  The width is a field rather
    than an index so a *list* of samples at different widths is an ordinary list. -/
structure ESam where
  /-- The sample's bit width. -/
  w : Nat
  /-- The sampled expression. -/
  e : Expr w

instance : Inhabited ESam := ⟨⟨1, .const (0 : BitVec 1)⟩⟩

/-- An `Expr` node's constructor, with the numeric payload that has to be *fitted* rather than
    compared: a literal's value, an extension amount, a bit index, a slice origin and length. -/
inductive Tag where
  /-- A literal, carrying its value at this sample. -/
  | const (v : Nat)
  /-- A named net. -/
  | var (n : String)
  | not | and | or | xor | add | sub | mul
  | shl | shr | sshr | udiv | umod | eq | ult | slt | mux | concat
  /-- Zero-extend by `k` bits at this sample. -/
  | zext (k : Nat)
  /-- Sign-extend by `k` bits at this sample. -/
  | sext (k : Nat)
  /-- Single-bit select at index `i` at this sample. -/
  | extract (i : Nat)
  /-- Field of `len` bits from bit `lo` at this sample. -/
  | slice (lo len : Nat)
  deriving Inhabited

/-- The constructor's identity, ignoring the numeric payload.  Two samples of the same node must
    agree on this and need not agree on the payload — the payload is what gets fitted. -/
def Tag.ctor : Tag → Nat
  | .const _ => 0  | .var _ => 1    | .not => 2      | .and => 3      | .or => 4
  | .xor => 5      | .add => 6      | .sub => 7      | .mul => 8      | .shl => 9
  | .shr => 10     | .sshr => 11    | .udiv => 12    | .umod => 13    | .eq => 14
  | .ult => 15     | .slt => 16     | .mux => 17     | .concat => 18  | .zext _ => 19
  | .sext _ => 20  | .extract _ => 21 | .slice _ _ => 22

/-- A short name for the tag, for refusal messages. -/
def Tag.name : Tag → String
  | .const _ => "const" | .var n => s!"var {n}" | .not => "not"   | .and => "and"
  | .or => "or"         | .xor => "xor"         | .add => "add"   | .sub => "sub"
  | .mul => "mul"       | .shl => "shl"         | .shr => "shr"   | .sshr => "sshr"
  | .udiv => "udiv"     | .umod => "umod"       | .eq => "eq"     | .ult => "ult"
  | .slt => "slt"       | .mux => "mux"         | .concat => "concat"
  | .zext _ => "zext"   | .sext _ => "sext"     | .extract _ => "extract"
  | .slice _ _ => "slice"

/-- Split one sample of a node into its tag and its children.  One function, so the recursion
    below is flat instead of twenty-three simultaneous dependent matches. -/
def peel : ESam → Tag × List ESam
  | ⟨_, .const v⟩      => (.const v.toNat, [])
  | ⟨_, .var n _⟩      => (.var n, [])
  | ⟨_, .not a⟩        => (.not, [⟨_, a⟩])
  | ⟨_, .and a b⟩      => (.and, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .or a b⟩       => (.or, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .xor a b⟩      => (.xor, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .add a b⟩      => (.add, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .sub a b⟩      => (.sub, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .mul a b⟩      => (.mul, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .shl a b⟩      => (.shl, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .shr a b⟩      => (.shr, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .sshr a b⟩     => (.sshr, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .udiv a b⟩     => (.udiv, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .umod a b⟩     => (.umod, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .eq a b⟩       => (.eq, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .ult a b⟩      => (.ult, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .slt a b⟩      => (.slt, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .mux s a b⟩    => (.mux, [⟨_, s⟩, ⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .concat a b⟩   => (.concat, [⟨_, a⟩, ⟨_, b⟩])
  | ⟨_, .zext k a⟩     => (.zext k, [⟨_, a⟩])
  | ⟨_, .sext k a⟩     => (.sext k, [⟨_, a⟩])
  | ⟨_, .extract i a⟩  => (.extract i, [⟨_, a⟩])
  | ⟨_, .slice lo l a⟩ => (.slice lo l, [⟨_, a⟩])

/-- Emitter state: fresh-net counter, accumulated `wire` declarations, and accumulated refusals.
    Refusals are collected rather than thrown so one emit reports every reason it failed, not just
    the first one an author would then fix and re-run into the next. -/
structure EMState where
  /-- Next fresh-net index. -/
  ctr   : Nat := 0
  /-- Accumulated `wire` declarations, most recent first. -/
  decls : List String := []
  /-- Accumulated refusal reasons, most recent first. -/
  errs  : List String := []
  deriving Inhabited

abbrev EM := StateM EMState

/-- Record a reason this module cannot be emitted parametrically. -/
def refuse (msg : String) : EM Unit :=
  modify fun s => { s with errs := if s.errs.contains msg then s.errs else msg :: s.errs }

/-- Is `s` already a simple Verilog identifier (safe to bit-select / replicate)? -/
def isIdent (s : String) : Bool :=
  match s.toList with
  | []     => false
  | c :: _ => !c.isDigit && s.all (fun ch => ch.isAlphanum || ch == '_')

/-- Bind `rhs` to a fresh net of the given fitted width; returns the fresh net name. -/
def freshNet (ctx : FitCtx) (f : WForm) (rhs : String) : EM String := do
  let st ← get
  let nm := s!"_t{st.ctr}"
  set { st with ctr := st.ctr + 1,
                decls := s!"  wire {rangeOfW f ctx.names}{nm} = {rhs};" :: st.decls }
  return nm

/-- Force `s` to be an identifier net, materialising a wire if it is a literal or a compound
    expression (so it can be bit-selected or replicated). -/
def ensureNet (ctx : FitCtx) (f : WForm) (s : String) : EM String :=
  if isIdent s then return s else freshNet ctx f s

/-- Fit one observation, or record a refusal naming what could not be expressed and fall back to
    the value at the first sample so the traversal stays total (the refusal is what fails the
    emit; a partial traversal would just lose the *other* reasons). -/
def fitOrRefuse (ctx : FitCtx) (what : String) (ys : List Nat) : EM WForm := do
  match fitNat ctx ys with
  | some f => return f
  | none =>
      refuse s!"cannot express {what} as a function of ({String.intercalate ", " ctx.names}); \
observed {ys.take 6} over the sample grid — it is not multilinear-plus-$clog2 in the parameters"
      return { konst := (ys.headD 1 : Int) }

/-- Emit an `Expr` as width-explicit SSA over all of its samples at once; returns the net (or
    literal, for a leaf) holding its value. -/
partial def emitExprN (ctx : FitCtx) (sams : List ESam) : EM String := do
  match sams with
  | [] =>
      refuse "internal: empty sample list"
      return "/* emit: no-samples */"
  | s0 :: _ =>
    let peeled := sams.map peel
    let tag0 := (peel s0).1
    if peeled.any (fun p => p.1.ctor != tag0.ctor) then
      refuse s!"the expression tree changes shape across parameter values (at a `{tag0.name}` \
node) — the parameter changes the design's structure, not just its widths, and this emitter walks \
the samples in lockstep"
      return "/* emit: shape-differs */"
    let wf ← fitOrRefuse ctx s!"the width of a `{tag0.name}` node" (sams.map (·.w))
    let child := fun (i : Nat) => peeled.map (fun p => p.2.getD i default)
    let one : WForm := { konst := 1 }
    match tag0 with
    | .const _ =>
        let vals := peeled.map (fun p => match p.1 with | .const v => v | _ => 0)
        let vf ← fitOrRefuse ctx "a literal's value" vals
        -- SIZED, and sized to the node's own fitted width.
        --
        -- A bare `1` is not a 1-bit constant in Verilog, it is a 32-bit SIGNED integer, and that
        -- leaks into every operator it touches.  `(0) - x` becomes a 32-bit signed subtraction
        -- rather than one at the datapath's width, and `(1) < x` follows the standard's coercion
        -- rule -- a comparison with any unsigned operand is done unsigned -- so a negative value
        -- on the other side compares as a very large positive one and the result inverts.  The
        -- compiler's netlist has neither behaviour, because it has no unsized literals: it carries
        -- the width on every node.  So a module that was correct in Lean shipped Verilog that
        -- disagreed with it, on a combinational design, at its DECLARED DEFAULT vector.
        --
        -- The size cast rather than `W'd<v>`: a sized literal's width must be a decimal *number*,
        -- so `(IN_WIDTH+1)'d1` is not legal Verilog, while the cast takes any constant expression
        -- and parameters are elaboration-time constants.  Checked against both toolchains this
        -- pipeline puts the text through (Yosys, and iverilog for `cosim`).
        let body := match vf.asConst? with
                    | some c => toString c
                    | none   => s!"({vf.render ctx.names})"
        return s!"(({wf.render ctx.names})'({body}))"
    | .var n =>
        if peeled.any (fun p => match p.1 with | .var m => m != n | _ => true) then
          refuse s!"a net's name changes across parameter values (near `{n}`)"
        return n
    | .not => do
        let x ← emitExprN ctx (child 0); freshNet ctx wf s!"(~{x})"
    | .and => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"({x} & {y})"
    | .or => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"({x} | {y})"
    | .xor => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"({x} ^ {y})"
    | .add => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"({x} + {y})"
    | .sub => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"({x} - {y})"
    | .mul => do
        -- LeanRTL `mul` has operand width = result width, so the operand nets are already full
        -- width; an unsigned product mod 2^w equals the exact product's low `w` bits.
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"({x} * {y})"
    | .shl => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"({x} << {y})"
    | .shr => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"({x} >> {y})"
    | .sshr => do
        -- arithmetic right shift: `$signed(net)` is self-determined at the net's (full) width,
        -- and the result is also that width, so no truncation.
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"($signed({x}) >>> {y})"
    | .udiv => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"({x} / {y})"
    | .umod => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf s!"({x} % {y})"
    | .eq => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx one s!"({x} == {y})"
    | .ult => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx one s!"({x} < {y})"
    | .slt => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx one s!"($signed({x}) < $signed({y}))"
    | .mux => do
        let s ← emitExprN ctx (child 0)
        let x ← emitExprN ctx (child 1); let y ← emitExprN ctx (child 2)
        freshNet ctx wf s!"({s} ? {x} : {y})"
    | .concat => do
        let x ← emitExprN ctx (child 0); let y ← emitExprN ctx (child 1)
        freshNet ctx wf ("{" ++ x ++ ", " ++ y ++ "}")
    | .zext _ => do
        let ks := peeled.map (fun p => match p.1 with | .zext k => k | _ => 0)
        let kf ← fitOrRefuse ctx "a zero-extension amount" ks
        let af ← fitOrRefuse ctx "a zero-extension operand width" ((child 0).map (·.w))
        let x ← ensureNet ctx af (← emitExprN ctx (child 0))
        freshNet ctx wf ("{ {" ++ kf.render ctx.names ++ "{1'b0}}, " ++ x ++ " }")
    | .sext _ => do
        let ks := peeled.map (fun p => match p.1 with | .sext k => k | _ => 0)
        let kf ← fitOrRefuse ctx "a sign-extension amount" ks
        let af ← fitOrRefuse ctx "a sign-extension operand width" ((child 0).map (·.w))
        let x ← ensureNet ctx af (← emitExprN ctx (child 0))
        freshNet ctx wf ("{ {" ++ kf.render ctx.names ++ "{" ++ x ++ "["
          ++ af.render ctx.names ++ "-1]}}, " ++ x ++ " }")
    | .extract _ => do
        let is := peeled.map (fun p => match p.1 with | .extract i => i | _ => 0)
        let jf ← fitOrRefuse ctx "a bit index" is
        let af ← fitOrRefuse ctx "a bit-select operand width" ((child 0).map (·.w))
        let x ← ensureNet ctx af (← emitExprN ctx (child 0))
        freshNet ctx one s!"{x}[{jf.render ctx.names}]"
    | .slice _ _ => do
        let los := peeled.map (fun p => match p.1 with | .slice l _ => l | _ => 0)
        let lens := peeled.map (fun p => match p.1 with | .slice _ n => n | _ => 0)
        let lof ← fitOrRefuse ctx "a slice origin" los
        let lenf ← fitOrRefuse ctx "a slice length" lens
        let af ← fitOrRefuse ctx "a slice operand width" ((child 0).map (·.w))
        let x ← ensureNet ctx af (← emitExprN ctx (child 0))
        -- `[lo +: len]` rather than `[lo+len-1 : lo]`: both origin and length are parameter
        -- expressions here, and the ascending part-select keeps the width syntactically obvious
        -- (and legal) without the emitter having to fold `lo + len - 1` itself.
        freshNet ctx wf s!"{x}[{lof.render ctx.names} +: {lenf.render ctx.names}]"

/-! ## Module emission -/

/-- Is `name` the name of some register in `m`? -/
def isRegName (m : Module) (name : String) : Bool := m.regs.any (·.name == name)

/-- The async-reset net (active-high) shared by the registers, if any. -/
def asyncResetNet (m : Module) : Option String :=
  m.regs.findSome? (fun r => r.asyncReset.map (·.1))

/-- Column `j` of a per-sample list of lists: the `j`-th element of every sample, in sample order.
    Used instead of positional indexing because `OutPort` and `Reg` carry width-indexed `Expr`
    fields and therefore have no `Inhabited` instance to index with. -/
def colsOf {α : Type} (n : Nat) (xss : List (List α)) : List (List α) :=
  (List.range n).map (fun j => xss.filterMap (fun xs => xs[j]?))

/-- Do all samples agree on the module's *shape* — the same ports, registers and names, in the same
    order?  A disagreement means the parameter changes the design's structure rather than its
    widths, which is the boundary of what this emitter can express.  It is checked explicitly, and
    named explicitly, because the emitter it replaces zipped its two samples with `List.zip`, and
    `List.zip` truncates: a design whose register count moved with the parameter silently lost
    registers and shipped anyway. -/
def shapeMismatch (names : List String) (ms : List Module) : Option String :=
  match ms with
  | [] => some "internal: no samples"
  | m0 :: rest =>
    -- Fields this emitter cannot render at all.  Checked FIRST, and on the sample the caller is
    -- about to emit rather than on a disagreement between samples: a latch is unrenderable whether
    -- or not the parameter moves it, and the failure it used to produce was a yosys parse error
    -- from the anchor, which names a line number in generated text instead of the feature.
    if !m0.latches.isEmpty then
      some s!"the module declares {m0.latches.length} transparent latch(es), which the generic \
parametric emitter does not render; the design belongs on the f9 / write_verilog route"
    else
    let bad := rest.find? (fun m =>
      m.name != m0.name
      || m.inputs.length != m0.inputs.length
      || m.outputs.length != m0.outputs.length
      || m.regs.length != m0.regs.length
      -- `wires` and `mems` used to be absent from this comparison AND from the emitter, so a
      -- design carrying either had it silently dropped: a memory vanished from the netlist, and a
      -- wire reference became an undeclared identifier.  Both are emitted now, and both are
      -- compared here, because a count that moves with the parameter is the same structural
      -- refusal as a register count that moves.
      || m.wires.length != m0.wires.length
      || m.mems.length != m0.mems.length
      || m.inputs.map (·.name) != m0.inputs.map (·.name)
      || m.outputs.map (·.name) != m0.outputs.map (·.name)
      || m.regs.map (·.name) != m0.regs.map (·.name)
      || m.wires.map (·.name) != m0.wires.map (·.name)
      || m.mems.map (·.name) != m0.mems.map (·.name)
      || m.mems.map (·.writes.length) != m0.mems.map (·.writes.length)
      || m.mems.map (·.reads.length) != m0.mems.map (·.reads.length)
      || m.clock != m0.clock)
    match bad with
    | none => none
    | some m =>
        if m.regs.length != m0.regs.length then
          some s!"the number of registers changes with ({String.intercalate ", " names}) \
({m0.regs.length} vs {m.regs.length}) — a parameter that sizes an array of individually-named \
registers changes the module's structure, not just its widths, and SAMPLING cannot express it: \
this emitter sees `gen` at points, and a point does not carry a loop.  Two ways out, both \
supported.  (1) Write the family symbolically as a `PModule` (`LeanRTL.Core.PModule`) and set \
`sym := some <family>` on the `paramMeta`: a `PReg` with `count := some <NatE>` is an array of \
parametric length and a `PExpr.fold` is a reduction over a parametric range, so nothing is fitted \
and nothing is refused for shape.  (2) If the registers are STORAGE rather than a datapath, model \
them as a `MemBlock` in `Module.mems`, whose `addrWidth` is fitted like any other width"
        else if m.wires.length != m0.wires.length then
          some s!"the number of wires changes with ({String.intercalate ", " names}) \
({m0.wires.length} vs {m.wires.length}) — the parameter changes the module's structure.  Write \
the family symbolically as a `PModule` and set `sym` on the `paramMeta`; a per-element net becomes \
a `PExpr.fold` or an array element rather than N separate wires"
        else if m.mems.length != m0.mems.length
             || m.mems.map (·.writes.length) != m0.mems.map (·.writes.length)
             || m.mems.map (·.reads.length) != m0.mems.map (·.reads.length) then
          some s!"the number of memories, or of a memory's read/write PORTS, changes with \
({String.intercalate ", " names}) — a memory's DEPTH may move with the parameters (it is fitted \
from `addrWidth`), but how many ports it has may not"
        else
          some s!"the module's ports or names change with ({String.intercalate ", " names}) — a \
parameter that adds, removes or renames a port changes the module's structure, not just its widths"

/-- Render a register's reset value, which may itself move with the parameters.

    Three shapes, in order.  A value that is the same at every sample is that literal.  An all-ones
    value is `{W{1'b1}}` — the one common reset that is `2^W - 1` and therefore exponential in the
    parameters, which no `WForm` can express and which would otherwise refuse a perfectly ordinary
    design.  Anything else is fitted like every other `Nat`. -/
def resetValue (ctx : FitCtx) (nm : String) (widthF : WForm) (col : List Reg) : EM String := do
  let vals := col.map (·.init.toNat)
  match vals with
  | [] => return "0"
  | v0 :: _ =>
    if vals.all (· == v0) then return toString v0
    if col.all (fun r => r.init.toNat + 1 == 2 ^ r.width) then
      return "{" ++ widthF.render ctx.names ++ "{1'b1}}"
    let f ← fitOrRefuse ctx s!"the reset value of register `{nm}`" vals
    return f.render ctx.names

/-- Emit the full parametric SystemVerilog for one `ParamMeta` at one sample octave, or the list of
    reasons it cannot be emitted. -/
def emitAtOctave (pm : ParamMeta) (e : Nat) : Except (List String) String := Id.run do
  let ctx := mkCtx pm.params e
  let mods := ctx.pts.map pm.gen
  match shapeMismatch ctx.names mods with
  | some why => return .error [why]
  | none => pure ()
  match mods with
  | [] => return .error ["internal: empty sample grid"]
  | m0 :: _ =>
  let clk := m0.clock
  let arst := asyncResetNet m0
  let names := ctx.names
  let inCols := colsOf m0.inputs.length (mods.map (·.inputs))
  let outCols := colsOf m0.outputs.length (mods.map (·.outputs))
  let regCols := colsOf m0.regs.length (mods.map (·.regs))
  let wireCols := colsOf m0.wires.length (mods.map (·.wires))
  let memCols := colsOf m0.mems.length (mods.map (·.mems))
  let act : EM String := do
    -- Port declarations.
    let mut inDecls : List String := []
    for col in inCols do
      match col with
      | [] => refuse "internal: missing input sample"
      | p :: _ =>
        if some p.name == clk || some p.name == arst then
          inDecls := inDecls ++ [s!"  input  {p.name}"]
        else
          let f ← fitOrRefuse ctx s!"the width of input `{p.name}`" (col.map (·.width))
          inDecls := inDecls ++ [s!"  input  {rangeOfW f names}{p.name}"]
    let mut outDecls : List String := []
    for col in outCols do
      match col with
      | [] => refuse "internal: missing output sample"
      | o :: _ =>
        let f ← fitOrRefuse ctx s!"the width of output `{o.name}`" (col.map (·.width))
        let reg := if isRegName m0 o.name then "reg " else ""
        outDecls := outDecls ++ [s!"  output {reg}{rangeOfW f names}{o.name}"]
    -- Memory arrays.  A `MemBlock` is `2^addrWidth` words of `dataWidth` bits and BOTH move with
    -- the parameters, so both are fitted like any other width.  This is the depth-parametric
    -- storage the register path cannot express: `shapeMismatch` fixes `regs.length`, so a design
    -- that models N words as N registers is refused, but one `MemBlock` stays one `MemBlock`
    -- however deep it gets — `2**(ADDR_WIDTH)` is a legal elaboration-time bound.
    --
    -- Emitted BEFORE `wires`, because a read port drives a net that a wire commonly consumes and
    -- the reverse (a read address computed by a wire) is rare; a forward net reference at module
    -- scope is what an implicit-net rule turns into a silent 1-bit truncation.
    let mut memDecls : List String := []
    let mut memBody : List String := []
    let mut memAlways : List String := []
    for col in memCols do
      match col with
      | [] => refuse "internal: missing memory sample"
      | mb :: _ =>
        let aw ← fitOrRefuse ctx s!"the address width of memory `{mb.name}`" (col.map (·.addrWidth))
        let dw ← fitOrRefuse ctx s!"the data width of memory `{mb.name}`" (col.map (·.dataWidth))
        memDecls := memDecls
          ++ [s!"  reg    {rangeOfW dw names}{mb.name} [0:(2**({aw.render names}))-1];"]
        for j in List.range mb.reads.length do
          match mb.reads[j]? with
          | none => refuse s!"internal: missing read port {j} of memory `{mb.name}`"
          | some rd0 =>
            let addrSams := col.filterMap (fun m =>
              m.reads[j]?.map (fun rd => (⟨m.addrWidth, rd.addr⟩ : ESam)))
            let net ← emitExprN ctx addrSams
            let st ← get
            set { st with decls := [] }
            memBody := memBody ++ st.decls.reverse
                    ++ [s!"  wire {rangeOfW dw names}{rd0.out} = {mb.name}[{net}];"]
        for j in List.range mb.writes.length do
          match mb.writes[j]? with
          | none => refuse s!"internal: missing write port {j} of memory `{mb.name}`"
          | some _ =>
            let clkS := col.filterMap (fun m => m.writes[j]?.map (fun w => (⟨1, w.clock⟩ : ESam)))
            let enS := col.filterMap (fun m => m.writes[j]?.map (fun w => (⟨1, w.en⟩ : ESam)))
            let adS := col.filterMap (fun m =>
              m.writes[j]?.map (fun w => (⟨m.addrWidth, w.addr⟩ : ESam)))
            let daS := col.filterMap (fun m =>
              m.writes[j]?.map (fun w => (⟨m.dataWidth, w.data⟩ : ESam)))
            let cN ← emitExprN ctx clkS
            let eN ← emitExprN ctx enS
            let aN ← emitExprN ctx adS
            let dN ← emitExprN ctx daS
            let st ← get
            set { st with decls := [] }
            memBody := memBody ++ st.decls.reverse
            -- No `emitGuardedArrayWrite` range guard here, and that is not an omission: the array
            -- is `2**addrWidth` words and the address is exactly `addrWidth` bits, so every value
            -- the address can take is in range.  The guard exists for a POINTER register wider
            -- than `$clog2(size)`, which is a different shape.
            memAlways := memAlways
              ++ [s!"  always @(posedge {cN}) begin\n    if ({eN}) {mb.name}[{aN}] <= {dN};\n  end"]
    -- Internal combinational nets.  `Module.wires` is topologically ordered among itself, so
    -- emitting in order keeps every wire-to-wire reference backward.  These used to be dropped
    -- entirely, which turned every reference to one into an undeclared identifier.
    let mut wireBody : List String := []
    for col in wireCols do
      match col with
      | [] => refuse "internal: missing wire sample"
      | w :: _ =>
        let f ← fitOrRefuse ctx s!"the width of wire `{w.name}`" (col.map (·.width))
        let net ← emitExprN ctx (col.map (fun ww => (⟨ww.width, ww.expr⟩ : ESam)))
        let st ← get
        set { st with decls := [] }
        wireBody := wireBody ++ st.decls.reverse
                 ++ [s!"  wire {rangeOfW f names}{w.name} = {net};"]
    -- Internal registers (those not already exposed as an output port), each register's
    -- next-state cone as SSA wires ending in `<name>_next`, and its reset value.
    let mut internalRegs : List String := []
    let mut body : List String := []
    let mut resets : List String := []
    for col in regCols do
      match col with
      | [] => refuse "internal: missing register sample"
      | r :: _ =>
        let f ← fitOrRefuse ctx s!"the width of register `{r.name}`" (col.map (·.width))
        if !(m0.outputs.any (·.name == r.name)) then
          internalRegs := internalRegs ++ [s!"  reg    {rangeOfW f names}{r.name};"]
        let net ← emitExprN ctx (col.map (fun rr => (⟨rr.width, rr.next⟩ : ESam)))
        let st ← get
        set { st with decls := [] }
        body := body ++ st.decls.reverse
                     ++ [s!"  wire {rangeOfW f names}{r.name}_next = {net};"]
        let rv ← resetValue ctx r.name f col
        resets := resets ++ [s!"{r.name} <= {rv};"]
    -- Combinational (non-reg-backed) outputs.
    let mut combOuts : List String := []
    for col in outCols do
      match col with
      | [] => pure ()
      | o :: _ =>
        if !(isRegName m0 o.name) then
          let net ← emitExprN ctx (col.map (fun oo => (⟨oo.width, oo.expr⟩ : ESam)))
          let st ← get
          set { st with decls := [] }
          combOuts := combOuts ++ st.decls.reverse ++ [s!"  assign {o.name} = {net};"]
    -- Sequential process.
    let sens := match clk, arst with
      | some c, some a => s!"@(posedge {c} or posedge {a})"
      | some c, none   => s!"@(posedge {c})"
      | none, _        => "@(*)"
    let normalAssigns :=
      String.intercalate "\n      " (m0.regs.map (fun r => s!"{r.name} <= {r.name}_next;"))
    let always :=
      match arst with
      | some a =>
        s!"  always {sens} begin\n    if ({a}) begin {String.intercalate " " resets} end\n" ++
        s!"    else begin\n      {normalAssigns}\n    end\n  end"
      | none =>
        s!"  always {sens} begin\n      {normalAssigns}\n  end"
    let hdr := String.intercalate ", " (pm.params.map (fun p => s!"parameter {p.1} = {p.2}"))
    let portList := String.intercalate ",\n" (inDecls ++ outDecls)
    let proc := if m0.regs.isEmpty then [] else [always]
    return String.intercalate "\n"
      ([ s!"module {m0.name} #({hdr}) (", portList, ");" ]
        ++ internalRegs ++ memDecls ++ memBody ++ wireBody
        ++ body ++ combOuts ++ proc ++ memAlways ++ ["endmodule", ""])
  let (out, st) := act.run {}
  if st.errs.isEmpty then return .ok out else return .error st.errs.reverse

/-- Emit genuinely parametric SystemVerilog for a `ParamMeta`, or say why it cannot be.

    Two octaves are tried.  The first uses small parameter values (5, 6, 9), which keeps `2^k`
    elaborated sample modules cheap; the second (9, 10, 17) is there for a design that special-cases
    a small parameter value, which would otherwise be reported as an unfittable width.  Both
    verify their fits before returning, so a success at either octave is a success that was
    checked, and a failure is reported with the first octave's reasons — the ones about the design
    rather than about the probe values. -/
def emitParamVerilog (pm : ParamMeta) : Except String String :=
  if pm.params.isEmpty then
    .error "the design declares no parameters, so there is nothing for `pverilog` to emit \
generically; it belongs on the f9 / write_verilog route"
  else
  match pm.sym with
  -- A symbolic family is rendered, not fitted.  Checked first and unconditionally: if the author
  -- went to the trouble of writing the loops down, falling back to sampling on a refusal would
  -- silently replace the module they wrote with a fitted approximation of it.
  | some s => emitPVerilog s
  | none =>
    match emitAtOctave pm 2 with
    | .ok s => .ok s
    | .error e1 =>
      match emitAtOctave pm 3 with
      | .ok s => .ok s
      | .error _ => .error (String.intercalate "\n" e1)

/-! ## Shared dynamic-index array-write invariant (M28 strike-2 promotion)

A parametric template's dynamic-index array WRITE `arr[idx] <= rhs` **aliases** in the
yosys-elaborated netlist whenever the index register is wider than `$clog2(array_size)`: yosys
truncates a memory write address to `$clog2(SIZE)` bits, so an in-principle out-of-bounds index (e.g.
a fill pointer at value `DEPTH` for a `DEPTH`-entry array with a `$clog2(DEPTH+1)`-bit pointer) wraps
onto word `idx mod SIZE` instead of being the intended no-op — diverging from both iverilog
semantics (OOB write = no-op) and the Lean gold's exact per-word pointer compare.  This bit two
designs, so the guard is PROMOTED to a framework invariant: **every** dynamic-index array write is
rendered through `emitGuardedArrayWrite`, which bakes in the explicit `if (idx < size)` range guard
so no template author can forget it.  The invariant is machine-enforced by `cvdp/param_check.py`'s
emitter lint, which fails loudly on any unguarded runtime-indexed array write in the emitted SV. -/

/-- Render a dynamic-index array WRITE with the in-range guard baked in:
    `if (idx < size) arr[idx] <= rhs;`.  Route every template's dynamic (pointer-indexed) array
    write through this so the OOB no-op stays explicit and yosys cannot silently alias a truncated
    write index.  (Loop-variable writes `for (i=0;i<size;…) arr[i] <= …` are already in range and
    need no guard; literal / constant-parameter indices are static.) -/
def emitGuardedArrayWrite (arr idx size rhs : String) : String :=
  s!"if ({idx} < {size}) {arr}[{idx}] <= {rhs};"

end LeanRTL.Designs.Param
