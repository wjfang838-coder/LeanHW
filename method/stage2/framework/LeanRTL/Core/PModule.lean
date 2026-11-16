import LeanRTL.Core.Syntax

/-!
# F2 tier 1 — a *symbolic* parametric module

`ParamBackend.lean` recovers a parametric module by **sampling**: it elaborates
`gen : List Nat → Module` at a grid of concrete parameter vectors and fits each width back out of
the numbers.  That works exactly as far as the module's *shape* is constant.  A parameter that is
an **element count** — a filter's tap count, an adder tree's input count, a matrix dimension, the
number of words in a store — moves the shape, `shapeMismatch` refuses, and no amount of better
fitting changes that: the emitter can only see the generator at points, and a point does not carry
a loop.

This file removes the sampling.  An author writes a `PModule`, in which every width is a `NatE`
(an elaboration-time expression over the parameter vector) and an expression may contain a `fold`
over a parametric range or a register may be an array of parametric length.  Two functions consume
it, and the split is the whole design:

* `PModule.elabAt : PModule → List Nat → Option Module` unfolds every fold and every register array
  at a **concrete** vector and produces the ordinary `Module` this framework already has.  The
  compiler, the semantics, `Refines`, and every L1 proof are untouched — they still talk about a
  monomorphic `Module`, because that is still what they get.
* `emitPVerilog : PModule → Except String String` renders `generate`-free but genuinely looped
  SystemVerilog — `reg [W-1:0] a [0:N-1]`, `for (i = 0; i < N; i = i + 1)` — with no fitting
  anywhere, and therefore no structural refusal.

The obligation that ties them together is the author's, and it is one line per anchored vector:
`pmod.elabAt v = some (implGen …)`, which is `rfl` when it holds.  The emitted text is then anchored
the same way the sampled route's is — `f9_emit.py::param_anchor` proves it equivalent to the
machine-checked compiler's own netlist at several parameter vectors.  Nothing here is trusted that
was not already trusted there; what changes is the class of design that reaches the anchor at all.
-/

namespace LeanRTL.Designs.Param

open LeanRTL

/-! ## `NatE` — elaboration-time arithmetic -/

/-- A `Nat`-valued expression over the parameter vector and any enclosing loop indices: exactly
    what a Verilog `parameter` expression may contain.

    `idx k` is a **de Bruijn index into the loop environment**, innermost first: inside a `fold`
    body, `idx 0` is that fold's own counter and `idx 1` the counter of the fold enclosing it. -/
inductive NatE where
  | lit   : Nat → NatE
  /-- The `i`-th declared parameter. -/
  | param : Nat → NatE
  /-- The `k`-th enclosing loop index, innermost first. -/
  | idx   : Nat → NatE
  | add   : NatE → NatE → NatE
  /-- Truncated subtraction, matching `Nat`.  Widths are never negative, and a form that would go
      negative is a design error the anchor catches rather than a value to represent. -/
  | sub   : NatE → NatE → NatE
  | mul   : NatE → NatE → NatE
  | div   : NatE → NatE → NatE
  | pow2  : NatE → NatE
  | clog2 : NatE → NatE
  deriving Repr, Inhabited, BEq

namespace NatE

/-- Ceiling log base 2, matching Verilog's `$clog2`. -/
def clog2Nat (n : Nat) : Nat := if n ≤ 1 then 0 else Nat.log2 (n - 1) + 1

/-- Evaluate at a concrete parameter vector and loop environment (innermost index first). -/
def eval (ps env : List Nat) : NatE → Nat
  | .lit n     => n
  | .param i   => ps.getD i 0
  | .idx k     => env.getD k 0
  | .add a b   => eval ps env a + eval ps env b
  | .sub a b   => eval ps env a - eval ps env b
  | .mul a b   => eval ps env a * eval ps env b
  | .div a b   => eval ps env a / eval ps env b
  | .pow2 a    => 2 ^ eval ps env a
  | .clog2 a   => clog2Nat (eval ps env a)

/-- Render as a SystemVerilog elaboration-time expression.  `names` are the parameter names in
    declaration order; `ivs` the enclosing loop variables, innermost first. -/
def render (names ivs : List String) : NatE → String
  | .lit n     => toString n
  | .param i   => names.getD i s!"__param{i}"
  | .idx k     => ivs.getD k s!"__idx{k}"
  | .add a b   => s!"({render names ivs a} + {render names ivs b})"
  | .sub a b   => s!"({render names ivs a} - {render names ivs b})"
  | .mul a b   => s!"({render names ivs a} * {render names ivs b})"
  | .div a b   => s!"({render names ivs a} / {render names ivs b})"
  | .pow2 a    => s!"(2**({render names ivs a}))"
  | .clog2 a   => s!"($clog2({render names ivs a}))"

/-- Is this literally the constant 1?  A 1-bit net takes no `[hi:lo]` range in Verilog. -/
def isOne : NatE → Bool
  | .lit 1 => true
  | _      => false

/-- Is this a value Verilog can compute at **elaboration** time — i.e. does it mention no enclosing
    loop index?  Parameters are elaboration-time constants; a `for` loop's counter is an `integer`
    and is not, so it may not appear where the language wants a constant expression (a declaration
    range, a part-select width, a size cast). -/
def elabConst : NatE → Bool
  | .lit _     => true
  | .param _   => true
  | .idx _     => false
  | .add a b   => elabConst a && elabConst b
  | .sub a b   => elabConst a && elabConst b
  | .mul a b   => elabConst a && elabConst b
  | .div a b   => elabConst a && elabConst b
  | .pow2 a    => elabConst a
  | .clog2 a   => elabConst a

/-- Does this mention parameter `k` or any parameter declared after it?

    A Verilog parameter's default may only name parameters declared **before** it, so this is the
    predicate a derived default has to fail at its own index. -/
def mentionsParamGE (k : Nat) : NatE → Bool
  | .lit _     => false
  | .param i   => i ≥ k
  | .idx _     => false
  | .add a b   => mentionsParamGE k a || mentionsParamGE k b
  | .sub a b   => mentionsParamGE k a || mentionsParamGE k b
  | .mul a b   => mentionsParamGE k a || mentionsParamGE k b
  | .div a b   => mentionsParamGE k a || mentionsParamGE k b
  | .pow2 a    => mentionsParamGE k a
  | .clog2 a   => mentionsParamGE k a

instance : OfNat NatE n := ⟨.lit n⟩instance : Add NatE := ⟨.add⟩
instance : Sub NatE := ⟨.sub⟩
instance : Mul NatE := ⟨.mul⟩

end NatE

/-- A declaration range for a net of the given width: `[W-1:0] `, or empty for a 1-bit scalar. -/
def rangeOfN (names ivs : List String) (w : NatE) : String :=
  if w.isOne then "" else s!"[{w.render names ivs}-1:0] "

/-! ## `PExpr` — parametric expressions -/

/-- Same-width binary operators, which are also the operators a `fold` may reduce with. -/
inductive PBin where
  | add | sub | mul | and | or | xor | udiv | umod
  deriving Repr, Inhabited, BEq

/-- Comparisons, which produce one bit whatever their operands' width. -/
inductive PCmp where
  | eq | ult | slt
  deriving Repr, Inhabited, BEq

/-- A parametric expression.  Every width is a `NatE`, and `fold` is the node that makes an
    element-count parameter expressible at all. -/
inductive PExpr where
  /-- A literal of the given width and value. -/
  | const  : NatE → NatE → PExpr
  /-- A named net of the given width. -/
  | var    : String → NatE → PExpr
  /-- A **statically** indexed element of a register array: `name[i]`, of the given element width.
      The index is a `NatE`, so it is a parameter/loop expression and not a runtime value; a
      runtime-indexed array is a `MemBlock` and belongs on the memory path. -/
  | sel    : String → NatE → NatE → PExpr
  | not    : PExpr → PExpr
  | bin    : PBin → PExpr → PExpr → PExpr
  | cmp    : PCmp → PExpr → PExpr → PExpr
  /-- `mux c t f`, with `c` one bit. -/
  | mux    : PExpr → PExpr → PExpr → PExpr
  | shl    : PExpr → PExpr → PExpr
  | shr    : PExpr → PExpr → PExpr
  | sshr   : PExpr → PExpr → PExpr
  /-- Zero-extend **by** `k` bits. -/
  | zext   : NatE → PExpr → PExpr
  /-- Sign-extend **by** `k` bits. -/
  | sext   : NatE → PExpr → PExpr
  /-- `e[lo +: len]`. -/
  | slice  : NatE → NatE → PExpr → PExpr
  /-- `{hi, lo}`. -/
  | concat : PExpr → PExpr → PExpr
  /-- `fold op count width seed body` — reduce `body` over `i = 0 .. count-1` with `op`, starting
      from `seed`, at `width` bits.  Inside `body`, `NatE.idx 0` is `i`.  This is the tap count, the
      adder-tree input count, the matrix dimension. -/
  | fold   : PBin → NatE → NatE → PExpr → PExpr → PExpr
  /-- The accumulator of the enclosing `foldA`, at the given width — its `i`-th value when the body
      is being evaluated for element `i`.  Innermost enclosing `foldA` only. -/
  | acc    : NatE → PExpr
  /-- `foldA count width seed body` — the same loop as `fold`, except that `body` computes the
      **new accumulator** outright rather than a value to be combined with a fixed operator, and may
      name the running one as `acc width`.

      `fold` can only reduce with a `PBin`, and a great many real reductions are not one.  A
      combinational maximum — "initialise the peak with the first sample, then for each remaining
      sample, if it is larger the peak becomes it" — is
      `foldA n w (sel …0) (mux (cmp .ult (acc w) elem) elem (acc w))`, and there is no `PBin` that
      expresses it.  Minimum, saturating add, a running index-of-max, a priority encoder and a
      compare-and-swap pass are all the same shape.  `fold op` is kept because it reads better
      where it fits, and is exactly `foldA` with `body = bin op (acc w) elem`. -/
  | foldA  : NatE → NatE → PExpr → PExpr → PExpr
  /-- `ifEq a b t f` — a conditional on two **elaboration-time** naturals, not on a runtime value.

      A shift register's element 0 takes the new sample and every other element takes its
      predecessor: one body, two cases, selected by the element index.  `cmp` cannot express that,
      because the index is not a net.  `elabE` resolves this away entirely — it evaluates `a` and
      `b` and elaborates only the branch that wins — so the ordinary `Module` never contains it,
      and the out-of-range `shft[-1]` the losing branch would name is never built. -/
  | ifEq   : NatE → NatE → PExpr → PExpr → PExpr
  deriving Repr, Inhabited

namespace PExpr

/-- The expression's width, symbolically.  Total and structural: every node either carries its
    width or derives it from a child that carries one. -/
def width : PExpr → NatE
  | .const w _     => w
  | .var _ w       => w
  | .sel _ w _     => w
  | .not a         => width a
  | .bin _ a _     => width a
  | .cmp _ _ _     => .lit 1
  | .mux _ t _     => width t
  | .shl a _       => width a
  | .shr a _       => width a
  | .sshr a _      => width a
  | .zext k a      => .add (width a) k
  | .sext k a      => .add (width a) k
  | .slice _ len _ => len
  | .concat a b    => .add (width a) (width b)
  | .fold _ _ w _ _ => w
  | .acc w         => w
  | .foldA _ w _ _ => w
  | .ifEq _ _ t _  => width t

/-- Does this cone contain a `fold`?  A cone that does cannot be a continuous `assign` — it needs
    a procedural loop — so the emitter renders it as an `always @(*)` block instead. -/
def hasFold : PExpr → Bool
  | .fold _ _ _ _ _ => true
  | .foldA _ _ _ _  => true
  | .not a          => hasFold a
  | .bin _ a b      => hasFold a || hasFold b
  | .cmp _ a b      => hasFold a || hasFold b
  | .mux c t f      => hasFold c || hasFold t || hasFold f
  | .shl a b        => hasFold a || hasFold b
  | .shr a b        => hasFold a || hasFold b
  | .sshr a b       => hasFold a || hasFold b
  | .zext _ a       => hasFold a
  | .sext _ a       => hasFold a
  | .slice _ _ a    => hasFold a
  | .concat a b     => hasFold a || hasFold b
  | .ifEq _ _ t f   => hasFold t || hasFold f
  | _               => false

/-- Every net this cone names, `sel`ected array elements included (by the array's name).

    Used by the emitter to decide which internal wires a register's next-state actually depends on,
    so that a sequential block can recompute exactly those and no more.  Duplicates are left in;
    the one caller dedups against an ordered wire list. -/
def varsPE : PExpr → List String
  | .var n _        => [n]
  | .sel n _ _      => [n]
  | .not a          => varsPE a
  | .bin _ a b      => varsPE a ++ varsPE b
  | .cmp _ a b      => varsPE a ++ varsPE b
  | .mux c t f      => varsPE c ++ varsPE t ++ varsPE f
  | .shl a b        => varsPE a ++ varsPE b
  | .shr a b        => varsPE a ++ varsPE b
  | .sshr a b       => varsPE a ++ varsPE b
  | .zext _ a       => varsPE a
  | .sext _ a       => varsPE a
  | .slice _ _ a    => varsPE a
  | .concat a b     => varsPE a ++ varsPE b
  | .fold _ _ _ s b => varsPE s ++ varsPE b
  | .foldA _ _ s b  => varsPE s ++ varsPE b
  | .ifEq _ _ t f   => varsPE t ++ varsPE f
  | _               => []

/-- Is this an expression `elabReg` will read as a **literal** power-on value?

    `Reg.init` is a `BitVec`, not an `Expr`, so `elabReg` pattern-matches the elaborated init
    against `Expr.const` and falls back to `0` for anything else.  That fallback is silent, and
    silence here is dangerous in a way it is nowhere else: the emitter would render the author's
    expression into the Verilog while the compiler's netlist carried `0`, and the two artifacts
    would differ at power-on only — which no proof mentions and only a from-arbitrary-state
    equivalence miter catches.  So the emitter refuses instead, and this is the predicate it
    refuses by.

    `ifEq` is admitted because it is resolved *at elaboration time*: `elabE` evaluates the two
    `NatE`s and elaborates only the winning branch, so an `ifEq` between two literals elaborates
    to a literal.  It is how an array gives element 0 a different power-on value from the rest. -/
def isConstInit : PExpr → Bool
  | .const _ _      => true
  | .ifEq _ _ t f   => isConstInit t && isConstInit f
  | _               => false

/-- How many times this expression names the accumulator of the `foldA` that **encloses** it.

    `elabE` elaborates a `foldA` by substitution: step `i`'s accumulator expression is dropped into
    every `.acc` of the body.  So a body naming its accumulator `k` times produces a term `k` times
    the size of the previous step's, and after `n` steps the term is `k^n` — which is why this
    count, and not the fold's length, is what decides whether the accumulator gets a name.

    Scoping matters and is the only subtle part.  A nested `.foldA` **rebinds** the accumulator, so
    the `.acc`s in its body belong to it and are not counted here; its *seed* is elaborated in the
    enclosing scope and is.  A nested `.fold op` does **not** rebind — `elabE` passes `av` straight
    through and applies the operator outside the body — so both its parts count.

    `ifEq` takes the maximum rather than the sum: `elabE` resolves it at elaboration time and
    elaborates only the winning branch, so the worst case over the iterations is the worse branch,
    not both. -/
def accUses : PExpr → Nat
  | .acc _          => 1
  | .not a          => accUses a
  | .bin _ a b      => accUses a + accUses b
  | .cmp _ a b      => accUses a + accUses b
  | .mux c t f      => accUses c + accUses t + accUses f
  | .shl a b        => accUses a + accUses b
  | .shr a b        => accUses a + accUses b
  | .sshr a b       => accUses a + accUses b
  | .zext _ a       => accUses a
  | .sext _ a       => accUses a
  | .slice _ _ a    => accUses a
  | .concat a b     => accUses a + accUses b
  | .ifEq _ _ t f   => max (accUses t) (accUses f)
  | .fold _ _ _ s b => accUses s + accUses b
  | .foldA _ _ s _  => accUses s
  | .const _ _      => 0
  | .var _ _        => 0
  | .sel _ _ _      => 0

end PExpr

/-! ## Elaboration to the ordinary `Module`

This is the bridge.  Everything downstream — `compileModuleM`, `Module.step`, `SimRefines`, every
L1 theorem an author writes — consumes a monomorphic `Module`, and continues to.
-/

/-- One expression of some width, existentially packed.  The same shape as `ParamBackend.ESam`,
    and for the same reason: a list of expressions at different widths is otherwise not a list. -/
structure XE where
  w : Nat
  e : Expr w

instance : Inhabited XE := ⟨⟨1, .const (0 : BitVec 1)⟩⟩

/-- Reconcile two packed expressions to a common width, or fail.  Width equality is decidable and
    the cast is by `Eq.mpr`, so an elaborated module still reduces with `rfl`. -/
def unify (a b : XE) : Option (Σ w : Nat, Expr w × Expr w) :=
  if h : a.w = b.w then some ⟨b.w, (h ▸ a.e, b.e)⟩ else none

/-- Apply a same-width binary operator. -/
def applyBin (op : PBin) {w : Nat} (a b : Expr w) : Expr w :=
  match op with
  | .add  => .add a b
  | .sub  => .sub a b
  | .mul  => .mul a b
  | .and  => .and a b
  | .or   => .or a b
  | .xor  => .xor a b
  | .udiv => .udiv a b
  | .umod => .umod a b

/-- Apply a comparison. -/
def applyCmp (op : PCmp) {w : Nat} (a b : Expr w) : Expr 1 :=
  match op with
  | .eq  => .eq a b
  | .ult => .ult a b
  | .slt => .slt a b

/-- The name an array element elaborates to: `arr[3]` becomes the ordinary register `arr_3`.

    This is what keeps the register array out of the compiler entirely.  A `PReg` with
    `count = some N` elaborates to N ordinary `Reg`s, so `Module.regs` stays the flat list every
    existing theorem quantifies over, and only the *emitter* knows they were ever an array. -/
def elemName (nm : String) (i : Nat) : String := s!"{nm}_{i}"

/-- Elaboration threads the combinational wires it had to introduce.

    `Option` is still the failure mode and means exactly what it meant before; the state is the
    only addition.  It is a `List` rather than an `Array` because the author's obligation
    `elabAt v = some impl` is discharged by `rfl`, and a `List` reduces in the kernel without
    going through `Array`'s representation. -/
abbrev ElabM := StateT (List Wire) Option

/-- The prefix every generated accumulator wire carries.  `elabAt` refuses a family that declares
    any name starting with it, so a generated name can never capture an author's. -/
def accWirePrefix : String := "_facc"

/-- Give a value a name, and hand back a reference to that name.

    A leaf is returned unchanged: naming a `.var` or a literal would only add an alias, and the
    point of the exercise is to keep the term small. -/
def bindAcc (w : Nat) (e : Expr w) : ElabM (Expr w) := fun ws =>
  match e with
  | .var _ _ => some (e, ws)
  | .const _ => some (e, ws)
  | _ =>
      let nm := s!"{accWirePrefix}{ws.length}"
      some (.var nm w, ws ++ [⟨nm, w, e⟩])

/-- Would substituting this accumulator into this body `cnt` times produce a term nothing can walk?

    `k` occurrences per step means `k^cnt` nodes, so the answer is a size estimate and not a
    property of the design.  Measured on an LFSR bit-step — which names its accumulator three
    times, once for the bit shifted out, once for the tap and once for the shifted body — the
    elaborated next-state is 281 nodes at `cnt = 4`, 22 961 at 8, 1 860 041 at 12 and about
    1.5 × 10⁸ at the 16 a byte-wide PRBS declares.  The in-memory object is a shared DAG and is
    small, but every consumer that matters walks it as a tree: `f9_emit.py::param_anchor`'s
    comparison against the emitted Verilog, and the verified compiler.  So a serial-over-a-word
    family — LFSR, PRBS, CRC, bit-serial multiplier or divider — was expressible on the symbolic
    route and then not checkable on it, which is the same as not being expressible.

    The threshold, rather than naming the accumulator unconditionally, is deliberate: `k = 1` (the
    plain running reduction) never grows, and the running maximum / saturating add / priority
    encoder idiom that `foldA` was introduced for has `k = 2` over a handful of elements, which is
    a couple of hundred nodes.  Naming the accumulator there would change the elaborated term of
    every family that already works, and every L1 proof stated against it, to buy nothing. -/
def bindsAcc (uses cnt : Nat) : Bool :=
  uses ≥ 2 && (cnt > 32 || uses ^ cnt > 4096)

/-- Elaborate a `PExpr` at a concrete parameter vector and loop environment.

    `none` means the expression is ill-formed at this vector — two operands of a same-width
    operator disagreeing, a mux condition that is not one bit, an `acc` outside any `foldA`.  It is
    `Option` rather than a partial function because the author's proof obligation is an equation
    about this value, and an equation about a `partial def` does not reduce.

    `av` is the enclosing `foldA`'s running accumulator, already elaborated.  It is threaded rather
    than substituted so that each step elaborates the body once: substituting the accumulated
    *expression* back into the body before elaborating would re-walk a tree that grows with every
    step, and the obligation `elabAt v = some impl` has to reduce in the kernel.

    Threading keeps the *elaboration* linear, but not the *term*: `av` is still dropped into every
    `.acc` of the body, so a body that names its accumulator more than once still squares the term
    at each step.  When `bindsAcc` says that is about to matter, the accumulator is given a wire
    name instead and the body sees a leaf — see `bindAcc`. -/
def elabE (ps : List Nat) : List Nat → Option XE → PExpr → ElabM XE
  | _,   _,  .const w v   => pure ⟨w.eval ps [], .const (BitVec.ofNat (w.eval ps []) (v.eval ps []))⟩
  | _,   _,  .var n w     => pure ⟨w.eval ps [], .var n (w.eval ps [])⟩
  | env, _,  .sel n w i   => pure ⟨w.eval ps env, .var (elemName n (i.eval ps env)) (w.eval ps env)⟩
  -- An `acc` whose declared width disagrees with the accumulator it names is a mistake worth
  -- failing on: the two are the same net, and letting the wider one silently win would make the
  -- emitted loop and the elaborated chain compute different things.
  | env, av, .acc w       => do
      let a ← av
      if a.w = w.eval ps env then pure a else failure
  | env, av, .not a       => do let x ← elabE ps env av a; pure ⟨x.w, .not x.e⟩
  | env, av, .bin op a b  => do
      let x ← elabE ps env av a
      let y ← elabE ps env av b
      let ⟨w, p⟩ ← unify x y
      pure ⟨w, applyBin op p.1 p.2⟩
  | env, av, .cmp op a b  => do
      let x ← elabE ps env av a
      let y ← elabE ps env av b
      let ⟨_, p⟩ ← unify x y
      pure ⟨1, applyCmp op p.1 p.2⟩
  | env, av, .mux c t f   => do
      let cx ← elabE ps env av c
      let tx ← elabE ps env av t
      let fx ← elabE ps env av f
      let ⟨w, p⟩ ← unify tx fx
      if h : cx.w = 1 then pure ⟨w, .mux (h ▸ cx.e) p.1 p.2⟩ else failure
  | env, av, .shl a b     => do
      let x ← elabE ps env av a; let y ← elabE ps env av b; pure ⟨x.w, .shl x.e y.e⟩
  | env, av, .shr a b     => do
      let x ← elabE ps env av a; let y ← elabE ps env av b; pure ⟨x.w, .shr x.e y.e⟩
  | env, av, .sshr a b    => do
      let x ← elabE ps env av a; let y ← elabE ps env av b; pure ⟨x.w, .sshr x.e y.e⟩
  | env, av, .zext k a    => do
      let x ← elabE ps env av a; pure ⟨x.w + k.eval ps env, .zext (k.eval ps env) x.e⟩
  | env, av, .sext k a    => do
      let x ← elabE ps env av a; pure ⟨x.w + k.eval ps env, .sext (k.eval ps env) x.e⟩
  | env, av, .slice lo len a => do
      let x ← elabE ps env av a
      pure ⟨len.eval ps env, .slice (lo.eval ps env) (len.eval ps env) x.e⟩
  | env, av, .concat a b  => do
      let x ← elabE ps env av a; let y ← elabE ps env av b; pure ⟨x.w + y.w, .concat x.e y.e⟩
  | env, av, .ifEq a b t f =>
      if a.eval ps env == b.eval ps env then elabE ps env av t else elabE ps env av f
  | env, av, .fold op cnt w seed bd => do
      let ww := w.eval ps env
      let s ← elabE ps env av seed
      if hs : s.w = ww then
        let start : Expr ww := hs ▸ s.e
        let e ← (List.range (cnt.eval ps env)).foldlM
          (fun (acc : Expr ww) (i : Nat) => do
            let b ← elabE ps (i :: env) av bd
            if hb : b.w = ww then pure (applyBin op acc (hb ▸ b.e)) else failure)
          start
        pure ⟨ww, e⟩
      else failure
  -- The seed is elaborated in the ENCLOSING accumulator's scope, not its own: it is what the
  -- accumulator starts as, so it cannot name it.  The body is elaborated with `av` rebound.
  | env, av, .foldA cnt w seed bd => do
      let ww := w.eval ps env
      let n  := cnt.eval ps env
      let s ← elabE ps env av seed
      if hs : s.w = ww then
        let start : Expr ww := hs ▸ s.e
        -- Decided once, outside the loop, from the body and the count: whether every step hands
        -- the body a wire name or the accumulated expression itself.
        let name := bindsAcc bd.accUses n
        let e ← (List.range n).foldlM
          (fun (acc : Expr ww) (i : Nat) => do
            let acc ← if name then bindAcc ww acc else pure acc
            let b ← elabE ps (i :: env) (some ⟨ww, acc⟩) bd
            if hb : b.w = ww then pure (hb ▸ b.e) else failure)
          start
        pure ⟨ww, e⟩
      else failure

/-! ## `PModule` -/

/-- A register, possibly an **array** of parametric length.

    `count = none` is an ordinary scalar register.  `count = some n` is `n` of them: the next-state
    and reset expressions may mention the element index as `NatE.idx 0`, and elaboration produces
    `n` ordinary `Reg`s named by `elemName`. -/
structure PReg where
  name  : String
  width : NatE
  next  : PExpr
  init  : PExpr
  /-- `some n` makes this an array of `n` elements; the body sees the index as `NatE.idx 0`. -/
  count : Option NatE := none
  /-- Asynchronous reset: `some (net, activeHi)` names the net that forces `init` and the level at
      which it is active (`true` ⇒ active-high, `false` ⇒ active-low).  The polarity has to be
      carried here rather than assumed high: an active-low `rst_n` forced through an inverter net
      reaches the always block one delta late and loses the race against a testbench that deasserts
      reset in the same timestep as a clock edge.  See `Reg.asyncReset` in `Core/Syntax.lean`. -/
  asyncReset : Option (String × Bool) := none
  deriving Inhabited

/-- Back-compatibility for the pre-polarity `PReg.asyncReset` spelling.

This field began as `Option String` — a net name alone, with the active level assumed high because
the compiler of that era hardcoded `("ARST_POLARITY", binStr32 1)` and had no way to say otherwise.
Adding the `Bool` above was a widening with no coercion, so every parametric design already written
against the bare-`String` form became a compile error, and one with no diagnostic pointing at the
cause: the author reads `Application type mismatch: "rst_a" ... expected String × Bool` in *their*
file, and nothing says the DSL moved underneath them.  Measured on `workspaces/_cvdp2/
cvOursParam2`: four of the 78 designs used the bare form and broke on the refresh, three of them
having previously passed.

`true` is therefore a transcription of what those designs actually compiled to, not a chosen
default.  Designs of that era expressed an active-low reset the only way the DSL allowed — through
an inverter net (`rst_a = ~rst_n`) — and that idiom keeps working unchanged on top of this
coercion, since it is the *net* that is active-high. -/
instance : CoeTail String (String × Bool) :=
  ⟨fun net => (net, true)⟩

/-- An output port. -/
structure POut where
  name  : String
  width : NatE
  expr  : PExpr
  deriving Inhabited

/-- An internal combinational net. -/
structure PWire where
  name  : String
  width : NatE
  expr  : PExpr
  deriving Inhabited

/-- A design family, written symbolically rather than sampled. -/
structure PModule where
  name    : String
  /-- Verilog parameters in declaration order, with their defaults. -/
  params  : List (String × Nat)
  inputs  : List (String × NatE)
  outputs : List POut
  wires   : List PWire := []
  regs    : List PReg := []
  clock   : Option String := none
  /-- Parameters whose emitted DEFAULT is a formula over the parameters declared before them,
      rather than a literal: `(name, formula)`.

      Verilog allows this — `#(parameter W = 8, parameter ACC = 2*W + $clog2(N))` — and a
      testbench relies on it.  A grader instantiates the module by overriding the parameters the
      spec calls primary and leaves every *derived* one alone, expecting it to follow.  A module
      that declares the derived one independently, at a literal, silently keeps its own default
      while the primary ones move: the design elaborates, simulates, and computes the right
      function at the wrong width.

      Measured on CVDP `matrix_multiplier`, whose spec says of `OUTPUT_DATA_WIDTH` that it
      "should be calculated to handle potential overflow from multiplication".  Its harness
      overrides `ROW_A COL_A ROW_B COL_B INPUT_DATA_WIDTH` and not `OUTPUT_DATA_WIDTH`, so every
      product came back truncated to the emitted default of 18 bits against expectations needing
      34.  Nothing was wrong with the arithmetic; there was no way to say what the width was.

      Empty by default, and every entry is checked at emit against the numeric default it
      accompanies — see `emitPVerilog` — so this cannot become a second, disagreeing source of
      truth for a parameter's value.  `elabAt`, `gen` and `param_anchor` are untouched: they take
      a full concrete vector and never read a default. -/
  derived : List (String × NatE) := []
  deriving Inhabited

namespace PModule

/-- The parameter names, in declaration order. -/
def names (pm : PModule) : List String := pm.params.map (·.1)

/-- The declared default vector. -/
def defaults (pm : PModule) : List Nat := pm.params.map (·.2)

/-- Rewrite an inverter-net asynchronous reset back onto the input port it inverts.

A register whose reset is `some ("nrst", true)`, where the design also declares
`nrst = ~rst_n` over an input port `rst_n`, means an *active-low reset on `rst_n`* and nothing
else.  Emitted literally it becomes `always @(posedge clk or posedge nrst)`, which is correct in
the pure-value sense and wrong in the sense that matters: `nrst` is a continuous assignment, so it
settles one delta cycle after `rst_n` does, and a testbench that deasserts reset in the same
timestep as a clock edge — the ordinary shape of a reset-release check — loses the race.  Naming
the port directly (`negedge rst_n`) has no delta to lose.

This is the same rewrite `ProcVerilog.asyncNet?` performs, and it was previously performed *only*
there.  The two emitters are chosen per design, so the inverter idiom was repaired on one route
and left racy on the other, with nothing in either file recording that the other existed.
Measured: every design in `workspaces/_cvdp2/cvOursParam2` that uses the idiom takes the `pverilog`
route, i.e. exactly the route that did not have the fix — so re-emitting them against the repaired
`ProcVerilog` produced byte-identical output and no change in verdict.

Grouping is by the *resolved* reset, so a design that spells the same reset both ways — one
register through the inverter net, another as `("rst_n", false)` — now lands in a single event
control rather than two contradictory ones. -/
def resolveArst (pm : PModule) : Option (String × Bool) → Option (String × Bool)
  | none            => none
  | some (net, hi)  =>
      match pm.wires.find? (·.name == net) with
      | some w =>
          match w.expr with
          | .not (.var p _) => if pm.inputs.any (·.1 == p) then some (p, !hi) else some (net, hi)
          | _               => some (net, hi)
      | none   => some (net, hi)

/-- Elaborate one `PReg` at a concrete vector into the ordinary `Reg`s it denotes: one, or `n` of
    them when it is an array. -/
def elabReg (ps : List Nat) (r : PReg) : ElabM (List Reg) :=
  match r.count with
  | none =>
      let w := r.width.eval ps []
      do
        let nx ← elabE ps [] none r.next
        let iv ← elabE ps [] none r.init
        if hn : nx.w = w then
          if hi : iv.w = w then
            let initBV : BitVec w := match hi ▸ iv.e with
              | .const c => c
              | _        => 0
            pure [{ name := r.name, width := w, next := hn ▸ nx.e, init := initBV
                  , asyncReset := r.asyncReset.map (fun n => (n.1, n.2, initBV)) }]
          else failure
        else failure
  | some cnt =>
      let n := cnt.eval ps []
      (List.range n).mapM (fun i =>
        let w := r.width.eval ps [i]
        do
          let nx ← elabE ps [i] none r.next
          let iv ← elabE ps [i] none r.init
          if hn : nx.w = w then
            if hi : iv.w = w then
              let initBV : BitVec w := match hi ▸ iv.e with
                | .const c => c
                | _        => 0
              pure { name := elemName r.name i, width := w, next := hn ▸ nx.e, init := initBV
                   , asyncReset := r.asyncReset.map (fun nm => (nm.1, nm.2, initBV)) }
            else failure
          else failure)

/-- Elaborate the whole family at a concrete parameter vector.

    This is the bridge to everything that already exists: the result is an ordinary `Module`, so
    the compiler, the semantics and every L1 proof apply to it unchanged.  The author's obligation
    is `pm.elabAt v = some impl` at each vector the emitted Verilog is anchored at.

    `Module.wires` must be topologically ordered, and the order here is the order of elaboration:
    the author's own wires in the order they were declared, each preceded by whatever accumulator
    wires `bindAcc` had to introduce for it, then the ones the outputs and registers needed.  A
    generated wire only ever names things elaborated before it, so this is the ordering the
    contract asks for and not a coincidence of the traversal. -/
def elabAt (pm : PModule) (ps : List Nat) : Option Module := do
  -- Generated names are `_facc<k>`.  An author name that could collide with one is refused rather
  -- than silently shadowed: shadowing would rewire the design, and it would do it invisibly.
  let declared := pm.inputs.map (·.1) ++ pm.wires.map (·.name) ++ pm.outputs.map (·.name)
                    ++ pm.regs.map (·.name)
  if declared.any (fun n => accWirePrefix.isPrefixOf n) then none else
  let ins := pm.inputs.map (fun p => (⟨p.1, p.2.eval ps []⟩ : InPort))
  let body : ElabM (List OutPort × List Reg) := do
    pm.wires.forM (fun w => do
      let x ← elabE ps [] none w.expr
      let ww := w.width.eval ps []
      if h : x.w = ww then modify (fun ws => ws ++ [(⟨w.name, ww, h ▸ x.e⟩ : Wire)]) else failure)
    let outs ← pm.outputs.mapM (fun o => do
      let x ← elabE ps [] none o.expr
      let ow := o.width.eval ps []
      if h : x.w = ow then pure (⟨o.name, ow, h ▸ x.e⟩ : OutPort) else failure)
    let rgs ← pm.regs.mapM (elabReg ps)
    pure (outs, rgs.flatten)
  let (⟨outs, rgs⟩, ws) ← body.run []
  some { name := pm.name, inputs := ins, outputs := outs, wires := ws
       , regs := rgs, clock := pm.clock
       , params := pm.params }

end PModule

/-- `ParamMeta.gen` derived from a symbolic family, for a design whose shape the parameters move.

    Where the shape is fixed an author writes `gen := implGen` and proves `sym.elabAt v =
    some (implGen v)` by `rfl`; where it is not, `implGen` has nothing to be — the register count
    is not known until the vector is — and the family itself is the definition.  Either way the
    guarantee at the end is the same one, and it is not weaker in the second case: `leanrtl extract
    --N v` runs the **verified compiler** on this `Module`, and `param_anchor` proves the emitted
    parametric text equivalent to that netlist at several vectors.  What that catches is
    `emitPVerilog` and `elabAt` disagreeing — two independent renderings of one `PModule`, which is
    exactly where an emitter bug would live.

    An ill-formed vector degenerates to an empty module rather than throwing, because the caller
    that matters already handles it: `extract --N` runs `checkErrors` and refuses, and
    `param_anchor` skips a vector whose gold cannot be produced (unless it is the declared
    defaults, where it fails). -/
def PModule.genOf (pm : PModule) (v : List Nat) : Module :=
  (pm.elabAt v).getD { name := pm.name, inputs := [], outputs := [], params := pm.params }

/-! ## Emission

The half of the design that never fits anything.  `ParamBackend`'s emitter observes the generator
at points and has to *recover* each width by numerical fitting, which is why a shape that moves is
a refusal and why a width like `DW*$clog2(NT)` is out of reach.  Here every width is already a
`NatE`, so rendering it is a syntactic walk, and an element count renders as the bound of a
`for` loop rather than as a number that has to stay constant.

Nothing below is proved.  It is *anchored*: `f9_emit.py::param_anchor` proves the emitted module
equivalent to the machine-checked compiler's own netlist at several `-chparam` vectors, exactly as
it does for the sampled route.  The obligation `pm.elabAt v = some impl` is what ties those
vectors back to the Lean-side proof.
-/

/-- Does this width mention a loop index?  A module-scope declaration cannot: `reg [W-1:0] a [0:N-1]`
    has one element width for the whole array, and a fold's accumulator is declared outside its own
    loop.  Rendering such a width would produce an out-of-scope identifier, so it is refused. -/
def NatE.mentionsIdx : NatE → Bool
  | .idx _     => true
  | .add a b   => a.mentionsIdx || b.mentionsIdx
  | .sub a b   => a.mentionsIdx || b.mentionsIdx
  | .mul a b   => a.mentionsIdx || b.mentionsIdx
  | .div a b   => a.mentionsIdx || b.mentionsIdx
  | .pow2 a    => a.mentionsIdx
  | .clog2 a   => a.mentionsIdx
  | _          => false

/-- Emission state: a fresh counter, module-scope declarations, `integer` loop variables, and the
    statements of the block currently being built. -/
structure PEmitState where
  fresh : Nat := 0
  /-- Module-scope declarations, most recent first. -/
  decls : List String := []
  /-- `integer` loop variables, most recent first. -/
  ints  : List String := []
  /-- Statements of the block being built, most recent first. -/
  stmts : List String := []
  /-- The identifiers of the accumulators of the enclosing `foldA`s, innermost first.

      Carried in the state rather than as a parameter of `renderPE` for one reason: `renderPE` is
      `mutual`ly recursive with `bindP` across some thirty call sites, and an extra parameter
      threaded through all of them is thirty chances to pass the wrong scope.  The state is already
      threaded correctly by `PM`, and the push/pop is confined to the one case that owns it. -/
  accs  : List String := []
  /-- Net renamings in force for the block being built: `(wire name, what to render instead)`.

      Set only while a sequential block is rendering a register's next-state.  A register whose
      next-state reads an internal wire cannot read the combinational block's copy of it — that is
      the delta-cycle race documented at the register loop in `emitPVerilog` — so the sequential
      block recomputes the wire into a shadow of its own and renders the reference against that.
      Carried in the state for the same reason `accs` is: `renderPE` would otherwise need the map
      threaded through thirty recursive call sites. -/
  wsub  : List (String × String) := []

abbrev PM := StateT PEmitState (Except String)

def freshP (pfx : String) : PM String := do
  let st ← get
  set { st with fresh := st.fresh + 1 }
  return s!"{pfx}{st.fresh}"

def addDeclP (d : String) : PM Unit := modify (fun st => { st with decls := d :: st.decls })
def addIntP (i : String) : PM Unit := modify (fun st => { st with ints := i :: st.ints })
def addStmtP (s : String) : PM Unit := modify (fun st => { st with stmts := s :: st.stmts })

/-- Run an action with a fresh statement buffer and hand back what it emitted, restoring the
    caller's buffer.  This is how a `fold` body's statements end up *inside* its `for` loop rather
    than beside it.  Declarations and the fresh counter deliberately survive: they are module-scope
    and must stay unique across the whole emission. -/
def captureP {α} (act : PM α) : PM (α × List String) := do
  let st0 ← get
  set { st0 with stmts := [] }
  let a ← act
  let st1 ← get
  set { st1 with stmts := st0.stmts }
  return (a, st1.stmts.reverse)

def binOpStr : PBin → String
  | .add => "+" | .sub => "-" | .mul => "*" | .and => "&"
  | .or  => "|" | .xor => "^" | .udiv => "/" | .umod => "%"

/-- Is this rendered text already a plain identifier or an array select — something a bit-select
    or part-select may be applied to directly? -/
def isSelectable (s : String) : Bool :=
  match s.toList with
  | []      => false
  | c :: _  => (c.isAlpha || c == '_') && !(s.any (fun ch => ch == ' ' || ch == '(' ))

mutual

/-- Render a parametric expression, emitting statements for any `fold` inside it, and return the
    Verilog text that denotes its value.

    Sub-expressions are rendered *inline* rather than bound to intermediate nets, and that is
    deliberate: Verilog's context-determined width propagates the width of an assignment's target
    down through `+ - * & | ^ ?:`, so binding only the top of a cone to a correctly-sized net sizes
    the whole cone.  The exception is a bit- or part-select, whose operand must be an identifier;
    `bindP` materialises one when it has to. -/
partial def renderPE (names ivs : List String) : PExpr → PM String
  | .const w v =>
      match w, v with
      -- A sized *literal* is only legal when both halves are literal: `(A+B)'d5` is not Verilog,
      -- because the width before the `'` must be a decimal number.
      | .lit n, .lit c => return s!"{n}'d{c}"
      | _, _           =>
        -- Everything else takes a size **cast**, whose width may be any elaboration-time constant
        -- expression, so `(IN_WIDTH+1)'(1)` is legal where `(IN_WIDTH+1)'d1` is not.
        --
        -- The unsized fallback that used to live here read the width off the assignment's target,
        -- on the reasoning quoted above this function.  That reasoning covers `+ - * & | ^ ?:` and
        -- nothing else, and a bare literal is not merely unsized, it is a 32-bit **signed** integer.
        -- Two places in one design showed what that costs.  `(0) - x` computed the subtraction at
        -- 32 bits signed instead of at the datapath width, because a comparison's operands and a
        -- shift's right-hand side are self-determined -- the target never reaches them.  And
        -- `(1) < x` inverted outright: the standard makes a comparison unsigned as soon as either
        -- operand is unsigned, so a negative left-hand side compares as a large positive one.  The
        -- module was correct in Lean and the compiler's netlist has neither behaviour -- it carries
        -- a width on every node -- so the emitted text disagreed with the design it came from, on a
        -- purely combinational module, at its own declared default parameter vector.
        --
        -- `BitVec.ofNat w v` truncates, and so does the cast, so this is also the faithful reading
        -- of `.const`'s semantics rather than a defensive widening.
        if w.elabConst then
          return s!"(({w.render names ivs})'({v.render names ivs}))"
        else
          -- A width that moves with a loop counter is not a constant expression, so it cannot go
          -- before the `'`.  Such a design cannot declare a net of that width either and will fail
          -- earlier; leave the old rendering rather than emit text that will not parse.
          return s!"({v.render names ivs})"
  | .var n _   => do
      let st ← get
      return (st.wsub.find? (·.1 == n)).elim n (·.2)
  | .sel n _ i => return s!"{n}[{i.render names ivs}]"
  | .not a     => do return s!"(~{← renderPE names ivs a})"
  | .bin op a b => do
      let x ← renderPE names ivs a
      let y ← renderPE names ivs b
      return s!"({x} {binOpStr op} {y})"
  | .cmp op a b => do
      let x ← renderPE names ivs a
      let y ← renderPE names ivs b
      match op with
      | .eq  => return s!"({x} == {y})"
      | .ult => return s!"({x} < {y})"
      | .slt => return s!"($signed({x}) < $signed({y}))"
  | .mux c t f => do
      let cx ← renderPE names ivs c
      let tx ← renderPE names ivs t
      let fx ← renderPE names ivs f
      return s!"({cx} ? {tx} : {fx})"
  | .shl a b  => do return s!"({← renderPE names ivs a} << {← renderPE names ivs b})"
  | .shr a b  => do return s!"({← renderPE names ivs a} >> {← renderPE names ivs b})"
  | .sshr a b => do
      let x ← renderPE names ivs a
      let y ← renderPE names ivs b
      let w := PExpr.width a
      -- `>>>` is arithmetic only if the EXPRESSION IT SITS IN is signed, and everything else this
      -- renderer emits is unsigned -- a net, a concatenation, a size cast of a non-negative value.
      -- So `$signed(x) >>> 1` written inline is arithmetic exactly when nothing encloses it, and
      -- silently degenerates to a logical `>>` the moment it becomes an operand of anything: the
      -- standard makes a mixed-sign expression unsigned and then converts the operands, and a
      -- shift's left operand is context-determined, so it is converted along with the rest.  That
      -- is not a width mistake with a bounded blast radius; it is the wrong shift.  On one design
      -- it turned `(-7) >>> 1 = -4` into `4`, which is the far end of the number line, and the
      -- equivalence miter refuted the module against the compiler that had just proven it.
      --
      -- Giving the shift its own assignment fixes it for good.  An assignment's left-hand side
      -- determines the right-hand side's WIDTH and not its SIGN, so in `t = $signed(x) >>> y;` the
      -- expression is signed all the way to the top, the shift is arithmetic, and `t` -- an
      -- ordinary unsigned net -- carries the resulting bits to the use site.  This also keeps the
      -- invariant the rest of the renderer wants: outside a comparison's own parentheses, no
      -- emitted subexpression is signed, so no enclosing operator has to reason about sign at all.
      if w.mentionsIdx then
        throw s!"an arithmetic shift is taken of a value whose width mentions an enclosing loop \
index; it needs a temporary of that width, which is declared at module scope and cannot have a \
loop-dependent width"
      let t ← freshP "_t"
      addDeclP s!"  reg    {rangeOfN names [] w}{t};"
      addStmtP s!"{t} = $signed({x}) >>> {y};"
      return t
  | .zext k a => do
      let x ← renderPE names ivs a
      return "{ {(" ++ k.render names ivs ++ "){1'b0}}, " ++ x ++ " }"
  | .sext k a => do
      let w := (PExpr.width a)
      let id ← bindP names ivs w a
      return "{ {(" ++ k.render names ivs ++ "){" ++ id ++ "[(" ++ w.render names ivs ++ ")-1]}}, "
             ++ id ++ " }"
  | .slice lo len a => do
      let id ← bindP names ivs (PExpr.width a) a
      -- Indexed part-select.  `[hi:lo]` needs both bounds constant; `[lo +: len]` needs only the
      -- WIDTH constant, which a parametric `len` still is at elaboration time.
      return s!"{id}[{lo.render names ivs} +: {len.render names ivs}]"
  | .concat a b => do
      let x ← renderPE names ivs a
      let y ← renderPE names ivs b
      return "{" ++ x ++ ", " ++ y ++ "}"
  | .ifEq a b t f => do
      -- Verilog has no elaboration-time conditional inside a `for` body — the loop variable is a
      -- runtime `integer` there — so this renders as a ternary whose condition is a constant
      -- expression.  Both arms are written out, and the losing arm may name an out-of-range array
      -- element; `?:` selects before that matters, and `elabE` never builds it at all.
      let x ← renderPE names ivs t
      let y ← renderPE names ivs f
      return s!"(({a.render names ivs}) == ({b.render names ivs}) ? {x} : {y})"
  | .fold op cnt w seed bd => do
      if w.mentionsIdx then
        throw s!"a fold's accumulator width mentions an enclosing loop index; the accumulator is \
declared outside its own loop, so its width must not depend on one"
      let acc ← freshP "_f"
      addDeclP s!"  reg    {rangeOfN names [] w}{acc};"
      let s ← renderPE names ivs seed
      addStmtP s!"{acc} = {s};"
      let iv ← freshP "_i"
      addIntP iv
      let (b, body) ← captureP (renderPE names (iv :: ivs) bd)
      addStmtP s!"for ({iv} = 0; {iv} < {cnt.render names ivs}; {iv} = {iv} + 1) begin"
      for line in body do addStmtP ("  " ++ line)
      addStmtP s!"  {acc} = {acc} {binOpStr op} {b};"
      addStmtP "end"
      return acc
  | .acc w => do
      let st ← get
      match st.accs with
      | []     => throw s!"`acc` names the accumulator of an enclosing `foldA`, and there is no \
enclosing `foldA` here (width {w.render names ivs})"
      | a :: _ => return a
  | .foldA cnt w seed bd => do
      if w.mentionsIdx then
        throw s!"a fold's accumulator width mentions an enclosing loop index; the accumulator is \
declared outside its own loop, so its width must not depend on one"
      let acc ← freshP "_f"
      addDeclP s!"  reg    {rangeOfN names [] w}{acc};"
      -- The seed is rendered BEFORE the accumulator is pushed, matching `elabE`: what the
      -- accumulator starts as cannot name the accumulator.
      let s ← renderPE names ivs seed
      addStmtP s!"{acc} = {s};"
      let iv ← freshP "_i"
      addIntP iv
      let st0 ← get
      set { st0 with accs := acc :: st0.accs }
      let (b, body) ← captureP (renderPE names (iv :: ivs) bd)
      modify (fun st => { st with accs := st0.accs })
      addStmtP s!"for ({iv} = 0; {iv} < {cnt.render names ivs}; {iv} = {iv} + 1) begin"
      for line in body do addStmtP ("  " ++ line)
      -- One blocking assignment per step, so the next step's `acc` reads this one's result — the
      -- same left-to-right order `elabE` folds in.
      addStmtP s!"  {acc} = {b};"
      addStmtP "end"
      return acc

/-- Render `e` and, if the result is not something a select may be applied to, bind it to a fresh
    net of width `w` first. -/
partial def bindP (names ivs : List String) (w : NatE) (e : PExpr) : PM String := do
  let x ← renderPE names ivs e
  if isSelectable x then return x
  if w.mentionsIdx then
    throw s!"a bit- or part-select is taken of a value whose width mentions an enclosing loop \
index; the temporary that would hold it is declared at module scope and cannot have a \
loop-dependent width"
  let t ← freshP "_t"
  addDeclP s!"  reg    {rangeOfN names [] w}{t};"
  addStmtP s!"{t} = {x};"
  return t

end

/-- Emit SystemVerilog for a whole design family.

    Every combinational cone — internal wires, output drivers, and each register's next-state and
    reset value — is computed in one `always @(*)` block, in that order, with blocking assignments.
    Wires are topologically ordered among themselves, so a single ordered pass is enough, and a
    block is what lets a `fold` become an actual `for` loop.  The sequential blocks that follow are
    then trivial: one non-blocking assignment, or one loop of them for a register array. -/
def emitPVerilog (pm : PModule) : Except String String := do
  let names := pm.names
  if pm.params.isEmpty then
    throw "the module declares no parameters; use the ordinary (non-parametric) emit route"
  if !pm.regs.isEmpty && pm.clock.isNone then
    throw "the module has registers but names no clock"
  for r in pm.regs do
    if !r.init.isConstInit then
      throw s!"the power-on value of register `{r.name}` is not a literal.  `elabReg` reads \
`Reg.init` as a `BitVec`, so anything that does not elaborate to a constant becomes 0 there — and \
the emitted Verilog would then carry the author's expression while the compiler's netlist carried \
0, a difference visible only at power-on.  Write `.const`, or an `.ifEq` between constants when \
element 0 of an array needs a different value from the rest."
  let clk := pm.clock.getD "clk"
  -- A derived default is checked here, once, before anything is rendered.  Three ways it can be
  -- wrong, and all three are silent in the emitted text if they are not caught:
  --   * it names a parameter that does not exist, and would render as a bare identifier Verilog
  --     resolves to nothing;
  --   * it names a parameter declared at or after its own position, which the language forbids and
  --     some tools accept anyway, with the value taken from wherever the tool happened to be;
  --   * it disagrees with the numeric default beside it — and THAT one is the dangerous case,
  --     because the numeric default is what `elabAt`, `gen` and every `param_anchor` proof see.
  --     A formula that evaluated to something else would mean the anchored netlist and the shipped
  --     module are different circuits at the module's own declared defaults.
  for (nm, f) in pm.derived do
    match pm.names.idxOf? nm with
    | none => throw s!"`derived` names `{nm}`, which is not a declared parameter"
    | some i =>
      if f.mentionsParamGE i then
        throw s!"the derived default of `{nm}` names a parameter declared at or after it; a \
Verilog parameter's default may only read the parameters before it"
      if !f.elabConst then
        throw s!"the derived default of `{nm}` mentions a loop index"
      let want := (pm.params.getD i ("", 0)).2
      let got := f.eval pm.defaults []
      if got != want then
        throw s!"the derived default of `{nm}` evaluates to {got} at the declared defaults, but \
the declared default is {want}.  The numeric default is what `elabAt`, `gen` and every \
`param_anchor` proof read, so a formula that disagrees would ship a different circuit from the \
one that was proved."

  let act : PM (List String × List String × List String) := do
    -- The single combinational block.
    let (_, comb) ← captureP do
      for w in pm.wires do
        if w.width.mentionsIdx then
          throw s!"the width of wire `{w.name}` mentions a loop index"
        addDeclP s!"  reg    {rangeOfN names [] w.width}{w.name};"
        let x ← renderPE names [] w.expr
        addStmtP s!"{w.name} = {x};"
      for o in pm.outputs do
        let x ← renderPE names [] o.expr
        addStmtP s!"{o.name} = {x};"
      -- Registers contribute only their DECLARATION here.  Their next-state and reset value are
      -- rendered further down, directly inside the sequential block.
      --
      -- They used to be rendered here too, into `<r>_nx` / `<r>_rv` companions that the sequential
      -- block then copied (`r <= r_nx;`).  That is the ordinary two-always-block style and it is
      -- correct RTL, but it puts a combinational stage between a primary input and the flop's D
      -- pin, and that stage costs a delta cycle the flop cannot wait for.
      --
      -- Verilog leaves the order of two active-region events unspecified.  When a testbench drives
      -- an input in the SAME time step as the clock edge -- which is exactly what cocotb does, since
      -- both the clock and the stimulus are written from Python into one ReadWrite region -- the
      -- `always @(*)` that recomputes `<r>_nx` and the `always @(posedge clk)` that samples it are
      -- both queued, and VCS ran them in that order: the flop read `<r>_nx` while it still held the
      -- value computed from the PREVIOUS input.  Every register in the module misses the edge by one
      -- cycle, together, so the design looks like it has one cycle too much latency and nothing
      -- looks locally wrong.
      --
      -- Measured on CVDP `low_pass_filter` (framework 6fff31c3a78d8224, VCS T-2022.06, cocotb
      -- 2.0.1): with the companion, `valid_in` rose at t=20 and `valid_out_q` was still 0 at t=30;
      -- the design scored 0/128 while the direct-Verilog control, which writes `valid_out <=
      -- valid_in` with no combinational stage, scored 128/128 on the same testbench.  Inlining the
      -- next-state expression into the sequential block -- and nothing else -- took it to 128/128.
      --
      -- What this does NOT reach: a next-state that reads a `pm.wires` entry still goes through the
      -- combinational block, because a wire is shared with the output logic and cannot be assigned
      -- from two always blocks.  Registers that read the module's inputs directly, which is the
      -- common case, are now immune.
      for r in pm.regs do
        if r.width.mentionsIdx then
          throw s!"the element width of register `{r.name}` mentions a loop index; every element \
of an array shares one declared width"
        let rng := rangeOfN names [] r.width
        match r.count with
        | none => addDeclP s!"  reg    {rng}{r.name};"
        | some cnt =>
            let n := cnt.render names []
            addDeclP s!"  reg    {rng}{r.name} [0:({n})-1];"

    -- The power-on state.  `elabReg` gives every elaborated `Reg` an `init`, and the compiler's
    -- netlist carries it; but until this block existed, a register with no *asynchronous reset* had
    -- no path in the emitted text that ever wrote it, so it powered up at `x` while the netlist
    -- powered up at `init`.  The two then agreed on every cycle except the zeroth — which no L1
    -- theorem mentions, because L1 quantifies over states rather than naming the initial one, and
    -- which only an equivalence miter starting from an unconstrained state catches.  It did.
    --
    -- Emitted for every register, reset or not: `init` is unconditional in the elaborated module,
    -- and an async-reset register's `initial` value is simply its reset value, so the block is
    -- redundant there rather than wrong.  `isConstInit` was checked above, so nothing here can emit
    -- a statement or a declaration of its own — every leaf is a literal.
    let (_, inits) ← captureP do
      for r in pm.regs do
        match r.count with
        | none =>
            let v ← renderPE names [] r.init
            addStmtP s!"{r.name} = {v};"
        | some cnt =>
            let n := cnt.render names []
            let jv ← freshP "_i"
            addIntP jv
            let v ← renderPE names [jv] r.init
            addStmtP s!"for ({jv} = 0; {jv} < {n}; {jv} = {jv} + 1) {r.name}[{jv}] = {v};"

    -- One sequential block per distinct asynchronous-reset net AND polarity, `none` included.
    -- Grouping by the reset rather than emitting one block per register keeps the text readable
    -- and, more to the point, keeps every register on a given reset in one event control — which is
    -- what a synthesiser reads as a single async-reset group.  Polarity is part of the key: two
    -- registers on the same net at opposite levels are two different event controls.
    let resets : List (Option (String × Bool)) :=
      pm.regs.foldl (fun acc r =>
        let k := pm.resolveArst r.asyncReset
        if acc.contains k then acc else acc ++ [k]) []
    let mut blocks : List String := []
    for rst in resets do
      let grp := pm.regs.filter (fun r => pm.resolveArst r.asyncReset == rst)
      -- An internal wire a register's next-state reads is the one way the delta-cycle race
      -- documented at the register loop above can come back.  The wire is still assigned in the
      -- combinational block -- it has to be, because the output drivers read it too and Verilog
      -- forbids two `always` blocks writing one variable -- so a sequential block that referenced
      -- it directly would sample the value computed from the PREVIOUS input, exactly as the old
      -- `<r>_nx` companion did.  So the block recomputes each wire it needs into a shadow of its
      -- own and renders the register's next-state against that.
      --
      -- Duplicated logic, deliberately: a synthesiser merges the two copies, and a simulator must
      -- not.  Only the wires this group actually reads are copied.
      let mut need : List String :=
        grp.foldl (fun acc r => acc ++ r.next.varsPE) []
      -- `pm.wires` is emitted in dependency order -- the combinational block assigns them with
      -- blocking assignments in this order, so a wire may only read wires declared before it --
      -- which is what makes one reverse pass enough to close the set.
      for w in pm.wires.reverse do
        if need.contains w.name then need := need ++ w.expr.varsPE
      let mut pre : List String := []
      for w in pm.wires do
        if need.contains w.name then
          let sn ← freshP "_sw"
          addDeclP s!"  reg    {rangeOfN names [] w.width}{sn};"
          -- Rendered BEFORE its own name enters the map, and after every earlier wire's has, so a
          -- wire that reads an earlier wire reads that wire's shadow and not the shared copy.
          let (x, body) ← captureP (renderPE names [] w.expr)
          pre := pre ++ body ++ [s!"{sn} = {x};"]
          modify (fun st => { st with wsub := (w.name, sn) :: st.wsub })
      -- `upd` and `rsts` are LINES, not statements: a next-state that needs a `for` loop or a
      -- temporary contributes several, and the caller indents each one.  Building them as
      -- statements and letting one carry embedded newlines would indent only its first line.
      let mut upd : List String := pre
      let mut rsts : List String := []
      for r in grp do
        match r.count with
        | none =>
            -- Blocking assignments to fresh temporaries, then ONE non-blocking assignment to the
            -- register.  Mixing the two in a single block is only a hazard when the blocking target
            -- is read elsewhere; every temporary `renderPE` makes is fresh and local to this
            -- statement, so the read-then-write order inside the block is exactly the intended
            -- dataflow and the flop still updates in the non-blocking region.
            let (x, body) ← captureP (renderPE names [] r.next)
            upd := upd ++ body ++ [s!"{r.name} <= {x};"]
            if rst.isSome then
              -- No wire shadows on the reset path: `isConstInit` is checked at the top of this
              -- function, so a reset value is a literal and can name no net at all.
              let (v, vbody) ← captureP (renderPE names [] r.init)
              rsts := rsts ++ vbody ++ [s!"{r.name} <= {v};"]
        | some cnt =>
            let n := cnt.render names []
            let kv ← freshP "_i"
            addIntP kv
            let (x, body) ← captureP (renderPE names [kv] r.next)
            upd := upd
              ++ [s!"for ({kv} = 0; {kv} < {n}; {kv} = {kv} + 1) begin"]
              ++ body.map (fun s => "  " ++ s)
              ++ [s!"  {r.name}[{kv}] <= {x};", "end"]
            if rst.isSome then
              let jv ← freshP "_i"
              addIntP jv
              let (v, vbody) ← captureP (renderPE names [jv] r.init)
              rsts := rsts
                ++ [s!"for ({jv} = 0; {jv} < {n}; {jv} = {jv} + 1) begin"]
                ++ vbody.map (fun s => "  " ++ s)
                ++ [s!"  {r.name}[{jv}] <= {v};", "end"]
      -- The shadow map is scoped to this block: the next group's registers get their own shadows,
      -- and the combinational block, which is already built, was rendered with an empty map.
      modify (fun st => { st with wsub := [] })
      match rst with
      | none =>
          blocks := blocks ++
            [ s!"  always @(posedge {clk}) begin\n"
              ++ String.intercalate "\n" (upd.map (fun s => "    " ++ s)) ++ "\n  end" ]
      | some (rn, activeHi) =>
          -- The declared polarity picks both the sensitivity edge and the branch test, so an
          -- active-low reset names the port directly instead of an inverter net.
          let edge := if activeHi then "posedge" else "negedge"
          let test := if activeHi then rn else s!"!{rn}"
          blocks := blocks ++
            [ s!"  always @(posedge {clk} or {edge} {rn}) begin\n    if ({test}) begin\n"
              ++ String.intercalate "\n" (rsts.map (fun s => "      " ++ s)) ++ s!"\n    end else begin\n"
              ++ String.intercalate "\n" (upd.map (fun s => "      " ++ s)) ++ "\n    end\n  end" ]
    return (comb, inits, blocks)

  match act.run {} with
  | .error e => throw e
  | .ok ((comb, inits, seqBlocks), st) =>
    -- A parameter with a `derived` entry emits its FORMULA; every other one emits its literal.
    -- The two agree at the declared defaults — checked above — so this changes nothing about the
    -- module a plain instantiation gets, and everything about the module an instantiation that
    -- overrides only the primary parameters gets.
    let hdr := String.intercalate ", " (pm.params.map (fun p =>
      match pm.derived.find? (·.1 == p.1) with
      | some (_, f) => s!"parameter {p.1} = {f.render names []}"
      | none        => s!"parameter {p.1} = {p.2}"))
    let ports :=
      pm.inputs.map (fun p => s!"  input  {rangeOfN names [] p.2}{p.1}")
      ++ pm.outputs.map (fun o => s!"  output reg {rangeOfN names [] o.width}{o.name}")
    let portList := String.intercalate ",\n" ports
    let ints := if st.ints.isEmpty then []
                else [String.intercalate "\n" (st.ints.reverse.map (fun i => s!"  integer {i};"))]
    let combBlock :=
      if comb.isEmpty then []
      else [ "  always @(*) begin\n"
             ++ String.intercalate "\n" (comb.map (fun s => "    " ++ s)) ++ "\n  end" ]
    let initBlock :=
      if inits.isEmpty then []
      else [ "  initial begin\n"
             ++ String.intercalate "\n" (inits.map (fun s => "    " ++ s)) ++ "\n  end" ]
    return String.intercalate "\n"
      ([ s!"module {pm.name} #({hdr}) (", portList, ");" ]
        ++ st.decls.reverse ++ ints ++ initBlock ++ combBlock ++ seqBlocks ++ ["endmodule", ""])

/-! ## Self-check: the author's obligation must be `rfl`

The whole proof story of this file rests on one property that is easy to lose by accident: at a
concrete parameter vector, `elabAt` must **reduce**.  An author writes their implementation out by
hand and discharges `pm.elabAt v = some impl` with `rfl`; if a future edit makes `elabE` or
`elabAt` opaque to the kernel — a `partial def`, a well-founded recursion, an `Option` bind that
does not unfold — that obligation stops closing, and it stops closing in *every* design at once
rather than here.

So it is checked here, on a family that is deliberately generic: two parameters, the second of
which moves the shape (a `count`), a `.fold` over it, and an `.ifEq` on the element index.  Those
are exactly the three nodes that exist only on this route.  The theorem below is the obligation an
author states, in the form they state it. -/

namespace SelfCheck

/-- A shift register of `.param 1` elements, `.param 0` bits wide, summed to the output. -/
private def famP : PModule :=
  { name    := "selfcheck_chain"
  , params  := [("W", 4), ("N", 3)]
  , inputs  := [("clk", 1), ("d", .param 0)]
  , outputs :=
      [ { name := "sum", width := .param 0
        , expr := .fold .add (.param 1) (.param 0) (.const (.param 0) 0)
                    (.sel "s" (.param 0) (.idx 0)) } ]
  , regs :=
      [ { name := "s", width := .param 0, count := some (.param 1)
        , init := .const (.param 0) 0
        , next := .ifEq (.idx 0) 0 (.var "d" (.param 0))
                        (.sel "s" (.param 0) (.sub (.idx 0) 1)) } ]
  , clock   := some "clk" }

/-- The same module written out by hand, as an author would write `impl`. -/
private def famImpl : Module :=
  { name    := "selfcheck_chain"
  , inputs  := [⟨"clk", 1⟩, ⟨"d", 4⟩]
  , outputs := [⟨"sum", 4,
      .add (.add (.add (.const (0 : BitVec 4)) (.var "s_0" 4)) (.var "s_1" 4)) (.var "s_2" 4)⟩]
  , regs    :=
      [ { name := "s_0", width := 4, next := .var "d" 4,   init := 0 }
      , { name := "s_1", width := 4, next := .var "s_0" 4, init := 0 }
      , { name := "s_2", width := 4, next := .var "s_1" 4, init := 0 } ]
  , clock   := some "clk"
  , params  := [("W", 4), ("N", 3)] }

/-- The obligation.  `rfl` here is the property every author on this route depends on. -/
theorem famP_elab : famP.elabAt [4, 3] = some famImpl := by rfl

/-- `genOf` is the same module, so an author who writes `gen := famP.genOf` and proves about
`famP.genOf [4, 3]` is proving about what the compiler compiles. -/
theorem famP_genOf : famP.genOf [4, 3] = famImpl := by rfl

/-- The count really moves the shape — which is the case the fitted route cannot reach. -/
theorem famP_shape_moves :
    ((famP.elabAt [4, 3]).map (fun m => m.regs.length),
     (famP.elabAt [4, 6]).map (fun m => m.regs.length)) = (some 3, some 6) := by rfl

/-! Emission does not refuse this shape.  An `#eval` rather than a theorem, and deliberately: the
renderer is a `partial def` over `StateT … Except`, so it does not reduce in the kernel and no
`rfl`/`decide` can see it — the honest alternatives were `native_decide`, which would put
`ofReduceBool` into the framework's trust base for a *convenience* check, or nothing.  A throwing
`#eval` fails the build the same way, and costs no axiom. -/
#eval show IO Unit from do
  match emitPVerilog famP with
  | .ok _     => pure ()
  | .error e  => throw (IO.userError s!"emitPVerilog refused the self-check family: {e}")

/-! ### The same, for a reduction no `PBin` expresses

A combinational maximum over a parametric number of elements.  This is checked separately from
`famP` because it exercises the one thing `fold` cannot do — the accumulator appearing inside its
own body — and because the failure mode it guards against is silent: an `acc` bound to the wrong
scope still emits, still elaborates, and computes something else. -/

/-- The maximum of `.param 1` registers, each `.param 0` bits wide. -/
private def maxP : PModule :=
  { name    := "selfcheck_max"
  , params  := [("W", 4), ("N", 3)]
  , inputs  := [("clk", 1), ("d", .param 0)]
  , outputs :=
      [ { name := "peak", width := .param 0
        , expr := .foldA (.sub (.param 1) 1) (.param 0) (.sel "s" (.param 0) 0)
            -- element i+1, since the seed already consumed element 0
            (.mux (.cmp .ult (.acc (.param 0)) (.sel "s" (.param 0) (.add (.idx 0) 1)))
                  (.sel "s" (.param 0) (.add (.idx 0) 1))
                  (.acc (.param 0))) } ]
  , regs :=
      [ { name := "s", width := .param 0, count := some (.param 1)
        , init := .const (.param 0) 0
        , next := .ifEq (.idx 0) 0 (.var "d" (.param 0))
                        (.sel "s" (.param 0) (.sub (.idx 0) 1)) } ]
  , clock   := some "clk" }

/-- Written out by hand: `max(max(s_0, s_1), s_2)` as a chain of muxes, left-nested, which is
exactly the order `foldA` folds in. -/
private def maxImpl : Module :=
  { name    := "selfcheck_max"
  , inputs  := [⟨"clk", 1⟩, ⟨"d", 4⟩]
  , outputs := [⟨"peak", 4,
      .mux (.ult (.mux (.ult (.var "s_0" 4) (.var "s_1" 4)) (.var "s_1" 4) (.var "s_0" 4))
                 (.var "s_2" 4))
           (.var "s_2" 4)
           (.mux (.ult (.var "s_0" 4) (.var "s_1" 4)) (.var "s_1" 4) (.var "s_0" 4))⟩]
  , regs    :=
      [ { name := "s_0", width := 4, next := .var "d" 4,   init := 0 }
      , { name := "s_1", width := 4, next := .var "s_0" 4, init := 0 }
      , { name := "s_2", width := 4, next := .var "s_1" 4, init := 0 } ]
  , clock   := some "clk"
  , params  := [("W", 4), ("N", 3)] }

/-- The accumulator really is threaded: if `acc` resolved to the seed each time instead of to the
running value, this would be `max(s_0, s_2)` and would not be this term. -/
theorem maxP_elab : maxP.elabAt [4, 3] = some maxImpl := by rfl

/-- And the count still moves the shape, so the chain lengthens with the parameter. -/
theorem maxP_count :
    (maxP.elabAt [4, 5]).map (fun m => m.regs.length) = some 5 := by rfl

/-! An `acc` with no enclosing `foldA` is not silently zero: it fails to elaborate. -/
theorem acc_needs_a_fold :
    elabE [4] [] none (.acc 4) = none := by rfl

#eval show IO Unit from do
  match emitPVerilog maxP with
  | .ok _     => pure ()
  | .error e  => throw (IO.userError s!"emitPVerilog refused the max self-check family: {e}")

/-! ### The power-on value must be a literal, and the emitter must say so

`elabReg` reads `Reg.init` as a `BitVec`, matching the elaborated init against `Expr.const` and
falling back to `0`.  An emitter that rendered the author's expression regardless would put one
power-on value in the Verilog and another in the compiler's netlist — a difference no L1 theorem
mentions, because L1 quantifies over states rather than naming the zeroth, and which surfaces only
in an equivalence miter that starts from an unconstrained state.  Checked here as an
expected-refusal rather than an expected-emit, for the same `partial def` reason as above. -/

private def badInitP : PModule :=
  { name    := "selfcheck_badinit"
  , params  := [("W", 4)]
  , inputs  := [("clk", 1), ("d", .param 0)]
  , outputs := [ { name := "q", width := .param 0, expr := .var "r" (.param 0) } ]
  , regs    := [ { name := "r", width := .param 0
                 , init := .var "d" (.param 0), next := .var "d" (.param 0) } ]
  , clock   := some "clk" }

#eval show IO Unit from do
  match emitPVerilog badInitP with
  | .error _ => pure ()
  | .ok _    => throw (IO.userError
      "emitPVerilog accepted a register whose power-on value is not a literal; the emitted \
Verilog and the compiler's netlist would then disagree at power-on")

/-! ### A derived parameter default must be rendered, and must agree with its number

A grader overrides the parameters a spec calls primary and leaves the ones it says are *calculated*
to follow.  Emitting the calculated one as a numeric literal makes it stay put while the others
move, and the design comes back truncated against expectations that widened — which looks like an
arithmetic bug in the design and is a header bug.  So the formula has to reach the header.

Two things are checked, an emit and a refusal, because the field is only safe if both hold.  The
formula must RENDER (`$clog2` and `**` are Verilog spellings, not Lean ones), and it must EVALUATE
at the declared defaults to the number already in `params` — that number is what `elabAt`, `gen`
and every `param_anchor` proof read, so a formula that disagreed with it would ship a different
circuit from the one that was proved, silently and only at the default instance. -/

private def derivedP : PModule :=
  { name    := "selfcheck_derived"
  , params  := [("N", 8), ("IN_W", 8), ("ACC_W", 19)]
    -- 2*IN_W + $clog2(N) = 16 + 3 = 19, which is the declared default of `ACC_W`.
  , derived := [("ACC_W", .add (.mul 2 (.param 1)) (.clog2 (.param 0)))]
  , inputs  := [("clk", 1), ("d", .param 1)]
  , outputs := [ { name := "acc", width := .param 2, expr := .var "r" (.param 2) } ]
  , regs    := [ { name := "r", width := .param 2
                 , init := .const (.param 2) 0
                 , next := .zext (.sub (.param 2) (.param 1)) (.var "d" (.param 1)) } ]
  , clock   := some "clk" }

#eval show IO Unit from do
  match emitPVerilog derivedP with
  | .error e => throw (IO.userError s!"emitPVerilog refused the derived-parameter self-check \
family: {e}")
  | .ok v    =>
      let want := "parameter ACC_W = ((2 * IN_W) + ($clog2(N)))"
      let hdr := (v.splitOn "\n").getD 0 ""
      if (v.splitOn want).length < 2 then
        throw (IO.userError s!"emitPVerilog did not render the derived default of `ACC_W` into \
the header; a grader that overrides IN_W and N would get the emitted literal instead.  Header \
was:\n{hdr}")

#eval show IO Unit from do
  -- The same family with the formula changed to `2*IN_W` (= 16), which no longer equals the
  -- declared default of 19.  This must refuse rather than ship a header the proofs do not match.
  match emitPVerilog { derivedP with derived := [("ACC_W", .mul 2 (.param 1))] } with
  | .error _ => pure ()
  | .ok _    => throw (IO.userError
      "emitPVerilog accepted a derived default that disagrees with the numeric default beside \
it; the emitted module and every proof about it would then be about different widths")

/-! ### `foldA` and the accumulator wire

    Three properties, and the first is the one that guards the others: a fold that does not need
    a wire must not get one, because that would rewrite the elaborated term of every family that
    already works and every L1 theorem stated against it. -/

/-- An LFSR bit-step: shift right, feedback at the MSB.  Names its accumulator three times, which
    is what a PRBS, a CRC and a bit-serial multiplier all do and what makes substitution `3^n`. -/
private def lfsrStep (L : NatE) : PExpr :=
  .slice 1 L (.concat (.bin .xor (.slice 0 1 (.acc L)) (.slice 3 1 (.acc L))) (.acc L))

/-- The same family at whatever fold count is asked for. -/
private def lfsrP (n : Nat) : PModule :=
  { name    := "selfcheck_lfsr"
  , params  := [("L", 8), ("W", n)]
  , inputs  := [("clk", 1)]
  , outputs := [ { name := "o", width := .param 0, expr := .var "r" (.param 0) } ]
  , regs    := [ { name := "r", width := .param 0
                 , init := .const (.param 0) 1
                 , next := .foldA (.param 1) (.param 0) (.var "r" (.param 0)) (lfsrStep (.param 0)) } ]
  , clock   := some "clk" }

#eval show IO Unit from do
  -- `.acc` is counted with the scoping `elabE` actually uses.
  if (lfsrStep (.param 0)).accUses ≠ 3 then
    throw (IO.userError s!"accUses miscounted an LFSR bit-step: got \
{(lfsrStep (.param 0)).accUses}, want 3")
  -- The threshold.  A plain running reduction never grows; the running-max idiom over a handful
  -- of elements grows to a couple of hundred nodes and is left alone.
  if bindsAcc 1 1000 then throw (IO.userError "bindsAcc named a single-use accumulator")
  if bindsAcc 2 8    then throw (IO.userError "bindsAcc named a 2-use accumulator over 8 steps, \
which is 256 nodes -- every family already using the running-max idiom would be rewritten")
  if !bindsAcc 3 16  then throw (IO.userError "bindsAcc left a 3-use accumulator unnamed over 16 \
steps, which substitutes to about 1.5e8 nodes")

#eval show IO Unit from do
  -- Below the threshold: byte-for-byte the elaboration this file had before accumulator wires.
  match (lfsrP 6).elabAt [8, 6] with
  | none   => throw (IO.userError "elabAt refused the LFSR self-check family at 6 steps")
  | some m =>
      if m.wires ≠ [] then throw (IO.userError s!"elabAt introduced {m.wires.length} wire(s) for a \
6-step fold that substitutes to 729 nodes; every family that already elaborates without wires \
would change shape")
  -- Above it: one wire per step but the last, and the term stops growing.
  match (lfsrP 16).elabAt [8, 16] with
  | none   => throw (IO.userError "elabAt refused the LFSR self-check family at 16 steps")
  | some m =>
      if m.wires.length ≠ 15 then
        throw (IO.userError s!"a 16-step 3-use fold elaborated to {m.wires.length} wire(s), want 15")
      if !m.wires.all (fun w => accWirePrefix.isPrefixOf w.name) then
        throw (IO.userError "an accumulator wire was emitted without the reserved prefix, so an \
author's name could collide with it")

#eval show IO Unit from do
  -- A family that could be captured by a generated name is refused, not silently rewired.
  let clash : PModule :=
    { lfsrP 16 with wires := [ { name := accWirePrefix ++ "0", width := .param 0
                               , expr := .const (.param 0) 0 } ] }
  match clash.elabAt [8, 16] with
  | none   => pure ()
  | some _ => throw (IO.userError s!"elabAt accepted a family declaring a wire named \
`{accWirePrefix}0`; a generated accumulator wire would have captured it")

end SelfCheck

end LeanRTL.Designs.Param
