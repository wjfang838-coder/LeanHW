---
id: asyncreset-value-trace
layer: pattern
applies_to: $adff asynchronous-reset registers
principle: commuting-square-and-generic-induction
tactics: [bv-decide-for-fixed-width]
lib: LeanRTL/Core/Semantics.lean (Reg.arstDen, Module.eraseArst), LeanRTL/Core/Coverage.lean (Module.coveredModuloArstb)
example: mirror of asyncload-value-trace (stepAld / regTraceAld)
maturity: provisional
---
# Async-reset value trace

An `$adff` register (`Reg.asyncReset := some (net, activeHi, val)`) is asynchronously forced to the
constant `val` while `net` sits at its active level, else clocks `next`.

**Read this first: declaring an async reset does NOT cost you the whole-design theorem.** That
belief is the single most expensive spec-reading error on this benchmark — it pushes authors into
folding a synchronous reset in-band when the reference RTL is `always @(posedge clk or negedge
rst_n)`, and the testbench then releases reset on a clock edge and the whole trace is one cycle
late (or all X). `Module.step` / `Module.simulate` never read `Reg.asyncReset` at all; the
framework proves this outright:

```lean
theorem Module.eraseArst_simulate (m : Module) (cycles : List (List (String × Nat))) :
    m.eraseArst.simulate cycles = m.simulate cycles
```

`Module.semanticCoverage` still reports `.asyncReset`, and that stays honest — the cycle model has
no edge-to-edge time in which to place a reset that fires between clocks. What it means is
narrower than it reads: only the reset **edge** is out of model. When the async reset is the *only*
out-of-model construct — decidable as `Module.coveredModuloArstb` — `leanrtl check` says so, and
you have two routes, both scoped to the reset-inactive segment.

> **Before you pick either: fold the reset in-band as well.** If every register's `next` is
> `.mux (.eq (.var "<rstPort>" 1) (.const <activeLevel>)) (.const <rstVal>) <normal>` matching the
> declared net/polarity/value, then `Module.arstFoldedb` reads true, `Reg.arstFolded_arstDen`
> proves `arstDen e = eval next e`, and there is **no scoping to route around** — the whole-design
> theorem covers reset-active edges too and you need neither route below. The routes here are for
> the case where the reset genuinely cannot be folded (a reset value that is not a constant of the
> register's own width, say). See CORE.md §2.2.

## Route 1 (default): the ordinary whole-design theorem, unchanged

Declare `asyncReset`, leave `next` free of any reset mux, and state your whole-design theorem about
`impl.simulate` exactly as you would for a reset-free design. It is true as written: on cycles
where the reset net stays inactive, the `$adff` steps as a `$dff` and `impl.simulate` is the trace.
Say so in the theorem's docstring — the scope is a fact about the statement, not a caveat bolted on.

The M6 gate comes from two `by decide` facts about `impl` itself:

```lean
example : CheckWidth.moduleChecksb impl.eraseArst = true :=
  coveredModuloArst_moduleChecks impl (by decide) (by decide)
```

and `Module.eraseArst_simulate` / `Module.eraseArst_step` / `Module.eraseArst_initRegs` /
`Module.eraseArst_outputs?eval` transport anything proved about the twin back onto `impl`.

## Route 2: also cover the reset-active cycles

Route 1 says nothing at all about cycles where the reset is asserted. If your spec's trace includes
them at cycle granularity, use `Reg.arstDen` to get a value-level whole-trace theorem that carries
the reset value too. This is the same Stage-2 route `asyncLoad` already has.

Do not read either route as proving the asynchronous reset's *sub-cycle* behaviour. It is not
proved. Route 2's theorem says: *given* the reset net's per-cycle level, the design's whole trace is
the specified one. The reset firing *between* two edges is pinned structurally instead — by the
`asyncReset` field the emitter reads, plus the polarity/edge check below — and is exercised by cosim.

`stepArst` is a conservative extension of `Module.step`: for an `asyncReset = none` register
`Reg.arstDen` reduces to `eval r.next`, so a mixed design keeps its ordinary law on every other
register. Gotcha: never combine `asyncReset` with `asyncLoad` on one register (the compiler drops
the load — CORE §1.3).

## Worked example (Route 2)

Mirror `stepAld` / `regTraceAld` exactly, substituting `arstDen` for `aldffDen`. These live in
YOUR design file, not in the framework — the framework supplies only `Reg.arstDen`.

```lean
def stepArst (m : Module) (regVals inputs : Env) (rstActive : Bool) : Env :=
  let e := evalWires m.wires (cycleEnv regVals inputs (m.regs.map (·.name)))
  fun n =>
    match m.regs.find? (·.name = n) with
    | some r => if rstActive then r.init.toNat else (r.arstDen e).toNat
    | none   => regVals n

def regTraceArst (m : Module) (inputs : Nat → Env) (rst : Nat → Bool) : Nat → Env
  | 0     => m.initRegs
  | t + 1 => stepArst m (regTraceArst m inputs rst t) (inputs t) (rst t)
```

`stepArst` is `Module.step` with `eval r.next e` replaced by `r.arstDen e` — same environment
(`evalWires ∘ cycleEnv`), same shape, so every lemma you already have about the environment
carries over unchanged.

State the trace theorem on the reset-inactive segment — the hypothesis is what keeps it honest:

```lean
theorem impl_trace_reset_inactive
    (inputs : Nat → Env) (rst : Nat → Bool)
    (hInactive : ∀ t, t < N → rst t = false) :
    ∀ t, t ≤ N → regTraceArst impl inputs rst t = specTrace t := by
  ...
```

## Pin the reset structurally, in the same file

The value trace says nothing about polarity, so assert it separately. This is the claim the emitter
actually consumes, and getting it wrong is what shifts a whole trace by one cycle:

```lean
theorem impl_reset_is_active_low :
    impl.regs.all (fun r => r.asyncReset == some ("rst_n", false, 0)) = true := by rfl
```

Name the **reset port itself** with its polarity. Do not build an inverter wire and declare the
reset active-high over it — see `reset-family-convention`.
