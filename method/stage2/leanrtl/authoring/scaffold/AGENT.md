# Workspace manual — two-author proof-carrying design

This workspace produces a **proof-carrying design** in LeanRTL: a formal specification of one
design's intended behaviour, a hardware implementation, machine-checked Lean proofs that the
implementation meets the specification, and an emitted Verilog artifact.

**Two authors write it, in order.** `ROLE_S.md` writes the specification; it is then frozen.
`ROLE_D.md` writes the implementation, and then the proof. You are one of them, and your role
card says which — read it first. It defines what you may read, what you may write, and the JSON
block you end with. **This file is the framework manual and settles none of that**; where the
two appear to disagree, your role card wins.

You are assigned ONE design, identified by `<key>`. Everything you need is in this workspace;
you have never seen this framework before, and that is expected — read the manual and the Core
sources, then build.

## What you have

- `specs/<key>.spec.txt` — the natural-language prose for YOUR design (the only prose you read).
- `contracts/<key>.json` — the interface, derived from that prose mechanically: module name,
  every port with direction and width, the clock, the reset and its polarity. It is **fixed**.
  The two fragments are compared through those names and nothing else.
- `frags/<key>/` — the three fragments, one file each:
  - `spec.lean` — S's, the specification. Frozen once committed: read-only on disk and on the
    confinement hook's read-only list: you read it, you cannot write it.
  - `impl.lean` — D's, the implementation.
  - `proof.lean` — D's, the proofs.
- `docs/dsl-reference.md` — the LeanRTL language manual.
- `LeanRTL/Core/*.lean` — the framework source (syntax, semantics, compiler, refinement
  vocabulary). Reading Core is allowed and encouraged.
- `scripts/bbf.py` — your ONLY build/verify entry point.
- `notes/<key>.<role>.md` — your notes file (see below), and `scratch/<key>.<role>/` — yours.

`LeanRTL/Blind/<Camel>.lean` is **generated**: `bbf.py` concatenates the three fragments into it
before every full build. Do not edit it and do not treat it as a file you own; the next command
overwrites it. In the proof phase you may read it — that is the file Lean actually elaborates,
so a line number in an error message points into it.

## Hard rules

1. **All building and verification goes through `python3 scripts/bbf.py <key> <cmd> --role <R>`**
   — `build` / `check` / `sim` / `cosim` / `simdiff` / `emit` / `audit` / `commit`. Never run
   `lake`, `lean`, `leanrtl` or `yosys` directly on the design.
   `build --frag <name>` type-checks one fragment on its own, against a private assembly, so a
   broken edit does not disturb the last good full build. Everything else assembles in full.
2. **File ownership is your role card's**, and it is enforced, not requested: an attempt to write
   a file that is not yours fails with exit 2 and is recorded. Nothing is quietly adjusted around
   it.
3. **Do not read** other designs' fragments, others' notes, other `specs/*`, anything under
   `log/` or `out/` that is not `<key>`'s, or **any path outside this workspace**. No network.
   Violations void the run.
4. Keep the section markers `/-! ## 3. L1 -/` and `/-! ## 4. whole-trace -/` in `proof.lean`.
   The assembler adds `## 1. impl` and `## 2. spec` around the other two fragments itself. The
   markers are load-bearing downstream: the mutation check attributes a surviving mutant to a
   section by them, and a file whose markers are missing or out of order is reported as
   unmeasurable rather than as passing.
5. **Zero `sorry` / `admit` / new axioms.** A proof that does not close is not a weaker
   deliverable, it is a different artifact, and the gates treat it as one.
6. The Verilog module name and every port name and width must match `contracts/<key>.json`
   exactly. The grading testbench instantiates by name and you will never see it. `emit` checks
   this for you.
   **If the prose declares the same pin under two spellings** — a signal table saying one thing,
   a module skeleton a few lines later saying another — do not pick one. Declare **both** and
   drive them identically: the testbench binds by name, so a duplicate output is inert while the
   spelling you dropped is one nothing can attach to. `emit` refuses this case, because it is the
   one interface mismatch you can always satisfy without guessing.
7. **Prefix your helper definitions** — `spec…` if you are S, `impl…` if you are D. The three
   fragments share one namespace in the assembled file, and a collision surfaces as an error in
   somebody else's fragment.

## Proof obligations

- **L1 (mandatory)**: for every register, a theorem that the implementation's next-state
  expression denotes the specification's next-state function, for ALL states and inputs;
  likewise for every output law. A purely combinational design is DONE at L1 — that is its full
  behaviour.
- **Then climb (default)**: for sequential designs, once L1 is green, state and prove whole-trace
  correctness over time (`SimRefines` / `Refines` in `LeanRTL/Core/Refine.lean`, `regTrace` in
  `LeanRTL/Core/CompilerCorrectSeq.lean`). There are no pre-built lift lemmas here; hand-write
  the induction. If you get genuinely stuck, you may stop — record where and why in your notes.

## If the contract gives the module Verilog `parameter`s

Read this **before** you write the impl if `contracts/<key>.json` lists a parameter — a data
width, a stage count, a divider constant. It changes how you model the design, not just how you
emit it.

The default emit route elaborates ONE module and renders it. If you model a parameterised design
as a fixed `impl : Module` at the default value, the emitted Verilog will declare
`parameter WIDTH = 8;` and then never read it: the body is hard-wired to 8. It elaborates, it
passes `check`, and the equivalence miter certifies it — none of those look at any width but the
default. A grader's testbench that instantiates your module at another width then gets the same
8-bit circuit and fails every vector. `emit` prints a WARNING when it detects this, but by then
the design is already built the wrong way.

Instead, write the impl as a **generator** over the parameters and register it as a `ParamMeta`:

```lean
/-- The design at an arbitrary parameter vector. -/
def implGen (width nStages : Nat) : Module :=
  { name := "<module name from the contract>"
  , inputs  := [⟨"clk", 1⟩, ⟨"rst", 1⟩, ⟨"din", width⟩]
  , outputs := [⟨"dout", width + 1, .var "acc" (width + 1)⟩]
  , regs    := [{ name := "cnt", width := clog2 nStages, … }, …]
  , clock   := some "clk" }

/-- Register the family.  `params` is the Verilog header's parameter list, in DECLARATION
    order, each with the default the contract states. -/
def paramMeta : ParamMeta :=
  { key    := "<key>"
  , params := [("WIDTH", 8), ("N_STAGES", 4)]
  , gen    := fun v => implGen v[0]! v[1]! }

/-- Keep `impl` so the L1 theorems still name one concrete module.  This is definitionally
    the instance the harness registers, so nothing is being asserted twice. -/
def impl : Module := implGen 8 4
```

What that buys you: `emit` takes the **parametric** route and emits a module whose widths are
real expressions in the parameters (`[WIDTH-1:0]`, `[WIDTH+1-1:0]`, `[$clog2(N_STAGES)-1:0]`),
so a testbench's override actually selects a different circuit.

Things to know:

- `ParamMeta` and `clog2` are already in scope; you do not add an import. The route is detected
  by the literal text `def paramMeta : ParamMeta`, so write that type annotation unqualified and
  exactly like that.
- `check` sweeps a grid of parameter vectors and reports which ones your `gen` builds a
  well-formed module at; `sim`, `cosim` and `extract` still run at the **default** vector unless
  you say otherwise, and so do your proofs. Prove L1 about `impl` exactly as you would for a
  non-parametric design. Proving a theorem universally quantified over the parameters is welcome
  but is not required.
- **Exercise your design off-default, and do it before you emit.** Add `--N <v1,v2,…>` — values
  in the order `params` declares them — to `check`, `sim` or `cosim`:

  ```
  python3 scripts/bbf.py <key> check --role D --N 2,2    is `gen` even well-formed there?
  python3 scripts/bbf.py <key> sim   --role D --N 2,2    the same stdin cycles, that instance
  python3 scripts/bbf.py <key> cosim --role D --N 2,2    Lean vs iverilog, that instance
  ```

  This is not optional care, it is the failure mode that costs the most designs. A grading
  testbench picks its own widths and depths. A generator that is correct at the defaults and
  wrong anywhere else is green on every command in this workspace and red on every one of theirs
  — and the default vector is the one instance that cannot show you. Pick vectors that stress the
  shape: the smallest legal one, one that is not a power of two, one where two parameters that
  are equal by default differ.
- The emitter does not trust itself. It builds your `gen` at a grid of parameter vectors, fits
  each width and constant, and then **re-checks the fitted formula at vectors it did not fit
  on**. If a formula does not reproduce, it refuses and tells you which one — it will not ship a
  width it has not verified.
- The emitted module is then proved equivalent to the machine-checked compiler's own netlist at
  **several** parameter vectors — the defaults, and one off-default value of each parameter in
  turn — not just at the defaults. A module that cannot be anchored at two or more vectors does
  not ship on this route; it falls back like a refusal.
- It refuses, by design, when a parameter changes the module's **structure** rather than its
  widths: a parameter that changes how many registers `gen` produces (a memory depth, an array
  length) is out of scope for the *fitted* route. It also refuses widths it cannot express, which
  is anything beyond sums and products of the parameters, plus `$clog2` of a parameter — so
  `WIDTH*WIDTH`, `2^WIDTH - 1`, and `WIDTH/2` are all refusals. **If it refuses on structure,
  read the next section: there is a second route that handles exactly that case.**
- A refusal is not a failed emit. `emit` prints the reason and falls back to the ordinary route,
  producing the same fixed-width module you would have got anyway. You still get `out/<key>.v`;
  you just do not get parametricity. Record the reason in your notes.
- Read `emit`'s route line to confirm which route you got.

If the contract has no `parameter`, ignore all of this and write a plain `def impl : Module`.

## When a parameter is a COUNT, not a width

A tap count, a number of stages to sum, a matrix dimension, the number of entries in a queue: a
parameter like that changes how many registers and how many adders the design has, not how wide
they are. `gen` is then a *different shape* at every value, and the emitter above — which learns
the module by building `gen` at a few points and fitting the numbers — cannot express it. A point
does not carry a loop.

For that case write the family **symbolically**, as a `PModule`, and hang it off the same
`paramMeta`:

```lean
/-- The family itself.  Every width is a `NatE`: an expression over the parameter vector, where
    `.param 0` is the first declared parameter, `.param 1` the second, and so on. -/
def famP : PModule :=
  { name   := "<module name from the contract>"
  , params := [("DATA_WIDTH", 8), ("N_STAGES", 4)]
  , inputs := [("clk", 1), ("rst", 1), ("din", .param 0)]
  , outputs :=
      [ { name := "sum", width := .add (.param 0) (.clog2 (.param 1))
          -- fold <op> <count> <width> <seed> <body>: reduce `body` over i = 0 .. count-1.
          -- Inside `body`, `.idx 0` is i.
        , expr := .fold .add (.param 1) (.add (.param 0) (.clog2 (.param 1)))
                    (.const (.add (.param 0) (.clog2 (.param 1))) 0)
                    (.zext (.clog2 (.param 1)) (.sel "stage" (.param 0) (.idx 0))) } ]
  , regs :=
      -- `count := some n` makes this an ARRAY of n registers.  The body sees the element index
      -- as `.idx 0`; `.ifEq a b t f` picks a branch by that index at elaboration time, which is
      -- how element 0 takes the new sample and the rest take their predecessor.
      [ { name := "stage", width := .param 0, count := some (.param 1)
        , asyncReset := some "rst", init := .const (.param 0) 0
        , next := .ifEq (.idx 0) 0 (.var "din" (.param 0))
                        (.sel "stage" (.param 0) (.sub (.idx 0) 1)) } ]
  , clock := some "clk" }

def paramMeta : ParamMeta :=
  { key    := "<key>"
  , params := famP.params      -- one source of truth for the header
  , gen    := famP.genOf       -- the family at a concrete vector, as an ordinary `Module`
  , sym    := some famP }      -- ← this field is what selects the symbolic route

/-- Your L1 theorems still name one concrete module, exactly as before. -/
def impl : Module := famP.genOf [8, 4]
```

Things to know:

- **`sym` is checked first and unconditionally.** If you set it, nothing is fitted and nothing is
  refused for shape. `.fold` becomes a real `for` loop and `count := some n` becomes a real
  `reg [W-1:0] name [0:n-1]`.
- `PModule`, `NatE` and `PExpr` are already in scope alongside `ParamMeta`; no import.
- **When the reduction has no operator, use `.foldA`.** `.fold` reduces with one of
  `+ - * & | ^ / %`, and a combinational maximum, minimum, saturating add, running index-of-max
  or priority encoder is none of them. `.foldA count width seed body` hands the body the running
  accumulator, which it names as `.acc width`, and the body computes the next one:

  ```lean
  -- the largest of `.param 1` elements of the array `s`
  .foldA (.sub (.param 1) 1) (.param 0) (.sel "s" (.param 0) 0)          -- seed: element 0
    (.mux (.cmp .ult (.acc (.param 0)) (.sel "s" (.param 0) (.add (.idx 0) 1)))
          (.sel "s" (.param 0) (.add (.idx 0) 1))
          (.acc (.param 0)))
  ```

- **A register's `init` must be a literal** — a `.const`, or an `.ifEq` between constants when
  element 0 of an array powers up differently from the rest. `Reg.init` is a `BitVec`, so
  anything else would put one value in the emitted Verilog and another in the compiler's
  netlist; the emitter refuses instead. Every register gets its `init` in an `initial` block
  whether or not it has an `asyncReset`, so a reset-less design does not power up at `x`.
- **The certificate is the same one.** `gen` is still what `leanrtl extract --N` runs the
  verified compiler on, and the emitted text is still proved equivalent to that netlist at
  several parameter vectors. Writing the loops down does not buy you a weaker check; it buys you
  a module the check can be run on at all.
- **`impl` and the family stay tied.** `famP.genOf [8, 4]` *is* the module `extract` compiles, so
  your proofs are about the thing that ships. If you prefer to write the default instance out by
  hand, do — and then state `theorem : famP.elabAt [8, 4] = some impl := by rfl`, which holds
  when the two agree and fails loudly when they do not.
- **What it still refuses**, and these are narrow: a width that depends on a loop index (every
  element of an array shares one declared width), and a parameter that adds or removes a *port*.
  A parameter that changes how many read/write ports a memory has is likewise out.
- Prefer the fitted route (no `sym`) when the parameters really are only widths. It emits more
  readable Verilog and needs no `NatE` at all. Reach for `sym` when you see a structure refusal.

## Workflow

Read the prose. Read the contract. Read this manual. Skim Core as needed. Then, by phase:

**S — specification.** Write `frags/<key>/spec.lean`: the typed functions over `BitVec`, and the
three untyped sim adapters `specInit` / `specStep` / `specOuts` the harness drives. After every
edit `bbf.py <key> build --frag spec --role S`. When it is right,
`bbf.py <key> commit --role S` — and that is the freeze. There is no editing afterwards, so do
not commit to stop thinking.

**D — implementation.** Write `frags/<key>/impl.lean` against the prose and the frozen
specification. If the contract declares Verilog `parameter`s, decide the `paramMeta` question
above **now**: it decides the shape of the implementation, and retrofitting it after the proofs
are green means rewriting them. After every edit `bbf.py <key> build --role D`. Then self-test:
`bbf.py <key> sim --role D` (input cycles on stdin, one line of `name=value` pairs per cycle)
and `bbf.py <key> cosim --role D`. You may write your own testbench under `scratch/<key>.D/` and
run `iverilog`/`vvp` there against `out/<key>.v` after an emit. You will NEVER see the grading
testbench or any reference solution; your reading of the prose is all you have.
The phase ends at `bbf.py <key> simdiff --role D`, which runs the specification's adapters and
your implementation against the same 160 cycles of deterministic pseudo-random stimulus and
requires them to agree.

**D — proof.** Write `frags/<key>/proof.lean`: L1, then climb. When a proof will not go through
you may re-encode `frags/<key>/impl.lean` — and then you must re-run `simdiff --role D` and it
must stay green. You may not edit the specification; if you believe it is wrong, challenge it,
by the route your role card describes. Finish with `bbf.py <key> emit --role D`, which must
succeed and produces `out/<key>.v`. Read its `route=` line and any WARNING under it — a warning
there is a statement about the artifact that gets graded, not about your proofs.

## Notes — `notes/<key>.<role>.md` (write AS YOU GO, not at the end)

Append the moment something happens: a failed proof round, a confusing error, a missing lemma,
a sentence of prose you had to read twice. Every entry needs a concrete anchor — error text,
theorem name, line, or the quoted sentence.

```markdown
# <key> — <role> notes
## 1. Reading      (what the prose left open, what you first mis-read, the reading you took)
## 2. Error → fix  (one entry per failed round: error head / root cause
##                  impl_bug | spec_misread | proof_technique / what fixed it)
## 3. Wish-list    (theorems/combinators/tactics/docs you reached for that don't exist)
## 4. Encoding     (choices you would redo)
## 5. Proving      (reusable patterns found; tactic limits hit)
## 6. Framework    (misleading error messages + what they should say; CLI/DSL/doc gaps)
## Retro: what you'd do differently; rough time split, as fractions
```

Record only — never modify the framework, the manual, or anything outside your own files.

## Final self-report

End your final message with exactly one fenced JSON block, **in the shape your role card
gives** — S's and D's differ, and D's differs between its two phases. Write the same object
verbatim to the notes path the prompt names as well: a report cannot count what only exists in a
chat reply.

Be honest in it. `corrections` must list every time a failed proof forced you to change
something, classified by what was actually wrong — the circuit, your reading of the prose, or
just proof technique — and it is cross-checked against the build log. `assumptions` and
`scope_claimed` are the places where you say what your artifact does *not* cover; an overstated
claim there is the one failure this whole workspace has no mechanism to catch.
