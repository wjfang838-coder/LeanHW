import LeanRTL.Core.Syntax
import LeanRTL.Core.Semantics
import LeanRTL.Core.Refine
import LeanRTL.Core.CompilerCorrectSeq

-- Off deliberately.  With `autoImplicit` on, a misspelled or unimported identifier becomes a
-- silently bound implicit variable rather than an error -- and the theorem using it is then
-- admitted with `sorryAx`, with no `sorry` in the source.  Writing this file reproduced exactly
-- that: two theorems referenced `regTrace`/`specTrace` before their module was imported, built
-- without a visible failure, and were caught only by the `#print axioms` audit at the bottom.
set_option autoImplicit false

/-!
# The whole method on one design

A 4-bit up-counter with synchronous reset and an enable.  Small enough to read in one sitting,
complete enough that nothing is elided: the four sections below are the same four a real design
carries, in the same order, and this file is built by `lake build` like any other, so it cannot
quietly rot.

The design is ours.  This repository contains no benchmark design, no benchmark prose, no
reference implementation and no testbench — only the framework, the harness, and this.

What each section is for:

1. **impl** — the hardware, as an ordinary Lean *data value*.  Not a string, not a template: a
   `Module` you can pattern-match on, and that the verified compiler lowers to RTLIL.
2. **spec** — the intended behaviour, as a pure function on `BitVec`.  Written before the proof
   and never edited to make a proof go through.
3. **L1** — one law per register and per output port: what the hardware computes *is* what the
   spec says, for every state and every input.
4. **whole trace** — the law lifted off a single cycle onto the entire run, for every input
   stream, through `SimRefines`.  This is the difference between "the next-state cone is right"
   and "the counter counts".

The last thing in the file is a `#print axioms` audit.  It is not decoration: a tactic that
*errors* leaves the theorem admitted with `sorryAx` and no `sorry` anywhere in the source, so
reading the source is not enough to know a proof closed.
-/

namespace LeanRTL.Example.Counter

open LeanRTL LeanRTL.Refine LeanRTL.CompilerCorrectSeq

/-! ## 1. impl — the hardware, as a data value -/

/-- Next state of `q`: reset wins over enable, enable wins over hold. -/
def qNext : Expr 4 :=
  .mux (.var "rst" 1) (.const 0) <|
  .mux (.var "en" 1) (.add (.var "q" 4) (.const 1)) (.var "q" 4)

def impl : Module :=
  { name    := "counter4"
    inputs  := [ { name := "clk", width := 1 }
               , { name := "rst", width := 1 }
               , { name := "en",  width := 1 } ]
    outputs := [ { name := "q", width := 4, expr := .var "q" 4 } ]
    regs    := [ { name := "q", width := 4, next := qNext, init := 0 } ]
    clock   := some "clk" }

/-! ## 2. spec — the intended meaning, as a pure function

Note what this is *not*: it is not a second copy of `qNext` in different syntax.  It is written
in terms of `BitVec` arithmetic, so `q + 1` is addition — the wrap at 15 is a consequence of the
type, not something the spec has to say. -/

/-- The abstract state is just the count. -/
abbrev S := BitVec 4

def specStep (q : S) (e : Env) : S :=
  if e.lookup "rst" 1 = 1 then 0
  else if e.lookup "en" 1 = 1 then q + 1
  else q

def s0 : S := 0

/-- Abstraction: read the spec state out of an implementation register environment. -/
def alpha (r : Env) : S := r.lookup "q" 4

/-! ## 3. L1 — the implementation meets the specification

One law, because there is one register and the single output is that register read straight
out.  A design with `n` registers and `m` output ports carries `n + m` of these. -/

theorem qNext_correct (e : Env) :
    eval qNext e = specStep (e.lookup "q" 4) e := by
  simp only [qNext, specStep, eval]

/-! ## 4. whole trace — the law lifted onto the entire run

`SimRefines` has four obligations.  The gluing invariant is `True` here because every 4-bit
value is reachable; a design whose registers have unreachable encodings carries a real one, and
that is where the work goes. -/

theorem impl_simrefines : SimRefines impl alpha specStep s0 (fun _ => True) where
  init_inv := trivial
  -- `decide`, not `native_decide`: the latter emits a per-theorem axiom the kernel TRUSTS
  -- rather than checks, and it showed up in this file's own audit the first time round.
  init_α   := by decide
  step_inv := fun _ _ _ => trivial
  step_α   := by
    intro r inputs _
    -- `impl.step` reduces to: evaluate `qNext` in the cycle environment (registers from `r`,
    -- everything else from `inputs`) and store its `Nat` back under "q".
    show BitVec.ofNat 4 ((eval qNext (cycleEnv r inputs ["q"])).toNat) = specStep (alpha r) inputs
    rw [qNext_correct]
    simp only [BitVec.ofNat_toNat, BitVec.setWidth_eq]
    rfl

/-- The payoff: at **every** cycle `t`, for **every** input stream, the counter's register trace
    read through `alpha` is exactly the spec trace.  Not one cycle — all of them. -/
theorem counter_trace (inputs : Nat → Env) (t : Nat) :
    alpha (regTrace impl inputs (fun _ => false) t) = specTrace specStep s0 inputs t :=
  (impl_simrefines.trace inputs t).2

/-! ## Properties of the specification, provable on their own

These are about the *spec*, not the implementation — and that is the point.  Section 4 has
already tied the implementation to the spec at every cycle, so a property proved here is a
property of the hardware.  This is the direction a proof can travel that a passing testbench
cannot: `counts_when_enabled` is a claim about all 16 states at once. -/

theorem reset_wins (q : S) (e : Env) (h : e.lookup "rst" 1 = 1) : specStep q e = 0 := by
  simp [specStep, h]

theorem counts_when_enabled (q : S) (e : Env)
    (hr : e.lookup "rst" 1 = 0) (he : e.lookup "en" 1 = 1) : specStep q e = q + 1 := by
  simp [specStep, hr, he]

theorem holds_when_idle (q : S) (e : Env)
    (hr : e.lookup "rst" 1 = 0) (he : e.lookup "en" 1 = 0) : specStep q e = q := by
  simp [specStep, hr, he]

/-- The wrap is a theorem, not a comment: 15 + 1 = 0 in `BitVec 4`. -/
theorem wraps_at_15 (e : Env) (hr : e.lookup "rst" 1 = 0) (he : e.lookup "en" 1 = 1) :
    specStep 15 e = 0 := by
  rw [counts_when_enabled _ _ hr he]; decide

end LeanRTL.Example.Counter

/-! ## Axiom audit

`sorry` in the source is easy to grep for.  The failure this catches is the one that is not:
a tactic block that *errors* leaves its theorem admitted, depending on `sorryAx`, with nothing
in the source to show for it.  `#print axioms` is the only thing that sees it.

`propext` and `Quot.sound` are the ambient Lean axioms and are expected.  `sorryAx` means the
proof does not exist.  A `_native.bv_decide.ax_*` would mean a SAT certificate the kernel
trusted rather than checked; `bv_decide` is used nowhere in this file. -/

#print axioms LeanRTL.Example.Counter.qNext_correct
#print axioms LeanRTL.Example.Counter.impl_simrefines
#print axioms LeanRTL.Example.Counter.counter_trace
#print axioms LeanRTL.Example.Counter.counts_when_enabled
#print axioms LeanRTL.Example.Counter.wraps_at_15
