import LeanRTL.Core.Refine
/-!
# `Lib/Semantic/Streams` — reusable boundary-input-stream idioms

Whole-trace headlines for *load-then-run* datapaths (dividers, multi-cycle multipliers, the
factorial engine, …) drive the real `regTrace` with a **single-shot latch**: one command pulse on
cycle 0 (`start` / `reset` / `opn_valid` high with the operands applied), then a steady idle
environment held forever after.  Four L5 designs hand-rolled the identical

    fun t => if t = 0 then loadEnv else runEnv

input stream.  This file extracts that idiom once as `loadThenRun`.

The steady phase `run` is a genuine parameter, **defaulting to the all-zero environment** (the
overwhelmingly common "everything idle-low" case).  Designs that must *hold* a control signal in
the run phase — e.g. an active-low `rst` deasserted (`= 1`) throughout the loop — pass their own
`run` environment.  Both shapes appear in the corpus and both are supported by the single def.
-/

namespace LeanRTL.Lib.Semantic.Streams
open LeanRTL

/-- **Load-then-run input stream.**  A command pulse `load` on cycle 0, then the steady `run`
    environment forever after (`run` defaults to the all-zero, everything-idle environment).
    This is the single-shot-latch drive shared by the load/iterate/finalize datapaths. -/
def loadThenRun (load : Env) (run : Env := fun _ => 0) : Nat → Env :=
  fun t => if t = 0 then load else run

@[simp] theorem loadThenRun_zero (load run : Env) : loadThenRun load run 0 = load := rfl

@[simp] theorem loadThenRun_succ (load run : Env) (t : Nat) :
    loadThenRun load run (t + 1) = run := rfl

end LeanRTL.Lib.Semantic.Streams
