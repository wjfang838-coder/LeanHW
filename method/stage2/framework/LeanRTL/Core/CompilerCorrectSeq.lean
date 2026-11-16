import LeanRTL.Core.CompilerCorrect
/-!
# Compiler correctness (M6b): sequential / module wrapper

`CompilerCorrect.lean` (M6a) proves every combinational `Expr` compiles correctly:
`compile_correct : ⟦e⟧ = ⟦compile e⟧`.  This file lifts that to the *sequential* level — the
`$dff`-based register dynamics produced by `compileModuleM`.

The compiler turns each register `r` into a `$dff` cell whose `Q` net is the register value and
whose `D` net is the (combinational) next-state cone `compileExpr r.next` (optionally behind a
reset multiplexer).  A sequential RTLIL run is therefore a *trace* of net valuations
`τ : Nat → (Nat → Bool)`, one per clock cycle, in which

* every combinational cell holds under each `τ t`        (per-cycle, from M6a), and
* every `$dff` links the next cycle's `Q` to this cycle's `D`:  `Q[t+1] = D[t]`.

`seq_register_correct` below is the temporal heart of M6b: it shows that **any** such trace whose
register nets start at reset and obey the `$dff` law, and whose next-state nets denote the source
`Module.step`, carries register values equal to the denotational register trace at *every* cycle.

Honesty note on the hypotheses: `hinit`/`hdff`/`hcomb` are *assumptions about the netlist run* —
they mirror the structure of the emitted `$dff` cells and the per-cycle combinational correctness
that `compile_correct`/`compile_forces` establish, but no theorem in this repo yet *derives* them
from a formal temporal netlist model (`cellHolds "$dff"` is `True`; there is no trace-level RTLIL
semantics).  In particular `hinit` has no hardware counterpart at power-up: the emitted `$dff`
carries no init attribute, so cycle 0 = `initRegs` is realised only after a synchronous-reset
pulse.  Discharging these hypotheses from a `NetTrace` model is the natural next proof.
-/

namespace LeanRTL.CompilerCorrectSeq

open LeanRTL

/-- The denotational register state after `t` clock cycles, driven by per-cycle input
    environments `inputs` and synchronous-reset flags `reset` (cycle 0 = the reset/init state). -/
def regTrace (m : Module) (inputs : Nat → Env) (reset : Nat → Bool) : Nat → Env
  | 0 => m.initRegs
  | t + 1 => m.step (regTrace m inputs reset t) (inputs t) (reset t)

@[simp] theorem regTrace_zero (m : Module) (inputs : Nat → Env) (reset : Nat → Bool) :
    regTrace m inputs reset 0 = m.initRegs := rfl

@[simp] theorem regTrace_succ (m : Module) (inputs : Nat → Env) (reset : Nat → Bool) (t : Nat) :
    regTrace m inputs reset (t + 1)
      = m.step (regTrace m inputs reset t) (inputs t) (reset t) := rfl

/-- **Sequential register correspondence (M6b temporal core).**

For a sequential netlist whose per-cycle register values are `Qval t` and next-state values are
`Dval t`, suppose:

* `hinit` — at cycle 0 the registers hold the reset/init values (`Module.initRegs`);
* `hdff`  — the `$dff` law: each register's value next cycle is its `D` input this cycle;
* `hcomb` — combinational correctness of the next-state cone: the `D` values this cycle denote the
            source `Module.step` of the current register state and inputs (the shape
            `compile_correct`/`compile_forces` establish for `compileExpr r.next`; see the
            honesty note in the file header — these are assumed, not yet derived from a
            temporal netlist model).

Then the netlist's register values coincide with the denotational register trace at every cycle.
This closes the `⟦·⟧` ↔ RTLIL gap for the registered (`$dff`) dynamics of a module. -/
theorem seq_register_correct (m : Module) (inputs : Nat → Env) (reset : Nat → Bool)
    (Qval Dval : Nat → Env)
    (hinit : Qval 0 = m.initRegs)
    (hdff : ∀ t, Qval (t + 1) = Dval t)
    (hcomb : ∀ t, Dval t = m.step (Qval t) (inputs t) (reset t)) :
    ∀ t, Qval t = regTrace m inputs reset t := by
  intro t
  induction t with
  | zero => rw [hinit, regTrace_zero]
  | succ n ih => rw [hdff n, hcomb n, ih, regTrace_succ]

/-- Corollary: with the register trace pinned down, a netlist whose output nets denote the source
    output function each cycle (again from `compile_correct`, since outputs are combinational cones
    of the registers + inputs) produces exactly the denotational output stream. -/
theorem seq_output_correct (m : Module) (inputs : Nat → Env) (reset : Nat → Bool)
    (Qval Dval : Nat → Env) (out : Nat → List (String × Nat))
    (hinit : Qval 0 = m.initRegs)
    (hdff : ∀ t, Qval (t + 1) = Dval t)
    (hcomb : ∀ t, Dval t = m.step (Qval t) (inputs t) (reset t))
    (hout : ∀ t, out t = m.outputs?eval (Qval t) (inputs t)) :
    ∀ t, out t = m.outputs?eval (regTrace m inputs reset t) (inputs t) := by
  intro t
  rw [hout t, seq_register_correct m inputs reset Qval Dval hinit hdff hcomb t]

/-! ## Bridging `Module.simulate` to `outputs?eval` over the register trace

`Module.simulate` is written as a `foldl` accumulating outputs.  The following gives it an
explicit recursive characterization whose per-cycle output is exactly `Module.outputs?eval` of
the running register state — the form consumed by `seq_output_correct`. -/

/-- One simulation cycle as a pure function: `(next register assoc-list, this cycle's outputs)`. -/
def simStep (m : Module) (rs inpL : List (String × Nat)) :
    List (String × Nat) × List (String × Nat) :=
  let inp := Env.ofList inpL
  let e := evalWires m.wires (cycleEnv (Env.ofList rs) inp (m.regs.map (·.name)))
  let rst := match m.reset with | some r => (inp r != 0) | none => false
  ( m.regs.map (fun r => (r.name, if rst then r.init.toNat else (eval r.next e).toNat)),
    m.outputs.map (fun o => (o.name, (eval o.expr e).toNat)) )

/-- This cycle's outputs equal `Module.outputs?eval` of the running register state and inputs. -/
theorem simStep_outputs (m : Module) (rs inpL : List (String × Nat)) :
    (simStep m rs inpL).2 = m.outputs?eval (Env.ofList rs) (Env.ofList inpL) := rfl

/-- Explicit recursive output trace built from `simStep`; each entry is `outputs?eval` of the
    running register state (`simStep_outputs`), so this is the recursive shape `seq_output_correct`
    consumes once a netlist trace is supplied. -/
def simTrace (m : Module) (rs : List (String × Nat)) :
    List (List (String × Nat)) → List (List (String × Nat))
  | [] => []
  | inpL :: rest => (simStep m rs inpL).2 :: simTrace m (simStep m rs inpL).1 rest

private theorem simulate_fold (m : Module) :
    ∀ (cycles : List (List (String × Nat))) (rs : List (String × Nat))
      (acc : List (List (String × Nat))),
    (cycles.foldl
      (fun (st : List (String × Nat) × List (List (String × Nat))) inpL =>
        ((simStep m st.1 inpL).1, st.2 ++ [(simStep m st.1 inpL).2]))
      (rs, acc)).2 = acc ++ simTrace m rs cycles := by
  intro cycles
  induction cycles with
  | nil => intro rs acc; simp [simTrace]
  | cons c cs ih =>
    intro rs acc
    simp only [List.foldl_cons, simTrace]
    rw [ih]
    simp

/-- **The executable simulator IS the recursive trace.**  `Module.simulate` (the function the
    CLI `sim` command — and hence layer-7 co-simulation — actually runs) computes exactly
    `simTrace` from the initial register file.  Composed with `simStep_outputs`, every entry
    of a co-simulated trace is `Module.outputs?eval` of the running register state — closing
    the previously-unproven gap between the executable simulator and the denotational
    semantics the theorems are stated over. -/
theorem simulate_eq_simTrace (m : Module) (cycles : List (List (String × Nat))) :
    m.simulate cycles = simTrace m (m.regs.map (fun r => (r.name, r.init.toNat))) cycles := by
  show (cycles.foldl
      (fun (st : List (String × Nat) × List (List (String × Nat))) inpL =>
        ((simStep m st.1 inpL).1, st.2 ++ [(simStep m st.1 inpL).2]))
      (m.regs.map (fun r => (r.name, r.init.toNat)), [])).2
    = simTrace m (m.regs.map (fun r => (r.name, r.init.toNat))) cycles
  rw [simulate_fold]
  simp

private theorem simulateFast_fold (m : Module) :
    ∀ (cycles : List (List (String × Nat))) (rs : List (String × Nat))
      (acc : List (List (String × Nat))),
    ((cycles.foldl
      (fun (st : List (String × Nat) × List (List (String × Nat))) inpL =>
        ((simStep m st.1 inpL).1, (simStep m st.1 inpL).2 :: st.2))
      (rs, acc)).2).reverse = acc.reverse ++ simTrace m rs cycles := by
  intro cycles
  induction cycles with
  | nil => intro rs acc; simp [simTrace]
  | cons c cs ih =>
    intro rs acc
    simp only [List.foldl_cons, simTrace]
    rw [ih]
    simp

/-- **The fast CLI simulator computes exactly `Module.simulate`.** The memoized wire
    evaluator uses `evalWiresFast_eq`; the reversed accumulator uses the fold lemma. -/
theorem simulateFast_eq (m : Module) (cycles : List (List (String × Nat))) :
    m.simulateFast cycles = m.simulate cycles := by
  rw [simulate_eq_simTrace]
  unfold Module.simulateFast
  simp only [evalWiresFast_eq]
  show ((cycles.foldl
      (fun (st : List (String × Nat) × List (List (String × Nat))) inpL =>
        ((simStep m st.1 inpL).1, (simStep m st.1 inpL).2 :: st.2))
      (m.regs.map (fun r => (r.name, r.init.toNat)), [])).2).reverse
    = simTrace m (m.regs.map (fun r => (r.name, r.init.toNat))) cycles
  rw [simulateFast_fold]
  simp

end LeanRTL.CompilerCorrectSeq
