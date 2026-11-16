import LeanRTL.Core.HierCorrect
/-!
# Sequential-hierarchy correctness (F10, "sequential hierarchy across multiple modules")

`HierCorrect.lean` proves that a `Parent` whose instances are **combinational** leaves flattens into a
flat combinational `Module` with equal behaviour (`flattenParent_correct`), inheriting the proven flat
compiler correctness.  This file extends the flattening to **sequential** children — the F10 feature.

The compiler needs **no** change for the sequential shape (verified end-to-end by co-simulation):
`compileParent` already lowers each child through the M6-proven `compileModule` (registers, clock,
reset all handled), and `compileInst` wires each child port — including a clock/reset threaded through
`ins` — to the parent net, so `yosys write_verilog` emits a real *sequential* module instantiation.
So a sequential child is, at the netlist level, exactly the child's own proven `compileModule` output
wired in — nothing new is trusted there.

What *is* new is the semantic flattening.  The heart is a **rename-and-substitute lemma over `eval`**
(`eval_substRename`) that generalises `HierCorrect.eval_substIns` in two ways needed for sequential
children:

* it substitutes a child **input port** by the parent-side instance expression (as before); **and**
* it **renames** every other referenced name `n` (a child register or internal wire) to the
  parent-visible `"<inst>.<n>"`, so a child register reference resolves to the flattened parent
  register — which is exactly how `Parent.simulateSeq` keys the hierarchical register state.

Unlike `eval_substIns`, `eval_substRename` needs **no** well-formedness hypothesis (the rename branch
handles every name), which makes it a clean, total substitution principle.  From it we characterise,
per instance, that the flattened next-state / output expressions compute exactly the child's
`Module.step` / `Module.outputs?eval` — the per-child characterization (à la F6 `Reg.aldffDen`, F8
`Latch.den`) that the task accepts.

*Honest boundary.*  As with the combinational flattening (Yosys `hierarchy -flatten` relates the
instance netlist to the flat one) and the F1/F6/F8 sub-cycle characterizations, the **whole**
multi-instance / multi-cycle hierarchical run and the netlist instance-wiring are pinned by
per-instance characterization here plus **co-simulation** of the emitted hierarchy (see
`Examples/SeqHierTest`), not by a single whole-design cycle theorem.  Each child individually carries
its full M6 compiler-correctness through `compileModule`.  Nothing here touches a proven core file —
it is purely additive.
-/

namespace LeanRTL

set_option linter.unusedVariables false

/-! ## Rename-and-substitute -/

/-- The parent-visible renaming for instance `inst`: a child-internal name `n` (register or wire)
    becomes `"<inst>.<n>"`. -/
def Inst.rename (inst : Inst) : String → String := fun n => inst.instName ++ "." ++ n

/-- Substitute a child input port (bound in `ins`) by its parent-side instance expression — coerced
    to the port width by a `0`-offset slice, exactly as `HierCorrect.substIns` — and **rename** every
    other referenced name via `ren`.  Total: no name is left dangling. -/
def substRename (ins : List (String × AnyExpr)) (ren : String → String) :
    {w : Nat} → Expr w → Expr w
  | _, .const v      => .const v
  | _, .var n w      => match ins.lookup n with
                        | some ae => Expr.slice 0 w ae.2
                        | none    => .var (ren n) w
  | _, .not a        => .not (substRename ins ren a)
  | _, .and a b      => .and (substRename ins ren a) (substRename ins ren b)
  | _, .or a b       => .or (substRename ins ren a) (substRename ins ren b)
  | _, .xor a b      => .xor (substRename ins ren a) (substRename ins ren b)
  | _, .add a b      => .add (substRename ins ren a) (substRename ins ren b)
  | _, .sub a b      => .sub (substRename ins ren a) (substRename ins ren b)
  | _, .mul a b      => .mul (substRename ins ren a) (substRename ins ren b)
  | _, .shl a b      => .shl (substRename ins ren a) (substRename ins ren b)
  | _, .shr a b      => .shr (substRename ins ren a) (substRename ins ren b)
  | _, .sshr a b     => .sshr (substRename ins ren a) (substRename ins ren b)
  | _, .udiv a b     => .udiv (substRename ins ren a) (substRename ins ren b)
  | _, .umod a b     => .umod (substRename ins ren a) (substRename ins ren b)
  | _, .eq a b       => .eq (substRename ins ren a) (substRename ins ren b)
  | _, .ult a b      => .ult (substRename ins ren a) (substRename ins ren b)
  | _, .slt a b      => .slt (substRename ins ren a) (substRename ins ren b)
  | _, .mux s a b    => .mux (substRename ins ren s) (substRename ins ren a) (substRename ins ren b)
  | _, .concat a b   => .concat (substRename ins ren a) (substRename ins ren b)
  | _, .zext k a     => .zext k (substRename ins ren a)
  | _, .sext k a     => .sext k (substRename ins ren a)
  | _, .extract i a  => .extract i (substRename ins ren a)
  | _, .slice lo len a => .slice lo len (substRename ins ren a)

/-- The child environment `substRename` induces, evaluated in a parent env `E`: a bound input port
    resolves to the value of its instance expression in `E`; every other name `n` resolves to the
    *renamed* parent net `E (ren n)` (i.e. the flattened register/wire). -/
def childEnvSeq (ins : List (String × AnyExpr)) (ren : String → String) (E : Env) : Env :=
  fun n => match ins.lookup n with
           | some ae => (eval ae.2 E).toNat
           | none    => E (ren n)

/-- **Rename-and-substitute lemma (the heart of F10 flattening).**  Evaluating a `substRename`d child
    expression in the parent env `E` equals evaluating the original in the induced child env — for
    *every* expression, with **no** well-formedness hypothesis. -/
theorem eval_substRename (ins : List (String × AnyExpr)) (ren : String → String) (E : Env) :
    {w : Nat} → (e : Expr w) → eval (substRename ins ren e) E = eval e (childEnvSeq ins ren E)
  | _, .const v => rfl
  | _, .var n w => by
      cases h : ins.lookup n with
      | some ae =>
          have hL : eval (substRename ins ren (Expr.var n w)) E
              = BitVec.ofNat w (eval ae.2 E).toNat := by
            simp only [substRename, h]; exact eval_slice0 w ae.2 E
          rw [hL]
          simp only [eval, Env.lookup, childEnvSeq, h]
      | none =>
          simp only [substRename, h, eval, Env.lookup, childEnvSeq]
  | _, .not a => by simp only [substRename, eval]; rw [eval_substRename ins ren E a]
  | _, .zext k a => by simp only [substRename, eval]; rw [eval_substRename ins ren E a]
  | _, .sext k a => by simp only [substRename, eval]; rw [eval_substRename ins ren E a]
  | _, .extract i a => by simp only [substRename, eval]; rw [eval_substRename ins ren E a]
  | _, .slice lo len a => by simp only [substRename, eval]; rw [eval_substRename ins ren E a]
  | _, .mux s a b => by
      simp only [substRename, eval]
      rw [eval_substRename ins ren E s, eval_substRename ins ren E a, eval_substRename ins ren E b]
  | _, .and a b | _, .or a b | _, .xor a b | _, .add a b | _, .sub a b | _, .mul a b
  | _, .shl a b | _, .shr a b | _, .sshr a b | _, .udiv a b | _, .umod a b | _, .eq a b
  | _, .ult a b | _, .slt a b | _, .concat a b => by
      simp only [substRename, eval]
      rw [eval_substRename ins ren E a, eval_substRename ins ren E b]

/-! ## The child's cycle environment, and the modelling agreement

`Module.outputs?eval` and `Module.step` evaluate the child's expressions in
`cycleEnv regVals inputs regNames` (register values overlaid by the current inputs), extended by the
child's internal wires.  For a **wire-free** child that is `cycleEnv (inst.regVals flat) (inst.childIn pe)
regNames`.  The next lemma shows that, on every name a child expression can reference (a bound input
port, or a register — disjoint sets in a well-formed child), this cycle environment *agrees* with
`childEnvSeq inst.ins inst.rename E`, provided the parent env `E` carries the flattened register
values `E (inst.rename r) = (inst.regVals flat) r`. -/

/-- The child's per-cycle environment (register values overlaid by inputs), read against a single
    parent env `E`: registers come from the flattened parent nets (`inst.regVals E n = E (inst.rename
    n)`), inputs from the instance-mapped expressions evaluated in `E`.  For a wire-free child this is
    exactly the env `Module.outputs?eval`/`Module.step` evaluate against. -/
def Inst.childCycleEnv (inst : Inst) (E : Env) : Env :=
  cycleEnv (inst.regVals E) (inst.childIn E) (inst.child.regs.map (·.name))

/-- `Inst.childIn E` is exactly `Env.ofList (HierCorrect.insVals inst.ins E)`, so it looks up a bound
    port to its instance-expression value and every other name to `0`. -/
theorem childIn_ofList (inst : Inst) (E : Env) (n : String) :
    inst.childIn E n =
      match inst.ins.lookup n with
      | some ae => (eval ae.2 E).toNat
      | none    => 0 :=
  ofList_insVals inst.ins E n

/-- **Modelling agreement.**  On every name a wire-free child's expression can reference — a bound
    input port or a register name — the flattening's induced child env `childEnvSeq inst.ins
    inst.rename E` equals the child's own cycle env `inst.childCycleEnv E`.  `hdisj` states that no
    register name is also a bound input port (a well-formedness fact `Module.checkErrors`'s
    `dupErrors` enforces); it is all that's needed once both envs are read against the one parent env
    `E` that carries the flattened register values. -/
theorem childEnvSeq_agrees (inst : Inst) (E : Env)
    (hdisj : ∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none) :
    ∀ n, (n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name)) →
      childEnvSeq inst.ins inst.rename E n = inst.childCycleEnv E n := by
  intro n hn
  rcases hn with hport | hreg
  · -- n is a bound input port: `ins.lookup n = some _`, and n is not a register name (disjointness).
    have hsome : (inst.ins.lookup n).isSome := by
      rw [List.lookup_isSome_iff]
      obtain ⟨p, hp, hpn⟩ := List.mem_map.mp hport
      exact ⟨p, hp, by simp [hpn]⟩
    obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp hsome
    have hnotreg : (inst.child.regs.map (·.name)).contains n = false := by
      rcases Bool.eq_false_or_eq_true ((inst.child.regs.map (·.name)).contains n) with hc | hc
      · obtain ⟨r, hr, hrn⟩ := List.mem_map.mp (List.mem_of_elem_eq_true hc)
        rw [← hrn] at hae; rw [hdisj r hr] at hae; simp at hae
      · exact hc
    simp only [childEnvSeq, hae, Inst.childCycleEnv, cycleEnv, hnotreg, childIn_ofList,
               Bool.false_eq_true, if_false]
  · -- n is a register name: `ins.lookup n = none` (disjointness), so both envs give `E (rename n)`.
    obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hreg
    subst hrn
    have hnone := hdisj r hr
    have hisreg : (inst.child.regs.map (·.name)).contains r.name = true :=
      List.elem_eq_true_of_mem (List.mem_map.mpr ⟨r, hr, rfl⟩)
    simp only [childEnvSeq, hnone, Inst.childCycleEnv, cycleEnv, hisreg, if_true, Inst.regVals,
               Inst.rename]

/-! ## Per-instance next-state / output characterization

Combining `eval_substRename` (transport substitution into the parent env) with `childEnvSeq_agrees`
(the induced env equals the child's cycle env on referenced names) and `eval_congr` (from
`HierCorrect`) gives the per-instance characterization: the flattened next-state / output expression
evaluates, in the parent env `E`, to exactly the value the child's `Module.step` / `Module.outputs?eval`
computes.  This is the F10 analogue of the F6/F8 per-instance characterizations. -/

/-- **Per-instance output characterization.**  For a wire-free child, the flattened output expression
    `substRename inst.ins inst.rename o.expr` — evaluated in the parent env `E` (which carries the
    flattened register values as the nets `"<inst>.<reg>"`) — equals `eval o.expr` over the child's
    cycle env, i.e. the child output value the hierarchical simulator samples via
    `Module.outputs?eval`. -/
theorem inst_output_correct (inst : Inst) (E : Env)
    (o : OutPort) (ho : o ∈ inst.child.outputs)
    (hbound : ∀ n ∈ o.expr.vars, n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name))
    (hdisj : ∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none) :
    eval (substRename inst.ins inst.rename o.expr) E = eval o.expr (inst.childCycleEnv E) := by
  rw [eval_substRename inst.ins inst.rename E o.expr]
  exact eval_congr o.expr _ _ (fun n hn => childEnvSeq_agrees inst E hdisj n (hbound n hn))

/-- **Per-instance next-state characterization.**  For a wire-free child, the flattened register
    next-state `substRename inst.ins inst.rename r.next` — evaluated in the parent env `E` — equals
    `eval r.next` over the child's cycle env, i.e. the (pre-reset) next value the child's
    `Module.step` clocks into that register. -/
theorem inst_next_correct (inst : Inst) (E : Env)
    (r : Reg) (hr : r ∈ inst.child.regs)
    (hbound : ∀ n ∈ r.next.vars, n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name))
    (hdisj : ∀ r' ∈ inst.child.regs, inst.ins.lookup r'.name = none) :
    eval (substRename inst.ins inst.rename r.next) E = eval r.next (inst.childCycleEnv E) := by
  rw [eval_substRename inst.ins inst.rename E r.next]
  exact eval_congr r.next _ _ (fun n hn => childEnvSeq_agrees inst E hdisj n (hbound n hn))

/-! ### Tying the child cycle env to the semantics functions

For a wire-free child, `inst.childCycleEnv E` is *exactly* the environment `Module.outputs?eval` and
`Module.step` evaluate expressions against (`evalWires [] e = e`).  The two lemmas below make that a
theorem rather than a definitional remark, so the per-instance characterizations above visibly pin
the flattened value to the value the child's own semantics produces. -/

/-- A wire-free child's `outputs?eval` is just its outputs evaluated in the cycle env. -/
theorem outputs?eval_wirefree (m : Module) (regVals inputs : Env) (hw : m.wires = []) :
    m.outputs?eval regVals inputs =
      m.outputs.map (fun o => (o.name,
        (eval o.expr (cycleEnv regVals inputs (m.regs.map (·.name)))).toNat)) := by
  simp only [Module.outputs?eval, hw, evalWires, List.foldl_nil]

/-- A wire-free child's `step` clocks register `r`'s `next` (no reset) evaluated in the cycle env. -/
theorem step_wirefree_reg (m : Module) (regVals inputs : Env) (hw : m.wires = [])
    (r : Reg) (hfind : m.regs.find? (·.name = r.name) = some r) :
    m.step regVals inputs false r.name
      = (eval r.next (cycleEnv regVals inputs (m.regs.map (·.name)))).toNat := by
  unfold Module.step
  simp only [hw, evalWires, List.foldl_nil, hfind, Bool.false_eq_true, if_false]

/-! ### The child-instance realizes its output/next-state through the flattening

Composing `inst_output_correct` with `outputs?eval_wirefree` (resp. `inst_next_correct` with
`step_wirefree`) gives the headline per-instance facts: the flattened output wire / register
next-state evaluated in the parent env `E` equals the value the child's own `Module.outputs?eval` /
`Module.step` produces — the child module (compiled by the M6-proven `compileModule`) is faithfully
realized as a renamed slice of the flat parent. -/

/-- **The flattened output wires compute the child's `outputs?eval`.**  For a wire-free child, the
    whole per-cycle output map the hierarchical simulator samples equals the list of flattened output
    wires evaluated in the parent env `E`. -/
theorem flatOut_eq_childOut (inst : Inst) (E : Env)
    (hw : inst.child.wires = [])
    (hbound : ∀ o ∈ inst.child.outputs, ∀ n ∈ o.expr.vars,
                n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name))
    (hdisj : ∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none) :
    inst.child.outputs?eval (inst.regVals E) (inst.childIn E)
      = inst.child.outputs.map (fun o =>
          (o.name, (eval (substRename inst.ins inst.rename o.expr) E).toNat)) := by
  rw [outputs?eval_wirefree inst.child (inst.regVals E) (inst.childIn E) hw]
  apply List.map_congr_left
  intro o ho
  have h := inst_output_correct inst E o ho (hbound o ho) hdisj
  simp only [Inst.childCycleEnv] at h
  rw [← h]

/-- **The flattened register next-state computes the child's `step` value** (no reset). -/
theorem flatNext_eq_childStep (inst : Inst) (E : Env) (r : Reg) (hr : r ∈ inst.child.regs)
    (hw : inst.child.wires = [])
    (hbound : ∀ n ∈ r.next.vars, n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name))
    (hdisj : ∀ r' ∈ inst.child.regs, inst.ins.lookup r'.name = none)
    (hfind : inst.child.regs.find? (·.name = r.name) = some r) :
    inst.child.step (inst.regVals E) (inst.childIn E) false r.name
      = (eval (substRename inst.ins inst.rename r.next) E).toNat := by
  rw [step_wirefree_reg inst.child (inst.regVals E) (inst.childIn E) hw r hfind,
      inst_next_correct inst E r hr hbound hdisj, Inst.childCycleEnv]

/-! ## Flattening a sequential parent into a flat sequential module

`flattenParentSeq` inlines every child instance into a single flat *sequential* `Module`: each child
register becomes a parent register renamed `"<inst>.<reg>"` (its next-state `substRename`d), each
child output/wire becomes a parent wire renamed `"<inst>.<name>"`, and the parent's own clock/reset
are the flat module's clock/reset.  This is the sequential analogue of `HierCorrect.flattenParent`;
its per-register next-state is characterised faithful by `inst_next_correct`, and its whole-run
behaviour is validated by co-simulation of the emitted hierarchy.  The flat module is register-shaped
so it inherits the M6-proven `compileModule` sequential correctness. -/

/-- Flattened registers of one instance: each child register renamed `"<inst>.<reg>"`, its next-state
    substituted-and-renamed, its `init` preserved. -/
def Inst.flatRegs (inst : Inst) : List Reg :=
  inst.child.regs.map (fun r =>
    { name := inst.rename r.name, width := r.width,
      next := substRename inst.ins inst.rename r.next, init := r.init, emitInit := r.emitInit,
      asyncReset := r.asyncReset.map (fun ar => (inst.rename ar.1, ar.2)),
      negedge := r.negedge })

theorem flatRegs_names (inst : Inst) :
    (inst.flatRegs.map (·.name)) = inst.child.regs.map (fun r => inst.rename r.name) := by
  simp only [Inst.flatRegs, List.map_map]; rfl

/-- Flattened wires of one instance: each child output *and* internal wire becomes a parent wire
    renamed `"<inst>.<name>"`, its expression substituted-and-renamed.  Child wires come first (they
    may be referenced by the outputs), then the outputs, matching the child's own topological order. -/
def Inst.flatWiresSeq (inst : Inst) : List Wire :=
  inst.child.wires.map (fun w =>
    { name := inst.rename w.name, width := w.width, expr := substRename inst.ins inst.rename w.expr })
  ++ inst.child.outputs.map (fun o =>
    { name := inst.rename o.name, width := o.width, expr := substRename inst.ins inst.rename o.expr })

/-- **The sequential flattening of a parent into one flat sequential `Module`.**  Every child
    instance's registers become parent registers renamed `"<inst>.<reg>"` (next-state
    `substRename`d), every child output/wire becomes a parent wire renamed `"<inst>.<name>"`, and the
    parent's own `clock`/`reset` drive the flat module.  The parent outputs are kept verbatim (they
    already reference `"<inst>.<port>"`, which are now flat wires).  This is the sequential analogue
    of `HierCorrect.flattenParent`: the result is a register-shaped flat `Module`, so it inherits the
    M6-proven `compileModule` sequential compiler-correctness; its per-register next-state and
    per-output value are pinned faithful by `flatNext_eq_childStep` / `flatOut_eq_childOut`, and the
    whole hierarchical run by co-simulation of the emitted instance netlist (Yosys `hierarchy`). -/
def flattenParentSeq (p : Parent) : Module :=
  { name := p.name, inputs := p.inputs, outputs := p.outputs,
    wires := p.insts.flatMap Inst.flatWiresSeq,
    regs := p.insts.flatMap Inst.flatRegs,
    clock := p.clock, reset := p.reset }

/-- The flattened module's registers are exactly the instance-qualified child registers. -/
theorem flattenParentSeq_regs (p : Parent) :
    (flattenParentSeq p).regs = p.insts.flatMap Inst.flatRegs := rfl

/-- The flattened module carries the parent's clock/reset — it is a genuine sequential module,
    whose flip-flops are the union of the children's, wired to the parent clock. -/
theorem flattenParentSeq_clock (p : Parent) :
    (flattenParentSeq p).clock = p.clock ∧ (flattenParentSeq p).reset = p.reset := ⟨rfl, rfl⟩

end LeanRTL
