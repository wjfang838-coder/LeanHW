import LeanRTL.Core.CompilerDeterministic
import LeanRTL.Core.CheckWidth
import LeanRTL.Core.CompilerCorrectSeq
/-!
# Temporal netlist model (M29): discharging the `seq_register_correct` hypotheses

`CompilerCorrectSeq.seq_register_correct` (M6b) is stated over three *assumptions* about a
sequential netlist run — `hinit`/`hdff`/`hcomb` — with no trace-level RTLIL model behind them
(see the honesty note in that file's header).  This file supplies the model and *derives* them:

* `NetTrace` — a net valuation per clock cycle (`Nat → (Nat → Bool)`);
* `DffHolds` — the temporal law of one `$dff` cell: `Q[t+1] = D[t]` (bus-denotationally);
* `TraceConsistent` — every combinational cell holds at every cycle (`ConsistentCells`, which
  ignores `$dff`s since `cellHolds "$dff"` is `True`), and every `$dff` cell obeys `DffHolds`;
* module-level **forcing** lemmas (the ∀σ direction of `compile_forces`, lifted through the
  wire / dff / output phases of `compileModuleM`): any single valuation consistent with the
  compiled module's cells and reproducing the input/register values on the setup buses is
  *forced* to place `eval` values on every wire net, register-D net, and output net
  (`compileWires_forces`, `compileDffs_forces_noreset` / `_reset`, `compileOutputs_forces`);
* the headline `netTrace_register_correct` / `netTrace_register_correct_reset`: for a module
  passing the decidable checks (`moduleChecksb`, plus register-name distinctness), **any**
  trace that is `TraceConsistent` with the compiled cells, whose input nets carry the input
  stream each cycle (and, for a sync-reset module, whose reset net carries the reset stream),
  and whose register Q nets start at `initRegs`, carries register values equal to the
  denotational `regTrace` at *every* cycle.  `netTrace_output_correct` / `_reset` extend this
  to the output nets.

Honest residue: the cycle-0 hypothesis (`hinit`) remains an assumption about the trace at the
Lean level — this temporal model does not itself formalise power-on.  In the *emitted* netlist,
though, each register's `Q` net now carries an RTLIL `init` attribute equal to `r.init` (F7, via
`compileReg`), which `yosys write_verilog` lowers to a power-on value (`reg q = init`); so a real
simulator realises `hinit` directly at cycle 0, without needing a reset pulse.  (A sync-reset
pulse still forces every register to `init` on the next cycle, which is `regTrace` restarted at
1.)  Everything else — the `$dff` law and the per-cycle combinational correctness (`hcomb`) — is
*derived* from `TraceConsistent`, not assumed.
-/

namespace LeanRTL

/-- A temporal netlist trace: one net valuation per clock cycle. -/
def NetTrace := Nat → (Nat → Bool)

end LeanRTL

namespace LeanRTL.NetTrace

open LeanRTL LeanRTL.Backend LeanRTL.BackendSem LeanRTL.CompilerCorrect
  LeanRTL.CompilerModuleCorrect LeanRTL.CompilerDeterministic LeanRTL.CheckWidth
  LeanRTL.CompilerCorrectSeq

/-! ## The temporal model -/

/-- The temporal law of one `$dff` cell: at every cycle, next cycle's `Q` bus denotes this
    cycle's `D` bus (at the `Q` bus's width — for the cells `compileModuleM` emits the `Q` bus
    is the register's `fresh`-allocated bus of exactly the register's width). -/
def DffHolds (τ : NetTrace) (c : Cell) : Prop :=
  ∀ t, busDen (τ (t + 1)) (conn c "Q").length (conn c "Q")
     = busDen (τ t) (conn c "Q").length (conn c "D")

/-- A trace is consistent with a compiled cell list when every cell holds combinationally at
    every cycle (`cellHolds` of a `$dff` is `True`, so this constrains only the combinational
    cells) and every `$dff` cell obeys the temporal law `DffHolds`. -/
def TraceConsistent (τ : NetTrace) (cells : List Cell) : Prop :=
  (∀ t, ConsistentCells (τ t) cells) ∧ (∀ c ∈ cells, c.type = "$dff" → DffHolds τ c)

/-! ## `dffCell` projections (the cell `compileDffSync` emits) -/

@[simp] theorem dffCell_type (cnt pol w : Nat) (clkBus dbus qbus : Bus) :
    (dffCell cnt pol w clkBus dbus qbus).type = "$dff" := rfl

@[simp] theorem conn_dffCell_D (cnt pol w : Nat) (clkBus dbus qbus : Bus) :
    conn (dffCell cnt pol w clkBus dbus qbus) "D" = dbus := rfl

@[simp] theorem conn_dffCell_Q (cnt pol w : Nat) (clkBus dbus qbus : Bus) :
    conn (dffCell cnt pol w clkBus dbus qbus) "Q" = qbus := rfl

/-! ## Cells are only ever prepended (module phases)

`compileExpr_cells_sub` says expression compilation preserves existing cells; these lift that
fact through the wire, dff, and output phases of `compileModuleM`, so consistency of the *final*
cell list restricts to consistency of every intermediate cell list. -/

theorem compileWires_cells_sub (wires : List Wire) :
    ∀ (acc : List NetName) (s : CState), ∀ c ∈ s.cells,
      c ∈ ((wires.foldlM compileWire acc).run s).2.cells := by
  induction wires with
  | nil => intro acc s c hc; exact hc
  | cons w ws ih =>
    intro acc s c hc
    rw [List.foldlM_cons]
    show c ∈ ((ws.foldlM compileWire ((compileWire acc w).run s).1).run
      ((compileWire acc w).run s).2).2.cells
    refine ih _ ((compileWire acc w).run s).2 c ?_
    rw [compileWire_cells]
    exact compileExpr_cells_sub w.expr s c hc

/-- `compileDff` (for a register without async reset) only prepends cells. -/
theorem compileDff_cells_sub (regBuses : List (String × Bus)) (reset clock : Option String)
    (r : Reg) (s : CState) (har : r.asyncReset = none) :
    ∀ c ∈ s.cells, c ∈ ((compileDff regBuses reset clock r).run s).2.cells := by
  intro c hc
  cases reset with
  | none =>
    rw [compileDff_noreset_cells (har := har)]
    exact List.mem_cons_of_mem _ (compileExpr_cells_sub r.next s c hc)
  | some rst =>
    rw [compileDff_reset_cells (har := har)]
    exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (compileExpr_cells_sub r.next s c hc))

theorem compileDffs_cells_sub (regBuses : List (String × Bus)) (clock : Option String) :
    ∀ (regs : List Reg) (acc : List Bus) (s : CState),
      (∀ r ∈ regs, r.asyncReset = none) →
      ∀ c ∈ s.cells, c ∈ ((regs.foldlM (dffStep regBuses clock) acc).run s).2.cells := by
  intro regs
  induction regs with
  | nil => intro acc s _ c hc; exact hc
  | cons r rs ih =>
    intro acc s har c hc
    rw [List.foldlM_cons]
    show c ∈ ((rs.foldlM (dffStep regBuses clock) ((dffStep regBuses clock acc r).run s).1).run
      ((dffStep regBuses clock acc r).run s).2).2.cells
    refine ih _ ((dffStep regBuses clock acc r).run s).2
      (fun r' hr' => har r' (List.mem_cons_of_mem r hr')) c ?_
    rw [dffStep_state]
    exact compileDff_cells_sub regBuses none clock r s (har r (List.mem_cons_self ..)) c hc

theorem compileDffsR_cells_sub (regBuses : List (String × Bus)) (rst : String)
    (clock : Option String) :
    ∀ (regs : List Reg) (acc : List Bus) (s : CState),
      (∀ r ∈ regs, r.asyncReset = none) →
      ∀ c ∈ s.cells, c ∈ ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).2.cells := by
  intro regs
  induction regs with
  | nil => intro acc s _ c hc; exact hc
  | cons r rs ih =>
    intro acc s har c hc
    rw [List.foldlM_cons]
    show c ∈ ((rs.foldlM (dffStepR regBuses rst clock)
        ((dffStepR regBuses rst clock acc r).run s).1).run
      ((dffStepR regBuses rst clock acc r).run s).2).2.cells
    refine ih _ ((dffStepR regBuses rst clock acc r).run s).2
      (fun r' hr' => har r' (List.mem_cons_of_mem r hr')) c ?_
    rw [dffStepR_state]
    exact compileDff_cells_sub regBuses (some rst) clock r s (har r (List.mem_cons_self ..)) c hc

theorem compileOutputs_cells_sub (outputs : List OutPort) :
    ∀ (acc : List Port × List NetName) (s : CState), ∀ c ∈ s.cells,
      c ∈ ((outputs.foldlM compileOutput acc).run s).2.cells := by
  induction outputs with
  | nil => intro acc s c hc; exact hc
  | cons o os ih =>
    intro acc s c hc
    rw [List.foldlM_cons]
    show c ∈ ((os.foldlM compileOutput ((compileOutput acc o).run s).1).run
      ((compileOutput acc o).run s).2).2.cells
    refine ih _ ((compileOutput acc o).run s).2 c ?_
    rw [compileOutput_state]
    exact compileExpr_cells_sub o.expr s c hc

/-! ## Phase-level environment invariance (dff fold) -/

theorem compileDffs_env (regBuses : List (String × Bus)) (clock : Option String) :
    ∀ (regs : List Reg) (acc : List Bus) (s : CState),
      (∀ r ∈ regs, r.asyncReset = none) →
      ((regs.foldlM (dffStep regBuses clock) acc).run s).2.env = s.env := by
  intro regs
  induction regs with
  | nil => intro acc s _; rfl
  | cons r rs ih =>
    intro acc s har
    rw [List.foldlM_cons]
    show ((rs.foldlM (dffStep regBuses clock) ((dffStep regBuses clock acc r).run s).1).run
      ((dffStep regBuses clock acc r).run s).2).2.env = s.env
    rw [ih _ _ (fun r' hr' => har r' (List.mem_cons_of_mem r hr')), dffStep_state,
        compileDff_noreset_env (har := har r (List.mem_cons_self ..)), compileExpr_env]

theorem compileDffsR_env (regBuses : List (String × Bus)) (rst : String)
    (clock : Option String) :
    ∀ (regs : List Reg) (acc : List Bus) (s : CState),
      (∀ r ∈ regs, r.asyncReset = none) →
      ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).2.env = s.env := by
  intro regs
  induction regs with
  | nil => intro acc s _; rfl
  | cons r rs ih =>
    intro acc s har
    rw [List.foldlM_cons]
    show ((rs.foldlM (dffStepR regBuses rst clock)
        ((dffStepR regBuses rst clock acc r).run s).1).run
      ((dffStepR regBuses rst clock acc r).run s).2).2.env = s.env
    rw [ih _ _ (fun r' hr' => har r' (List.mem_cons_of_mem r hr')), dffStepR_state,
        compileDff_reset_env (har := har r (List.mem_cons_self ..)), compileExpr_env]

/-! ## Wire-phase forcing (∀σ)

The ∀σ analogue of `compileWires_sound`: with σ *fixed* (no `setRange` σ-surgery, no frame
lemmas), consistency of the wire fold's cells forces every wire net to denote its `eval`, growing
`CEnvOK` to the wire-extended value environment `evalWires wires vals`. -/

theorem compileWires_forces : ∀ (wires : List Wire) (acc : List NetName) (s : CState)
    (σ : Nat → Bool) (vals : Env),
    CEnvOK σ s.env vals → WiresOK s.env wires →
    ConsistentCells σ ((wires.foldlM compileWire acc).run s).2.cells →
    CEnvOK σ ((wires.foldlM compileWire acc).run s).2.env (evalWires wires vals) := by
  intro wires
  induction wires with
  | nil => intro acc s σ vals hc _ _; simpa [evalWires] using hc
  | cons w ws ih =>
    intro acc s σ vals hc hwf hcons
    obtain ⟨hwf_head, hwf_tail⟩ := hwf
    rw [List.foldlM_cons] at hcons ⊢
    have hcons' : ConsistentCells σ
        ((ws.foldlM compileWire ((compileWire acc w).run s).1).run
          ((compileWire acc w).run s).2).2.cells := hcons
    have hconsHead : ConsistentCells σ ((compileExpr w.expr).run s).2.cells := by
      intro c hcm
      refine hcons' c (compileWires_cells_sub ws _ ((compileWire acc w).run s).2 c ?_)
      rw [compileWire_cells]
      exact hcm
    have hlen : ((compileExpr w.expr).run s).1.length = w.width :=
      compileExpr_len w.expr (supp_all w.expr) s hwf_head
    have hval : busDen σ w.width ((compileExpr w.expr).run s).1 = eval w.expr vals :=
      compile_forces w.expr vals s hwf_head σ hconsHead hc
    have hc' : CEnvOK σ ((compileWire acc w).run s).2.env
        (fun n => if n = w.name then (eval w.expr vals).toNat else vals n) := by
      rw [compileWire_env, compileExpr_env]
      refine CEnvOK_cons_wire ?_ hc
      rw [hlen, hval, BitVec_ofNat_toNat_self]
    have hwf' : WiresOK ((compileWire acc w).run s).2.env ws := by
      rw [compileWire_env, compileExpr_env]
      exact hwf_tail _ hlen
    have hfinal := ih ((compileWire acc w).run s).1 ((compileWire acc w).run s).2 σ
      (fun n => if n = w.name then (eval w.expr vals).toNat else vals n) hc' hwf' hcons'
    show CEnvOK σ ((ws.foldlM compileWire ((compileWire acc w).run s).1).run
        ((compileWire acc w).run s).2).2.env (evalWires (w :: ws) vals)
    rw [show evalWires (w :: ws) vals
          = evalWires ws (fun n => if n = w.name then (eval w.expr vals).toNat else vals n)
        from rfl]
    exact hfinal

/-! ## Dff-phase forcing (∀σ)

The ∀σ analogue of `compileDffs_sound_noreset` / `_reset`: for every register, the emitted
`$dff` cell is in the final cell list, its `Q` connection is the register's setup-phase bus,
and (consistency forcing the next-state cone and, in the sync-reset case, the reset `$mux`)
its `D` connection is *forced* to denote `eval r.next vals` (resp. `reset ? init : next`). -/

theorem compileDffs_forces_noreset (regBuses : List (String × Bus)) (clock : Option String)
    (env : Env) :
    ∀ (regs : List Reg) (acc : List Bus) (s : CState) (σ : Nat → Bool),
      (∀ r ∈ regs, WidthOK s.env r.next) →
      (∀ r ∈ regs, r.asyncReset = none) →
      CEnvOK σ s.env env →
      ConsistentCells σ ((regs.foldlM (dffStep regBuses clock) acc).run s).2.cells →
      ∀ r ∈ regs, ∃ c ∈ ((regs.foldlM (dffStep regBuses clock) acc).run s).2.cells,
        c.type = "$dff" ∧ conn c "Q" = (regBuses.lookup r.name).getD [] ∧
        busDen σ r.width (conn c "D") = eval r.next env := by
  intro regs
  induction regs with
  | nil => intro acc s σ _ _ _ _ r hr; simp at hr
  | cons r rs ih =>
    intro acc s σ hwf har hmem hcons
    have har0 := har r (List.mem_cons_self ..)
    rw [List.foldlM_cons] at hcons ⊢
    have hcons' : ConsistentCells σ
        ((rs.foldlM (dffStep regBuses clock) ((dffStep regBuses clock acc r).run s).1).run
          ((dffStep regBuses clock acc r).run s).2).2.cells := hcons
    have hsub : ∀ c ∈ ((compileDff regBuses none clock r).run s).2.cells,
        c ∈ ((rs.foldlM (dffStep regBuses clock) ((dffStep regBuses clock acc r).run s).1).run
          ((dffStep regBuses clock acc r).run s).2).2.cells := by
      intro c hcm
      refine compileDffs_cells_sub regBuses clock rs _ ((dffStep regBuses clock acc r).run s).2
        (fun r' hr' => har r' (List.mem_cons_of_mem r hr')) c ?_
      rw [dffStep_state]
      exact hcm
    have hconsDff : ConsistentCells σ ((compileDff regBuses none clock r).run s).2.cells :=
      fun c hcm => hcons' c (hsub c hcm)
    have hconsCone : ConsistentCells σ ((compileExpr r.next).run s).2.cells := by
      intro c hcm
      apply hconsDff
      rw [compileDff_noreset_cells (har := har0)]
      exact List.mem_cons_of_mem _ hcm
    have hval : busDen σ r.width ((compileExpr r.next).run s).1 = eval r.next env :=
      compile_forces r.next env s (hwf r (List.mem_cons_self ..)) σ hconsCone hmem
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr''
    · exact ⟨dffCell ((compileExpr r'.next).run s).2.count (if r'.negedge then 0 else 1) r'.width
          (clkBusOf clock ((compileExpr r'.next).run s).2.env)
          ((compileExpr r'.next).run s).1 ((regBuses.lookup r'.name).getD []),
        hsub _ (by rw [compileDff_noreset_cells (har := har0)]; exact List.mem_cons_self ..),
        rfl, rfl, hval⟩
    · have henv2 : ((dffStep regBuses clock acc r).run s).2.env = s.env := by
        rw [dffStep_state, compileDff_noreset_env (har := har0), compileExpr_env]
      have hwf' : ∀ r'' ∈ rs, WidthOK ((dffStep regBuses clock acc r).run s).2.env r''.next := by
        rw [henv2]; exact fun r'' hrr => hwf r'' (List.mem_cons_of_mem r hrr)
      have hmem' : CEnvOK σ ((dffStep regBuses clock acc r).run s).2.env env := by
        rw [henv2]; exact hmem
      exact ih _ ((dffStep regBuses clock acc r).run s).2 σ hwf'
        (fun r'' hrr => har r'' (List.mem_cons_of_mem r hrr)) hmem' hcons' r' hr''

theorem compileDffs_forces_reset (regBuses : List (String × Bus)) (rst : String)
    (clock : Option String) (env : Env) :
    ∀ (regs : List Reg) (acc : List Bus) (s : CState) (σ : Nat → Bool),
      (∀ r ∈ regs, WidthOK s.env r.next) →
      (∀ r ∈ regs, r.asyncReset = none) →
      CEnvOK σ s.env env →
      ConsistentCells σ ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).2.cells →
      ∀ r ∈ regs, ∃ c ∈ ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).2.cells,
        c.type = "$dff" ∧ conn c "Q" = (regBuses.lookup r.name).getD [] ∧
        busDen σ r.width (conn c "D")
          = (if busDen σ 1 ((s.env.lookup rst).getD [Bit.zero]) = 1
             then r.init else eval r.next env) := by
  intro regs
  induction regs with
  | nil => intro acc s σ _ _ _ _ r hr; simp at hr
  | cons r rs ih =>
    intro acc s σ hwf har hmem hcons
    have har0 := har r (List.mem_cons_self ..)
    rw [List.foldlM_cons] at hcons ⊢
    have hcons' : ConsistentCells σ
        ((rs.foldlM (dffStepR regBuses rst clock)
            ((dffStepR regBuses rst clock acc r).run s).1).run
          ((dffStepR regBuses rst clock acc r).run s).2).2.cells := hcons
    have hsub : ∀ c ∈ ((compileDff regBuses (some rst) clock r).run s).2.cells,
        c ∈ ((rs.foldlM (dffStepR regBuses rst clock)
            ((dffStepR regBuses rst clock acc r).run s).1).run
          ((dffStepR regBuses rst clock acc r).run s).2).2.cells := by
      intro c hcm
      refine compileDffsR_cells_sub regBuses rst clock rs _
        ((dffStepR regBuses rst clock acc r).run s).2
        (fun r' hr' => har r' (List.mem_cons_of_mem r hr')) c ?_
      rw [dffStepR_state]
      exact hcm
    have hconsDff : ConsistentCells σ ((compileDff regBuses (some rst) clock r).run s).2.cells :=
      fun c hcm => hcons' c (hsub c hcm)
    have hconsCone : ConsistentCells σ ((compileExpr r.next).run s).2.cells := by
      intro c hcm
      apply hconsDff
      rw [compileDff_reset_cells (har := har0)]
      exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ hcm)
    have hval : busDen σ r.width ((compileExpr r.next).run s).1 = eval r.next env :=
      compile_forces r.next env s (hwf r (List.mem_cons_self ..)) σ hconsCone hmem
    -- the reset mux holds under σ, so the freshly-allocated D bus is forced
    have hmux : cellHolds σ (muxCell ((compileExpr r.next).run s).2 r.width
        ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero])
        (constBits r.init) ((compileExpr r.next).run s).1) := by
      apply hconsDff
      rw [compileDff_reset_cells (har := har0)]
      exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
    have hY : busDen σ (freshBus ((compileExpr r.next).run s).2 r.width).length
          (freshBus ((compileExpr r.next).run s).2 r.width)
        = if busDen σ 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) = 1
          then busDen σ (freshBus ((compileExpr r.next).run s).2 r.width).length
                 (constBits r.init)
          else busDen σ (freshBus ((compileExpr r.next).run s).2 r.width).length
                 ((compileExpr r.next).run s).1 := hmux
    have hflen : (freshBus ((compileExpr r.next).run s).2 r.width).length = r.width := by
      simp [freshBus]
    rw [hflen] at hY
    have henvc : ((compileExpr r.next).run s).2.env = s.env := compileExpr_env r.next s
    rw [henvc] at hY
    have hD : busDen σ r.width (freshBus ((compileExpr r.next).run s).2 r.width)
        = (if busDen σ 1 ((s.env.lookup rst).getD [Bit.zero]) = 1
           then r.init else eval r.next env) := by
      rw [hY, busDen_constBits, hval]
    intro r' hr'
    rcases List.mem_cons.mp hr' with rfl | hr''
    · exact ⟨dffCell (((compileExpr r'.next).run s).2.count + 1) (if r'.negedge then 0 else 1)
          r'.width
          (clkBusOf clock ((compileExpr r'.next).run s).2.env)
          (freshBus ((compileExpr r'.next).run s).2 r'.width)
          ((regBuses.lookup r'.name).getD []),
        hsub _ (by rw [compileDff_reset_cells (har := har0)]; exact List.mem_cons_self ..),
        rfl, rfl, hD⟩
    · have henv2 : ((dffStepR regBuses rst clock acc r).run s).2.env = s.env := by
        rw [dffStepR_state, compileDff_reset_env (har := har0), compileExpr_env]
      have hwf' : ∀ r'' ∈ rs,
          WidthOK ((dffStepR regBuses rst clock acc r).run s).2.env r''.next := by
        rw [henv2]; exact fun r'' hrr => hwf r'' (List.mem_cons_of_mem r hrr)
      have hmem' : CEnvOK σ ((dffStepR regBuses rst clock acc r).run s).2.env env := by
        rw [henv2]; exact hmem
      have := ih _ ((dffStepR regBuses rst clock acc r).run s).2 σ hwf'
        (fun r'' hrr => har r'' (List.mem_cons_of_mem r hrr)) hmem' hcons' r' hr''
      rw [henv2] at this
      exact this

/-! ## Output-phase forcing (∀σ) -/

theorem compileOutputs_forces (outputs : List OutPort) (env : Env) :
    ∀ (acc : List Port × List NetName) (s : CState) (σ : Nat → Bool),
      (∀ o ∈ outputs, WidthOK s.env o.expr) → CEnvOK σ s.env env →
      ConsistentCells σ ((outputs.foldlM compileOutput acc).run s).2.cells →
      ∀ o ∈ outputs, ∃ port ∈ ((outputs.foldlM compileOutput acc).run s).1.1,
        port.name = o.name ∧ port.dir = Dir.output ∧
        busDen σ o.width port.bits = eval o.expr env := by
  induction outputs with
  | nil => intro acc s σ _ _ _ o ho; simp at ho
  | cons o os ih =>
    intro acc s σ hwf hmem hcons
    rw [List.foldlM_cons] at hcons ⊢
    have hcons' : ConsistentCells σ
        ((os.foldlM compileOutput ((compileOutput acc o).run s).1).run
          ((compileOutput acc o).run s).2).2.cells := hcons
    have hconsHead : ConsistentCells σ ((compileExpr o.expr).run s).2.cells := by
      intro c hcm
      refine hcons' c (compileOutputs_cells_sub os _ ((compileOutput acc o).run s).2 c ?_)
      rw [compileOutput_state]
      exact hcm
    have hval : busDen σ o.width ((compileExpr o.expr).run s).1 = eval o.expr env :=
      compile_forces o.expr env s (hwf o (List.mem_cons_self ..)) σ hconsHead hmem
    intro o' ho'
    rcases List.mem_cons.mp ho' with rfl | ho''
    · refine ⟨{ name := o'.name, dir := .output, bits := ((compileExpr o'.expr).run s).1 },
        ?_, rfl, rfl, hval⟩
      show { name := o'.name, dir := Dir.output, bits := ((compileExpr o'.expr).run s).1 }
        ∈ ((os.foldlM compileOutput ((compileOutput acc o').run s).1).run
            ((compileOutput acc o').run s).2).1.1
      obtain ⟨extra, hextra⟩ := compileOutputs_acc_prefix os ((compileOutput acc o').run s).1
        ((compileOutput acc o').run s).2
      rw [hextra, compileOutput_acc]
      simp
    · have henv2 : ((compileOutput acc o).run s).2.env = s.env := by
        rw [compileOutput_state, compileExpr_env]
      have hwf' : ∀ o'' ∈ os, WidthOK ((compileOutput acc o).run s).2.env o''.expr := by
        rw [henv2]; exact fun o'' ho2 => hwf o'' (List.mem_cons_of_mem o ho2)
      have hmem' : CEnvOK σ ((compileOutput acc o).run s).2.env env := by
        rw [henv2]; exact hmem
      exact ih _ ((compileOutput acc o).run s).2 σ hwf' hmem' hcons' o' ho''

/-! ## Module-level plumbing: named phase states and the register readout -/

/-- The compiler state after the input phase of `compileModuleM m` (from the empty state). -/
abbrev inputState (m : Module) : CState := ((m.inputs.foldlM compileInput ([], [])).run {}).2

/-- The compiler state after the setup (input + register) phases. -/
abbrev setupState (m : Module) : CState :=
  ((m.regs.foldlM compileReg ([], [])).run (inputState m)).2

/-- The name→Q-bus register map built by the register phase (the `regBuses` fed to the dffs). -/
abbrev regBusesOf (m : Module) : List (String × Bus) :=
  ((m.regs.foldlM compileReg ([], [])).run (inputState m)).1.1

/-- The compiler state after the wire phase. -/
abbrev wireState (m : Module) : CState :=
  ((m.wires.foldlM compileWire []).run (setupState m)).2

/-- The compiled `Q` bus of the register named `n`. -/
abbrev qbusOf (m : Module) (n : String) : Bus := ((regBusesOf m).lookup n).getD []

/-- A shadowed-key singleton lookup misses. -/
theorem lookup_singleton_ne {b : Bus} {n a : String} (h : ¬(n = a)) :
    [(a, b)].lookup n = none := by
  rw [List.lookup_cons]
  split
  · rename_i heq; exact absurd (by simpa using heq) h
  · rfl

/-- The register file a trace carries at cycle `t`: each register name reads its `Q` bus's
    nat value under `τ t`; non-register names read 0 (matching `Module.initRegs`). -/
def regReadout (m : Module) (τ : NetTrace) (t : Nat) : Env :=
  fun n => match m.regs.find? (·.name = n) with
    | some _ => busValNat (τ t) (qbusOf m n)
    | none => 0

/-! ### Register-phase lookup structure

The register phase *prepends* env bindings but *appends* `regBuses` bindings, so with distinct
register names both lookups agree (and give a bus of exactly the declared width); names not
bound by the register phase fall through to the input phase's bindings. -/

theorem compileRegs_env_lookup_notmem (regs : List Reg) :
    ∀ (acc : List (String × Bus) × List NetName) (s : CState) (n : String),
      n ∉ regs.map (·.name) →
      ((regs.foldlM compileReg acc).run s).2.env.lookup n = s.env.lookup n := by
  induction regs with
  | nil => intro acc s n _; rfl
  | cons r rs ih =>
    intro acc s n hn
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [List.foldlM_cons]
    show ((rs.foldlM compileReg ((compileReg acc r).run s).1).run
      ((compileReg acc r).run s).2).2.env.lookup n = s.env.lookup n
    rw [ih _ _ n hn.2, compileReg_env, List.lookup_cons]
    split
    · rename_i heq
      exact absurd (by simpa using heq) hn.1
    · rfl

theorem compileRegs_acc_lookup_notmem (regs : List Reg) :
    ∀ (acc : List (String × Bus) × List NetName) (s : CState) (n : String),
      n ∉ regs.map (·.name) →
      ((regs.foldlM compileReg acc).run s).1.1.lookup n = acc.1.lookup n := by
  induction regs with
  | nil => intro acc s n _; rfl
  | cons r rs ih =>
    intro acc s n hn
    simp only [List.map_cons, List.mem_cons, not_or] at hn
    rw [List.foldlM_cons]
    show ((rs.foldlM compileReg ((compileReg acc r).run s).1).run
      ((compileReg acc r).run s).2).1.1.lookup n = acc.1.lookup n
    rw [ih _ _ n hn.2, compileReg_acc, List.lookup_append, lookup_singleton_ne hn.1,
        Option.or_none]

theorem compileRegs_lookup_agree (regs : List Reg) :
    ∀ (acc : List (String × Bus) × List NetName) (s : CState),
      (regs.map (·.name)).Nodup →
      (∀ r ∈ regs, acc.1.lookup r.name = none) →
      ∀ r ∈ regs, ∃ bus,
        ((regs.foldlM compileReg acc).run s).2.env.lookup r.name = some bus ∧
        ((regs.foldlM compileReg acc).run s).1.1.lookup r.name = some bus ∧
        bus.length = r.width := by
  induction regs with
  | nil => intro acc s _ _ r hr; simp at hr
  | cons r rs ih =>
    intro acc s hnd hacc r' hr'
    simp only [List.map_cons, List.nodup_cons] at hnd
    rw [List.foldlM_cons]
    show ∃ bus,
      ((rs.foldlM compileReg ((compileReg acc r).run s).1).run
        ((compileReg acc r).run s).2).2.env.lookup r'.name = some bus ∧
      ((rs.foldlM compileReg ((compileReg acc r).run s).1).run
        ((compileReg acc r).run s).2).1.1.lookup r'.name = some bus ∧
      bus.length = r'.width
    rcases List.mem_cons.mp hr' with rfl | hr''
    · refine ⟨freshBus s r'.width, ?_, ?_, by simp [freshBus]⟩
      · rw [compileRegs_env_lookup_notmem rs _ _ _ hnd.1, compileReg_env]
        simp [List.lookup]
      · rw [compileRegs_acc_lookup_notmem rs _ _ _ hnd.1, compileReg_acc, List.lookup_append,
            hacc r' (List.mem_cons_self ..), Option.none_or]
        simp [List.lookup]
    · have hacc' : ∀ r'' ∈ rs, ((compileReg acc r).run s).1.1.lookup r''.name = none := by
        intro r'' hrr
        have hne : ¬(r''.name = r.name) :=
          fun hc => hnd.1 (hc ▸ List.mem_map.mpr ⟨r'', hrr, rfl⟩)
        rw [compileReg_acc, List.lookup_append, hacc r'' (List.mem_cons_of_mem r hrr),
            lookup_singleton_ne hne, Option.or_none]
      exact ih _ ((compileReg acc r).run s).2 hnd.2 hacc' r' hr''

/-- Module-level repackaging: for distinct register names, each register's setup-env binding
    and its `regBuses` binding are the *same* bus — `qbusOf` — of exactly the register's width. -/
theorem regBus_lookup (m : Module) (hnd : (m.regs.map (·.name)).Nodup)
    (r : Reg) (hr : r ∈ m.regs) :
    (setupState m).env.lookup r.name = some (qbusOf m r.name) ∧
    (regBusesOf m).lookup r.name = some (qbusOf m r.name) ∧
    (qbusOf m r.name).length = r.width := by
  obtain ⟨qbus, henvl, haccl, hqlen⟩ :=
    compileRegs_lookup_agree m.regs ([], []) (inputState m) hnd (fun r' _ => rfl) r hr
  have haccl' : (regBusesOf m).lookup r.name = some qbus := haccl
  have henvl' : (setupState m).env.lookup r.name = some qbus := henvl
  have hq : qbusOf m r.name = qbus := by
    unfold qbusOf
    rw [haccl']
    rfl
  rw [hq]
  exact ⟨henvl', haccl', hqlen⟩

/-- **Per-cycle interface**: a trace whose input nets carry `inputs t` reproduces, on the whole
    setup environment, the cycle environment built from its own register readout — the `CEnvOK`
    the forcing lemmas consume.  (The register bindings hold *definitionally* by the choice of
    `regReadout`; the input bindings come from the boundary hypothesis.) -/
theorem setup_cenvOK_readout (m : Module) (hnd : (m.regs.map (·.name)).Nodup)
    (τ : NetTrace) (inputs : Nat → Env) (t : Nat)
    (hin : CEnvOK (τ t) (inputState m).env (inputs t)) :
    CEnvOK (τ t) (setupState m).env
      (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))) := by
  intro n bus hl
  by_cases hn : n ∈ m.regs.map (·.name)
  · obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hn
    subst hrn
    obtain ⟨henvl, _, _⟩ := regBus_lookup m hnd r hr
    have hbq : bus = qbusOf m r.name := by
      have := henvl.symm.trans hl
      exact (Option.some.inj this).symm
    subst hbq
    have hcy : cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name)) r.name
        = regReadout m τ t r.name := by
      simp [cycleEnv, hn]
    have hro : regReadout m τ t r.name = busValNat (τ t) (qbusOf m r.name) := by
      unfold regReadout
      cases hf : m.regs.find? (·.name = r.name) with
      | none =>
        rw [List.find?_eq_none] at hf
        exact absurd (by simp) (hf r hr)
      | some r0 => rfl
    show busDen (τ t) (qbusOf m r.name).length (qbusOf m r.name)
        = BitVec.ofNat (qbusOf m r.name).length
            (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name)) r.name)
    rw [hcy, hro]
    rfl
  · have hl2 : ((m.regs.foldlM compileReg ([], [])).run (inputState m)).2.env.lookup n
        = some bus := hl
    rw [compileRegs_env_lookup_notmem m.regs ([], []) (inputState m) n hn] at hl2
    have hval := hin n bus hl2
    have hcy : cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name)) n
        = inputs t n := by
      simp [cycleEnv, hn]
    show busDen (τ t) bus.length bus
        = BitVec.ofNat bus.length
            (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name)) n)
    rw [hcy]
    exact hval

/-! ### `compileModuleM`'s final state is the phase composition -/

theorem compileModuleM_state_noreset (m : Module) (hr : m.reset = none) :
    ((compileModuleM m).run {}).2
      = ((m.outputs.foldlM compileOutput ([], [])).run
          ((m.regs.foldlM (dffStep (regBusesOf m) m.clock) []).run (wireState m)).2).2 := by
  simp only [compileModuleM, run_bind, run_pure, hr, compileDffs]
  rfl

theorem compileModuleM_state_reset (m : Module) (rst : String) (hr : m.reset = some rst) :
    ((compileModuleM m).run {}).2
      = ((m.outputs.foldlM compileOutput ([], [])).run
          ((m.regs.foldlM (dffStepR (regBusesOf m) rst m.clock) []).run (wireState m)).2).2 := by
  simp only [compileModuleM, run_bind, run_pure, hr, compileDffs]
  rfl

/-! ## The headline theorems -/

/-- **Temporal netlist correctness — registers, reset-free.**  For a module passing the
    decidable checks (`moduleChecksb`, plus distinct register names), ANY trace `τ` that

    * is `TraceConsistent` with the compiled cells (combinational cells hold every cycle,
      `$dff`s obey `Q[t+1] = D[t]`),
    * carries the input stream on the compiled input nets each cycle (`hin`), and
    * starts with each register's `Q` bus at its `init` value (`hinit` — the honest cycle-0
      assumption; hardware realises it via a reset pulse),

    has register readouts equal to the denotational register trace at **every** cycle.
    `hdff`/`hcomb` of `seq_register_correct` are *derived* here: `hcomb` from the module-level
    forcing lemmas applied to `τ t` (which is *some* consistent valuation, hence pinned), and
    `hdff` from `DffHolds` of the emitted `$dff` cells. -/
theorem netTrace_register_correct (m : Module) (hr : m.reset = none)
    (hchk : moduleChecksb m = true) (hnd : (m.regs.map (·.name)).Nodup)
    (τ : NetTrace) (inputs : Nat → Env)
    (htr : TraceConsistent τ ((compileModuleM m).run {}).2.cells)
    (hin : ∀ t, CEnvOK (τ t) (inputState m).env (inputs t))
    (hinit : ∀ r ∈ m.regs, busDen (τ 0) r.width (qbusOf m r.name) = r.init) :
    ∀ t, regReadout m τ t = regTrace m inputs (fun _ => false) t := by
  obtain ⟨har, hwfd, hwfo, hwires⟩ := moduleChecks_sound m hchk
  obtain ⟨hcomb, hdffs⟩ := htr
  have hcellseq : ((compileModuleM m).run {}).2.cells
      = ((m.outputs.foldlM compileOutput ([], [])).run
          ((m.regs.foldlM (dffStep (regBusesOf m) m.clock) []).run (wireState m)).2).2.cells := by
    rw [compileModuleM_state_noreset m hr]
  -- per-cycle forcing: every register's D net denotes `eval r.next` of the readout cycle env
  have hQstep : ∀ (t : Nat) (r : Reg), r ∈ m.regs →
      busValNat (τ (t + 1)) (qbusOf m r.name)
        = (eval r.next (evalWires m.wires
            (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))).toNat := by
    intro t r hrm
    have hconsAll : ConsistentCells (τ t) ((m.outputs.foldlM compileOutput ([], [])).run
        ((m.regs.foldlM (dffStep (regBusesOf m) m.clock) []).run (wireState m)).2).2.cells := by
      rw [← hcellseq]; exact hcomb t
    have hconsDffFold : ConsistentCells (τ t)
        ((m.regs.foldlM (dffStep (regBusesOf m) m.clock) []).run (wireState m)).2.cells :=
      fun c hc => hconsAll c (compileOutputs_cells_sub m.outputs _ _ c hc)
    have hconsWire : ConsistentCells (τ t)
        ((m.wires.foldlM compileWire []).run (setupState m)).2.cells :=
      fun c hc => hconsDffFold c
        (compileDffs_cells_sub (regBusesOf m) m.clock m.regs [] (wireState m) har c hc)
    have hce0 := setup_cenvOK_readout m hnd τ inputs t (hin t)
    have hcew : CEnvOK (τ t) (wireState m).env
        (evalWires m.wires (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name)))) :=
      compileWires_forces m.wires [] (setupState m) (τ t)
        (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))) hce0 hwires hconsWire
    obtain ⟨c, hcmem, hctype, hcQ, hcD⟩ :=
      compileDffs_forces_noreset (regBusesOf m) m.clock
        (evalWires m.wires (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))
        m.regs [] (wireState m) (τ t) hwfd har hcew hconsDffFold r hrm
    have hlaw := hdffs c
      (by rw [hcellseq]; exact compileOutputs_cells_sub m.outputs _ _ c hcmem) hctype t
    obtain ⟨_, _, hqlen⟩ := regBus_lookup m hnd r hrm
    have hcQ' : conn c "Q" = qbusOf m r.name := hcQ
    rw [hcQ', hqlen] at hlaw
    calc busValNat (τ (t + 1)) (qbusOf m r.name)
        = (busDen (τ (t + 1)) r.width (qbusOf m r.name)).toNat :=
          (busDen_toNat _ _ _ hqlen).symm
      _ = (busDen (τ t) r.width (conn c "D")).toNat := by rw [hlaw]
      _ = (eval r.next (evalWires m.wires
            (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))).toNat := by
          rw [hcD]
  -- the readout obeys the denotational step at every cycle (hdff + hcomb, combined)
  have hstep : ∀ t, regReadout m τ (t + 1)
      = m.step (regReadout m τ t) (inputs t) false := by
    intro t
    funext n
    show (match m.regs.find? (·.name = n) with
          | some _ => busValNat (τ (t + 1)) (qbusOf m n)
          | none => 0)
        = (match m.regs.find? (·.name = n) with
          | some r => if false then r.init.toNat
                      else (eval r.next (evalWires m.wires
                        (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))).toNat
          | none => regReadout m τ t n)
    cases hf : m.regs.find? (·.name = n) with
    | none =>
      show (0 : Nat) = regReadout m τ t n
      unfold regReadout
      rw [hf]
    | some r =>
      have hrn : r.name = n := by simpa using List.find?_some hf
      have hrm : r ∈ m.regs := List.mem_of_find?_eq_some hf
      show busValNat (τ (t + 1)) (qbusOf m n)
          = (eval r.next (evalWires m.wires
              (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))).toNat
      rw [← hrn]
      exact hQstep t r hrm
  -- the readout starts at `initRegs` (the honest hinit)
  have hinit' : regReadout m τ 0 = m.initRegs := by
    funext n
    show (match m.regs.find? (·.name = n) with
          | some _ => busValNat (τ 0) (qbusOf m n)
          | none => 0)
        = (match m.regs.find? (·.name = n) with
          | some r => r.init.toNat
          | none => 0)
    cases hf : m.regs.find? (·.name = n) with
    | none => rfl
    | some r =>
      have hrn : r.name = n := by simpa using List.find?_some hf
      have hrm : r ∈ m.regs := List.mem_of_find?_eq_some hf
      show busValNat (τ 0) (qbusOf m n) = r.init.toNat
      rw [← hrn]
      obtain ⟨_, _, hqlen⟩ := regBus_lookup m hnd r hrm
      rw [← busDen_toNat (τ 0) (qbusOf m r.name) r.width hqlen, hinit r hrm]
  -- conclude by the M6b temporal core
  intro t
  exact seq_register_correct m inputs (fun _ => false) (regReadout m τ)
    (fun t => m.step (regReadout m τ t) (inputs t) false)
    hinit' hstep (fun _ => rfl) t

/-- **Temporal netlist correctness — registers, synchronous reset.**  Like
    `netTrace_register_correct`, with one extra boundary condition: the compiled reset net
    carries the reset stream each cycle (`hrst`).  The reset `$mux` in front of each `$dff`
    is then forced, so `D[t]` denotes `reset t ? init : next` — exactly `Module.step` with
    synchronous reset — and the readout equals `regTrace` at every cycle. -/
theorem netTrace_register_correct_reset (m : Module) (rst : String) (hr : m.reset = some rst)
    (hchk : moduleChecksb m = true) (hnd : (m.regs.map (·.name)).Nodup)
    (τ : NetTrace) (inputs : Nat → Env) (reset : Nat → Bool)
    (htr : TraceConsistent τ ((compileModuleM m).run {}).2.cells)
    (hin : ∀ t, CEnvOK (τ t) (inputState m).env (inputs t))
    (hrst : ∀ t, busDen (τ t) 1 (((wireState m).env.lookup rst).getD [Bit.zero])
      = if reset t then 1 else 0)
    (hinit : ∀ r ∈ m.regs, busDen (τ 0) r.width (qbusOf m r.name) = r.init) :
    ∀ t, regReadout m τ t = regTrace m inputs reset t := by
  obtain ⟨har, hwfd, hwfo, hwires⟩ := moduleChecks_sound m hchk
  obtain ⟨hcomb, hdffs⟩ := htr
  have hcellseq : ((compileModuleM m).run {}).2.cells
      = ((m.outputs.foldlM compileOutput ([], [])).run
          ((m.regs.foldlM (dffStepR (regBusesOf m) rst m.clock) []).run
            (wireState m)).2).2.cells := by
    rw [compileModuleM_state_reset m rst hr]
  have hQstep : ∀ (t : Nat) (r : Reg), r ∈ m.regs →
      busValNat (τ (t + 1)) (qbusOf m r.name)
        = (if reset t then r.init.toNat
           else (eval r.next (evalWires m.wires
             (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))).toNat) := by
    intro t r hrm
    have hconsAll : ConsistentCells (τ t) ((m.outputs.foldlM compileOutput ([], [])).run
        ((m.regs.foldlM (dffStepR (regBusesOf m) rst m.clock) []).run
          (wireState m)).2).2.cells := by
      rw [← hcellseq]; exact hcomb t
    have hconsDffFold : ConsistentCells (τ t)
        ((m.regs.foldlM (dffStepR (regBusesOf m) rst m.clock) []).run (wireState m)).2.cells :=
      fun c hc => hconsAll c (compileOutputs_cells_sub m.outputs _ _ c hc)
    have hconsWire : ConsistentCells (τ t)
        ((m.wires.foldlM compileWire []).run (setupState m)).2.cells :=
      fun c hc => hconsDffFold c
        (compileDffsR_cells_sub (regBusesOf m) rst m.clock m.regs [] (wireState m) har c hc)
    have hce0 := setup_cenvOK_readout m hnd τ inputs t (hin t)
    have hcew : CEnvOK (τ t) (wireState m).env
        (evalWires m.wires (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name)))) :=
      compileWires_forces m.wires [] (setupState m) (τ t)
        (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))) hce0 hwires hconsWire
    obtain ⟨c, hcmem, hctype, hcQ, hcD⟩ :=
      compileDffs_forces_reset (regBusesOf m) rst m.clock
        (evalWires m.wires (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))
        m.regs [] (wireState m) (τ t) hwfd har hcew hconsDffFold r hrm
    have hlaw := hdffs c
      (by rw [hcellseq]; exact compileOutputs_cells_sub m.outputs _ _ c hcmem) hctype t
    obtain ⟨_, _, hqlen⟩ := regBus_lookup m hnd r hrm
    have hcQ' : conn c "Q" = qbusOf m r.name := hcQ
    rw [hcQ', hqlen] at hlaw
    have hcD' : busDen (τ t) r.width (conn c "D")
        = (if busDen (τ t) 1 (((wireState m).env.lookup rst).getD [Bit.zero]) = 1
           then r.init
           else eval r.next (evalWires m.wires
             (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))) := hcD
    rw [hrst t] at hcD'
    calc busValNat (τ (t + 1)) (qbusOf m r.name)
        = (busDen (τ (t + 1)) r.width (qbusOf m r.name)).toNat :=
          (busDen_toNat _ _ _ hqlen).symm
      _ = (busDen (τ t) r.width (conn c "D")).toNat := by rw [hlaw]
      _ = (if reset t then r.init.toNat
           else (eval r.next (evalWires m.wires
             (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))).toNat) := by
          rw [hcD']
          cases reset t <;> rfl
  have hstep : ∀ t, regReadout m τ (t + 1)
      = m.step (regReadout m τ t) (inputs t) (reset t) := by
    intro t
    funext n
    show (match m.regs.find? (·.name = n) with
          | some _ => busValNat (τ (t + 1)) (qbusOf m n)
          | none => 0)
        = (match m.regs.find? (·.name = n) with
          | some r => if reset t then r.init.toNat
                      else (eval r.next (evalWires m.wires
                        (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))).toNat
          | none => regReadout m τ t n)
    cases hf : m.regs.find? (·.name = n) with
    | none =>
      show (0 : Nat) = regReadout m τ t n
      unfold regReadout
      rw [hf]
    | some r =>
      have hrn : r.name = n := by simpa using List.find?_some hf
      have hrm : r ∈ m.regs := List.mem_of_find?_eq_some hf
      show busValNat (τ (t + 1)) (qbusOf m n)
          = if reset t then r.init.toNat
            else (eval r.next (evalWires m.wires
              (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))).toNat
      rw [← hrn]
      exact hQstep t r hrm
  have hinit' : regReadout m τ 0 = m.initRegs := by
    funext n
    show (match m.regs.find? (·.name = n) with
          | some _ => busValNat (τ 0) (qbusOf m n)
          | none => 0)
        = (match m.regs.find? (·.name = n) with
          | some r => r.init.toNat
          | none => 0)
    cases hf : m.regs.find? (·.name = n) with
    | none => rfl
    | some r =>
      have hrn : r.name = n := by simpa using List.find?_some hf
      have hrm : r ∈ m.regs := List.mem_of_find?_eq_some hf
      show busValNat (τ 0) (qbusOf m n) = r.init.toNat
      rw [← hrn]
      obtain ⟨_, _, hqlen⟩ := regBus_lookup m hnd r hrm
      rw [← busDen_toNat (τ 0) (qbusOf m r.name) r.width hqlen, hinit r hrm]
  intro t
  exact seq_register_correct m inputs reset (regReadout m τ)
    (fun t => m.step (regReadout m τ t) (inputs t) (reset t))
    hinit' hstep (fun _ => rfl) t

/-! ## Bus-level corollaries -/

/-- Bus form of the reset-free headline: each register's compiled `Q` bus denotes the
    denotational register trace at every cycle. -/
theorem netTrace_register_bus (m : Module) (hr : m.reset = none)
    (hchk : moduleChecksb m = true) (hnd : (m.regs.map (·.name)).Nodup)
    (τ : NetTrace) (inputs : Nat → Env)
    (htr : TraceConsistent τ ((compileModuleM m).run {}).2.cells)
    (hin : ∀ t, CEnvOK (τ t) (inputState m).env (inputs t))
    (hinit : ∀ r ∈ m.regs, busDen (τ 0) r.width (qbusOf m r.name) = r.init) :
    ∀ t, ∀ r ∈ m.regs, busDen (τ t) r.width (qbusOf m r.name)
      = (regTrace m inputs (fun _ => false) t).lookup r.name r.width := by
  intro t r hrm
  have h := netTrace_register_correct m hr hchk hnd τ inputs htr hin hinit t
  have hro : regReadout m τ t r.name = busValNat (τ t) (qbusOf m r.name) := by
    unfold regReadout
    cases hf : m.regs.find? (·.name = r.name) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp) (hf r hrm)
    | some r0 => rfl
  calc busDen (τ t) r.width (qbusOf m r.name)
      = BitVec.ofNat r.width (regReadout m τ t r.name) := by rw [hro]; rfl
    _ = Env.lookup (regReadout m τ t) r.name r.width := rfl
    _ = (regTrace m inputs (fun _ => false) t).lookup r.name r.width := by rw [h]

/-- Bus form of the sync-reset headline. -/
theorem netTrace_register_bus_reset (m : Module) (rst : String) (hr : m.reset = some rst)
    (hchk : moduleChecksb m = true) (hnd : (m.regs.map (·.name)).Nodup)
    (τ : NetTrace) (inputs : Nat → Env) (reset : Nat → Bool)
    (htr : TraceConsistent τ ((compileModuleM m).run {}).2.cells)
    (hin : ∀ t, CEnvOK (τ t) (inputState m).env (inputs t))
    (hrst : ∀ t, busDen (τ t) 1 (((wireState m).env.lookup rst).getD [Bit.zero])
      = if reset t then 1 else 0)
    (hinit : ∀ r ∈ m.regs, busDen (τ 0) r.width (qbusOf m r.name) = r.init) :
    ∀ t, ∀ r ∈ m.regs, busDen (τ t) r.width (qbusOf m r.name)
      = (regTrace m inputs reset t).lookup r.name r.width := by
  intro t r hrm
  have h := netTrace_register_correct_reset m rst hr hchk hnd τ inputs reset htr hin hrst hinit t
  have hro : regReadout m τ t r.name = busValNat (τ t) (qbusOf m r.name) := by
    unfold regReadout
    cases hf : m.regs.find? (·.name = r.name) with
    | none =>
      rw [List.find?_eq_none] at hf
      exact absurd (by simp) (hf r hrm)
    | some r0 => rfl
  calc busDen (τ t) r.width (qbusOf m r.name)
      = BitVec.ofNat r.width (regReadout m τ t r.name) := by rw [hro]; rfl
    _ = Env.lookup (regReadout m τ t) r.name r.width := rfl
    _ = (regTrace m inputs reset t).lookup r.name r.width := by rw [h]

/-! ## Output correctness

With the register trace pinned, the output phase's forcing lemma pins every output net to
`eval o.expr` over the *denotational* cycle environment at every cycle. -/

/-- **Temporal netlist correctness — outputs, reset-free.**  Every output port's net is forced
    (for the given trace, at every cycle) to denote `eval o.expr` over the wire-extended
    denotational cycle environment — the exact value `Module.outputs?eval` computes. -/
theorem netTrace_output_correct (m : Module) (hr : m.reset = none)
    (hchk : moduleChecksb m = true) (hnd : (m.regs.map (·.name)).Nodup)
    (τ : NetTrace) (inputs : Nat → Env)
    (htr : TraceConsistent τ ((compileModuleM m).run {}).2.cells)
    (hin : ∀ t, CEnvOK (τ t) (inputState m).env (inputs t))
    (hinit : ∀ r ∈ m.regs, busDen (τ 0) r.width (qbusOf m r.name) = r.init) :
    ∀ t, ∀ o ∈ m.outputs,
      ∃ port ∈ ((m.outputs.foldlM compileOutput ([], [])).run
          ((m.regs.foldlM (dffStep (regBusesOf m) m.clock) []).run (wireState m)).2).1.1,
        port.name = o.name ∧ port.dir = Dir.output ∧
        busDen (τ t) o.width port.bits
          = eval o.expr (evalWires m.wires
              (cycleEnv (regTrace m inputs (fun _ => false) t) (inputs t)
                (m.regs.map (·.name)))) := by
  intro t o ho
  obtain ⟨har, hwfd, hwfo, hwires⟩ := moduleChecks_sound m hchk
  have hcomb := htr.1
  have hconsAll : ConsistentCells (τ t) ((m.outputs.foldlM compileOutput ([], [])).run
      ((m.regs.foldlM (dffStep (regBusesOf m) m.clock) []).run (wireState m)).2).2.cells := by
    rw [← compileModuleM_state_noreset m hr]; exact hcomb t
  have hconsDffFold : ConsistentCells (τ t)
      ((m.regs.foldlM (dffStep (regBusesOf m) m.clock) []).run (wireState m)).2.cells :=
    fun c hc => hconsAll c (compileOutputs_cells_sub m.outputs _ _ c hc)
  have hconsWire : ConsistentCells (τ t)
      ((m.wires.foldlM compileWire []).run (setupState m)).2.cells :=
    fun c hc => hconsDffFold c
      (compileDffs_cells_sub (regBusesOf m) m.clock m.regs [] (wireState m) har c hc)
  have hce0 := setup_cenvOK_readout m hnd τ inputs t (hin t)
  have hcew : CEnvOK (τ t) (wireState m).env
      (evalWires m.wires (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name)))) :=
    compileWires_forces m.wires [] (setupState m) (τ t)
      (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))) hce0 hwires hconsWire
  have henvd : ((m.regs.foldlM (dffStep (regBusesOf m) m.clock) []).run (wireState m)).2.env
      = (wireState m).env := compileDffs_env (regBusesOf m) m.clock m.regs [] (wireState m) har
  have hwfo' : ∀ o' ∈ m.outputs, WidthOK
      ((m.regs.foldlM (dffStep (regBusesOf m) m.clock) []).run (wireState m)).2.env o'.expr := by
    rw [henvd]; exact hwfo
  have hcew' : CEnvOK (τ t)
      ((m.regs.foldlM (dffStep (regBusesOf m) m.clock) []).run (wireState m)).2.env
      (evalWires m.wires (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name)))) := by
    rw [henvd]; exact hcew
  have hport := compileOutputs_forces m.outputs
    (evalWires m.wires (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))
    ([], []) _ (τ t) hwfo' hcew' hconsAll o ho
  rw [netTrace_register_correct m hr hchk hnd τ inputs htr hin hinit t] at hport
  exact hport

/-- **Temporal netlist correctness — outputs, synchronous reset.** -/
theorem netTrace_output_correct_reset (m : Module) (rst : String) (hr : m.reset = some rst)
    (hchk : moduleChecksb m = true) (hnd : (m.regs.map (·.name)).Nodup)
    (τ : NetTrace) (inputs : Nat → Env) (reset : Nat → Bool)
    (htr : TraceConsistent τ ((compileModuleM m).run {}).2.cells)
    (hin : ∀ t, CEnvOK (τ t) (inputState m).env (inputs t))
    (hrst : ∀ t, busDen (τ t) 1 (((wireState m).env.lookup rst).getD [Bit.zero])
      = if reset t then 1 else 0)
    (hinit : ∀ r ∈ m.regs, busDen (τ 0) r.width (qbusOf m r.name) = r.init) :
    ∀ t, ∀ o ∈ m.outputs,
      ∃ port ∈ ((m.outputs.foldlM compileOutput ([], [])).run
          ((m.regs.foldlM (dffStepR (regBusesOf m) rst m.clock) []).run (wireState m)).2).1.1,
        port.name = o.name ∧ port.dir = Dir.output ∧
        busDen (τ t) o.width port.bits
          = eval o.expr (evalWires m.wires
              (cycleEnv (regTrace m inputs reset t) (inputs t) (m.regs.map (·.name)))) := by
  intro t o ho
  obtain ⟨har, hwfd, hwfo, hwires⟩ := moduleChecks_sound m hchk
  have hcomb := htr.1
  have hconsAll : ConsistentCells (τ t) ((m.outputs.foldlM compileOutput ([], [])).run
      ((m.regs.foldlM (dffStepR (regBusesOf m) rst m.clock) []).run
        (wireState m)).2).2.cells := by
    rw [← compileModuleM_state_reset m rst hr]; exact hcomb t
  have hconsDffFold : ConsistentCells (τ t)
      ((m.regs.foldlM (dffStepR (regBusesOf m) rst m.clock) []).run (wireState m)).2.cells :=
    fun c hc => hconsAll c (compileOutputs_cells_sub m.outputs _ _ c hc)
  have hconsWire : ConsistentCells (τ t)
      ((m.wires.foldlM compileWire []).run (setupState m)).2.cells :=
    fun c hc => hconsDffFold c
      (compileDffsR_cells_sub (regBusesOf m) rst m.clock m.regs [] (wireState m) har c hc)
  have hce0 := setup_cenvOK_readout m hnd τ inputs t (hin t)
  have hcew : CEnvOK (τ t) (wireState m).env
      (evalWires m.wires (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name)))) :=
    compileWires_forces m.wires [] (setupState m) (τ t)
      (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))) hce0 hwires hconsWire
  have henvd : ((m.regs.foldlM (dffStepR (regBusesOf m) rst m.clock) []).run
      (wireState m)).2.env = (wireState m).env :=
    compileDffsR_env (regBusesOf m) rst m.clock m.regs [] (wireState m) har
  have hwfo' : ∀ o' ∈ m.outputs, WidthOK
      ((m.regs.foldlM (dffStepR (regBusesOf m) rst m.clock) []).run
        (wireState m)).2.env o'.expr := by
    rw [henvd]; exact hwfo
  have hcew' : CEnvOK (τ t)
      ((m.regs.foldlM (dffStepR (regBusesOf m) rst m.clock) []).run (wireState m)).2.env
      (evalWires m.wires (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name)))) := by
    rw [henvd]; exact hcew
  have hport := compileOutputs_forces m.outputs
    (evalWires m.wires (cycleEnv (regReadout m τ t) (inputs t) (m.regs.map (·.name))))
    ([], []) _ (τ t) hwfo' hcew' hconsAll o ho
  rw [netTrace_register_correct_reset m rst hr hchk hnd τ inputs reset htr
      hin hrst hinit t] at hport
  exact hport

end LeanRTL.NetTrace
