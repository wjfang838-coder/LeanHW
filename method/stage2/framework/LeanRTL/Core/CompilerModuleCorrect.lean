import LeanRTL.Core.CompilerCorrect
/-!
# Module-fold structural lemmas (M6b, step 1)

Foundational facts about the `foldlM` phase helpers of `compileModuleM` (`compileInput`,
`compileReg`).  These characterise how the input/register setup phases grow the net id counter,
the environment, and (crucially) leave the emitted-cell list untouched — the scaffolding the
module-fold soundness proof builds on.
-/

namespace LeanRTL.CompilerModuleCorrect

open LeanRTL LeanRTL.Backend LeanRTL.BackendSem LeanRTL.CompilerCorrect

/-- Extending the bus environment by a binding that denotes the right value preserves `CEnvOK`. -/
theorem CEnvOK_cons {σ : Nat → Bool} {name : String} {bus : Bus} {cenv : List (String × Bus)}
    {vals : Env} (hbus : busDen σ bus.length bus = vals.lookup name bus.length)
    (h : CEnvOK σ cenv vals) : CEnvOK σ ((name, bus) :: cenv) vals := by
  intro n b hl
  rw [List.lookup_cons] at hl
  split at hl
  · rename_i heq
    cases hl
    have hn : n = name := by simpa using heq
    subst hn; exact hbus
  · exact h n b hl

/-- Extending the bus environment *and* the value environment by one wire binding (whose bus
    denotes the wire's value) preserves `CEnvOK`.  Used for the wire phase, where `evalWires` grows
    the value environment as each wire binds. -/
theorem CEnvOK_cons_wire {σ : Nat → Bool} {name : String} {bus : Bus}
    {cenv : List (String × Bus)} {vals : Env} {newval : Nat}
    (hbus : busDen σ bus.length bus = BitVec.ofNat bus.length newval) (h : CEnvOK σ cenv vals) :
    CEnvOK σ ((name, bus) :: cenv) (fun n => if n = name then newval else vals n) := by
  intro n b hl
  rw [List.lookup_cons] at hl
  split at hl
  · rename_i heq
    cases hl
    have hn : n = name := by simpa using heq
    subst hn
    simp only [Env.lookup, ↓reduceIte]
    exact hbus
  · have hn' : n ≠ name := by
      rename_i hne; intro hc; subst hc; simp at hne
    have heq2 : Env.lookup (fun n' => if n' = name then newval else vals n') n b.length
        = Env.lookup vals n b.length := by simp only [Env.lookup, if_neg hn']
    rw [heq2]; exact h n b hl

/-- Prepending a bounded binding preserves `EnvBounded`. -/
theorem EnvBounded_cons {name : String} {bus : Bus} {env : List (String × Bus)} {n : Nat}
    (hbus : BusBelow n bus) (henv : EnvBounded env n) : EnvBounded ((name, bus) :: env) n := by
  intro name' bus' h
  rw [List.lookup_cons] at h
  split at h
  · cases h; exact hbus
  · exact henv name' bus' h

theorem compileInput_env (acc : List Port × List NetName) (p : InPort) (s : CState) :
    ((compileInput acc p).run s).2.env = (p.name, freshBus s p.width) :: s.env := rfl
theorem compileInput_nextId (acc : List Port × List NetName) (p : InPort) (s : CState) :
    ((compileInput acc p).run s).2.nextId = s.nextId + p.width := rfl

/-- For any value assignment, the input phase admits a net valuation realizing it (`CEnvOK`),
    extending any base valuation below the starting id. -/
theorem compileInputs_sigma (vals : Env) : ∀ (inputs : List InPort)
    (acc : List Port × List NetName) (s : CState) (σbase : Nat → Bool),
    EnvBounded s.env s.nextId → CEnvOK σbase s.env vals →
    ∃ σ, (∀ k, k < s.nextId → σ k = σbase k) ∧
      CEnvOK σ ((inputs.foldlM compileInput acc).run s).2.env vals := by
  intro inputs
  induction inputs with
  | nil => intro acc s σbase _ hc; exact ⟨σbase, fun _ _ => rfl, hc⟩
  | cons p ps ih =>
    intro acc s σbase hbnd hc
    have hσ1 : ∀ k, k < s.nextId →
        setRange σbase s.nextId p.width (vals.lookup p.name p.width) k = σbase k :=
      fun k hk => setRange_lt σbase s.nextId p.width _ k hk
    have hc1 : CEnvOK (setRange σbase s.nextId p.width (vals.lookup p.name p.width))
        ((compileInput acc p).run s).2.env vals := by
      rw [compileInput_env]
      refine CEnvOK_cons ?_ (CEnvOK_frame hbnd (fun k hk => (hσ1 k hk).symm) hc)
      have hl : (freshBus s p.width).length = p.width := by simp [freshBus]
      rw [hl]
      simpa [freshBus] using setRange_get σbase s.nextId p.width (vals.lookup p.name p.width)
    have hbnd1 : EnvBounded ((compileInput acc p).run s).2.env
        ((compileInput acc p).run s).2.nextId := by
      rw [compileInput_env, compileInput_nextId]
      exact EnvBounded_cons (BusBelow_freshBus s p.width) (EnvBounded_mono hbnd (Nat.le_add_right _ _))
    obtain ⟨σ, hext, hcfinal⟩ := ih ((compileInput acc p).run s).1 ((compileInput acc p).run s).2
      (setRange σbase s.nextId p.width (vals.lookup p.name p.width)) hbnd1 hc1
    refine ⟨σ, ?_, ?_⟩
    · intro k hk
      rw [hext k (by rw [compileInput_nextId]; exact Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)),
          hσ1 k hk]
    · rw [List.foldlM_cons]
      show CEnvOK σ ((ps.foldlM compileInput _).run ((compileInput acc p).run s).2).2.env vals
      exact hcfinal

/-- The input phase keeps the environment bounded by the (advanced) id counter. -/
theorem compileInputs_envBounded (inputs : List InPort) (acc : List Port × List NetName)
    (s : CState) (h : EnvBounded s.env s.nextId) :
    EnvBounded ((inputs.foldlM compileInput acc).run s).2.env
      ((inputs.foldlM compileInput acc).run s).2.nextId := by
  induction inputs generalizing acc s with
  | nil => exact h
  | cons p ps ih =>
    rw [List.foldlM_cons]
    show EnvBounded ((ps.foldlM compileInput _).run ((compileInput acc p).run s).2).2.env
      ((ps.foldlM compileInput _).run ((compileInput acc p).run s).2).2.nextId
    refine ih _ ((compileInput acc p).run s).2 ?_
    -- after one input: env = (p.name, freshBus s p.width) :: s.env, nextId = s.nextId + p.width
    refine EnvBounded_cons (BusBelow_freshBus s p.width) ?_
    exact EnvBounded_mono h (Nat.le_add_right _ _)

/-- The input phase emits no cells. -/
theorem compileInputs_cells (inputs : List InPort) (acc : List Port × List NetName) (s : CState) :
    ((inputs.foldlM compileInput acc).run s).2.cells = s.cells := by
  induction inputs generalizing acc s with
  | nil => rfl
  | cons p ps ih =>
    rw [List.foldlM_cons]
    show ((ps.foldlM compileInput _).run ((compileInput acc p).run s).2).2.cells = s.cells
    rw [ih]
    rfl

/-- The input phase advances the id counter by the total input width, monotonically. -/
theorem compileInputs_nextId_le (inputs : List InPort) (acc : List Port × List NetName)
    (s : CState) : s.nextId ≤ ((inputs.foldlM compileInput acc).run s).2.nextId := by
  induction inputs generalizing acc s with
  | nil => exact Nat.le_refl _
  | cons p ps ih =>
    rw [List.foldlM_cons]
    show s.nextId ≤ ((ps.foldlM compileInput _).run ((compileInput acc p).run s).2).2.nextId
    exact Nat.le_trans (Nat.le_add_right s.nextId p.width)
      (ih _ ((compileInput acc p).run s).2)

/-- The register phase keeps the environment bounded by the (advanced) id counter. -/
theorem compileRegs_envBounded (regs : List Reg) (acc : List (String × Bus) × List NetName)
    (s : CState) (h : EnvBounded s.env s.nextId) :
    EnvBounded ((regs.foldlM compileReg acc).run s).2.env
      ((regs.foldlM compileReg acc).run s).2.nextId := by
  induction regs generalizing acc s with
  | nil => exact h
  | cons r rs ih =>
    rw [List.foldlM_cons]
    show EnvBounded ((rs.foldlM compileReg _).run ((compileReg acc r).run s).2).2.env
      ((rs.foldlM compileReg _).run ((compileReg acc r).run s).2).2.nextId
    refine ih _ ((compileReg acc r).run s).2 ?_
    refine EnvBounded_cons (BusBelow_freshBus s r.width) ?_
    exact EnvBounded_mono h (Nat.le_add_right _ _)

/-- The register binding one `compileReg` appends. -/
theorem compileReg_acc (acc : List (String × Bus) × List NetName) (r : Reg) (s : CState) :
    ((compileReg acc r).run s).1.1 = acc.1 ++ [(r.name, freshBus s r.width)] := rfl

theorem compileReg_env (acc : List (String × Bus) × List NetName) (r : Reg) (s : CState) :
    ((compileReg acc r).run s).2.env = (r.name, freshBus s r.width) :: s.env := rfl
theorem compileReg_nextId (acc : List (String × Bus) × List NetName) (r : Reg) (s : CState) :
    ((compileReg acc r).run s).2.nextId = s.nextId + r.width := rfl

/-- For any value assignment, the register phase admits a net valuation realizing it. -/
theorem compileRegs_sigma (vals : Env) : ∀ (regs : List Reg)
    (acc : List (String × Bus) × List NetName) (s : CState) (σbase : Nat → Bool),
    EnvBounded s.env s.nextId → CEnvOK σbase s.env vals →
    ∃ σ, (∀ k, k < s.nextId → σ k = σbase k) ∧
      CEnvOK σ ((regs.foldlM compileReg acc).run s).2.env vals := by
  intro regs
  induction regs with
  | nil => intro acc s σbase _ hc; exact ⟨σbase, fun _ _ => rfl, hc⟩
  | cons r rs ih =>
    intro acc s σbase hbnd hc
    have hσ1 : ∀ k, k < s.nextId →
        setRange σbase s.nextId r.width (vals.lookup r.name r.width) k = σbase k :=
      fun k hk => setRange_lt σbase s.nextId r.width _ k hk
    have hc1 : CEnvOK (setRange σbase s.nextId r.width (vals.lookup r.name r.width))
        ((compileReg acc r).run s).2.env vals := by
      rw [compileReg_env]
      refine CEnvOK_cons ?_ (CEnvOK_frame hbnd (fun k hk => (hσ1 k hk).symm) hc)
      have hl : (freshBus s r.width).length = r.width := by simp [freshBus]
      rw [hl]
      simpa [freshBus] using setRange_get σbase s.nextId r.width (vals.lookup r.name r.width)
    have hbnd1 : EnvBounded ((compileReg acc r).run s).2.env
        ((compileReg acc r).run s).2.nextId := by
      rw [compileReg_env, compileReg_nextId]
      exact EnvBounded_cons (BusBelow_freshBus s r.width) (EnvBounded_mono hbnd (Nat.le_add_right _ _))
    obtain ⟨σ, hext, hcfinal⟩ := ih ((compileReg acc r).run s).1 ((compileReg acc r).run s).2
      (setRange σbase s.nextId r.width (vals.lookup r.name r.width)) hbnd1 hc1
    refine ⟨σ, ?_, ?_⟩
    · intro k hk
      rw [hext k (by rw [compileReg_nextId]; exact Nat.lt_of_lt_of_le hk (Nat.le_add_right _ _)),
          hσ1 k hk]
    · rw [List.foldlM_cons]
      show CEnvOK σ ((rs.foldlM compileReg _).run ((compileReg acc r).run s).2).2.env vals
      exact hcfinal

/-- Every register bus produced by the register phase is bounded by the (advanced) id counter. -/
theorem compileRegs_regBuses_below (regs : List Reg) (acc : List (String × Bus) × List NetName)
    (s : CState) (h : ∀ p ∈ acc.1, BusBelow s.nextId p.2) :
    ∀ p ∈ ((regs.foldlM compileReg acc).run s).1.1,
      BusBelow ((regs.foldlM compileReg acc).run s).2.nextId p.2 := by
  induction regs generalizing acc s with
  | nil => intro p hp; exact h p hp
  | cons r rs ih =>
    rw [List.foldlM_cons]
    show ∀ p ∈ ((rs.foldlM compileReg _).run ((compileReg acc r).run s).2).1.1,
      BusBelow ((rs.foldlM compileReg _).run ((compileReg acc r).run s).2).2.nextId p.2
    refine ih _ ((compileReg acc r).run s).2 ?_
    intro p hp
    rcases List.mem_append.1 hp with hp' | hp'
    · exact BusBelow_mono (h p hp') (Nat.le_add_right _ _)
    · simp only [List.mem_singleton] at hp'; subst hp'; exact BusBelow_freshBus s r.width

/-- The empty environment is vacuously bounded. -/
theorem EnvBounded_nil (n : Nat) : EnvBounded [] n := by
  intro name bus h; simp [List.lookup] at h

/-- The post-setup state (inputs then registers, from the initial empty compiler state) has a
    bounded environment. -/
theorem setup_envBounded (m : Module) :
    EnvBounded ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env
      ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.nextId :=
  compileRegs_envBounded _ _ _ (compileInputs_envBounded _ _ _ (EnvBounded_nil _))

/-- **Full setup drive.** For any value assignment `vals`, the post-setup (inputs+registers)
    environment admits a net valuation realizing it (`CEnvOK`) — combining the input and register
    drives.  This discharges the interface hypothesis of `compileModule_comb_sound` for any cycle's
    input/register values. -/
theorem setup_sigma (m : Module) (vals : Env) :
    ∃ σ, CEnvOK σ ((m.regs.foldlM compileReg ([], [])).run
      ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env vals := by
  obtain ⟨σ1, _, hc1⟩ := compileInputs_sigma vals m.inputs ([], []) {} (fun _ => false)
    (EnvBounded_nil _) (by intro n b h; simp [List.lookup] at h)
  obtain ⟨σ, _, hc⟩ := compileRegs_sigma vals m.regs ([], [])
    ((m.inputs.foldlM compileInput ([], [])).run {}).2 σ1
    (compileInputs_envBounded m.inputs ([], []) {} (EnvBounded_nil _)) hc1
  exact ⟨σ, hc⟩

/-- A register-bus lookup into a bounded list is bounded (default `[]` has no nets). -/
theorem BusBelow_regBuses_lookup (n : Nat) (name : String) :
    ∀ (regBuses : List (String × Bus)), (∀ p ∈ regBuses, BusBelow n p.2) →
      BusBelow n ((regBuses.lookup name).getD []) := by
  intro regBuses
  induction regBuses with
  | nil => intro _ j hj; simp [List.lookup] at hj
  | cons p ps ih =>
    intro h
    rw [List.lookup_cons]
    split
    · exact h p (List.mem_cons_self ..)
    · exact ih (fun q hq => h q (List.mem_cons_of_mem p hq))

/-- The register phase emits no cells. -/
theorem compileRegs_cells (regs : List Reg) (acc : List (String × Bus) × List NetName)
    (s : CState) : ((regs.foldlM compileReg acc).run s).2.cells = s.cells := by
  induction regs generalizing acc s with
  | nil => rfl
  | cons r rs ih =>
    rw [List.foldlM_cons]
    show ((rs.foldlM compileReg _).run ((compileReg acc r).run s).2).2.cells = s.cells
    rw [ih]
    rfl

/-- The register phase advances the id counter monotonically. -/
theorem compileRegs_nextId_le (regs : List Reg) (acc : List (String × Bus) × List NetName)
    (s : CState) : s.nextId ≤ ((regs.foldlM compileReg acc).run s).2.nextId := by
  induction regs generalizing acc s with
  | nil => exact Nat.le_refl _
  | cons r rs ih =>
    rw [List.foldlM_cons]
    show s.nextId ≤ ((rs.foldlM compileReg _).run ((compileReg acc r).run s).2).2.nextId
    exact Nat.le_trans (Nat.le_add_right s.nextId r.width)
      (ih _ ((compileReg acc r).run s).2)

/-! ## Single-phase soundness (one wire / one output)

These reduce the per-element phase actions to `sound` (M6a): compiling one output or one wire is,
on the emitted cells, exactly compiling its expression — the surrounding `pure`/`modify` only
touch the accumulator and the name→bus environment. -/

/-- `compileOutput` changes the compiler state exactly as compiling its expression does. -/
theorem compileOutput_state (acc : List Port × List NetName) (o : OutPort) (s : CState) :
    ((compileOutput acc o).run s).2 = ((compileExpr o.expr).run s).2 := rfl

/-- Soundness of one output port: there is a valuation under which the emitted cells hold and the
    output bus denotes `eval o.expr`. -/
theorem compileOutput_sound (acc : List Port × List NetName) (o : OutPort) (env : Env)
    (s : CState) (σ₀ : Nat → Bool)
    (hwf : WidthOK s.env o.expr) (hmem : CEnvOK σ₀ s.env env) (hbnd : EnvBounded s.env s.nextId)
    (hcons : ConsistentCells σ₀ s.cells) (hcb : CellsBounded s.cells s.nextId) :
    ∃ σ, (∀ k, k < s.nextId → σ k = σ₀ k) ∧
      ConsistentCells σ ((compileOutput acc o).run s).2.cells ∧
      CellsBounded ((compileOutput acc o).run s).2.cells ((compileOutput acc o).run s).2.nextId ∧
      BusBelow ((compileExpr o.expr).run s).2.nextId ((compileExpr o.expr).run s).1 ∧
      s.nextId ≤ ((compileOutput acc o).run s).2.nextId ∧
      ((compileOutput acc o).run s).2.env = s.env ∧
      busDen σ o.width ((compileExpr o.expr).run s).1 = eval o.expr env := by
  obtain ⟨σ, hext, hcc, hcbd, hbb, hmono, henv, hval⟩ :=
    sound o.expr env (supp_all o.expr) s σ₀ hwf hmem hbnd hcons hcb
  refine ⟨σ, hext, ?_, ?_, hbb, ?_, ?_, hval⟩
  · rw [compileOutput_state]; exact hcc
  · rw [compileOutput_state]; exact hcbd
  · rw [compileOutput_state]; exact hmono
  · rw [compileOutput_state]; exact henv

/-- `compileWire`'s state effect: same cells/id as its expression, with the wire bound by name. -/
theorem compileWire_state_cells (acc : List NetName) (w : Wire) (s : CState) :
    ((compileWire acc w).run s).2.cells = ((compileExpr w.expr).run s).2.cells := rfl
theorem compileWire_state_nextId (acc : List NetName) (w : Wire) (s : CState) :
    ((compileWire acc w).run s).2.nextId = ((compileExpr w.expr).run s).2.nextId := rfl
theorem compileWire_state_env (acc : List NetName) (w : Wire) (s : CState) :
    ((compileWire acc w).run s).2.env
      = (w.name, ((compileExpr w.expr).run s).1) :: ((compileExpr w.expr).run s).2.env := rfl

/-- The port a single `compileOutput` appends. -/
theorem compileOutput_acc (acc : List Port × List NetName) (o : OutPort) (s : CState) :
    ((compileOutput acc o).run s).1.1
      = acc.1 ++ [{ name := o.name, dir := .output, bits := ((compileExpr o.expr).run s).1 }] := rfl

/-- The output fold only appends to the port accumulator: the prior ports remain a prefix. -/
theorem compileOutputs_acc_prefix (outputs : List OutPort) (acc : List Port × List NetName)
    (s : CState) : ∃ extra, ((outputs.foldlM compileOutput acc).run s).1.1 = acc.1 ++ extra := by
  induction outputs generalizing acc s with
  | nil => exact ⟨[], by simp⟩
  | cons o os ih =>
    obtain ⟨extra, hextra⟩ :=
      ih ((compileOutput acc o).run s).1 ((compileOutput acc o).run s).2
    refine ⟨{ name := o.name, dir := .output, bits := ((compileExpr o.expr).run s).1 } :: extra, ?_⟩
    rw [List.foldlM_cons]
    show ((os.foldlM compileOutput ((compileOutput acc o).run s).1).run
            ((compileOutput acc o).run s).2).1.1 = _
    rw [hextra, compileOutput_acc]
    simp

/-! ## Output-phase fold soundness

Composing `compileOutput_sound` across the whole output list: there is a single valuation `σ`
under which *every* emitted output cell holds and each output port's bus denotes `eval`, with `σ`
extending the input/register valuation.  This is the combinational core of module-fold soundness. -/

theorem compileOutputs_sound (outputs : List OutPort) (env : Env)
    (acc : List Port × List NetName) :
    ∀ (s : CState) (σ₀ : Nat → Bool),
      (∀ o ∈ outputs, WidthOK s.env o.expr) →
      CEnvOK σ₀ s.env env → EnvBounded s.env s.nextId →
      ConsistentCells σ₀ s.cells → CellsBounded s.cells s.nextId →
      ∃ σ, (∀ k, k < s.nextId → σ k = σ₀ k) ∧
        ConsistentCells σ ((outputs.foldlM compileOutput acc).run s).2.cells ∧
        CellsBounded ((outputs.foldlM compileOutput acc).run s).2.cells
          ((outputs.foldlM compileOutput acc).run s).2.nextId ∧
        s.nextId ≤ ((outputs.foldlM compileOutput acc).run s).2.nextId ∧
        ((outputs.foldlM compileOutput acc).run s).2.env = s.env ∧
        ∀ o ∈ outputs, ∃ port ∈ ((outputs.foldlM compileOutput acc).run s).1.1,
          port.name = o.name ∧ port.dir = Dir.output ∧
          busDen σ o.width port.bits = eval o.expr env := by
  induction outputs generalizing acc with
  | nil =>
    intro s σ₀ _ _ _ hcons hcb
    refine ⟨σ₀, fun _ _ => rfl, hcons, hcb, Nat.le_refl _, rfl, ?_⟩
    intro o ho; simp at ho
  | cons o os ih =>
    intro s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨σ1, hext1, hcc1, hcbd1, hbb1, hmono1, henv1, hval1⟩ :=
      compileOutput_sound acc o env s σ₀ (hwf o (List.mem_cons_self ..)) hmem hbnd hcons hcb
    have hmemb : CEnvOK σ1 ((compileOutput acc o).run s).2.env env := by
      rw [henv1]; exact CEnvOK_frame hbnd (fun k hk => (hext1 k hk).symm) hmem
    have hbndb : EnvBounded ((compileOutput acc o).run s).2.env
        ((compileOutput acc o).run s).2.nextId := by
      rw [henv1]; exact EnvBounded_mono hbnd hmono1
    have hwfb : ∀ o' ∈ os, WidthOK ((compileOutput acc o).run s).2.env o'.expr := by
      rw [henv1]; exact fun o' ho' => hwf o' (List.mem_cons_of_mem o ho')
    obtain ⟨σ2, hext2, hcc2, hcbd2, hmono2, henv2, hvals2⟩ :=
      ih ((compileOutput acc o).run s).1 ((compileOutput acc o).run s).2 σ1
        hwfb hmemb hbndb hcc1 hcbd1
    -- o's own port persists into the final accumulator, and its value frames up to σ2
    have hport_o : { name := o.name, dir := Dir.output, bits := ((compileExpr o.expr).run s).1 } ∈
        ((os.foldlM compileOutput ((compileOutput acc o).run s).1).run
          ((compileOutput acc o).run s).2).1.1 := by
      obtain ⟨extra, hextra⟩ := compileOutputs_acc_prefix os ((compileOutput acc o).run s).1
        ((compileOutput acc o).run s).2
      rw [hextra, compileOutput_acc]
      simp
    have hvalo : busDen σ2 o.width ((compileExpr o.expr).run s).1 = eval o.expr env := by
      rw [busDen_frame σ2 σ1 o.width ((compileExpr o.expr).run s).1
            ((compileExpr o.expr).run s).2.nextId hbb1 hext2]
      exact hval1
    refine ⟨σ2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [hext2 k (Nat.lt_of_lt_of_le hk hmono1), hext1 k hk]
    all_goals rw [List.foldlM_cons]; simp only [run_bind]
    · exact hcc2
    · exact hcbd2
    · exact Nat.le_trans hmono1 hmono2
    · rw [henv2, henv1]
    · intro o' ho'
      rcases List.mem_cons.1 ho' with rfl | ho''
      · exact ⟨_, hport_o, rfl, rfl, hvalo⟩
      · exact hvals2 o' ho''

/-! ## DFF-phase soundness (reset-free)

The flip-flop is combinationally vacuous (`cellHolds` of a `$dff` is `True`); its temporal meaning
is carried by `seq_register_correct`.  So the dff phase's only combinational content is the
next-state cone `compileExpr r.next`, which `sound` already proves correct. -/

/-- Any `$dff` cell is satisfied by every valuation. -/
theorem cellHolds_dff (σ : Nat → Bool) (c : Cell) (h : c.type = "$dff") : cellHolds σ c := by
  unfold cellHolds; rw [h]; trivial

/-- **Bridge: for a register with no async reset, `compileDff` is the synchronous body.**  This is
    the single rewrite the M6 proofs use to reduce the new `match r.asyncReset` to the pre-existing
    `$dff` emission `compileDffSync`; every structural / soundness lemma below threads it as the
    hypothesis `r.asyncReset = none`. -/
theorem compileDff_sync_eq (regBuses : List (String × Bus)) (reset clock : Option String) (r : Reg)
    (har : r.asyncReset = none) :
    compileDff regBuses reset clock r = compileDffSync regBuses reset clock r := by
  simp only [compileDff, har]

/-- For a reset-free register, `compileDff` returns the next-state bus and prepends one `$dff`
    cell to the next-state cone's cells. -/
theorem compileDff_noreset_fst (regBuses : List (String × Bus)) (clock : Option String) (r : Reg)
    (s : CState) (har : r.asyncReset = none) :
    ((compileDff regBuses none clock r).run s).1 = ((compileExpr r.next).run s).1 := by
  rw [compileDff_sync_eq regBuses none clock r har]; rfl

theorem compileDff_noreset_nextId (regBuses : List (String × Bus)) (clock : Option String)
    (r : Reg) (s : CState) (har : r.asyncReset = none) :
    ((compileDff regBuses none clock r).run s).2.nextId = ((compileExpr r.next).run s).2.nextId := by
  rw [compileDff_sync_eq regBuses none clock r har]; rfl

theorem compileDff_noreset_env (regBuses : List (String × Bus)) (clock : Option String) (r : Reg)
    (s : CState) (har : r.asyncReset = none) :
    ((compileDff regBuses none clock r).run s).2.env = ((compileExpr r.next).run s).2.env := by
  rw [compileDff_sync_eq regBuses none clock r har]; rfl

/-- The clock bus selected for a register's `$dff` (a 1-bit env signal, or constant zero). -/
def clkBusOf (clock : Option String) (env : List (String × Bus)) : Bus :=
  match clock with | some c => (env.lookup c).getD [Bit.zero] | none => [Bit.zero]

/-- The exact `$dff` cell `compileDff` (reset-free) emits.  `pol` is the `CLK_POLARITY` value
    (`if r.negedge then 0 else 1`); it flows only into the string parameters, so every soundness /
    boundedness lemma below is independent of it. -/
def dffCell (cnt pol w : Nat) (clkBus dbus qbus : Bus) : Cell :=
  { name := s!"$auto{cnt}", type := "$dff",
    parameters := [("CLK_POLARITY", binStr32 pol), ("WIDTH", binStr32 w)],
    portDirections := [("CLK", Dir.input), ("D", Dir.input), ("Q", Dir.output)],
    connections := [("CLK", clkBus), ("D", dbus), ("Q", qbus)], hideName := true }

theorem compileDff_noreset_cells (regBuses : List (String × Bus)) (clock : Option String) (r : Reg)
    (s : CState) (har : r.asyncReset = none) :
    ((compileDff regBuses none clock r).run s).2.cells
      = dffCell ((compileExpr r.next).run s).2.count (if r.negedge then 0 else 1) r.width
          (clkBusOf clock ((compileExpr r.next).run s).2.env)
          ((compileExpr r.next).run s).1 ((regBuses.lookup r.name).getD [])
        :: ((compileExpr r.next).run s).2.cells := by
  rw [compileDff_sync_eq regBuses none clock r har]; rfl

theorem CellBelow_dffCell {m cnt pol w clkBus dbus qbus} (hclk : BusBelow m clkBus)
    (hd : BusBelow m dbus) (hq : BusBelow m qbus) : CellBelow m (dffCell cnt pol w clkBus dbus qbus) := by
  intro k b hmem
  simp only [dffCell, List.mem_cons, List.not_mem_nil, or_false, Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption

/-- A name-lookup into a bounded environment yields a bounded bus (the default `[zero]`/`[]` has
    no nets). -/
theorem BusBelow_lookup_getD {env : List (String × Bus)} {n : Nat} (henv : EnvBounded env n)
    (name : String) (d : Bus) (hd : BusBelow n d) : BusBelow n ((env.lookup name).getD d) := by
  cases h : env.lookup name with
  | none => simpa [h] using hd
  | some bus => simpa [h] using henv name bus h

theorem BusBelow_clkBusOf {env : List (String × Bus)} {n : Nat} (henv : EnvBounded env n)
    (clock : Option String) : BusBelow n (clkBusOf clock env) := by
  cases clock with
  | none => intro j hj; simp [clkBusOf] at hj
  | some c =>
    refine BusBelow_lookup_getD henv c [Bit.zero] ?_
    intro j hj; simp at hj

/-- Soundness of one reset-free register's dff phase: a valuation under which all emitted cells
    (next-state cone + `$dff`) hold and the returned D-bus denotes `eval r.next`. -/
theorem compileDff_sound_noreset (regBuses : List (String × Bus)) (clock : Option String) (r : Reg)
    (env : Env) (s : CState) (σ₀ : Nat → Bool)
    (hwf : WidthOK s.env r.next) (hmem : CEnvOK σ₀ s.env env) (hbnd : EnvBounded s.env s.nextId)
    (hq : BusBelow s.nextId ((regBuses.lookup r.name).getD []))
    (hcons : ConsistentCells σ₀ s.cells) (hcb : CellsBounded s.cells s.nextId)
    (har : r.asyncReset = none) :
    ∃ σ, (∀ k, k < s.nextId → σ k = σ₀ k) ∧
      ConsistentCells σ ((compileDff regBuses none clock r).run s).2.cells ∧
      CellsBounded ((compileDff regBuses none clock r).run s).2.cells
        ((compileDff regBuses none clock r).run s).2.nextId ∧
      s.nextId ≤ ((compileDff regBuses none clock r).run s).2.nextId ∧
      ((compileDff regBuses none clock r).run s).2.env = s.env ∧
      busDen σ r.width ((compileDff regBuses none clock r).run s).1 = eval r.next env ∧
      BusBelow ((compileExpr r.next).run s).2.nextId ((compileExpr r.next).run s).1 := by
  obtain ⟨σ, hext, hcc, hcbd, hbb, hmono, henv, hval⟩ :=
    sound r.next env (supp_all r.next) s σ₀ hwf hmem hbnd hcons hcb
  refine ⟨σ, hext, ?_, ?_, ?_, ?_, ?_, hbb⟩
  · -- ConsistentCells: $dff (vacuous) :: next-state cells
    rw [compileDff_noreset_cells (har := har)]
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact cellHolds_dff σ _ rfl
    · exact hcc c hc
  · -- CellsBounded: bound the $dff cell + the next-state cells
    rw [compileDff_noreset_cells (har := har), compileDff_noreset_nextId (har := har)]
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · refine CellBelow_dffCell ?_ hbb ?_
      · rw [henv]; exact BusBelow_mono (BusBelow_clkBusOf hbnd clock) hmono
      · exact BusBelow_mono hq hmono
    · exact hcbd c hc
  · rw [compileDff_noreset_nextId (har := har)]; exact hmono
  · rw [compileDff_noreset_env (har := har)]; exact henv
  · rw [compileDff_noreset_fst (har := har)]; exact hval

/-! ### Synchronous-reset dff (the `$mux`-based reset variant)

With `m.reset = some rst`, `compileDff` wraps the next-state cone in a `$mux` (`D' = reset ? init :
next`) before the `$dff`.  The mux is exactly the `muxCell` proven correct in `sound`'s `.mux` case,
so the same `setRange` σ-construction applies: the returned D-bus denotes `reset ? init : next` =
`Module.step` with synchronous reset. -/

theorem compileDff_reset_fst (regBuses : List (String × Bus)) (clock : Option String) (rst : String)
    (r : Reg) (s : CState) (har : r.asyncReset = none) :
    ((compileDff regBuses (some rst) clock r).run s).1
      = freshBus ((compileExpr r.next).run s).2 r.width := by
  rw [compileDff_sync_eq regBuses (some rst) clock r har]; rfl
theorem compileDff_reset_env (regBuses : List (String × Bus)) (clock : Option String) (rst : String)
    (r : Reg) (s : CState) (har : r.asyncReset = none) :
    ((compileDff regBuses (some rst) clock r).run s).2.env
      = ((compileExpr r.next).run s).2.env := by
  rw [compileDff_sync_eq regBuses (some rst) clock r har]; rfl
theorem compileDff_reset_nextId (regBuses : List (String × Bus)) (clock : Option String)
    (rst : String) (r : Reg) (s : CState) (har : r.asyncReset = none) :
    ((compileDff regBuses (some rst) clock r).run s).2.nextId
      = ((compileExpr r.next).run s).2.nextId + r.width := by
  rw [compileDff_sync_eq regBuses (some rst) clock r har]; rfl
theorem compileDff_reset_cells (regBuses : List (String × Bus)) (clock : Option String)
    (rst : String) (r : Reg) (s : CState) (har : r.asyncReset = none) :
    ((compileDff regBuses (some rst) clock r).run s).2.cells
      = dffCell (((compileExpr r.next).run s).2.count + 1) (if r.negedge then 0 else 1) r.width
            (clkBusOf clock ((compileExpr r.next).run s).2.env)
            (freshBus ((compileExpr r.next).run s).2 r.width)
            ((regBuses.lookup r.name).getD [])
        :: muxCell ((compileExpr r.next).run s).2 r.width
            ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero])
            (constBits r.init) ((compileExpr r.next).run s).1
        :: ((compileExpr r.next).run s).2.cells := by
  rw [compileDff_sync_eq regBuses (some rst) clock r har]; rfl

/-- A constant bus has no net bits, so it is bounded by any id counter. -/
theorem BusBelow_constBits {w : Nat} (v : BitVec w) (n : Nat) : BusBelow n (constBits v) := by
  intro k hk
  simp only [constBits, List.mem_map, List.mem_range] at hk
  obtain ⟨i, _, hik⟩ := hk
  split at hik <;> exact Bit.noConfusion hik

/-- Soundness of one synchronous-reset register's dff phase: a valuation under which all emitted
    cells (next-state cone + `$mux` + `$dff`) hold and the returned D-bus denotes `reset ? init :
    next` (= `Module.step` with synchronous reset). -/
theorem compileDff_sound_reset (regBuses : List (String × Bus)) (clock : Option String)
    (rst : String) (r : Reg) (env : Env) (s : CState) (σ₀ : Nat → Bool)
    (hwf : WidthOK s.env r.next) (hmem : CEnvOK σ₀ s.env env) (hbnd : EnvBounded s.env s.nextId)
    (hq : BusBelow s.nextId ((regBuses.lookup r.name).getD []))
    (hcons : ConsistentCells σ₀ s.cells) (hcb : CellsBounded s.cells s.nextId)
    (har : r.asyncReset = none) :
    ∃ σ, (∀ k, k < s.nextId → σ k = σ₀ k) ∧
      ConsistentCells σ ((compileDff regBuses (some rst) clock r).run s).2.cells ∧
      CellsBounded ((compileDff regBuses (some rst) clock r).run s).2.cells
        ((compileDff regBuses (some rst) clock r).run s).2.nextId ∧
      s.nextId ≤ ((compileDff regBuses (some rst) clock r).run s).2.nextId ∧
      ((compileDff regBuses (some rst) clock r).run s).2.env = s.env ∧
      busDen σ r.width ((compileDff regBuses (some rst) clock r).run s).1
        = (if busDen σ 1 ((s.env.lookup rst).getD [Bit.zero]) = 1 then r.init else eval r.next env) := by
  obtain ⟨σ1, hext, hcc, hcbd, hbb, hmono, henv, hval⟩ :=
    sound r.next env (supp_all r.next) s σ₀ hwf hmem hbnd hcons hcb
  -- sbus = reset input bus (env unchanged by the cone), below the cone's id counter
  have hsbus : BusBelow ((compileExpr r.next).run s).2.nextId
      ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) := by
    rw [henv]
    exact BusBelow_mono (BusBelow_lookup_getD hbnd rst [Bit.zero] (by intro j hj; simp at hj)) hmono
  -- the mux output value, computed from σ1
  refine ⟨setRange σ1 ((compileExpr r.next).run s).2.nextId r.width
      (if busDen σ1 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) = 1
       then busDen σ1 r.width (constBits r.init)
       else busDen σ1 r.width ((compileExpr r.next).run s).1), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- extends σ₀
    intro k hk
    rw [setRange_lt σ1 _ r.width _ k (Nat.lt_of_lt_of_le hk hmono), hext k hk]
  · -- ConsistentCells: $dff (vacuous) :: $mux :: cone cells
    rw [compileDff_reset_cells (har := har)]
    have hframe : ∀ i, i < ((compileExpr r.next).run s).2.nextId →
        setRange σ1 ((compileExpr r.next).run s).2.nextId r.width
          (if busDen σ1 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) = 1
           then busDen σ1 r.width (constBits r.init)
           else busDen σ1 r.width ((compileExpr r.next).run s).1) i = σ1 i :=
      fun i hi => setRange_lt σ1 _ r.width _ i hi
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · exact cellHolds_dff _ _ rfl
    rcases List.mem_cons.1 hc with rfl | hc
    · -- the $mux holds
      have hflen : (freshBus ((compileExpr r.next).run s).2 r.width).length = r.width := by
        simp [freshBus]
      show busDen _ (freshBus ((compileExpr r.next).run s).2 r.width).length
            (freshBus ((compileExpr r.next).run s).2 r.width)
          = if busDen _ 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) = 1
            then busDen _ (freshBus ((compileExpr r.next).run s).2 r.width).length (constBits r.init)
            else busDen _ (freshBus ((compileExpr r.next).run s).2 r.width).length
              ((compileExpr r.next).run s).1
      rw [hflen,
          busDen_frame _ σ1 1 _ _ hsbus hframe,
          busDen_frame _ σ1 r.width _ _ hbb hframe]
      simp only [busDen_constBits]
      simpa [freshBus, busDen_constBits] using
        setRange_get σ1 ((compileExpr r.next).run s).2.nextId r.width
          (if busDen σ1 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) = 1
           then busDen σ1 r.width (constBits r.init)
           else busDen σ1 r.width ((compileExpr r.next).run s).1)
    · exact ConsistentCells_frame hcbd (fun i hi => (hframe i hi).symm) hcc c hc
  · -- CellsBounded
    rw [compileDff_reset_cells (har := har), compileDff_reset_nextId (har := har)]
    intro c hc
    rcases List.mem_cons.1 hc with rfl | hc
    · refine CellBelow_dffCell ?_ (BusBelow_freshBus _ _) (BusBelow_mono hq (Nat.le_trans hmono (Nat.le_add_right _ _)))
      rw [henv]
      exact BusBelow_mono (BusBelow_clkBusOf hbnd clock) (Nat.le_trans hmono (Nat.le_add_right _ _))
    rcases List.mem_cons.1 hc with rfl | hc
    · exact CellBelow_muxCell (BusBelow_mono hsbus (Nat.le_add_right _ _))
        (BusBelow_constBits r.init _)
        (BusBelow_mono hbb (Nat.le_add_right _ _)) (BusBelow_freshBus _ _)
    · exact CellsBounded_mono hcbd (Nat.le_add_right _ _) c hc
  · rw [compileDff_reset_nextId (har := har)]; exact Nat.le_trans hmono (Nat.le_add_right _ _)
  · rw [compileDff_reset_env (har := har)]; exact henv
  · -- D-value = reset ? init : next
    rw [compileDff_reset_fst (har := har)]
    have hframe : ∀ i, i < ((compileExpr r.next).run s).2.nextId →
        setRange σ1 ((compileExpr r.next).run s).2.nextId r.width
          (if busDen σ1 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) = 1
           then busDen σ1 r.width (constBits r.init)
           else busDen σ1 r.width ((compileExpr r.next).run s).1) i = σ1 i :=
      fun i hi => setRange_lt σ1 _ r.width _ i hi
    have hY : busDen (setRange σ1 ((compileExpr r.next).run s).2.nextId r.width
          (if busDen σ1 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) = 1
           then busDen σ1 r.width (constBits r.init)
           else busDen σ1 r.width ((compileExpr r.next).run s).1)) r.width
          (freshBus ((compileExpr r.next).run s).2 r.width)
        = (if busDen σ1 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) = 1
           then busDen σ1 r.width (constBits r.init)
           else busDen σ1 r.width ((compileExpr r.next).run s).1) := by
      simpa [freshBus] using setRange_get σ1 ((compileExpr r.next).run s).2.nextId r.width
        (if busDen σ1 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) = 1
         then busDen σ1 r.width (constBits r.init)
         else busDen σ1 r.width ((compileExpr r.next).run s).1)
    have hcond : busDen (setRange σ1 ((compileExpr r.next).run s).2.nextId r.width
          (if busDen σ1 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) = 1
           then busDen σ1 r.width (constBits r.init)
           else busDen σ1 r.width ((compileExpr r.next).run s).1)) 1
          ((s.env.lookup rst).getD [Bit.zero])
        = busDen σ1 1 ((((compileExpr r.next).run s).2.env.lookup rst).getD [Bit.zero]) := by
      rw [← henv]
      exact busDen_frame _ σ1 1 _ _ hsbus hframe
    rw [hY, hcond, busDen_constBits, hval]

/-- One step of the reset-free dff fold (compile a register, append its D-bus). -/
def dffStep (regBuses : List (String × Bus)) (clock : Option String) (acc : List Bus) (r : Reg) :
    CM (List Bus) := do
  let d ← compileDff regBuses none clock r; pure (acc ++ [d])

theorem dffStep_state (regBuses clock acc r s) :
    ((dffStep regBuses clock acc r).run s).2 = ((compileDff regBuses none clock r).run s).2 := rfl

theorem dffStep_acc (regBuses clock acc r s) :
    ((dffStep regBuses clock acc r).run s).1
      = acc ++ [((compileDff regBuses none clock r).run s).1] := rfl

/-- The dff fold only appends D-buses: prior accumulator is a prefix. -/
theorem compileDffs_acc_prefix (regs : List Reg) (regBuses : List (String × Bus))
    (clock : Option String) (acc : List Bus) (s : CState) :
    ∃ extra, ((regs.foldlM (dffStep regBuses clock) acc).run s).1 = acc ++ extra := by
  induction regs generalizing acc s with
  | nil => exact ⟨[], by simp⟩
  | cons r rs ih =>
    obtain ⟨extra, hextra⟩ :=
      ih (acc ++ [((compileDff regBuses none clock r).run s).1])
        ((compileDff regBuses none clock r).run s).2
    refine ⟨((compileDff regBuses none clock r).run s).1 :: extra, ?_⟩
    rw [List.foldlM_cons]
    show ((rs.foldlM (dffStep regBuses clock)
            (acc ++ [((compileDff regBuses none clock r).run s).1])).run
            ((compileDff regBuses none clock r).run s).2).1 = _
    rw [hextra]
    simp

/-- The reset-free dff fold composes `compileDff_sound_noreset` over all registers: one valuation
    under which every emitted cell (next-state cones + `$dff`s) holds and each register's D-bus
    (the value clocked next cycle) denotes `eval r.next`. -/
theorem compileDffs_sound_noreset (regs : List Reg) (regBuses : List (String × Bus))
    (clock : Option String) (env : Env) (acc : List Bus) :
    ∀ (s : CState) (σ₀ : Nat → Bool),
      (∀ r ∈ regs, WidthOK s.env r.next) →
      (∀ r ∈ regs, r.asyncReset = none) →
      CEnvOK σ₀ s.env env → EnvBounded s.env s.nextId →
      (∀ r ∈ regs, BusBelow s.nextId ((regBuses.lookup r.name).getD [])) →
      ConsistentCells σ₀ s.cells → CellsBounded s.cells s.nextId →
      ∃ σ, (∀ k, k < s.nextId → σ k = σ₀ k) ∧
        ConsistentCells σ ((regs.foldlM (dffStep regBuses clock) acc).run s).2.cells ∧
        CellsBounded ((regs.foldlM (dffStep regBuses clock) acc).run s).2.cells
          ((regs.foldlM (dffStep regBuses clock) acc).run s).2.nextId ∧
        s.nextId ≤ ((regs.foldlM (dffStep regBuses clock) acc).run s).2.nextId ∧
        ((regs.foldlM (dffStep regBuses clock) acc).run s).2.env = s.env ∧
        ∀ r ∈ regs, ∃ d ∈ ((regs.foldlM (dffStep regBuses clock) acc).run s).1,
          BusBelow ((regs.foldlM (dffStep regBuses clock) acc).run s).2.nextId d ∧
          busDen σ r.width d = eval r.next env := by
  induction regs generalizing acc with
  | nil =>
    intro s σ₀ _ _ _ _ _ hcons hcb
    refine ⟨σ₀, fun _ _ => rfl, hcons, hcb, Nat.le_refl _, rfl, ?_⟩
    intro r hr; simp at hr
  | cons r rs ih =>
    intro s σ₀ hwf har hmem hbnd hq hcons hcb
    obtain ⟨σ1, hext1, hcc1, hcbd1, hmono1, henv1, hval1, hbb1⟩ :=
      compileDff_sound_noreset regBuses clock r env s σ₀ (hwf r (List.mem_cons_self ..)) hmem hbnd
        (hq r (List.mem_cons_self ..)) hcons hcb (har r (List.mem_cons_self ..))
    -- the returned D-bus is `compileExpr r.next`'s bus; restate the bound about it in terms of
    -- `compileDff` (the match on `r.asyncReset` no longer reduces definitionally).
    have hbb1' : BusBelow ((compileDff regBuses none clock r).run s).2.nextId
        ((compileDff regBuses none clock r).run s).1 := by
      rw [compileDff_noreset_fst regBuses clock r s (har r (List.mem_cons_self ..)),
          compileDff_noreset_nextId regBuses clock r s (har r (List.mem_cons_self ..))]
      exact hbb1
    have hmemb : CEnvOK σ1 ((compileDff regBuses none clock r).run s).2.env env := by
      rw [henv1]; exact CEnvOK_frame hbnd (fun k hk => (hext1 k hk).symm) hmem
    have hbndb : EnvBounded ((compileDff regBuses none clock r).run s).2.env
        ((compileDff regBuses none clock r).run s).2.nextId := by
      rw [henv1]; exact EnvBounded_mono hbnd hmono1
    have hwfb : ∀ r' ∈ rs, WidthOK ((compileDff regBuses none clock r).run s).2.env r'.next := by
      rw [henv1]; exact fun r' hr' => hwf r' (List.mem_cons_of_mem r hr')
    have hqb : ∀ r' ∈ rs, BusBelow ((compileDff regBuses none clock r).run s).2.nextId
        ((regBuses.lookup r'.name).getD []) :=
      fun r' hr' => BusBelow_mono (hq r' (List.mem_cons_of_mem r hr')) hmono1
    obtain ⟨σ2, hext2, hcc2, hcbd2, hmono2, henv2, hvals2⟩ :=
      ih (acc ++ [((compileDff regBuses none clock r).run s).1])
        ((compileDff regBuses none clock r).run s).2 σ1 hwfb
        (fun r' hr' => har r' (List.mem_cons_of_mem r hr')) hmemb hbndb hqb hcc1 hcbd1
    have hd_mem : ((compileDff regBuses none clock r).run s).1 ∈
        ((rs.foldlM (dffStep regBuses clock)
          (acc ++ [((compileDff regBuses none clock r).run s).1])).run
          ((compileDff regBuses none clock r).run s).2).1 := by
      obtain ⟨extra, hextra⟩ := compileDffs_acc_prefix rs regBuses clock
        (acc ++ [((compileDff regBuses none clock r).run s).1])
        ((compileDff regBuses none clock r).run s).2
      rw [hextra]; simp
    have hvald : busDen σ2 r.width ((compileDff regBuses none clock r).run s).1 = eval r.next env := by
      rw [busDen_frame σ2 σ1 r.width ((compileDff regBuses none clock r).run s).1
            ((compileDff regBuses none clock r).run s).2.nextId hbb1' hext2]
      exact hval1
    refine ⟨σ2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [hext2 k (Nat.lt_of_lt_of_le hk hmono1), hext1 k hk]
    all_goals rw [List.foldlM_cons]; simp only [dffStep, run_bind, run_pure]
    · exact hcc2
    · exact hcbd2
    · exact Nat.le_trans hmono1 hmono2
    · rw [henv2, henv1]
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr''
      · exact ⟨_, hd_mem, BusBelow_mono hbb1' hmono2, hvald⟩
      · exact hvals2 r' hr''

/-! ### Synchronous-reset dff fold -/

/-- One step of the sync-reset dff fold. -/
def dffStepR (regBuses : List (String × Bus)) (rst : String) (clock : Option String)
    (acc : List Bus) (r : Reg) : CM (List Bus) := do
  let d ← compileDff regBuses (some rst) clock r; pure (acc ++ [d])

theorem dffStepR_state (regBuses rst clock acc r s) :
    ((dffStepR regBuses rst clock acc r).run s).2
      = ((compileDff regBuses (some rst) clock r).run s).2 := rfl
theorem dffStepR_acc (regBuses rst clock acc r s) :
    ((dffStepR regBuses rst clock acc r).run s).1
      = acc ++ [((compileDff regBuses (some rst) clock r).run s).1] := rfl

theorem compileDffs_acc_prefix_reset (regs : List Reg) (regBuses : List (String × Bus))
    (rst : String) (clock : Option String) (acc : List Bus) (s : CState) :
    ∃ extra, ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).1 = acc ++ extra := by
  induction regs generalizing acc s with
  | nil => exact ⟨[], by simp⟩
  | cons r rs ih =>
    obtain ⟨extra, hextra⟩ :=
      ih (acc ++ [((compileDff regBuses (some rst) clock r).run s).1])
        ((compileDff regBuses (some rst) clock r).run s).2
    refine ⟨((compileDff regBuses (some rst) clock r).run s).1 :: extra, ?_⟩
    rw [List.foldlM_cons]
    show ((rs.foldlM (dffStepR regBuses rst clock)
            (acc ++ [((compileDff regBuses (some rst) clock r).run s).1])).run
            ((compileDff regBuses (some rst) clock r).run s).2).1 = _
    rw [hextra]
    simp

/-- The sync-reset dff fold composes `compileDff_sound_reset` over all registers: one valuation
    under which every cell holds and each register's D-bus denotes `reset ? init : next` (the reset
    bit `busDen σ₀ rst` is below `s.nextId`, hence frame-invariant across the fold). -/
theorem compileDffs_sound_reset (regs : List Reg) (regBuses : List (String × Bus))
    (rst : String) (clock : Option String) (env : Env) (acc : List Bus) :
    ∀ (s : CState) (σ₀ : Nat → Bool),
      (∀ r ∈ regs, WidthOK s.env r.next) →
      (∀ r ∈ regs, r.asyncReset = none) →
      CEnvOK σ₀ s.env env → EnvBounded s.env s.nextId →
      (∀ r ∈ regs, BusBelow s.nextId ((regBuses.lookup r.name).getD [])) →
      ConsistentCells σ₀ s.cells → CellsBounded s.cells s.nextId →
      ∃ σ, (∀ k, k < s.nextId → σ k = σ₀ k) ∧
        ConsistentCells σ ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).2.cells ∧
        CellsBounded ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).2.cells
          ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).2.nextId ∧
        s.nextId ≤ ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).2.nextId ∧
        ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).2.env = s.env ∧
        ∀ r ∈ regs, ∃ d ∈ ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).1,
          BusBelow ((regs.foldlM (dffStepR regBuses rst clock) acc).run s).2.nextId d ∧
          busDen σ r.width d
            = if busDen σ 1 ((s.env.lookup rst).getD [Bit.zero]) = 1 then r.init else eval r.next env := by
  induction regs generalizing acc with
  | nil =>
    intro s σ₀ _ _ _ _ _ hcons hcb
    refine ⟨σ₀, fun _ _ => rfl, hcons, hcb, Nat.le_refl _, rfl, ?_⟩
    intro r hr; simp at hr
  | cons r rs ih =>
    intro s σ₀ hwf har hmem hbnd hq hcons hcb
    obtain ⟨σ1, hext1, hcc1, hcbd1, hmono1, henv1, hval1⟩ :=
      compileDff_sound_reset regBuses clock rst r env s σ₀ (hwf r (List.mem_cons_self ..)) hmem hbnd
        (hq r (List.mem_cons_self ..)) hcons hcb (har r (List.mem_cons_self ..))
    have hmemb : CEnvOK σ1 ((compileDff regBuses (some rst) clock r).run s).2.env env := by
      rw [henv1]; exact CEnvOK_frame hbnd (fun k hk => (hext1 k hk).symm) hmem
    have hbndb : EnvBounded ((compileDff regBuses (some rst) clock r).run s).2.env
        ((compileDff regBuses (some rst) clock r).run s).2.nextId := by
      rw [henv1]; exact EnvBounded_mono hbnd hmono1
    have hwfb : ∀ r' ∈ rs, WidthOK ((compileDff regBuses (some rst) clock r).run s).2.env r'.next := by
      rw [henv1]; exact fun r' hr' => hwf r' (List.mem_cons_of_mem r hr')
    have hqb : ∀ r' ∈ rs, BusBelow ((compileDff regBuses (some rst) clock r).run s).2.nextId
        ((regBuses.lookup r'.name).getD []) :=
      fun r' hr' => BusBelow_mono (hq r' (List.mem_cons_of_mem r hr')) hmono1
    obtain ⟨σ2, hext2, hcc2, hcbd2, hmono2, henv2, hvals2⟩ :=
      ih (acc ++ [((compileDff regBuses (some rst) clock r).run s).1])
        ((compileDff regBuses (some rst) clock r).run s).2 σ1 hwfb
        (fun r' hr' => har r' (List.mem_cons_of_mem r hr')) hmemb hbndb hqb hcc1 hcbd1
    have hd_mem : ((compileDff regBuses (some rst) clock r).run s).1 ∈
        ((rs.foldlM (dffStepR regBuses rst clock)
          (acc ++ [((compileDff regBuses (some rst) clock r).run s).1])).run
          ((compileDff regBuses (some rst) clock r).run s).2).1 := by
      obtain ⟨extra, hextra⟩ := compileDffs_acc_prefix_reset rs regBuses rst clock
        (acc ++ [((compileDff regBuses (some rst) clock r).run s).1])
        ((compileDff regBuses (some rst) clock r).run s).2
      rw [hextra]; simp
    have hyb : BusBelow ((compileDff regBuses (some rst) clock r).run s).2.nextId
        ((compileDff regBuses (some rst) clock r).run s).1 := by
      rw [compileDff_reset_fst (har := har r (List.mem_cons_self ..)),
          compileDff_reset_nextId (har := har r (List.mem_cons_self ..))]
      exact BusBelow_freshBus _ _
    have hsb : BusBelow ((compileDff regBuses (some rst) clock r).run s).2.nextId
        ((s.env.lookup rst).getD [Bit.zero]) :=
      BusBelow_mono (BusBelow_lookup_getD hbnd rst [Bit.zero] (by intro j hj; simp at hj)) hmono1
    have hvald : busDen σ2 r.width ((compileDff regBuses (some rst) clock r).run s).1
        = if busDen σ2 1 ((s.env.lookup rst).getD [Bit.zero]) = 1 then r.init else eval r.next env := by
      rw [busDen_frame σ2 σ1 r.width _ _ hyb hext2, busDen_frame σ2 σ1 1 _ _ hsb hext2]
      exact hval1
    refine ⟨σ2, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [hext2 k (Nat.lt_of_lt_of_le hk hmono1), hext1 k hk]
    all_goals rw [List.foldlM_cons]; simp only [dffStepR, run_bind, run_pure]
    · exact hcc2
    · exact hcbd2
    · exact Nat.le_trans hmono1 hmono2
    · rw [henv2, henv1]
    · intro r' hr'
      rcases List.mem_cons.1 hr' with rfl | hr''
      · exact ⟨_, hd_mem, BusBelow_mono hyb hmono2, hvald⟩
      · have := hvals2 r' hr''
        rw [henv1] at this
        exact this

/-! ## Dff + output composition (the combinational core of a wire-free reset-free module)

Running the dff phase then the output phase from a setup state where the inputs and registers are
already bound (`CEnvOK`), there is a single valuation under which every emitted cell holds, each
output port denotes `eval o.expr`, and each register's D-bus denotes `eval r.next`.  The output
phase extends the dff valuation, so the dff cells stay satisfied and the D-values frame up
(via the D-bus bound). -/
theorem dff_output_sound (regBuses : List (String × Bus)) (clock : Option String)
    (regs : List Reg) (outputs : List OutPort) (env : Env) (s : CState) (σ₀ : Nat → Bool)
    (hwfd : ∀ r ∈ regs, WidthOK s.env r.next) (hwfo : ∀ o ∈ outputs, WidthOK s.env o.expr)
    (hmem : CEnvOK σ₀ s.env env) (hbnd : EnvBounded s.env s.nextId)
    (hq : ∀ r ∈ regs, BusBelow s.nextId ((regBuses.lookup r.name).getD []))
    (hcons : ConsistentCells σ₀ s.cells) (hcb : CellsBounded s.cells s.nextId)
    (har : ∀ r ∈ regs, r.asyncReset = none) :
    ∃ σ,
      ConsistentCells σ ((outputs.foldlM compileOutput ([], [])).run
        ((regs.foldlM (dffStep regBuses clock) []).run s).2).2.cells ∧
      (∀ o ∈ outputs, ∃ port ∈ ((outputs.foldlM compileOutput ([], [])).run
            ((regs.foldlM (dffStep regBuses clock) []).run s).2).1.1,
          port.name = o.name ∧ port.dir = Dir.output ∧ busDen σ o.width port.bits = eval o.expr env) ∧
      (∀ r ∈ regs, ∃ d ∈ ((regs.foldlM (dffStep regBuses clock) []).run s).1,
          busDen σ r.width d = eval r.next env) := by
  obtain ⟨σ1, hext1, hcc1, hcbd1, hmono1, henv1, hvals1⟩ :=
    compileDffs_sound_noreset regs regBuses clock env [] s σ₀ hwfd har hmem hbnd hq hcons hcb
  have hwfo' : ∀ o ∈ outputs,
      WidthOK ((regs.foldlM (dffStep regBuses clock) []).run s).2.env o.expr := by
    rw [henv1]; exact hwfo
  have hmem' : CEnvOK σ1 ((regs.foldlM (dffStep regBuses clock) []).run s).2.env env := by
    rw [henv1]; exact CEnvOK_frame hbnd (fun k hk => (hext1 k hk).symm) hmem
  have hbnd' : EnvBounded ((regs.foldlM (dffStep regBuses clock) []).run s).2.env
      ((regs.foldlM (dffStep regBuses clock) []).run s).2.nextId := by
    rw [henv1]; exact EnvBounded_mono hbnd hmono1
  obtain ⟨σ2, hext2, hcc2, _hcbd2, _hmono2, _henv2, hvalo⟩ :=
    compileOutputs_sound outputs env ([], [])
      ((regs.foldlM (dffStep regBuses clock) []).run s).2 σ1 hwfo' hmem' hbnd' hcc1 hcbd1
  refine ⟨σ2, hcc2, hvalo, ?_⟩
  intro r hr
  obtain ⟨d, hd_mem, hd_below, hd_val⟩ := hvals1 r hr
  exact ⟨d, hd_mem, by
    rw [busDen_frame σ2 σ1 r.width d
      ((regs.foldlM (dffStep regBuses clock) []).run s).2.nextId hd_below hext2]
    exact hd_val⟩

/-- Sync-reset analogue of `dff_output_sound`: dff fold (with reset mux) then output fold, one
    valuation under which all cells hold, outputs denote `eval o.expr`, and each register's D-bus
    denotes `reset ? init : next`. -/
theorem dff_output_sound_reset (regBuses : List (String × Bus)) (rst : String)
    (clock : Option String) (regs : List Reg) (outputs : List OutPort) (env : Env) (s : CState)
    (σ₀ : Nat → Bool)
    (hwfd : ∀ r ∈ regs, WidthOK s.env r.next) (hwfo : ∀ o ∈ outputs, WidthOK s.env o.expr)
    (hmem : CEnvOK σ₀ s.env env) (hbnd : EnvBounded s.env s.nextId)
    (hq : ∀ r ∈ regs, BusBelow s.nextId ((regBuses.lookup r.name).getD []))
    (hcons : ConsistentCells σ₀ s.cells) (hcb : CellsBounded s.cells s.nextId)
    (har : ∀ r ∈ regs, r.asyncReset = none) :
    ∃ σ,
      ConsistentCells σ ((outputs.foldlM compileOutput ([], [])).run
        ((regs.foldlM (dffStepR regBuses rst clock) []).run s).2).2.cells ∧
      (∀ o ∈ outputs, ∃ port ∈ ((outputs.foldlM compileOutput ([], [])).run
            ((regs.foldlM (dffStepR regBuses rst clock) []).run s).2).1.1,
          port.name = o.name ∧ port.dir = Dir.output ∧ busDen σ o.width port.bits = eval o.expr env) ∧
      (∀ r ∈ regs, ∃ d ∈ ((regs.foldlM (dffStepR regBuses rst clock) []).run s).1,
          busDen σ r.width d
            = if busDen σ 1 ((s.env.lookup rst).getD [Bit.zero]) = 1 then r.init else eval r.next env) := by
  obtain ⟨σ1, hext1, hcc1, hcbd1, hmono1, henv1, hvals1⟩ :=
    compileDffs_sound_reset regs regBuses rst clock env [] s σ₀ hwfd har hmem hbnd hq hcons hcb
  have hwfo' : ∀ o ∈ outputs,
      WidthOK ((regs.foldlM (dffStepR regBuses rst clock) []).run s).2.env o.expr := by
    rw [henv1]; exact hwfo
  have hmem' : CEnvOK σ1 ((regs.foldlM (dffStepR regBuses rst clock) []).run s).2.env env := by
    rw [henv1]; exact CEnvOK_frame hbnd (fun k hk => (hext1 k hk).symm) hmem
  have hbnd' : EnvBounded ((regs.foldlM (dffStepR regBuses rst clock) []).run s).2.env
      ((regs.foldlM (dffStepR regBuses rst clock) []).run s).2.nextId := by
    rw [henv1]; exact EnvBounded_mono hbnd hmono1
  obtain ⟨σ2, hext2, hcc2, _hcbd2, _hmono2, _henv2, hvalo⟩ :=
    compileOutputs_sound outputs env ([], [])
      ((regs.foldlM (dffStepR regBuses rst clock) []).run s).2 σ1 hwfo' hmem' hbnd' hcc1 hcbd1
  have hsb : BusBelow ((regs.foldlM (dffStepR regBuses rst clock) []).run s).2.nextId
      ((s.env.lookup rst).getD [Bit.zero]) :=
    BusBelow_mono (BusBelow_lookup_getD hbnd rst [Bit.zero] (by intro j hj; simp at hj)) hmono1
  refine ⟨σ2, hcc2, hvalo, ?_⟩
  intro r hr
  obtain ⟨d, hd_mem, hd_below, hd_val⟩ := hvals1 r hr
  refine ⟨d, hd_mem, ?_⟩
  rw [busDen_frame σ2 σ1 r.width d
        ((regs.foldlM (dffStepR regBuses rst clock) []).run s).2.nextId hd_below hext2,
      busDen_frame σ2 σ1 1 _
        ((regs.foldlM (dffStepR regBuses rst clock) []).run s).2.nextId hsb hext2]
  exact hd_val

/-- The post-setup state has emitted no cells. -/
theorem setup_cells (m : Module) :
    ((m.regs.foldlM compileReg ([], [])).run
      ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.cells = [] := by
  rw [compileRegs_cells, compileInputs_cells]

/-! ## Wire phase (CEnvOK growth for modules with internal wires) -/

/-- Round-trip: a bit-vector is recovered from its `Nat` value. -/
theorem BitVec_ofNat_toNat_self {w : Nat} (x : BitVec w) : BitVec.ofNat w x.toNat = x := by
  apply BitVec.eq_of_toNat_eq; rw [BitVec.toNat_ofNat]; exact Nat.mod_eq_of_lt x.isLt

theorem compileWire_env (acc : List NetName) (w : Wire) (s : CState) :
    ((compileWire acc w).run s).2.env
      = (w.name, ((compileExpr w.expr).run s).1) :: ((compileExpr w.expr).run s).2.env := rfl
theorem compileWire_cells (acc : List NetName) (w : Wire) (s : CState) :
    ((compileWire acc w).run s).2.cells = ((compileExpr w.expr).run s).2.cells := rfl
theorem compileWire_nextId (acc : List NetName) (w : Wire) (s : CState) :
    ((compileWire acc w).run s).2.nextId = ((compileExpr w.expr).run s).2.nextId := rfl

/-- Topological well-formedness of a wire list: each wire's expression is `WidthOK` against the
    environment built from all *earlier* wires (the bus chosen for each is immaterial beyond its
    width, hence the `∀ bus` quantifier — instantiated at the actual compiled bus in the proof). -/
def WiresOK : List (String × Bus) → List Wire → Prop
  | _, [] => True
  | cenv, w :: ws => WidthOK cenv w.expr ∧
      ∀ bus : Bus, bus.length = w.width → WiresOK ((w.name, bus) :: cenv) ws

/-- **Wire phase soundness.** Folding `compileWire` over a topologically well-formed wire list
    extends the valuation so that every emitted cell holds and the bus environment satisfies
    `CEnvOK` against the *grown* value environment `evalWires wires vals` — each wire's net denotes
    its `eval`. -/
theorem compileWires_sound : ∀ (wires : List Wire) (acc : List NetName) (s : CState)
    (σ : Nat → Bool) (vals : Env),
    CEnvOK σ s.env vals → EnvBounded s.env s.nextId → ConsistentCells σ s.cells →
    CellsBounded s.cells s.nextId → WiresOK s.env wires →
    ∃ σ', (∀ k, k < s.nextId → σ' k = σ k) ∧
      CEnvOK σ' ((wires.foldlM compileWire acc).run s).2.env (evalWires wires vals) ∧
      ConsistentCells σ' ((wires.foldlM compileWire acc).run s).2.cells ∧
      CellsBounded ((wires.foldlM compileWire acc).run s).2.cells
        ((wires.foldlM compileWire acc).run s).2.nextId ∧
      EnvBounded ((wires.foldlM compileWire acc).run s).2.env
        ((wires.foldlM compileWire acc).run s).2.nextId ∧
      s.nextId ≤ ((wires.foldlM compileWire acc).run s).2.nextId := by
  intro wires
  induction wires with
  | nil =>
    intro acc s σ vals hc hb hcons hcb _
    exact ⟨σ, fun _ _ => rfl, by simpa [evalWires] using hc, hcons, hcb, hb, Nat.le_refl _⟩
  | cons w ws ih =>
    intro acc s σ vals hc hb hcons hcb hwf
    obtain ⟨hwf_head, hwf_tail⟩ := hwf
    obtain ⟨σ1, hext1, hcc1, hcb1, hbb1, hmono1, henv1, hval1⟩ :=
      sound w.expr vals (supp_all w.expr) s σ hwf_head hc hb hcons hcb
    have hlen : ((compileExpr w.expr).run s).1.length = w.width :=
      compileExpr_len w.expr (supp_all w.expr) s hwf_head
    have hc' : CEnvOK σ1 ((compileWire acc w).run s).2.env
        (fun n => if n = w.name then (eval w.expr vals).toNat else vals n) := by
      rw [compileWire_env, henv1]
      refine CEnvOK_cons_wire ?_ (CEnvOK_frame hb (fun k hk => (hext1 k hk).symm) hc)
      rw [hlen, hval1, BitVec_ofNat_toNat_self]
    have hb' : EnvBounded ((compileWire acc w).run s).2.env
        ((compileWire acc w).run s).2.nextId := by
      rw [compileWire_env, compileWire_nextId, henv1]
      exact EnvBounded_cons hbb1 (EnvBounded_mono hb hmono1)
    have hcons' : ConsistentCells σ1 ((compileWire acc w).run s).2.cells := by
      rw [compileWire_cells]; exact hcc1
    have hcb' : CellsBounded ((compileWire acc w).run s).2.cells
        ((compileWire acc w).run s).2.nextId := by
      rw [compileWire_cells, compileWire_nextId]; exact hcb1
    have hwf' : WiresOK ((compileWire acc w).run s).2.env ws := by
      rw [compileWire_env, henv1]; exact hwf_tail _ hlen
    obtain ⟨σ', hext', hCE', hCo', hCB', hEB', hMono'⟩ :=
      ih ((compileWire acc w).run s).1 ((compileWire acc w).run s).2 σ1
        (fun n => if n = w.name then (eval w.expr vals).toNat else vals n) hc' hb' hcons' hcb' hwf'
    refine ⟨σ', ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      have hk' : k < ((compileWire acc w).run s).2.nextId := by
        rw [compileWire_nextId]; exact Nat.lt_of_lt_of_le hk hmono1
      rw [hext' k hk', hext1 k hk]
    · rw [List.foldlM_cons]
      show CEnvOK σ' ((ws.foldlM compileWire _).run ((compileWire acc w).run s).2).2.env
        (evalWires (w :: ws) vals)
      rw [show evalWires (w :: ws) vals
            = evalWires ws (fun n => if n = w.name then (eval w.expr vals).toNat else vals n) from rfl]
      exact hCE'
    · rw [List.foldlM_cons]; exact hCo'
    · rw [List.foldlM_cons]; exact hCB'
    · rw [List.foldlM_cons]; exact hEB'
    · rw [List.foldlM_cons]
      refine Nat.le_trans ?_ hMono'
      rw [compileWire_nextId]; exact hmono1

/-- **Setup + wire drive.** For any value assignment, the post-wire state (inputs, registers, then
    the wire fold) admits a valuation realizing the grown value environment `evalWires m.wires vals`
    (`CEnvOK`), with all setup+wire cells consistent and bounded — combining `setup_sigma` (free
    inputs/registers) with `compileWires_sound` (computed wires). -/
theorem setup_wires_sigma (m : Module) (vals : Env)
    (hwires : WiresOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env m.wires) :
    ∃ σ, CEnvOK σ ((m.wires.foldlM compileWire []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env
        (evalWires m.wires vals) ∧
      ConsistentCells σ ((m.wires.foldlM compileWire []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.cells ∧
      EnvBounded ((m.wires.foldlM compileWire []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env
        ((m.wires.foldlM compileWire []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.nextId ∧
      CellsBounded ((m.wires.foldlM compileWire []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.cells
        ((m.wires.foldlM compileWire []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.nextId ∧
      ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.nextId
        ≤ ((m.wires.foldlM compileWire []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.nextId := by
  obtain ⟨σ0, hc0⟩ := setup_sigma m vals
  obtain ⟨σ, _, hCE, hCo, hCB, hEB, hMono⟩ :=
    compileWires_sound m.wires [] _ σ0 vals hc0 (setup_envBounded m)
      (by rw [setup_cells]; intro c hc; simp at hc)
      (by rw [setup_cells]; intro c hc; simp at hc) hwires
  exact ⟨σ, hCE, hCo, hEB, hCB, hMono⟩

/-- **Compiled module computes the source function — general (with internal wires) reset-free case.**
    For any input/register value assignment `vals`, the compiled module has a valuation under which
    every cell holds, each output port denotes `eval o.expr` and each register's D-bus denotes
    `eval r.next` — both over the *wire-extended* environment `evalWires m.wires vals` (= the cycle
    environment a Moore/Mealy module's combinational cones actually see).  The `CEnvOK` interface and
    the wire cells are discharged by `setup_wires_sigma`; `WidthOK` (against the post-wire env) and
    topological `WiresOK` are the only hypotheses. -/
theorem compileModule_drives_wires (m : Module) (hr : m.reset = none)
    (har : ∀ r ∈ m.regs, r.asyncReset = none)
    (hwfd : ∀ r ∈ m.regs, WidthOK ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env r.next)
    (hwfo : ∀ o ∈ m.outputs, WidthOK ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env o.expr)
    (hwires : WiresOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env m.wires)
    (vals : Env) :
    ∃ σ, ConsistentCells σ ((compileModuleM m).run {}).2.cells ∧
      (∀ o ∈ m.outputs, ∃ port ∈ ((m.outputs.foldlM compileOutput ([], [])).run
            ((m.regs.foldlM (dffStep (((m.regs.foldlM compileReg ([], [])).run
                ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock) []).run
              ((m.wires.foldlM compileWire []).run
                ((m.regs.foldlM compileReg ([], [])).run
                  ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).2).1.1,
          port.name = o.name ∧ port.dir = Dir.output ∧
          busDen σ o.width port.bits = eval o.expr (evalWires m.wires vals)) ∧
      (∀ r ∈ m.regs, ∃ d ∈ ((m.regs.foldlM (dffStep (((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock) []).run
          ((m.wires.foldlM compileWire []).run
            ((m.regs.foldlM compileReg ([], [])).run
              ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).1,
          busDen σ r.width d = eval r.next (evalWires m.wires vals)) := by
  obtain ⟨σw, hCE, hCo, hEB, hCB, hMono⟩ := setup_wires_sigma m vals hwires
  have hq : ∀ r ∈ m.regs,
      BusBelow ((m.wires.foldlM compileWire []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.nextId
        ((((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1.lookup r.name).getD []) := by
    intro r _
    exact BusBelow_mono (BusBelow_regBuses_lookup _ r.name _
      (compileRegs_regBuses_below m.regs ([], [])
        ((m.inputs.foldlM compileInput ([], [])).run {}).2 (by intro p hp; simp at hp))) hMono
  obtain ⟨σ, hcc, hvalo, hvald⟩ :=
    dff_output_sound (((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock m.regs m.outputs
      (evalWires m.wires vals)
      ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2 σw
      hwfd hwfo hCE hEB hq hCo hCB har
  refine ⟨σ, ?_, hvalo, hvald⟩
  simp only [compileModuleM, run_bind, run_pure, hr, compileDffs]
  exact hcc

/-- **Compiled module computes the source function — general (with wires) synchronous-reset case.**
    Like `compileModule_drives_wires`, but for `m.reset = some rst`: each register's D-bus denotes
    `reset ? init : next` (the reset bit read from the compiled reset-input net). Drops to the same
    statement when the reset input is held low. -/
theorem compileModule_drives_wires_reset (m : Module) (rst : String) (hr : m.reset = some rst)
    (har : ∀ r ∈ m.regs, r.asyncReset = none)
    (hwfd : ∀ r ∈ m.regs, WidthOK ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env r.next)
    (hwfo : ∀ o ∈ m.outputs, WidthOK ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env o.expr)
    (hwires : WiresOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env m.wires)
    (vals : Env) :
    ∃ σ, ConsistentCells σ ((compileModuleM m).run {}).2.cells ∧
      (∀ o ∈ m.outputs, ∃ port ∈ ((m.outputs.foldlM compileOutput ([], [])).run
            ((m.regs.foldlM (dffStepR (((m.regs.foldlM compileReg ([], [])).run
                ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) rst m.clock) []).run
              ((m.wires.foldlM compileWire []).run
                ((m.regs.foldlM compileReg ([], [])).run
                  ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).2).1.1,
          port.name = o.name ∧ port.dir = Dir.output ∧
          busDen σ o.width port.bits = eval o.expr (evalWires m.wires vals)) ∧
      (∀ r ∈ m.regs, ∃ d ∈ ((m.regs.foldlM (dffStepR (((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) rst m.clock) []).run
          ((m.wires.foldlM compileWire []).run
            ((m.regs.foldlM compileReg ([], [])).run
              ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).1,
          busDen σ r.width d
            = if busDen σ 1 (((((m.wires.foldlM compileWire []).run
                  ((m.regs.foldlM compileReg ([], [])).run
                    ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env).lookup rst).getD
                  [Bit.zero]) = 1
              then r.init else eval r.next (evalWires m.wires vals)) := by
  obtain ⟨σw, hCE, hCo, hEB, hCB, hMono⟩ := setup_wires_sigma m vals hwires
  have hq : ∀ r ∈ m.regs,
      BusBelow ((m.wires.foldlM compileWire []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.nextId
        ((((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1.lookup r.name).getD []) := by
    intro r _
    exact BusBelow_mono (BusBelow_regBuses_lookup _ r.name _
      (compileRegs_regBuses_below m.regs ([], [])
        ((m.inputs.foldlM compileInput ([], [])).run {}).2 (by intro p hp; simp at hp))) hMono
  obtain ⟨σ, hcc, hvalo, hvald⟩ :=
    dff_output_sound_reset (((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) rst m.clock m.regs m.outputs
      (evalWires m.wires vals)
      ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2 σw
      hwfd hwfo hCE hEB hq hCo hCB har
  refine ⟨σ, ?_, hvalo, hvald⟩
  simp only [compileModuleM, run_bind, run_pure, hr, compileDffs]
  exact hcc

/-! ## Connection to `compileModuleM` (wire-free reset-free modules)

The refactored `compileModuleM` unfolds (`simp`) to: setup (inputs, registers) → dff fold →
output fold.  Feeding the setup state into `dff_output_sound` gives a single valuation under which
**the actual compiled module's cells all hold**, every output port denotes `eval o.expr`, and every
register's D-bus denotes `eval r.next` — the well-formedness (`WidthOK`) and the input/register
interface (`CEnvOK`) against the post-setup environment are the only hypotheses. -/
theorem compileModule_comb_sound (m : Module) (hw : m.wires = []) (hr : m.reset = none)
    (har : ∀ r ∈ m.regs, r.asyncReset = none)
    (env : Env) (σ₀ : Nat → Bool)
    (hwfd : ∀ r ∈ m.regs, WidthOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env r.next)
    (hwfo : ∀ o ∈ m.outputs, WidthOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env o.expr)
    (hmem : CEnvOK σ₀ ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env env) :
    ∃ σ, ConsistentCells σ ((compileModuleM m).run {}).2.cells ∧
      (∀ o ∈ m.outputs, ∃ port ∈ ((m.outputs.foldlM compileOutput ([], [])).run
            ((m.regs.foldlM (dffStep (((m.regs.foldlM compileReg ([], [])).run
                ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock) []).run
              ((m.regs.foldlM compileReg ([], [])).run
                ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).1.1,
          port.name = o.name ∧ port.dir = Dir.output ∧
          busDen σ o.width port.bits = eval o.expr env) ∧
      (∀ r ∈ m.regs, ∃ d ∈ ((m.regs.foldlM (dffStep (((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock) []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).1,
          busDen σ r.width d = eval r.next env) := by
  have hq : ∀ r ∈ m.regs,
      BusBelow ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.nextId
        ((((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1.lookup r.name).getD []) := by
    intro r _
    exact BusBelow_regBuses_lookup _ r.name _
      (compileRegs_regBuses_below m.regs ([], [])
        ((m.inputs.foldlM compileInput ([], [])).run {}).2 (by intro p hp; simp at hp))
  obtain ⟨σ, hcc, hvalo, hvald⟩ :=
    dff_output_sound (((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock m.regs m.outputs env
      ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2 σ₀
      hwfd hwfo hmem (setup_envBounded m) hq
      (by rw [setup_cells]; intro c hc; simp at hc)
      (by rw [setup_cells]; intro c hc; simp at hc) har
  refine ⟨σ, ?_, hvalo, hvald⟩
  simp only [compileModuleM, run_bind, run_pure, hw, hr, compileDffs, List.foldlM_nil]
  exact hcc

/-- **Compiled module computes the source function (interface discharged).** For *any* input/register
    value assignment `vals`, the compiled module (wire-free reset-free) has a valuation under which
    every cell holds, each output port denotes `eval o.expr vals`, and each register's D-bus denotes
    `eval r.next vals`.  The `CEnvOK` interface hypothesis of `compileModule_comb_sound` is now
    discharged by `setup_sigma` — only well-formedness (`WidthOK`) remains.  Instantiating `vals` at
    each cycle's register-trace/inputs yields the per-cycle sequential correctness. -/
theorem compileModule_drives (m : Module) (hw : m.wires = []) (hr : m.reset = none)
    (har : ∀ r ∈ m.regs, r.asyncReset = none)
    (hwfd : ∀ r ∈ m.regs, WidthOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env r.next)
    (hwfo : ∀ o ∈ m.outputs, WidthOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env o.expr)
    (vals : Env) :
    ∃ σ, ConsistentCells σ ((compileModuleM m).run {}).2.cells ∧
      (∀ o ∈ m.outputs, ∃ port ∈ ((m.outputs.foldlM compileOutput ([], [])).run
            ((m.regs.foldlM (dffStep (((m.regs.foldlM compileReg ([], [])).run
                ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock) []).run
              ((m.regs.foldlM compileReg ([], [])).run
                ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).1.1,
          port.name = o.name ∧ port.dir = Dir.output ∧
          busDen σ o.width port.bits = eval o.expr vals) ∧
      (∀ r ∈ m.regs, ∃ d ∈ ((m.regs.foldlM (dffStep (((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock) []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).1,
          busDen σ r.width d = eval r.next vals) := by
  obtain ⟨σ₀, hmem⟩ := setup_sigma m vals
  exact compileModule_comb_sound m hw hr har vals σ₀ hwfd hwfo hmem

/-- **Sequential correctness (M6b, wire-free reset-free).** For an arbitrary register-value trace
    `Q` and input stream `inputs`, at *every* cycle `t` the compiled netlist has a valuation under
    which all cells hold, each output port's bus denotes `eval o.expr` over the cycle environment
    `cycleEnv (Q t) (inputs t)`, and each register's D-bus denotes `eval r.next` over the same.

    Since (for `wires = []`) `Module.outputs?eval (Q t) (inputs t)` is exactly the per-output
    `(eval o.expr (cycleEnv (Q t) (inputs t) …)).toNat` and `Module.step (Q t) (inputs t) false`
    is the per-register `(eval r.next (cycleEnv …)).toNat`, this says the netlist's output nets and
    register-D nets carry the denotational `outputs?eval`/`step` values every cycle.  Taking
    `Q = regTrace` (so `Q (t+1) = step (Q t) …`, supplied by the `$dff` law of
    `seq_register_correct`) gives the full source-trace correspondence. -/
theorem compileModule_seq_correct (m : Module) (hw : m.wires = []) (hr : m.reset = none)
    (har : ∀ r ∈ m.regs, r.asyncReset = none)
    (hwfd : ∀ r ∈ m.regs, WidthOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env r.next)
    (hwfo : ∀ o ∈ m.outputs, WidthOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env o.expr)
    (Q inputs : Nat → Env) :
    ∀ t, ∃ σ, ConsistentCells σ ((compileModuleM m).run {}).2.cells ∧
      (∀ o ∈ m.outputs, ∃ port ∈ ((m.outputs.foldlM compileOutput ([], [])).run
            ((m.regs.foldlM (dffStep (((m.regs.foldlM compileReg ([], [])).run
                ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock) []).run
              ((m.regs.foldlM compileReg ([], [])).run
                ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).1.1,
          port.name = o.name ∧ port.dir = Dir.output ∧
          busDen σ o.width port.bits
            = eval o.expr (cycleEnv (Q t) (inputs t) (m.regs.map (·.name)))) ∧
      (∀ r ∈ m.regs, ∃ d ∈ ((m.regs.foldlM (dffStep (((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock) []).run
          ((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).1,
          busDen σ r.width d
            = eval r.next (cycleEnv (Q t) (inputs t) (m.regs.map (·.name)))) := by
  intro t
  exact compileModule_drives m hw hr har hwfd hwfo
    (cycleEnv (Q t) (inputs t) (m.regs.map (·.name)))

/-- **Sequential correctness — general (with internal wires) reset-free case.** Like
    `compileModule_seq_correct`, but valid for modules with internal wires: at every cycle, each
    output net denotes `eval o.expr` and each register-D net denotes `eval r.next` over the
    *wire-extended* cycle environment `evalWires m.wires (cycleEnv (Q t) (inputs t) …)` — exactly the
    environment `Module.outputs?eval`/`Module.step` evaluate against.  With `Q = regTrace`, the
    netlist's output/register traces coincide with the denotational simulation. -/
theorem compileModule_seq_correct_wires (m : Module) (hr : m.reset = none)
    (har : ∀ r ∈ m.regs, r.asyncReset = none)
    (hwfd : ∀ r ∈ m.regs, WidthOK ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env r.next)
    (hwfo : ∀ o ∈ m.outputs, WidthOK ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env o.expr)
    (hwires : WiresOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env m.wires)
    (Q inputs : Nat → Env) :
    ∀ t, ∃ σ, ConsistentCells σ ((compileModuleM m).run {}).2.cells ∧
      (∀ o ∈ m.outputs, ∃ port ∈ ((m.outputs.foldlM compileOutput ([], [])).run
            ((m.regs.foldlM (dffStep (((m.regs.foldlM compileReg ([], [])).run
                ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock) []).run
              ((m.wires.foldlM compileWire []).run
                ((m.regs.foldlM compileReg ([], [])).run
                  ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).2).1.1,
          port.name = o.name ∧ port.dir = Dir.output ∧
          busDen σ o.width port.bits
            = eval o.expr (evalWires m.wires (cycleEnv (Q t) (inputs t) (m.regs.map (·.name))))) ∧
      (∀ r ∈ m.regs, ∃ d ∈ ((m.regs.foldlM (dffStep (((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) m.clock) []).run
          ((m.wires.foldlM compileWire []).run
            ((m.regs.foldlM compileReg ([], [])).run
              ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).1,
          busDen σ r.width d
            = eval r.next (evalWires m.wires (cycleEnv (Q t) (inputs t) (m.regs.map (·.name))))) := by
  intro t
  exact compileModule_drives_wires m hr har hwfd hwfo hwires
    (cycleEnv (Q t) (inputs t) (m.regs.map (·.name)))

/-- **Sequential correctness — general (with wires) synchronous-reset case.** Like
    `compileModule_seq_correct_wires`, but for `m.reset = some rst`: each register-D net denotes
    `reset ? init : next` over the wire-extended cycle environment — exactly `Module.step` with
    synchronous reset.  Together with `compileModule_seq_correct`/`_wires`, M6b now covers **all
    synchronous modules** (wire-free/with-wire × reset-free/sync-reset).  Registers with an
    *asynchronous* reset (`asyncReset = some _`, compiled to `$adff`) are excluded by `har`
    and remain unproven — `cellHolds` has no `$adff` case. -/
theorem compileModule_seq_correct_wires_reset (m : Module) (rst : String) (hr : m.reset = some rst)
    (har : ∀ r ∈ m.regs, r.asyncReset = none)
    (hwfd : ∀ r ∈ m.regs, WidthOK ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env r.next)
    (hwfo : ∀ o ∈ m.outputs, WidthOK ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env o.expr)
    (hwires : WiresOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env m.wires)
    (Q inputs : Nat → Env) :
    ∀ t, ∃ σ, ConsistentCells σ ((compileModuleM m).run {}).2.cells ∧
      (∀ o ∈ m.outputs, ∃ port ∈ ((m.outputs.foldlM compileOutput ([], [])).run
            ((m.regs.foldlM (dffStepR (((m.regs.foldlM compileReg ([], [])).run
                ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) rst m.clock) []).run
              ((m.wires.foldlM compileWire []).run
                ((m.regs.foldlM compileReg ([], [])).run
                  ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).2).1.1,
          port.name = o.name ∧ port.dir = Dir.output ∧
          busDen σ o.width port.bits
            = eval o.expr (evalWires m.wires (cycleEnv (Q t) (inputs t) (m.regs.map (·.name))))) ∧
      (∀ r ∈ m.regs, ∃ d ∈ ((m.regs.foldlM (dffStepR (((m.regs.foldlM compileReg ([], [])).run
            ((m.inputs.foldlM compileInput ([], [])).run {}).2).1.1) rst m.clock) []).run
          ((m.wires.foldlM compileWire []).run
            ((m.regs.foldlM compileReg ([], [])).run
              ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2).1,
          busDen σ r.width d
            = if busDen σ 1 (((((m.wires.foldlM compileWire []).run
                  ((m.regs.foldlM compileReg ([], [])).run
                    ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env).lookup rst).getD
                  [Bit.zero]) = 1
              then r.init
              else eval r.next (evalWires m.wires (cycleEnv (Q t) (inputs t) (m.regs.map (·.name))))) := by
  intro t
  exact compileModule_drives_wires_reset m rst hr har hwfd hwfo hwires
    (cycleEnv (Q t) (inputs t) (m.regs.map (·.name)))

end LeanRTL.CompilerModuleCorrect
