import LeanRTL.Core.CompilerModuleCorrect
import LeanRTL.Core.Check
/-!
# Executable width checkers for the module-correctness hypotheses (M6 applicability)

The flagship theorems `compileModule_seq_correct` / `_wires` / `_wires_reset` are quantified
over `WidthOK` (every `var` bound at the right width in the *compiled* environment) and
`WiresOK` (topological `WidthOK` for the wire list).  Those are `Prop`s over the compiled
name→bus environment, so they could not previously be discharged on a concrete design.

Key fact: `WidthOK cenv e` depends only on the name→**width** projection of `cenv`.  So we

1. define Boolean checkers `widthOKb` / `wiresOKb` over a plain `(name, width)` table and
   prove them sound against any `cenv` realizing that table (`CenvWidths`);
2. characterize the environments the compiler's input/register/wire phases actually build
   (`setup_cenvWidths`, `full_cenvWidths`) — each phase prepends a bus of exactly the
   declared width (`fresh`/`compileExpr_len`);
3. package everything into one executable `moduleChecksb : Module → Bool` whose truth
   (`by decide` / `rfl` on a concrete design) yields *all* the well-formedness hypotheses
   (`moduleChecks_sound`), and restate the flagship theorems with that single Boolean
   hypothesis (`compileModule_seq_correct_wires_checked`, `_wires_reset_checked`).

See `LeanRTL/Examples/Counter/ModuleCorrect.lean` for a concrete instantiation.
-/

namespace LeanRTL.CheckWidth

open LeanRTL LeanRTL.Backend LeanRTL.BackendSem LeanRTL.CompilerCorrect
  LeanRTL.CompilerModuleCorrect

/-! ## The Boolean checkers -/

/-- Boolean width checker: every `var n w` in `e` is bound in the width table `ws` at
    exactly width `w`.  Mirrors `WidthOK` structurally. -/
def widthOKb (ws : List (String × Nat)) : {w : Nat} → Expr w → Bool
  | _, .const _      => true
  | _, .var n w      => ws.lookup n == some w
  | _, .not a        => widthOKb ws a
  | _, .and a b      => widthOKb ws a && widthOKb ws b
  | _, .or a b       => widthOKb ws a && widthOKb ws b
  | _, .xor a b      => widthOKb ws a && widthOKb ws b
  | _, .add a b      => widthOKb ws a && widthOKb ws b
  | _, .sub a b      => widthOKb ws a && widthOKb ws b
  | _, .mul a b      => widthOKb ws a && widthOKb ws b
  | _, .shl a b      => widthOKb ws a && widthOKb ws b
  | _, .shr a b      => widthOKb ws a && widthOKb ws b
  | _, .sshr a b     => widthOKb ws a && widthOKb ws b
  | _, .udiv a b     => widthOKb ws a && widthOKb ws b
  | _, .umod a b     => widthOKb ws a && widthOKb ws b
  | _, .eq a b       => widthOKb ws a && widthOKb ws b
  | _, .ult a b      => widthOKb ws a && widthOKb ws b
  | _, .slt a b      => widthOKb ws a && widthOKb ws b
  | _, .mux s a b    => widthOKb ws s && widthOKb ws a && widthOKb ws b
  | _, .concat a b   => widthOKb ws a && widthOKb ws b
  | _, .zext _ a     => widthOKb ws a
  | _, .sext _ a     => widthOKb ws a
  | _, .extract _ a  => widthOKb ws a
  | _, .slice _ _ a  => widthOKb ws a

/-- Boolean topological wire checker: each wire's expression checks against the table of
    inputs/registers/*earlier* wires, then the wire's own `(name, width)` joins the table.
    Mirrors `WiresOK` structurally. -/
def wiresOKb (ws : List (String × Nat)) : List Wire → Bool
  | []        => true
  | w :: rest => widthOKb ws w.expr && wiresOKb ((w.name, w.width) :: ws) rest

/-- `cenv` realizes the name→width table `ws`: every table binding has a bus in `cenv` of
    the recorded width.  This is the *only* thing `WidthOK` needs from the compiled
    environment. -/
def CenvWidths (cenv : List (String × Bus)) (ws : List (String × Nat)) : Prop :=
  ∀ n w', ws.lookup n = some w' → ∃ bus, cenv.lookup n = some bus ∧ bus.length = w'

theorem CenvWidths_nil (cenv : List (String × Bus)) : CenvWidths cenv [] := by
  intro n w' h; simp [List.lookup] at h

/-- Prepending one binding of the right width to both sides preserves the realization. -/
theorem CenvWidths_cons {cenv : List (String × Bus)} {ws : List (String × Nat)}
    {name : String} {bus : Bus} {w : Nat}
    (hlen : bus.length = w) (h : CenvWidths cenv ws) :
    CenvWidths ((name, bus) :: cenv) ((name, w) :: ws) := by
  intro n w' hl
  rw [List.lookup_cons] at hl
  simp only [List.lookup_cons]
  cases hb : (n == name) with
  | true =>
    simp only [hb] at hl ⊢
    cases Option.some.inj hl
    exact ⟨bus, rfl, hlen⟩
  | false =>
    simp only [hb] at hl ⊢
    exact h n w' hl

/-! ## Soundness of the checkers -/

/-- **Checker soundness.** If `e` passes `widthOKb` against a width table realized by
    `cenv`, then `WidthOK cenv e`. -/
theorem widthOKb_sound {ws : List (String × Nat)} {cenv : List (String × Bus)}
    (hcw : CenvWidths cenv ws) : ∀ {w : Nat} (e : Expr w),
    widthOKb ws e = true → WidthOK cenv e := by
  intro w e
  induction e with
  | const _ => intro _; trivial
  | var n w =>
    intro h
    simp only [widthOKb] at h
    exact hcw n w (by simpa using h)
  | not a iha => intro h; exact iha h
  | and a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | or a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | xor a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | add a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | sub a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | mul a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | shl a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | shr a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | sshr a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | udiv a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | umod a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | eq a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | ult a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | slt a b iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨iha h.1, ihb h.2⟩
  | mux sg a b ihs iha ihb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h
    exact ⟨ihs h.1.1, iha h.1.2, ihb h.2⟩
  | concat ea eb ihea iheb =>
    intro h; simp only [widthOKb, Bool.and_eq_true] at h; exact ⟨ihea h.1, iheb h.2⟩
  | zext k a iha => intro h; exact iha h
  | sext k a iha => intro h; exact iha h
  | extract idx a iha => intro h; exact iha h
  | slice lo len a iha => intro h; exact iha h

/-- **Wire-checker soundness.**  The `∀ bus, bus.length = w.width → …` obligation of
    `WiresOK` follows because prepending `(w.name, bus)` to `cenv` and `(w.name, w.width)`
    to `ws` preserves `CenvWidths` for *any* bus of the declared width. -/
theorem wiresOKb_sound : ∀ (wires : List Wire) (ws : List (String × Nat))
    (cenv : List (String × Bus)), wiresOKb ws wires = true → CenvWidths cenv ws →
    WiresOK cenv wires := by
  intro wires
  induction wires with
  | nil => intro ws cenv _ _; trivial
  | cons w rest ih =>
    intro ws cenv hb hcw
    simp only [wiresOKb, Bool.and_eq_true] at hb
    refine ⟨widthOKb_sound hcw w.expr hb.1, ?_⟩
    intro bus hlen
    exact ih ((w.name, w.width) :: ws) ((w.name, bus) :: cenv) hb.2 (CenvWidths_cons hlen hcw)

/-! ## The compiled environments realize the declared width tables -/

/-- Width table grown by the input phase (mirrors the env fold: prepends per input). -/
def inputWidths (inputs : List InPort) (ws : List (String × Nat)) : List (String × Nat) :=
  inputs.foldl (fun acc p => (p.name, p.width) :: acc) ws

/-- Width table grown by the register phase. -/
def regWidths (regs : List Reg) (ws : List (String × Nat)) : List (String × Nat) :=
  regs.foldl (fun acc r => (r.name, r.width) :: acc) ws

/-- Width table grown by the wire phase. -/
def wireWidths (wires : List Wire) (ws : List (String × Nat)) : List (String × Nat) :=
  wires.foldl (fun acc w => (w.name, w.width) :: acc) ws

/-- The name→width table after the setup (inputs, then registers) phases. -/
def setupWidths (m : Module) : List (String × Nat) :=
  regWidths m.regs (inputWidths m.inputs [])

/-- The full name→width table after setup and the wire phase — the table the register
    next-state and output expressions are checked against. -/
def fullWidths (m : Module) : List (String × Nat) :=
  wireWidths m.wires (setupWidths m)

/-- The input phase binds each input to a `fresh`-allocated bus of exactly its width. -/
theorem compileInputs_cenvWidths (inputs : List InPort) (acc : List Port × List NetName)
    (s : CState) (ws : List (String × Nat)) (h : CenvWidths s.env ws) :
    CenvWidths ((inputs.foldlM compileInput acc).run s).2.env (inputWidths inputs ws) := by
  induction inputs generalizing acc s ws with
  | nil => exact h
  | cons p ps ih =>
    rw [List.foldlM_cons]
    show CenvWidths ((ps.foldlM compileInput _).run ((compileInput acc p).run s).2).2.env
      (inputWidths ps ((p.name, p.width) :: ws))
    refine ih _ ((compileInput acc p).run s).2 ((p.name, p.width) :: ws) ?_
    rw [compileInput_env]
    exact CenvWidths_cons (by simp [freshBus]) h

/-- The register phase binds each register to a `fresh`-allocated bus of exactly its width. -/
theorem compileRegs_cenvWidths (regs : List Reg) (acc : List (String × Bus) × List NetName)
    (s : CState) (ws : List (String × Nat)) (h : CenvWidths s.env ws) :
    CenvWidths ((regs.foldlM compileReg acc).run s).2.env (regWidths regs ws) := by
  induction regs generalizing acc s ws with
  | nil => exact h
  | cons r rs ih =>
    rw [List.foldlM_cons]
    show CenvWidths ((rs.foldlM compileReg _).run ((compileReg acc r).run s).2).2.env
      (regWidths rs ((r.name, r.width) :: ws))
    refine ih _ ((compileReg acc r).run s).2 ((r.name, r.width) :: ws) ?_
    rw [compileReg_env]
    exact CenvWidths_cons (by simp [freshBus]) h

/-- The wire phase binds each wire to its compiled cone's output bus, whose length is the
    declared width (`compileExpr_len`, using the wire's own `widthOKb` check). -/
theorem compileWires_cenvWidths (wires : List Wire) (acc : List NetName)
    (s : CState) (ws : List (String × Nat)) (h : CenvWidths s.env ws)
    (hb : wiresOKb ws wires = true) :
    CenvWidths ((wires.foldlM compileWire acc).run s).2.env (wireWidths wires ws) := by
  induction wires generalizing acc s ws with
  | nil => exact h
  | cons w rest ih =>
    simp only [wiresOKb, Bool.and_eq_true] at hb
    rw [List.foldlM_cons]
    show CenvWidths ((rest.foldlM compileWire _).run ((compileWire acc w).run s).2).2.env
      (wireWidths rest ((w.name, w.width) :: ws))
    refine ih _ ((compileWire acc w).run s).2 ((w.name, w.width) :: ws) ?_ hb.2
    rw [compileWire_env, compileExpr_env]
    exact CenvWidths_cons
      (compileExpr_len w.expr (supp_all w.expr) s (widthOKb_sound h w.expr hb.1)) h

/-- **Setup-environment characterization.** The post-setup compiled environment (of
    `compileModuleM`, i.e. inputs then registers from the empty state) realizes the
    module's declared setup width table. -/
theorem setup_cenvWidths (m : Module) :
    CenvWidths ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env (setupWidths m) :=
  compileRegs_cenvWidths m.regs ([], []) _ _
    (compileInputs_cenvWidths m.inputs ([], []) {} [] (CenvWidths_nil _))

/-- **Full-environment characterization.** If the wires pass `wiresOKb`, the post-wire
    compiled environment realizes the full declared width table — exactly the environment
    the flagship theorems' `WidthOK` hypotheses are stated against. -/
theorem full_cenvWidths (m : Module) (hw : wiresOKb (setupWidths m) m.wires = true) :
    CenvWidths ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env (fullWidths m) :=
  compileWires_cenvWidths m.wires [] _ _ (setup_cenvWidths m) hw

/-! ## The single module-level check -/

/-- **Executable module well-formedness check.**  True iff
    * no register uses an asynchronous reset (`asyncReset`), an asynchronous load (`asyncLoad`),
      or a per-register clock (`clockNet`) — the flagship theorems' plain `$dff`, module-clock
      shape (those features are lowered by unproven post-passes, pinned per-instance instead),
    * the module has no addressed memories (`mems = []` — the `$mem_v2` post-pass likewise
      carries no whole-design theorem),
    * the wire list is topologically width-correct (`wiresOKb`), and
    * every register next-state and output expression is width-correct against the full
      width table (`widthOKb`).
    On a concrete design this evaluates by `decide`/`rfl`; `moduleChecks_sound` turns its
    truth into all the well-formedness hypotheses of the module-correctness theorems. -/
def moduleChecksb (m : Module) : Bool :=
  m.regs.all (fun r => r.asyncReset.isNone)
    && m.regs.all (fun r => r.asyncLoad.isNone)
    && m.regs.all (fun r => r.clockNet.isNone)
    && m.mems.isEmpty
    && wiresOKb (setupWidths m) m.wires
    && m.regs.all (fun r => widthOKb (fullWidths m) r.next)
    && m.outputs.all (fun o => widthOKb (fullWidths m) o.expr)

/-- **Check soundness (hypothesis package).**  `moduleChecksb m = true` discharges every
    well-formedness hypothesis of `compileModule_seq_correct_wires` /
    `compileModule_seq_correct_wires_reset` at `m`: the async-reset-freedom, the two
    `WidthOK` families against the post-wire compiled environment, and the topological
    `WiresOK` against the post-setup compiled environment. -/
theorem moduleChecks_sound (m : Module) (h : moduleChecksb m = true) :
    (∀ r ∈ m.regs, r.asyncReset = none) ∧
    (∀ r ∈ m.regs, WidthOK ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env r.next) ∧
    (∀ o ∈ m.outputs, WidthOK ((m.wires.foldlM compileWire []).run
        ((m.regs.foldlM compileReg ([], [])).run
          ((m.inputs.foldlM compileInput ([], [])).run {}).2).2).2.env o.expr) ∧
    WiresOK ((m.regs.foldlM compileReg ([], [])).run
        ((m.inputs.foldlM compileInput ([], [])).run {}).2).2.env m.wires := by
  simp only [moduleChecksb, Bool.and_eq_true, List.all_eq_true] at h
  -- F6/F11/mem: the extra `asyncLoad.isNone` (`_hal`), `clockNet.isNone` (`_hcn`), and
  -- `mems.isEmpty` (`_hmem`) conjuncts make `moduleChecksb` reject any register carrying an async
  -- load or a per-register (multi-/gated-)clock net, and any module carrying an addressed memory —
  -- those compile via a post-pass outside the whole-design theorems (an `$aldff`, a flip-flop
  -- clocked off a derived net, or a `$mem_v2` array), so all three are intentionally discarded here
  -- (the theorems apply only to the `$dff` shape clocked by the single module clock).
  obtain ⟨⟨⟨⟨⟨⟨har, _hal⟩, _hcn⟩, _hmem⟩, hwires⟩, hregs⟩, houts⟩ := h
  have hfull := full_cenvWidths m hwires
  exact ⟨fun r hr => Option.isNone_iff_eq_none.mp (har r hr),
         fun r hr => widthOKb_sound hfull r.next (hregs r hr),
         fun o ho => widthOKb_sound hfull o.expr (houts o ho),
         wiresOKb_sound m.wires (setupWidths m) _ hwires (setup_cenvWidths m)⟩

/-! ## Flagship theorems with executable side conditions

The two theorems below are `compileModule_seq_correct_wires` and
`compileModule_seq_correct_wires_reset` with all `WidthOK`/`WiresOK`/async hypotheses
replaced by the single decidable `moduleChecksb m = true` — dischargeable by `by decide`
(or `rfl`) on any concrete design.  Together they cover every module shape
(with/without wires × reset-free/sync-reset; the wire-free case is `wires = []`). -/

/-- **Checked sequential correctness (with wires, reset-free).** -/
theorem compileModule_seq_correct_wires_checked (m : Module) (hr : m.reset = none)
    (hchk : moduleChecksb m = true) (Q inputs : Nat → Env) :
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
  obtain ⟨har, hwfd, hwfo, hwires⟩ := moduleChecks_sound m hchk
  exact compileModule_seq_correct_wires m hr har hwfd hwfo hwires Q inputs

/-- **Checked sequential correctness (with wires, synchronous reset).** -/
theorem compileModule_seq_correct_wires_reset_checked (m : Module) (rst : String)
    (hr : m.reset = some rst) (hchk : moduleChecksb m = true) (Q inputs : Nat → Env) :
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
  obtain ⟨har, hwfd, hwfo, hwires⟩ := moduleChecks_sound m hchk
  exact compileModule_seq_correct_wires_reset m rst hr har hwfd hwfo hwires Q inputs

end LeanRTL.CheckWidth
