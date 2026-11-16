import LeanRTL.Core.CheckWidth
/-!
# `Module.semanticCoverage` — the "language ≤ semantics" boundary as a machine verdict (M32)

The LeanRTL *object language* can express more than the *reference semantics*
(`Module.simulate` / `Module.step`, the one-active-edge-per-cycle Moore model) faithfully
models.  Which constructs fall outside that model was, until now, a prose convention
scattered across per-design honesty notes.  This file promotes that boundary to a *decidable
verdict*: for any `Module`, `Module.semanticCoverage` reports whether the whole-design
simulate theorems apply, and — when they do not — exactly *which* out-of-model constructs are
responsible.

The M6 executable gate `CheckWidth.moduleChecksb` already *pins* the applicability of the
flagship whole-design theorems (`compileModule_seq_correct_wires_checked` /
`_reset_checked`).  But it is a bare `Bool`: on a `false` it says nothing about *why*, and —
being tuned to the compiler-correctness hypotheses — it does **not** flag two constructs that
are genuinely outside `Module.simulate`'s reach yet do not disturb the compiler proof:
level-sensitive **latches** (`Module.latches`) and **dual-edge** designs (a posedge and a
negedge register coexisting).  `semanticCoverage` is the *honest, strictly stronger* verdict:
its `.full` implies `moduleChecksb = true` (given width well-formedness, `semanticCoverage_full_moduleChecks`)
**and** additionally rules out latches and dual-edge interleaving.

## The verdict

* `Coverage.full` — no out-of-model construct: the whole-design simulate theorems apply.
* `Coverage.perRegister reasons` — at least one construct puts the design on the
  per-register / per-access characterization + co-simulation path; `reasons` lists which.

Each `CoverageReason` corresponds to a row of the CORE.md §1.1/§1.3 capability matrix.
-/

namespace LeanRTL

/-- A single reason the reference semantics does **not** fully cover a design — an
    out-of-model construct the object language can express but `Module.simulate` cannot
    faithfully model.  Each maps to a capability-matrix row (CORE.md §1.1/§1.3). -/
inductive CoverageReason where
  /-- F4 asynchronous reset (`Reg.asyncReset`, a `$adff`): fires between clock edges;
      `moduleChecksb` gates it out of the whole-design theorems. -/
  | asyncReset
  /-- F6 asynchronous dynamic load (`Reg.asyncLoad`, a `$aldff`): loads a runtime value
      between clock edges; `moduleChecksb` gates it out. -/
  | asyncLoad
  /-- F11 per-register clock net (`Reg.clockNet`): multi-clock / gated / derived clock;
      `Module.simulate` is single-clock, so `moduleChecksb` gates it out. -/
  | clockNet
  /-- Dual-edge design: a posedge register and a negedge register coexist.  The two edges
      interleave *within* a clock period, which the one-edge-per-cycle model does not
      capture.  (Pure single-edge negedge stays in the model — see `WholeDesign/Negedge`.) -/
  | negedgeMix
  /-- F8 level-sensitive transparent latch (`Module.latches`, a `$dlatch`): intra-cycle
      transparency is not represented by the Moore one-value-per-cycle model. -/
  | latch
  /-- Addressed memory array (`Module.mems`, a `$mem_v2`): the register-file Moore model
      carries no memory array; `moduleChecksb` gates any non-empty `mems` out. -/
  | memShape
  /-- F13 delay-driven timebase (`Module.stepDelay`): the design advances on `#n` rather than a
      clock edge.  The cycle model is untouched — a step is still a step, and every `simulate`
      theorem about this module holds — but *what makes a step happen* has left the model, so
      nothing in Lean fixes the emitted design's relationship to simulation time, and no netlist
      equivalence check can see the delay at all. -/
  | timedStep
  /-- Fixed-seed simulation does not quantify over arbitrary power-on states. -/
  | unconstrainedInit
  deriving DecidableEq, Repr

/-- A one-line human-readable explanation of a coverage reason (used by `leanrtl check`). -/
def CoverageReason.describe : CoverageReason → String
  | .asyncReset =>
      "asyncReset — register(s) use an asynchronous reset ($adff), which fires between clock edges; " ++
      "the reset EDGE is outside the whole-design simulate class (pinned per-register by Reg.arstDen " ++
      "+ co-simulation), but Module.step/simulate never read asyncReset, so if this is the only " ++
      "reason listed (Module.coveredModuloArstb) the whole-design theorems still apply verbatim via " ++
      "Module.eraseArst_simulate — scoped to the reset-inactive segment UNLESS the same reset is " ++
      "also folded in-band (Module.arstFoldedb), in which case Reg.arstFolded_arstDen removes the " ++
      "scoping and every clock edge is covered.  Fold AND declare; do NOT downgrade to a " ++
      "synchronous reset to regain them"
  | .asyncLoad =>
      "asyncLoad — register(s) asynchronously load a dynamic value ($aldff); " ++
      "outside the whole-design simulate class (pinned per-register + co-simulation)"
  | .clockNet =>
      "clockNet — register(s) clocked by a per-register/derived net (multi-clock / gated clock); " ++
      "Module.simulate is single-clock, so outside the whole-design simulate class (pinned per-register + co-simulation)"
  | .negedgeMix =>
      "negedgeMix — posedge and negedge registers coexist (dual-edge); " ++
      "the one-edge-per-cycle model does not capture their sub-cycle interleaving (pinned per-register + co-simulation)"
  | .latch =>
      "latch — level-sensitive transparent latch(es) ($dlatch); " ++
      "their intra-cycle transparency is not modelled by Module.simulate (pinned by Latch.den + co-simulation)"
  | .memShape =>
      "memShape — addressed memory array(s) ($mem_v2); " ++
      "the register-file Moore model carries no memory array (pinned per-access + co-simulation)"
  | .timedStep =>
      "timedStep — the step timebase is delay-driven (#n), not a clock edge; " ++
      "the cycle semantics still apply, but the map from cycles to simulation time is outside the " ++
      "model and the emitted always block is unreachable by the equivalence miter (clocked-rendering " ++
      "miter + one-line delta check)"
  | .unconstrainedInit =>
      "unconstrainedInit — register(s) have no hardware power-on constraint; use step theorems " ++
      "from corresponding arbitrary states, not Module.simulate's fixed initial seed"

/-- The whole-design semantic-coverage verdict of a module. -/
inductive Coverage where
  /-- No out-of-model construct: the whole-design simulate theorems apply. -/
  | full
  /-- One or more constructs put the design on the per-register / per-access +
      co-simulation path; `reasons` enumerates them. -/
  | perRegister (reasons : List CoverageReason)
  deriving DecidableEq, Repr

/-! ## The verdict, as decidable functions -/

/-- The out-of-model constructs present in `m`, in capability-matrix order.  Empty iff the
    design is fully covered by the reference semantics. -/
def Module.coverageReasons (m : Module) : List CoverageReason :=
  (if m.regs.any (fun r => r.asyncReset.isSome) then [CoverageReason.asyncReset] else [])
    ++ (if m.regs.any (fun r => r.asyncLoad.isSome) then [CoverageReason.asyncLoad] else [])
    ++ (if m.regs.any (fun r => r.clockNet.isSome) then [CoverageReason.clockNet] else [])
    ++ (if m.regs.any (fun r => r.negedge) && m.regs.any (fun r => !r.negedge)
          then [CoverageReason.negedgeMix] else [])
    ++ (if !m.latches.isEmpty then [CoverageReason.latch] else [])
    ++ (if !m.mems.isEmpty then [CoverageReason.memShape] else [])
    ++ (if m.stepDelay.isSome then [CoverageReason.timedStep] else [])
    ++ (if m.regs.any (fun r => !r.emitInit) then [CoverageReason.unconstrainedInit] else [])

/-- Boolean form of "fully covered": no out-of-model construct.  The first four conjuncts
    are exactly the *construct* conjuncts of `CheckWidth.moduleChecksb` (verbatim); the last
    three (`latches` empty, no dual-edge, no delay-driven timebase) are the honest strengthening
    `moduleChecksb` misses. -/
def Module.fullyCoveredb (m : Module) : Bool :=
  m.regs.all (fun r => r.asyncReset.isNone)
    && m.regs.all (fun r => r.asyncLoad.isNone)
    && m.regs.all (fun r => r.clockNet.isNone)
    && m.mems.isEmpty
    && m.latches.isEmpty
    && !(m.regs.any (fun r => r.negedge) && m.regs.any (fun r => !r.negedge))
    && m.stepDelay.isNone
    && m.regs.all (fun r => r.emitInit)

/-- **The semantic-coverage verdict.**  `.full` iff no out-of-model construct is present;
    otherwise `.perRegister reasons` naming the offending constructs. -/
def Module.semanticCoverage (m : Module) : Coverage :=
  if m.fullyCoveredb then .full else .perRegister m.coverageReasons

/-! ## Covered modulo the asynchronous reset (F4)

`fullyCoveredb` demands `asyncReset.isNone`, and that demand is right: an `$adff` fires
*between* clock edges and the one-edge-per-cycle model does not represent that.  But it was
also being read as "declaring an async reset costs you the whole-design `simulate` theorem",
and that is false.  `Module.step` / `Module.simulate` never read `Reg.asyncReset` at all —
`Module.eraseArst_simulate` (Core/Semantics.lean) proves `m.simulate = m.eraseArst.simulate`
outright.  So the whole-design theorem an author would have written for the synchronous twin
holds verbatim of the async design, on the segment where the reset stays inactive — and on *every*
cycle, reset-active ones included, as soon as the same reset is also folded in-band, which is what
`Module.arstFoldedb` / `Reg.arstFolded_arstDen` (Core/Semantics.lean) decide and prove.  The fold
and the declaration are complements: the fold gives the cycle model its reset-active edges, the
declaration gives the emitted Verilog its `negedge rst_n`.

`coveredModuloArstb` is the decidable verdict for exactly that situation: *the async reset is
the only thing out of model*.  It is deliberately **not** a new `Coverage` constructor —
`semanticCoverage` keeps reporting `.perRegister [.asyncReset]`, which stays honest about the
reset edge, and every existing exhaustive match on `Coverage` keeps compiling. -/

/-- **Fully covered except for the asynchronous reset.**  True when the design *does* carry an
    async reset and erasing it would make the design fully covered — i.e. the `$adff` is the
    single out-of-model construct.  Such a design gets the whole-design results by transport
    along `Module.eraseArst_simulate`, scoped to the reset-inactive segment unless
    `Module.arstFoldedb` also holds, which removes the scoping; the reset value itself is covered
    per register by `Reg.arstDen`. -/
def Module.coveredModuloArstb (m : Module) : Bool :=
  m.regs.any (fun r => r.asyncReset.isSome) && m.eraseArst.fullyCoveredb

/-- A design is never both fully covered and covered-modulo-async-reset. -/
theorem coveredModuloArst_not_full (m : Module) (h : m.coveredModuloArstb = true) :
    m.fullyCoveredb = false := by
  simp only [Module.coveredModuloArstb, Bool.and_eq_true] at h
  have hall : m.regs.all (fun r => r.asyncReset.isNone) = false := by
    cases hb : m.regs.all (fun r => r.asyncReset.isNone) with
    | false => rfl
    | true =>
        obtain ⟨r, hr, hrs⟩ := List.any_eq_true.mp h.1
        have hn := List.all_eq_true.mp hb r hr
        cases hopt : r.asyncReset with
        | none      => rw [hopt] at hrs; simp at hrs
        | some _    => rw [hopt] at hn;  simp at hn
  simp [Module.fullyCoveredb, hall]

/-- The erased twin is fully covered — the verdict's whole content, made usable. -/
theorem coveredModuloArst_eraseArst_full (m : Module) (h : m.coveredModuloArstb = true) :
    m.eraseArst.semanticCoverage = .full := by
  simp only [Module.coveredModuloArstb, Bool.and_eq_true] at h
  simp [Module.semanticCoverage, h.2]

/-- The *width* half of `CheckWidth.moduleChecksb` (verbatim): the wire list is topologically
    width-correct, and every register next-state / output cone is width-correct against the
    post-wire compiled environment.  This is orthogonal well-formedness (the same obligation
    `Module.checkErrors` lints) — *not* a semantic-coverage question — so it is a separate
    hypothesis of the certification theorem rather than a `CoverageReason`. -/
def Module.wellWidthedb (m : Module) : Bool :=
  CheckWidth.wiresOKb (CheckWidth.setupWidths m) m.wires
    && m.regs.all (fun r => CheckWidth.widthOKb (CheckWidth.fullWidths m) r.next)
    && m.outputs.all (fun o => CheckWidth.widthOKb (CheckWidth.fullWidths m) o.expr)

/-! ## Soundness: full coverage certifies the whole-design simulate class -/

/-- `.full` unfolds to `fullyCoveredb = true`. -/
theorem semanticCoverage_full_fullyCovered (m : Module)
    (h : m.semanticCoverage = .full) : m.fullyCoveredb = true := by
  simp only [Module.semanticCoverage] at h
  split at h
  · assumption
  · exact absurd h (by simp)

/-- **Full coverage ⟹ no out-of-model construct.**  Every construct the reference semantics
    cannot faithfully model is absent — the honest "language ≤ semantics" certificate. -/
theorem semanticCoverage_full_constructs (m : Module) (h : m.semanticCoverage = .full) :
    m.regs.all (fun r => r.asyncReset.isNone) = true ∧
    m.regs.all (fun r => r.asyncLoad.isNone) = true ∧
    m.regs.all (fun r => r.clockNet.isNone) = true ∧
    m.mems.isEmpty = true ∧
    m.latches.isEmpty = true ∧
    (m.regs.any (fun r => r.negedge) && m.regs.any (fun r => !r.negedge)) = false ∧
    m.stepDelay.isNone = true ∧
    m.regs.all (fun r => r.emitInit) = true := by
  have hf := semanticCoverage_full_fullyCovered m h
  simp only [Module.fullyCoveredb, Bool.and_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨⟨⟨har, hal⟩, hcn⟩, hmem⟩, hlatch⟩, hneg⟩, hstep⟩, hinit⟩ := hf
  refine ⟨har, hal, hcn, hmem, hlatch, ?_, hstep, hinit⟩
  -- `hneg : (!(X && Y)) = true`; case-split the Bool to read off `(X && Y) = false`.
  cases hh : (m.regs.any (fun r => r.negedge) && m.regs.any (fun r => !r.negedge)) with
  | false => rfl
  | true  => rw [hh] at hneg; simp at hneg

/-- **`semanticCoverage = .full` certifies the M6 gate.**  Given width well-formedness
    (`hw`, the orthogonal lint obligation), full semantic coverage discharges the *whole*
    `CheckWidth.moduleChecksb` hypothesis — so the checked flagship theorems
    `compileModule_seq_correct_wires_checked` / `_reset_checked` apply verbatim.

    This is the machine form of "language ≤ semantics ⟹ the whole-design simulate class
    applies": no re-proof, just a reduction to the existing M6 gate. -/
theorem semanticCoverage_full_moduleChecks (m : Module)
    (h : m.semanticCoverage = .full) (hw : m.wellWidthedb = true) :
    CheckWidth.moduleChecksb m = true := by
  have hf := semanticCoverage_full_fullyCovered m h
  simp only [Module.fullyCoveredb, Bool.and_eq_true] at hf
  simp only [Module.wellWidthedb, Bool.and_eq_true] at hw
  obtain ⟨⟨⟨⟨⟨⟨⟨har, hal⟩, hcn⟩, hmem⟩, _hlatch⟩, _hneg⟩, _hstep⟩, _hinit⟩ := hf
  obtain ⟨⟨hwires, hnext⟩, houts⟩ := hw
  simp only [CheckWidth.moduleChecksb, Bool.and_eq_true]
  exact ⟨⟨⟨⟨⟨⟨har, hal⟩, hcn⟩, hmem⟩, hwires⟩, hnext⟩, houts⟩

/-! ## Soundness: covered-modulo-async-reset certifies the same class on the erased twin -/

/-- The setup width table is blind to the erasure (it reads `name` / `width` only). -/
theorem eraseArst_setupWidths (m : Module) :
    CheckWidth.setupWidths m.eraseArst = CheckWidth.setupWidths m := by
  simp [CheckWidth.setupWidths, CheckWidth.regWidths, Module.eraseArst, List.foldl_map]

/-- Hence so is the full table. -/
theorem eraseArst_fullWidths (m : Module) :
    CheckWidth.fullWidths m.eraseArst = CheckWidth.fullWidths m := by
  simp only [CheckWidth.fullWidths, eraseArst_setupWidths,
    show m.eraseArst.wires = m.wires from rfl]

/-- The register `next` cones survive the erasure unchanged. -/
theorem eraseArst_regsAllNext (m : Module) (ws : List (String × Nat)) :
    m.eraseArst.regs.all (fun r => CheckWidth.widthOKb ws r.next)
      = m.regs.all (fun r => CheckWidth.widthOKb ws r.next) := by
  simp [Module.eraseArst, List.all_map, Function.comp_def]

/-- **Width well-formedness is blind to the async reset.**  It reads `name` / `width` / `next`,
    all preserved by the erasure — so an author discharges the `hw` hypothesis below by
    `decide` on `m` itself, never on the twin. -/
theorem eraseArst_wellWidthed (m : Module) : m.eraseArst.wellWidthedb = m.wellWidthedb := by
  simp only [Module.wellWidthedb, eraseArst_setupWidths, eraseArst_fullWidths,
    eraseArst_regsAllNext, show m.eraseArst.wires = m.wires from rfl,
    show m.eraseArst.outputs = m.outputs from rfl]

/-- **`coveredModuloArstb` certifies the M6 gate on the erased twin.**  Given the same
    orthogonal width obligation (`hw`, stated on `m` itself), a design whose *only* out-of-model
    construct is the asynchronous reset discharges `CheckWidth.moduleChecksb m.eraseArst`, so the
    checked flagship theorems `compileModule_seq_correct_wires_checked` / `_reset_checked` apply
    verbatim to `m.eraseArst`.

    Combined with `Module.eraseArst_simulate` (`m.simulate = m.eraseArst.simulate`), this puts
    the *whole-design* result on the shipped design `m` — **scoped to the reset-inactive
    segment**.  What is deliberately not claimed: the compiled netlist of `m` carries `$adff`
    cells where the twin's carries `$dff`, so the compiler-correctness statement transports to
    `m` only on traces where no declared reset net reaches its active level.  A reset firing
    between clock edges is outside this theorem, `Reg.arstDen` is the per-register law that
    covers the reset value, and co-simulation is what validates the two together. -/
theorem coveredModuloArst_moduleChecks (m : Module)
    (h : m.coveredModuloArstb = true) (hw : m.wellWidthedb = true) :
    CheckWidth.moduleChecksb m.eraseArst = true :=
  semanticCoverage_full_moduleChecks m.eraseArst
    (coveredModuloArst_eraseArst_full m h)
    (by rw [eraseArst_wellWidthed]; exact hw)

end LeanRTL
