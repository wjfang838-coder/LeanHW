import LeanRTL.Core.HierRefine
/-!
# `Parent.regTrace` over the HIERARCHICAL `simulateSeq` state (wire-free children)

`HierRefine.lean` states the parent whole-trace `Parent.regTrace p` over the **flat `Module`**
`flattenParentSeq p`.  `HierSeqCorrect.lean`'s per-instance characterizations
(`flatNext_eq_childStep` / `flatOut_eq_childOut`) pin each flat register/output faithful to the
child's own `Module.step` / `Module.outputs?eval` — but only for a **wire-free child**.

This file discharges the documented extension: under an explicit **wire-free-children** hypothesis
(`WFParentSeq p`), the flat-`Module` whole-trace ALSO equals the hierarchical
`Parent.nextFlat` / `Parent.simulateSeq` register state.  The bridge is a sequential analogue of the
combinational `HierCorrect.flat_fold`: a joint induction over the instance list (`flatSeq_fold`)
shows the flat module's `evalWires` reproduces, on every parent-input and instance-output net, exactly
the values `Parent.cycleEnvList` computes — now carrying each child's register file through the fold.

## Honest scope

The three step-level bridges and the trace corollary hold **conditionally** on `WFParentSeq p`:
every child is wire-free (`inst.child.wires = []`), reset-free (`inst.child.reset = none` — the flat
reset-free trace `fun _ => false` is the honest match, exactly what L3 `Parent.simRefines_trace`
uses), each child output/next references only its bound input ports or registers, each instance
expression references only already-defined names (parent inputs and *earlier* instance outputs — so
inter-instance carry chains are supported, just like `WFInsts`), and the net names are distinct.
Both proof-of-concept parents (`sync_serial`, the equalizer) have **wire-carrying** children, so
NEITHER satisfies `WFParentSeq`; for those the flat-`Module` whole-trace of `HierRefine` remains the
delivered form.  A clean conditional theorem is the deliverable: it is the general hierarchical bridge
for wire-free-children parents.
-/

namespace LeanRTL
open LeanRTL.CompilerCorrectSeq

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Small `List` helpers -/

theorem contains_true_of_mem {l : List String} {n : String} (h : n ∈ l) :
    l.contains n = true := List.elem_eq_true_of_mem h

theorem contains_false_of_not_mem {l : List String} {n : String} (h : n ∉ l) :
    l.contains n = false := by
  cases hc : l.contains n with
  | false => rfl
  | true => exact absurd (List.mem_of_elem_eq_true hc) h

/-- `Env.ofList` at a key of a nodup-keyed assoc list returns that key's value. -/
theorem ofList_mem_nodup (xs : List (String × Nat)) (k : String) (v : Nat)
    (h : (k, v) ∈ xs) (hnd : (xs.map (·.1)).Nodup) : Env.ofList xs k = v := by
  have hx : xs.map (fun x => (x.1, x.2)) = xs := by simp
  have hlm := ofList_lookup_mem xs (·.1) (·.2) (k, v) h hnd
  rw [hx] at hlm
  exact hlm

/-- `List.find? (·.name = r.name)` returns `r` when the names are nodup and `r` is present. -/
theorem find?_name_nodup (regs : List Reg) (r : Reg)
    (h : r ∈ regs) (hnd : (regs.map (·.name)).Nodup) :
    regs.find? (·.name = r.name) = some r := by
  induction regs with
  | nil => simp at h
  | cons a rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hanr, hndr⟩ := hnd
      rcases List.mem_cons.mp h with rfl | hr
      · simp
      · have hane : ¬ (a.name = r.name) := by
          intro hc; exact hanr (hc ▸ List.mem_map.mpr ⟨r, hr, rfl⟩)
        rw [List.find?_cons]
        simp only [hane]
        exact ih hr hndr

/-! ## `substRename` free variables -/

/-- The names a `substRename`d expression can reference: an instance-expression variable (in `known`)
    or a *renamed* child-internal name (a register, once outputs are closed over ports+registers). -/
theorem substRename_vars (ins : List (String × AnyExpr)) (ren : String → String)
    (known regNames : List String) :
    {w : Nat} → (e : Expr w) → (hb : ∀ n ∈ e.vars, n ∈ ins.map (·.1) ∨ n ∈ regNames) →
    (hins : ∀ pe ∈ ins, ∀ n ∈ pe.2.2.vars, n ∈ known) →
    ∀ k ∈ (substRename ins ren e).vars, k ∈ known ∨ k ∈ regNames.map ren
  | _, .const v, _, _ => by intro k hk; simp [substRename, Expr.vars] at hk
  | _, .var x w, hb, hins => by
      intro k hk
      cases h : ins.lookup x with
      | some ae =>
          have haemem : (x, ae) ∈ ins := by
            obtain ⟨l₁, l₂, hl, _⟩ := List.lookup_eq_some_iff.mp h; rw [hl]; simp
          simp only [substRename, h, Expr.vars] at hk
          exact Or.inl (hins (x, ae) haemem k hk)
      | none =>
          simp only [substRename, h, Expr.vars, List.mem_singleton] at hk
          subst hk
          have hxmem : x ∈ regNames := by
            rcases hb x (by simp [Expr.vars]) with hin | hreg
            · exfalso
              obtain ⟨p, hp, hpx⟩ := List.mem_map.mp hin
              have hsome : (ins.lookup x).isSome := by
                rw [List.lookup_isSome_iff]; exact ⟨p, hp, by simp [hpx]⟩
              rw [h] at hsome; simp at hsome
            · exact hreg
          exact Or.inr (List.mem_map.mpr ⟨x, hxmem, rfl⟩)
  | _, .not a, hb, hins => by
      simpa [substRename, Expr.vars] using substRename_vars ins ren known regNames a hb hins
  | _, .zext k a, hb, hins => by
      simpa [substRename, Expr.vars] using substRename_vars ins ren known regNames a hb hins
  | _, .sext k a, hb, hins => by
      simpa [substRename, Expr.vars] using substRename_vars ins ren known regNames a hb hins
  | _, .extract i a, hb, hins => by
      simpa [substRename, Expr.vars] using substRename_vars ins ren known regNames a hb hins
  | _, .slice lo len a, hb, hins => by
      simpa [substRename, Expr.vars] using substRename_vars ins ren known regNames a hb hins
  | _, .mux s a b, hb, hins => by
      intro k hk
      simp only [substRename, Expr.vars, List.mem_append] at hk
      rcases hk with (hk | hk) | hk
      · exact substRename_vars ins ren known regNames s
          (fun m hm => hb m (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hm))))) hins k hk
      · exact substRename_vars ins ren known regNames a
          (fun m hm => hb m (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm))))) hins k hk
      · exact substRename_vars ins ren known regNames b
          (fun m hm => hb m (List.mem_append.mpr (Or.inr hm))) hins k hk
  | _, .and a b, hb, hins | _, .or a b, hb, hins | _, .xor a b, hb, hins | _, .add a b, hb, hins
  | _, .sub a b, hb, hins | _, .mul a b, hb, hins | _, .shl a b, hb, hins | _, .shr a b, hb, hins
  | _, .sshr a b, hb, hins | _, .udiv a b, hb, hins | _, .umod a b, hb, hins | _, .eq a b, hb, hins
  | _, .ult a b, hb, hins | _, .slt a b, hb, hins | _, .concat a b, hb, hins => by
      intro k hk
      simp only [substRename, Expr.vars, List.mem_append] at hk
      rcases hk with hk | hk
      · exact substRename_vars ins ren known regNames a
          (fun m hm => hb m (List.mem_append.mpr (Or.inl hm))) hins k hk
      · exact substRename_vars ins ren known regNames b
          (fun m hm => hb m (List.mem_append.mpr (Or.inr hm))) hins k hk

/-! ## The flattened wire list for a wire-free child -/

/-- The flattened registers of the whole parent, by name — `"<inst>.<reg>"` for each child register. -/
def regNamesOf (insts : List Inst) : List String :=
  insts.flatMap (fun inst => inst.child.regs.map (fun r => inst.rename r.name))

theorem flatWiresSeq_wirefree (inst : Inst) (hwire : inst.child.wires = []) :
    Inst.flatWiresSeq inst = inst.child.outputs.map (fun o =>
      { name := inst.rename o.name, width := o.width,
        expr := substRename inst.ins inst.rename o.expr }) := by
  simp [Inst.flatWiresSeq, hwire]

theorem flatWiresSeq_names_wirefree (inst : Inst) (hwire : inst.child.wires = []) :
    (Inst.flatWiresSeq inst).map (·.name) = instOutNames inst := by
  rw [flatWiresSeq_wirefree inst hwire]
  simp only [instOutNames, Inst.rename, List.map_map]; rfl

theorem flattenParentSeq_regNames (p : Parent) :
    (flattenParentSeq p).regs.map (·.name) = regNamesOf p.insts := by
  rw [flattenParentSeq_regs]
  simp only [regNamesOf, List.map_flatMap, Inst.flatRegs, List.map_map]; rfl

/-! ## The hierarchical cycle-environment fold -/

/-- One instance of `Parent.cycleEnvList`'s fold: append the child's outputs (from its *current*
    registers `inst.regVals F` and its instance-mapped inputs) renamed `"<inst>.<port>"`. -/
def cycleStep (F : Env) (acc : List (String × Nat)) (inst : Inst) : List (String × Nat) :=
  acc ++ (inst.child.outputs?eval (inst.regVals F) (inst.childIn (Env.ofList acc))).map
           (fun pv => (inst.instName ++ "." ++ pv.1, pv.2))

theorem cycleEnvList_eq (p : Parent) (F : Env) (inputs : List (String × Nat)) :
    Parent.cycleEnvList p F inputs = p.insts.foldl (cycleStep F) inputs := rfl

theorem cycleStep_eq (F : Env) (inst : Inst) (acc : List (String × Nat))
    (hwire : inst.child.wires = []) :
    cycleStep F acc inst
      = acc ++ inst.child.outputs.map (fun o =>
          (inst.instName ++ "." ++ o.name,
           (eval o.expr (cycleEnv (inst.regVals F) (inst.childIn (Env.ofList acc))
              (inst.child.regs.map (·.name)))).toNat)) := by
  simp only [cycleStep, outputs?eval_wirefree _ _ _ hwire, List.map_map]; rfl

theorem cycleStep_keys (F : Env) (inst : Inst) (acc : List (String × Nat))
    (hwire : inst.child.wires = []) :
    (cycleStep F acc inst).map (·.1) = acc.map (·.1) ++ instOutNames inst := by
  rw [cycleStep_eq F inst acc hwire]
  simp only [List.map_append, List.map_map, instOutNames]; rfl

/-! ## Well-formedness of a sequential hierarchy (left-to-right cascade) -/

/-- Sequential analogue of `HierCorrect.WFInsts`, processed left to right with a growing set of
    `known` names: each child is wire-free; each child output references only its bound input ports or
    its own registers; no register name is a bound input port; each instance expression references only
    already-`known` names (parent inputs and *earlier* instance outputs). -/
def WFInstsSeq : List Inst → List String → Prop
  | [], _ => True
  | inst :: rest, known =>
      inst.child.wires = []
    ∧ (∀ o ∈ inst.child.outputs, ∀ n ∈ o.expr.vars,
          n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name))
    ∧ (∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none)
    ∧ (∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ known)
    ∧ WFInstsSeq rest (known ++ instOutNames inst)

/-- Extract the per-instance (`known`-independent) facts from `WFInstsSeq`. -/
theorem WFInstsSeq_mem : ∀ (insts : List Inst) (known : List String), WFInstsSeq insts known →
    ∀ inst ∈ insts,
      inst.child.wires = []
    ∧ (∀ o ∈ inst.child.outputs, ∀ n ∈ o.expr.vars,
          n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name))
    ∧ (∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none)
  | [], _, _ => by intro inst h; simp at h
  | inst₀ :: rest, known, hwf => by
      obtain ⟨hwire, hout, hdisj, _, hrest⟩ := hwf
      intro inst hinst
      rcases List.mem_cons.mp hinst with rfl | hr
      · exact ⟨hwire, hout, hdisj⟩
      · exact WFInstsSeq_mem rest _ hrest inst hr

/-- Each instance expression references only names in `known ++ visNames insts`. -/
theorem WFInstsSeq_ins_mem : ∀ (insts : List Inst) (known : List String), WFInstsSeq insts known →
    ∀ inst ∈ insts, ∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ known ++ visNames insts
  | [], _, _ => by intro inst h; simp at h
  | inst₀ :: rest, known, hwf => by
      obtain ⟨_, _, _, hins, hrest⟩ := hwf
      intro inst hinst pe hpe n hn
      rcases List.mem_cons.mp hinst with rfl | hr
      · exact List.mem_append.mpr (Or.inl (hins pe hpe n hn))
      · have hthis := WFInstsSeq_ins_mem rest _ hrest inst hr pe hpe n hn
        rw [visNames_cons, ← List.append_assoc]
        exact hthis

/-! ## Per-instance flattened output value -/

/-- The flattened output net `substRename inst.ins inst.rename o.expr`, evaluated in a flat env `fe`
    that (a) carries the parent's register values on the renamed register nets and (b) agrees with the
    accumulated parent env on the instance-expression variables, computes exactly the value the
    hierarchical `outputs?eval` samples. -/
theorem flatWireSeq_val (inst : Inst) (F fe : Env) (acc : List (String × Nat)) (o : OutPort)
    (ho : o ∈ inst.child.outputs)
    (hout : ∀ o ∈ inst.child.outputs, ∀ n ∈ o.expr.vars,
              n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name))
    (hdisj : ∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none)
    (hins : ∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ acc.map (·.1))
    (hag : ∀ n ∈ acc.map (·.1), fe n = Env.ofList acc n)
    (hfe_reg : ∀ r ∈ inst.child.regs, fe (inst.rename r.name) = F (inst.rename r.name)) :
    eval (substRename inst.ins inst.rename o.expr) fe
      = eval o.expr (cycleEnv (inst.regVals F) (inst.childIn (Env.ofList acc))
          (inst.child.regs.map (·.name))) := by
  rw [eval_substRename inst.ins inst.rename fe o.expr]
  apply eval_congr
  intro n hn
  rcases hout o ho n hn with hport | hreg
  · obtain ⟨pp, hpp, hppn⟩ := List.mem_map.mp hport
    have hsome : (inst.ins.lookup n).isSome := by
      rw [List.lookup_isSome_iff]; exact ⟨pp, hpp, by simp [hppn]⟩
    obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp hsome
    have hnotreg : n ∉ inst.child.regs.map (·.name) := by
      intro hc
      obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hc
      rw [← hrn] at hae; rw [hdisj r hr] at hae; simp at hae
    have haemem : (n, ae) ∈ inst.ins := by
      obtain ⟨l₁, l₂, hl, _⟩ := List.lookup_eq_some_iff.mp hae; rw [hl]; simp
    simp only [childEnvSeq, cycleEnv, contains_false_of_not_mem hnotreg,
               Bool.false_eq_true, if_false, childIn_ofList, hae]
    congr 1
    apply eval_congr
    intro k hk
    exact hag k (hins (n, ae) haemem k hk)
  · obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hreg
    have hnone : inst.ins.lookup n = none := by rw [← hrn]; exact hdisj r hr
    simp only [childEnvSeq, hnone, cycleEnv, contains_true_of_mem hreg, if_true,
               Inst.regVals, Inst.rename]
    rw [← hrn]
    exact hfe_reg r hr

/-! ## The sequential fold lemma — flat `evalWires` reproduces `Parent.cycleEnvList` -/

/-- **Core sequential fold lemma.**  For wire-free, well-formed instances, and a flat env `fe` that
    agrees with the accumulator on the defined names and carries each child's register file (via `F`),
    the flattened wires reproduce, on every parent-input and instance-output net, exactly the values
    the hierarchical `Parent.cycleEnvList` fold computes.  Sequential analogue of
    `HierCorrect.flat_fold`. -/
theorem flatSeq_fold (F : Env) (insts : List Inst) :
    ∀ (acc : List (String × Nat)) (fe : Env),
      WFInstsSeq insts (acc.map (·.1)) →
      (acc.map (·.1) ++ visNames insts).Nodup →
      (∀ n ∈ acc.map (·.1), fe n = Env.ofList acc n) →
      (∀ inst ∈ insts, ∀ r ∈ inst.child.regs, fe (inst.rename r.name) = F (inst.rename r.name)) →
      (∀ inst ∈ insts, ∀ r ∈ inst.child.regs, inst.rename r.name ∉ visNames insts) →
      ∀ n ∈ acc.map (·.1) ++ visNames insts,
        evalWires (insts.flatMap Inst.flatWiresSeq) fe n
          = Env.ofList (insts.foldl (cycleStep F) acc) n := by
  induction insts with
  | nil =>
      intro acc fe _ _ hag _ _ n hn
      simp only [visNames, List.flatMap_nil, List.append_nil] at hn
      simpa [List.flatMap_nil, evalWires] using hag n hn
  | cons inst rest ih =>
      intro acc fe hwf hnd hag hfereg hregvis n hn
      obtain ⟨hwire, hout, hdisj, hins, hrest⟩ := hwf
      have hkeys := cycleStep_keys F inst acc hwire
      rw [visNames_cons] at hnd
      have hdisjN := (List.nodup_append.mp hnd).2.2
      have hndtail := (List.nodup_append.mp hnd).2.1
      have hndinstout := (List.nodup_append.mp hndtail).1
      have hnd' : ((acc.map (·.1) ++ instOutNames inst) ++ visNames rest).Nodup := by
        rw [List.append_assoc]; exact hnd
      have hflatnames : (Inst.flatWiresSeq inst).map (·.name) = instOutNames inst :=
        flatWiresSeq_names_wirefree inst hwire
      have hfereg_head : ∀ r ∈ inst.child.regs, fe (inst.rename r.name) = F (inst.rename r.name) :=
        fun r hr => hfereg inst (List.mem_cons_self) r hr
      have hB : ∀ m ∈ (cycleStep F acc inst).map (·.1),
            evalWires (Inst.flatWiresSeq inst) fe m = Env.ofList (cycleStep F acc inst) m := by
        intro m hm
        rw [hkeys] at hm
        rcases List.mem_append.mp hm with hmacc | hmout
        · have hmnotout : m ∉ (Inst.flatWiresSeq inst).map (·.name) := by
            rw [hflatnames]; intro hc
            exact hdisjN m hmacc m (List.mem_append.mpr (Or.inl hc)) rfl
          rw [evalWires_not_mem _ m hmnotout fe, hag m hmacc, cycleStep,
              ofList_append_left _ _ m hmacc]
        · obtain ⟨o, ho, hmo⟩ := List.mem_map.mp hmout
          subst hmo
          have hmnotacc : inst.instName ++ "." ++ o.name ∉ acc.map (·.1) := by
            intro hc
            exact hdisjN _ hc _ (List.mem_append.mpr (Or.inl hmout)) rfl
          have hindepf : ∀ w ∈ Inst.flatWiresSeq inst, ∀ k ∈ w.expr.vars,
              k ∉ (Inst.flatWiresSeq inst).map (·.name) := by
            intro w hw k hk
            rw [flatWiresSeq_wirefree inst hwire] at hw
            obtain ⟨o', ho', hwo'⟩ := List.mem_map.mp hw
            subst hwo'
            rw [hflatnames]
            rcases substRename_vars inst.ins inst.rename (acc.map (·.1))
                (inst.child.regs.map (·.name)) o'.expr (hout o' ho') hins k hk with hkknown | hkreg
            · intro hc; exact hdisjN k hkknown k (List.mem_append.mpr (Or.inl hc)) rfl
            · obtain ⟨rn, hrn, hrke⟩ := List.mem_map.mp hkreg
              obtain ⟨rr, hrr, hrrn⟩ := List.mem_map.mp hrn
              intro hc
              apply hregvis inst (List.mem_cons_self) rr hrr
              rw [visNames_cons]
              have hk_eq : inst.rename rr.name = k := by rw [hrrn]; exact hrke
              rw [hk_eq]
              exact List.mem_append.mpr (Or.inl hc)
          have hfe1 : evalWires (Inst.flatWiresSeq inst) fe (inst.instName ++ "." ++ o.name)
              = (eval (substRename inst.ins inst.rename o.expr) fe).toNat := by
            have hh := evalWires_indep (Inst.flatWiresSeq inst)
              (by rw [hflatnames]; exact hndinstout) hindepf fe
              { name := inst.rename o.name, width := o.width,
                expr := substRename inst.ins inst.rename o.expr }
              (by rw [flatWiresSeq_wirefree inst hwire]; exact List.mem_map.mpr ⟨o, ho, rfl⟩)
            simpa [Inst.rename] using hh
          rw [hfe1, flatWireSeq_val inst F fe acc o ho hout hdisj hins hag hfereg_head,
              cycleStep_eq F inst acc hwire, ofList_append_right _ _ _ hmnotacc]
          exact (ofList_lookup_mem inst.child.outputs (fun o => inst.instName ++ "." ++ o.name)
            (fun o => (eval o.expr (cycleEnv (inst.regVals F) (inst.childIn (Env.ofList acc))
              (inst.child.regs.map (·.name)))).toNat) o ho hndinstout).symm
      have hC : WFInstsSeq rest ((cycleStep F acc inst).map (·.1)) := by rw [hkeys]; exact hrest
      have hD : ((cycleStep F acc inst).map (·.1) ++ visNames rest).Nodup := by rw [hkeys]; exact hnd'
      have hfereg' : ∀ inst' ∈ rest, ∀ r ∈ inst'.child.regs,
          evalWires (Inst.flatWiresSeq inst) fe (inst'.rename r.name) = F (inst'.rename r.name) := by
        intro inst' hinst' r hr
        have hnotwire : inst'.rename r.name ∉ (Inst.flatWiresSeq inst).map (·.name) := by
          rw [hflatnames]; intro hc
          exact hregvis inst' (List.mem_cons_of_mem _ hinst') r hr
            (by rw [visNames_cons]; exact List.mem_append.mpr (Or.inl hc))
        rw [evalWires_not_mem _ _ hnotwire fe]
        exact hfereg inst' (List.mem_cons_of_mem _ hinst') r hr
      have hregvis' : ∀ inst' ∈ rest, ∀ r ∈ inst'.child.regs, inst'.rename r.name ∉ visNames rest := by
        intro inst' hinst' r hr hc
        exact hregvis inst' (List.mem_cons_of_mem _ hinst') r hr
          (by rw [visNames_cons]; exact List.mem_append.mpr (Or.inr hc))
      have hn' : n ∈ (cycleStep F acc inst).map (·.1) ++ visNames rest := by
        rw [hkeys, List.append_assoc, ← visNames_cons]; exact hn
      rw [List.flatMap_cons, evalWires_append, List.foldl_cons]
      exact ih (cycleStep F acc inst) (evalWires (Inst.flatWiresSeq inst) fe) hC hD hB hfereg' hregvis' n hn'

/-! ## Flat register / wire name inventories -/

theorem initFlat_keys (p : Parent) : (Parent.initFlat p).map (·.1) = regNamesOf p.insts := by
  simp only [Parent.initFlat, regNamesOf, List.map_flatMap, List.map_map, Inst.rename]; rfl

theorem nextFlat_keys (p : Parent) (F : Env) (inputs : List (String × Nat)) :
    (Parent.nextFlat p F inputs).map (·.1) = regNamesOf p.insts := by
  simp only [Parent.nextFlat, regNamesOf, List.map_flatMap, List.map_map, Inst.rename]; rfl

theorem flatWireNames_aux : ∀ (insts : List Inst), (∀ inst ∈ insts, inst.child.wires = []) →
    (insts.flatMap Inst.flatWiresSeq).map (·.name) = insts.flatMap instOutNames := by
  intro insts
  induction insts with
  | nil => intro _; rfl
  | cons a rest ih =>
      intro hall
      simp only [List.flatMap_cons, List.map_append]
      rw [flatWiresSeq_names_wirefree a (hall a (List.mem_cons_self)),
          ih (fun inst h => hall inst (List.mem_cons_of_mem _ h))]

theorem flattenParentSeq_wireNames (p : Parent)
    (hallwf : ∀ inst ∈ p.insts, inst.child.wires = []) :
    (flattenParentSeq p).wires.map (·.name) = visNames p.insts := by
  show (p.insts.flatMap Inst.flatWiresSeq).map (·.name) = p.insts.flatMap instOutNames
  exact flatWireNames_aux p.insts hallwf

/-! ## Well-formedness of a wire-free-children sequential parent -/

/-- Bundled well-formedness for the hierarchical bridges: every child is wire-free & reset-free, each
    child output/next references only bound ports or registers, register/output/input net names are
    distinct, and each instance expression references only already-defined names. -/
structure WFParentSeq (p : Parent) : Prop where
  wf         : WFInstsSeq p.insts (p.inputs.map (·.name))
  ndOut      : (p.inputs.map (·.name) ++ visNames p.insts).Nodup
  ndReg      : (regNamesOf p.insts).Nodup
  ndChildReg : ∀ inst ∈ p.insts, (inst.child.regs.map (·.name)).Nodup
  regWire    : ∀ q ∈ regNamesOf p.insts, q ∉ visNames p.insts
  regIn      : ∀ q ∈ regNamesOf p.insts, q ∉ p.inputs.map (·.name)
  nextBd     : ∀ inst ∈ p.insts, ∀ r ∈ inst.child.regs, ∀ n ∈ r.next.vars,
                 n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name)
  noRst      : ∀ inst ∈ p.insts, inst.child.reset = none
  outPO      : ∀ o ∈ p.outputs, ∀ n ∈ o.expr.vars, n ∈ p.inputs.map (·.name) ++ visNames p.insts

theorem WFParentSeq.allWireFree {p : Parent} (wf : WFParentSeq p) :
    ∀ inst ∈ p.insts, inst.child.wires = [] :=
  fun inst h => (WFInstsSeq_mem p.insts _ wf.wf inst h).1

/-! ## The env-agreement corollary: flat `evalWires` = hierarchical `cycleEnvList` -/

/-- The flat cycle environment agrees with the hierarchical `Parent.cycleEnvList` on every
    parent-input and instance-output net, provided the flat and hierarchical register states agree on
    the flat register names. -/
theorem flatSeq_agree (p : Parent) (wf : WFParentSeq p) (Fflat Fhier : Env)
    (inputs : List (String × Nat)) (hin : inputs.map (·.1) = p.inputs.map (·.name))
    (hagreeReg : ∀ q ∈ regNamesOf p.insts, Fflat q = Fhier q) :
    ∀ n ∈ inputs.map (·.1) ++ visNames p.insts,
      evalWires (flattenParentSeq p).wires
          (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name))) n
        = Env.ofList (Parent.cycleEnvList p Fhier inputs) n := by
  have hregeq := flattenParentSeq_regNames p
  have hag : ∀ n ∈ inputs.map (·.1),
      cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name)) n
        = Env.ofList inputs n := by
    intro n hn
    have hnin : n ∈ p.inputs.map (·.name) := by rw [← hin]; exact hn
    have hnotreg : n ∉ regNamesOf p.insts := fun hc => wf.regIn n hc hnin
    simp only [cycleEnv, hregeq, contains_false_of_not_mem hnotreg, Bool.false_eq_true, if_false]
  have hfereg : ∀ inst ∈ p.insts, ∀ r ∈ inst.child.regs,
      cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name)) (inst.rename r.name)
        = Fhier (inst.rename r.name) := by
    intro inst hinst r hr
    have hmem : inst.rename r.name ∈ regNamesOf p.insts :=
      List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
    simp only [cycleEnv, hregeq, contains_true_of_mem hmem, if_true]
    exact hagreeReg _ hmem
  have hregvis : ∀ inst ∈ p.insts, ∀ r ∈ inst.child.regs, inst.rename r.name ∉ visNames p.insts :=
    fun inst hinst r hr =>
      wf.regWire _ (List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, rfl⟩⟩)
  have hmain := flatSeq_fold Fhier p.insts inputs
    (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name)))
    (by rw [hin]; exact wf.wf) (by rw [hin]; exact wf.ndOut) hag hfereg hregvis
  intro n hn
  exact hmain n hn

/-! ## Bridge (1): init -/

/-- **init bridge.**  The flat module's initial register file agrees with the hierarchical
    `Parent.initFlat` on every flat register net. -/
theorem initRegs_eq_initFlat (p : Parent) (wf : WFParentSeq p)
    (q : String) (hq : q ∈ regNamesOf p.insts) :
    (flattenParentSeq p).initRegs q = Env.ofList (Parent.initFlat p) q := by
  obtain ⟨inst, hinst, hq2⟩ := List.mem_flatMap.mp hq
  obtain ⟨r, hr, hqe⟩ := List.mem_map.mp hq2
  have hqe' : inst.instName ++ "." ++ r.name = q := hqe
  have hnd : ((flattenParentSeq p).regs.map (·.name)).Nodup := by
    rw [flattenParentSeq_regNames]; exact wf.ndReg
  have hmem : (⟨inst.rename r.name, r.width, substRename inst.ins inst.rename r.next, r.init, r.emitInit,
      r.asyncReset.map (fun ar => (inst.rename ar.1, ar.2)), r.negedge, none, none⟩ : Reg)
        ∈ (flattenParentSeq p).regs := by
    rw [flattenParentSeq_regs]
    exact List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
  have hfind := find?_name_nodup (flattenParentSeq p).regs _ hmem hnd
  rw [hqe] at hfind
  have hR : Env.ofList (Parent.initFlat p) q = r.init.toNat := by
    apply ofList_mem_nodup
    · exact List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, by rw [hqe']⟩⟩
    · rw [initFlat_keys]; exact wf.ndReg
  rw [hR]
  simp only [Module.initRegs, hfind]

/-! ## Bridge (2): step -/

/-- **step bridge.**  One flat `Module.step` of a flat state `Fflat` agrees with the hierarchical
    `Parent.nextFlat` of a hierarchical state `Fhier` on every flat register net, provided the two
    states agree there (reset-free — matching `inst.child.reset = none`). -/
theorem flatStep_eq_nextFlat (p : Parent) (wf : WFParentSeq p)
    (Fflat Fhier : Env) (inputs : List (String × Nat))
    (hin : inputs.map (·.1) = p.inputs.map (·.name))
    (hagreeReg : ∀ q ∈ regNamesOf p.insts, Fflat q = Fhier q)
    (q : String) (hq : q ∈ regNamesOf p.insts) :
    (flattenParentSeq p).step Fflat (Env.ofList inputs) false q
      = Env.ofList (Parent.nextFlat p Fhier inputs) q := by
  obtain ⟨inst, hinst, hq2⟩ := List.mem_flatMap.mp hq
  obtain ⟨r, hr, hqe⟩ := List.mem_map.mp hq2
  have hqe' : inst.instName ++ "." ++ r.name = q := hqe
  obtain ⟨hwire, hout, hdisj⟩ := WFInstsSeq_mem p.insts _ wf.wf inst hinst
  have hndchild := wf.ndChildReg inst hinst
  have hnextbd := wf.nextBd inst hinst r hr
  have hallwf := wf.allWireFree
  let e : Env := evalWires (flattenParentSeq p).wires
      (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name)))
  have he : e = evalWires (flattenParentSeq p).wires
      (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name))) := rfl
  let pe : Env := Env.ofList (Parent.cycleEnvList p Fhier inputs)
  have hpe : pe = Env.ofList (Parent.cycleEnvList p Fhier inputs) := rfl
  have hnd : ((flattenParentSeq p).regs.map (·.name)).Nodup := by
    rw [flattenParentSeq_regNames]; exact wf.ndReg
  have hmemF : (⟨inst.rename r.name, r.width, substRename inst.ins inst.rename r.next, r.init, r.emitInit,
      r.asyncReset.map (fun ar => (inst.rename ar.1, ar.2)), r.negedge, none, none⟩ : Reg)
        ∈ (flattenParentSeq p).regs := by
    rw [flattenParentSeq_regs]
    exact List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
  have hfindF := find?_name_nodup (flattenParentSeq p).regs _ hmemF hnd
  rw [hqe] at hfindF
  have hFlat : (flattenParentSeq p).step Fflat (Env.ofList inputs) false q
      = (eval (substRename inst.ins inst.rename r.next) e).toNat := by
    rw [he]; simp only [Module.step, hfindF, Bool.false_eq_true, if_false]
  rw [inst_next_correct inst e r hr hnextbd hdisj] at hFlat
  have hHier : Env.ofList (Parent.nextFlat p Fhier inputs) q
      = inst.child.step (inst.regVals Fhier) (inst.childIn pe) false r.name := by
    have hmemN : (q, inst.child.step (inst.regVals Fhier) (inst.childIn pe)
        (inst.resetActive pe) r.name) ∈ Parent.nextFlat p Fhier inputs :=
      List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, by rw [hqe']⟩⟩
    have hndN : ((Parent.nextFlat p Fhier inputs).map (·.1)).Nodup := by
      rw [nextFlat_keys]; exact wf.ndReg
    rw [ofList_mem_nodup _ q _ hmemN hndN,
        show inst.resetActive pe = false from by
          simp only [Inst.resetActive, wf.noRst inst hinst]]
  rw [hFlat, hHier, step_wirefree_reg inst.child (inst.regVals Fhier) (inst.childIn pe) hwire r
      (find?_name_nodup inst.child.regs r hr hndchild)]
  simp only [Inst.childCycleEnv]
  congr 1
  apply eval_congr
  intro n hn
  rcases hnextbd n hn with hport | hreg
  · obtain ⟨pp, hpp, hppn⟩ := List.mem_map.mp hport
    have hsome : (inst.ins.lookup n).isSome := by
      rw [List.lookup_isSome_iff]; exact ⟨pp, hpp, by simp [hppn]⟩
    obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp hsome
    have hnotreg : n ∉ inst.child.regs.map (·.name) := by
      intro hc; obtain ⟨rr, hrr, hrrn⟩ := List.mem_map.mp hc
      rw [← hrrn] at hae; rw [hdisj rr hrr] at hae; simp at hae
    have haemem : (n, ae) ∈ inst.ins := by
      obtain ⟨l₁, l₂, hl, _⟩ := List.lookup_eq_some_iff.mp hae; rw [hl]; simp
    simp only [cycleEnv, contains_false_of_not_mem hnotreg, Bool.false_eq_true, if_false,
               childIn_ofList, hae]
    congr 1
    apply eval_congr
    intro k hk
    have hkknown : k ∈ p.inputs.map (·.name) ++ visNames p.insts :=
      WFInstsSeq_ins_mem p.insts _ wf.wf inst hinst (n, ae) haemem k hk
    have hkin : k ∈ inputs.map (·.1) ++ visNames p.insts := by rw [hin]; exact hkknown
    exact flatSeq_agree p wf Fflat Fhier inputs hin hagreeReg k hkin
  · obtain ⟨rr, hrr, hrrn⟩ := List.mem_map.mp hreg
    have hmem2 : inst.rename n ∈ regNamesOf p.insts :=
      List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨rr, hrr, by rw [hrrn]⟩⟩
    have hnotwire : inst.instName ++ "." ++ n ∉ (flattenParentSeq p).wires.map (·.name) := by
      rw [flattenParentSeq_wireNames p hallwf]; exact wf.regWire (inst.rename n) hmem2
    have hmemF2 : inst.instName ++ "." ++ n ∈ (flattenParentSeq p).regs.map (·.name) := by
      rw [flattenParentSeq_regNames]; exact hmem2
    simp only [cycleEnv, contains_true_of_mem hreg, if_true, Inst.regVals]
    rw [he, evalWires_not_mem _ (inst.instName ++ "." ++ n) hnotwire]
    simp only [cycleEnv, contains_true_of_mem hmemF2, if_true]
    exact hagreeReg (inst.instName ++ "." ++ n) hmem2

/-! ## Bridge (3): output -/

/-- **output bridge.**  The flat module's per-cycle output map equals the hierarchical
    `Parent.outCycle` output map, given agreeing register states. -/
theorem flatOutputs_eq_outCycle (p : Parent) (wf : WFParentSeq p)
    (Fflat Fhier : Env) (inputs : List (String × Nat))
    (hin : inputs.map (·.1) = p.inputs.map (·.name))
    (hagreeReg : ∀ q ∈ regNamesOf p.insts, Fflat q = Fhier q) :
    (flattenParentSeq p).outputs?eval Fflat (Env.ofList inputs) = Parent.outCycle p Fhier inputs := by
  have hagree := flatSeq_agree p wf Fflat Fhier inputs hin hagreeReg
  show p.outputs.map (fun o => (o.name,
        (eval o.expr (evalWires (flattenParentSeq p).wires
           (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name))))).toNat))
     = p.outputs.map (fun o => (o.name,
        (eval o.expr (Env.ofList (Parent.cycleEnvList p Fhier inputs))).toNat))
  apply List.map_congr_left
  intro o ho
  have heq : eval o.expr (evalWires (flattenParentSeq p).wires
        (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name))))
      = eval o.expr (Env.ofList (Parent.cycleEnvList p Fhier inputs)) := by
    apply eval_congr
    intro n hn
    exact hagree n (by rw [hin]; exact wf.outPO o ho n hn)
  rw [heq]

/-! ## Bridge (4): the whole-trace corollary over `simulateSeq` -/

/-- The hierarchical register trace: cycle 0 is `Parent.initFlat`, cycle `t+1` is one
    `Parent.nextFlat`.  This is the register state `Parent.simulateSeq` threads across cycles. -/
def Parent.hierRegTrace (p : Parent) (inputs : Nat → List (String × Nat)) : Nat → Env
  | 0 => Env.ofList (Parent.initFlat p)
  | t + 1 => Env.ofList (Parent.nextFlat p (Parent.hierRegTrace p inputs t) (inputs t))

/-- **Whole-trace corollary.**  For a wire-free-children parent, the flat-`Module` whole register
    trace `Parent.regTrace` (reset-free) agrees, on every flat register net and at every cycle, with
    the HIERARCHICAL register state `Parent.hierRegTrace` that `Parent.nextFlat` / `Parent.simulateSeq`
    computes.  Induction on `t` reusing the init (1) and step (2) bridges. -/
theorem Parent.regTrace_eq_hierRegTrace (p : Parent) (wf : WFParentSeq p)
    (inputs : Nat → List (String × Nat))
    (hin : ∀ t, (inputs t).map (·.1) = p.inputs.map (·.name)) :
    ∀ (t : Nat) (q : String), q ∈ regNamesOf p.insts →
      p.regTrace (fun t => Env.ofList (inputs t)) (fun _ => false) t q
        = Parent.hierRegTrace p inputs t q := by
  intro t
  induction t with
  | zero =>
      intro q hq
      simp only [Parent.regTrace_zero, Parent.hierRegTrace]
      exact initRegs_eq_initFlat p wf q hq
  | succ n ih =>
      intro q hq
      simp only [Parent.regTrace_succ, Parent.hierRegTrace]
      exact flatStep_eq_nextFlat p wf
        (p.regTrace (fun t => Env.ofList (inputs t)) (fun _ => false) n)
        (Parent.hierRegTrace p inputs n) (inputs n) (hin n) ih q hq


/-!
# Extension (M34b): the hierarchical `simulateSeq` bridge for WIRE-CARRYING children

The bridge above requires every child to be wire-free (`WFParentSeq`).  This section discharges the
documented M34b extension: children may carry internal combinational **wires**.  The reference
semantics evaluate a child's outputs and register next-states over `evalWires child.wires (cycleEnv …)`
— the cycle env *extended by the child's wire cones* — and the flattened module carries each child's
renamed wire cones (`Inst.flatWiresSeq`).  The heart is a naturality square
(`childEnvSeq_evalWires_comm`): the flat-derived child env of the renamed wire fold IS the child wire
fold of the flat-derived child env (no topological/Nodup hypothesis — arbitrary intra-child wire
chains supported); combined with a topological raw congruence (`evalWires_congr_chain`) this shows the
flat `evalWires` reproduces every child's local `evalWires` at its renamed nets.

## Honest scope

The four step-level bridges and the trace corollary hold **conditionally** on `WFParentSeq'` (the
wire-carrying analogue of `WFParentSeq`): each child's internal wires are **topologically ordered**
(`WFWireChain` — the discipline `evalWires`'s semantics already assume) over its ports+registers;
each output / register-next references only bound ports, registers, or internal wires; every renamed
wire net is a fresh parent-visible net (distinct from inputs, registers, and every other flat net);
children are reset-free (`inst.child.reset = none`).  Inter-instance carry chains (a child input
driven by an earlier child's output) ARE supported, exactly as in the wire-free `WFParentSeq`.  This
is the general hierarchical bridge for topologically-wired sequential children.
-/

/-! ## Renamed-wire builders and rename injectivity -/

/-- Rename a child wire into the flat parent net (matching `Inst.flatWiresSeq`'s wire branch). -/
def Inst.renWire (inst : Inst) (w : Wire) : Wire :=
  { name := inst.rename w.name, width := w.width, expr := substRename inst.ins inst.rename w.expr }

/-- Rename a child output into the flat parent net (matching `Inst.flatWiresSeq`'s output branch). -/
def Inst.renOut (inst : Inst) (o : OutPort) : Wire :=
  { name := inst.rename o.name, width := o.width, expr := substRename inst.ins inst.rename o.expr }

theorem flatWiresSeq_eq (inst : Inst) :
    Inst.flatWiresSeq inst = inst.child.wires.map inst.renWire ++ inst.child.outputs.map inst.renOut :=
  rfl

theorem rename_inj (inst : Inst) {n m : String} (h : inst.rename n = inst.rename m) : n = m := by
  simp only [Inst.rename] at h
  exact (String.append_right_inj _).mp h

/-! ## Naturality: `childEnvSeq` commutes with the renamed wire fold

The heart of the wire-carrying extension.  For ANY flat env `fe`, the flat-derived child env of the
renamed wire fold is the child wire fold of the flat-derived child env — a clean naturality square
requiring NO topological/Nodup hypothesis (it holds for arbitrary wire chains). -/

theorem childEnvSeq_evalWires_comm (inst : Inst) :
    ∀ (ws : List Wire) (fe : Env),
      (∀ w ∈ ws, inst.ins.lookup w.name = none) →
      (∀ w ∈ ws, ∀ pe ∈ inst.ins, inst.rename w.name ∉ pe.2.2.vars) →
      childEnvSeq inst.ins inst.rename (evalWires (ws.map inst.renWire) fe)
        = evalWires ws (childEnvSeq inst.ins inst.rename fe) := by
  intro ws
  induction ws with
  | nil => intro fe _ _; rfl
  | cons w rest ih =>
      intro fe hport hdisj
      have hpw : inst.ins.lookup w.name = none := hport w (List.mem_cons_self ..)
      rw [List.map_cons, evalWires_cons, evalWires_cons,
          ih _ (fun w' hw' => hport w' (List.mem_cons_of_mem _ hw'))
                (fun w' hw' => hdisj w' (List.mem_cons_of_mem _ hw'))]
      congr 1
      funext n
      by_cases hnw : n = w.name
      · subst hnw
        simp only [childEnvSeq, hpw, Inst.renWire]
        rw [eval_substRename]
      · cases hln : inst.ins.lookup n with
        | some ae =>
            have haemem : (n, ae) ∈ inst.ins := by
              obtain ⟨l₁, l₂, hl, _⟩ := List.lookup_eq_some_iff.mp hln; rw [hl]; simp
            have hdj := hdisj w (List.mem_cons_self ..) (n, ae) haemem
            simp only [childEnvSeq, hln, if_neg hnw]
            congr 1
            apply eval_congr
            intro m hm
            have hmne : m ≠ (inst.renWire w).name := by
              simp only [Inst.renWire]; intro hc; exact hdj (hc ▸ hm)
            simp only [if_neg hmne]
        | none =>
            have hne : inst.rename n ≠ (inst.renWire w).name := by
              simp only [Inst.renWire]; intro hc; exact hnw (rename_inj inst hc)
            simp only [childEnvSeq, hln, if_neg hnw, if_neg hne]

/-! ## Topological wire chain and its evalWires congruence -/

/-- Each wire's cone references only names already in `ext` (processed left to right, `ext` grows by
    each wire's own name).  This is exactly the "topologically ordered wires" discipline the semantics
    of `evalWires` already assume, made an explicit predicate. -/
def WFWireChain (ext : List String) : List Wire → Prop
  | [] => True
  | w :: rest => (∀ n ∈ w.expr.vars, n ∈ ext) ∧ WFWireChain (ext ++ [w.name]) rest

/-- **Raw evalWires congruence for a topological chain.**  Two base envs agreeing on the external
    names `ext` (all names the chain reads before binding) produce equal wire folds on `ext` and on
    every wire name.  No Nodup needed — the fold binds each wire to a value depending only on `ext`
    and earlier wires, which agree by induction. -/
theorem evalWires_congr_chain :
    ∀ (ws : List Wire) (ext : List String) (B₁ B₂ : Env),
      WFWireChain ext ws →
      (∀ n ∈ ext, B₁ n = B₂ n) →
      ∀ n ∈ ext ++ ws.map (·.name), evalWires ws B₁ n = evalWires ws B₂ n := by
  intro ws
  induction ws with
  | nil =>
      intro ext B₁ B₂ _ hbase n hn
      simp only [List.map_nil, List.append_nil] at hn
      simpa only [evalWires, List.foldl_nil] using hbase n hn
  | cons w rest ih =>
      intro ext B₁ B₂ hwf hbase n hn
      obtain ⟨hcone, hrest⟩ := hwf
      have hval : eval w.expr B₁ = eval w.expr B₂ :=
        eval_congr w.expr B₁ B₂ (fun m hm => hbase m (hcone m hm))
      rw [evalWires_cons, evalWires_cons]
      have hbase' : ∀ m ∈ ext ++ [w.name],
          (fun k => if k = w.name then (eval w.expr B₁).toNat else B₁ k) m
            = (fun k => if k = w.name then (eval w.expr B₂).toNat else B₂ k) m := by
        intro m hm
        by_cases hmw : m = w.name
        · simp only [hmw, if_true, hval]
        · simp only [if_neg hmw]
          rcases List.mem_append.mp hm with hme | hmw'
          · exact hbase m hme
          · simp only [List.mem_singleton] at hmw'; exact absurd hmw' hmw
      have hn' : n ∈ (ext ++ [w.name]) ++ rest.map (·.name) := by
        rw [List.append_assoc, List.singleton_append]
        simpa only [List.map_cons] using hn
      exact ih (ext ++ [w.name]) _ _ hrest hbase' n hn'

/-! ## The child's wire-extended cycle environment (register carrier `F`, accumulated env `acc`) -/

/-- The child's per-cycle base env: registers projected from the flat carrier `F` overlaid by the
    instance-mapped inputs (evaluated in the accumulated parent env `Env.ofList acc`). -/
def childBaseSeq (F : Env) (acc : List (String × Nat)) (inst : Inst) : Env :=
  cycleEnv (inst.regVals F) (inst.childIn (Env.ofList acc)) (inst.child.regs.map (·.name))

/-- The child's per-cycle env EXTENDED by its internal wires — the env `Module.outputs?eval` /
    `Module.step` evaluate expressions against. -/
def childExtSeq (F : Env) (acc : List (String × Nat)) (inst : Inst) : Env :=
  evalWires inst.child.wires (childBaseSeq F acc inst)

/-- The renamed child-internal names (registers ++ wires), the target set of `substRename_vars`. -/
def childIntNames (inst : Inst) : List String :=
  inst.child.regs.map (·.name) ++ inst.child.wires.map (·.name)

/-- **P3 — flat-derived child env agrees with the child base on ports and registers.**  Sequential
    analogue of `childEnvSeq_agrees`, but read against the two-env child base `childBaseSeq` (registers
    from `F`, inputs from `acc`). -/
theorem childEnvSeq_agrees_base (inst : Inst) (F : Env) (acc : List (String × Nat)) (fe : Env)
    (hregport : ∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none)
    (hins : ∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ acc.map (·.1))
    (hag : ∀ n ∈ acc.map (·.1), fe n = Env.ofList acc n)
    (hfereg : ∀ r ∈ inst.child.regs, fe (inst.rename r.name) = F (inst.rename r.name)) :
    ∀ n ∈ inst.ins.map (·.1) ++ inst.child.regs.map (·.name),
      childEnvSeq inst.ins inst.rename fe n = childBaseSeq F acc inst n := by
  intro n hn
  rcases List.mem_append.mp hn with hport | hreg
  · obtain ⟨pp, hpp, hppn⟩ := List.mem_map.mp hport
    have hsome : (inst.ins.lookup n).isSome := by
      rw [List.lookup_isSome_iff]; exact ⟨pp, hpp, by simp [hppn]⟩
    obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp hsome
    have hnotreg : n ∉ inst.child.regs.map (·.name) := by
      intro hc; obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hc
      rw [← hrn] at hae; rw [hregport r hr] at hae; simp at hae
    have haemem : (n, ae) ∈ inst.ins := by
      obtain ⟨l₁, l₂, hl, _⟩ := List.lookup_eq_some_iff.mp hae; rw [hl]; simp
    simp only [childEnvSeq, hae, childBaseSeq, cycleEnv, contains_false_of_not_mem hnotreg,
               Bool.false_eq_true, if_false, childIn_ofList]
    congr 1
    apply eval_congr
    intro k hk
    exact hag k (hins (n, ae) haemem k hk)
  · obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hreg
    have hnone : inst.ins.lookup n = none := by rw [← hrn]; exact hregport r hr
    simp only [childEnvSeq, hnone, childBaseSeq, cycleEnv, contains_true_of_mem hreg, if_true,
               Inst.regVals, Inst.rename]
    rw [← hrn]
    exact hfereg r hr

/-- **Cone transport through the two wire folds.**  For an expression referencing only ports,
    registers, or (topologically ordered) wires, evaluating it over the child wire fold of the flat
    env equals evaluating it over the child's own wire-extended cycle env. -/
theorem childExt_congr (inst : Inst) (F : Env) (acc : List (String × Nat)) (fe : Env)
    {w : Nat} (e : Expr w)
    (hchain : WFWireChain (inst.ins.map (·.1) ++ inst.child.regs.map (·.name)) inst.child.wires)
    (hevars : ∀ n ∈ e.vars, n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name)
                ∨ n ∈ inst.child.wires.map (·.name))
    (hregport : ∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none)
    (hins : ∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ acc.map (·.1))
    (hag : ∀ n ∈ acc.map (·.1), fe n = Env.ofList acc n)
    (hfereg : ∀ r ∈ inst.child.regs, fe (inst.rename r.name) = F (inst.rename r.name)) :
    eval e (evalWires inst.child.wires (childEnvSeq inst.ins inst.rename fe))
      = eval e (childExtSeq F acc inst) := by
  have hagbase := childEnvSeq_agrees_base inst F acc fe hregport hins hag hfereg
  have hfold := evalWires_congr_chain inst.child.wires
      (inst.ins.map (·.1) ++ inst.child.regs.map (·.name))
      (childEnvSeq inst.ins inst.rename fe) (childBaseSeq F acc inst) hchain hagbase
  apply eval_congr
  intro n hn
  refine hfold n ?_
  rcases hevars n hn with h1 | h2 | h3
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl h1)))
  · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr h2)))
  · exact List.mem_append.mpr (Or.inr h3)

/-- The renamed-output wire nets are exactly `instOutNames inst`. -/
theorem renOut_names (inst : Inst) :
    (inst.child.outputs.map inst.renOut).map (·.name) = instOutNames inst := by
  simp only [instOutNames, List.map_map]
  apply List.map_congr_left
  intro o _
  rfl

theorem rename_injective (inst : Inst) : Function.Injective inst.rename :=
  fun _ _ h => rename_inj inst h

/-- `Nodup` is preserved by an injective map (local; the toolchain has no Mathlib). -/
theorem nodup_map_inj {α β : Type} {l : List α} {f : α → β}
    (hf : Function.Injective f) (h : l.Nodup) : (l.map f).Nodup := by
  induction l with
  | nil => simp
  | cons a rest ih =>
      simp only [List.map_cons, List.nodup_cons] at h ⊢
      obtain ⟨ha, hr⟩ := h
      refine ⟨?_, ih hr⟩
      intro hc
      obtain ⟨b, hb, hbe⟩ := List.mem_map.mp hc
      exact ha (hf hbe ▸ hb)

/-! ## Per-instance flat-net value reproductions -/

/-- **A flattened internal-wire net reproduces the child's wire value.**  The flat fold of one
    instance's `flatWiresSeq`, at a renamed internal-wire net, equals the value the child's own
    `evalWires child.wires` binds there. -/
theorem flatWireNet_val (inst : Inst) (F : Env) (acc : List (String × Nat)) (fe : Env)
    (w : Wire) (hw : w ∈ inst.child.wires)
    (hchain : WFWireChain (inst.ins.map (·.1) ++ inst.child.regs.map (·.name)) inst.child.wires)
    (hregport : ∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none)
    (hwireport : ∀ w' ∈ inst.child.wires, inst.ins.lookup w'.name = none)
    (hportdisj : ∀ w' ∈ inst.child.wires, ∀ pe ∈ inst.ins, inst.rename w'.name ∉ pe.2.2.vars)
    (howdisj : ∀ o ∈ inst.child.outputs, o.name ∉ inst.child.wires.map (·.name))
    (hins : ∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ acc.map (·.1))
    (hag : ∀ n ∈ acc.map (·.1), fe n = Env.ofList acc n)
    (hfereg : ∀ r ∈ inst.child.regs, fe (inst.rename r.name) = F (inst.rename r.name)) :
    evalWires (Inst.flatWiresSeq inst) fe (inst.rename w.name) = childExtSeq F acc inst w.name := by
  rw [flatWiresSeq_eq, evalWires_append]
  have hnotout : inst.rename w.name ∉ (inst.child.outputs.map inst.renOut).map (·.name) := by
    rw [renOut_names]
    simp only [instOutNames, List.mem_map, not_exists]
    rintro o ⟨ho, hoe⟩
    have hoe' : inst.rename o.name = inst.rename w.name := hoe
    exact howdisj o ho ((rename_inj inst hoe') ▸ List.mem_map.mpr ⟨w, hw, rfl⟩)
  rw [evalWires_not_mem _ _ hnotout]
  have hpw : inst.ins.lookup w.name = none := hwireport w hw
  have hcomm := childEnvSeq_evalWires_comm inst inst.child.wires fe hwireport hportdisj
  have hkey : (evalWires (inst.child.wires.map inst.renWire) fe) (inst.rename w.name)
      = childEnvSeq inst.ins inst.rename (evalWires (inst.child.wires.map inst.renWire) fe) w.name := by
    simp only [childEnvSeq, hpw]
  rw [hkey, hcomm]
  have hagbase := childEnvSeq_agrees_base inst F acc fe hregport hins hag hfereg
  have hfold := evalWires_congr_chain inst.child.wires
      (inst.ins.map (·.1) ++ inst.child.regs.map (·.name))
      (childEnvSeq inst.ins inst.rename fe) (childBaseSeq F acc inst) hchain hagbase
  exact hfold w.name (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨w, hw, rfl⟩)))

/-- **A flattened output net reproduces the child's `outputs?eval` value.**  The flat fold of one
    instance's `flatWiresSeq`, at a renamed output net, equals `eval o.expr` over the child's
    wire-extended cycle env — i.e. the value the hierarchical `Module.outputs?eval` samples. -/
theorem flatOutNet_val (inst : Inst) (F : Env) (acc : List (String × Nat)) (fe : Env)
    (o : OutPort) (ho : o ∈ inst.child.outputs)
    (hchain : WFWireChain (inst.ins.map (·.1) ++ inst.child.regs.map (·.name)) inst.child.wires)
    (houtvars : ∀ o' ∈ inst.child.outputs, ∀ n ∈ o'.expr.vars,
        n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name) ∨ n ∈ inst.child.wires.map (·.name))
    (hregport : ∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none)
    (hwireport : ∀ w' ∈ inst.child.wires, inst.ins.lookup w'.name = none)
    (hportdisj : ∀ w' ∈ inst.child.wires, ∀ pe ∈ inst.ins, inst.rename w'.name ∉ pe.2.2.vars)
    (hond : (inst.child.outputs.map (·.name)).Nodup)
    (howdisj : ∀ o' ∈ inst.child.outputs, o'.name ∉ inst.child.wires.map (·.name))
    (hregout : ∀ r ∈ inst.child.regs, r.name ∉ inst.child.outputs.map (·.name))
    (haccout : ∀ n ∈ acc.map (·.1), n ∉ instOutNames inst)
    (hins : ∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ acc.map (·.1))
    (hag : ∀ n ∈ acc.map (·.1), fe n = Env.ofList acc n)
    (hfereg : ∀ r ∈ inst.child.regs, fe (inst.rename r.name) = F (inst.rename r.name)) :
    evalWires (Inst.flatWiresSeq inst) fe (inst.rename o.name)
      = (eval o.expr (childExtSeq F acc inst)).toNat := by
  rw [flatWiresSeq_eq, evalWires_append]
  have hndR : ((inst.child.outputs.map inst.renOut).map (·.name)).Nodup := by
    rw [renOut_names]
    have hio : instOutNames inst = (inst.child.outputs.map (·.name)).map inst.rename := by
      simp only [instOutNames, List.map_map]
      apply List.map_congr_left; intro o _; rfl
    rw [hio]; exact nodup_map_inj (rename_injective inst) hond
  have hindep : ∀ w' ∈ inst.child.outputs.map inst.renOut, ∀ m ∈ w'.expr.vars,
      m ∉ (inst.child.outputs.map inst.renOut).map (·.name) := by
    intro w' hw' m hm
    obtain ⟨o', ho', hw'e⟩ := List.mem_map.mp hw'
    subst hw'e
    simp only [Inst.renOut] at hm
    have hb : ∀ n ∈ o'.expr.vars, n ∈ inst.ins.map (·.1) ∨ n ∈ childIntNames inst := by
      intro n hn
      rcases houtvars o' ho' n hn with h1 | h2 | h3
      · exact Or.inl h1
      · exact Or.inr (List.mem_append.mpr (Or.inl h2))
      · exact Or.inr (List.mem_append.mpr (Or.inr h3))
    rw [renOut_names]
    rcases substRename_vars inst.ins inst.rename (acc.map (·.1)) (childIntNames inst) o'.expr hb hins m hm
      with hknown | hren
    · exact haccout m hknown
    · obtain ⟨x, hx, hxe⟩ := List.mem_map.mp hren
      simp only [instOutNames, List.mem_map, not_exists]
      rintro o'' ⟨ho'', ho''e⟩
      have hxo : x = o''.name := rename_inj inst (hxe.trans ho''e.symm)
      rcases List.mem_append.mp hx with hxr | hxw
      · obtain ⟨r, hr, hrn⟩ := List.mem_map.mp hxr
        apply hregout r hr
        rw [hrn, hxo]
        exact List.mem_map.mpr ⟨o'', ho'', rfl⟩
      · obtain ⟨wv, hwv, hwn⟩ := List.mem_map.mp hxw
        apply howdisj o'' ho''
        rw [← hxo, ← hwn]
        exact List.mem_map.mpr ⟨wv, hwv, rfl⟩
  have hind := evalWires_indep (inst.child.outputs.map inst.renOut) hndR hindep
      (evalWires (inst.child.wires.map inst.renWire) fe) (inst.renOut o) (List.mem_map.mpr ⟨o, ho, rfl⟩)
  simp only [Inst.renOut] at hind
  rw [hind, eval_substRename, childEnvSeq_evalWires_comm inst inst.child.wires fe hwireport hportdisj,
      childExt_congr inst F acc fe o.expr hchain (houtvars o ho) hregport hins hag hfereg]

/-! ## The extended hierarchical cycle fold (carrying internal wires)

`Parent.cycleEnvList` folds only child OUTPUT nets.  `cycleStepExt` folds internal WIRE nets too — the
renamed nets the flat module's wire list additionally carries — so a single fold statement (`flatSeq_fold'`)
can pin the whole flat `evalWires` against it.  A later corollary shows the wire entries are fresh keys,
so on parent-inputs and output nets it agrees with `Parent.cycleEnvList`. -/

/-- The renamed internal-wire nets of one instance. -/
def instWireNames (inst : Inst) : List String := inst.child.wires.map (fun w => inst.rename w.name)

/-- All parent-visible flat nets of one instance: internal wires then outputs (matching
    `Inst.flatWiresSeq`). -/
def instAllNames (inst : Inst) : List String := instWireNames inst ++ instOutNames inst

/-- All flat wire/output nets across the whole parent. -/
def allFlatNames (insts : List Inst) : List String := insts.flatMap instAllNames

theorem allFlatNames_cons (inst : Inst) (rest : List Inst) :
    allFlatNames (inst :: rest) = instAllNames inst ++ allFlatNames rest := by
  simp [allFlatNames, List.flatMap_cons]

/-- One instance of the extended cycle fold: append the child's internal-wire values (renamed) then
    its output values (renamed), all computed against the child's wire-extended cycle env. -/
def cycleStepExt (F : Env) (acc : List (String × Nat)) (inst : Inst) : List (String × Nat) :=
  acc
  ++ inst.child.wires.map (fun w => (inst.rename w.name, childExtSeq F acc inst w.name))
  ++ inst.child.outputs.map (fun o => (inst.rename o.name, (eval o.expr (childExtSeq F acc inst)).toNat))

theorem flatWiresSeq_names (inst : Inst) :
    (Inst.flatWiresSeq inst).map (·.name) = instAllNames inst := by
  rw [flatWiresSeq_eq]
  simp only [List.map_append, renOut_names, instAllNames, instWireNames]
  congr 1
  simp only [List.map_map]
  apply List.map_congr_left
  intro w _; rfl

theorem cycleStepExt_keys (F : Env) (acc : List (String × Nat)) (inst : Inst) :
    (cycleStepExt F acc inst).map (·.1) = acc.map (·.1) ++ instAllNames inst := by
  have hw : (inst.child.wires.map
        (fun w => (inst.rename w.name, childExtSeq F acc inst w.name))).map (·.1)
      = instWireNames inst := by
    simp only [instWireNames, List.map_map]; apply List.map_congr_left; intro w _; rfl
  have ho : (inst.child.outputs.map
        (fun o => (inst.rename o.name, (eval o.expr (childExtSeq F acc inst)).toNat))).map (·.1)
      = instOutNames inst := by
    simp only [instOutNames, List.map_map]; apply List.map_congr_left; intro o _; rfl
  simp only [cycleStepExt, List.map_append, hw, ho, instAllNames, List.append_assoc]

/-! ## Well-formed sequential hierarchy with wire-carrying children -/

/-- Sequential analogue of `WFInstsSeq`, allowing wire-carrying children: each child's internal wires
    are topologically ordered over its ports+registers; each output/register-next references only bound
    ports, registers, or internal wires; register and wire names are not bound ports; renamed wire nets
    are not referenced by any instance expression; the child's output/wire/register names are mutually
    distinct; and each instance expression references only already-`known` names. -/
def WFInstsSeq' : List Inst → List String → Prop
  | [], _ => True
  | inst :: rest, known =>
      WFWireChain (inst.ins.map (·.1) ++ inst.child.regs.map (·.name)) inst.child.wires
    ∧ (∀ o ∈ inst.child.outputs, ∀ n ∈ o.expr.vars,
          n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name) ∨ n ∈ inst.child.wires.map (·.name))
    ∧ (∀ r ∈ inst.child.regs, ∀ n ∈ r.next.vars,
          n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name) ∨ n ∈ inst.child.wires.map (·.name))
    ∧ (∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none)
    ∧ (∀ w ∈ inst.child.wires, inst.ins.lookup w.name = none)
    ∧ (∀ w ∈ inst.child.wires, ∀ pe ∈ inst.ins, inst.rename w.name ∉ pe.2.2.vars)
    ∧ (inst.child.outputs.map (·.name)).Nodup
    ∧ (∀ o ∈ inst.child.outputs, o.name ∉ inst.child.wires.map (·.name))
    ∧ (∀ r ∈ inst.child.regs, r.name ∉ inst.child.outputs.map (·.name))
    ∧ (∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ known)
    ∧ WFInstsSeq' rest (known ++ instOutNames inst)

/-- Extract the per-instance (`known`-independent) facts from `WFInstsSeq'`. -/
theorem WFInstsSeq'_mem : ∀ (insts : List Inst) (known : List String), WFInstsSeq' insts known →
    ∀ inst ∈ insts,
      WFWireChain (inst.ins.map (·.1) ++ inst.child.regs.map (·.name)) inst.child.wires
    ∧ (∀ o ∈ inst.child.outputs, ∀ n ∈ o.expr.vars,
          n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name) ∨ n ∈ inst.child.wires.map (·.name))
    ∧ (∀ r ∈ inst.child.regs, ∀ n ∈ r.next.vars,
          n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name) ∨ n ∈ inst.child.wires.map (·.name))
    ∧ (∀ r ∈ inst.child.regs, inst.ins.lookup r.name = none)
    ∧ (∀ w ∈ inst.child.wires, inst.ins.lookup w.name = none)
    ∧ (∀ w ∈ inst.child.wires, ∀ pe ∈ inst.ins, inst.rename w.name ∉ pe.2.2.vars)
    ∧ (inst.child.outputs.map (·.name)).Nodup
    ∧ (∀ o ∈ inst.child.outputs, o.name ∉ inst.child.wires.map (·.name))
    ∧ (∀ r ∈ inst.child.regs, r.name ∉ inst.child.outputs.map (·.name))
  | [], _, _ => by intro inst h; simp at h
  | inst₀ :: rest, known, hwf => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, _, hrest⟩ := hwf
      intro inst hinst
      rcases List.mem_cons.mp hinst with rfl | hr
      · exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩
      · exact WFInstsSeq'_mem rest _ hrest inst hr

/-- Each instance expression references only names in `known ++ visNames insts`. -/
theorem WFInstsSeq'_ins_mem : ∀ (insts : List Inst) (known : List String), WFInstsSeq' insts known →
    ∀ inst ∈ insts, ∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ known ++ visNames insts
  | [], _, _ => by intro inst h; simp at h
  | inst₀ :: rest, known, hwf => by
      obtain ⟨_, _, _, _, _, _, _, _, _, hins, hrest⟩ := hwf
      intro inst hinst pe hpe n hn
      rcases List.mem_cons.mp hinst with rfl | hr
      · exact List.mem_append.mpr (Or.inl (hins pe hpe n hn))
      · have hthis := WFInstsSeq'_ins_mem rest _ hrest inst hr pe hpe n hn
        rw [visNames_cons, ← List.append_assoc]
        exact hthis

/-- `WFInstsSeq'` is monotone in `known`: enlarging the set of already-defined names preserves it. -/
theorem WFInstsSeq'_weaken : ∀ (insts : List Inst) (k1 k2 : List String),
    (∀ q ∈ k1, q ∈ k2) → WFInstsSeq' insts k1 → WFInstsSeq' insts k2
  | [], _, _, _, _ => trivial
  | inst :: rest, k1, k2, hsub, hwf => by
      obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, hins, hrest⟩ := hwf
      refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9,
        fun pe hpe n hn => hsub _ (hins pe hpe n hn), ?_⟩
      exact WFInstsSeq'_weaken rest _ _ (fun q hq => by
        rcases List.mem_append.mp hq with h | h
        · exact List.mem_append.mpr (Or.inl (hsub q h))
        · exact List.mem_append.mpr (Or.inr h)) hrest

theorem instWireNames_nodup_of (inst : Inst) (h : (instAllNames inst).Nodup) :
    (instWireNames inst).Nodup :=
  (List.nodup_append.mp h).1

theorem wireEntries_keys (F : Env) (acc : List (String × Nat)) (inst : Inst) :
    (inst.child.wires.map
      (fun w => (inst.rename w.name, childExtSeq F acc inst w.name))).map (·.1) = instWireNames inst := by
  simp only [instWireNames, List.map_map]; apply List.map_congr_left; intro w _; rfl

theorem outEntries_keys (F : Env) (acc : List (String × Nat)) (inst : Inst) :
    (inst.child.outputs.map
      (fun o => (inst.rename o.name, (eval o.expr (childExtSeq F acc inst)).toNat))).map (·.1)
        = instOutNames inst := by
  simp only [instOutNames, List.map_map]; apply List.map_congr_left; intro o _; rfl

/-- `Env.ofList` of `cycleStepExt` at an internal-wire net gives the child's wire value. -/
theorem cycleStepExt_wire (F : Env) (acc : List (String × Nat)) (inst : Inst)
    (w : Wire) (hw : w ∈ inst.child.wires)
    (hndall : (instAllNames inst).Nodup)
    (hnotacc : inst.rename w.name ∉ acc.map (·.1)) :
    Env.ofList (cycleStepExt F acc inst) (inst.rename w.name) = childExtSeq F acc inst w.name := by
  have hmemwire : inst.rename w.name ∈ instWireNames inst := List.mem_map.mpr ⟨w, hw, rfl⟩
  have hndwire : (instWireNames inst).Nodup := instWireNames_nodup_of inst hndall
  have hdisj := (List.nodup_append.mp hndall).2.2
  have hmem_accwire : inst.rename w.name
      ∈ ((acc ++ inst.child.wires.map
          (fun w => (inst.rename w.name, childExtSeq F acc inst w.name))).map (·.1)) := by
    rw [List.map_append, wireEntries_keys]; exact List.mem_append.mpr (Or.inr hmemwire)
  simp only [cycleStepExt]
  rw [ofList_append_left _ _ _ hmem_accwire, ofList_append_right _ _ _ hnotacc]
  exact ofList_lookup_mem inst.child.wires (fun w => inst.rename w.name)
    (fun w => childExtSeq F acc inst w.name) w hw hndwire

/-- `Env.ofList` of `cycleStepExt` at an output net gives the child's output value. -/
theorem cycleStepExt_out (F : Env) (acc : List (String × Nat)) (inst : Inst)
    (o : OutPort) (ho : o ∈ inst.child.outputs)
    (hndall : (instAllNames inst).Nodup)
    (hnotacc : inst.rename o.name ∉ acc.map (·.1)) :
    Env.ofList (cycleStepExt F acc inst) (inst.rename o.name)
      = (eval o.expr (childExtSeq F acc inst)).toNat := by
  have hmemout : inst.rename o.name ∈ instOutNames inst := List.mem_map.mpr ⟨o, ho, rfl⟩
  have hndout : (instOutNames inst).Nodup := (List.nodup_append.mp hndall).2.1
  have hdisj := (List.nodup_append.mp hndall).2.2
  have hnotwire : inst.rename o.name ∉ instWireNames inst :=
    fun hc => hdisj (inst.rename o.name) hc (inst.rename o.name) hmemout rfl
  have hnot_accwire : inst.rename o.name
      ∉ ((acc ++ inst.child.wires.map
          (fun w => (inst.rename w.name, childExtSeq F acc inst w.name))).map (·.1)) := by
    rw [List.map_append, wireEntries_keys]
    intro hc; rcases List.mem_append.mp hc with h1 | h2
    · exact hnotacc h1
    · exact hnotwire h2
  simp only [cycleStepExt]
  rw [ofList_append_right _ _ _ hnot_accwire]
  exact ofList_lookup_mem inst.child.outputs (fun o => inst.rename o.name)
    (fun o => (eval o.expr (childExtSeq F acc inst)).toNat) o ho hndout

/-! ## The sequential fold lemma — flat `evalWires` reproduces `cycleStepExt`

Wire-carrying analogue of `flatSeq_fold`: the whole flat wire fold reproduces, on every parent-input,
internal-wire, and instance-output net, exactly the values the extended hierarchical fold computes —
now carrying each child's register file (via `F`) AND its internal wire cone. -/
theorem flatSeq_fold' (F : Env) (insts : List Inst) :
    ∀ (acc : List (String × Nat)) (fe : Env),
      WFInstsSeq' insts (acc.map (·.1)) →
      (acc.map (·.1) ++ allFlatNames insts).Nodup →
      (∀ n ∈ acc.map (·.1), fe n = Env.ofList acc n) →
      (∀ inst ∈ insts, ∀ r ∈ inst.child.regs, fe (inst.rename r.name) = F (inst.rename r.name)) →
      (∀ inst ∈ insts, ∀ r ∈ inst.child.regs, inst.rename r.name ∉ allFlatNames insts) →
      ∀ n ∈ acc.map (·.1) ++ allFlatNames insts,
        evalWires (insts.flatMap Inst.flatWiresSeq) fe n
          = Env.ofList (insts.foldl (cycleStepExt F) acc) n := by
  induction insts with
  | nil =>
      intro acc fe _ _ hag _ _ n hn
      simp only [allFlatNames, List.flatMap_nil, List.append_nil] at hn
      simpa [List.flatMap_nil, evalWires] using hag n hn
  | cons inst rest ih =>
      intro acc fe hwf hnd hag hfereg hregvis n hn
      obtain ⟨hchain, houtvars, hnextbd, hregport, hwireport, hportdisj, hond, howdisj,
              hregout, hins, hrest⟩ := hwf
      have hkeys := cycleStepExt_keys F acc inst
      rw [allFlatNames_cons] at hnd
      have hdisjN := (List.nodup_append.mp hnd).2.2
      have hndtail := (List.nodup_append.mp hnd).2.1
      have hndinstall := (List.nodup_append.mp hndtail).1
      have hnd' : ((acc.map (·.1) ++ instAllNames inst) ++ allFlatNames rest).Nodup := by
        rw [List.append_assoc]; exact hnd
      have hflatnames : (Inst.flatWiresSeq inst).map (·.name) = instAllNames inst :=
        flatWiresSeq_names inst
      have hfereg_head : ∀ r ∈ inst.child.regs, fe (inst.rename r.name) = F (inst.rename r.name) :=
        fun r hr => hfereg inst (List.mem_cons_self) r hr
      have hB : ∀ m ∈ (cycleStepExt F acc inst).map (·.1),
            evalWires (Inst.flatWiresSeq inst) fe m = Env.ofList (cycleStepExt F acc inst) m := by
        intro m hm
        rw [hkeys] at hm
        rcases List.mem_append.mp hm with hmacc | hmall
        · have hmnotall : m ∉ (Inst.flatWiresSeq inst).map (·.name) := by
            rw [hflatnames]; intro hc
            exact hdisjN m hmacc m (List.mem_append.mpr (Or.inl hc)) rfl
          rw [evalWires_not_mem _ m hmnotall fe, hag m hmacc]
          simp only [cycleStepExt]
          rw [ofList_append_left _ _ m
                (by rw [List.map_append]; exact List.mem_append.mpr (Or.inl hmacc)),
              ofList_append_left _ _ m hmacc]
        · rcases List.mem_append.mp hmall with hmwire | hmout
          · obtain ⟨w, hw, hmw⟩ := List.mem_map.mp hmwire
            subst hmw
            have hnotacc : inst.rename w.name ∉ acc.map (·.1) := fun hc =>
              hdisjN _ hc _ (List.mem_append.mpr (Or.inl hmall)) rfl
            rw [flatWireNet_val inst F acc fe w hw hchain hregport hwireport hportdisj howdisj
                  hins hag hfereg_head,
                cycleStepExt_wire F acc inst w hw hndinstall hnotacc]
          · obtain ⟨o, ho, hmo⟩ := List.mem_map.mp hmout
            subst hmo
            show evalWires (Inst.flatWiresSeq inst) fe (inst.rename o.name)
              = Env.ofList (cycleStepExt F acc inst) (inst.rename o.name)
            have hnotacc : inst.rename o.name ∉ acc.map (·.1) := fun hc =>
              hdisjN _ hc _ (List.mem_append.mpr (Or.inl hmall)) rfl
            have haccout : ∀ nn ∈ acc.map (·.1), nn ∉ instOutNames inst := fun nn hnn hc =>
              hdisjN nn hnn nn (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hc)))) rfl
            rw [flatOutNet_val inst F acc fe o ho hchain houtvars hregport hwireport hportdisj hond
                  howdisj hregout haccout hins hag hfereg_head,
                cycleStepExt_out F acc inst o ho hndinstall hnotacc]
      have hC : WFInstsSeq' rest ((cycleStepExt F acc inst).map (·.1)) := by
        rw [hkeys]
        refine WFInstsSeq'_weaken rest _ _ ?_ hrest
        intro q hq
        rcases List.mem_append.mp hq with h | h
        · exact List.mem_append.mpr (Or.inl h)
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr h)))
      have hD : ((cycleStepExt F acc inst).map (·.1) ++ allFlatNames rest).Nodup := by rw [hkeys]; exact hnd'
      have hfereg' : ∀ inst' ∈ rest, ∀ r ∈ inst'.child.regs,
          evalWires (Inst.flatWiresSeq inst) fe (inst'.rename r.name) = F (inst'.rename r.name) := by
        intro inst' hinst' r hr
        have hnotwire : inst'.rename r.name ∉ (Inst.flatWiresSeq inst).map (·.name) := by
          rw [hflatnames]; intro hc
          exact hregvis inst' (List.mem_cons_of_mem _ hinst') r hr
            (by rw [allFlatNames_cons]; exact List.mem_append.mpr (Or.inl hc))
        rw [evalWires_not_mem _ _ hnotwire fe]
        exact hfereg inst' (List.mem_cons_of_mem _ hinst') r hr
      have hregvis' : ∀ inst' ∈ rest, ∀ r ∈ inst'.child.regs, inst'.rename r.name ∉ allFlatNames rest := by
        intro inst' hinst' r hr hc
        exact hregvis inst' (List.mem_cons_of_mem _ hinst') r hr
          (by rw [allFlatNames_cons]; exact List.mem_append.mpr (Or.inr hc))
      have hn' : n ∈ (cycleStepExt F acc inst).map (·.1) ++ allFlatNames rest := by
        rw [hkeys, List.append_assoc, ← allFlatNames_cons]; exact hn
      rw [List.flatMap_cons, evalWires_append, List.foldl_cons]
      exact ih (cycleStepExt F acc inst) (evalWires (Inst.flatWiresSeq inst) fe)
        hC hD hB hfereg' hregvis' n hn'

/-! ## Relating the extended fold back to `Parent.cycleEnvList`

`cycleStepExt` (with internal-wire entries) reproduces the flat fold; `Parent.cycleEnvList` (output-only)
is the reference hierarchical env.  They agree on parent-inputs and output nets: the extra wire entries
are fresh keys, and each output value is `eval o.expr (childExtSeq …)` whose child cone is insensitive to
the accumulator's wire entries (child inputs read only bound ports, which reference the shared clean keys). -/

/-- `childExtSeq` depends on the accumulator only through the instance-port expressions. -/
theorem childExtSeq_congr_acc (F : Env) (accE accC : List (String × Nat)) (inst : Inst)
    (hport : ∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, Env.ofList accE n = Env.ofList accC n) :
    childExtSeq F accE inst = childExtSeq F accC inst := by
  have hchildin : inst.childIn (Env.ofList accE) = inst.childIn (Env.ofList accC) := by
    funext n
    rw [childIn_ofList, childIn_ofList]
    cases hln : inst.ins.lookup n with
    | none => rfl
    | some ae =>
        have haemem : (n, ae) ∈ inst.ins := by
          obtain ⟨l₁, l₂, hl, _⟩ := List.lookup_eq_some_iff.mp hln; rw [hl]; simp
        show (eval ae.snd (Env.ofList accE)).toNat = (eval ae.snd (Env.ofList accC)).toNat
        rw [eval_congr ae.snd (Env.ofList accE) (Env.ofList accC)
              (fun k hk => hport (n, ae) haemem k hk)]
  simp only [childExtSeq, childBaseSeq, hchildin]

/-- Wire-agnostic key inventory of `cycleStep` (its keys are the output nets regardless of wires). -/
theorem cycleStep_keys' (F : Env) (acc : List (String × Nat)) (inst : Inst) :
    (cycleStep F acc inst).map (·.1) = acc.map (·.1) ++ instOutNames inst := by
  simp only [cycleStep, List.map_append, Module.outputs?eval, List.map_map, instOutNames]
  rfl

/-- One `cycleStep` (output-only) equals the output slice of `cycleStepExt` (given accumulator agreement),
    packaged as: their `Env.ofList`s agree on the parent-inputs and output nets, and the accumulator
    invariant is maintained.  See `cycleStepExt_agree`. -/
theorem cycleStepExt_agree (F : Env) (insts : List Inst) :
    ∀ (accE accC : List (String × Nat)),
      (∀ n ∈ accC.map (·.1), Env.ofList accE n = Env.ofList accC n) →
      (∀ n ∈ accC.map (·.1), n ∈ accE.map (·.1)) →
      WFInstsSeq' insts (accC.map (·.1)) →
      (accE.map (·.1) ++ allFlatNames insts).Nodup →
      ∀ n ∈ accC.map (·.1) ++ visNames insts,
        Env.ofList (insts.foldl (cycleStepExt F) accE) n
          = Env.ofList (insts.foldl (cycleStep F) accC) n := by
  induction insts with
  | nil =>
      intro accE accC hagree _ _ _ n hn
      simp only [visNames, List.flatMap_nil, List.append_nil] at hn
      simpa only [List.foldl_nil] using hagree n hn
  | cons inst rest ih =>
      intro accE accC hagree hsub hwf hnd n hn
      obtain ⟨hchain, houtvars, hnextbd, hregport, hwireport, hportdisj, hond, howdisj,
              hregout, hins, hrest⟩ := hwf
      -- child value insensitivity
      have hce : childExtSeq F accE inst = childExtSeq F accC inst :=
        childExtSeq_congr_acc F accE accC inst (fun pe hpe k hk => hagree k (hins pe hpe k hk))
      -- key inventories
      have hkeysE := cycleStepExt_keys F accE inst
      have hkeysC := cycleStep_keys' F accC inst
      rw [allFlatNames_cons] at hnd
      have hndE := (List.nodup_append.mp hnd)
      have hdisjE := hndE.2.2                 -- accE keys ⟂ (instAllNames inst ++ allFlatNames rest)
      have hndinstall := (List.nodup_append.mp hndE.2.1).1
      -- output entries of the two steps are equal
      have hout : (inst.child.outputs.map
            (fun o => (inst.rename o.name, (eval o.expr (childExtSeq F accE inst)).toNat)))
          = ((inst.child.outputs?eval (inst.regVals F) (inst.childIn (Env.ofList accC))).map
              (fun pv => (inst.instName ++ "." ++ pv.1, pv.2))) := by
        simp only [Module.outputs?eval, List.map_map, hce]
        apply List.map_congr_left; intro o _; simp only [childExtSeq, childBaseSeq]; rfl
      -- accumulator agreement maintained after one step
      have hagree' : ∀ m ∈ (cycleStep F accC inst).map (·.1),
          Env.ofList (cycleStepExt F accE inst) m = Env.ofList (cycleStep F accC inst) m := by
        intro m hm
        rw [cycleStep_keys'] at hm
        rcases List.mem_append.mp hm with hmc | hmo
        · -- old clean key
          have hmE : m ∈ accE.map (·.1) := hsub m hmc
          have hmnotall : m ∉ instAllNames inst := fun hc =>
            hdisjE m hmE m (List.mem_append.mpr (Or.inl hc)) rfl
          have hmnotout : m ∉ instOutNames inst := fun hc =>
            hmnotall (List.mem_append.mpr (Or.inr hc))
          have hmnotwire : m ∉ instWireNames inst := fun hc =>
            hmnotall (List.mem_append.mpr (Or.inl hc))
          -- ofList (cycleStepExt) m = ofList accE m ; ofList (cycleStep) m = ofList accC m
          have hE : Env.ofList (cycleStepExt F accE inst) m = Env.ofList accE m := by
            simp only [cycleStepExt]
            rw [ofList_append_left _ _ m (by
                  rw [List.map_append, wireEntries_keys]
                  exact List.mem_append.mpr (Or.inl hmE)),
                ofList_append_left _ _ m hmE]
          have hC' : Env.ofList (cycleStep F accC inst) m = Env.ofList accC m := by
            simp only [cycleStep]
            rw [ofList_append_left _ _ m hmc]
          rw [hE, hC', hagree m hmc]
        · -- new output key
          obtain ⟨o, ho, hmo⟩ := List.mem_map.mp hmo
          subst hmo
          show Env.ofList (cycleStepExt F accE inst) (inst.rename o.name)
            = Env.ofList (cycleStep F accC inst) (inst.rename o.name)
          have hnotaccE : inst.rename o.name ∉ accE.map (·.1) := fun hc =>
            hdisjE _ hc _ (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr
              (List.mem_map.mpr ⟨o, ho, rfl⟩))))) rfl
          have hnotaccC : inst.rename o.name ∉ accC.map (·.1) := fun hc =>
            hnotaccE (hsub _ hc)
          have hEeq : Env.ofList (cycleStepExt F accE inst) (inst.rename o.name)
              = (eval o.expr (childExtSeq F accE inst)).toNat :=
            cycleStepExt_out F accE inst o ho hndinstall hnotaccE
          have hCeq : Env.ofList (cycleStep F accC inst) (inst.rename o.name)
              = (eval o.expr (childExtSeq F accE inst)).toNat := by
            simp only [cycleStep]
            rw [ofList_append_right _ _ _ hnotaccC, ← hout]
            exact ofList_lookup_mem inst.child.outputs (fun o => inst.rename o.name)
              (fun o => (eval o.expr (childExtSeq F accE inst)).toNat) o ho
              (by have := (List.nodup_append.mp hndinstall).2.1; exact this)
          rw [hEeq, hCeq]
      have hsub' : ∀ m ∈ (cycleStep F accC inst).map (·.1), m ∈ (cycleStepExt F accE inst).map (·.1) := by
        intro m hm
        rw [hkeysE]; rw [cycleStep_keys'] at hm
        rcases List.mem_append.mp hm with hmc | hmo
        · exact List.mem_append.mpr (Or.inl (hsub m hmc))
        · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hmo)))
      have hrest' : WFInstsSeq' rest ((cycleStep F accC inst).map (·.1)) := by
        rw [cycleStep_keys']; exact hrest
      have hnd'' : ((cycleStepExt F accE inst).map (·.1) ++ allFlatNames rest).Nodup := by
        rw [hkeysE, List.append_assoc]; exact hnd
      have hn' : n ∈ (cycleStep F accC inst).map (·.1) ++ visNames rest := by
        rw [cycleStep_keys', List.append_assoc, ← visNames_cons]; exact hn
      rw [List.foldl_cons, List.foldl_cons]
      exact ih (cycleStepExt F accE inst) (cycleStep F accC inst) hagree' hsub' hrest' hnd'' n hn'

/-! ## The extended fold only appends — prefix values are preserved -/

theorem cycleStepExt_fold_prefix (F : Env) (insts : List Inst) :
    ∀ (acc : List (String × Nat)) (m : String), m ∈ acc.map (·.1) →
      (∀ inst ∈ insts, m ∉ instAllNames inst) →
      Env.ofList (insts.foldl (cycleStepExt F) acc) m = Env.ofList acc m := by
  induction insts with
  | nil => intro acc m hm _; rfl
  | cons inst rest ih =>
      intro acc m hm hfresh
      rw [List.foldl_cons]
      have hmnew : m ∈ (cycleStepExt F acc inst).map (·.1) := by
        rw [cycleStepExt_keys]; exact List.mem_append.mpr (Or.inl hm)
      rw [ih (cycleStepExt F acc inst) m hmnew
            (fun inst' hinst' => hfresh inst' (List.mem_cons_of_mem _ hinst'))]
      -- ofList (cycleStepExt F acc inst) m = ofList acc m
      have hmnotall : m ∉ instAllNames inst := hfresh inst (List.mem_cons_self)
      have hmnotwire : m ∉ instWireNames inst := fun hc =>
        hmnotall (List.mem_append.mpr (Or.inl hc))
      simp only [cycleStepExt]
      rw [ofList_append_left _ _ m (by
            rw [List.map_append, wireEntries_keys]; exact List.mem_append.mpr (Or.inl hm)),
          ofList_append_left _ _ m hm]

theorem cycleStep_fold_prefix (F : Env) (insts : List Inst) :
    ∀ (acc : List (String × Nat)) (m : String), m ∈ acc.map (·.1) →
      (∀ inst ∈ insts, m ∉ instOutNames inst) →
      Env.ofList (insts.foldl (cycleStep F) acc) m = Env.ofList acc m := by
  induction insts with
  | nil => intro acc m hm _; rfl
  | cons inst rest ih =>
      intro acc m hm hfresh
      rw [List.foldl_cons]
      have hmnew : m ∈ (cycleStep F acc inst).map (·.1) := by
        rw [cycleStep_keys']; exact List.mem_append.mpr (Or.inl hm)
      rw [ih (cycleStep F acc inst) m hmnew
            (fun inst' hinst' => hfresh inst' (List.mem_cons_of_mem _ hinst'))]
      simp only [cycleStep]
      rw [ofList_append_left _ _ m hm]

/-- The accumulator agreement is maintained by one `cycleStepExt`/`cycleStep` step. -/
theorem cycleStepExt_maintain (F : Env) (accE accC : List (String × Nat)) (inst : Inst)
    (hagree : ∀ n ∈ accC.map (·.1), Env.ofList accE n = Env.ofList accC n)
    (hsub : ∀ n ∈ accC.map (·.1), n ∈ accE.map (·.1))
    (hins : ∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ accC.map (·.1))
    (hndinstall : (instAllNames inst).Nodup)
    (hfreshE : ∀ q ∈ accE.map (·.1), q ∉ instAllNames inst) :
    (∀ m ∈ (cycleStep F accC inst).map (·.1),
        Env.ofList (cycleStepExt F accE inst) m = Env.ofList (cycleStep F accC inst) m)
    ∧ (∀ m ∈ (cycleStep F accC inst).map (·.1), m ∈ (cycleStepExt F accE inst).map (·.1)) := by
  have hce : childExtSeq F accE inst = childExtSeq F accC inst :=
    childExtSeq_congr_acc F accE accC inst (fun pe hpe k hk => hagree k (hins pe hpe k hk))
  have hout : (inst.child.outputs.map
        (fun o => (inst.rename o.name, (eval o.expr (childExtSeq F accE inst)).toNat)))
      = ((inst.child.outputs?eval (inst.regVals F) (inst.childIn (Env.ofList accC))).map
          (fun pv => (inst.instName ++ "." ++ pv.1, pv.2))) := by
    simp only [Module.outputs?eval, List.map_map, hce]
    apply List.map_congr_left; intro o _; simp only [childExtSeq, childBaseSeq]; rfl
  refine ⟨?_, ?_⟩
  · intro m hm
    rw [cycleStep_keys'] at hm
    rcases List.mem_append.mp hm with hmc | hmo
    · have hmE : m ∈ accE.map (·.1) := hsub m hmc
      have hmnotall : m ∉ instAllNames inst := hfreshE m hmE
      have hmnotwire : m ∉ instWireNames inst := fun hc =>
        hmnotall (List.mem_append.mpr (Or.inl hc))
      have hE : Env.ofList (cycleStepExt F accE inst) m = Env.ofList accE m := by
        simp only [cycleStepExt]
        rw [ofList_append_left _ _ m (by
              rw [List.map_append, wireEntries_keys]; exact List.mem_append.mpr (Or.inl hmE)),
            ofList_append_left _ _ m hmE]
      have hC' : Env.ofList (cycleStep F accC inst) m = Env.ofList accC m := by
        simp only [cycleStep]; rw [ofList_append_left _ _ m hmc]
      rw [hE, hC', hagree m hmc]
    · obtain ⟨o, ho, hmo⟩ := List.mem_map.mp hmo
      subst hmo
      show Env.ofList (cycleStepExt F accE inst) (inst.rename o.name)
        = Env.ofList (cycleStep F accC inst) (inst.rename o.name)
      have hnotaccE : inst.rename o.name ∉ accE.map (·.1) := fun hc =>
        hfreshE _ hc (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨o, ho, rfl⟩)))
      have hnotaccC : inst.rename o.name ∉ accC.map (·.1) := fun hc => hnotaccE (hsub _ hc)
      have hEeq : Env.ofList (cycleStepExt F accE inst) (inst.rename o.name)
          = (eval o.expr (childExtSeq F accE inst)).toNat :=
        cycleStepExt_out F accE inst o ho hndinstall hnotaccE
      have hCeq : Env.ofList (cycleStep F accC inst) (inst.rename o.name)
          = (eval o.expr (childExtSeq F accE inst)).toNat := by
        simp only [cycleStep]
        rw [ofList_append_right _ _ _ hnotaccC, ← hout]
        exact ofList_lookup_mem inst.child.outputs (fun o => inst.rename o.name)
          (fun o => (eval o.expr (childExtSeq F accE inst)).toNat) o ho
          ((List.nodup_append.mp hndinstall).2.1)
      rw [hEeq, hCeq]
  · intro m hm
    rw [cycleStepExt_keys]; rw [cycleStep_keys'] at hm
    rcases List.mem_append.mp hm with hmc | hmo
    · exact List.mem_append.mpr (Or.inl (hsub m hmc))
    · exact List.mem_append.mpr (Or.inr (List.mem_append.mpr (Or.inr hmo)))

/-- The full extended fold's value at an internal-wire net equals `childExtSeq` over the full
    (clean) cycle-env fold — matching the internal wire `Parent.nextFlat`'s child step recomputes. -/
theorem cycleStepExt_wire_val (F : Env) (insts : List Inst) :
    ∀ (accE accC : List (String × Nat)),
      (∀ n ∈ accC.map (·.1), Env.ofList accE n = Env.ofList accC n) →
      (∀ n ∈ accC.map (·.1), n ∈ accE.map (·.1)) →
      WFInstsSeq' insts (accC.map (·.1)) →
      (accE.map (·.1) ++ allFlatNames insts).Nodup →
      ∀ inst ∈ insts, ∀ w ∈ inst.child.wires,
        Env.ofList (insts.foldl (cycleStepExt F) accE) (inst.rename w.name)
          = childExtSeq F (insts.foldl (cycleStep F) accC) inst w.name := by
  induction insts with
  | nil => intro _ _ _ _ _ _ inst hinst; simp at hinst
  | cons inst0 rest ih =>
      intro accE accC hagree hsub hwf hnd inst hinst w hw
      obtain ⟨hchain, houtvars, hnextbd, hregport, hwireport, hportdisj, hond, howdisj,
              hregout, hins, hrest⟩ := hwf
      rw [allFlatNames_cons] at hnd
      have hndE := (List.nodup_append.mp hnd)
      have hdisjE := hndE.2.2
      have hndinstall := (List.nodup_append.mp hndE.2.1).1
      have hfreshE : ∀ q ∈ accE.map (·.1), q ∉ instAllNames inst0 := fun q hq hc =>
        hdisjE q hq q (List.mem_append.mpr (Or.inl hc)) rfl
      obtain ⟨hagree', hsub'⟩ := cycleStepExt_maintain F accE accC inst0 hagree hsub hins hndinstall hfreshE
      have hrest' : WFInstsSeq' rest ((cycleStep F accC inst0).map (·.1)) := by
        rw [cycleStep_keys']; exact hrest
      have hnd'' : ((cycleStepExt F accE inst0).map (·.1) ++ allFlatNames rest).Nodup := by
        rw [cycleStepExt_keys, List.append_assoc]; exact hnd
      -- fresh facts for prefix lemmas: accC keys ⟂ instOutNames of every inst
      have haccCfreshOut : ∀ n ∈ accC.map (·.1), ∀ inst' ∈ (inst0 :: rest), n ∉ instOutNames inst' := by
        intro n hn inst' hinst' hc
        have hnE := hsub n hn
        have hmem : n ∈ allFlatNames (inst0 :: rest) := by
          rw [allFlatNames_cons]
          rcases List.mem_cons.mp hinst' with rfl | hr
          · exact List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hc)))
          · exact List.mem_append.mpr (Or.inr (List.mem_flatMap.mpr ⟨inst', hr,
              List.mem_append.mpr (Or.inr hc)⟩))
        exact hdisjE n hnE n (by rw [← allFlatNames_cons]; exact hmem) rfl
      rw [List.foldl_cons, List.foldl_cons]
      rcases List.mem_cons.mp hinst with rfl | hr
      · -- head instance
        have hdisj2 := (List.nodup_append.mp hndE.2.1).2.2  -- instAllNames inst0 ⟂ allFlatNames rest
        have hwirenet : inst.rename w.name ∈ instAllNames inst :=
          List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨w, hw, rfl⟩))
        have hfreshRest : ∀ inst' ∈ rest, inst.rename w.name ∉ instAllNames inst' := by
          intro inst' hinst' hc
          exact hdisj2 (inst.rename w.name) hwirenet (inst.rename w.name)
            (List.mem_flatMap.mpr ⟨inst', hinst', hc⟩) rfl
        have hmemE : inst.rename w.name ∈ (cycleStepExt F accE inst).map (·.1) := by
          rw [cycleStepExt_keys]; exact List.mem_append.mpr (Or.inr hwirenet)
        rw [cycleStepExt_fold_prefix F rest (cycleStepExt F accE inst) (inst.rename w.name)
              hmemE hfreshRest]
        have hnotaccE : inst.rename w.name ∉ accE.map (·.1) := fun hc => hfreshE _ hc hwirenet
        rw [cycleStepExt_wire F accE inst w hw hndinstall hnotaccE]
        have hRHS : childExtSeq F (rest.foldl (cycleStep F) (cycleStep F accC inst)) inst
            = childExtSeq F accC inst := by
          apply childExtSeq_congr_acc
          intro pe hpe k hk
          have hkC : k ∈ accC.map (·.1) := hins pe hpe k hk
          have hpref : Env.ofList ((inst :: rest).foldl (cycleStep F) accC) k = Env.ofList accC k :=
            cycleStep_fold_prefix F (inst :: rest) accC k hkC
              (fun inst' hinst' => haccCfreshOut k hkC inst' hinst')
          rwa [List.foldl_cons] at hpref
        rw [hRHS, childExtSeq_congr_acc F accE accC inst
              (fun pe hpe k hk => hagree k (hins pe hpe k hk))]
      · -- tail instance
        exact ih (cycleStepExt F accE inst0) (cycleStep F accC inst0) hagree' hsub' hrest' hnd''
          inst hr w hw

/-! ## Well-formed wire-carrying sequential parent -/

theorem visNames_sub_allFlatNames (insts : List Inst) (n : String) (h : n ∈ visNames insts) :
    n ∈ allFlatNames insts := by
  obtain ⟨inst, hinst, hn⟩ := List.mem_flatMap.mp h
  exact List.mem_flatMap.mpr ⟨inst, hinst, List.mem_append.mpr (Or.inr hn)⟩

/-- Bundled well-formedness for the wire-carrying hierarchical bridges.  Extends `WFParentSeq` along
    the wire dimension: children may carry internal wires (topologically ordered, distinct, feeding
    outputs and register next-states); every renamed wire net is a fresh parent-visible net (distinct
    from inputs, registers, and every other flat net). -/
structure WFParentSeq' (p : Parent) : Prop where
  wf         : WFInstsSeq' p.insts (p.inputs.map (·.name))
  ndAll      : (p.inputs.map (·.name) ++ allFlatNames p.insts).Nodup
  ndReg      : (regNamesOf p.insts).Nodup
  ndChildReg : ∀ inst ∈ p.insts, (inst.child.regs.map (·.name)).Nodup
  regAll     : ∀ q ∈ regNamesOf p.insts, q ∉ allFlatNames p.insts
  regIn      : ∀ q ∈ regNamesOf p.insts, q ∉ p.inputs.map (·.name)
  nextBd     : ∀ inst ∈ p.insts, ∀ r ∈ inst.child.regs, ∀ n ∈ r.next.vars,
                 n ∈ inst.ins.map (·.1) ∨ n ∈ inst.child.regs.map (·.name)
                   ∨ n ∈ inst.child.wires.map (·.name)
  noRst      : ∀ inst ∈ p.insts, inst.child.reset = none
  outPO      : ∀ o ∈ p.outputs, ∀ n ∈ o.expr.vars, n ∈ p.inputs.map (·.name) ++ visNames p.insts

/-- The flat module's wire nets are exactly the parent's `allFlatNames`. -/
theorem flattenParentSeq_wireNames' (p : Parent) :
    (flattenParentSeq p).wires.map (·.name) = allFlatNames p.insts := by
  show (p.insts.flatMap Inst.flatWiresSeq).map (·.name) = allFlatNames p.insts
  rw [List.map_flatMap]
  show p.insts.flatMap (fun inst => (Inst.flatWiresSeq inst).map (·.name)) = p.insts.flatMap instAllNames
  have hf : (fun inst => (Inst.flatWiresSeq inst).map (·.name)) = instAllNames := by
    funext inst; exact flatWiresSeq_names inst
  rw [hf]

/-! ## Bridge (1): init (registers are wire-agnostic) -/

theorem initRegs_eq_initFlat' (p : Parent) (hndReg : (regNamesOf p.insts).Nodup)
    (q : String) (hq : q ∈ regNamesOf p.insts) :
    (flattenParentSeq p).initRegs q = Env.ofList (Parent.initFlat p) q := by
  obtain ⟨inst, hinst, hq2⟩ := List.mem_flatMap.mp hq
  obtain ⟨r, hr, hqe⟩ := List.mem_map.mp hq2
  have hqe' : inst.instName ++ "." ++ r.name = q := hqe
  have hnd : ((flattenParentSeq p).regs.map (·.name)).Nodup := by
    rw [flattenParentSeq_regNames]; exact hndReg
  have hmem : (⟨inst.rename r.name, r.width, substRename inst.ins inst.rename r.next, r.init, r.emitInit,
      r.asyncReset.map (fun ar => (inst.rename ar.1, ar.2)), r.negedge, none, none⟩ : Reg)
        ∈ (flattenParentSeq p).regs := by
    rw [flattenParentSeq_regs]
    exact List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
  have hfind := find?_name_nodup (flattenParentSeq p).regs _ hmem hnd
  rw [hqe] at hfind
  have hR : Env.ofList (Parent.initFlat p) q = r.init.toNat := by
    apply ofList_mem_nodup
    · exact List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, by rw [hqe']⟩⟩
    · rw [initFlat_keys]; exact hndReg
  rw [hR]
  simp only [Module.initRegs, hfind]

/-! ## Base env-agreement: flat `evalWires` = the extended hierarchical fold -/

theorem flatSeq_agree' (p : Parent) (wf : WFParentSeq' p) (Fflat Fhier : Env)
    (inputs : List (String × Nat)) (hin : inputs.map (·.1) = p.inputs.map (·.name))
    (hagreeReg : ∀ q ∈ regNamesOf p.insts, Fflat q = Fhier q) :
    ∀ n ∈ inputs.map (·.1) ++ allFlatNames p.insts,
      evalWires (flattenParentSeq p).wires
          (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name))) n
        = Env.ofList (p.insts.foldl (cycleStepExt Fhier) inputs) n := by
  have hregeq := flattenParentSeq_regNames p
  have hag : ∀ n ∈ inputs.map (·.1),
      cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name)) n
        = Env.ofList inputs n := by
    intro n hn
    have hnin : n ∈ p.inputs.map (·.name) := by rw [← hin]; exact hn
    have hnotreg : n ∉ regNamesOf p.insts := fun hc => wf.regIn n hc hnin
    simp only [cycleEnv, hregeq, contains_false_of_not_mem hnotreg, Bool.false_eq_true, if_false]
  have hfereg : ∀ inst ∈ p.insts, ∀ r ∈ inst.child.regs,
      cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name)) (inst.rename r.name)
        = Fhier (inst.rename r.name) := by
    intro inst hinst r hr
    have hmem : inst.rename r.name ∈ regNamesOf p.insts :=
      List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
    simp only [cycleEnv, hregeq, contains_true_of_mem hmem, if_true]
    exact hagreeReg _ hmem
  have hregvis : ∀ inst ∈ p.insts, ∀ r ∈ inst.child.regs, inst.rename r.name ∉ allFlatNames p.insts :=
    fun inst hinst r hr =>
      wf.regAll _ (List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, rfl⟩⟩)
  have hmain := flatSeq_fold' Fhier p.insts inputs
    (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name)))
    (by rw [hin]; exact wf.wf) (by rw [hin]; exact wf.ndAll) hag hfereg hregvis
  intro n hn
  exact hmain n hn

/-- The flat cycle env agrees with `Parent.cycleEnvList` on parent-inputs and output nets. -/
theorem flatSeq_agree'_out (p : Parent) (wf : WFParentSeq' p) (Fflat Fhier : Env)
    (inputs : List (String × Nat)) (hin : inputs.map (·.1) = p.inputs.map (·.name))
    (hagreeReg : ∀ q ∈ regNamesOf p.insts, Fflat q = Fhier q) :
    ∀ n ∈ inputs.map (·.1) ++ visNames p.insts,
      evalWires (flattenParentSeq p).wires
          (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name))) n
        = Env.ofList (Parent.cycleEnvList p Fhier inputs) n := by
  intro n hn
  have hn' : n ∈ inputs.map (·.1) ++ allFlatNames p.insts := by
    rcases List.mem_append.mp hn with h | h
    · exact List.mem_append.mpr (Or.inl h)
    · exact List.mem_append.mpr (Or.inr (visNames_sub_allFlatNames _ n h))
  rw [flatSeq_agree' p wf Fflat Fhier inputs hin hagreeReg n hn',
      cycleStepExt_agree Fhier p.insts inputs inputs (fun _ _ => rfl) (fun _ h => h)
        (by rw [hin]; exact wf.wf) (by rw [hin]; exact wf.ndAll) n hn,
      cycleEnvList_eq]

/-! ## Bridge (3): output -/

theorem flatOutputs_eq_outCycle' (p : Parent) (wf : WFParentSeq' p)
    (Fflat Fhier : Env) (inputs : List (String × Nat))
    (hin : inputs.map (·.1) = p.inputs.map (·.name))
    (hagreeReg : ∀ q ∈ regNamesOf p.insts, Fflat q = Fhier q) :
    (flattenParentSeq p).outputs?eval Fflat (Env.ofList inputs) = Parent.outCycle p Fhier inputs := by
  have hagree := flatSeq_agree'_out p wf Fflat Fhier inputs hin hagreeReg
  show p.outputs.map (fun o => (o.name,
        (eval o.expr (evalWires (flattenParentSeq p).wires
           (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name))))).toNat))
     = p.outputs.map (fun o => (o.name,
        (eval o.expr (Env.ofList (Parent.cycleEnvList p Fhier inputs))).toNat))
  apply List.map_congr_left
  intro o ho
  have heq : eval o.expr (evalWires (flattenParentSeq p).wires
        (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name))))
      = eval o.expr (Env.ofList (Parent.cycleEnvList p Fhier inputs)) := by
    apply eval_congr
    intro n hn
    exact hagree n (by rw [hin]; exact wf.outPO o ho n hn)
  rw [heq]

/-! ## Bridge (2): step -/

/-- A (possibly wire-carrying) child's `step` clocks register `r`'s `next` (no reset) evaluated in the
    wire-extended cycle env. -/
theorem step_reg (m : Module) (regVals inputs : Env) (r : Reg)
    (hfind : m.regs.find? (·.name = r.name) = some r) :
    m.step regVals inputs false r.name
      = (eval r.next (evalWires m.wires (cycleEnv regVals inputs (m.regs.map (·.name))))).toNat := by
  unfold Module.step
  simp only [hfind, Bool.false_eq_true, if_false]

theorem flatStep_eq_nextFlat' (p : Parent) (wf : WFParentSeq' p)
    (Fflat Fhier : Env) (inputs : List (String × Nat))
    (hin : inputs.map (·.1) = p.inputs.map (·.name))
    (hagreeReg : ∀ q ∈ regNamesOf p.insts, Fflat q = Fhier q)
    (q : String) (hq : q ∈ regNamesOf p.insts) :
    (flattenParentSeq p).step Fflat (Env.ofList inputs) false q
      = Env.ofList (Parent.nextFlat p Fhier inputs) q := by
  obtain ⟨inst, hinst, hq2⟩ := List.mem_flatMap.mp hq
  obtain ⟨r, hr, hqe⟩ := List.mem_map.mp hq2
  have hqe' : inst.instName ++ "." ++ r.name = q := hqe
  obtain ⟨hchain, houtvars, hnextbd_all, hregport, hwireport, hportdisj, hond, howdisj, hregout⟩ :=
    WFInstsSeq'_mem p.insts _ wf.wf inst hinst
  have hndchild := wf.ndChildReg inst hinst
  have hnextbd := wf.nextBd inst hinst r hr
  let e : Env := evalWires (flattenParentSeq p).wires
      (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name)))
  have he : e = evalWires (flattenParentSeq p).wires
      (cycleEnv Fflat (Env.ofList inputs) ((flattenParentSeq p).regs.map (·.name))) := rfl
  have hnd : ((flattenParentSeq p).regs.map (·.name)).Nodup := by
    rw [flattenParentSeq_regNames]; exact wf.ndReg
  have hmemF : (⟨inst.rename r.name, r.width, substRename inst.ins inst.rename r.next, r.init, r.emitInit,
      r.asyncReset.map (fun ar => (inst.rename ar.1, ar.2)), r.negedge, none, none⟩ : Reg)
        ∈ (flattenParentSeq p).regs := by
    rw [flattenParentSeq_regs]
    exact List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, rfl⟩⟩
  have hfindF := find?_name_nodup (flattenParentSeq p).regs _ hmemF hnd
  rw [hqe] at hfindF
  have hFlat : (flattenParentSeq p).step Fflat (Env.ofList inputs) false q
      = (eval (substRename inst.ins inst.rename r.next) e).toNat := by
    rw [he]; simp only [Module.step, hfindF, Bool.false_eq_true, if_false]
  have hHier : Env.ofList (Parent.nextFlat p Fhier inputs) q
      = inst.child.step (inst.regVals Fhier)
          (inst.childIn (Env.ofList (Parent.cycleEnvList p Fhier inputs))) false r.name := by
    have hmemN : (q, inst.child.step (inst.regVals Fhier)
        (inst.childIn (Env.ofList (Parent.cycleEnvList p Fhier inputs)))
        (inst.resetActive (Env.ofList (Parent.cycleEnvList p Fhier inputs))) r.name)
          ∈ Parent.nextFlat p Fhier inputs :=
      List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨r, hr, by rw [hqe']⟩⟩
    have hndN : ((Parent.nextFlat p Fhier inputs).map (·.1)).Nodup := by
      rw [nextFlat_keys]; exact wf.ndReg
    rw [ofList_mem_nodup _ q _ hmemN hndN,
        show inst.resetActive (Env.ofList (Parent.cycleEnvList p Fhier inputs)) = false from by
          simp only [Inst.resetActive, wf.noRst inst hinst]]
  rw [hFlat, hHier,
      step_reg inst.child (inst.regVals Fhier)
        (inst.childIn (Env.ofList (Parent.cycleEnvList p Fhier inputs))) r
        (find?_name_nodup inst.child.regs r hr hndchild),
      show evalWires inst.child.wires (cycleEnv (inst.regVals Fhier)
            (inst.childIn (Env.ofList (Parent.cycleEnvList p Fhier inputs)))
            (inst.child.regs.map (·.name)))
          = childExtSeq Fhier (Parent.cycleEnvList p Fhier inputs) inst from rfl,
      eval_substRename]
  congr 1
  apply eval_congr
  intro n hn
  -- childEnvSeq inst.ins inst.rename e n = childExtSeq Fhier (cycleEnvList) inst n
  rcases hnextbd n hn with hport | hreg | hwire
  · -- input port
    obtain ⟨pp, hpp, hppn⟩ := List.mem_map.mp hport
    have hsome : (inst.ins.lookup n).isSome := by
      rw [List.lookup_isSome_iff]; exact ⟨pp, hpp, by simp [hppn]⟩
    obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp hsome
    have haemem : (n, ae) ∈ inst.ins := by
      obtain ⟨l₁, l₂, hl, _⟩ := List.lookup_eq_some_iff.mp hae; rw [hl]; simp
    have hnotreg : n ∉ inst.child.regs.map (·.name) := by
      intro hc; obtain ⟨rr, hrr, hrrn⟩ := List.mem_map.mp hc
      rw [← hrrn] at hae; rw [hregport rr hrr] at hae; simp at hae
    have hnotwire : n ∉ inst.child.wires.map (·.name) := by
      intro hc; obtain ⟨wv, hwv, hwn⟩ := List.mem_map.mp hc
      rw [← hwn] at hae; rw [hwireport wv hwv] at hae; simp at hae
    simp only [childEnvSeq, hae, childExtSeq]
    rw [evalWires_not_mem _ n hnotwire]
    simp only [childBaseSeq, cycleEnv, contains_false_of_not_mem hnotreg, Bool.false_eq_true,
               if_false, childIn_ofList, hae]
    congr 1
    apply eval_congr
    intro k hk
    have hkin : k ∈ p.inputs.map (·.name) ++ visNames p.insts :=
      WFInstsSeq'_ins_mem p.insts _ wf.wf inst hinst (n, ae) haemem k hk
    have hkin' : k ∈ inputs.map (·.1) ++ visNames p.insts := by rw [hin]; exact hkin
    have hagr := flatSeq_agree'_out p wf Fflat Fhier inputs hin hagreeReg k hkin'
    rw [he]; exact hagr
  · -- register
    obtain ⟨rr, hrr, hrrn⟩ := List.mem_map.mp hreg
    have hnone : inst.ins.lookup n = none := by rw [← hrrn]; exact hregport rr hrr
    have hregnet : inst.rename n ∈ regNamesOf p.insts :=
      List.mem_flatMap.mpr ⟨inst, hinst, List.mem_map.mpr ⟨rr, hrr, by rw [hrrn]⟩⟩
    have hnotwire : n ∉ inst.child.wires.map (·.name) := by
      intro hc; obtain ⟨wv, hwv, hwn⟩ := List.mem_map.mp hc
      have hwirenet : inst.rename n ∈ allFlatNames p.insts :=
        List.mem_flatMap.mpr ⟨inst, hinst,
          List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨wv, hwv, by rw [hwn]⟩))⟩
      exact wf.regAll (inst.rename n) hregnet hwirenet
    have hLHS : childEnvSeq inst.ins inst.rename e n = Fhier (inst.rename n) := by
      simp only [childEnvSeq, hnone]
      have hnotflatwire : inst.rename n ∉ (flattenParentSeq p).wires.map (·.name) := by
        rw [flattenParentSeq_wireNames']; exact wf.regAll (inst.rename n) hregnet
      have hmemreg : inst.rename n ∈ (flattenParentSeq p).regs.map (·.name) := by
        rw [flattenParentSeq_regNames]; exact hregnet
      rw [he, evalWires_not_mem _ (inst.rename n) hnotflatwire]
      simp only [cycleEnv, contains_true_of_mem hmemreg, if_true]
      exact hagreeReg (inst.rename n) hregnet
    have hRHS : childExtSeq Fhier (Parent.cycleEnvList p Fhier inputs) inst n = Fhier (inst.rename n) := by
      simp only [childExtSeq]
      rw [evalWires_not_mem _ n hnotwire]
      simp only [childBaseSeq, cycleEnv, contains_true_of_mem hreg, if_true, Inst.regVals, Inst.rename]
    rw [hLHS, hRHS]
  · -- internal wire
    obtain ⟨wv, hwv, hwn⟩ := List.mem_map.mp hwire
    have hnone : inst.ins.lookup n = none := by rw [← hwn]; exact hwireport wv hwv
    have hmem_all : inst.rename n ∈ inputs.map (·.1) ++ allFlatNames p.insts := by
      refine List.mem_append.mpr (Or.inr ?_)
      exact List.mem_flatMap.mpr ⟨inst, hinst,
        List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨wv, hwv, by rw [hwn]⟩))⟩
    simp only [childEnvSeq, hnone]
    rw [he, flatSeq_agree' p wf Fflat Fhier inputs hin hagreeReg (inst.rename n) hmem_all]
    have hwval := cycleStepExt_wire_val Fhier p.insts inputs inputs (fun _ _ => rfl) (fun _ h => h)
      (by rw [hin]; exact wf.wf) (by rw [hin]; exact wf.ndAll) inst hinst wv hwv
    rw [show inst.rename n = inst.rename wv.name from by rw [hwn], hwval, cycleEnvList_eq]
    simp only [childExtSeq, childBaseSeq]
    rw [hwn]

/-! ## Bridge (4): the whole-trace corollary over `simulateSeq` -/

/-- **Whole-trace corollary (wire-carrying children).**  For a well-formed wire-carrying parent, the
    flat-`Module` whole register trace `Parent.regTrace` (reset-free) agrees, on every flat register net
    and at every cycle, with the HIERARCHICAL register state `Parent.hierRegTrace` computed by
    `Parent.nextFlat` / `Parent.simulateSeq`. -/
theorem Parent.regTrace_eq_hierRegTrace' (p : Parent) (wf : WFParentSeq' p)
    (inputs : Nat → List (String × Nat))
    (hin : ∀ t, (inputs t).map (·.1) = p.inputs.map (·.name)) :
    ∀ (t : Nat) (q : String), q ∈ regNamesOf p.insts →
      p.regTrace (fun t => Env.ofList (inputs t)) (fun _ => false) t q
        = Parent.hierRegTrace p inputs t q := by
  intro t
  induction t with
  | zero =>
      intro q hq
      simp only [Parent.regTrace_zero, Parent.hierRegTrace]
      exact initRegs_eq_initFlat' p wf.ndReg q hq
  | succ n ih =>
      intro q hq
      simp only [Parent.regTrace_succ, Parent.hierRegTrace]
      exact flatStep_eq_nextFlat' p wf
        (p.regTrace (fun t => Env.ofList (inputs t)) (fun _ => false) n)
        (Parent.hierRegTrace p inputs n) (inputs n) (hin n) ih q hq

end LeanRTL
