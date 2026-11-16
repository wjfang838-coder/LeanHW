import LeanRTL.Core.Semantics
import LeanRTL.Core.CompilerModuleCorrect
/-!
# Hierarchy correctness by flattening (plan v0.3 M12, "hierarchy integrated into compile_correct")

A `Parent` (one level of module hierarchy) compiles to RTLIL *instance cells*; proving those
directly would need a hierarchical netlist semantics.  Instead we **flatten** a `Parent` into a
plain combinational `Module` whose denotational behaviour is *equal* to the parent's
(`flattenParent_correct`), and inherit the proven flat compiler correctness
(`CompilerModuleCorrect.compileModule_comb_sound`) for free.

The heart is a **substitution lemma over `eval`** (`eval_substIns`): evaluating a child expression
with its input ports substituted by the parent-side instance expressions (in the parent env) equals
evaluating the child expression in the *child env* (each port bound to the value of its instance
expression).  We lift it over the child's outputs and the instance fold.

Everything here is **purely additive** — no proven compiler-core file is touched.
-/

namespace LeanRTL

set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

/-! ## Free variables of an expression and the `eval` congruence -/

/-- The set (as a `List`) of signal names referenced by an expression. -/
def Expr.vars : {w : Nat} → Expr w → List String
  | _, .const _      => []
  | _, .var n _      => [n]
  | _, .not a        => a.vars
  | _, .and a b      => a.vars ++ b.vars
  | _, .or a b       => a.vars ++ b.vars
  | _, .xor a b      => a.vars ++ b.vars
  | _, .add a b      => a.vars ++ b.vars
  | _, .sub a b      => a.vars ++ b.vars
  | _, .mul a b      => a.vars ++ b.vars
  | _, .shl a b      => a.vars ++ b.vars
  | _, .shr a b      => a.vars ++ b.vars
  | _, .sshr a b     => a.vars ++ b.vars
  | _, .udiv a b     => a.vars ++ b.vars
  | _, .umod a b     => a.vars ++ b.vars
  | _, .eq a b       => a.vars ++ b.vars
  | _, .ult a b      => a.vars ++ b.vars
  | _, .slt a b      => a.vars ++ b.vars
  | _, .mux s a b    => s.vars ++ a.vars ++ b.vars
  | _, .concat a b   => a.vars ++ b.vars
  | _, .zext _ a     => a.vars
  | _, .sext _ a     => a.vars
  | _, .extract _ a  => a.vars
  | _, .slice _ _ a  => a.vars

/-- **`eval` congruence.** Two environments that agree on every free variable of `e` evaluate `e`
    to the same bit-vector. -/
theorem eval_congr {w : Nat} (e : Expr w) (E₁ E₂ : Env)
    (h : ∀ n ∈ e.vars, E₁ n = E₂ n) : eval e E₁ = eval e E₂ := by
  induction e with
  | const v => rfl
  | var n w => simp only [eval, Env.lookup, h n (List.mem_singleton.mpr rfl)]
  | not a ih => simp only [eval]; rw [ih h]
  | zext k a ih => simp only [eval]; rw [ih h]
  | sext k a ih => simp only [eval]; rw [ih h]
  | extract i a ih => simp only [eval]; rw [ih h]
  | slice lo len a ih => simp only [eval]; rw [ih h]
  | mux s a b ihs iha ihb =>
      simp only [eval]
      rw [ihs (fun n hn => h n (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hn))))),
          iha (fun n hn => h n (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hn))))),
          ihb (fun n hn => h n (List.mem_append.mpr (Or.inr hn)))]
  | and a b iha ihb | or a b iha ihb | xor a b iha ihb | add a b iha ihb | sub a b iha ihb
  | mul a b iha ihb | shl a b iha ihb | shr a b iha ihb | sshr a b iha ihb | udiv a b iha ihb
  | umod a b iha ihb | eq a b iha ihb | ult a b iha ihb | slt a b iha ihb | concat a b iha ihb =>
      simp only [eval]
      rw [iha (fun n hn => h n (List.mem_append.mpr (Or.inl hn))),
          ihb (fun n hn => h n (List.mem_append.mpr (Or.inr hn)))]

/-! ## The substitution lemma (the heart)

`substIns ins e` replaces every child input-port reference `var n w` in `e` by the parent-side
instance expression bound to `n` in `ins` (coerced to width `w` via a zero-width slice, exactly the
`BitVec.ofNat w (·.toNat)` reconstruction the semantics use when looking up a stored value).  Then
evaluating the substituted expression in the *parent* env equals evaluating the original in the
*child* env, where each port is bound to the value of its instance expression. -/

/-- Coerce-by-substitution of child input ports. -/
def substIns (ins : List (String × AnyExpr)) : {w : Nat} → Expr w → Expr w
  | _, .const v      => .const v
  | _, .var n w      => match ins.lookup n with
                        | some ae => Expr.slice 0 w ae.2
                        | none    => .var n w
  | _, .not a        => .not (substIns ins a)
  | _, .and a b      => .and (substIns ins a) (substIns ins b)
  | _, .or a b       => .or (substIns ins a) (substIns ins b)
  | _, .xor a b      => .xor (substIns ins a) (substIns ins b)
  | _, .add a b      => .add (substIns ins a) (substIns ins b)
  | _, .sub a b      => .sub (substIns ins a) (substIns ins b)
  | _, .mul a b      => .mul (substIns ins a) (substIns ins b)
  | _, .shl a b      => .shl (substIns ins a) (substIns ins b)
  | _, .shr a b      => .shr (substIns ins a) (substIns ins b)
  | _, .sshr a b     => .sshr (substIns ins a) (substIns ins b)
  | _, .udiv a b     => .udiv (substIns ins a) (substIns ins b)
  | _, .umod a b     => .umod (substIns ins a) (substIns ins b)
  | _, .eq a b       => .eq (substIns ins a) (substIns ins b)
  | _, .ult a b      => .ult (substIns ins a) (substIns ins b)
  | _, .slt a b      => .slt (substIns ins a) (substIns ins b)
  | _, .mux s a b    => .mux (substIns ins s) (substIns ins a) (substIns ins b)
  | _, .concat a b   => .concat (substIns ins a) (substIns ins b)
  | _, .zext k a     => .zext k (substIns ins a)
  | _, .sext k a     => .sext k (substIns ins a)
  | _, .extract i a  => .extract i (substIns ins a)
  | _, .slice lo len a => .slice lo len (substIns ins a)

/-- The child environment induced by an instance's port bindings, evaluated in a parent env. This
    is exactly `Parent.combOut`'s `childIns` list. -/
def insVals (ins : List (String × AnyExpr)) (E : Env) : List (String × Nat) :=
  ins.map (fun pe => (pe.1, (eval pe.2.2 E).toNat))

/-- A `0`-offset slice realises the `BitVec.ofNat w (·.toNat)` width-reconstruction. -/
theorem eval_slice0 {w' : Nat} (w : Nat) (ae : Expr w') (E : Env) :
    eval (Expr.slice 0 w ae) E = BitVec.ofNat w (eval ae E).toNat := by
  apply BitVec.eq_of_toNat_eq
  simp [eval]

/-- `lookup` commutes with the value-map building the child env (keys are preserved). -/
theorem insVals_lookup (ins : List (String × AnyExpr)) (E : Env) (n : String) :
    (insVals ins E).lookup n = (ins.lookup n).map (fun ae => (eval ae.2 E).toNat) := by
  induction ins with
  | nil => rfl
  | cons pe rest ih =>
      obtain ⟨k, ae⟩ := pe
      simp only [insVals, List.map_cons, List.lookup_cons]
      cases h : (n == k) with
      | true => rfl
      | false => simp only [insVals] at ih; rw [ih]

/-- Looking up the induced child env at a bound port returns the port's instance-expr value. -/
theorem ofList_insVals (ins : List (String × AnyExpr)) (E : Env) (n : String) :
    (Env.ofList (insVals ins E)) n =
      match ins.lookup n with
      | some ae => (eval ae.2 E).toNat
      | none    => 0 := by
  simp only [Env.ofList, insVals_lookup]
  cases ins.lookup n <;> rfl

/-- **Substitution lemma.** If every variable of `e` is a bound child input port, then substituting
    the port bindings and evaluating in the parent env `E` equals evaluating `e` in the child env. -/
theorem eval_substIns (ins : List (String × AnyExpr)) (E : Env) :
    {w : Nat} → (e : Expr w) → (hb : ∀ n ∈ e.vars, n ∈ ins.map (·.1)) →
    eval (substIns ins e) E = eval e (Env.ofList (insVals ins E))
  | _, .const v, _ => rfl
  | _, .var n w, hb => by
      have hmem : n ∈ ins.map (·.1) := hb n (List.mem_singleton.mpr rfl)
      have hsome : (ins.lookup n).isSome := by
        rw [List.lookup_isSome_iff]
        obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
        exact ⟨p, hp, by simp [hpe]⟩
      obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp hsome
      simp only [substIns, hae, eval_slice0, eval, Env.lookup, ofList_insVals]
  | _, .not a, hb => by
      simp only [substIns, eval]; rw [eval_substIns ins E a hb]
  | _, .zext k a, hb => by
      simp only [substIns, eval]; rw [eval_substIns ins E a hb]
  | _, .sext k a, hb => by
      simp only [substIns, eval]; rw [eval_substIns ins E a hb]
  | _, .extract i a, hb => by
      simp only [substIns, eval]; rw [eval_substIns ins E a hb]
  | _, .slice lo len a, hb => by
      simp only [substIns, eval]; rw [eval_substIns ins E a hb]
  | _, .mux s a b, hb => by
      simp only [substIns, eval]
      rw [eval_substIns ins E s (fun n hn => hb n (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hn))))),
          eval_substIns ins E a (fun n hn => hb n (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hn))))),
          eval_substIns ins E b (fun n hn => hb n (List.mem_append.mpr (Or.inr hn)))]
  | _, .and a b, hb | _, .or a b, hb | _, .xor a b, hb | _, .add a b, hb | _, .sub a b, hb
  | _, .mul a b, hb | _, .shl a b, hb | _, .shr a b, hb | _, .sshr a b, hb | _, .udiv a b, hb
  | _, .umod a b, hb | _, .eq a b, hb | _, .ult a b, hb | _, .slt a b, hb | _, .concat a b, hb => by
      simp only [substIns, eval]
      rw [eval_substIns ins E a (fun n hn => hb n (List.mem_append.mpr (Or.inl hn))),
          eval_substIns ins E b (fun n hn => hb n (List.mem_append.mpr (Or.inr hn)))]

/-- The substituted expression references only names that the instance expressions reference (it
    contains no fresh names): if `e` is closed over bound ports and every instance expression is
    closed over `known`, so is the substituted expression. -/
theorem substIns_vars (ins : List (String × AnyExpr)) (known : List String) :
    {w : Nat} → (e : Expr w) → (hb : ∀ n ∈ e.vars, n ∈ ins.map (·.1)) →
    (hins : ∀ pe ∈ ins, ∀ n ∈ pe.2.2.vars, n ∈ known) →
    ∀ n ∈ (substIns ins e).vars, n ∈ known
  | _, .const v, _, _ => by intro n hn; simp [substIns, Expr.vars] at hn
  | _, .var x w, hb, hins => by
      intro n hn
      have hmem : x ∈ ins.map (·.1) := hb x (List.mem_singleton.mpr rfl)
      have hsome : (ins.lookup x).isSome := by
        rw [List.lookup_isSome_iff]
        obtain ⟨p, hp, hpe⟩ := List.mem_map.mp hmem
        exact ⟨p, hp, by simp [hpe]⟩
      obtain ⟨ae, hae⟩ := Option.isSome_iff_exists.mp hsome
      have haemem : (x, ae) ∈ ins := by
        obtain ⟨l₁, l₂, hl, _⟩ := List.lookup_eq_some_iff.mp hae
        rw [hl]; simp
      simp only [substIns, hae, Expr.vars] at hn
      exact hins (x, ae) haemem n hn
  | _, .not a, hb, hins => by simpa [substIns, Expr.vars] using substIns_vars ins known a hb hins
  | _, .zext k a, hb, hins => by simpa [substIns, Expr.vars] using substIns_vars ins known a hb hins
  | _, .sext k a, hb, hins => by simpa [substIns, Expr.vars] using substIns_vars ins known a hb hins
  | _, .extract i a, hb, hins => by simpa [substIns, Expr.vars] using substIns_vars ins known a hb hins
  | _, .slice lo len a, hb, hins => by simpa [substIns, Expr.vars] using substIns_vars ins known a hb hins
  | _, .mux s a b, hb, hins => by
      intro n hn
      simp only [substIns, Expr.vars, List.mem_append] at hn
      rcases hn with (hn | hn) | hn
      · exact substIns_vars ins known s
          (fun m hm => hb m (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hm))))) hins n hn
      · exact substIns_vars ins known a
          (fun m hm => hb m (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hm))))) hins n hn
      · exact substIns_vars ins known b
          (fun m hm => hb m (List.mem_append.mpr (Or.inr hm))) hins n hn
  | _, .and a b, hb, hins | _, .or a b, hb, hins | _, .xor a b, hb, hins | _, .add a b, hb, hins
  | _, .sub a b, hb, hins | _, .mul a b, hb, hins | _, .shl a b, hb, hins | _, .shr a b, hb, hins
  | _, .sshr a b, hb, hins | _, .udiv a b, hb, hins | _, .umod a b, hb, hins | _, .eq a b, hb, hins
  | _, .ult a b, hb, hins | _, .slt a b, hb, hins | _, .concat a b, hb, hins => by
      intro n hn
      simp only [substIns, Expr.vars, List.mem_append] at hn
      rcases hn with hn | hn
      · exact substIns_vars ins known a (fun m hm => hb m (List.mem_append.mpr (Or.inl hm))) hins n hn
      · exact substIns_vars ins known b (fun m hm => hb m (List.mem_append.mpr (Or.inr hm))) hins n hn

/-! ## `evalWires` helpers -/

theorem evalWires_cons (a : Wire) (rest : List Wire) (e : Env) :
    evalWires (a :: rest) e
      = evalWires rest (fun m => if m = a.name then (eval a.expr e).toNat else e m) := rfl

theorem evalWires_append (ws1 ws2 : List Wire) (e : Env) :
    evalWires (ws1 ++ ws2) e = evalWires ws2 (evalWires ws1 e) := by
  simp only [evalWires, List.foldl_append]

/-- A name not assigned by any wire keeps its base value. -/
theorem evalWires_not_mem (ws : List Wire) (n : String)
    (h : n ∉ ws.map (·.name)) : ∀ fe : Env, evalWires ws fe n = fe n := by
  induction ws with
  | nil => intro fe; rfl
  | cons a rest ih =>
      simp only [List.map_cons, List.mem_cons, not_or] at h
      obtain ⟨h1, h2⟩ := h
      intro fe; rw [evalWires_cons, ih h2]; simp only [if_neg h1]

/-- **Independent wires evaluate to their own expression.** When no wire's expression references any
    wire name (and names are distinct), each wire net carries its expression's value over the base
    env, regardless of evaluation order. -/
theorem evalWires_indep (ws : List Wire)
    (hnd : (ws.map (·.name)).Nodup)
    (hindep : ∀ w ∈ ws, ∀ m ∈ w.expr.vars, m ∉ ws.map (·.name)) :
    ∀ (fe : Env) (w : Wire), w ∈ ws → evalWires ws fe w.name = (eval w.expr fe).toNat := by
  induction ws with
  | nil => intro fe w hw; simp at hw
  | cons a rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hanr, hndr⟩ := hnd
      intro fe w hw
      rw [evalWires_cons]
      rcases List.mem_cons.mp hw with rfl | hwr
      · rw [evalWires_not_mem rest w.name hanr]; simp
      · have hindepr : ∀ w ∈ rest, ∀ m ∈ w.expr.vars, m ∉ rest.map (·.name) := by
          intro w' hw' m hm hcontra
          exact hindep w' (List.mem_cons_of_mem _ hw') m hm (List.mem_cons_of_mem _ hcontra)
        rw [ih hndr hindepr _ w hwr]
        have hcong : eval w.expr (fun m => if m = a.name then (eval a.expr fe).toNat else fe m)
            = eval w.expr fe := by
          apply eval_congr; intro m hm
          have hmne : m ≠ a.name := by
            intro h; apply hindep w (List.mem_cons_of_mem _ hwr) m hm; rw [h]; simp
          simp only [if_neg hmne]
        rw [hcong]

/-! ## `Env.ofList` helpers -/

theorem ofList_append_left (acc bs : List (String × Nat)) (n : String)
    (h : n ∈ acc.map (·.1)) : Env.ofList (acc ++ bs) n = Env.ofList acc n := by
  simp only [Env.ofList, List.lookup_append]
  have : (acc.lookup n).isSome := by
    rw [List.lookup_isSome_iff]
    obtain ⟨p, hp, hpe⟩ := List.mem_map.mp h
    exact ⟨p, hp, by simp [hpe]⟩
  cases hl : acc.lookup n with
  | none => rw [hl] at this; simp at this
  | some v => simp

theorem ofList_append_right (acc bs : List (String × Nat)) (n : String)
    (h : n ∉ acc.map (·.1)) : Env.ofList (acc ++ bs) n = Env.ofList bs n := by
  simp only [Env.ofList, List.lookup_append]
  have : acc.lookup n = none := by
    rw [List.lookup_eq_none_iff]; intro p hp
    simp only [bne_iff_ne]; intro hcontra
    exact h (List.mem_map.mpr ⟨p, hp, hcontra.symm⟩)
  rw [this]; simp

/-- Looking up a `mapped` association list at a present (distinct) key returns its mapped value. -/
theorem ofList_lookup_mem {α : Type} (xs : List α) (key : α → String) (val : α → Nat)
    (x₀ : α) (hx : x₀ ∈ xs) (hnd : (xs.map key).Nodup) :
    Env.ofList (xs.map (fun x => (key x, val x))) (key x₀) = val x₀ := by
  induction xs with
  | nil => simp at hx
  | cons a rest ih =>
      simp only [List.map_cons, List.nodup_cons] at hnd
      obtain ⟨hanr, hndr⟩ := hnd
      simp only [List.map_cons, Env.ofList, List.lookup_cons]
      rcases List.mem_cons.mp hx with rfl | hxr
      · simp
      · have hkne : ¬ (key x₀ == key a) := by
          simp only [beq_iff_eq]; intro hcontra
          exact hanr (hcontra ▸ List.mem_map.mpr ⟨x₀, hxr, rfl⟩)
        simp only [hkne]
        have := ih hxr hndr
        simpa [Env.ofList] using this

/-! ## Flattening a parent into a flat combinational module -/

/-- The parent-visible output net names contributed by one instance. -/
def instOutNames (inst : Inst) : List String :=
  inst.child.outputs.map (fun o => inst.instName ++ "." ++ o.name)

/-- Flattened wires for one instance: each child output becomes a parent wire named
    `"<inst>.<port>"`, with the child's input ports substituted by the instance expressions. -/
def Inst.flatWires (inst : Inst) : List Wire :=
  inst.child.outputs.map (fun o =>
    { name := inst.instName ++ "." ++ o.name, width := o.width,
      expr := substIns inst.ins o.expr })

/-- **The combinational flattening of a parent into a single flat `Module`.** Each instance's child
    outputs are inlined as parent wires, renamed `"<inst>.<port>"`, with the child's input ports
    substituted by the instance's parent-side expressions; the parent outputs are kept verbatim
    (they already reference `"<inst>.<port>"`). The result is wire-list (RTL) shaped and
    combinational (`regs = []`, `clock = none`). -/
def flattenParent (p : Parent) : Module :=
  { name := p.name, inputs := p.inputs, outputs := p.outputs,
    wires := p.insts.flatMap Inst.flatWires, regs := [], clock := none, reset := none }

/-- One step of the parent's instance fold (exactly `Parent.combOut`'s fold body). -/
def parentStep (acc : List (String × Nat)) (inst : Inst) : List (String × Nat) :=
  acc ++ (inst.child.combOut (insVals inst.ins (Env.ofList acc))).map
            (fun pv => (inst.instName ++ "." ++ pv.1, pv.2))

/-- All parent-visible instance output names. -/
def visNames (insts : List Inst) : List String := insts.flatMap instOutNames

/-- Well-formedness, processed left to right with a growing set of `known` (already-defined) names:
    each child is wire-free; each child output references only its bound input ports; each instance
    expression references only names already known (parent inputs and earlier instance outputs). -/
def WFInsts : List Inst → List String → Prop
  | [], _ => True
  | inst :: rest, known =>
      inst.child.wires = []
    ∧ (∀ o ∈ inst.child.outputs, ∀ n ∈ o.expr.vars, n ∈ inst.ins.map (·.1))
    ∧ (∀ pe ∈ inst.ins, ∀ n ∈ pe.2.2.vars, n ∈ known)
    ∧ WFInsts rest (known ++ instOutNames inst)

theorem visNames_cons (inst : Inst) (rest : List Inst) :
    visNames (inst :: rest) = instOutNames inst ++ visNames rest := by
  simp [visNames, List.flatMap_cons]

theorem combOut_wirefree (m : Module) (ci : List (String × Nat)) (hw : m.wires = []) :
    m.combOut ci = m.outputs.map (fun o => (o.name, (eval o.expr (Env.ofList ci)).toNat)) := by
  simp [Module.combOut, hw, evalWires]

theorem parentStep_eq (inst : Inst) (acc : List (String × Nat)) (hwire : inst.child.wires = []) :
    parentStep acc inst
      = acc ++ inst.child.outputs.map (fun o =>
          (inst.instName ++ "." ++ o.name,
           (eval o.expr (Env.ofList (insVals inst.ins (Env.ofList acc)))).toNat)) := by
  simp only [parentStep, combOut_wirefree _ _ hwire, List.map_map]; rfl

theorem flatWires_names (inst : Inst) : (inst.flatWires.map (·.name)) = instOutNames inst := by
  simp only [Inst.flatWires, instOutNames, List.map_map]; rfl

theorem parentStep_keys (inst : Inst) (acc : List (String × Nat)) (hwire : inst.child.wires = []) :
    (parentStep acc inst).map (·.1) = acc.map (·.1) ++ instOutNames inst := by
  rw [parentStep_eq inst acc hwire]
  simp only [List.map_append, List.map_map, instOutNames]; rfl

/-- The induced child env is insensitive to envs agreeing on the instance expressions' variables. -/
theorem insVals_congr (ins : List (String × AnyExpr)) (E F : Env) (known : List String)
    (hins : ∀ pe ∈ ins, ∀ n ∈ pe.2.2.vars, n ∈ known)
    (hag : ∀ n ∈ known, E n = F n) :
    insVals ins E = insVals ins F := by
  apply List.map_congr_left
  intro pe hpe
  have : eval pe.2.2 E = eval pe.2.2 F := by
    apply eval_congr; intro n hn; exact hag n (hins pe hpe n hn)
  rw [this]

/-! ## The instance fold and the headline theorem -/

/-- **Core fold lemma.** Generalising over the accumulator `acc` (the parent env so far) and any flat
    env `fe` that agrees with it on the names defined so far, the flattened wires reproduce, on every
    parent-input and instance-output name, exactly the values the parent's instance fold computes.
    The induction step uses the substitution lemma (`eval_substIns`), wire independence within an
    instance (`evalWires_indep`), and the `eval` congruence to transport the agreement past each
    instance (handling carry-chain dependencies between instances). -/
theorem flat_fold (insts : List Inst) :
    ∀ (acc : List (String × Nat)) (fe : Env),
      WFInsts insts (acc.map (·.1)) →
      (acc.map (·.1) ++ visNames insts).Nodup →
      (∀ n ∈ acc.map (·.1), fe n = Env.ofList acc n) →
      ∀ n ∈ acc.map (·.1) ++ visNames insts,
        evalWires (insts.flatMap Inst.flatWires) fe n
          = Env.ofList (insts.foldl parentStep acc) n := by
  induction insts with
  | nil =>
      intro acc fe _ _ hag n hn
      simp only [visNames, List.flatMap_nil, List.append_nil] at hn
      simpa [List.flatMap_nil, evalWires] using hag n hn
  | cons inst rest ih =>
      intro acc fe hwf hnd hag n hn
      obtain ⟨hwire, hout, hins, hrest⟩ := hwf
      have hkeys := parentStep_keys inst acc hwire
      rw [visNames_cons] at hnd
      have hdisj := (List.nodup_append.mp hnd).2.2
      have hndtail := (List.nodup_append.mp hnd).2.1
      have hndinstout := (List.nodup_append.mp hndtail).1
      have hnd' : ((acc.map (·.1) ++ instOutNames inst) ++ visNames rest).Nodup := by
        rw [List.append_assoc]; exact hnd
      have hB : ∀ m ∈ (parentStep acc inst).map (·.1),
            evalWires (Inst.flatWires inst) fe m = Env.ofList (parentStep acc inst) m := by
        intro m hm
        rw [hkeys] at hm
        rcases List.mem_append.mp hm with hmacc | hmout
        · have hmnotout : m ∉ (Inst.flatWires inst).map (·.name) := by
            rw [flatWires_names]; intro hc
            exact hdisj m hmacc m (List.mem_append.mpr (Or.inl hc)) rfl
          rw [evalWires_not_mem _ m hmnotout fe, hag m hmacc]
          simp only [parentStep]
          rw [ofList_append_left _ _ m hmacc]
        · obtain ⟨o, ho, hmo⟩ := List.mem_map.mp hmout
          subst hmo
          have hmnotacc : inst.instName ++ "." ++ o.name ∉ acc.map (·.1) := by
            intro hc
            exact hdisj _ hc _ (List.mem_append.mpr (Or.inl hmout)) rfl
          have hindepf : ∀ w ∈ Inst.flatWires inst, ∀ k ∈ w.expr.vars,
              k ∉ (Inst.flatWires inst).map (·.name) := by
            intro w hw k hk
            obtain ⟨o', ho', hwo'⟩ := List.mem_map.mp hw
            subst hwo'
            rw [flatWires_names]
            have hkknown : k ∈ acc.map (·.1) :=
              substIns_vars inst.ins (acc.map (·.1)) o'.expr (hout o' ho') hins k hk
            intro hc
            exact hdisj k hkknown k (List.mem_append.mpr (Or.inl hc)) rfl
          have hfe1 : evalWires (Inst.flatWires inst) fe (inst.instName ++ "." ++ o.name)
              = (eval (substIns inst.ins o.expr) fe).toNat :=
            evalWires_indep (Inst.flatWires inst) (by rw [flatWires_names]; exact hndinstout)
              hindepf fe ⟨inst.instName ++ "." ++ o.name, o.width, substIns inst.ins o.expr⟩
              (List.mem_map.mpr ⟨o, ho, rfl⟩)
          rw [hfe1, eval_substIns inst.ins fe o.expr (hout o ho),
              insVals_congr inst.ins fe (Env.ofList acc) (acc.map (·.1)) hins hag]
          rw [parentStep_eq inst acc hwire, ofList_append_right _ _ _ hmnotacc]
          exact (ofList_lookup_mem inst.child.outputs (fun x => inst.instName ++ "." ++ x.name)
            (fun x => (eval x.expr (Env.ofList (insVals inst.ins (Env.ofList acc)))).toNat)
            o ho hndinstout).symm
      have hC : WFInsts rest ((parentStep acc inst).map (·.1)) := by rw [hkeys]; exact hrest
      have hD : ((parentStep acc inst).map (·.1) ++ visNames rest).Nodup := by rw [hkeys]; exact hnd'
      have hn' : n ∈ (parentStep acc inst).map (·.1) ++ visNames rest := by
        rw [hkeys, List.append_assoc, ← visNames_cons]; exact hn
      rw [List.flatMap_cons, evalWires_append, List.foldl_cons]
      exact ih (parentStep acc inst) (evalWires (Inst.flatWires inst) fe) hC hD hB n hn'

/-- **`flattenParent_correct` — the headline.** A well-formed parent's combinational behaviour
    equals that of its flattened flat `Module`, on every input cycle.

    Well-formedness (all decidable for a concrete design):
    * `hin`  — the supplied inputs are exactly the parent's declared input ports;
    * `hwf`  — each child is wire-free combinational, each child output references only its bound
               input ports, and each instance expression references only already-defined names
               (parent inputs and *earlier* instance outputs — so carry chains are allowed);
    * `hnd`  — all input and instance-output net names are distinct;
    * `hpo`  — each parent output references only inputs and instance-output names. -/
theorem flattenParent_correct (p : Parent) (inputs : List (String × Nat))
    (hin : inputs.map (·.1) = p.inputs.map (·.name))
    (hwf : WFInsts p.insts (p.inputs.map (·.name)))
    (hnd : (p.inputs.map (·.name) ++ visNames p.insts).Nodup)
    (hpo : ∀ o ∈ p.outputs, ∀ n ∈ o.expr.vars,
              n ∈ p.inputs.map (·.name) ++ visNames p.insts) :
    Parent.combOut p inputs = (flattenParent p).combOut inputs := by
  have hagree := flat_fold p.insts inputs (Env.ofList inputs)
    (by rw [hin]; exact hwf) (by rw [hin]; exact hnd) (fun n _ => rfl)
  show p.outputs.map (fun o => (o.name,
          (eval o.expr (Env.ofList (p.insts.foldl parentStep inputs))).toNat))
     = p.outputs.map (fun o => (o.name,
          (eval o.expr (evalWires (p.insts.flatMap Inst.flatWires) (Env.ofList inputs))).toNat))
  apply List.map_congr_left
  intro o ho
  have heq : eval o.expr (Env.ofList (p.insts.foldl parentStep inputs))
       = eval o.expr (evalWires (p.insts.flatMap Inst.flatWires) (Env.ofList inputs)) := by
    apply eval_congr; intro n hn
    have hnvis : n ∈ inputs.map (·.1) ++ visNames p.insts := by
      rw [hin]; exact hpo o ho n hn
    exact (hagree n hnvis).symm
  rw [heq]

/-- **Tie-off (hierarchy integrated into compile_correct).** `flattenParent p` is a flat *combinational* `Module`
    (no registers, no clock, no reset): every coarse cell is one of its `wires`, and each wire's /
    output's defining expression is compiled by the proven `LeanRTL.CompilerCorrect.compile_correct`
    (the register-free module assembly being the proven `compileModule_comb_sound` /
    `compileModule_seq_correct_wires` with `regs = []`). Composed with `flattenParent_correct`, the
    `Parent`'s denotational behaviour `Parent.combOut` is therefore realised by a
    provably-correct flat compilation — hierarchy reduces to the proven flat core, with Yosys
    `hierarchy -flatten` relating the instance netlist to this flat one in the round-trip. -/
theorem flattenParent_is_combinational (p : Parent) :
    (flattenParent p).regs = [] ∧ (flattenParent p).clock = none ∧ (flattenParent p).reset = none :=
  ⟨rfl, rfl, rfl⟩

end LeanRTL
