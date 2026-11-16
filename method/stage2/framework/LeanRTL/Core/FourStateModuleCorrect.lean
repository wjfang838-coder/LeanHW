import LeanRTL.Core.FourStateEnvironmentCorrect

namespace LeanRTL.FourState.Encoding

def encodedWire (wire : FourState.Wire) : List LeanRTL.Wire :=
  let r := compile wire.expr
  [{ name := "t__" ++ wire.name, width := wire.width, expr := r.tag },
   { name := "d__" ++ wire.name, width := wire.width, expr := r.data }]

def valueWireStep (env : FourState.Env) (wire : FourState.Wire) : FourState.Env :=
  putValue env wire.name (FourState.eval wire.expr env)

def wireScope (scope : List (String × Nat)) (wires : List FourState.Wire) : List (String × Nat) :=
  wires.foldl (fun scope wire => (wire.name, wire.width)::scope) scope

/-- Topological, fresh wire declarations with well-formed expressions. -/
def wiresValid (scope : List (String × Nat)) : List FourState.Wire → Bool
  | [] => true
  | wire::rest => (scope.lookup wire.name == none) && wire.expr.valid scope &&
    wiresValid ((wire.name,wire.width)::scope) rest

theorem encoded_wire_correct (wire : FourState.Wire) (scope : List (String × Nat))
    (enc : LeanRTL.Env) (original : FourState.Env)
    (hf : scope.lookup wire.name = none) (hv : wire.expr.valid scope = true)
    (he : ScopeAgree scope (decodedEnv enc) original) :
    ScopeAgree ((wire.name,wire.width)::scope)
      (decodedEnv (LeanRTL.evalWires (encodedWire wire) enc)) (valueWireStep original wire) := by
  have hd := compile_data_fresh wire.expr scope enc wire.name
    (LeanRTL.eval (compile wire.expr).tag enc).toNat hv hf
  change ScopeAgree _ (decodedEnv (putNat
    (putNat enc ("t__" ++ wire.name) (LeanRTL.eval (compile wire.expr).tag enc).toNat)
    ("d__" ++ wire.name) (LeanRTL.eval (compile wire.expr).data
      (putNat enc ("t__" ++ wire.name) (LeanRTL.eval (compile wire.expr).tag enc).toNat)).toNat)) _
  rw [hd]
  exact put_rails_agree scope enc original wire.name (compile wire.expr) _ he
    (compile_correct_related wire.expr scope enc original hv he)

theorem encoded_wires_correct (wires : List FourState.Wire) (scope : List (String × Nat))
    (enc : LeanRTL.Env) (original : FourState.Env)
    (hv : wiresValid scope wires = true) (he : ScopeAgree scope (decodedEnv enc) original) :
    ScopeAgree (wireScope scope wires)
      (decodedEnv (LeanRTL.evalWires (wires.flatMap encodedWire) enc))
      (wires.foldl valueWireStep original) := by
  induction wires generalizing scope enc original with
  | nil => exact he
  | cons wire rest ih =>
    simp only [wiresValid, Bool.and_eq_true, beq_iff_eq] at hv
    have hstep := encoded_wire_correct wire scope enc original hv.1.1 hv.1.2 he
    have hrest := ih ((wire.name,wire.width)::scope)
      (LeanRTL.evalWires (encodedWire wire) enc) (valueWireStep original wire) hv.2 hstep
    simpa only [wireScope, List.foldl_cons, List.flatMap_cons, LeanRTL.evalWires,
      List.foldl_append] using hrest


theorem value_bits_getD {w : Nat} (value : Value w) (i : Nat) :
    ((List.finRange w).map (fun j => value j)).getD i .x = getBit value i := by
  by_cases hi : i < w <;> simp [List.getD, getBit, hi]

theorem valuesEnv_cons {w : Nat} (values : List (String × List Bit)) (input : FourState.Env)
    (name : String) (value : Value w) :
    valuesEnv ((name, (List.finRange w).map (fun i => value i))::values) input =
      putValue (valuesEnv values input) name value := by
  funext n i
  by_cases hn : n = name
  · subst n
    simpa only [valuesEnv, putValue, List.lookup_cons_self, ↓reduceIte] using value_bits_getD value i
  · have hb : (n == name) = false := beq_eq_false_iff_ne.mpr hn
    simp [valuesEnv, putValue, hn, List.lookup_cons, hb]

theorem wireValues_correct (m : FourState.Module) (input : FourState.Env) :
    valuesEnv (m.wireValues input) input = m.wires.foldl valueWireStep input := by
  have h := List.foldl_hom (fun values => valuesEnv values input)
    (g₁ := fun (values : List (String × List Bit)) (wire : FourState.Wire) =>
      (wire.name, (List.finRange wire.width).map
        (FourState.eval wire.expr (valuesEnv values input)))::values)
    (g₂ := valueWireStep) (l := m.wires) (init := [])
    (fun values wire => (valuesEnv_cons values input wire.name
      (FourState.eval wire.expr (valuesEnv values input))).symm)
  exact h.symm

/-- Structural precondition checked on the actual imported module. -/
def encodingValid (m : FourState.Module) : Bool :=
  let scope := m.inputs.map (fun p => (p.name,p.width))
  wiresValid scope m.wires &&
    m.outputs.all (fun p => p.expr.valid (wireScope scope m.wires))

theorem module_values_correct (m : FourState.Module) (enc : LeanRTL.Env) (original : FourState.Env)
    (hv : encodingValid m = true)
    (he : ScopeAgree (m.inputs.map (fun p => (p.name,p.width))) (decodedEnv enc) original) :
    m.outputs.map (fun p => (p.name, renderValue (den (compile p.expr)
      (LeanRTL.evalWires (module m).wires enc)))) = m.eval original := by
  simp only [encodingValid, Bool.and_eq_true] at hv
  have hw := encoded_wires_correct m.wires _ enc original hv.1 he
  dsimp only [FourState.Module.eval]
  rw [wireValues_correct]
  apply List.map_congr_left
  intro output hout
  congr 1
  apply congrArg renderValue
  exact compile_correct_related output.expr _ _ _ (List.all_eq_true.mp hv.2 output hout) hw


/-- Decode exactly paired, correctly named encoded output ports. A missing,
extra, reordered, or misnamed port is rejected rather than silently ignored. -/
def decodeOutputPairs : List FourState.Wire → List (String × Nat) → Option (List (String × String))
  | [], [] => some []
  | p::ps, (tn,t)::(dn,d)::rest =>
    if tn == "t__" ++ p.name && dn == "d__" ++ p.name then
      ((p.name, renderValue (decodeVectors (BitVec.ofNat p.width t) (BitVec.ofNat p.width d))) :: ·) <$>
        decodeOutputPairs ps rest
    else none
  | _, _ => none

def encodedOutput (p : FourState.Wire) : List LeanRTL.OutPort :=
  let r := compile p.expr
  [{name := "t__" ++ p.name, width := p.width, expr := r.tag},
   {name := "d__" ++ p.name, width := p.width, expr := r.data}]

theorem decode_encoded_outputs (outputs : List FourState.Wire) (env : LeanRTL.Env) :
    decodeOutputPairs outputs ((outputs.flatMap encodedOutput).map
      (fun p => (p.name, (LeanRTL.eval p.expr env).toNat))) =
    some (outputs.map (fun p => (p.name, renderValue (den (compile p.expr) env)))) := by
  induction outputs with
  | nil => rfl
  | cons p ps ih =>
    simpa [encodedOutput, decodeOutputPairs, den, decodeVectors] using
      congrArg (Option.map ((p.name, renderValue (den (compile p.expr) env)) :: ·)) ih

/-- Exact output-list correspondence for the actual emitted two-plane module,
including ordered internal-wire evaluation and the four-state memo evaluator. -/
theorem module_correct (m : FourState.Module) (enc : LeanRTL.Env) (original : FourState.Env)
    (hv : encodingValid m = true)
    (he : ScopeAgree (m.inputs.map (fun p => (p.name,p.width))) (decodedEnv enc) original) :
    decodeOutputPairs m.outputs ((module m).outputs?eval (fun _ => 0) enc) = some (m.eval original) := by
  have ho := decode_encoded_outputs m.outputs (LeanRTL.evalWires (module m).wires enc)
  have hv := module_values_correct m enc original hv he
  rw [hv] at ho
  simpa only [LeanRTL.Module.outputs?eval, module, LeanRTL.cycleEnv, List.map_nil,
    List.contains_nil, Bool.false_eq_true, ↓reduceIte, encodedOutput] using ho

/-- No input restrictions: every binary assignment is a legal four-state code. -/
theorem module_correct_decoded (m : FourState.Module) (hv : encodingValid m = true)
    (enc : LeanRTL.Env) :
    decodeOutputPairs m.outputs ((module m).outputs?eval (fun _ => 0) enc) =
      some (m.eval (decodedEnv enc)) :=
  module_correct m enc (decodedEnv enc) hv (by intros _ _ _ _; rfl)

end LeanRTL.FourState.Encoding
