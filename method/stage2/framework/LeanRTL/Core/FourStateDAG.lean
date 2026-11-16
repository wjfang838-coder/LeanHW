import LeanRTL.Core.FourStateSubstitution

namespace LeanRTL.FourState.DAG
open Encoding Source

structure Block where
  source : FourState.Wire
  locals : List FourState.Wire
  result : FourState.Expr source.width

def Block.fragment (b : Block) (scope : List (String × Nat)) : FourState.Module :=
  { name := "fragment", inputs := scope.map (fun (n,w) => {name := n,width := w}),
    wires := b.locals, outputs := [{name := b.source.name,width := b.source.width,expr := b.result}] }

def Block.valid (b : Block) (scope : List (String × Nat)) : Bool :=
  b.source.expr.valid scope && b.locals.all (fun w => scope.lookup w.name == none) &&
    moduleTyped (b.fragment scope)

structure CheckedBlock where
  block : Block
  inlined : inlineWires block.locals block.result = block.source.expr

def Block.lower (b : Block) : List FourState.Wire :=
  b.locals ++ [{b.source with expr := b.result}]

theorem fresh_wires_preserve (wires : List FourState.Wire) (scope : List (String × Nat))
    (fresh : ∀ w ∈ wires, scope.lookup w.name = none) (env : FourState.Env) :
    ScopeAgree scope (wires.foldl valueWireStep env) env := by
  induction wires generalizing env with
  | nil => intro n w _ i; rfl
  | cons w rest ih =>
    intro n k hn i
    have hne : n ≠ w.name := by intro h; subst n; simp [fresh w (by simp)] at hn
    have hr := ih (fun v h => fresh v (by simp [h])) (valueWireStep env w) n k hn i
    simpa [valueWireStep, putValue, hne] using hr

theorem block_value_correct (b : CheckedBlock) (scope : List (String × Nat))
    (hv : b.block.valid scope = true) (env : FourState.Env) :
    eval b.block.result (b.block.locals.foldl valueWireStep env) = eval b.block.source.expr env := by
  have hv' := hv
  simp only [Block.valid, Bool.and_eq_true] at hv'
  have ht : moduleTyped (b.block.fragment scope) = true := hv'.2
  simp only [moduleTyped, Bool.and_eq_true] at ht
  have hw : ∀ w ∈ b.block.locals, bindingValid (allScope (b.block.fragment scope)) w := by
    intro w h
    have hh := List.all_eq_true.mp ht.1 w h
    simpa [bindingValid] using hh
  have he : b.block.result.valid (allScope (b.block.fragment scope)) = true := by
    simpa [Block.fragment] using ht.2
  rw [← inlineWires_correct b.block.locals _ hw b.block.result he env, b.inlined]

theorem block_scope_correct (b : CheckedBlock) (scope : List (String × Nat))
    (hv : b.block.valid scope = true) (a z : FourState.Env) (ha : ScopeAgree scope a z) :
    ScopeAgree ((b.block.source.name,b.block.source.width)::scope)
      (b.block.lower.foldl valueWireStep a) (valueWireStep z b.block.source) := by
  have hv' := hv
  simp only [Block.valid, Bool.and_eq_true] at hv'
  have hs : b.block.source.expr.valid scope = true := hv'.1.1
  have hf : ∀ w ∈ b.block.locals, scope.lookup w.name = none := by
    have h := hv'.1.2
    intro w hw
    simpa using List.all_eq_true.mp h w hw
  have hh := block_value_correct b scope hv a
  have he := eval_scope_congr b.block.source.expr scope a z ha hs
  intro n k hn i
  simp only [Block.lower, List.foldl_append, List.foldl_cons, List.foldl_nil, valueWireStep]
  by_cases hname : n = b.block.source.name
  · subst n
    simp only [List.lookup_cons_self, Option.some.injEq] at hn
    subst k
    simp only [putValue, ↓reduceIte, hh, he]
  · have hbeq : (n == b.block.source.name) = false := beq_eq_false_iff_ne.mpr hname
    have hlookup : scope.lookup n = some k := by simpa [List.lookup_cons,hbeq] using hn
    simp only [putValue, hname, ↓reduceIte]
    exact (fresh_wires_preserve b.block.locals scope hf a n k hlookup i).trans (ha n k hlookup i)

def blocksValid (scope : List (String × Nat)) : List CheckedBlock → Bool
  | [] => true
  | b::rest => b.block.valid scope && blocksValid ((b.block.source.name,b.block.source.width)::scope) rest

theorem blocks_scope_correct (blocks : List CheckedBlock) (scope : List (String × Nat))
    (hv : blocksValid scope blocks = true) (a z : FourState.Env) (ha : ScopeAgree scope a z) :
    ScopeAgree (wireScope scope (blocks.map (·.block.source)))
      ((blocks.flatMap (·.block.lower)).foldl valueWireStep a)
      ((blocks.map (·.block.source)).foldl valueWireStep z) := by
  induction blocks generalizing scope a z with
  | nil => exact ha
  | cons b rest ih =>
    have h := hv
    simp only [blocksValid, Bool.and_eq_true] at h
    simpa only [List.flatMap_cons,List.map_cons,List.foldl_append,List.foldl_cons,wireScope]
      using ih _ h.2 _ _ (block_scope_correct b scope h.1 a z ha)

def expanded (m : FourState.Module) (blocks : List CheckedBlock) : FourState.Module :=
  {m with wires := blocks.flatMap (·.block.lower)}

theorem expanded_correct (m : FourState.Module) (blocks : List CheckedBlock)
    (hw : blocks.map (·.block.source) = m.wires)
    (hv : blocksValid (m.inputs.map (fun p => (p.name,p.width))) blocks = true)
    (ho : m.outputs.all (fun p => p.expr.valid (wireScope (m.inputs.map (fun p => (p.name,p.width))) m.wires)) = true)
    (env : FourState.Env) : (expanded m blocks).eval env = m.eval env := by
  have ha : ScopeAgree (m.inputs.map (fun p => (p.name,p.width))) env env := by intro n w _ i; rfl
  have h := blocks_scope_correct blocks _ hv env env ha
  rw [hw] at h
  simp only [FourState.Module.eval, wireValues_correct]
  apply List.map_congr_left
  intro o hm
  congr 1
  exact congrArg renderValue (eval_scope_congr o.expr _ _ _ h (List.all_eq_true.mp ho o hm))


/-- Each operator gets a private wire before encoding; operands become names.
The generated block is accepted only with its concrete inlining certificate and
freshness/typing checks. This generator adds no trusted axiom. -/
abbrev BuildState := Nat × List FourState.Wire

def saveExpr (stem : String) {w : Nat} (expr : FourState.Expr w) : StateM BuildState (FourState.Expr w) := do
  let (index,wires) ← get
  let name := stem ++ toString index
  set (index+1, {name,width:=w,expr}::wires)
  return .var name w

def splitExpr (stem : String) : {w : Nat} → FourState.Expr w → StateM BuildState (FourState.Expr w)
  | _, .const v => pure (.const v)
  | _, .fill v => pure (.fill v)
  | _, .var n w => pure (.var n w)
  | _, .not a => do saveExpr stem (.not (← splitExpr stem a))
  | _, .and a b => do saveExpr stem (.and (← splitExpr stem a) (← splitExpr stem b))
  | _, .or a b => do saveExpr stem (.or (← splitExpr stem a) (← splitExpr stem b))
  | _, .xor a b => do saveExpr stem (.xor (← splitExpr stem a) (← splitExpr stem b))
  | _, .add a b => do saveExpr stem (.add (← splitExpr stem a) (← splitExpr stem b))
  | _, .sub a b => do saveExpr stem (.sub (← splitExpr stem a) (← splitExpr stem b))
  | _, .mul a b => do saveExpr stem (.mul (← splitExpr stem a) (← splitExpr stem b))
  | _, .udiv a b => do saveExpr stem (.udiv (← splitExpr stem a) (← splitExpr stem b))
  | _, .shl a b => do saveExpr stem (.shl (← splitExpr stem a) (← splitExpr stem b))
  | _, .shr a b => do saveExpr stem (.shr (← splitExpr stem a) (← splitExpr stem b))
  | _, .sshr a b => do saveExpr stem (.sshr (← splitExpr stem a) (← splitExpr stem b))
  | _, .eq a b => do saveExpr stem (.eq (← splitExpr stem a) (← splitExpr stem b))
  | _, .caseEq a b => do saveExpr stem (.caseEq (← splitExpr stem a) (← splitExpr stem b))
  | _, .ult a b => do saveExpr stem (.ult (← splitExpr stem a) (← splitExpr stem b))
  | _, .slt a b => do saveExpr stem (.slt (← splitExpr stem a) (← splitExpr stem b))
  | _, .concat a b => do saveExpr stem (.concat (← splitExpr stem a) (← splitExpr stem b))
  | _, .mux a b c => do saveExpr stem (.mux (← splitExpr stem a) (← splitExpr stem b) (← splitExpr stem c))
  | _, .pmux a b c => do saveExpr stem (.pmux (← splitExpr stem a) (← splitExpr stem b) (← splitExpr stem c))
  | _, .zext k a => do saveExpr stem (.zext k (← splitExpr stem a))
  | _, .sext k a => do saveExpr stem (.sext k (← splitExpr stem a))
  | _, .extract k a => do saveExpr stem (.extract k (← splitExpr stem a))
  | _, .slice lo len a => do saveExpr stem (.slice lo len (← splitExpr stem a))

def Block.ofWire (stem : String) (source : FourState.Wire) : Block :=
  let (result, (_,wires)) := (splitExpr stem source.expr).run (0,[])
  {source,locals:=wires.reverse,result}


theorem outputs_values_correct (outputs : List FourState.Wire) (scope : List (String × Nat))
    (hf : ∀ o ∈ outputs, scope.lookup o.name = none)
    (hv : ∀ o ∈ outputs, o.expr.valid scope = true)
    (hn : (outputs.map (·.name)).Nodup) (env : FourState.Env) :
    ∀ o ∈ outputs, eval (.var o.name o.width) (outputs.foldl valueWireStep env) = eval o.expr env := by
  induction outputs generalizing env with
  | nil => simp
  | cons first rest ih =>
    have hnames := List.nodup_cons.mp hn
    intro o ho
    rcases List.mem_cons.mp ho with rfl | ho
    · have hrest : ∀ w ∈ rest, [(o.name,o.width)].lookup w.name = none := by
        intro w hw
        have hne : w.name ≠ o.name := by
          intro h
          exact hnames.1 (by simpa [h] using List.mem_map_of_mem (f := fun w : Wire => w.name) hw)
        simp [List.lookup_cons,beq_eq_false_iff_ne.mpr hne]
      have h := fresh_wires_preserve rest [(o.name,o.width)] hrest (valueWireStep env o)
      apply value_ext
      intro i
      have hi := h o.name o.width (by simp) i
      simpa [eval,valueWireStep,putValue,getBit,i.isLt] using hi
    · have h := ih (fun w hw => hf w (by simp [hw])) (fun w hw => hv w (by simp [hw]))
          hnames.2 (valueWireStep env first) o ho
      have hread := fresh_wires_preserve [first] scope
        (by
          intro w hw
          have hw' : w = first := by simpa using hw
          subst w
          exact hf first (by simp)) env
      have he := eval_scope_congr o.expr scope _ env hread (hv o (by simp [ho]))
      exact h.trans he

def outputAliases (m : FourState.Module) (stem : String) : List FourState.Wire :=
  m.outputs.map fun o => {o with name := stem ++ o.name}

def expose (m : FourState.Module) (stem : String) : FourState.Module :=
  {m with
    wires := m.wires ++ outputAliases m stem
    outputs := m.outputs.map (fun o => {o with expr := .var (stem ++ o.name) o.width})}

theorem expose_correct (m : FourState.Module) (stem : String)
    (hf : (outputAliases m stem).all (fun o => (wireScope (m.inputs.map (fun p => (p.name,p.width))) m.wires).lookup o.name == none) = true)
    (hv : m.outputs.all (fun o => o.expr.valid (wireScope (m.inputs.map (fun p => (p.name,p.width))) m.wires)) = true)
    (hn : ((outputAliases m stem).map (·.name)).Nodup) (env : FourState.Env) :
    (expose m stem).eval env = m.eval env := by
  have h := outputs_values_correct (outputAliases m stem)
    (wireScope (m.inputs.map (fun p => (p.name,p.width))) m.wires)
    (by intro o ho; simpa using List.all_eq_true.mp hf o ho)
    (by intro o ho; rcases List.mem_map.mp ho with ⟨q,hq,rfl⟩; exact List.all_eq_true.mp hv q hq)
    hn (m.wires.foldl valueWireStep env)
  simp only [FourState.Module.eval,wireValues_correct,expose,List.map_map,Function.comp_def,List.foldl_append]
  apply List.map_congr_left
  intro o ho
  congr 1
  exact congrArg renderValue (h {o with name := stem ++ o.name} (List.mem_map_of_mem ho))



/-- Render candidate data; the generated file still checks every inlining
certificate, the complete source-wire correspondence, freshness and typing. -/
def renderExpr : {w : Nat} → FourState.Expr w → String
  | w, .const v => s!"(@Expr.const {w} (BitVec.ofNat {w} {v.toNat}))"
  | w, .fill b => s!"(@Expr.fill {w} .{match b with | .zero => "zero" | .one => "one" | .x => "x" | .z => "z"})"
  | _, .var n w => s!"(.var {reprStr n} {w})"
  | _, .not a => s!"(.not {renderExpr a})"
  | _, .and a b => s!"(.and {renderExpr a} {renderExpr b})"
  | _, .or a b => s!"(.or {renderExpr a} {renderExpr b})"
  | _, .xor a b => s!"(.xor {renderExpr a} {renderExpr b})"
  | _, .add a b => s!"(.add {renderExpr a} {renderExpr b})"
  | _, .sub a b => s!"(.sub {renderExpr a} {renderExpr b})"
  | _, .mul a b => s!"(.mul {renderExpr a} {renderExpr b})"
  | _, .udiv a b => s!"(.udiv {renderExpr a} {renderExpr b})"
  | _, .shl a b => s!"(.shl {renderExpr a} {renderExpr b})"
  | _, .shr a b => s!"(.shr {renderExpr a} {renderExpr b})"
  | _, .sshr a b => s!"(.sshr {renderExpr a} {renderExpr b})"
  | _, .eq a b => s!"(.eq {renderExpr a} {renderExpr b})"
  | _, .caseEq a b => s!"(.caseEq {renderExpr a} {renderExpr b})"
  | _, .ult a b => s!"(.ult {renderExpr a} {renderExpr b})"
  | _, .slt a b => s!"(.slt {renderExpr a} {renderExpr b})"
  | _, .concat a b => s!"(.concat {renderExpr a} {renderExpr b})"
  | _, .mux a b c => s!"(.mux {renderExpr a} {renderExpr b} {renderExpr c})"
  | _, .pmux a b c => s!"(.pmux {renderExpr a} {renderExpr b} {renderExpr c})"
  | _, .zext k a => s!"(.zext {k} {renderExpr a})"
  | _, .sext k a => s!"(.sext {k} {renderExpr a})"
  | _, .extract k a => s!"(.extract {k} {renderExpr a})"
  | _, .slice lo len a => s!"(.slice {lo} {len} {renderExpr a})"

def renderWire (w : FourState.Wire) : String :=
  "{name := " ++ reprStr w.name ++ ", width := " ++ toString w.width ++ ", expr := " ++ renderExpr w.expr ++ "}"

def renderBlock (b : Block) : String :=
  "{source := " ++ renderWire b.source ++ ", locals := [" ++
    String.intercalate ", " (b.locals.map renderWire) ++ "], result := " ++ renderExpr b.result ++ "}"

def renderCheckedBlocks (m : FourState.Module) : String := Id.run do
  let mut declarations := []
  let mut names := []
  for (wire,index) in m.wires.zipIdx do
    let name := "dag_block_" ++ toString index
    let b := Block.ofWire ("_transition_dag_" ++ toString index ++ "_") wire
    declarations := declarations ++ ["def " ++ name ++ " : DAG.CheckedBlock := {block := " ++ renderBlock b ++
      ", inlined := by source_kernel_rfl}\n"]
    names := names ++ [name]
  return String.intercalate "\n" declarations ++ "\ndef dag_blocks : List DAG.CheckedBlock := [" ++
    String.intercalate ", " names ++ "]\n"

/-- Structured candidate data for optional sharing before kernel certification. -/
def candidateJson (m : FourState.Module) : Lean.Json :=
  .arr ((m.wires.zipIdx.map fun (wire,index) =>
    let b := Block.ofWire ("_transition_dag_" ++ toString index ++ "_") wire
    Lean.Json.mkObj [
      ("source", .str (renderWire b.source)),
      ("locals", .arr ((b.locals.map fun w => Lean.Json.mkObj [
        ("name", .str w.name), ("width", Lean.toJson w.width),
        ("expr", .str (renderExpr w.expr))]).toArray)),
      ("result", .str (renderExpr b.result))]).toArray)

end LeanRTL.FourState.DAG
