import Lean
import FrozenRefinement

open Lean Meta Elab Command

/- The generator below constructs an ordinary proof term from two existing
theorems. addDecl sends that term to the Lean kernel. It never changes either
model or relation. Source request variables remain rigid, so matching cannot
specialize the universal request list to []. Propositional side assumptions
are rejected rather than generalized into a misleading theorem. -/
namespace Strengthening.Compose

def eqSides (t : Expr) : MetaM (Expr × Expr) := do
  let t ← whnf t
  unless t.isAppOfArity ``Eq 3 do throwError "Not an equality: {t}"
  return (t.getArg! 1,t.getArg! 2)

def finish (name : Name) (proof : Expr) : MetaM Unit := do
  let value ← instantiateMVars proof
  let r ← abstractMVars value
  let value := r.expr
  let type ← inferType value
  forallTelescope type fun xs _ => do
    for x in xs do
      if ← isProp (← inferType x) then
        throwError "Refuse unproved propositional side assumption: {x}"
  unless !value.hasMVar && !type.hasMVar do throwError "Unresolved metavariables"
  addDecl <| .thmDecl {name,levelParams:=r.paramNames.toList,type,value}
  logInfo m!"COMPOSED_TYPE: {← ppExpr type}"

def compose (name sp bp : Name) : MetaM Unit := do
  let spc ← mkConstWithFreshMVarLevels sp
  let bpc ← mkConstWithFreshMVarLevels bp
  forallTelescope (← inferType spc) fun sourceArgs sourceBody => do
    let (source,expected) ← eqSides sourceBody
    let sourceProof := mkAppN spc sourceArgs
    let (args,_,body) ← forallMetaTelescopeReducing (← inferType bpc)
    let actualProof := mkAppN bpc args
    let body ← whnf body
    let proof ← if body.isAppOfArity ``Eq 3 then do
        let (actual,expectedRTL) ← eqSides body
        unless ← isDefEq expected expectedRTL do
          throwError "Behavior observations do not definitionally align: {expected} versus {expectedRTL}"
        if ← isDefEq source actual then throwError "Refuse identical endpoint expressions"
        mkEqTrans sourceProof (← mkEqSymm actualProof)
      else if body.isAppOfArity ``FrozenRefinement.All₂ 5 then do
        let expectedRTL := body.getArg! 3
        let actual := body.getArg! 4
        unless ← isDefEq expected expectedRTL do throwError "Output refinement observations do not align"
        withLocalDeclD `outputs (← inferType source) fun x => do
          let proposition := mkAppN body.getAppFn #[body.getArg! 0,body.getArg! 1,body.getArg! 2,x,actual]
          let f ← mkLambdaFVars #[x] proposition
          let transported ← mkCongrArg f sourceProof
          mkEqMPR transported actualProof
      else throwError "Unsupported RTL trace theorem: {body}"
    let proof ← mkLambdaFVars sourceArgs proof
    finish name proof

elab "#compose_trace " name:ident " using " sp:ident " and " bp:ident : command => do
  liftTermElabM <| compose name.getId sp.getId bp.getId

elab "#compose_any " name:ident " specs " specs:str " rtls " rtls:str : command => do
  liftTermElabM do
    let mut errors : Array String := #[]
    for sp in specs.getString.splitOn "," do
      for bp in rtls.getString.splitOn "," do
        let state ← saveState
        try
          compose name.getId sp.toName bp.toName
          logInfo ("COMPOSED_FROM: " ++ sp ++ " + " ++ bp)
          return
        catch e =>
          errors := errors.push (sp ++ " + " ++ bp ++ ": " ++ (← e.toMessageData.toString))
          state.restore
    throwError "No exact observation composition: {String.intercalate "\n" errors.toList}"

end Strengthening.Compose
