import LeanRTL.Lib.EvalLookup

namespace CaseCPU.NetFacts
open LeanRTL

theorem append_eval (a b : List Wire) (e : Env) :
    evalWires (a ++ b) e = evalWires b (evalWires a e) := by
  simp [evalWires, List.foldl_append]

theorem not_written (ws : List Wire) (e : Env) (n : String)
    (h : n ∉ ws.map (·.name)) : evalWires ws e n = e n := by
  induction ws generalizing e with
  | nil => rfl
  | cons w ws ih =>
    simp only [List.map_cons, List.mem_cons, not_or] at h
    rw [evalWires_cons, ih _ h.2]
    simp [h.1]

/-- A generic semantic equation for a topologically ordered wire. The circuit-specific
    evidence is only list decomposition and the checked absence of forward references. -/
theorem equation (before after : List Wire) (w : Wire) (e : Env)
    (hn : w.name ∉ after.map (·.name))
    (hc : w.expr.varsW.all (fun p => !((w :: after).map (·.name)).contains p.1) = true) :
    evalWires (before ++ w :: after) e w.name =
      (eval w.expr (evalWires (before ++ w :: after) e)).toNat := by
  let b := evalWires before e
  have he : eval w.expr b = eval w.expr (evalWires (w :: after) b) := by
    apply eval_lookup_congr
    intro p hp
    have hn' : p.1 ∉ (w :: after).map (·.name) := by
      have hh := List.all_eq_true.mp hc p hp
      simpa using hh
    unfold Env.lookup
    rw [not_written _ _ _ hn']
  rw [append_eval, evalWires_cons, not_written _ _ _ hn]
  simp only [ite_true]
  exact congrArg BitVec.toNat he
end CaseCPU.NetFacts

namespace CaseCPU.NetFacts
open LeanRTL
def closed (known : List String) : List Wire → Bool
  | [] => true
  | w :: ws => w.expr.varsW.all (fun p => known.contains p.1) && closed (w.name :: known) ws

/-- Verified shallow evaluation: a candidate valuation satisfying the actual wire
    equations agrees with the deep LeanRTL evaluator. Topology and base agreement
    are explicit obligations, so no wire result is assumed as an axiom. -/
theorem shallow_correct (ws : List Wire) (base candidate : Env) (known : List String)
    (hc : closed known ws = true)
    (hb : ∀ n ∈ known, base n = candidate n)
    (he : ∀ w ∈ ws, candidate w.name = (eval w.expr candidate).toNat) :
    ∀ n ∈ ws.map (·.name) ++ known, evalWires ws base n = candidate n := by
  induction ws generalizing known base with
  | nil => simpa [evalWires] using hb
  | cons w ws ih =>
    simp only [closed, Bool.and_eq_true] at hc
    have hv : eval w.expr base = eval w.expr candidate := by
      apply eval_lookup_congr
      intro p hp
      have hk : p.1 ∈ known := by simpa using List.all_eq_true.mp hc.1 p hp
      unfold Env.lookup
      rw [hb p.1 hk]
    have hnext : ∀ n ∈ w.name :: known,
        (if n = w.name then (eval w.expr base).toNat else base n) = candidate n := by
      intro n hn
      by_cases h : n = w.name
      · subst n; simp [hv, ← he w (by simp)]
      · simp only [List.mem_cons] at hn
        simp only [h, ↓reduceIte]
        exact hb n (hn.resolve_left h)
    rw [evalWires_cons]
    intro n hn
    apply ih _ (w.name :: known) hc.2 hnext (fun v hv => he v (by simp [hv])) n
    simpa [List.mem_cons, or_assoc, or_left_comm, or_comm] using hn
end CaseCPU.NetFacts
