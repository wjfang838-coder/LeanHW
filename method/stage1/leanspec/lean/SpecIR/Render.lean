import SpecIR.Machine

/-!
# `SpecIR.Render` — the golden trace, computed rather than written.

Every certified specification carries a concrete cycle-by-cycle table. This module is the only
thing allowed to produce it: the table is `#eval`'d from the IR, so it cannot disagree with the
IR.

That rule exists because of a specific mistake. While hand-writing the eight specifications in
`baselines/oracle_spec`, the `LFSR` sequence was written out by hand — and it was **wrong**, and
had to be recomputed. A table a model writes can be wrong in the same direction as the model's
misreading of the prose, which is precisely the direction that does the damage. A table Lean
evaluates cannot be.
-/

namespace SpecIR

private def pad (s : String) (n : Nat) : String :=
  if s.length ≥ n then s else s ++ String.ofList (List.replicate (n - s.length) ' ')

private def cell (v : Val) : String := v.render

namespace Design

variable {σ ι : Type}

/-- The trace as a GitHub-flavoured markdown table, ready to paste into rendered prose. -/
def table (d : Design σ ι) (stim : List ι) : String :=
  let rows := d.trace stim
  match rows with
  | [] => "(empty stimulus)"
  | r0 :: _ =>
    let inNames  := r0.ins.map Prod.fst
    let outNames := r0.outs.map Prod.fst
    let header := "| " ++ timebaseLabel ++ " | " ++
      String.intercalate " | " (inNames ++ outNames) ++ " |"
    let sep := "|" ++ String.join (List.replicate (1 + inNames.length + outNames.length) "---|")
    let body := rows.map (fun r =>
      "| " ++ toString r.cycle ++ " | " ++
      String.intercalate " | " ((r.ins.map (fun p => cell p.2)) ++
                                (r.outs.map (fun p => cell p.2))) ++ " |")
    String.intercalate "\n" (header :: sep :: body)
where
  timebaseLabel : String :=
    match d.timebase with
    | .fullCycle => "cycle"
    | .halfCycle => "half-cycle"

/-- A fixed-width plain-text rendering, for prose that should not look like a document. -/
def tableText (d : Design σ ι) (stim : List ι) : String :=
  let rows := d.trace stim
  match rows with
  | [] => "(empty stimulus)"
  | r0 :: _ =>
    let names := (r0.ins.map Prod.fst) ++ (r0.outs.map Prod.fst)
    let cells := rows.map (fun r => (r.ins.map (fun p => cell p.2)) ++
                                    (r.outs.map (fun p => cell p.2)))
    let widths := names.zipIdx.map (fun (nm, i) =>
      cells.foldl (fun w row => max w ((row[i]?.getD "").length)) nm.length)
    let line := fun (xs : List String) =>
      "  " ++ String.intercalate "  " (xs.zipIdx.map (fun (s, i) => pad s (widths[i]?.getD 0)))
    String.intercalate "\n" (line names :: rows.zipIdx.map (fun (_, i) =>
      line (cells[i]?.getD [])))

end Design
end SpecIR
