---
id: bv-decide-for-fixed-width
layer: tactic
applies_to: fixed-width BitVec equality leaves
principle: leaf-is-decision-not-induction
lib: "—"
maturity: promoted
---
# `bv_decide` for fixed-width leaves

The default closer for a single-step BitVec goal over concrete widths: `bv_decide` bit-blasts to SAT and emits an LRAT certificate, so the proof stays inside the audited axiom whitelist (`propext`/`Classical.choice`/`Quot.sound` + the bv_decide LRAT axioms — check with `#print axioms`). Use it for next-state cones, FSM transition tables, flag laws, byte-lane selects — anything finite and combinational. Gotcha: it does NOT scale to a full multiplier product (see restate-to-avoid-sat-blowup) and cannot see a Nat-level `%`/`+` — convert to BitVec or restate arithmetically first.
