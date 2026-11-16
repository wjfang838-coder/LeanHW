# Fixed-target refinement framework

General framework code extracted from the original experiment directory, excluding per-case proofs, experiment rosters, and results.

- `lean/FrozenRefinement.lean`: Model, ValueRefines, OutputsRefine, Refines, Certificate, and composition theorems.
- `lean/BasicRewrite.lean`: general rewrite-proof support.
- `lean/RefinementTests.lean`: semantic boundary regressions.
- `lean/Compose.lean`: kernel proof terms composing existing endpoint theorems; rejects unproved propositional side assumptions and identical endpoints.
- `lean/BitwiseBridge.lean`: Nat / BitVec helper lemmas.
- `refinement_contract.py`: contracts fixing the interface, input normalization, model, and observations.
- `refinement_checks.py`: fixed-target proof.term replay, source binding, and axiom audit.
- `refinement_artifacts.py`: structural checks and emission after acceptance.
- `proof_checks.py`: the older two-state exact-equivalence certificate checker, retained as a related interface.

These are library interfaces. A new design still needs a frozen specification, actual Imported.lean, a contract, and a proof term. There is no guarantee of automatically proving arbitrary NL / arbitrary RTL correct.

The current `clockedInitial` explicitly uses a fixed-zero profile; its clocked adapter cannot prove arbitrary-initial-state refinement. This profile does not replace the symbolic model's arbitrary initialization or the CPU's native-RAM-specific proofs. During migration, two old regressions expecting nonzero initial states were corrected to match this existing zero-initialization definition; framework semantics were not changed.
