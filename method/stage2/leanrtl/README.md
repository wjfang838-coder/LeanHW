# Stage 2 — proof-native RTL implementation

The input is a clarified, frozen specification. Generate RTL, obtain LeanRTL through the actual parser/importer, then prove that its behavior satisfies the frozen specification.

- `stage.py`, `two_author.py`, `pipeline.py`: workspaces, author roles, and implementation/proof workflows.
- `frozen.py`, `contract.py`, `verify.py`: frozen contracts, correction loops, independent gates, and emission.
- `method/stage2/v2lean/import_refinement.py`: the import-only frontend, with an explicit symbolic, clocked, system, timed, or fourstate model. It does not treat roundtrip equivalence as ISA refinement.
- `method/stage2/v2lean/native_memory.py`: preserves actual Yosys `$mem_v2` nodes to import the CPU's register + RAM semantics. See `method/stage2/framework/LeanRTL/Core/NativeMemory.md` for supported constructs.
- `method/stage2/framework/LeanRTL/`: execution semantics, observations, refinement, and compiler correctness.
- `method/stage2/refinement/lean/FrozenRefinement.lean`: fixed targets over all traces and all named outputs, plus the certificate interface.
- `method/stage2/refinement/refinement_checks.py`: checks proof terms, cold replay, and the axiom roster against a frozen target. `cold=False` provides feedback only; authoritative replay requires `cold=True`. Callers must first verify input and framework provenance.

The LLM may write an auxiliary relation, but it must ultimately prove initialization, step preservation, and output observation, and derive the fixed `Refines` target. A `True` relation alone is not an acceptance criterion. Proving only similar internal states does not establish complete instruction correctness. Any input restriction, reset prefix, or transaction protocol must appear explicitly in the theorem's scope.

Parser entry point, from the repository root:

```bash
source env.sh
python3 -m v2lean.import_refinement --help
```

See `case_cpu/memory/` for the complete actual RTL → cycle LeanSpec → transaction ISA application. Framework compiler theorems, the Python importer, and the native-memory frontend have different trust boundaries and are not substitutes for one another.
