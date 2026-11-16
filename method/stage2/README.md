# Stage 2 — LeanRTL

Proof-native RTL implementation: generate or correct RTL, obtain LeanRTL through the actual parser, and perform agentic theorem proving.

| Component | Source | Responsibility |
|---|---|---|
| RTL-to-Lean parser | `v2lean/` | Yosys RTLIL / SystemVerilog → symbolic, clocked, four-state, and native-memory models |
| Agentic implementation and proving | `leanrtl/` | Workspaces and frozen contracts, author loops, implementation/proof correction, validation gates, and emission after acceptance |
| LeanRTL semantics | `framework/` | Circuit and timing semantics, refinement, compiler correctness |
| Fixed-target proving | `refinement/` | Fixed observation/input contracts, `FrozenRefinement.Refines`, proof replay, axiom audit |
| Proof resources | `assets/`, `profiles/`, `audit/` | Lemmas, prompts, workflow configuration, and checks |

`leanrtl/frozen.py` provides the author/correction runner for frozen specifications; `two_author.py`, `pipeline.py`, and `verify.py` manage implementation and proof feedback. `refinement/refinement_checks.py` independently checks a fixed proposition: an LLM-selected relation alone cannot be the acceptance criterion. Configure the agent backend and model separately; this repository contains no personal credentials or private server addresses.

From the repository root:

```bash
source env.sh
lake build LeanRTL FrozenRefinement
python3 -m v2lean.import_refinement --help
python3 -m leanrtl.frozen --help
```

The complete actual RTL → cycle LeanSpec → transaction ISA case is in `case_cpu/memory/` at the repository root. Native RAM import is not a general SV compiler-correctness theorem; see the case README for scope and assumptions.

Detailed entry points: [leanrtl](leanrtl/README.md), [parser](v2lean/README.md), and [fixed-target refinement](refinement/README.md).

For an end-to-end smoke run, see the [MUX profile](example/mux_e2e/README.md): `python3 -m leanrtl.e2e_mux --case mux_fresh` starts from NL, generates RTL, and checks both the handoff theorem for the original LeanSpec trace relation and the fixed refinement target for the actual LeanRTL. This entry point connects relational and executable specifications. Its current scope is an explicitly declared one-bit stateless MUX profile.
