# Stage 1 — LeanSpec

Specification formalization, diagnosis, and designer / human-in-the-loop clarification and revision.

| Step | Source | Input → output |
|---|---|---|
| Formalization | `leanspec/author.py`, `cli.py`, `schema.py` | NL → clauses / candidate readings / holes → `Partial.lean` |
| Diagnosis | `leanspec/diagnose.py`, `propcheck.py`, `lean/LeanSpec/` | Finite `admits` model → ambiguity, contradiction, undetermined behavior, and Lean witness certificates |
| Clarification | `leanspec/witness.py`, `oracle.py` | Concrete witnesses → questions and candidate behaviors → designer answers |
| Revision | `leanspec/patch.py`, `refine.py`, `emit.py` | Decisions → prose / Lean revisions → checks → frozen NL / LeanSpec |
| Orchestration | `leanspec/pipeline.py`, `cases.py` | Steps, rounds, artifact handoff, and provenance |

Clarification is currently a designer question/answer protocol. By default, `oracle.py` invokes a designer agent through `common.agent_backend`. Human-in-the-loop describes where designer decisions enter the method; **the current code has no separate web or terminal UI for human input**. Default agent answers must not be described as human answers. Manual integrations should use the same question/answer records and checking protocol, preserving the source of each answer.

`leanspec/lean/LeanSpec/` provides partial-specification and diagnosis semantics. `leanspec/lean/SpecIR/` provides the executable specification representation. Both belong to this stage, but the names are not interchangeable. Shared agent, sandbox, and path support is in `common/`, also used by Stage 2.

From the repository root:

```bash
source env.sh
lake build LeanSpec SpecIR
python3 -m leanspec.cli --help
python3 -m leanspec.author --help
```

See [leanspec/README.md](leanspec/README.md) for the workflow and the [source-based detection summary](docs/stage1-spec-issue-detection-summary.md) for the detection mechanisms.

`LeanSpec/Handoff.lean` provides selection from a finite observation relation and its soundness/exactness theorems. Stage 2's MUX e2e profile additionally checks exact correspondence with the original `admits` relation for arbitrary-length traces. A finite diagnosis sweep is not a substitute for that proof.
