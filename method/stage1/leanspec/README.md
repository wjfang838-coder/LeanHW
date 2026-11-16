# Stage 1 — specification formalization and clarification

1. `cli.py` / `author.py`: the LLM extracts clauses with provenance, candidate readings, and holes from NL, then writes `Partial.lean`.
2. `lean/LeanSpec/Core.lean`: evaluates `admits` over enumerated legal inputs. `queryDifference` finds different admitted observations between two readings; `queryDeadness` finds an empty admitted set; `queryFreedom` finds multiple admitted observations.
3. `diagnose.py` / `propcheck.py`: run queries and property checks, producing witness certificates that Lean can check.
4. `witness.py` / `oracle.py`: turn witnesses into concrete clarification questions and obtain designer resolutions.
5. `patch.py` / `refine.py` / `emit.py`: revise and check, then output decided NL / LeanSpec. `pipeline.py` manages steps, rounds, and provenance.

Diagnosis checks the finite relational model authored by the LLM. There are no built-in `conflict` or `unresolved` CPU execution states. NL that the model omits or mistranslates does not automatically receive a semantic correctness guarantee. See the [detection summary](../docs/stage1-spec-issue-detection-summary.md).

After `source env.sh` at the repository root:

```bash
python3 -m leanspec.cli new demo --prose benchmarks/verilogeval/clarified/Prob001_zero/spec.clarified.txt
python3 -m leanspec.cli prompt demo --stage 1
python3 -m leanspec.author --help
```

`prompt` displays the author's required inputs; it does not replace authored artifacts. Configure an agent backend to run the author/pipeline. Outputs default to `data/`, overridable with `LEANSILICON_DATA`.
