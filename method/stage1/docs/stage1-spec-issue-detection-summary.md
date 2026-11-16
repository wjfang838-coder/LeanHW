# Stage 1 specification issue detection: implementation summary

The implementation uses **an LLM to extract requirements, candidate readings, and missing behavior and to write a partial LeanSpec; Lean mechanically searches for and verifies diagnostic witnesses**. The internal steps are 01 extraction, 02 formalization, 03 diagnosis, and 04 property checking.

LeanSpec centers on `admits : Cfg → Ctx → Obs → Bool`. Let $A_\theta(c)$ be the observations admitted by configuration $\theta$ in legal input context $c$, which may be an input trace.

1. **Ambiguity**: two candidate readings admit different observations for the same legal input:
   $$\exists c:\ A_{\theta_a}(c)\ne A_{\theta_b}(c).$$
   For deterministic models, this simplifies to $f_{\theta_a}(c)\ne f_{\theta_b}(c)$. The implementation is `queryDifference`; comparisons involving an unsatisfiable reading are recorded separately as repair options.

2. **Contradiction**: the current default reading admits no observation for some legal input:
   $$\exists c:\ A_{\theta_0}(c)=\varnothing.$$
   The implementation is `queryDeadness`; **there is no built-in `conflict` execution state**. A separate property check searches for an observation allowed by the definitions but forbidden by a stated guarantee:
   $\exists c,o:\ o\in A_{\theta_0}(c)\land ante_P(c)\land\neg holds_P(c,o)$.
   This is entailment failure, distinct from an empty admitted set.

3. **Incompleteness**: multiple observations remain admitted for the same legal input:
   $$\exists c:\ |A_{\theta_0}(c)|>1.$$
   The implementation is `queryFreedom`. The LLM represents unspecified behavior using `h_* : Option T := none`; `none` is an open configuration hole, **not an `unresolved` execution state**. `emitHole` also checks whether filling that hole changes the admitted set, establishing attribution.

Diagnosis first searches by executing Lean, then generates a proof for the same witness. Evidence that cannot be proved or depends on `sorryAx` is marked uncertified. Detection is limited to the formalized requirements and enumerated input/observation domains; it cannot guarantee discovery of NL issues the LLM did not extract or encode correctly. The implemented `admitSet` is a filtered list, so interpreting its length as set cardinality assumes a duplicate-free observation enumeration.

Source entry points:

- `method/stage1/leanspec/lean/LeanSpec/Core.lean`: `admitSet`, `queryDifference`, `queryDeadness`, `queryFreedom`, `emitHole`.
- `method/stage1/leanspec/lean/LeanSpec/Property.lean`: `violationAt`, `violation`, `entails`.
- `method/stage1/leanspec/diagnose.py`: search and certificate generation; `propcheck.py`: property checking.
- `method/stage1/leanspec/cli.py`, `author.py`, `pipeline.py`: orchestration of LLM authoring and mechanical checks.
