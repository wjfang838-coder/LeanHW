---
id: friction-hook
layer: process
applies_to: every iteration run
principle: friction-to-promotion
lib: docs/instructions/CORE.md §5; benchmarks/cvdp_agentic/friction/*.json
maturity: promoted
---
# Log a friction JSON every run

Every ITER run writes a root-cause JSON AND a `<key>.friction.json` (schema = `eval_v3/*/friction.json`): each friction entry records `kind` (spec | framework-gap | proof | tooling), `what` stuck, `resolution`, and a `sediment` note naming the library model/law/α that should be promoted (with its strike count). Write it even with zero frictions (`"frictions": []`) — zero friction is fitness data. This is the input to the 2-strike counter (friction-to-promotion): a `framework-gap` entry recurring a second time triggers a promotion evaluation. No log, no counting, no promotion.
