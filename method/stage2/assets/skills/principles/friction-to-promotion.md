---
id: friction-to-promotion
layer: principle
applies_to: library and process evolution
lib: docs/instructions/CORE.md §5 (friction hook); benchmarks/cvdp_agentic/friction/*.json
maturity: principle
---
# Friction → promotion (2-strike rule)

Recurring proof pain is a measurable signal, not an annoyance. Every iteration logs a friction JSON with a `sediment` note and a strike count; the second recurrence of the same gap triggers a promotion evaluation (plan v0.8 M28). The pain then crystallizes into a `LeanRTL/Lib/` combinator, a CORE.md authoring rule, or a tactic macro — after which the marginal cost of that class of proof drops toward zero. This library is the promoted layer; the friction JSONs remain the raw sediment pool feeding it. Examples that graduated: `ofNat_toNat_ofNat` (strike 2 → `@[simp]` in Lift), F9-wire-free (strike 3 → CORE §2.8), Parent whole-trace (strike 3 → `flattenParentSeq` machinery).
