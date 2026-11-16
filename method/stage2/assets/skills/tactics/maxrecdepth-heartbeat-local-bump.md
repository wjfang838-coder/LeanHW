---
id: maxrecdepth-heartbeat-local-bump
layer: tactic
applies_to: a single proof that overruns default limits
principle: leaf-is-decision-not-induction
lib: "—"
maturity: sediment
---
# Bump maxRecDepth / heartbeats locally only

When one big `bv_decide` or a deep transition table overruns `maxRecDepth` or `maxHeartbeats`, raise the limit with a `set_option … in` on that single theorem, not file-wide. A global bump masks accidental blow-ups elsewhere and slows the whole build. Prefer fixing the statement (restate-to-avoid-sat-blowup) first; use the local bump only when the proof is genuinely large-but-finite and you have confirmed it terminates.
