---
id: decide-for-finite
layer: tactic
applies_to: small finite enumerations and known-answer checks
principle: leaf-is-decision-not-induction
lib: "—"
maturity: promoted
---
# `decide` for small finite checks

For a small, fully-concrete finite claim — a single wrap state in a counter, a CRC known-answer test, a 7-entry transition row — `decide` evaluates the `Decidable` instance to `isTrue` and closes it, keeping the proof self-contained (no SAT certificate needed). Use it for the ONE wrap case in counter-decode-mod and for KATs in crc-step-law-plus-kat. Gotcha: `decide` is not `bv_decide` — it kernel-reduces, so it is fine for a handful of cases but blows up on a full-width sweep; use `bv_decide` (with its LRAT certificate) once the space is large.
