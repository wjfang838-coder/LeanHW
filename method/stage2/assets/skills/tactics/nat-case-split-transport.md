---
id: nat-case-split-transport
layer: tactic
applies_to: addressed-word reads over an N-entry bank
principle: leaf-is-decision-not-induction
lib: LeanRTL/Lib/Lift.lean (ofNat_toNat_ofNat)
maturity: sediment
strike: 1
---
# Case-split + `ofNat_toNat_ofNat` transport

To prove an addressed read selects the right entry from an N-register bank (register-bank-list-induction), split the address into its N concrete values (`rcases`, bounded-nat-case-split) and transport each selected word through `ofNat_toNat_ofNat` so the `.toNat`-indexed lookup matches the `ofNat` register value. In `CacheController.lean` this is a 32-way split feeding `readSel_select`. Gotcha: the transport lemma is what makes the `env.lookup (…).toNat` on one side equal the `BitVec.ofNat` register on the other — without it the two sides are defeq but the case's `rfl` does not fire.
