---
id: ofnat-tonat-ofnat-simp
layer: tactic
applies_to: multi-register bridges (the reg-value round-trip)
principle: commuting-square-and-generic-induction
lib: LeanRTL/Lib/Lift.lean (ofNat_toNat_ofNat, @[simp])
maturity: promoted
strike: 2
---
# `ofNat_toNat_ofNat` round-trip normalizer

Every multi-register lift hits `BitVec.ofNat w ((BitVec.ofNat w n).toNat)` — a register value written back and read again. `ofNat_toNat_ofNat : BitVec.ofNat w ((BitVec.ofNat w n).toNat) = BitVec.ofNat w n` is the `@[simp]` normalizer that kills it at the source, BEFORE `toNat` is pushed into a concrete literal modulus. Promoting this one lemma (strike 2) let every later bridge drop its bespoke `ofNat_mod<2^w>` lemmas. It fires automatically in the `hstep_simp` set — just make sure `simp only` includes it (or `hstep_simp`) rather than a full `simp` that would race ahead to the literal form.
