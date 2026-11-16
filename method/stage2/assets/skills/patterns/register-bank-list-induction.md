---
id: register-bank-list-induction
layer: pattern
applies_to: N-entry register banks with a selected read
principle: leaf-is-decision-not-induction
tactics: [nat-case-split-transport]
lib: LeanRTL/Designs/CvdpAgentic/CacheController.lean (readSel_select) — design-local, not yet in Lib
example: cache_controller 32 entries (LeanRTL/Designs/CvdpAgentic/CacheController.lean)
maturity: sediment
strike: 1
---
# Register-bank list induction

To avoid a `$mem` (which disables F9 and powers up X), model a small storage as N named registers and prove the address-select cone with ONE k-parameterized list-induction lemma, instantiated N times. In `CacheController.lean`, `readSel` builds a mux tree over `List.range 32` and `readSel_select` proves `eval (readSel l) env = env.lookup (entryName (addr).toNat) …` by induction on the entry list; the top read is one instantiation over `List.range 32`. Gotcha: this lemma is design-local (promotion candidate for a shared `bankSelect`); the addressed-word transport at each entry needs a case-split + `ofNat_toNat_ofNat` (see nat-case-split-transport).

## Worked example

```lean
theorem readSel_select (env : Env) :
    ∀ (l : List Nat), (eval addrV env).toNat ∈ l → (∀ j ∈ l, j < 32) →
      eval (readSel l) env = env.lookup (entryName (eval addrV env).toNat) 32 := by
  intro l; induction l with
  | nil => intro h _; simp at h
  | cons x xs ih => …
```
> Source: LeanRTL/Designs/CvdpAgentic/CacheController.lean:275 (design-local; promotion candidate `bankSelect`)
