---
id: verify-by-regenerate-diff
layer: process
applies_to: generated registries / derived files
lib: LeanRTL/Designs/Param/Registry.lean
maturity: sediment
---
# Verify generated files by regenerate + diff

For any file that is machine-generated (the param registry, an emitted index), the check is: regenerate it and `git diff` should be empty. A non-empty diff means the source of truth and the checked-in artifact have drifted. Do not hand-edit a generated file — edit its generator and regenerate. This keeps the "proof reaches artifact" chain (proof-carrying-reaches-artifact) honest at the registry level, where a stale entry would silently route emission to the wrong impl (see registry-shadowing).
