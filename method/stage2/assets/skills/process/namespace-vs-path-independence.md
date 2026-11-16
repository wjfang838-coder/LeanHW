---
id: namespace-vs-path-independence
layer: process
applies_to: moving .lean files around
lib: "—"
maturity: sediment
---
# Namespace vs. import path are independent

Moving a `.lean` file changes its **import path** (`import LeanRTL.Designs.Foo`), not its declared **namespace** (`namespace LeanRTL.Cvdp`). Open/qualified references to a declaration survive a file move as long as the namespace is unchanged — only the `import` lines that pull the file in need updating (and `LeanRTL.lean`'s import list). So a reorg is safe for downstream proofs if you fix imports and leave namespaces alone; do not rename declarations just because their file moved.
