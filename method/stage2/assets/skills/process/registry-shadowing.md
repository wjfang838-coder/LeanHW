---
id: registry-shadowing
layer: process
applies_to: parametric emission via the registry
lib: LeanRTL/Designs/Param/Registry.lean
maturity: sediment
---
# Registry shadowing — grep which impl is served

`leanrtl extract`/`pverilog` resolves a design by a toplevel key in the param registry. That key can be **shadowed** across registries, so the emitted RTL may come from a different impl than you edited — and, on a shared build, a stale `leanrtl` exe silently serves the previous version. Before trusting an emission: confirm `lake build` is green in the SAME command, and grep the registry to verify which impl the key actually points at. A shadowed key is a silent way for "proof reaches artifact" to break (proof-carrying-reaches-artifact).
