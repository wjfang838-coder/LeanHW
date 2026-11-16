---
id: crc-step-law-plus-kat
layer: pattern
applies_to: streaming CRC / LFSR checksum engines
principle: leaf-is-decision-not-induction
tactics: [bv-decide-for-fixed-width, decide-for-finite]
lib: LeanRTL/Designs/CvdpAgentic/EthernetMiiTx.lean (crcStepE / crcStepE_eval) — design-local
example: ethernet_mii_tx (LeanRTL/Designs/CvdpAgentic/EthernetMiiTx.lean)
maturity: sediment
strike: 1
---
# CRC step law + known-answer tests

For a streaming CRC, prove two things: (1) a per-step LFSR law — the emitted XOR cone for one byte equals a clean `crcSpecStep` (`crcStepE_eval` in `EthernetMiiTx.lean`, `bv_decide` over the byte×CRC state), and (2) `decide`-checked known-answer tests (KATs) that pin the polynomial/bit-order end to end. The step law gives generality; the KATs catch a wrong reflection or init constant that a single-step law alone would not. Gotcha: get the bit consumption order right — here `crcStepE byte crc` consumes the RAW payload byte, and the cone is applied once per byte at the odd-nibble edge; a swapped nibble order passes the step law but fails the KAT.

## Worked example

```lean
theorem crcStepE_eval (d : Expr 8) (c : Expr 32) (env : Env) :
    eval (crcStepE d c) env = crcSpecStep (eval d env) (eval c env) := by
  simp only [crcStepE, crcSpecStep, X, dB, cB, dS, cS, …, eval, if_xor, ofBool_if]

theorem crc_kat_spec_byte : crcSpecStep 0x2D 0xFFFFFFFF = 0xE0324416 := by decide
```
> Source: LeanRTL/Designs/CvdpAgentic/EthernetMiiTx.lean:306 (KAT at :332)
