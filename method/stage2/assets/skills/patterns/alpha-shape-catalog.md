---
id: alpha-shape-catalog
layer: pattern
applies_to: choosing the abstraction function α (impl registers ↦ spec state) for a refinement
principle: sedimentation-surface-for-alpha-shapes
tactics: [pick-worked-instance-then-copy]
lib: "—"
example: eval_v3/<id>/Refinement.lean (per-row worked instances)
maturity: sediment
---
# α-shape catalog — how impls represent spec states

The creative core of every refinement is **α** (the abstraction function: impl registers ↦
abstract spec state) and its **gluing invariant**. This catalog is the sedimentation surface for
α *shapes*: once a shape is used by ≥2 designs it is a reusable pattern, and the table below points
the next impl-author at the worked instance to copy. (Formerly the prose head of
`LeanRTL/Lib/Refine/Alpha.lean`; the code lemmas `αReg` / `αReg_step` / `αReg_reset` were dead in
the live tree and pruned — the register-readout move is now inlined per design, and the per-step
plumbing it wrapped is `HWLib.regStepWF` / `HWLib.regResetWF` directly.)

## Catalog (v0.8 M27 batch, 8 designs — worked instances under `eval_v3/<id>/Refinement.lean`)

| pattern | shape | worked instances |
|---|---|---|
| register readout | one register IS the abstract state (`α env := BitVec.ofNat w (env "name")`) | 40_pwm, 61_mul32 (per stage), 93_seqdet, 32_cpu (per architectural reg) |
| state decode | small reg ↦ enum phase | 93_seqdet (2-bit state), 74_rv32m (job FSM) |
| pointer-pair → List | buffer slice of length `occ`; gluing inv `occ ≤ cap` | 63_fifo16 |
| delay-line readout | pipe regs ↦ spec delay list | 61_mul32_pipe |
| architectural projection | regfile+PC, pipeline regs washed out via `sInit` wash-out lemma | 32_cpu |
| phase collapse | warm/dead impl states ↦ adjacent spec phase (stutter absorbs) | 69_axi (both channels) |
| channel views | multi-channel spec split into per-channel views; observations must FACTOR through the views (prove `*_factors`) | 69_axi |
| job-state machine | CALC ↦ busy record; hold-cycle ↦ post-completion strobe state | 74_rv32m |

Commit-predicate patterns (for `StutterRefines`): "the handshake the current phase awaits fires"
(69_axi) · "completion / strobe / launch edges" (74_rv32m).

## The register-readout move (most common)

`α env := BitVec.ofNat w (env "count")`. Its two step obligations reduce directly through the
HWLib per-step laws (wire-free module):

- non-reset step: `HWLib.regStepWF m hw r i rg hfind` rewrites `(m.step r i false) rg.name` to
  `(eval rg.next (cycleEnv r i (m.regs.map (·.name)))).toNat` — the standard first move of `step_α`.
- reset step: `HWLib.regResetWF m r i rg hfind` rewrites `(m.step r i true) rg.name` to
  `rg.init.toNat` — the standard first move of `reset_α`.

1-bit port Bool-bridge (specs observe the low bit as a `Bool`): `(x.getLsbD 0).toNat = x.toNat`
for `BitVec 1`, closed by `decide +revert`.

## Candidates awaiting their second strike (per friction ledger)

output validity mask (63_fifo16 + 32_cpu dead values — arguably 2nd strike as a class) ·
`StutterRefinesInband` (74_rv32m) · `EventuallyRefines` liveness judgment (36_gcd) ·
concat-regroup lemma pack (69_axi) · signed-div bridge pack → HWLib (74_rv32m).
