---
id: memory-raw-laws
layer: pattern
applies_to: addressed $mem designs (RAM / byte-enable)
principle: leaf-is-decision-not-induction
tactics: [bv-decide-for-fixed-width, nat-case-split-transport]
lib: LeanRTL/Core/MemSemantics.lean; LeanRTL/Designs/Examples/MemoryStage1.lean (read-after-write theorem)
example: byte_enable_ram / apb_dsp (LeanRTL/Designs/CvdpAgentic/ByteEnableRam.lean, Cvdp/CvdpApbDspUnit0001.lean)
maturity: promoted
---
# Memory raw laws (per-access read-after-write)

Addressed memory (`$mem_v2`) rarely gets a whole-design `simulate` theorem; instead prove per-access laws honestly. In `ByteEnableRam.lean`: byte-lane selection (`selA_a_wins`/`selA_b_fills`/`selA_untouched`), collision (`w_coll_correct`), write cones (`wr_data_*`), and a `read_pipeline_correct` read-after-write law, over a free-input trace. The module-clocked-write + async-read shape does get a whole-design read-after-write theorem (`WholeDesign/Memory.lean`, CORE §1.3 Stage 1); other shapes stay per-access + cosim. Gotcha: keep the input trace genuinely free (do not assume a write precedes every read) — the read-after-write law must state the ordering it needs, not smuggle it in.

## Worked example

```lean
theorem mem_raw_a (e : Env) (hen : eval wrA.en e = 1) :
    MemBlock.readVal (MemBlock.writeStep wrA m e) wrA.addr e = eval wrA.data e :=
  MemBlock.read_after_write wrA m e hen
```
> Source: LeanRTL/Designs/CvdpAgentic/ByteEnableRam.lean:228
