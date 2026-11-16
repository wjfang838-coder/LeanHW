#!/usr/bin/env python3
"""leanSpec — from a natural-language specification to a decided one.

Part one of leanSilicon, and it runs alone.  Nothing here imports `leanrtl`, reads a workspace,
or knows that an implementation half exists; what it produces is prose plus a record of how the
prose was settled, which is a deliverable whether or not anyone builds the design.

The method is one loop:

    extract      clauses, with byte-exact provenance in the original text
    formalize    `admits : Cfg → Ctx → Obs → Bool` — a RELATION, so both failure directions
                 are queries rather than judgement calls
    diagnose     four queries: difference, freedom, deadness, equivalence — every finding
                 re-proved as a theorem before it is believed
    properties   the claims the prose makes about itself, checked in the same finite frame
    witness      for each finding, the cheapest context at which the readings provably differ
    resolve      put that context in front of the designer as waveforms; record what survives
    decide       which coordinate the answer fixes, and which sentence has to change
    output       decided prose, decided Lean, and the questions with their answers

Repeated until the decided configuration admits exactly one observation at every legal context,
certified by the kernel — or until the record says why it cannot, which is a result too.

  * `cases`       one run's directory, registry, ledger and audit
  * `schema`      what an extraction must contain to be checkable at all
  * `diagnose`    the four queries and their certificates
  * `propcheck`   entailment, vacuity, pinning, independence
  * `witness`     the cheapest separating context, with predictions recorded before any query
  * `oracle`      the designer, asked about behaviour and never about our vocabulary
  * `refine`      what an answer eliminates, and whether the result is determined
  * `emit`        the decided Lean spec, from the decisions and nothing else
  * `patch`       byte-exact prose edits, each quoting the sentence it revises
  * `pipeline`    the ten steps, on the shared step-document contract
"""
from __future__ import annotations

import os
import sys

# Shared agent support lives in the adjacent common package.
