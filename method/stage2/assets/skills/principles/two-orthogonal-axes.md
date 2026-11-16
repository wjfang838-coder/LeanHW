---
id: two-orthogonal-axes
layer: principle
applies_to: grading and reporting proof strength
lib: scripts/proof_level.py
maturity: principle
---
# Two orthogonal axes of proof strength

Proof strength is not a scalar. It has a **vertical** axis L0–L5 (how much of the time/logic is captured: single-step → whole-trace → observed outputs → semantic headline) and a **horizontal** axis 📐∀N (breadth: a fixed instance vs. a parametric ∀N theorem). The two are independent: a design can be L5-on-a-fixed-width yet not ∀N, or ∀N yet only L3. The reported level is the **max reached** on the vertical axis; the ∀N badge is orthogonal and does not raise or lower it. `proof_level.py` classifies designs on this grid. Do not conflate "proved for all N" with "proved the whole trace".
