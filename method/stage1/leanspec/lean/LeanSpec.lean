import LeanSpec.Core
import LeanSpec.Property

/-!
# LeanSpec — Part 1 of leanSilicon.

Lean defines the authoritative semantics of a partial specification.  Everything else in this
half (the Python driver, the designer oracle) either *feeds* this library or *reads what it
printed*; nothing else decides what a specification means.

  * `LeanSpec.Core`      the `admits` relation, the four diagnosis queries, witness search,
                         candidate-space splitting, and the finding emitters.
  * `LeanSpec.Property`  what the prose *asserts*, checked against what it *defines*:
                         entailment, vacuity, pinning, independence.

This library does not import `LeanRTL` and `LeanRTL` does not import it.  The two parts of
leanSilicon are decoupled all the way down to the Lean dependency graph — see `GOAL.md`.
-/
