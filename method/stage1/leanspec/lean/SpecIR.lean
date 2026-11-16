import SpecIR.Val
import SpecIR.Machine
import SpecIR.Render
import SpecIR.Check

/-!
# specIR — a specification as a formal object whose determinacy is a theorem.

  * `SpecIR.Val`      the value lattice, with `hole` as a first-class undetermined value
  * `SpecIR.Machine`  what a specification denotes: a total machine over `Val`-valued ports
  * `SpecIR.Render`   the golden trace, computed from the IR and never written by a model
  * `SpecIR.Check`    the obligations, and the JSON the Python driver reads

This executable specification representation belongs to Stage 1. See
`method/stage1/README.md` for its relationship to the partial LeanSpec diagnosis model.
-/
