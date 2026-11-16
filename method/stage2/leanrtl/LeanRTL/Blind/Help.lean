-- @blind --help
import LeanRTL.Core.Syntax
import LeanRTL.Core.Semantics
import LeanRTL.Core.DSL
import LeanRTL.Core.Refine
import LeanRTL.Core.CompilerCorrectSeq
-- Hierarchy.  A `Parent` design's intended proof route is `flattenParent_correct` / `WFInsts`
-- from HierCorrect, and none of the imports above reach it, so a fragment authoring a hierarchy
-- found them to be unknown identifiers and had to abandon the route.  Same shape as the
-- accumulated library being staged but unreachable: a fragment is spliced in after the opens and
-- can never add an import of its own.
import LeanRTL.Core.HierCorrect
import LeanRTL.Core.HierSeqCorrect
import LeanRTL.Core.HierRefine
import LeanRTL.Core.HierSeqBridge
-- F2.  A design whose spec gives it Verilog `parameter`s is modelled as a generator plus a
-- `paramMeta : ParamMeta`, and `bb.py` gates the parametric emit route on that declaration.  The
-- import is here rather than left to the author for the same reason as the hierarchy block above:
-- a fragment is spliced in after the opens and can never add one, so without this the route is
-- unreachable on the F arms whatever the spec says.  It costs nothing -- every workspace already
-- builds this module for its auto-generated ParamModule registry.
import LeanRTL.Core.ParamBackend
import Std.Tactic.BVDecide
set_option maxHeartbeats 1600000
namespace LeanRTL.Blind.Help
open LeanRTL
-- `SimRefines`/`Refines` live in `LeanRTL.Refine`, which `open LeanRTL` does not reach.  A
-- fragment is spliced in after this line and cannot add an `open`, so without this every author
-- must fully qualify them -- and `autoImplicit` turns a forgotten qualification into
-- "Function expected ... type ?m.1", which names neither the namespace nor the identifier.
open LeanRTL.Refine
-- `bb.py` gates the parametric route on the regex `def paramMeta : ParamMeta`, so the type has to
-- appear UNQUALIFIED for the route to be taken at all.  Opened by name rather than wholesale:
-- with `autoImplicit` on, a collision against a design's own definition would not be an error, it
-- would silently become a free variable -- which is how the first attempt at this route failed.
-- `PModule`/`NatE`/`PExpr` are the SYMBOLIC form of the same route, for a parameter that moves the
-- module's shape rather than its widths.  They are named here for the same reason `ParamMeta` is:
-- the author writes `def famP : PModule` as a type annotation, and `private def DW : NatE` as the
-- abbreviation that keeps the family readable, and neither can be qualified into scope from a
-- spliced fragment.  Both documented routes therefore reach every F arm, or neither does.
open LeanRTL.Designs.Param (ParamMeta clog2 PModule NatE PExpr)

/-! ## 1. impl -/
-- (impl fragment not yet committed)
def impl : Module :=
  { name := "__stub__", inputs := [], outputs := [], regs := [], clock := none }

/-! ## 2. spec -/
-- (spec fragment not yet committed)
def specInit : List (String × Nat) := []
def specStep (_regs _ins : List (String × Nat)) : List (String × Nat) := []
def specOuts (_regs _ins : List (String × Nat)) : List (String × Nat) := []

/-! ## 3. L1 -/
-- (proof fragment not yet committed)
/-! ## 4. whole-trace -/
-- (not yet climbed)

end LeanRTL.Blind.Help
