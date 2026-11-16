#!/usr/bin/env python3
"""Fragment assembler: the design file is ASSEMBLED from role-owned fragments — roles never
edit the assembled file directly.

Layout in the workspace:
    frags/<key>/impl.lean   (role D: hardware defs, `def impl : Module|Parent` last)
    frags/<key>/spec.lean   (role S: typed spec fns + the untyped sim adapters
                             specInit/specStep/specOuts).  Frozen once S commits.
    frags/<key>/proof.lean  (role D: L1 + whole-trace; MUST begin with the
                             `## 3. L1` marker block and contain the `## 4.` marker)

    python3 scripts/asm_f.py <key> [--frag spec|impl|impl+spec]   (--frag: stub the others)

Writes LeanRTL/Blind/<Camel>.lean with the four bb section markers intact.  The markers are load
bearing: `proof_mutation.py` attributes every mutant to a section through them, so an assembly
that loses one turns a killed mutant into an unattributable one.
"""
import os, sys, re, json

WS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

HEADER = """-- @blind {key}
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
{lib_imports}import Std.Tactic.BVDecide
set_option maxHeartbeats 1600000
namespace LeanRTL.Blind.{camel}
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
"""


def lib_imports() -> str:
    """Import whatever accumulated library this workspace was staged with.

    Discovered, not hard-coded: `LeanRTL.Lib.*` is a PROFILE-SELECTED asset, and a workspace
    staged for a bare arm has no `LeanRTL/Lib/` at all — a fixed import list would break its
    build and quietly redefine what "bare" means.

    Fixing a real gap: the library was importable from the workspace root and still unreachable
    from a role fragment, because a fragment is spliced in AFTER `namespace`/`open` and an
    import must precede it — so a role could never add one, whatever the profile granted.  Role
    P planned to use `refines_triv`, could not, and re-derived it by hand; that is the second
    run in a row where the accumulated library was staged and paid for but not usable.
    """
    root = os.path.join(WS, "LeanRTL", "Lib")
    if not os.path.isdir(root):
        return ""
    mods = []
    for dp, _, fns in os.walk(root):
        for fn in sorted(fns):
            if fn.endswith(".lean"):
                rel = os.path.relpath(os.path.join(dp, fn), root)
                mods.append("LeanRTL.Lib." + os.path.splitext(rel)[0].replace(os.sep, "."))
    return "".join(f"import {m}\n" for m in sorted(mods))

STUB_IMPL = """-- (impl fragment not yet committed)
def impl : Module :=
  { name := "__stub__", inputs := [], outputs := [], regs := [], clock := none }
"""
STUB_SPEC = """-- (spec fragment not yet committed)
def specInit : List (String × Nat) := []
def specStep (_regs _ins : List (String × Nat)) : List (String × Nat) := []
def specOuts (_regs _ins : List (String × Nat)) : List (String × Nat) := []
"""
STUB_PROOF = """/-! ## 3. L1 -/
-- (proof fragment not yet committed)
/-! ## 4. whole-trace -/
-- (not yet climbed)
"""


def camel_of(key):
    # Split on `-` and `.` as well as `_`.  The result names a Lean MODULE — `stage.py` writes it
    # as `LeanRTL/Blind/<camel>.lean` and closes the file with `end LeanRTL.Blind.<camel>` — and a
    # hyphen there does not survive: `lake` quotes the component as `«Prob000Four-to-one…»` while
    # the `end` clause does not, and the module fails to build.  ChipBench is the first benchmark
    # whose keys carry hyphens (`Prob000_Four-to-one_multiplexer`), and 7 of its 45 designs failed
    # this way, taking the whole workspace's `lake build` down with them.
    #
    # Widening the split cannot move a number already on disk: of the 324 keys across rtllm,
    # cvdp, verilogeval and realbench, ZERO contain `-` or `.`, so every existing camel is
    # unchanged, character for character.  It also settles a latent disagreement — `single.py`'s
    # own `camel` fallback has always split on `[_\-]`, so on a hyphenated key the two functions
    # named different files.
    return "".join(p[0].upper() + p[1:] for p in re.split(r"[_\-.]", key) if p)


def read_frag(key, name):
    p = os.path.join(WS, "frags", key, name + ".lean")
    return open(p).read() if os.path.isfile(p) else None


def assemble(key, frag_only=None, out_path=None):
    camel = camel_of(key)
    impl = read_frag(key, "impl")
    spec = read_frag(key, "spec")
    proof = read_frag(key, "proof")
    if frag_only == "impl":
        # Blind-parallel scope: the implementer never saw the specification, so a build of the
        # implementation alone must not put the specification's identifiers on its stdout.
        spec, proof = None, None
    if frag_only == "impl+spec":
        # Serial scope.  The implementer writes AGAINST a frozen specification and is meant to
        # read it, so stubbing it here would type-check the implementation against a stub and
        # then hand it to a proof step that sees the real one — a build that goes green on a
        # file nobody will ever assemble.  What kept the two apart under blind authoring is now
        # the freeze, which makes the specification unwritable rather than unreadable.
        proof = None
    if frag_only == "spec":
        impl, proof = None, None
    body = HEADER.format(lib_imports=lib_imports(), key=key, camel=camel)
    body += "\n/-! ## 1. impl -/\n" + (impl if impl is not None else STUB_IMPL)
    body += "\n/-! ## 2. spec -/\n" + (spec if spec is not None else STUB_SPEC)
    pf = proof if proof is not None else STUB_PROOF
    if "## 3. L1" not in pf:
        pf = "/-! ## 3. L1 -/\n" + pf
    if "## 4. whole-trace" not in pf:
        pf += "\n/-! ## 4. whole-trace -/\n-- (not climbed)\n"
    body += "\n" + pf
    body += f"\nend LeanRTL.Blind.{camel}\n"
    out = out_path or os.path.join(WS, "LeanRTL", "Blind", camel + ".lean")
    os.makedirs(os.path.dirname(out), exist_ok=True)
    open(out, "w").write(body)
    return out


if __name__ == "__main__":
    key = sys.argv[1]
    frag = None
    if "--frag" in sys.argv:
        frag = sys.argv[sys.argv.index("--frag") + 1]
    print("asm:", assemble(key, frag))
