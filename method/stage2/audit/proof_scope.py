#!/usr/bin/env python3
"""The SCOPE of a design's proof, and the assumptions it rests on.

    audit/proof_scope.py <assembled.lean> [--ws <workspace>] [--json]

## No single word

There is no summary label here, and that is the point.  A word like "complete" is true only
inside the model, and would be read as complete full stop.  What the proof does not reach is
not small: the formal spec may be a misreading of ambiguous prose; the emitted Verilog's meaning
in a real simulator is not in Lean (that is what co-simulation checks, empirically); latches,
delta cycles, X-propagation and true dual-edge designs are outside `Module.simulate` entirely;
`LegalInputs` is an assumption; and the framework's own theorems rest on trusted axioms.

Compressing that into one token is how a claim gets quoted past its own boundary.  So this
reports two things and refuses to collapse them.

## Not "coverage"

To a hardware engineer `coverage` means simulation coverage — line, toggle, functional.  The
framework separately has `Module.semanticCoverage`, which asks whether a DESIGN is inside the
reference semantics at all and has nothing to do with proofs.  Three unrelated meanings for one
word, in a domain where the third is the default reading, is exactly the kind of label that gets
misread.  So this reports a **scope** and its **assumptions**, and the word coverage is left to
the simulator.

## scope — three independent axes, not a ladder

    time      cycle | trace       one clock, or all of them
    observed  registers | pins    the design's own state, or its declared output ports
    reset     n/a | never | any   combinational; asserted never; asserted at will

They are NOT ordered.  `SimRefines` gives `time=trace` but says nothing whatsoever about the
output ports, while the one-cycle output law gives `observed=pins` for a single clock.  Neither
implies the other — verified in this repository's own first design, where the pin law
`impl_obs` sits in the L1 section and `accu_simRefines` never mentions `outputs?eval`.  A
numbered level implies a total order that does not exist, which is why there are no numbers.

## `rests_on` — the per-design side condition, checked

There is no `assumes` field.  The word flattened three different epistemic statuses into one:
a condition Lean decides, a hypothesis with a physical justification, and something nobody
checks at all.  Reading them as equivalent is how a boundary gets lost.

Only ONE of them varies per design, so only that one is reported here:
`Module.semanticCoverage` (Core/Coverage.lean) decides whether a design is inside the reference
semantics at all, and names the constructs responsible when it is not — a whole-trace proof
about a design the simulator does not model is a proof about something else.

The rest — the Lean kernel's axioms, the framework's own compiler-correctness theorems,
`LegalInputs`, the emitted Verilog's meaning under a real simulator, and above all that the
formal spec is what the prose meant — are constant across designs and belong in
`docs/TRUST_BASE.md`, stated once, rather than repeated on every row where they would read as
having been checked.
"""

import argparse
import json
import os
import re
import subprocess
import sys

# Statement-level markers: what appears in a theorem's TYPE, after the colon.
SIMREFINES = re.compile(r":\s*SimRefines\b|:\s*Refine\.SimRefines\b")
REFINES = re.compile(r":\s*Refines\b|:\s*Refine\.Refines\b")
THEOREM = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?theorem\s+([A-Za-z_][\w'!?]*)\s*(.*)$", re.M)


def statements(src: str):
    """(name, statement-text) for each theorem — the text from the name to the `:=`."""
    out = []
    for m in THEOREM.finditer(src):
        tail = src[m.start(2): m.start(2) + 2000]
        cut = tail.find(":= by")
        if cut < 0:
            cut = tail.find(":=")
        out.append((m.group(1), tail[:cut if cut > 0 else 600]))
    return out


def semantic_coverage(ws: str, path: str) -> dict:
    """Ask Lean whether this design is inside the reference semantics, and if not, why.

    Not a caveat in prose: a whole-trace proof about a design `Module.simulate` does not model
    is a proof about something else.  `Module.coverageReasons` names the constructs.
    """
    if not ws:
        return {"checked": False, "why": "no --ws given; the verdict needs the Lake package"}
    src = open(path, errors="replace").read()
    ns = re.search(r"^namespace\s+(\S+)", src, re.M)
    if not ns:
        return {"checked": False, "why": "no namespace in the assembled file"}
    q = ns.group(1)
    probe = os.path.join(ws, "scratch", "coverage_probe.lean")
    os.makedirs(os.path.dirname(probe), exist_ok=True)
    # `Coverage` is not in the assembler's header, and an import cannot be appended -- inject it
    # after the file's own last import rather than probing from a separate module, which would
    # resolve through the .olean and reintroduce the staleness this repo already got caught by.
    lines = src.splitlines()
    last = max((i for i, l in enumerate(lines) if l.startswith("import ")), default=-1)
    lines.insert(last + 1, "import LeanRTL.Core.Coverage")
    # A hierarchy needs a DIFFERENT probe.  `Coverage.lean` has no `Parent` case -- no
    # `fullyCoveredb`, no `coverageReasons` -- and `Parent` has `insts`, not `regs`.  The probe
    # therefore failed to elaborate, returned `checked: False`, and the classifier silently fell
    # back to grepping for `regs := []`, which a Parent never contains.  `adder_32bit` -- which
    # proved arbitrary-length trace laws at the pins on a two-instance CLA -- was reported as
    # `cycle / reset:never`, understating exactly the axis the report leads with.
    is_parent = bool(re.search(r"def\s+impl\s*:\s*Parent", src))
    # Marked, and parsed by marker.  Reading out[0]/out[1] by POSITION breaks the moment the
    # design's own fragment contains an `#eval` or `#print axioms` of its own -- which a role P
    # mid-proof routinely does, and which then reported an axioms line as an out-of-model
    # construct.
    # Whether the design has state is a FACT ABOUT THE VALUE, so ask Lean.  Grepping the
    # assembled file for `regs := []` matched a theorem statement in one arm's PROOF and not in
    # the other's, so two authors of the same combinational design were labelled differently on
    # the axis that carries the claim.
    if is_parent:
        # A hierarchy is stateless iff no child holds a register and the parent names no clock.
        state = (f"({q}.impl.insts.all (fun i => i.child.regs.isEmpty "
                 f"&& i.child.clock.isNone) && {q}.impl.clock.isNone)")
        cov = ""          # Coverage.lean has no Parent case; report absent, do not fabricate
    else:
        state = f"({q}.impl.regs.isEmpty && {q}.impl.clock.isNone)"
        cov = (f"#eval (\"@@COV \" ++ toString ({q}.impl.fullyCoveredb : Bool))\n"
               f"#eval (\"@@ARST \" ++ toString ({q}.impl.coveredModuloArstb : Bool))\n"
               f"#eval (\"@@WHY \" ++ toString ({q}.impl.coverageReasons.map (·.describe)))\n")
    open(probe, "w").write("\n".join(lines) + "\n\n" + cov
                           + f"#eval (\"@@STATE \" ++ toString {state})\n")
    r = subprocess.run([os.path.expanduser("~/.elan/bin/lake"), "env", "lean",
                        os.path.relpath(probe, ws)], cwd=ws, capture_output=True, text=True)
    out = (r.stdout + r.stderr).strip().splitlines()
    os.remove(probe)
    cov = [l for l in out if "@@COV" in l]
    why = [l for l in out if "@@WHY" in l]
    st = [l for l in out if "@@STATE" in l]
    if r.returncode != 0 or (not cov and not st):
        return {"checked": False, "why": (r.stdout + r.stderr)[-300:]}
    stateless = (st[-1].split("@@STATE", 1)[1].strip().strip('"') == "true") if st else None
    if is_parent:
        # Statelessness IS answered for a hierarchy; the coverage verdict is not, and saying so
        # is different from saying the design is outside the semantics.
        return {"checked": True, "stateless": stateless, "hierarchy": True,
                "inside_reference_semantics": None,
                "out_of_model_constructs":
                    "not computed: Coverage.lean has no Parent case, so a hierarchy gets no "
                    "coverage verdict.  Absent, not negative."}
    inside = cov[-1].split("@@COV", 1)[1].strip().strip('"') == "true"
    reasons = why[-1].split("@@WHY", 1)[1].strip().strip('"') if why else "[]"
    # `fullyCoveredb = false` is NOT the same claim as "the whole-design theorems do not apply".
    # `Module.step`/`simulate` never read `Reg.asyncReset`, and `Module.eraseArst_simulate` proves
    # `m.simulate = m.eraseArst.simulate` outright -- so when the async reset is the ONLY reason
    # (`Module.coveredModuloArstb`), the whole-design class still applies, scoped to the
    # reset-inactive segment.  Reporting those designs as "out of the reference semantics" said the
    # framework change had not happened; twelve of ChipBench's fourteen async-reset designs are in
    # exactly this state.  The reset EDGE remains out of model, which is why `inside` stays false.
    arst = [l for l in out if "@@ARST" in l]
    modulo = arst[-1].split("@@ARST", 1)[1].strip().strip('"') == "true" if arst else False
    return {"checked": True, "inside_reference_semantics": inside,
            "covered_modulo_async_reset": modulo,
            "out_of_model_constructs": reasons, "stateless": stateless}


def classify(path: str, ws: str = "") -> dict:
    src = open(path, errors="replace").read()
    stmts = statements(src)
    body = "\n".join(s for _, s in stmts)
    sc = semantic_coverage(ws, path)
    if sc.get("stateless") is not None:
        combinational = sc["stateless"]          # evaluated
    else:                                         # no workspace: fall back, and say so
        combinational = bool(re.search(r"regs\s*:=\s*\[\]", src)) and \
            bool(re.search(r"clock\s*:=\s*none", src))

    has_l4 = [n for n, s in stmts if REFINES.search(":" + s.split(":", 1)[-1])] or \
             [n for n, s in stmts if REFINES.search(s)]
    has_l3 = [n for n, s in stmts if SIMREFINES.search(s)]
    # L5 is a claim, not a derivation: record what the author nominated.
    l5_claim = re.findall(r"(?m)^\s*/-!?\s*#+\s*L5\b.*$|L5 headline", src)

    if has_l4:
        level = "L4"
    elif has_l3:
        level = "L3"
    elif stmts:
        level = "L1"          # `combinational` says whether that is complete; it is not a rung
    else:
        level = None          # no theorems: nothing was proved, which is not a low level
    scope = {
        # `n/a (combinational)`, never `cycle`: on a design with no state one cycle IS the whole
        # behaviour, and a reader should not have to derive that from a separate boolean.  The
        # predecessor ladder made exactly that mistake and called it a rung of its own.
        "time": ("n/a (combinational)" if combinational
                 else "trace" if (has_l3 or has_l4) else "cycle"),
        # `Parent.combOut` is the hierarchy's observation function, exactly as `outputs?eval` is
        # the flat module's.  Recognising only the latter reported a Parent design that had
        # proved a law per output port as `observed=registers` -- the precise opposite of what it
        # proved, on the axis that carries the benchmark claim.
        "observed": ("pins" if (has_l4 or re.search(r"outputs\?eval|\bcombOut\b", body))
                     else "registers"),
        "reset": "n/a (combinational)" if combinational else ("any" if has_l4 else "never"),
    }
    return {
        "file": os.path.basename(path),
        "scope": scope,
        "combinational": combinational,
        "n_theorems": len(stmts),
        "simrefines_theorems": has_l3,
        "refines_theorems": has_l4,
        "semantic_headline_claimed": bool(l5_claim),
        "rests_on": {"in_reference_semantics": sc},
        "note": ("A semantic headline is claimed.  Whether a statement is meaningful is a "
                 "judgement and is not derived here." if l5_claim else ""),
    }


def main() -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("files", nargs="+")
    ap.add_argument("--ws", default="", help="workspace (Lake package) for the "
                                            "reference-semantics verdict")
    ap.add_argument("--json", action="store_true")
    a = ap.parse_args()
    out = [classify(f, a.ws) for f in a.files]
    if a.json:
        print(json.dumps(out, indent=1))
    else:
        for r in out:
            c, top = r["scope"], {"time": "trace", "observed": "pins", "reset": "any"}
            print(f"  {r['file']}")
            for axis, floor in (("time", "cycle"), ("observed", "registers"),
                                ("reset", "never")):
                got = c[axis]
                if got.startswith("n/a"):
                    line, mark = f"{got:<26}", "-"
                else:
                    line = f"{floor} --> {top[axis]}".ljust(26)
                    mark = "reached" if got == top[axis] else f"stops at {got}"
                print(f"    scope     {axis:<9} {line}{mark}")
            sc = r["rests_on"]["in_reference_semantics"]
            if sc.get("checked"):
                ok = sc["inside_reference_semantics"]
                print(f"    rests on  inside the reference semantics: "
                      f"{'yes' if ok else 'NO'}"
                      + ("" if ok else f"  out of model: {sc['out_of_model_constructs']}"))
            else:
                print(f"    rests on  reference semantics NOT CHECKED "
                      f"({sc.get('why', '')[:50]})")
            print(f"              other premises are constant across designs; "
                  f"see docs/TRUST_BASE.md")
            print(f"    theorems  {r['n_theorems']}"
                  + ("   (a semantic headline is claimed, not derived)"
                     if r["semantic_headline_claimed"] else ""))
    return 0


if __name__ == "__main__":
    sys.exit(main())
