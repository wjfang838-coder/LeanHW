#!/usr/bin/env python3
"""The certification gates: does this workspace's proof-carrying claim actually hold?

    python3 -m leanrtl.verify --ws <workspace> --key <design> [--profile <name>]

Writes `<ws>/verify.json`.  Nothing downstream may report a design as passing without this
file, because everything else in the pipeline reports what the *author* believes.

## Why this is a separate step

Profiles declare gates — `zero_sorry`, `axiom_clean`, `undriven_nets` — and for a long time
nothing enforced them.  `bb.py build` *warns* about `sorry` and `bb.py emit` does not check at
all, so a design could carry an admitted proof all the way to a scored artifact.  A declared
gate that nothing runs is worse than no gate: it is a claim in a config file that a reader will
believe.

The gates:

  * **builds** — the assembled design elaborates.  A verdict about an artifact that does not
    compile is a verdict about nothing.
  * **proves_impl** — at least one theorem's STATEMENT mentions the implementation.  A design
    whose proof fragment held one scratch `example` and no theorem passed every other gate.
  * **zero_sorry** — `sorry` / `admit` / `sorryAx` / user `axiom` in the assembled design.  A
    proof with a hole proves nothing, and the hole is invisible in the emitted Verilog.
  * **axiom_clean** — `#print axioms` over the design's theorems.  Lean's standard three
    (`propext`, `Classical.choice`, `Quot.sound`) are fine; anything else is a hole that
    `scan_sorry` cannot see, because a user axiom in an *imported* file is not in this file.
    One further family is admitted, conditionally, and `NATIVE_LRAT` below says why.
  * **undriven_nets** — an undriven wire in the emitted netlist.  This one is not a proof
    property at all: a compiler bug silently allocated a floating net while `build`, `check`,
    `sim` and `emit` all stayed green, so the artifact being scored was not the circuit that
    was proved.  Three authors found it independently before anyone believed it.

Plus `proof_scope`, which is DESCRIPTIVE and gates nothing: it lists what the proofs do not
reach.  A one-word summary of a proof's coverage is the thing this method exists to avoid.

## One design per workspace

The upstream version of this file took a `manifest.json` and an `--only` list, because a
workspace there held fifty designs.  Here a slot holds one (`common/workspace.py` says why), so
`--key` names it and there is no merge logic: a re-check rewrites the file it is about.
"""
from __future__ import annotations

import argparse
import hashlib
import json
import os
import re
import signal
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}

# `bv_decide`'s LRAT-reflection axiom, admitted CONDITIONALLY — see `check_axioms`.
#
# `Lean/Meta/Native.lean:36 nativeEqTrue` compiles a closed `Bool` term, runs it natively, and
# if it evaluates to `true` asserts `<term> = true` as an axiom named `<thm>._native.<tac>.ax_N_M`.
# The kernel never checks that equation.  For `bv_decide` the term is
# `verifyBVExpr <bitblasted goal> <CaDiCaL's LRAT certificate>`
# (`Lean/Elab/Tactic/BVDecide/Frontend/BVDecide.lean:288-290`), so what is being asserted is
# "the LRAT checker accepted this certificate".  Bitblasting and the checker's correctness
# theorem are both kernel-checked, and CaDiCaL itself is not trusted at all — it has to produce
# a certificate.  The single unchecked step is the checker's EXECUTION, which is native.  The
# trusted base therefore grows by Lean's compiler, its runtime, and the C compiler.
#
# This is a different kind of thing from `sorryAx`, which is why it does not share its verdict:
# the axiom is one closed decidable equation that the kernel could in principle reduce (just not
# in feasible time), and nothing about the design under test appears in it — reflection has
# already happened, so the evaluated term mentions only `bv_decide`'s own constants.
#
# It is admitted rather than banned because banning it is not "prove it properly": v4.29's
# `LratCert.toReflectionProof` calls `nativeEqTrue` unconditionally, with no option to check the
# certificate in the kernel, so rejecting the axiom is equivalent to forbidding the tactic.
#
# The condition is the one known way this class of axiom goes wrong.  `@[implemented_by]` and
# `@[extern]` make native execution diverge from the logical definition, and then `<term> = true`
# can be asserted of a term that is logically false.  That is checkable, so it is checked, and
# the admission is void where it fails.  Both readings are recorded either way: `pass` admits
# this family, `pass_kernel_only` does not.
NATIVE_LRAT = re.compile(r"\._native\.bv_decide\.ax_")
_HIJACK = re.compile(r"@\[[^\]]*\b(?:implemented_by|extern)\b")

_framework_hijacks: list[str] | None = None


def framework_hijacks() -> list[str]:
    """`@[implemented_by]` / `@[extern]` anywhere in the framework the design imports.

    Scanning only the design's own source would miss the interesting case: the design is clean
    and the override sits in a shared file it imports.  Computed once per process — this is a
    property of the checkout, not of any one design.
    """
    global _framework_hijacks
    if _framework_hijacks is None:
        found = []
        for base, _, files in os.walk(os.path.join(ROOT, "framework")):
            for f in files:
                if not f.endswith(".lean"):
                    continue
                p = os.path.join(base, f)
                text = open(p, errors="replace").read()
                for m in _HIJACK.finditer(re.sub(r"--[^\n]*", "", text)):
                    found.append(f"{os.path.relpath(p, ROOT)}: {m.group(0)}")
        _framework_hijacks = sorted(found)
    return _framework_hijacks


# The scaffold's section-1 marker, verbatim from `leanrtl/stage.py`.  It sits in the docstring of
# the placeholder implementation, which is the one section every arm's author must replace, so it
# is the only one of the scaffold's four markers whose survival means "unauthored".
SCAFFOLD_IMPL = "A 4-bit counter, here only so the scaffold compiles"


def is_scaffold(ws: str, key: str) -> bool:
    """Is this design's Lean file still the scaffold's untouched placeholder?

    `stage.py` writes a stub so the registry resolves and the template can be built warm before
    any author sees it.  The stub is a 4-bit counter carrying `REPLACE ME`, and it is a hazard
    precisely because it is well-formed: it elaborates, holds no `sorry`, and drives its nets, so
    every gate that does not read a theorem passes on it.  Graded, an unauthored design comes out
    looking like an author who wrote a compiling design and forgot to prove anything.

    The evidence is the marker in SECTION 1, and only that one.  The test used to be "the string
    `REPLACE ME` appears anywhere in the file", which is a different question: the scaffold writes
    the marker into all four sections, an author replaces the sections they author, and a marker
    left behind in a section they were not asked to author says nothing about whether they worked.
    On one ablation it said the opposite of the truth on 42 of 50 designs — that arm leaves
    section 2 EMPTY by instruction, so its section-2 marker survives on every design its author
    completed, and 42 files of 500-650 lines carrying 33-58 theorems apiece were skipped as
    "never authored" and came back unverified.  The arm's gate column read 6 of 50.

    Section 1 is the implementation, every arm authors it, and the scaffold's own impl is the
    4-bit counter whose docstring holds the marker.  So its survival means the author never
    replaced the implementation, which is exactly what "still the stub" means.

    A file with no `## 1.` section marker is not treated as a scaffold: that is a malformed
    design, which is a real finding and must not be skipped.
    """
    p = assembled(ws, key)
    if not p:
        return False
    src = open(p, errors="replace").read()
    return SCAFFOLD_IMPL in src and re.search(r"/-!\s*##\s*1\.", src) is not None


def assembled(ws: str, key: str) -> str | None:
    """The assembled design file, found by its `-- @blind <key>` header line.

    Found by the header rather than by a name computed from the key, because the Lean module
    name is CamelCase and the key is not, and two functions that both compute that mapping will
    eventually disagree about one design.  The file says what it is.
    """
    d = os.path.join(ws, "LeanRTL", "Blind")
    if not os.path.isdir(d):
        return None
    for f in sorted(os.listdir(d)):
        if f.endswith(".lean"):
            p = os.path.join(d, f)
            try:
                head = open(p, errors="replace").readline().strip()
            except OSError:
                continue
            if re.match(rf"--\s*@blind\s+{re.escape(key)}\s*$", head):
                return p
    return None


BUILD_TIMEOUT = int(os.environ.get("LEANSILICON_VERIFY_BUILD_TIMEOUT", "900"))
LAKE = os.path.expanduser("~/.elan/bin/lake")


def run_lean(argv: list, cwd: str, timeout: int | None = None):
    """`lake env lean ...`, bounded.  Returns None if it did not finish in time.

    `subprocess.run(timeout=)` kills the direct child only, and the direct child is `lake`; the
    `lean` process it spawned keeps the core.  So the child gets its own session and the whole
    group is signalled.
    """
    t = BUILD_TIMEOUT if timeout is None else timeout
    p = subprocess.Popen(argv, cwd=cwd, stdout=subprocess.PIPE, stderr=subprocess.PIPE,
                         text=True, start_new_session=True)
    try:
        o, e = p.communicate(timeout=t)
    except subprocess.TimeoutExpired:
        try:
            os.killpg(os.getpgid(p.pid), signal.SIGKILL)
        except (ProcessLookupError, PermissionError):
            p.kill()
        p.communicate()
        return None
    return subprocess.CompletedProcess(argv, p.returncode, o, e)


def check_builds(ws: str, path: str) -> dict:
    """Does the assembled design elaborate at all?

    Everything below this is a verdict about the artifact, and a verdict about an artifact that
    does not compile is a verdict about nothing.  Learned the hard way: a design was judged while
    its proof role was still iterating -- `zero_sorry` said clean (no `sorry` token in the
    source), `undriven_nets` said ok, and only the axiom probe dissented, with `sorryAx`, because
    an `omega` that ERRORS leaves the theorem proved by `sorryAx` while the source contains no
    `sorry` at all.

    The emitted `.v` existing is NOT a completion signal: an author legitimately runs `emit` to
    validate a hierarchy long before the proofs exist.
    """
    r = run_lean([LAKE, "env", "lean", os.path.relpath(path, ws)], ws)
    if r is None:
        # An elaboration that does not terminate is a FAILED build with a nameable cause, not a
        # stalled run.  Seen on a one-shot ablation, whose authors get no build feedback and so
        # never learn that a `decide` over a 32-bit vector does not come back: one design held
        # this gate for over an hour with no output and would have held it indefinitely.
        return {"pass": False, "n_errors": 0, "timeout_s": BUILD_TIMEOUT,
                "detail": f"elaboration did not terminate within {BUILD_TIMEOUT}s"}
    out = r.stdout + r.stderr
    errs = [l for l in out.splitlines() if "error" in l.lower()]
    return {"pass": r.returncode == 0, "n_errors": len(errs),
            "detail": "\n".join(errs[:5])[:800]}


IMPL_DEF = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                      r"(?:def|abbrev)\s+(impl[A-Za-z0-9_'!?]*)", re.M)
# `def impl : Module := gen 0` — the head symbol on the right of an `impl*` definition.  See
# `generator_of` for why the gate follows it.
IMPL_ALIAS = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                        r"(?:def|abbrev)\s+impl[A-Za-z0-9_'!?]*\s*(?::[^:=]*)?:=\s*"
                        r"([A-Za-z_][\w'!?]*)", re.M)
ANY_DEF = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*"
                     r"(?:def|abbrev)\s+([A-Za-z_][\w'!?]*)", re.M)


def impl_names(raw: str) -> tuple[list[str], str]:
    """The implementation names THIS file declares, read out of its own section 1.

    `impl` alone is not enough.  One design names its top module `implTop` and keeps
    `def impl : Parent := implTop` only as an alias no theorem mentions; every one of its
    theorems — including `refines : Refines (flattenParentSeq implTop) ...` — states its claim
    about `implTop`, and `\\bimpl\\b` cannot match that, because `T` is a word character.  The
    gate scored the file as carrying no proof while it carried the strongest one in the run.

    The names are taken from section 1 (`/-! ## 1.` up to `/-! ## 2.`) so that they are the
    implementation's, and are restricted to the `impl` PREFIX rather than admitting every `def`
    the section declares.  Admitting all of them is too loose in a way that showed up on real
    files: one design declares `specN` and `specQ` inside section 1, and a gate that accepted
    those would count a specification theorem as a proof about the design — the exact hole this
    check exists to close.  The prefix, by contrast, is implementation-side by construction, and
    restricting to names actually DECLARED means a stray `implies` in a statement cannot match.
    """
    m1 = re.search(r"/-!\s*##\s*1\.", raw)
    if not m1:
        return ["impl"], "no `## 1.` section marker — fell back to `impl` alone"
    m2 = re.search(r"/-!\s*##\s*2\.", raw)
    end = m2.start() if m2 and m2.start() > m1.end() else len(raw)
    body = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", raw[m1.end():end], flags=re.S))
    names = {m.group(1) for m in IMPL_DEF.finditer(body)} | {"impl"}
    gens = generator_of(body, names)
    return sorted(names | gens), (
        f"section 1 declares {', '.join('`' + n + '`' for n in sorted(names))}"
        + (f"; {', '.join('`' + g + '`' for g in sorted(gens))} is the generator it is an "
           "instance of" if gens else ""))


def generator_of(body: str, impls: set) -> set:
    """The generator an `impl` is a one-instance alias OF, when it is one.

    ## Why the gate follows the alias

    `check_proves` asks whether any theorem states something about the design.  It looks for the
    implementation's own name, which is right for a design that IS a module and wrong for a
    design that is a *generator* — the F2 shape, where the module is `gen n` for a parameter `n`
    and `def impl : Module := gen 0` exists only so the non-parametric commands have something to
    run.  Such a file proves `∀ (a : Nat), P (gen a)`; nothing mentions `impl`; and the gate read
    that as "carries no proof about the design".

    That verdict is not merely unlucky, it is backwards.  `∀ a, P (gen a)` **entails** `P impl`,
    because `impl` is `gen 0` by definition — the proof is strictly STRONGER than the one the
    gate was looking for, and the gate failed it for being so.  One real case: 13 theorems, every
    one quantified over both parameter values rather than fixed at the emitted one.

    So: when an `impl*` definition is a bare application of a name that section 1 also declares,
    that name is admitted too.  The conditions are what keep this from becoming a licence:

      * the alias must be an `impl*` DEFINITION, not any definition;
      * the head must be a `def`/`abbrev` **declared in section 1 of this same file**, so a
        theorem about some imported combinator still does not count;
      * nothing else is admitted — the specification side is untouched, and a section-1 `specN`
        remains outside, which is the hole `impl_names` was narrowed to close.

    Recorded before the run, not after: this is a change to what the probe accepts, and deciding
    it once a design's verdict is on the table is how a gate becomes an argument.
    """
    declared = {m.group(1) for m in ANY_DEF.finditer(body)}
    return {m.group(1) for m in IMPL_ALIAS.finditer(body)
            if m.group(1) in declared and m.group(1) not in impls}


def check_proves(path: str) -> dict:
    """Does the design's proof section prove anything ABOUT THE DESIGN?

    Nothing checked this, and the hole is wide: a design whose proof fragment held one scratch
    `example` and no theorem at all passed every gate.  `builds` passed (the scratch compiled),
    `zero_sorry` passed (no `sorry` token), `undriven_nets` passed (the implementation author had
    emitted), and `axiom_clean` passed because it counts theorems in the ASSEMBLED file — which
    includes the specification's own theorems, all of them clean and none of them about the
    implementation.

    So: count theorems whose STATEMENT mentions one of the implementation names the file itself
    declares (see `impl_names`).  A specification theorem cannot; a proof about the design cannot
    avoid it.  Zero means the proof-carrying arm carried no proof.

    `lemma` counts alongside `theorem`.  The two differ in Lean by nothing that bears on this
    question — a `lemma` whose statement is about the implementation is a proof about the
    implementation — and admitting only one spelling is the same class of defect as admitting
    only one spelling of `impl`.
    """
    raw = open(path, errors="replace").read()
    names, how = impl_names(raw)
    probe = re.compile("|".join(rf"\b{re.escape(n)}\b" for n in names))
    src = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", raw, flags=re.S))
    about = []
    for m in re.finditer(r"^\s*(?:@\[[^\]]*\]\s*)?(?:theorem|lemma)\s+([A-Za-z_][\w'!?]*)",
                         src, re.M):
        tail = src[m.end(): m.end() + 3000]
        cut = tail.find(":= by")
        stmt = tail[:cut if cut > 0 else min(len(tail), 800)]
        if probe.search(stmt):
            about.append(m.group(1))
    return {"pass": bool(about), "n_about_impl": len(about), "theorems": about[:8],
            "impl_names": names,
            "detail": how if about else
                      f"no theorem in this file states anything about the implementation "
                      f"({how}) — the proof section is empty or scratch, and the other gates "
                      f"cannot see that"}


def check_sorry(ws: str, path: str) -> dict:
    """`scan_sorry.py` over the assembled file.

    Run from the workspace's own `scripts/` rather than from the repository, so what is enforced
    is the checker the author was building against.  A gate the author cannot run locally is a
    gate that fails at the end of a session for a reason nobody could have seen coming.
    """
    scan = os.path.join(ws, "scripts", "scan_sorry.py")
    if not os.path.isfile(scan):
        scan = os.path.join(os.path.dirname(os.path.abspath(__file__)), "authoring",
                            "scan_sorry.py")
    r = subprocess.run([sys.executable, scan, path], capture_output=True, text=True)
    return {"pass": r.returncode == 0, "detail": (r.stdout + r.stderr).strip()[:600]}


def check_axioms(ws: str, path: str, key: str) -> dict:
    """`#print axioms` over every theorem the design declares, elaborated FROM SOURCE.

    The obvious implementation — `import LeanRTL.Blind.<Camel>` in a probe file — resolves
    through the compiled `.olean`, and `bb.py build` runs `lake env lean` on the assembled
    source without writing one.  The gate then reports on whatever was last compiled.  One author
    hit the harmless direction: the gate named a tactic the source provably no longer contained.
    The dangerous direction is the same bug mirrored — a stale clean `.olean` passing a design
    whose current source has an unchecked axiom.

    `lake build` does not fix it: the assembler rewrites the assembled file on every command,
    so its mtime advances while its content does not, and Lake correctly declines to rebuild.
    Comparing timestamps therefore reports a false staleness (verified: `lake build` rc=0, and
    the `.olean` is still older than the file).

    So the probe does not import the design at all.  It is the design's own source text with
    the `#print axioms` commands appended, elaborated in one process.  What is checked is
    exactly what is on disk, and the sha of that text is recorded in the verdict.
    """
    src = open(path, errors="replace").read()
    src_sha = hashlib.sha256(src.encode()).hexdigest()[:12]
    # Strip comments BEFORE looking for theorems.  Without this, a docstring sentence like
    # "the theorem quantifies over all reset streams" is read as a declaration named
    # `quantifies`, the probe reports it unknown, and the "silence is not a pass" rule then
    # fails a design whose proofs are in fact clean.  A false alarm costs an author a round.
    bare = re.sub(r"--[^\n]*", "", re.sub(r"/-.*?-/", "", src, flags=re.S))
    # Qualify each theorem with the namespace path it is ACTUALLY in, by walking
    # `namespace` / `end` as they appear.  Assuming the file's first namespace put an `ext'`
    # declared inside a nested `namespace SpecState` at the wrong path, so it produced no
    # `#print axioms` line and was recorded as uncovered.  The design was clean.
    # `end` closes a `section` as well as a `namespace`.  Tracking only `namespace` under-flowed
    # the stack on the first `end Foo` of a section, after which every later theorem was
    # qualified with an EMPTY path -- the probe emitted `#print axioms freeTrace_phase`, Lean
    # said `Unknown constant`, and the gate failed a clean design.  So push for both and let
    # only namespaces contribute to the path.
    stack: list[str | None] = []
    thms: list[tuple[str, str]] = []          # (fully-qualified, short)
    for line in bare.splitlines():
        m = re.match(r"\s*namespace\s+(\S+)", line)
        if m:
            stack.append(m.group(1))
            continue
        if re.match(r"\s*section\b", line):
            stack.append(None)                # contributes nothing to the name path
            continue
        if re.match(r"\s*end\b", line) and stack:
            stack.pop()
            continue
        m = re.match(r"\s*(?:@\[[^\]]*\]\s*)?theorem\s+([A-Za-z_][\w'!?]*)", line)
        if m:
            thms.append((".".join([x for x in stack if x] + [m.group(1)]), m.group(1)))
    if not thms:
        return {"pass": False, "detail": "no theorems declared — nothing was proved",
                "n_theorems": 0, "source_sha": src_sha}
    probe = os.path.join(ws, "scratch", f"{key}.axioms.lean")
    os.makedirs(os.path.dirname(probe), exist_ok=True)
    open(probe, "w").write(src + "\n\n"
                           + "\n".join(f"#print axioms {q}" for q, _ in thms) + "\n")
    r = run_lean([LAKE, "env", "lean", os.path.relpath(probe, ws)], ws)
    if r is None:
        return {"pass": False, "verdict": "probe_timeout", "n_theorems": len(thms),
                "source_sha": src_sha, "extra_axioms": [],
                "detail": f"the axiom probe did not elaborate within {BUILD_TIMEOUT}s — the "
                          f"same file `builds` runs, plus one `#print axioms` per theorem"}
    out = r.stdout + r.stderr
    # Match by NAME, not by counting lines.  A design's own fragment may already contain
    # `#print axioms` -- a proof author deliberately leaves them in so every build re-checks --
    # and the probe then appends its own, so line counts double and the arithmetic goes negative.
    # What is actually being asked is whether every declared theorem was covered, which is a
    # question about a SET.
    # `[^']+` cannot match a name that ENDS in a prime.  Lean prints
    #     'LeanRTL.Blind.JCCounter.Q_next_law'' depends on axioms: [propext, Quot.sound]
    # for `Q_next_law'`, i.e. two consecutive quotes, and a character class excluding `'` stops
    # at the first of them and then fails on the second.  The line matched nothing, the theorem
    # was recorded as UNREPORTED, and the gate failed the design -- with `extra_axioms: []`,
    # i.e. having found no bad axiom at all.  Twelve of fifty designs failed this way, every one
    # of them clean.  Lazy-match up to the literal suffix instead.
    per = re.findall(r"'(.+?)' depends on axioms: \[([^\]]*)\]", out)
    free = re.findall(r"'(.+?)' does not depend on any axioms", out)
    extra = sorted({a.strip() for _, grp in per for a in grp.split(",") if a.strip()}
                   - STD_AXIOMS)
    covered = {n.split(".")[-1] for n, _ in per} | {n.split(".")[-1] for n in free}
    missing = sorted({short for _, short in thms} - covered)
    reported, none_form = per, len(free)
    unreported = len(missing)
    # TWO different verdicts, and conflating them is how twelve clean designs were reported as
    # having unchecked axioms:
    #   extra_axioms  -- a forbidden axiom WAS found.  A statement about the design.
    #   unreported    -- a declared theorem produced no `#print axioms` line.  A statement about
    #                    this checker: either its name regex and Lean's output disagree, or the
    #                    theorem does not live under the file's first namespace so the probe's
    #                    qualified name does not resolve.
    # Silence still is not a pass -- an uncovered theorem is uncertified -- so the gate fails on
    # either.  But the reason is now named, and `verdict` says which.
    unresolved = bool(re.search(r"unknown (identifier|constant)", out))
    # Partition before judging.  `native_lrat` is admitted only while the hijack precondition
    # holds; `forbidden` is everything the gate has always rejected.  Two verdicts come out:
    # `pass` (the published reading) and `pass_kernel_only` (nothing outside STD_AXIOMS).  An arm
    # that never invokes `bv_decide` has `native_lrat == []`, so both readings and the recorded
    # verdict string are what they would be without this partition.
    native_lrat = [a for a in extra if NATIVE_LRAT.search(a)]
    forbidden = [a for a in extra if not NATIVE_LRAT.search(a)]
    hijacks = ([f"{os.path.basename(path)}: {m.group(0)}"
                for m in _HIJACK.finditer(bare)] + framework_hijacks()) if native_lrat else []
    admitted = bool(native_lrat) and not hijacks
    ok = r.returncode == 0 and not forbidden and not hijacks and unreported == 0
    ok_kernel_only = r.returncode == 0 and not extra and unreported == 0
    verdict = ("clean" if ok and not native_lrat
               else "clean (rests on native LRAT)" if ok
               else "FORBIDDEN AXIOM" if forbidden
               else "native LRAT axiom with an @[implemented_by]/@[extern] in scope" if hijacks
               else "checker could not resolve some theorem names" if unresolved
               else "some theorems produced no #print axioms line" if unreported
               else "the probe did not elaborate")

    # WHICH SECTION declared the offending theorem.  The gate deliberately scans the whole
    # assembled file -- the specification is part of the trusted artifact, since the
    # implementation is proved against it, so a spec property resting on an unchecked SAT result
    # makes "the prose property holds of the spec" SAT-certified rather than kernel-checked.
    # But blaming the proof author for the spec author's tactic is a different error, so say
    # where.
    sections = []
    for mk, name in ((r"/-!\s*##\s*1\.", "impl"), (r"/-!\s*##\s*2\.", "spec"),
                     (r"/-!\s*##\s*3\.", "proof")):
        m2 = re.search(mk, src)
        sections.append((m2.start() if m2 else -1, name))
    sections = sorted((p_, n) for p_, n in sections if p_ >= 0)

    def section_of(thm):
        d = re.search(rf"^\s*(?:@\[[^\]]*\]\s*)?theorem\s+{re.escape(thm)}\b", src, re.M)
        if not d:
            return "?"
        here = "?"
        for p_, n in sections:
            if p_ <= d.start():
                here = n
        return here

    blame = {}
    for ax in extra:
        owner = ax.split("._native.")[0].split(".")[-1] if "._native." in ax else ax
        blame[ax] = section_of(owner)
    return {"pass": ok, "pass_kernel_only": ok_kernel_only, "verdict": verdict,
            "n_theorems": len(thms), "n_reported": len(reported),
            "unreported": missing[:8],
            "blame": blame,
            "rests_on_native_lrat": {"admitted": admitted,
                                     "n_axioms": len(native_lrat),
                                     "axioms": native_lrat[:8],
                                     "hijacks": hijacks[:8]},
            "n_axiom_free": none_form,
            "extra_axioms": extra, "source_sha": src_sha,
            "detail": out.strip()[-800:] if not ok else ""}


def check_undriven(ws: str, key: str) -> dict:
    v = os.path.join(ws, "out", key + ".v")
    if not os.path.isfile(v):
        # NOT the same finding as a floating net.  Reporting "undriven_nets FAIL" for a design
        # whose author has not reached `emit` reads as a netlist defect and is a different fact
        # entirely -- it means the run is unfinished, and a verdict on it is premature.
        return {"pass": False, "not_emitted": True,
                "detail": "no emitted Verilog — the design has not reached `emit`; "
                          "verifying it now is premature, not a netlist defect"}
    r = subprocess.run([sys.executable, os.path.join(ROOT, "audit", "lint_undriven.py"),
                        v, "--strict"], capture_output=True, text=True)
    return {"pass": r.returncode == 0, "detail": (r.stdout + r.stderr).strip()[:600]}


def check_asset_leak(ws: str, key: str) -> dict:
    """Workspace-level: does the shared material this author reads name any OTHER design?

    Declared in profiles and run by nothing, and that is exactly the gap a second isolation
    breach went through -- a shared proof library named three designs and gave two of them their
    behavioural reading, while every per-design gate stayed green.  A declared gate nothing runs
    is a claim in a config file.

    Exit 2 from the scanner means "no design keys were found", which is NOT a pass and is not
    reported as one: with no benchmark installed there is no population to leak, and a gate with
    nothing to check must say so rather than go green.
    """
    r = subprocess.run([sys.executable, os.path.join(ROOT, "audit", "asset_leak.py"),
                        "--ws", ws, "--key", key, "--strict"], capture_output=True, text=True)
    out = (r.stdout + r.stderr)
    new = [l for l in out.splitlines() if l.strip().startswith("NEW LEAK")]
    if r.returncode == 2:
        return {"pass": False, "checked": False, "n_new": 0,
                "detail": "no design keys available — the leak gate had nothing to check, "
                          "which is not a pass"}
    return {"pass": r.returncode == 0 and not new, "checked": True,
            "n_new": len(new), "detail": new[:20]}


def verify(ws: str, key: str, gates: dict) -> dict:
    """Every gate this profile declares, over one design.  Returns the verdict record."""
    res: dict = {"key": key}
    if is_scaffold(ws, key):
        # The workspace ships a `REPLACE ME` scaffold so the registry resolves and the template
        # builds warm.  It is a 4-bit counter: it ELABORATES, it holds no `sorry`, and it states
        # no theorem — so grading it produces `builds=ok`, `zero_sorry=ok`, `proves_impl=FAIL`,
        # which is a gate failure attributed to an author that never ran.  A scaffold is a HOLE,
        # and a hole is what it should look like downstream.
        return {"key": key, "scaffold": True, "assembled": True, "all_pass": False,
                "detail": "still the scaffold's `REPLACE ME` stub — not authored, so not "
                          "verified; this is a hole, not a gate failure"}
    path = assembled(ws, key)
    res["assembled"] = bool(path)
    if path:
        res["source"] = os.path.relpath(path, ws)
        res["builds"] = check_builds(ws, path)
        if not res["builds"]["pass"]:
            # Do not spend a Lean run per gate on a design that does not compile, and do not
            # record verdicts that would read as findings about the work.
            res["all_pass"] = False
            res["detail"] = (f"the assembled design does not elaborate "
                             f"({res['builds']['n_errors']} error(s)) — no verdict")
            return res
        res["proves_impl"] = check_proves(path)
        sys.path.insert(0, os.path.join(ROOT, "audit"))
        import proof_scope
        res["proof_scope"] = proof_scope.classify(path, ws)
        if gates.get("zero_sorry"):
            res["zero_sorry"] = check_sorry(ws, path)
        if gates.get("axiom_clean"):
            res["axiom_clean"] = check_axioms(ws, path, key)
    if gates.get("undriven_nets"):
        res["undriven_nets"] = check_undriven(ws, key)
    if gates.get("asset_leak"):
        res["asset_leak"] = check_asset_leak(ws, key)
    # `proof_scope` is DESCRIPTIVE, not a gate — a correct L1 design is not a failure.  It has no
    # `pass` key, so this comprehension leaves it out on its own rather than by an exclusion list
    # that would have to be maintained.
    checks = [v for k, v in res.items() if isinstance(v, dict) and "pass" in v]
    # An assembled Lean file is required only by the gates that READ one.  `bool(path)` was an
    # unconditional conjunct here, and a control arm — whose profile declares exactly
    # `undriven_nets` and `asset_leak`, both of which passed for all fifty of its designs —
    # scored 0/50, because direct-Verilog authoring produces no Lean file to assemble.  That is
    # not a gate failing, it is a gate that does not apply being counted as one, and it would
    # have gone into the comparison as "the control passes no gates".
    needs_lean = any(gates.get(g) for g in ("zero_sorry", "axiom_clean", "builds",
                                            "proves_impl"))
    res["all_pass"] = (bool(path) or not needs_lean) and all(c.get("pass") for c in checks)
    return res


def line(res: dict) -> str:
    """One line, naming WHY rather than just which gate."""
    key = res.get("key", "?")
    if res.get("scaffold"):
        return f"{key:28} SCAFFOLD     {res.get('detail', '')}"
    if not res.get("all_pass") and "builds" in res and not res["builds"]["pass"]:
        return f"{key:28} INCOMPLETE   {res.get('detail', '')}"
    marks = " ".join(f"{k}={'ok' if v.get('pass') else 'FAIL'}"
                     for k, v in res.items() if isinstance(v, dict) and "pass" in v)
    # Name WHY axiom_clean failed.  "axiom_clean=FAIL" reads as "this design has an unchecked
    # axiom"; on twelve designs it meant "the checker could not match a theorem name".
    av = res.get("axiom_clean") or {}
    if av and not av.get("pass"):
        marks += f"  [{av.get('verdict', '?')}]"
    cv = (res.get("proof_scope") or {}).get("scope", {})
    sc = (res.get("proof_scope") or {}).get("rests_on", {}).get("in_reference_semantics", {})
    marks += (f"  scope[time={cv.get('time', '?')} obs={cv.get('observed', '?')} "
              f"reset={cv.get('reset', '?')}]")
    if sc.get("checked") and not sc.get("inside_reference_semantics"):
        # An async reset alone does NOT put a design outside the whole-design class -- see
        # `Module.eraseArst_simulate` / `coveredModuloArst_moduleChecks`.  Only the reset EDGE is
        # out of model, so label it as the narrower thing it is.
        marks += ("  IN-MODEL/mod-arst" if sc.get("covered_modulo_async_reset")
                  else "  OUT-OF-MODEL")
    return f"{key:28} {'PASS' if res['all_pass'] else 'FAIL'}   {marks}"


def reassemble(ws: str, key: str) -> bool:
    """Regenerate `LeanRTL/Blind/<Camel>.lean` from the fragments before judging it.

    The canonical assembled file is rewritten only by a FULL-assembly command; an author running
    `build --frag proof` assembles to a private scratch path instead.  So after an author edits a
    fragment the canonical file is stale, and every verdict below would be about the previous
    version -- which is exactly how a repaired specification kept reporting the axiom it no
    longer contained.

    A workspace with no fragments has nothing to regenerate: the design file IS the source, and
    re-running the assembler would overwrite the author's work with a stub.
    """
    if not os.path.isdir(os.path.join(ws, "frags", key)):
        return True
    asm = os.path.join(ws, "scripts", "asm_f.py")
    if not os.path.isfile(asm):
        return False
    r = subprocess.run([sys.executable, asm, key], cwd=ws, capture_output=True, text=True)
    return r.returncode == 0


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ws", required=True)
    ap.add_argument("--key", required=True)
    ap.add_argument("--profile", help="which gates to run.  Without it every gate runs, which "
                                     "is the stricter reading and the right default for a "
                                     "one-off check.")
    a = ap.parse_args(argv)
    ws = os.path.abspath(os.path.expanduser(a.ws))
    if a.profile:
        from common import profiles
        prof = profiles.load(a.profile)
        gates, pname = profiles.gates(prof), prof["name"]
    else:
        gates = {g: True for g in ("builds", "proves_impl", "zero_sorry", "axiom_clean",
                                   "undriven_nets", "asset_leak")}
        pname = None

    # Assemble FIRST, then ask whether what came out is still the stub.  The check must read the
    # bytes that are about to be graded, not the bytes that happened to be on disk: an author
    # whose fragments have just landed still has the previous cycle's stub sitting in `Blind/`,
    # and testing before assembly would skip a design that was in fact authored.
    if not reassemble(ws, a.key):
        rec = {"key": a.key, "assembled": False, "all_pass": False,
               "detail": "could not assemble from the current fragments"}
        print(f"{a.key:28} INCOMPLETE   {rec['detail']}")
    else:
        rec = verify(ws, a.key, gates)
        print(line(rec))

    if gates.get("undriven_nets") and not os.path.isfile(os.path.join(ws, "out", a.key + ".v")):
        print("\n  PREMATURE: the design has not been emitted yet — this verdict is about an "
              "unfinished run, not about the work")
    al = rec.get("asset_leak") or {}
    if al and not al.get("checked", True):
        print(f"\n  asset_leak: {al['detail']}")

    vp = os.path.join(ws, "verify.json")
    json.dump({"profile": pname, "gates": gates, "key": a.key, "design": rec},
              open(vp, "w"), indent=1)
    print(f"\nverify: {'PASS' if rec.get('all_pass') else 'FAIL'} -> "
          f"{os.path.relpath(vp, ROOT) if vp.startswith(ROOT) else vp}")
    return 0 if rec.get("all_pass") else 3


if __name__ == "__main__":
    sys.exit(main())
