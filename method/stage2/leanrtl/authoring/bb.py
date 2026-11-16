#!/usr/bin/env python3
"""bb — the ONLY build/verify entry point for blind-workspace authoring agents.

    python3 scripts/bb.py <key> build     type-check your design file (lake env lean)
    python3 scripts/bb.py <key> audit     scan your file for sorry/admit/axiom
    python3 scripts/bb.py <key> check     leanrtl check <key>   (well-formedness lint)
    python3 scripts/bb.py <key> sim       leanrtl sim <key>     (stdin: `name=value …` cycles)
    python3 scripts/bb.py <key> cosim     Lean-sim vs iverilog on the emitted Verilog (random vectors)
    python3 scripts/bb.py <key> emit      final emission -> out/<key>.v (F9-miter, else yosys)

If your design declares a `paramMeta`, add `--N <v1,v2,…>` to check / sim / cosim to run it at a
NON-default parameter vector (values in the order `paramMeta.params` declares them):

    python3 scripts/bb.py <key> check --N 2,8      well-formedness at that instance
    python3 scripts/bb.py <key> sim   --N 2,8      the same stdin cycles, that instance
    python3 scripts/bb.py <key> cosim --N 2,8      Lean vs iverilog, that instance

Do this.  Every other command in this file tests the DEFAULT instance and only that one, while a
grading testbench instantiates your module at whatever widths it likes.  A generator that is
correct at the defaults and wrong elsewhere is green here and red there.  Plain `check` now sweeps
a grid of vectors and tells you which ones are ill-formed; `--N` is how you then look at one.

After a FAILED command, add `--diagnose "<artifact>: <one line>"` to the next one, where
<artifact> is one of spec / impl / proof / toolchain — what you decided was wrong and are now
changing.  It is recorded on the round that tests the decision, so it costs nothing and is the
only record of what you thought before you knew.

Every invocation appends one JSON line to log/<key>.jsonl (objective process log).
Your design file is LeanRTL/Blind/<Camel>.lean, first line `-- @blind <key>`.
Keep the four section markers (`/-! ## 1. impl` … `## 4. whole-trace`) intact.
"""
import sys, os, re, json, time, hashlib, subprocess, fcntl, shutil, tempfile, glob

WS = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
LAKE = os.path.expanduser("~/.elan/bin/lake")
EXE = os.path.join(WS, ".lake", "build", "bin", "leanrtl")
BLIND_DIR = os.path.join(WS, "LeanRTL", "Blind")
REGISTRY = os.path.join(WS, "LeanRTL", "BlindRegistry.lean")
PARAM_REGISTRY = os.path.join(WS, "LeanRTL", "BlindParamRegistry.lean")
LOG_DIR = os.path.join(WS, "log")
OUT_DIR = os.path.join(WS, "out")
LOCK = os.path.join(WS, ".bb.lock")
BUILD_TIMEOUT = int(os.environ.get("BB_TIMEOUT", "900"))

MARKERS = [("impl", "/-! ## 1. impl"), ("spec", "/-! ## 2. spec"),
           ("l1", "/-! ## 3. L1"), ("wt", "/-! ## 4. whole-trace")]

SYNTAX_RE = re.compile(
    r"unexpected token|unexpected identifier|unknown identifier|unknown constant"
    r"|unknown namespace|expected token|unexpected command|unterminated comment")


def sha(s):
    return hashlib.sha256(s.encode()).hexdigest()[:12]


def resolve(key):
    """key -> (path, camel) via the `-- @blind <key>` line-1 header."""
    if os.path.isdir(BLIND_DIR):
        for f in sorted(os.listdir(BLIND_DIR)):
            if not f.endswith(".lean"):
                continue
            p = os.path.join(BLIND_DIR, f)
            first = open(p).readline().strip()
            if re.match(rf"--\s*@blind\s+{re.escape(key)}\s*$", first):
                return p, f[:-5]
    sys.exit(f"bb: no LeanRTL/Blind/*.lean with header '-- @blind {key}'")


def sec_sha(src):
    """Hash the scaffold's four sections (+ prelude) separately.  Markers are matched at
    LINE START only (a marker string quoted mid-line in a comment must not split the file).
    Degrades gracefully when a marker is missing (metrics then falls back to whole-file
    diffing)."""
    pos = []
    for name, mark in MARKERS:
        m = re.search(r"(?m)^" + re.escape(mark), src)
        pos.append((name, m.start() if m else -1))
    if any(i < 0 for _, i in pos) or [i for _, i in pos] != sorted(i for _, i in pos):
        return {"degraded": True}
    out = {"prelude": sha(src[:pos[0][1]])}
    for k in range(len(pos)):
        start = pos[k][1]
        end = pos[k + 1][1] if k + 1 < len(pos) else len(src)
        out[pos[k][0]] = sha(src[start:end])
    return out


def classify(rc, text, timed_out):
    if timed_out:
        return "timeout"
    if rc == 0:
        return "green"
    if SYNTAX_RE.search(text):
        return "syntax"
    return "proof_fail"


def first_error_head(text, n=200):
    m = re.search(r"error:.*", text, re.S)
    return (m.group(0)[:n]) if m else text[-n:]


def sh(cmd, timeout=BUILD_TIMEOUT, cwd=WS, stdin_data=None):
    try:
        r = subprocess.run(cmd, cwd=cwd, capture_output=True, text=True,
                           timeout=timeout, input=stdin_data)
        return r.returncode, r.stdout, r.stderr, False
    except subprocess.TimeoutExpired as e:
        so = e.stdout.decode() if isinstance(e.stdout, bytes) else (e.stdout or "")
        se = e.stderr.decode() if isinstance(e.stderr, bytes) else (e.stderr or "")
        return 124, so, se, True


def scan_sorry(path):
    rc, so, se, _ = sh([sys.executable, os.path.join(WS, "scripts", "scan_sorry.py"), path],
                       timeout=60)
    return rc == 0, (so + se).strip()


# Rows written by the ablation-7.3 emit pass (harness/oneshot_emit.py) rather than by an author.
# That arm's author never had this tool, so its ledger must not read as though it spent rounds on
# it; the rows are kept, because a build result nobody can check is not a result, and stamped, so
# `analysis/recovery/recovery.py` can exclude them from the repair-round counts.
BY = "oneshot_emit" if os.environ.get("LEANRTL_ONESHOT_EMIT") else None


def log(key, entry):
    if BY:
        entry = dict(entry, by=BY)
    os.makedirs(LOG_DIR, exist_ok=True)
    with open(os.path.join(LOG_DIR, key + ".jsonl"), "a") as f:
        fcntl.flock(f, fcntl.LOCK_EX)
        f.write(json.dumps(entry, ensure_ascii=False) + "\n")
        fcntl.flock(f, fcntl.LOCK_UN)


SNAP_DIR = os.path.join(WS, "snapshot")


def first_green(key, path, src, vpath, fsha, ssha, extra):
    """Archive this design the FIRST time it emits green.  Section 6.3's first-attempt snapshot.

    Metric 6.3 (Design Fix / Recovery Rate) needs a definition of "initially failed" that the
    loop cannot move.  Inside the loop there is none: the author does not stop until the chain is
    green, so "initially" would mean whatever the report chose it to mean afterwards.  The plan's
    answer is a snapshot -- the artifact as it stood the instant it first satisfied every check
    the author can see -- scored out of band against the testbench and never shown back.  Recovery
    is then `first snapshot fails the oracle` -> `final artifact passes it`.

    It has to be taken HERE because nothing else can see the instant.  `verify.py` and `score.py`
    run after the session is over and see only the final bytes; the machine ledger records the
    shas of every round but not the bytes, so an archive reconstructed from it afterwards is not
    possible even in principle.

    "All gates green" is read as far as this tool can read it: `emit` succeeded, which entails the
    file elaborates and the extraction ran, and `scan_sorry` finds no sorry / admit / axiom.  The
    two remaining gates -- `axiom_clean`'s `#print axioms` probe and `undriven_nets` -- are
    out-of-band by construction, and the snapshot is graded by exactly the same `verify.py` that
    grades the final artifact.  `gates_at_snapshot` records which were actually checked here, so
    nobody has to infer it from this comment.

    Written once and never overwritten: `os.path.exists` is the whole guard.  A second green emit
    is the loop continuing to work, not a new first attempt.
    """
    os.makedirs(SNAP_DIR, exist_ok=True)
    meta_p = os.path.join(SNAP_DIR, key + ".json")
    if os.path.exists(meta_p):
        return None
    clean, hits = scan_sorry(path)
    if not clean:
        return None                       # green emit over a file with a hole in it: not green
    red = 0
    lp = os.path.join(LOG_DIR, key + ".jsonl")
    if os.path.isfile(lp):
        for line in open(lp, errors="replace"):
            line = line.strip()
            if not line.startswith("{"):
                continue
            try:
                r = json.loads(line)
            except ValueError:
                continue
            if r.get("by"):
                continue
            if r.get("rc") or r.get("err_class") == "green_with_sorry":
                red += 1
    shutil.copy(vpath, os.path.join(SNAP_DIR, key + ".v"))
    open(os.path.join(SNAP_DIR, key + ".lean"), "w").write(src)
    meta = {"key": key, "ts": round(time.time(), 3),
            "iso": time.strftime("%Y-%m-%dT%H:%M:%S"),
            "file_sha": fsha, "sec_sha": ssha,
            "red_rounds_before": red,
            "gates_at_snapshot": {"builds": True, "extracted": True, "emitted": True,
                                  "zero_sorry": True,
                                  "axiom_clean": "out of band — leanrtl/verify.py",
                                  "undriven_nets": "out of band — leanrtl/verify.py",
                                  "proves_impl": "out of band — leanrtl/verify.py"},
            "what": "the artifact as it stood at its FIRST green emit; scored out of band for "
                    "metric 6.3's first-attempt snapshot, never shown back to the author"}
    meta.update(extra)
    json.dump(meta, open(meta_p, "w"), indent=1)
    return meta


EMIT_DIR = os.path.join(WS, "emits")


def archive_emit(key, src, vpath, fsha, ssha, extra):
    """Archive EVERY green emit, together with the Lean source that produced it.

    `first_green` above answers "what did the artifact look like the first instant everything the
    author can see was green".  That is a DIFFERENT question from "what did the RTL look like
    before the proofs were written", and the difference is its `scan_sorry` guard: a file whose
    proof sections are still holes never reaches it.  Measuring what the PROOF is worth needs
    precisely the emit `first_green` refuses -- the one taken while the proof was still absent.

    So this archives unconditionally and classifies nothing.  Which archived emit counts as
    pre-proof is decided out of band by whatever reads `emits/`, using the same `check_proves`
    predicate `leanrtl/verify.py`'s `proves_impl` gate applies.  Deciding it here would freeze the
    definition into every workspace's copy of this file, where revising it would mean re-running
    sessions.

    Never read back by the author, and it decides nothing: the return value is not consulted, and
    no verdict, ledger class or return code depends on it.  The `except` is the same commitment --
    a failure to take a measurement must not fail the thing being measured.
    """
    try:
        os.makedirs(EMIT_DIR, exist_ok=True)
        n = len(glob.glob(os.path.join(EMIT_DIR, glob.escape(key) + ".*.v")))
        stem = os.path.join(EMIT_DIR, f"{key}.{n:03d}")
        shutil.copy(vpath, stem + ".v")
        open(stem + ".lean", "w").write(src)
        meta = {"key": key, "seq": n, "ts": round(time.time(), 3),
                "iso": time.strftime("%Y-%m-%dT%H:%M:%S"),
                "file_sha": fsha, "sec_sha": ssha,
                "what": "one green emit, archived out of band; pre/post-proof is classified "
                        "later by whatever reads this directory, never here"}
        meta.update(extra)
        json.dump(meta, open(stem + ".json", "w"), indent=1)
    except Exception as e:
        sys.stderr.write(f"bb: emit archive skipped ({e})\n")


def snapshot(path):
    src = open(path).read()
    return src, sha(src), sec_sha(src)


# The repair-budget guard of the evaluation plan, section 10.  The decision recorded there is
# **no cap**: authors run the diagnose / repair / rebuild loop until it converges or until the
# launcher's wall-clock timeout ends the session.  The number below is not a budget, it is a
# runaway guard -- the previous round's worst design hit 15 red builds and the median was 3, so a
# hundred is ~7x the maximum ever observed and stopped 0 of 50.
#
# It is enforced HERE rather than left as prose because the plan says the parameter exists, and a
# parameter that nothing reads is a sentence, not a guard.  It is enforced by COUNTING THE LEDGER
# rather than by a session counter for the same reason `log/<key>.jsonl` is the denominator of
# metric 10: an author that is restarted keeps its history, so a loop that has already burned the
# budget cannot buy a fresh one by crashing.
#
# Non-green is the unit, matching `analysis/recovery/recovery.py`'s reading of "hit a red bb.py".
# `green_with_sorry` counts as red: it is the class where the file compiles and the proof has a
# hole, which is exactly a round the loop still has to spend.
REPAIR_CAP = int(os.environ.get("LEANRTL_REPAIR_CAP", "100"))


def runaway(key):
    """True when this design has already spent REPAIR_CAP red rounds.  Prints why and refuses."""
    if REPAIR_CAP <= 0:
        return False
    p = os.path.join(LOG_DIR, key + ".jsonl")
    if not os.path.isfile(p):
        return False
    red = 0
    for line in open(p, errors="replace"):
        line = line.strip()
        if not line:
            continue
        try:
            r = json.loads(line)
        except ValueError:
            continue
        if r.get("by"):                     # not an author's round; see BY above
            continue
        if r.get("err_class") not in (None, "green"):
            red += 1
    if red < REPAIR_CAP:
        return False
    print(f"bb: RUNAWAY GUARD — {key} has {red} red rounds on log/{key}.jsonl, at or past the "
          f"cap of {REPAIR_CAP}.  This is not a budget you have run out of; it is the guard the "
          f"run policy sets against a loop that is not converging.  Stop, write down in "
          f"notes/{key}.md what the loop kept failing on, and end the session.", file=sys.stderr)
    return True


PARAM_META_RE = re.compile(r"(?m)^\s*def\s+paramMeta\s*:\s*ParamMeta\b")


def strip_comments(src):
    """Lean comments out (nested `/- … -/` and `-- …`), positions preserved by blanking, so a
    declaration QUOTED in a docstring is never mistaken for the real thing.  The scaffold's own
    problem card shows the `paramMeta` shape, so a plain regex over the raw source would report
    every design that merely read the documentation as parametric."""
    out, i, depth, n = list(src), 0, 0, len(src)
    while i < n:
        if depth == 0 and src.startswith("--", i):
            j = src.find("\n", i)
            j = n if j < 0 else j
            for k in range(i, j):
                out[k] = " "
            i = j
            continue
        if src.startswith("/-", i):
            depth += 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0 and src.startswith("-/", i):
            depth -= 1
            out[i] = out[i + 1] = " "
            i += 2
            continue
        if depth > 0 and src[i] != "\n":
            out[i] = " "
        i += 1
    return "".join(out)


def param_meta(src):
    """The design's own `paramMeta : ParamMeta` (F2 ParamModule), as `{key, params}` where
    `params` is `[(name, default), …]` in declaration order, or None.

    This — not the presence of the registry file — is what gates the parametric route.  No RTLLM
    design declares a `paramMeta`, so every RTLLM design takes the f9 / write_verilog path it
    took before the F2 wiring existed.

    The order of `params` is load-bearing everywhere downstream: it is the order `gen` reads its
    argument vector in, the order the `#(parameter …)` header is emitted in, and the order
    `extract --N` expects.  `re.findall` over the literal preserves it; do not sort it or hand it
    through a dict.
    """
    if not os.path.exists(PARAM_REGISTRY):
        return None
    code = strip_comments(src)
    m = PARAM_META_RE.search(code)
    if m is None:
        return None
    body = code[m.end():m.end() + 1200]
    cut = re.search(r"(?m)^\s*(def|theorem|lemma|example|end|open|/-!)\b", body)
    if cut:
        body = body[:cut.start()]
    out = {}
    mm = re.search(r'key\s*:=\s*"([^"]+)"', body)
    if mm:
        out["key"] = mm.group(1)
    lst = re.search(r"params\s*:=\s*\[(.*?)\]", body, re.S)
    if lst is None:
        # A design whose parameters move its SHAPE writes the family as a `PModule` and then
        # `params := <family>.params`, so the literal lives one definition up.  Follow the
        # reference rather than reporting no parameters: an empty `params` here does not fail
        # loudly, it makes `param_anchor` prove the default vector and nothing else, which is
        # precisely the blind spot the parametric route exists to close.
        ref = re.search(r"params\s*:=\s*([A-Za-z_][A-Za-z0-9_'.]*)\s*\.params\b", body)
        if ref:
            src_def = re.search(
                r"(?m)^\s*def\s+" + re.escape(ref.group(1)) + r"\s*:\s*PModule\b", code)
            if src_def:
                tail = code[src_def.end():src_def.end() + 1200]
                tcut = re.search(r"(?m)^\s*(def|theorem|lemma|example|end|open|/-!)\b", tail)
                lst = re.search(r"params\s*:=\s*\[(.*?)\]",
                                tail[:tcut.start()] if tcut else tail, re.S)
    if lst:
        out["params"] = [(n, int(v))
                         for n, v in re.findall(r'\(\s*"([^"]+)"\s*,\s*(\d+)\s*\)', lst.group(1))]
    return out


def _equiv_verdict(route, why):
    """What the pipeline PROVED about the bytes it just wrote, as one token.

    Every route ends in `bb: emitted <path> (route=…, f9=…)`, and the equivalence verdict was a
    substring of `f9=` — which by then also carries the port-order note and the parameter-injection
    detail, so the single fact that says whether the shipped file was checked *at all* was the
    hardest thing on the line to find.  An author reading a log cannot be asked to parse it.

      proven      the shipped bytes were proved equivalent to the verified netlist by `equiv_induct`
      proven_modulo_timebase
                  ditto for a clocked twin differing on one `always` sensitivity line.  What
                  advances a step is not certified, and cannot be: RTLIL has no delay.
      translated  Yosys wrote the file from the verified netlist and nothing re-checked the result

    `translated` is not a failure and must not be read as one: a purely combinational module has no
    `always @(posedge …)` for the F9 route to help with, so it takes the backend emission of the
    same netlist deliberately.  It is a weaker claim than `proven`, and the point of the token is
    that it now READS weaker — `f9=` still names which of the several reasons applied, including
    the one that matters most, an F9 candidate the miter DISPROVED against our own netlist.
    """
    if "timed_step:clocked_twin_proven" in why:
        return "proven_modulo_timebase"
    if route.endswith("f9") and "miter_proven" in why:
        return "proven"
    # The write_verilog route re-proves only when it injected parameters.  `no_params` means the
    # file that shipped is Yosys's own translation with nothing checked on top of it.
    if "params_injected" in why:
        return "proven"
    return "translated"


def _inert_or_empty(vpath):
    """Parameters the emitted module declares and never reads, or `[]` if it cannot be asked.

    Kept tolerant on purpose: this is a diagnostic bolted onto a path that already succeeded, so a
    missing helper or an unreadable file must not turn a green emit red.  The cost of the tolerance
    is that a silent `[]` and a genuine `[]` look alike here; `leanrtl/iface_conform.py` re-derives
    the same fact from the run's artifacts afterwards, where the distinction can be drawn.
    """
    try:
        sys.path.insert(0, os.path.join(WS, "scripts"))
        from f9_emit import inert_params
        return inert_params(open(vpath).read())
    except Exception:
        return []


def _iface_gate(key, vpath):
    """`(severity, message, detail)`: does the emitted module answer to what the spec declares?

    Severity is `ok`, `warn` or `refuse`, and the split is the whole design of this check.  Most
    of what `emit` can report is a matter of degree -- a fixed-width fallback is narrower evidence
    than a parametric one, an inert parameter is a module that is right at one width.  A module
    missing a pin the spec declares is different in kind: a testbench binds by name, so it never
    attaches at all and no vector is applied.  But "the spec names a port we do not have" is not
    always that, because a long spec quotes the RTL around the design as well as the design, and
    measured across four benchmarks it flags modules that pass.  `iface_gate` draws the line where
    the author can always comply -- see its docstring -- and only that case refuses.

    Not every finding here is about a pin.  The gate also reports a magnitude the spec NAMES and
    the module declares nowhere: a threshold or a factor the author inlined as a literal instead
    of as a `parameter`.  That one warns, because a harness that reads such a name off the DUT
    agrees with whatever the author chose and cannot bind to a literal at all.

    A refusal refuses AFTER the artifact is on disk, deliberately: the file stays exactly where a
    passing emit would have left it, so an author that runs out of budget here is no worse off
    than before this check existed, and the ledger names the reason either way.

    Tolerant about its inputs for the same reason `_inert_or_empty` is: a workspace with no spec
    file, or a helper that fails to import, must not turn a good emit red.
    """
    try:
        sys.path.insert(0, os.path.join(WS, "scripts"))
        from iface_gate import gate
        sev, msg, det = gate(os.path.join(WS, "specs", key + ".spec.txt"), vpath)
        # Only the actionable fields reach the ledger.  `gate` also returns both full port lists
        # and the per-source breakdown, which are what a HUMAN needs when reading one design and
        # pure weight when written into every entry of a 78-design run; `iface_conform.py`
        # re-derives them from the same two files whenever they are wanted.
        #
        # `dead_input` and `named_constant` are here because they are the two findings that are
        # NOT re-derivable from the header alone -- one needs the module body, the other the spec
        # prose -- so a ledger that dropped them would be the only record that they ever fired,
        # and it would be an empty one.
        keep = {k: det[k] for k in ("missing_port", "missing_param", "extra_port",
                                    "prose_self_conflict", "dead_input", "named_constant")
                if det.get(k)}
        return sev, msg, keep
    except Exception:
        return "ok", "", {}


def _iface_report(key, vpath):
    """Run the gate, print what it found, and say whether the emit may be called green."""
    sev, msg, det = _iface_gate(key, vpath)
    if sev == "refuse":
        print(f"bb: REFUSING to call {key} emitted — {msg}")
    elif sev == "warn":
        print(f"bb: WARNING {key} — {msg}")
    return sev, det


def sync_param_registry_single(camel, has_meta):
    """Registry-of-one for ParamModules, the same discipline as the module registry: the CLI's
    `pverilog` / `extract --N` see this design's generator and nothing else."""
    if not os.path.exists(PARAM_REGISTRY):
        return
    imports = ["import LeanRTL.Core.ParamBackend"]
    if has_meta:
        imports.append(f"import LeanRTL.Blind.{camel}")
    entries = f"[_root_.LeanRTL.Blind.{camel}.paramMeta]" if has_meta else "[]"
    txt = "\n".join(imports + [
        "/-! # Blind-workspace ParamModule registry (AUTO-GENERATED by `scripts/bb.py`).",
        "    Do not edit by hand. -/",
        "namespace LeanRTL.Designs.Param",
        "",
        "def paramRegistry : List ParamMeta :=",
        f"  {entries}",
        "",
        "def findParamMeta? (key : String) : Option ParamMeta :=",
        "  paramRegistry.find? (·.key == key)",
        "",
        "end LeanRTL.Designs.Param",
    ]) + "\n"
    if open(PARAM_REGISTRY).read() != txt:
        open(PARAM_REGISTRY, "w").write(txt)


def sync_registry_single(key, camel, src):
    """Registry-of-one: the exe serves only the requesting design (under the global lock),
    so one agent's broken file can never fail another agent's build."""
    is_parent = re.search(r"def\s+impl\s*:\s*Parent", src) is not None
    pm = param_meta(src)
    sync_param_registry_single(camel, pm is not None)
    # A ParamModule has no `impl : Module` to register; the Module registry gets its DEFAULT
    # instance, so check / sim / cosim / extract keep working at the declared default width
    # while `pverilog` serves the parametric family.
    entry = (f'("{key}", Blind.{camel}.paramMeta.gen Blind.{camel}.paramMeta.defaults)'
             if pm is not None else f'("{key}", Blind.{camel}.impl)')
    mods = "[]" if is_parent else f"[{entry}]"
    pars = f"[{entry}]" if is_parent else "[]"
    txt = "\n".join([
        "import LeanRTL.Core.Syntax",
        f"import LeanRTL.Blind.{camel}",
        "/-! # Blind-workspace module registry (AUTO-GENERATED by `scripts/bb.py`).",
        "    Do not edit by hand. -/",
        "namespace LeanRTL",
        "",
        f"def blindRegistry : List (String × Module) :=",
        f"  {mods}",
        "",
        f"def blindParentRegistry : List (String × Parent) :=",
        f"  {pars}",
        "",
        "end LeanRTL",
    ]) + "\n"
    if not os.path.exists(REGISTRY) or open(REGISTRY).read() != txt:
        open(REGISTRY, "w").write(txt)


def top_name(src):
    """The module yosys should take as top.

    NOT simply the first `name := "…"` in the file.  For a `Parent`, the child cells are usually
    defined before the parent that instantiates them, so the first literal is a CHILD's name and
    the emitted Verilog then contains only that child -- silently, with no error anywhere.  Found
    by role R while authoring a two-instance hierarchy, which had to be restructured to put the
    parent's name first textually just to get correct output.

    So: find the definition that `def impl` resolves to and take ITS name.  `impl` is the
    fragment contract -- every design ends in `def impl : Module` or `def impl : Parent` -- and
    for a `Parent` whose body is an application (`implTop implAdder8`), follow one level to the
    function being applied.  Falls back to the old behaviour only when nothing resolves.
    """
    m = re.search(r"^\s*def\s+impl\s*:\s*(Module|Parent)\s*:=\s*(.*)$", src, re.M)
    if m:
        body = m.group(2).strip()
        # `def impl : Parent := implTop implAdder8` -> look inside `implTop`
        head = re.match(r"([A-Za-z_]\w*)", body)
        if head:
            d = re.search(rf"^\s*def\s+{re.escape(head.group(1))}\b.*?name\s*:=\s*\"([^\"]+)\"",
                          src, re.M | re.S)
            if d:
                return d.group(1)
        n = re.search(r'name\s*:=\s*"([^"]+)"', body)
        if n:
            return n.group(1)
        # `def impl : Module := { name := "x", … }` spanning lines after the `:=`
        tail = src[m.end(2):]
        n = re.search(r'name\s*:=\s*"([^"]+)"', tail)
        if n:
            return n.group(1)
    m = re.search(r'name\s*:=\s*"([^"]+)"', src)
    return m.group(1) if m else None


def main():
    if len(sys.argv) < 3:
        print(__doc__)
        return 2
    key, cmd = sys.argv[1], sys.argv[2]
    # `--N <v1,v2,…>` — run this command on a NON-default parameter vector.
    #
    # Without it every command in this file tests exactly one instance: the defaults the design's
    # own `paramMeta` declares.  A grader does not.  It instantiates the module at whatever widths
    # and depths its testbench picks, and a generator that is right at the defaults and wrong
    # anywhere else passes every gate in this workspace and fails every one of theirs.  There was
    # no command here that could show an author that, so the failure was invisible until scoring.
    #
    # Consumed and REMOVED from argv before `--diagnose` is read, because `--diagnose` deliberately
    # swallows the rest of the line as free text; leaving `--N` in would file it as part of the
    # author's sentence.
    nvec = None
    if "--N" in sys.argv:
        i = sys.argv.index("--N")
        if i + 1 >= len(sys.argv):
            print("bb: --N needs a comma-separated vector in the design's declared parameter "
                  "order, e.g. --N 8,16")
            return 2
        nvec = sys.argv[i + 1]
        del sys.argv[i:i + 2]
        if cmd not in ("check", "sim", "cosim"):
            print(f"bb: --N applies to check/sim/cosim, not '{cmd}'.  `emit` always ships the "
                  "parametric module and anchors it at several vectors on its own.")
            return 2
    # `--diagnose <artifact>: <one line>` — section 6.1's instrumentation requirement.
    #
    # Metric 8 (Artifact Diagnosis Accuracy) asks whether the agent knows WHAT to change when a
    # proof fails.  Three of the four things it needs are already objective: the failure is the
    # previous red row, the artifact actually modified is the `sec_sha` that moved between the two
    # rows, and the outcome is this row's `rc`.  The fourth — what the author BELIEVED should
    # change — exists nowhere but in the author's head, and reconstructing it afterwards from
    # prose notes is what made the previous round's number a reading of a self-report rather than
    # a measurement.
    #
    # So it is taken here, on the round that acts on the diagnosis, and it costs one flag.  A
    # diagnosis recorded on the run that TESTS it can be checked against what that run changed and
    # whether it worked; one recorded in a notes file at the end cannot be tied to either.
    #
    # Free text after the category on purpose.  The categories are the plan's four, the row keeps
    # whatever was typed, and nothing here validates the sentence: a tool that rejected a
    # diagnosis would be teaching the author which diagnoses to give.
    diag = None
    if "--diagnose" in sys.argv:
        i = sys.argv.index("--diagnose")
        diag = " ".join(sys.argv[i + 1:]).strip()[:400] or None
    if runaway(key):
        return 2
    path, camel = resolve(key)
    src, fsha, ssha = snapshot(path)
    t0 = time.time()
    entry = {"ts": round(t0, 3), "iso": time.strftime("%Y-%m-%dT%H:%M:%S"),
             "key": key, "cmd": cmd, "file_sha": fsha, "sec_sha": ssha}
    if diag:
        entry["diagnosis"] = diag
    if nvec:
        # The ledger row must say which instance was tested, or a green `sim` at 2,2 and a green
        # `sim` at the defaults are the same row.
        entry["N"] = nvec

    def finish(rc, err_class, err_head="", **extra):
        entry.update({"rc": rc, "wall_s": round(time.time() - t0, 1),
                      "err_class": err_class, "err_head": err_head})
        entry.update(extra)
        log(key, entry)
        return 0 if rc == 0 else 1

    if cmd == "build":
        rel = os.path.relpath(path, WS)
        rc, so, se, to = sh([LAKE, "env", "lean", rel])
        text = so + se
        sys.stdout.write(so); sys.stderr.write(se)
        ec = classify(rc, text, to)
        if ec == "green":
            clean, hits = scan_sorry(path)
            if not clean:
                ec = "green_with_sorry"
                print("bb: WARNING — file contains sorry/admit/axiom:\n" + hits)
        return finish(rc, ec, first_error_head(text) if rc else "")

    if cmd == "audit":
        clean, hits = scan_sorry(path)
        print(hits or "clean")
        return finish(0 if clean else 1, "green" if clean else "sorry_found",
                      hits[:200] if not clean else "")

    if cmd not in ("check", "sim", "cosim", "emit"):
        print(__doc__)
        return 2

    # ---- locked exe ops: registry-of-one + lake build + the op ----
    stdin_data = sys.stdin.read() if cmd == "sim" else None
    with open(LOCK, "a") as lockf:
        fcntl.flock(lockf, fcntl.LOCK_EX)
        sync_registry_single(key, camel, src)
        rc, so, se, to = sh([LAKE, "build", "leanrtl", "-q"], timeout=max(BUILD_TIMEOUT, 1200))
        if rc != 0:
            text = so + se
            sys.stdout.write(so); sys.stderr.write(se)
            return finish(rc, "exe_build_" + classify(rc, text, to), first_error_head(text))

        nflag = ["--N", nvec] if nvec else []

        if cmd == "check":
            rc, so, se, to = sh([EXE, "check", key] + nflag, timeout=120)
            sys.stdout.write(so); sys.stderr.write(se)
            return finish(rc, classify(rc, so + se, to), first_error_head(so + se) if rc else "")

        if cmd == "sim":
            rc, so, se, to = sh([EXE, "sim", key] + nflag, timeout=300, stdin_data=stdin_data)
            sys.stdout.write(so); sys.stderr.write(se)
            return finish(rc, classify(rc, so + se, to), first_error_head(so + se) if rc else "")

        scratch = os.path.join(WS, "scratch", key)
        os.makedirs(scratch, exist_ok=True)
        gold = os.path.join(scratch, "gold.rtlil.json")
        # `--N` goes before `-o`: that is the order `extract` accepts.
        rc, so, se, to = sh([EXE, "extract", key] + nflag + ["-o", gold], timeout=300)
        if rc != 0:
            text = so + se
            sys.stdout.write(so); sys.stderr.write(se)
            return finish(rc, "extract_fail", first_error_head(text))
        top = top_name(src) or key

        if cmd == "cosim":
            vv = os.path.join(scratch, "cosim.v")
            rc, so, se, to = sh(["yosys", "-q", "-p",
                                 f"read_json {gold}; hierarchy -top {top}; proc; opt; write_verilog {vv}"],
                                timeout=300)
            if rc != 0:
                sys.stderr.write(se)
                return finish(rc, "yosys_fail", first_error_head(se))
            # Pass the clock's NAME through, not just the fact that there is one.  cosim used to
            # rediscover it from a {clk, clock} whitelist, so `asyn_fifo` -- whose clock is
            # `wclk` -- died with "--seq but no clock input found" and was logged as cosim_fail,
            # i.e. as a defect of the design.  See docs/findings/HARNESS_SELF_ATTRIBUTION.md.
            mclk = re.search(r'clock\s*:=\s*some\s*"([^"]+)"', src)
            seq = ["--seq"] if re.search(r"clock\s*:=\s*some", src) else []
            if mclk:
                seq += ["--clock", mclk.group(1)]
            if re.search(r"clockNet\s*:=\s*some", src):
                seq += ["--multiclock"]
            rc, so, se, to = sh([sys.executable, os.path.join(WS, "scripts", "cosim.py"),
                                 gold, vv, "--key", key] + seq + nflag, timeout=600)
            sys.stdout.write(so); sys.stderr.write(se)
            # A harness/toolchain error is not a disagreement between the design and its spec.
            # Keep it out of the field that means "the emitted Verilog contradicts the Lean
            # semantics", or the metric reports the harness's bug as the candidate's.
            harness_err = '"status": "harness_error"' in so or '"harness_error"' in so
            cls = ("cosim_pass" if rc == 0 else "timeout" if to
                   else "harness_error" if harness_err else "cosim_fail")
            return finish(rc, cls, first_error_head(so + se) if rc else "")

        if cmd == "emit":
            os.makedirs(OUT_DIR, exist_ok=True)
            shutil.copy(gold, os.path.join(OUT_DIR, key + ".rtlil.json"))
            sh([sys.executable, os.path.join(WS, "scripts", "validate_rtlil.py"), gold],
               timeout=120)
            route, vpath = None, os.path.join(OUT_DIR, key + ".v")
            # F2: a ParamModule emits genuinely parametric SystemVerilog (real `parameter`
            # declarations), not the elaborated default instance.  Without this route a
            # parametric design would fall back to f9 / write_verilog and ship the default
            # width silently -- a regression manufactured by the pipeline that would read as a
            # benchmark result.  Gated on the DESIGN's own `paramMeta`, so a benchmark with no
            # parametric design never reaches it.
            pm = param_meta(src)
            pv_refusal = None
            sys.path.insert(0, os.path.join(WS, "scripts"))

            # ---- Stage 1: the fixed-width artifact, ALWAYS, and before anything expensive.
            #
            # This used to run only as the parametric route's fallback, after `param_anchor`.  That
            # ordering meant an author killed at its budget mid-anchor shipped NOTHING -- not the
            # parametric module it was still certifying, and not the fixed-width one it already
            # could have.  It happened to a design whose four proof sections were all green.
            #
            # Nothing here depends on the parametric route's outcome, and the artifact it writes is
            # exactly what that route falls back to on a refusal.  So write it first and let stage 2
            # overwrite it on success: the successful end state is byte-identical, and the
            # interrupted one is a shipped design instead of a hole in the run.
            order = None
            try:
                from f9_emit import (f9_or_none, contract_port_order, module_params,
                                     inject_params)
                order = contract_port_order(os.path.join(WS, "contracts", key + ".json"))
                p, why = f9_or_none(EXE, key, top, gold, scratch, port_order=order)
            except Exception as e:
                p, why = None, f"f9 exception: {e}"
            if p is not None:
                shutil.copy(p, vpath)
                route = "f9"
            else:
                rc, so, se, to = sh(["yosys", "-q", "-p",
                                     f"read_json {gold}; hierarchy -top {top}; proc; opt; write_verilog {vpath}"],
                                    timeout=300)
                route = "write_verilog" if rc == 0 else "fail"
                if rc != 0:
                    sys.stderr.write(se)
                    return finish(rc, "emit_fail", first_error_head(se), emit_route=route)
                # RTLIL cannot carry a Verilog parameter, so this route has to add them back and
                # re-prove the result against the same gold netlist.  A failed injection is an
                # error, not a silent revert: the design would elaborate wrong in the testbench.
                pr = module_params(EXE, key)
                ok, inj_detail = inject_params(vpath, pr, gold, top, scratch)
                why += "|" + inj_detail
                if not ok:
                    return finish(1, "emit_fail", inj_detail, emit_route=route, f9_detail=why)

            # ---- Stage 2: try to UPGRADE that artifact to a genuinely parametric module.
            # F2: a ParamModule emits genuinely parametric SystemVerilog (real `parameter`
            # declarations), not the elaborated default instance.  Without this route a
            # parametric design would ship the default width silently -- a regression manufactured
            # by the pipeline that would read as a benchmark result.  Gated on the DESIGN's own
            # `paramMeta`, so a benchmark with no parametric design never reaches it.
            if pm is not None:
                rc, so, se, to = sh([EXE, "pverilog", key], timeout=300)
                if rc == 0 and "module" in so:
                    # Written to SCRATCH, not to `out/`, until it is anchored.  Stage 1 already put
                    # a certified module at `out/<key>.v`, and a parametric module left sitting
                    # there uncertified is exactly the thing this route exists to stop shipping.
                    cand = os.path.join(scratch, key + ".param.v")
                    open(cand, "w").write(so)
                    pnames = [n for n, _ in pm.get("params") or []]
                    pdefs = [v for _, v in pm.get("params") or []]
                    try:
                        from f9_emit import param_anchor
                        pok, anchor_detail = param_anchor(EXE, key, top, pnames, pdefs,
                                                          cand, scratch)
                    except Exception as e:
                        pok, anchor_detail = False, f"param_anchor exception: {e}"
                    if not pok:
                        # The emitted module and the machine-checked compiler's own netlist
                        # disagree at some parameter vector, or too few vectors could be anchored.
                        # Either way this is not a certificate about the family, so the parametric
                        # file does not ship and stage 1's artifact stands: same discipline as
                        # `f9_or_none` returning None.
                        pv_refusal = anchor_detail
                        print(f"bb: pverilog emitted {key} but it is NOT anchored "
                              f"({anchor_detail}); keeping the f9 / write_verilog artifact")
                    else:
                        shutil.copy(cand, vpath)
                        # Leads with what was PROVED, for the same reason the f9 line below does.
                        # `anchored` is its own token because it is a different claim from either
                        # of that line's: not one instance certified, but a grid of parameter
                        # vectors -- which is stronger about the family and says nothing extra
                        # about any single width.
                        print(f"bb: emitted {vpath} equivalence=anchored "
                              f"(route=pverilog, "
                              f"params: {', '.join(f'{n}={v}' for n, v in zip(pnames, pdefs))}, "
                              f"{anchor_detail})")
                        # Asked on this route too, where the expected answer is `[]`.  The point
                        # of `pverilog` is that it emits a width-generic module, so an inert
                        # parameter here would mean the parametric route itself is not
                        # parametric -- a defect worth catching on the designs that take it
                        # rather than assuming it away.
                        pdead = _inert_or_empty(vpath)
                        if pdead:
                            print(f"bb: WARNING the parametric route emitted inert parameter(s): "
                                  f"{', '.join(pdead)}")
                        isev, idet = _iface_report(key, vpath)
                        if isev == "refuse":
                            return finish(1, "iface_mismatch",
                                          ",".join(idet.get("missing_port") or []),
                                          emit_route="pverilog", top=top,
                                          param_names=pnames, param_defaults=pdefs,
                                          param_anchor=anchor_detail, inert_params=pdead,
                                          equivalence="anchored",
                                          f9_detail=why, port_order=order, iface=idet)
                        archive_emit(key, src, vpath, fsha, ssha,
                                     {"emit_route": "pverilog", "top": top})
                        snap = first_green(key, path, src, vpath, fsha, ssha,
                                           {"emit_route": "pverilog", "top": top})
                        return finish(0, "green", "", emit_route="pverilog", top=top,
                                      param_names=pnames, param_defaults=pdefs,
                                      param_anchor=anchor_detail, inert_params=pdead,
                                      equivalence="anchored",
                                      f9_detail=why, port_order=order, iface=idet,
                                      first_green_snapshot=bool(snap))
                else:
                    # A refusal is not an emit failure.  The generic emitter refuses when it
                    # cannot express a width or a structure it has not verified -- a memory depth
                    # that changes the register count, a `2^N-1` mask -- and returning `emit_fail`
                    # here would turn a design that used to ship a fixed-width module into a
                    # design that ships nothing.  That destroys the evidence instead of reporting
                    # it.  So: print the reason, keep the stage 1 artifact the design would have
                    # taken before F2 existed, and record BOTH the reason and the fact that this
                    # route was a fallback, so the route counts do not quietly absorb these
                    # designs into the plain-f9 population.
                    # A refusal from the SAMPLED route is a statement about sampling, not about the
                    # design, and the author cannot act on it unless they can read it whole.  200
                    # characters cut `…the parameters\n  - cannot express a bit index…` down to
                    # `ters\n  - cannot express a bit index as a function of (…)` -- a reason that
                    # begins mid-word and drops the list of what else was refused.  A refusal is a
                    # handful of lines by construction, so keep them.
                    pv_refusal = first_error_head(so + se, 4000)
                    sys.stderr.write(se)
                    print(f"bb: pverilog refused {key}; keeping the f9 / write_verilog "
                          f"artifact (the emitted module will NOT be width-generic)")
                    # Every refusal above comes from FITTING -- the route that recovers a family by
                    # elaborating `gen` at a grid of vectors and reading the widths back out of the
                    # numbers.  It refuses whenever the family's shape moves with a parameter (a
                    # depth, a tap count, a matrix dimension) or a width is not multilinear in
                    # them.  The SYMBOLIC route has neither limit, because it is handed the loop
                    # instead of inferring one, and it is reached by one field.  Say so here: the
                    # refusal text explains what could not be fitted and never mentions that there
                    # is a route where nothing is fitted at all.
                    print("bb: this refusal is from the SAMPLED route.  Write the family as a "
                          "`PModule` and set `sym := some famP` in your `paramMeta` -- see "
                          "docs/dsl-reference.md §6.2.  A parametric register COUNT, a bit index "
                          "that moves with a parameter, and a `2**N-1` mask are all expressible "
                          "there; none of them is fittable here.")
            # Only present when the parametric route was tried AND refused.  `finish`'s kwargs go
            # straight into the ledger entry, so passing `None` unconditionally would stamp a null
            # field onto every f9 emit of every benchmark, including the ones with no `paramMeta`
            # to refuse.  Absence is the honest encoding of "this design never asked".
            pv_extra = {"pverilog_refusal": pv_refusal} if pv_refusal else {}
            # A fallback f9 is not the same population as a plain f9: it is a design that ASKED
            # for the parametric route and was refused, so the emitted module is fixed-width for a
            # reason the ledger can name.  Give it its own route bucket, or a report counting
            # routes quietly absorbs these designs into the plain-f9 population and the parametric
            # route looks like it was never attempted.
            if pv_refusal:
                route = "pverilog_refused->" + route
            equiv = _equiv_verdict(route, why)
            print(f"bb: emitted {vpath} equivalence={equiv} (route={route}, f9={why})")
            dead = _inert_or_empty(vpath)
            if dead:
                # The author's own signal.  Everything else this session can tell them is green:
                # the design elaborates, `check` proves it, the miter certifies the netlist.  None
                # of that is a statement about a width other than the default, so a design whose
                # testbench overrides a parameter can be green here and still fail every run.  It
                # is said on stdout, where the author reads it, because it is theirs to fix -- and
                # the fix is to model the design as a `ParamModule` (`paramMeta`), which is the
                # one route in this pipeline that emits a genuinely width-generic module.
                print(f"bb: WARNING {vpath} declares parameter(s) its body never reads: "
                      f"{', '.join(dead)}.  Overriding one at elaboration changes nothing, so a "
                      f"testbench that instantiates this module at another width gets this same "
                      f"fixed-width circuit.  If the spec means these to be real, model the "
                      f"design as a ParamModule with a `paramMeta` and re-emit.")
            isev, idet = _iface_report(key, vpath)
            if isev == "refuse":
                return finish(1, "iface_mismatch", ",".join(idet.get("missing_port") or []),
                              emit_route=route, top=top, f9_detail=why, equivalence=equiv,
                              port_order=order, inert_params=dead, iface=idet, **pv_extra)
            archive_emit(key, src, vpath, fsha, ssha, {"emit_route": route, "top": top})
            snap = first_green(key, path, src, vpath, fsha, ssha,
                               {"emit_route": route, "top": top})
            return finish(0, "green", "", emit_route=route, top=top, f9_detail=why,
                          equivalence=equiv,
                          port_order=order, inert_params=dead, iface=idet,
                          **pv_extra,
                          first_green_snapshot=bool(snap))


if __name__ == "__main__":
    sys.exit(main())
