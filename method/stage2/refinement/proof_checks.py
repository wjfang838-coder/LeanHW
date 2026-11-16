"""Independent fixed-target v2lean certificate checking and emission.

The caller must verify frozen input/framework provenance before invoking this module.
Only cold=True establishes an authoritative source-only replay; warm checks are feedback.
No benchmark, roundtrip, Jasper, or model calls occur here.
"""
from __future__ import annotations

import hashlib
import json
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[3]
sys.path.insert(0, str(ROOT / "method/stage1"))
sys.path.insert(0, str(ROOT / "method/stage2"))
try:
    from leanrtl.frozen_exec import command_prefix
    from leanrtl.authoring.scan_sorry import strip_comments_and_strings
except ImportError:  # Self-contained certificate replay tools.
    from frozen_exec import command_prefix
    from scan_sorry import strip_comments_and_strings

STD_AXIOMS = {"propext", "Classical.choice", "Quot.sound"}
NATIVE_LRAT = re.compile(r"\._native\.bv_decide\.ax_")
HIJACK = re.compile(r"@\[[^\]]*\b(?:implemented_by|extern)\b")
THEOREM_TYPE = "FrozenSpecBridge.Equivalent SpecIR.Gen.spec V2LeanImported.impl"
HEADER = ("import FrozenSpec\nimport Imported\nimport FrozenSpecBridge\n"
          "set_option maxHeartbeats 3200000\nset_option maxRecDepth 32768\n"
          "set_option autoImplicit false\ntheorem frozen_equivalence :\n    "
          + THEOREM_TYPE + " :=\n")
AUDIT_NAMES = ("frozen_equivalence", "FrozenSpecBridge.Certificate.equivalent",
               "imported_checks", "imported_coverage",
               "LeanRTL.CheckWidth.compileModule_seq_correct_wires_checked",
               "LeanRTL.CheckWidth.compileModule_seq_correct_wires_reset_checked")
AUDIT = """import FrozenProof
import LeanRTL.Core.Coverage
set_option maxHeartbeats 16000000
set_option maxRecDepth 32768
example : FrozenSpecBridge.Equivalent SpecIR.Gen.spec V2LeanImported.impl := frozen_equivalence
theorem imported_checks : LeanRTL.CheckWidth.moduleChecksb V2LeanImported.impl = true := by decide +kernel
theorem imported_coverage : V2LeanImported.impl.semanticCoverage = .full := by decide +kernel
#print axioms frozen_equivalence
#print axioms FrozenSpecBridge.Certificate.equivalent
#print axioms imported_checks
#print axioms imported_coverage
#print axioms LeanRTL.CheckWidth.compileModule_seq_correct_wires_checked
#print axioms LeanRTL.CheckWidth.compileModule_seq_correct_wires_reset_checked
"""
SOURCE_NAMES = ("LeanRTL", "LeanRTL.lean", "SpecIR", "SpecIR.lean", "FrozenSpec.lean",
                "Imported.lean", "FrozenSpecBridge.lean", "lean-toolchain", "lakefile.toml",
                "lake-manifest.json", "proof.term", "entrypoint-adapter.json", "iface.json")


def sha(path: Path) -> str:
    return hashlib.sha256(path.read_bytes()).hexdigest()


def save(path: Path, obj: dict) -> None:
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + "\n")


def source_manifest(ws: Path) -> dict:
    result = {}
    for name in SOURCE_NAMES:
        path = ws / name
        if path.is_symlink():
            raise ValueError(f"Symlink source forbidden: {name}")
        if path.is_dir():
            for child in sorted(path.rglob("*")):
                if child.is_symlink():
                    raise ValueError(f"Symlink source forbidden: {child}")
                if child.is_file() and child.suffix == ".lean":
                    result[str(child.relative_to(ws))] = sha(child)
        elif path.is_file():
            result[name] = sha(path)
    required = {"FrozenSpec.lean", "Imported.lean", "FrozenSpecBridge.lean", "proof.term",
                "lean-toolchain", "lakefile.toml"}
    if required - result.keys():
        raise ValueError(f"Missing proof inputs: {sorted(required - result.keys())}")
    return result


def scan_authored(text: str) -> list[str]:
    bare = strip_comments_and_strings(text)
    hits = re.findall(r"\b(?:sorry|sorryAx|admit|axiom|native_decide|elab|macro|syntax|"
                      r"run_tac|unsafe|initialize|notation)\b|debug\.skipKernelTC|"
                      r"#\s*(?:eval|run|exit)|\bLean\.ofReduceBool\b", bare)
    if HIJACK.search(bare) or re.search(r"\battribute\s+\[[^\]]*\b(?:extern|implemented_by)\b", bare):
        hits.append("native execution override")
    return sorted(set(hits))


def parse_axioms(output: str, expected=AUDIT_NAMES) -> dict:
    records = {}
    for name in expected:
        pattern = (r"^'" + re.escape(name) + r"' (?:depends on axioms: \[([^\]]*)\]|"
                   r"does not depend on any axioms)\s*$")
        matches = re.findall(pattern, output, re.M)
        if len(matches) != 1:
            raise ValueError(f"Missing or duplicate canonical axiom audit for {name}")
        records[name] = [x.strip() for x in matches[0].split(",") if x.strip()]
    return records


def axiom_policy(axioms: dict, ws: Path) -> dict:
    extras = sorted({a for deps in axioms.values() for a in deps} - STD_AXIOMS)
    native = [a for a in extras if NATIVE_LRAT.search(a)]
    unexpected = [a for a in extras if not NATIVE_LRAT.search(a)]
    hijacks = []
    # Audit the complete source dependency closure supplied in the sealed workspace,
    # including the actual Imported implementation (missing in the historical runner).
    if native:
        for name in list(source_manifest(ws)) + ["FrozenProof.lean", "FrozenAudit.lean"]:
            if not name.endswith((".lean", ".term")):
                continue
            bare = strip_comments_and_strings((ws / name).read_text())
            if HIJACK.search(bare) or re.search(r"\battribute\s+\[[^\]]*\b(?:extern|implemented_by)\b", bare):
                hijacks.append(name)
    return {"ok": not unexpected and not hijacks, "axioms": axioms,
            "unexpected_axioms": unexpected, "native_lrat": native,
            "native_override_hijacks": hijacks, "kernel_only": not extras,
            "trusted_base": "Lean kernel + standard axioms" +
            (" + native LRAT execution (Lean compiler/runtime/C compiler)" if native else "")}


def run(ws: Path, argv: list[str], logdir: Path, name: str, timeout=3600) -> dict:
    logdir.mkdir(parents=True, exist_ok=True)
    protected = [ws / n for n in SOURCE_NAMES if (ws / n).exists()]
    protected += [p for p in ws.glob("*.lean") if p not in protected]
    started = time.monotonic()
    try:
        proc = subprocess.run(command_prefix(ws, readonly=protected) + argv, cwd=ws,
                              capture_output=True, text=True, timeout=timeout)
        output, rc = proc.stdout + proc.stderr, proc.returncode
    except subprocess.TimeoutExpired as exc:
        output = "Command timed out\n" + str(exc.stdout or "") + str(exc.stderr or "")
        rc = 124
    logfile = logdir / (name + ".log")
    logfile.write_text(output)
    result = {"ok": rc == 0, "argv": argv, "exit_code": rc,
              "seconds": time.monotonic() - started, "log": str(logfile),
              "log_sha256": sha(logfile), "tail": output[-12000:],
              "isolation": "offline bubblewrap; home/repository hidden"}
    save(logdir / (name + ".json"), result)
    return result


def copy_sources(ws: Path, dest: Path, manifest: dict) -> None:
    dest.mkdir(parents=True, exist_ok=False)
    for name, expected in manifest.items():
        path = dest / name
        path.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ws / name, path)
        if sha(path) != expected:
            raise ValueError(f"Input changed during source-only copy: {name}")


def write_replay(replay: Path, manifest: dict) -> None:
    tools = replay / "tools"
    tools.mkdir(exist_ok=True)
    shutil.copyfile(__file__, tools / "proof_checks.py")
    import inspect
    shutil.copyfile(inspect.getfile(command_prefix), tools / "frozen_exec.py")
    shutil.copyfile(inspect.getfile(strip_comments_and_strings), tools / "scan_sorry.py")
    save(replay / "source-manifest.json", manifest)
    save(replay / "tools-manifest.json", {p.name: sha(p) for p in tools.iterdir() if p.is_file()})
    (replay / "replay.py").write_text('''#!/usr/bin/env python3
"""Independently rebuild certificate source in a new empty destination, offline."""
import hashlib, json, pathlib, sys
base = pathlib.Path(__file__).resolve().parent
for folder, manifest in [('source', 'source-manifest.json'), ('tools', 'tools-manifest.json')]:
    for name, expected in json.loads((base / manifest).read_text()).items():
        if hashlib.sha256((base / folder / name).read_bytes()).hexdigest() != expected:
            raise SystemExit('Certificate hash mismatch: ' + folder + '/' + name)
sys.path.insert(0, str(base / 'tools'))
from proof_checks import check
dest = pathlib.Path(sys.argv[1]).resolve()
if dest.exists():
    raise SystemExit('Replay destination must not exist')
result = check(base / 'source', dest, cold=True)
print(json.dumps(result, indent=2))
raise SystemExit(0 if result['ok'] else 1)
''')


def check(ws: Path, logdir: Path, cold: bool = False) -> dict:
    ws, logdir = Path(ws).resolve(), Path(logdir).resolve()
    result = {"ok": False, "clean_rebuild": cold, "theorem_name": "frozen_equivalence",
              "theorem_type": THEOREM_TYPE,
              "theorem_type_sha256": hashlib.sha256(THEOREM_TYPE.encode()).hexdigest()}
    try:
        manifest = source_manifest(ws)
        result["source_manifest"] = manifest
        for name in ("Imported.lean", "proof.term"):
            hits = scan_authored((ws / name).read_text())
            if hits:
                raise ValueError(f"Forbidden authored constructs in {name}: {hits}")
        if cold:
            replay = logdir / "replay"
            dest = replay / "source"
            copy_sources(ws, dest, manifest)
            write_replay(replay, manifest)
            ws = dest
            result["replay_workspace"] = str(ws)
            result["replay_command"] = f"python3 {replay / 'replay.py'} /absolute/new/destination"
        (ws / "FrozenProof.lean").write_text(HEADER + (ws / "proof.term").read_text() + "\n")
        (ws / "FrozenAudit.lean").write_text(AUDIT)
        for argv, name in [(["lake", "build", "FrozenSpec", "Imported", "FrozenSpecBridge"], "build"),
                           (["lake", "env", "lean", "-o", "FrozenProof.olean", "FrozenProof.lean"], "proof")]:
            status = run(ws, argv, logdir, name)
            if not status["ok"]:
                result.update(failure_stage=name, command=status, tail=status["tail"])
                save(logdir / "result.json", result)
                return result
        target = ws / ".lake/build/lib/lean/FrozenProof.olean"
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ws / "FrozenProof.olean", target)
        status = run(ws, ["lake", "env", "lean", "-o", "FrozenAudit.olean", "FrozenAudit.lean"], logdir, "audit")
        if not status["ok"]:
            result.update(failure_stage="audit", command=status, tail=status["tail"])
        else:
            result.update(axiom_policy(parse_axioms(Path(status["log"]).read_text()), ws))
            result.update(final_impl_sha256=sha(ws / "Imported.lean"),
                          impl_sha256=sha(ws / "Imported.lean"),
                          proof_source_sha256=sha(ws / "FrozenProof.lean"),
                          olean_sha256=sha(ws / "FrozenProof.olean"),
                          semantic_coverage="full", module_checks=True)
        if source_manifest(ws) != manifest:
            raise ValueError("Protected source changed during checking")
        save(ws / "checked-result.json", result)
    except (OSError, ValueError, RuntimeError) as exc:
        result.update(ok=False, failure_stage="checker", tail=str(exc))
    save(logdir / "result.json", result)
    return result


EMITTER = """import Imported
def main : IO Unit := do
  IO.FS.writeFile "emit.rtlil.json" V2LeanImported.impl.interfaceCore.toRtlilJson
  IO.FS.writeFile "emit.wrapper.v" V2LeanImported.impl.interfaceWrapper
"""


def emit(ws: Path, outdir: Path) -> dict:
    """Emit the checked Module directly; never trust an author-editable IO entrypoint."""
    ws, outdir = Path(ws).resolve(), Path(outdir).resolve()
    result = {"ok": False, "roundtrip": False, "jasper": False}
    try:
        accepted = json.loads((ws / "checked-result.json").read_text())
        if not accepted.get("ok") or not accepted.get("clean_rebuild"):
            raise ValueError("Emission requires successful independent cold check")
        if source_manifest(ws) != accepted["source_manifest"]:
            raise ValueError("Checked sources changed before emission")
        for name in ("emit.rtlil.json", "emit.wrapper.v", "emit.core.v", "emit.final.v"):
            (ws / name).unlink(missing_ok=True)
        (ws / "VerifiedEmit.lean").write_text(EMITTER)
        status = run(ws, ["lake", "env", "lean", "--run", "VerifiedEmit.lean"], outdir, "lean-emit")
        if not status["ok"]:
            raise ValueError(status["tail"])
        data = json.loads((ws / "emit.rtlil.json").read_text())
        names = list(data["modules"])
        if len(names) != 1 or not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_$]*", names[0]):
            raise ValueError(f"Unsupported emitted module names: {names}")
        (ws / "emit.ys").write_text("read_json emit.rtlil.json\nhierarchy -check -top " + names[0] +
            "\ncheck -assert\nwreduce -keepdc t:$mul t:$add t:$sub\nopt_clean\nwrite_verilog -noattr emit.core.v\n")
        status = run(ws, ["yosys", "-Q", "-T", "-s", "emit.ys"], outdir, "yosys-emit")
        if not status["ok"]:
            raise ValueError(status["tail"])
        (ws / "emit.final.v").write_text((ws / "emit.core.v").read_text() + "\n" + (ws / "emit.wrapper.v").read_text())
        status = run(ws, ["iverilog", "-g2012", "-tnull", "emit.final.v"], outdir, "syntax")
        if not status["ok"]:
            raise ValueError(status["tail"])
        outdir.mkdir(parents=True, exist_ok=True)
        for src, dest in (("emit.final.v", "final.v"), ("emit.rtlil.json", "final.rtlil.json"),
                          ("emit.wrapper.v", "wrapper.v")):
            shutil.copyfile(ws / src, outdir / dest)
        result.update(ok=True, final_path=str(outdir / "final.v"),
                      final_verilog_sha256=sha(outdir / "final.v"),
                      final_rtlil_sha256=sha(outdir / "final.rtlil.json"),
                      final_impl_sha256=sha(ws / "Imported.lean"),
                      interface_wrapper=bool((outdir / "wrapper.v").read_text().strip()))
    except (OSError, ValueError, KeyError) as exc:
        result.update(tail=str(exc))
    save(outdir / "result.json", result)
    return result
