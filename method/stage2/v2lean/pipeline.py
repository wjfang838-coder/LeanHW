"""Reproducible Verilog import and optional local round-trip checks."""
from collections import Counter
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import signal
import shutil
import subprocess
import time

from .importer import Importer, Unsupported, require

ROOT = Path(__file__).resolve().parents[3]
AST_ALLOWED = {
    "MODULE", "WIRE", "RANGE", "CONSTANT", "ASSIGN", "IDENTIFIER", "CONCAT",
    "REPLICATE", "ADD", "SUB", "MUL", "BIT_AND", "BIT_OR", "BIT_XOR", "BIT_NOT", "TERNARY",
}


def digest(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def save_json(path, value):
    Path(path).write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def lean_run_command(directory, *arguments):
    directory = Path(directory).resolve()
    cache = directory / "lean_cache.json"
    if not cache.exists():
        return ["lake", "env", "lean", "-s", "65536", "--run", str(directory / "Imported.lean"), *arguments]
    binding = json.loads(cache.read_text())
    framework_root = Path(binding.get("framework_root", ROOT))
    for name, sha in binding["files"].items():
        require(digest(directory / name) == sha, f"checked Lean cache changed: {name}")
    for name, sha in binding["framework_hashes"].items():
        require(digest(framework_root / name) == sha, "framework changed since the Lean cache was checked")
    return ["lake", "env", "env", f"LEAN_PATH={directory}:{framework_root / '.lake/build/lib/lean'}",
            "lean", "-s", "65536", "--run", str(directory / "Run.lean"), *arguments]


def run(command, cwd, log, *, timeout=120, stdin=None, check=True):
    started = time.monotonic()
    child = subprocess.Popen(command, cwd=cwd, stdin=subprocess.PIPE, stdout=subprocess.PIPE,
                             stderr=subprocess.PIPE, text=True, start_new_session=True)
    try:
        stdout, stderr = child.communicate(input=stdin, timeout=timeout)
        proc = subprocess.CompletedProcess(command, child.returncode, stdout, stderr)
    except subprocess.TimeoutExpired as error:
        # lake can spawn Lean as a child; killing only lake leaves the timed-out
        # evaluator running indefinitely. Terminate this command's whole group.
        try: os.killpg(child.pid, signal.SIGKILL)
        except ProcessLookupError: pass
        stdout, stderr = child.communicate()
        Path(log).write_text(stdout + stderr + "\n" + str(error))
        save_json(str(log) + ".command.json", {"argv": command, "cwd": str(cwd), "status": "timeout"})
        raise
    Path(log).write_text(proc.stdout + proc.stderr)
    save_json(str(log) + ".command.json", {"argv": command, "cwd": str(cwd),
                                          "exit_code": proc.returncode,
                                          "seconds": time.monotonic() - started})
    if check and proc.returncode:
        raise RuntimeError(f"command failed ({proc.returncode}); see {log}")
    return proc


def audit_ast(log, corpus=False, sequential=False):
    # This consumes Yosys's parser output; it does not attempt to parse Verilog.
    nodes = re.findall(r"^\s+AST_(\w+)\s+<.*$", log, flags=re.MULTILINE)
    if corpus:
        require(nodes and "MODULE" in nodes, "missing parsed modules")
        forbidden = set(nodes) & ({"TASK", "TCALL"} if sequential else {"INITIAL", "POSEDGE", "NEGEDGE", "MEMORY", "TASK", "TCALL"})
        require(not forbidden, f"source constructs need state/event support: {sorted(forbidden)}")
        # Procedural combinational logic is accepted only if proc leaves no state
        # cells, all resulting operators are supported, and external SEC succeeds.
        return {"status": "pass", "ast_nodes": dict(Counter(nodes)),
                "warnings": [s for s in log.splitlines() if "Warning:" in s],
                "source_semantics": "synthesizable RTL; hierarchy flattened; state preserved" if sequential else "synthesizable combinational RTL; hierarchy flattened"}
    require(nodes and nodes.count("MODULE") == 1, "expected one parsed source module")
    unsupported = sorted(set(nodes) - AST_ALLOWED)
    require(not unsupported, f"unsupported source AST constructs: {unsupported}")
    for line in log.splitlines():
        if "AST_CONSTANT" in line:
            match = re.search(r"bits='([^']*)'", line)
            require(match and re.fullmatch("[01]+", match[1]), "unknown or malformed AST constant")
        if "AST_WIRE" in line:
            require(not re.search(r"\b(signed|reg)\b", line), "signed/state source wire unsupported")
    require("Warning:" not in log, "Yosys warning requires explicit review")
    return {"status": "pass", "ast_nodes": dict(Counter(nodes))}


def local_equivalence(directory, top, gate="roundtrip.v", prefix="local_equiv"):
    directory = Path(directory)
    require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", top), "invalid top")
    require(re.fullmatch(r"[A-Za-z0-9_.-]+", gate), "invalid gate artifact name")
    script = f'''read_verilog -sv original.v
hierarchy -check -top {top}
proc
flatten
memory_collect
memory_map -keepdc
rename {top} gold
design -stash gold
read_verilog -sv {gate}
hierarchy -check -top {top}
proc
flatten
memory_collect
memory_map -keepdc
rename {top} gate
design -stash gate
design -copy-from gold -as gold gold
design -copy-from gate -as gate gate
miter -equiv -flatten gold gate equiv
hierarchy -check -top equiv
proc
opt_clean
check -assert
opt -full
techmap
opt -full
abc -g AND
opt_clean
sat -verify -prove trigger 0 -show-inputs -show-outputs -dump_json {prefix}.counterexample.json
'''
    (directory / f"{prefix}.ys").write_text(script)
    proc = run(["yosys", "-Q", "-T", "-s", f"{prefix}.ys"], directory,
               directory / f"{prefix}.log", check=False)
    log = proc.stdout + proc.stderr
    if proc.returncode == 0 and "SAT proof finished - no model found: SUCCESS!" in log:
        status = "pass"
    elif "proof did fail" in log and (directory / f"{prefix}.counterexample.json").exists():
        status = "counterexample"
    else:
        status = "tool_error" if proc.returncode else "unknown"
    result = {"status": status, "semantics": "all combinational two-state inputs",
              "reference_sha256": digest(directory / "original.v"),
              "implementation_sha256": digest(directory / gate), "log": f"{prefix}.log"}
    save_json(directory / f"{prefix}.json", result)
    return result


def roundtrip(manifest_path, output, *, build_framework=True):
    return _convert(manifest_path, output, build_framework=build_framework,
                    framework_root=ROOT, emit_roundtrip=True)


def import_verilog(manifest_path, output, *, build_framework=True, framework_root=None):
    """Import and kernel-check LeanRTL without emission or round-trip/SEC checks.

    ``framework_root`` selects the Lake workspace containing LeanRTL. Importer
    sources are still those of this Python package and are hashed separately.
    Existing lowering-generated X/Z independence checks remain part of import;
    those checks do not emit or compare round-trip Verilog.
    """
    return _convert(manifest_path, output, build_framework=build_framework,
                    framework_root=framework_root or ROOT, emit_roundtrip=False)


def _convert(manifest_path, output, *, build_framework, framework_root, emit_roundtrip):
    framework_root = Path(framework_root).resolve()
    manifest_path = Path(manifest_path).resolve()
    manifest = json.loads(manifest_path.read_text())
    out = Path(output).resolve()
    # Never overwrite previous evidence, even if its prior run failed.
    out.mkdir(parents=True, exist_ok=False)
    report = {"created_utc": datetime.now(timezone.utc).isoformat(), "status": "running"}
    if emit_roundtrip:
        report.update(jasper_sec={"status": "not_run"}, model_checks={"status": "not_run"})
    else:
        report.update(mode="import_only", framework_root=str(framework_root),
                      trusted_boundary="Verilog/Yosys/importer translation is not a Lean equivalence theorem")
    try:
        require(manifest.get("semantics") in ("combinational_two_state", "sequential_two_state"), "unsupported semantics")
        sequential = manifest["semantics"] == "sequential_two_state"
        corpus = manifest.get("profile") == "corpus"
        memory_mode = manifest.get("memory_mode", "mapped")
        require(memory_mode in ("mapped", "native", "auto"), "invalid memory_mode")
        require(memory_mode == "mapped" or (corpus and sequential), "native memory requires sequential corpus profile")
        require(manifest.get("language") in (("verilog", "systemverilog") if corpus else ("verilog",)), "unsupported language")
        for key in ("parameters", "defines", "include_dirs"):
            require(not manifest.get(key), f"prototype does not yet accept {key}")
        require(len(manifest.get("sources", [])) == 1, "prototype requires one source file")
        top = manifest["top"]
        require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", top), "invalid top name")
        src = (manifest_path.parent / manifest["sources"][0]).resolve()
        (out / "original.v").write_bytes(src.read_bytes())
        save_json(out / "manifest.json", manifest)
        report["input"] = {"source": str(src), "sha256": digest(out / "original.v"), "top": top}
        if not emit_roundtrip:
            report["input"].update(manifest_path=str(manifest_path), manifest_sha256=digest(manifest_path))
        report["implementation_hashes"] = {str(p.relative_to(ROOT)): digest(p)
            for p in sorted((ROOT / "method/stage2/v2lean").glob("*.py"))}
        report["framework_hashes"] = {str(p.relative_to(framework_root)): digest(p)
            for p in sorted((framework_root / "method/stage2/framework").rglob("*.lean"))}
        if not emit_roundtrip:
            if not report["framework_hashes"]:
                framework_files = list((framework_root / "LeanRTL").rglob("*.lean"))
                if (framework_root / "LeanRTL.lean").is_file():
                    framework_files.append(framework_root / "LeanRTL.lean")
                report["framework_hashes"] = {str(p.relative_to(framework_root)): digest(p)
                                                for p in sorted(framework_files)}
            require(report["framework_hashes"], "no LeanRTL framework sources in selected Lake workspace")
            report["framework_hashes"].update({name: digest(framework_root / name) for name in
                ("lakefile.toml", "lakefile.lean", "lake-manifest.json", "lean-toolchain")
                if (framework_root / name).is_file()})
        for tool, args in (("yosys", ["yosys", "-V"]), ("lean", ["lake", "env", "lean", "--version"])):
            report.setdefault("tools", {})[tool] = run(args, framework_root, out / f"{tool}_version.log").stdout.strip()
        language_flag = "-sv " if manifest["language"] == "systemverilog" else ""
        memory_pass = "memory_map -keepdc" if memory_mode == "mapped" else "memory_share"
        normalize = f"write_json hierarchy.rtlil.json\nflatten\nmemory_collect\n{memory_pass}\npmuxtree\nopt_expr\nopt_muxtree\nopt_clean\n" if corpus else ""
        preserve_memory = "-nomem2reg " if memory_mode != "mapped" else ""
        script = f'''read_verilog {language_flag}{preserve_memory}-dump_ast1 original.v
hierarchy -check -top {top}
proc
opt_clean
{normalize}check -assert
write_json -noscopeinfo import.rtlil.json
'''
        (out / "frontend.ys").write_text(script)
        frontend = run(["yosys", "-Q", "-T", "-s", "frontend.ys"], out, out / "frontend.log", check=False)
        if frontend.returncode and memory_mode == "auto":
            # Some memories (notably arrays written during async reset) cannot
            # be represented as a native Yosys memory. Preserve the rejected
            # frontend evidence and retry the ordinary register-array lowering.
            for name in ("frontend.ys", "frontend.log", "frontend.log.command.json"):
                shutil.copyfile(out / name, out / ("native_attempt_" + name))
            report["memory_frontend_fallback"] = "native array elaboration failed; retry ordinary array lowering"
            (out / "frontend.ys").write_text(script.replace("-nomem2reg ", ""))
            frontend = run(["yosys", "-Q", "-T", "-s", "frontend.ys"], out, out / "frontend.log")
        elif frontend.returncode:
            raise RuntimeError("Yosys frontend failed; see frontend.log")
        report["frontend"] = audit_ast(frontend.stdout + frontend.stderr, corpus=corpus, sequential=sequential)
        design = json.loads((out / "import.rtlil.json").read_text())
        memories = []
        original_ports = design["modules"][top]["ports"]
        if memory_mode != "mapped" and any(c["type"].startswith("$mem") for c in design["modules"][top]["cells"].values()):
            from .memblock_compat import describe, cut_memories
            save_json(out / "native_source.json", design)
            try:
                require(not any(c["type"] == "$dlatch" for c in design["modules"][top]["cells"].values()),
                        "native memory with latches requires mapped lowering")
                require(not any(p.get(k, 0) for p in original_ports.values() for k in ("signed", "upto", "offset")),
                        "native memory with nondefault port layouts requires mapped lowering")
                memories = describe(design["modules"][top])
                cut_module, contracts = cut_memories(design["modules"][top], memories)
            except Unsupported as error:
                if memory_mode == "native": raise
                report["memory_fallback"] = str(error)
                (out / "memory_fallback.ys").write_text(f"read_json native_source.json\nmemory_map -keepdc\nopt_clean\ncheck -assert\nwrite_json -noscopeinfo import.rtlil.json\n")
                run(["yosys", "-Q", "-T", "-s", "memory_fallback.ys"], out, out / "memory_fallback.log")
                design = json.loads((out / "import.rtlil.json").read_text())
                memories = []
            else:
                design = {"modules": {top: cut_module}}
                save_json(out / "native_memories.json", memories)
                save_json(out / "native_memory_contracts.source.json", contracts)
                save_json(out / "import.rtlil.json", design)
        if corpus:
            from .lowering import expand_slices
            design, report["slice_lowering"] = expand_slices(out, design, top)
            save_json(out / "import.rtlil.json", design)
        if corpus and any(b in ("x", "z") for c in design["modules"][top].get("cells", {}).values() for bs in c["connections"].values() for b in bs):
            # Only lowering-generated unknowns are eligible. Explicit source
            # X/Z requires a four-state semantics, not this independence proof.
            require(not any(re.search(r"bits='[^']*[xz]", line, re.I) for line in frontend.stdout.splitlines() if "AST_CONSTANT" in line), "explicit source X/Z needs four-state support")
            from .unknowns import eliminate
            save_json(out / "import.before_unknowns.json", design)
            design, report["unknown_normalization"] = eliminate(out, design, top)
            save_json(out / "import.rtlil.json", design)
        if memories:
            from .memblock_compat import NativeImporter
            importer = NativeImporter(design, top, original_ports, memories)
        else:
            importer = Importer(design, top, allow_state=sequential, allow_port_layouts=corpus, allow_bit_cells=corpus,
                                compact_names=corpus, proof_tables=corpus)
        (out / "Imported.lean").write_text(importer.build())
        wrapped = bool(importer.port_layouts)
        core_name = top + "__v2lean_core" if wrapped else top
        instance = next(f"__v2lean_core_{i}" for i in range(len(importer.ports) + 1) if f"__v2lean_core_{i}" not in importer.ports)
        gate_scope = instance + "." if wrapped else ""
        for state in importer.states: state["gate_register"] = gate_scope + state["register"]
        save_json(out / "signal_map.json", {"cells": importer.mapping, "netnames": importer.module.get("netnames", {})})
        report["import"] = {"status": "pass", "cells": dict(Counter(x["type"] for x in importer.mapping)),
                            "wires": len(importer.wires), "registers": len(importer.states), "states": importer.states,
                            "memories": memories}
        report["semantics"] = {"profile": manifest["semantics"], "coverage_reasons": importer.coverage_reasons,
                               "clock": importer.clock, "port_layouts": importer.port_layouts, "gate_scope": gate_scope}
        if build_framework:
            run(["lake", "build", "LeanRTL"], framework_root, out / "framework_build.log", timeout=300)
        run(["lake", "env", "lean", "-s", "65536", "-R", str(out), "-o", str(out / "Imported.olean"), str(out / "Imported.lean")],
            framework_root, out / "lean_check.log", timeout=max(120, min(1200, len(importer.wires) // 3)))
        (out / "Run.lean").write_text("import Imported\n")
        save_json(out / "lean_cache.json", {"files": {n: digest(out / n) for n in ("Imported.lean", "Imported.olean", "Run.lean")},
                                           "framework_hashes": report["framework_hashes"],
                                           **({"framework_root": str(framework_root)} if not emit_roundtrip else {})})
        report["lean_build"] = {"status": "pass", "checks": ["checkErrors", "transitionView.moduleChecksb" if importer.latches or memories else "wellWidthedb" if importer.coverage_reasons else "moduleChecksb", "semanticCoverage"],
                                "coverage_reasons": importer.coverage_reasons}
        if not emit_roundtrip:
            report["status"] = "import_pass"
            report["implementation"] = {"module": "Imported", "symbol": "V2LeanImported.impl",
                                        "source_sha256": digest(out / "Imported.lean"),
                                        "olean_sha256": digest(out / "Imported.olean")}
            return report
        run(lean_run_command(out, "export", str(out / "export.rtlil.json")),
            ROOT, out / "lean_export.log")
        verilog = "core.v" if wrapped else "roundtrip.v"
        (out / "export.ys").write_text(f"read_json export.rtlil.json\nhierarchy -check -top {core_name}\ncheck -assert\nwreduce -keepdc t:$mul t:$add t:$sub\nopt_clean\nwrite_verilog -noattr {verilog}\n")
        run(["yosys", "-Q", "-T", "-s", "export.ys"], out, out / "verilog_export.log")
        if wrapped:
            run(lean_run_command(out, "wrapper", str(out / "interface_wrapper.v")), ROOT, out / "interface_wrapper.log")
            (out / "roundtrip.v").write_text((out / "core.v").read_text() + "\n" + (out / "interface_wrapper.v").read_text())
        report["export"] = {"status": "pass", "interface_wrapper": wrapped}
        (out / "interface.ys").write_text(f"read_verilog roundtrip.v\nhierarchy -check -top {top}\nproc\nwrite_json interface.json\n")
        run(["yosys", "-Q", "-T", "-s", "interface.ys"], out, out / "interface.log")
        ports = json.loads((out / "interface.json").read_text())["modules"][top]["ports"]
        def signature(ps):
            return [(n, p["direction"], len(p["bits"]), p.get("signed", 0), p.get("offset", 0), p.get("upto", 0)) for n, p in ps.items()]
        require(signature(ports) == signature(importer.ports), "emitted interface/order changed")
        report["interface"] = {"status": "pass", "ports": signature(ports)}
        if memories:
            from .memorycheck import check as memory_check
            report["local_precheck"] = memory_check(out, top, importer.states, memories)
            report["import"]["memories"] = json.loads((out / "native_memories.json").read_text())
        elif importer.states:
            from .statecheck import check as state_check
            report["local_precheck"] = state_check(out, top, importer.states)
        else:
            report["local_precheck"] = local_equivalence(out, top)
        if report["local_precheck"]["status"] != "pass":
            raise RuntimeError("local equivalence did not pass; see local_equiv.log")
        report["status"] = "local_roundtrip_pass_pending_jasper_and_model_checks"
    except Exception as error:
        report["status"] = "unsupported" if isinstance(error, Unsupported) else "tool_error"
        report["error"] = str(error)
        raise
    finally:
        report["artifact_hashes"] = {name: digest(out / name) for name in
            ("original.v", "Imported.lean", "Imported.olean", "Run.lean", "lean_cache.json", "slices_input.json", "slices_output.json", "slices.ys", "slices.log", "import.before_unknowns.json", "unknown_gold.json", "unknown_gate.json", "unknown_proof.ys", "unknown_proof.log", "unknown_proof.json", "import.rtlil.json", "export.rtlil.json", "core.v", "interface_wrapper.v", "roundtrip.v", "native_source.json", "native_gate.json", "native_memories.json", "native_memory_contracts.json", "native_port_matching.json", "state_contracts.json", "state_gold.cut.json", "state_gate.cut.json") if (out / name).exists()}
        if not emit_roundtrip:
            report["artifact_hashes"].update({p.name: digest(p) for p in out.iterdir()
                                              if p.is_file() and p.name != "report.json"})
        save_json(out / "report.json", report)
    return report
