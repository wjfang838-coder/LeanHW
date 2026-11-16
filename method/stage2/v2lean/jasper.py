"""Run the combinational SEC template in an isolated project on usr."""
import argparse
import copy
import json
from pathlib import Path
import re
import shlex
import shutil
import subprocess
import tarfile
import uuid

from .pipeline import digest, save_json, ROOT

SSH_OPTIONS = ["-o", "BatchMode=yes", "-o", "ConnectTimeout=15", "-o", "LogLevel=ERROR"]


def only_initial_correspondence_notice(signoff):
    summary = signoff["Signoff Summary"]
    expected = {"Boundary outputs mapping", "Boundary outputs proof", "User cutpoints proof",
                "Imported assertions proof", "Imported covers proof", "Reset value abstraction",
                "X signals and undrivens", "Mapped stopats", "Assumption management", "Overall SEC status"}
    if set(summary) != expected: return False
    for key, value in summary.items():
        if value["Status"] != ("Incomplete" if key in ("X signals and undrivens", "Overall SEC status") else "Complete"):
            return False
    notice = signoff["X signals and undrivens"]
    return (notice["Status"] == "Incomplete" and notice["Description"].startswith(
        "The SEC proof has some uninitialized variables (X initialized) mapped to each other.")
        and all(value["Status"] == "Complete" for key, value in signoff["Assumption management"].items()
                if isinstance(value, dict)))


def only_read_correspondence_notice(signoff):
    """Accept exactly the observed combined notice, with all other gates intact."""
    expected = (ROOT / 'method/stage2/v2lean/templates/read_correspondence_notice.txt').read_text().strip()
    if signoff.get('X signals and undrivens', {}).get('Description', '').strip() != expected:
        return False
    initial = copy.deepcopy(signoff)
    initial['X signals and undrivens']['Description'] = (
        'The SEC proof has some uninitialized variables (X initialized) mapped to each other.')
    return only_initial_correspondence_notice(initial)


def initial_pairs(run_dir, report, evidence_dir=None, *, force_bits=False):
    """Corresponding Q bits for the first bound, never persistent assumptions.

    Jasper's default analysis ignores Verilog initial blocks. Local statecheck
    separately verifies those exact constraints; proving from ALL corresponding
    states is stronger than proving only from the initialized subset.
    """
    module = json.loads((run_dir / "import.rtlil.json").read_text())["modules"][report["input"]["top"]]
    parsed = subprocess.run(["yosys", "-Q", "-T", "-p", "read_verilog -sv -dump_ast1 roundtrip.v"],
                            cwd=run_dir, capture_output=True, text=True, timeout=30, check=True)
    source_parsed = subprocess.run(["yosys", "-Q", "-T", "-p", "read_verilog -sv -dump_ast1 original.v"],
                                   cwd=run_dir, capture_output=True, text=True, timeout=30, check=True)
    if evidence_dir:
        (evidence_dir / "mapping_frontend.log").write_text(parsed.stdout + parsed.stderr + source_parsed.stdout + source_parsed.stderr)
    source_storage = set()
    for line in source_parsed.stdout.splitlines():
        if ("AST_WIRE" in line or "AST_MEMORY" in line) and re.search(r"\breg\b", line.split("str=", 1)[-1].split("'", 2)[-1]):
            match = re.search(r"str='\\([^']+)'", line)
            if match: source_storage.add(match[1])
    def source_rank(name):
        return (name.rsplit(".", 1)[-1].split("[", 1)[0] not in source_storage, name)
    physical_regs = set()
    for line in parsed.stdout.splitlines():
        if "AST_WIRE" in line and re.search(r"\breg\b", line.split("str=", 1)[-1].split("'", 2)[-1]):
            match = re.search(r"str='\\([^']+)'", line)
            if match: physical_regs.add(match[1])
    gate_module = json.loads((run_dir / "state_gate.json").read_text())["modules"][report["input"]["top"]]
    physical_gate_nets = [(n, net) for n, net in gate_module["netnames"].items()
                          if (n in physical_regs or n.rsplit(".", 1)[-1] in physical_regs)
                          and n.startswith(report.get("semantics", {}).get("gate_scope", ""))]
    source_physical_bits = {b for n, net in module["netnames"].items()
                            if not source_rank(n)[0] for b in net["bits"]}
    pairs = []
    for state in report.get("import", {}).get("states", []):
        whole = [(n, net) for n, net in module["netnames"].items()
                 if not net.get("hide_name") and net["bits"] == state["bits"]
                 and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.\[\]]*", n)]
        gate_register = state.get("gate_register", state["register"])
        gate_bits = gate_module["netnames"][gate_register]["bits"]
        # Yosys may coalesce several state buses into one physical output reg.
        # Find the actual contiguous slice, not merely an equal-width alias.
        gate_aliases = []
        for n, net in physical_gate_nets:
            try: start = net["bits"].index(gate_bits[0])
            except ValueError: continue
            if net["bits"][start:start + len(gate_bits)] == gate_bits:
                gate_aliases.append((len(net["bits"]), n, start, net))
        if gate_aliases:
            _, imp_name, gate_start, imp_net = min(gate_aliases, key=lambda item: item[:2])
        else:
            imp_name, gate_start, imp_net = gate_register, 0, gate_module["netnames"][gate_register]
        def gate_ref(index=None):
            def position(i):
                bit = gate_start + i
                return imp_net.get("offset", 0) + (len(imp_net["bits"]) - 1 - bit if imp_net.get("upto") else bit)
            if len(imp_net["bits"]) == 1 and not imp_net.get("offset", 0): return imp_name
            if index is not None or state["width"] == 1:
                return f"{imp_name}[{position(index or 0)}]"
            return f"{imp_name}[{position(state['width'] - 1)}:{position(0)}]"
        # A whole-bus wire alias can combine constants and real flops. Prefer
        # slices of actual source registers over such aliases for -init.
        physical_bits = any(b in source_physical_bits for b in state["bits"])
        if not force_bits and whole and (any(not source_rank(n)[0] for n, _ in whole) or not physical_bits):
            name, net = sorted(whole, key=lambda item: source_rank(item[0]))[0]
            lo, hi = net.get("offset", 0), net.get("offset", 0) + state["width"] - 1
            spec = name if state["width"] == 1 and lo == 0 else name + (f"[{lo}:{hi}]" if net.get("upto") else f"[{hi}:{lo}]")
            imp = gate_ref()
            pairs.append((spec, report["input"]["top"] + "_imp." + imp))
            continue
        for index, bit in enumerate(state["bits"]):
            choices = [(n, net) for n, net in module["netnames"].items()
                       if not net.get("hide_name") and bit in net["bits"]
                       and re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.\[\]]*", n)]
            if not choices: raise ValueError(f"no source HDL name for initial-state bit {bit}")
            name, net = sorted(choices, key=lambda x: (source_rank(x[0])[0], len(x[1]["bits"]), x[0]))[0]
            position = net["bits"].index(bit)
            offset = net.get("offset", 0)
            position = offset + (len(net["bits"]) - 1 - position if net.get("upto") else position)
            spec = name if len(net["bits"]) == 1 and not offset else f"{name}[{position}]"
            imp = gate_ref(index)
            pairs.append((spec, report["input"]["top"] + "_imp." + imp))
    for mem in report.get("import", {}).get("memories", []):
        source = mem["source_memid"].removeprefix("\\")
        target = report.get("semantics", {}).get("gate_scope", "") + mem["name"]
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", source):
            raise ValueError("unsupported source memory identifier for SEC")
        if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_.]*", target):
            raise ValueError("unsupported emitted memory identifier for SEC")
        for address in range(mem.get("size", 1 << mem["aw"])):
            pairs.append((f"{source}[{address}][{mem['dw']-1}:0]",
                          f"{report['input']['top']}_imp.{target}[{address}][{mem['dw']-1}:0]"))
    return pairs


def command(argv, log, *, stdin=None, timeout=60):
    try:
        proc = subprocess.run(argv, input=stdin, capture_output=True, text=True, timeout=timeout)
    except subprocess.TimeoutExpired as exc:
        Path(log).write_text(str(exc))
        raise
    Path(log).write_text(proc.stdout + proc.stderr)
    save_json(str(log) + ".command.json", {"argv": argv, "stdin_script": stdin, "exit_code": proc.returncode})
    return proc


def run_sec(run_dir, *, host="usr", gate="roundtrip.v", label="jasper_sec", helpers=False, initial_bits=False, timeout=180, read_unknowns=False, trace=False):
    run_dir = Path(run_dir).resolve()
    if type(timeout) is not int or timeout <= 0:
        raise ValueError("SEC timeout must be a positive integer number of seconds")
    if not re.fullmatch(r"[A-Za-z0-9_.@-]+", host) or host.startswith("-"):
        raise ValueError("invalid SSH host")
    if not re.fullmatch(r"[A-Za-z0-9_-]+", label):
        raise ValueError("invalid run label")
    if not re.fullmatch(r"[A-Za-z0-9_.-]+", gate):
        raise ValueError("gate must be a named artifact in the run directory")
    if read_unknowns and (helpers or gate != 'roundtrip.v'):
        raise ValueError('read-X certification requires the actual roundtrip.v and no helper variant')
    if trace and (helpers or read_unknowns):
        raise ValueError('trace mode currently supports the standard SEC template only')
    report = json.loads((run_dir / "report.json").read_text())
    for name in ("original.v", "roundtrip.v", "Imported.lean"):
        if digest(run_dir / name) != report["artifact_hashes"][name]:
            raise ValueError(f"artifact changed since import/export: {name}")
    top = report["input"]["top"]
    if not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", top):
        raise ValueError("unsupported top identifier")
    out = run_dir / label
    out.mkdir(exist_ok=False)
    sequential = bool(report.get("import", {}).get("states") or report.get("import", {}).get("memories"))
    template = ("sec_helpers.tcl" if helpers else "sec_free.tcl") if sequential else "sec_comb.tcl"
    if read_unknowns:
        template = 'sec_read_unknowns.tcl'
    if trace:
        template = 'sec_trace.tcl'
    for src, dst in ((run_dir / "original.v", "original.v"), (run_dir / gate, "roundtrip.v"),
                     (ROOT / "method/stage2/v2lean/templates" / template, "sec.tcl")):
        shutil.copyfile(src, out / dst)
    def output_signal(port):
        n, _, w, _, offset, upto = port
        if w == 1:
            scalar = (n in report['interface']['scalar_ports']) if 'scalar_ports' in report['interface'] else offset == 0
            return n if scalar else f"{n}[{offset}]"
        lo, hi = offset, offset + w - 1
        return n + (f"[{lo}:{hi}]" if upto else f"[{hi}:{lo}]")
    # Physical inout observations are part of the interface contract as well.
    # If Jasper does not expose the expected property, the query must fail;
    # silently omitting that bus could certify a broken drive path.
    outputs = [output_signal(p) for p in report["interface"]["ports"] if p[1] in ("output", "inout")]
    if not outputs or any(not re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*(\[-?[0-9]+(?::-?[0-9]+)?\])?", n) for n in outputs):
        raise ValueError("unsupported or empty output list")
    pairs = initial_pairs(run_dir, report, out, force_bits=initial_bits) if sequential else []
    certificate = None
    if read_unknowns:
        from .read_unknowns import certify
        certificate = certify(run_dir, out)
    (out / "config.tcl").write_text(f"set v2lean_top {{{top}}}\nset v2lean_outputs {{" + " ".join("{" + n + "}" for n in outputs) + "}\n"
        + "set v2lean_initial_pairs {" + " ".join("{{" + a + "} {" + b + "}}" for a, b in pairs) + "}\n")
    if certificate:
        with (out / 'config.tcl').open('a') as config:
            config.write('set v2lean_read_pairs {' + ' '.join('{{' + a + '} {' + b + '}}'
                         for a, b in certificate['pairs']) + '}\n')
    files = ["original.v", "roundtrip.v", "sec.tcl", "config.tcl"]
    if certificate:
        files.append('read_correspondence.json')
    hashes = {name: digest(out / name) for name in files}
    (out / "SHA256SUMS").write_text("".join(f"{sha}  {name}\n" for name, sha in hashes.items()))
    remote = f"/tmp/v2lean-{uuid.uuid4().hex}"
    result = {"status": "running", "host": host, "remote_dir": remote,
              "input_hashes": hashes, "semantics": "sequential; free-running clocks; no reset assumptions" if sequential else "combinational_two_state; no clock or reset"}
    result["initial_state_correspondence"] = pairs
    result["initial_mapping_granularity"] = "bit" if initial_bits else "bus_preferred"
    result["state_helper_assertions"] = bool(helpers and sequential)
    result["timeout_seconds"] = timeout
    trace_files = (['unknown_signals.tsv'] + [f'trace_{i}_{side}.vcd'
                   for i in range(len(outputs)) for side in ('spec', 'imp')]) if trace else []
    result['trace_requested'] = bool(trace)
    if certificate:
        result['read_correspondence'] = certificate
        result['semantics'] += '; corresponding arbitrary undefined read values, no constants'
    save_json(out / "result.json", result)
    try:
        ssh = ["ssh", *SSH_OPTIONS, host, "/bin/bash", "-s"]
        proc = command(ssh, out / "prepare.log", stdin=f"set -eu\numask 077\nmkdir {shlex.quote(remote)}\n")
        if proc.returncode:
            raise RuntimeError("remote preparation failed")
        proc = command(["scp", *SSH_OPTIONS, *[str(out / n) for n in files + ["SHA256SUMS"]], f"{host}:{remote}/"], out / "upload.log")
        if proc.returncode:
            raise RuntimeError("upload failed")
        script = f'''set -eu
export LC_ALL=C
cd {shlex.quote(remote)}
sha256sum -c SHA256SUMS > hashes.before.log
jg -version > version.log 2>&1
set +e
timeout --signal=TERM --kill-after=15s {timeout}s jg -sec -batch -no_wait -proj project -tcl sec.tcl > run.log 2>&1
v2lean_jg_rc=$?
set -e
printf '%s\\n' "$v2lean_jg_rc" > exit_code.txt
sha256sum -c SHA256SUMS > hashes.after.log
# A timed-out GUI backend can still flush its diagnostic session files. A
# changing optional session archive must not prevent collecting the exit code,
# proof status and logs needed to classify that timeout accurately.
if ! tar -czf session.tar.gz project > session_archive.log 2>&1; then
  mv session.tar.gz session.incomplete.tar.gz
fi
v2lean_evidence=()
for v2lean_file in version.log run.log run_status.txt exit_code.txt hashes.before.log hashes.after.log signoff.json signoff.txt mapping.txt properties.tsv helpers.tsv read_signals.tsv session.tar.gz session_archive.log {' '.join(trace_files)}; do
  if [ -f "$v2lean_file" ]; then v2lean_evidence+=("$v2lean_file"); fi
done
tar -czf evidence.tar.gz "${{v2lean_evidence[@]}}"
'''
        proc = command(ssh, out / "remote.log", stdin=script, timeout=timeout + 60)
        result["remote_exit_code"] = proc.returncode
        # Fetch each named result so an absent signoff cannot be mistaken for success.
        required = ["version.log", "run.log", "run_status.txt", "exit_code.txt", "hashes.before.log", "hashes.after.log"]
        optional = ["signoff.json", "signoff.txt", "mapping.txt", "properties.tsv", "helpers.tsv", "session.tar.gz", "session_archive.log"]
        optional.extend(trace_files)
        if certificate:
            required.append('read_signals.tsv')
        fetched = command(["scp", *SSH_OPTIONS, f"{host}:{remote}/evidence.tar.gz", str(out / "evidence.tar.gz")], out / "fetch.log")
        if fetched.returncode:
            raise RuntimeError("missing remote evidence archive")
        # Only named regular members are copied; never extract arbitrary paths.
        with tarfile.open(out / "evidence.tar.gz", "r:gz") as archive:
            members = {m.name: m for m in archive.getmembers()}
            for name in required + optional:
                member = members.get(name)
                if member is None:
                    if name in required: raise RuntimeError(f"missing remote artifact {name}")
                    continue
                if not member.isfile(): raise RuntimeError(f"nonregular evidence artifact {name}")
                with archive.extractfile(member) as stream:
                    (out / name).write_bytes(stream.read())
        result["jg_exit_code"] = int((out / "exit_code.txt").read_text().strip())
        result["completion"] = (out / "run_status.txt").read_text().strip()
        result["status"] = "completed_pending_signoff_review" if result["completion"] == "COMPLETE" else "tool_error"
        if result["jg_exit_code"] in (124, 137):
            result["status"] = "timeout"
        if result["completion"] == "COMPLETE" and result["jg_exit_code"] == 0 and proc.returncode == 0:
            signoff = json.loads((out / "signoff.json").read_text())
            properties = dict(line.split("\t") for line in (out / "properties.tsv").read_text().splitlines())
            result["properties"] = properties
            result["overall_sec_status"] = signoff["Signoff Summary"]["Overall SEC status"]["Status"]
            result["version"] = signoff["Session"]["Version"]
            exact_targets = set(properties) == set(outputs) and bool((out / "mapping.txt").read_text().strip())
            if certificate:
                observed_reads = [line.split('\t') for line in (out / 'read_signals.tsv').read_text().splitlines()]
                exact_targets = exact_targets and observed_reads == certificate['pairs']
                exact_targets = exact_targets and all(digest(run_dir / n) == sha
                    for n, sha in certificate['local_artifact_hashes'].items())
                exact_targets = exact_targets and all(digest(out / n) == sha
                    for n, sha in certificate['proof_artifact_hashes'].items())
            if helpers and sequential:
                helper_status = dict(line.split("\t") for line in (out / "helpers.tsv").read_text().splitlines())
                expected_helpers = {f"<embedded>::v2lean_helper_{i}:{a}_{b}" for i, (a, b) in
                                    enumerate((a, b) for a, b in pairs if a not in outputs)}
                result["helper_properties"] = helper_status
                exact_targets = exact_targets and set(helper_status) == expected_helpers and all(v == "proven" for v in helper_status.values())
            hashes_ok = all((out / f"hashes.{stage}.log").read_text().splitlines() == [f"{n}: OK" for n in files] for stage in ("before", "after"))
            result["hash_checks"] = "pass" if hashes_ok else "fail"
            if (certificate and exact_targets and hashes_ok and pairs
                    and all(status == 'proven' for status in properties.values())
                    and only_read_correspondence_notice(signoff)):
                result['status'] = 'diagnostic_pass_with_read_correspondence'
                result['signoff_limitation'] = ('All outputs proved with certified initial-state and undefined-read '
                    'correspondence; this is not an initial-only or full-signoff pass. No X-propagation freedom claim.')
            elif exact_targets and hashes_ok and all(status == "proven" for status in properties.values()) and result["overall_sec_status"] == "Complete" and not certificate:
                result["status"] = "pass"
            elif (not certificate and exact_targets and hashes_ok and pairs and all(s == "proven" for s in properties.values())
                  and only_initial_correspondence_notice(signoff)
                  and report.get("local_precheck", {}).get("status") == "pass"
                  and report.get("model_checks", {}).get("status") == "pass" and gate == "roundtrip.v"):
                result["status"] = "pass_with_initial_correspondence"
                result["signoff_limitation"] = "Overall SEC status is Incomplete only for intentional unconstrained initial-state correspondence; X-propagation freedom is not claimed."
            elif exact_targets and hashes_ok and any(status == "cex" for status in properties.values()):
                result["status"] = "counterexample"
            else:
                result["status"] = "unknown"
        result["artifact_hashes"] = {name: digest(out / name) for name in required + optional if (out / name).exists()}
        if (out / "mapping_frontend.log").exists():
            result["artifact_hashes"]["mapping_frontend.log"] = digest(out / "mapping_frontend.log")
        if certificate:
            for name in ['read_correspondence.json', *certificate['proof_artifact_hashes']]:
                result['artifact_hashes'][name] = digest(out / name)
    except Exception as exc:
        result["status"] = "timeout" if isinstance(exc, subprocess.TimeoutExpired) else "tool_error"
        result["error"] = str(exc)
    save_json(out / "result.json", result)
    return result


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("run_dir")
    parser.add_argument("--host", default="usr")
    parser.add_argument("--gate", default="roundtrip.v")
    parser.add_argument("--label", default="jasper_sec")
    parser.add_argument("--helpers", action="store_true")
    parser.add_argument("--read-unknowns", action="store_true", help="certified undefined-read correspondence diagnostic; separately classified")
    parser.add_argument("--trace", action="store_true", help="collect unknown-signal categories and counterexample VCDs without altering proof conditions")
    parser.add_argument("--initial-bits", action="store_true", help="express the same initial Q correspondence as individual bit mappings")
    parser.add_argument("--timeout", type=int, default=180, help="Jasper process time limit in seconds")
    args = parser.parse_args()
    result = run_sec(args.run_dir, host=args.host, gate=args.gate, label=args.label, helpers=args.helpers, initial_bits=args.initial_bits, timeout=args.timeout, read_unknowns=args.read_unknowns, trace=args.trace)
    print(json.dumps(result, indent=2))
    raise SystemExit(0 if result["status"] in ("pass", "pass_with_initial_correspondence") else 1)
