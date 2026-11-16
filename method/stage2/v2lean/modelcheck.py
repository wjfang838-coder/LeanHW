"""Independent original/Lean/emitted evaluation for arbitrary combinational ports."""
import json
from pathlib import Path
import random

from .pipeline import ROOT, digest, lean_run_command, run, save_json


def check(directory, samples=128):
    out = Path(directory).resolve()
    report = json.loads((out / "report.json").read_text())
    ports = report["interface"]["ports"]
    sequential = bool(report.get("import", {}).get("states") or report.get("import", {}).get("memories"))
    if sequential:
        cut = json.loads((out / "state_gold.cut.json").read_text())["modules"]["gold"]
        ports = [(n, p["direction"], len(p["bits"])) for n, p in cut["ports"].items()]
    inputs = [(n, w) for n, d, w, *_ in ports if d == "input"]
    outputs = [(n, w) for n, d, w, *_ in ports if d == "output"]
    bits = sum(w for _, w in inputs)
    rng = random.Random(report["input"]["sha256"])
    encodings = list(range(1 << bits)) if bits <= 10 else [0, (1 << bits) - 1] + [rng.getrandbits(bits) for _ in range(samples)]
    vectors = []
    for encoding in encodings:
        values = {}
        for name, width in inputs:
            values[name] = encoding & ((1 << width) - 1)
            encoding >>= width
        vectors.append(values)
    stdin = "".join((" ".join(f"{n}={v}" for n, v in vs.items()) or "dummy=0") + "\n" for vs in vectors)
    lean = run(lean_run_command(out, "eval"), ROOT,
               out / "model_lean.log", timeout=180, stdin=stdin)
    lean_values = []
    for line in lean.stdout.splitlines():
        values = dict(v.split("=") for v in line.split())
        lean_values.append(tuple(int(values[n]) for n, _ in outputs))
    if len(lean_values) != len(vectors): raise RuntimeError("Lean returned an unexpected number of vectors")
    decls = [f"{'reg' if d == 'input' else 'wire'} [{w-1}:0] {n};" for n, d, w, *_ in ports]
    conn = ", ".join(f".{n}({n})" for n, *_ in ports)
    fmt = " ".join("%0d" for _ in outputs)
    names = ", ".join(n for n, _ in outputs)
    stimuli = []
    for values in vectors:
        stimuli.append(" ".join(f"{n}={w}'h{values[n]:x};" for n, w in inputs))
        stimuli.append(f'#1; $display("{fmt}", {names});')
    (out / "model_tb.v").write_text("module v2lean_tb;\n" + "\n".join(decls) +
        f"\n{report['input']['top']} dut({conn});\ninitial begin\n" + "\n".join(stimuli) + "\nend\nendmodule\n")
    for source, filename in (("original", "state_gold.cut.v" if sequential else "original.v"),
                             ("roundtrip", "state_gate.cut.v" if sequential else "roundtrip.v")):
        run(["iverilog", "-g2012", "-s", "v2lean_tb", "-o", f"model_{source}.simv", "model_tb.v", filename],
            out, out / f"model_{source}_build.log")
        proc = run(["vvp", f"model_{source}.simv"], out, out / f"model_{source}.log")
        actual = [tuple(map(int, line.split())) for line in proc.stdout.splitlines()]
        if actual != lean_values: raise RuntimeError(f"{source} differs from Lean semantics")
    result = {"status": "pass", "scope": "arbitrary_state_transition_cones" if sequential else "combinational_two_state", "vectors": len(vectors),
              "exhaustive": bits <= 10, "validator_sha256": digest(Path(__file__)),
              "input_sha256": report["input"]["sha256"]}
    report["model_checks"] = result
    save_json(out / "model_checks.json", result)
    save_json(out / "report.json", report)
    return result
