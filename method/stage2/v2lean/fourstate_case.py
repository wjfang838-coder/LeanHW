"""Three-way four-state simulation diagnostics, not an unbounded certificate."""
import argparse
import json
from pathlib import Path
import random
import re
import shutil

from .fourstate import FourStateImporter
from .importer import require
from .pipeline import ROOT, digest, run, save_json


def run_case(source, top, out, *, count=128, vectors=None, frontend="yosys"):
    require(type(count) is int and count > 0, "sample count must be positive")
    require(frontend in ("yosys", "slang"), "unknown four-state frontend")
    out = Path(out).resolve()
    require(not out.exists(), "preserve previous evidence; use a new directory")
    require(re.fullmatch(r"[A-Za-z_][A-Za-z0-9_]*", top), "invalid top name")
    out.mkdir(parents=True)
    framework = {str(p.relative_to(ROOT)): digest(p) for p in (ROOT / "method/stage2/framework").rglob("*.lean")}
    implementation = {str(p.relative_to(ROOT)): digest(p) for p in (ROOT / "method/stage2/v2lean").glob("*.py")}
    for name in framework | implementation:
        target = out / "source" / name
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / name, target)
    shutil.copyfile(source, out / "original.v")
    if frontend == "yosys":
        (out / "read.ys").write_text(f"read_verilog -sv original.v\nhierarchy -check -top {top}\n"
                                     "proc -noopt\nflatten\nwrite_json source.json\n")
        run(["yosys", "-Q", "-T", "-s", "read.ys"], out, out / "read.log")
        design = json.loads((out / "source.json").read_text())
        importer = FourStateImporter(design, top, compact_names=True)
    else:
        from .slang import SlangImporter
        importer = SlangImporter(out / "original.v", top)
    (out / "Imported.lean").write_text(importer.build())
    if frontend == "slang": save_json(out / "source.json", importer.metadata)
    targets = ["LeanRTL.Core.FourStateVerilog"] + (["LeanRTL.Core.FourStateProcedural"] if frontend == "slang" else [])
    run(["lake", "build", *targets], ROOT, out / "build.log")
    exported = run(["lake", "env", "lean", "-s", "65536", "--run", str(out / "Imported.lean"), "export", str(out / "emitted.v")],
        ROOT, out / "export.log", timeout=300)
    if frontend == "slang":
        from .slang import audit_source_proofs
        certificate = audit_source_proofs(exported.stdout, importer.metadata)
        certificate["proof_hash"] = digest(out / "Imported.lean")
        save_json(out / "source_certificate.json", certificate)
    ports = importer.ports
    inputs = [(n, len(p["bits"])) for n, p in ports.items() if p["direction"] == "input"]
    outputs = [(n, len(p["bits"])) for n, p in ports.items() if p["direction"] == "output"]
    if vectors is None:
        rng = random.Random(7801)
        vectors = [{n: format((i if w <= 6 else rng.getrandbits(w)) % (1 << w), f"0{w}b")
                    for n, w in inputs} for i in range(count)]
        # Exercise unknown inputs too; deterministic and recorded verbatim.
        for _ in range(count):
            values = {}
            for n, w in inputs:
                bits = list(format(rng.getrandbits(w), f"0{w}b"))
                for _ in range(rng.randrange(1, min(w, 4) + 1)):
                    bits[rng.randrange(w)] = rng.choice("xz")
                values[n] = "".join(bits)
            vectors.append(values)
    require(bool(vectors), "empty simulation does not validate a design")
    for row in vectors:
        require(set(row) == {n for n, _ in inputs}, "vector input set mismatch")
        for n, w in inputs:
            require(len(row[n]) == w and set(row[n]) <= set("01xz"), "invalid vector")
    save_json(out / "vectors.json", vectors)
    input_text = "\n".join(" ".join(f"{n}={row[n]}" for n, _ in inputs) for row in vectors) + "\n"
    fmt = " ".join(n + "=%b" for n, _ in outputs)
    tb = ["module tb;"]
    tb += [f"reg [{w-1}:0] {n};" for n, w in inputs]
    tb += [f"wire [{w-1}:0] {n};" for n, w in outputs]
    tb += [f"{top} dut(" + ",".join(f".{n}({n})" for n in ports) + ");", "initial begin"]
    for row in vectors:
        tb += [" ".join(f"{n} = {w}'b{row[n]};" for n, w in inputs),
               '#1; $display("' + fmt + '",' + ",".join(n for n, _ in outputs) + ");"]
    tb += ["$finish; end endmodule"]
    (out / "tb.v").write_text("\n".join(tb) + "\n")
    traces = {}
    for artifact in ("original", "emitted"):
        run(["iverilog", "-g2012", "-s", "tb", "-o", artifact + ".vvp", artifact + ".v", "tb.v"],
            out, out / (artifact + ".compile.log"))
        p = run(["vvp", artifact + ".vvp"], out, out / (artifact + ".trace.log"))
        # Icarus also prints a $finish location; retain it in the raw log, not as a sample.
        traces[artifact] = [line for line in p.stdout.splitlines() if line.startswith(outputs[0][0] + "=")]
    p = run(["lake", "env", "lean", "-s", "65536", "--run", str(out / "Imported.lean"), "eval"], ROOT,
            out / "lean.trace.log", stdin=input_text, timeout=300)
    traces["lean"] = [line for line in p.stdout.splitlines() if line.startswith(outputs[0][0] + "=")]
    if frontend == "slang": audit_source_proofs(p.stdout, importer.metadata)
    failures = []
    for i, row in enumerate(vectors):
        values = {k: v[i] if i < len(v) else None for k, v in traces.items()}
        if len(set(values.values())) != 1:
            failures.append({"index": i, "inputs": row, "outputs": values})
    lengths_match = all(len(t) == len(vectors) for t in traces.values())
    sources_unchanged = all(digest(ROOT / n) == h for n, h in (framework | implementation).items())
    result = {"status": ("simulation_pass" if not failures and lengths_match else "simulation_mismatch")
                        if sources_unchanged else "source_changed_during_run",
              "scope": "finite four-state samples; no SEC or whole-module proof claimed",
              "frontend": frontend, "samples": len(vectors), "trace_lengths": {k: len(v) for k, v in traces.items()},
              "failures": failures,
              "artifact_hashes": {p.name: digest(p) for p in out.iterdir() if p.is_file()},
              "framework_hashes": framework, "implementation_hashes": implementation}
    save_json(out / "result.json", result)
    return result


if __name__ == "__main__":
    p = argparse.ArgumentParser()
    p.add_argument("source", type=Path)
    p.add_argument("top")
    p.add_argument("out", type=Path)
    p.add_argument("--count", type=int, default=128)
    p.add_argument("--frontend", choices=("yosys", "slang"), default="yosys")
    args = p.parse_args()
    result = run_case(args.source, args.top, args.out, count=args.count, frontend=args.frontend)
    print(json.dumps({k: result[k] for k in ("status", "samples", "trace_lengths")}))
    raise SystemExit(0 if result["status"] == "simulation_pass" else 1)
