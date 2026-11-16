"""One-command end-to-end word_mix acceptance, including Jasper negative control."""
import argparse
import json
from pathlib import Path

from .jasper import run_sec
from .pipeline import ROOT, digest, roundtrip, save_json
from .validate_case import validate


def execute(output, host):
    out = Path(output).resolve()
    print("1/4: Import RTLIL, check Lean, export Verilog, prove local equivalence", flush=True)
    roundtrip(ROOT / "method/stage2/v2lean/tests/fixtures/word_mix.json", out)
    print("2/4: Exhaust all 131072 inputs and replay a known incorrect mutation", flush=True)
    validate(out)
    print("3/4: Run Jasper SEC on original vs actual exported Verilog", flush=True)
    positive = run_sec(out, host=host)
    print(f"Jasper original vs roundtrip: {positive['status']}", flush=True)
    print("4/4: Run Jasper SEC on the output-bit mutation", flush=True)
    negative = run_sec(out, host=host, gate="mutant.v", label="jasper_negative")
    print(f"Jasper negative control: {negative['status']}", flush=True)
    report = json.loads((out / "report.json").read_text())
    report["jasper_sec"] = positive
    report["jasper_negative"] = negative
    unchanged = all(digest(out / name) == sha for name, sha in report["artifact_hashes"].items())
    bound = (positive["input_hashes"]["original.v"] == report["artifact_hashes"]["original.v"]
             and positive["input_hashes"]["roundtrip.v"] == report["artifact_hashes"]["roundtrip.v"]
             and negative["input_hashes"]["original.v"] == report["artifact_hashes"]["original.v"]
             and negative["input_hashes"]["roundtrip.v"] == digest(out / "mutant.v"))
    complete = (unchanged and bound and positive["status"] == "pass"
                and negative["status"] == "counterexample"
                and report["model_checks"]["status"] == "pass"
                and report["local_precheck"]["status"] == "pass")
    report["status"] = "roundtrip_pass" if complete else "acceptance_incomplete"
    report["final_artifact_binding"] = "pass" if unchanged and bound else "fail"
    report["scope"] = "word_mix only: combinational two-state behavior, 17 input bits, 9 output bits"
    save_json(out / "report.json", report)
    return report


if __name__ == "__main__":
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("--out", required=True, help="new directory, never overwritten")
    parser.add_argument("--host", default="usr")
    args = parser.parse_args()
    result = execute(args.out, args.host)
    print(json.dumps({"status": result["status"], "report": str(Path(args.out) / "report.json")}, indent=2))
    raise SystemExit(0 if result["status"] == "roundtrip_pass" else 1)
