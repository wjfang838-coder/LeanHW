"""Independent exhaustive oracle and negative control for the word_mix fixture."""
import argparse
import json
from pathlib import Path

from .pipeline import ROOT, digest, local_equivalence, run, save_json


def validate(directory):
    out = Path(directory).resolve()
    report = json.loads((out / "report.json").read_text())
    fixture = ROOT / "method/stage2/v2lean/tests/fixtures/word_mix.v"
    if report["input"]["top"] != "word_mix" or digest(out / "original.v") != digest(fixture):
        raise ValueError("this exhaustive mathematical oracle is specific to the unchanged word_mix fixture")
    for name, expected_hash in report["artifact_hashes"].items():
        if digest(out / name) != expected_hash:
            raise ValueError(f"artifact changed since round-trip: {name}")
    vectors = [(a, b, sel) for a in range(256) for b in range(256) for sel in range(2)]
    expected = [(((a + b) & 255) if sel else a ^ (((b & 15) << 4) | (b >> 4)), (a + b) >> 8)
                for a, b, sel in vectors]
    stdin = "".join(f"a={a} b={b} sel={sel}\n" for a, b, sel in vectors)
    lean = run(["lake", "env", "lean", "--run", str(out / "Imported.lean"), "eval"],
               ROOT, out / "lean_eval.log", timeout=180, stdin=stdin)
    lean_outputs = []
    for line in lean.stdout.splitlines():
        values = dict(item.split("=") for item in line.split())
        lean_outputs.append((int(values["y"]), int(values["carry"])))
    if lean_outputs != expected:
        raise AssertionError("Lean semantics differ from exhaustive mathematical oracle")
    tb = '''module tb;
reg [7:0] a, b;
reg sel;
wire [7:0] y;
wire carry;
integer ai, bi, si;
word_mix dut(.a(a), .b(b), .sel(sel), .y(y), .carry(carry));
initial begin
  for (ai=0; ai<256; ai=ai+1)
    for (bi=0; bi<256; bi=bi+1)
      for (si=0; si<2; si=si+1) begin
        a=ai; b=bi; sel=si;
        #1;
        $display("%0d %0d", y, carry);
      end
end
endmodule
'''
    (out / "exhaustive_tb.v").write_text(tb)
    simulations = {}
    for kind, file in (("original", "original.v"), ("roundtrip", "roundtrip.v")):
        run(["iverilog", "-g2012", "-s", "tb", "-o", f"{kind}.simv", "exhaustive_tb.v", file],
            out, out / f"{kind}_compile.log")
        sim = run(["vvp", f"{kind}.simv"], out, out / f"{kind}_eval.log")
        values = [tuple(map(int, line.split())) for line in sim.stdout.splitlines() if line.strip()]
        if values != expected:
            raise AssertionError(f"{kind} Verilog differs from exhaustive mathematical oracle")
        simulations[kind] = {"status": "pass", "vectors": len(values)}
    # Mutate the actual emitted Verilog by wrapping it and inverting one output.
    gate = (out / "roundtrip.v").read_text()
    if gate.count("module word_mix(") != 1:
        raise ValueError("unexpected emitted module header")
    mutant = gate.replace("module word_mix(", "module word_mix_inner(", 1) + '''
module word_mix(input [7:0] a,b, input sel, output [7:0] y, output carry);
wire [7:0] inner_y;
word_mix_inner u(.a(a),.b(b),.sel(sel),.y(inner_y),.carry(carry));
assign y = inner_y ^ 8'h01;
endmodule
'''
    (out / "mutant.v").write_text(mutant)
    negative = local_equivalence(out, "word_mix", "mutant.v", "negative_equiv")
    if negative["status"] != "counterexample":
        raise AssertionError(f"negative control not detected: {negative}")
    # Replay the same exhaustive stimuli on the mutation through an independent simulator.
    run(["iverilog", "-g2012", "-s", "tb", "-o", "mutant.simv", "exhaustive_tb.v", "mutant.v"],
        out, out / "mutant_compile.log")
    mutated = run(["vvp", "mutant.simv"], out, out / "mutant_eval.log")
    actual = [tuple(map(int, line.split())) for line in mutated.stdout.splitlines() if line.strip()]
    if len(actual) != len(expected) or any(y != (ey ^ 1) or c != ec for (y, c), (ey, ec) in zip(actual, expected)):
        raise AssertionError("mutation replay did not show exactly the intended bit flip")
    result = {"status": "pass", "vectors": len(vectors), "input_bits": 17,
              "oracle": "independent Python arithmetic; complete two-state truth table",
              "lean": "pass", "verilog_simulations": simulations,
              "negative_control": negative, "mutation_replay_mismatches": len(actual),
              "artifact_hashes": report["artifact_hashes"],
              "validator_sha256": digest(Path(__file__)),
              "counterexample_example": {"a": 0, "b": 0, "sel": 0, "expected_y": 0, "mutant_y": 1}}
    save_json(out / "model_checks.json", result)
    report["model_checks"] = result
    report["status"] = "local_validated_pending_jasper"
    save_json(out / "report.json", report)
    return {"status": result["status"], "vectors": len(vectors), "negative_control": negative["status"]}


if __name__ == "__main__":
    parser = argparse.ArgumentParser()
    parser.add_argument("run_dir")
    args = parser.parse_args()
    print(json.dumps(validate(args.run_dir), indent=2))
