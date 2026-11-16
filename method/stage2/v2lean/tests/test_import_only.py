import json
from pathlib import Path
import shutil
import tempfile
import unittest
from unittest.mock import patch

from v2lean import pipeline


@unittest.skipUnless(shutil.which("yosys") and shutil.which("lake"), "requires Yosys and Lean")
class ImportOnlyTests(unittest.TestCase):
    def manifest(self, directory, source, top="top", **options):
        (directory / "source.v").write_text(source)
        manifest = {"sources": ["source.v"], "top": top, "language": "verilog",
                    "semantics": "combinational_two_state", **options}
        path = directory / "case.json"
        pipeline.save_json(path, manifest)
        return path

    def checked_import(self, directory, manifest):
        out = directory / "import"
        with patch.object(pipeline, "local_equivalence", side_effect=AssertionError("roundtrip SAT called")), \
             patch("v2lean.statecheck.check", side_effect=AssertionError("state roundtrip called")), \
             patch("v2lean.memorycheck.check", side_effect=AssertionError("memory roundtrip called")):
            report = pipeline.import_verilog(manifest, out, build_framework=False,
                                              framework_root=pipeline.ROOT)
        self.assertEqual(report["status"], "import_pass")
        self.assertEqual(report["implementation"]["symbol"], "V2LeanImported.impl")
        self.assertEqual(report["implementation"]["source_sha256"], pipeline.digest(out / "Imported.lean"))
        self.assertEqual(report["input"]["sha256"], pipeline.digest(directory / "source.v"))
        self.assertTrue((out / "Imported.olean").stat().st_size)
        self.assertEqual(json.loads((out / "report.json").read_text()), json.loads(json.dumps(report)))
        for name, expected in report["artifact_hashes"].items():
            self.assertEqual(pipeline.digest(out / name), expected)
        for name in ("roundtrip.v", "export.ys", "export.rtlil.json", "local_equiv.ys", "interface.ys"):
            self.assertFalse((out / name).exists(), name)
        for key in ("export", "local_precheck", "jasper_sec", "model_checks"):
            self.assertNotIn(key, report)
        command = json.loads((out / "lean_check.log.command.json").read_text())
        self.assertEqual(command["exit_code"], 0)
        for command_file in out.glob("*.command.json"):
            argv = json.loads(command_file.read_text())["argv"]
            self.assertNotIn("export", argv)
            self.assertNotIn("wrapper", argv)
        return out, report

    def test_combinational_import_and_immutable_output(self):
        with tempfile.TemporaryDirectory(prefix="v2lean-import-") as tmp:
            directory = Path(tmp)
            manifest = self.manifest(directory, "module top(input [7:0] a,b, output [7:0] y); assign y=a+b; endmodule")
            out, _ = self.checked_import(directory, manifest)
            before = (out / "report.json").read_bytes()
            with self.assertRaises(FileExistsError):
                pipeline.import_verilog(manifest, out, build_framework=False)
            self.assertEqual(before, (out / "report.json").read_bytes())

    def test_sequential_and_native_memory(self):
        fixtures = [("top", "module top(input clk, input [7:0] d, output reg [7:0] q); always @(posedge clk) q <= d; endmodule", "mapped"),
                    ("native_memory_only", (pipeline.ROOT / "method/stage2/v2lean/tests/fixtures/native_memory_only.v").read_text(), "native")]
        for top, source, memory_mode in fixtures:
            with self.subTest(memory_mode=memory_mode), tempfile.TemporaryDirectory(prefix="v2lean-import-") as tmp:
                directory = Path(tmp)
                manifest = self.manifest(directory, source, top=top, semantics="sequential_two_state",
                                         profile="corpus", memory_mode=memory_mode)
                _, report = self.checked_import(directory, manifest)
                if memory_mode == "native":
                    self.assertTrue(report["import"]["memories"])
                    self.assertIn("native_memory_contracts.source.json", report["artifact_hashes"])
                else:
                    self.assertEqual(report["import"]["registers"], 1)

    def test_existing_unknown_independence_lowering_is_retained(self):
        with tempfile.TemporaryDirectory(prefix="v2lean-import-") as tmp:
            directory = Path(tmp)
            source = "module top(input [2:0] data, input [2:0] index, output value); assign value = index < 3 ? data[index] : 1'b0; endmodule"
            manifest = self.manifest(directory, source, profile="corpus", language="systemverilog")
            _, report = self.checked_import(directory, manifest)
            self.assertEqual(report["unknown_normalization"]["status"], "pass")

    def test_staged_framework_layout_and_cache_binding(self):
        with tempfile.TemporaryDirectory(prefix="v2lean-staged-import-") as tmp:
            directory = Path(tmp)
            framework = directory / "workspace"
            framework.mkdir()
            shutil.copytree(pipeline.ROOT / "method/stage2/framework/LeanRTL", framework / "LeanRTL")
            shutil.copyfile(pipeline.ROOT / "method/stage2/framework/LeanRTL.lean", framework / "LeanRTL.lean")
            shutil.copyfile(pipeline.ROOT / "lean-toolchain", framework / "lean-toolchain")
            (framework / "lakefile.toml").write_text('name = "import_test"\n[[lean_lib]]\nname = "LeanRTL"\n')
            shutil.copytree(pipeline.ROOT / ".lake/build/lib/lean/LeanRTL",
                            framework / ".lake/build/lib/lean/LeanRTL")
            manifest = self.manifest(directory, "module top(output y); assign y=1'b0; endmodule")
            out = directory / "import"
            report = pipeline.import_verilog(manifest, out, build_framework=False, framework_root=framework)
            self.assertEqual(report["status"], "import_pass")
            self.assertIn("LeanRTL.lean", report["framework_hashes"])
            self.assertIn("lean-toolchain", report["framework_hashes"])
            pipeline.lean_run_command(out, "eval")
            (framework / "LeanRTL.lean").write_text("-- modified dependency\n")
            with self.assertRaisesRegex(pipeline.Unsupported, "framework changed"):
                pipeline.lean_run_command(out, "eval")

    def test_roundtrip_still_runs_existing_export_and_equivalence(self):
        with tempfile.TemporaryDirectory(prefix="v2lean-roundtrip-regression-") as tmp:
            directory = Path(tmp)
            manifest = self.manifest(directory, "module top(input a, output y); assign y=~a; endmodule")
            report = pipeline.roundtrip(manifest, directory / "roundtrip", build_framework=False)
            self.assertEqual(report["status"], "local_roundtrip_pass_pending_jasper_and_model_checks")
            self.assertEqual(report["export"]["status"], "pass")
            self.assertEqual(report["local_precheck"]["status"], "pass")


if __name__ == "__main__":
    unittest.main()
