"""Certificate boundary regressions; optional offline Lean integration with V2LEAN_INTEGRATION=1."""
import json
import os
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

sys.path.insert(0, str(Path(__file__).resolve().parent))
import proof_checks as pc


class ProtocolTests(unittest.TestCase):
    def test_forbidden_terms_and_override_forms(self):
        for text in ("by sorry", "by admit", "by exact sorryAx _ false", "axiom foo : False",
                     "by native_decide", "by run_tac pure ()", "@[implemented_by x] def y := 1",
                     "attribute [extern x] y", "#eval IO.println 42", "unsafe def x := 1"):
            with self.subTest(text=text):
                self.assertTrue(pc.scan_authored(text))
        self.assertEqual(pc.scan_authored('by bv_decide\n/- sorry /- admit -/ -/\n-- native_decide\n'), [])
        self.assertEqual(pc.scan_authored('def message := "sorry and unsafe"'), [])

    def test_missing_or_duplicate_audit_cannot_pass(self):
        output = "'frozen_equivalence' depends on axioms: [propext, Quot.sound]\n"
        self.assertEqual(pc.parse_axioms(output, ("frozen_equivalence",)),
                         {"frozen_equivalence": ["propext", "Quot.sound"]})
        for text in ("", output + output, "'other' does not depend on any axioms\n"):
            with self.assertRaises(ValueError):
                pc.parse_axioms(text, ("frozen_equivalence",))

    def test_cold_copy_omits_forged_build_caches_and_rejects_symlinks(self):
        with tempfile.TemporaryDirectory() as directory:
            ws = Path(directory) / "ws"
            ws.mkdir()
            for name in ("FrozenSpec.lean", "Imported.lean", "FrozenSpecBridge.lean", "proof.term",
                         "lean-toolchain", "lakefile.toml"):
                (ws / name).write_text("source")
            (ws / ".lake/build").mkdir(parents=True)
            (ws / ".lake/build/FrozenSpec.olean").write_text("forged")
            (ws / "FrozenProof.olean").write_text("forged")
            manifest = pc.source_manifest(ws)
            dest = Path(directory) / "cold"
            pc.copy_sources(ws, dest, manifest)
            self.assertFalse((dest / ".lake").exists())
            self.assertFalse((dest / "FrozenProof.olean").exists())
            (ws / "Imported.lean").unlink()
            (ws / "Imported.lean").symlink_to(ws / "FrozenSpec.lean")
            with self.assertRaises(ValueError):
                pc.source_manifest(ws)

    def test_native_lrat_requires_complete_override_audit(self):
        with tempfile.TemporaryDirectory() as directory:
            ws = Path(directory)
            for name in ("FrozenSpec.lean", "Imported.lean", "FrozenSpecBridge.lean", "proof.term",
                         "lean-toolchain", "lakefile.toml", "FrozenProof.lean", "FrozenAudit.lean"):
                (ws / name).write_text("")
            ax = {"frozen_equivalence": ["frozen_equivalence._native.bv_decide.ax_1_1"]}
            self.assertTrue(pc.axiom_policy(ax, ws)["ok"])
            (ws / "Imported.lean").write_text("@[implemented_by other] def unsafeReflection := true")
            result = pc.axiom_policy(ax, ws)
            self.assertFalse(result["ok"])
            self.assertEqual(result["native_override_hijacks"], ["Imported.lean"])
            self.assertFalse(pc.axiom_policy({"x": ["customAx"]}, ws)["ok"])


@unittest.skipUnless(os.environ.get("V2LEAN_INTEGRATION") == "1", "offline Lean integration opt-in")
class LeanIntegrationTests(unittest.TestCase):
    def test_replay_emission_and_negative_controls(self):
        pilot = pc.ROOT / "data_v2lean/runs/pilot-001/verilogeval/Prob001_zero/proof"
        with tempfile.TemporaryDirectory(prefix="v2lean-verifier-test-") as directory:
            base = Path(directory)
            result = pc.check(pilot, base / "check", cold=True)
            self.assertTrue(result["ok"], result)
            self.assertTrue(result["kernel_only"])
            ws = Path(result["replay_workspace"])
            emitted = pc.emit(ws, base / "emission")
            self.assertTrue(emitted["ok"], emitted)
            self.assertTrue(Path(emitted["final_path"]).is_file())
            replay = subprocess.run([sys.executable, str(ws.parent / "replay.py"), str(base / "second")],
                                    capture_output=True, text=True, timeout=3600)
            self.assertEqual(replay.returncode, 0, replay.stdout + replay.stderr)
            impl = ws / "Imported.lean"
            original = impl.read_text()
            impl.write_text(original.replace('portLayouts := []',
                'portLayouts := [{ name := "zero", signed := true }]'))
            wrapped = pc.check(ws, base / "wrapped-check", cold=True)
            self.assertTrue(wrapped["ok"], wrapped)
            wrapped_emission = pc.emit(Path(wrapped["replay_workspace"]), base / "wrapped-emission")
            self.assertTrue(wrapped_emission["ok"], wrapped_emission)
            self.assertTrue(wrapped_emission["interface_wrapper"])
            self.assertIn("output signed zero", (base / "wrapped-emission/wrapper.v").read_text())
            impl.write_text(original.replace("BitVec.ofNat 1 0", "BitVec.ofNat 1 1"))
            rejected_emit = pc.emit(ws, base / "changed-emission")
            self.assertFalse(rejected_emit["ok"])
            self.assertIn("changed", rejected_emit["tail"])
            rejected = pc.check(ws, base / "wrong-output")
            self.assertFalse(rejected["ok"])
            self.assertEqual(rejected["failure_stage"], "proof")
            # A correct output theorem alone cannot certify timed hardware outside
            # Module.simulate. Remove the importer's optional coverage example so
            # the independent driver's mandatory gate is what rejects it.
            timed = original.replace("  clock := none", "  stepDelay := some 1\n  clock := none")
            timed = timed.replace("example : impl.semanticCoverage = .full := by decide +kernel", "")
            impl.write_text(timed)
            rejected = pc.check(ws, base / "out-of-model")
            self.assertFalse(rejected["ok"])
            self.assertEqual(rejected["failure_stage"], "audit", rejected)
            impl.write_text(original)
            (ws / "proof.term").write_text("by sorry\n")
            rejected = pc.check(ws, base / "admitted")
            self.assertFalse(rejected["ok"])
            self.assertIn("Forbidden", rejected["tail"])


if __name__ == "__main__":
    unittest.main()
