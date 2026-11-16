import copy
import json
from pathlib import Path
import tempfile
from types import SimpleNamespace
import unittest
from unittest.mock import patch

from v2lean.jasper import initial_pairs, only_initial_correspondence_notice, only_read_correspondence_notice
from v2lean.pipeline import ROOT


class InitialMappingTests(unittest.TestCase):
    def test_coalesced_physical_register_slices_preserve_bit_positions(self):
        # Two logical states become slices of one emitted output register.
        report = {"input": {"top": "dut"}, "import": {"states": [
            {"register": "r0", "bits": [2, 3, 4], "width": 3},
            {"register": "r1", "bits": [5], "width": 1}]}}
        gold = {"netnames": {"sa": {"bits": [2, 3, 4]}, "sb": {"bits": [5]}}}
        gate = {"netnames": {"r0": {"bits": [12, 13, 14]}, "r1": {"bits": [15]},
                              "joined": {"bits": [12, 13, 14, 15]}}}
        ast = "\n".join("AST_WIRE str='\\" + n + "' reg" for n in ("sa", "sb", "joined"))
        with tempfile.TemporaryDirectory() as directory, patch("v2lean.jasper.subprocess.run",
                return_value=SimpleNamespace(stdout=ast, stderr="")):
            out = Path(directory)
            (out / "import.rtlil.json").write_text(json.dumps({"modules": {"dut": gold}}))
            (out / "state_gate.json").write_text(json.dumps({"modules": {"dut": gate}}))
            self.assertEqual(initial_pairs(out, report), [
                ("sa[2:0]", "dut_imp.joined[2:0]"), ("sb", "dut_imp.joined[3]")])
            gate["netnames"]["joined"].update(offset=4, upto=True)
            (out / "state_gate.json").write_text(json.dumps({"modules": {"dut": gate}}))
            self.assertEqual(initial_pairs(out, report), [
                ("sa[2:0]", "dut_imp.joined[5:7]"), ("sb", "dut_imp.joined[4]")])
            self.assertEqual(initial_pairs(out, report, force_bits=True), [
                ("sa[0]", "dut_imp.joined[7]"), ("sa[1]", "dut_imp.joined[6]"),
                ("sa[2]", "dut_imp.joined[5]"), ("sb", "dut_imp.joined[4]")])


class SignoffTests(unittest.TestCase):
    def setUp(self):
        sections = ["Boundary outputs mapping", "Boundary outputs proof", "User cutpoints proof",
                    "Imported assertions proof", "Imported covers proof", "Reset value abstraction",
                    "X signals and undrivens", "Mapped stopats", "Assumption management", "Overall SEC status"]
        self.signoff = {"Signoff Summary": {n: {"Status": "Complete"} for n in sections},
                        "X signals and undrivens": {"Status": "Incomplete", "Description":
                            "The SEC proof has some uninitialized variables (X initialized) mapped to each other."},
                        "Assumption management": {"Status": "Complete", "Assumptions conflict": {"Status": "Complete"}}}
        for name in ("X signals and undrivens", "Overall SEC status"):
            self.signoff["Signoff Summary"][name]["Status"] = "Incomplete"

    def test_only_the_declared_initial_notice_is_accepted(self):
        self.assertTrue(only_initial_correspondence_notice(self.signoff))
        for section in ("Boundary outputs proof", "Assumption management", "Mapped stopats"):
            changed = copy.deepcopy(self.signoff)
            changed["Signoff Summary"][section]["Status"] = "Incomplete"
            self.assertFalse(only_initial_correspondence_notice(changed))
        self.signoff["X signals and undrivens"]["Description"] = "Unmapped undriven signals"
        self.assertFalse(only_initial_correspondence_notice(self.signoff))

    def test_conflicting_assumptions_and_new_signoff_fields_fail_closed(self):
        self.signoff["Assumption management"]["Assumptions conflict"]["Status"] = "Incomplete"
        self.assertFalse(only_initial_correspondence_notice(self.signoff))
        self.signoff["Assumption management"]["Assumptions conflict"]["Status"] = "Complete"
        self.signoff["Signoff Summary"]["New warning"] = {"Status": "Incomplete"}
        self.assertFalse(only_initial_correspondence_notice(self.signoff))

    def test_read_notice_is_distinct_and_does_not_accept_other_failures(self):
        self.signoff['X signals and undrivens']['Description'] = (
            ROOT / 'method/stage2/v2lean/templates/read_correspondence_notice.txt').read_text().strip()
        self.assertFalse(only_initial_correspondence_notice(self.signoff))
        self.assertTrue(only_read_correspondence_notice(self.signoff))
        for section in ('Boundary outputs proof', 'Mapped stopats', 'Assumption management'):
            bad = copy.deepcopy(self.signoff)
            bad['Signoff Summary'][section]['Status'] = 'Incomplete'
            self.assertFalse(only_read_correspondence_notice(bad))
        self.signoff['X signals and undrivens']['Description'] += '\nUnexpected extra warning'
        self.assertFalse(only_read_correspondence_notice(self.signoff))
