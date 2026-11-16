import copy
from pathlib import Path
import tempfile
import unittest

from v2lean.importer import Unsupported
from v2lean.unknowns import abstract_shared_arithmetic, eliminate


class UnknownIndependenceTests(unittest.TestCase):
    def test_arithmetic_abstraction_cannot_hide_unknown_dependence(self):
        def cell(kind, con):
            return {"type": kind, "connections": con,
                    "port_directions": {p: "output" if p == "Y" else "input" for p in con}}
        gold = {"ports": {}, "netnames": {}, "cells": {
            "shared": cell("$mul", {"A": [2], "B": [3], "Y": [6]}),
            "propagate": cell("$not", {"A": [5], "Y": [8]}),
            "tainted": cell("$mul", {"A": [8], "B": [3], "Y": [7]})}}
        gate = copy.deepcopy(gold)
        gate["cells"]["propagate"]["connections"]["A"] = ["0"]
        result = abstract_shared_arithmetic(gold, gate, [5])
        self.assertEqual([entry["cell"] for entry in result], ["shared"])
        self.assertIn("tainted", gold["cells"])
        self.assertEqual(gold["ports"], gate["ports"])

    def test_correlated_guards_hide_unknown_but_observable_unknown_is_rejected(self):
        def mux(a, b, s, y):
            return {"type": "$mux", "parameters": {"WIDTH": "1"},
                    "port_directions": {"A": "input", "B": "input", "S": "input", "Y": "output"},
                    "connections": {"A": [a], "B": [b], "S": [s], "Y": [y]}}
        module = {"ports": {"a": {"direction": "input", "bits": [2]},
                            "s": {"direction": "input", "bits": [3]},
                            "y": {"direction": "output", "bits": [5]}}, "netnames": {},
                  "cells": {"inner": mux("x", 2, 3, 4), "outer": mux(2, 4, 3, 5)}}
        design = {"modules": {"top": module}}
        with tempfile.TemporaryDirectory() as directory:
            normalized, report = eliminate(directory, design, "top")
            self.assertEqual(report["status"], "pass")
            self.assertEqual(normalized["modules"]["top"]["cells"]["inner"]["connections"]["A"], ["0"])
            self.assertEqual(design["modules"]["top"]["cells"]["inner"]["connections"]["A"], ["x"])
        bad = copy.deepcopy(design)
        bad["modules"]["top"]["cells"]["outer"]["connections"]["A"] = [4]
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaises(Unsupported): eliminate(directory, bad, "top")
            self.assertTrue((Path(directory) / "unknown.counterexample.json").exists())
