import copy
import unittest

from v2lean.importer import Importer, Unsupported
from v2lean.pipeline import audit_ast


def design():
    return {"modules": {"top": {
        "ports": {"a": {"direction": "input", "bits": [2, 3]},
                  "b": {"direction": "input", "bits": [4, 5]},
                  "sel": {"direction": "input", "bits": [6]},
                  "y": {"direction": "output", "bits": [7, 8]}},
        "cells": {"choose": {"type": "$mux", "parameters": {"WIDTH": "10"},
                             "port_directions": {"A": "input", "B": "input", "S": "input", "Y": "output"},
                             "connections": {"A": [2, 3], "B": [4, 5], "S": [6], "Y": [7, 8]}}},
        "netnames": {}}}}


class ImportTests(unittest.TestCase):
    def test_connection_semantics(self):
        importer = Importer(design(), "top")
        importer.build()
        # Asymmetric reorder/repetition exercises LSB-first chunk reconstruction.
        actual = importer.bus([3, 2, 3, "1"])
        self.assertEqual(actual.width, 4)
        self.assertIn('.slice 1 1 (.var "a" 2)', actual.code)
        self.assertIn('@Expr.concat 1 3 (.const (BitVec.ofNat 1 1))', actual.code)

    def test_reject_unsupported_semantics(self):
        for kind in ("$adff", "$dff", "$dlatch", "child", "$_AND_"):
            d = design()
            d["modules"]["top"]["cells"]["choose"]["type"] = kind
            with self.subTest(kind=kind), self.assertRaises(Unsupported):
                Importer(d, "top").build()

    def test_reject_unknown_undriven_and_bad_width(self):
        for bits in (["x", 3], ["z", 3], [99, 3], [2]):
            d = design()
            d["modules"]["top"]["cells"]["choose"]["connections"]["A"] = bits
            with self.subTest(bits=bits), self.assertRaises(Unsupported):
                Importer(d, "top").build()

    def test_reject_multiple_drivers_and_cycles(self):
        d = design()
        d["modules"]["top"]["cells"]["another"] = copy.deepcopy(d["modules"]["top"]["cells"]["choose"])
        with self.assertRaises(Unsupported):
            Importer(d, "top").build()
        d = design()
        d["modules"]["top"]["cells"]["choose"]["connections"]["A"] = [7, 8]
        with self.assertRaises(Unsupported):
            Importer(d, "top").build()

    def test_unknown_metadata_does_not_drive_the_circuit(self):
        d = design()
        m = d["modules"]["top"]
        m["netnames"]["unused_temporary"] = {"bits": ["x", "z"]}
        Importer(d, "top").build()
        m["ports"]["y"]["bits"] = ["x", "z"]
        with self.assertRaises(Unsupported): Importer(d, "top").build()

    def test_reject_source_construct_before_lowering(self):
        for kind in ("INITIAL", "ALWAYS", "MEMORY", "CELL", "TASK"):
            with self.subTest(kind=kind), self.assertRaises(Unsupported):
                audit_ast(f"    AST_MODULE <fixture:1>\n      AST_{kind} <fixture:2>\n")

    def test_dynamic_slice_requires_a_proven_in_range_index(self):
        d = design()
        m = d["modules"]["top"]
        m["ports"]["y"]["bits"] = [7]
        m["cells"] = {"slice": {"type": "$shiftx", "parameters": {
            "A_WIDTH": "100", "B_WIDTH": "10", "Y_WIDTH": "1", "A_SIGNED": "0", "B_SIGNED": "0"},
            "connections": {"A": [2, 3, 4, 5], "B": [2, 3], "Y": [7]},
            "port_directions": {"A": "input", "B": "input", "Y": "output"}}}
        self.assertIn('.shr', Importer(d, "top").build())
        m["cells"]["slice"]["parameters"]["B_SIGNED"] = "1"
        with self.assertRaises(Unsupported): Importer(d, "top").build()
        m["cells"]["slice"]["parameters"]["B_SIGNED"] = "0"
        m["cells"]["slice"]["parameters"]["Y_WIDTH"] = "10"
        m["cells"]["slice"]["connections"]["Y"] = [7, 8]
        m["ports"]["y"]["bits"] = [7, 8]
        with self.assertRaises(Unsupported): Importer(d, "top").build()

    def test_generic_signed_shift_selects_direction_from_count_sign(self):
        d = design()
        m = d["modules"]["top"]
        m["cells"] = {"shift": {"type": "$shift", "parameters": {
            "A_WIDTH": "10", "B_WIDTH": "10", "Y_WIDTH": "10",
            "A_SIGNED": "0", "B_SIGNED": "1"},
            "connections": {"A": [2, 3], "B": [4, 5], "Y": [7, 8]},
            "port_directions": {"A": "input", "B": "input", "Y": "output"}}}
        text = Importer(d, "top").build()
        self.assertIn('.mux (.extract 1', text)
        self.assertIn('.shl', text)
        self.assertIn('.sub (.const (BitVec.ofNat 2 0))', text)
        self.assertIn('.shr', text)

    def test_division_rejects_possible_zero(self):
        d = design()
        m = d["modules"]["top"]
        m["cells"] = {"divide": {"type": "$div", "parameters": {
            "A_WIDTH": "10", "B_WIDTH": "10", "Y_WIDTH": "10", "A_SIGNED": "0", "B_SIGNED": "0"},
            "connections": {"A": [2, 3], "B": [4, 5], "Y": [7, 8]},
            "port_directions": {"A": "input", "B": "input", "Y": "output"}}}
        with self.assertRaises(Unsupported): Importer(d, "top").build()
        m["cells"]["divide"]["connections"]["B"] = ["1", 5]
        Importer(d, "top").build()


if __name__ == "__main__":
    unittest.main()
