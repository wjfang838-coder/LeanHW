import copy
import unittest

from v2lean.statecheck import cut


class StateContractTests(unittest.TestCase):
    def setUp(self):
        self.module = {"ports": {"clk": {"direction": "input", "bits": [2]},
                                  "d": {"direction": "input", "bits": [3]},
                                  "q": {"direction": "output", "bits": [4]}},
                       "netnames": {"_v2l_reg_0": {"bits": [4], "attributes": {}}},
                       "cells": {"flop": {"type": "$dff", "parameters": {"WIDTH": "1", "CLK_POLARITY": "1"},
                                             "connections": {"CLK": [2], "D": [3], "Q": [4]}}}}
        self.states = [{"cell": "flop", "register": "_v2l_reg_0"}]

    def test_state_is_arbitrary_shared_input(self):
        module, contract = cut(self.module, self.states, emitted=False)
        self.assertEqual(module["cells"], {})
        self.assertEqual(module["ports"]["_v2l_reg_0"], {"direction": "input", "bits": [4]})
        self.assertEqual(contract[0]["initial_bits_lsb"], ["x"])
        self.assertEqual(module["ports"]["v2lean_state_0_CLK"]["bits"], [2])

    def test_added_initial_value_and_changed_edge_are_observable(self):
        _, original = cut(self.module, self.states, emitted=False)
        for mutation in ("initial", "edge"):
            gate = copy.deepcopy(self.module)
            if mutation == "initial": gate["netnames"]["_v2l_reg_0"]["attributes"]["init"] = "0"
            else: gate["cells"]["flop"]["parameters"]["CLK_POLARITY"] = "0"
            _, changed = cut(gate, self.states, emitted=True)
            self.assertNotEqual(original, changed)

    def test_unmatched_storage_rejected(self):
        self.module["cells"]["extra"] = {"type": "$dlatch"}
        with self.assertRaises(ValueError): cut(self.module, self.states, emitted=False)

    def test_low_latch_compares_active_enable_without_constraining_q(self):
        self.module["cells"]["flop"] = {"type": "$dlatch", "parameters": {"WIDTH": "1", "EN_POLARITY": "0"},
            "connections": {"EN": [2], "D": [3], "Q": [4]}}
        self.module["ports"]["unused"] = {"direction": "input", "bits": [100]}
        cut_module, contract = cut(self.module, self.states, emitted=False)
        self.assertEqual(contract[0]["parameters"]["EN_POLARITY"], 1)
        invert = cut_module["cells"]["v2lean_state_0_active_enable"]
        self.assertEqual(invert["connections"], {"A": [2], "Y": [101]})
        self.assertEqual(cut_module["ports"]["v2lean_state_0_EN"]["bits"], [101])
        self.assertEqual(contract[0]["initial_bits_lsb"], ["x"])
