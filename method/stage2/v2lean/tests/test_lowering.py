import unittest

from v2lean.lowering import _restore_port_order


class LoweringTests(unittest.TestCase):
    def test_slice_lowering_preserves_original_port_order(self):
        # Yosys JSON is alphabetic here; the source interface was not.
        lowered = {
            "done": {"direction": "output"},
            "new_choice": {"direction": "input"},
            "start": {"direction": "input"},
            "yout": {"direction": "output"},
        }
        restored = _restore_port_order(lowered, ["start", "yout", "done"])
        self.assertEqual(list(restored), ["start", "yout", "done", "new_choice"])


if __name__ == "__main__":
    unittest.main()
