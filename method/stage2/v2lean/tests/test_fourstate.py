"""Independent Verilog simulation checks the Lean four-state evaluator/emitter."""
import itertools
from pathlib import Path
import shutil
import tempfile
import unittest

from v2lean.fourstate_case import run_case
from v2lean.fourstate_encoding import compare_case


class FourStateSemanticsTests(unittest.TestCase):
    @unittest.skipUnless(all(shutil.which(x) for x in ('yosys', 'iverilog', 'vvp', 'lake')),
                         'requires the HDL and Lean toolchain')
    def test_exhaustive_two_bit_values(self):
        vectors = [dict(a=a+b, b=c+d, s=s)
                   for a, b, c, d, s in itertools.product('01xz', repeat=5)]
        with tempfile.TemporaryDirectory(prefix='v2lean-fourstate-') as temp:
            result = run_case(Path(__file__).parent/'fixtures/fourstate_ops.v', 'fourstate_ops',
                              Path(temp)/'case', vectors=vectors)
            self.assertEqual(result['trace_lengths'], dict(original=1024, emitted=1024, lean=1024))
            self.assertEqual(result['failures'], [])
            self.assertEqual(result['status'], 'simulation_pass')
            encoded = compare_case(Path(temp)/'case', Path(temp)/'encoded')
            self.assertEqual(encoded['status'], 'encoded_diagnostic_pass')
            self.assertTrue(encoded['sample_match'])
            self.assertTrue(encoded['sat_pass'])


if __name__ == '__main__':
    unittest.main()
