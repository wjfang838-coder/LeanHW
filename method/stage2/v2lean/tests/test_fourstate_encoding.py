import shutil
from pathlib import Path
import tempfile
import unittest

from v2lean.fourstate_encoding import encode_artifact
from v2lean.pipeline import ROOT, run


class EncodingMutationTests(unittest.TestCase):
    @unittest.skipUnless(all(shutil.which(x) for x in ('yosys', 'lake')), 'requires Yosys and Lean')
    def test_z_to_x_changes_encoded_behavior(self):
        with tempfile.TemporaryDirectory(prefix='v2lean-z-mutation-') as temp:
            p = Path(temp)
            good = "module released(input a, output y); assign y = a ? 1'b1 : 1'bz; endmodule\n"
            (p / 'good.v').write_text(good)
            (p / 'bad.v').write_text(good.replace("1'bz", "1'bx"))
            run(['lake', 'build', 'LeanRTL.Core.FourStateModuleCorrect', 'LeanRTL.Core.FourStateVerilog'],
                ROOT, p / 'build.log')
            encode_artifact(p / 'good.v', 'released', p / 'gold')
            encode_artifact(p / 'bad.v', 'released', p / 'gate')
            (p / 'miter.ys').write_text('''read_verilog gold/encoded.v
rename released_fourstate gold
read_verilog gate/encoded.v
rename released_fourstate gate
miter -equiv -flatten gold gate miter
hierarchy -check -top miter
proc
opt -full
sat -prove trigger 0 -show-inputs -show-outputs -dump_json cex.json
''')
            r = run(['yosys', '-Q', '-T', '-s', 'miter.ys'], p, p / 'miter.log', check=False)
            self.assertEqual(r.returncode, 0)
            self.assertIn('model found: FAIL', r.stdout)
            self.assertTrue((p / 'cex.json').exists())


if __name__ == '__main__':
    unittest.main()
