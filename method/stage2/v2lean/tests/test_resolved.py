"""Four-state external drive resolution and preservation of native inout ports."""
import importlib.util
import itertools
from pathlib import Path
import shutil
import tempfile
import unittest

from v2lean.pipeline import ROOT,run
from v2lean.resolved import ResolvedImporter
from v2lean.resolved_case import run_case,encode,check_encoded_pair
from v2lean.slang import SlangImporter

TOOLS=all(shutil.which(n) for n in ('lake','iverilog','vvp','yosys'))


@unittest.skipUnless(importlib.util.find_spec('pyslang'), 'optional pyslang')
class ResolvedTests(unittest.TestCase):
    @classmethod
    def setUpClass(cls):
        if TOOLS:
            with tempfile.TemporaryDirectory(prefix='resolved-build-') as tmp:
                run(['lake','build','LeanRTL.Core.FourStateNetlist'],ROOT,Path(tmp)/'build.log')

    @unittest.skipUnless(TOOLS,'requires Lean/Yosys/HDL tools')
    def test_exhaustive_scalar_and_mixed_word_drives(self):
        scalar=[dict(zip(['a','b','ea','eb','bus'],xs)) for xs in itertools.product('01xz',repeat=5)]
        words=[''.join(x) for x in itertools.product('01xz',repeat=2)]
        word=[dict(a=a,b=b,ea=ea,eb=eb,data=words[(i+3*j)%16])
              for i,a in enumerate(words) for j,b in enumerate(words) for ea,eb in [('1','1'),('x','1'),('1','z')]]
        word.append(dict(a='10',b='11',ea='1',eb='1',data='zz'))
        with tempfile.TemporaryDirectory(prefix='resolved-positive-') as tmp:
            for name,vectors in [('resolved_bus',scalar),('resolved_word',word)]:
                with self.subTest(name=name):
                    out=Path(tmp)/name
                    r=run_case(Path(__file__).parent/'fixtures'/(name+'.v'),name,out,vectors=vectors)
                    self.assertEqual(r['status'],'resolved_diagnostic_pass')
                    self.assertEqual(r['samples'],len(vectors))
                    if name=='resolved_word':
                        self.assertIn('observed=1x data=1x',(out/'original.trace.log').read_text())

    @unittest.skipUnless(TOOLS,'requires Lean/Yosys/HDL tools')
    def test_missing_driver_is_detected_by_encoded_miter(self):
        source=Path(__file__).parent/'fixtures/resolved_bus.v'
        with tempfile.TemporaryDirectory(prefix='resolved-mutation-') as tmp:
            tmp=Path(tmp);bad=tmp/'bad.v'
            bad.write_text(source.read_text().replace("assign bus = eb ? b : 1'bz;", "assign bus = 1'bz;"))
            encode(source,'resolved_bus',tmp/'gold');encode(bad,'resolved_bus',tmp/'gate')
            self.assertFalse(check_encoded_pair(tmp,'resolved_bus',verify=False))
            self.assertIn('model found: FAIL!',(tmp/'miter.log').read_text())
            self.assertTrue((tmp/'cex.json').exists())

    def test_rejects_unmodeled_resolution(self):
        cases=[
          ('module m(input a,inout wand bus,output y); assign bus=a; assign y=bus; endmodule','net type'),
          ('module m(input a,inout bus,output y); assign (weak1,weak0) bus=a; assign y=bus; endmodule','strength'),
          ('module m(inout bus,output y); assign bus=~bus; assign y=bus; endmodule','cyclic'),
          ('module m(input signed [1:0] a,inout [1:0] bus,output [1:0] y); assign bus=a; assign y=bus; endmodule','signed'),
          ('module m(input a,inout [1:0] bus,output y); assign bus[0]=a; assign y=bus[0]; endmodule','partial/array'),
          ('module m(input clk,inout bus,output reg y); always @(posedge clk) y=bus; endmodule','member'),
        ]
        with tempfile.TemporaryDirectory(prefix='resolved-reject-') as tmp:
            p=Path(tmp)/'m.v'
            for text,message in cases:
                with self.subTest(message=message):
                    p.write_text(text)
                    with self.assertRaisesRegex(ValueError,message): ResolvedImporter(p,'m').build()
            p.write_text('module m(inout bus,output y); assign y=bus; endmodule')
            with self.assertRaisesRegex(ValueError,'inout'): SlangImporter(p,'m')
            with self.assertRaisesRegex(ValueError,'resolved netlist'): SlangImporter(p,'m',allow_inout=True).build()


if __name__=='__main__': unittest.main()
