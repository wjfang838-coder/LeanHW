"""Physical-time round trips and mutation checks for autonomous signals."""
import importlib.util
from pathlib import Path
import shutil
import tempfile
import unittest

from v2lean.pipeline import ROOT, run
from v2lean.timed import TimedImporter
from v2lean.timed_case import run_case, equivalence_source


@unittest.skipUnless(importlib.util.find_spec('pyslang'), 'optional pyslang dependency')
class TimedTests(unittest.TestCase):
    @unittest.skipUnless(all(shutil.which(n) for n in ('lake','iverilog','vvp')), 'requires Lean and HDL tools')
    def test_word_counter_and_four_state_physical_time(self):
        with tempfile.TemporaryDirectory(prefix='timed-trace-') as tmp:
            for name, period in [('timed_counter',30_000_000), ('timed_fourstate',2000)]:
                with self.subTest(name=name):
                    result=run_case(Path(__file__).parent/'fixtures'/(name+'.v'),name,Path(tmp)/name,ticks=33)
                    self.assertEqual(result['status'],'timed_model_roundtrip_pass')
                    self.assertEqual(result['period_fs'],period)
                    self.assertEqual(result['samples'],100)
                    trace=(Path(tmp)/name/'original.trace.log').read_text()
                    if name=='timed_counter':
                        self.assertIn('0 count=0000',trace)
                        self.assertIn('480000000 count=0000',trace)
                    else:
                        self.assertIn('0 q=01xz',trace)
                        self.assertIn('2000 q=10xx',trace)

    @unittest.skipUnless(shutil.which('lake'), 'requires Lean')
    def test_changed_period_initial_and_update_fail_certificate(self):
        base="`timescale 1ns / 1ps\nmodule m(output reg q); initial q=1'b0; always #5 q=~q; endmodule"
        variants={'period':base.replace('#5','#6'),
                  'initial':base.replace("initial q=1'b0","initial q=1'b1"),
                  'update':base.replace('q=~q','q=q')}
        with tempfile.TemporaryDirectory(prefix='timed-mutation-') as tmp:
            tmp=Path(tmp); source=tmp/'gold.v'; source.write_text(base)
            gold=TimedImporter(source,'m'); gold.build()
            for name, text in variants.items():
                with self.subTest(name=name):
                    gate_path=tmp/(name+'.v'); gate_path.write_text(text)
                    gate=TimedImporter(gate_path,'m'); gate.build()
                    proof=tmp/(name+'.lean'); proof.write_text(equivalence_source(gold,gate))
                    result=run(['lake','env','lean','-s','65536',str(proof)],ROOT,tmp/(name+'.log'),check=False)
                    self.assertNotEqual(result.returncode,0)
                    self.assertIn('timed_models_equal',result.stdout+result.stderr)
                    self.assertIn('(kernel)',result.stdout+result.stderr)

    def test_unmodeled_scheduler_constructs_rejected(self):
        cases=[
          ("module m(output reg q); initial q=0; always #0 q=~q; endmodule",'positive'),
          ("module m(input a,output reg q); initial q=0; always #1 q=a; endmodule",'no inputs'),
          ("module m(output reg q); initial q=0; always #1 q=~q; always #2 q=~q; endmodule",'exactly one'),
          ("module m(output reg q); initial q=0; always begin q=~q; #1; end endmodule",'outside'),
          ("module m(output reg q); initial q=0; always #0.5 q=~q; endmodule",'fractional'),
          ("module m(output reg q); initial begin q=0; $display(\"active\"); end always #1 q=~q; endmodule",'assignment'),
          ("module m(output reg q); initial q=0; always #1 q<=~q; endmodule",'blocking assignments'),
          ("module m(output reg q); initial begin q=1; q=0; end always #5 q=~q; endmodule",'same-time initial'),
          ("module m(output reg q); initial q=0; always #5 begin q=1; q=0; end endmodule",'same-time update'),
        ]
        with tempfile.TemporaryDirectory(prefix='timed-reject-') as tmp:
            path=Path(tmp)/'m.v'
            for text,message in cases:
                with self.subTest(message=message):
                    path.write_text('`timescale 1ns / 1ps\n'+text)
                    with self.assertRaisesRegex(ValueError,message): TimedImporter(path,'m').build()


if __name__=='__main__': unittest.main()
