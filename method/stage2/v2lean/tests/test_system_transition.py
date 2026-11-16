import importlib.util
import json
from pathlib import Path
import shutil
import tempfile
import unittest

from v2lean.clocked_case import run_case
from v2lean.pipeline import ROOT, run
from v2lean.system_transition import compare, encode

AVAILABLE=importlib.util.find_spec('pyslang') is not None and all(
    shutil.which(t) for t in ('lake','iverilog','vvp','yosys'))


@unittest.skipUnless(AVAILABLE,'requires pinned pyslang, Lean, Icarus and Yosys')
class SystemTransitionTests(unittest.TestCase):
    def test_all_state_transition_and_mutated_pending_write(self):
        source='''module top(input clk, input reset_n, input [1:0] d,
                    input _0, input _1, inout [1:0] bus, output [1:0] q);
          reg [1:0] state;
          always @(posedge clk or negedge reset_n)
            if (!reset_n) state <= 0; else state <= d;
          assign bus = _0 ? state : 2'bzz;
          assign q = state;
        endmodule
        '''
        # Both used and unused physical inputs occupy candidate private names.
        # Freshness must preserve the actual bus-driver semantics and interface.
        vectors=[{'clk':clk,'reset_n':'1','d':d,'_0':'1','_1':'0','bus':'zz'}
                 for d in ('01','xz') for clk in ('0','1')]
        with tempfile.TemporaryDirectory() as tmp:
            tmp=Path(tmp);src=tmp/'original.v';src.write_text(source)
            case=tmp/'case';out=tmp/'transition'
            run_case(src,'top',case,vectors=vectors,frontend='system')
            result=compare(case,out)
            self.assertEqual(result['status'],'fourstate_transition_diagnostic_pass')
            self.assertEqual(result['state_bits'],2)
            for side in ('gold','gate'):
                statistics=json.loads((out/side/'dag_statistics.json').read_text())
                self.assertGreater(statistics['removed'],0)
                certificate=json.loads((out/side/'certificate.json').read_text())
                self.assertIn('transition_dag_correct',certificate['transition_theorems'])
            # Actual HDL mutation changes only the queued write expression.
            # A trace restricted to X could miss it; the all-state miter must fail.
            mutant=tmp/'mutant.v';mutant.write_text(source.replace('state <= d;', 'state <= ~d;'))
            encode(mutant,'top',out/'mutant')
            script=(out/'miter.ys').read_text().replace('gate/encoded.v','mutant/encoded.v')
            (out/'mutant.ys').write_text(script)
            sat=run(['yosys','-Q','-T','-s','mutant.ys'],out,out/'mutant.log',check=False)
            self.assertNotEqual(sat.returncode,0)
            self.assertIn('proof did fail',sat.stdout+sat.stderr)
            self.assertTrue((out/'cex.json').exists())


if __name__=='__main__':unittest.main()
