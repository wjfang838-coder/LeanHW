"""Semantic regression tests for the import-only symbolic profile."""
import json
import importlib.util
from pathlib import Path
import shutil
import subprocess
import tempfile
import unittest

from v2lean.import_refinement import import_model
from v2lean.pipeline import ROOT


@unittest.skipUnless(shutil.which('yosys') and shutil.which('lake'), 'requires local Yosys and Lean')
class SymbolicIntegration(unittest.TestCase):
    def check(self, source, assertions, kind='symbolic'):
        with tempfile.TemporaryDirectory(prefix='v2lean-symbolic-') as temp:
            folder=Path(temp)
            rtl=folder/'input.v';rtl.write_text(source)
            out=folder/'import'
            report=import_model(rtl,'test',out,kind=kind,build=False)
            test=out/'Regression.lean'
            test.write_text('import Imported\nimport LeanRTL.Core.Symbolic\nopen LeanRTL.Symbolic\n'
                'set_option maxRecDepth 32768\nset_option maxHeartbeats 4000000\n'+assertions)
            p=subprocess.run(['lake','env','env','LEAN_PATH='+str(out)+':'+str(ROOT/'.lake/build/lib/lean'),
                              'lean',str(test)],cwd=ROOT,text=True,capture_output=True)
            self.assertEqual(p.returncode,0,p.stdout+p.stderr)
            self.assertEqual(report['status'],'import_pass')
            persisted=json.loads((out/'report.json').read_text())
            self.assertEqual(persisted['port_order'],report['port_order'])
            self.assertFalse(report['roundtrip'])
            self.assertFalse(any('roundtrip' in f.name or 'unknown_proof' in f.name for f in out.iterdir()))
            return report

    def test_packed_unknown_bits_remain_independent(self):
        r=self.check("module test(output a,output b); assign a=1'bx; assign b=1'bx; endmodule", '''
example : V2LeanImported.impl.outputs [] [] (fun _ => 1) = [("a",1,1),("b",1,0)] := by decide +kernel
example : V2LeanImported.impl.outputs [] [] (fun _ => 2) = [("a",1,0),("b",1,1)] := by decide +kernel
''')
        self.assertEqual([w for _,w in r['choices']],[2])

    def test_high_impedance_constant_is_a_symbolic_choice(self):
        r=self.check("module test(output a); assign a=1'bz; endmodule", '''
example : V2LeanImported.impl.outputs [] [] (fun _ => 0) = [("a",1,0)] := by decide +kernel
example : V2LeanImported.impl.outputs [] [] (fun _ => 1) = [("a",1,1)] := by decide +kernel
''')
        self.assertEqual([w for _,w in r['choices']],[1])

    def test_high_impedance_async_reset_is_a_symbolic_load(self):
        r=self.check("""module test(input clk,input rst_n,output reg q);
always @(posedge clk or negedge rst_n) begin
  if (!rst_n) q <= 1'bz; else q <= 1'b0;
end
endmodule""", '')
        self.assertEqual([w for _,w in r['choices']],[1])
        self.assertEqual(r['states'][0]['type'],'$aldff')

    def test_division_zero_is_arbitrary_and_nonzero_is_exact(self):
        self.check('module test(input [7:0] a,b, output [7:0] q); assign q=a/b; endmodule', '''
example : V2LeanImported.impl.outputs [] [("a",10),("b",0)] (fun _ => 17) = [("q",8,17)] := by decide +kernel
example : V2LeanImported.impl.outputs [] [("a",10),("b",0)] (fun _ => 91) = [("q",8,91)] := by decide +kernel
example : V2LeanImported.impl.outputs [] [("a",10),("b",2)] (fun _ => 91) = [("q",8,5)] := by decide +kernel
''')

    def test_uninitialized_register_is_not_fixed_zero(self):
        self.check('module test(input clk,input d,output reg q); always @(posedge clk) q<=d; endmodule', '''
example : V2LeanImported.impl.outputs (V2LeanImported.impl.initial (fun _ => 1)) [] (fun _ => 0) = [("q",1,1)] := by decide +kernel
example : V2LeanImported.impl.outputs (V2LeanImported.impl.initial (fun _ => 0)) [] (fun _ => 0) = [("q",1,0)] := by decide +kernel
''')

    def test_physical_order_survives_sorted_json(self):
        r=self.check('module test(input z,input a,output q); assign q=a; endmodule','')
        self.assertEqual(r['port_order'],['z','a','q'])

    @unittest.skipUnless(importlib.util.find_spec('pyslang'), 'requires pinned pyslang')
    def test_initial_forever_preserves_physical_delay(self):
        self.check('''`timescale 1ns/1ps
module test #(parameter PERIOD=10)(output reg q);
initial begin q=0; forever #(PERIOD/2) q=~q; end
endmodule''', '''
example : V2LeanImported.impl.periodFS = 5000000 := by decide +kernel
example : V2LeanImported.impl.renderAt 0 = "0" := by decide +kernel
example : V2LeanImported.impl.renderAt 4999999 = "0" := by decide +kernel
example : V2LeanImported.impl.renderAt 5000000 = "1" := by decide +kernel
example : V2LeanImported.impl.renderAt 10000000 = "0" := by decide +kernel
''', kind='timed')


if __name__=='__main__': unittest.main()
