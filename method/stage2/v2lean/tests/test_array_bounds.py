import shutil
import subprocess
import tempfile
import unittest
from pathlib import Path

from v2lean.array_bounds import prepare


@unittest.skipUnless(shutil.which('yosys') and shutil.which('iverilog'), 'requires RTL tools')
class ArrayBoundsTests(unittest.TestCase):
    def test_guards_preserve_else_binding_and_procedural_x_decision(self):
        source = '''module dut(input clk, input [2:0] idx, input [3:0] d,
output reg q, output rawcmp);
reg [3:0] arr [0:3];
assign rawcmp = arr[idx] > arr[idx+1];
always @(posedge clk) begin
  if (arr[idx] > arr[idx+1]) q <= 1; else q <= 0;
  if (d[0]) arr[idx] <= d; else arr[0] <= 0;
end
endmodule
'''
        tb = '''module tb; reg clk; reg [2:0] idx; reg [3:0] d;wire q,rawcmp;
dut dut(clk,idx,d,q,rawcmp); integer i,j,k;
initial begin clk=0;idx=0;d=0;
for(i=0;i<8;i=i+1) for(j=0;j<16;j=j+1) begin
idx=i;d=j;dut.q=0;for(k=0;k<4;k=k+1) dut.arr[k]=k*3+1;
#5;clk=1;#1;$display("%b %b %b %b %b %b",q,rawcmp,dut.arr[0],dut.arr[1],dut.arr[2],dut.arr[3]);
#4;clk=0;
end $finish;end endmodule
'''
        with tempfile.TemporaryDirectory() as directory:
            out = Path(directory)
            (out/'original.v').write_text(source)
            report = prepare(out, 'dut')
            self.assertEqual(sorted(e['kind'] for e in report['edits']), ['relational_if_bounds', 'write_bound'])
            (out/'tb.v').write_text(tb)
            traces = []
            for name in ('original.v', 'bounds_guarded.v'):
                subprocess.run(['iverilog','-g2012','-s','tb','-o','test.vvp',name,'tb.v'],
                               cwd=out, check=True, capture_output=True)
                result = subprocess.run(['vvp','test.vvp'], cwd=out, check=True, capture_output=True, text=True)
                trace = [s for s in result.stdout.splitlines() if not s.startswith('tb.v:')]
                self.assertEqual(len(trace), 128)
                traces.append(trace)
            self.assertEqual(*traces)

    def test_signed_or_shadowed_indices_are_not_treated_as_unsigned(self):
        sources = [
            '''module dut(input clk,input signed [2:0] idx,input [3:0] d,output [3:0] q);
reg [3:0] arr[0:7];assign q=arr[0];always @(posedge clk) arr[idx]<=d;endmodule
''',
            '''module dut(input clk,input [2:0] idx,input [3:0] d,output [3:0] q);
reg [3:0] arr[0:7];assign q=arr[idx];
always @(posedge clk) begin: local_block
integer idx; idx=-1; arr[idx]<=d;
end endmodule
''']
        for source in sources:
            with self.subTest(source=source), tempfile.TemporaryDirectory() as directory:
                out = Path(directory);(out/'original.v').write_text(source)
                self.assertEqual(prepare(out,'dut')['edits'], [])
                self.assertEqual((out/'bounds_guarded.v').read_text(), source)


if __name__ == '__main__':
    unittest.main()
