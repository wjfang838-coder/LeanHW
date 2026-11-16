import importlib.util
from itertools import product
from pathlib import Path
import random
import shutil
import tempfile
import unittest

from v2lean.clocked import ClockedImporter
from v2lean.clocked_case import run_case

FIXTURES=Path(__file__).parent/'fixtures'
AVAILABLE=importlib.util.find_spec('pyslang') is not None and all(shutil.which(t) for t in ('lake','iverilog','vvp'))


@unittest.skipUnless(AVAILABLE,'requires pinned pyslang, Lean and Icarus')
class ClockedTests(unittest.TestCase):
    def test_nonblocking_old_values_overlap_and_last_write(self):
        row={'clk':'0','reset_n':'0','en':'0','d':'0000'}
        vectors=[row.copy()]
        for en in '01xz':
            for bits in product('01xz',repeat=4):
                row.update(clk='0',reset_n='1',en=en,d=''.join(bits)); vectors.append(row.copy())
                row['clk']='1';vectors.append(row.copy())
        with tempfile.TemporaryDirectory() as tmp:
            result=run_case(FIXTURES/'nba_overlap.v','nba_overlap',Path(tmp)/'case',vectors=vectors)
            self.assertEqual(result['status'],'clocked_trace_diagnostic_pass',result['first_mismatch'])
            # These first two active cycles also discriminate blocking semantics:
            # after reset a=0,b=1; first commit a=0,b=1; next b still uses old a=0.
            rows=(Path(tmp)/'case/original.trace.log').read_text().splitlines()
            self.assertIn('a=0000 b=0001',rows)

    def test_signed_dynamic_partial_packed_reads_and_overlapping_writes(self):
        row={'clk':'0','reset_n':'0','index':'0000','d':'000'}
        vectors=[row.copy()]
        rng=random.Random(195)
        indices=[format(i,'04b') for i in range(16)]+['00x1','z100','xxxx','zzzz']
        for index,d in product(indices,map(''.join,product('01xz',repeat=3))):
            row.update(clk='0',reset_n='1',index=index,d=d);vectors.append(row.copy())
            row['clk']=rng.choice('1xz');vectors.append(row.copy())
        with tempfile.TemporaryDirectory() as tmp:
            result=run_case(FIXTURES/'nba_packed.v','nba_packed',Path(tmp)/'case',vectors=vectors)
            self.assertEqual(result['status'],'clocked_trace_diagnostic_pass',result['first_mismatch'])

    def test_fourstate_edge_transitions_and_disjoint_process_commit(self):
        source='''module edges(input clk, input reset_n, output reg [7:0] p, output reg [7:0] n);
always @(posedge clk or negedge reset_n) if (!reset_n) p <= 0; else p <= n+1'b1;
always @(negedge clk or negedge reset_n) if (!reset_n) n <= 0; else n <= p+1'b1;
endmodule'''
        row={'clk':'0','reset_n':'0'};vectors=[row.copy()]
        for reset,old,new in product('01xz',repeat=3):
            row.update(clk=old,reset_n='0');vectors.append(row.copy())
            row['reset_n']=reset;vectors.append(row.copy())
            row['clk']=new;vectors.append(row.copy())
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'edges.v';p.write_text(source)
            result=run_case(p,'edges',Path(tmp)/'case',vectors=vectors)
            self.assertEqual(result['status'],'clocked_trace_diagnostic_pass',result['first_mismatch'])

    def test_reject_unmodeled_clocked_semantics(self):
        cases=[
          ('input clk, input d, output reg q','always @(posedge clk) q = d;', 'nonblocking'),
          ('input clk, input d, output reg q','always @(posedge clk) q <= #1 d;', 'untimed'),
          ('input clk, input d, output reg q','always @(posedge (clk & d)) q <= d;', 'direct input'),
          ('input clk, input d, output reg q','always @(posedge clk) q <= d; always @(negedge clk) q <= d;', 'multiple processes'),
          ('input clk, input d, output reg q','wire missing; always @(posedge clk) q <= missing;', 'undriven'),
          ('input clk, input [1:0] index, output reg [3:0] q','always @(posedge clk) q[index -: 2] <= 0;', 'descending'),
        ]
        for ports,body,message in cases:
            with self.subTest(message=message), tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp)/'bad.v';p.write_text(f'module bad({ports}); {body} endmodule')
                with self.assertRaisesRegex(ValueError,message): ClockedImporter(p,'bad').build()

    def test_same_edge_processes_read_precommit_state(self):
        source='''module parallel_nba(input clk, input reset_n,
output reg [3:0] p, output reg [3:0] q);
always @(posedge clk or negedge reset_n) if (!reset_n) p <= 0; else p <= q;
always @(posedge clk or negedge reset_n) if (!reset_n) q <= 1; else q <= p;
endmodule'''
        vectors=[{'clk':'0','reset_n':'0'},{'clk':'0','reset_n':'1'}]
        for _ in range(8):
            vectors += [{'clk':'1','reset_n':'1'},{'clk':'0','reset_n':'1'}]
        with tempfile.TemporaryDirectory() as tmp:
            p=Path(tmp)/'parallel.v';p.write_text(source)
            result=run_case(p,'parallel_nba',Path(tmp)/'case',vectors=vectors)
            self.assertEqual(result['status'],'clocked_trace_diagnostic_pass',result['first_mismatch'])
            rows=(Path(tmp)/'case/original.trace.log').read_text().splitlines()
            self.assertEqual(rows[2],'p=0001 q=0000')
            self.assertEqual(rows[4],'p=0000 q=0001')


if __name__=='__main__': unittest.main()
