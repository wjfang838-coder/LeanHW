import importlib.util
from pathlib import Path
import random
import shutil
import tempfile
import unittest

from v2lean.system import SystemImporter
from v2lean.clocked_case import run_case

FIXTURE=Path(__file__).parent/'fixtures/hierarchy_bus.v'
AVAILABLE=importlib.util.find_spec('pyslang') is not None and all(shutil.which(t) for t in ('lake','iverilog','vvp'))


@unittest.skipUnless(AVAILABLE,'requires pinned pyslang, Lean and Icarus')
class SystemTests(unittest.TestCase):
    def test_preserve_scalar_and_explicit_one_bit_vector_ports(self):
        source='''module top(input clk, input [0:0] d, output q, output [0:0] v);
          reg state;
          always @(posedge clk) state <= d;
          assign q = state;
          assign v = state;
        endmodule
        '''
        vectors=[{'clk':clk,'d':d} for d in '01xz' for clk in '01']
        with tempfile.TemporaryDirectory() as tmp:
            src=Path(tmp)/'original.v';src.write_text(source)
            out=Path(tmp)/'case'
            result=run_case(src,'top',out,vectors=vectors,frontend='system')
            self.assertEqual(result['status'],'clocked_trace_diagnostic_pass',result['first_mismatch'])
            import json
            for name in ('source.json','reimported.json'):
                metadata=json.loads((out/name).read_text())
                self.assertEqual(metadata['scalar_ports'],['clk','q'])
            emitted=(out/'emitted.v').read_text()
            for declaration in ('input wire clk;', 'input wire [0:0] d;',
                                'output wire q;', 'output wire [0:0] v;'):
                self.assertIn(declaration,emitted)

    def test_parameterized_nested_hierarchy_resolved_bus_and_nba(self):
        row={'clk':'0','reset_n':'0','d0':'01','d1':'10','ea':'1','eb':'1','select_a':'0','bus':'zz'}
        vectors=[row.copy()];row.update(reset_n='1');vectors.append(row.copy())
        row.update(clk='1');vectors.append(row.copy())
        rng=random.Random(217)
        for _ in range(256):
            row.update(clk='0',d0=''.join(rng.choices('01xz',k=2)),d1=''.join(rng.choices('01xz',k=2)),
                       ea=rng.choice('01xz'),eb=rng.choice('01xz'),select_a=rng.choice('01xz'),
                       bus=''.join(rng.choices('01xz',k=2)))
            vectors.append(row.copy());row['clk']='1';vectors.append(row.copy())
        with tempfile.TemporaryDirectory() as tmp:
            out=Path(tmp)/'case'
            result=run_case(FIXTURE,'hierarchy_bus',out,vectors=vectors,frontend='system')
            self.assertEqual(result['status'],'clocked_trace_diagnostic_pass',result['first_mismatch'])
            self.assertEqual(result['state_bits'],4)
            self.assertEqual(result['samples'],2*len(vectors))
            self.assertIn('observed=xx bus=xx',(out/'original.trace.log').read_text())
            self.assertIn('inout wire [1:0] bus;',(out/'emitted.v').read_text())
            import json
            metadata=json.loads((out/'source.json').read_text())
            self.assertEqual(len(metadata['hierarchy']),4)
            self.assertEqual(len({s['name'] for s in metadata['states']}),2)

    def test_reject_unmodeled_hierarchy_or_event_semantics(self):
        cases=[
          ('module leaf(input clk,inout bus); reg q; always @(posedge clk) q<=bus; endmodule\n'
           'module top(input clk,inout bus); leaf a(clk,bus); endmodule','child inout'),
          ('module top(input clk,output reg q); wire derived=~clk; always @(posedge derived) q<=0; endmodule','internally generated'),
          ('module top(input clk,output reg q); initial q=0; always @(posedge clk) q<=1; endmodule','process timing'),
          ('module top(input clk,output reg q); always @(posedge clk) q<=0; always @(negedge clk) q<=1; endmodule','multiple hierarchy'),
          ('module top(input clk,input en,output reg q); reg s; always @(posedge clk) s<=en; always @* if(en) q=s; endmodule','latch/read'),
        ]
        for text,message in cases:
            with self.subTest(message=message),tempfile.TemporaryDirectory() as tmp:
                p=Path(tmp)/'bad.v';p.write_text(text)
                with self.assertRaisesRegex(ValueError,message):SystemImporter(p,'top').build()


if __name__=='__main__':unittest.main()
