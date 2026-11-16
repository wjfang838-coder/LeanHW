import json
from pathlib import Path
import tempfile
import unittest
from refinement_contract import write_contract


class ContractMetadata(unittest.TestCase):
    def test_half_cycle_clocked_uses_edge_adapter_and_explicit_clock(self):
        with tempfile.TemporaryDirectory() as tmp:
            ws = Path(tmp)
            (ws/'iface.json').write_text(json.dumps({
                'module':'divider', 'timebase':'half',
                'inputs':[{'name':'rst_n','width':1,'role':'reset'},
                          {'name':'clk','width':1,'role':'clock'}],
                'outputs':[{'name':'q','width':1}]}))
            (ws/'FrozenSpec.lean').write_text(
                'namespace SpecIR.Gen\nstructure In where\n  rst_n : Nat := 0\n'
                '  clk : Nat := 0\nderiving Repr, Inhabited\n'
                'def renderIn (i : In) := [("rst_n", Val.mk 1 i.rst_n), '
                '("clk", Val.mk 1 i.clk)]\ndef suite := []\nend SpecIR.Gen\n')
            report = {
                'kind':'clocked', 'source_sha256':'fixture',
                'port_order':['rst_n','clk','q'],
                'ports':{
                    'rst_n':{'direction':'input','bits':[0]},
                    'clk':{'direction':'input','bits':[1]},
                    'q':{'direction':'output','bits':[2]},
                }}
            write_contract(ws,'divider',report)
            text = (ws/'FrozenContract.lean').read_text()
            self.assertIn('FrozenRefinement.clocked spec ["clk"] m', text)
            self.assertNotIn('FrozenRefinement.clockedCycle', text)
            self.assertIn('«clk» := i.«clk» % (2 ^ 1)', text)
            self.assertIn('[(' + '"rst_n", 1), ("clk", 1)]', text)

    def test_full_cycle_clocked_uses_cycle_adapter_and_implicit_clock(self):
        with tempfile.TemporaryDirectory() as tmp:
            ws = Path(tmp)
            (ws/'iface.json').write_text(json.dumps({
                'module':'counter', 'timebase':'fullCycle',
                'inputs':[{'name':'rst_n','width':1,'role':'reset'},
                          {'name':'clk','width':1,'role':'clock'}],
                'outputs':[{'name':'q','width':1}]}))
            (ws/'FrozenSpec.lean').write_text(
                'namespace SpecIR.Gen\nstructure In where\n  rst_n : Nat := 0\n'
                'deriving Repr, Inhabited\n'
                'def renderIn (i : In) := [("rst_n", Val.mk 1 i.rst_n)]\n'
                'def suite := []\nend SpecIR.Gen\n')
            report = {
                'kind':'clocked', 'source_sha256':'fixture',
                'port_order':['rst_n','clk','q'],
                'ports':{
                    'rst_n':{'direction':'input','bits':[0]},
                    'clk':{'direction':'input','bits':[1]},
                    'q':{'direction':'output','bits':[2]},
                }}
            write_contract(ws,'counter',report)
            text = (ws/'FrozenContract.lean').read_text()
            self.assertIn('FrozenRefinement.clockedCycle spec ["clk"] m', text)
            self.assertNotIn('«clk» :=', text)
            self.assertIn('[("rst_n", 1)]', text)

    def test_accepts_indented_deriving_clause(self):
        with tempfile.TemporaryDirectory() as tmp:
            ws = Path(tmp)
            (ws/'iface.json').write_text(json.dumps({
                'module':'test', 'timebase':'full',
                'inputs':[{'name':'a','width':1}],
                'outputs':[{'name':'y','width':1}]}))
            (ws/'FrozenSpec.lean').write_text(
                'namespace SpecIR.Gen\nstructure In where\n  a : Nat := 0\n'
                '  deriving Repr, Inhabited\n'
                'def renderIn (i : In) := [("a", Val.mk 1 i.a)]\n'
                'def suite := []\nend SpecIR.Gen\n')
            report = {
                'kind':'symbolic', 'source_sha256':'fixture',
                'port_order':['a','y'],
                'ports':{
                    'a':{'direction':'input','bits':[0]},
                    'y':{'direction':'output','bits':[1]},
                }}
            write_contract(ws,'fixture',report)
            self.assertIn('«a» := i.«a» % (2 ^ 1)',
                          (ws/'FrozenContract.lean').read_text())

    def test_quotes_lean_keyword_input_fields(self):
        with tempfile.TemporaryDirectory() as tmp:
            ws = Path(tmp)
            (ws/'iface.json').write_text(json.dumps({
                'module':'keyword_input', 'timebase':'full',
                'timing':{'active_edge':'posedge'},
                'inputs':[{'name':'in','width':8}],
                'outputs':[{'name':'out','width':1}]}))
            (ws/'FrozenSpec.lean').write_text(
                'namespace SpecIR.Gen\nstructure In where\n  in_ : Nat := 0\n'
                'deriving Repr, Inhabited\n'
                'def renderIn (i : In) := [("in", Val.mk 8 i.in_)]\n'
                'def suite := []\nend SpecIR.Gen\n')
            report = {
                'kind':'symbolic', 'source_sha256':'fixture',
                'port_order':['in','out'],
                'ports':{
                    'in':{'direction':'input','bits':list(range(8))},
                    'out':{'direction':'output','bits':[8]},
                }}
            write_contract(ws,'fixture',report)
            text = (ws/'FrozenContract.lean').read_text()
            self.assertIn('«in_» := i.«in_» % (2 ^ 8)', text)

    def test_uses_explicit_header_order_not_json_key_order(self):
        with tempfile.TemporaryDirectory() as tmp:
            ws=Path(tmp)
            (ws/'iface.json').write_text(json.dumps({'module':'test','timebase':'full',
                'timing':{'active_edge':'posedge'},'inputs':[{'name':'z','width':1},{'name':'a','width':1}],
                'outputs':[{'name':'q','width':1}]}))
            (ws/'FrozenSpec.lean').write_text(
                'namespace SpecIR.Gen\nstructure In where\n  z : Nat := 0\n  a : Nat := 0\n'
                'deriving Repr, Inhabited\n'
                'def renderIn (i : In) := [("z", Val.mk 1 i.z), ("a", Val.mk 1 i.a)]\n'
                'def suite := []\nend SpecIR.Gen\n')
            r={'kind':'symbolic','source_sha256':'fixture','port_order':['z','a','q'],
               'ports':{'a':{'direction':'input','bits':[2]},'q':{'direction':'output','bits':[3]},
                        'z':{'direction':'input','bits':[4]}}}
            write_contract(ws,'fixture',r)
            text=(ws/'FrozenContract.lean').read_text()
            self.assertIn('[("z", 1), ("a", 1)]',text)
            self.assertIn('["z", "a", "q"]',text)
            self.assertNotIn('["a", "q", "z"]',text)
            del r['port_order']
            with self.assertRaises(ValueError):write_contract(ws,'fixture',r)

    def test_system_lower_inputs_append_external_inout_drivers(self):
        with tempfile.TemporaryDirectory() as tmp:
            ws = Path(tmp)
            (ws/'iface.json').write_text(json.dumps({
                'module':'TopModule', 'timebase':'fullCycle',
                'inputs':[{'name':'inputReady','width':1},
                          {'name':'reset_n','width':1},
                          {'name':'clk','width':1,'role':'clock'},
                          {'name':'data','width':16}],
                'outputs':[{'name':'readM','width':1}]}))
            (ws/'FrozenSpec.lean').write_text(
                'namespace SpecIR.Gen\nstructure In where\n  inputReady : Nat := 0\n'
                '  reset_n : Nat := 0\n  clk : Nat := 0\n  data : Nat := 0\n'
                'deriving Repr, Inhabited\n'
                'def renderIn (i : In) := [("inputReady", Val.mk 1 i.inputReady), '
                '("reset_n", Val.mk 1 i.reset_n), ("clk", Val.mk 1 i.clk), '
                '("data", Val.mk 16 i.data)]\ndef suite := []\nend SpecIR.Gen\n')
            report = {
                'kind':'system', 'source_sha256':'fixture',
                'port_order':['readM','data','inputReady','reset_n','clk'],
                'ports':{
                    'readM':{'direction':'output','bits':[0]},
                    'data':{'direction':'inout','bits':list(range(16))},
                    'inputReady':{'direction':'input','bits':[0]},
                    'reset_n':{'direction':'input','bits':[0]},
                    'clk':{'direction':'input','bits':[0]},
                }}
            write_contract(ws,'cpu_fixture',report)
            text = (ws/'FrozenContract.lean').read_text()
            self.assertIn(
                'm.lower.inputs.map fun p => (p.name,p.width)) == '
                '[("inputReady", 1), ("reset_n", 1), ("clk", 1), '
                '("__external_data", 16)]', text)


if __name__=='__main__':unittest.main()
