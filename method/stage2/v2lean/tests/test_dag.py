from pathlib import Path
import shutil
import tempfile
import unittest

from v2lean.pipeline import ROOT, run


@unittest.skipUnless(shutil.which('lake'),'requires Lean')
class DAGTests(unittest.TestCase):
    def test_local_certificate_and_name_capture_rejection(self):
        source='''import LeanRTL.Core.FourStateDAG
open LeanRTL.FourState
def term : Expr 8 := .mux (.caseEq (.var "a0" 8) (.const 0))
  (.add (.var "a0" 8) (.const 1)) (.xor (.var "a0" 8) (.not (.var "b" 8)))
def original : Wire := {name := "q",width := 8,expr := term}
def block : DAG.CheckedBlock := {
  block := DAG.Block.ofWire "private_" original
  inlined := by source_kernel_rfl
}
example : block.block.valid [("a0",8),("b",8)] = true := by decide +kernel
example : (DAG.Block.ofWire "a" original).valid [("a0",8),("b",8)] = false := by decide +kernel
example (env : Env) :
  eval block.block.result (block.block.locals.foldl Encoding.valueWireStep env) = eval term env :=
  DAG.block_value_correct block [("a0",8),("b",8)] (by decide +kernel) env
'''
        with tempfile.TemporaryDirectory() as tmp:
            tmp=Path(tmp);p=tmp/'Certificate.lean';p.write_text(source)
            run(['lake','build','LeanRTL.Core.FourStateDAG'],ROOT,tmp/'build.log')
            valid=run(['lake','env','lean',str(p)],ROOT,tmp/'valid.log',check=False)
            self.assertEqual(valid.returncode,0,valid.stdout+valid.stderr)
            bad=tmp/'Bad.lean'
            bad.write_text(source+'''\ndef wrong : DAG.CheckedBlock := {
  block := { source := original, locals := [], result := .const 0 }
  inlined := by source_kernel_rfl
}
''')
            result=run(['lake','env','lean',str(bad)],ROOT,tmp/'bad.log',check=False)
            self.assertNotEqual(result.returncode,0)
            self.assertIn('kernel',result.stdout+result.stderr)


if __name__=='__main__':unittest.main()
