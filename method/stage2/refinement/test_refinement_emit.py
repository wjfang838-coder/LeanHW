"""Exercise the trusted serializer on a synthetic symbolic fixture, no roundtrip."""
import json
import os
from pathlib import Path
import subprocess
import tempfile
import unittest
from unittest.mock import patch

import refinement_artifacts
from v2lean.import_refinement import import_model
from v2lean.pipeline import ROOT


class SymbolicEmission(unittest.TestCase):
    def test_choices_hidden_and_physical_header_preserved(self):
        with tempfile.TemporaryDirectory(prefix='refinement-emit-') as tmp:
            root=Path(tmp); source=root/'test.v'
            source.write_text("module test(input z, input a, output q); assign q=a ? 1'bx : z; endmodule")
            ws=root/'model'; r=import_model(source,'test',ws,build=False)
            (ws/'contract.json').write_text(json.dumps({'model_kind':'symbolic', 'top':'test',
                'ports':r['ports'],'port_order':r['port_order']}))
            env=dict(os.environ,LEAN_PATH=str(ws)+':'+str(ROOT/'.lake/build/lib/lean'))
            # Unit-test transport only; production uses the offline frozen executor.
            def local_run(folder,args,logs,name):
                if args[:2]==['lake','env']:
                    args=['lake','env','env','-C',str(folder),*args[2:]]
                    cwd=ROOT
                else: cwd=folder
                p=subprocess.run(args,cwd=cwd,env=env,text=True,capture_output=True)
                return {'ok':p.returncode==0,'tail':p.stdout+p.stderr}
            with patch.object(refinement_artifacts.checks,'run',side_effect=local_run):
                result=refinement_artifacts.emit(ws,root/'emitted')
            self.assertTrue(result['ok'],result)
            text=Path(result['final_path']).read_text()
            self.assertIn('module test(z, a, q);',text)
            self.assertIn("1'bx",text)
            self.assertIn('test__symbolic_implementation',text)
            self.assertFalse(result['roundtrip'])


if __name__=='__main__': unittest.main()
