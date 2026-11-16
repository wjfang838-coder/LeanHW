"""Version 3 local proof and acceptance feedback; driver repeats it independently."""
import json
import os
from pathlib import Path
import subprocess
import sys
import time

WS=Path(__file__).resolve().parent
sys.path.insert(0,str(WS/'tooling'))

def run(args):
    subprocess.run(args,cwd=WS,check=True)

def main():
    config=json.loads((WS/'local-config.json').read_text())
    run(['lake','build','FrozenSpec','FrozenRefinement','FrozenContract'])
    leanpath=str(WS/'.lake/build/lib/lean')
    if config['arm']=='verilog_correction':
        from v2lean.import_refinement import import_model
        out=WS/'previews'/str(time.time_ns())
        out.parent.mkdir(exist_ok=True)
        import_model(WS/'candidate.v',config['top'],out,kind=config['model_kind'],framework_root=WS,build=False)
        leanpath=str(out)+':'+leanpath
    else:
        run(['lake','build','Imported'])
    target='FrozenRefinement.Refines FrozenContract.spec (FrozenContract.model V2LeanImported.impl)'
    (WS/'LocalProof.lean').write_text('import FrozenContract\nimport Imported\n'
        'set_option maxHeartbeats 16000000\nset_option maxRecDepth 32768\nset_option autoImplicit false\n'
        'theorem frozen_refinement : '+target+' :=\n'+(WS/'proof.term').read_text()+'\n'
        'example : FrozenContract.valid V2LeanImported.impl = true := by decide +kernel\n'
        '#print axioms frozen_refinement\n')
    run(['python3','scan_sorry.py','LocalProof.lean'])
    run(['lake','env','env','LEAN_PATH='+leanpath,'lean','LocalProof.lean'])

if __name__=='__main__': main()
