#!/usr/bin/env python3
"""Reimport the frozen RTL, check source binding, and replay both refinement levels.

The manifest records native finite certificates explicitly. No PDR or simulation
result is used as a premise of the Lean proof.
"""
import argparse
from datetime import datetime, timezone
import hashlib
import json
import os
from pathlib import Path
import re
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parents[1]
REPO = ROOT.parent
BRIDGE = ROOT / 'bridge'
sys.path.insert(0, str(REPO / 'method/stage2'))
MODULES = ['ImportedData','ImportCertificate','NetFacts','WordMath','RawCPU','DecodeSpec',
           'DecoderTable','Circuit','Shallow','Physical','StorageCircuit','DecoderCircuit',
           'ALUCircuit','DecodeFields','ControlCircuit','Forwarding','DispatchCircuit',
           'AcceptCircuit','NetlistStep','SourceRefinement','PacketPC','Events','Audit']
UPPER = ['ISA','Pipeline','Refinement']

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

def run(cmd, log, env, seconds):
    start = time.monotonic()
    with log.open('w') as f:
        p = subprocess.run([str(x) for x in cmd],cwd=REPO,env=env,stdout=f,
                           stderr=subprocess.STDOUT,timeout=seconds)
    if p.returncode:
        raise RuntimeError(f'{cmd[0]} exited {p.returncode}: {log}\n{log.read_text()[-2000:]}')
    return round(time.monotonic()-start,3)

def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--out',type=Path)
    parser.add_argument('--module-seconds',type=int,default=900)
    args = parser.parse_args()
    stamp = datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out = (args.out or ROOT/f'evidence/bridge/{stamp}').resolve()
    out.mkdir(parents=True,exist_ok=False)
    env = dict(os.environ,LEAN_PATH=f'{BRIDGE}:{ROOT}/lean:{REPO}/.lake/build/lib/lean')
    result = dict(status='running',evidence=str(out.relative_to(ROOT)),
                  proof_scope='imported LeanRTL -> frozen cycle LeanSpec -> transaction ISA',
                  started_utc=stamp,modules={},source_binding={})
    path = out/'result.json'
    def save(): path.write_text(json.dumps(result,indent=2)+'\n')
    save()
    try:
        result['lean_version'] = subprocess.check_output(['lean','--version'],text=True).strip()
        result['yosys_version'] = subprocess.check_output(['yosys','-V'],text=True).strip()
        # The frontend is part of the explicitly recorded trust boundary.
        ys = '\n'.join(['read_verilog -sv case_cpu/rtl/cpu.sv','hierarchy -check -top case_cpu',
                        'proc','flatten','memory_collect','memory_map -keepdc','pmuxtree',
                        'opt -nodffe -nosdff','wreduce','opt -nodffe -nosdff',
                        f'write_json -noscopeinfo {out}/import.rtlil.json'])+'\n'
        (out/'import.ys').write_text(ys)
        result['frontend_seconds'] = run(['yosys','-Q','-s',out/'import.ys'],out/'yosys.log',env,300)
        from v2lean.symbolic import SymbolicImporter
        imp = SymbolicImporter(json.loads((out/'import.rtlil.json').read_text()),'case_cpu')
        generated = imp.build()
        (out/'Imported.full.lean.txt').write_text(generated)
        prefix = generated.split('def lintBase',1)[0]+'end V2LeanImported\n'
        if prefix != (BRIDGE/'ImportedData.lean').read_text():
            (out/'ImportedData.expected.lean.txt').write_text(prefix)
            raise RuntimeError('frozen ImportedData differs from a fresh import of rtl/cpu.sv')
        (out/'states.json').write_text(json.dumps(imp.states,indent=2)+'\n')
        (out/'mapping.json').write_text(json.dumps(imp.mapping,indent=2)+'\n')
        result['source_binding'] = dict(status='exact_text_match',rtl_sha256=sha(ROOT/'rtl/cpu.sv'),
            imported_sha256=sha(BRIDGE/'ImportedData.lean'),wires=len(imp.wires),
            register_groups=len(imp.states),choice_ports=imp.choices)
        # The generator emits equations whose proofs bind every shallow node to the AST.
        expected = {n:(BRIDGE/f'{n}.lean').read_bytes() for n in ['Circuit','Shallow']}
        run([sys.executable,ROOT/'scripts/gen_shallow.py'],out/'generator.log',env,30)
        if any((BRIDGE/f'{n}.lean').read_bytes()!=v for n,v in expected.items()):
            raise RuntimeError('shallow generator differs from frozen proof sources')
        sources = [ROOT/'rtl/cpu.sv',ROOT/'scripts/gen_shallow.py',Path(__file__).resolve()]
        sources += [BRIDGE/f'{n}.lean' for n in MODULES]
        sources += [ROOT/f'lean/{n}.lean' for n in UPPER]
        sources += sorted((REPO/'method/stage2/framework').rglob('*.lean'))
        sources += sorted((REPO/'method/stage2/assets/lib').rglob('*.lean'))
        sources += sorted((REPO/'method/stage2/v2lean').glob('*.py'))
        result['sources'] = {str(p.relative_to(REPO)):sha(p) for p in sources}
        for folder,names in [(ROOT/'lean',UPPER),(BRIDGE,MODULES)]:
            for name in names:
                print(f'Checking {name}',flush=True)
                log = out/f'{name}.log'
                elapsed = run(['lean','-j2','-s65536','-o',folder/f'{name}.olean',folder/f'{name}.lean'],
                              log,env,args.module_seconds)
                text = log.read_text()
                if re.search(r'\bsorryAx\b|declaration uses .sorry.|\berror:',text):
                    raise RuntimeError(f'uncertified module: {log}')
                result['modules'][name] = dict(seconds=elapsed,log=str(log.relative_to(ROOT)),
                                               source_sha256=sha(folder/f'{name}.lean'))
                save()
        audit = (out/'Audit.log').read_text()
        axioms = sorted(set(re.findall(r'[\w.]+\._native\.(?:bv_decide|native_decide)\.ax_[\w]+',audit)))
        if 'sorryAx' in audit:
            raise RuntimeError('final theorem depends on sorryAx')
        result['native_certificates'] = axioms
        result['trust_boundary'] = [
            'SystemVerilog/Yosys RTLIL lowering and the symbolic importer (fresh source bound by exact text).',
            'Lean kernel, standard propext/Classical.choice/Quot.sound.',
            'Native LRAT checking for bv_decide finite combinational lemmas.',
            'Native finite evaluation for topology, decoder table and import shape/width checks.'
        ]
        result['quantification'] = 'arbitrary initial environment; first synchronous reset; arbitrary finite subsequent words, seeds, resets, five stalls and all undefined-value choices'
        result['limits'] = ['safety only; no fairness or termination claim',
                            'frontend source equivalence is in the trust boundary, not a theorem about SystemVerilog operational semantics',
                            'native finite certificate trust is explicit; this is not a native-axiom-free proof']
        result['status'] = 'proved'
        result['replay_seconds'] = round(sum(m['seconds'] for m in result['modules'].values()),3)
        save()
        (ROOT/'evidence/bridge-latest.json').write_text(json.dumps(result,indent=2)+'\n')
        print(f"PROVED; {result['replay_seconds']}s certificate replay; {out}",flush=True)
    except BaseException as e:
        result['status']='failed'; result['error']=str(e); save()
        raise

if __name__=='__main__': main()
