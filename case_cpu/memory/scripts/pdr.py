#!/usr/bin/env python3
"""Yosys -> AIGER -> Yosys-bundled ABC PDR. No SMT/BMC fallback."""
import argparse
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import signal
import subprocess
import time

ROOT = Path(__file__).resolve().parents[1]

def invoke(cmd, log, limit):
    start = time.monotonic()
    with log.open('w') as f:
        p = subprocess.Popen(cmd, cwd=ROOT, stdout=f, stderr=subprocess.STDOUT,
                             start_new_session=True)
        timeout = False
        try:
            code = p.wait(timeout=limit)
        except subprocess.TimeoutExpired:
            timeout = True
            os.killpg(p.pid, signal.SIGTERM)
            try:
                code = p.wait(timeout=3)
            except subprocess.TimeoutExpired:
                os.killpg(p.pid, signal.SIGKILL)
                code = p.wait()
    return dict(command=cmd, seconds=round(time.monotonic()-start,3),
                exit_code=code, timeout=timeout, log=str(log.relative_to(ROOT)))

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--task',choices=['full','architecture','order','sanity'],default='full')
    ap.add_argument('--seconds',type=int,default=60)
    ap.add_argument('--synthesis-seconds',type=int,default=180)
    ap.add_argument('--rtl',type=Path,default=ROOT/'rtl/cpu.sv')
    ap.add_argument('--out',type=Path)
    ap.add_argument('--reuse-aig',action='store_true',help='reuse this output directory after checking all source hashes')
    args=ap.parse_args()
    if args.seconds<=0 or args.synthesis_seconds<=0:
        ap.error('time budgets must be positive')
    out=args.out or ROOT/'evidence'/('pdr-'+args.task)
    out=out.resolve(); out.mkdir(parents=True,exist_ok=True)
    # Never retain a counterexample from an older run when this run times out.
    (out/'counterexample.aiw').unlink(missing_ok=True)
    prop=['full','architecture','order','sanity'].index(args.task)
    script=(f'read_verilog -formal -sv -Irtl -DPROPERTY={prop} {args.rtl.resolve()}\n'
            'hierarchy -check -top case_cpu_memory\ndelete -output w:*\n'
            'prep -top case_cpu_memory -flatten\n'
            'async2sync\nchformal -lower\nmemory_map\nopt\n'
            'dffunmap\ntechmap\nsetundef -undriven -anyseq\nabc -fast -g AND\nopt_clean\naigmap\nexpose -input t:$anyseq %x:o\ndelete t:$anyseq\n'
            f'write_aiger -zinit {out}/design.aig\n')
    if not args.reuse_aig:
        (out/'synthesis.ys').write_text(script)
    record=dict(task=args.task,synthesis_script_sha256=hashlib.sha256(script.encode()).hexdigest(),engine='Yosys/ABC PDR',pdr_seconds=args.seconds,
                rtl_sha256=hashlib.sha256(args.rtl.read_bytes()).hexdigest(),
                miter_sha256=hashlib.sha256((ROOT/'rtl/memory_reference.svh').read_bytes()).hexdigest(),
                reference_sha256=hashlib.sha256((ROOT/'rtl/isa_reference.svh').read_bytes()).hexdigest(),
                assumptions=['first edge reset'] + (['equality of the two arbitrary initial RAM arrays'] if prop in [0,1] else []) + ['two-state synchronous semantics'],
                fairness_assumptions=[], auxiliary_invariants=[])
    record['versions']={
        'yosys':subprocess.check_output(['yosys','-V'],text=True).strip(),
        'abc':subprocess.check_output(['yosys-abc','-c','version'],text=True).strip()}
    if args.reuse_aig:
        prior=json.loads((out/'result.json').read_text())
        for key in ['rtl_sha256','miter_sha256','reference_sha256','synthesis_script_sha256']:
            if prior[key]!=record[key]: raise RuntimeError(f'cannot reuse stale AIG: {key}')
        if not (out/'design.aig').is_file(): raise RuntimeError('no AIG to reuse')
        record['synthesis']=dict(prior['synthesis'],reused=True)
    else:
        record['synthesis']=invoke(['yosys','-Q','-T','-s',str(out/'synthesis.ys')],
                                    out/'yosys.log',args.synthesis_seconds)
    syn=record['synthesis']
    if syn['timeout']:
        record['status']='synthesis_timeout'
    elif syn['exit_code']!=0:
        record['status']='synthesis_error'
    else:
        with (out/'design.aig').open('rb') as f:
            header=f.readline().decode().split()
        record['aiger']=dict(zip(['max_variable','inputs','latches','outputs','ands','bad','constraints'],
                                 map(int,header[1:8])))
        if record['aiger'].get('outputs')!=0 or record['aiger'].get('bad',0)<1 or record['aiger'].get('constraints')!=1:
            raise RuntimeError('expected assertions plus exactly one first-reset assumption')
        abc=shutil.which('yosys-abc') or shutil.which('berkeley-abc')
        if not abc:
            record['status']='abc_unavailable'
        else:
            # Explicitly OR all bad outputs: default single-output PDR must not
            # silently check only one assertion of a multi-property AIGER file.
            cmd=f'read_aiger {out}/design.aig; fold; strash; orpos; pdr -v -T {args.seconds}; write_cex -a {out}/counterexample.aiw'
            (out/'pdr.abc').write_text(cmd+'\n')
            record['pdr']=invoke([abc,'-c',cmd],out/'abc.log',args.seconds+10)
            log=(out/'abc.log').read_text()
            if record['pdr']['timeout']:
                record['status']='pdr_timeout'
            elif re.search(r'Output \d+.*asserted in frame',log):
                record['status']='counterexample'
            elif 'Property proved' in log:
                record['status']='proved'
            elif re.search(r'Timeout|Time limit|Reached (?:time|timeout)|UNDECIDED',log,re.I):
                record['status']='pdr_timeout'
            else:
                record['status']='pdr_error_or_unknown'
    (out/'result.json').write_text(json.dumps(record,indent=2)+'\n')
    print(json.dumps(record,indent=2))
    return int(record['status'] in ['synthesis_error','abc_unavailable','pdr_error_or_unknown'])

if __name__=='__main__':
    raise SystemExit(main())
