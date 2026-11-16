#!/usr/bin/env python3
"""Reproduce diagnosis, kernel proofs, three-way co-simulation and scripted repairs."""
import argparse
from collections import Counter, deque
from datetime import datetime, timezone
import difflib
import hashlib
import json
import os
from pathlib import Path
import random
import subprocess
import sys
import time

from model import CPU, OPS, R, I, MASK, apply, decode, effect, encode

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent
ENV=dict(os.environ,LEAN_PATH=f'{ROOT}/lean:{REPO}/.lake/build/lib/lean')

def run(cmd,log,timeout=120,env=None):
    start=time.monotonic()
    with log.open('w') as out:
        p=subprocess.run([str(x) for x in cmd],cwd=ROOT,env=env,stdout=out,
                         stderr=subprocess.STDOUT,timeout=timeout)
    if p.returncode:
        raise RuntimeError(f'{cmd[0]} exited {p.returncode}: {log}\n{log.read_text()[-3000:]}')
    return round(time.monotonic()-start,3)

def proof(out):
    sources=['ISA','Pipeline','Refinement','Diagnosis','Mutants','Trace']
    evidence={}
    for name in sources:
        log=out/f'{name}.log'
        seconds=run(['lean','-o',ROOT/f'lean/{name}.olean',ROOT/f'lean/{name}.lean'],log,180,ENV)
        text=log.read_text()
        if 'sorryAx' in text or 'Lean.ofReduceBool' in text or 'error:' in text:
            raise RuntimeError(f'untrusted or unsuccessful proof: {log}')
        evidence[name]=dict(seconds=seconds,log=str(log.relative_to(ROOT)),
                            axiom_audit=[s for s in text.splitlines() if 'axiom' in s])
    findings=[json.loads(s.removeprefix('LEANSPEC:'))
              for s in (out/'Diagnosis.log').read_text().splitlines() if s.startswith('LEANSPEC:')]
    assert findings[-1]['determined'] is True
    assert sum(x.get('separated',False) for x in findings)==3
    assert sum(x.get('free',False) for x in findings)==2
    assert sum(x.get('dead',False) for x in findings)==2
    (out/'diagnosis.json').write_text(json.dumps(findings,indent=2)+'\n')
    return evidence

def make_stimuli(out,batches):
    rng=random.Random(0x20261020)
    cpu=CPU(); rows=[]; expected=[]; inflight=deque()
    counts=Counter(); ops=Counter(); masks=Counter()
    reference_rf=[0]*32; reference_pc=0
    seed=[0,0x80000000,0xffffffff,0,33,0x7fffffff]+[rng.getrandbits(32) for _ in range(26)]

    def emit(rst=0,valid=0,word=0x13,stalls=0,dbg=None):
        nonlocal reference_rf,reference_pc
        row=[rst,valid,word,stalls,len(rows)%32 if dbg is None else dbg]+seed
        before_remaining=cpu.remaining
        obs=cpu.step(row)
        rows.append(row); expected.append(obs); masks[stalls]+=1
        counts['cycles']+=1
        if rst:
            counts['resets']+=1; counts['discarded_by_reset']+=len(inflight)
            inflight.clear(); reference_rf=[0]+seed[1:]; reference_pc=0
        else:
            accepted,retired,ri,rpc,rv,rd,pc,debug,occ=obs
            counts['full_pipeline_cycles']+=int(occ==31)
            counts['wb_backpressure_cycles']+=int(bool(occ&16 and stalls&16))
            counts['multicycle_hold_cycles']+=int(before_remaining>0 and bool(stalls&4))
            if retired:
                assert inflight and inflight.popleft()==ri, ('order',len(rows))
                erd,ev=effect(reference_rf,reference_pc,ri)
                assert (rd,rv,rpc)==(erd,ev,reference_pc), ('ISA',len(rows))
                reference_rf,reference_pc=apply(reference_rf,reference_pc,erd,ev)
                counts['retired']+=1; ops[decode(ri)[0]]+=1
            if accepted:
                inflight.append(word); counts['accepted']+=1
            elif valid and decode(word) is None:
                counts['invalid_words_rejected']+=1
        assert cpu.rf==reference_rf and cpu.pc==reference_pc
        return obs[0]

    def program(words,policy='random'):
        pos=0; local=0
        while pos<len(words) or any(x is not None for x in cpu.slots):
            if local>30000: raise RuntimeError('test program did not drain')
            if policy=='blocked':
                stalls=16 if local<65 else 0
            elif policy=='random':
                stalls=sum((rng.random()<.23)<<i for i in range(5))
                if local%211<27: stalls|=16
            else: stalls=0
            valid=pos<len(words) and (policy!='random' or rng.random()>.08)
            accepted=emit(valid=int(valid),word=words[pos] if pos<len(words) else 0x13,stalls=stalls)
            if accepted: pos+=1
            local+=1
        for r in range(32): emit(dbg=r)

    emit(rst=1)
    # Explicit youngest-writer forwarding under prolonged WB backpressure.
    program([encode('addi',1,0,imm=7),encode('addi',1,0,imm=9),
             encode('add',2,1,0),encode('addi',0,0,imm=7),encode('add',3,0,2)],'blocked')
    directed=[]
    for op in OPS:
        for a,b in [(1,2),(2,3),(5,4),(0,0)]:
            directed += [encode(op,6,a,b,imm=-1 if op in I else 0x81234000),
                         encode('add',7,6,6)]
    program(directed)
    # Every unsupported opcode, reserved R funct7, and malformed shift is rejected.
    for opc in range(128):
        w=(0x12345600|opc)&MASK
        if decode(w) is None: emit(valid=1,word=w)
    for w in [0xffffffff,0,encode('slli')|(1<<25),encode('srli')|(1<<25),0xfe000033]:
        emit(valid=1,word=w)
    # Reset with occupied stages discards all pending instructions and suppresses retirement.
    for j in range(12): emit(valid=1,word=encode('addi',1,1,imm=1),stalls=16)
    emit(rst=1,valid=1,stalls=31)
    for batch in range(batches):
        seed=[rng.getrandbits(32) for _ in range(32)]
        seed[1:6]=[0x80000000,0xffffffff,0,33,0x7fffffff]
        emit(rst=1)
        words=[]
        for j in range(64):
            op=rng.choice(OPS)
            words.append(encode(op,rng.randrange(32),rng.randrange(12),rng.randrange(12),rng.getrandbits(32)))
        program(words)
    # PC wraparound is proved arithmetically by BitVec; these simulations start pc=0.
    assert not inflight
    assert counts['accepted']==counts['retired']+counts['discarded_by_reset']
    assert set(ops)==set(OPS), set(OPS)-set(ops)
    assert set(masks)==set(range(32))
    assert all(counts[k]>0 for k in ['full_pipeline_cycles','wb_backpressure_cycles','multicycle_hold_cycles'])
    (out/'stimulus.txt').write_text(''.join(' '.join(map(str,r))+'\n' for r in rows))
    (out/'python.trace').write_text(''.join(' '.join(map(str,r))+'\n' for r in expected))
    return rows,expected,dict(counts=counts,retired_by_opcode=ops,stall_masks=masks,
                              seed='0x20261020',all_32_registers_observed_after_each_drain=True)

def read_trace(path):
    return [tuple(map(int,line.split())) for line in path.read_text().splitlines()]

def simulate(rtl,out,stimulus):
    out.mkdir(parents=True,exist_ok=True)
    run(['iverilog','-g2012','-s','tb','-o',out/'sim.vvp',rtl,ROOT/'rtl/tb.sv'],out/'compile.log')
    run(['vvp',out/'sim.vvp',f'+input={stimulus}',f'+output={out}/rtl.trace'],out/'simulate.log')
    return read_trace(out/'rtl.trace')

def mismatches(expected,actual):
    if len(actual)!=len(expected): raise RuntimeError(f'trace lengths {len(actual)} != {len(expected)}')
    return [j for j,(e,a) in enumerate(zip(expected,actual)) if e!=a]

def mutation_repairs(out,expected,stimulus):
    source=(ROOT/'rtl/cpu.sv').read_text()
    wb='''      if (n_wv && n_wi[11:7]!=0 && n_wi[11:7]==r1) a=n_wval;
      if (n_wv && n_wi[11:7]!=0 && n_wi[11:7]==r2) b=n_wval;
'''
    mem='''      if (n_mv && n_mi[11:7]!=0 && n_mi[11:7]==r1) a=n_mval;
      if (n_mv && n_mi[11:7]!=0 && n_mi[11:7]==r2) b=n_mval;
'''
    mutations={
      'missing_forwarding':(wb+mem,'      // BUG: bypass paths omitted\n'),
      'oldest_writer_wins':(wb+mem,mem+wb),
      'divide_zero_returns_zero':("if (b==0) alu=32'hffffffff;","if (b==0) alu=32'b0;"),
      'ignore_writeback_stall':('assign retire_valid=!rst && wv && !stall_writeback;',
                                'assign retire_valid=!rst && wv;'),
      'add_substitution':('ADD: alu=a+b;','ADD: alu=a-b;'),
      'logical_signed_shift':('SRA: alu=$signed(a)>>>b[4:0];','SRA: alu=a>>b[4:0];'),
    }
    evidence=[]
    for name,(old,new) in mutations.items():
        assert source.count(old)==1,(name,source.count(old))
        mutant=source.replace(old,new)
        task=out/name; task.mkdir()
        faulty=task/'faulty.sv'; faulty.write_text(mutant)
        actual=simulate(faulty,task/'faulty',stimulus)
        diff=mismatches(expected,actual)
        if not diff: raise RuntimeError(f'undetected mutant {name}')
        first=diff[0]
        failure=dict(cycle=first,expected=expected[first],actual=actual[first],
                     stimulus=str(stimulus.relative_to(ROOT)),replay_prefix_rows=first+1,
                     columns=['accepted','retired','instruction','retire_pc','value','rd','pc','debug','occupancy'])
        (task/'counterexample.json').write_text(json.dumps(failure,indent=2)+'\n')
        # This demo uses an explicit local repair rule, not an independent or blind LLM repair.
        assert mutant.count(new)==1
        corrected=mutant.replace(new,old)
        assert corrected==source
        repaired=task/'repaired.sv'; repaired.write_text(corrected)
        (task/'correction.patch').write_text(''.join(difflib.unified_diff(
            mutant.splitlines(True),corrected.splitlines(True),fromfile='faulty.sv',tofile='repaired.sv')))
        repaired_trace=simulate(repaired,task/'repaired',stimulus)
        assert not mismatches(expected,repaired_trace),name
        evidence.append(dict(name=name,first_failing_cycle=first,
                             faulty_status='counterexample_in_simulation',
                             repaired_status='all_vectors_pass',
                             repaired_sha256=hashlib.sha256(corrected.encode()).hexdigest(),
                             repair_kind='scripted_local_rule'))
    return evidence

def main():
    ap=argparse.ArgumentParser()
    ap.add_argument('--batches',type=int,default=24)
    ap.add_argument('--skip-pdr',action='store_true')
    ap.add_argument('--pdr-seconds',type=int,default=60)
    ap.add_argument('--synthesis-seconds',type=int,default=300)
    args=ap.parse_args()
    if args.batches<1: ap.error('--batches must be positive')
    stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
    out=ROOT/'evidence'/stamp; out.mkdir(parents=True)
    result=dict(status='running',evidence=str(out.relative_to(ROOT)))
    (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
    try:
        print('Checking Lean certificates...',flush=True)
        result['lean']=proof(out)
        print('Generating deterministic stall/dependency tests...',flush=True)
        rows,expected,coverage=make_stimuli(out,args.batches)
        result['simulation']=coverage
        print(f'Comparing RTL, Lean and Python over {len(rows)} edges...',flush=True)
        actual=simulate(ROOT/'rtl/cpu.sv',out/'baseline',out/'stimulus.txt')
        diffs=mismatches(expected,actual)
        if diffs:
            j=diffs[0]
            raise RuntimeError(f'RTL mismatch at {j}: expected {expected[j]}, got {actual[j]}')
        result['lean_trace_seconds']=run(['lean','--run',ROOT/'lean/Trace.lean',out/'stimulus.txt',out/'lean.trace'],
                                         out/'lean-trace.log',180,ENV)
        actual=read_trace(out/'lean.trace')
        diffs=mismatches(expected,actual)
        if diffs:
            j=diffs[0]
            raise RuntimeError(f'Lean mismatch at {j}: expected {expected[j]}, got {actual[j]}')
        print('Injecting and correcting six RTL faults...',flush=True)
        result['mutations']=mutation_repairs(out,expected,out/'stimulus.txt')
        if not args.skip_pdr:
            result['pdr']={}
            for task in ['sanity','order','full']:
                print(f'Running Yosys/ABC PDR: {task}...',flush=True)
                target=out/('pdr-'+task)
                run([sys.executable,ROOT/'scripts/pdr.py','--task',task,'--seconds',args.pdr_seconds,
                     '--synthesis-seconds',args.synthesis_seconds,'--out',target],out/f'pdr-{task}.log',
                     args.synthesis_seconds+args.pdr_seconds+30)
                result['pdr'][task]=json.loads((target/'result.json').read_text())
        result['status']='passed'
    except Exception as exc:
        result['status']='failed'; result['error']=str(exc)
        raise
    finally:
        source_paths=sorted(p for folder in ['lean','rtl','scripts','spec'] for p in (ROOT/folder).rglob('*')
                            if p.is_file() and p.suffix in ['.lean','.sv','.svh','.py','.txt','.json'])
        result['sources']={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest() for p in source_paths}
        (out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
        (ROOT/'evidence/latest.json').write_text(json.dumps(result,indent=2)+'\n')
        print(json.dumps({k:result[k] for k in ['status','evidence','error'] if k in result},indent=2),flush=True)
    return 0

if __name__=='__main__': raise SystemExit(main())
