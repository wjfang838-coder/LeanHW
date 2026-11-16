#!/usr/bin/env python3
"""Compare every RTL edge against an independent byte-addressed ISA pipeline."""
from pathlib import Path
from collections import Counter,deque
import hashlib,json,random,subprocess
from model import CPU,OPS,encode,decode,MASK
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'evidence/simulation';OUT.mkdir(parents=True,exist_ok=True)
rng=random.Random(20261021)
initial_mem=[rng.getrandbits(8) for _ in range(1024)]
cpu=CPU(mem=initial_mem.copy());rows=[];expected=[];coverage=Counter();masks=Counter();faults=Counter()
seed=[0,0x80000000,0xffffffff,0,33,0x7fffffff]+[rng.getrandbits(32) for _ in range(26)]
def emit(rst=0,valid=0,word=0x13,stalls=0,delay=0):
    row=[rst,valid,word,stalls,delay,len(rows)%32,len(rows)%256,len(rows)%16]+seed
    obs=cpu.step(row);rows.append(row);expected.append(obs);masks[stalls]+=1
    if obs[1]:coverage[decode(obs[2])[0]]+=1
    if obs[10]:faults[obs[11]]+=1
    return obs[0]
def send(word):
    while not emit(valid=1,word=word,stalls=rng.randrange(32),delay=rng.randrange(16)):
        if cpu.fault:raise RuntimeError('unexpected trap before instruction accepted')
def drain():
    for _ in range(1500):
        if not any(p is not None for p in cpu.slots):break
        emit(stalls=rng.randrange(32),delay=rng.randrange(16))
    else:raise RuntimeError('pipeline did not drain')
    for _ in range(256):emit()
emit(rst=1)
# Exercise every arithmetic instruction with dependency chains.
for op in OPS:
    if op in ['lb','lh','lw','lbu','lhu','sb','sh','sw','fence']:continue
    send(encode(op,rd=7,rs1=1,rs2=2,imm=0xfffff004 if op in ['lui','auipc'] else 3))
drain()
# Byte/halfword overlap, signed loads, x0 loads, full/partial store preservation.
for op,off in [('sw',0),('sb',1),('sh',2),('lb',1),('lbu',1),('lh',2),('lhu',2),('lw',0),('fence',0),('lw',0)]:
    send(encode(op,rd=9,rs1=0,rs2=2,imm=off))
drain()
for block in range(12):
    for _ in range(45):
        op=rng.choice(OPS)
        off=rng.randrange(1024)
        if op in ['lh','lhu','sh']:off&=~1
        if op in ['lw','sw']:off&=~3
        send(encode(op,rd=rng.randrange(32),rs1=0 if op in ['lb','lbu','lh','lhu','lw','sb','sh','sw'] else rng.randrange(32),rs2=rng.randrange(32),imm=off if op in ['lb','lbu','lh','lhu','lw','sb','sh','sw'] else rng.randrange(32)))
    drain()
# Four precise faults, younger accepted words aborted, then reset retaining RAM.
for op,off,cause in [('lw',1,1),('sw',2,2),('lb',1024,3),('sb',1024,4)]:
    send(encode(op,rd=8,rs1=0,rs2=2,imm=off))
    for _ in range(100):
        emit(valid=1,word=encode('addi',rd=12,imm=7),stalls=0,delay=3)
        if cpu.fault:break
    assert cpu.fault==cause
    for _ in range(20):emit(valid=1,word=encode('sw',rs2=2),stalls=rng.randrange(32),delay=15)
    before=cpu.mem.copy();emit(rst=1);assert cpu.mem==before
    drain()
# Reset with nonempty backend and stalled store; suppressed stores must not leak.
send(encode('sw',rs2=2,imm=64))
for _ in range(8):emit(stalls=16,delay=0)
emit(rst=1);drain()
assert set(coverage)==set(OPS),(set(OPS)-set(coverage))
assert len(masks)==32 and set(faults)=={1,2,3,4}
(OUT/'ram.hex').write_text(''.join(f'{int.from_bytes(initial_mem[4*i:4*i+4],"little"):08x}\n' for i in range(256)))
with (OUT/'vectors.txt').open('w') as f:
    for r in rows:
        rst,v,w,st,d,dr,dm,dc,*rf=r
        pack=sum(x<<(32*i) for i,x in enumerate(rf))
        f.write(f'{rst} {v} {w:08x} {st} {d} {dr} {dm} {dc} {pack:0256x}\n')
(OUT/'expected.trace').write_text(''.join(' '.join(map(str,x))+'\n' for x in expected))
subprocess.run(['iverilog','-g2012','-s','tb','-o',str(OUT/'sim.vvp'),str(ROOT/'rtl/cpu.sv'),str(ROOT/'rtl/tb.sv')],check=True)
p=subprocess.run(['vvp',str(OUT/'sim.vvp'),f'+VECTORS={OUT}/vectors.txt',f'+MEM={OUT}/ram.hex',f'+TRACE={OUT}/rtl.trace'],check=True,capture_output=True,text=True,timeout=90)
(OUT/'sim.log').write_text(p.stdout+p.stderr)
actual=[tuple(int(v) for v in line.split()) for line in (OUT/'rtl.trace').read_text().splitlines()]
assert len(actual)==len(expected),(len(actual),len(expected))
for n,(a,e) in enumerate(zip(actual,expected)):
    if a!=e:
        (OUT/'failure.json').write_text(json.dumps(dict(cycle=n,row=rows[n],actual=a,expected=e),indent=2)+'\n')
        raise RuntimeError(f'mismatch at cycle {n}: {a} != {e}')
sources=[ROOT/'rtl/cpu.sv',ROOT/'rtl/tb.sv',ROOT/'scripts/model.py',ROOT.parent/'scripts/model.py',Path(__file__).resolve()]
result=dict(status='passed',source_sha256={str(p.relative_to(ROOT.parent.parent)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sources},cycles=len(rows),retired=sum(coverage.values()),instructions=dict(coverage),stall_masks=len(masks),faults=dict(faults),ram_bytes=1024)
(OUT/'result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
