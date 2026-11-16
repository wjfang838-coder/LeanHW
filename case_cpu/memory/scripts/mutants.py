#!/usr/bin/env python3
"""Inject concrete RTL defects; compare against the same frozen reference vectors.
Detection is differential simulation, not a substitute for refinement proof.
"""
from pathlib import Path
import hashlib,json,subprocess
ROOT=Path(__file__).resolve().parents[1]
OUT=ROOT/'evidence/mutations';OUT.mkdir(parents=True,exist_ok=True)
source=(ROOT/'rtl/cpu.sv').read_text()
mutations={
 'trap_rd_leak':("assign retire_rd = (writeback_fire && writeback_packet.fault == 0) ? writeback_packet.destination : 5'b0;", "assign retire_rd = writeback_fire ? writeback_packet.destination : 5'b0;"),
 'lb_zero_ext':("load_result = {{24{selected[7]}}, selected[7:0]};","load_result = {24'b0, selected[7:0]};"),
 'sb_clobbers_word':("store_mask = 32'h000000ff << {address[1:0], 3'b0};","store_mask = 32'hffffffff;"),
 'store_during_wb_stall':('wire store_commit = writeback_fire &&','wire store_commit = !rst && fault == FAULT_NONE && writeback_valid &&'),
 'delay_not_sampled':("next_memory_remaining = memory_remaining - 4'd1;","next_memory_remaining = memory_delay;")}
sim=ROOT/'evidence/simulation'
expected=[tuple(map(int,r.split())) for r in (sim/'expected.trace').read_text().splitlines()]
result=[]
for name,(old,new) in mutations.items():
 assert source.count(old)==1,(name,source.count(old))
 text=source.replace(old,new)
 d=OUT/name;d.mkdir(exist_ok=True);rtl=d/'cpu.sv';rtl.write_text(text)
 subprocess.run(['iverilog','-g2012','-s','tb','-o',str(d/'sim.vvp'),str(rtl),str(ROOT/'rtl/tb.sv')],check=True)
 p=subprocess.run(['vvp',str(d/'sim.vvp'),f'+VECTORS={sim}/vectors.txt',f'+MEM={sim}/ram.hex',f'+TRACE={d}/rtl.trace'],capture_output=True,text=True,timeout=90)
 (d/'sim.log').write_text(p.stdout+p.stderr)
 assert p.returncode==0,(name,p.returncode)
 actual=[tuple(map(int,r.split())) for r in (d/'rtl.trace').read_text().splitlines()]
 assert len(actual)==len(expected)
 first=next((i for i,(a,b) in enumerate(zip(actual,expected)) if a!=b),None)
 assert first is not None,f'mutant survived: {name}'
 witness=dict(cycle=first,actual=actual[first],expected=expected[first],vector=(sim/'vectors.txt').read_text().splitlines()[first])
 (d/'witness.json').write_text(json.dumps(witness,indent=2)+'\n')
 result.append(dict(name=name,status='detected',cycle=first,mutant_sha256=hashlib.sha256(text.encode()).hexdigest(),witness=str((d/'witness.json').relative_to(ROOT))))
record=dict(method='frozen-vector differential RTL simulation',mutations=result,correction='revert each single mutation to frozen rtl/cpu.sv; replay via simulate.py',corrected_rtl_sha256=hashlib.sha256(source.encode()).hexdigest())
(OUT/'result.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
