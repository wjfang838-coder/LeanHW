#!/usr/bin/env python3
"""Publish source-bound evidence only after all circuit/ISA proof modules replay."""
from datetime import datetime,timezone
from pathlib import Path
import hashlib,json,re,subprocess,sys
ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parents[1]
sys.path.insert(0,str(REPO/'method/stage2'))
from v2lean.native_memory import NativeMemoryImporter

def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def read(p):return json.loads(p.read_text())
def main():
 audit=ROOT/'evidence/Audit.log';text=audit.read_text()
 assert not re.search(r'\berror:|sorryAx|Unknown constant',text),'Audit failed'
 assert all(n in text for n in ['CaseCPUMem.NativeRAM.actual_sb','CaseCPUMem.Source.rtl_to_transaction_isa','CaseCPUMem.Source.rtl_accepted_program_refinement','CaseCPUMem.Source.reachable_retirement_payload'])
 sources=sorted((ROOT/'lean').glob('*.lean'))
 for p in sources:
  obj=p.with_suffix('.olean')
  assert obj.exists() and obj.stat().st_mtime_ns>=p.stat().st_mtime_ns,f'outdated proof object: {p}'
  assert not re.search(r'^\s*(?:axiom\s|sorry\b|admit\b)',p.read_text(),re.M),p
 design=read(ROOT/'evidence/native.rtlil.json');imp=NativeMemoryImporter(design,'case_cpu_memory')
 assert imp.build()==(ROOT/'lean/NativeImported.lean').read_text(),'import is stale'
 rtl=ROOT/'rtl/cpu.sv';rtl_hash=sha(rtl)
 sim=read(ROOT/'evidence/simulation/result.json')
 assert sim['status']=='passed' and sim['source_sha256']['case_cpu/memory/rtl/cpu.sv']==rtl_hash
 mutants=read(ROOT/'evidence/mutations/result.json')
 assert mutants['corrected_rtl_sha256']==rtl_hash and all(x['status']=='detected' for x in mutants['mutations'])
 boundary=read(ROOT/'evidence/import-check.json');assert boundary['status']=='passed'
 pdr={}
 for task in ['sanity','full']:
  f=ROOT/f'evidence/pdr-{task}/result.json';r=read(f)
  assert r['rtl_sha256']==rtl_hash
  assert r['miter_sha256']==sha(ROOT/'rtl/memory_reference.svh') and r['reference_sha256']==sha(ROOT/'rtl/isa_reference.svh')
  assert r['aiger']['outputs']==0 and r['aiger']['constraints']==1 and r['aiger']['bad']>0
  pdr[task]=dict(status=r['status'],seconds=r['pdr_seconds'],aiger=r['aiger'],result=str(f.relative_to(ROOT)))
 all_sources=sources+sorted((ROOT/'rtl').glob('*'))+sorted((ROOT/'spec').glob('*'))+sorted((ROOT/'scripts').glob('*.py'))
 all_sources += [REPO/'method/stage2/framework/LeanRTL/Core/NativeMemory.lean',REPO/'method/stage2/v2lean/native_memory.py']+list((ROOT.parent/'lean').glob('*.lean'))+list((ROOT.parent/'bridge').glob('*.lean'))
 replay=read(ROOT/'evidence/replay-latest.json')
 assert replay['status']=='full_refinement_proved' and replay['closed_rtl_to_isa']
 assert all(name in replay['modules'] for name in ['MemCircuitRefinement','MemPortRefinement','MemAcceptRefinement','MemTraceRefinement','MemMetadata','MemOutputRefinement','MemAudit'])
 for name,rec in replay['modules'].items():
  assert rec['source_sha256']==sha(ROOT/f'lean/{name}.lean'),f'proof replay source mismatch: {name}'
 result=dict(proof_replay=dict(status=replay['status'],shallow_cache_reused=replay['shallow_cache_reused'],record='evidence/replay-latest.json'),status='full_refinement_proved',generated_utc=datetime.now(timezone.utc).isoformat(),closed_rtl_to_isa=True,
  rtl=dict(path='rtl/cpu.sv',sha256=rtl_hash,lines=len(rtl.read_text().splitlines()),instructions=38,pipeline_stages=5),
  native_import=dict(word_nodes=len(imp.pure.wires),register_groups=len(imp.pure.states),scalar_state_bits=sum(s['width'] for s in imp.pure.states),ram_bits=8192,memories=imp.metadata,flattened_ram=False),
  proved=['actual imported RTL/native RAM -> register-shaped pipeline -> cycle LeanSpec -> transaction ISA',
   'whole-cycle refinement and reachable relation for arbitrary stalls, delay, undefined choices and repeated resets',
   'architectural register file, PC, all RAM words and precise fault state',
   'physical input acceptance and retirement ports -> abstract event stream',
   'physical drain -> ISA execution of the actual accepted instruction program',
   'retirement PC, destination/result and store byte-lane observations',
   'all actual imported AST node equations and native RAM read/write/frame/reset semantics',
   'cycle FIFO conservation with explicit reset/trap abort accounting'],
  open=[],
  scope=dict(reset='one initial reset; arbitrary later resets in the trace theorem',
    memory='arbitrary initial 256x32 native RAM, retained on reset',
    instructions=38,control='stream input, in-order backend; no branch/jump/CSR/cache/instruction RAM',
    progress='safety for arbitrary stalls; accepted-program theorem conditional on physical drain',
    projected_out='12 diagnostic performance counters and their read mux; not architectural ISA state'),
  theorems=['CaseCPUMem.Source.circuit_cycle_refinement','CaseCPUMem.Source.rtl_to_transaction_isa',
    'CaseCPUMem.Source.rtl_accepted_program_refinement','CaseCPUMem.Source.reachable_retirement_payload'],
  simulation=sim,mutations=mutants,pdr=pdr,
  trust=['SystemVerilog/Yosys lowering and importer','Lean kernel and standard propext/Classical.choice/Quot.sound',
   'native LRAT checking for bv_decide and native evaluation for checker/topology'],
  audit=dict(path='evidence/Audit.log',sha256=sha(audit),sorryAx=False),
  sources={str(p.relative_to(REPO)):sha(p) for p in all_sources if p.is_file()})
 path=ROOT/'evidence/latest.json';path.write_text(json.dumps(result,indent=2)+'\n')
 print(json.dumps({k:result[k] for k in ['status','closed_rtl_to_isa','rtl','native_import','proved','open','pdr']},indent=2))
if __name__=='__main__':main()
