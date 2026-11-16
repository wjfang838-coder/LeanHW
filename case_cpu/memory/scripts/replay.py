#!/usr/bin/env python3
"""Reimport actual native-RAM RTL and replay the complete two-level ISA proof."""
import argparse,hashlib,json,os,re,shutil,subprocess,sys,time
from datetime import datetime,timezone
from pathlib import Path
ROOT=Path(__file__).resolve().parents[1];REPO=ROOT.parents[1]
sys.path.insert(0,str(REPO/'method/stage2'))
from v2lean.native_memory import NativeMemoryImporter
MODULES=['MemISA','MemPipeline','MemRefinement','MemEvents','MemRaw','MemRawProof',
 'MemRawBridge','MemWordRefinement','MemMetadata','NativeImported','NativeCertificate','MemoryCircuit',
 'MemoryShallow','MemNativeMemory','MemNativeStore','MemNativeLanes','MemDecode',
 'MemDecoderCircuit','MemPhysical','MemNetlistStep','MemALUCircuit','MemStorageCircuit',
 'MemControlCircuit','MemMemoryCircuit','MemExecuteCircuit','MemRelation','MemMemoryCommit',
 'MemStageRefinement','MemDecodeFields','MemIssueCircuit','MemFrontCircuit','MemDispatchRelation',
 'MemCircuitRefinement','MemPortRefinement','MemAcceptRefinement','MemTraceRefinement','MemOutputRefinement',
 'MemoryDiagnosis','MemAudit']
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 ap.add_argument('--module-seconds',type=int,default=1800)
 ap.add_argument('--reuse-shallow',action='store_true',help='reuse the previously checked expensive shallow object only after verifying its source/AST/dependency hashes against evidence/latest.json')
 args=ap.parse_args()
 stamp=datetime.now(timezone.utc).strftime('%Y%m%dT%H%M%S%fZ')
 out=ROOT/'evidence/replay'/stamp;out.mkdir(parents=True)
 objects=out/'olean';objects.mkdir()
 env=dict(os.environ,LEAN_PATH=':'.join(map(str,[objects,ROOT/'lean',ROOT.parent/'lean',ROOT.parent/'bridge',REPO/'.lake/build/lib/lean'])))
 result=dict(status='running',closed_rtl_to_isa=False,scope='actual imported RTL/native RAM -> register-shaped pipeline -> cycle LeanSpec -> transaction ISA, including physical acceptance/retirement',modules={})
 def save():(out/'result.json').write_text(json.dumps(result,indent=2)+'\n')
 def run(cmd,name,limit=300):
  print(name,flush=True);start=time.monotonic();log=out/(name+'.log')
  with log.open('w') as f:p=subprocess.run(list(map(str,cmd)),cwd=REPO,env=env,stdout=f,stderr=subprocess.STDOUT,timeout=limit)
  content=log.read_text()
  if p.returncode or re.search(r'\berror:|\bsorryAx\b|declaration uses .sorry.',content):raise RuntimeError(f'failed {name}: {log}')
  return dict(seconds=round(time.monotonic()-start,3),log=str(log.relative_to(ROOT)))
 save()
 try:
  original=(ROOT/'rtl/cpu.sv').read_bytes()
  run([sys.executable,ROOT/'scripts/build_rtl.py'],'render')
  if original!=(ROOT/'rtl/cpu.sv').read_bytes():raise RuntimeError('RTL generator differs from frozen CPU')
  run(['yosys','-Q','-T','-s',ROOT/'evidence/native.ys'],'yosys')
  importer=NativeMemoryImporter(json.loads((ROOT/'evidence/native.rtlil.json').read_text()),'case_cpu_memory')
  if importer.build()!=(ROOT/'lean/NativeImported.lean').read_text():raise RuntimeError('fresh native import differs from frozen AST')
  result['source_binding']=dict(status='exact_text_match',rtl_sha256=sha(ROOT/'rtl/cpu.sv'),ast_sha256=sha(ROOT/'lean/NativeImported.lean'),memories=importer.metadata)
  run([sys.executable,ROOT/'scripts/check_import.py'],'import-boundary')
  frozen={n:(ROOT/f'lean/{n}.lean').read_bytes() for n in ['MemoryCircuit','MemoryShallow']}
  frozen_times={n:(ROOT/f'lean/{n}.lean').stat() for n in frozen}
  run([sys.executable,ROOT/'scripts/gen_shallow.py'],'shallow-generator')
  if any((ROOT/f'lean/{n}.lean').read_bytes()!=b for n,b in frozen.items()):raise RuntimeError('shallow generator differs from frozen certificates')
  for n,st in frozen_times.items():os.utime(ROOT/f'lean/{n}.lean',ns=(st.st_atime_ns,st.st_mtime_ns))
  sources=list((ROOT/'lean').glob('*.lean'))+list((ROOT/'rtl').glob('*'))+list((ROOT/'spec').glob('*'))+list((ROOT/'scripts').glob('*.py'))
  sources += list((REPO/'method/stage2/framework').rglob('*.lean'))+list((REPO/'method/stage2/assets/lib').rglob('*.lean'))+list((REPO/'method/stage2/v2lean').glob('*.py'))
  sources += list((ROOT.parent/'lean').glob('*.lean'))+list((ROOT.parent/'bridge').glob('*.lean'))
  result['sources']={str(p.relative_to(REPO)):sha(p) for p in sorted(set(sources)) if p.is_file()};save()
  core=REPO/'.lake/build/lib/lean/LeanRTL/Core/NativeMemory.olean';core.parent.mkdir(parents=True,exist_ok=True)
  run(['lean','-j2','-s65536','-o',core,REPO/'method/stage2/framework/LeanRTL/Core/NativeMemory.lean'],'NativeMemory',args.module_seconds)
  for name,src in [('ISA',ROOT.parent/'lean/ISA.lean'),('WordMath',ROOT.parent/'bridge/WordMath.lean'),('NetFacts',ROOT.parent/'bridge/NetFacts.lean')]:
   run(['lean','-j2','-s65536','-o',objects/(name+'.olean'),src],name,args.module_seconds)
  for name in MODULES:
   if name=='MemoryShallow' and args.reuse_shallow:
    cert=ROOT/'evidence/shallow-latest.json'
    manifest=json.loads((cert if cert.exists() else ROOT/'evidence/latest.json').read_text())
    if cert.exists():
     if manifest['status']!='checked':raise RuntimeError('shallow certificate not checked')
     if manifest['object_sha256']!=sha(ROOT/'lean/MemoryShallow.olean'):raise RuntimeError('shallow object hash differs from certificate')
    for dep in [ROOT/'lean/MemoryShallow.lean',ROOT/'lean/MemoryCircuit.lean',ROOT/'lean/NativeImported.lean',ROOT.parent/'bridge/NetFacts.lean',REPO/'method/stage2/framework/LeanRTL/Core/NativeMemory.lean']:
     if manifest['sources'][str(dep.relative_to(REPO))]!=sha(dep):raise RuntimeError(f'shallow cache source mismatch: {dep}')
    cached=ROOT/'lean/MemoryShallow.olean'
    if cached.stat().st_mtime_ns<(ROOT/'lean/MemoryShallow.lean').stat().st_mtime_ns:raise RuntimeError('shallow cache predates source')
    shutil.copyfile(cached,objects/'MemoryShallow.olean')
    result['modules'][name]=dict(mode='previously_checked_object_reused',certificate='evidence/shallow-latest.json' if cert.exists() else 'evidence/latest.json',source_sha256=sha(ROOT/'lean/MemoryShallow.lean'),object_sha256=sha(cached));save();continue
   src=ROOT/f'lean/{name}.lean';rec=run(['lean','-j2','-s65536','-o',objects/(name+'.olean'),src],name,args.module_seconds)
   result['modules'][name]=dict(rec,source_sha256=sha(src));save()
  result.update(status='full_refinement_proved',closed_rtl_to_isa=True,shallow_cache_reused=args.reuse_shallow,
    lean_version=subprocess.check_output(['lean','--version'],text=True).strip())
  save();(ROOT/'evidence/replay-latest.json').write_text(json.dumps(result,indent=2)+'\n')
  shutil.copyfile(out/'MemAudit.log',ROOT/'evidence/Audit.log')
  for name in MODULES:shutil.copyfile(objects/(name+'.olean'),ROOT/'lean'/(name+'.olean'))
  print('Complete actual RTL -> cycle -> transaction ISA proof replayed.',flush=True)
 except BaseException as e:
  result.update(status='failed',error=str(e));save();raise
if __name__=='__main__':main()
