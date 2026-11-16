#!/usr/bin/env python3
"""Read-only source-package integrity, roster and Lean dependency checks."""
from pathlib import Path
import ast, hashlib, json, sys
ROOT=Path(__file__).resolve().parents[1]
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 manifest=json.loads((ROOT/'method/MIGRATION.json').read_text())
 errors=[]
 stage_dirs={p.name for p in (ROOT/'method').iterdir() if p.is_dir() and not p.name.startswith('.') and p.name!='__pycache__'}
 if stage_dirs!={'stage1','stage2'}:errors.append('method must contain exactly stage1 and stage2')
 for retired in ('specir','v2lean','scripts','docs'):
  if (ROOT/retired).exists():errors.append('obsolete top-level method directory: '+retired)
 for rel,record in manifest['source_files'].items():
  p=ROOT/rel
  if not p.is_file():errors.append('missing: '+rel);continue
  if digest(p)!=record.get('package_sha256',record['sha256']):errors.append('hash mismatch: '+rel)
 for rel,expected in manifest.get('added_files',{}).items():
  p=ROOT/rel
  if not p.is_file() or digest(p)!=expected:errors.append('missing/changed added file: '+rel)
 for bench,count in manifest['benchmark_counts'].items():
  cases=list((ROOT/'benchmarks'/bench/'clarified').glob('*/spec.clarified.txt'))
  if len(cases)!=count:errors.append(f'roster {bench}: {len(cases)} != {count}')
  for p in cases:
   if not p.with_name('interface.json').is_file():errors.append('missing interface: '+str(p))
 for p in ROOT.rglob('*'):
  if any(x in {'.lake','__pycache__','.pytest_cache','data'} for x in p.relative_to(ROOT).parts):continue
  if p.is_symlink():errors.append('symbolic link: '+str(p))
  if p.suffix=='.py':
   try:ast.parse(p.read_text(),filename=str(p))
   except SyntaxError as e:errors.append(str(e))
 # Both CPU variants use flat local module names alongside shared namespaces.
 roots=[ROOT/'case_cpu/lean',ROOT/'case_cpu/bridge',ROOT/'case_cpu/memory/lean',
        ROOT/'method/stage2/framework',ROOT/'method/stage2/assets/lib',ROOT/'method/stage1/leanspec/lean',
        ROOT/'method/stage1/leanspec/lean',ROOT/'method/stage2/refinement/lean']
 for folder in roots[:3]:
  for p in folder.glob('*.lean'):
   for line in p.read_text().splitlines():
    if not line.startswith('import '):continue
    for module in line[7:].split():
     if module.split('.')[0] in {'Lean','Std','Init'}:continue
     rel=Path(*module.split('.')).with_suffix('.lean')
     if not any((base/rel).is_file() for base in roots):errors.append(f'{p.name}: unresolved import {module}')
 if errors:
  print('\n'.join(errors));return 1
 print(json.dumps({'status':'passed','benchmark_cases':sum(manifest['benchmark_counts'].values()),
  'source_files':len(manifest['source_files']),'added_files':len(manifest.get('added_files',{})),
  'cpu_lean_modules':sum(len(list(p.glob('*.lean'))) for p in roots[:3])},indent=2))
 return 0
if __name__=='__main__':sys.exit(main())
