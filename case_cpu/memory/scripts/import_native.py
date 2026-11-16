#!/usr/bin/env python3
from pathlib import Path
import json
import sys
ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parents[1]
sys.path.insert(0,str(REPO/'method/stage2'))
from v2lean.native_memory import NativeMemoryImporter
source=ROOT/'evidence/native.rtlil.json'
imp=NativeMemoryImporter(json.loads(source.read_text()),'case_cpu_memory')
text=imp.build()
(ROOT/'lean/NativeImported.lean').write_text(text)
for name,obj in [('states',imp.pure.states),('mapping',imp.pure.mapping),('memories',imp.metadata),('choices',imp.pure.choices)]:
    (ROOT/f'evidence/{name}.json').write_text(json.dumps(obj,indent=2)+'\n')
print(len(imp.pure.wires),'word nodes;',len(imp.pure.states),'register groups;',imp.metadata)
