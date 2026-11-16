#!/usr/bin/env python3
"""Exercise the new native-RAM acceptance boundary on the actual CPU RTLIL."""
from copy import deepcopy
from pathlib import Path
import json,sys
ROOT=Path(__file__).resolve().parents[1];sys.path.insert(0,str(ROOT.parents[1]/'method/stage2'))
from v2lean.native_memory import NativeMemoryImporter
from v2lean.importer import Unsupported
source=json.loads((ROOT/'evidence/native.rtlil.json').read_text())
module=source['modules']['case_cpu_memory']
ram_name=next(n for n,c in module['cells'].items() if c['type']=='$mem_v2')
checked=[]
def reject(name,edit,message):
 d=deepcopy(source);c=d['modules']['case_cpu_memory']['cells'][ram_name];edit(d,c)
 try:NativeMemoryImporter(d,'case_cpu_memory').build()
 except Unsupported as e:
  assert message in str(e),(name,str(e));checked.append(dict(name=name,status='rejected',reason=str(e)))
 else:raise AssertionError(f'unsupported shape accepted: {name}')
def param(c,name,value):c['parameters'][name]=f'{value:032b}'
positive=NativeMemoryImporter(source,'case_cpu_memory');text=positive.build()
assert text==(ROOT/'lean/NativeImported.lean').read_text(),'imported AST is stale'
assert positive.metadata==[dict(name='ram',addr_width=8,data_width=32,size=256,read_ports=3,write_ports=1,initial_contents='arbitrary')]
checked.append(dict(name='native CPU RAM preserved',status='accepted',word_nodes=len(positive.pure.wires),state_groups=len(positive.pure.states)))
reject('clocked read',lambda d,c:param(c,'RD_CLK_ENABLE',1),'asynchronous reads')
reject('two writes',lambda d,c:param(c,'WR_PORTS',2),'at most one write')
reject('initialized image',lambda d,c:c['parameters'].__setitem__('INIT','0'+c['parameters']['INIT'][1:]),'initialization proof')
reject('partial depth',lambda d,c:param(c,'SIZE',255),'partial-depth')
reject('negative edge write',lambda d,c:param(c,'WR_CLK_POLARITY',0),'positive edge')
reject('read-enable gating',lambda d,c:c['connections']['RD_EN'].__setitem__(0,'0'),'read-enable')
reject('read reset',lambda d,c:c['connections']['RD_SRST'].__setitem__(0,'1'),'read-reset')
reject('read through RAM data',lambda d,c:c['connections']['RD_ADDR'].__setitem__(slice(0,8),c['connections']['RD_DATA'][:8]),'old registers/inputs')
record=dict(status='passed',checks=checked)
(ROOT/'evidence/import-check.json').write_text(json.dumps(record,indent=2)+'\n');print(json.dumps(record,indent=2))
