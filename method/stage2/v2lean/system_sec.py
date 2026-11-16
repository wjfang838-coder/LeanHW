"""Prepare ordinary Jasper SEC for an actual resolved-system HDL roundtrip.

Yosys is used only to identify physical register bits for initial correspondence.
It does not replace either HDL input or certify the four-state frontend.
"""
import argparse
import json
from pathlib import Path
import shutil

from .pipeline import ROOT,digest,run,save_json
from .importer import require
from .jasper import run_sec


def prepare(case,out):
    case=Path(case).resolve();out=Path(out).resolve()
    result=json.loads((case/'result.json').read_text())
    require(result['status']=='clocked_trace_diagnostic_pass' and result['frontend']=='system',
            'requires a completed system roundtrip diagnostic')
    require(all(digest(case/n)==h for n,h in result['artifact_hashes'].items()),'system artifact changed')
    require(all(digest(ROOT/n)==h for n,h in result['source_hashes'].items()),'implementation changed since system diagnostic')
    metadata=json.loads((case/'source.json').read_text())
    top=next(iter(metadata['modules']))
    require(not out.exists(),'preserve previous system SEC evidence')
    out.mkdir(parents=True)
    for src,dst in [('original.v','original.v'),('emitted.v','roundtrip.v'),('Imported.lean','Imported.lean')]:
        shutil.copyfile(case/src,out/dst)
    script=f'''read_verilog -sv original.v
hierarchy -check -top {top}
flatten
# Only a physical-name/bit index is needed here. Discard processes from this
# temporary in-memory design; the original HDL sent to Jasper is unchanged.
delete p:*
write_json import.rtlil.json
design -reset
read_verilog -sv roundtrip.v
hierarchy -check -top {top}
flatten
delete p:*
write_json state_gate.json
'''
    (out/'mapping.ys').write_text(script)
    run(['yosys','-Q','-T','-s','mapping.ys'],out,out/'mapping.log',timeout=300)
    gold=json.loads((out/'import.rtlil.json').read_text())['modules'][top]
    gate=json.loads((out/'state_gate.json').read_text())['modules'][top]
    states=[];source_seen=set();gate_seen=set()
    for state in metadata['states']:
        name,width=state['name'],state['width'];origin=metadata['state_origins'][name]
        require(origin in gold['netnames'] and name in gate['netnames'],'missing physical state origin')
        a,b=gold['netnames'][origin]['bits'],gate['netnames'][name]['bits']
        require(len(a)==len(b)==width and all(type(x) is int for x in a+b),'state bits changed or constant-folded')
        require(len(set(a))==len(set(b))==width and not source_seen.intersection(a) and not gate_seen.intersection(b),
                'ambiguous or overlapping state correspondence')
        source_seen.update(a);gate_seen.update(b)
        states.append({'register':name,'gate_register':name,'width':width,'bits':a,'source_origin':origin})
    interface=[]
    for name,port in metadata['modules'][top]['ports'].items():
        interface.append([name,port['direction'],len(port['bits']),name in metadata['signed_ports'],0,False])
    save_json(out/'report.json',{'status':'prepared_system_sec','input':{'top':top},'import':{'states':states},
        'interface':{'ports':interface,'scalar_ports':metadata['scalar_ports']},
        'semantics':{'profile':'native resolved hierarchy; ordinary free-clock SEC; no reset assumptions',
                     'mapping_scope':'Yosys identifies exact physical register nets only; both actual HDL files are unchanged'},
        'source_diagnostic':{'path':str(case),'result_sha256':digest(case/'result.json')},
        'artifact_hashes':{n:digest(out/n) for n in ['original.v','roundtrip.v','Imported.lean','import.rtlil.json','state_gate.json']}})
    return out


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('case',type=Path);p.add_argument('out',type=Path)
    p.add_argument('--prepare-only',action='store_true');p.add_argument('--timeout',type=int,default=180)
    a=p.parse_args();out=prepare(a.case,a.out)
    if a.prepare_only:print(out)
    else:
        result=run_sec(out,timeout=a.timeout,trace=True)
        print(json.dumps(result,indent=2))
