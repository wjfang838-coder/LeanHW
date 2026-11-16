"""Native inout round trips and explicit four-state resolution encoding checks."""
import argparse
import json
from pathlib import Path
import random
import re
import shutil

from .importer import require
from .pipeline import ROOT, digest, run, save_json
from .resolved import ResolvedImporter


def check_axioms(stdout, expected):
    records=re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]",stdout,re.S)
    free=re.findall(r"'([^']+)' does not depend on any axioms",stdout)
    require(len(records)+len(free)==len(expected) and {n for n,_ in records}|set(free)==set(expected), 'missing resolution proof audit')
    result={n:sorted({a.strip() for a in ax.split(',') if a.strip()}) for n,ax in records}
    result.update({n:[] for n in free})
    require(all(set(ax)<={'propext','Classical.choice','Quot.sound'} for ax in result.values()),'untrusted resolution proof axiom')
    return result


def encode(source,top,out):
    out.mkdir()
    shutil.copyfile(source,out/'input.v')
    importer=ResolvedImporter(out/'input.v',top)
    text=importer.build().replace('def main (args', '''theorem encoding_valid : Encoding.encodingValid impl.lower = true := by decide +kernel
theorem encoding_correct (env : LeanRTL.Env) :
  Encoding.decodeOutputPairs impl.lower.outputs
    ((Encoding.module impl.lower).outputs?eval (fun _ => 0) env) =
    some (impl.eval (Encoding.decodedEnv env)) :=
  Resolved.encoded_netlist_correct impl encoding_valid env
#print axioms encoding_correct
def main (args''')
    (out/'Imported.lean').write_text(text);save_json(out/'source.json',importer.metadata)
    proof=run(['lake','env','lean','-s','65536','--run',str(out/'Imported.lean'),'encode',str(out/'encoded.json')],ROOT,out/'encode.log',timeout=300)
    deps=check_axioms(proof.stdout,['resolution_correct','encoding_correct'])
    save_json(out/'certificate.json',{'status':'kernel_checked','theorems':deps,'proof_hash':digest(out/'Imported.lean'),
                                      'json_hash':digest(out/'encoded.json')})
    (out/'emit.ys').write_text('read_json encoded.json\ncheck -assert\nopt_clean\nwrite_verilog -noattr encoded.v\n')
    run(['yosys','-Q','-T','-s','emit.ys'],out,out/'emit.log')
    return importer


def check_encoded_pair(out,top,*,verify=True):
    (out/'miter.ys').write_text(f'''read_verilog gold/encoded.v
rename {top}_fourstate gold
read_verilog gate/encoded.v
rename {top}_fourstate gate
miter -equiv -flatten gold gate miter
hierarchy -check -top miter
proc
opt -full
check -assert
sat {'-verify ' if verify else ''}-prove trigger 0 -show-inputs -show-outputs -dump_json cex.json
''')
    sat=run(['yosys','-Q','-T','-s','miter.ys'],out,out/'miter.log',timeout=300,check=False)
    return sat.returncode==0 and 'SAT proof finished - no model found: SUCCESS!' in sat.stdout


def run_case(source,top,out,*,vectors=None):
    out=Path(out).resolve()
    require(not out.exists(),'preserve prior evidence')
    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',top),'invalid top name')
    out.mkdir()
    hashes={str(p.relative_to(ROOT)):digest(p) for p in (ROOT/'method/stage2/framework').rglob('*.lean')}
    hashes.update({str(p.relative_to(ROOT)):digest(p) for p in (ROOT/'method/stage2/v2lean').glob('*.py')})
    for n in hashes:
        dest=out/'source'/n;dest.parent.mkdir(parents=True,exist_ok=True);shutil.copyfile(ROOT/n,dest)
    shutil.copyfile(source,out/'original.v')
    importer=ResolvedImporter(out/'original.v',top)
    (out/'Imported.lean').write_text(importer.build());save_json(out/'source.json',importer.metadata)
    run(['lake','build','LeanRTL.Core.FourStateNetlist','LeanRTL.Core.FourStateModuleCorrect'],ROOT,out/'build.log')
    r=run(['lake','env','lean','-s','65536','--run',str(out/'Imported.lean'),'export',str(out/'emitted.v')],ROOT,out/'export.log',timeout=300)
    deps=check_axioms(r.stdout,['resolution_correct'])
    save_json(out/'resolution_certificate.json',{'status':'kernel_checked','theorems':deps,'proof_hash':digest(out/'Imported.lean')})
    gate=ResolvedImporter(out/'emitted.v',top);gate.build()
    require(list(importer.ports.items())==list(gate.ports.items()),'physical port direction/order/width changed')
    names=importer.output_names+[n['name'] for n in importer.net_metadata if n['external_input']]
    inputs={n:len(p['bits']) for n,p in importer.ports.items() if p['direction'] in ('input','inout')}
    if vectors is None:
        rng=random.Random(8129)
        vectors=[{n:''.join(rng.choice('01xz') for _ in range(w)) for n,w in inputs.items()} for _ in range(256)]
    require(bool(vectors),'empty resolved simulation')
    for row in vectors:
        require(set(row)==set(inputs) and all(len(row[n])==w and set(row[n])<=set('01xz') for n,w in inputs.items()),'invalid external-drive vector')
    save_json(out/'vectors.json',vectors)
    (out/'inputs.txt').write_text('\n'.join(' '.join(n+'='+row[n] for n in inputs) for row in vectors)+'\n')
    prefix='_'*(1+max(map(len,importer.ports)))
    tb=['`timescale 1ns / 1ps','module tb;']
    for n,p in importer.ports.items():
        w=len(p['bits']);typ='reg' if p['direction']=='input' else 'wire'
        tb.append(f'{typ} [{w-1}:0] {n};')
        if p['direction']=='inout':tb += [f'reg [{w-1}:0] {prefix+n};',f'assign {n}={prefix+n};']
    tb += [top+' dut('+', '.join('.'+n+'('+n+')' for n in importer.ports)+');','initial begin']
    fmt=' '.join(n+'=%b' for n in names)
    for row in vectors:
        for n,w in inputs.items():
            target=prefix+n if importer.ports[n]['direction']=='inout' else n
            tb.append(f"{target}={w}'b{row[n]};")
        tb.append('#1; $display("'+fmt+'", '+', '.join(names)+');')
    tb += ['$finish;','end','endmodule','']
    (out/'tb.v').write_text('\n'.join(tb))
    traces={}
    for label in ['original','emitted']:
        run(['iverilog','-g2012','-s','tb','-o',label+'.vvp',label+'.v','tb.v'],out,out/(label+'.compile.log'))
        sim=run(['vvp',label+'.vvp'],out,out/(label+'.trace.log'))
        traces[label]=[x for x in sim.stdout.splitlines() if x.startswith(names[0]+'=')]
    lean=run(['lake','env','lean','-s','65536','--run',str(out/'Imported.lean'),'eval',str(out/'inputs.txt')],ROOT,out/'lean.trace.log',timeout=300)
    check_axioms(lean.stdout,['resolution_correct'])
    traces['lean']=[x for x in lean.stdout.splitlines() if x.startswith(names[0]+'=')]
    require(all(len(xs)==len(vectors) for xs in traces.values()),'resolved trace length mismatch')
    agree=traces['original']==traces['emitted']==traces['lean']
    require(agree,'resolved four-state simulation mismatch')
    encode(out/'original.v',top,out/'gold')
    encode(out/'emitted.v',top,out/'gate')
    proved=check_encoded_pair(out,top)
    unchanged=all(digest(ROOT/n)==h for n,h in hashes.items())
    result={'status':'resolved_diagnostic_pass' if agree and proved and unchanged else 'failed',
            'samples':len(vectors),'traces_match':agree,'encoded_sat_pass':proved,'sources_unchanged':unchanged,
            'scope':'native physical inout and external-drive resolution; both actual HDL imports kernel-certified for resolution/encoding; no whole-Verilog frontend theorem or corpus promotion',
            'source_hashes':hashes,'input_sha256':digest(out/'original.v'),
            'artifact_hashes':{str(p.relative_to(out)):digest(p) for p in out.rglob('*') if p.is_file() and 'source' not in p.relative_to(out).parts}}
    save_json(out/'result.json',result)
    return result


if __name__=='__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('source',type=Path);p.add_argument('top');p.add_argument('out',type=Path)
    a=p.parse_args();r=run_case(a.source,a.top,a.out)
    print(json.dumps({k:r[k] for k in ['status','samples','traces_match','encoded_sat_pass']}))
    raise SystemExit(0 if r['status']=='resolved_diagnostic_pass' else 1)
