"""Physical event/settled-state diagnostics for actual clocked HDL roundtrips."""
import json
from pathlib import Path
import re
import shutil

from .clocked import ClockedImporter
from .pipeline import ROOT, digest, run, save_json
from .importer import require
from .slang import audit_source_proofs


def compile_model(out, filename, executable, importer):
    source=out/filename
    cfile=out/(executable+'.c')
    proof=run(['lake','env','lean','-s','65536','--root='+str(out),'-c',str(cfile),str(source)],
              ROOT,out/(executable+'.kernel.log'),timeout=300)
    certificate=audit_source_proofs(proof.stdout,importer.metadata)
    archive=ROOT/'.lake/build/lib/libleansilicon_LeanRTL.a'
    require(archive.exists(),'missing compiled LeanRTL library')
    run(['lake','env','leanc','-O3','-o',str(out/executable),str(cfile),str(archive)],
        ROOT,out/(executable+'.link.log'),timeout=300)
    certificate.update(proof_hash=digest(source),c_hash=digest(cfile),
                       executable_hash=digest(out/executable),archive_hash=digest(archive))
    return certificate


def run_case(source, top, out, *, vectors, frontend='clocked'):
    out = Path(out).resolve()
    require(not out.exists(), 'preserve previous clocked evidence')
    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',top), 'invalid top identifier')
    require(frontend in ('clocked','system'),'unknown clocked frontend')
    if frontend=='system':
        from .system import SystemImporter
        importer_type=SystemImporter
    else: importer_type=ClockedImporter
    out.mkdir(parents=True)
    hashes = {str(p.relative_to(ROOT)):digest(p) for p in (ROOT/'method/stage2/framework').rglob('*.lean')}
    hashes.update({str(p.relative_to(ROOT)):digest(p) for p in (ROOT/'method/stage2/v2lean').glob('*.py')})
    for n in hashes:
        dest=out/'source'/n; dest.parent.mkdir(parents=True,exist_ok=True); shutil.copyfile(ROOT/n,dest)
    shutil.copyfile(source,out/'original.v')
    gold = importer_type(out/'original.v',top)
    (out/'Imported.lean').write_text(gold.build()); save_json(out/'source.json',gold.metadata)
    run(['lake','build','LeanRTL:static'],ROOT,out/'build.log',timeout=300)
    gold_cert=compile_model(out,'Imported.lean','gold_model',gold)
    run([str(out/'gold_model'),'export',str(out/'emitted.v')],out,out/'export.log')
    gate = importer_type(out/'emitted.v',top)
    (out/'Reimported.lean').write_text(gate.build()); save_json(out/'reimported.json',gate.metadata)
    gate_cert=compile_model(out,'Reimported.lean','gate_model',gate)
    require(list(gold.ports.items())==list(gate.ports.items()), 'clocked port order/direction/width changed')
    require(gold.metadata['events']==gate.metadata['events'], 'clock/reset event controls changed')
    require(gold.metadata['states']==gate.metadata['states'], 'state correspondence changed')
    require(gold.metadata['signed_ports']==gate.metadata['signed_ports'], 'physical port signedness changed')
    if frontend=='system':
        require(gold.metadata['scalar_ports']==gate.metadata['scalar_ports'],'scalar/vector port shape changed')
    inputs={n:len(p['bits']) for n,p in gold.ports.items() if p['direction'] in ('input','inout')}
    names=gold.output_names+gold.inout_names
    require(bool(vectors) and bool(names), 'clocked diagnostic requires inputs and observations')
    for row in vectors:
        require(set(row)==set(inputs) and all(len(row[n])==w and set(row[n])<=set('01xz') for n,w in inputs.items()),
                'invalid clocked input vector')
    save_json(out/'vectors.json',vectors)
    steps=vectors
    if frontend=='system':
        # Stabilize external data before changing clock/reset controls. Compare
        # both settled phases; do not hide combinational observations in between.
        controls={n for events in gold.metadata['events'] for n,_ in events}
        previous={n:'x'*w for n,w in inputs.items()};steps=[]
        for row in vectors:
            data_phase={n:previous[n] if n in controls else row[n] for n in inputs}
            steps += [data_phase,dict(row)];previous=row
    save_json(out/'steps.json',steps)
    (out/'inputs.txt').write_text('\n'.join(' '.join(n+'='+row[n] for n in inputs) for row in steps)+'\n')
    tb=['`timescale 1ns / 1ps','module tb;']
    prefix='_'*(1+max(map(len,gold.ports)))
    drive_names={n:prefix+n if p['direction']=='inout' else n for n,p in gold.ports.items() if p['direction'] in ('input','inout')}
    for n,p in gold.ports.items():
        tb.append(f'{"reg" if p["direction"]=="input" else "wire"} [{len(p["bits"])-1}:0] {n};')
        if p['direction']=='inout':
            tb += [f'reg [{len(p["bits"])-1}:0] {drive_names[n]};',f'assign {n}={drive_names[n]};']
    tb += [top+' dut('+', '.join('.'+n+'('+n+')' for n in gold.ports)+');', 'initial begin']
    fmt=' '.join(n+'=%b' for n in names)
    for row in steps:
        # One concatenated blocking assignment updates all external stimulus
        # values before triggered processes execute. Observations are settled.
        tb += ['{'+', '.join(drive_names[n] for n in inputs)+'} = {'+', '.join(f"{w}'b{row[n]}" for n,w in inputs.items())+'};',
               '#1; $display("'+fmt+'", '+', '.join(names)+');']
    tb += ['$finish;','end','endmodule','']
    (out/'tb.v').write_text('\n'.join(tb))
    def observations(stdout):
        records=[]
        for line in stdout.splitlines():
            tokens=line.strip().split()
            if not tokens or not all(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*=[01xz]+',t) for t in tokens):continue
            values=dict(t.split('=') for t in tokens)
            require(len(tokens)==len(values) and set(values)==set(names),'invalid/duplicate model output names')
            require(all(len(values[n])==len(gold.ports[n]['bits']) for n in names),'model output width changed')
            records.append(' '.join(n+'='+values[n] for n in names))
        return records
    traces={}
    for label in ('original','emitted'):
        run(['iverilog','-g2012','-s','tb','-o',label+'.vvp',label+'.v','tb.v'],out,out/(label+'.compile.log'))
        sim=run(['vvp',label+'.vvp'],out,out/(label+'.trace.log'))
        traces[label]=observations(sim.stdout)
    certificates={'gold':gold_cert,'gate':gate_cert}
    for label,executable in [('lean','gold_model'),('reimported','gate_model')]:
        result=run([str(out/executable),'eval',str(out/'inputs.txt')],
                   ROOT,out/(label+'.trace.log'),timeout=300)
        traces[label]=observations(result.stdout)
    require(all(len(xs)==len(steps) for xs in traces.values()), 'clocked trace length mismatch')
    mismatch=next((i for i in range(len(steps)) if len({xs[i] for xs in traces.values()})!=1),None)
    unchanged=all(digest(ROOT/n)==h for n,h in hashes.items())
    report={'status':'clocked_trace_diagnostic_pass' if mismatch is None and unchanged else 'failed',
            'samples':len(steps),'supplied_vectors':len(vectors),'frontend':frontend,
            'state_bits':gold.metadata['state_bits'],'traces_match':mismatch is None,
            'first_mismatch':None if mismatch is None else {'index':mismatch,'input':steps[mismatch],
                'outputs':{n:xs[mismatch] for n,xs in traces.items()}},
            'scope':'actual HDL and both Lean imports, selected input-transition traces; not universal temporal equivalence or corpus promotion',
            'source_hashes':hashes,'sources_unchanged':unchanged,'input_sha256':digest(out/'original.v'),
            'process_certificates':certificates,
            'artifact_hashes':{str(p.relative_to(out)):digest(p) for p in out.rglob('*') if p.is_file() and 'source' not in p.relative_to(out).parts}}
    save_json(out/'result.json',report)
    return report


if __name__=='__main__':
    import argparse
    parser=argparse.ArgumentParser(description=__doc__)
    parser.add_argument('source',type=Path);parser.add_argument('top');parser.add_argument('out',type=Path)
    parser.add_argument('--vectors',type=Path,required=True)
    parser.add_argument('--frontend',choices=['clocked','system'],default='clocked')
    args=parser.parse_args()
    result=run_case(args.source,args.top,args.out,vectors=json.loads(args.vectors.read_text()),frontend=args.frontend)
    print(json.dumps({k:result[k] for k in ('status','samples','first_mismatch')}))
    raise SystemExit(0 if result['status']=='clocked_trace_diagnostic_pass' else 1)
