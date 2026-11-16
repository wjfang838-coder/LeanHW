"""Round-trip diagnostics for initialized autonomous constant-delay RTL.

Includes equality of the two actual imported timed Lean models for every model
timestamp, source update certificates, and three-way physical-time simulation.
This is a separate timed profile, not a claim of ordinary Jasper SEC signoff.
"""
import argparse
import json
from pathlib import Path
import re
import shutil

from .pipeline import ROOT, digest, run, save_json
from .importer import require
from .slang import audit_source_proofs
from .timed import TimedImporter


def equivalence_source(gold, gate):
    headers = 'import LeanRTL.Core.FourStateTimed\nimport LeanRTL.Core.FourStateProcedural\n'
    def body(importer):
        return '\n'.join(line for line in importer.model_text.splitlines() if not line.startswith('import '))
    return (headers + 'namespace Gold\n' + body(gold) + '\nend Gold\nnamespace Gate\n' + body(gate)
            + '\nend Gate\n'
            + 'theorem timed_models_equal : Gold.impl = Gate.impl := by source_kernel_rfl\n'
            + 'theorem timed_roundtrip (t : Nat) : Gold.impl.renderAt t = Gate.impl.renderAt t :=\n'
            + '  LeanRTL.FourState.Timed.trace_equiv Gold.impl Gate.impl timed_models_equal t\n'
            + '#print axioms timed_roundtrip\n')


def run_case(source, top, out, *, ticks=64):
    out = Path(out).resolve()
    require(not out.exists(), 'preserve prior evidence; choose a new directory')
    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', top), 'invalid top identifier')
    require(type(ticks) is int and 1 <= ticks <= 1000, 'ticks must be in 1..1000')
    out.mkdir(parents=True)
    hashes = {str(p.relative_to(ROOT)): digest(p) for p in (ROOT/'method/stage2/framework').rglob('*.lean')}
    hashes.update({str(p.relative_to(ROOT)): digest(p) for p in (ROOT/'method/stage2/v2lean').glob('*.py')})
    for name in hashes:
        dest = out/'source'/name
        dest.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT/name, dest)
    shutil.copyfile(source, out/'original.v')
    gold = TimedImporter(out/'original.v', top)
    (out/'Imported.lean').write_text(gold.build())
    save_json(out/'source.json', gold.metadata)
    run(['lake', 'build', 'LeanRTL.Core.FourStateTimed', 'LeanRTL.Core.FourStateProcedural'], ROOT, out/'build.log')
    result = run(['lake', 'env', 'lean', '-s', '65536', '--run', str(out/'Imported.lean'),
                  'export', str(out/'emitted.v')], ROOT, out/'export.log', timeout=120)
    cert = audit_source_proofs(result.stdout, gold.metadata)
    cert['proof_hash'] = digest(out/'Imported.lean')
    save_json(out/'source_certificate.json', cert)
    gate = TimedImporter(out/'emitted.v', top)
    (out/'Reimported.lean').write_text(gate.build())
    save_json(out/'reimported.json', gate.metadata)
    (out/'Roundtrip.lean').write_text(equivalence_source(gold, gate))
    proof = run(['lake', 'env', 'lean', '-s', '65536', str(out/'Roundtrip.lean')], ROOT, out/'proof.log')
    audits = re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", proof.stdout, re.S)
    free = re.findall(r"'([^']+)' does not depend on any axioms", proof.stdout)
    expected = {'Gold.source_initial_correct', 'Gold.source_update_correct',
                'Gate.source_initial_correct', 'Gate.source_update_correct', 'timed_roundtrip'}
    require(len(audits)+len(free) == len(expected) and {n for n,_ in audits}|set(free) == expected,
            'missing or ambiguous timed proof audit')
    deps = {n: sorted({a.strip() for a in axioms.split(',') if a.strip()}) for n,axioms in audits}
    deps.update({n: [] for n in free})
    require(all(set(xs) <= {'propext','Classical.choice','Quot.sound'} for xs in deps.values()), 'untrusted timed proof axiom')
    save_json(out/'timed_certificate.json', {'status': 'kernel_checked', 'theorem': 'timed_roundtrip',
        'scope': 'actual source and emitted HDL imports have identical timed Lean models at every nonnegative femtosecond timestamp; AST parsing/elaboration remains trusted; no ordinary Jasper signoff',
        'theorems': deps, 'proof_hash': digest(out/'Roundtrip.lean'),
        'hdl_hashes': {n: digest(out/n) for n in ('original.v','emitted.v')}})
    period = gold.period_fs
    times = sorted({0} | {n*period+d for n in range(1,ticks+1) for d in (-1,0,1)})
    require(times[-1]+1 < 2**64, 'simulation horizon exceeds time range')
    (out/'times.txt').write_text('\n'.join(map(str,times))+'\n')
    name = gold.output_names[0]
    width = len(gold.ports[name]['bits'])
    body = ['`timescale 1fs / 1fs', 'module tb;', f'wire [{width-1}:0] observed;',
            f'{top} dut(.{name}(observed));', 'initial begin',
            '$dumpfile("wave.vcd"); $dumpvars(0,tb);']
    prev = 0
    for t in times:
        body += [f"#(64'd{t-prev});", f'$strobe("{t} {name}=%b", observed);']
        prev = t
    body += ['#1; $finish;', 'end', 'endmodule', '']
    (out/'tb.v').write_text('\n'.join(body))
    traces = {}
    pattern = re.compile(r'\d+ '+re.escape(name)+r'=([01xz]+)')
    for label in ('original','emitted'):
        run(['iverilog','-g2012','-s','tb','-o',label+'.vvp',label+'.v','tb.v'],out,out/(label+'.compile.log'))
        sim = run(['vvp',label+'.vvp'],out,out/(label+'.trace.log'))
        (out/'wave.vcd').rename(out/(label+'.vcd'))
        traces[label] = [x.strip() for x in sim.stdout.splitlines() if pattern.fullmatch(x.strip())]
    lean = run(['lake','env','lean','-s','65536','--run',str(out/'Imported.lean'),'eval',str(out/'times.txt')],
               ROOT,out/'lean.trace.log')
    audit_source_proofs(lean.stdout,gold.metadata)
    traces['lean'] = [x.strip() for x in lean.stdout.splitlines() if pattern.fullmatch(x.strip())]
    require(all(len(xs)==len(times) for xs in traces.values()), 'timed trace length mismatch')
    agree = traces['original']==traces['emitted']==traces['lean']
    unchanged = all(digest(ROOT/n)==h for n,h in hashes.items())
    report = {'status': 'timed_model_roundtrip_pass' if agree and unchanged else 'failed',
              'samples':len(times),'ticks':ticks,'period_fs':period,'traces_match':agree,
              'trace_lengths':{n:len(xs) for n,xs in traces.items()},'sources_unchanged':unchanged,
              'ordinary_jasper_sec':'not applicable to the modeled simulation delay; not a corpus promotion',
              'source_hashes':hashes,'input_sha256':digest(out/'original.v'),
              'artifact_hashes':{str(p.relative_to(out)):digest(p) for p in out.rglob('*') if p.is_file() and 'source' not in p.relative_to(out).parts}}
    save_json(out/'result.json', report)
    return report


if __name__ == '__main__':
    p=argparse.ArgumentParser(description=__doc__)
    p.add_argument('source',type=Path); p.add_argument('top'); p.add_argument('out',type=Path)
    p.add_argument('--ticks',type=int,default=64)
    a=p.parse_args(); r=run_case(a.source,a.top,a.out,ticks=a.ticks)
    print(json.dumps({k:r[k] for k in ('status','samples','period_fs','traces_match')}))
    raise SystemExit(0 if r['status']=='timed_model_roundtrip_pass' else 1)
