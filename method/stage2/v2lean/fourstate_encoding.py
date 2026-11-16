"""Encode both actual HDL artifacts into explicit 0/1/X/Z planes for diagnostics.

Unlike an X-only mask, tag/data preserves Z as (1,1) and X as (1,0).
The encoding compiler has general expression/module correctness proofs.
Original Verilog frontend fidelity remains a separate boundary: encoded miters
alone do not promote a corpus case.
"""
import json
from pathlib import Path
import re
import shutil

from .fourstate import FourStateImporter
from .importer import require
from .pipeline import ROOT, digest, run, save_json


def encode_artifact(source, top, out, *, frontend="yosys"):
    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', top), 'invalid top identifier')
    require(frontend in ('yosys', 'slang'), 'unknown encoding frontend')
    out = Path(out).resolve()
    out.mkdir(parents=True, exist_ok=False)
    shutil.copyfile(source, out / 'input.v')
    if frontend == 'yosys':
        (out / 'read.ys').write_text(f'read_verilog -sv input.v\nhierarchy -check -top {top}\n'
                                    'proc -noopt\nflatten\nwrite_json input.json\n')
        run(['yosys', '-Q', '-T', '-s', 'read.ys'], out, out / 'read.log')
        design = json.loads((out / 'input.json').read_text())
        text = FourStateImporter(design, top, compact_names=True).build()
    else:
        from .slang import SlangImporter
        importer = SlangImporter(out / 'input.v', top)
        text = importer.build()
        design = importer.metadata
        save_json(out / 'input.json', design)
    # Bind the general semantic theorem to the actual imported/encoded module.
    text = 'import LeanRTL.Core.FourStateModuleCorrect\n' + text
    text = text.replace('def main (args',
                        'example : (Encoding.module impl).checkErrors = [] := by decide +kernel\n'
                        'theorem encoding_valid : Encoding.encodingValid impl = true := by decide +kernel\n'
                        'theorem encoding_correct (env : LeanRTL.Env) :\n'
                        '  Encoding.decodeOutputPairs impl.outputs\n'
                        '    ((Encoding.module impl).outputs?eval (fun _ => 0) env) =\n'
                        '    some (impl.eval (Encoding.decodedEnv env)) :=\n'
                        '  Encoding.module_correct_decoded impl encoding_valid env\n'
                        '#print axioms encoding_correct\n'
                        'def main (args')
    require('theorem encoding_correct' in text, 'missing generated proof insertion point')
    (out / 'Imported.lean').write_text(text)
    result = run(['lake', 'env', 'lean', '-s', '65536', '--run', str(out / 'Imported.lean'),
                  'encode', str(out / 'encoded.json')], ROOT, out / 'encode.log', timeout=300)
    if frontend == 'slang':
        from .slang import audit_source_proofs
        source_certificate = audit_source_proofs(result.stdout, design)
        source_certificate['proof_hash'] = digest(out / 'Imported.lean')
        save_json(out / 'source_certificate.json', source_certificate)
    matches = re.findall(r"'encoding_correct' depends on axioms: \[([^\]]*)\]", result.stdout, re.S)
    require(len(matches) == 1, 'missing or ambiguous encoding correctness axiom audit')
    axioms = {a.strip() for a in matches[0].split(',') if a.strip()}
    require(axioms <= {'propext', 'Classical.choice', 'Quot.sound'}, 'untrusted encoding proof axiom')
    save_json(out / 'encoding_certificate.json', {
        'status': 'kernel_checked', 'theorem': 'encoding_correct', 'axioms': sorted(axioms),
        'frontend': frontend,
        'scope': 'actual four-state Module.eval equals decoded actual encoded Module outputs for every '
                 'binary environment; Verilog frontend and downstream serialization are separate boundaries',
        'proof_hash': digest(out / 'Imported.lean'), 'encoded_json_hash': digest(out / 'encoded.json'),
    })
    encoded = json.loads((out / 'encoded.json').read_text())
    module = encoded['modules'][top + '_fourstate']
    for cell in module['cells'].values():
        for bits in cell['connections'].values():
            require(all(type(b) is int or b in ('0', '1') for b in bits), 'encoded logic contains X/Z')
    for port in module['ports'].values():
        require(all(type(b) is int or b in ('0', '1') for b in port['bits']), 'encoded port contains X/Z')
    (out / 'emit.ys').write_text('read_json encoded.json\ncheck -assert\nopt_clean\nwrite_verilog -noattr encoded.v\n')
    run(['yosys', '-Q', '-T', '-s', 'emit.ys'], out, out / 'emit.log')
    return design['modules'][top]['ports']


def simulate_encoding(out, top, ports, vectors):
    out = Path(out)
    ins = {n: len(p['bits']) for n, p in ports.items() if p['direction'] == 'input'}
    outs = {n: len(p['bits']) for n, p in ports.items() if p['direction'] == 'output'}
    lines = ['module tb;']
    for direction, wires in [('reg', ins), ('wire', outs)]:
        for n, w in wires.items():
            for rail in ('t', 'd'):
                lines.append(f'{direction} [{w-1}:0] {rail}__{n};')
    names = [r + '__' + n for n in ports for r in ('t', 'd')]
    lines += [f'{top}_fourstate dut(' + ','.join(f'.{n}({n})' for n in names) + ');', 'initial begin']
    fmt = ' '.join(r + '__' + n + '=%b' for n in outs for r in ('t', 'd'))
    for values in vectors:
        for n, w in ins.items():
            tag = ''.join('1' if b in 'xz' else '0' for b in values[n])
            data = ''.join('1' if b in '1z' else '0' for b in values[n])
            lines.append(f"t__{n}={w}'b{tag}; d__{n}={w}'b{data};")
        lines.append('#1; $display("' + fmt + '",' + ','.join(r + '__' + n for n in outs for r in ('t', 'd')) + ');')
    lines += ['$finish; end endmodule']
    (out / 'tb.v').write_text('\n'.join(lines) + '\n')
    run(['iverilog', '-g2012', '-s', 'tb', '-o', 'sim.vvp', 'encoded.v', 'tb.v'], out, out / 'compile.log')
    r = run(['vvp', 'sim.vvp'], out, out / 'trace.log')
    traces = []
    for line in r.stdout.splitlines():
        if not line.startswith('t__'): continue
        values = dict(t.split('=') for t in line.split())
        decoded = {}
        for n, w in outs.items():
            t, d = values['t__' + n], values['d__' + n]
            require(len(t) == len(d) == w and set(t+d) <= set('01'), 'encoded simulation is not binary')
            decoded[n] = ''.join({'00': '0', '01': '1', '10': 'x', '11': 'z'}[a+b] for a, b in zip(t, d))
        traces.append(' '.join(n + '=' + decoded[n] for n in outs))
    (out / 'decoded.log').write_text('\n'.join(traces) + '\n')
    require(len(traces) == len(vectors), 'encoded sample count mismatch')
    return traces


def compare_case(case_dir, out, *, gold_frontend="yosys", gate_frontend="yosys"):
    case_dir, out = Path(case_dir).resolve(), Path(out).resolve()
    require(not out.exists(), 'preserve prior evidence')
    out.mkdir(parents=True)
    source_report = json.loads((case_dir / 'result.json').read_text())
    require(source_report['status'] == 'simulation_pass', 'three-way samples must already pass')
    for n in ('original.v', 'emitted.v', 'Imported.lean', 'vectors.json', 'source.json', 'original.trace.log'):
        require(digest(case_dir / n) == source_report['artifact_hashes'][n], 'changed case artifact: ' + n)
    top = next(iter(json.loads((case_dir / 'source.json').read_text())['modules']))
    vectors = json.loads((case_dir / 'vectors.json').read_text())
    hashes = {str(p.relative_to(ROOT)): digest(p) for p in (ROOT / 'method/stage2/framework').rglob('*.lean')}
    hashes.update({str(p.relative_to(ROOT)): digest(p) for p in (ROOT / 'method/stage2/v2lean').glob('*.py')})
    for n in hashes:
        target = out / 'source' / n
        target.parent.mkdir(parents=True, exist_ok=True)
        shutil.copyfile(ROOT / n, target)
    run(['lake', 'build', 'LeanRTL.Core.FourStateModuleCorrect', 'LeanRTL.Core.FourStateVerilog',
         *(['LeanRTL.Core.FourStateProcedural'] if 'slang' in (gold_frontend, gate_frontend) else [])],
        ROOT, out / 'build.log')
    traces = {}
    for label, name in [('gold', 'original.v'), ('gate', 'emitted.v')]:
        ports = encode_artifact(case_dir / name, top, out / label,
                                frontend=gold_frontend if label == 'gold' else gate_frontend)
        traces[label] = simulate_encoding(out / label, top, ports, vectors)
    expected = [l for l in (case_dir / 'original.trace.log').read_text().splitlines()
                if l.startswith(next(n for n, p in ports.items() if p['direction'] == 'output') + '=')]
    sample_match = traces['gold'] == traces['gate'] == expected
    script = f'''read_verilog gold/encoded.v
rename {top}_fourstate gold
read_verilog gate/encoded.v
rename {top}_fourstate gate
miter -equiv -flatten gold gate miter
hierarchy -check -top miter
proc
opt -full
check -assert
sat -verify -prove trigger 0 -show-inputs -show-outputs -dump_json cex.json
'''
    (out / 'miter.ys').write_text(script)
    r = run(['yosys', '-Q', '-T', '-s', 'miter.ys'], out, out / 'miter.log', timeout=300, check=False)
    sat_pass = r.returncode == 0 and 'SAT proof finished - no model found: SUCCESS!' in r.stdout
    unchanged = all(digest(ROOT / n) == h for n, h in hashes.items())
    result = {'status': 'encoded_diagnostic_pass' if sample_match and sat_pass and unchanged else 'failed',
              'frontends': {'gold': gold_frontend, 'gate': gate_frontend},
              'samples': len(vectors), 'sample_match': sample_match, 'sat_pass': sat_pass,
              'sources_unchanged': unchanged, 'source_hashes': hashes,
              'scope': 'all binary assignments of both encoding planes; includes all four-state inputs; '
                       'encoding Module.eval correctness kernel-certified; Verilog frontend fidelity remains '
                       'a separate boundary; not a corpus pass',
              'input_hashes': {n: digest(case_dir / n) for n in ('original.v', 'emitted.v', 'Imported.lean', 'vectors.json')},
              'artifact_hashes': {str(p.relative_to(out)): digest(p) for p in out.rglob('*')
                                  if p.is_file() and 'source' not in p.relative_to(out).parts}}
    save_json(out / 'result.json', result)
    return result


if __name__ == '__main__':
    import argparse
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('case_dir', type=Path)
    parser.add_argument('out', type=Path)
    parser.add_argument('--gold-frontend', choices=('yosys', 'slang'), default='yosys')
    parser.add_argument('--gate-frontend', choices=('yosys', 'slang'), default='yosys')
    args = parser.parse_args()
    result = compare_case(args.case_dir, args.out, gold_frontend=args.gold_frontend, gate_frontend=args.gate_frontend)
    print(json.dumps({k: result[k] for k in ('status', 'samples', 'sample_match', 'sat_pass')}))
    raise SystemExit(0 if result['status'] == 'encoded_diagnostic_pass' else 1)
