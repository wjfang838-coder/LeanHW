"""Import-only entry for symbolic, clocked, and physical-time LeanRTL models.

No emission, roundtrip, Jasper, benchmark scoring, or author calls. Model kind
is explicit and recorded; a cycle-only proof cannot certify an event model.
"""
import argparse
import json
from pathlib import Path
import re
import shutil

from .pipeline import ROOT, digest, run, save_json
from .importer import Unsupported, require


def import_model(source, top, output, *, kind='symbolic', framework_root=ROOT, build=True):
    out, framework = Path(output).resolve(), Path(framework_root).resolve()
    out.mkdir(parents=True, exist_ok=False)
    report = {'status': 'running', 'mode': 'import_only', 'kind': kind,
              'roundtrip': False, 'jasper': False, 'parameter_scope': 'benchmark_defaults'}
    try:
        require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', top), 'invalid top')
        shutil.copyfile(source, out/'original.v')
        report['source_sha256'] = digest(out/'original.v')
        report['top'] = top
        report['importer_hashes'] = {p.name:digest(p) for p in sorted(Path(__file__).parent.glob('*.py'))}
        if kind == 'symbolic':
            from .symbolic import SymbolicImporter
            from .lowering import expand_slices
            (out/'frontend.ys').write_text(
                f'read_verilog -sv original.v\nhierarchy -check -top {top}\n'
                'proc\nflatten\nmemory_collect\nmemory_map -keepdc\n'
                'pmuxtree\nopt_expr -keepdc\nopt_clean\ncheck -assert\n'
                'write_json -noscopeinfo import.rtlil.json\n')
            run(['yosys','-Q','-T','-s','frontend.ys'], out, out/'frontend.log', timeout=300)
            design = json.loads((out/'import.rtlil.json').read_text())
            design, report['slice_lowering'] = expand_slices(out, design, top)
            importer = SymbolicImporter(design, top)
            report['parameters'] = design['modules'][top].get('parameter_default_values', {})
        elif kind in ('clocked', 'system', 'timed', 'fourstate'):
            from .clocked import ClockedImporter
            from .system import SystemImporter
            from .timed import TimedImporter
            from .slang import SlangImporter
            importer = {'clocked': ClockedImporter, 'system': SystemImporter,
                        'timed': TimedImporter, 'fourstate': SlangImporter}[kind](out/'original.v', top)
        else:
            raise Unsupported('unknown model kind')
        text = importer.build()
        if kind != 'symbolic':
            # Deterministic namespace adaptation, preserving the actual model.
            lines = text.splitlines()
            header = [l for l in lines if l.startswith('import ')]
            body = [l for l in lines if not l.startswith('import ')]
            text = '\n'.join(header+['namespace V2LeanImported']+body+['end V2LeanImported',''])
            report['metadata'] = importer.metadata
            report['parameters'] = {m.name:str(m.value) for m in importer.members if m.kind.name=='Parameter'}
        (out/'Imported.lean').write_text(text)
        report['ports'] = getattr(importer, 'physical_ports', importer.ports)
        # save_json sorts object keys for reproducibility. Preserve HDL order
        # explicitly; alphabetic JSON order is not the physical port order.
        report['port_order'] = list(report['ports'])
        if kind!='symbolic':
            for member in importer.members:
                if member.kind.name=='Port' and member.type.isSigned:
                    report['ports'][member.name]['signed']=1
        report['choices'] = getattr(importer, 'choices', [])
        report['choice_ranges'] = getattr(importer, 'choice_ranges', [])
        report['states'] = importer.states
        if build:
            run(['lake','build','LeanRTL'], framework, out/'framework.log', timeout=600)
        run(['lake','env','lean','-s','65536','-R',str(out),'-o',str(out/'Imported.olean'),
             str(out/'Imported.lean')], framework, out/'lean.log', timeout=1200)
        report.update(status='import_pass', implementation='V2LeanImported.impl',
                      implementation_sha256=digest(out/'Imported.lean'))
        return report
    except Exception as exc:
        report.update(status='unsupported' if isinstance(exc, Unsupported) else 'tool_error', error=str(exc))
        raise
    finally:
        report['artifacts'] = {p.name:digest(p) for p in out.iterdir() if p.is_file() and p.name!='report.json'}
        save_json(out/'report.json', report)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument('source'); p.add_argument('top'); p.add_argument('out')
    p.add_argument('--kind', choices=['symbolic','clocked','system','timed','fourstate'], default='symbolic')
    p.add_argument('--framework-root', default=str(ROOT)); p.add_argument('--no-build', action='store_true')
    a = p.parse_args()
    r = import_model(a.source,a.top,a.out,kind=a.kind,framework_root=a.framework_root,build=not a.no_build)
    print(json.dumps({k:r[k] for k in ('status','kind','parameter_scope')}))


if __name__ == '__main__': main()
