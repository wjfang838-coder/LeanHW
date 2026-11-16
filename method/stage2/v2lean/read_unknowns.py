"""Certify corresponding undefined reads of native memories.

This establishes a relation between arbitrary read values, never their value.
Jasper must independently confirm the exact proposed signals are its entire
out-of-bounds-read signal sets before any mapping is applied. Other X sources
are outside this certificate. Source HDL and the emitted HDL remain unchanged.
"""
import copy
import json
from pathlib import Path
import re
import shutil

from .importer import require
from .memblock_compat import cut_memories
from .pipeline import ROOT, digest, run, save_json


def without_priorities(module):
    result = copy.deepcopy(module)
    for cell in result['cells'].values():
        if cell['type'] == '$mem_v2':
            value = cell['parameters']['WR_PRIORITY_MASK']
            cell['parameters']['WR_PRIORITY_MASK'] = '0' * len(value)
    return result


def collision_certificate(wd, source_name, directory):
    require((wd / directory / 'result.json').is_file() and (wd / source_name).is_file(),
            'read-X requires the complete no-collision certificate: ' + directory)
    certificate = json.loads((wd / directory / 'result.json').read_text())
    require(certificate['status'] == 'pass' and certificate['source_sha256'] == digest(wd / source_name),
            'read-X no-collision certificate/input disagreement')
    require(set(certificate['artifact_hashes']) == {'collision.json', 'collision.ys', 'collision.log'},
            'read-X incomplete no-collision artifact manifest')
    for name, sha in certificate['artifact_hashes'].items():
        require(digest(wd / directory / name) == sha, 'changed no-collision evidence')
    require('SAT proof finished - no model found: SUCCESS!' in (wd / directory / 'collision.log').read_text(),
            'read-X no-collision proof missing')
    return certificate


def read_origins(module, mem, *, emitted=False):
    """Bind each physical RD_DATA bus to one unambiguous source read location."""
    filename = 'roundtrip.v' if emitted else 'original.v'
    name = mem['name'] if emitted else mem['source_memid'].removeprefix('\\')
    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', name),
            'read-X certificate requires an unambiguous flat memory identifier')
    cells = [c for c in module['cells'].values()
             if c['type'] == '$mem_v2' and c['parameters']['MEMID'] == '\\' + name]
    require(len(cells) == 1, 'read-X physical memory matching')
    cell = cells[0]
    pattern = re.compile(r'\$memrd\$\\' + re.escape(name) + r'\$' + re.escape(filename)
                         + r':([0-9]+)\$[0-9]+_DATA')
    origins = []
    for port in range(mem['rp']):
        bits = cell['connections']['RD_DATA'][port * mem['dw']:(port + 1) * mem['dw']]
        candidates = []
        for alias, net in module['netnames'].items():
            match = pattern.fullmatch(alias)
            if match and net['bits'] == bits:
                line = int(match[1])
                source = net.get('attributes', {}).get('src', '')
                require(re.fullmatch(re.escape(filename) + ':' + str(line) + r'\.[0-9]+-[0-9]+\.[0-9]+', source),
                        'read-X alias/source-position disagreement')
                candidates.append({'port': port, 'line': line, 'alias': alias, 'source': source,
                                   'signal': f':X__{line}_{mem["dw"]}_{mem["dw"]}_0__{name}'})
        require(len(candidates) == 1, 'ambiguous or missing physical read origin')
        origins.append(candidates[0])
    require(len({r['signal'] for r in origins}) == len(origins),
            'multiple reads share a Jasper source location')
    return origins


def certify(run_dir, evidence_dir):
    """Check the local premises and emit a hash-bound correspondence proposal.

    This does not by itself prove SEC or authorize a pass classification.
    """
    wd, out = Path(run_dir).resolve(), Path(evidence_dir).resolve()
    report = json.loads((wd / 'report.json').read_text())
    for name, sha in report['artifact_hashes'].items():
        require(digest(wd / name) == sha, 'changed local evidence: ' + name)
    for stage in ('lean_build', 'local_precheck', 'model_checks'):
        require(report.get(stage, {}).get('status') == 'pass', 'read-X requires ' + stage)
    require(not report.get('semantics', {}).get('gate_scope'), 'read-X wrapped hierarchy unsupported')
    top = report['input']['top']
    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', top), 'read-X invalid top')
    memories = report['import']['memories']
    require(memories, 'read-X requires native memories')
    require(any(m['size'] < 1 << m['aw'] for m in memories), 'no partial-depth memory')
    source = json.loads((wd / 'native_source.json').read_text())['modules'][top]
    gate = json.loads((wd / 'native_gate.json').read_text())['modules'][top]
    multiwrite = any(m['wp'] > 1 for m in memories)
    collision_proofs = {}
    if multiwrite:
        # The production native subset has no priority or collision matrices.
        # A multiwrite candidate must separately prove the source normalization,
        # absence of simultaneous collisions and actual emitted normalization.
        collision_proofs['grouping'] = collision_certificate(wd, 'native_source.json', 'grouping_collision')
        grouping = report.get('write_grouping', {})
        require(grouping.get('after_sha256') == digest(wd / 'roundtrip.v'), 'read-X grouped HDL changed')
        groups = grouping.get('groups', [])
        require({(g['memory'], g['ports']) for g in groups} ==
                {(m['name'], m['wp']) for m in memories if m['wp'] > 1}, 'read-X incomplete write grouping')
        if (wd / 'native_priority_source.json').exists():
            collision_proofs['source_priority'] = collision_certificate(wd, 'native_priority_source.json', 'priority_collision')
            raw_source = json.loads((wd / 'native_priority_source.json').read_text())['modules'][top]
            require(without_priorities(raw_source) == source, 'source normalization changed more than write priorities')
        collision_proofs['gate_priority'] = collision_certificate(wd, 'native_gate.before_priority.json', 'gate_priority_collision')
        raw_gate = json.loads((wd / 'native_gate.before_priority.json').read_text())['modules'][top]
        require(without_priorities(raw_gate) == gate, 'gate normalization changed more than write priorities')
        require(all(c['validator_sha256'] == report['implementation_hashes'].get('method/stage2/v2lean/memory_collisions.py')
                    for c in collision_proofs.values()), 'no-collision validator differs from the checked implementation')
    _, source_contracts = cut_memories(source, memories)
    _, gate_contracts = cut_memories(gate, memories, emitted=True)
    require(source_contracts == gate_contracts, 'read-X memory contracts differ')
    matching = json.loads((wd / 'native_port_matching.json').read_text())
    require(matching == report['local_precheck'] and matching['status'] == 'pass',
            'read-X transition proof/report disagreement')
    require(matching['original_sha256'] == digest(wd / 'original.v')
            and matching['emitted_sha256'] == digest(wd / 'roundtrip.v'), 'read-X transition inputs changed')
    require('SAT proof finished - no model found: SUCCESS!' in (wd / 'state_equiv.log').read_text(),
            'read-X complete transition SAT proof missing')

    # Keep hidden read aliases, then prove this is exactly the same re-elaborated
    # gate used by the accepted local proof after its documented opt_clean step.
    shutil.copyfile(wd / 'roundtrip.v', out / 'roundtrip.v')
    (out / 'read_origins.ys').write_text(
        f'read_verilog -sv roundtrip.v\nhierarchy -check -top {top}\nproc\nflatten\nmemory_collect\n'
        'write_json -noscopeinfo read_origins.json\nopt_clean\n'
        'write_json -noscopeinfo read_gate_verified.json\n')
    run(['yosys', '-Q', '-T', '-s', 'read_origins.ys'], out, out / 'read_origins.log')
    verified = json.loads((out / 'read_gate_verified.json').read_text())['modules'][top]
    require(verified == (raw_gate if multiwrite else gate),
            'read-X re-elaboration differs from checked emitted memory')
    origins_gate = json.loads((out / 'read_origins.json').read_text())['modules'][top]
    pairs, origins = [], []
    for mem in memories:
        if mem['size'] == 1 << mem['aw']:
            continue
        left = read_origins(source, mem)
        right = read_origins(origins_gate, mem, emitted=True)
        for a, b in zip(left, right):
            pairs.append([a['signal'], top + '_imp.' + b['signal']])
        origins.append({'memory': mem, 'source': left, 'emitted': right})
    require(len({a for a, _ in pairs}) == len(pairs)
            and len({b for _, b in pairs}) == len(pairs), 'read-X matching is not bijective')

    shutil.copyfile(ROOT / 'method/stage2/v2lean/proofs/ReadUnknownCorrespondence.lean', out / 'ReadUnknownCorrespondence.lean')
    run(['lake', 'env', 'lean', '-o', str(out / 'ReadUnknownCorrespondence.olean'),
         str(out / 'ReadUnknownCorrespondence.lean')], ROOT, out / 'read_theorems.log')
    local_hashes = {**report['artifact_hashes'], 'state_equiv.log': digest(wd / 'state_equiv.log')}
    proof_files = ['ReadUnknownCorrespondence.lean', 'ReadUnknownCorrespondence.olean',
                   'read_theorems.log', 'read_origins.ys', 'read_origins.log',
                   'read_origins.json', 'read_gate_verified.json']
    certificate = {
        'status': 'local_premises_checked_pending_jasper_signal_validation',
        'scope': 'corresponding arbitrary initial states and arbitrary undefined memory read values',
        'pairs': pairs, 'read_origins': origins, 'local_artifact_hashes': local_hashes,
        'collision_proofs': collision_proofs,
        'proof_artifact_hashes': {n: digest(out / n) for n in proof_files},
        'framework_hashes': {str(p.relative_to(ROOT)): digest(p)
                             for p in sorted((ROOT / 'method/stage2/framework').rglob('*.lean'))},
        'validator_sha256': digest(Path(__file__)),
        'premises': ['identical normalized physical memory contracts', 'single writer or proved collision-free grouped writes',
                     'all read addresses and write/state/output cones proved equal',
                     'equal addresses have identical definedness predicates',
                     'arbitrary read choices remain universally quantified'],
        'limitations': 'No X-propagation freedom or specification correctness claim.'}
    save_json(out / 'read_correspondence.json', certificate)
    return certificate
