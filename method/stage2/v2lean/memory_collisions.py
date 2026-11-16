"""Prove memory write-port collisions unreachable for arbitrary Q/read values.

This is evidence for a future priority-preserving lowering; it does not mutate
memory contracts or classify any round-trip as passing.
"""
import copy
import json
from pathlib import Path

from .importer import parameter, require
from .pipeline import digest, run, save_json


def check(source_path, top, output):
    source_path, out = Path(source_path).resolve(), Path(output).resolve()
    out.mkdir(parents=True, exist_ok=False)
    module = copy.deepcopy(json.loads(source_path.read_text())['modules'][top])
    memories = [(name, c) for name, c in module['cells'].items() if c['type'] == '$mem_v2']
    require(memories, 'no memory write ports to check')
    bits = [b for c in module['cells'].values() for bs in c['connections'].values() for b in bs]
    bits += [b for p in module['ports'].values() for b in p['bits']]
    next_bit = 1 + max(b for b in bits if type(b) is int)
    prefix = 'v2lean_collision'
    used = set(module['ports']) | set(module['netnames']) | set(module['cells'])
    while any(n.startswith(prefix) for n in used):
        prefix += '_'
    serial = 0
    def fresh_name():
        nonlocal serial
        serial += 1
        return prefix + str(serial)
    def allocate(width):
        nonlocal next_bit
        result = list(range(next_bit, next_bit + width)); next_bit += width
        return result
    def input_port(bits):
        module['ports'][fresh_name()] = {'direction': 'input', 'bits': bits}
    def cell(ty, con, parameters):
        module['cells'][fresh_name()] = {
            'type': ty, 'parameters': {k: format(v, '032b') for k, v in parameters.items()},
            'port_directions': {k: 'output' if k == 'Y' else 'input' for k in con}, 'connections': con}
    module['ports'] = {n: p for n, p in module['ports'].items() if p['direction'] == 'input'}
    # Every state/read output is a free input. No reachable-state or reset
    # assumptions are available to make the collision property easier.
    for name, c in list(module['cells'].items()):
        if c['type'] in ('$dff', '$adff', '$aldff', '$dlatch'):
            input_port(c['connections']['Q']); del module['cells'][name]
        elif c['type'] == '$mem_v2':
            input_port(c['connections']['RD_DATA']); del module['cells'][name]
        else:
            require(not c['type'].startswith('$mem'), 'uncollected memory primitive')
    pairs, collision_bits = [], []
    for name, mem in memories:
        aw, dw, wp = [parameter(mem, k) for k in ('ABITS', 'WIDTH', 'WR_PORTS')]
        con = mem['connections']
        for i in range(wp):
            for j in range(i):
                same, overlap, active, collision = allocate(1), allocate(dw), allocate(1), allocate(1)
                cell('$eq', {'A': con['WR_ADDR'][i*aw:(i+1)*aw],
                             'B': con['WR_ADDR'][j*aw:(j+1)*aw], 'Y': same},
                     {'A_SIGNED': 0, 'B_SIGNED': 0, 'A_WIDTH': aw, 'B_WIDTH': aw, 'Y_WIDTH': 1})
                cell('$and', {'A': con['WR_EN'][i*dw:(i+1)*dw],
                              'B': con['WR_EN'][j*dw:(j+1)*dw], 'Y': overlap},
                     {'A_SIGNED': 0, 'B_SIGNED': 0, 'A_WIDTH': dw, 'B_WIDTH': dw, 'Y_WIDTH': dw})
                cell('$reduce_bool', {'A': overlap, 'Y': active},
                     {'A_SIGNED': 0, 'A_WIDTH': dw, 'Y_WIDTH': 1})
                cell('$and', {'A': same, 'B': active, 'Y': collision},
                     {'A_SIGNED': 0, 'B_SIGNED': 0, 'A_WIDTH': 1, 'B_WIDTH': 1, 'Y_WIDTH': 1})
                collision_bits += collision; pairs.append([name, j, i])
    require(pairs, 'no pair of write ports')
    any_collision = allocate(1)
    cell('$reduce_bool', {'A': collision_bits, 'Y': any_collision},
         {'A_SIGNED': 0, 'A_WIDTH': len(collision_bits), 'Y_WIDTH': 1})
    unknowns = 0
    for c in module['cells'].values():
        for port, bits in c['connections'].items():
            for i, bit in enumerate(bits):
                if bit in ('x', 'z'):
                    require(c['port_directions'][port] == 'input', 'undefined output driver')
                    replacement = allocate(1)
                    input_port(replacement); bits[i] = replacement[0]; unknowns += 1
    # Attributes such as init must not restrict the new arbitrary state inputs.
    for net in module['netnames'].values():
        net['attributes'] = {}
    module['ports'][prefix + '_bad'] = {'direction': 'output', 'bits': any_collision}
    save_json(out / 'collision.json', {'modules': {'collision': module}})
    (out / 'collision.ys').write_text(
        'read_json collision.json\nhierarchy -check -top collision\nopt -full\n'
        'techmap\nopt -full\nabc -g AND\nopt_clean\ncheck -assert\n'
        f'sat -verify -prove {prefix}_bad 0 -show-inputs -show-outputs -dump_json counterexample.json\n')
    result = run(['yosys', '-Q', '-T', '-s', 'collision.ys'], out, out / 'collision.log', check=False)
    passed = result.returncode == 0 and 'SAT proof finished - no model found: SUCCESS!' in result.stdout
    status = 'pass' if passed else 'counterexample' if (out / 'counterexample.json').exists() else 'tool_error'
    report = {'status': status, 'source_sha256': digest(source_path), 'pairs': pairs,
              'independent_unknown_bits': unknowns, 'validator_sha256': digest(Path(__file__)),
              'scope': 'all inputs, arbitrary Q and memory read values; all overlapping write masks at equal addresses',
              'artifact_hashes': {n: digest(out/n) for n in ('collision.json', 'collision.ys', 'collision.log')}}
    save_json(out / 'result.json', report)
    return report
