"""Check native memory contracts and infer write-port order by full SAT proof.

Port matching is a search for a proved correspondence, never an assumption.
All read addresses, write clocks/masks and active write addresses/data, register
controls and D inputs, and original outputs remain in every candidate miter.
"""
import copy
from itertools import permutations, product
import json
from math import factorial
from pathlib import Path
import re
import shutil

from .importer import require
from .memblock_compat import cut_memories
from .pipeline import digest, run, save_json
from .statecheck import cut


def write_orders(memories, limit=720):
    """Bound combinatorial search explicitly; no silent unmatched fallback."""
    count = 1
    for mem in memories:
        count *= factorial(mem['wp'])
        require(count <= limit, 'native write-port matching search limit exceeded')
    return product(*(permutations(range(mem['wp'])) for mem in memories))


def rejected_write_pairs(counterexample, memories):
    """Use witnessed unequal write observations to prune only failed matches.

    Read inputs and Q correspondence stay fixed across permutations; swapping
    write observations does not change either underlying cone. A zero cmp port
    witnesses failure of that source/target write pair for one actual input.
    Missing or unknown values do not justify pruning. Acceptance still requires
    a whole-miter SAT proof for a complete bijection.
    """
    unequal = {s['name'] for s in counterexample.get('signal', [])
               if s.get('wave', '').startswith('0')}
    rejected = set()
    for mi, mem in enumerate(memories):
        order = mem.get('gate_write_order', list(range(mem['wp'])))
        for i, j in enumerate(order):
            if any(f'cmp_{mem["name"]}_{field}{i}' in unequal for field in ('wc', 'we', 'wa', 'wd')):
                rejected.add((mi, i, j))
    return rejected


def check(directory, top, states, memories):
    out = Path(directory)
    require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*', top), 'invalid top')
    # Never overwrite a rejected candidate or evidence from an earlier run.
    attempts_dir = out / 'memory_matching'
    attempts_dir.mkdir(exist_ok=False)
    script = (f'read_verilog -sv roundtrip.v\nhierarchy -check -top {top}\n'
              'proc\nflatten\nmemory_collect\nopt_clean\n'
              'write_json -noscopeinfo native_gate.json\n')
    (out / 'native_gate.ys').write_text(script)
    run(['yosys', '-Q', '-T', '-s', 'native_gate.ys'], out, out / 'native_gate.log')
    target = json.loads((out / 'native_gate.json').read_text())['modules'][top]
    native_source = json.loads((out / 'native_source.json').read_text())['modules'][top]
    _, original_contracts = cut_memories(native_source, memories)
    source = json.loads((out / 'import.rtlil.json').read_text())['modules'][top]
    gold, gc = cut(source, states, emitted=False)
    attempts, rejected = [], set()
    pruned_orders = 0
    for number, orders in enumerate(write_orders(memories)):
        if any((mi, i, j) in rejected for mi, order in enumerate(orders) for i, j in enumerate(order)):
            pruned_orders += 1
            continue
        candidate = copy.deepcopy(memories)
        for mem, order in zip(candidate, orders):
            mem['gate_write_order'] = list(order)
        gate_before_cut, contracts = cut_memories(target, candidate, emitted=True)
        require(contracts == original_contracts, 'native memory contract changed')
        gate, ic = cut(gate_before_cut, states, emitted=True)
        require(gc == ic, 'register contract changed')
        trial = attempts_dir / f'{number:03d}'
        trial.mkdir()
        save_json(trial / 'state_gold.cut.json', {'modules': {'gold': gold}})
        save_json(trial / 'state_gate.cut.json', {'modules': {'gate': gate}})
        (trial / 'state_equiv.ys').write_text(
            'read_json state_gold.cut.json\nread_json state_gate.cut.json\n'
            'miter -equiv -make_outcmp -flatten gold gate equiv\nhierarchy -check -top equiv\n'
            'opt -full\ntechmap\nopt -full\nabc -g AND\nopt_clean\ncheck -assert\n'
            'sat -verify -prove trigger 0 -show-inputs -show-outputs '
            '-dump_json state.counterexample.json\n')
        proc = run(['yosys', '-Q', '-T', '-s', 'state_equiv.ys'], trial,
                   trial / 'state_equiv.log', check=False)
        success = proc.returncode == 0 and 'SAT proof finished - no model found: SUCCESS!' in proc.stdout
        counterexample = ('proof did fail' in proc.stdout + proc.stderr
                          and (trial / 'state.counterexample.json').exists())
        status = 'pass' if success else 'counterexample' if counterexample else 'tool_error'
        attempts.append({'directory': str(trial.relative_to(out)), 'write_orders': orders,
                         'status': status, 'exit_code': proc.returncode})
        if counterexample:
            new_rejections = rejected_write_pairs(json.loads((trial / 'state.counterexample.json').read_text()), candidate)
            attempts[-1]['rejected_write_pairs'] = sorted(new_rejections)
            rejected.update(new_rejections)
        report = {'status': status, 'attempts': attempts,
                  'pruned_orders': pruned_orders, 'rejected_write_pairs': sorted(rejected),
                  'scope': 'native memory/register contracts and all transition cones; arbitrary read values and Q',
                  'original_sha256': digest(out / 'original.v'),
                  'emitted_sha256': digest(out / 'roundtrip.v')}
        save_json(out / 'native_port_matching.json', report)
        if success:
            save_json(out / 'native_memories.json', candidate)
            save_json(out / 'native_memory_contracts.json', {'original': original_contracts, 'emitted': contracts})
            save_json(out / 'state_contracts.json', {'original': gc, 'emitted': ic, 'states': states})
            save_json(out / 'state_gate.json', {'modules': {top: gate_before_cut}})
            for name in ('state_gold.cut.json', 'state_gate.cut.json', 'state_equiv.ys', 'state_equiv.log'):
                shutil.copyfile(trial / name, out / name)
            for side in ('gold', 'gate'):
                name = f'state_{side}.emit.ys'
                (out / name).write_text(f'read_json state_{side}.cut.json\nrename {side} {top}\n'
                                        f'write_verilog -noattr state_{side}.cut.v\n')
                run(['yosys', '-Q', '-T', '-s', name], out, out / f'state_{side}.emit.log')
            return report
        # A tool failure is not evidence against a correspondence. Stop and
        # expose it, rather than spending an unbounded sequence of timeouts.
        require(counterexample, 'native port matching tool failed; see candidate log')
    report['pruned_orders'] = pruned_orders
    save_json(out / 'native_port_matching.json', report)
    require(False, 'no write-port permutation proved the complete transition relation')
