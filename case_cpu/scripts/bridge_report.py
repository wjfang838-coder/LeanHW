#!/usr/bin/env python3
"""Verify the new two-level certificate manifest and summarize it separately from PDR."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]
REPO=ROOT.parent

def main():
    r=json.loads((ROOT/'evidence/bridge-latest.json').read_text())
    assert r['status']=='proved'
    for name,digest in r['sources'].items():
        if hashlib.sha256((REPO/name).read_bytes()).hexdigest()!=digest:
            raise RuntimeError(f'proof source changed since replay: {name}')
    for name,m in r['modules'].items():
        text=(ROOT/m['log']).read_text()
        if 'sorryAx' in text or 'error:' in text:
            raise RuntimeError(f'proof replay failed: {name}')
    audit=(ROOT/r['modules']['Audit']['log']).read_text()
    required=['rtl_cycle_refinement','rtl_isa_refinement','rtl_isa_physical_events',
              'rtl_drained_refinement','rtl_conservation','rtl_accepted_cycle',
              'retirement_pc','retirement_value','port_debug','port_arch_pc']
    if any(f'CaseCPU.Bridge.{n}' not in audit for n in required):
        raise RuntimeError('final audit missing a required theorem')
    old=json.loads((ROOT/'evidence/final.json').read_text())
    if old['rtl_sha256']!=r['source_binding']['rtl_sha256']:
        raise RuntimeError('PDR and Lean evidence refer to different RTL revisions')
    lines=[
        'RV32 arithmetic CPU: two-level refinement certificate',
        f"Evidence: {r['evidence']}",
        f"RTL SHA-256: {r['source_binding']['rtl_sha256']}",
        'Status: PROVED (unbounded safety over arbitrary finite traces).',
        '',
        'Fresh Yosys/symbolic import: exact text match with the proved AST.',
        '341 combinational nodes; 19 state groups / 1419 state bits.',
        'All five choice ports (210 bits) remain arbitrary and universally quantified.',
        'One initial synchronous reset; arbitrary later words, seeds, stalls and resets.',
        '',
        'rtl_cycle_refinement: real imported core.step -> frozen cycle LeanSpec.',
        'rtl_isa_refinement: compose cycle model -> transaction ISA.',
        'rtl_isa_physical_events: ISA reference consumes actual RTL retirement outputs.',
        'rtl_conservation: physical retirements + pending = initial pending + physical acceptances.',
        'rtl_drained_refinement: execute exactly all physically accepted instructions once drained.',
        'Retirement PC/result and architectural PC/debug observations are connected to real ports.',
        '',
        f"Full certificate replay: {r['replay_seconds']:.3f}s; this excludes proof-development time.",
        f"Native certificate dependencies in the audited theorem set: {len(r['native_certificates'])}.",
        'No sorryAx, assumed step equivalence, fixed program, fixed choices or simulation premises.',
        'Trust: Lean/standard axioms; native LRAT/finite checks; Yosys/symbolic frontend.',
        'This is explicitly NOT a native-axiom-free or frontend-correctness proof.',
        '',
        f"Unchanged ABC PDR full result: {old['pdr']['full']['status']} at its recorded budget.",
        'The Lean proof does not change PDR timeout into PDR success.',
        'No liveness/fairness theorem or fair speedup comparison is claimed.',
        '',
        'Reproduce: python3 case_cpu/scripts/bridge.py',
        'Verify this summary: python3 case_cpu/scripts/bridge_report.py',
    ]
    (ROOT/'BRIDGE_RESULTS.txt').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))

if __name__=='__main__': main()
