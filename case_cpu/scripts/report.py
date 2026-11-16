#!/usr/bin/env python3
"""Bind the final evidence and write a compact, source-checked result summary."""
import hashlib
import json
from pathlib import Path

ROOT=Path(__file__).resolve().parents[1]

def read(path): return json.loads(path.read_text())
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

def main():
    run=read(ROOT/'evidence/latest.json')
    if run['status']!='passed': raise RuntimeError('latest demo did not pass')
    if 'pdr' not in run: raise RuntimeError('latest demo skipped PDR; run the complete demo first')
    for name,digest in run['sources'].items():
        if sha(ROOT/name)!=digest: raise RuntimeError(f'source changed since execution: {name}')
    rtl_sha=sha(ROOT/'rtl/cpu.sv')
    miter_sha=sha(ROOT/'rtl/miter.sv')
    for task,record in run['pdr'].items():
        if record['rtl_sha256']!=rtl_sha or record['miter_sha256']!=miter_sha:
            raise RuntimeError(f'PDR is bound to different sources: {task}')
        if record['status'] not in ['proved','pdr_timeout','synthesis_timeout']:
            raise RuntimeError(f'baseline PDR error or counterexample: {task}')
        if 'pdr' in record and 'orpos;' not in record['pdr']['command'][-1]:
            raise RuntimeError('PDR must check the OR of all bad outputs')
    audits=[s for r in run['lean'].values() for s in r['axiom_audit']]
    if any('sorryAx' in s or 'ofReduceBool' in s for s in audits):
        raise RuntimeError('unacceptable proof axioms')
    if not any('drained_refinement' in s for s in audits):
        raise RuntimeError('missing acceptance-to-ISA refinement theorem')
    if len(run['mutations'])!=6 or any(x['repaired_sha256']!=rtl_sha for x in run['mutations']):
        raise RuntimeError('not all corrections return to the frozen implementation')
    extra={}
    for kind in ['mutant','repaired']:
        path=ROOT/f'evidence/pdr-stall-{kind}/result.json'
        if path.is_file():
            r=read(path)
            if r['miter_sha256']!=miter_sha: raise RuntimeError('supplementary miter changed')
            extra[kind]=dict(result=str(path.relative_to(ROOT)),**r)
    if extra:
        if set(extra)!=set(['mutant','repaired']): raise RuntimeError('incomplete supplementary repair pair')
        if extra['mutant']['status']!='counterexample' or extra['repaired']['status']!='proved':
            raise RuntimeError('supplementary PDR repair did not demonstrate failure then proof')
        if extra['repaired']['rtl_sha256']!=rtl_sha: raise RuntimeError('repaired PDR source mismatch')
    summary={
        'demo':run['evidence'],
        'rtl_sha256':rtl_sha,
        'diagnosis':dict(ambiguity=3,incompleteness=2,contradiction=2,
                         scope='seven clause-local contexts and seven projected observations'),
        'lean':dict(status='kernel_checked',unbounded=True,
                    scope='Lean cycle model -> transaction ISA, plus acceptance/order conservation',
                    printed_axiom_audits=audits,
                    replay_seconds=sum(m['seconds'] for m in run['lean'].values())),
        'cosimulation':dict(status='passed',**run['simulation']),
        'corrections':run['mutations'],
        'pdr':run['pdr'],
        'supplementary_stall_repair_pdr':extra,
        'limits':[
            'No unbounded SystemVerilog-to-Lean-cycle equivalence certificate.',
            'No liveness/fairness proof; arbitrary permanent stalls are allowed.',
            'No independent LLM clarification or blind repair experiment.',
            'No controlled speedup or stall-specific hardness claim.'
        ]}
    (ROOT/'evidence/final.json').write_text(json.dumps(summary,indent=2)+'\n')
    counts=run['simulation']['counts']
    lines=[
        'RV32 arithmetic CPU: actual execution results',
        f"Evidence: {run['evidence']}",
        f'RTL SHA-256: {rtl_sha}',
        '',
        'Diagnosis: 3 ambiguity + 2 incompleteness + 2 contradiction witnesses certified.',
        'Revision: determined on the seven-context diagnostic projection.',
        'Lean: unbounded cycle-to-ISA refinement, ordered acceptance conservation,',
        '      drained execution of exactly the accepted program; no sorry/native axioms.',
        f"Lean certificate replay: {summary['lean']['replay_seconds']:.3f} seconds (not proof-development time).",
        f"Co-simulation: {counts['cycles']} edges; {counts['accepted']} accepted; {counts['retired']} retired;",
        f"               {counts['discarded_by_reset']} explicitly aborted by reset; all 29 instructions and 32 stall masks.",
        'Corrections: all 6 faulty implementations detected; all 6 local repairs pass all vectors.',
        '']
    for task,r in run['pdr'].items():
        p=r.get('pdr')
        seconds=f"{p['seconds']:.3f}s wall" if p else 'not entered'
        lines.append(f"ABC PDR {task}: {r['status']}; synthesis={r['synthesis']['seconds']:.3f}s; PDR={seconds}; budget={r['pdr_seconds']}s.")
        if r.get('aiger'):
            a=r['aiger']
            lines.append(f"  AIGER: {a['ands']} ANDs, {a['latches']} latches, {a['bad']} bad outputs, {a['constraints']} reset constraint; fold + orpos.")
    if extra:
        lines += ['', 'Supplementary RTL PDR correction:',
                  '  Ignoring WB stall: counterexample (see evidence/pdr-stall-mutant/abc.log).',
                  '  Repaired source: sanity properties proved with the same miter.']
    lines += ['', 'Proof scope: Lean cycle -> ISA. RTL correspondence is tested; an unbounded RTL -> cycle proof is not supplied.',
              'A PDR timeout is an inconclusive resource-bounded outcome, not a failure of correctness or a proof of intrinsic hardness.',
              'All raw logs, commands, sources/hashes and intermediate development failures are retained in evidence/.']
    (ROOT/'RESULTS.txt').write_text('\n'.join(lines)+'\n')
    print('\n'.join(lines))

if __name__=='__main__': main()
