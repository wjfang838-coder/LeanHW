"""Fresh NL → relational LeanSpec → generated RTL → checked refinement smoke run.

This explicit profile covers the one-bit, stateless mux benchmark and its Stage 1
trace representation. It refuses incompatible artifacts rather than claiming a
general sequential-design adapter. Results and agent transcripts stay in data/.
Run from the repository after source env.sh; external author calls require the
operator's authorization. No historical RTL or proof is used.
"""
from __future__ import annotations
import argparse
import json
from pathlib import Path
import shutil
import subprocess
import sys

from common import agent, agent_backend, paths
from leanspec import cases
from v2lean.import_refinement import import_model
from refinement_contract import write_contract
from refinement_checks import check, sha, source_manifest

ROOT = Path(paths.REPO)
TEMPLATES = ROOT / 'method/stage2/example/mux_e2e'


def save(p: Path, value):
    p.parent.mkdir(parents=True, exist_ok=True)
    p.write_text(json.dumps(value, indent=2, ensure_ascii=False) + '\n')


def invoke(work: Path, tag: str, prompt: str, frozen: list[Path]):
    before = {str(p.relative_to(work)): sha(p) for p in frozen if p.is_file()}
    role = agent.Role(tag=tag, tools=agent.BASE_TOOLS + agent.LEAN_TOOLS,
                      allow=(str(work),), readonly=tuple(map(str, frozen)),
                      inputs=tuple(map(str, frozen)), timeout=1800)
    result = agent_backend.run(role, str(work), prompt,
                               str(work / 'logs' / (tag + '.jsonl')))
    after = {str(p.relative_to(work)): sha(p) for p in frozen if p.is_file()}
    if before != after:
        raise RuntimeError('Protected inputs changed during author session')
    save(work / 'logs' / (tag + '.result.json'), result)
    if result['rc'] or result.get('session_error'):
        raise RuntimeError(f'{tag}: {result.get("session_error") or result["stderr"]}')


def stage(work: Path, case):
    work.mkdir(parents=True, exist_ok=False)
    out = Path(case.dir) / 'out'
    handoff = json.loads((out / 'HANDOFF.json').read_text())
    for src, dst in ((out / 'DecidedSpec.lean', 'DecidedSpec.lean'),
                     (Path(case.sandbox) / 'Partial.lean', 'Partial.lean'),
                     (Path(case.sandbox) / 'spec.txt', 'spec.txt')):
        shutil.copyfile(src, work / dst)
    for name in ('FrozenSpec.lean', 'HandoffContract.lean'):
        shutil.copyfile(TEMPLATES / name, work / name)
    for name in ('LeanSpec', 'SpecIR'):
        base = ROOT / 'method/stage1/leanspec/lean'
        shutil.copytree(base / name, work / name, ignore=shutil.ignore_patterns('*.olean', '__pycache__'))
        shutil.copyfile(base / (name + '.lean'), work / (name + '.lean'))
    base = ROOT / 'method/stage2/framework'
    shutil.copytree(base / 'LeanRTL', work / 'LeanRTL', ignore=shutil.ignore_patterns('*.olean', '__pycache__'))
    shutil.copyfile(base / 'LeanRTL.lean', work / 'LeanRTL.lean')
    shutil.copyfile(ROOT / 'method/stage2/refinement/lean/FrozenRefinement.lean', work / 'FrozenRefinement.lean')
    shutil.copyfile(ROOT / 'lean-toolchain', work / 'lean-toolchain')
    libs = ['LeanSpec', 'SpecIR', 'LeanRTL', 'Partial', 'DecidedSpec', 'FrozenSpec',
            'Imported', 'FrozenRefinement', 'FrozenContract', 'HandoffContract', 'Rewrite']
    (work / 'lakefile.toml').write_text('name = "mux_certificate"\n' + '\n'.join(
        f'[[lean_lib]]\nname = "{n}"\nglobs = ' +
        json.dumps([n, n + '.+'] if (work / n).is_dir() else [n]) + '\n' for n in libs))
    save(work / 'iface.json', {'module': 'TopModule', 'timebase': 'fullCycle',
         'inputs': [{'name': n, 'width': 1} for n in ('a', 'b', 'sel')],
         'outputs': [{'name': 'out', 'width': 1}]})
    save(work / 'handoff.json', {'profile': 'stateless-one-bit-mux-traces',
         'source_spec_sha256': sha(work / 'spec.txt'),
         'partial_sha256': sha(work / 'Partial.lean'),
         'decided_sha256': sha(work / 'DecidedSpec.lean'),
         'stage1_handoff_sha256': sha(out / 'HANDOFF.json'),
         'stage1_handoff': handoff,
         'claim': 'exact original relation equivalence for every finite Boolean input/output trace',
         'target': 'HandoffContract.Exact'})


def negative_controls(work: Path):
    """Incorrect implementation and vacuous handoff must both fail the same checker."""
    from refinement_checks import copy_sources
    manifest = source_manifest(work)
    base = work.parent / 'negative-controls'
    results = {}
    for kind in ('wrong-rtl', 'vacuous-handoff'):
        dest = base / kind
        copy_sources(work, dest, manifest)
        # Warm caches only speed rejection checks; the accepted certificate uses cold replay.
        if (work / '.lake').is_dir():
            shutil.copytree(work / '.lake', dest / '.lake')
        if kind == 'wrong-rtl':
            (dest / 'candidate.v').write_text(
                "module TopModule(input a, input b, input sel, output out);\n"
                "assign out = 1'b0;\nendmodule\n")
            import_model(dest / 'candidate.v', 'TopModule', dest / 'bad-import',
                         framework_root=ROOT, build=False)
            shutil.copyfile(dest / 'bad-import/Imported.lean', dest / 'Imported.lean')
            shutil.copyfile(dest / 'bad-import/report.json', dest / 'import-report.json')
            report = json.loads((dest / 'import-report.json').read_text())
            write_contract(dest, 'negative-mux', report)
        else:
            (dest / 'handoff.term').write_text('by trivial\n')
        result = check(dest, dest / 'check', cold=False)
        if result['ok']:
            raise RuntimeError('Negative control unexpectedly passed: ' + kind)
        expected = {'rewrite', 'proof'} if kind == 'wrong-rtl' else {'handoff'}
        if result.get('failure_stage') not in expected:
            raise RuntimeError(f'Negative control failed for infrastructure, not semantics: {result}')
        results[kind] = {'rejected': True, 'failure_stage': result['failure_stage'],
                         'log': str((dest / 'check/result.json').relative_to(work.parent))}
    save(base / 'summary.json', results)
    return results


def execute(case_name: str, reuse_stage1: bool = False, max_repairs: int = 4):
    if not reuse_stage1:
        prose = ROOT / 'benchmarks/verilogeval/clarified/Prob022_mux2to1/spec.clarified.txt'
        subprocess.run([sys.executable, '-m', 'leanspec.cli', 'new', case_name,
                        '--bench', 'local', '--prose', str(prose),
                        '--why', 'Fresh end-to-end mux run'], cwd=ROOT, check=True)
        profile_path = Path(cases.find(case_name).dir) / 'formalization-profile.json'
        save(profile_path, {'name': 'stateless-bool-mux-traces-v1'})
        profile_hash = sha(profile_path)
        subprocess.run([sys.executable, '-u', '-m', 'leanspec.author', '--case', case_name,
                        '--workers', '1', '--max-rounds', '2', '--repairs', '2'], cwd=ROOT, check=True)
        if sha(profile_path) != profile_hash:
            raise RuntimeError('Stage 1 changed the representation profile')
    case = cases.find(case_name)
    # An author process exit is not itself evidence that diagnosis converged.
    rounds = sorted((Path(case.dir) / 'steps').glob('round*/09_*.json'))
    if not rounds or not json.loads(rounds[-1].read_text()).get('ok'):
        raise RuntimeError('Stage 1 did not converge; inspect its step 09 and author log')
    work = Path(paths.part2('local', case_name, 'e2e'))
    if work.exists():
        raise FileExistsError(f'Use a fresh case name; existing evidence is preserved: {work}')
    stage(work, case)
    frozen = [p for p in work.iterdir() if p.name != 'logs']
    print('Stage 2: authoring fresh RTL from this case specification', flush=True)
    invoke(work, 'implement', '''Read spec.txt. Write candidate.v containing exactly TopModule
with a,b,sel one-bit inputs and out one-bit output, declaration order a,b,sel,out.
Implement the specified stateless combinational behavior. No testbench, no other files.
No historical implementation or proof is available. Do not read credentials.''', frozen)
    report = import_model(work / 'candidate.v', 'TopModule', work / 'import', framework_root=ROOT)
    if report['states'] or report['choices']:
        raise ValueError('This smoke profile requires stateless deterministic RTL')
    shutil.copyfile(work / 'import/Imported.lean', work / 'Imported.lean')
    shutil.copyfile(work / 'import/report.json', work / 'import-report.json')
    write_contract(work, case_name, report)
    (work / 'Rewrite.lean').write_text('import FrozenSpec\nimport Imported\nimport FrozenContract\n')
    return prove(work, case_name, max_repairs)


def prove(work: Path, case_name: str, max_repairs: int = 4):
    feedback = ''
    for attempt in range(1, max_repairs + 2):
        frozen = [p for p in work.iterdir() if p.name not in {
            'Rewrite.lean', 'proof.term', 'handoff.term', 'logs', '.lake', 'lake-manifest.json'}]
        prompt = '''Complete a kernel-checked proof of the actual imported RTL against the
frozen reference. Read Partial.lean, DecidedSpec.lean, FrozenSpec.lean, Imported.lean,
FrozenContract.lean, FrozenRefinement.lean and HandoffContract.lean.
Write ONLY Rewrite.lean (supporting lemmas), proof.term and handoff.term.
proof.term must have exactly the type:
FrozenRefinement.Refines FrozenContract.spec (FrozenContract.model V2LeanImported.impl)
handoff.term must have exactly the type HandoffContract.Exact.
Both files contain a Lean term (typically `by ...`), not a theorem declaration.
The latter connects the actual Stage 1 relation to the functionalized reference for
ALL finite traces, including empty traces. A finite diagnostic sweep is insufficient.
Use lean/lake locally to check lemmas. All inputs/library sources are frozen.
No sorry/admit/new axioms/native_decide/unsafe/metaprogramming or altered targets.
Standard tactics including simp, omega, decide +kernel and ordinary induction are allowed.
For this no-state circuit, a Certificate with relation True is sound ONLY if you prove
its mandatory observe obligation for EVERY input and oracle. Do not drop ports.
Use #print axioms for helpers. You may write scratch *.lean files, but all lemmas needed
for the certificate must be in Rewrite.lean (no imports from scratch files).
Do not read credentials. Do not modify candidate.v or Imported.lean.
'''
        if feedback:
            prompt += '\nCompiler/checker feedback:\n' + feedback
        print(f'Stage 2: proof author attempt {attempt}', flush=True)
        invoke(work, f'prove-{attempt}', prompt, frozen)
        for name in ('proof.term', 'handoff.term', 'Rewrite.lean'):
            if not (work / name).is_file():
                raise RuntimeError('Author did not produce ' + name)
        checked = check(work, work / 'logs' / f'check-{attempt}', cold=False)
        if checked['ok']:
            break
        feedback = json.dumps({k: checked.get(k) for k in ('failure_stage', 'tail', 'unexpected_axioms')})
        print('Proof feedback:', feedback[-2500:], flush=True)
    else:
        raise RuntimeError('Proof repair budget exhausted; generated evidence is preserved')
    print('Stage 2: source-only isolated replay', flush=True)
    final = check(work, work / 'logs/final-cold', cold=True)
    if not final['ok']:
        raise RuntimeError('Cold replay failed: ' + str(final.get('tail')))
    print('Stage 2: negative controls', flush=True)
    negatives = negative_controls(work)
    save(work / 'end-to-end.json', {'ok': True, 'case': case_name,
         'negative_controls': negatives,
         'stages': ['NL extraction', 'LeanSpec diagnosis/convergence', 'exact trace handoff',
                    'RTL authoring', 'Yosys actual RTL import', 'unbounded refinement', 'cold replay'],
         'provenance': 'fresh external author/prover sessions, recorded in logs',
         'rtl_sha256': sha(work / 'candidate.v'),
         'imported_sha256': sha(work / 'Imported.lean'),
         'handoff_sha256': sha(work / 'handoff.json'),
         'proof_source_manifest': source_manifest(work),
         'axioms': final['axioms'], 'kernel_only': final['kernel_only'],
         'scope': 'binary stateless mux, all finite traces; no physical delay or X/Z claim'})
    print('PASS:', work / 'end-to-end.json', flush=True)
    return work


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--case', default='mux_e2e')
    parser.add_argument('--reuse-stage1', action='store_true')
    parser.add_argument('--max-repairs', type=int, default=4)
    a = parser.parse_args()
    execute(a.case, a.reuse_stage1, a.max_repairs)


if __name__ == '__main__':
    main()
