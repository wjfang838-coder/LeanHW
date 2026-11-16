#!/usr/bin/env python3
"""Decided-only, immutable SpecIR → LeanRTL → emit → equivalence → emit runner.

Run from method with LEANSILICON_DATA set to data_all. This entry never invokes
an NL/specification author or the old original-arm/challenge state machine.
"""
from __future__ import annotations

import argparse
import datetime as dt
import fcntl
import hashlib
import json
import os
from pathlib import Path
import re
import shutil
import subprocess
import sys
import time
import tempfile

from common import agent, paths, variant
from leanrtl import contract, stage, verify
from leanrtl.frozen_exec import command_prefix

REPO = Path(paths.REPO)
from common import agent_backend


# This runner performs LeanRTL correction against an already frozen LeanSpec.
# Source RTL/spec generation may use another model, but correction authorship is
# deliberately fixed so source-model labels cannot leak into this phase.
CORRECTION_MODEL = 'gpt-5.6-sol'


def sha(p: Path) -> str:
    return hashlib.sha256(p.read_bytes()).hexdigest()


def write(p: Path, obj) -> None:
    p.parent.mkdir(parents=True, exist_ok=True)
    tmp = p.with_name(p.name + '.tmp')
    tmp.write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n')
    tmp.replace(p)


def now() -> str:
    return dt.datetime.now(dt.timezone.utc).isoformat()


def inventory(root: Path) -> dict:
    return {str(p.relative_to(root)): sha(p) for p in sorted(root.rglob('*'))
            if p.is_file() and not p.is_symlink() and
            not any(x in p.parts for x in ('.lake', '.git', '__pycache__'))}


def check_inventory(root: Path, expected: dict) -> None:
    for rel, digest in expected.items():
        p = root / rel
        if p.is_symlink() or any(x.is_symlink() for x in p.parents if x != root.parent) or not p.is_file() or sha(p) != digest:
            raise RuntimeError(f'immutable input changed: {p}')


def run_command(ws: Path, argv: list[str], name: str, timeout=1200) -> dict:
    started = time.time()
    dest = ws / 'attempts' / name
    dest.mkdir(parents=True, exist_ok=True)
    try:
        protected = [ws/p for p in ('inputs','SpecIR','scripts','contracts','specs','assets','snapshots') if (ws/p).exists()]
        protected.extend((ws/'out').glob('*.preproof.v'))
        protected.extend(ws/p for p in ('proof-result.json','evaluation-ready.json') if (ws/p).exists())
        actual_argv = command_prefix(ws, readonly=protected) + argv
        proc = subprocess.run(actual_argv, cwd=ws, capture_output=True, text=True, timeout=timeout)
        rc, output = proc.returncode, proc.stdout + proc.stderr
    except subprocess.TimeoutExpired as exc:
        rc = 124
        output = str(exc.stdout or '') + str(exc.stderr or '') + '\nTIMEOUT'
    (dest / 'command.log').write_text(output)
    result = dict(ok=rc == 0, rc=rc, argv=argv, elapsed=time.time()-started,
                  log=str(dest / 'command.log'), tail=output[-18000:],
                  isolation='private-network-pid-home-workspace-only')
    write(dest / 'command.json', result)
    return result


def guard(ws: Path, run: dict) -> None:
    manifest = json.loads((Path(paths.DATA)/'inputs-manifest.json').read_text())
    row = next(x for x in manifest['cases'] if (x['benchmark'], x['key']) == (run['bench'], run['key']))
    frozen = json.loads((Path(run['input_source'])/'frozen.json').read_text())
    # Older rosters stored the frozen *content* digest directly.  The v2lean
    # roster stores the file digest in spec_frozen_sha256 and retains the
    # content digest under historical_compile, so do not confuse the two.
    expected_frozen_sha256 = row.get('frozen_sha256') or (row.get('historical_compile') or {}).get('frozen_sha256')
    if expected_frozen_sha256 != frozen['content_sha256']:
        raise RuntimeError('case freeze differs from authoritative input roster')
    content_digest = hashlib.sha256(json.dumps(frozen['files'], sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    if content_digest != expected_frozen_sha256:
        raise RuntimeError('frozen file list no longer matches authoritative input roster')
    expected_source = {f['path']: f['sha256'] for f in frozen['files']}
    source_root = Path(run['input_source'])
    actual_source = {str(p.relative_to(source_root)) for p in source_root.rglob('*') if p.is_file() or p.is_symlink()}
    if actual_source != set(expected_source) | {'frozen.json'}:
        raise RuntimeError('Frozen input file closure changed')
    check_inventory(source_root, expected_source)
    expected_copy = {k: v for k, v in expected_source.items() if k == 'spec.decided.txt' or k.startswith('lean/')}
    actual_copy = {str(p.relative_to(ws/'inputs')) for p in (ws/'inputs').rglob('*') if p.is_file() or p.is_symlink()}
    if actual_copy != set(expected_copy):
        raise RuntimeError('Copied frozen input file closure changed')
    check_inventory(ws/'inputs', expected_copy)
    check_inventory(Path(run['input_source']), run['input_inventory'])
    check_inventory(ws / 'inputs', run['copied_input_inventory'])
    check_inventory(ws, run['immutable'])
    for name in ('preproof', 'final'):
        p = ws / 'snapshots' / name / 'manifest.json'
        if p.exists():
            rec = json.loads(p.read_text())
            check_inventory(p.parent, rec['files'])
            if name in ('preproof', 'final'):
                suffix = '.preproof.v' if name == 'preproof' else '.v'
                published = ws/'out'/(run['key'] + suffix)
                expected = p.parent/'out'/f"{run['key']}.v"
                if not published.is_file() or sha(published) != sha(expected):
                    raise RuntimeError(f'published {name} artifact differs from immutable emission snapshot')
    if (ws / 'evaluation.json').exists():
        raise RuntimeError('workspace has evaluator feedback; author resumption requires a clean private copy')


def state(ws: Path, phase: str, **extra) -> None:
    previous = json.loads((ws / 'status.json').read_text()) if (ws / 'status.json').exists() else {}
    write(ws / 'status.json', {**previous, 'status': phase, 'updated_at': now(), **extra})
    print(f'{ws.parent.name}: {phase}', flush=True)


def snapshot(ws: Path, key: str, name: str, run: dict) -> dict:
    published = ws / 'snapshots' / name
    if published.exists():
        raise RuntimeError(f'refusing to overwrite immutable snapshot: {published}')
    published.parent.mkdir(parents=True, exist_ok=True)
    dest = Path(tempfile.mkdtemp(prefix='.'+name+'.pending-', dir=published.parent))
    selected = ['frags', 'LeanRTL', 'SpecIR', 'SpecIR.lean', 'FrozenSpec.lean',
                'FrozenSpecBridge.lean', 'FrozenProof.lean', 'lakefile.toml', 'lean-toolchain',
                'Main.lean', 'LeanRTL.lean', 'scripts', 'inputs', 'contracts', 'specs']
    for rel in selected:
        src = ws / rel
        if src.is_dir():
            shutil.copytree(src, dest / rel, ignore=shutil.ignore_patterns('__pycache__'))
        elif src.is_file():
            shutil.copy2(src, dest / rel)
    (dest / 'out').mkdir()
    for ext in ('.v', '.rtlil.json'):
        src = ws / 'out' / (key + ext)
        if src.exists():
            shutil.copy2(src, dest / 'out' / src.name)
    rec = dict(stage=name, at=now(), files=inventory(dest),
               input_sha256=run['frozen_sha256'], method=run['method'])
    write(dest / 'manifest.json', rec)
    for p in dest.rglob('*'):
        if p.is_file():
            p.chmod(0o444)
    dest.rename(published)
    return rec


def frozen_toplevel(source: Path, override: str | None = None) -> str:
    """The emitted module name is part of the frozen interface, never the case key."""
    path = source/'lean/iface.json'
    if not path.is_file():
        raise RuntimeError(f'input_blocked: frozen interface is absent: {path}')
    name = json.loads(path.read_text()).get('module')
    if not isinstance(name, str) or not re.fullmatch(r'[A-Za-z_][A-Za-z0-9_$]*', name):
        raise RuntimeError(f'input_blocked: unsupported frozen module name: {name!r}')
    if override is not None and override != name:
        raise RuntimeError(f'--toplevel {override!r} contradicts frozen interface module {name!r}')
    return name


def stage_frozen(a) -> tuple[Path, dict]:
    source = Path(a.input or Path(paths.DATA) / 'part1' / a.bench / a.key).resolve()
    ws = Path(a.ws or Path(paths.DATA) / 'part2' / a.bench / a.key / 'decided').resolve()
    if (ws / 'frozen-run.json').exists():
        run = json.loads((ws / 'frozen-run.json').read_text())
        if (run['bench'], run['key'], run['input_source']) != (a.bench, a.key, str(source)):
            raise RuntimeError('run identity mismatch')
        if run.get('config', {}).get('model') != CORRECTION_MODEL:
            raise RuntimeError(
                f"correction workspace was authored with {run.get('config', {}).get('model')!r}; "
                f"correction requires {CORRECTION_MODEL!r} and must use a clean workspace"
            )
        if run['method']['digest'] != variant.method_digest():
            raise RuntimeError('method version changed; use a new --ws and preserve this run')
        if run['toplevel'] != frozen_toplevel(source, getattr(a, 'toplevel', None)):
            raise RuntimeError('run top-level module differs from frozen interface')
        guard(ws, run)
        return ws, run
    if not (source / 'frozen.json').is_file():
        raise RuntimeError(f'input_blocked: missing {source / "frozen.json"}')
    freeze = json.loads((source / 'frozen.json').read_text())
    check_inventory(source, {f['path']: f['sha256'] for f in freeze['files']})
    if freeze.get('input_status') not in ('ready', 'frozen', 'available', 'input_ready', 'ok', 'spec_scope_unresolved'):
        raise RuntimeError('input_blocked: '+str(freeze.get('input_status')))
    source_inventory = inventory(source)
    # The authoritative freeze producer validates its own richer manifest; we additionally bind
    # every copied input/evidence byte here and recheck these bytes at every transition.
    top = frozen_toplevel(source, getattr(a, 'toplevel', None))
    stage.main(['--profile', 'two-author', '--key', a.key, '--spec',
                str(source / 'spec.decided.txt'), '--ws', str(ws), '--toplevel', top,
                '--arm', 'decided', '--no-build'])
    (ws / 'inputs').mkdir()
    shutil.copy2(source / 'spec.decided.txt', ws / 'inputs/spec.decided.txt')
    shutil.copytree(source / 'lean', ws / 'inputs/lean')
    # Historical evidence and source selection records are withheld from the author.
    lean = source / 'lean'
    entry = next((lean / n for n in ('decided.lean', 'FrozenSpec.lean', 'Spec.lean')
                  if (lean / n).is_file()), None)
    if entry is None:
        raise RuntimeError('input_blocked: frozen Lean entry is absent')
    # Prefer the byte-exact dependency closure supplied by the freeze producer.
    dep = lean / 'deps' / 'SpecIR'
    if not dep.is_dir() or not (lean / 'deps' / 'SpecIR.lean').is_file():
        raise RuntimeError('input_blocked: frozen SpecIR dependency closure is absent')
    shutil.copytree(dep, ws / 'SpecIR')
    shutil.copy2(lean / 'deps' / 'SpecIR.lean', ws / 'SpecIR.lean')
    shutil.copy2(entry, ws / 'FrozenSpec.lean')
    bridge = REPO / 'method/stage2/framework/FrozenSpecBridge.lean'
    if not bridge.exists():
        raise RuntimeError('bridge framework not ready')
    shutil.copy2(bridge, ws / bridge.name)
    with (ws / 'lakefile.toml').open('a') as stream:
        stream.write('\n[[lean_lib]]\nname = "SpecIR"\nglobs = ["SpecIR", "SpecIR.+"]\n'
                     '\n[[lean_lib]]\nname = "FrozenSpec"\n'
                     '\n[[lean_lib]]\nname = "FrozenSpecBridge"\n')
    write(ws / 'contracts' / f'{a.key}.json',
          contract.derive((source / 'spec.decided.txt').read_text(), a.key, top))
    for folder in ('attempts', 'snapshots', 'bridge', 'logs'):
        (ws / folder).mkdir(exist_ok=True)
    iface = json.loads((ws/'inputs/lean/iface.json').read_text())
    public_parameters = iface.get('integration_contract', {}).get('parameters', [])
    parameter_scope = {'kind': 'fixed_frozen_instance', 'public_parameters': public_parameters,
                       'covers_all_declared_values': not public_parameters,
                       'limitation': ('Frozen SpecIR.Gen.spec and current Module target have no quantified parameter family' if public_parameters else '')}
    static = ['inputs', 'SpecIR', 'SpecIR.lean', 'FrozenSpec.lean', 'FrozenSpecBridge.lean',
              'scripts', 'contracts', 'specs', 'assets', 'LeanRTL/Core', 'LeanRTL/Lib',
              'lakefile.toml', 'Main.lean', 'LeanRTL.lean', 'lean-toolchain']
    immutable = {}
    for rel in static:
        p = ws / rel
        if p.is_dir():
            immutable.update({str(Path(rel) / k): v for k, v in inventory(p).items()})
        elif p.exists():
            immutable[rel] = sha(p)
    for rel in immutable:
        (ws / rel).chmod(0o444)
    run = dict(schema=1, arm='decided', frozen_spec=True, bench=a.bench, key=a.key,
               toplevel=top, toplevel_source='lean/iface.json.module', input_source=str(source), input_inventory=source_inventory,
               copied_input_inventory=inventory(ws/'inputs'),
               frozen_sha256=freeze['content_sha256'], frozen_metadata_sha256=sha(source/'frozen.json'), immutable=immutable, created_at=now(),
               parameter_scope=parameter_scope,
               event_scope={'bridge':'fullCycle Module.simulate', 'subcycle_events_proved':False},
               method={'digest': variant.method_digest(), 'backend': agent_backend.identity()},
               config={'attempts_per_phase': a.attempts, 'agent_timeout': a.agent_timeout,
                       'model': agent_backend.codex_model(), 'backend': agent_backend.backend()})
    write(ws/'frozen-run.json', run)
    state(ws, 'staged', bench=a.bench, key=a.key, arm='decided')
    return ws, run


def author(ws: Path, run: dict, phase: str, attempt: int, feedback: str) -> dict:
    key = run['key']
    impl = f'frags/{key}/impl.lean'
    proof = f'frags/{key}/equivalence.lean'
    common = f'''Work only in {ws}. Read inputs/spec.decided.txt and FrozenSpec.lean (the frozen
SpecIR.Gen.spec) and docs/dsl-reference.md plus relevant current LeanRTL framework sources.
This is decided-only. No NL formalization, spec replacement, spec challenge or reference RTL.
The frozen SpecIR object is authoritative. Do not alter its semantics, parameters, assumptions,
input space, output names, unknown values, initial states, timebase or latency. Write only
{impl}, {proof if phase == 'proof' else 'notes/implementation.md'} and notes/ diagnostics.
Never edit scripts, dependencies, generated assembled files, Verilog, contracts, or snapshots.
Emit a LeanRTL.Module named `impl` with module name `{run['toplevel']}`. Fragments are inserted
inside namespace LeanRTL.Blind.{stage.camel_of(key)}, so do not add imports or namespace wrappers.
Use hardware constructs supported by the current LeanRTL DSL and implement every observable
output. Do not write `sorry`, `admit`, custom axioms, unsafe overrides or native_decide.
`bv_decide` is allowed only with audited native LRAT axioms and no native overrides; the result
will disclose its larger trusted base. `native_decide` and arbitrary native axioms are forbidden.
You can run `python3 scripts/bbf.py {key} build --role frozen-driver` to check the implementation.
Driver alone decides phase completion and runs the authoritative emitter/proof gates.
'''
    if phase == 'impl':
        task = f'''FIRST IMPLEMENTATION PHASE. Write {impl}. This phase is before any functional
equivalence proof; do not write equivalence lemmas, proofs, proof fragments, or use equivalence
counterexamples to redesign. Type/build/emission errors may be fixed. Do not invoke emit; the
driver will capture the first successfully emitted Verilog immediately after your session.
Do not write {proof}. The proof phase begins only after preproof snapshot exists.'''
    elif phase == 'correction':
        task = f'''SIMDIFF CORRECTION PHASE. Correct {impl} using only the frozen LeanSpec,
LeanRTL build/emission diagnostics, and the internal frozen-spec simdiff supplied below.
Do not read or use benchmark testbenches, reference RTL, evaluator outputs, or prior TB results.
Do not write {proof}; proof is deferred because a candidate with zero grounded simdiff may be
sealed and evaluated first. Preserve the frozen interface and latency exactly. Run the local
build and FrozenDiagnostic checks as useful, and leave the best compiling implementation in
{impl}.'''
    else:
        task = f'''PROOF PHASE. The original successful emission has been captured immutably.
Read FrozenSpecBridge.lean. Write {proof} as a Lean TERM proving exactly:
  FrozenSpecBridge.Equivalent SpecIR.Gen.spec LeanRTL.Blind.{stage.camel_of(key)}.impl
Usually start the file with `by`. The driver embeds it in a fixed theorem; no declarations before
or after the proof term. You may add helper lemmas to impl.lean, or use `have` inside the proof.
Equivalent requires exact equality for EVERY finite input trace, initial observation, all outputs,
concrete input encoding, and supported fullCycle semantics. Use Certificate if useful.
No restricted input predicates, no ignored unknown values, no altered initial state or shifts.
Fix proof or impl as needed, preserving frozen SpecIR. A proof failure alone is not evidence of
inequivalence. Record actual semantic counterexamples or unsupported semantics in notes.
Do not emit final Verilog yourself; driver will freshly rebuild the theorem and emit twice.'''
        task += f'''
LOCAL PROOF CHECK (required after your last change): `bbf.py ... build` checks the
implementation only. It does NOT read equivalence.lean or refresh the imported implementation
olean. Do not report proof success from that command.
1. Run `python3 scripts/asm_f.py {key}`, then
   `lake build LeanRTL.Blind.{stage.camel_of(key)}`. These trusted assembly/build commands are
   permitted; never hand-edit their generated sources. Repeat after every implementation edit.
2. Write notes/FrozenProofCheck.lean with EXACTLY this header followed by the current, unchanged
   contents of {proof}:
import FrozenSpec
import FrozenSpecBridge
import LeanRTL.Blind.{stage.camel_of(key)}
set_option maxHeartbeats 3200000
set_option autoImplicit false
theorem frozen_equivalence : FrozenSpecBridge.Equivalent SpecIR.Gen.spec LeanRTL.Blind.{stage.camel_of(key)}.impl :=
Do not add namespaces, `open` commands, imports, assumptions or helper declarations to this
wrapper. Helpers belong in impl.lean or inside the proof term. The proof is at the root namespace;
qualify implementation names explicitly.
3. Run `lake env lean notes/FrozenProofCheck.lean` and fix the actual errors. Recreate the wrapper
from the current proof after every edit; never rely on an earlier successful check or stale olean.
Only the driver's subsequent independent axiom audit, clean rebuild and emission gates establish
formal completion; this local check is feedback for your proof authoring session.
'''
    prompt = common + '\n' + task + '\nDriver feedback from prior attempt:\n' + (feedback or 'None yet.')
    stem = f'{phase}.{attempt:03d}'
    (ws/'attempts'/stem).mkdir(exist_ok=True)
    (ws/'attempts'/stem/'prompt.txt').write_text(prompt)
    readonly = tuple(str(ws/p) for p in ['inputs','SpecIR','SpecIR.lean','FrozenSpec.lean',
       'FrozenSpecBridge.lean','scripts','contracts','specs','assets','LeanRTL/Core','LeanRTL/Lib',
       'lakefile.toml','Main.lean','LeanRTL.lean','lean-toolchain','snapshots','frozen-run.json']
       if (ws/p).exists())
    role = agent.Role(tag='frozen-'+phase, tools=agent.FILE_TOOLS, allow=(str(ws),),
                      readonly=readonly, timeout=run['config']['agent_timeout'],
                      model=run['config']['model'])
    guard(ws, run)
    result = agent_backend.run(role, str(ws), prompt, str(ws/'attempts'/stem/'agent.jsonl'))
    write(ws/'attempts'/stem/'agent.json', result)
    guard(ws, run)
    return result


def emit(ws: Path, key: str, name: str) -> dict:
    candidate = ws/'out'/f'{key}.v'
    if candidate.exists():
        candidate.unlink()  # stale output cannot make a failed emission pass
    impl_sha = sha(ws/'frags'/key/'impl.lean')
    result = run_command(ws, [sys.executable, 'scripts/bbf.py', key, 'emit',
                            '--role', 'frozen-driver'], name)
    if result['ok'] and candidate.is_file():
        result.update(impl_sha256=impl_sha, verilog_sha256=sha(candidate))
        write(ws/'attempts'/name/'command.json', result)
    return result


def proof_check(ws: Path, run: dict, name: str, clean_build=False) -> dict:
    key = run['key']
    term = ws/'frags'/key/'equivalence.lean'
    if not term.exists():
        return {'ok': False, 'tail': 'Missing equivalence.lean proof term'}
    # Final validation discards every model-writable build cache and reconstructs all imports.
    if clean_build:
        shutil.rmtree(ws/'.lake/build', ignore_errors=True)
        rebuilt = run_command(ws, [stage.LAKE, 'build', 'LeanRTL', 'leanrtl', 'SpecIR',
                                   'FrozenSpec', 'FrozenSpecBridge'], name+'-clean-build', 3600)
        if not rebuilt['ok']:
            return rebuilt
    # Rebuild the actual implementation imported by the theorem, never a stale olean.
    prep = run_command(ws, [sys.executable, 'scripts/asm_f.py', key], name+'-assemble')
    if not prep['ok']:
        return prep
    prep = run_command(ws, [stage.LAKE, 'build', f'LeanRTL.Blind.{stage.camel_of(key)}'], name+'-impl')
    if not prep['ok']:
        return prep
    body = term.read_text()
    clean_impl = verify.check_sorry(str(ws), str(ws/'frags'/key/'impl.lean'))
    if not clean_impl['pass']:
        return {'ok': False, 'tail': str(clean_impl)}
    authored = body + (ws/'frags'/key/'impl.lean').read_text()
    sys.path.insert(0, str(Path(__file__).parent/'authoring'))
    from scan_sorry import strip_comments_and_strings
    bare = strip_comments_and_strings(authored)
    if re.search(r'\b(?:elab|macro|syntax|run_tac|unsafe)\b|debug\.skipKernelTC', bare):
        return {'ok': False, 'tail': 'Custom elaborators, macros, unsafe code and kernel bypasses are outside the frozen proof protocol'}
    if re.search(r'@\[[^\]]*\b(?:implemented_by|extern)\b', authored):
        return {'ok': False, 'tail': 'Native execution overrides are forbidden'}
    wrapper = ('import FrozenSpec\nimport FrozenSpecBridge\n'
               f'import LeanRTL.Blind.{stage.camel_of(key)}\n'
               'set_option maxHeartbeats 3200000\nset_option autoImplicit false\n'
               'theorem frozen_equivalence : FrozenSpecBridge.Equivalent SpecIR.Gen.spec '
               f'LeanRTL.Blind.{stage.camel_of(key)}.impl :=\n{body}\n'
               '')
    (ws/'FrozenProof.lean').write_text(wrapper)
    clean = verify.check_sorry(str(ws), str(ws/'FrozenProof.lean'))
    if not clean['pass']:
        return {'ok': False, 'tail': str(clean)}
    result = run_command(ws, [stage.LAKE, 'env', 'lean', '-o', 'FrozenProof.olean',
                             'FrozenProof.lean'], name)
    if result['ok']:
        (ws/'.lake/build/lib/lean').mkdir(parents=True, exist_ok=True)
        shutil.copy2(ws/'FrozenProof.olean', ws/'.lake/build/lib/lean/FrozenProof.olean')
        (ws/'FrozenAudit.lean').write_text('import FrozenProof\n#print axioms frozen_equivalence\n')
        audit = run_command(ws, [stage.LAKE, 'env', 'lean', 'FrozenAudit.lean'], name+'-audit')
        if not audit['ok']:
            return audit
        result['audit'] = audit
        output = Path(audit['log']).read_text()
        audit_lines = re.findall(r"^'frozen_equivalence' (?:depends on axioms: \[[^\]]*\]|does not depend on any axioms)\s*$", output, re.M)
        if len(audit_lines) != 1:
            return {**result, 'ok': False, 'tail': 'Missing or duplicate canonical theorem axiom audit'}
        match = re.search(r"'frozen_equivalence' depends on axioms: \[(.*?)\]", output, re.S)
        if match:
            axioms = [x.strip() for x in match.group(1).split(',') if x.strip()]
        elif "'frozen_equivalence' does not depend on any axioms" in output:
            axioms = []
        else:
            return {**result, 'ok': False, 'tail': 'Missing theorem axiom audit output: '+output}
        extras = [x for x in axioms if x not in verify.STD_AXIOMS]
        native_lrat = [x for x in extras if verify.NATIVE_LRAT.search(x)]
        unexpected = [x for x in extras if not verify.NATIVE_LRAT.search(x)]
        hijacks = []
        if native_lrat:
            for folder in ('LeanRTL', 'SpecIR'):
                for path in (ws/folder).rglob('*.lean'):
                    if verify._HIJACK.search(path.read_text()):
                        hijacks.append(str(path.relative_to(ws)))
            for filename in ('FrozenSpec.lean', 'FrozenSpecBridge.lean', 'FrozenProof.lean'):
                if verify._HIJACK.search((ws/filename).read_text()):
                    hijacks.append(filename)
        result.update(axioms=axioms, unexpected_axioms=unexpected, native_lrat=native_lrat,
                      native_override_hijacks=hijacks, kernel_only=not extras,
                      trusted_base='Lean kernel + standard axioms' +
                      (' + native LRAT execution (Lean compiler/runtime/C compiler)' if native_lrat else ''),
                      ok=not unexpected and not hijacks,
                      theorem='frozen_equivalence', proposition='FrozenSpecBridge.Equivalent',
                      olean_sha256=sha(ws/'FrozenProof.olean'),
                      impl_sha256=sha(ws/'frags'/key/'impl.lean'))
    return result


def diagnostic(ws: Path, run: dict, name: str) -> dict:
    key = run['key']
    prep = run_command(ws, [sys.executable, 'scripts/asm_f.py', key], name+'-assemble')
    if not prep['ok']:
        return prep
    prep = run_command(ws, [stage.LAKE, 'build', f'LeanRTL.Blind.{stage.camel_of(key)}'], name+'-build')
    if not prep['ok']:
        return prep
    # Compare typed output rows: stringifying Repr preserves widths and Val constructors.
    # Diagnostic only: the final gate is the unbounded theorem, never this finite suite.
    code = ('import FrozenSpec\nimport FrozenSpecBridge\n'
            f'import LeanRTL.Blind.{stage.camel_of(key)}\n'
            'def frozenDiagnostic : IO Unit := do\n'
            '  let mut failures := 0\n'
            '  for (stim, idx) in SpecIR.Gen.suite.zipIdx do\n'
            '    let expected := (SpecIR.Gen.spec.trace stim).map (fun r => r.outs)\n'
            f'    let actual := ((FrozenSpecBridge.design SpecIR.Gen.spec LeanRTL.Blind.{stage.camel_of(key)}.impl).trace stim).map (fun r => r.outs)\n'
            '    if reprStr expected != reprStr actual then\n'
            '      failures := failures + 1\n'
            '      IO.println s!"stimulus {idx}: expected {reprStr expected}; actual {reprStr actual}"\n'
            '  IO.println s!"FROZEN_SIMDIFF failures={failures} traces={SpecIR.Gen.suite.length}"\n'
            '#eval frozenDiagnostic\n')
    (ws/'FrozenDiagnostic.lean').write_text(code)
    return run_command(ws, [stage.LAKE, 'env', 'lean', 'FrozenDiagnostic.lean'], name)


def execute(ws: Path, run: dict, a) -> int:
    key = run['key']
    guard(ws, run)
    if not (ws/'attempts'/'setup'/'command.json').exists():
        build = run_command(ws, [stage.LAKE, 'build', 'LeanRTL', 'leanrtl', 'SpecIR',
                                 'FrozenSpec', 'FrozenSpecBridge'], 'setup', 3600)
        if not build['ok']:
            state(ws, 'input_build_failed', failure=build)
            return 1
    else:
        build = json.loads((ws/'attempts'/'setup'/'command.json').read_text())
        if not build['ok']:
            raise RuntimeError('initial frozen-input build failed; diagnose before resuming')
    if a.stage_only:
        state(ws, 'ready')
        return 0
    feedback = ''
    if not (ws/'snapshots'/'preproof'/'manifest.json').exists():
        completed = sorted((ws/'attempts').glob('impl.*-emit/command.json'))
        for record in completed:
            emitted = json.loads(record.read_text())
            if not emitted.get('ok') or not emitted.get('verilog_sha256'):
                continue
            if (not (ws/'out'/f'{key}.v').is_file() or
                sha(ws/'out'/f'{key}.v') != emitted['verilog_sha256'] or
                sha(ws/'frags'/key/'impl.lean') != emitted['impl_sha256']):
                raise RuntimeError('First successful emission awaits snapshot but candidate has changed')
            snapshot(ws, key, 'preproof', run)
            shutil.copy2(ws/'out'/f'{key}.v', ws/'out'/f'{key}.preproof.v')
            (ws/'out'/f'{key}.preproof.v').chmod(0o444)
            write(ws/'out'/f'{key}.preproof.json', dict(ok=True, faithful=True, stashed=False,
                  recovered=True, at=now(), impl_sha256=emitted['impl_sha256'],
                  verilog_sha256=emitted['verilog_sha256'], emission=emitted,
                  snapshot='snapshots/preproof/manifest.json'))
            state(ws, 'preproof_captured', preproof=True)
            break
    if not (ws/'snapshots'/'preproof'/'manifest.json').exists():
        for _ in range(a.attempts):
            n = len(list((ws/'attempts').glob('impl.[0-9][0-9][0-9]'))) + 1
            state(ws, 'implementation_running', impl_attempt=n)
            res = author(ws, run, 'impl', n, feedback)
            if res['rc'] != 0:
                state(ws, 'author_unavailable', failure=res)
                return 1
            forbidden = [ws/'frags'/key/x for x in ('proof.lean','equivalence.lean')]
            if any(p.exists() for p in forbidden):
                state(ws, 'protocol_violation', failure='functional proof fragment exists before preproof')
                return 1
            if not (ws/'frags'/key/'impl.lean').exists():
                if res['rc'] != 0:
                    state(ws, 'author_unavailable', failure=res)
                    return 1
                feedback = 'No impl.lean was produced. Agent result: '+json.dumps(res)
                continue
            emitted = emit(ws, key, f'impl.{n:03d}-emit')
            guard(ws, run)
            if emitted['ok'] and (ws/'out'/f'{key}.v').is_file():
                snapshot(ws, key, 'preproof', run)
                shutil.copy2(ws/'out'/f'{key}.v', ws/'out'/f'{key}.preproof.v')
                (ws/'out'/f'{key}.preproof.v').chmod(0o444)
                write(ws/'out'/f'{key}.preproof.json', dict(ok=True, faithful=True,
                      stashed=False, at=now(), impl_sha256=sha(ws/'frags'/key/'impl.lean'),
                      verilog_sha256=sha(ws/'out'/f'{key}.preproof.v'), emission=emitted,
                      snapshot='snapshots/preproof/manifest.json'))
                state(ws, 'preproof_captured', preproof=True)
                break
            feedback = emitted['tail']
        else:
            state(ws, 'implementation_incomplete', failure=feedback)
            return 1
    if a.preproof_only:
        return 0
    diag = diagnostic(ws, run, 'preproof-simdiff')
    write(ws/'simdiff/frozen.json', diag)
    feedback = 'Finite frozen-spec diagnostic (not a proof):\n' + diag['tail']
    recovering_final = False
    if (ws/'snapshots'/'final'/'manifest.json').exists():
        manifest = json.loads((ws/'snapshots/final/manifest.json').read_text())
        check_inventory(ws, manifest['files'])
        seal_path, proof_path = ws/'evaluation-ready.json', ws/'proof-result.json'
        if not seal_path.exists() or not proof_path.exists():
            recovering_final = True
            state(ws, 'final_seal_incomplete', failure='Revalidating archived final candidate to recover interrupted seal')
        else:
            seal, proved = json.loads(seal_path.read_text()), json.loads(proof_path.read_text())
            if not seal.get('ready') or not proved.get('complete_equivalence') or not proved.get('ok'):
                raise RuntimeError('Final snapshot has no accepted equivalence/seal')
            if proved.get('olean_sha256') != sha(ws/'FrozenProof.olean') or proved.get('impl_sha256') != sha(ws/'frags'/key/'impl.lean'):
                raise RuntimeError('Final proof object/implementation binding failed')
            if proved.get('final_snapshot_sha256') != sha(ws/'snapshots/final/manifest.json'):
                raise RuntimeError('Final snapshot binding failed')
            if seal.get('proof_result_sha256') != sha(proof_path) or seal.get('artifacts') != {
                    'preproof': sha(ws/'out'/f'{key}.preproof.v'), 'final': sha(ws/'out'/f'{key}.v')}:
                raise RuntimeError('Final proof/RTL seal binding failed')
            state(ws, 'formal_and_emission_complete', proof=True, final_emission=True,
                  final_verilog_sha256=seal['artifacts']['final'], evaluation='pending',
                  failure=None, resumed_from_verified_seal=True)
            return 0
    for _ in range(a.attempts):
        n = len(list((ws/'attempts').glob('proof.[0-9][0-9][0-9]'))) + 1
        state(ws, 'proof_running', proof_attempt=n)
        res = {'rc':0} if recovering_final else author(ws, run, 'proof', n, feedback)
        if res['rc'] != 0:
            state(ws, 'author_unavailable', failure=res)
            return 1
        diag = diagnostic(ws, run, f'proof.{n:03d}-simdiff')
        check = proof_check(ws, run, f'proof.{n:03d}-check')
        guard(ws, run)
        parameter_scope = run.get('parameter_scope', {'covers_all_declared_values':True})
        scope_complete = parameter_scope['covers_all_declared_values']
        write(ws/'proof-result.json', {**check, 'at': now(), 'attempt': n,
              'input_sha256': run['frozen_sha256'], 'instance_equivalence':check['ok'],
              'parameter_scope': parameter_scope, 'event_scope':run.get('event_scope'),
              'complete_equivalence': check['ok'] and scope_complete})
        if check['ok'] and not scope_complete:
            state(ws, 'spec_scope_unresolved', failure=parameter_scope['limitation'],
                  instance_equivalence=True, complete_equivalence=False)
            return 1
        if not check['ok']:
            feedback = check['tail']
            continue
        emitted = emit(ws, key, f'proof.{n:03d}-emit')
        if not emitted['ok']:
            feedback = emitted['tail']
            continue
        original = sha(ws/'out'/f'{key}.v')
        # A second proof check binds the final assembled object and requires no model edits.
        recheck = proof_check(ws, run, f'proof.{n:03d}-recheck', clean_build=True)
        repeated = emit(ws, key, f'proof.{n:03d}-reemit')
        guard(ws, run)
        if not recheck['ok'] or not repeated['ok'] or sha(ws/'out'/f'{key}.v') != original:
            feedback = json.dumps({'recheck':recheck,'reemission':repeated})
            continue
        src = (ws/'frags'/key/'impl.lean').read_text()
        clock = re.search(r'clock\s*:=\s*some\s*"([^"]+)"', src)
        flags = ['--seq', '--clock', clock.group(1)] if clock else []
        if re.search(r'clockNet\s*:=\s*some', src):
            flags += ['--multiclock']
        cosim = run_command(ws, [sys.executable, 'scripts/cosim.py',
                f'out/{key}.rtlil.json', f'out/{key}.v', '--key', key, '--strict-observations', *flags],
                f'proof.{n:03d}-cosim', 600)
        if not cosim['ok']:
            feedback = cosim['tail']
            continue
        undriven = verify.check_undriven(str(ws), key)
        if not undriven['pass']:
            feedback = json.dumps(undriven)
            continue
        if recovering_final:
            check_inventory(ws, json.loads((ws/'snapshots/final/manifest.json').read_text())['files'])
        else:
            snapshot(ws, key, 'final', run)
        write(ws/'proof-result.json', dict(**recheck, at=now(), attempt=n,
              input_sha256=run['frozen_sha256'], complete_equivalence=True,
              parameter_scope=run.get('parameter_scope'), event_scope=run.get('event_scope'),
              preproof_sha256=sha(ws/'out'/f'{key}.preproof.v'),
              final_verilog_sha256=original, final_snapshot_sha256=sha(ws/'snapshots/final/manifest.json'),
              emission=emitted, repeated_emission=repeated, undriven_nets=undriven, cosim=cosim,
              trustworthy_scope='Lean theorem over frozen SpecIR trace and actual Module; emission separately checked'))
        write(ws/'evaluation-ready.json', dict(ready=True, at=now(),
              artifacts={'preproof': sha(ws/'out'/f'{key}.preproof.v'), 'final': original},
              proof_result_sha256=sha(ws/'proof-result.json')))
        state(ws, 'formal_and_emission_complete', proof=True, final_emission=True,
              final_verilog_sha256=original, evaluation='pending')
        return 0
    state(ws, 'proof_incomplete', failure=feedback)
    return 1


def main(argv=None) -> int:
    ap = argparse.ArgumentParser(description=__doc__)
    ap.add_argument('--bench', required=True)
    ap.add_argument('--key', required=True)
    ap.add_argument('--input')
    ap.add_argument('--ws')
    ap.add_argument('--toplevel')
    ap.add_argument('--attempts', type=int, default=4)
    ap.add_argument('--agent-timeout', type=int, default=1800)
    ap.add_argument('--stage-only', action='store_true')
    ap.add_argument('--preproof-only', action='store_true')
    a = ap.parse_args(argv)
    os.environ.setdefault('LEANSILICON_AGENT_BACKEND', 'codex')
    os.environ['LEANSILICON_CODEX_MODEL'] = CORRECTION_MODEL
    expected_ws = Path(a.ws or Path(paths.DATA)/'part2'/a.bench/a.key/'decided').resolve()
    expected_ws.parent.mkdir(parents=True, exist_ok=True)
    with (expected_ws.parent/('.'+expected_ws.name+'.stage.lock')).open('a') as stage_lock:
        try:
            fcntl.flock(stage_lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
        except BlockingIOError:
            raise RuntimeError('staging or runner already live for this workspace')
        ws, run = stage_frozen(a)
        with (ws/'runner.lock').open('a') as lock:
            try:
                fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
            except BlockingIOError:
                raise RuntimeError('runner already live for this workspace')
            return execute(ws, run, a)


if __name__ == '__main__':
    sys.exit(main())
