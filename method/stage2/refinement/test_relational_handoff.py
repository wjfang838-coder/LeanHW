"""Regression checks for the source-bound Stage 1 → Stage 2 handoff."""
from pathlib import Path
import pytest
import refinement_checks as checks


def workspace(tmp_path):
    for name in ('FrozenSpec.lean', 'Imported.lean', 'FrozenRefinement.lean',
                 'FrozenContract.lean', 'Rewrite.lean', 'proof.term',
                 'lean-toolchain', 'lakefile.toml'):
        (tmp_path / name).write_text('fixture')
    return tmp_path


def test_cold_replay_carries_original_relation_and_handoff_target(tmp_path):
    ws = workspace(tmp_path)
    for name in ('Partial.lean', 'DecidedSpec.lean', 'HandoffContract.lean', 'handoff.term'):
        (ws / name).write_text(name)
    (ws / 'LeanSpec').mkdir()
    (ws / 'LeanSpec/Handoff.lean').write_text('library')
    manifest = checks.source_manifest(ws)
    checks.copy_sources(ws, ws / 'copy', manifest)
    for name in ('Partial.lean', 'DecidedSpec.lean', 'HandoffContract.lean',
                 'handoff.term', 'LeanSpec/Handoff.lean'):
        assert (ws / 'copy' / name).read_bytes() == (ws / name).read_bytes()
    before = manifest['Partial.lean']
    (ws / 'Partial.lean').write_text('changed relation')
    assert checks.source_manifest(ws)['Partial.lean'] != before


def test_missing_handoff_proof_cannot_pass(tmp_path):
    ws = workspace(tmp_path)
    (ws / 'HandoffContract.lean').write_text('def Exact : Prop := True')
    result = checks.check(ws, ws / 'log')
    assert not result['ok']
    assert 'requires handoff.term' in result['tail']


def test_handoff_axioms_are_not_ignored():
    with pytest.raises(ValueError, match='handoff_exact'):
        checks.parse_axioms('', ('handoff_exact',))
    assert not checks.axiom_policy({'handoff_exact': ['sorryAx']}, Path('.'))['ok']
