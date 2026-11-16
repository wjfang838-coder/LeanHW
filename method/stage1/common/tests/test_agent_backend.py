import json
from pathlib import Path
from types import SimpleNamespace

import pytest

from common.agent import Role
from common.paths import REPO
from common import agent_backend


def test_backend_is_explicit_and_rejects_unknown_values(monkeypatch):
    monkeypatch.setenv("LEANSILICON_AGENT_BACKEND", "codex")
    assert agent_backend.backend() == "codex"
    monkeypatch.setenv("LEANSILICON_AGENT_BACKEND", "mystery")
    with pytest.raises(ValueError, match="claude or codex"):
        agent_backend.backend()


def test_codex_model_freezes_the_resolved_alias(monkeypatch):
    monkeypatch.delenv("LEANSILICON_CODEX_MODEL", raising=False)
    monkeypatch.setenv("ANTHROPIC_DEFAULT_OPUS_MODEL", "gpt-fixture")
    assert agent_backend.codex_model("opus") == "gpt-fixture"
    monkeypatch.setenv("LEANSILICON_CODEX_MODEL", "gpt-explicit")
    assert agent_backend.codex_model("opus") == "gpt-explicit"


def test_codex_namespace_hides_repo_and_mounts_only_declared_grants(tmp_path, monkeypatch):
    root = tmp_path / "stage"
    root.mkdir()
    toolkit = tmp_path / "Machine.lean"
    toolkit.write_text("structure Machine")
    role = Role(tag="fixture", tools=("Read",), allow=(str(root), str(toolkit)),
                readonly=(str(toolkit),), inputs=(str(toolkit),))
    monkeypatch.setattr(agent_backend, "_bwrap", lambda: "/test/bwrap")

    args = agent_backend._mount_args(role, str(root))

    hidden = {args[i + 1] for i, arg in enumerate(args) if arg == "--tmpfs"}
    assert {"/tmp", "/home", "/root", str(Path(REPO).resolve())} <= hidden
    triples = [args[index:index + 3] for index, value in enumerate(args) if value == "--bind"]
    assert ["--bind", str(root.resolve()), str(root.resolve())] in triples
    readonly = [args[index:index + 3] for index, value in enumerate(args) if value == "--ro-bind"]
    assert ["--ro-bind", str(toolkit.resolve()), str(toolkit.resolve())] in readonly


def test_codex_namespace_rebinds_nested_inputs_readonly(tmp_path, monkeypatch):
    root = tmp_path / "stage"
    inputs = root / "inputs"
    inputs.mkdir(parents=True)
    (inputs / "spec.txt").write_text("immutable")
    role = Role(tag="fixture", tools=("Read",), allow=(str(root),),
                readonly=(str(inputs),), inputs=(str(inputs),))
    monkeypatch.setattr(agent_backend, "_bwrap", lambda: "/test/bwrap")

    args = agent_backend._mount_args(role, str(root))

    triples = [args[index:index + 3] for index, value in enumerate(args) if value == "--ro-bind"]
    assert ["--ro-bind", str(inputs.resolve()), str(inputs.resolve())] in triples


def test_codex_cp_profile_mounts_only_its_config(tmp_path, monkeypatch):
    root = tmp_path / "stage"
    root.mkdir()
    profile = tmp_path / ".codex-cp"
    profile.mkdir()
    config = profile / "config.toml"
    config.write_text('model_provider = "copilot"')
    role = Role(tag="fixture", tools=("Read",), allow=(str(root),))
    monkeypatch.setenv("LEANSILICON_CODEX_PROFILE", "cp")
    monkeypatch.setattr(agent_backend, "_codex_source_home", lambda: str(profile))
    monkeypatch.setattr(agent_backend, "_bwrap", lambda: "/test/bwrap")

    args = agent_backend._mount_args(role, str(root))

    assert ["--ro-bind", str(config), "/tmp/leansilicon-codex-home/config.toml"] in [
        args[index:index + 3] for index, value in enumerate(args) if value == "--ro-bind"]


def test_codex_home_can_be_pinned_for_reproducible_provider_config(tmp_path, monkeypatch):
    configured = tmp_path / "codex-provider"
    monkeypatch.setenv("LEANSILICON_CODEX_HOME", str(configured))

    assert agent_backend._codex_source_home() == str(configured.resolve())


def test_agent_identity_ignores_environment_dependent_stderr(monkeypatch):
    monkeypatch.setattr(agent_backend.subprocess, "run", lambda *_args, **_kwargs:
                        SimpleNamespace(returncode=0, stdout="codex-cli 1.2.3\n",
                                        stderr="warning: sandbox detail\n"))
    monkeypatch.setenv("LEANSILICON_CODEX_MODEL", "gpt-fixture")

    got = agent_backend.identity("codex")

    assert got == {"ok": True, "backend": "codex", "rc": 0,
                   "output": "codex-cli 1.2.3", "model": "gpt-fixture"}


def test_completed_codex_turn_supersedes_a_transient_reconnect_error(tmp_path):
    transcript = tmp_path / "session.jsonl"
    transcript.write_text("\n".join([
        json.dumps({"type": "error", "message": "Reconnecting... tls handshake eof"}),
        json.dumps({"type": "turn.completed", "usage": {"input_tokens": 10}}),
    ]))

    assert agent_backend._codex_error(str(transcript), 0) == ""


def test_codex_error_remains_terminal_without_later_completion(tmp_path):
    transcript = tmp_path / "session.jsonl"
    transcript.write_text("\n".join([
        json.dumps({"type": "turn.completed", "usage": {}}),
        json.dumps({"type": "error", "message": "terminal transport failure"}),
    ]))

    assert agent_backend._codex_error(str(transcript), 0) == "terminal transport failure"


def test_first_external_grant_is_not_skipped(tmp_path, monkeypatch):
    root = tmp_path / "stage"
    root.mkdir()
    library = tmp_path / "library"
    library.mkdir()
    monkeypatch.setattr(agent_backend, "_bwrap", lambda: "/test/bwrap")
    role = Role(tag="spec-author", tools=("Read",), allow=(str(library),))
    args = agent_backend._mount_args(role, str(root))
    assert ["--bind", str(library), str(library)] in [
        args[i:i + 3] for i, value in enumerate(args) if value == "--bind"]
