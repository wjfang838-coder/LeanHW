"""Model-session backend selected explicitly for one experiment.

The historical runner is Claude Code.  Current managed environments can instead expose Codex while
leaving ``ANTHROPIC_BASE_URL`` unauthenticated.  Codex is run inside an outer bubblewrap namespace:
the repository is hidden, then only the stage-private root and the role's declared external grants
are mounted back.  Codex's own sandbox remains enabled as a second write/network boundary.
"""
from __future__ import annotations

import glob
import json
import os
from pathlib import Path
import shutil
import subprocess
import time

from common import agent

from .paths import REPO


def backend() -> str:
    value = os.environ.get("LEANSILICON_AGENT_BACKEND", "claude").strip().lower()
    if value not in {"claude", "codex"}:
        raise ValueError("LEANSILICON_AGENT_BACKEND must be claude or codex")
    return value


def codex_model(alias: str = "opus") -> str:
    explicit = os.environ.get("LEANSILICON_CODEX_MODEL")
    if explicit:
        return explicit
    mapped = {
        "opus": os.environ.get("ANTHROPIC_DEFAULT_OPUS_MODEL"),
        "sonnet": os.environ.get("ANTHROPIC_DEFAULT_SONNET_MODEL"),
        "haiku": os.environ.get("ANTHROPIC_DEFAULT_HAIKU_MODEL"),
    }.get(alias)
    return mapped or (alias if alias not in {"opus", "sonnet", "haiku"} else "gpt-5.6-sol")


def codex_profile() -> str:
    value = os.environ.get("LEANSILICON_CODEX_PROFILE", "default").strip().lower()
    if value not in {"default", "cp"}:
        raise ValueError("LEANSILICON_CODEX_PROFILE must be default or cp")
    return value


def _codex_source_home() -> str:
    explicit = os.environ.get("LEANSILICON_CODEX_HOME", "").strip()
    if explicit:
        return os.path.realpath(os.path.expanduser(explicit))
    name = ".codex-cp" if codex_profile() == "cp" else ".codex"
    return os.path.realpath(os.path.expanduser("~/" + name))


def _bwrap() -> str:
    found = shutil.which("bwrap")
    if found:
        return found
    launcher = shutil.which("codex")
    if not launcher:
        raise FileNotFoundError("codex CLI is not on PATH")
    package = os.path.dirname(os.path.dirname(os.path.realpath(launcher)))
    matches = glob.glob(os.path.join(
        package, "node_modules", "@openai", "codex-linux-*", "vendor", "*",
        "codex-resources", "bwrap"))
    if not matches:
        raise FileNotFoundError("Codex bubblewrap helper was not found")
    return sorted(matches)[0]


def _mount_args(role: agent.Role, root: str) -> list[str]:
    real_root = os.path.realpath(root)
    codex_home = _codex_source_home()
    auth = os.path.join(codex_home, "auth.json")
    config = os.path.join(codex_home, "config.toml")
    isolated_codex_home = "/tmp/leansilicon-codex-home"
    args = [
        _bwrap(), "--die-with-parent", "--new-session",
        "--ro-bind", "/", "/",
        "--tmpfs", "/tmp",
        "--tmpfs", "/home",
        "--tmpfs", "/root",
        # Hide every benchmark, reference, historical run and method note in one operation.
        "--tmpfs", os.path.realpath(REPO),
        # Recent Codex CLIs initialize an in-process app server even for ephemeral execs and must
        # create runtime files in CODEX_HOME.  The managed host can expose the real home as
        # read-only, so use this process's private /tmp and mount only the selected profile's
        # credential/config files into it.  No persistent session is needed.
        "--dir", isolated_codex_home,
        "--setenv", "CODEX_HOME", isolated_codex_home,
        "--bind", real_root, real_root,
    ]
    # Hide sibling repositories and user files as well as this repository. Restore
    # only installed language runtimes, then the role's explicit data grants.
    runtimes = {os.path.realpath(agent.ELAN)}
    node = shutil.which("node")
    if node:
        runtimes.add(str(Path(os.path.realpath(node)).parent.parent))
    for runtime in sorted(runtimes):
        if os.path.isdir(runtime) and runtime not in {"/", "/usr", "/usr/local"}:
            args += ["--ro-bind", runtime, runtime]
    if os.path.isfile(auth):
        args += ["--ro-bind", auth, isolated_codex_home + "/auth.json"]
    if codex_profile() == "cp":
        if not os.path.isfile(config):
            raise FileNotFoundError("codex-cp config.toml was not found")
        args += ["--ro-bind", config, isolated_codex_home + "/config.toml"]
    readonly = {os.path.realpath(path) for path in role.readonly}
    # ``root`` itself must remain writable because it is where the role emits its named outputs,
    # but a role can also carry immutable inputs *inside* that root.  The original Codex backend
    # only made externally granted paths read-only; an in-root ``spec.txt`` or harness directory
    # was protected only by an after-the-fact content snapshot.  Re-bind nested readonly inputs
    # after the writable root bind so the mount namespace enforces the freeze while the snapshot
    # still proves it.
    for real in sorted(readonly):
        try:
            nested = os.path.commonpath((real_root, real)) == real_root and real != real_root
        except ValueError:
            nested = False
        if nested and os.path.exists(real):
            args += ["--ro-bind", real, real]
    for path in role.allow:
        real = os.path.realpath(path)
        if real == real_root:
            continue
        mode = "--ro-bind" if real in readonly or os.path.isfile(real) else "--bind"
        args += [mode, real, real]
    args += ["--dev", "/dev", "--proc", "/proc", "--chdir", real_root]
    return args


def _codex_error(transcript: str, rc: int) -> str:
    """Return only an error that remains terminal in the JSONL event stream.

    Codex can emit a transient top-level ``error`` while reconnecting and later finish the turn.
    Treating any historical error as terminal discarded valid outputs and paid for a full repair
    session even though ``turn.completed`` was the final state.
    """
    error = ""
    try:
        with open(transcript, errors="replace") as stream:
            for line in stream:
                try:
                    event = json.loads(line)
                except ValueError:
                    continue
                if event.get("type") in {"turn.failed", "error"}:
                    error = str(event.get("error") or event.get("message") or event)[:300]
                elif event.get("type") == "turn.completed":
                    error = ""
    except OSError as exc:
        return "transcript unreadable: %s" % exc
    if error:
        return error
    return "codex exited %d" % rc if rc else ""


def run_codex(role: agent.Role, root: str, prompt: str, transcript: str,
              cwd: str | None = None, extra_env: dict | None = None) -> dict:
    """Run Codex with the same result contract as ``common.agent.run``."""
    del cwd  # bubblewrap fixes the only visible writable cwd to ``root``.
    os.makedirs(os.path.dirname(os.path.abspath(transcript)), exist_ok=True)
    agent._keep(transcript)
    model = codex_model(role.model)
    profile = codex_profile()
    cmd = _mount_args(role, root) + [
        "codex", "--ask-for-approval", "never", "exec",
        "--ephemeral", "--skip-git-repo-check",
    ]
    if profile == "default":
        cmd += ["--ignore-user-config"]
    cmd += [
        "--ignore-rules",
        "--disable", "multi_agent", "--sandbox", "workspace-write",
        "--model", model, "--json", prompt,
    ]
    env = dict(os.environ, **(extra_env or {}))
    if profile == "cp":
        env["CODEX_COPILOT_API_KEY"] = "dummy"
        for name in ("NO_PROXY", "no_proxy"):
            current = env.get(name, "")
            local = "127.0.0.1,localhost,::1"
            env[name] = current + ("," if current else "") + local
    started = time.time()
    errfile = os.path.splitext(transcript)[0] + ".stderr"
    try:
        with open(transcript, "w") as output, open(errfile, "w") as errors:
            output.write(json.dumps({"type": "system", "subtype": "init", "model": model}) +
                         "\n")
            output.flush()
            process = subprocess.Popen(cmd, stdout=output, stderr=errors, stdin=subprocess.DEVNULL,
                                       text=True, env=env)
            rc, how = agent._supervise(process, transcript, role.timeout, started)
    except FileNotFoundError as exc:
        rc, how = -2, "no-cli"
        with open(errfile, "a") as errors:
            errors.write(str(exc))
    session_error = _codex_error(transcript, rc)
    return {
        "role": role.tag, "rc": rc, "how": how,
        "stderr": agent._tail(errfile), "elapsed": round(time.time() - started, 1),
        "transcript": os.path.abspath(transcript), "session_error": session_error,
        "denied": agent.denied_calls(transcript), "refusals": agent.refusals(transcript),
        "execution": {
            "backend": "codex", "profile": profile, "model": model,
            "outer_isolation": "repository-hidden-stage-root-only",
            "inner_sandbox": "workspace-write", "approval_policy": "never",
            "ephemeral": True, "user_config": profile == "cp", "project_rules": False,
            # Codex exposes shell/apply-patch tools; the outer namespace, rather than a prompt,
            # enforces which design data those tools can reach.
            "tool_surface": ["shell", "apply_patch"],
        },
    }


def run(role: agent.Role, root: str, prompt: str, transcript: str,
        cwd: str | None = None, extra_env: dict | None = None) -> dict:
    if backend() == "codex":
        return run_codex(role, root, prompt, transcript, cwd=cwd, extra_env=extra_env)
    if extra_env is None:
        return agent.run(role, root, prompt, transcript, cwd=cwd)
    return agent.run(role, root, prompt, transcript, cwd=cwd, extra_env=extra_env)


def identity(selected: str | None = None) -> dict:
    chosen = selected or backend()
    if chosen == "codex":
        command = ["codex", "--version"]
        model = codex_model()
    elif chosen == "claude":
        command = ["claude", "--version"]
        model = None
    else:
        return {"ok": False, "backend": chosen, "error": "unsupported agent backend"}
    try:
        env = dict(os.environ)
        if chosen == "codex" and codex_profile() == "cp":
            env.update({"CODEX_HOME": _codex_source_home(), "CODEX_COPILOT_API_KEY": "dummy"})
        proc = subprocess.run(command, text=True, capture_output=True, timeout=30, env=env)
        value = {"ok": proc.returncode == 0, "backend": chosen, "rc": proc.returncode,
                 # Startup warnings depend on the caller's filesystem sandbox and are not part of
                 # the executable identity.  Hash the version printed on stdout, not incidental
                 # stderr such as a failed best-effort PATH-alias update.
                 "output": proc.stdout.strip()[:1200]}
        if proc.returncode and proc.stderr.strip():
            value["error"] = proc.stderr.strip()[:1200]
    except (OSError, subprocess.TimeoutExpired) as exc:
        value = {"ok": False, "backend": chosen,
                 "error": "%s: %s" % (type(exc).__name__, exc)}
    if model:
        value["model"] = model
    return value
