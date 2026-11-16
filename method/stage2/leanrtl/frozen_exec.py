"""Offline mount isolation for trusted drivers that compile untrusted authored Lean.

Author sessions and compiler invocations are distinct trust boundaries: Lean `#eval`
executes during a build, so the compiler must not inherit the repository, home secrets,
other runs, network, or parent-process filesystem view. No unsandboxed fallback exists.
"""
from __future__ import annotations

import glob
import json
from pathlib import Path
import os
import shutil
import sys

REPO = Path(__file__).resolve().parents[3]


def bubblewrap() -> str:
    found = shutil.which("bwrap")
    if found:
        return found
    launcher = shutil.which("codex")
    if not launcher:
        raise FileNotFoundError("bubblewrap is required for frozen compiler execution")
    package = Path(launcher).resolve().parent.parent
    matches = sorted(glob.glob(str(package / "node_modules/@openai/codex-linux-*/vendor/*/codex-resources/bwrap")))
    if not matches:
        raise FileNotFoundError("No bubblewrap binary found; refusing unsandboxed compiler execution")
    return matches[0]


def command_prefix(workspace: Path | str, *, readonly=()) -> list[str]:
    ws = Path(workspace).resolve(strict=True)
    if not ws.is_dir() or ws == REPO or ws == Path.home():
        raise ValueError("A dedicated workspace directory is required")
    home = Path.home().resolve()
    elan = home / ".elan"
    if not elan.is_dir():
        raise FileNotFoundError("Installed offline Lean toolchain is required")
    namespaces = ["--unshare-pid", "--unshare-ipc", "--unshare-uts"]
    # Codex already supplies a network-restricted outer sandbox.  Creating a
    # second network namespace there can fail at loopback setup because the
    # outer sandbox intentionally withholds NETLINK_ROUTE.  Keep bubblewrap's
    # filesystem/process isolation and omit only the redundant network layer
    # when the caller explicitly attests that outer restriction.
    if os.environ.get("LEANSILICON_OUTER_NETWORK_SANDBOX") != "1":
        namespaces.insert(0, "--unshare-net")
    args = [bubblewrap(), "--die-with-parent", "--new-session", *namespaces,
            "--ro-bind", "/", "/", "--tmpfs", "/tmp", "--tmpfs", str(home)]
    # REPO may live outside HOME in another installation.
    if not REPO.is_relative_to(home):
        args += ["--tmpfs", str(REPO)]
    args += ["--ro-bind", str(elan), str(elan), "--bind", str(ws), str(ws)]
    frozen_run = ws / "frozen-run.json"
    protected = {Path(p).resolve() for p in readonly}
    if frozen_run.is_file():
        run = json.loads(frozen_run.read_text())
        protected.update(ws / rel for rel in run.get("immutable", {}))
        protected.add(frozen_run)
    for path in sorted(protected):
        if not path.is_relative_to(ws) or path == ws:
            raise ValueError(f"Read-only binding must belong to workspace: {path}")
        if path.is_symlink():
            raise ValueError(f"Symlink is not a frozen compiler input: {path}")
        if path.exists():
            args += ["--ro-bind", str(path), str(path)]
    safe_path = ":".join(dict.fromkeys([
        str(Path(sys.executable).parent), str(elan / "bin"),
        "/usr/local/sbin", "/usr/local/bin", "/usr/sbin", "/usr/bin", "/sbin", "/bin"]))
    args += ["--dev", "/dev", "--proc", "/proc", "--clearenv",
             "--setenv", "HOME", str(home), "--setenv", "ELAN_HOME", str(elan),
             "--setenv", "PATH", safe_path, "--setenv", "LANG", "C.UTF-8",
             "--setenv", "TMPDIR", "/tmp", "--setenv", "PYTHONDONTWRITEBYTECODE", "1",
             "--chdir", str(ws), "--"]
    return args
