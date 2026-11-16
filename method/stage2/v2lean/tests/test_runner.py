import json
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest

from v2lean.pipeline import run


class RunnerTests(unittest.TestCase):
    def test_timeout_stops_descendant_evaluator(self):
        with tempfile.TemporaryDirectory(prefix="v2lean-timeout-") as directory:
            wd = Path(directory)
            script = ("import subprocess, sys, time; from pathlib import Path; "
                      "p = subprocess.Popen([sys.executable, '-c', 'import time; time.sleep(30)']); "
                      "Path('child.pid').write_text(str(p.pid)); time.sleep(30)")
            with self.assertRaises(subprocess.TimeoutExpired):
                run([sys.executable, "-c", script], wd, wd / "run.log", timeout=1)
            pid = int((wd / "child.pid").read_text())
            status = Path(f"/proc/{pid}/status")
            # A killed orphan may briefly remain a zombie until the container
            # init reaps it; it must not remain a running/sleeping evaluator.
            if status.exists():
                self.assertIn("State:\tZ", status.read_text())
            metadata = json.loads((wd / "run.log.command.json").read_text())
            self.assertEqual(metadata["status"], "timeout")
