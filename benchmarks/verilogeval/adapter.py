#!/usr/bin/env python3
"""VerilogEval: 156 problems, each shipping a prompt, a reference and a checker.

Installed data, not method — this file lives under `benchmarks/`, which is gitignored, and the
dataset itself is a symlink to a checkout outside both.  Nothing here may look at how the
Verilog it grades was produced.

## Layout

    <dataset>/<stem>_prompt.txt   the task, in prose        -- the ONLY thing an author may read
    <dataset>/<stem>_ref.sv       `module RefModule`        -- the golden design
    <dataset>/<stem>_test.sv      `module tb`               -- instantiates BOTH and compares

A candidate is one file defining `TopModule`.  The checker samples every clock edge, counts the
edges on which the two disagree, and prints its own verdict line:

    Mismatches: 0 in 100 samples

Note that `key != toplevel` on all 156 problems — the key is `Prob067_countslow` and the module
the checker instantiates is `TopModule`.  That is the first benchmark here where the two differ,
and `leanrtl/launch.py` reads `Design.toplevel` rather than defaulting to the key because of it.

## The oracle

Icarus Verilog, locally, and it is stamped into every verdict rather than left implicit.  Unlike
RTLLM this is not a stand-in for something better: VerilogEval's own harness runs Icarus, all 156
checkers elaborate under it, and the golden control below runs under the same simulator that
judges the arms.  A verdict that does not name its simulator reads as a fact about the design and
gets carried across a toolchain change that invalidates it.

## Provenance

The checkout is byte-identical to `NVlabs/verilog-eval@main`, all 471 files of
`dataset_spec-to-rtl`, verified by fetching upstream and diffing the directory rather than by
trusting where the copy came from.  That check was worth running: the copy this was taken from
sat inside a directory its parent project gitignores, so `git log` there walked up to the parent
repository and answered about the wrong tree — there was no commit to quote and no way to tell an
edited prompt from an original one by inspection.

The one file that differed was a stray `wave.vcd`, which is the artifact described below: a
previous scorer ran `vvp` with `cwd=<dataset>` and left a waveform in somebody else's checkout.
It has been moved out of the dataset directory, and `dataset_id()` would not have hashed it
anyway.  Nothing else in the corpus had been touched.

## Scoring runs in a private directory

All 156 checkers `$dumpfile("wave.vcd")`.  A scorer that ran them with `cwd=<dataset>` — one did —
writes a waveform into somebody else's checkout on every design, each run clobbering the last, and
two designs scored at the same time write the same file at the same time.  The candidate is copied
into a temporary directory and the run happens there, which is also what makes `score_all` safe to
overlap.

## The golden control

`golden_source` renames `RefModule` to `TopModule` in a copy of the reference, so the benchmark's
own golden design can be pushed through the candidate slot of the benchmark's own checker.  Every
`_ref.sv` declares exactly one module and every one is called `RefModule`, so the rename is a
single unambiguous substitution and no submodule can be caught by it.

This is what makes `known_defects()` falsifiable rather than folklore: a design whose own reference
does not pass its own checker is excluded from a denominator by evidence.  Note what the control
does NOT establish — `TopModule` compared against `RefModule` where both are the same source is a
tautology on the comparison, but not on elaboration, stimulus or timing, which is where the
failures turn out to be.

## No `KNOWN_DEFECTS.json` ships with this adapter

The previous repository's copy carried one.  Those entries are the *result* of running that
control there, under that Icarus, on that checkout — a measurement, not benchmark metadata — and
importing a measurement is how a new repository inherits an old conclusion without re-earning it.
`known_defects()` returns `{}` until the control is run here and the file is written from what it
found.
"""
from __future__ import annotations

import concurrent.futures
import glob
import hashlib
import os
import re
import subprocess
import tempfile

try:
    from _adapter import Adapter, Design, Verdict
except ModuleNotFoundError:                    # direct execution, e.g. the self-check at the foot
    # `common.adapter.load` binds itself as `_adapter` before running this file, so the import
    # above is the normal path and this one only fires when nobody called `load` — running this
    # file as a script with `method/` on PYTHONPATH.  It resolves to the SAME module object, not
    # a copy, so the classes are the ones every other adapter implements.
    from common.adapter import Adapter, Design, Verdict          # noqa: E402

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.environ.get("VEVAL_ROOT", os.path.join(HERE, "dataset"))

# "Mismatches: 0 in 100 samples" -- the count that decides the verdict is the first number.
_MISMATCH = re.compile(r"mismatches\s*:\s*(\d+)\s+in\s+(\d+)", re.I)
# "Hint: Output 'out' has 12 mismatches. First mismatch occurred at time 45."
_PER_OUT = re.compile(r"Output\s+'([^']+)'\s+has\s+(\d+)\s+mismatch", re.I)


def _camel(key: str) -> str:
    return "".join(w[:1].upper() + w[1:] for w in re.split(r"[_\-.]", key) if w)


class VerilogEval(Adapter):
    name = "verilogeval"
    oracle = "icarus"

    # -- the design set ----------------------------------------------------------

    def designs(self) -> list[Design]:
        # An absent dataset must not read as "this benchmark has no designs" -- the trap RTLLM
        # fell into, where a fresh clone scored 0/0 and exited 0.
        if not os.path.isdir(ROOT):
            raise FileNotFoundError(
                f"verilogeval: dataset not found at {ROOT}.\n"
                f"  The benchmark checkout is external data and is not vendored.\n"
                f"  Point VEVAL_ROOT at a `dataset_spec-to-rtl` directory, or fix the\n"
                f"  `dataset` symlink beside this file.\n"
                f"  Expected layout: <root>/<stem>_{{prompt.txt,ref.sv,test.sv}}")
        out = []
        for p in sorted(glob.glob(os.path.join(ROOT, "*_prompt.txt"))):
            stem = os.path.basename(p)[: -len("_prompt.txt")]
            ref = os.path.join(ROOT, stem + "_ref.sv")
            tb = os.path.join(ROOT, stem + "_test.sv")
            out.append(Design(
                key=stem, bench=self.name, spec_path=p,
                # Every problem's candidate module is `TopModule`; the prompt says so in its
                # first sentence.  It is NOT the key, and taking the key would emit a module the
                # checker cannot find -- which arrives as `compile_fail` and reads as a hardware
                # error rather than as a naming mistake.
                toplevel="TopModule", camel=_camel(stem),
                meta={"ref": ref, "tb": tb,
                      "has_ref": os.path.isfile(ref), "has_tb": os.path.isfile(tb)}))
        return out

    def dataset_id(self) -> dict:
        """Hash the exact bytes being graded: prompt, reference and checker of every problem.

        Per design as well as overall.  The checkout has no version control of its own, so this
        hash — not a path and not a commit — is the statement of *which* VerilogEval this is.  See
        the provenance note above for what it was checked against once, by hand; this is what
        makes a later drift visible without repeating that check.
        """
        h = hashlib.sha256()
        per = {}
        for d in self.designs():
            dh = hashlib.sha256()
            sources = (("prompt/" + os.path.basename(d.spec_path), d.spec_path),
                       ("reference/" + os.path.basename(d.meta["ref"]), d.meta["ref"]),
                       ("checker/" + os.path.basename(d.meta["tb"]), d.meta["tb"]))
            files = []
            for logical, path in sources:
                data = open(path, "rb").read() if os.path.isfile(path) else None
                digest = hashlib.sha256(data).hexdigest() if data is not None else None
                dh.update(logical.encode())
                dh.update(b"\0")
                dh.update(data if data is not None else b"<missing>")
                dh.update(b"\0")
                files.append({"name": logical, "sha256": digest})
            per[d.key] = {
                "sha256": dh.hexdigest(), "files": files,
                "scorer_files": [logical for logical, _path in sources
                                 if logical.startswith(("reference/", "checker/"))],
            }
            h.update(d.key.encode())
            h.update(b"\0")
            h.update(dh.digest())
        return {"bench": self.name, "root": os.path.realpath(ROOT), "designs": len(per),
                "reference_available": True,
                "sha256": h.hexdigest(), "oracle": self.oracle, "per_design": per}

    def stage(self, design: Design, ws: str) -> None:
        """Copy ONLY the prompt.

        The reference and the checker sit in the same directory under adjacent filenames, and
        neither may ever follow the prompt into a workspace.
        """
        dst = os.path.join(ws, "specs", f"{design.key}.spec.txt")
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(design.spec_path, errors="replace") as f:
            open(dst, "w").write(f.read())

    # -- the golden control ------------------------------------------------------

    def golden_source(self, design: Design) -> str | None:
        """The benchmark's own reference, rebound to the candidate slot.

        The checker instantiates `RefModule` and `TopModule` and compares them, and compiles the
        real `_ref.sv` alongside whatever occupies the candidate slot -- so the copy must be
        renamed or the two definitions collide.  `count=1` on the module DECLARATION only: an
        instantiation of `RefModule` inside the file (there are none today) is not a declaration
        and must not be rewritten into a self-instantiation.
        """
        ref = design.meta["ref"]
        if not os.path.isfile(ref):
            return None
        src = open(ref, errors="replace").read()
        new, n = re.subn(r"^([ \t]*module[ \t]+)RefModule\b", r"\1TopModule", src,
                         count=1, flags=re.M)
        if n != 1:
            return None          # not the shape this control assumes; say so by declining
        return new

    # -- scoring -----------------------------------------------------------------

    def score(self, design: Design, vpath: str) -> Verdict:
        v = Verdict(key=design.key, oracle=self.oracle)
        try:
            return self._score(design, vpath, v)
        except Exception as e:                                   # score must be total
            v.status, v.detail = "harness_error", f"{type(e).__name__}: {e}"
            return v

    def _score(self, design: Design, vpath: str, v: Verdict) -> Verdict:
        if not (design.meta["has_tb"] and design.meta["has_ref"]):
            v.status, v.detail = "harness_error", "benchmark ships no test or no reference"
            return v
        # Read each oracle input once, hash those exact bytes, then execute copies of those
        # same bytes.  Besides closing a small TOCTOU window, this makes the score/control and
        # golden-apparatus arms auditable against dataset_id()["per_design"].
        ref_name = "reference/" + os.path.basename(design.meta["ref"])
        tb_name = "checker/" + os.path.basename(design.meta["tb"])
        ref_raw = open(design.meta["ref"], "rb").read()
        tb_raw = open(design.meta["tb"], "rb").read()
        scorer_inputs = [
            {"name": ref_name, "sha256": hashlib.sha256(ref_raw).hexdigest()},
            {"name": tb_name, "sha256": hashlib.sha256(tb_raw).hexdigest()},
        ]
        v.extra["dataset_inputs"] = list(scorer_inputs)
        v.extra["score_inputs"] = list(scorer_inputs)
        if not os.path.isfile(vpath):
            v.status, v.detail = "not_emitted", f"no {vpath}"
            return v
        with tempfile.TemporaryDirectory(prefix=f"veval-{design.key}-") as wd:
            cand = os.path.join(wd, "cand.sv")
            ref = os.path.join(wd, "ref.sv")
            tb = os.path.join(wd, "test.sv")
            open(cand, "w").write(open(vpath, errors="replace").read())
            open(ref, "wb").write(ref_raw)
            open(tb, "wb").write(tb_raw)
            sim = os.path.join(wd, "sim")
            c = subprocess.run(["iverilog", "-g2012", "-o", sim, tb, ref, cand],
                               capture_output=True, text=True, timeout=300)
            if c.returncode != 0:
                v.status, v.detail = "compile_fail", (c.stderr + c.stdout).strip()[-700:]
                return v
            v.syntax_pass = True
            try:
                r = subprocess.run(["vvp", sim], cwd=wd, capture_output=True,
                                   text=True, timeout=180)
            except subprocess.TimeoutExpired:
                v.status, v.detail = "timeout", "vvp did not return within 180 s"
                return v
        return self._read(r.stdout + r.stderr, v)

    @staticmethod
    def _read(out: str, v: Verdict) -> Verdict:
        """Adjudicate from the checker's own words.

        `TIMEOUT` is not folded into the mismatch count, and this matters in the direction that
        would otherwise manufacture passes.  The checker's timeout calls `$finish`, which runs
        the `final` block, which prints `Mismatches: <n> in <m> samples` -- so a design that hung
        on sample 3 of 100 still prints a mismatch line, and if it happened to agree on those
        three samples the line reads `Mismatches: 0`.  Counting that as a pass would be counting
        a truncated sample as a complete one.
        """
        m = _MISMATCH.search(out)
        v.mismatch_outputs = [{"out": g.group(1), "n": int(g.group(2))}
                              for g in _PER_OUT.finditer(out)]
        if "TIMEOUT" in out:
            v.status, v.detail = "timeout", out.strip()[-700:]
            if m:
                v.extra["mismatches_at_timeout"] = int(m.group(1))
                v.extra["samples_at_timeout"] = int(m.group(2))
            return v
        if m:
            n, total = int(m.group(1)), int(m.group(2))
            v.extra["mismatches"], v.extra["samples"] = n, total
            # A checker that reached its verdict line having sampled nothing has not passed.
            if total == 0:
                v.status, v.detail = "no_verdict", "checker reported 0 samples"
                return v
            v.func_pass = n == 0
            v.status = "func_pass" if v.func_pass else "func_fail"
            if not v.func_pass:
                v.detail = out.strip()[-700:]
            return v
        low = out.lower()
        v.status = "sim_error" if ("error" in low or "syntax" in low) else "no_verdict"
        v.detail = out.strip()[-700:]
        return v

    def score_all(self, items, workers: int = 1) -> dict:
        """Judge many designs.  Each runs in its own temporary directory and touches nothing
        outside it, so they are independent; a lane of 156 local simulations is worth
        overlapping."""
        if workers <= 1 or len(items) <= 1:
            return {d.key: self.score(d, p) for d, p in items}
        out = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
            futs = {ex.submit(self.score, d, p): d.key for d, p in items}
            for f in concurrent.futures.as_completed(futs):
                out[futs[f]] = f.result()
        return out


def adapter() -> Adapter:
    return VerilogEval()


if __name__ == "__main__":
    import sys
    a = adapter()
    ds = a.designs()
    ident = a.dataset_id()
    print(f"verilogeval: {len(ds)} designs, oracle {a.oracle}")
    print(f"  {ident['sha256']}  {ident['root']}")
    if "-v" in sys.argv:
        for d in ds:
            flags = ("" if d.meta["has_ref"] else " NO-REF") + ("" if d.meta["has_tb"]
                                                                else " NO-TB")
            print(f"  {d.key:34} {d.toplevel:12} {d.camel}{flags}")
