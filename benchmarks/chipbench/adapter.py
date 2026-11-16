#!/usr/bin/env python3
"""ChipBench (Verilog Gen): 45 spec-to-RTL problems across three subsets, judged by Icarus.

Installed data, not method — this file lives under `benchmarks/`, which is gitignored, and the
dataset itself is a symlink to a checkout outside both.  Nothing here may look at how the Verilog
it grades was produced.

## Layout

ChipBench's `Verilog Gen/` is VerilogEval's file shape, three times over:

    <subset>/<stem>_prompt.txt   the task, in prose      -- the ONLY thing an author may read
    <subset>/<stem>_ref.sv       `module RefModule`      -- the golden design
    <subset>/<stem>_test.sv      `module tb`             -- instantiates BOTH and compares

with `<subset>` one of `dataset_self_contain` (30), `dataset_not_self_contain` (6) and
`dataset_cpu_ip` (9).  All 45 stems are distinct, all 45 references declare `RefModule`, all 45
testbenches declare `tb` and instantiate `TopModule`, so the key is the stem and the subset is
metadata.  The subset is carried in `meta` and in every `Verdict.extra` regardless: the three are
not one population, and a pass rate quoted over the union without saying so is three numbers
averaged by accident.

The three subsets are NOT enumerated from the `problems.txt` sitting in each of them.  Those files
are leftovers of a partial run: `dataset_not_self_contain/problems.txt` names one task of the six
and `dataset_cpu_ip/problems.txt` names one of the nine.  Reading them would have posed 32 of the
45 problems and reported a full sweep.

## 20 of the 45 prompts carry a `Clarification:` paragraph, and it is upstream's

This matters to Part 1 and not to Part 2.  A `Clarification:` paragraph is the dataset author
pre-answering the question leanSpec exists to find, so on those 20 designs the spec-check phase has
less material and will report fewer findings — a property of the corpus, not of the method.  It was
checked rather than assumed: the checkout has a single commit `b4ba3a0` by Chenyang Zhou against
`github.com/zhongkaiyu/ChipBench`, message "Consolidate fixed self-contained prompts", so the
paragraphs predate this repository and no prompt here has been edited by us.

Any comparison of finding counts between this benchmark and another must therefore say which side
of that 20/25 split it is quoting.

## Oracle

Icarus locally — `iverilog -g2012` then `vvp`, over the problem's own `_test.sv`, exactly as on the
VerilogEval lane and for the same reason: this is the flow ChipBench's own `Makefile.in` drives, so
the arms and the reference control are judged by the simulator the benchmark was built against.
It is stamped into every verdict rather than left implicit.

Scoring happens in a private temporary directory because all 45 checkers `$dumpfile("wave.vcd")`
into their cwd, and the benchmark checkout is not ours to write to.

## Bridge: the reference's own submodules are namespaced

Three references declare a helper module beside `RefModule` — `slave_mod` (Prob001) and
`dual_port_RAM` (Prob003, Prob004) — and the prompts for those problems hand the author that same
helper's source and instruct them to include it.  The testbench compiles the reference and the
candidate into one flat Verilog namespace, so a compliant author's file and the reference collide
on the helper's name and Icarus refuses the whole compilation:

    error: 'dual_port_RAM' has already been declared in this scope.

That makes three designs unwinnable *by construction* for exactly the authors who did what the
prose told them.  `_ref_namespaced` therefore renames every module a reference declares other than
`RefModule`, and every whole-word occurrence of that name inside that file, to `<name>__cbref`, in
a private copy.  Verified against the three files: the name occurs only at its declaration, at its
instantiation and (Prob003 line 107) as an instance name, never as a port or a signal, and no
`_test.sv` mentions either name — so the rename cannot reach anything but the reference's private
wiring.

What it deliberately does NOT touch is a module the reference *instantiates without declaring*:
`decoder_38` (Prob002) and `bit_8_AND`/`bit_8_OR`/`bit_8_ADDER` (Prob005) live only in the prompt,
and ChipBench's design there is that the CANDIDATE supplies them and the reference binds to the
candidate's copy.  Renaming those would break the benchmark rather than repair it.

The bridge runs for every candidate, whoever wrote it, including the golden control — it is a
property of scoring, and there is one scoring path on purpose.  It is reported in
`Verdict.bridges`, because a bridge nobody can see in the output is indistinguishable from a
bridge that did not run.

## The golden control

`golden_source` renames `RefModule` to `TopModule` in a copy of the reference and appends every
module the *prompt* defines that the copy does not already declare.  Both halves are needed and
neither is cosmetic: the rename is what puts the golden design in the candidate slot, and the
append is what makes it a COMPLIANT candidate — Prob002 and Prob005 instruct the author to include
the provided helper, and a golden copy without it fails to elaborate for a reason that is about
the control and not about the design.

## The verdict line is not one string here

VerilogEval's checker ends with `Mismatches: N in M samples` and a reader that knows only that
string is wrong on this corpus.  Two of ChipBench's 45 checkers (`Prob008_chapter12_ctrl`,
`Prob009_cp0_reg`) never print it; they print `Hint: Total mismatched samples is N out of M
samples.`, and Prob008 prints `Hint: No mismatched samples.` instead when the count is zero.  Both
of those designs' own references pass.  A one-string reader scores them `no_verdict` — two silent
non-passes out of 45, more than four points of pass rate, on the arm-independent side.  So `_read`
tries all three, in that order, and records which one answered in `extra["verdict_line"]` so a row
can never be quoted without knowing what was parsed.

## No `KNOWN_DEFECTS.json` ships with this adapter

The previous repository's copy carried one, and its ancestor's docstring even quoted a count of
designs the control could not pass.  Those entries are the *result* of running that control there,
under that Icarus, on that checkout — a measurement, not benchmark metadata — and importing a
measurement is how a new repository inherits an old conclusion without re-earning it.
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
ROOT = os.environ.get("CHIPBENCH_ROOT", os.path.join(HERE, "dataset"))

#: The three subsets, in the order ChipBench's own README introduces them.  A list rather than a
#: glob of `dataset_*`: a fourth directory appearing in a later checkout would silently enlarge
#: every denominator on this lane, and enlarging a population is a decision, not a discovery.
SUBSETS = ("dataset_self_contain", "dataset_not_self_contain", "dataset_cpu_ip")

# "Mismatches: 0 in 100 samples" -- VerilogEval's line, on 43 of the 45 checkers.
_MISMATCH = re.compile(r"mismatches\s*:\s*(\d+)\s+in\s+(\d+)", re.I)
# "Hint: Total mismatched samples is 0 out of 283 samples." -- the only line on the other two.
_TOTAL = re.compile(r"total\s+mismatched\s+samples\s+is\s+(\d+)\s+out\s+of\s+(\d+)", re.I)
# "Hint: No mismatched samples." -- Prob008's zero branch, which carries no sample count at all.
_NONE = re.compile(r"no\s+mismatched\s+samples", re.I)
# "Hint: Output 'out' has 12 mismatches. First mismatch occurred at time 45."
_PER_OUT = re.compile(r"Output\s+'?([A-Za-z_0-9]+)'?\s+has\s+(\d+)\s+mismatch", re.I)

_MODULE_DECL = re.compile(r"^[ \t]*module[ \t]+([A-Za-z_][A-Za-z_0-9$]*)", re.M)
# One `module ... endmodule` span, for lifting a provided helper out of a prompt.  `endmodule`
# must start its own line, which is how it is written in all five prompts that carry Verilog.
_MODULE_SPAN = re.compile(
    r"^[ \t]*module[ \t]+([A-Za-z_][A-Za-z_0-9$]*).*?^[ \t]*endmodule", re.M | re.S)


def _camel(key: str) -> str:
    return "".join(w[:1].upper() + w[1:] for w in re.split(r"[_\-.]", key) if w)


def _decls(src: str) -> list[str]:
    return _MODULE_DECL.findall(src)


class ChipBench(Adapter):
    name = "chipbench"
    oracle = "icarus"

    # -- the design set ----------------------------------------------------------

    def designs(self) -> list[Design]:
        # An absent dataset must not read as "this benchmark has no designs" -- the trap RTLLM
        # fell into, where a fresh clone scored 0/0 and exited 0.
        if not os.path.isdir(ROOT):
            raise FileNotFoundError(
                f"chipbench: dataset not found at {ROOT}.\n"
                f"  The benchmark checkout is external data and is not vendored.\n"
                f"  Point CHIPBENCH_ROOT at a ChipBench `Verilog Gen` directory, or fix the\n"
                f"  `dataset` symlink beside this file.\n"
                f"  Expected layout: <root>/<subset>/<stem>_{{prompt.txt,ref.sv,test.sv}}\n"
                f"  Subsets: {', '.join(SUBSETS)}")
        out, seen = [], {}
        for sub in SUBSETS:
            d = os.path.join(ROOT, sub)
            if not os.path.isdir(d):
                raise FileNotFoundError(
                    f"chipbench: subset {sub!r} is missing from {ROOT}.  The population is the "
                    f"three subsets together; a run over two of them is a different experiment "
                    f"and must say so rather than silently shrink.")
            for p in sorted(glob.glob(os.path.join(d, "*_prompt.txt"))):
                stem = os.path.basename(p)[: -len("_prompt.txt")]
                # The three subsets number their problems independently (`Prob001_` appears in
                # all three).  The full stems are distinct today and the key is the stem, which
                # keeps report rows readable -- but "distinct today" is a fact about a checkout,
                # so it is asserted rather than assumed.
                if stem in seen:
                    raise ValueError(
                        f"chipbench: stem {stem!r} appears in both {seen[stem]} and {sub}.  "
                        f"Keys collide, so one design's row would overwrite the other's — "
                        f"namespace the key by subset before running anything.")
                seen[stem] = sub
                ref = os.path.join(d, stem + "_ref.sv")
                tb = os.path.join(d, stem + "_test.sv")
                out.append(Design(
                    key=stem, bench=self.name, spec_path=p,
                    # Every problem's candidate module is `TopModule`, never the key.  Taking the
                    # key would emit a module the checker cannot find -- which arrives as
                    # `compile_fail` and reads as a hardware error rather than a naming mistake.
                    toplevel="TopModule", camel=_camel(stem),
                    meta={"ref": ref, "tb": tb, "subset": sub,
                          "has_ref": os.path.isfile(ref), "has_tb": os.path.isfile(tb)}))
        return out

    def dataset_id(self) -> dict:
        """Hash the exact bytes being graded: prompt, reference and checker of every problem.

        Per design as well as overall, and the subset list alongside, because the same 45 stems
        drawn from two of the three directories would hash differently but read the same.
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
            scorer_files = [name for name, _path in sources if
                            name.startswith(("reference/", "checker/"))]
            per[d.key] = {"sha256": dh.hexdigest(), "files": files,
                          "scorer_files": scorer_files}
            h.update(d.key.encode())
            h.update(dh.digest())
        return {"bench": self.name, "designs": len(per), "subsets": list(SUBSETS),
                "sha256": h.hexdigest(), "per_design": per}

    def stage(self, design: Design, ws: str) -> None:
        """Copy ONLY the prompt.

        The reference and the checker sit in the same directory under adjacent filenames, and
        neither may ever follow the prompt into a workspace.
        """
        dst = os.path.join(ws, "specs", f"{design.key}.spec.txt")
        os.makedirs(os.path.dirname(dst), exist_ok=True)
        with open(design.spec_path, errors="replace") as f:
            open(dst, "w").write(f.read())

    # -- the scoring bridge ------------------------------------------------------

    @staticmethod
    def _ref_namespaced(src: str) -> tuple[str, list[str]]:
        """The reference with its own helper modules renamed out of the shared namespace.

        Returns `(text, renamed)`.  `renamed` is reported in `Verdict.bridges` so a row says
        which designs were scored through this and which were untouched.
        """
        helpers = [m for m in _decls(src) if m != "RefModule"]
        for name in helpers:
            src = re.sub(r"\b" + re.escape(name) + r"\b", name + "__cbref", src)
        return src, helpers

    @staticmethod
    def _prompt_modules(prompt: str, already: set[str]) -> tuple[str, list[str]]:
        """Modules the prose HANDS the author, minus the ones the file already declares.

        Five prompts carry Verilog.  Two of them (Prob003, Prob004) hand over a helper the
        reference also declares, so `already` is what stops the golden control from declaring
        `dual_port_RAM` twice in one file.
        """
        got, names = [], []
        for m in _MODULE_SPAN.finditer(prompt):
            if m.group(1) in already or m.group(1) in names:
                continue
            names.append(m.group(1))
            got.append(m.group(0))
        return ("\n\n".join(got) + "\n") if got else "", names

    # -- the golden control ------------------------------------------------------

    def golden_source(self, design: Design) -> str | None:
        """ChipBench's own reference, rebound to the candidate slot and made COMPLIANT.

        `count=1` on the module DECLARATION only: an instantiation of `RefModule` inside the file
        (there are none today) is not a declaration and must not be rewritten into a
        self-instantiation.
        """
        ref = design.meta.get("ref")
        if not (ref and os.path.isfile(ref)):
            return None
        src = open(ref, errors="replace").read()
        new, n = re.subn(r"^([ \t]*module[ \t]+)RefModule\b", r"\1TopModule", src,
                         count=1, flags=re.M)
        if n != 1:
            return None          # not the shape this control assumes; say so by declining
        extra, _ = self._prompt_modules(
            open(design.spec_path, errors="replace").read(), set(_decls(new)))
        return new + ("\n\n" + extra if extra else "")

    # -- scoring -----------------------------------------------------------------

    def score(self, design: Design, vpath: str) -> Verdict:
        v = Verdict(key=design.key, oracle=self.oracle)
        v.extra["subset"] = design.meta.get("subset", "")
        try:
            return self._score(design, vpath, v)
        except Exception as e:                                   # score must be total
            v.status, v.detail = "harness_error", f"{type(e).__name__}: {e}"
            return v

    def _score(self, design: Design, vpath: str, v: Verdict) -> Verdict:
        if not (design.meta["has_tb"] and design.meta["has_ref"]):
            v.status, v.detail = "harness_error", "benchmark ships no test or no reference"
            return v
        if not os.path.isfile(vpath):
            v.status, v.detail = "not_emitted", f"no {vpath}"
            return v
        # A private cwd: all 45 checkers `$dumpfile("wave.vcd")` into it, and the benchmark
        # checkout is not ours to write to.
        with tempfile.TemporaryDirectory(prefix=f"chipbench-{design.key}-") as wd:
            # Read each live dataset input exactly once.  The hashes below name the same bytes that
            # are then written into this private scoring directory, closing the hash/open race that
            # a preflight-only dataset digest leaves between concurrent arms.
            ref_raw = open(design.meta["ref"], "rb").read()
            tb_raw = open(design.meta["tb"], "rb").read()
            v.extra["dataset_inputs"] = [
                {"name": "reference/" + os.path.basename(design.meta["ref"]),
                 "sha256": hashlib.sha256(ref_raw).hexdigest()},
                {"name": "checker/" + os.path.basename(design.meta["tb"]),
                 "sha256": hashlib.sha256(tb_raw).hexdigest()},
            ]
            cand = os.path.join(wd, "cand.sv")
            open(cand, "w").write(open(vpath, errors="replace").read())
            refsrc, renamed = self._ref_namespaced(ref_raw.decode(errors="replace"))
            refp, tbp = os.path.join(wd, "ref.sv"), os.path.join(wd, "test.sv")
            open(refp, "w").write(refsrc)
            open(tbp, "wb").write(tb_raw)
            v.extra["score_inputs"] = [
                {"name": "ref.sv", "sha256": hashlib.sha256(refsrc.encode()).hexdigest()},
                {"name": "test.sv", "sha256": hashlib.sha256(tb_raw).hexdigest()},
            ]
            if renamed:
                v.bridges["ref_submodule_namespaced"] = renamed
            sim = os.path.join(wd, "sim")
            # The testbench goes FIRST: it is where `WORD_SIZE`, `FUNC_*` and `OPCODE_*` are
            # `define`d, and Icarus resolves macros in command-line order, so a reference
            # compiled ahead of it sees them undefined and assumed null.
            c = subprocess.run(["iverilog", "-g2012", "-o", sim, tbp, refp, cand],
                               capture_output=True, text=True, timeout=300)
            if c.returncode != 0:
                v.status, v.detail = "compile_fail", (c.stderr + c.stdout).strip()[-700:]
                return v
            v.syntax_pass = True
            try:
                r = subprocess.run(["vvp", sim], cwd=wd, capture_output=True,
                                   text=True, timeout=300)
            except subprocess.TimeoutExpired:
                v.status, v.detail = "timeout", "vvp did not return within 300 s"
                return v
        return self._read(r.stdout + r.stderr, v)

    @staticmethod
    def _read(out: str, v: Verdict) -> Verdict:
        """Adjudicate from the checker's own words, in whichever of its three dialects it speaks.

        `TIMEOUT` is not folded into the mismatch count, and this matters in the direction that
        would otherwise manufacture passes.  The checker's timeout calls `$finish`, which runs the
        `final` block, which prints the verdict line — so a design that hung on sample 3 of 100
        still prints one, and if it happened to agree on those three samples it reads
        `Mismatches: 0`.  Counting that as a pass would be counting a truncated sample as a
        complete one.
        """
        v.mismatch_outputs = [{"out": g.group(1), "n": int(g.group(2))}
                              for g in _PER_OUT.finditer(out)]
        m = _MISMATCH.search(out) or _TOTAL.search(out)
        if "TIMEOUT" in out:
            v.status, v.detail = "timeout", out.strip()[-700:]
            if m:
                v.extra["mismatches_at_timeout"] = int(m.group(1))
                v.extra["samples_at_timeout"] = int(m.group(2))
            return v
        if m:
            v.extra["verdict_line"] = "mismatches" if _MISMATCH.search(out) else "total"
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
        if _NONE.search(out):
            # `Prob008_chapter12_ctrl`'s zero branch, which prints no counts.  It is a verdict —
            # the checker ran its comparison and reported no mismatch — but it carries NO
            # denominator, so `samples` is left absent rather than invented, and the flag below
            # is what stops a per-sample statistic from being computed off this row.
            v.extra["verdict_line"] = "none"
            v.extra["samples_reported"] = False
            v.extra["mismatches"] = 0
            v.func_pass, v.status = True, "func_pass"
            return v
        low = out.lower()
        v.status = "sim_error" if ("error" in low or "syntax" in low) else "no_verdict"
        v.detail = out.strip()[-700:]
        return v

    def score_all(self, items, workers: int = 1) -> dict:
        """Judge many designs.  Each runs in its own temporary directory and touches nothing
        outside it, so they are independent; 45 local simulations are worth overlapping."""
        if workers <= 1 or len(items) <= 1:
            return {d.key: self.score(d, p) for d, p in items}
        out = {}
        with concurrent.futures.ThreadPoolExecutor(max_workers=workers) as ex:
            futs = {ex.submit(self.score, d, p): d.key for d, p in items}
            for f in concurrent.futures.as_completed(futs):
                out[futs[f]] = f.result()
        return out


def adapter() -> Adapter:
    return ChipBench()


if __name__ == "__main__":
    import sys
    a = adapter()
    ds = a.designs()
    ident = a.dataset_id()
    n_sub: dict[str, int] = {}
    for d in ds:
        n_sub[d.meta["subset"]] = n_sub.get(d.meta["subset"], 0) + 1
    print(f"chipbench: {len(ds)} designs, oracle {a.oracle}")
    print(f"  {ident['sha256']}")
    print("  " + ", ".join(f"{s}={n_sub.get(s, 0)}" for s in SUBSETS))
    if "-v" in sys.argv:
        for d in ds:
            flags = ("" if d.meta["has_ref"] else " NO-REF") + ("" if d.meta["has_tb"]
                                                                else " NO-TB")
            print(f"  {d.key:40} {d.meta['subset']:26} {d.camel}{flags}")
