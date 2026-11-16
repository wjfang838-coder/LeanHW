#!/usr/bin/env python3
"""The implementation as it stood BEFORE the proof, emitted.

    python3 -m leanrtl.preproof --ws <workspace> --key <key>
    python3 -m leanrtl.preproof --ws <workspace> --key <key> --stash-proof   # after the fact

Two Verilog modules come out of one leanRTL run, and this file produces the first of them:

    out/<key>.preproof.v   D wrote an implementation against the frozen specification and it
                           was emitted with NO proof in the file.
    out/<key>.v            the same implementation after the proof phase, which D is permitted
                           to re-encode in order to make a proof close.

## Why the pair is worth taking

The claim this half makes is that writing a proof changes the artifact — that a design forced to
refine an executable specification comes out different from one that merely agreed with it on a
few hundred vectors.  That claim is not testable against `out/<key>.v` alone, because by the time
anyone reads it the correction has already happened and left nothing behind to compare against.

It is also not testable by running a second arm with the proof step switched off.  That arm has a
different author session, a different sampling of the model, and a different set of things D
happened to try; the difference between the two Verilog files would then be the proof phase plus
everything else that differs between two sessions.  Taking BOTH artifacts out of ONE session is
the only version of this measurement with one variable in it.

## Why it is not simply read out of `emits/`

`bb.archive_emit` already files every green emit, and its docstring says which one counts as
pre-proof is "decided out of band by whatever reads `emits/`".  Nothing read it, and on the runs
on disk there was nothing to read: D's inner loop during the implementation phase is
`build`/`check`/`sim`, and D does not call `emit` until there is something to emit for.  On
`accu` the first archived emit on both arms already carries a populated `l1` and `wt` section.
The archive is a record of what happened to be emitted, and what happened was that nobody emitted
before proving.  So this takes the measurement rather than looking for it.

## What makes it faithful

Nothing is stubbed and nothing is reconstructed.  At the tail of step 04 the file
`frags/<key>/proof.lean` does not exist yet — D writes it at step 06 — so the ordinary full
assembly `asm_f.py` produces at that moment ALREADY has the stub proof in it.  The pre-proof
artifact is therefore the normal emit path run at the normal time, not a special assembly mode,
and the `--frag` machinery is not involved.

`--stash-proof` is the after-the-fact form, for a workspace that finished before this file
existed.  It moves `frags/<key>/proof.lean` aside, emits, and puts it back, restoring the
assembled file and `out/<key>.v` byte for byte and refusing to exit until their hashes match what
they were.  It is a separate flag rather than the default because the two are not equally
trustworthy: the in-pipeline capture observes a state the run actually passed through, and the
stashed capture reconstructs one.  They are indistinguishable in the emitted Verilog and must not
be indistinguishable in the record, so `preproof.json` says which was taken.

The reconstruction is faithful only when the proof phase did not re-encode the implementation,
and that is checkable rather than assumed: `bb.py` records `sec_sha.impl` on every invocation, so
the implementation section's hash through the whole session is in `log/<key>.jsonl`.  `delta()`
below reports whether it ever moved.  Where it did move, a stashed capture emits the FINAL
implementation with the proof removed, which is not the pre-proof implementation and is reported
as `faithful: false` rather than quietly filed beside the honest ones.

`bb.archive_emit` also files this emit in `emits/` as an ordinary green emit, which is correct: it
IS one, it really happened, and suppressing it would leave `log/<key>.jsonl` recording an emit with
no artifact beside it.  It is self-identifying there without needing a flag — `asm_f.STUB_PROOF` is
a constant, so a pre-proof emit's `sec_sha.l1` and `sec_sha.wt` are the same two values in every
workspace of every design, and no emit taken with a real proof in the file can carry them.

## What it must not do

Fail the step it is attached to.  This is a measurement, and `bb.archive_emit` states the same
commitment for the same reason: a run that dies because its instrumentation died has been
destroyed by the act of observing it.  Every entry point here returns a record with `ok` in it
and raises nothing.

Be visible to the author.  It runs after a session has ended, writes only under `out/`, and no
prompt names it.  An implementer who knew a pre-proof snapshot was being scored would be writing
for two graders.
"""
from __future__ import annotations

import argparse
import glob
import json
import os
import re
import shutil
import subprocess
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

from common import ledger, paths, provenance                                       # noqa: E402

#: The suffix that marks the earlier of the two artifacts.  One string, used for the Verilog, the
#: Lean it came from and the record beside them, so that `compare.discover` can recognise the set
#: by a single name rather than by three that have to be kept in agreement.
TAG = "preproof"


def _sha(path: str) -> str:
    if not os.path.isfile(path):
        return ""
    with open(path, "rb") as f:
        return provenance.sha256(f.read())


def blind_file(ws: str, key: str) -> str | None:
    """The assembled design file, found the way `bb.py` finds it: by its header, not its name.

    `asm_f.camel_of` derives the filename from the key through a rule that has been widened once
    already (for hyphenated ChipBench keys).  Re-deriving it here would put a second copy of that
    rule in the tree, and the failure mode of the two disagreeing is silent: this file would
    restore a design file that is not the one it moved.
    """
    for p in sorted(glob.glob(os.path.join(ws, "LeanRTL", "Blind", "*.lean"))):
        with open(p, errors="replace") as f:
            if re.match(rf"--\s*@blind\s+{re.escape(key)}\s*$", f.readline().strip()):
                return p
    return None


def delta(ws: str, key: str) -> dict:
    """Did the proof phase re-encode the implementation?

    Read out of `log/<key>.jsonl`, which `bb.py` writes a line to on every invocation carrying
    `sec_sha` — the four scaffold sections hashed separately.  The implementation section's hash
    over the whole session is therefore already on disk, and this needs no instrumentation of its
    own.

    Lines whose `sec_sha` is `{"degraded": True}` or absent are skipped rather than treated as a
    change.  Those are the fragment-scoped `f_build` / `f_check` invocations, which assemble one
    fragment without the section markers; reading a missing marker as a moved implementation
    would report a correction on every run.
    """
    p = os.path.join(ws, "log", key + ".jsonl")
    seen: list[str] = []
    if os.path.isfile(p):
        with open(p, errors="replace") as f:
            for line in f:
                line = line.strip()
                if not line.startswith("{"):
                    continue
                try:
                    r = json.loads(line)
                except ValueError:
                    continue
                s = r.get("sec_sha")
                if not isinstance(s, dict) or s.get("degraded") or not s.get("impl"):
                    continue
                if not seen or seen[-1] != s["impl"]:
                    seen.append(s["impl"])
    return {"impl_section_shas": seen,
            "changed": len(seen) > 1,
            "n_distinct": len(seen),
            "means": ("the implementation section moved during the session, so the proof phase "
                      "re-encoded it — the pre-proof and final Verilog are about different Lean"
                      if len(seen) > 1 else
                      "the implementation section never moved: D closed the proof against the "
                      "implementation as written, with no correction.  A pre-proof and a final "
                      "artifact that differ anyway differ for a reason that is not a correction, "
                      "and that is worth a look rather than a shrug"
                      if len(seen) == 1 else
                      "no undegraded sec_sha in the log — nothing can be said either way, which "
                      "is not the same as nothing having changed")}


def capture(ws: str, key: str, stash_proof: bool = False) -> dict:
    """Emit the implementation with no proof in the file.  Never raises.

    Returns a record and writes it to `out/<key>.preproof.json`.  The caller is a pipeline step
    whose success must not depend on this, so every failure below is a field in the record.
    """
    rec: dict = {"key": key, "tag": TAG, "ok": False, "how": "", "stashed": bool(stash_proof)}
    try:
        return _capture(ws, key, stash_proof, rec)
    except Exception as e:                        # noqa: BLE001 — see the module docstring
        rec["how"] = f"{type(e).__name__}: {e}"
        _write(ws, key, rec)
        return rec


def _write(ws: str, key: str, rec: dict) -> None:
    out = os.path.join(ws, "out")
    os.makedirs(out, exist_ok=True)
    with open(os.path.join(out, f"{key}.{TAG}.json"), "w") as f:
        json.dump(rec, f, indent=1)


def _capture(ws: str, key: str, stash_proof: bool, rec: dict) -> dict:
    frag = os.path.join(ws, "frags", key, "impl.lean")
    proof = os.path.join(ws, "frags", key, "proof.lean")
    if not os.path.isfile(frag):
        rec["how"] = "no frags/%s/impl.lean — nothing was implemented" % key
        _write(ws, key, rec)
        return rec

    rec["impl_sha256"] = _sha(frag)
    rec["delta"] = delta(ws, key)

    if os.path.isfile(proof) and not stash_proof:
        # In-pipeline this is the guard that says the capture happened at the right moment: at the
        # tail of step 04 there is no proof yet.  A proof on disk means the caller is asking for
        # this after the fact and has not said so, and the emit would silently be of the PROVEN
        # design under a filename claiming it was not.
        rec["how"] = ("frags/%s/proof.lean exists, so this is not the pre-proof moment.  Pass "
                      "--stash-proof to take the after-the-fact reconstruction, which is "
                      "recorded as such." % key)
        _write(ws, key, rec)
        return rec

    # What has to survive: the assembled design file and the emitted artifacts.  This runs `emit`,
    # which overwrites both, and on an after-the-fact capture both already hold the FINAL result
    # of a finished run.  Losing them would destroy the second half of the pair in the act of
    # taking the first.
    blind = blind_file(ws, key)
    guarded = [p for p in (blind,
                           os.path.join(ws, "out", key + ".v"),
                           os.path.join(ws, "out", key + ".rtlil.json")) if p]
    before = {p: _sha(p) for p in guarded}
    keep = {p: p + ".preproof-guard" for p in guarded if before[p]}
    stash = proof + ".preproof-stash"

    try:
        for src, dst in keep.items():
            shutil.copy2(src, dst)
        if stash_proof and os.path.isfile(proof):
            os.replace(proof, stash)

        r = subprocess.run([sys.executable, os.path.join(ws, "scripts", "bbf.py"),
                            key, "emit", "--role", "D"],
                           cwd=ws, capture_output=True, text=True)
        rec["rc"] = r.returncode
        tail = (r.stdout + r.stderr)[-2000:]

        v = os.path.join(ws, "out", key + ".v")
        if os.path.isfile(v):
            shutil.copy2(v, os.path.join(ws, "out", f"{key}.{TAG}.v"))
            rec["verilog"] = f"out/{key}.{TAG}.v"
            rec["verilog_sha256"] = _sha(v)
            rec["bytes"] = os.path.getsize(v)
        b = blind_file(ws, key)
        if b:
            shutil.copy2(b, os.path.join(ws, "out", f"{key}.{TAG}.lean"))
            rec["lean"] = f"out/{key}.{TAG}.lean"
        rec["ok"] = bool(rec.get("verilog")) and r.returncode == 0
        if not rec["ok"]:
            rec["how"] = f"emit exited {r.returncode}" if r.returncode else "emit produced no .v"
            rec["tail"] = tail
    finally:
        # Restoration is unconditional and verified.  An exception in the block above leaves a
        # finished workspace holding a proof-free emit under the name of its final artifact,
        # which is the one outcome of this file that would be worse than not running it.
        if os.path.isfile(stash):
            os.replace(stash, proof)
        for src, dst in keep.items():
            if os.path.isfile(dst):
                shutil.copy2(dst, src)
                os.remove(dst)
        rec["restored"] = {os.path.relpath(p, ws): (_sha(p) == before[p]) for p in guarded}

    bad = [p for p, good in rec["restored"].items() if not good]
    if bad:
        rec["ok"] = False
        rec["how"] = ("RESTORE FAILED for " + ", ".join(bad) + " — the workspace no longer holds "
                      "the artifacts it held before this ran, and its final result is not "
                      "trustworthy until they are put back by hand from `emits/`.")

    # `faithful` is about the reconstruction, not the emit.  A stashed capture of a run whose
    # implementation section moved emits the FINAL implementation with its proof deleted, and
    # that is not the artifact the name claims.  Said in the record rather than in a README,
    # because a table is built from the record.
    changed = rec.get("delta", {}).get("changed")
    rec["faithful"] = (not rec["stashed"]) or (changed is False)
    rec["faithful_why"] = (
        "captured in-pipeline at the tail of step 04, before any proof existed"
        if not rec["stashed"] else
        "reconstructed after the fact, and the implementation section never moved during the "
        "session, so the file emitted here is byte-identical to the one D had before proving"
        if changed is False else
        "reconstructed after the fact on a run whose implementation section DID move: this is "
        "the final implementation with its proof removed, which is not what D wrote before "
        "proving.  Not comparable with an in-pipeline capture."
        if changed else
        "reconstructed after the fact, and the log cannot say whether the implementation moved")

    _write(ws, key, rec)
    try:
        ledger.log(paths.DATA, "preproof", ws=os.path.basename(ws), key=key,
                   ok=rec["ok"], stashed=rec["stashed"], faithful=rec["faithful"],
                   impl_changed=changed)
    except Exception:                                       # noqa: BLE001
        pass
    return rec


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ws", required=True)
    ap.add_argument("--key", required=True)
    ap.add_argument("--stash-proof", action="store_true",
                    help="take the after-the-fact reconstruction on a finished workspace: move "
                         "the proof fragment aside, emit, put it back")
    a = ap.parse_args(argv)
    ws = os.path.abspath(os.path.expanduser(a.ws))
    rec = capture(ws, a.key, a.stash_proof)
    print(json.dumps({k: v for k, v in rec.items() if k != "tail"}, indent=1))
    return 0 if rec["ok"] else 1


if __name__ == "__main__":
    raise SystemExit(main())
