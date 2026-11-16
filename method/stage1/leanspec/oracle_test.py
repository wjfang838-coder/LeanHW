"""What a menu may and may not do to the behaviours it was built from.

`python3 -m leanspec.oracle_test`

Step 06 is the only place in leanSpec where a fact arrives from outside the prose, and the menu
is the whole of the question.  So a reduction of it is dangerous in the direction the output does
not show: drop the wrong behaviour and a `chosen` answer eliminates a reading it should not have,
or an `outside` reports a hole in the variant space that the reduction invented.  Nothing
downstream can tell the difference -- `refine` sees a verdict and a letter, not the menu the
letter came from.

`oracle.focus` reduces menus, so every case here is about what survives the reduction rather than
about how small it gets.  The one that motivated the file is the last kind: two readings that
agree about the value set of every single coordinate and differ only in which values occur
*together*.  Filtering coordinates one at a time -- the obvious implementation, and the first one
written -- finds nothing to keep there and silently turns a real question into a one-option page.

## And who is answering

The second half of the file is about the other thing step 06 can get wrong, which is not what was
asked but WHO was asked.  A benchmark run answers the same questions from the design's reference
implementation, and the failure to prevent is not that it produces a bad specification -- it
produces a fine one -- but that the result becomes indistinguishable from a designer's.  Every
case there checks a way the two could be confused: a default that could drift, two sittings that
could share a directory, an "any" a simulator has no standing to give, and an answer key that
could reach an authoring root.
"""
from __future__ import annotations

import inspect
import itertools
import json
import os
import sys
import tempfile

from common import agent

from leanspec import author, cases as cases_mod, oracle, refine


def _w(tags: dict, kind: str = "ambiguity", choice: str = "q") -> dict:
    """A witness carrying nothing but the predictions, which is all `focus` reads."""
    return {"id": f"{kind}:{choice}", "kind": kind, "choice": choice,
            "ctx": {"steps": [{"in": 0}]}, "predicted": tags}


def _obs(*steps) -> dict:
    return {"steps": list(steps)}


# A fork about `v`, asked where a second coordinate `d` is still open.  This is the shape that
# produced 596 waveforms on `accu`: the readings disagree about one bit and the menu is that bit
# times everything else the prose has not yet pinned down.
CONTAMINATED = _w({
    "q:a": [_obs({"v": 0, "d": k}) for k in (0, 1, 2)],
    "q:b": [_obs({"v": 1, "d": k}) for k in (0, 1, 2)],
})

# Two readings, four behaviours, and no single coordinate tells them apart: `x` is 0 or 1 under
# both and so is `y`.  What differs is the pairing.
CORRELATED = _w({
    "q:a": [_obs({"x": 0, "y": 0}), _obs({"x": 1, "y": 1})],
    "q:b": [_obs({"x": 0, "y": 1}), _obs({"x": 1, "y": 0})],
})

# The readings admit exactly the same behaviours: a witness that cannot eliminate anything, whose
# honest outcome is `silent`.  A reduction must not manufacture a distinction here.
INDISTINGUISHABLE = _w({
    "q:a": [_obs({"v": 0}), _obs({"v": 1})],
    "q:b": [_obs({"v": 0}), _obs({"v": 1})],
})

# Overlapping, not disjoint: `b` admits everything `a` does and one more.  Only `a` is refutable.
NESTED = _w({
    "q:a": [_obs({"v": 0, "d": 0}), _obs({"v": 0, "d": 1})],
    "q:b": [_obs({"v": 0, "d": 0}), _obs({"v": 0, "d": 1}), _obs({"v": 1, "d": 0})],
})

ALL = {"contaminated": CONTAMINATED, "correlated": CORRELATED,
       "indistinguishable": INDISTINGUISHABLE, "nested": NESTED}


def _sets(w: dict) -> dict:
    tags = oracle._relevant(w)
    return {t: {oracle._key(o) for o in (w["predicted"][t] or [])} for t in tags}


def _projected(w: dict) -> dict:
    tags, foc = oracle._relevant(w), oracle.focus(w)
    return {t: {oracle._key(oracle._project(o, foc)) for o in (w["predicted"][t] or [])}
            for t in tags}


def cases() -> list[tuple[str, bool]]:
    out = []

    # 1. The contamination is removed and the question is not.  `d` is another witness's
    #    coordinate; offering the product asks the designer to answer that one too, at a context
    #    chosen to be minimal for this one, and then scores only this one.
    out.append(("a free coordinate is dropped from the menu",
                oracle.focus(CONTAMINATED) == [("v", 0)]))
    out.append(("...and the menu is the readings' own distinction",
                len(oracle.options(CONTAMINATED)) == 2))

    # 2. Correlation survives.  A per-coordinate filter would return no coordinates at all here.
    out.append(("a correlated pair is found, not discarded",
                oracle.focus(CORRELATED) == [("x", 0), ("y", 0)]))
    out.append(("...and the four behaviours are still four",
                len(oracle.options(CORRELATED)) == 4))

    # 3. Refutability is the quantity that may not be lost, in either direction.  Every reading
    #    the unprojected menu could eliminate, the projected one still eliminates -- and no
    #    reading becomes refutable that was not, which would be a distinction invented by the
    #    reduction.
    for name, w in ALL.items():
        tags = oracle._relevant(w)
        out.append((f"{name}: refutable readings are exactly preserved",
                    oracle._refutable(_sets(w), tags)
                    == oracle._refutable(_projected(w), tags)))

    # 4. Disjointness too: a witness where *any* answer refutes a reading keeps that property,
    #    because that is what makes a `discriminating` witness worth the query.
    for name, w in ALL.items():
        full, proj = _sets(w), _projected(w)
        ok = all(bool(full[a] & full[b]) or not (proj[a] & proj[b])
                 for a, b in itertools.combinations(oracle._relevant(w), 2))
        out.append((f"{name}: disjoint readings stay disjoint", ok))

    # 5. A menu never collapses to a single option, which is not a question.
    for name, w in ALL.items():
        n = len({oracle._key(o) for t in oracle._relevant(w) for o in w["predicted"][t]})
        out.append((f"{name}: a menu of {n} does not become one",
                    len(oracle.options(w)) >= min(2, n)))

    # 6. Nothing is dropped: the options partition the behaviours.  Every original behaviour maps
    #    onto exactly one option, and an option carries the union of its members' tags -- so the
    #    reduction can only make an answer *less* eliminating, never more.
    for name, w in ALL.items():
        foc = oracle.focus(w)
        keys = {oracle._key(o["obs"]) for o in oracle.options(w)}
        covered = all(oracle._key(oracle._project(o, foc)) in keys
                      for t in oracle._relevant(w) for o in w["predicted"][t])
        tags_ok = all(set(o["tags"]) == {t for t in oracle._relevant(w)
                                         if any(oracle._key(oracle._project(p, foc))
                                                == oracle._key(o["obs"])
                                                for p in w["predicted"][t])}
                      for o in oracle.options(w))
        out.append((f"{name}: options partition the behaviours", covered and tags_ok))

    # 7. `refine` scores on the same projection.  If it did not, the chosen behaviour -- which
    #    asserts only the focus coordinates -- would be matched against predictions carrying
    #    values for coordinates nobody was asked about, and every reading would be eliminated.
    for name, w in ALL.items():
        foc = oracle.focus(w)
        agree = True
        for o in oracle.options(w):
            obs = refine._seq(o["obs"])
            got = {t for t in oracle._relevant(w)
                   if any(refine._matches(oracle._project(a, foc), obs)
                          for a in (w["predicted"][t] or []))}
            agree = agree and got == set(o["tags"])
        out.append((f"{name}: refine reproduces each option's tags", agree))

    # 8. A witness with one reading has nothing to focus on, and the unprojected path is the
    #    identity -- so a menu this function declines to reduce is exactly the menu it was.
    one = _w({"q:a": [_obs({"v": 0}), _obs({"v": 1})]})
    out.append(("a single reading is not projected", oracle.focus(one) is None))
    ob = _obs({"v": 0, "d": 3})
    out.append(("no focus is the identity", oracle._project(ob, None) == ob))

    # 9. The labels.  `LETTERS[pos]` raised `IndexError` on 8 of `accu`'s 10 witnesses; the
    #    labelling is now total, and total is only useful if it round-trips.
    out.append(("labels round-trip past the alphabet",
                all(oracle._unlabel(oracle._label(i)) == i for i in range(2000))))
    out.append(("labels are what they were for a short menu",
                [oracle._label(i) for i in range(4)] == ["A", "B", "C", "D"]))
    out.append(("the alphabet rolls over rather than raising",
                oracle._label(24) == "AA" and oracle._label(23) == "Z"))
    out.append(("a non-label is not an option index",
                oracle._unlabel("I") == -1 and oracle._unlabel("") == -1
                and oracle._unlabel("A1") == -1))

    # ...and a two-letter answer names the behaviour it was printed beside.
    big = [{"obs": _obs({"v": i}), "tags": ["q:a"]} for i in range(30)]
    perm = oracle.order("seed", len(big))
    v = oracle._verdict("AB", big, perm)
    out.append(("a two-letter answer resolves to its option",
                v["verdict"] == "chosen" and v["obs"] == big[perm[25]]["obs"]))
    out.append(("an off-menu letter is unparsed, not rounded",
                oracle._verdict("ZZ", big, perm)["verdict"] == "unparsed"))

    # 10. Rendering.  A projected option draws its focus and leaves the rest don't-care; the
    #     coordinates it does not fix must not appear as though it fixed them at zero.
    drawn = oracle.waveform(oracle.options(CONTAMINATED)[0]["obs"])
    out.append(("a projected waveform omits what it does not assert",
                "d" not in drawn and "v" in drawn))

    out += reference_cases()
    return out


# ------------------------------------------------- the other authority, and its four guards
#
# The reference backend answers the same questions from the benchmark's own implementation of the
# design, and every guard on it is about keeping the two authorities distinguishable AFTERWARDS.
# So what is checked here is not that it works -- that needs a simulator and a design -- but that
# nothing about it is reachable, or recordable, by accident.
#
# `ask_all` itself is not called: it launches an agent.  What is called is everything that decides
# WHERE it would write, WHAT it would put, and HOW an answer would be read back, which is where
# every one of the four guards lives.

def _prepared(w):
    """One `prepared` entry, in the shape `questions_markdown` reads."""
    opts = oracle.options(w)
    qid = oracle.question_id(w)
    return {"witness": w, "id": w["id"], "purpose": w["kind"], "qid": qid,
            "opts": opts, "perm": oracle.order(qid, len(opts))}


def reference_cases() -> list[tuple[str, bool]]:
    out = []
    items = [_prepared(CONTAMINATED)]

    # Guard 1: never the default.  Both the module's own idea of who is asking and the parameter
    # default on the function that asks.  A third place that could disagree with these two would
    # be a place the answer key turns on quietly, so a wrong `kind` raises rather than falling
    # back -- a typo that produced a designer sitting would produce a correct-LOOKING result.
    out.append(("the default authority is the designer",
                oracle.asking() == oracle.KIND_DESIGNER
                and inspect.signature(oracle.ask_all).parameters["kind"].default
                == oracle.KIND_DESIGNER))
    out.append(("...and the flag's default spells the same thing",
                oracle.FLAG_KINDS["designer"] == oracle.KIND_DESIGNER
                and oracle.FLAG_KINDS["rtl"] == oracle.KIND_REFERENCE))
    try:
        oracle.ask_with("rtl")            # the FLAG spelling, not a kind
        bad_kind_refused = False
    except ValueError:
        bad_kind_refused = True
    out.append(("an unknown kind is refused, not rounded to the designer", bad_kind_refused
                and oracle.asking() == oracle.KIND_DESIGNER))

    # The two sittings do not mix.  This is the guard that stops a designer's stored answers being
    # replayed under a reference run's ledger rows -- silently, since a replay writes no
    # transcript of its own and every other field of the row would be identical.
    c = cases_mod.Case(name="t.guard", bench="rtllm")
    dd = oracle.query_dir(c, 1, "questions", oracle.KIND_DESIGNER)
    dr = oracle.query_dir(c, 1, "questions", oracle.KIND_REFERENCE)
    out.append(("the two authorities sit in different directories", dd != dr))
    out.append(("...and the designer's is where it has always been",
                dd == oracle.query_dir(c, 1, "questions")))

    # The questions are the same questions.  If they were not, a reference run would measure a
    # second method that happens to share a name.  What differs between the two documents is the
    # brief, the closing line, and the two lines per question that speak of the document as its
    # reader's own -- so the check is that those are the ONLY lines that differ, and that the
    # stimulus and the lettered menu below them are the same bytes.
    qd = oracle.questions_markdown(oracle.PROSE, items, None, oracle.KIND_DESIGNER)
    qr = oracle.questions_markdown(oracle.PROSE, items, None, oracle.KIND_REFERENCE,
                                   ["verified_accu.v"])
    bd = oracle._question_body(CONTAMINATED, items[0]["opts"], items[0]["perm"], None, "###",
                               oracle.KIND_DESIGNER)
    br = oracle._question_body(CONTAMINATED, items[0]["opts"], items[0]["perm"], None, "###",
                               oracle.KIND_REFERENCE)
    voiced = oracle._VOICE[oracle.KIND_DESIGNER].values()
    moved = [i for i, (x, y) in enumerate(zip(bd, br)) if x != y]
    out.append(("the two authorities differ in voice and only in voice",
                len(bd) == len(br) and moved
                and all(any(bd[i].endswith(s) for s in voiced) for i in moved)))
    menu = "\n".join(bd[max(moved) + 1:])                     # the waveforms, below the last voice
    stim = oracle.waveform(CONTAMINATED["ctx"])
    out.append(("...so both are shown the same stimulus and the same menu",
                stim in qd and stim in qr and menu in qd and menu in qr))
    out.append(("the designer is addressed as the document's author",
                "your specification" in qd and "your specification" not in qr))
    out.append(("the reference is not handed the specification",
                "spec.txt" in qd and "spec.txt" not in qr))
    out.append(("...and is told which file is the authority", "verified_accu.v" in qr))
    out.append(("`any` is offered to the designer and not to the reference",
                '"any"' in qd and 'no "any"' in qr.lower().replace("**", "")))

    # A violation question is the one shape where the framing is a substantive instruction rather
    # than a pronoun: a designer is asked which sentence they meant to keep, and a reference is
    # told to find out which one the implementation breaks.  Both are still shown the same
    # waveform, the same guarantee and the same two clauses.
    vw = dict(CONTAMINATED, kind="violation", property="p", statement="v must never be 1",
              admitted=_obs({"v": 1}), admits=[_obs({"v": 1})])
    vopts = [{"text": "the definition is wrong", "tags": ["a"]},
             {"text": "the guarantee is wrong", "tags": ["b"]}]
    vd = "\n".join(oracle._violation_body(vw, vopts, [0, 1], None, "###",
                                          oracle.KIND_DESIGNER))
    vr = "\n".join(oracle._violation_body(vw, vopts, [0, 1], None, "###",
                                          oracle.KIND_REFERENCE))
    out.append(("a contradiction shows both authorities the same evidence",
                "v must never be 1" in vd and "v must never be 1" in vr
                and all(o["text"] in vd and o["text"] in vr for o in vopts)))
    out.append(("...and only the designer is told that only they know which",
                "only you know which" in vd and "only you know which" not in vr
                and "what the reference does decides which" in vr))

    # ...which makes the digests differ, which is a second wall in front of the same failure the
    # split directories prevent.  Not the primary one; the primary one is above.
    out.append(("the two briefs digest differently",
                cases_mod.sha256(qd) != cases_mod.sha256(qr)))

    # Guard 2 in the part of it that is checkable without an agent: a reference answer of "any" is
    # `refused`, not accepted as a declared degree of freedom.  An implementation does one thing
    # at one input; the other candidates being untaken is not evidence that they are permitted.
    opts, perm = items[0]["opts"], items[0]["perm"]
    out.append(("`any` from a designer is a degree of freedom",
                oracle._verdict("any", opts, perm, allow_any=True)["verdict"] == "any"))
    out.append(("...and from a reference it is refused",
                oracle._verdict("any", opts, perm, allow_any=False)["verdict"] == "refused"))

    # Guard 4: the answer key stays out of every authoring root.  The authoring role reaches its
    # case sandbox plus the Lean library, and a reference sitting is neither -- it is a sibling of
    # the sandbox, so no path of it is under an authoring session's root, and nothing here is
    # added to `author.AUTHOR.allow`.  Asserted rather than described: the claim that the method
    # did not read the answer key is exactly this containment.
    root = os.path.realpath(c.sandbox) + os.sep
    out.append(("a reference sitting is outside the authoring root",
                not os.path.realpath(dr).startswith(root)))
    out.append(("...and no authoring role is granted a path to one",
                all(not os.path.realpath(dr).startswith(os.path.realpath(a) + os.sep)
                    for a in author.AUTHOR.allow)))
    out.append(("the reference role gets a simulator and not a shell",
                "Bash" not in oracle.REFERENCE.tools
                and set(agent.SIM_TOOLS) <= set(oracle.REFERENCE.tools)))

    # A reference is resolved from the case's own source directory, so a case registered from a
    # loose file gets none -- and is TOLD so, rather than being handed whatever RTL happens to sit
    # near it.  A missing answer key is a reported reason and not a crash.
    got, why = oracle.reference_files(cases_mod.Case(name="t.noref", source=""))
    out.append(("a case with no source has no reference, and says why", not got and bool(why)))

    # `_replayable` binds an answer to the implementation it was read out of as well as to the
    # question it was given for.  A benchmark that corrects its reference between two runs has
    # changed WHO answered, and replaying the old verdicts would put the old implementation's
    # behaviour into a specification labelled as measured against the new one.
    with tempfile.TemporaryDirectory() as d:
        with open(os.path.join(d, oracle.ANSWERS), "w") as f:
            json.dump({"answers": [{"q": 1, "answer": "A"}]}, f)
        with open(os.path.join(d, oracle.ASKED), "w") as f:
            json.dump({"question_sha256": "Q", "questions": 1, "round": 1,
                       "oracle_kind": oracle.KIND_REFERENCE, "reference_sha256": "R1"}, f)
        out.append(("an answer to this question, from this reference, replays",
                    oracle._replayable(d, "Q", refsha="R1") == (True, None)))
        same_q, why2 = oracle._replayable(d, "Q", refsha="R2")
        out.append(("...and the same answer from a different reference does not",
                    not same_q and "different reference" in (why2 or "")))
        out.append(("...while a designer run, which has none, is unaffected",
                    oracle._replayable(d, "Q") == (True, None)))

    # THE BATCH DRIVER'S CHILD.  `oracle._ASKING` is a module global in whatever process set it,
    # and every pipeline step the batch driver runs is a `cli.py run` in a CHILD process.  So a
    # fifty-design benchmark batch that set the kind here and did not put it on the child's argv
    # would answer all fifty from the designer while its own banner, its ledger and its operator
    # all said `reference_rtl` -- the labelling failure the rest of this file exists to prevent,
    # arriving through the label rather than around it.  Nothing downstream could catch it: each
    # child would honestly record `oracle_kind: designer`, and the only disagreement would be
    # with a sentence printed by a process that wrote none of the artifacts.
    argv: list[list[str]] = []

    class _Done:
        returncode, stdout, stderr = 0, "", ""

    was_run, was_asking = author.subprocess.run, oracle.asking()
    try:
        author.subprocess.run = lambda cmd, **kw: (argv.append(cmd), _Done())[1]
        c2 = cases_mod.Case(name="t.forward", source="")
        author.machine(c2, (6, 6), 1, oracle.KIND_REFERENCE)
        out.append(("the batch driver puts the kind on the child's command line",
                    argv[-1][-2:] == ["--oracle", oracle.KIND_REFERENCE]))

        # The trap, asserted as a trap: this process is now answering as the reference, and a
        # `machine` called without the argument must STILL send `designer`.  If the two were ever
        # coupled -- an implicit read of `asking()` in the default -- this case would pass while
        # the one above became decorative.
        oracle.ask_with(oracle.KIND_REFERENCE)
        author.machine(c2, (6, 6), 1)
        out.append(("...and does not inherit it, because a module global does not cross a fork",
                    argv[-1][-2:] == ["--oracle", oracle.KIND_DESIGNER]))
    finally:
        author.subprocess.run = was_run
        oracle.ask_with(was_asking)

    # Every value the batch driver accepts is one the child can resolve.  `cli._asking` looks the
    # flag up in `FLAG_KINDS` with a bare subscript, so a kind the batch offers and that table
    # does not hold is a `KeyError` in the child of a run that has already started -- and the
    # kinds `machine` forwards are the RESOLVED ones, which must be keys of it too (they are:
    # `reference_rtl` maps to itself, which is what makes forwarding a resolved kind safe).
    ap = author._parser()
    choices = next(x.choices for x in ap._actions if x.dest == "oracle")
    out.append(("every kind the batch driver offers is one the child can resolve",
                bool(choices) and set(choices) <= set(oracle.FLAG_KINDS)))
    out.append(("...including the resolved ones it actually forwards",
                {oracle.FLAG_KINDS[k] for k in choices} <= set(oracle.FLAG_KINDS)))
    out.append(("...and the batch default is the designer",
                oracle.FLAG_KINDS[next(x.default for x in ap._actions if x.dest == "oracle")]
                == oracle.KIND_DESIGNER))
    return out


def main() -> int:
    bad = [label for label, ok in cases() if not ok]
    for label, ok in cases():
        print(f"  {'ok ' if ok else 'BAD'}  {label}")
    if bad:
        print(f"\n{len(bad)} case(s) wrong:")
        for label in bad:
            print(f"  {label}")
        return 1
    print(f"\noracle: all {len(cases())} cases hold — the menu is smaller and it eliminates "
          f"exactly what it eliminated, and the two authorities cannot be mistaken for each other")
    return 0


if __name__ == "__main__":
    sys.exit(main())
