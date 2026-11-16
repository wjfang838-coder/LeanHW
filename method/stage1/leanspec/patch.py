#!/usr/bin/env python3
"""Turning a decision into an edit of the specification's own text.

Until this module existed the pipeline's repairs were *instructions*: a decision recorded a
`consequence` reading "C8 should say the result appears on the same clock edge that consumes
the fourth datum", and a human was left to perform the edit.  That is a gap between what the
framework proves and what it delivers.  `goal.md` asks for a decided specification; a
decided specification that only a person can produce is a decided specification the pipeline
does not have.

So a decision now carries hunks, and a hunk is checked against the same discipline stage 1's
clauses are:

    {"op": "replace", "clause": "C8", "span": [199, 356],
     "original": "<the exact bytes of prose[199:356]>",
     "replacement": "<what it should say instead>"}

    {"op": "insert_after", "clause": "C2", "at": 481, "text": "<a new sentence>"}

Three rules, all mechanical, all rejections rather than warnings:

  * **the quote must be byte-exact.**  `prose[span[0]:span[1]] == original`, the same check
    `schema.validate_extraction` makes of a clause.  An edit whose anchor has been re-typed is
    an edit against a specification nobody has, and it would silently land in the wrong place
    once the offsets moved.
  * **hunks may not overlap.**  Two decisions rewriting the same sentence is a real situation
    -- one clause can carry two questions -- and the resolution is one hunk written by both
    decisions, not two hunks applied in an order nobody chose.
  * **a hunk must sit inside a clause the decision is based on.**  This is provenance in the
    other direction: stage 1 requires every finding to name the sentence it came from, and
    this requires every repair to land on one of those sentences.  A decision about
    `out_phase` cannot rewrite the port table.

`apply` is offset-stable by construction: hunks are sorted by start and applied from the end
backwards, so an earlier hunk's offsets are still valid when it is reached.
"""
from __future__ import annotations

OPS = ("replace", "insert_after")


def validate(hunks: list[dict], prose: str, clause_spans: dict[str, tuple[int, int]],
             allowed_clauses: dict[int, set[str]] | None = None) -> list[str]:
    """Structural check of a hunk list against the prose it claims to edit.

    `allowed_clauses` maps a hunk's index to the clause ids its decision is based on; when it
    is supplied, a hunk landing outside them is an error.  It is optional so that a caller
    with no decision context (a hand-written patch file, a test) can still check the quotes.
    """
    errs: list[str] = []
    spans: list[tuple[int, int, int]] = []
    for i, h in enumerate(hunks):
        w = f"patch[{i}]"
        op = h.get("op")
        if op not in OPS:
            errs.append(f"{w}: op {op!r} is not one of {OPS}")
            continue
        cl = h.get("clause")
        if cl not in clause_spans:
            errs.append(f"{w}: clause {cl!r} is not a clause id in the extraction")
            continue
        if allowed_clauses is not None and cl not in allowed_clauses.get(i, set()):
            errs.append(f"{w}: clause {cl!r} is not among the clauses this decision is based "
                        f"on ({sorted(allowed_clauses.get(i, set()))}) -- a repair must land "
                        f"on a sentence the finding came from")
        cs, ce = clause_spans[cl]
        if op == "replace":
            if not isinstance(h.get("span"), list) or len(h["span"]) != 2:
                errs.append(f"{w}: replace needs span [start, end]")
                continue
            s, e = h["span"]
            if not (0 <= s < e <= len(prose)):
                errs.append(f"{w}: span {h['span']} outside the spec (0..{len(prose)})")
                continue
            if prose[s:e] != h.get("original"):
                errs.append(f"{w}: span does not quote the spec byte for byte; "
                            f"prose[{s}:{e}]={prose[s:e][:80]!r} but "
                            f"original={str(h.get('original'))[:80]!r}")
            if not (cs <= s and e <= ce):
                errs.append(f"{w}: span {h['span']} is not inside clause {cl}'s span "
                            f"[{cs}, {ce}]")
            if not isinstance(h.get("replacement"), str):
                errs.append(f"{w}: replace needs a string `replacement`")
            spans.append((s, e, i))
        else:
            at = h.get("at")
            if not isinstance(at, int) or not (0 <= at <= len(prose)):
                errs.append(f"{w}: insert_after needs an offset `at` inside the spec")
                continue
            if not (cs <= at <= ce):
                errs.append(f"{w}: insertion point {at} is not inside clause {cl}'s span "
                            f"[{cs}, {ce}]")
            if not isinstance(h.get("text"), str):
                errs.append(f"{w}: insert_after needs a string `text`")
            spans.append((at, at, i))

    spans.sort()
    for (s1, e1, i1), (s2, e2, i2) in zip(spans, spans[1:]):
        if s2 < e1:
            errs.append(f"patch[{i1}] and patch[{i2}]: hunks overlap at [{s2}, {e1}) -- one "
                        f"sentence gets one rewrite, written by both decisions")
    return errs


def validate_conformance(hunks: list[dict], prose: str) -> list[str]:
    """`validate` for a repair that has no clause behind it, because it had no reading behind it.

    Every check in `validate` survives here except one: the requirement that a hunk name a clause
    in the extraction and land inside it.  That rule enforces "a repair must land on a sentence
    the finding came from", and it is the right rule for a decision -- a rewrite with no sentence
    under it is a rewrite with no argument under it.

    An interface repair has no such sentence, and that is not a weakness in it.  Its basis is the
    port list the harness binds; the defect it corrects is precisely that the prose contains NO
    clause saying the thing.  `radix2_div`'s `res_ready` cannot land inside a clause about
    `res_ready` because the specification has none -- that absence is the defect.  Demanding one
    would make the rule unsatisfiable for exactly the case it exists to handle.

    So the clause rule is dropped and everything that checks the edit against the document is
    kept: the quote must be byte-exact, the span must be inside the prose, and no two hunks may
    rewrite overlapping text.  These are the checks that catch a broken extractor, which is the
    failure this gate is actually guarding against at step 00 -- a bad conformance hunk there
    would corrupt the document every later step reads.
    """
    errs: list[str] = []
    for i, h in enumerate(hunks):
        w = f"conformance[{i}]"
        if h.get("op") != "replace":
            errs.append(f"{w}: op {h.get('op')!r} -- a conformance repair rewrites a span it "
                        f"quotes, so that the quote is checkable")
            continue
        if not isinstance(h.get("span"), list) or len(h["span"]) != 2:
            errs.append(f"{w}: replace needs span [start, end]")
            continue
        s, e = h["span"]
        if not (0 <= s < e <= len(prose)):
            errs.append(f"{w}: span {h['span']} outside the spec (0..{len(prose)})")
            continue
        if prose[s:e] != h.get("original"):
            errs.append(f"{w}: span does not quote the spec byte for byte; "
                        f"prose[{s}:{e}]={prose[s:e][:80]!r} but "
                        f"original={str(h.get('original'))[:80]!r}")
        if not isinstance(h.get("replacement"), str):
            errs.append(f"{w}: replace needs a string `replacement`")
    return errs + overlaps(hunks)


def supersede(hunks: list[dict]) -> tuple[list[dict], list[dict]]:
    """Later rounds' rewrites of a sentence an earlier round already rewrote.

    Every round reads the same original prose, so every round's spans mean the same thing and the
    decided prose is the original with all of them applied.  That arrangement was written for
    rounds that repair different sentences, and it has no way to express the case that a second
    round exists to produce: a repair the next round's evidence shows was wrong.

    It happens, and it is the method working rather than failing.  On `accu`, round 1 adjudicated
    a contradiction by rewriting a sentence to say the four accumulated values are "the 4 most
    recently received"; round 2's property check then proved that reading breaks
    `valid_out_single_cycle`, because a sliding window pulses on every cycle after the fourth,
    and round 2 rewrote the same sentence to say "the 4 received since the last output".  Two
    hunks, one span, and the later one is the answer.  Handed to `apply` they interleave into
    nonsense; handed to `overlaps` they are refused and no specification is emitted at all.

    So a hunk that rewrites EXACTLY the span an earlier hunk rewrote supersedes it.  Exactly is
    the whole rule: both hunks quote the same original bytes, so they are addressing the same
    sentence, and the later round's replacement is that sentence's current text.  A PARTIAL
    overlap is left to `overlaps` and stays an error -- there neither hunk's quote is the text
    the other left behind, and no composition of the two is defined.

    Returns `(kept, superseded)`.  The dropped hunks are returned rather than discarded because a
    reader of the decided prose cannot see them: the sentence carries one rewrite and nothing in
    it says a round wrote a different one first, which is a fact about the run worth keeping.
    """
    by_span: dict[tuple, list[dict]] = {}
    for h in hunks:
        if h.get("op") != "replace":
            continue
        by_span.setdefault(tuple(h["span"]), []).append(h)
    dropped: list[int] = []
    superseded: list[dict] = []
    for span, group in by_span.items():
        if len(group) < 2:
            continue
        # Order by round, then by position in the list, so "later" means what it says even for
        # two hunks the same round wrote -- which `validate` has already refused, but this
        # function does not get to assume it ran.
        order = sorted(group, key=lambda h: (h.get("round") or 0, hunks.index(h)))
        winner = order[-1]
        for h in order[:-1]:
            dropped.append(id(h))
            superseded.append({"span": list(span), "by_round": winner.get("round"),
                               "by_decision": winner.get("decision"),
                               "round": h.get("round"), "decision": h.get("decision"),
                               "replacement": h.get("replacement")})
    return [h for h in hunks if id(h) not in dropped], superseded


def overlaps(hunks: list[dict]) -> list[str]:
    """The overlap rule alone, over hunks that have each already been validated.

    `validate` checks one round's hunks against one round's clause spans.  A multi-round case
    applies every round's hunks to the *same* original prose, and the pair that crosses can be
    one round-1 hunk and one round-3 hunk -- neither round can see it, because each was checked
    on its own.  So the rule is available separately, keyed by whatever label the caller put on
    the hunk (`round`, `decision`) rather than by an index into a list the reader never saw.

    Across rounds the caller runs `supersede` first, so an exact repeat of a span is already gone
    by the time this sees the list and what remains to catch is the partial cross -- two rounds
    editing texts that share some bytes and not others, which no order of application composes.
    Called directly, on one round's hunks or on step 00's conformance repairs, nothing has been
    superseded and an exact repeat is caught here like any other.
    """
    errs: list[str] = []
    spans = []
    for h in hunks:
        s = h["span"][0] if h.get("op") == "replace" else h.get("at")
        e = h["span"][1] if h.get("op") == "replace" else h.get("at")
        if s is None:
            continue
        spans.append((s, e, h))
    spans.sort(key=lambda t: (t[0], t[1]))
    for (s1, e1, h1), (s2, e2, h2) in zip(spans, spans[1:]):
        if s2 < e1:
            errs.append(f"{_label(h1)} and {_label(h2)} rewrite overlapping text at "
                        f"[{s2}, {e1}) -- one sentence gets one rewrite, and two rounds "
                        f"editing it means the later round is repairing the earlier round's "
                        f"repair against a copy of the prose that no longer says that")
    return errs


def _label(h: dict) -> str:
    r = h.get("round")
    d = h.get("decision") or h.get("clause")
    return f"round {r}'s {d!r}" if r is not None else f"{d!r}"


def apply(prose: str, hunks: list[dict]) -> tuple[str, list[dict]]:
    """Apply validated hunks.  Returns the new prose and a per-hunk record of what moved.

    The record carries both offsets -- where the hunk was in the original and where its text
    ends up in the result -- so the modified specification can be diffed against the original
    without re-deriving the alignment.
    """
    ordered = sorted(range(len(hunks)),
                     key=lambda i: (hunks[i]["span"][0] if hunks[i]["op"] == "replace"
                                    else hunks[i]["at"]))
    out = prose
    # Applied back to front so that each hunk's recorded offsets are still the offsets of the
    # text it is about; the shift accumulated by later hunks is then added afterwards.
    shifts: dict[int, int] = {}
    for i in reversed(ordered):
        h = hunks[i]
        if h["op"] == "replace":
            s, e = h["span"]
            out = out[:s] + h["replacement"] + out[e:]
            shifts[i] = len(h["replacement"]) - (e - s)
        else:
            at = h["at"]
            out = out[:at] + h["text"] + out[at:]
            shifts[i] = len(h["text"])

    record, delta = [], 0
    for i in ordered:
        h = hunks[i]
        s = h["span"][0] if h["op"] == "replace" else h["at"]
        e = h["span"][1] if h["op"] == "replace" else h["at"]
        new = h["replacement"] if h["op"] == "replace" else h["text"]
        record.append({"index": i, "op": h["op"], "clause": h["clause"],
                       "decision": h.get("decision"), "round": h.get("round"),
                       "original_span": [s, e], "original": prose[s:e],
                       "new_span": [s + delta, s + delta + len(new)], "new": new,
                       "delta_bytes": shifts[i]})
        delta += shifts[i]
    return out, record


def unified(before: str, after: str, name_a: str = "spec.txt",
            name_b: str = "spec.decided.txt") -> str:
    """A unified diff of the two specifications, for the report.

    `difflib` rather than `diff(1)` because this has to work with no subprocess and no
    temporary files: the modified specification exists in memory before it exists on disk, and
    the diff is part of the step's output, not a thing produced afterwards.
    """
    import difflib
    return "".join(difflib.unified_diff(before.splitlines(keepends=True),
                                        after.splitlines(keepends=True),
                                        fromfile=name_a, tofile=name_b))
