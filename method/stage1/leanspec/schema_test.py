"""Regression cases for the `Partial.lean` readers, all found the same way.

`python3 -m leanspec.schema_test`

Stage 2 writes a Lean file and something reads it back.  For a long time that something was
three separate regexes — `schema.check_partial` for the structural obligations, `emit.cfg_fields`
for the coordinates `decidedCfg` must be total over, and `emit.pin_options` for the menu the
designer is shown — none of which elaborated anything, and the first complete run of `accu` broke
all three in ways that no amount of reading the specification would have surfaced:

* a doc comment's continuation line parsed as a `Cfg` field, inventing a coordinate;
* `def properties` written as the last declaration in the file was reported as missing;
* seven properties of the wrong type passed the check whose error message names the type.

The third was pinned here for a while as *known and unfixed*, on the argument that tightening the
regex to check the type would make it a worse version of the elaborator.  That argument was
right about the regex and wrong about the conclusion: the answer is not a better regex, it is to
stop reading the file and hand the obligations to the elaborator as Lean.  `check_partial` now
appends one declaration per obligation to the case file and elaborates it, so the case below
asserts the type IS checked — and three more assert what only that arrangement can see: a
coordinate stage 2 invented, a `cfgPins_` menu built by `.map` rather than by literal pairs, and
the difference between a name that is missing and a name that is there at the wrong type.

`emit.cfg_fields` is still a parser, because it needs each coordinate's type and default *as
written* and only the source has those.  What changed is that it is no longer the authority on
which fields exist: it is handed the elaborated environment's list and drops anything else.

The shared property of all of these: the file is syntactically fine, Lean is happy, and a regex
disagrees.  That is not a class of bug an author can diagnose from the error it produces, which
is why they are worth a test rather than a comment.

`GOOD` must elaborate.  That is not decoration — every case here now runs Lean over it, so a
fixture that only looked like Lean would make the whole file assert nothing.
"""
from __future__ import annotations

import json
import sys

from leanspec import emit, pipeline, schema

EXT = {
    "design": "t",
    "choices": [{"name": "k", "candidates": [{"tag": "a"}, {"tag": "b"}], "default": "a"}],
    "holes": [{"name": "h", "candidates": [{"tag": "0"}, {"tag": "1"}]}],
    "properties": [{"name": "p", "expressible": True},
                   {"name": "q", "expressible": False}],
}

# Everything `check_partial` demands, in the order stage 2's passes write it, with the two
# shapes that used to be misread put deliberately where they used to break.
GOOD = '''\
import LeanSpec

open LeanSpec

inductive Kk where
  | a
  | b
  deriving DecidableEq, Repr

structure Cfg where
  /-- The fork.  This doc comment is two lines on purpose, and its second line is a name, a
  colon and some text -- which is also what a field looks like. -/
  c_k : Kk := .a
  /-- The hole.  Closed
  domain: strictly between 0 and 4. -/
  h_h : Option Nat := none
  deriving DecidableEq, Repr

structure Ctx where x : Nat deriving DecidableEq, Repr
structure Obs where y : Nat deriving DecidableEq, Repr

def ctxUniverse : List Ctx := [{ x := 0 }]
def obsUniverse : List Obs := [{ y := 0 }]
def ctxCost : Ctx -> Nat := fun _ => 0
def legal : Ctx -> Bool := fun _ => true
def admits : Cfg -> Ctx -> Obs -> Bool := fun _ _ _ => true
def ctxJson : Ctx -> String := fun _ => "{}"
def ctxLean : Ctx -> String := fun _ => "{}"
def obsJson : Obs -> String := fun _ => "{}"
def defaultCfg : Cfg := {}

def case : Case Ctx Obs :=
  { ctxs := ctxUniverse, obs := obsUniverse, legal := legal, cost := ctxCost,
    ctxJson := ctxJson, ctxLean := ctxLean, obsJson := obsJson }

def cfgPins_h : List (String × Cfg) :=
  [("0", defaultCfg), ("1", defaultCfg)]

def prop_p : Property Ctx Obs :=
  { name := "p", ante := fun _ => true, holds := fun _ _ => true }

def properties : List (Property Ctx Obs) :=
  [prop_p]
'''

# The decided extraction, reduced to the seven keys `validate_extraction` insists on before it
# will look at anything else.  Everything the decision cases below assert on is a substring of
# one error, so this document does not have to be otherwise valid -- which is deliberate: a
# fixture built well enough to pass every *other* check would be a second thing to maintain, and
# these cases are about which decision kinds exist, not about clause provenance.
DECIDED = {"design": "t", "source": "test", "clauses": [], "choices": [], "holes": [],
           "properties": [], "ports": []}
PROSE = ""


def cases() -> list[tuple[str, bool]]:
    """`(label, passed)` for each regression, evaluated eagerly so a raise is a failure."""
    out = []

    # 0. The fixture is a Lean file.  Everything below asks the elaborator about it, so a
    #    fixture that did not elaborate would turn every case here into a vacuous pass.
    out.append(("the fixture elaborates", schema._report(GOOD, EXT)["broken"] == []))

    # Driver-generated wiring must not assume an authored `open LeanSpec`.
    no_open = GOOD.replace("open LeanSpec\n", "").replace(
        "Property Ctx Obs", "LeanSpec.Property Ctx Obs")
    start = no_open.index("def case :")
    end = no_open.index("def cfgPins_h", start)
    no_open = no_open[:start] + no_open[end:]
    no_open += "\n" + emit.case_stanza(no_open)
    out.append(("generated Case wiring elaborates without open LeanSpec",
                schema._report(no_open, EXT)["broken"] == []))

    # 1. `def properties` is the LAST declaration.  The body regex terminated only on a line
    #    starting with a non-space character, so at end of file it matched nothing and the
    #    declaration sitting right there was reported missing.  `emit.py` had already been
    #    fixed with `|\\Z` and the other four sites had not, which is what makes it an
    #    incomplete edit rather than a decision.
    out.append(("properties last in file is found", schema.check_partial(GOOD, EXT) == []))

    # ...and it is still found with something after it, which is the case that always worked.
    out.append(("properties mid-file is found",
                schema.check_partial(GOOD + "\n#eval 1\n", EXT) == []))

    # 2. A doc comment's continuation line is not a `Cfg` coordinate.  `derive` is total over
    #    this list, so a phantom here is a hard error at step 07 naming a field no decision
    #    could ever mention -- and it would point at the decisions.
    fields = emit.cfg_fields(GOOD)
    out.append(("cfg_fields ignores block comments",
                [f["field"] for f in fields] == ["c_k", "h_h"]))
    out.append(("cfg_fields keeps kind and default",
                [f["kind"] for f in fields] == ["choice", "hole"]
                and fields[0]["default"] == ".a" and fields[1]["default"] == "none"))

    # ...and the class is closed rather than the instance: handed the elaborated environment's
    # field list, the parser cannot report a coordinate Lean has never heard of, whatever the
    # comment above it looks like.
    out.append(("cfg_fields is bounded by the environment",
                schema.cfg_field_names(GOOD, EXT) == ["c_k", "h_h"]
                and [f["field"] for f in emit.cfg_fields(
                    GOOD.replace("  h_h : Option Nat := none",
                                 "  h_h : Option Nat := none\n  -- ghost : Nat := 0"),
                    ["c_k", "h_h"])] == ["c_k", "h_h"]))

    # 3. A missing aggregate is still reported, and named.  This is the error the first
    #    complete run actually drew, and the one the pass prompt now asks for.
    no_agg = GOOD.replace("def properties : List (Property Ctx Obs) :=\n  [prop_p]\n", "")
    out.append(("a missing `properties` is still an error",
                schema.check_partial(no_agg, EXT)
                == ["Partial.lean: no `def properties : List (Property Ctx Obs)`"]))

    # ...as is one that omits a property it should hold: `allEntailed` over a list without it
    # returns true, so the guarantee would read as checked and never have been.  Read off the
    # definition's VALUE now rather than off its source text, so a `prop_` named in a comment
    # beside the list no longer counts as listed.
    empty = GOOD.replace("[prop_p]", "[]")
    out.append(("`properties` omitting an entry is an error",
                any("not in `properties`" in e for e in schema.check_partial(empty, EXT))))
    out.append(("a `prop_` named only in a comment is not listed",
                any("not in `properties`" in e for e in schema.check_partial(
                    GOOD.replace("[prop_p]", "[]  -- prop_p"), EXT))))

    # 4. An inexpressible property must NOT be demanded.  Asking for one pushes stage 2 into
    #    writing the approximation the `expressible: false` declaration exists to refuse.
    out.append(("an inexpressible property is not demanded",
                not any("prop_q" in e for e in schema.check_partial(GOOD, EXT))))

    # 5. WAS KNOWN AND UNFIXED: the type in the error message is now the type that is checked.
    #    Seven folded `Cfg -> Ctx -> Obs -> Bool` predicates passed this gate on the real run,
    #    and the reason they could is gone -- the obligation is `example : Property Ctx Obs :=
    #    prop_p`, appended to the file and elaborated, so the message and the check are the
    #    same sentence.
    wrong = GOOD.replace(
        'def prop_p : Property Ctx Obs :=\n  { name := "p", ante := fun _ => true, '
        'holds := fun _ _ => true }',
        "def prop_p (_cfg : Cfg) (_c : Ctx) (_o : Obs) : Bool := true").replace(
        "[prop_p]", "[]")
    out.append(("the wrong prop_ type is rejected, at the type the message names",
                any("`prop_p` is not a `Property Ctx Obs`" in e
                    for e in schema.check_partial(wrong, EXT))))

    # ...and a name that is absent is still told apart from a name that is present at the wrong
    #    type, because they are different repairs.
    absent = GOOD.replace("def prop_p", "def prop_pp").replace("[prop_p]", "[prop_pp]")
    out.append(("a missing prop_ says missing, not mistyped",
                any("no `def prop_p : Property Ctx Obs`" in e
                    for e in schema.check_partial(absent, EXT))))

    # 5b. What the type hole actually let through, and what is checked instead.  On the real run
    #     the folded predicates did not reach `properties` bare -- they reached it wrapped:
    #
    #         def asProperty (name) (ante) (p : Cfg -> Ctx -> Obs -> Bool) : Property Ctx Obs :=
    #           { name := name, ante := ante,
    #             holds := fun c o => propReadings.any (fun cfg => p cfg c o) }
    #
    #     Every earlier check passes -- each `def prop_<name>` exists, each name appears in the
    #     list, the result is genuinely a `Property Ctx Obs` -- and the meaning is gone: `holds`
    #     now says "true under SOME candidate reading", so `emitPropertyPin` varies candidates
    #     against a claim that already contains them and `survivors` measures nothing.  This is
    #     the one obligation that did NOT move to the elaborator, and the reason is exact:
    #     `asProperty "p" ante prop_p` and `prop_p` have the same type, so there is no Lean
    #     question whose answer separates them.  The SHAPE is required because the shape is what
    #     carries the meaning and it is exactly checkable.
    wrapped = GOOD.replace("[prop_p]", '[asProperty "p" (fun _ => true) prop_p]')
    out.append(("a wrapped `properties` entry is rejected",
                any("not `prop_` declarations" in e
                    for e in schema.check_partial(wrapped, EXT))))

    # ...and the shape the prompt asks for is accepted however it is laid out, so the rule is
    # about the entries and not about whitespace.
    spread = GOOD.replace("[prop_p]", "[\n    prop_p,\n  ]")
    out.append(("a bare list spread over lines is accepted",
                schema.check_partial(spread, EXT) == []))

    # 5c. A MENTION of `decidedCfg` is not a definition of one.  Step 02 forbids a hand-written
    #     `decidedCfg`, and the test was `"decidedCfg" in src` — so the second `accu` sweep, which
    #     wrote none and said so in a doc comment ("`decidedCfg` is *not* written here in any
    #     pass"), was told "Partial.lean defines `decidedCfg`".  Nothing an author can do fixes
    #     that: the artifact was right, the message named a declaration that did not exist, and the
    #     only edit that clears it is deleting the sentence that shows they understood the rule.
    #     `_strip_decided_cfg` had always anchored at line start; only the gate had not.
    mentions = GOOD.replace("import LeanSpec",
                            "import LeanSpec\n\n/-- `decidedCfg` is not written here in any pass;\n"
                            "step 08 derives it from the decision record. -/", 1)
    out.append(("a doc comment mentioning decidedCfg is not a definition",
                not pipeline._DEFINES_DECIDED_CFG.search(mentions)))
    out.append(("a real decidedCfg definition is still caught",
                bool(pipeline._DEFINES_DECIDED_CFG.search(
                    mentions + "\ndef decidedCfg : Cfg := { c_k := .a }\n"))))

    # 5d. `kind: "property"` is a decision the author is TOLD to write and the decided-extraction
    #     checker refused.  `author.py`'s stage 7 prompt names it, `pipeline.py`'s step 07
    #     validates it against step 04's certified pin, and only `validate_extraction` had never
    #     heard of it -- so a run that earned a property pin would produce a decision no edit
    #     could make acceptable: drop it and a settled fork is lost, keep it and the extraction
    #     fails.  It did not fire on `accu` only because step 04 certified no pin there, and the
    #     author's *unearned* property decision was caught by the check that should have caught
    #     it, one line above the one that should not have.
    dec = dict(DECIDED)
    dec["decisions"] = [{"kind": "property", "name": "k", "resolved_to": "a", "witness": None,
                         "evidence": "the prose's own guarantee", "round": 1}]
    out.append(("a property decision is a decision",
                not any("is not choice|hole" in e
                        for e in schema.validate_extraction(dec, PROSE))))

    # ...and it closes the fork it decided, exactly as a `choice` does.  Left in `choices`, the
    # question is put to the designer again next round, with a query, having been answered free.
    still = dict(dec)
    still["choices"] = [{"id": "K1", "name": "k", "candidates": [{"tag": "a", "reading": "r"},
                                                                 {"tag": "b", "reading": "r"}],
                         "default": "a", "basis": ["C1"], "question": "?"}]
    out.append(("a property-decided fork may not stay open",
                any("still open in `choices`" in e
                    for e in schema.validate_extraction(still, PROSE))))

    # ...and a kind nobody defined is still refused, so this is a fourth kind and not an opening.
    bogus = dict(dec)
    bogus["decisions"] = [dict(dec["decisions"][0], kind="vibes")]
    out.append(("an undefined decision kind is still refused",
                any("is not choice|hole" in e
                    for e in schema.validate_extraction(bogus, PROSE))))

    # 6. The cross-checks that must keep firing.  A fork that vanishes between stage 1 and
    #    stage 2 is the failure this whole check exists for.
    out.append(("a missing Cfg field is an error",
                any("no field `c_k`" in e for e in
                    schema.check_partial(GOOD.replace("c_k : Kk := .a", "c_kk : Kk := .a"),
                                         EXT))))
    out.append(("a disagreeing enum is an error",
                any("extraction.json says" in e for e in
                    schema.check_partial(GOOD.replace("  | b\n", ""), EXT))))
    out.append(("a disagreeing pin menu is an error",
                any("cfgPins_h` offers" in e for e in
                    schema.check_partial(GOOD.replace('("1", defaultCfg)',
                                                      '("2", defaultCfg)'), EXT))))
    out.append(("a missing core declaration is an error",
                any("no declaration of `admits`" in e for e in
                    schema.check_partial(GOOD.replace("def admits", "def adm1ts"), EXT))))

    # 7. The three the regex could not have asked, in either direction.
    #
    #    A coordinate stage 2 invented.  `decidedCfg` is total over `Cfg`, so an undeclared
    #    field is an assignment no query justified at a coordinate no answer names -- and the
    #    old check looked only for declared fields that were missing, never for present fields
    #    that were undeclared.
    ghost = GOOD.replace("  h_h : Option Nat := none",
                         "  h_h : Option Nat := none\n  c_phantom : Bool := false")
    out.append(("an undeclared Cfg coordinate is an error",
                any("does not declare" in e for e in schema.check_partial(ghost, EXT))))

    #    A `cfgPins_` written as a `.map` over a value list carries no labels in its source, so
    #    the regex skipped it and the menu the designer would be shown went unchecked.  `#eval`
    #    runs the definition instead of looking at it, so the form no longer matters.
    mapped = GOOD.replace('[("0", defaultCfg), ("1", defaultCfg)]',
                          '(["0", "2"]).map (fun v => (v, defaultCfg))')
    out.append(("a computed pin menu is checked, not skipped",
                any("cfgPins_h` offers" in e for e in schema.check_partial(mapped, EXT))))

    #    And a case file that does not elaborate says so, in the half of the verdict that is
    #    not `property_problems` -- which is what makes `author._owner_of` refuse to blame
    #    pass 8 for it and drop the whole record instead.
    broke = GOOD.replace("def ctxCost : Ctx -> Nat := fun _ => 0",
                         "def ctxCost : Ctx -> Bool := fun _ => true")
    out.append(("a file that does not elaborate is reported as that",
                any("does not elaborate" in e for e in schema.check_partial(broke, EXT))
                and not any("does not elaborate" in e
                            for e in schema.property_problems(broke, EXT))))
    return out


def main() -> int:
    # Evaluated once and held.  Every case here now runs `lean`, so the old `len(cases())` in
    # the closing line was a second full sweep -- about a minute of elaboration to print a
    # number the first sweep already had.
    got = cases()
    bad = [label for label, ok in got if not ok]
    for label, ok in got:
        print(f"  {'ok ' if ok else 'BAD'}  {label}")
    if bad:
        print(f"\n{len(bad)} case(s) wrong:")
        for label in bad:
            print(f"  {label}")
        return 1
    print(f"\nschema: all {len(got)} cases hold — the obligations are asked of the elaborator, "
          f"and the cross-checks still fire")
    return 0


if __name__ == "__main__":
    sys.exit(main())
