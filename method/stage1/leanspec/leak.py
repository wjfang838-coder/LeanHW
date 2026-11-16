#!/usr/bin/env python3
"""The leak scanner: names that could only have come from somewhere the run could not see.

This is an **audit tool and not a pipeline step**, which is a change of position rather than of
method.  In the tree this comes from it ran inside the pipeline, because the pipeline had a
ground-truth step to run it against.  leanSpec has no such step: it carries no reference
implementation, no testbench and no benchmark data, so there is nothing in the run to compare an
artifact against and the scanner has no place in the chain.

It is still worth having, and it is still worth having *here*, because the claim it checks is not
about this repository — it is about a benchmark's own checkout, which an adapter reaches at run
time.  Whoever audits a run names the reference on the command line; the scanner reports what it
finds; and the report is a heuristic and says so.  It cannot prove an agent did not look.  What it
catches is the thing that actually happens when one does: a reference's private identifier — an
internal register, a helper module, a state encoding — turning up in an artifact that was supposed
to be derived from the prose alone.

Everything below the vocabulary tables is carried over unchanged, including every stated cost.
The subtractions are the whole design of this scanner and each one is a decision someone can
disagree with; a subtraction whose price is not written down is a hole.
"""
from __future__ import annotations

import glob
import json
import os
import re

_COMMON = set("""
clk clock rst rst_n reset resetn en enable valid ready data in out i o a b c d q x y z sum
module endmodule input output wire reg assign always begin end if else case default posedge
negedge parameter localparam integer genvar generate for while function endfunction task
signed unsigned initial forever repeat and or not xor nand nor buf bufif notif tri wand wor

def import from class return try except raise with lambda async await yield assert elif pass
none true false self int str list dict tuple bool print len range enumerate zip map filter
sorted random randint choice getattr setattr format join append extend items keys values

cocotb dut coroutine simulator runner test_runner harness_library pytest parametrize
risingedge fallingedge timer clockcycles readonly nextTimeStep triggers regression decorators
binary binaryvalue logicarray deque collections os sys pathlib subprocess plusargs waves
build_dir hdl_toplevel toplevel toplevel_lang verilog_sources sim get_runner
clean sources build_args parameters timescale log_file verbose test_module test_dir seed unit
fs ps ns us ms py sv vh svh tb ro as
""".split())


def _identifiers(text: str) -> set[str]:
    """Identifiers of two characters or more, minus the vocabulary every design shares.

    Two and not three.  A three-character floor is quieter, and it is quiet in the wrong place:
    a reference's private registers are routinely named `a0`, `d1`, `s1`, and those are exactly
    the names whose appearance in a stage-1 artifact would be evidence.  Three of the twelve
    cases had an *empty* private set under the old floor -- `rtllm/edge_detect` (whose reference's
    only private name is `a0`) and `rtllm/parallel2serial` (`d0`, `d1`, `d3`) among them -- which
    means their leak scans could not have reported a leak whatever the artifacts contained.
    Lowering it admits ten real register names across the corpus and five tokens that are not
    names at all: the timescale units and the file-extension fragments the CVDP harness paths
    are made of, added to `_COMMON` above.
    """
    return {w for w in re.findall(r"[A-Za-z_][A-Za-z_0-9]{1,}", text)} - _COMMON


# Ordinary English words that a reference is also free to use as a wire name.  These are
# subtracted from the *private* set only -- that is, from the evidence side, never from the
# artifact side -- because the claim the scanner makes is "this name is distinctive enough that
# finding it in a stage-1 artifact means the agent read the reference".  A bare English word is
# not distinctive: an agent writing `starts the next attempt` in a comment collides with a
# reference that happens to name a wire `next`, and reporting that as a leak costs more than it
# catches.  The cost is real and is stated rather than hidden: if a reference's only private
# identifier is one of these, a genuine leak of it goes unreported.  Compound names -- the
# `next_state`, `state_reg`, `shift_cnt` a leak actually looks like -- are untouched.
#
# The list grew once, and it is worth saying why.  RealBench's references `include` a header
# shared by a whole design family, so a clock divider's ground truth carries the SD controller's
# vocabulary: `bit_crc_cycle` and `sdc_clk_static`, which are distinctive, but also `read`,
# `per`, `transfer`, `max`, `defines`, which are not.  Widening the evidence set to make the
# oracle compile widened this set too, and the words below are the ordinary-English residue of
# that, not a patch fitted to one case's three hits.
_ENGLISH = set("""
next previous last first current new old value values set clear hold count counter index
state states step steps bit bits byte bytes word words high low true false zero one two
found done ready start stop run running result results temp tmp buffer flag flags shift
read write reads writes send recv per each all any add sub inc dec max min equal
change changed changing define defines defined internal external custom simulator simulation
documentation transfer transfers mode modes size length width depth level type kind
test tests testbench check checks expect expected assert asserts stream streams window windows
""".split())


_PY_SKIP = re.compile(r"""(?xs)
      \#[^\n]*
    | [rRbBuUfF]{0,3}\"\"\".*?\"\"\"
    | [rRbBuUfF]{0,3}'''.*?'''
    | [rRbBuUfF]{0,3}\"(?:\\.|[^\"\\\n])*\"
    | [rRbBuUfF]{0,3}'(?:\\.|[^'\\\n])*'
""")

_V_SKIP = re.compile(r"""(?xs)
      //[^\n]*
    | /\*.*?\*/
    | \"(?:\\.|[^\"\\\n])*\"
    | \d[\w]*\s*'\s*[sS]?[bBoOdDhH][0-9a-fA-FxXzZ?_]+
    | '\s*[sS]?[bBoOdDhH][0-9a-fA-FxXzZ?_]+
""")


def _strip_noncode(name: str, src: str) -> str:
    """Comments and string literals removed, so that a reference's *identifiers* are what is
    compared.

    Applied to the ground-truth side only.  A reference is code and a header is often mostly
    English: `e203_defines.v` runs to thousands of lines of commentary, and reading its words
    as identifiers makes `since`, `unless` and `well` count as the reference's private names.
    An agent writing an ordinary English sentence then trips the detector, which is a false
    alarm expensive enough to make the whole scan worthless.

    String literals are removed for the same reason and it is a distinct one, so it is worth
    stating.  A cocotb harness's assertion message -- `f"Error: clk_out period {p} ns does not
    match expected {e}"` -- is English prose that happens to live inside quotes, and every word
    of it was arriving in the evidence set as one of the reference's private identifiers.  That
    is what a `$display` string is too.  The words in a diagnostic message are not names of
    anything in the design.

    Verilog's *based literals* go with them, and they are the third distinct reason.  `'d0`,
    `1'b0`, `4'hFF` are numbers, but `'` is not an identifier character, so a tokenizer reading
    the text left to right hands back `d0`, `b0` and `hFF` -- and those then enter the evidence
    set as private names of the design.  They are not names of anything.  `rtllm/parallel2serial`
    was reported as leaking `d0` into its `Partial.lean` on exactly this: the reference writes
    `data <= 'd0`, the Lean file binds a lambda variable `d0`, and the two have nothing to do
    with each other.  Deleting the literal keeps the register beside it -- `reg a0;` in
    `edge_detect` is still a name, and still evidence.

    The syntax is chosen by extension rather than applied together, and that is not fussiness.
    `#` opens a comment in Python and opens a *parameter list* in Verilog: running the Python
    rule over `module foo #(parameter N = 3) (` would delete the rest of the line, and with it
    the parameter names -- quietly shrinking the set of things a leak could be caught on.  A
    scanner that under-reports is worse than one that over-reports, because nobody looks at it
    again.  Files with neither extension are left alone.  Comments and strings are one
    alternation rather than two passes, so a `#` inside a string cannot open a comment and a
    quote inside a comment cannot open a string.

    What this costs, precisely: a name that occurs in the reference *only* inside a string --
    a cocotb harness reaching an internal signal through `getattr(dut, "state_reg")` and
    nowhere else -- is no longer evidence, so a leak of that one name would go unreported.
    That is a narrower hole than the alternative, which is an ever-growing list of English
    words fitted to whichever case last false-alarmed.  An f-string's interpolations are lost
    with the rest of the literal, but the names inside them are bound elsewhere in the file and
    survive there.

    The artifact side keeps its comments and its strings, deliberately: a leaked name written
    into a Lean docstring is still a leaked name, and that is the side the claim is about.
    """
    ext = os.path.splitext(name)[1].lower()
    if ext in (".v", ".sv", ".vh", ".svh", ".verilog"):
        return _V_SKIP.sub(" ", src)
    if ext in (".py", ".pyi"):
        return _PY_SKIP.sub(" ", src)
    return src



def clause_ids(case_dir: str) -> set[str]:
    """Every clause identifier this case declares, in any round.

    These are the framework's own addressing scheme -- `C1` is "the first sentence the extraction
    cut out of the prose" -- and they are written into `Partial.lean`'s docstrings, into
    `decisions.json`'s patch hunks and into every step document that carries an extraction.  They
    are not names of anything in any design, and a case declares them before it has looked at
    anything.  `leak_scan` subtracts them for that reason; see the cost stated there.
    """
    out: set[str] = set()
    seen: set[str] = set()
    for pat in ("authored/round*/extraction.json", "rounds/round*/extraction.json",
                "state/extraction.json", "extraction.json"):
        for p in glob.glob(os.path.join(case_dir, pat)):
            rp = os.path.realpath(p)
            if rp in seen:
                continue
            seen.add(rp)
            try:
                doc = json.load(open(p, errors="replace"))
            except (OSError, ValueError):
                continue
            for c in doc.get("clauses") or []:
                if isinstance(c, dict) and isinstance(c.get("id"), str):
                    out.add(c["id"])
    return out


def schema_vocabulary(docs: dict[str, str], filenames: tuple[str, ...] = ()) -> set[str]:
    """The framework's own words in documents the framework wrote: the object keys of its step
    schema, and the names of the files it emits.

    This exists for the same reason `clause_ids` does and it is drawn the same way -- from the
    framework, not from a list fitted to whichever case last false-alarmed -- but it applies to a
    narrower scan.  `cli.audit` runs `leak_scan` twice.  The first pass scans the *artifacts*, and
    that is the claim about what the agent wrote; nothing here is subtracted from it, because an
    agent has no occasion to write the pipeline's field names into an extraction and if it did
    that would be worth seeing.  The second pass scans the *step documents*, and that is the claim
    about what the pipeline carried.  A step document is generated: `pipeline.py` writes
    `"diff": ""` into step 07 whether the prose was patched or not, and lists `out/spec.diff`
    among the files it materialised, and it does so with no reference to anything the agent or
    the reference contains.

    `rtllm/comparator_4bit` is what surfaced it.  Its reference computes `A - B` into a wire it
    calls `diff`, which is the obvious name for it, and the prose never uses that word -- so
    `diff` is a private identifier, correctly.  The scan then reported it in step 07, twice, on
    the schema key and the filename, and nothing an author could write would remove either.  A
    scanner that reports a leak in a field the scanner's own harness emitted is reporting on
    itself.

    The cost is the same shape as the one `clause_ids` pays and it is smaller: if a reference's
    private signal is named exactly like one of the pipeline's schema keys or like a fragment of
    one of its output filenames -- `diff`, `span`, `reading`, `decided` -- a leak of that one
    name goes unreported *in the step documents*.  It is still reported in the artifacts, which
    is where an agent's own writing lives and where the claim actually bites.

    Only keys are taken, never values.  Every name that could be a leak -- a `Cfg` field, a
    candidate tag, a clause's quoted prose -- is a value in this schema, and values are left
    alone.
    """
    out: set[str] = set()

    def walk(node) -> None:
        if isinstance(node, dict):
            for k, v in node.items():
                out.add(k)
                walk(v)
        elif isinstance(node, list):
            for v in node:
                walk(v)

    for text in docs.values():
        try:
            walk(json.loads(text))
        except ValueError:
            continue
    for f in filenames:
        out.update(re.split(r"[^A-Za-z0-9_]+", f))
    return {w for w in out if w}


def leak_scan(prose: str, gt_files: dict[str, str] | str,
              artifacts: dict[str, str], toplevel: str = "",
              reserved: set[str] | None = None) -> dict:
    """Names that occur in the ground truth and in the agent's stage-1/2 output, but not in
    the prose.

    This is a *heuristic* and is reported as one.  It cannot prove an agent did not look; it
    catches the thing that actually happens when one does, which is that a reference's private
    identifier -- an internal register, a helper module, a state encoding -- turns up in an
    artifact that was supposed to be derived from the prose alone.

    `gt_files` is the ground truth keyed by filename so the comment and string syntax can be
    chosen per file; a bare string is accepted and stripped as Verilog, which is what the callers
    that predate the CVDP backend were passing.  What `_strip_noncode` removes from the evidence
    side, and what that costs, is stated there.

    `toplevel` is the module name the harness instantiates, and it is subtracted for a reason
    that is not a concession.  It is build configuration, not a private name: a candidate module
    has to be called that or it does not elaborate, so every agent that emits RTL at all is
    handed it by the manifest before it reads anything.  Most specifications also state it in
    prose -- `The module clock_divider should take an input clock` -- and then it is subtracted
    anyway, by the ordinary rule.  The scan should not report a leak in exactly the cases where
    the specification forgot to name its own module, which is a defect in the specification and
    is filed as one.  The cost is narrow and worth stating: if a reference's toplevel is also the
    name of one of its internal signals, a leak of that name goes unreported.

    `reserved` is the framework's own vocabulary, and it is subtracted for the same kind of reason
    with a narrower cost.  A clause identifier is positional addressing -- `C1` is the first
    sentence the extraction cut out, `C2` the second -- generated before the reference is opened
    and written into the docstrings, the patch hunks and every step document that carries an
    extraction.  The scan tokenizes case-insensitively, so it cannot tell the artifact's `C1` from
    a reference's carry wire `c1`, and carry wires called `c1..c4` are what a hand-written adder
    has: `rtllm/adder_32bit` and `rtllm/adder_pipe_64bit` both reported every clause they cite as
    a leak, in every sealed step, on nothing but that collision.  A scanner that cries wolf on the
    framework's own addressing is a scanner nobody reads.

    The cost is one sentence and it is real: if a reference's private signal is named exactly like
    one of *this case's* clause identifiers -- which in practice means a letter and a digit -- a
    leak of that one name goes unreported.  It is bounded to the identifiers the case actually
    declares, so it does not grow, and it is not a list of words fitted to whichever case last
    false-alarmed.
    """
    if isinstance(gt_files, str):
        gt_files = {"ref.v": gt_files}
    gt_text = " ".join(_strip_noncode(n, s) for n, s in gt_files.items())
    pros, gt = _identifiers(prose.lower()), _identifiers(gt_text.lower())
    private = gt - pros - _ENGLISH - _identifiers(toplevel.lower())
    private -= {r.lower() for r in (reserved or set())}
    hits = {}
    for name, text in artifacts.items():
        found = sorted(private & _identifiers(text.lower()))
        if found:
            hits[name] = found
    return {"private_gt_identifiers": len(private), "hits": hits, "clean": not hits}
