#!/usr/bin/env python3
"""Does the emitted module header carry the interface the SPEC declares?

This module is the extraction half of the interface check, split out of `leanrtl/iface_conform.py`
so that the same code can run in two places that must not disagree: after a run, over its
artifacts, as a scored predictor; and DURING authoring, inside `bb.py emit`, where a mismatch is
still cheap to fix.  A second implementation would drift, and the post-hoc one carries a published
hit rate, so there is one implementation and the authoring loop imports it.

It reads exactly two things: the spec prose the author was given, and the Verilog we ourselves
emitted.  It never opens a testbench.  That is what makes a repair it motivates traceable to the
spec rather than fitted to an answer key -- on a benchmark whose harness IS the ground truth, a
check that consulted the harness would be scoring against the answers.

## Where a declared interface hides in a spec

Five shapes, in descending order of authority:

  1. a fenced ```verilog / ```systemverilog block holding a `module ... (...);` header --
     the spec writing its interface out as code;
  2. a markdown table with a direction column (`| clk | 1 bit | input | System clock |`);
  3. a direction-LED declaration list (` - input  clk`, ` - output q (4 bits)`) -- the spec
     writing its interface out as a list, one pin per line, direction first;
  4. bulleted declarations under an Interface/Inputs/Outputs/Ports/Signals heading;
  5. a Parameters section naming SCREAMING_CASE identifiers.

Three of those are STRUCTURED and are believed: the code header, the direction table and the
direction-led list.  Shape 4 is collected and reported but never flagged: across a benchmark's
worth of prompts a bullet under an "Inputs" heading is as often a sentence as a declaration, and
taking them at face value pulls in headings, example bit patterns and internal net names,
dropping precision to about a third.

Shape 3 is a bulleted list too, and the distinction between it and shape 4 is worth being exact
about, because it is the only thing keeping that precision loss out of the believed set: shape 3
requires the DIRECTION KEYWORD FIRST and the line to end at the name (or at a `(N bits)`
parenthetical).  A sentence cannot do that.  `- valid_a indicates the validity of input data_in`
is shape 4; `- input  valid_a` is shape 3, and one ChipBench prompt contains both.  See
`_DECL_ITEM` and `_decl_list_ports`, and note that shape 3 matches ZERO of RTLLM's 50
descriptions -- promoting it moved no verdict on the benchmark every existing verdict came from.

A sixth thing is read, and it is not an interface: a magnitude the spec NAMES and never gives a
value for -- `ERROR_THRESHOLD`, a limit, a timeout.  It is here rather than in a file of its own
because it is answered by the same two inputs and the same set difference, and because a
testbench that reads such a name is doing exactly what a testbench that binds a port does.  See
`_lone_constants`.

## When the two structured sources DISAGREE

A spec can name the same pin two ways -- one spelling in its signal table, another a few lines
later in its module skeleton.  Neither reading is wrong, and a checker that silently picked one
would hide the defect, so the disagreement is reported as its own field and both spellings are
treated as declared.  The consequence for an author is asymmetric and that asymmetry is the whole
advice: a port the module declares and nothing drives costs nothing, while a port the module
lacks is fatal, because a name-probing testbench cannot bind to a pin that is not there.  So when
the prose conflicts on a NAME, declare both and drive them identically rather than adjudicating.
"""
from __future__ import annotations

import difflib
import os
import re

#: Verilog/SystemVerilog keywords that can appear where a port name would be parsed from.
_KW = {
    "input", "output", "inout", "reg", "wire", "logic", "signed", "unsigned", "parameter",
    "localparam", "integer", "genvar", "bit", "byte", "int", "shortint", "longint", "real",
    "module", "endmodule", "begin", "end", "if", "else", "case", "endcase", "default",
}

#: Headings under which a bulleted list is a port declaration rather than prose.  `interfaces?`
#: rather than `interface`: the `\b` after the group makes the singular fail on `### Interfaces:`,
#: which is how a spec that splits its pins across Control/Input/Output subsections heads them.
_IFACE_HEAD = re.compile(
    r"^\s{0,3}#{1,6}\s*\**\s*(?:\d+\.\s*)?"
    r"(interfaces?|inputs?|outputs?|ports?|signals?|i/?o|pin\s*list|port\s*list)\b",
    re.I | re.M)

#: Headings under which SCREAMING_CASE identifiers are parameters.
_PARAM_HEAD = re.compile(r"^\s{0,3}(?:#{1,6}\s*)?\**\s*(?:\d+\.\s*)?parameters?\b\s*:?\s*\**\s*$",
                         re.I | re.M)

#: A bare `[HI:LO]` / `[W-1:0]` range prefix, stripped before the name is read.
_RANGE = re.compile(r"\[[^\]]*\]")

#: A non-ANSI parameter declaration run: `parameter [signed] [W-1:0] A = 1, B = 2;`.  `\b` keeps
#: it off `localparam`, which is not part of the interface -- a localparam cannot be overridden
#: at elaboration, so its being unread is a dead-code question, not an interface lie.
_NONANSI_PARAM = re.compile(r"\bparameter\b(?!\s*\btype\b)([^;]*);", re.S)


def _ident(tok: str) -> str | None:
    """The identifier in `tok`, or None.  Strips markdown, ranges, and trailing punctuation."""
    t = tok.strip().strip("`*_ ")
    t = _RANGE.sub(" ", t).strip()
    # `[ROW x COL x W -1 : 0] name` and `name[ ... ]` both reduce to a trailing word
    m = re.findall(r"[A-Za-z_]\w*", t)
    if not m:
        return None
    name = m[-1] if not re.match(r"^[A-Za-z_]\w*$", t) else t
    return name if name.lower() not in _KW else None


# --------------------------------------------------------------------------- prose extraction

def _code_headers(text: str, top: str | None = None) -> list[dict]:
    """Module headers written out as code in the prose.  The most authoritative shape.

    Fenced blocks, then -- only when `top` is known -- the raw document, for the indented
    UNFENCED `module TopModule (...);` that three VerilogEval prompts use.  This mirrors
    `contract._code_contract` deliberately and must keep mirroring it: the two readers are the
    same claim about the same document made twice, and a header one of them believes and the
    other does not turns into a phantom `unstructured` entry that reads like a missing pin.
    The `top` gate and the ANSI-only rule below are that function's, for that function's reasons.
    """
    out = []
    scans = [(b, False) for b in re.findall(r"```[^\n]*\n(.*?)```", text, re.S)]
    if top:
        scans.append((text, True))
    for blk, unfenced in scans:
        for m in re.finditer(r"\bmodule\s+([A-Za-z_]\w*)\s*(#\s*\((.*?)\))?\s*\((.*?)\)\s*;",
                             blk, re.S):
            if unfenced and not re.search(r"\b(input|output|inout)\b", m.group(4)):
                continue
            params = set()
            if m.group(3):
                for p in re.finditer(r"\bparameter\b[^,\n]*?([A-Za-z_]\w*)\s*=", m.group(3)):
                    params.add(p.group(1))
                if not params:                       # `#(WIDTH = 8)` with no `parameter` keyword
                    for p in re.finditer(r"([A-Za-z_]\w*)\s*=", m.group(3)):
                        if p.group(1).lower() not in _KW:
                            params.add(p.group(1))
            ports, body = set(), m.group(4)
            for line in body.split(","):
                nm = _ident(line)
                if nm:
                    ports.add(nm)
            out.append({"module": m.group(1), "ports": ports, "params": params})
    return out


def _iface_regions(text: str) -> list | None:
    """Line spans in which a direction table declares THIS module's interface.

    `None` means the document has no interface heading at all to scope by, and every table is
    read -- the shape of a short spec that states its pins in one unlabelled table.

    The scoping exists because a longer spec describes more than one module.  A spec that lists
    the submodules it instantiates gives each of them its own signal table, under a heading like
    `## Submodule List` / `### <name>` / `#### Signal Interface`, and that innermost heading looks
    exactly like an interface heading because it is one -- just not THIS module's.  Unscoped, a
    third of one benchmark's designs were reported as missing forty-odd ports, every one of them a
    submodule pin.

    The rule is structural, not a guess at wording: an interface heading counts unless one of its
    ANCESTORS is a heading that is not itself an interface heading.  A level-1 heading is exempt,
    being the document's own title.  `## Interface` under `# <design> Specification` counts;
    `#### Signal Interface` under `## Submodule List` does not.
    """
    lines = text.split("\n")
    heads = []                                       # (line, level, is_interface_heading)
    for i, l in enumerate(lines):
        m = re.match(r"^\s{0,3}(#{1,6})\s", l)
        if m:
            heads.append((i, len(m.group(1)), bool(_IFACE_HEAD.match(l))))
    if not any(h[2] for h in heads):
        return None
    out = []
    for n, (i, lvl, is_if) in enumerate(heads):
        if not is_if:
            continue
        nested_under_other, cur = False, lvl
        for (_, l2, if2) in reversed(heads[:n]):     # walk outward through the ancestry
            if l2 < cur:
                cur = l2
                if l2 > 1 and not if2:
                    nested_under_other = True
                    break
        if nested_under_other:
            continue
        end = next((j for (j, l2, _) in heads[n + 1:] if l2 <= lvl), len(lines))
        out.append((i, end))
    # Every interface heading in the document turned out to be nested under something else.  That
    # is not a document with no interface tables, it is a document this function did not follow,
    # and returning an empty scope would silently read NOTHING -- strictly worse than the unscoped
    # behaviour it replaced.  Fall back to reading every table, and let the tolerant severities do
    # the rest.
    return out or None


def _table_ports(text: str) -> set:
    """Names from markdown tables that carry a direction column, scoped to this module's own
    interface sections when the document has any."""
    regions = _iface_regions(text)

    def in_scope(ln: int) -> bool:
        return regions is None or any(a <= ln < b for a, b in regions)

    ports = set()
    rows, block, start = [], [], 0
    lines = text.split("\n") + [""]
    for i, line in enumerate(lines):
        if line.strip().startswith("|") and line.count("|") >= 3:
            if not block:
                start = i
            block.append(line)
            continue
        if block:
            rows.append((start, block))
            block = []
    for start, blk in rows:
        if not in_scope(start):
            continue
        cells = [[c.strip() for c in r.strip().strip("|").split("|")] for r in blk]
        cells = [c for c in cells if not all(re.fullmatch(r":?-{2,}:?", x or "-") for x in c)]
        if len(cells) < 2:
            continue
        head = [c.lower() for c in cells[0]]
        body = cells[1:]
        ncol = len(head)
        # the direction column: header says so, or its cells are input/output words
        dcol = next((i for i, h in enumerate(head) if "direction" in h or h in ("dir", "i/o")), None)
        if dcol is None:
            for i in range(ncol):
                vals = [r[i].lower().strip("*` ") for r in body if i < len(r)]
                if vals and all(v in ("input", "output", "inout", "in", "out") for v in vals):
                    dcol = i
                    break
        if dcol is None:
            continue
        ncol_name = next((i for i, h in enumerate(head)
                          if "signal" in h or "name" in h or "port" in h), 0)
        for r in body:
            if ncol_name < len(r):
                nm = _ident(r[ncol_name])
                if nm:
                    ports.add(nm)
    return ports


#: A line that ends a section without being a `#` heading.  Specs head their blocks three ways --
#: `### Parameters`, `**Parameters**`, and a bare table -- and a reader that only knows the first
#: swallows the rest of the document.  A spec that heads its parameters `**Parameters**` ran to
#: EOF and picked up FSM state names from a paragraph fourteen lines later, reporting three
#: parameters the design never had.
_SECTION_END = re.compile(r"^\s{0,3}(?:#{1,6}\s|\*\*[^*]+\*\*\s*:?\s*$|\|)")


def _sections(text: str, head_re) -> list[str]:
    """Bodies of the sections whose heading matches, up to the next heading of ANY of the three
    shapes a spec uses."""
    out, lines = [], text.split("\n")
    starts = [i for i, l in enumerate(lines) if head_re.match(l)]
    for s in starts:
        body = []
        for l in lines[s + 1:]:
            if _SECTION_END.match(l):
                break
            body.append(l)
        out.append("\n".join(body))
    return out


#: A plain `Input ports:` / `Output ports:` line -- a heading with no `#`, no bold, no bullet.
#: Kept separate from `_IFACE_HEAD` rather than folded into it: that pattern also decides heading
#: nesting for `_table_ports`, which is a BELIEVED source, and widening it would let a verdict
#: move.  This one is read by `_plain_decl_ports` alone and reaches nothing but the unflagged
#: record.
_PLAIN_IFACE_HEAD = re.compile(r"^[ \t]{0,3}(input|output|inout|in|out)\s*(?:/\s*\w+\s*)?"
                               r"(?:ports?|signals?|pins?)\s*:\s*$", re.I)


def _plain_decl_ports(text: str) -> set:
    """Indented `name[7:0]: description` lines under a plain `Input ports:` heading.

    The fifth shape, and the one every RTLLM specification uses:

        Input ports:
        \tclk: Clock input for synchronization.
        \tdata_in[7:0]: 8-bit input data for addition.

    No fence, no table, no bullet, no `#`.  `_bullet_ports` requires a bullet marker and
    `_IFACE_HEAD` requires a markdown heading, so before this existed the prose side of the
    interface check came back EMPTY for that entire benchmark -- `prose_ports: []`, every emitted
    pin reported as `extra_port`, and `flag: false` for a reason that was about this file rather
    than about any design.  A check that cannot fire is worse than one that is absent, because it
    reports as a pass.

    Deliberately narrow, for the same reason `_bullet_ports` is.  The heading must be a line that
    is nothing but the heading, the run of declarations ends at the first line that is neither
    indented nor blank, and a name must be followed by `:` on its own line.  Prose that merely
    mentions `valid_in` in a sentence is not a declaration and is not read as one.
    """
    ports, lines = set(), text.split("\n")
    for i, l in enumerate(lines):
        if not _PLAIN_IFACE_HEAD.match(l):
            continue
        for line in lines[i + 1:]:
            if not line.strip():
                continue
            if not re.match(r"^[ \t]+\S", line):        # the run ends at the first flush line
                break
            m = re.match(r"^[ \t]+([A-Za-z_]\w*)\s*(\[[^\]]*\])?\s*:", line)
            if not m:
                break
            nm = _ident(m.group(1))
            if nm and not re.fullmatch(r"[A-Z][A-Z0-9_]*", nm):
                ports.add(nm)
    return ports


def _bullet_ports(text: str) -> set:
    """Bulleted declarations under an interface heading, plus the plain-heading shape."""
    ports = set(_plain_decl_ports(text))
    for body in _sections(text, _IFACE_HEAD):
        for line in body.split("\n"):
            m = re.match(r"^\s*(?:[-*+]|\d+\.)\s+(.+)$", line)
            if not m:
                continue
            item = m.group(1)
            # the declaration is the part before the first ':' that separates name from prose
            decl = re.split(r"\s*[:—-]\s", item, maxsplit=1)[0]
            decl = decl.split(":")[0] if ":" in decl and "[" not in decl else decl
            cand = re.findall(r"`([^`]+)`|\*\*([^*]+)\*\*", decl)
            picks = [a or b for a, b in cand] or [decl]
            for p in picks[:1]:                     # only the leading token names the port
                nm = _ident(p)
                if nm and not re.fullmatch(r"[A-Z][A-Z0-9_]*", nm):
                    ports.add(nm)
    return ports


#: A direction-LED item in a declaration list: `- input  clk`, ` - output q (4 bits)`,
#: `* inout [7:0] data`.  Anchored at both ends, so the line must be nothing but the declaration:
#: the direction keyword comes first, an optional range or a trailing `(N bits)` gives the width,
#: and anything else on the line -- a colon, a sentence, a second clause -- fails the match.
#:
#: That anchoring is the whole difference between this and `_bullet_ports`, and it is why this
#: shape is BELIEVED where that one is not.  `- valid_a indicates the validity of input data_in`
#: and `- Input interface: Uses valid-ready handshake` are both bullets carrying a direction word,
#: and both sit in the same prompt as a real list; neither matches this.  A sentence cannot lead
#: with a bare direction keyword and end at the name.
_DECL_ITEM = re.compile(
    r"^[ \t]{0,4}(?:[-*+•]|\d+[.)])[ \t]+"
    r"(input|output|inout)\b[ \t]*"
    r"(?:(?:wire|reg|logic|signed|unsigned)[ \t]+)*"
    r"(\[[^\]]*\])?[ \t]*"
    r"[`*]{0,2}([A-Za-z_]\w*)[`*]{0,2}[ \t]*"
    r"(?:\([ \t]*([^()]*?)[ \t]*\))?"
    r"[ \t]*[,;]?[ \t]*$", re.I)

#: The same declaration, wrapped by the document in a CODE SPAN and then described:
#:
#:      - **`input [31:0] num_in`**: The 32-bit unsigned number to be reversed.
#:
#: `_DECL_ITEM` is anchored at both ends and must stay that way -- that anchoring is the entire
#: difference between the believed shape 3 and the unbelieved shape 4, and relaxing it to allow a
#: trailing `: sentence` would immediately admit `- Input interface: Uses valid-ready handshake`
#: with `interface` as a port.  So the anchor is not removed here, it is MOVED: the backticks are
#: the document itself saying where the code ends, and what is inside them still has to satisfy
#: `_DECL_ITEM` in full -- direction keyword first, ending at the name.  A bullet whose code span
#: holds prose (`- \`num_in\`: the input bus`) yields `- num_in`, which leads with no direction
#: keyword and matches nothing, exactly as before.
#:
#: Only `:` and the dashes are accepted as the separator before the description.  A line that
#: continues in bare prose (``- `input clk` is driven by the PLL``) is left unmatched: it is a
#: sentence that happens to quote a declaration, and the code span alone does not make it a
#: declaration list.  `cvdp_copilot_reverse_bits_0001` writes both its ports this way and read as
#: having no interface at all.
_DECL_SPAN = re.compile(r"^[ \t]{0,4}((?:[-*+•]|\d+[.)])[ \t]+)"
                        r"\*{0,2}`([^`]+)`\*{0,2}[ \t]*(?:[:—–][ \t]*.*)?$")


def _decl_list_ports(text: str) -> list[dict]:
    """The direction-led declaration list, in document order, with its ranges unparsed.

    The fifth shape, and the one VerilogEval and ChipBench state their interface in -- 153 of the
    former's 156 prompts and 40 of the latter's 45 carry nothing else:

         - input  clk
         - input  reset
         - output q (4 bits)

    No fence, no table, no heading, no colon.  Before this existed both ends of the interface
    check came back EMPTY on those two benchmarks, and the two ends failed DIFFERENTLY, which is
    the only reason it was caught: `contract.derive` refused with "no ports could be read out of
    the prose", while `iface_conform` reported `flag: false` with `vacuous: true` -- a check that
    could not fire, reading as a pass.

    Returned raw -- direction keyword as written, range and parenthetical as strings -- because
    `leanrtl/contract.py` and this file want different things from it, and the one thing they must
    not do is read the line differently.  Widths are computed there, once, by `_eval_width`.

    ## Why a single item is enough

    A run of two was the first rule and it was wrong: three VerilogEval designs
    (`Prob001_zero`, `Prob002_m2014_q4i`, `Prob003_step_one`) declare exactly one port, a constant
    output, and a rule that demanded a list would have read their whole interface as absent.  The
    anchoring is what does the work here; a count would only have added a way to be wrong.

    ## What it does not match, measured

    Zero of RTLLM's 50 descriptions produce a single item from this pattern, which is what makes
    it safe to promote to a believed source: the benchmark that every existing verdict came from
    reads exactly as it did before.
    """
    out, seen = [], set()
    for line in text.split("\n"):
        m = _DECL_ITEM.match(line)
        if not m and (sm := _DECL_SPAN.match(line)):
            # Unwrapped and re-read, rather than parsed by a second pattern: there is one
            # declaration pattern in this file and it stays the only one, so a shape accepted
            # here cannot drift from a shape accepted there.
            m = _DECL_ITEM.match(sm.group(1) + sm.group(2))
        if not m:
            continue
        nm = _ident(m.group(3))
        # No SCREAMING_CASE test here, unlike every other reader in this file.  Casing is the
        # usual evidence that a name is a parameter, but this line has already matched a
        # DIRECTION KEYWORD, which is stronger evidence in the other direction: a parameter is
        # never written `- input WIDTH`.  Suppressing on casing dropped every upper-case port a
        # spec declared -- ChipBench `Prob024` names its only two ports `A` and `B` and read as
        # having NO interface at all, and `Prob011`'s `C_1`/`S`/`CO` and `Prob031`'s `Q` went the
        # same way, silently.  The other five sites keep the test: there casing is the only
        # evidence there is, and at three of them it is a POSITIVE test inside a region already
        # scoped to parameters, where loosening would admit parameters rather than ports.
        if not nm or nm in seen:
            continue
        seen.add(nm)
        out.append({"name": nm, "dir": m.group(1).lower(), "range": (m.group(2) or "").strip(),
                    "paren": (m.group(4) or "").strip()})
    return out


def _param_table(text: str) -> set:
    """SCREAMING_CASE names in the leading column of a table that FOLLOWS a parameters heading.

    The third shape a spec declares parameters in, and the one `_prose_params` structurally cannot
    see: `_SECTION_END` treats a `|` line as the end of a section, so a `## Parameters` heading
    followed immediately by `| Parameter | Description | Default | Constraints |` yields an empty
    body and the design reads as having no declared parameters at all.  Measured on CVDP
    `qam16_demapper_interpolated`, whose three parameters are a table of exactly that shape and
    whose `prose_params` came back empty.

    Deliberately narrow, for the same reason `_bullet_ports` is: only the FIRST column, only
    directly after the heading, and only while the rows stay contiguous.  A table elsewhere in the
    document -- a truth table, an opcode map, a register map -- is not a parameter declaration, and
    the separator row (`|---|---|`) and a `| Parameter |` header row carry no SCREAMING_CASE name
    so they drop out on their own.
    """
    params, lines = set(), text.split("\n")
    for i, l in enumerate(lines):
        if not _PARAM_HEAD.match(l):
            continue
        j = i + 1
        while j < len(lines) and not lines[j].strip():
            j += 1
        while j < len(lines) and lines[j].lstrip().startswith("|"):
            cells = [c.strip() for c in lines[j].strip().strip("|").split("|")]
            if cells:
                nm = _ident(cells[0].strip("`* "))
                if nm and re.fullmatch(r"[A-Z][A-Z0-9_]{1,}", nm):
                    params.add(nm)
            j += 1
    return params


def _prose_params(text: str) -> set:
    """SCREAMING_CASE identifiers declared as parameters.

    Only LIST ITEMS inside a parameters section count.  A spec declares parameters one per bullet
    (`- \\`DEPTH\\`: the number of data elements`); a prose *paragraph* inside the same section
    names FSM states and constants in the same backticked SCREAMING_CASE and is not a declaration.
    """
    params = set()
    for body in _sections(text, _PARAM_HEAD):
        for line in body.split("\n"):
            if not re.match(r"^\s*(?:[-*+]|\d+[.)])\s+", line):
                continue
            for m in re.finditer(r"`([A-Z][A-Z0-9_]{1,})`|\*\*`?([A-Z][A-Z0-9_]{1,})`?\*\*", line):
                params.add(m.group(1) or m.group(2))
    params |= _param_table(text)
    # prose that names one inline instead: "a parameter named 'AFFINITY'".  Kept narrow -- a bare
    # `parameter` followed by any capitalised word matches ordinary sentences.
    for m in re.finditer(r"parameter\s+named\s+[`'\"]([A-Z][A-Z0-9_]{1,})[`'\"]", text):
        params.add(m.group(1))
    return {p for p in params if p.lower() not in _KW}


#: A backticked SCREAMING_CASE identifier with at least one underscore.  The backticks are load
#: bearing: they are the spec's own statement that the token is an identifier and not an English
#: word, and without them the pattern eats `FIFO`, `DUT`, `RTL` and every acronym in the prose.
_BT_CONST = re.compile(r"`([A-Z][A-Z0-9]*(?:_[A-Z0-9]+)+)`")

#: A name the spec presents as a PREPROCESSOR macro rather than a parameter.  Either the prose
#: says so in the same breath -- "the `FPGA_SOURCE` compilation macro" -- or it writes the
#: directive.  The distinction is not pedantic: a macro is set by the compile command or an
#: external defines file, and `parameter FPGA_SOURCE = ...` neither reads it nor can be overridden
#: the way one is, so the advice this check gives would be actively wrong.
def _is_macro(text: str, name: str) -> bool:
    return bool(re.search(
        r"(?:`(?:ifn?def|define|undef)\s+%s\b)"
        r"|(?:`?%s`?[^.\n]{0,40}?\b(?:macro|define[sd]?)\b)"
        r"|(?:\b(?:macro|`define)\b[^.\n]{0,40}?`?%s\b)" % ((re.escape(name),) * 3), text, re.I))


#: The spec's own word for the ROLE the name plays.  Required on the same LINE as an occurrence,
#: which is both tighter than a character window and easier to justify: every shape this check is
#: for states the role in the same breath as the name ("the `NUM_DIV` parameter specifies", "a
#: predefined threshold (e.g., `ERROR_THRESHOLD`)", "submodule parameter `FORCE_X2ZERO` is set to
#: 0"), while a name that is a state, a bitfield or a module gets a line that says so instead
#: (`| [7:6] | \`WORD_SELECT\` | Word Select |`).
_ROLE = re.compile(r"\b(parameters?|thresholds?|constants?|defaults?\s+to|default\s+value)\b", re.I)


def _lone_constants(text: str, known: set, declared_params: set) -> list:
    """SCREAMING_CASE names the spec uses as VALUES and the module declares nowhere.

    A spec that names a magnitude -- a threshold, a division factor, a conditional default -- and
    never declares it in an interface closes nothing: an author still has to choose the number.
    Inlining the chosen number closes the hole invisibly.  Declaring it as a `parameter` under the
    spec's own name closes it in the open, and that difference is worth a warning because a
    testbench can READ a declared parameter: when it does, it models against whatever the author
    chose and agrees at every value, while against an inlined literal it cannot bind at all.

    ## Four filters, and why each one is load bearing

    The naive form of this check -- every backticked SCREAMING_CASE name the module does not
    declare -- is worse than guessing.  Over the 78 emitted modules of `cvOurs` it fires on 7, of
    which 5 PASS their harness: 29% precision against a 44% base rate.  Over all 3614 emitted
    modules of the four benchmarks it fires on 37 designs.  Each filter below was added because a
    named class of false positive survived the ones before it, and the four together take that 37
    to 3.

      1. **Backticks.**  They are the spec's own statement that the token is an identifier and not
         an English word; without them the pattern eats `FIFO`, `DUT`, `RTL` and every acronym.
      2. **Not already a declared parameter.**  A name the spec puts in a Parameters section is
         `missing_param`'s business, and `missing_param` deliberately does not gate -- see `gate`.
         Without this the check re-imports that exact false positive (`low_pass_filter`'s
         `NBW_MULT`, a width the design carries internally, 128/128 passing).
      3. **Not a preprocessor macro.**  `FPGA_SOURCE` alone accounted for 28 of the 37, across
         RealBench's e203 core.  A macro comes from the compile command or an external defines
         file; `parameter FPGA_SOURCE = ...` neither reads it nor is overridden the way one is, so
         the advice would be actively wrong.  See `_is_macro`.
      4. **No sibling, and a role word.**  What is left is mostly FSM state names, and what
         separates them from a magnitude is that they come in FAMILIES -- `S_IDLE`/`S_RECV_CHECKSUM`,
         `COOL_LOW`/`COOL_MED`/`COOL_FULL`, `H_ACTIVE`/`H_BACK`/`H_FRONT` -- because that is what
         makes an enumeration read as one.  So a candidate is dropped when another candidate in
         the same spec shares its first or last underscore-separated segment.  That alone leaves
         8; requiring the spec to say on the same line what the name IS (`_ROLE`) drops the five
         that survive as a state (`WRITE_CRC`, beside the prefix-sharing `GET_RX_BD`/`GET_TX_BD`),
         a bitfield (`WORD_SELECT`), a module (`ALU_DPATH`), or a build option (`SDC_IRQ_ENABLE`).

    ## What the three are

    Three designs, on three benchmarks, in three different arms -- and on every one of them our
    arm fails where the direct-Verilog control passes, which is the only pattern that makes a
    finding ours to fix.

      * `qam16_demapper_interpolated` (CVDP) -- "the error flag is set if the absolute difference
        exceeds a predefined threshold (e.g., `ERROR_THRESHOLD`)", and no value anywhere.  Our
        author inlined one; the harness opens with `threshold = int(dut.ERROR_THRESHOLD.value)`
        and dies on `contains no child object named ERROR_THRESHOLD` before the first edge.
        `cvOurs` 0/1, `cvCtrl` passes.
      * `e203_itcm_ram` (RealBench) -- `FORCE_X2ZERO`, which the spec calls a submodule parameter
        and gives two different conditional values for.  `rbOurs` fails, `rbCtrl` passes.
      * `freq_divbyeven` (RTLLM) -- "The `NUM_DIV` parameter specifies the division factor, which
        must be an even number, and defaults to ...".  `ours` does not even compile; `oursClar`,
        which asked about it, passes.

    Three fires and no false positive is a better card than `dead_input`'s, but the rate is still
    not why it warns.  It warns because the repair is FREE and always available, which is the same
    reason `_ADVICE_CONFLICT` refuses: a named constant declared and used in place of a literal is
    the identical circuit, and one declared and left unused is inert.  A check whose advice costs
    nothing when it is wrong can be tuned for recall, and that is what these filters buy -- they
    are there to keep it CREDIBLE, not to keep it safe.
    """
    cand = set(_BT_CONST.findall(text))
    lines = text.split("\n")
    out = []
    for c in cand:
        if c.upper() in known or c.lower() in _KW:
            continue
        if c in declared_params or _is_macro(text, c):
            continue
        seg = c.split("_")
        if any(o != c and (o.split("_")[0] == seg[0] or o.split("_")[-1] == seg[-1])
               for o in cand):
            continue
        pat = re.compile(r"\b%s\b" % re.escape(c))
        if not any(_ROLE.search(ln) for ln in lines if pat.search(ln)):
            continue
        out.append(c)
    return sorted(out)


def prose_iface(text: str, top: str | None = None) -> dict:
    """The interface the prose declares, with the sources that declared it.

    Only the STRUCTURED sources are believed -- see this module's docstring for why a bulleted
    declaration under an "Inputs" heading is collected and reported but never flagged, and why a
    direction-LED list is not the same thing and is.

    `top`, when given, is the name of the module we actually emitted, and it settles an attribution
    question that does not arise on every benchmark.  A spec that quotes the SURROUNDING RTL -- the
    submodules the design instantiates, the parent that instantiates it -- carries many
    `module ... (...);` headers, and believing all of them reports every one of those other
    modules' pins as a port this design is missing.  Unfiltered, that fired on a third of one
    benchmark's designs with lists of forty-odd names, every one of them a submodule's port.

    So: the NAME decides, and the count is immaterial.  A single header used to be believed
    unconditionally, on the premise that a spec stating its interface once has no ambiguity.
    ChipBench falsifies that premise: `Prob002`, `Prob003` and `Prob004` each quote exactly one
    module header and it belongs to somebody else -- the prompt says so in plain English, `Dual-port
    RAM module (provided):`, handing the author a helper to instantiate.  A lone header is a header
    like any other and has to name the module to be believed.

    If none of them names the module we emitted, no code header is believed and the direction table
    stands alone -- the conservative direction, and the right one, because a set difference against
    the wrong module's interface is not weaker evidence, it is evidence about a different module.
    """
    code = _code_headers(text, top)
    if top and code:
        code = [c for c in code if (c["module"] or "").lower() == top.lower()]
    code_ports = set().union(*[c["ports"] for c in code]) if code else set()
    code_params = set().union(*[c["params"] for c in code]) if code else set()
    tab, bul = _table_ports(text), _bullet_ports(text)
    decl = {d["name"] for d in _decl_list_ports(text)}
    par = _prose_params(text) | code_params
    ports = (code_ports | tab | decl) - par

    # Pairwise across whatever believed sources this document HAS, rather than the code-vs-table
    # pair alone.  With only those two present the set is identical to what that expression gave,
    # so no existing verdict moves; with a declaration list present the same question is now
    # asked of it, because a spec that heads its pins one way in a skeleton and another way in a
    # bulleted list contradicts itself exactly as much as one that does it in a table.
    believed = [s for s in (code_ports, tab, decl) if s]
    clash: set = set()
    for i, a in enumerate(believed):
        for b in believed[i + 1:]:
            clash |= a ^ b
    return {"ports": ports, "params": par,
            "by_source": {"code": sorted(code_ports), "table": sorted(tab),
                          "decl_list": sorted(decl),
                          "bullet_unflagged": sorted(bul - ports - par)},
            # a name in one believed source but not another when SEVERAL exist
            "self_conflict": sorted(clash - par)}


# ------------------------------------------------------------------------ emitted extraction

def _decl_names(blob: str) -> list:
    """`(name, start, end)` for each `NAME = ...` in one declaration run, in source order.

    The spans are what let a USE be told from a DECLARATION later: the name appears in its own
    `parameter NAME = 16;` whether or not anything reads it, so counting bare occurrences would
    call every parameter live.
    """
    out = []
    for m in re.finditer(r"([A-Za-z_]\w*)\s*=", blob):
        if m.group(1).lower() not in _KW:
            out.append((m.group(1), m.start(1), m.end(1)))
    return out


def emitted_iface(path: str) -> dict:
    """Ports, parameters and INERT parameters of the emitted module.

    Both declaration styles are read.  Only the ANSI `#(...)` form used to be, and since our
    extraction route emits every module in the NON-ANSI style -- a bare port list, then
    `parameter DATA_WIDTH = 16;` after the `);` -- that made this function report zero parameters
    for every module we emit, while a direct-Verilog control parsed clean.  The arm split that
    produced was a property of this file, not of either route.

    `inert_params` is a parameter the module declares and never reads.  It is worth more than a
    missing one: it needs no prose and no testbench, so no repair it motivates can be fitted to an
    answer key; and it is invisible to every other gate, because the module elaborates,
    synthesises, has no undriven net, and a proof about the fixed-width module is perfectly true
    of the fixed-width module.  A reference inside another parameter's initialiser counts as a
    use, which over-approximates "used" -- the safe direction for a predictor whose whole value is
    that a flag means something.
    """
    src = open(path, errors="replace").read()
    src = re.sub(r"//[^\n]*", "", re.sub(r"/\*.*?\*/", "", src, flags=re.S))
    m = re.search(r"\bmodule\s+([A-Za-z_]\w*)\s*(#\s*\((.*?)\))?\s*\((.*?)\)\s*;", src, re.S)
    if not m:
        return {"module": None, "ports": set(), "params": set(), "inert_params": set(),
                "dead_inputs": set(), "inputs": set()}

    params, decl_at = set(), {}
    if m.group(3):                                  # ANSI: `module foo #(parameter A = 1) (...)`
        for nm, s, e in _decl_names(m.group(3)):
            params.add(nm)
            decl_at.setdefault(nm, []).append((m.start(3) + s, m.start(3) + e))

    # Non-ANSI: `parameter A = 1;` between the `);` and this module's `endmodule`.  Scoping to
    # the top module matters -- an emitted file may carry helper modules, and their parameters
    # are not this module's interface.
    end = src.find("endmodule", m.end())
    body = src[m.end():end if end != -1 else len(src)]
    for d in _NONANSI_PARAM.finditer(body):
        for nm, s, e in _decl_names(d.group(1)):
            params.add(nm)
            decl_at.setdefault(nm, []).append((m.end() + d.start(1) + s,
                                               m.end() + d.start(1) + e))

    inert = set()
    for nm in params:
        spans = set(decl_at.get(nm, []))
        if not [u for u in re.finditer(r"\b%s\b" % re.escape(nm), src) if u.span() not in spans]:
            inert.add(nm)

    ports = set()
    for chunk in m.group(4).split(","):
        nm = _ident(chunk)
        if nm:
            ports.add(nm)

    # A DEAD INPUT: an input port the module declares and never reads.  Same shape as
    # `inert_params` and found the same way -- occurrences outside the declaration spans -- but it
    # answers a different question, and one no other gate can reach.  An inert parameter is a
    # width that did not generalise.  A dead input is a pin the testbench will drive and nothing
    # will look at, and its usual cause is that the design reads the SAME pin under a different
    # spelling: the spec gave the pin two names, the author declared both (which is what
    # `_ADVICE_CONFLICT` asks for) and then read one of them.  For an OUTPUT that is a complete
    # repair -- the duplicate is driven identically and binding by name cannot tell.  For an INPUT
    # it is not a repair at all: only one spelling is driven, the other reads X, and if the design
    # read the undriven one every output it feeds is X.  Declaring both leaves `missing_port`
    # empty, so the conflict refusal never fires and the gate passes the design clean.  This is
    # the signal that does not.
    #
    # Both declaration styles again.  In the ANSI form the direction declaration IS the port-list
    # entry, one span; in the non-ANSI form the name appears twice before any use -- once in the
    # bare port list, once in `input foo;` -- and counting bare occurrences would call every input
    # live.
    decl_spans = {}
    for d in re.finditer(r"\binput\b(?:\s+(?:wire|reg|logic|signed))*\s*(?:\[[^\]]*\]\s*)?"
                         r"([A-Za-z_]\w*)", src):
        decl_spans.setdefault(d.group(1), []).append(d.span(1))
    for chunk_m in re.finditer(r"[A-Za-z_]\w*", m.group(4)):
        nm = chunk_m.group(0)
        if nm in decl_spans:
            decl_spans[nm].append((m.start(4) + chunk_m.start(), m.start(4) + chunk_m.end()))
    dead_in = set()
    for nm in decl_spans:
        spans = set(decl_spans[nm])
        if not [u for u in re.finditer(r"\b%s\b" % re.escape(nm), src) if u.span() not in spans]:
            dead_in.add(nm)

    # a bare port list declares directions on later lines; those names are already in `ports`
    return {"module": m.group(1), "ports": ports, "params": params, "inert_params": inert,
            "dead_inputs": dead_in, "inputs": set(decl_spans)}


# ------------------------------------------------------------------------------- the check

def compare(spec_text: str, vpath: str) -> dict:
    """The set differences between what the prose declares and what we emitted."""
    e = emitted_iface(vpath)
    # The emitted module's NAME is read first and handed to the prose reader: it is what lets a
    # spec that quotes several module headers say which of them is this design's interface.
    p = prose_iface(spec_text, e["module"])
    # A dead input is reported with its nearest LIVE port name, because that is the whole content
    # of the finding: `s_ready` declared and never read, beside a heavily-read `s_read`, says the
    # two are one pin under two spellings.  A dead input with no near twin is a different and
    # weaker fact -- behaviour the author did not implement -- and is reported with `None`.
    live = sorted(e["ports"] - e["dead_inputs"])
    dead = {n: (difflib.get_close_matches(n, live, n=1, cutoff=0.75) or [None])[0]
            for n in sorted(e["dead_inputs"])}
    # Checked against what the module DECLARES, ports and parameters alike, and case-insensitively:
    # a spec writes a magnitude `ERROR_THRESHOLD` and a module may legitimately carry it as
    # `error_threshold`, and a testbench binding by name is the only thing that could tell them
    # apart.  It cannot, so neither does this.
    declared = {n.upper() for n in e["ports"]} | {n.upper() for n in e["params"]}
    return {"module": e["module"],
            "missing_port": sorted(p["ports"] - e["ports"]),
            "missing_param": sorted(p["params"] - e["params"]),
            "named_constant": _lone_constants(spec_text, declared, p["params"]),
            "extra_port": sorted(e["ports"] - p["ports"]),
            "prose_self_conflict": p["self_conflict"],
            "inert_param": sorted(e["inert_params"]),
            "dead_input": dead,
            "prose_ports": sorted(p["ports"]), "prose_params": sorted(p["params"]),
            "emitted_ports": sorted(e["ports"]), "emitted_params": sorted(e["params"]),
            "by_source": p["by_source"]}


#: What `bb.py emit` prints when a missing port is also a name the spec contradicts itself on.
_ADVICE_CONFLICT = (
    "The spec declares this pin twice under two spellings -- once in a direction table, once in a "
    "module header -- so there is no reading of it under which BOTH are absent.\n"
    "  Do not adjudicate which spelling is meant.  Declare BOTH and drive them identically: a "
    "testbench binds by name, so an extra output duplicating a real one is inert, while the one "
    "that is missing is the one nothing can attach to."
)

#: What it prints when the spec names a port we simply do not have.
_ADVICE_MISSING = (
    "A testbench binds by name, so if these are pins of THIS module the module cannot be attached "
    "to at all.  Check whether they are: a long spec often quotes the surrounding RTL -- a pin "
    "template, a submodule's signals, a neighbour's interface -- and those are not this design's "
    "ports.  If they are this design's, add them and re-emit."
)

#: What it prints when an input is declared and nothing reads it.
_ADVICE_DEAD_IN = (
    "An input nothing reads is not inert the way a duplicated OUTPUT is.  A testbench drives ONE "
    "spelling of a pin; the other reads X, and X through a mux or a comparison poisons every "
    "output downstream of it.  So if two of these names are one pin under two spellings, "
    "declaring both did not resolve the clash -- it only moved it, and you must now decide which "
    "spelling the testbench will drive.\n"
    "  Decide it from the spec, not from the module header: a header inside a spec is quoted "
    "text and is exactly where a one-character typo survives.  The direction table's DESCRIPTION "
    "column is the adjudicator, because a description is prose and cannot be a typo of another "
    "name -- a pin glossed \"ready to accept the transaction\" is a `ready`, whatever the header "
    "spells it.\n"
    "  If instead the name has no near twin, then it is behaviour you did not implement: the "
    "spec gives this design an input and your module ignores it.  Re-read what it is for."
)

#: What it prints when the spec names a magnitude the module does not declare.  Takes the name it
#: is about, because a worked example written against ANOTHER design's identifier is both less
#: useful and, in a workspace that ships this file, a mention of a design the author is not on.
def _advice_const(name: str) -> str:
    return (
        "The spec names this quantity but does not say what it IS -- it gives it a name and "
        "leaves you the value.  You chose one; the question is whether you wrote the NUMBER or "
        "the NAME.\n"
        f"  Declare it: `parameter {name} = <your value>;` and use the parameter everywhere you "
        "would have written the literal.  The circuit is identical, so this costs nothing even if "
        "the name turns out to be irrelevant -- and if it is not, it is the whole design.  A "
        "testbench cannot see a literal, but it can read a parameter: one that does reads your "
        "value and checks your module against it, and then it agrees with you WHATEVER you chose. "
        " Inlined, there is no value it can agree with and it cannot bind to the module at all.\n"
        "  This applies to a magnitude the spec left open, not to an FSM state encoding."
    )


def gate(spec_path: str, vpath: str) -> tuple[str, str, dict]:
    """`(severity, message, detail)` for the authoring loop, severity one of `ok`/`warn`/`refuse`.

    Tolerant about its INPUTS: a missing spec or an unreadable emitted file is `ok` with an empty
    detail, because this runs bolted onto a path that already succeeded and a missing helper must
    not turn a good emit red.

    ## Why a missing port is usually a warning and sometimes a refusal

    A missing port is close to fatal when it is real, and it is not always real.  Measured over
    every emitted module of four benchmarks, `missing_port` fires on 46; on one benchmark's larger
    designs it fires on modules that PASS their testbench, because their specs quote a generic pin
    template and the surrounding RTL alongside the design's own interface, and no structural rule
    separates a template from a declaration.  Refusing on that signal alone would throw away
    passing designs, so it warns.

    What is different about the other case is not how many names are missing but WHY.  When the
    two structured sources contradict each other on the very name we did not emit -- the direction
    table calls a pin one thing, the module header another -- the spec is not describing context,
    it is declaring one pin twice.  That is a defect in the spec, and unlike an ambiguous one it
    has a resolution that is always available and always free: declare both spellings.  A refusal
    is worth making when the author can always satisfy it, so this case, and only this case,
    refuses.  Across ~1900 emitted modules of four benchmarks it selects one design, which fails
    in every arm including the direct-Verilog control.

    `missing_param` never gates: our extraction route folds a parameter into the netlist far more
    often than it drops one, so the prose naming a parameter we do not declare is usually a
    statement about the route rather than about the interface.  Re-checked after `_param_table`
    made the signal available on the four CVDP specs whose parameters are a TABLE, and after the
    parametric (`pverilog`) route made "folded into the netlist" inapplicable -- on that route the
    author declares the parameters by hand and nothing is folded, so the old explanation should
    not cover it.  It still does not gate: over the 15 parametric and 78 non-parametric CVDP
    modules the rule "warn when `missing_param` and the module declares parameters at all" fires
    exactly once, on `low_pass_filter` (`NBW_MULT`, a width the spec names in its table and the
    design carries as an internal width), which passes 128/128 of its own harness.  One firing,
    and it is wrong.  `extra_port` never gates either -- it is the harmless direction, and prose
    routinely omits a clock it mentions in passing.

    ## Why a dead input warns

    `dead_input` is the one signal here that fires on a design NO other check reaches.  It exists
    because `_ADVICE_CONFLICT` -- declare both spellings -- is a complete repair for an output and
    only half a repair for an input, and taking it empties `missing_port`, so the conflict refusal
    that produced the advice cannot fire a second time on the design it already advised.

    It warns rather than refuses, by this file's own rule: a refusal is worth making when the
    author can always satisfy it, and this one they cannot.  Declaring both spellings is free;
    choosing between them is a judgement about which one a testbench they cannot see will drive.

    Measured over the 93 emitted modules of the two CVDP arms -- 78 non-parametric, 15 parametric,
    both declaration styles -- it fires three times.

      * `data_bus_controller` (`s_ready`, beside a live `s_read`) -- the case above.  That spec
        puts `s_ready` in its direction table and `s_read` in its quoted module header, its
        testbench drives `s_ready` and never mentions `s_read`, and our module reads `s_read`, so
        every output is X and the harness dies on `Cannot convert Logic('X') to bool`.
      * `wishbone_to_ahb_bridge` (`hclk`, `hresp`, neither with a near twin) -- a bridge that
        ignores the AHB clock and the AHB error response.  Fails in both arms.
      * `microcode_sequencer` (`cc`) -- a sequencer that ignores its condition-code input, and
        PASSES its own harness anyway.

    So one of the three fires on a passing design, and the rate is not the reason to keep it.  The
    reason is that unlike `missing_param` -- whose one firing was a false STATEMENT, about a width
    the design does carry -- every one of these three is true as written: the input really is
    declared and really is unread.  A warning that is always true and sometimes urgent is worth an
    author's attention; a warning that is sometimes false is not.  That is the line this file
    draws, and it is why one gates and the other does not.

    ## Why a named constant warns

    `named_constant` is the only check here that is not about a PIN, and it warns for the reason
    `_ADVICE_CONFLICT` refuses: the repair is free.  Declaring `parameter ERROR_THRESHOLD = 1;`
    and writing the name where the literal was is the identical circuit, so a wrong firing costs
    an author nothing, while a right one -- on a harness that opens by READING that parameter off
    the DUT and modelling against it, so it agrees at every value and can bind at none -- takes a
    design from 0/1 to passing.  Over all 3614 emitted modules of the four benchmarks it fires on
    three designs, on three benchmarks, and on every one of them our arm fails where the
    direct-Verilog control passes.  See `_lone_constants` for the four filters that get it there.

    It is placed last because it is the least urgent finding here and the only one that is about
    a value rather than a connection: a module missing a pin cannot be attached to, and a module
    reading an undriven pin goes X, while a module that inlined a number is a working circuit
    that merely cannot be interrogated.  Only one message is returned, so the order is the
    priority.
    """
    if not (os.path.isfile(spec_path) and os.path.isfile(vpath)):
        return "ok", "", {}
    try:
        d = compare(open(spec_path, errors="replace").read(), vpath)
    except Exception as e:                          # a parse failure is not a design verdict
        return "ok", "", {"iface_gate_error": str(e)}
    missing = d["missing_port"]
    conflicted = [n for n in missing if n in set(d["prose_self_conflict"])]
    if conflicted:
        return ("refuse",
                "the spec declares port(s) this module does not carry, and contradicts ITSELF on "
                "them: " + ", ".join(conflicted) + "\n" + _ADVICE_CONFLICT, d)
    if missing:
        return ("warn",
                "the spec declares port(s) this module does not carry: " + ", ".join(missing)
                + "\n" + _ADVICE_MISSING, d)
    # After `missing_port`, not before: a module that is missing a pin outright has a bigger
    # problem than one that carries a pin it ignores, and only one message is returned.
    if d["dead_input"]:
        named = ", ".join(f"{n} (beside `{t}`)" if t else n
                          for n, t in sorted(d["dead_input"].items()))
        return ("warn", "this module declares input(s) nothing reads: " + named
                + "\n" + _ADVICE_DEAD_IN, d)
    # Last, and after every check about PINS: a name that is only a value is the least urgent of
    # these findings and the cheapest to act on, so it must not displace one that is neither.
    if d["named_constant"]:
        return ("warn", "the spec names value(s) this module declares nowhere: "
                + ", ".join(d["named_constant"])
                + "\n" + _advice_const(d["named_constant"][0]), d)
    return "ok", "", d
