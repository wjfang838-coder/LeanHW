#!/usr/bin/env python3
"""The interface contract, derived from the prose.  Nobody is asked for it.

    python3 -m leanrtl.contract --ws ../data/part2/rtllm/accu/decided --key accu

The contract is the module name, the ports, their directions and their widths — the one part of a
design that both authors must agree on before either starts, because a specification whose output
is called `q` and an implementation whose output is called `dout` cannot be compared at all, and
the comparison is the whole method.

## Why this is computed and not written

The tree this comes from had a role whose first job was to read the prose and write
`contracts/<key>.json`.  That is an agent transcribing a list, and it has the failure mode every
transcription has: it is plausible when it is wrong.  A contract with one port name mistyped
produces a specification and an implementation that agree with each other perfectly and mean
nothing about the design, and nothing downstream can see it, because every gate compares the two
artifacts against each other and both were built from the same wrong list.

So the list is derived, deterministically, from the same parsers `authoring/iface_gate.py` uses to
check the emitted Verilog against the prose after the fact.  One extractor, used at both ends: if
it reads the prose wrong here it reads it wrong there too, and the two errors cancel — which is
bad, but it is *visibly* bad, because `leanrtl/iface_conform.py` reports what it read.  Two
extractors that disagree produce a design that fails its interface gate for reasons no one can
locate.

## Where it refuses

A derived contract that guesses is worse than no contract, so this refuses rather than defaults:

  * a port whose direction the prose never gives is `undetermined`, not an input;
  * a port whose width the prose NAMES and never fixes is `undetermined`, not 1 bit.
    `[DATA_WIDTH-1:0]` with no value for `DATA_WIDTH`, `E203_XLEN` in a width column, `(WIDTH
    bits)` in a parenthetical — the document answered the question with a name and then never
    gave the name a value, and 1 is not the answer to that question;
  * a name the code header and the direction table disagree about is a `conflict`, and neither
    reading is preferred.  One real case named its slave-ready pin one thing in the table and
    another eleven lines later in the skeleton; both authors followed the skeleton and the
    testbench followed the table.

## Where it stopped refusing, and what had to be true first

A port the document mentions by name and never characterises at all is one bit.  That is the one
guess this file makes, it is made last, and `width_from` records that it was made.

It was not always here, and the reason it is has a price tag.  On RTLLM the strict reading left
15 of 50 designs with every width `undetermined`; 13 of them were run anyway and died at
`05_simdiff` with zero vectors compared, having first paid for a specification author and an
implementation author — 28 sessions, roughly a fifth of that benchmark's API spend, to reach a
wall the free deterministic step above could have named.

What makes the default defensible is the four readings that now run before it, each filling only
what the ones above left empty:

  * `_widths_by_omission` — the notation.  A bare `clk` beside `data_in[7:0]` is one bit.
  * `_widths_by_statement` — the sentence.  "All ports are one bit unless otherwise specified."
  * `_resolve_symbolic` — the parameter block, including the unfenced `Parameter:` blocks RTLLM
    writes and `_PARAM_DECL` never saw, which is how `asyn_fifo`'s 8-bit bus was undetermined in
    a document that says `WIDTH = 8`.
  * `_widths_from_body` — the implementation narrative.  `right_shifter` states `reg [7:0] q`
    eleven lines below a pin list that gives no widths at all.

Measured against the reference RTL of the two benchmarks that ship it: 47 of RTLLM's 50 contracts
now match the reference interface exactly, and 700 realbench ports with known widths have none
wrong.  The one design the default gets wrong is RTLLM's `RAM`, whose address and data pins are 8
and 6 bits and whose pin list says neither — it comes out as eight one-bit ports and says
`defaulted` in every one of them.

`derive()` returns those lists and `main()` exits 3 when any is non-empty.  A run that continues
past a refusal is a run whose two authors were handed different designs.
"""
from __future__ import annotations

import argparse
import json
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
if __package__ in (None, ""):
    sys.path.insert(0, ROOT)

sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "authoring"))
from iface_gate import (                                                     # noqa: E402
    _KW, _RANGE, _decl_list_ports, _ident, _iface_regions, prose_iface,
)

# `input [7:0] a, b` — one direction keyword governing a run of names, which is how a Verilog
# header is actually written.  The range is optional and, when absent, the width is 1.
_DIRRUN = re.compile(r"\b(input|output|inout)\b((?:\s+(?:reg|wire|logic|signed|unsigned))*)"
                     r"\s*(\[[^\]]*\])?\s*([^,;)]*)")
_PARAM_DECL = re.compile(r"\bparameter\b(?!\s*\btype\b)[^=;,]*?([A-Za-z_]\w*)\s*=\s*([^,;)\n]+)")
# `8`, `8 bits`, `1-bit`, `[7:0]`, `[DATA_WIDTH-1:0]`
_WIDTH_CELL = re.compile(r"^\**\s*`?\s*(?:\[(?P<range>[^\]]*)\]|(?P<n>\d+)\s*[- ]?\s*bits?"
                         r"|(?P<bare>\d+))\s*`?\s*\**$", re.I)
#: A width column that NAMES its magnitude instead of stating it: `E203_PC_SIZE`, `E203_XLEN`,
#: `DATA_WIDTH`.  `_WIDTH_CELL` reads ranges, digits and `N bits` and nothing else, and a cell it
#: could not match was discarded — width `None`, `width_expr` empty, which downstream is
#: indistinguishable from a table that never filled the column in.  That distinction did not matter
#: while an unknown width was a refusal either way.  It matters now that `_widths_by_default`
#: exists: 241 realbench ports across 27 of its 40 designs are this shape, every one of them a 32-
#: or 64-bit bus in a table that states a width on every single row, and read as silence they would
#: each have become one bit — in a contract, with no gate downstream able to see it.
#:
#: The name is not resolved here and usually cannot be: `E203_XLEN` is a `define` in a header file
#: this module deliberately never reads.  Recording it is the whole point — a port whose width the
#: document named and left symbolic belongs in `undetermined`, not in the default.
#:
#: Two shapes, because these tables write both: a bare magnitude (`E203_PC_SIZE`, `E203_XLEN / 8`)
#: and a range with the brackets left off (`RAM_MEM_WIDTH-1:0`, ten pins of `sd_data_master`).
#: The colon is what tells them apart, and it has to, because they mean different numbers.
#:
#: A term may be parenthesised.  This pattern used to demand that the cell START with an identifier,
#: so `(N + N/2)*OUT_WIDTH` — how `16qam_mapper_0001` and `_0006` write the width of `I` and `Q` —
#: matched nothing and the cell was discarded.  Discarded is the dangerous direction: with no width
#: and no `width_expr` the port is indistinguishable from one the table never filled in, so it fell
#: through to `_widths_by_default` and became ONE BIT — silently, in a document that states 18 on
#: the row.  `_eval_int` already reduces innermost parentheses first; recording the expression was
#: the only thing missing.  The head still may not be a bare number, as before: `_WIDTH_CELL` owns
#: cells that are just digits and has already been tried by the time this one is.
_SYM_PAREN = r"\(\s*[A-Za-z_]\w*(?:\s*[-+*/]\s*(?:[A-Za-z_]\w*|\d+))*\s*\)"
_SYM_TAIL = rf"(?:\s*[-+*/]\s*(?:\w+|{_SYM_PAREN}))*"
_SYM_EXPR = rf"(?:[A-Za-z_]\w*|{_SYM_PAREN}){_SYM_TAIL}"
#: The low end of a range may be a bare number, and almost always is — `WIDTH-1:0`.  Only the HIGH
#: end has to name something, which is what keeps a cell of plain digits out of here.
_SYM_LOW = rf"(?:\w+|{_SYM_PAREN}){_SYM_TAIL}"
#: A term may lead with a NUMBER, but only across `*`, `/` or `+` — never a bare `-`.  `2*DATA_WIDTH`
#: is how `configurable_digital_low_pass_filter_0014` states the width of `result1`, and with the
#: head restricted to identifiers it matched nothing and the port became one bit.
#:
#: The excluded operator is the whole safety argument.  These documents are full of register FIELD
#: MAPS written `| 31 - 20 | reserved |`, and a numeric head across `-` reads `31 - 20` as the
#: arithmetic 11 — `static_branch_predict_0001` alone carries 25 such cells, every one of them a bit
#: range and not a width.  Requiring `*`, `/` or `+` admits the one and refuses all 25, measured
#: across all five benchmarks.  Pure-digit cells remain `_WIDTH_CELL`'s, which is tried first and
#: which no expression carrying an operator can reach.
_SYM_NUMHEAD = rf"\d+\s*[*/+]\s*(?:[A-Za-z_]\w*|{_SYM_PAREN}){_SYM_TAIL}"
_SYM_ANY = rf"(?:{_SYM_EXPR}|{_SYM_NUMHEAD})"
#: The code span may CLOSE BEFORE the unit word.  A cell is written `` `DATA_WIDTH` bits ``  as
#: readily as `` `DATA_WIDTH bits` ``, and with the closing backtick permitted only after `bits`
#: the first spelling matched nothing — the cell was discarded, and a discarded cell is the
#: dangerous direction here for the reason the paragraph above gives: no width AND no `width_expr`
#: is indistinguishable from a column never filled in, so `_widths_by_default` made it ONE BIT.
#: `configurable_digital_low_pass_filter_0014` states `DATA_WIDTH` on three input rows that way and
#: shipped a contract calling all three scalars; the harness sweeps `DATA_WIDTH` and iverilog
#: refused the design outright with `can not select part of scalar: x_in`, so it ran zero tests.
#: The other two `configurable_digital_low_pass_filter` designs write `` `DATA_WIDTH * N` bits ``
#: and `` `DATA_WIDTH+1` bits ``.  Across the other four benchmarks this spelling does not occur, so
#: the backtick is the whole change and it reaches three designs.
_SYMBOLIC_CELL = re.compile(rf"^\**\s*`?\s*({_SYM_ANY}(?:\s*:\s*{_SYM_LOW})?)\s*`?\s*"
                            r"(?:[-\s]?\s*bits?)?\s*`?\s*\**$", re.I)
_DIR_WORD = {"input": "in", "in": "in", "output": "out", "out": "out", "inout": "inout"}


def _eval_int(s: str, params: dict[str, int]) -> int | None:
    """`8` -> 8; `DATA_WIDTH-1` -> 7 when the prose gives `DATA_WIDTH = 8`; anything else -> None.

    Only `+`, `-` and `*` over integers and known parameter defaults.  Deliberately not `eval` on
    arbitrary text: this reads a benchmark's prose, and the prose is untrusted input.

    At module level rather than closed over inside `_eval_width` because three callers now need
    it — the range form, the `(WIDTH bits)` form and the re-resolution pass that runs once the
    prose's own parameter block has been read.
    """
    s = s.strip()
    # Innermost parentheses first, each reduced to the integer it evaluates to.  Without this the
    # split below hands `(32` to `int()` and the whole expression goes undetermined — which is how
    # `(DATA_WIDTH/8)-1:0`, the write-strobe width on every AXI design here, stayed symbolic even
    # with `DATA_WIDTH` bound.  Division was never the problem; the brackets around it were.
    # A negative sub-expression is refused rather than substituted: splicing `-1` back in would
    # produce `x--1`, and no bit width is negative anyway.
    while (m := re.search(r"\(([^()]*)\)", s)):
        v = _eval_int(m.group(1), params)
        if v is None or v < 0:
            return None
        s = s[:m.start()] + str(v) + s[m.end():]
    if re.fullmatch(r"-?\d+", s):
        return int(s)
    # Tokens, then TWO folds: `*` and `/` before `+` and `-`.  A single left-to-right accumulator
    # is what this was, and it is wrong on any expression that mixes the two precedences:
    # `(N + N/2)*OUT_WIDTH` with `N=4, OUT_WIDTH=3` came out 12, because `N + N/2` folded as
    # `(N+N)/2 = 4` rather than `4+2 = 6`.  Nothing in these corpora currently RECORDS such an
    # expression, so no contract was ever wrong because of it — but `16qam_mapper`'s `I`/`Q` are
    # written exactly that way, and a width that is quietly 12 instead of 18 is worse than one
    # that is undetermined: the gate refuses the second and hands the first to both authors.
    toks: list = []
    for t in re.split(r"([+\-*/])", s):
        t = t.strip()
        if not t:
            continue
        if t in "+-*/":
            toks.append(t)
            continue
        v = int(t) if re.fullmatch(r"\d+", t) else params.get(t)
        if v is None:
            return None
        toks.append(v)
    if not toks or isinstance(toks[0], str):
        return None
    i = 1
    while i < len(toks) - 1:
        if toks[i] in "*/":
            a, b = toks[i - 1], toks[i + 1]
            if toks[i] == "*":
                r = a * b
            else:
                # `E203_XLEN/8` — a byte mask, which is how six realbench designs write the width
                # of their write-strobe pins.  Integer division, because a bit width is an integer
                # and a document that divides an odd width by 8 has not described a real port.
                if b == 0 or a % b:
                    return None
                r = a // b
            toks[i - 1:i + 2] = [r]
        else:
            i += 2
    acc = toks[0]
    for i in range(1, len(toks) - 1, 2):
        acc = acc + toks[i + 1] if toks[i] == "+" else acc - toks[i + 1]
    return acc


def _eval_width(rng: str, params: dict[str, int]) -> tuple[int | None, str]:
    """`[7:0]` -> 8.  `[DATA_WIDTH-1:0]` -> 8 when the prose gives `DATA_WIDTH = 8`.

    Returns `(width, expression)` and never invents a number.  The expression is kept even when
    the width resolves, because it is what makes a design parametric: `bb.py`'s F2 route needs to
    know the width came from `DATA_WIDTH` and not from the literal 8, and a contract that has
    already collapsed it cannot tell it.
    """
    expr = rng.strip()
    if ":" not in expr:
        # `[3]` — a single bit selected by index, so one bit wide.
        if re.fullmatch(r"\d+", expr):
            return 1, expr
        # `[WIDTH-1]` — an MSB INDEX with the `:0` left off, so the port is WIDTH bits and not
        # WIDTH-1.  The colon-free reading downstream is a bit COUNT (`_resolve_symbolic`'s second
        # try, which serves `(WIDTH bits)`), and that reading is off by one exactly here: nobody
        # writes a count as `N-1`, and an expression that ends in `-1` is the top index of a range
        # whose bottom is 0.  `prbs_gen_0003` writes ``- `data_in [WIDTH-1]`` against a `WIDTH`
        # whose own default is 16 and whose description reads "Bit width of the `data_in` and
        # `data_out` buses"; the count reading gave 15, and a 15-bit port against a 16-bit harness
        # is a contract that is wrong rather than incomplete.  Two ports of one design across all
        # five benches carry a colon-free expression ending in `-1`, both of them these.
        if re.search(r"-\s*1$", expr) and (top := _eval_int(expr, params)) is not None:
            return top + 1, expr
        return None, expr
    hi, lo = (s.strip() for s in expr.split(":", 1))
    h, l = _eval_int(hi, params), _eval_int(lo, params)
    if h is None or l is None:
        return None, expr
    return abs(h - l) + 1, expr


def _code_contract(text: str, top: str | None) -> dict | None:
    """The module header written out as code — direction, width and ORDER, all at once.

    Order matters and no other shape carries it: a `Module` literal holds inputs and outputs as
    two separate lists, so the emitter takes the header order from here.  A design whose ports come
    out in the wrong order still elaborates and still passes every proof; it fails at a positional
    port connection in someone else's testbench, with an error that points nowhere near the cause.
    """
    best = None
    # Fenced blocks first, then -- only when the caller named a toplevel -- the raw document.
    # Three VerilogEval prompts (`Prob062_bugs_mux2`, `Prob123_bugs_addsubz`,
    # `Prob132_always_if2`) state their interface as an INDENTED, UNFENCED `module TopModule
    # (...);` under a line of running prose ("Consider the following implementation of an 8-bit
    # 2-to-1 mux:").  Scanning fences alone read all three as zero ports, which is a refusal at
    # `01_contract`, so none of them ever ran: three designs lost to a markdown convention.
    #
    # The raw pass goes LAST, so a fenced header still wins wherever there is one, and it is
    # gated on `top` because the name test below is the entire safety property here.  Gap 1
    # established that a header has to NAME the module we emitted to be believed; without a name
    # to test against, scanning running prose for `module ... (...)` would re-open exactly the
    # submodule hijack that test closed.  With it, the fallback cannot bind somebody else's pins.
    scans = [(b, False) for b in re.findall(r"```[^\n]*\n(.*?)```", text, re.S)]
    if top:
        scans.append((text, True))
    for blk, unfenced in scans:
        for m in re.finditer(r"\bmodule\s+([A-Za-z_]\w*)\s*(#\s*\((.*?)\))?\s*\((.*?)\)\s*;",
                             blk, re.S):
            name = m.group(1)
            # When the toplevel is known, the NAME decides and nothing else does.  There used to
            # be an `and best is not None` here, which let the FIRST header in the document stand
            # as a fallback however it was named -- and a prompt that hands the author a helper to
            # instantiate quotes exactly one header belonging to somebody else.  ChipBench
            # `Prob002`/`Prob003`/`Prob004` each quote only `decoder_38` or `dual_port_RAM`, and
            # the fallback made `derive()["module"]` the HELPER's name and seeded the contract
            # with the helper's pins.  Across 369 designs only 7 carry a fenced header at all, and
            # name-matching separates them perfectly, so the strict rule costs nothing.
            if top and name.lower() != top.lower():
                continue
            params: dict[str, int] = {}
            for src in (m.group(3) or "", blk):
                for pm in _PARAM_DECL.finditer(src):
                    v = pm.group(2).strip().rstrip(",);")
                    if re.fullmatch(r"\d+", v):
                        params.setdefault(pm.group(1), int(v))
            ports, seen = [], set()
            body = m.group(4)
            if not re.search(r"\b(input|output|inout)\b", body):
                if unfenced:
                    # The unfenced pass believes ANSI headers ONLY.  An ANSI header is
                    # self-delimiting: every port it contributes is read out of the parenthesised
                    # list this regex already matched, so nothing outside the header can reach the
                    # contract however much prose surrounds it.  A non-ANSI one is not -- its
                    # directions come from `_DIRRUN` over `blk[m.end():]`, which unfenced is the
                    # whole rest of the document, and a direction run scanned across running prose
                    # is the exact shape that invented `Prob149_ece241_2013_q4`'s `time` port.
                    # No observed design states an unfenced non-ANSI header, so this costs nothing
                    # measured; it is here so that the cost cannot arrive later unnoticed.
                    continue
                # A non-ANSI header: `module f(a, b, q);` with the directions declared in the
                # body below it.  Read them from the body, and keep the header's order.
                order = [n for n in (_ident(t) for t in body.split(",")) if n]
                decl = {}
                for dm in _DIRRUN.finditer(blk[m.end():]):
                    for tok in dm.group(4).split(","):
                        nm = _ident(tok)
                        if nm:
                            decl[nm] = (_DIR_WORD[dm.group(1)], dm.group(3) or "")
                for nm in order:
                    d, rng = decl.get(nm, (None, ""))
                    w, expr = _eval_width(rng.strip("[]"), params) if rng else (1, "")
                    ports.append({"name": nm, "dir": d, "width": w, "width_expr": expr,
                                  "source": "code header (non-ANSI)"})
            else:
                for dm in _DIRRUN.finditer(body):
                    rng = (dm.group(3) or "").strip("[]")
                    w, expr = _eval_width(rng, params) if rng else (1, "")
                    for tok in dm.group(4).split(","):
                        nm = _ident(tok)
                        if nm and nm not in seen:
                            seen.add(nm)
                            ports.append({"name": nm, "dir": _DIR_WORD[dm.group(1)],
                                          "width": w, "width_expr": expr,
                                          "source": "code header"})
            cand = {"module": name, "ports": ports, "params": params}
            if top and name.lower() == top.lower():
                return cand
            best = best or cand
    return best


def _table_contract(text: str) -> list[dict]:
    """Ports from a markdown table, with widths where the table gives them.

    Scoped by `iface_gate._iface_regions`, so a spec that lists the submodules it instantiates does
    not contribute their pins.  Unscoped, a third of one benchmark's designs came back missing
    forty-odd ports, every one of them a submodule's.

    ## Where the direction comes from when the table has no direction column

    A document that writes one table per direction — `### Inputs` above one, `### Outputs` above
    the next, and `| Name | Width | Description |` in both — has stated every direction it needs
    to, in the only place there was room to put it.  Requiring the word inside the table read those
    documents as having no interface at all: on CVDP's `cid003` it returned zero ports on nine
    designs whose pin tables are complete and unambiguous, and zero ports is a refusal at
    `01_contract`, so the design never ran.

    The heading is used ONLY when the table has no direction column of its own.  A column beats a
    heading because it is per-row and the heading is per-table, and a table that carries both and
    disagrees is a document contradicting itself about its own interface — which is what
    `conflicts` is for, one layer up.

    The fallback also requires the table to name its name column (`Name`, `Signal`, `Port`).
    Without a direction column there is nothing else marking the block as a pin list, and `ncol`
    defaulting to 0 would read the first column of every table under a direction heading —
    including the register maps and the truth tables these documents are full of — as port names.
    """
    regions = _iface_regions(text)

    def in_scope(ln: int) -> bool:
        return regions is None or any(a <= ln < b for a, b in regions)

    out, rows, block, start = [], [], [], 0
    lines = text.split("\n") + [""]

    #: The direction in effect at each line, from the headings above it.  Same rule as
    #: `_inline_ports`: a direction heading opens a section, any other heading closes it, and a
    #: blank line does neither — these tables are routinely separated from their heading by one.
    sections, sec = [], None
    for line in lines:
        h = _DIR_HEAD.match(line)
        if h:
            sec = _DIR_WORD[h.group(1).lower()]
        elif _is_other_head(line):
            sec = None
        sections.append(sec)

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
        #: Header cells are stripped of emphasis and code markers, exactly as the BODY cells are
        #: two lines below and at `dcol`'s value scan.  Without it the column tests split in two by
        #: accident: `ncol` and `dcol` ask `"port" in h` / `"direction" in h` and survive a
        #: `**Port**` heading, while `wcol` and `dcol`'s fallback ask `h in ("bits", "size", ...)`
        #: and do not.  So a table heading its width column `**Size**` — which is how all three
        #: `configurable_digital_low_pass_filter` designs write it — had its names and directions
        #: read and its widths silently dropped: every port `width: None`, `width_expr: ''`,
        #: indistinguishable from a column never filled in, and `_widths_by_default` made all nine
        #: of `_0014`'s ports ONE BIT off a table that states a width on every row.
        head = [c.lower().strip("*` ") for c in cells[0]]
        body = cells[1:]
        dcol = next((i for i, h in enumerate(head)
                     if "direction" in h or h in ("dir", "i/o")), None)
        if dcol is None:
            for i in range(len(head)):
                vals = [r[i].lower().strip("*` ") for r in body if i < len(r)]
                if vals and all(v in _DIR_WORD for v in vals):
                    dcol = i
                    break
        ncol = next((i for i, h in enumerate(head)
                     if i != dcol and ("signal" in h or "name" in h or "port" in h)), None)
        head_dir = None
        if dcol is None:
            # No column says it, so the heading above the block has to — and it has to have named
            # the rows, per the docstring.
            head_dir = sections[start] if start < len(sections) else None
            if head_dir is None or ncol is None:
                continue
        if ncol is None:
            ncol = 0
        wcol = next((i for i, h in enumerate(head)
                     if "width" in h or h in ("bits", "size", "range")), None)
        for r in body:
            if ncol >= len(r):
                continue
            nm = _ident(r[ncol])
            if not nm:
                continue
            if dcol is None:
                d = head_dir
            else:
                d = _DIR_WORD.get(r[dcol].lower().strip("*` ")) if dcol < len(r) else None
            w, expr = None, ""
            if wcol is not None and wcol < len(r):
                cell = r[wcol].strip()
                m = _WIDTH_CELL.match(cell)
                if m:
                    if m.group("range"):
                        w, expr = _eval_width(m.group("range"), {})
                    else:
                        w = int(m.group("n") or m.group("bare"))
                elif (sm := _SYMBOLIC_CELL.match(cell)):
                    # A bare magnitude is a bit COUNT and is normalised to a range so that
                    # `_resolve_symbolic` has one form to evaluate; a cell that already carries a
                    # colon IS the range and is passed through unchanged.  `RAM_MEM_WIDTH-1:0`
                    # rewritten as `RAM_MEM_WIDTH-1:0-1:0` resolves to nothing at all.
                    e = sm.group(1).strip()
                    expr = e if ":" in e else f"{e}-1:0"
            out.append({"name": nm, "dir": d, "width": w, "width_expr": expr,
                        "source": "direction table"})
    return out


#: A width stated in running prose: `1 bit`, `4-bit`, `8 bits wide`, `[7:0]`.
_WIDTH_INLINE = re.compile(r"\[(?P<range>[^\]]*)\]|(?P<n>\d+)\s*[-\s]?\s*bits?\b", re.I)
#: A direction stated in running prose.  `\b` on both sides so `outputs` and `inputs` count and
#: `throughput` does not.
_DIR_INLINE = re.compile(r"\b(input|output|inout)s?\b", re.I)
#: `a data width of "size" bits`, `a data width of 2*size bits` — a width whose magnitude is a
#: parameter NAME, stated in the description rather than in a notation.  `_WIDTH_INLINE` reads only
#: digits and matches neither, so `multi_pipe_4bit` reported all five of its pins undetermined
#: while its own description gives the width of three of them and its own parameter block gives
#: `size = 4`.  The quotes are optional because the document uses them on one line and not the
#: next.
_SYMBOLIC_INLINE = re.compile(r"\bwidth\s+of\s+[\"'`]?\s*([A-Za-z_0-9][\w\s*+-]*?)\s*[\"'`]?\s*"
                              r"bits?\b", re.I)
#: `q (4 bits, output)` — the parenthetical form, anywhere on a line.  The emphasis markers repeat
#: because markdown nests them: CVDP writes ``**`q`**``, and a pattern that allowed at most one
#: marker stopped at the backtick with `**` still between the name and the `(`, so the port was
#: never seen.  `*` rather than `?` on both sides is the whole fix.
_PAREN_PORT = re.compile(r"(?:^|[\s,;:*`])(?:\*\*|`)*([A-Za-z_]\w*)(?:\*\*|`)*\s*\(([^)]*)\)")
#: `- **awaddr_i**: [ADDR_W-1:0], input — write address` — the bullet form, anchored at the start
#: of the line so it cannot run backwards over a name that belongs to something else.  The range
#: group sits between the name and the closing markdown so that `data_in[7:0]:` and
#: `**data_in[7:0]**:` both parse; without it the name pattern stopped at `data_in` and the `[`
#: kept the colon from ever being reached, so the port vanished entirely.
#:
#: The parenthetical group is the same shape one step further along: `- **`data_in`** (8-bits,
#: [7:0]): the 8-bit input data` puts the width between the name and the colon, and with no slot
#: for it the colon was never reached either.  It is captured rather than skipped because it is
#: part of the declaration — see `_inline_ports.colon`.  Emphasis markers repeat here for the same
#: reason they do in `_PAREN_PORT`.
#: The description after the colon is OPTIONAL — the tail is wrapped in `(?:...)?` and nothing
#: else about this pattern changes.  A bare bulleted name under a direction heading (`- `clk`` with
#: no colon and no description) is the whole interface of some designs, and with the tail mandatory
#: the pattern did not match those lines at all.  The parenthetical group has to stay: drop it and
#: `- **`data_in`** (8-bits, [7:0]): ...` stops matching, which silently guts ~30 designs.
#:
#: `lead` is the range written BEFORE the name, Verilog's own order: ``- **`[ADDR_WIDTH-1:0]
#: awaddr_i`**: write address``.  Without a slot for it the name pattern had nothing to match at
#: the `[`, so the line did not match AT ALL and the port vanished — 31 ports over 8 CVDP designs,
#: four of them every data port `restoring_division_0001` has.  It is guarded to ranges containing
#: a `:` on purpose: a bare `[...]` at the head of a bullet is markdown (`- [ ] todo:`, `- [see
#: below]: ...`), and every real Verilog range says `hi:lo`.  A leading range is consumed only when
#: a name follows it, so a line it does not fit falls through unmatched exactly as before.
#:
#: `more` is the rest of a COMMA RUN sharing one declaration: ``- `d0`, `d1`, `d2`, `d3` — 2-bit
#: data inputs (`[1:0]`)``.  With only a single-name slot the pattern needed its separator straight
#: after the name, met `` `, `` instead, and did not match the line AT ALL — so the bullet
#: contributed nothing and `Prob000_Four-to-one_multiplexer` emitted a two-port module that would
#: not compile.  The run only extends across names that carry the backtick or bold markup ON BOTH
#: SIDES of the comma, which is the same orthography convention `colon`'s bare-form guard leans on:
#: a marked-up comma list is a declaration, a plain one (`- clk, the clock: ...`) is a sentence, and
#: this pattern must not start reading sentences.
#:
#: The groups are NAMED rather than numbered because this pattern has now grown a slot three times,
#: and the first two times every `m.group(n)` after the insertion point silently shifted by one.
_COLON_PORT = re.compile(r"^\s*(?:(?:[-*+]|\d+[.)]|[•‣▪●·])\s*)?(?:\*\*|`)*"
                         r"(?:(?P<lead>\[[^\]]*:[^\]]*\])\s*(?:\*\*|`)*\s*)?"
                         r"(?P<name>[A-Za-z_]\w*)"
                         r"(?P<more>(?:\s*(?:\*\*|`)+\s*,\s*(?:\*\*|`)+[A-Za-z_]\w*)*)"
                         r"\s*(?P<rng>\[[^\]]*\])?"
                         r"\s*(?:\*\*|`)*\s*(?P<paren>\([^)]*\))?\s*(?:\*\*|`)*\s*"
                         r"(?:(?:[:—–]|(?<=\s)-(?=\s))\s*(?P<desc>.*))?$")
#: The separator was `[:—-]` with no spacing requirement on either side, which let a HYPHENATED
#: PHRASE split itself: `3. **Back-to-Back Transactions**:` read as the port `Back` described as
#: `to-Back Transactions`.  A dash used as a separator is written with space around it; a hyphen
#: inside a compound word is not, and that is the whole distinction.  The colon and the em/en
#: dashes keep their old spacing freedom — neither appears inside a word.
#:
#: Latent long before it fired: a `- ` bulleted line of the same shape would always have done
#: this.  Widening `_BULLET` to numbered lists is only what made it show up, on `wb2ahb_0001`,
#: as one phantom port in a BINDING contract.
#: The names inside `_COLON_PORT`'s `more` group.  The group keeps its markup so that the pattern
#: can require it; this pulls the identifiers back out of it.
_RUN_NAME = re.compile(r"[A-Za-z_]\w*")
#: A human-readable LABEL followed by the machine name in a code span, then the description:
#:
#:     - **generate** signal (`o_generate`) : 1-bit signal, true if both `i_A` and `i_B` are 1
#:     - **Clock Signal (`clock`)**: The register shifts its contents on the rising edge of this
#:
#: `_COLON_PORT` cannot reach these: it allows markup between the name and the parenthetical but
#: not a WORD, so ` signal ` breaks the match and the line yields nothing.  Rewritten to the
#: canonical `- o_generate: 1-bit signal, true if ...` it goes through the ordinary reader, which
#: means every guard downstream — the direction section, `_dir_of`, `keep`, the width readers —
#: applies to it unchanged.  Nothing is believed here that would not be believed if the document
#: had written the line the plain way.
#:
#: The parenthetical must hold a code span and NOTHING else.  That is what separates a naming
#: convention from a sentence that happens to quote an identifier: `- If a specific configuration
#: macro (e.g., `E203_CFG_ADDR_SIZE_IS_32`) is defined` has `e.g., ` inside the parentheses and
#: does not match, and neither does `- `stack_mux_sel` == 1'b1 : `data_in` is selected.`, which
#: has no parenthetical at all.  Both are lines this admitted under a looser rule that asked only
#: for one code span before the colon; that rule pulled in 31 realbench macro lines and four
#: cvdp mux conditions, and is why the parentheses are required rather than merely allowed.
#:
#: The description after the colon must carry a word.  `LABEL (name): description` with nothing
#: in the description slot is a sub-heading introducing a block, not a declaration — the same
#: document writes `#### 3. **Elapsed Time Register (`slv_reg_t`):**` as an actual heading three
#: lines up.  Without this, `axil_precision_counter_0001` gained `slv_reg_irq_mask` and
#: `slv_reg_irq_thresh`, two internal registers, as output ports.
_LABEL_SPAN = re.compile(r"^(\s{0,4}(?:[-*+]|\d+[.)]|[•‣▪●·])\s)[^`()\[\]]*"
                         r"\(\s*`\s*([A-Za-z_]\w*)\s*`\s*\)[\s*`]*[:—–][ \t]*(?=[^\n]*\w)(.*)$")
#: A plain-text heading that gives the direction for everything under it: `Input ports:`,
#: `Outputs`, `### Inout signals:`.  Not the same thing as `_DIR_INLINE` on a heading line — this
#: one must match the WHOLE line, so a sentence that merely mentions inputs is not a heading.
#:
#: The colon is permitted on EITHER side of the closing emphasis.  `**Inputs:**` and
#: `- **Input ports:**` write it inside, and allowing it only outside meant those headings were
#: not headings: the list under them lost its direction and, with it, its ports.  ChipBench
#: `Prob008_chapter12_ctrl` read 3 ports of 10 and `Prob009_cp0_reg` 4 of 19 for this reason
#: alone -- both are well-formed declaration lists, not the prose interfaces they looked like.
_DIR_HEAD = re.compile(r"^\s{0,4}(?:#{1,6}\s*)?(?:[-*+]\s*)?(?:\d+[.)]\s*)?(?:\*\*|`)?\s*"
                       r"(input|output|inout)s?"
                       r"(?:\s+(?:ports?|signals?|pins?|interfaces?|list))?"
                       r"\s*:?\s*(?:\*\*|`)?\s*:?\s*$", re.I)
#: A heading that is not a direction heading, which CLOSES a direction section: `Implementation:`,
#: `Module name:`, `## Behaviour`.  Distinguished from a port whose description happens to be
#: empty by `_is_other_head` below, not by this pattern alone.
#:
#: The `\d+[.)]` is here because `_DIR_HEAD` has always had it and this did not, and a document
#: that numbers one kind of heading numbers both.  `axil_precision_counter_0001` opens `#### 4.
#: **Interrupt Mechanism:**` sixty lines below its `#### Outputs`, and with that line failing to
#: read as a heading the output section never closed — every `Register (`slv_reg_*`)` label in
#: the functional description was still inside it.
#: The colon is NOT permitted inside the closing emphasis here, though `_DIR_HEAD` allows it.
#: The asymmetry is deliberate and measured: this pattern CLOSES a section, so every heading it
#: newly recognises risks dropping the ports below it, and allowing `**Interrupt Mechanism:**`
#: cost `ethernet_packet_parser_0001` all six of its ports — a design that converges and passes.
#: A direction heading that goes unread loses its section's directions; an other-heading that
#: goes unread leaves a section open too long.  Those are not the same size of mistake.
_OTHER_HEAD = re.compile(r"^\s{0,4}(?:#{1,6}\s*)?(?:\d+[.)]\s*)?(?:\*\*|`)?([A-Za-z][\w /()-]*?)"
                         r"(?:\*\*|`)?\s*:\s*$")
#: Words that introduce a port list without being in it.
_LABELS = {"ports", "port", "inputs", "outputs", "signals", "signal", "interface", "interfaces",
           "parameters", "parameter", "pins", "pin", "io", "i/o", "pinout", "portlist"}


#: A bullet marker followed by WHITESPACE.  The trailing space is load-bearing: a test that merely
#: asks whether the first character is one of `-*+` reads `**Summary:**` as a bulleted line and
#: lets a heading through as a port.
#:
#: `-*+` are markdown's own three.  The other two shapes are here because a document that numbers
#: its port list, or bullets it with U+2022, is writing a list just as plainly, and reading only
#: markdown's three meant those documents produced NO ports at all — not a short list, an empty
#: one, which `01_contract` then refuses as a parse failure.  Four CVDP designs read zero ports
#: for this reason alone: `ttc_lite_0001` (14 numbered declarations under `Inputs:`/`Outputs:`),
#: `secure_read_write_register_bank_0001` (16), `convolutional_encoder_0001` (5), and
#: `piso_0001`, which writes `•` and a TAB.  `_DIR_HEAD` already accepted `\d+[.)]` on the
#: heading above such a list, so the heading was found and everything under it was not.
_BULLET = re.compile(r"\s*(?:[-*+]|\d+[.)]|[•‣▪●·])\s")


def _head_shaped(t: str) -> bool:
    """Orthography alone: several words, or one capitalised word with no underscore and no digit.

    Split out of `_is_other_head` so the same discriminator can be applied where `_OTHER_HEAD`
    structurally cannot reach — see `_inline_ports.colon`.  Port names in these documents are
    lower-case, or carry an underscore or a digit, or both.
    """
    return " " in t or (t[:1].isupper() and "_" not in t and not any(c.isdigit() for c in t))


def _is_other_head(line: str) -> bool:
    """Is this a heading that ends whatever direction section is open?

    `Implementation:` and `Module name:` are; `valid_in:` with nothing after it is not, and the
    difference has to be got right in that direction — mistaking a heading for a port adds one
    bogus entry that the caller sees, while mistaking a port for a heading silently drops every
    port after it.

    The discriminator is orthography, which is what actually separates the two in these documents:
    a heading is either several words, or one capitalised word with no underscore and no digit.
    Port names in the same documents are lower-case, or carry an underscore or a digit, or both.
    """
    m = _OTHER_HEAD.match(line)
    if not m or _DIR_HEAD.match(line):
        return False
    return _head_shaped(m.group(1).strip())


def _in_code_span(name: str, text: str) -> bool:
    """Does `name` appear anywhere in `text` inside a backtick span?"""
    return bool(re.search(r"`[^`\n]*\b%s\b[^`\n]*`" % re.escape(name), text))


def _label_phantoms(ports: list[dict], text: str) -> set[str]:
    """Names that are prose SECTION LABELS the loose reader mistook for pins.

    `- **Width:** 1 bit` and `- **Purpose:**` are sub-bullets describing the port above them, not
    ports.  `_inline_ports.colon` already owns this question and already has the right
    discriminator — `_head_shaped` — but reaches it on only two paths: a flush-left line, and the
    bare form with no description at all.  These are indented, bulleted AND carry a description, so
    neither guard fires and the label lands in a BINDING contract as a pin.

    `_head_shaped` cannot simply be applied to every bulleted line.  It is orthography alone, and
    it does not separate `Purpose` from RTLLM's real `Rst`, `Clk`, `EMPTY`, `Cin`, `Q` and `MATCH` —
    the reason `colon` conjoins it with flush-left rather than using it neat.  What does separate
    them is not the name, it is the DOCUMENT: these prompts mark every signal name they mention in
    a code span, and never mark a section label in one.  So the conjunction here is `_head_shaped`
    AND never-in-a-code-span, gated on the document being one that does this consistently.

    The gate is what keeps the rule where it was measured.  A document qualifies only if at least
    four fifths of its identifier-shaped port names appear in a code span, and the denominator
    counts only the NOT-`_head_shaped` names — the ordinary `data_in`/`rst_n` pins — because
    counting the candidates themselves would let a document with enough phantoms in it vote its own
    gate shut.  `axil_precision_counter_0001` is exactly that document: 11 of its 32 ports are
    labels, and on the whole-list denominator it falls under the threshold and keeps all 11.

    Measured across all five corpora this drops 20 ports on 6 CVDP designs and NOTHING anywhere
    else, because RTLLM, VerilogEval and ChipBench barely use code spans at all — 2 of 50, 0 of 156
    and 5 of 45 of their documents pass the gate, so it never opens and their `Rst`/`Clk`/`Q` are
    untouched by construction rather than by luck.
    """
    ident = [p["name"] for p in ports if not _head_shaped(p["name"])]
    if not ident or sum(_in_code_span(n, text) for n in ident) / len(ident) < 0.8:
        return set()
    return {p["name"] for p in ports
            if _head_shaped(p["name"]) and not _in_code_span(p["name"], text)}


def _inline_ports(text: str) -> list[dict]:
    """Ports declared in running prose rather than in a table or a skeleton.

    `q (4 bits, output)` and `- **awaddr_i**: [ADDR_W-1:0], input — write address` are how a short
    specification states its interface, and neither of the two structured shapes sees them.  A
    parser that read only tables and code blocks reported ZERO ports on a four-line counter spec
    and exited 0, which is the same defect as a gate that passes when it had nothing to check:
    the caller cannot tell "this document declares no interface" from "I could not read it".

    Two shapes:

        NAME ( ... input ... )        the parenthetical form
        NAME [HI:LO] : ...            the bullet / colon form, to end of line

    ## Where the direction comes from, and why the heading wins

    Outside a direction section a line must carry a direction word of its own, because without one
    there is nothing distinguishing a port from any other backticked identifier in the document.

    Inside one — under `Input ports:` — the heading supplies it, and the heading OVERRIDES any
    direction word in the line.  Both halves of that were bugs found on one benchmark design whose
    pin list is six lines under two such headings:

      * Requiring a word per line dropped `rst_n: Active-low reset signal.`, which names no
        direction because the heading already did.  A dropped port is the worst outcome this
        module has: the contract came back with three pins and looked like a contract.
      * The three that survived did so because the words "input" and "Output" happen to occur in
        their English descriptions.  That is direction by coincidence, and it reverses on the very
        next design, where an output is described as "the registered version of the input".  A
        heading is a structural claim about every line beneath it; a word inside a sentence is
        not a claim about anything.

    Scoped by `_iface_regions` when the document has interface headings, for the reason
    `_table_ports` is: a spec that lists its submodules gives each of them a pin list too.
    """
    regions = _iface_regions(text)
    lines = text.split("\n")
    # A name this document DECLARES as a module is a module, not a pin of the toplevel.  The
    # prompt for `Prob005_8_bit_alu` hands the author four submodules under "The following
    # submodules are already provided", as a bullet-and-colon list --
    # `- bit_8_AND: Performs bitwise AND operation on two 8-bit inputs` -- and then writes out
    # `module bit_8_AND(aANDb,A,B);` in a fence forty lines later.  The colon form read all four
    # as ports, taking their direction from the word "inputs" at the end of a sentence about what
    # the submodule computes.  `_code_contract` already refuses those headers by name (they are
    # not the toplevel); this is the same refusal, made available to the prose reader, which sees
    # the sentence and not the header.  The pattern is the module-header pattern of
    # `_code_contract` truncated to its name group.
    declared = set(re.findall(r"\bmodule\s+([A-Za-z_]\w*)", text))

    def in_scope(ln: int) -> bool:
        return regions is None or any(a <= ln < b for a, b in regions)

    out, seen = [], set()
    section = None                                   # the direction the enclosing heading gives
    fenced = False
    # Is the reader at a point where a flush-left declaration may BEGIN?  True at the top of the
    # document, after a blank line, after a heading, and after a line that declared something;
    # False once a line has been read that declared nothing.  Only `colon()` consults it, and
    # only for flush-left lines -- see the note there for what it is separating.
    run_open = True
    for i, line in enumerate(lines):
        if line.lstrip().startswith("```"):
            fenced = not fenced
            run_open = True
            continue
        if fenced:
            # A fenced block is quoted code, and `_code_contract` already owns it -- and already
            # decided, by module NAME and nothing else, whether to believe it at all.  Reading
            # prose declarations out of the same fence is that same error committed by a second
            # reader, where the name test cannot reach it: `Prob006_cpu_top` documents a `Control`
            # submodule inside a 150-line fence, and `ALUOp   : Controls ALU operation. Directly
            # connected to the input OP of the ALU.` became a port of the toplevel -- direction by
            # the word "input" in a sentence about somebody else's pin.
            continue
        if not line.strip():
            run_open = True
            continue
        h = _DIR_HEAD.match(line)
        if h:
            section = _DIR_WORD[h.group(1).lower()]
            run_open = True
            continue
        if _is_other_head(line):
            # A blank line does NOT close the section: these lists are routinely broken up by
            # one, and closing on whitespace would drop everything after the first paragraph gap.
            section = None
            run_open = True
            continue
        if not in_scope(i) or line.strip().startswith("|"):
            continue
        if section is None and not _DIR_INLINE.search(line):
            run_open = False
            continue

        def keep(cands):
            # `Ports`, `Inputs`, `Signals` — the word that introduces the list is not a member of
            # it.  `_KW` already covers `input`/`output`/`inout`.  Filtering HERE rather than at
            # the point of use is what lets "nothing survived" fall through to the other shape.
            return [c for c in cands
                    if c[0].lower() not in _KW and c[0].lower() not in _LABELS
                    and c[0] not in declared
                    and c[0] not in seen]

        def paren():
            # The direction must be inside the parentheses even when a section is open.  A
            # section vouches for the line-anchored colon form beneath it; it does not vouch for
            # every parenthesis in the sentences there.  Letting it do so read `Carry-in input
            # (1-bit)` as a port named `input` and `a valid BCD digit (0–9)` as one named `digit`.
            #
            # And it must be a direction CLAIM, not merely a direction word: `_dir_claim` requires
            # the word to stand alone as an item of a property list, which is what separates
            # `q (4 bits, output)` from `statement (output out_assign)`.  See its docstring.
            return keep([(m.group(1), "", m.group(2), d)
                         for m in _PAREN_PORT.finditer(line)
                         if (d := _dir_claim(m.group(2)))])

        def colon():
            m = _COLON_PORT.match(line)
            if not m and (lm := _LABEL_SPAN.match(line)):
                m = _COLON_PORT.match(f"{lm.group(1)}{lm.group(2)}: {lm.group(3)}")
            if not m:
                return []
            # A heading written FLUSH-LEFT with prose after the colon.  `_OTHER_HEAD` is anchored
            # to end at the colon, so `Clarification: rst is an asynchronous active-low reset ...`
            # never reaches `_is_other_head` and was read as a port named `Clarification` — on 13
            # ChipBench designs, one of which had that as its ONLY port.  Both conjuncts are
            # required: the orthography test alone false-positives on the colon-form port names
            # RTLLM writes (`Rst`, `Clk`, `EMPTY`, `Cin`, `Q`, `MATCH`), and demanding flush-left
            # as well spares every one of them — colon-form ports are bulleted or indented 481
            # times against 28 flush-left, and all 11 real ones among those 28 are lower-case.
            # This refuses ONE candidate line and deliberately does not close the section:
            # closing it is what dropped every port after the heading on 9 RTLLM designs.
            if not (line[:1].isspace() or _BULLET.match(line)) and _head_shaped(m.group("name")):
                return []
            # The same argument, for the same flush-left lines, one step earlier in the sentence.
            # These prompts are hard-wrapped at about 75 columns, so ANY word can begin a line,
            # and a flush-left candidate that is not the FIRST of a run is the second half of a
            # sentence rather than a declaration.  Three VerilogEval designs declared a port that
            # way, each time taking the direction from a word in the running prose:
            #   `...produces a different circuit from the other`  +  `two: There is a flip- flop
            #      so the output is delayed.`                             -> `two`, out
            #   `...has an output connected to the input of a`    +  `two-input XOR. The second
            #      input of the XOR is 'in3.'`                            -> `two`, in
            #   `...the second input of the XOR is its corresponding` + `flip-flop's output, the
            #      second input of the AND is...`                         -> `flip`, out
            # A flush-left list is entered from a blank line or a heading and every line of it
            # declares something; wrapped prose is entered from prose.  `run_open` is that
            # distinction and nothing more -- it does NOT test the shape of the previous line,
            # which fails: `cvdp_copilot_complex_multiplier_0001` writes eight flush-left
            # declarations that each stop mid-sentence (`1 bit input to the design. This is the
            # Clock signal for the design`), and a predecessor-shape test drops six of them.
            # What separates the two is whether the predecessor DECLARED anything, so that is
            # what is carried.  Indented and bulleted lines are exempt: their shape is the claim,
            # and wrapped prose is never indented.
            if not (line[:1].isspace() or _BULLET.match(line)) and not run_open:
                return []
            # The bare form — a name with no colon and no description at all.  Nothing on the line
            # says "declaration" except the name itself, so the two orthography conventions and the
            # bullet shape have to carry it, exactly where `_decl_list_ports` has a direction
            # keyword to outrank them and this does not.  Rejects `HEAT_FULL`/`AMBIENT` (state
            # names), `Behavior`/`Summary`/`Width`, and fenced-block language tags; accepts `clk`,
            # `rst_n`, `a`, `match`, `o_heater_full`.
            if m.group("desc") is None and (not _BULLET.match(line)
                                            or not any(c.islower() for c in m.group("name"))
                                            or _head_shaped(m.group("name"))):
                return []
            paren = m.group("paren") or ""
            # A parenthetical that is exactly ONE BACKTICKED IDENTIFIER is the document NAMING
            # the signal rather than commenting on it, and the name it gives outranks the prose
            # word in front of it:
            #
            #     - **carry-out** signal (`o_Cout `) : 1-bit carry-out signal, computed using ...
            #
            # `Carry_Lookahead_Adder_0001` writes all three of its outputs that way and read as
            # having NONE: the commentary rule below refused every one of those lines, and the
            # contract that shipped held its three inputs, no outputs at all, and a phantom
            # `carry` scavenged out of the hyphen in `carry-out` by a separator class that did
            # not require spacing.  It converged and scored `func_pass` in that state.
            #
            # The two lines the commentary rule exists to reject still are: `- **S0 (IDLE)**:`
            # has no backticks in its parenthetical, and `- `WIDTH` (Default 4, must be greater
            # than 0):` has four words in its.  A code span holding a single identifier and
            # nothing else — that is the whole test, and neither of them passes it.
            span = re.fullmatch(r"\(\s*`\s*([A-Za-z_]\w*)\s*`\s*\)", paren)
            named = span.group(1) if span else ""
            if span:
                # The parenthetical is the name, so it is NOT also a width: the width has to come
                # from the sentence, where these lines write it (`1-bit signal, true if ...`).
                paren = ""
            elif paren and not (_WIDTH_INLINE.search(paren) or _DIR_INLINE.search(paren)
                                or _SYMBOLIC_PAREN.match(paren)):
                # A parenthetical that states neither a width nor a direction is commentary, and
                # the line is not a declaration.  Accepting it read `- **S0 (IDLE)**: wait for
                # `go`` as a port named `S0` and `- `WIDTH` (Default 4, must be greater than 0):`
                # as one named `WIDTH` — a state and a parameter, on the same design.  Refusing
                # the line puts it back where it was before the parenthetical had a slot at all,
                # which is the conservative direction: this module drops a port it cannot read
                # rather than invent one it can.
                return []
            # Otherwise the parenthetical is part of the declaration and the width has to come out
            # of it rather than out of the sentence.  On `- **`shift_bits`** (3-bits, [2:0]): ...
            # to `3'b111` (7-bit shift)` the description carries a width too, and it is the wrong
            # one — 7 where the author wrote 3.
            body = (paren + " " + (m.group("desc") or "")).strip()
            d = section or _dir_of(body)
            # Trailing range beats leading only because a line carrying both would be malformed;
            # in practice a design writes one or the other, never two for one pin.
            rng = m.group("rng") or m.group("lead") or ""
            # Every name in a comma run shares the one declaration that follows it — the range,
            # the parenthetical and the description are stated once for all of them.  `keep`
            # still filters each name individually, so a run that picks up a label or an
            # already-seen name loses that entry and not the whole line.
            names = [m.group("name")] + _RUN_NAME.findall(m.group("more") or "")
            if named:
                # A code-span name replaces the run rather than joining it: the run group holds
                # the OTHER prose words of the same phrase, and none of them is a port.
                names = [named]
            return keep([(n, rng, body, d) for n in names]) if d else []

        # Inside a section the colon form is tried FIRST: it is anchored at the start of the line
        # and the heading above it says what it is.  Outside one the parenthetical goes first,
        # because the colon form runs to end of line and on `Ports: clk (1 bit, input), q (4 bits,
        # output)` it eats the whole line and yields ONE port named after the heading — which is
        # what it did, and the counter smoke test came back with a single 1-bit input called
        # `Ports`.
        order = (colon, paren) if section else (paren, colon)
        found = order[0]() or order[1]()
        # A line that declared nothing ends the run: whatever follows it flush-left is prose
        # continuing, not a list continuing.
        run_open = bool(found)

        for name, rng, body, d in found:
            w, expr = None, ""
            if rng:
                # A range attached to the NAME beats one found in the description.  `data_in[7:0]:
                # 8-bit input data` agrees with itself, but where the two disagree the declaration
                # is the declaration and the sentence is commentary.
                w, expr = _eval_width(rng.strip("[]"), {})
            else:
                wm = _WIDTH_INLINE.search(body)
                if wm:
                    if wm.group("range"):
                        w, expr = _eval_width(wm.group("range"), {})
                    else:
                        w = int(wm.group("n"))
                elif (bm := _SYMBOLIC_PAREN.match(body)):
                    # Same normalisation, same reason: a COUNT written as a range, once, here.
                    expr = f"{bm.group(1).strip()}-1:0"
                elif (sm := _SYMBOLIC_INLINE.search(body)):
                    # Normalised to a RANGE here rather than kept as a bare count, so that
                    # `_resolve_symbolic` has one form to evaluate instead of two with different
                    # meanings: `size` as a range is bit number `size`, and as a count it is
                    # `size` bits, and the document means the second.  Writing `size-1:0` says so
                    # once, at the point where the reading is actually known.
                    expr = f"{sm.group(1).strip()}-1:0"
            seen.add(name)
            out.append({"name": name, "dir": d, "width": w, "width_expr": expr,
                        "source": "prose declaration"})
    return _widths_by_omission(out)


def _dir_of(s: str) -> str | None:
    m = _DIR_INLINE.search(s or "")
    return _DIR_WORD[m.group(1).lower()] if m else None


#: A token that belongs to a property list rather than to a sentence: a range, a bit count, or
#: the word `bits` itself.  `4 bits`, `[7:0]`, `8-bit`, `wide`.
#: A parenthetical that states a width by NAMING it: `- `data_in` (DATA_WIDTH bits)`.  Anchored to
#: the parenthesis, which is the whole of its safety: the same expression loose in a sentence would
#: read `the data bits` as a port `data` of `data-1:0`, and these descriptions are full of that.
#:
#: `_SYMBOLIC_BITS` is the same shape, matched against a declaration list's already-isolated
#: parenthetical; this one has to find its own, because `_inline_ports` hands its width readers the
#: parenthetical and the description concatenated.
#:
#: Without it, `colon`'s commentary rule below refused the line WHOLE — a parenthetical stating
#: neither a numeral nor a direction is commentary, and `DATA_WIDTH bits` is neither.  So
#: `sync_lifo_0001` lost `data_in` and `data_out` outright: a contract of six pins with the two the
#: design exists to move missing, and its `params` empty as a consequence, because
#: `_narrative_params` binds only names some port width refers to and no port width was left to
#: refer to `DATA_WIDTH`.
_SYMBOLIC_PAREN = re.compile(r"^\(\s*([A-Za-z_]\w*(?:\s*[-+*]\s*\w+)*)\s*[-\s]?\s*bits?\s*\)", re.I)
_WIDTHY = re.compile(r"^(?:\[[^\]]*\]|\d+\s*-?\s*bits?|\d+|bits?|wide|-)$", re.I)


def _norm_dir(t: str) -> str | None:
    """`Outputs` -> `output`, `bits` -> None.  Singular and plural both, for `_dir_claim`."""
    t = (t or "").lower().rstrip("s")
    return t if t in ("input", "output", "inout") else None


def _dir_claim(s: str) -> str | None:
    """`_dir_of`, restricted to a direction word that IS its own item in a property list.

    A direction word inside a parenthetical is a claim about the name *outside* it only when the
    parenthetical is a property list about that name -- `q (4 bits, output)`, `out (output)`,
    `data (8-bit input)`.  When the word has other words attached inside its own comma-item, the
    parenthetical is a sentence, or a declaration of something else, and the word before the
    bracket is just the last word of an English phrase:

        a continuous assignment statement (output out_assign)   -> declares `out_assign`
        in vibrate mode (input vibrate_mode = 1)                -> declares `vibrate_mode`
        driven by exactly one source (output of a gate)         -> declares nothing
        low for a long time (no sensors asserted, and all
            four outputs asserted)                              -> declares nothing

    Reading those as ports invented ten pins across eight VerilogEval prompts.  Nine were
    survivable: VerilogEval's harness connects by name, so an unconnected extra port on the
    emitted header is legal Verilog and the design passed anyway -- which is the bad part, since
    every gate was green about a contract with a pin the prose never declared.  The tenth was
    `Prob149_ece241_2013_q4`'s `time`, a Verilog keyword, and it took the design out at the
    oracle with a syntax error on line 1.

    The standalone-item test is the whole rule, and PLURALS ARE NOT PART OF IT.  A first cut
    also refused `inputs`/`outputs` on the theory that a plural is a noun about several things
    rather than a direction keyword about this one.  That is true inside a phrase -- it is what
    makes `all four outputs asserted` prose -- but the item test already refuses every such
    phrase, and refusing the plural on top of it dropped `fact` from
    `cvdp_copilot_factorial_0001`, whose declaration reads ``6- `fact` (Outputs): A 64-bit
    output``.  A parenthetical that is nothing but a direction word is a direction claim in
    whatever number it is written.
    """
    for item in re.split(r"[,;]", s or ""):
        toks = [t for t in re.split(r"[\s*`]+", item.strip().strip(".")) if t]
        dirs = [d for d in (_norm_dir(t) for t in toks) if d]
        if len(dirs) == 1 and all(_norm_dir(t) or _WIDTHY.match(t) for t in toks):
            return _DIR_WORD[dirs[0]]
    return None


def _widths_by_omission(ports: list[dict]) -> list[dict]:
    """In a list that states widths, a port stated without one is one bit.

    `data_in[7:0]` beside a bare `clk` is a positive statement about `clk` in that notation, not
    silence about it: the author wrote the range where there was a range to write.  Reading it as
    undetermined makes the contract refuse on four of six pins of a document that is not actually
    ambiguous, and the refusal teaches the next reader to stop believing refusals.

    The condition is the whole of the rule.  When NOTHING in the list carries a width the notation
    is not one that states them, silence means silence, and every port stays undetermined — a
    document that never mentions bit widths has not told anyone that its bus is one bit wide.

    A port carrying a `width_expr` is NOT silent and is skipped, even though its width is still
    `None` here: this runs before `_resolve_symbolic`, so every symbolic range is unresolved at
    this point and testing `width is None` alone reads `[C_S_AXI_DATA_WIDTH-1:0] axi_wdata` as an
    omission.  It stamped 1 bit on the address and data buses of `axil_precision_counter_0001` —
    a 32-bit bus recorded as 1 bit, with a reason string saying the author omitted the range they
    had in fact written.  That is worse than the refusal it replaces: `None` is caught downstream
    and a confident 1 is not.  Resolving these is `_resolve_symbolic`'s job, and a name it cannot
    bind stays undetermined, which is what the module rule at the top of this file promises.
    """
    if not any(p.get("width") for p in ports):
        return ports
    for p in ports:
        if p.get("width") is None and not p.get("width_expr"):
            p["width"] = 1
            p["width_from"] = "no range, in a list that gives ranges"
    return ports


#: `(WIDTH bits)` — a parenthetical width whose magnitude is a name.  Kept apart from
#: `_WIDTH_INLINE`, which only reads numbers: this one resolves to no width at all and exists so
#: that the refusal can say WHICH name went unanswered instead of "the prose states no width".
_SYMBOLIC_BITS = re.compile(r"^([A-Za-z_]\w*(?:\s*[-+*]\s*\w+)*)\s*[-\s]?\s*bits?$", re.I)


def _decl_contract(text: str, params: dict[str, int]) -> list[dict]:
    """The direction-led declaration list, as contract ports.

    The line parser is `iface_gate._decl_list_ports` and is not duplicated here — that file is the
    one both ends of the interface check share, and this module's whole argument for deriving the
    contract rather than having it transcribed is that the reader here and the reader in the gate
    are the same reader.  What is done HERE and not there is the arithmetic: directions normalised
    to `in`/`out`/`inout`, `[7:0]` and `(4 bits)` turned into 8 and 4 by `_eval_width`, and the
    stated-width rule of `_widths_by_omission` applied to the list as a whole.

    That last one is what makes this shape usable at all.  VerilogEval and ChipBench both open
    with "All input and output ports are one bit unless otherwise specified" and then write the
    width only where it is not one, so a reader that took silence for silence would refuse on
    three of `Prob067_countslow`'s four pins.  `_widths_by_omission` reaches the same answer from
    the notation rather than from that sentence, which is the right way round: the sentence is
    this template's, and the notation is every list's.

    A parenthetical that is not a width leaves the width unset rather than rejecting the line — a
    port declared with a comment where a width was expected is still a port, and dropping it would
    be the silent-loss failure this module exists to avoid.  `(WIDTH bits)`, which four ChipBench
    prompts carry, keeps the name as `width_expr` so the refusal can name it.
    """
    out = []
    for d in _decl_list_ports(text):
        w, expr = None, ""
        if d["range"]:
            w, expr = _eval_width(d["range"].strip("[]"), params)
        elif d["paren"]:
            wm = _WIDTH_INLINE.search(d["paren"])
            if wm and wm.group("range"):
                w, expr = _eval_width(wm.group("range"), params)
            elif wm:
                w = int(wm.group("n"))
            elif (sm := _SYMBOLIC_BITS.match(d["paren"])):
                expr = sm.group(1).strip()
        out.append({"name": d["name"], "dir": _DIR_WORD[d["dir"]], "width": w, "width_expr": expr,
                    "source": "declaration list"})
    return _widths_by_omission(out)


#: The default width, STATED.  "All input and output ports are one bit unless otherwise
#: specified" opens 152 of VerilogEval's 156 prompts and 40 of ChipBench's 45, and none of
#: RTLLM's 50.  `\s+` spans the newline because the template hard-wraps the sentence across two
#: lines more often than not.
_ONE_BIT_DEFAULT = re.compile(
    r"all\s+(?:the\s+)?(?:input\s+and\s+output\s+|i/?o\s+)?ports?\s+are\s+(?:one|1)[-\s]*bits?"
    r"\s+unless\s+otherwise\s+specified", re.I)


def _widths_by_statement(ports: list[dict], text: str) -> list[dict]:
    """A width the prose gives in a sentence rather than in a notation.

    `_widths_by_omission` infers the same 1 from how the list is written and declines when the
    list writes no widths at all -- correctly, because silence is silence.  This is the case where
    the document is not silent: it says, in English, in its first paragraph, what an unwritten
    width means.  Reading that sentence is not the guess this module refuses; refusing anyway is
    refusing to read.

    The difference is not cosmetic.  Every all-one-bit design in these two benchmarks -- a NOT
    gate, a D flip-flop, a state machine over single-bit inputs, 79 VerilogEval prompts and 20
    ChipBench ones -- writes no width anywhere, so `_widths_by_omission` leaves every port
    undetermined and `main()` exits 3 on a document that is not ambiguous at all.  A refusal that
    fires on half a benchmark teaches the next reader to stop believing refusals, which is the
    same failure as not refusing.

    Applied to the ASSEMBLED port list rather than inside any one shape's parser, because the
    sentence is a claim about the interface and not about the notation any particular pin was
    written in, and applied AFTER `_widths_by_omission` so the notation still wins where it spoke.
    """
    if not _ONE_BIT_DEFAULT.search(text):
        return ports
    for p in ports:
        if p.get("width") is None and not p.get("width_expr"):
            # `width_expr` set and width unresolved means a SYMBOLIC range -- `[DATA_WIDTH-1:0]`,
            # `(WIDTH bits)`.  That port is "otherwise specified": the prose named its width and
            # then never gave the name a value, and 1 is not the answer to that question.
            p["width"] = 1
            p["width_from"] = "the prose states that unspecified ports are one bit"
    return ports


#: A parameter block written as PROSE rather than fenced as code: `Parameter:` alone on a line,
#: then `WIDTH = 8` / `size = 4` / `DEPTH = 8;` beneath it.  `_PARAM_DECL` reads only inside
#: ```` ``` ```` blocks, which is where VerilogEval and ChipBench put their parameters and is NOT
#: where RTLLM puts its: 20 of RTLLM's 50 documents carry an unfenced block like this and none of
#: them fence it, so `params` came back empty on every one and every `[WIDTH-1:0]` those documents
#: declare stayed symbolic forever.  That is how `asyn_fifo` reached `05_simdiff` with its 8-bit
#: data bus recorded as `undetermined` — the prose says `WIDTH = 8` in as many words.
#: The `\d+[.)]` and `definitions?` are here on the argument `_OTHER_HEAD` already makes for the
#: same addition: a document that numbers one kind of heading numbers both.  `sync_lifo_0001` heads
#: its block `2. **Parameter Definitions**:` and missed on both counts at once.
_PARAM_HEAD = re.compile(r"^\s{0,4}(?:#{1,6}\s*)?(?:[-*+]\s*)?(?:\d+[.)]\s*)?(?:\*\*|`)?\s*"
                         r"(?:module\s+|design\s+)?parameters?"
                         r"(?:\s+(?:list|values?|declarations?|definitions?|settings?))?"
                         r"\s*:?\s*(?:\*\*|`)?\s*:?\s*$", re.I)
#: One row of such a block.  A NUMBER is required on the right: `Q: Number of fractional bits`
#: sits under `Input parameters:` in `fixed_point_adder` and is a description, not a value, and
#: reading it as one would put a width on a port whose width the document genuinely never fixes.
_PARAM_ROW = re.compile(r"^\s*(?:[-*+]\s*)?(?:\*\*|`)*([A-Za-z_]\w*)(?:\*\*|`)*\s*"
                        r"(?:=|:)\s*(?:\*\*|`)*\s*(\d+)\s*(?:\*\*|`)*\s*[;,.]?\s*$")
#: The same row with the value in a PARENTHESIS instead of after a colon, which is how both of the
#: documents that state a parameters block in bullets write it:
#:
#:     - `POLY_LENGTH` (default: 31)
#:     - `DATA_WIDTH` (default = 8): Specifies the bit-width of the data to be stored in the LIFO.
#:
#: The word `default` is required and does the work `_PARAM_ROW`'s end-anchor does there: it is what
#: separates a value from the constraint and range figures these lines are otherwise full of, so
#: nothing has to be assumed about what follows the parenthesis — and something must follow it in
#: the second shape, which is why this pattern deliberately does not anchor at the end.
_PARAM_ROW_PAREN = re.compile(r"^\s*(?:[-*+]|\d+[.)])\s*(?:\*\*|`)*([A-Za-z_]\w*)(?:\*\*|`)*\s*"
                              r"\(\s*default\s*[:=]?\s*(\d+)\s*\)", re.I)


#: A parameter declared in RUNNING PROSE with its default stated in words rather than as an
#: assignment.  Four shapes, all of them real, all on CVDP:
#:
#:     - `WIDTH` (Default 4, must be greater than 0): Bit-width of `A`, `B`
#:     - **`DATA_WIDTH`**: Width of the input data. Default value is 8 bits.
#:     - `GPIO_WIDTH = 8` (default, configurable). Defines the number of GPIO pins.
#:     - The default value of `DATA_WIDTH` is 64.
#:
#: Neither `_PARAM_DECL` (Verilog syntax only) nor `_PARAM_ROW` (`NAME = int` alone on a line under
#: a `Parameters:` heading) reads any of them, so `[DATA_WIDTH-1:0]` stayed symbolic on documents
#: that state the number plainly.  On CVDP that is 12 designs.
#:
#: There is no single pattern here because the value sits in a different place in each: before the
#: word `default` in one, after it in another, and after `is` in the fourth.  What holds them
#: together is the line, so the line is what gets matched and the value is chosen from it by the
#: rules in `_narrative_params`.
_PARAM_MENTIONS_DEFAULT = re.compile(r"\bdefaults?\b", re.I)


def _narrative_params(text: str, wanted: set[str]) -> dict[str, int]:
    """Defaults for parameters the document declares in a sentence.

    Restricted to `wanted` — the names some port's `width_expr` actually refers to — because the
    reading is loose by construction: a line that names something and says "default" also
    describes plenty of lines that declare no parameter.  `sorter_0001` carries
    `**Latency and Timing**: ... by default, consume multiple cycles` two bullets below its real
    `N` declaration, and the containment is the only thing that keeps it out.  A name no width
    expression refers to cannot change any port, so binding only those names keeps a loose reader
    from having loose consequences — the same trick `_iface_regions` plays on position, played on
    a value.

    A line must name EXACTLY ONE wanted parameter.  Two on one line and there is no way to tell
    which the number belongs to, and guessing would bind a width to the wrong name — worse than
    leaving it open, because the result is a plausible contract rather than a refusal.

    The value is then the first of these the line offers, in this order: `NAME = 8`, an integer
    after the word `default`, an integer after `is`.  The order is what separates
    ``- `WIDTH` (Default 4, must be greater than 0)`` — where `0` also follows `default` — from
    ``- `GPIO_WIDTH = 8` (default, configurable)``, where the value precedes the word entirely.
    """
    out: dict[str, int] = {}
    for line in text.split("\n"):
        if not _PARAM_MENTIONS_DEFAULT.search(line):
            continue
        here = [n for n in wanted if re.search(r"\b%s\b" % re.escape(n), line)]
        if len(here) != 1 or here[0] in out:
            continue
        name = here[0]
        tail = _PARAM_MENTIONS_DEFAULT.split(line, 1)[-1]
        for m in (re.search(r"\b%s\b\s*(?:=|:)\s*(?:\*\*|`)*\s*(\d+)" % re.escape(name), line),
                  re.search(r"(\d+)", tail),
                  re.search(r"\bis\b\s*(?:\*\*|`)*\s*(\d+)", line, re.I)):
            if m:
                out[name] = int(m.group(1))
                break
    return out


def _table_params(text: str) -> dict[str, int]:
    """Parameter defaults from a markdown table that has a `Default` column.

    The same documents that write their PINS as a table routinely write their PARAMETERS as one
    too, directly above:

        | Parameter   | Description                            | Default | Constraints |
        | `N`         | Number of input symbols                | 4       | >= 2 ...    |
        | `IN_WIDTH`  | Bit width of each input symbol (fixed) | 4       | Fixed at 4  |

    `_table_contract` reads the pin table and nothing read this one, so `bits[N*IN_WIDTH-1:0]`
    stayed symbolic on a document that states both numbers in a column headed `Default`.  Both
    CVDP `16qam_mapper` designs refused at `01_contract` for that reason alone.

    The name column must be headed `Parameter`.  Accepting a bare `Name` column beside a `Default`
    one would read the register maps these documents are full of — `| Register | Address | Default |`
    — as a parameter block, and a register's reset value is not a parameter's default.  Requiring
    the word costs nothing here: a table laid out for parameters says so.

    First value wins, as everywhere else in this file: a document that gives one parameter two
    values is contradicting itself, and taking the later one silently picks a side.
    """
    out: dict[str, int] = {}
    block: list[str] = []
    for line in text.split("\n") + [""]:
        if line.strip().startswith("|") and line.count("|") >= 3:
            block.append(line)
            continue
        if not block:
            continue
        blk, block = block, []
        cells = [[c.strip() for c in r.strip().strip("|").split("|")] for r in blk]
        cells = [c for c in cells if not all(re.fullmatch(r":?-{2,}:?", x or "-") for x in c)]
        if len(cells) < 2:
            continue
        head = [c.lower() for c in cells[0]]
        ncol = next((i for i, h in enumerate(head) if "param" in h), None)
        vcol = next((i for i, h in enumerate(head) if "default" in h), None)
        if ncol is None or vcol is None:
            continue
        for r in cells[1:]:
            if ncol >= len(r) or vcol >= len(r):
                continue
            nm = _ident(r[ncol])
            # A cell holding no number is a parameter the table declines to fix — `-`, blank, or
            # a sentence.  It is not a default of zero.
            v = re.search(r"\d+", r[vcol])
            if nm and v:
                out.setdefault(nm, int(v.group()))
    return out


def _prose_params(text: str) -> dict[str, int]:
    """Parameter defaults from an unfenced `Parameter:` block.

    Scanned forward from the heading and stopped by the first line that is neither a `NAME = int`
    row nor blank, so the block cannot run on into `Implementation:` and pick up the assignments in
    the narrative there — `q <= (q >> 1)` and `ST_nt = s0` are not parameter defaults.

    Blank lines do not stop it: RTLLM separates the block from its heading with one about as often
    as not.  A line indented DEEPER than the rows does not stop it either — it is a property of the
    row above it, which is how `prbs_gen_0003` writes its block:

        - `POLY_LENGTH` (default: 31)
          - **Type:** Integer parameter
          - **Description:** Length of the polynomial (number of shift register stages).

    Stopping at the first `**Type:**` read one parameter of four and left `POLY_LENGTH` and
    `POLY_TAP` unknown to a module whose harness overrides both.  The depth is taken from the first
    row matched rather than assumed, so the containment the block relies on is unchanged for
    everything at or left of that column: a `Behaviour:` heading is not indented past the list it
    follows, and still ends it.

    Only the FIRST value for a name is kept, on the same rule as everywhere else in this
    file: a document that gives its parameter two values is contradicting itself, and taking the
    later one silently picks a side.
    """
    out: dict[str, int] = {}
    lines = text.split("\n")
    i = 0
    while i < len(lines):
        if not _PARAM_HEAD.match(lines[i]):
            i += 1
            continue
        i += 1
        depth = None
        while i < len(lines):
            line = lines[i]
            if not line.strip():
                i += 1
                continue
            m = _PARAM_ROW.match(line) or _PARAM_ROW_PAREN.match(line)
            if not m:
                if depth is not None and len(line) - len(line.lstrip()) > depth:
                    i += 1
                    continue
                break
            if depth is None:
                depth = len(line) - len(line.lstrip())
            out.setdefault(m.group(1), int(m.group(2)))
            i += 1
    return out


def _resolve_symbolic(ports: list[dict], params: dict[str, int]) -> list[dict]:
    """Second pass over widths the prose NAMED but this file could not yet evaluate.

    The shape parsers each resolve what they can as they go, and two of the three can only pass an
    empty parameter map while doing it: `_table_contract` and `_inline_ports` run before anything
    has read a parameter block, because the block is somewhere else in the document.  So a port
    written `[WIDTH-1:0]` comes out of them with `width: None` and `width_expr: "WIDTH-1:0"`, which
    is not a refusal — it is a note saying "ask again once you know WIDTH".  This asks again.

    A `width_expr` with no colon is tried as a range first and as a bit COUNT second, which is the
    `(WIDTH bits)` form `_decl_contract` stores bare.  The two readings collide only on a symbolic
    single-bit select — `[WIDTH]` meaning bit number WIDTH — which appears nowhere in these corpora
    against four ChipBench prompts that write `(WIDTH bits)`, so the count reading is the useful
    one.  A range that still will not evaluate is left exactly as it was.
    """
    for p in ports:
        expr = p.get("width_expr")
        if p.get("width") is not None or not expr:
            continue
        w = _eval_width(expr, params)[0]
        if w is None and ":" not in expr:
            w = _eval_int(expr, params)
        if w is not None and w > 0:
            p["width"] = w
            p["width_from"] = f"`{expr}` resolved against the prose's own parameter block"
    return ports


#: `reg [7:0] q` — a width the document gives in its implementation narrative rather than in its
#: port list.  Anchored on the direction/storage keyword and requiring an explicit range, so the
#: assignments and comparisons those sections are full of cannot match.
_BODY_DECL = re.compile(r"\b(?:input|output|inout|reg|wire|logic)\b"
                        r"(?:\s+(?:reg|wire|logic|signed|unsigned))*\s*"
                        r"\[([^\]]*)\]\s*([A-Za-z_]\w*)\b")


def _widths_from_body(ports: list[dict], text: str, params: dict[str, int]) -> list[dict]:
    """A port's width, taken from a declaration of that same port further down the document.

    RTLLM writes its pin list with no widths at all and then declares the storage behind it in the
    `Implementation:` section: `right_shifter` lists `q: Output signal representing the result` and
    says, eleven lines later, "The register is defined as reg [7:0] q".  Eight bits, stated, in
    English, in the same document — and unreadable to every shape parser above, all three of which
    stop at the interface region `_iface_regions` marks out.

    Matched on the port's EXACT name and applied only where the width is otherwise unknown, so a
    document that declares its ports properly is untouched by this and an internal signal that
    merely resembles a port name cannot outrank a stated width.  It can still collide with an
    internal register that happens to share a port's name and not its width; that is a real risk
    and it is taken deliberately, because the alternative on these documents is not a narrower
    answer but no answer.
    """
    want = {p["name"] for p in ports if p.get("width") is None}
    if not want:
        return ports
    found: dict[str, tuple[int, str]] = {}
    for m in _BODY_DECL.finditer(text):
        name = m.group(2)
        if name not in want or name in found:
            continue
        w, expr = _eval_width(m.group(1), params)
        if w is not None and w > 0:
            found[name] = (w, expr)
    for p in ports:
        if p["name"] in found:
            w, expr = found[p["name"]]
            p["width"] = w
            p["width_expr"] = p.get("width_expr") or expr
            p["width_from"] = "declared with a range in the document body"
    return ports


def _widths_by_default(ports: list[dict]) -> list[dict]:
    """The last resort: a port the document never said anything about at all is one bit.

    This is the rule `contract.py` refused for most of its life, and the module docstring still
    explains why — a derived contract that guesses is worse than no contract.  The reason it is
    here now is that the refusal was measured, and on RTLLM it cost 28 authoring sessions and
    roughly a fifth of the benchmark's API spend to reach `05_simdiff` on 13 designs and stop.

    What makes it defensible is everything that now runs BEFORE it.  `_widths_by_omission` reads
    the notation, `_widths_by_statement` reads the sentence, `_resolve_symbolic` reads the
    parameter block and `_widths_from_body` reads the implementation narrative.  A port that
    survives all four is one the document mentions by name and never characterises, and one bit is
    what Verilog itself says an undecorated port is.  Of the 15 RTLLM designs whose contract was
    entirely undetermined, that describes 8, and every one of the 8 is 1-bit in the reference.

    A port with a `width_expr` is NOT covered, exactly as in `_widths_by_statement`: `[N-1:0]` with
    no value for `N` is a document that named its width and declined to fix it, and 1 is not the
    answer to that question.  `fixed_point_adder` is that case and still refuses, correctly — its
    operands are 32 bits and no sentence in it says so.

    This does not make the guess invisible.  `width_from` records that the number was defaulted
    rather than read, so a reader of `contracts/<key>.json` can always tell the two apart, and
    `RAM` — whose address and data pins are 8 and 6 bits in the reference and unstated in the pin
    list — comes out of here as eight one-bit ports, wrong, and says so in the field.
    """
    for p in ports:
        if p.get("width") is None and not p.get("width_expr"):
            p["width"] = 1
            p["width_from"] = ("defaulted: the prose states no width for this port and names no "
                               "parameter for it")
    return ports


def _clock_and_reset(ports: list[dict], text: str) -> tuple[str | None, dict | None]:
    """The clock pin's name, and the reset pin with its polarity and synchronicity.

    Named here rather than left to the authors because both need the same answer and the answer is
    mechanical.  The polarity is read from the prose, and when the prose does not give it the field
    is `null` — a reset whose polarity was guessed is a design that is wrong exactly half the time,
    and half is not a rate anything downstream would notice as a pattern.
    """
    ins = [p["name"] for p in ports if p.get("dir") == "in"]
    clk = next((n for n in ins if n.lower() in ("clk", "clock", "i_clk", "clk_i", "clki")), None)
    if clk is None:
        clk = next((n for n in ins if re.search(r"\bclk|clock", n, re.I)), None)
    rst = next((n for n in ins if re.search(r"rst|reset|clr|clear", n, re.I)), None)
    if rst is None:
        return clk, None
    low = text.lower()
    active = ("low" if (re.search(r"active[\s\-_]*low", low)
                        or re.search(r"\bn(?:_)?" + re.escape(rst.lower()) + r"\b", low)
                        or rst.lower().endswith("_n") or rst.lower().startswith("n"))
              else "high" if re.search(r"active[\s\-_]*high", low) else None)
    sync = ("async" if re.search(r"asynchronous(?:ly)?\s+reset|async(?:hronous)?\s+reset", low)
            else "sync" if re.search(r"synchronous(?:ly)?\s+reset|sync(?:hronous)?\s+reset|"
                                     r"on\s+the\s+(?:rising|positive)\s+edge.{0,60}reset", low)
            else None)
    return clk, {"name": rst, "active": active, "sync": sync}


def derive(prose: str, key: str, toplevel: str | None = None) -> dict:
    """The contract, plus everything the prose failed to determine about it."""
    code = _code_contract(prose, toplevel)
    module = (code or {}).get("module") or toplevel or key
    params = dict((code or {}).get("params") or {})
    # The prose's own parameter block, added BEFORE the shapes run so `_decl_contract` can resolve
    # a range against it on the first pass.  A fenced header still wins on a name they both give:
    # a document that writes its parameters as code has committed to those values, and the block
    # above is the summary.
    for k, v in _prose_params(prose).items():
        params.setdefault(k, v)
    # And the same block written as a table.  After `_prose_params` only so that a document
    # carrying both keeps the same first-value-wins order it would have had; in practice no
    # document in these corpora writes its parameters twice.
    for k, v in _table_params(prose).items():
        params.setdefault(k, v)
    decl = _decl_contract(prose, params)
    table = _table_contract(prose)
    inline = _inline_ports(prose)

    # The code header wins on ORDER and on width, because it is the document writing the interface
    # out as code and it is the only shape that carries either.  The declaration list is next and
    # is nearly as good — it gives direction, width and order too, and is simply that same header
    # written as prose; on VerilogEval and ChipBench it is the ONLY shape present, and a reader
    # without it reported zero ports on 153 of 156 prompts.  The table contributes names the
    # header does not have, appended in the order the table gives them — a spec that heads its
    # pins in a table and writes no skeleton is common, and dropping it would leave nothing.  The
    # running-prose form is read last and only fills what the others left empty: it is the
    # loosest parser here and the one most likely to pick up a word that is not a pin.
    ports: list[dict] = []
    have = set()
    for p in list((code or {}).get("ports", [])) + decl:
        if p["name"] not in have:
            have.add(p["name"])
            ports.append(dict(p))
    dmap = {p["name"]: p for p in decl}
    tmap = {p["name"]: p for p in table}
    imap = {p["name"]: p for p in inline}
    for p in ports:                       # fill gaps from the table without overriding the header
        for src, label in ((dmap.get(p["name"]), "declaration list"),
                           (tmap.get(p["name"]), "table"), (imap.get(p["name"]), "prose")):
            # A port does not fill its own gaps: when the header is absent the declaration list IS
            # the seed, and crediting it a second time would write `declaration list + declaration
            # list (width)` into a field whose whole job is to say where a number came from.
            if not src or p["source"].startswith(src["source"]):
                continue
            if p.get("dir") is None and src.get("dir") is not None:
                p["dir"], p["source"] = src["dir"], p["source"] + f" + {label} (direction)"
            if p.get("width") is None and src.get("width") is not None:
                p["width"] = src["width"]
                p["width_expr"] = p.get("width_expr") or src.get("width_expr", "")
                p["source"] += f" + {label} (width)"
    for t in table + inline:
        if t["name"] not in have:
            have.add(t["name"])
            ports.append(dict(t))

    # A name the document declares as a PARAMETER is not a port, however port-shaped the line it
    # was read off looks.  The loosest of the three shapes picks these up routinely — `WIDTH`,
    # `CLK_FREQ`, `TAG_ID_1`, `OUTPUT_DATA_WIDTH`, and the `N` of `fixed_point_substractor`, on
    # eight designs across two benchmarks — and until now the damage was bounded, because a
    # phantom port carries no width and the run stopped at the refusal that caused.
    #
    # `_widths_by_default` removes that bound: the phantom gets one bit like anything else, the
    # refusal never fires, and a contract with an invented pin in it is precisely the failure this
    # module exists to prevent — both authors build against it, agree perfectly, and the gates
    # compare them only to each other.  So the filter has to be here, and it has to run BEFORE the
    # default, not after it.
    declared = prose_iface(prose, module)
    params_declared = declared["params"] | set(params)
    ports = [p for p in ports if p["name"] not in params_declared]
    have -= params_declared

    # And the same argument for a name that is not a parameter either, but a heading: `Purpose`,
    # `Width`, `Description`, `Result`.  Same position and for the same reason — before
    # `_widths_by_default` can hand the phantom a bit and retire the refusal that used to bound it.
    labels = _label_phantoms(ports, prose)
    ports = [p for p in ports if p["name"] not in labels]
    have -= labels

    # A parameter whose default the document states in a sentence rather than as an assignment.
    # Read HERE, not beside `_prose_params` above, because it is scoped to the names some port's
    # `width_expr` actually refers to and those expressions do not exist until the shapes have
    # run.  `setdefault`, so a value written as code or in a `Parameters:` block still wins: those
    # are the document committing to a number, and this is the document mentioning one.
    for _k, _v in _narrative_params(
            prose, {n for p in ports for n in re.findall(r"[A-Za-z_]\w*", p.get("width_expr") or "")}
    ).items():
        params.setdefault(_k, _v)

    # Four readings of a width, weakest last, and each one only fills what the ones above left
    # empty.  The order is the whole of the rule: the notation beats the sentence, the sentence
    # beats the parameter block, the parameter block beats the narrative, and all four beat the
    # default — which is a guess, is marked as one in `width_from`, and never overrides anything.
    _resolve_symbolic(ports, params)
    _widths_from_body(ports, prose, params)
    _widths_by_statement(ports, prose)
    _widths_by_default(ports)

    # Names the prose declares that neither structured shape produced — a bulleted interface list,
    # usually.  They are reported rather than added: a name with no direction and no width is not a
    # port, it is a hole, and adding it as a one-bit input would be the guess this file refuses.
    unstructured = sorted(declared["ports"] - have - params_declared)

    undetermined = [{"name": p["name"], "what": "direction",
                     "why": "no direction column and no direction keyword in a code header"}
                    for p in ports if p.get("dir") is None]
    undetermined += [{"name": p["name"], "what": "width",
                      "why": (f"the range `[{p['width_expr']}]` is symbolic and the prose gives no "
                              f"default for it" if p.get("width_expr")
                              else "the prose states no width for this port")}
                     for p in ports if p.get("width") is None]
    undetermined += [{"name": n, "what": "direction and width",
                      "why": "declared in prose only (a bulleted list or a bare mention), which "
                             "gives neither"} for n in unstructured]

    return {
        "key": key,
        "module": module,
        "ports": ports,
        "params": [{"name": k, "default": v} for k, v in sorted(params.items())]
                  + [{"name": n, "default": None} for n in sorted(declared["params"] - set(params))],
        "clock": _clock_and_reset(ports, prose)[0],
        "reset": _clock_and_reset(ports, prose)[1],
        "undetermined": undetermined,
        # `prose_iface` computes this over the same two shapes, and it is a fact about the
        # DOCUMENT: a name that appears in the skeleton and not in the table (or the reverse) means
        # the specification contradicts itself about its own interface.  Neither reading is
        # preferred here; the run stops and a person decides.
        "conflicts": declared["self_conflict"],
        "derived_from": {"code_header": bool(code and code.get("ports")),
                         "declaration_list": bool(decl),
                         "direction_table": bool(table),
                         "prose_declaration": bool(inline),
                         "prose_only": unstructured},
        "how": "derived by leanrtl/contract.py from the prose alone — no agent transcribed it, "
               "and no testbench, reference implementation or dataset file was read",
    }


def main(argv: list[str] | None = None) -> int:
    ap = argparse.ArgumentParser(description=__doc__,
                                 formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument("--ws", required=True)
    ap.add_argument("--key", help="default: the key in the workspace's provenance stamp")
    ap.add_argument("--toplevel", help="default: the stamp's toplevel, else the key")
    ap.add_argument("--allow-undetermined", action="store_true",
                    help="write the contract even where the prose left a port's direction or "
                         "width open. The gap is recorded in `undetermined` either way; this "
                         "only decides whether the run continues past it.")
    a = ap.parse_args(argv)

    ws = os.path.abspath(os.path.expanduser(a.ws))
    from common import provenance                                            # noqa: E402
    stamp = provenance.read(ws) or {}
    key = a.key or stamp.get("key")
    if not key:
        sys.exit("contract: no --key, and this workspace has no provenance stamp")
    spec = os.path.join(ws, "specs", key + ".spec.txt")
    if not os.path.isfile(spec):
        sys.exit(f"contract: no prose at {os.path.relpath(spec, ws)}")

    c = derive(open(spec, errors="replace").read(), key,
               a.toplevel or stamp.get("toplevel") or key)
    dest = os.path.join(ws, "contracts", key + ".json")
    os.makedirs(os.path.dirname(dest), exist_ok=True)
    json.dump(c, open(dest, "w"), indent=1)

    print(f"contract: `{c['module']}` — {len(c['ports'])} port(s), {len(c['params'])} parameter(s)")
    for p in c["ports"]:
        w = p["width"] if p["width"] is not None else "?"
        e = f"  [{p['width_expr']}]" if p.get("width_expr") else ""
        # A defaulted width is printed as a guess, because it is one.  The number is the same
        # either way and the difference is the whole of what a reader needs to weigh.
        g = "  (defaulted)" if str(p.get("width_from", "")).startswith("defaulted") else ""
        print(f"    {p['name']:24} {str(p.get('dir') or '?'):5} {str(w):>4} bit{e}{g}")
    if c["clock"]:
        print(f"  clock  {c['clock']}")
    if c["reset"]:
        r = c["reset"]
        print(f"  reset  {r['name']}  active-{r['active'] or '?'}  {r['sync'] or '?'}")
        if not (r["active"] and r["sync"]):
            print("         the prose does not say; this stays open and the specification author "
                  "must record the reading it takes")
    print(f"  wrote {os.path.relpath(dest, ws)}")

    if c["conflicts"]:
        print("\nTHE PROSE CONTRADICTS ITSELF about its own interface: "
              + ", ".join(c["conflicts"])
              + "\n  A name is in the code skeleton and not in the direction table, or the "
                "reverse.\n  Neither reading is preferred here.  Both authors would follow the "
                "same one and\n  agree with each other about the wrong design.")
    for u in c["undetermined"]:
        print(f"\nUNDETERMINED  {u['name']} — {u['what']}\n  {u['why']}")

    if not c["ports"]:
        # An empty contract is the shape of every parser failure here, and it is the shape most
        # likely to be read as success: zero missing ports, zero undetermined fields, zero
        # conflicts, exit 0.  A four-line counter specification whose pins were stated in running
        # prose produced exactly that, and nothing downstream would have noticed — S and D would
        # each have invented an interface, agreed with neither, and the emitted module would have
        # failed a testbench for reasons pointing nowhere near this file.
        #
        # A module with no ports is not a design.  So this is an error and not a warning, and
        # `--allow-undetermined` does not cover it: that flag says "carry a known gap forward as a
        # declared assumption", and there is nothing here to declare.
        print("\ncontract: NO PORTS FOUND.  This is a parse failure, not a portless design.\n"
              "  Three shapes are read — a ```verilog module header, a markdown table with a\n"
              "  direction column, and a running-prose declaration carrying a direction word.\n"
              "  This document matched none of them.  Nothing downstream can detect that: both\n"
              "  authors would invent an interface and the gates only compare them to each other.")
        return 3

    if not any(p.get("dir") in ("out", "inout") for p in c["ports"]):
        # The same argument as above, one step weaker and one step later: the shapes DID match,
        # and what they produced drives nothing.  A module with no output and no inout computes
        # nothing observable, so there is nothing for a specification to be a specification OF.
        #
        # This is the failure that is invisible downstream, which is why it belongs here and not
        # to a gate.  Every gate still passes on such a design: it builds, `proves_impl` proves an
        # `outputs := []` law, `undriven_nets` has no net to find undriven, `axiom_clean` and
        # `zero_sorry` are about a proof that is true and empty.  The one step that notices is
        # `simdiff`, and what it reports is `vacuous` — 0 checked — which reads as a simulation
        # problem, forty minutes of authoring after the interface was already wrong.
        #
        # `verilogeval/Prob031_dff` is the observed case.  Its interface block reads `- input clk`,
        # `- input d`, `- input q`, and `q` is the flip-flop's output; the reference declares
        # `output reg q`.  The reader was right about the document and the document was wrong, and
        # the whole run was spent finding that out.  Refusing here does not win the design — no
        # reading of that prose does, and it is recorded as `spec-contradicts-reference` in the
        # benchmark's `KNOWN_DEFECTS.json` — but it says so in eight seconds instead of forty
        # minutes, and it says it about the interface rather than about the simulator.
        #
        # Not covered by `--allow-undetermined`, for the reason the no-ports guard gives: that
        # flag carries a KNOWN gap forward as a declared assumption, and "which of these inputs
        # was meant to be the output" is not a gap the document left open — it is a claim the
        # document made and got wrong.  Naming a direction here would be the guess this module
        # exists to refuse.
        print("\ncontract: NO OUTPUT PORTS.  Every port this document declares is an `input`.\n"
              "  A module that drives nothing is not a design, and nothing downstream will say\n"
              "  so: the gates would all pass on an empty output law and `simdiff` would report\n"
              "  `vacuous` after the authoring is already paid for.\n"
              "  Read as declared: "
              + ", ".join(f"{p['name']} ({p.get('dir') or '?'})" for p in c["ports"]) + "\n"
              "  If the prose names one of these as an output, fix the prose; this file will not\n"
              "  pick which one.")
        return 3

    if (c["conflicts"] or c["undetermined"]) and not a.allow_undetermined:
        print("\ncontract: refusing.  A derived contract that guesses is worse than none: both "
              "authors\n  would build against the same guess, agree perfectly, and mean nothing "
              "about the design.\n  Fix the prose, or pass --allow-undetermined and carry the "
              "gap forward as a declared\n  assumption rather than a default.")
        return 3
    return 0


if __name__ == "__main__":
    sys.exit(main())
