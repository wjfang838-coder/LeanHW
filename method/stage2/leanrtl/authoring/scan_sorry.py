#!/usr/bin/env python3
"""Layer-2 source scan: find real `sorry` / `admit` / `sorryAx` uses and user-declared
`axiom`s in Lean sources, ignoring comments and string literals.

  scan_sorry.py <dir-or-file> [...]

Exit 0 iff clean.  Prints each offending location as  path:line: token.

This replaces the old raw grep, which (a) false-positived on doc comments that merely
mention `sorry`, and (b) missed the identifier `sorryAx` and user `axiom` declarations.
"""
import os, re, sys

TOKEN_RE = re.compile(r"\bsorry\b|\badmit\b|\bsorryAx\b")
AXIOM_RE = re.compile(r"^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+|unsafe\s+)*axiom\s")


def strip_comments_and_strings(src: str) -> str:
    """Blank out nested block comments, line comments, and string literals,
    preserving newlines so line numbers survive."""
    out = []
    i, n = 0, len(src)
    depth = 0          # block-comment nesting
    in_line = False    # line comment
    in_str = False     # double-quoted string
    while i < n:
        c = src[i]
        nxt = src[i + 1] if i + 1 < n else ""
        if in_line:
            if c == "\n":
                in_line = False
                out.append("\n")
            else:
                out.append(" ")
            i += 1
        elif depth > 0:
            if c == "/" and nxt == "-":
                depth += 1
                out.append("  ")
                i += 2
            elif c == "-" and nxt == "/":
                depth -= 1
                out.append("  ")
                i += 2
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        elif in_str:
            if c == "\\":
                out.append("  ")
                i += 2
            elif c == '"':
                in_str = False
                out.append(" ")
                i += 1
            else:
                out.append("\n" if c == "\n" else " ")
                i += 1
        else:
            if c == "/" and nxt == "-":
                depth = 1
                out.append("  ")
                i += 2
            elif c == "-" and nxt == "-":
                in_line = True
                out.append("  ")
                i += 2
            elif c == '"':
                in_str = True
                out.append(" ")
                i += 1
            else:
                out.append(c)
                i += 1
    return "".join(out)


def scan_file(path: str):
    with open(path, encoding="utf-8") as f:
        src = f.read()
    code = strip_comments_and_strings(src)
    hits = []
    for lineno, line in enumerate(code.split("\n"), 1):
        m = TOKEN_RE.search(line)
        if m:
            hits.append((path, lineno, m.group(0)))
        elif AXIOM_RE.match(line):
            hits.append((path, lineno, "axiom declaration"))
    return hits


def main(argv):
    targets = argv or ["LeanRTL"]
    hits = []
    for t in targets:
        if os.path.isfile(t):
            hits += scan_file(t)
        else:
            for root, _dirs, files in os.walk(t):
                for fn in sorted(files):
                    if fn.endswith(".lean"):
                        hits += scan_file(os.path.join(root, fn))
    for path, lineno, tok in hits:
        print(f"{path}:{lineno}: {tok}")
    return 1 if hits else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
