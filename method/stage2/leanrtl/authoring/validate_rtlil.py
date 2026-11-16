#!/usr/bin/env python3
"""Layer 4: structural validity of LeanRTL-emitted RTLIL JSON.

Checks the JSON shape Yosys expects, independent of Yosys itself, so that a malformed
extraction is diagnosed before the Yosys backend layer.  Exit 0 = valid."""
import json, sys

CONST_BITS = {"0", "1", "x", "z"}


def err(msg):
    print(f"validate_rtlil: ERROR: {msg}", file=sys.stderr)
    sys.exit(1)


def check_bit(b, ctx, nets):
    if isinstance(b, int):
        if b < 2:
            err(f"{ctx}: net id {b} < 2 (0/1 are reserved; use string constants)")
        nets.add(b)
    elif isinstance(b, str):
        if b not in CONST_BITS:
            err(f"{ctx}: bad constant bit {b!r} (expected one of {CONST_BITS})")
    else:
        err(f"{ctx}: bit {b!r} is neither an int net id nor a constant string")


def main(path):
    with open(path) as f:
        d = json.load(f)
    if "modules" not in d or not isinstance(d["modules"], dict):
        err("top-level 'modules' object missing")
    if not d["modules"]:
        err("design contains no modules")
    for mname, m in d["modules"].items():
        for key in ("ports", "cells", "netnames"):
            if key not in m or not isinstance(m[key], dict):
                err(f"module {mname}: missing/invalid '{key}'")
        nets = set()
        # ports
        for pname, p in m["ports"].items():
            if p.get("direction") not in ("input", "output", "inout"):
                err(f"module {mname} port {pname}: bad direction {p.get('direction')!r}")
            if not isinstance(p.get("bits"), list) or not p["bits"]:
                err(f"module {mname} port {pname}: 'bits' must be a non-empty list")
            for b in p["bits"]:
                check_bit(b, f"{mname}.{pname}", nets)
        # cells
        for cname, c in m["cells"].items():
            if not isinstance(c.get("type"), str) or not c["type"]:
                err(f"module {mname} cell {cname}: missing 'type'")
            conns = c.get("connections", {})
            if not isinstance(conns, dict):
                err(f"module {mname} cell {cname}: 'connections' must be an object")
            for port, bits in conns.items():
                if not isinstance(bits, list):
                    err(f"module {mname} cell {cname}.{port}: connection must be a list")
                for b in bits:
                    check_bit(b, f"{mname}.{cname}.{port}", nets)
            # width params, if present, must be 32-char binary strings
            for k, v in c.get("parameters", {}).items():
                if k.endswith("WIDTH") or k.endswith("SIGNED") or k in ("WIDTH", "CLK_POLARITY"):
                    if not (isinstance(v, str) and set(v) <= {"0", "1"}):
                        err(f"module {mname} cell {cname}: param {k}={v!r} not a binary string")
        # netnames
        for nname, n in m["netnames"].items():
            for b in n.get("bits", []):
                check_bit(b, f"{mname}.netname.{nname}", nets)
    print(f"validate_rtlil: OK ({path})")
    return 0


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("usage: validate_rtlil.py <design.rtlil.json>", file=sys.stderr)
        sys.exit(2)
    sys.exit(main(sys.argv[1]))
