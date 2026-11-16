"""Targeted lowering for dynamic slices needing explicit out-of-range branches."""
import copy
import json
from pathlib import Path

from .importer import parameter
from .pipeline import run, save_json


def _restore_port_order(ports, original_order):
    """Undo Yosys JSON key sorting without losing newly introduced ports."""
    return {
        name: ports[name] for name in original_order if name in ports
    } | {
        name: port for name, port in ports.items() if name not in original_order
    }


def expand_slices(directory, design, top):
    # Yosys writes JSON object keys alphabetically.  A slice-expansion round
    # trip must not therefore change the observable HDL port order: trace
    # refinement represents outputs as lists and the Verilog emitter also uses
    # this order for the module header.
    port_order = list(design["modules"][top].get("ports", {}))
    selected = []
    for name, cell in design["modules"][top].get("cells", {}).items():
        if cell["type"] != "$shiftx": continue
        con = cell["connections"]
        maximum = sum(1 << i for i, b in enumerate(con["B"]) if b != "0")
        if (parameter(cell, "B_SIGNED") and con["B"][-1] != "0") or maximum + len(con["Y"]) > len(con["A"]):
            selected.append(name)
    if not selected:
        return design, {"status": "not_needed"}
    out = Path(directory)
    marked = copy.deepcopy(design)
    attribute = "v2lean_expand_slice"
    while any(attribute in c.get("attributes", {}) for c in marked["modules"][top]["cells"].values()):
        attribute += "_"
    for name in selected:
        marked["modules"][top]["cells"][name].setdefault("attributes", {})[attribute] = "1"
    save_json(out / "slices_input.json", marked)
    (out / "slices.ys").write_text(f"""read_json slices_input.json
techmap a:{attribute}
opt_expr
opt_clean
check -assert
write_json -noscopeinfo slices_output.json
""")
    run(["yosys", "-Q", "-T", "-s", "slices.ys"], out, out / "slices.log")
    lowered = json.loads((out / "slices_output.json").read_text())
    ports = lowered["modules"][top].get("ports", {})
    lowered["modules"][top]["ports"] = _restore_port_order(ports, port_order)
    return lowered, {"status": "expanded", "cells": selected,
        "scope": "only slices without a static in-range bound; retain generated X for the separate independence check"}
