"""Prove internal lowering-generated unknowns unobservable before removing them.

Each X occurrence is a separate arbitrary bit. All original outputs and storage
input cones must be independent of every such bit, for all inputs and arbitrary
Q. Observable unknowns are rejected. This is a two-state noninterference check,
not a four-state Verilog semantics theorem; callers must reject explicit source
X/Z constants, and the original HDL still requires final SEC.
"""
import copy
from pathlib import Path

from .importer import require
from .pipeline import digest, run, save_json
from .statecheck import STATE_TYPES, cut


def abstract_shared_arithmetic(gold, gate, unknown_bits):
    """Overapproximate identical, X-independent expensive arithmetic by inputs.

    A shared arbitrary result includes every value of the original operation.
    Never share an abstraction whose operands depend on any unknown occurrence.
    The returned replacement design remains concrete; only the proof miter uses
    these extra inputs.
    """
    tainted = set(unknown_bits)
    changed = True
    while changed:
        previous = len(tainted)
        for cell in gold["cells"].values():
            directions = cell["port_directions"]
            if any(b in tainted for p, bs in cell["connections"].items() if directions[p] == "input" for b in bs):
                tainted.update(b for p, bs in cell["connections"].items() if directions[p] == "output" for b in bs)
        changed = len(tainted) != previous
    abstracted = []
    for name, cell in list(gold["cells"].items()):
        if cell["type"] not in ("$mul", "$div", "$mod"): continue
        con = cell["connections"]
        if any(b in tainted for p, bs in con.items() if cell["port_directions"][p] == "input" for b in bs): continue
        require(cell == gate["cells"][name], "arithmetic abstraction must be structurally identical")
        require(set(p for p, direction in cell["port_directions"].items() if direction == "output") == {"Y"}, "unexpected arithmetic outputs")
        label = f"v2lean_unknown_arithmetic_{len(abstracted)}"
        for module in (gold, gate):
            require(label not in module["ports"] and label not in module["netnames"], "arithmetic abstraction name collision")
            del module["cells"][name]
            module["ports"][label] = {"direction": "input", "bits": con["Y"]}
            module["netnames"][label] = {"bits": con["Y"], "hide_name": 0, "attributes": {}}
        abstracted.append({"cell": name, "type": cell["type"], "input": label, "bits": con["Y"]})
    return abstracted


def eliminate(directory, design, top):
    out = Path(directory)
    module = design["modules"][top]
    occurrences = [(n, p, i) for n, c in sorted(module.get("cells", {}).items())
                   for p, bits in sorted(c["connections"].items()) for i, b in enumerate(bits) if b in ("x", "z")]
    if not occurrences:
        return design, {"status": "not_needed"}
    require(all(b not in ("x", "z") for p in module["ports"].values() for b in p["bits"]), "unknown value at a public port")
    require(not module.get("memories") and not any(c["type"].startswith("$mem") for c in module["cells"].values()), "unknown proof requires fully lowered storage")
    gold, gate = copy.deepcopy(module), copy.deepcopy(module)
    used = set(module["ports"]) | set(module["netnames"])
    unknown = "v2lean_unknown_inputs"
    require(unknown not in used, "unknown-proof name collision")
    buses = [n["bits"] for group in (module["ports"], module["netnames"]) for n in group.values()]
    buses += [bs for c in module["cells"].values() for bs in c["connections"].values()]
    first = 1 + max((b for bs in buses for b in bs if type(b) is int), default=1)
    bits = list(range(first, first + len(occurrences)))
    for index, (name, port, offset) in enumerate(occurrences):
        require(module["cells"][name]["port_directions"][port] == "input", "unknown value drives a cell output")
        gold["cells"][name]["connections"][port][offset] = bits[index]
        gate["cells"][name]["connections"][port][offset] = "0"
    replacement = copy.deepcopy(design)
    replacement["modules"][top] = copy.deepcopy(gate)
    for side in (gold, gate):
        side["ports"][unknown] = {"direction": "input", "bits": bits}
        side["netnames"][unknown] = {"bits": bits, "hide_name": 0, "attributes": {}}
    states = []
    for name, cell in sorted(module["cells"].items()):
        if cell["type"] in STATE_TYPES:
            qname = f"v2lean_unknown_q_{len(states)}"
            require(qname not in used, "unknown-proof state name collision")
            states.append({"cell": name, "register": qname})
    gold, gold_contract = cut(gold, states, emitted=False)
    gate, gate_contract = cut(gate, states, emitted=False)
    require(gold_contract == gate_contract, "unknown normalization changes a storage contract")
    abstracted = abstract_shared_arithmetic(gold, gate, bits)
    save_json(out / "unknown_gold.json", {"modules": {"gold": gold}})
    save_json(out / "unknown_gate.json", {"modules": {"gate": gate}})
    script = """read_json unknown_gold.json
read_json unknown_gate.json
miter -equiv -flatten gold gate equiv
hierarchy -check -top equiv
opt_merge
opt_expr
opt_clean
check -assert
techmap
opt
abc -g AND
opt_clean
sat -verify -prove trigger 0 -show-inputs -show-outputs -dump_json unknown.counterexample.json
"""
    (out / "unknown_proof.ys").write_text(script)
    proc = run(["yosys", "-Q", "-T", "-s", "unknown_proof.ys"], out, out / "unknown_proof.log", check=False)
    passed = proc.returncode == 0 and "SAT proof finished - no model found: SUCCESS!" in proc.stdout
    result = {"status": "pass" if passed else "failed", "unknown_bits": len(bits), "occurrences": occurrences,
              "shared_arithmetic_abstractions": abstracted,
              "scope": "all two-state inputs and arbitrary Q; independent symbolic bit per unknown occurrence; every output and storage input cone",
              "artifact_hashes": {n: digest(out / n) for n in ("unknown_gold.json", "unknown_gate.json", "unknown_proof.ys", "unknown_proof.log")}}
    save_json(out / "unknown_proof.json", result)
    require(passed, "internal X/Z independence was not proven; see unknown_proof.log")
    return replacement, result
