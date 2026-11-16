"""Compare clocked storage contracts and all combinational cones at matched Q cuts.

Every Q becomes the SAME arbitrary input in both circuits. D, CLK and asynchronous
control/data become additional observable outputs. This is an inductive transition
correspondence check, including clock/reset cones, without assuming a reset sequence.
Jasper SEC on the untouched HDL remains the required final equivalence gate.
"""
import copy
import json
from pathlib import Path

from .pipeline import digest, run, save_json

STATE_TYPES = {"$dff", "$adff", "$aldff", "$dlatch"}


def init_bits(module):
    values = {}
    for net in module.get("netnames", {}).values():
        attr = net.get("attributes", {}).get("init")
        if attr is None:
            continue
        if len(attr) != len(net["bits"]): raise ValueError("initial-value width mismatch")
        for bit, value in zip(net["bits"], reversed(attr)):
            if value == "x": continue
            if value not in "01": raise ValueError("unsupported initial value")
            if bit in values and values[bit] != value: raise ValueError("conflicting initial values")
            values[bit] = value
    return values


def cut(module, states, *, emitted):
    module = copy.deepcopy(module)
    init = init_bits(module)
    used = set(module["ports"]) | set(module["netnames"])
    buses = [net["bits"] for group in (module["ports"], module["netnames"]) for net in group.values()]
    buses += [bits for c in module["cells"].values() for bits in c.get("connections", {}).values()]
    next_bit = 1 + max((b for bits in buses for b in bits if type(b) is int), default=1)
    contracts = []
    for index, state in enumerate(states):
        if emitted:
            q = module["netnames"][state.get("gate_register", state["register"])]["bits"]
            matches = [n for n, c in module["cells"].items() if c["type"] in STATE_TYPES and c["connections"]["Q"] == q]
            if len(matches) != 1: raise ValueError("emitted state matching is not one-to-one")
            name = matches[0]
        else:
            name = state["cell"]
        cell = module["cells"].pop(name)
        if cell["type"] == "$dlatch" and int(cell["parameters"]["EN_POLARITY"], 2) == 0:
            # Compare active enables, preserving low-transparent latch semantics.
            invert = f"v2lean_state_{index}_active_enable"
            if invert in module["cells"] or invert in used: raise ValueError("state-cut inverter collision")
            module["cells"][invert] = {"type": "$not", "parameters": {"A_SIGNED": "0", "A_WIDTH": "1", "Y_WIDTH": "1"},
                "port_directions": {"A": "input", "Y": "output"}, "connections": {"A": cell["connections"]["EN"], "Y": [next_bit]}}
            cell["connections"]["EN"] = [next_bit]
            next_bit += 1
            cell["parameters"]["EN_POLARITY"] = "1"
        contracts.append({"type": cell["type"], "parameters": {n: int(v, 2) for n, v in cell["parameters"].items()},
                          "initial_bits_lsb": [init.get(b, "x") for b in cell["connections"]["Q"]]})
        for port, bits in cell["connections"].items():
            label = state["register"] if port == "Q" else f"v2lean_state_{index}_{port}"
            if label in module["ports"] or (port != "Q" and label in used): raise ValueError("state-cut name collision")
            used.add(label)
            module["ports"][label] = {"direction": "input" if port == "Q" else "output", "bits": bits}
            module["netnames"][label] = {"hide_name": 0, "bits": bits, "attributes": {}}
    if any(c["type"] in STATE_TYPES or c["type"].startswith("$mem") for c in module["cells"].values()):
        raise ValueError("unmatched storage left after state cut")
    for net in module["netnames"].values():
        net.get("attributes", {}).pop("init", None)
    return module, contracts


def check(directory, top, states):
    out = Path(directory)
    # Read the actual emitted HDL again, so exporter damage is included.
    (out / "state_gate.ys").write_text(f"read_verilog -sv roundtrip.v\nhierarchy -check -top {top}\nproc\nflatten\nopt_clean\nwrite_json -noscopeinfo state_gate.json\n")
    run(["yosys", "-Q", "-T", "-s", "state_gate.ys"], out, out / "state_gate.log")
    source = json.loads((out / "import.rtlil.json").read_text())["modules"][top]
    target = json.loads((out / "state_gate.json").read_text())["modules"][top]
    gold, gc = cut(source, states, emitted=False)
    gate, ic = cut(target, states, emitted=True)
    save_json(out / "state_contracts.json", {"original": gc, "emitted": ic, "states": states})
    if gc != ic: raise ValueError("storage type, parameters or initial state changed")
    save_json(out / "state_gold.cut.json", {"modules": {"gold": gold}})
    save_json(out / "state_gate.cut.json", {"modules": {"gate": gate}})
    for side in ("gold", "gate"):
        (out / f"state_{side}.emit.ys").write_text(f"read_json state_{side}.cut.json\nrename {side} {top}\nwrite_verilog -noattr state_{side}.cut.v\n")
        run(["yosys", "-Q", "-T", "-s", f"state_{side}.emit.ys"], out, out / f"state_{side}.emit.log")
    (out / "state_equiv.ys").write_text("""read_json state_gold.cut.json
read_json state_gate.cut.json
miter -equiv -flatten gold gate equiv
hierarchy -check -top equiv
opt_clean
check -assert
opt -full
techmap
opt -full
abc -g AND
opt_clean
sat -verify -prove trigger 0 -show-inputs -show-outputs -dump_json state.counterexample.json
""")
    (out / "state_structural.ys").write_text("""read_json state_gold.cut.json
read_json state_gate.cut.json
equiv_make gold gate equiv
hierarchy -check -top equiv
equiv_struct
equiv_simple
equiv_status -assert
""")
    result = run(["yosys", "-Q", "-T", "-s", "state_structural.ys"], out, out / "state_structural.log", check=False)
    success = result.returncode == 0 and "Equivalence successfully proven!" in result.stdout
    method = "equiv_struct + equiv_simple + equiv_status -assert"
    if not success:
        result = run(["yosys", "-Q", "-T", "-s", "state_equiv.ys"], out, out / "state_equiv.log", check=False)
        success = result.returncode == 0 and "SAT proof finished - no model found: SUCCESS!" in result.stdout
        method = "whole-miter SAT"
    report = {"status": "pass" if success else "failed", "storage_contracts": "pass", "states": len(states), "method": method,
              "scope": "all two-state inputs and corresponding arbitrary Q states; D/clock/async-control cones",
              "original_sha256": digest(out / "original.v"), "emitted_sha256": digest(out / "roundtrip.v")}
    save_json(out / "state_equiv.json", report)
    if not success: raise RuntimeError("state transition equivalence failed; see state_equiv.log")
    return report
