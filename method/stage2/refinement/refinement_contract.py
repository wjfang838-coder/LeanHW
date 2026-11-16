"""Trusted, case-frozen adapters for the version 4 default-instance target."""
import json
from pathlib import Path
import re

ROOT = Path(__file__).resolve().parents[3]


def quoted(s):
    return json.dumps(s)


def lean_field(name):
    """Render a generated SpecIR record field as a Lean identifier.

    Verilog permits port names such as `in`, which is a Lean keyword.  Quoted
    identifiers work for ordinary names as well, so use them uniformly rather
    than maintaining a second keyword list here.
    """
    if "»" in name:
        raise ValueError("SpecIR field name cannot contain a quoted-identifier terminator")
    return f'«{name}»'


def contract_source(key, kind, ports, iface, spec_field_map=None):
    def signature(direction):
        return '['+', '.join('('+quoted(n)+', '+str(len(p['bits']))+')'
                             for n,p in ports.items()
                             if p['direction']==direction or
                                (direction=='input' and p['direction']=='inout'))+']'
    inputs, outputs = signature('input'), signature('output')
    # SpecIR input records use Nat so that generated specifications stay
    # simple, while every Verilog input is a fixed-width bit vector.  Run the
    # specification on the physical representative of each input.  Without
    # this normalization, two Nat inhabitants that render to the same port
    # bits can demand different behavior and make refinement impossible for
    # every RTL implementation.
    half = iface.get('timebase') in ('half', 'halfCycle')
    implicit_clocks = {
        p['name'] for p in iface.get('inputs', [])
        if p.get('role') == 'clock' and not half
    }
    spec_inputs = [
        (n, len(p['bits'])) for n, p in ports.items()
        if p['direction'] in ('input', 'inout') and n not in implicit_clocks
    ]
    if spec_inputs:
        def spec_field(port_name):
            if not spec_field_map:
                return port_name
            if port_name not in spec_field_map:
                raise ValueError(f'no SpecIR input field for physical port {port_name!r}')
            return spec_field_map[port_name]
        updates = ', '.join(
            f'{lean_field(spec_field(n))} := i.{lean_field(spec_field(n))} % (2 ^ {w})'
            for n, w in spec_inputs
        )
        norm = f'(i : SpecIR.Gen.In) : SpecIR.Gen.In := {{i with {updates}}}'
        proof = 'by intro i; simp [normalizeInput, Nat.mod_mod]'
        render_proof = ('by intro i; simp [normalizeInput, SpecIR.Gen.spec, '
                        'SpecIR.Gen.renderIn, SpecIR.Val.mk, Nat.mod_mod]')
    else:
        norm = '(i : SpecIR.Gen.In) : SpecIR.Gen.In := i'
        proof = 'by intro i; rfl'
        render_proof = 'by intro i; rfl'
    if kind == 'symbolic':
        typ = 'LeanRTL.Symbolic.Module'
        adapter = 'edges' if half else 'cycle'
        model = f'FrozenRefinement.{adapter} spec m'
        valid = 'm.valid' if half else 'm.cycleValid'
        valid += ' && m.controlsSupported'
        valid += ' && (m.core.name == '+quoted(iface['module'])+')'
        if not half:
            negative=iface.get('timing',{}).get('active_edge')=='negedge'
            valid += ' && (m.core.regs.all fun r => r.negedge == '+str(negative).lower()+')'
        input_expr, output_expr = 'm.inputs', 'm.core.outputs'
        order = '(m.core.portOrder.filter fun n => !(m.choices.any fun p => p.name == n))'
        layout_expr = 'm.core.portLayouts.map fun p => (p.name, p.signed, p.offset, p.upto)'
        expected_layout = '['+', '.join('('+quoted(n)+', '+str(bool(p.get('signed',0))).lower()+', '
            +str(p.get('offset',0))+', '+str(bool(p.get('upto',0))).lower()+')'
            for n,p in ports.items() if any(p.get(k,0) for k in ('signed','offset','upto')))+']'
    elif kind in ('clocked','fourstate'):
        if kind=='fourstate' and any(p.get('signed') or p.get('offset') or p.get('upto') for p in ports.values()):
            raise ValueError('four-state combinational emitter needs port-layout support for this interface')
        typ = 'LeanRTL.FourState.NBA.Clocked' if kind=='clocked' else 'LeanRTL.FourState.Module'
        clocks = [p['name'] for p in iface['inputs'] if p.get('role')=='clock']
        if kind=='clocked' and not clocks:
            raise ValueError('event adapter requires declared physical clocks')
        if kind == 'clocked':
            adapter = 'clocked' if half else 'clockedCycle'
            model = f'FrozenRefinement.{adapter} spec ['+', '.join(map(quoted,clocks))+'] m'
        else:
            model = 'FrozenRefinement.combinational spec m'
        valid = 'm.valid'
        valid += ' && (m.name == '+quoted(iface['module'])+')'
        if kind=='clocked':
            valid += ' && (m.signedPorts == ['+', '.join(quoted(n) for n,p in ports.items() if p.get('signed'))+'])'
        input_expr, output_expr = 'm.inputs', 'm.outputs'
        order = 'm.portOrder' if kind=='clocked' else '['+', '.join(map(quoted,ports))+']'
        layout_expr, expected_layout = '([] : List (String × Bool × Int × Bool))','[]'
    elif kind == 'system':
        typ = 'LeanRTL.FourState.Resolved.System'
        clocks = [p['name'] for p in iface['inputs'] if p.get('role')=='clock']
        if not clocks:
            raise ValueError('resolved event adapter requires declared physical clocks')
        inouts = [n for n,p in ports.items() if p['direction']=='inout']
        aliases = [('__external_'+n,n) for n in inouts]
        output_names = [n for n,p in ports.items() if p['direction']=='output']
        model = ('FrozenRefinement.systemCycle spec ['+', '.join(map(quoted,clocks))+'] ['+
                 ', '.join('('+quoted(target)+', '+quoted(source)+')' for target,source in aliases)+'] ['+
                 ', '.join(map(quoted,output_names))+'] m')
        # The resolved lowerer keeps ordinary inputs in physical-port order
        # and appends one synthetic external driver for each inout net.
        typ_inputs = ([(n, len(p['bits'])) for n,p in ports.items()
                       if p['direction']=='input'] +
                      [('__external_'+n, len(p['bits'])) for n,p in ports.items()
                       if p['direction']=='inout'])
        expected_inputs = '['+', '.join('('+quoted(n)+', '+str(w)+')' for n,w in typ_inputs)+']'
        valid = ('m.valid && (m.network.name == '+quoted(iface['module'])+')'
                 + ' && ((m.lower.inputs.map fun p => (p.name,p.width)) == '+expected_inputs+')'
                 + ' && ((m.network.outputs.map fun p => (p.name,p.width)) == '+outputs+')'
                 + ' && (m.portOrder == ['+', '.join(map(quoted,ports))+'])')
        input_expr = output_expr = None
        order = layout_expr = expected_layout = None
    elif kind == 'timed':
        if key != 'clkgenerator':
            raise ValueError('timed model needs an explicitly grounded sampling interval')
        if inputs!='[]' or len(ports)!=1:
            raise ValueError('autonomous time model interface mismatch')
        typ = 'LeanRTL.FourState.Timed.Signal'
        model = 'FrozenRefinement.timed (ι := SpecIR.Gen.In) 1000000 m'
        valid = f'm.valid && ([(m.name, m.width)] == {outputs})'
        input_expr = output_expr = None
        order = layout_expr = expected_layout = None
    else:
        raise ValueError('no audited refinement adapter for '+kind)
    if input_expr:
        valid += f' && (({input_expr}.map fun p => (p.name,p.width)) == {inputs})'
        valid += f' && (({output_expr}.map fun p => (p.name,p.width)) == {outputs})'
        valid += ' && ('+order+' == ['+', '.join(map(quoted,ports))+'])'
        valid += ' && (('+layout_expr+') == '+expected_layout+')'
    needed = [(n,len(p['bits'])) for n,p in ports.items() if p['direction'] in ('input','inout')]
    if (kind in ('symbolic', 'clocked') and not half) or kind == 'system':
        implicit={p['name'] for p in iface['inputs'] if p.get('role')=='clock'}
        needed=[(n,w) for n,w in needed if n not in implicit]
    required='['+', '.join('('+quoted(n)+', '+str(w)+')' for n,w in needed)+']'
    return f'''import FrozenSpec
import FrozenRefinement
set_option maxRecDepth 32768
set_option maxHeartbeats 3200000
namespace FrozenContract
def normalizeInput {norm}
theorem normalization_idempotent : ∀ i, normalizeInput (normalizeInput i) = normalizeInput i := {proof}
theorem normalization_preserves_render : ∀ i,
    SpecIR.Gen.spec.renderIn (normalizeInput i) = SpecIR.Gen.spec.renderIn i := {render_proof}
def spec := FrozenRefinement.normalize SpecIR.Gen.spec normalizeInput
theorem inputs_concrete : ∀ i, ∀ p ∈ spec.renderIn i, ∃ w n, p.2 = SpecIR.Val.bits w n := by
  intro i
  simp [spec, FrozenRefinement.normalize, SpecIR.Gen.spec, SpecIR.Gen.renderIn, SpecIR.Val.mk]
theorem inputs_covered : ∀ i, ∀ p ∈ ({required} : List (String × Nat)),
    ∃ v, (p.1,v) ∈ spec.renderIn i ∧ v.width = p.2 := by
  intro i
  simp [spec, FrozenRefinement.normalize, SpecIR.Gen.spec, SpecIR.Gen.renderIn, SpecIR.Val.mk, SpecIR.Val.width]
def model (m : {typ}) := {model}
def valid (m : {typ}) : Bool := {valid}
end FrozenContract
'''


def write_contract(ws, key, report):
    ws = Path(ws)
    iface = json.loads((ws/'iface.json').read_text())
    order=report.get('port_order')
    if not order or len(order)!=len(set(order)) or set(order)!=set(report['ports']):
        raise ValueError('Import report must explicitly preserve the original physical port order')
    ports={n:report['ports'][n] for n in order}
    frozen_spec = (ws/'FrozenSpec.lean').read_text()
    # Generated specs may indent the `deriving` clause with the fields.
    structure = re.search(r'(?ms)^structure In where\s*\n(.*?)^[ \t]*deriving\b', frozen_spec)
    if not structure:
        raise ValueError('FrozenSpec does not declare SpecIR.Gen.In')
    spec_fields = set(re.findall(
        r"(?m)^\s{2}([A-Za-z_][A-Za-z0-9_']*)\s*:", structure.group(1)))
    render = re.search(r'(?ms)^def renderIn\b.*?^def suite\b', frozen_spec)
    rendered_fields = {}
    if render:
        for physical, field in re.findall(
                r'\(\s*"([^"\\]+)"\s*,\s*Val\.mk\s+\d+\s+i\.([A-Za-z_][A-Za-z0-9_\']*)\s*\)',
                render.group(0)):
            rendered_fields[physical] = field
    spec_field_map = {}
    implicit_clocks = {
        p['name'] for p in iface.get('inputs', [])
        if p.get('role') == 'clock' and iface.get('timebase') not in ('half', 'halfCycle')
    }
    for name, port in ports.items():
        if port['direction'] not in ('input', 'inout') or name in implicit_clocks:
            continue
        if name in rendered_fields:
            spec_field_map[name] = rendered_fields[name]
        elif name in spec_fields:
            spec_field_map[name] = name
        elif name + '_' in spec_fields:
            spec_field_map[name] = name + '_'
        else:
            raise ValueError(f'FrozenSpec.renderIn has no field binding for physical port {name!r}')
    source = contract_source(key,report['kind'],ports,iface,spec_field_map)
    (ws/'FrozenContract.lean').write_text(source)
    (ws/'contract.json').write_text(json.dumps({
        'version': 4, 'key': key, 'model_kind': report['kind'],
        'top': iface['module'], 'ports': ports, 'port_order':order,
        'parameter_scope': 'benchmark_defaults', 'parameters': report.get('parameters',{}),
        'spec_parameters': iface.get('integration_contract',{}).get('parameters',[]),
        'input_adapter': 'all SpecIR Nat inputs reduced modulo their physical port width',
        'initial_state_scope': 'fixed_zero_registers' if report['kind'] in ('clocked','system') else None,
        'timebase': iface.get('timebase'),
        'sample_fs': 1000000 if report['kind']=='timed' else None,
        'source_sha256': report['source_sha256'],
        'claim': 'unbounded default-instance refinement', 'roundtrip': False, 'jasper': False},indent=2)+'\n')
