"""BTOR-style nondeterministic RTLIL import (separate from legacy two-state import).

X/Z are internal choices, not physical inputs and never selected zero. Initial
registers without emitInit are quantified by LeanRTL.Symbolic.initial. This
profile overapproximates independent undef uses, as documented in its report.
"""
from copy import deepcopy
from .importer import Importer, Expr, resize, parameter, require, lean_string


class SymbolicImporter(Importer):
    def __init__(self, design, top):
        design = deepcopy(design)
        module = design['modules'][top]
        self.physical_ports = deepcopy(module['ports'])
        self.choices = []
        self.choice_prefix = '__v2lean_choice_'
        while any(n.startswith(self.choice_prefix) for n in
                  list(module['ports']) + list(module.get('netnames', {}))):
            self.choice_prefix += '_'
        bits = [b for p in module['ports'].values() for b in p['bits']]
        bits += [b for c in module['cells'].values() for bs in c['connections'].values() for b in bs]
        next_bit = max([b for b in bits if type(b) is int] + [1]) + 1

        def choice(width):
            nonlocal next_bit
            name = self.choice_prefix + str(len(self.choices))
            net = list(range(next_bit, next_bit + width)); next_bit += width
            self.choices.append((name, width))
            module['ports'][name] = {'direction': 'input', 'bits': net}
            return net

        # Preserve each explicit anyseq cell's fanout identity.
        for name, cell in list(module['cells'].items()):
            if cell['type'] == '$anyseq':
                net = cell['connections']['Y']
                n = self.choice_prefix + str(len(self.choices))
                self.choices.append((n, len(net)))
                module['ports'][n] = {'direction': 'input', 'bits': net}
                del module['cells'][name]
        def replace(net):
            # At this post-flattened word-level boundary, X and high impedance
            # constants are both nondeterministic bit choices.  This is a sound
            # overapproximation of Z resolution; duplicate physical drivers are
            # still rejected later by Importer.bind.
            result, pos = [], 0
            while pos < len(net):
                if net[pos] not in ('x', 'z'):
                    result.append(net[pos]); pos += 1
                else:
                    end = pos + 1
                    unknown = net[pos]
                    while end < len(net) and net[end] == unknown: end += 1
                    result.extend(choice(end-pos)); pos = end
            return result

        # `$adff` stores its reset value as a cell parameter, outside ordinary
        # input connections.  Turn an X/Z reset value into an asynchronous load
        # from the same reset net and a symbolic data expression so no unknown
        # bit is silently coerced to zero.
        for cell in module['cells'].values():
            raw = cell.get('parameters', {}).get('ARST_VALUE')
            if cell['type'] != '$adff' or not isinstance(raw, str) or not ({'x', 'z'} & set(raw)):
                continue
            require(set(raw) <= {'0', '1', 'x', 'z'}, 'malformed symbolic ARST_VALUE')
            params = cell['parameters']
            params['ALOAD_POLARITY'] = params.pop('ARST_POLARITY')
            params.pop('ARST_VALUE')
            cell['type'] = '$aldff'
            con = cell['connections']
            con['ALOAD'] = con.pop('ARST')
            con['AD'] = replace(list(reversed(raw)))
            directions = cell['port_directions']
            directions['ALOAD'] = directions.pop('ARST')
            directions['AD'] = 'input'
        for name in self.physical_ports:
            port = module['ports'][name]
            if port['direction'] == 'output': port['bits'] = replace(port['bits'])
        for cell in module['cells'].values():
            for port, net in cell['connections'].items():
                if cell['port_directions'][port] == 'input':
                    cell['connections'][port] = replace(net)
        self.choice_ranges = []
        if len(self.choices) > 1:
            # A single packed oracle vector still ranges over the Cartesian
            # product of all bits. Packing avoids quadratic scope checks on
            # thousands of independent input declarations; no choices merge.
            packed = []
            for name,width in self.choices:
                self.choice_ranges.append((name,len(packed),width))
                packed.extend(module['ports'].pop(name)['bits'])
            name = self.choice_prefix+'packed'
            self.choices = [(name,len(packed))]
            module['ports'][name] = {'direction':'input','bits':packed}
        super().__init__(design, top, allow_state=True, allow_port_layouts=True,
                         allow_bit_cells=True, compact_names=True, proof_tables=True)

    def cell_expr(self, cell):
        if cell['type'] not in ('$div', '$mod'):
            return super().cell_expr(cell)
        conn = cell['connections']
        a, b = self.bus(conn['A']), self.bus(conn['B'])
        width = len(conn['Y'])
        require(parameter(cell, 'A_WIDTH') == a.width and parameter(cell, 'B_WIDTH') == b.width
                and parameter(cell, 'Y_WIDTH') == width, 'division dimensions')
        signed = bool(parameter(cell, 'A_SIGNED') and parameter(cell, 'B_SIGNED'))
        common = max(width, a.width, b.width)
        a, b = resize(a, common, signed), resize(b, common, signed)
        zero = f'(.const (BitVec.ofNat {common} 0))'
        op = 'udiv' if cell['type'] == '$div' else 'umod'
        if signed:
            sa, sb = (f'(.extract {common-1} {e.code})' for e in (a,b))
            aa = f'(.mux {sa} (.sub {zero} {a.code}) {a.code})'
            bb = f'(.mux {sb} (.sub {zero} {b.code}) {b.code})'
            mag = f'(.{op} {aa} {bb})'
            sign = f'(.xor {sa} {sb})' if op == 'udiv' else sa
            result = f'(.mux {sign} (.sub {zero} {mag}) {mag})'
        else:
            result = f'(.{op} {a.code} {b.code})'
        name = self.choice_prefix + str(len(self.choices))
        self.choices.append((name, common)); self.inputs.append((name, common))
        self.used_names.add(name)
        self.ports[name] = {'direction': 'input', 'bits': []}
        return resize(Expr(common, f'(.mux (.eq {b.code} {zero}) '
                            f'(.var {lean_string(name)} {common}) {result})'), width)

    def render(self, outputs):
        require(not self.latches, 'symbolic latch requires settled-event semantics')
        # The ordinary object remains real LeanRTL data. The wrapper adds only
        # internal choice declarations; the trusted semantics lives in Symbolic.
        core = super().render(outputs)
        marker = '-- The executable'
        prefix = core.split(marker)[0]
        prefix = 'import LeanRTL.Core.Symbolic\n' + prefix
        # Existing render closes the namespace after the model and before IO.
        prefix = prefix.replace('def impl : Module :=', 'def core : Module :=')
        import re
        prefix = re.sub(r'\bimpl\b', 'core', prefix)
        prefix = prefix.replace('example : core.checkErrors = []', 'theorem core_checks : core.checkErrors = []')
        prefix = prefix.replace('example : core.wellWidthedb = true', 'theorem core_width : core.wellWidthedb = true')
        end = 'end V2LeanImported'
        require(end in prefix, 'unexpected generated namespace boundary')
        entries = ', '.join('{ name := '+lean_string(n)+f', width := {w} }}' for n,w in self.choices)
        valid_proof = 'by decide +kernel'
        if self.coverage_reasons:
            valid_proof = ('by\n  simp only [LeanRTL.Symbolic.Module.valid, impl, core_width, core_checks, '
                           'List.isEmpty_nil, Bool.true_and]\n  decide +kernel')
        extra = ('def impl : LeanRTL.Symbolic.Module := { core := core, choices := ['+entries+'] }\n'
                 'theorem imported_valid : impl.valid = true := '+valid_proof+'\n')
        prefix = prefix.replace(end, extra+end)
        return prefix + '\n'
