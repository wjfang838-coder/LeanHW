"""Preserve bounds on simple unsigned array writes before mem2reg lowering.

This narrow frontend pass inserts no environment assumptions. Only pure
identifier/nonnegative-add index expressions and pure scalar RHS values are
eligible; unsupported forms stay unchanged and still require end-to-end SEC.
"""
import re
from collections import Counter
from pathlib import Path
from .importer import require
from .pipeline import digest, run, save_json


def prepare(directory, top):
    out = Path(directory)
    script = f'read_verilog -sv -nomem2reg -dump_ast1 original.v\nhierarchy -check -top {top}\nwrite_rtlil bounds_native.il\n'
    (out / 'bounds_native.ys').write_text(script)
    proc = run(['yosys', '-Q', '-T', '-s', 'bounds_native.ys'], out, out / 'bounds_native.log')
    il = (out / 'bounds_native.il').read_text()
    require(re.findall(r'^module \\(\S+)', il, re.M) == [top], 'array bounds pass requires one flat module')
    arrays = {m[2]: int(m[1]) for m in re.finditer(r'^  memory width \d+ size (\d+) \\([A-Za-z_][A-Za-z0-9_]*)$', il, re.M)}
    require(all(0 < size < 2**31 for size in arrays.values()), 'unsupported array depth for bound literal')
    unsigned = set()
    for m in re.finditer(r'^  wire (.*?)\\([A-Za-z_][A-Za-z0-9_]*)$', il, re.M):
        if 'signed' not in m[1].split(): unsigned.add(m[2])
    nodes, stack = [], []
    for line in (proc.stdout + proc.stderr).splitlines():
        match = re.match(r'(\s*)(AST_\w+) <original\.v:(\d+)\.(\d+)-(\d+)\.(\d+)> \[[^]]+\](.*)', line)
        if not match: continue
        node = {'kind': match[2], 'pos': tuple(map(int, match.group(3,4,5,6))), 'text': match[7], 'children': []}
        depth = len(match[1])
        while stack and stack[-1][0] >= depth: stack.pop()
        if stack: stack[-1][1]['children'].append(node)
        stack.append((depth,node));nodes.append(node)
    source = (out / 'original.v').read_text()
    require(source.isascii(), 'array bounds source positions currently require ASCII')
    starts = [0]
    for line in source.splitlines(keepends=True): starts.append(starts[-1] + len(line))
    def span(node):
        a,b,c,d = node['pos'];require(a>0 and c>0, 'missing concrete source span')
        return starts[a-1]+b-1, starts[c-1]+d-1
    def name(node):
        match = re.search(r"str='\\([A-Za-z_][A-Za-z0-9_]*)'",node['text'])
        return match[1] if match else None
    declarations = Counter(name(n) for n in nodes if n['kind'] in ('AST_WIRE','AST_MEMORY'))
    # Do not confuse a local declaration with a same-named module signal.
    unsigned = {n for n in unsigned if declarations[n] == 1}
    arrays = {n: size for n, size in arrays.items() if declarations[n] == 1}
    def pure_index(node):
        if node['kind'] == 'AST_IDENTIFIER': return not node['children'] and name(node) in unsigned
        if node['kind'] == 'AST_ADD' and len(node['children'])==2:
            a,b = node['children'];constant = re.search(r"bits='([01]+)'\((\d+)\)",b['text'])
            return pure_index(a) and b['kind']=='AST_CONSTANT' and constant is not None and constant[1][0]=='0'
        return False
    edits = []
    for node in nodes:
        if node['kind'] not in ('AST_ASSIGN_LE','AST_ASSIGN_EQ') or len(node['children']) != 2: continue
        lhs,rhs = node['children'];array=name(lhs)
        if lhs['kind']!='AST_IDENTIFIER' or array not in arrays: continue
        if len(lhs['children'])!=1 or lhs['children'][0]['kind']!='AST_RANGE': continue
        indices=lhs['children'][0]['children']
        if len(indices)!=1 or not pure_index(indices[0]): continue
        if rhs['kind'] not in ('AST_IDENTIFIER','AST_CONSTANT') or rhs['children']: continue
        first,last=span(node);a,b=span(indices[0]);index=source[a:b]
        require(source[last:last+1]==';','assignment span must end at its semicolon')
        stmt=source[first:last+1]
        replacement=f"begin if ($unsigned({index}) < 32'd{arrays[array]}) begin {stmt} end end"
        edits.append({'kind':'write_bound','start':first,'end':last+1,'array':array,'size':arrays[array], 'index':index,
                      'original':stmt,'replacement':replacement})
    for node in nodes:
        # An invalid array read is all X. A relational comparison involving it
        # is X, and a procedural `if` takes its else arm. Preserve that decision
        # explicitly before Yosys narrows an unpacked-array index. This rule is
        # deliberately not applied to comparisons used as ordinary data.
        if node['kind'] != 'AST_CASE' or not node['children']: continue
        if node['pos'][0] == 0: continue
        a,b=span(node)
        if not re.match(r'if\s*\(', source[a:b]): continue
        test=node['children'][0]
        if test['kind']!='AST_REDUCE_BOOL' or len(test['children'])!=1: continue
        compare=test['children'][0]
        if compare['kind'] not in ('AST_GT','AST_GE','AST_LT','AST_LE') or len(compare['children'])!=2: continue
        guards=[]
        for operand in compare['children']:
            array=name(operand)
            if operand['kind']!='AST_IDENTIFIER' or array not in arrays: break
            if len(operand['children'])!=1 or operand['children'][0]['kind']!='AST_RANGE': break
            indices=operand['children'][0]['children']
            if len(indices)!=1 or not pure_index(indices[0]): break
            first,last=span(indices[0]);index=source[first:last]
            guards.append({'array':array,'size':arrays[array],'index':index})
        if len(guards)!=2: continue
        first,last=span(compare);expr=source[first:last]
        guard=' && '.join(f"($unsigned({g['index']}) < 32'd{g['size']})" for g in guards)
        edits.append({'kind':'relational_if_bounds','start':first,'end':last,'reads':guards,
                      'original':expr,'replacement':f'({guard} && ({expr}))'})
    edits.sort(key=lambda e:e['start'])
    require(all(a['end'] <= b['start'] for a,b in zip(edits,edits[1:])), 'overlapping array-write edits')
    result=source
    for edit in reversed(edits): result=result[:edit['start']]+edit['replacement']+result[edit['end']:]
    (out/'bounds_guarded.v').write_text(result)
    report={'status':'prepared_pending_equivalence','edits':edits,'original_sha256':digest(out/'original.v'),
            'guarded_sha256':digest(out/'bounds_guarded.v'),'validator_sha256':digest(Path(__file__)),
            'scope':'explicit bounds on eligible unsigned array writes and relational procedural-if reads; source RTL remains SEC gold'}
    save_json(out/'array_bounds.json',report)
    return report
