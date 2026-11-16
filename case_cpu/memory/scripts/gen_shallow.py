#!/usr/bin/env python3
"""Produce a proof-carrying shallow evaluator from the actual imported LeanRTL AST."""
from pathlib import Path
import re
ROOT=Path(__file__).resolve().parents[1]
source=(ROOT/'lean/NativeImported.lean').read_text()
wires=re.findall(r'\{ name := "([^"]+)", width := (\d+), expr := (.*?) \}',source.split('def core',1)[0])
base=re.findall(r'\{ name := "([^"]+)", width := (\d+) \}',source.split('  inputs := [',1)[1].split('  wires :=',1)[0])
base+=re.findall(r'\{ name := "([^"]+)", width := (\d+), next :=',source.split('  regs := [',1)[1])
known={n:int(w) for n,w in base}; earlier={}
def parse(text):
    toks=re.findall(r'"[^"\\]*(?:\\.[^"\\]*)*"|[()]|[^()\s]+',text)
    pos=0
    def go():
        nonlocal pos
        t=toks[pos];pos+=1
        if t!='(':return t
        out=[]
        while toks[pos]!=')':out.append(go())
        pos+=1
        return out
    out=go();assert pos==len(toks)
    return out

def shallow(x):
    tag=x[0]
    if tag=='.const':
        _,w,n=x[1];return int(w),f'({n}#{w})'
    if tag=='.var':
        _,n,w=x;n=n[1:-1];w=int(w)
        if n in earlier:assert earlier[n]==w;return w,f'(V_{n} b)'
        assert known[n]==w,(n,w)
        return w,f'(b.lookup "{n}" {w})'
    if tag in ['.not']:
        w,a=shallow(x[1]);return w,f'(~~~ {a})'
    if tag in ['.and','.or','.xor','.add','.sub','.mul','.shl','.shr','.sshr','.udiv','.umod','.eq','.ult','.slt']:
        w,a=shallow(x[1]);ww,c=shallow(x[2])
        op={'.and':'&&&','.or':'|||','.xor':'^^^','.add':'+','.sub':'-','.mul':'*','.udiv':'/','.umod':'%'}
        if tag in op:return w,f'({a} {op[tag]} {c})'
        if tag in ['.shl','.shr']:return w,f'({a} {"<<<" if tag==".shl" else ">>>"} {c}.toNat)'
        if tag=='.sshr':return w,f'({a}.sshiftRight {c}.toNat)'
        cond=f'{a} {"=" if tag==".eq" else "<"} {c}' if tag!='.slt' else f'{a}.toInt < {c}.toInt'
        return 1,f'(if {cond} then (1#1) else 0)'
    if tag=='.mux':
        _,s=shallow(x[1]);w,a=shallow(x[2]);wb,c=shallow(x[3]);assert w==wb
        return w,f'(if {s} = 1 then {a} else {c})'
    if tag=='@Expr.concat':
        _,wa,wb,a,c=x;_,a=shallow(a);_,c=shallow(c)
        return int(wa)+int(wb),f'({a} ++ {c})'
    if tag in ['.zext','.sext']:
        w,a=shallow(x[2]);w+=int(x[1]);return w,f'({a}.{ "setWidth" if tag==".zext" else "signExtend"} {w})'
    if tag=='.extract':
        _,a=shallow(x[2]);return 1,f'(if {a}.getLsbD {x[1]} then (1#1) else 0)'
    if tag=='.slice':
        _,a=shallow(x[3]);return int(x[2]),f'(({a} >>> {x[1]}).setWidth {x[2]})'
    raise ValueError(tag)

lines=['import NativeImported','import NetFacts','open LeanRTL','namespace MemCPUShallow',
       'set_option maxRecDepth 65536','set_option maxHeartbeats 16000000',
       'set_option linter.unusedSimpArgs false','noncomputable section']
for name,width,expr in wires:
    w,term=shallow(parse(expr));assert w==int(width)
    lines.append(f'@[irreducible] noncomputable def V_{name} (b : Env) : BitVec {w} := {term}')
    earlier[name]=w
# A balanced lookup avoids quadratic kernel reduction of a 341-element if chain.
def decision_tree(items):
    if len(items)==1:
        n,w,e=items[0]
        return f'(if n = "{n}" then (V_{n} b).toNat else b n)'
    mid=len(items)//2
    pivot=items[mid][0]
    return f'(if n < "{pivot}" then {decision_tree(items[:mid])} else {decision_tree(items[mid:])})'
ident_map={n:re.sub(r'[^A-Za-z0-9_]', '_', n) for n,w,e in wires}
assert len(set(ident_map.values()))==len(ident_map)
def safe_identifiers(text):
    for orig,safe in sorted(ident_map.items(),key=lambda p:-len(p[0])):
        if orig==safe:continue
        for pref in ['V_','at_','equation_','value_']:
            text=text.replace(pref+orig,pref+safe)
    return text
(ROOT/'lean/MemoryCircuit.lean').write_text(safe_identifiers('\n'.join(lines[:1]+lines[2:]+['end','end MemCPUShallow',''])))
lines=['import MemoryCircuit','import NetFacts','open LeanRTL','namespace MemCPUShallow', 'noncomputable section','set_option maxRecDepth 65536','set_option maxHeartbeats 16000000','set_option linter.unusedSimpArgs false']
# Named tree nodes keep the kernel certificates small: each lookup unfolds
# only a logarithmic path, with siblings left as references to small definitions.
node_counter=0
node_lookup={}
def named_tree(items):
    global node_counter
    idx=node_counter;node_counter+=1
    name=f'lookupTree_{idx}'
    if len(items)==1:
        n,w,e=items[0]
        body=f'if n = "{n}" then (V_{n} b).toNat else b n'
        node_lookup[name]=(None,n)
    else:
        mid=len(items)//2
        left=named_tree(items[:mid]);right=named_tree(items[mid:]);pivot=items[mid][0]
        body=f'if n < "{pivot}" then {left} b n else {right} b n'
        node_lookup[name]=(pivot,left,right)
    lines.append(f'@[irreducible] noncomputable def {name} (b : Env) (n : String) : Nat := {body}')
    return name
root_node=named_tree(sorted(wires))
lines += [f'noncomputable def candidate (b : Env) : Env := {root_node} b']
def path_to(n):
    out=[];cur=root_node
    while True:
        out.append(cur)
        entry=node_lookup[cur]
        if entry[0] is None:return out
        pivot,left,right=entry
        cur=left if n<pivot else right
lines.append('def known : List String := ['+', '.join('"'+n+'"' for n,w in base)+']')
for name,width in base+[(n,w) for n,w,e in wires]:
    rhs=f'(V_{name} b).toNat' if name in earlier else f'b \"{name}\"'
    lines.append(f'theorem at_{name} (b : Env) : candidate b \"{name}\" = {rhs} := by simp only [candidate,{", ".join(path_to(name))},String.reduceLT,String.reduceEq,↓reduceIte]')
for eq_index,(name,width,expr) in enumerate(wires):
    if eq_index%32==0:
        pass
    lines += [f'theorem equation_{name} (b : Env) : candidate b "{name}" = (eval {expr} (candidate b)).toNat := by',
              f'  simp only [eval, Env.lookup, '+', '.join('at_'+n for n in [name]+sorted(set(re.findall(r'\.var \"([^\"]+)\"',expr))))+f', BitVec.ofNat_toNat, BitVec.setWidth_eq, V_{name}, ↓reduceIte] <;> rfl']
lines+=['theorem topology : CaseCPU.NetFacts.closed known MemCPUImported.core.wires = true := by native_decide']
chunks=re.findall(r'def (wireChunk_\d+) : List Wire := (.*?)(?=\n\ndef|\n\nend)',source,re.S)
assert len(chunks)>0
for cn,chunk in chunks:
    names=re.findall(r'\{ name := "([^"\n]+)", width := \d+, expr :=',chunk)
    lines += [f'theorem equations_{cn} (b : Env) : ∀ w ∈ MemCPUImported.{cn}, candidate b w.name = (eval w.expr (candidate b)).toNat := by',
              '  intro w h',f'  simp only [MemCPUImported.{cn}, List.mem_cons, List.not_mem_nil, or_false] at h',
              '  rcases h with '+' | '.join('rfl' for _ in names)]
    lines += [f'  · exact equation_{n} b' for n in names]
lines += ['theorem all_equations (b : Env) : ∀ w ∈ MemCPUImported.core.wires, candidate b w.name = (eval w.expr (candidate b)).toNat := by',
          '  intro w h', '  simp only [MemCPUImported.core, List.mem_append, or_assoc] at h',
          '  rcases h with '+' | '.join('h' for _ in chunks)]
lines += [f'  · exact equations_{cn} b w h' for cn,_ in chunks]
lines+=['theorem base_agreement (b : Env) : ∀ n ∈ known, b n = candidate b n := by',
        '  intro n h',
        '  simp only [known, List.mem_cons, List.not_mem_nil, or_false, or_assoc] at h',
        '  rcases h with '+' | '.join('rfl' for _ in base),
        *[f'  · exact (at_{n} b).symm' for n,w in base],
        'theorem all_values (b : Env) : ∀ n ∈ MemCPUImported.core.wires.map (·.name) ++ known, evalWires MemCPUImported.core.wires b n = candidate b n :=',
        '  CaseCPU.NetFacts.shallow_correct _ b (candidate b) known topology (base_agreement b) (all_equations b)']
for name,width,expr in wires:
    lines += [f'theorem value_{name} (b : Env) : evalWires MemCPUImported.core.wires b "{name}" = (V_{name} b).toNat := by',
              f'  have h := all_values b "{name}" (by decide +kernel)',
              f'  exact h.trans (at_{name} b)']
lines+=['#print axioms all_values','end','end MemCPUShallow','']
(ROOT/'lean/MemoryShallow.lean').write_text(safe_identifiers('\n'.join(lines)))
print('Generated',len(wires),'shallow definitions with checked equations.')
