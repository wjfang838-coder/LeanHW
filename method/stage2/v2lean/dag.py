"""Build smaller candidate DAG data; acceptance remains a Lean kernel check.

Only generated private variable references are renamed. Each candidate is later
checked against its original expression and the complete source wire list.
"""
import re

from .importer import require, lean_string

PRIVATE=re.compile(r'_transition_dag_[0-9]+_[0-9]+')
REFERENCE=re.compile(r'\(\.var "(_transition_dag_[0-9]+_[0-9]+)" ([0-9]+)\)')
QUOTED=re.compile(r'"(?:[^"\\]|\\.)*"')


def compact_names(blocks, reserved_names=()):
    """Short, fresh private names reduce kernel string-comparison work.

    Reserve every quoted name before allocating candidates. Source expressions
    stay unchanged; the existing kernel certificates check the renamed DAG.
    """
    reserved={lean_string(name) for name in reserved_names}
    for block in blocks:
        texts=[block['source'],block['result']]
        texts += [wire['expr'] for wire in block['locals']]
        reserved.update('"'+wire['name']+'"' for wire in block['locals'])
        for text in texts:reserved.update(QUOTED.findall(text))
    alphabet='0123456789abcdefghijklmnopqrstuvwxyz'
    def name(index):
        digits=''
        while True:
            index,digit=divmod(index,36);digits=alphabet[digit]+digits
            if not index:return '_'+digits
    names={};index=0
    for block in blocks:
        for wire in block['locals']:
            old=wire['name']
            require(old not in names,'duplicate private DAG name across blocks')
            while '"'+name(index)+'"' in reserved:index+=1
            names[old]=name(index);index+=1
    def rewrite(expr):
        return REFERENCE.sub(lambda m:f'(.var "{names.get(m[1],m[1])}" {m[2]})',expr)
    result=[{'source':b['source'],
             'locals':[{'name':names[w['name']],'width':w['width'],'expr':rewrite(w['expr'])}
                       for w in b['locals']],
             'result':rewrite(b['result'])} for b in blocks]
    return result,{'private_name_chars_before':sum(map(len,names)),
                   'private_name_chars_after':sum(map(len,names.values()))}


def deduplicate(blocks, reserved_names=()):
    result=[];before=after=0
    for block in blocks:
        aliases={};seen={};names=set();wires=[]
        def rewrite(expr):
            return REFERENCE.sub(lambda match:
                f'(.var "{aliases.get(match[1],match[1])}" {match[2]})',expr)
        for wire in block['locals']:
            name,width,expr=wire['name'],wire['width'],wire['expr']
            require(PRIVATE.fullmatch(name) is not None and name not in names,'invalid/duplicate private DAG name')
            require(type(width) is int and width>0 and isinstance(expr,str),'invalid DAG wire data')
            names.add(name);before+=1
            expr=rewrite(expr);key=(width,expr)
            if key in seen:
                aliases[name]=seen[key]
            else:
                seen[key]=name;wires.append({'name':name,'width':width,'expr':expr});after+=1
        result.append({'source':block['source'],'locals':wires,'result':rewrite(block['result'])})
    result,name_statistics=compact_names(result,reserved_names)
    return result,{'before':before,'after':after,'removed':before-after,**name_statistics}


def render_checked(blocks):
    declarations=[];names=[]
    for index,block in enumerate(blocks):
        name=f'dag_block_{index}';names.append(name)
        wires=', '.join('{name := "'+w['name']+'", width := '+str(w['width'])+', expr := '+w['expr']+'}'
                        for w in block['locals'])
        candidate='{source := '+block['source']+', locals := ['+wires+'], result := '+block['result']+'}'
        declarations.append('def '+name+' : DAG.CheckedBlock := {block := '+candidate+', inlined := by source_kernel_rfl}')
    return '\n'.join(declarations)+'\ndef dag_blocks : List DAG.CheckedBlock := ['+', '.join(names)+']\n'
