"""Native word memories: bounded physical depth, asynchronous reads, clocked writes.

This parser is staged for pipeline integration. Every accepted instance still
requires exact primitive-contract and complete transition-cone checks, followed
by SEC on the original and emitted HDL. Complete known initialization requires
the initialized MemBlock framework extension; no initialization is discarded.
"""
import copy
from .importer import Importer, Expr, parameter, require, lean_string


def describe(module):
    memories = []
    used = set(module['ports']) | set(module['netnames'])
    prefix = 'v2lean_memory'
    while any(n.startswith(prefix) for n in used): prefix += '_'
    for cell_name, cell in sorted(module['cells'].items()):
        if cell['type'] != '$mem_v2': continue
        aw,dw,rp,wp = [parameter(cell,k) for k in ('ABITS','WIDTH','RD_PORTS','WR_PORTS')]
        require(0 < aw <= 32 and dw > 0 and rp > 0 and wp > 0, 'native memory dimensions/ports')
        size = parameter(cell,'SIZE')
        require(0 < size <= 2**aw and size < 2**31 and parameter(cell,'OFFSET') == 0, 'native memory size/offset')
        init = cell['parameters']['INIT']
        require(len(init)==size*dw, 'native memory init width')
        require(init=='x'*len(init) or set(init)<=set('01'), 'partial memory initialization needs four-state words')
        init_words = None if 'x' in init else [int(init[len(init)-(i+1)*dw:len(init)-i*dw],2) for i in range(size)]
        for k in ('RD_CE_OVER_SRST','RD_CLK_ENABLE','RD_CLK_POLARITY','RD_COLLISION_X_MASK','RD_TRANSPARENCY_MASK','RD_WIDE_CONTINUATION','WR_PRIORITY_MASK','WR_WIDE_CONTINUATION'):
            require(parameter(cell,k)==0, 'native memory unsupported '+k)
        for k in ('WR_CLK_ENABLE','WR_CLK_POLARITY'):
            require(parameter(cell,k)==2**wp-1, 'native memory requires posedge clocked writes')
        for k in ('RD_ARST_VALUE','RD_SRST_VALUE','RD_INIT_VALUE'):
            require(cell['parameters'][k]=='x'*(rp*dw), 'native memory unsupported '+k)
        con=cell['connections']
        widths={'RD_ADDR':aw*rp,'RD_ARST':rp,'RD_CLK':rp,'RD_DATA':dw*rp,'RD_EN':rp,'RD_SRST':rp,'WR_ADDR':aw*wp,'WR_CLK':wp,'WR_DATA':dw*wp,'WR_EN':dw*wp}
        require(set(con)==set(widths) and all(len(con[k])==w for k,w in widths.items()),'native memory port dimensions')
        require(cell['port_directions']=={k:'output' if k=='RD_DATA' else 'input' for k in widths},'native memory port directions')
        require(con['RD_EN']==['1']*rp and con['RD_ARST']==['0']*rp and con['RD_SRST']==['0']*rp,'native read controls')
        require(all(b in ('0','1','x') for b in con['RD_CLK']), 'disabled read clock must be constant')
        i=len(memories)
        memories.append({'cell':cell_name,'name':f'{prefix}_{i}','source_memid':cell['parameters']['MEMID'],'aw':aw,'dw':dw,'rp':rp,'wp':wp,'size':size,'init_words':init_words})
    require(memories,'no native memories')
    return memories


def cut_memories(module, memories, emitted=False):
    module=copy.deepcopy(module)
    buses=[x['bits'] for group in ('ports','netnames') for x in module[group].values()]
    buses += [bs for c in module['cells'].values() for bs in c['connections'].values()]
    nxt=1+max(b for bs in buses for b in bs if type(b) is int)
    def allocate(width):
        nonlocal nxt
        result=list(range(nxt,nxt+width));nxt+=width;return result
    def port(name,direction,bits):
        require(name not in module['ports'],'memory cut port collision')
        module['ports'][name]={'direction':direction,'bits':bits}
        module['netnames'][name]={'hide_name':0,'bits':bits,'attributes':{}}
    def cell(name,ty,con,parameters):
        require(name not in module['cells'],'memory cut cell collision')
        module['cells'][name]={'type':ty,'parameters':{k:format(v,'032b') for k,v in parameters.items()},'port_directions':{k:'output' if k=='Y' else 'input' for k in con},'connections':con}
    contracts=[]
    for mem in memories:
        name,aw,dw,rp,wp=[mem[k] for k in ('name','aw','dw','rp','wp')]
        if emitted:
            matches=[n for n,c in module['cells'].items() if c['type']=='$mem_v2' and c['parameters']['MEMID']=='\\'+name]
            require(len(matches)==1,'emitted memory matching');key=matches[0]
        else:key=mem['cell']
        c=module['cells'].pop(key);con=c['connections']
        # Validate before cutting, including dormant controls and initialization.
        described=describe({'ports':{},'netnames':{},'cells':{key:c}})[0]
        require(all(described[k]==mem[k] for k in ('aw','dw','rp','wp','size')),'memory dimensions changed')
        contracts.append({k:int(v,2) if v and set(v)<=set('01') else v for k,v in c['parameters'].items() if k!='MEMID'})
        for i in range(rp):
            port(f'{name}_rd{i}','input',con['RD_DATA'][i*dw:(i+1)*dw])
            port(f'{name}_ra{i}','output',con['RD_ADDR'][i*aw:(i+1)*aw])
        order = mem.get('gate_write_order', list(range(wp))) if emitted else list(range(wp))
        require(sorted(order)==list(range(wp)), 'write-port matching must be a bijection')
        # The accepted clock flags are uniform and every priority/collision
        # matrix is zero; their contracts are invariant under this permutation.
        for i, j in enumerate(order):
            en=con['WR_EN'][j*dw:(j+1)*dw]
            active=allocate(1)
            cell(f'{name}_active{i}','$reduce_bool',{'A':en,'Y':active},{'A_SIGNED':0,'A_WIDTH':dw,'Y_WIDTH':1})
            port(f'{name}_wc{i}','output',con['WR_CLK'][j:j+1])
            port(f'{name}_we{i}','output',en)
            for field,width,suffix in [('WR_ADDR',aw,'wa'),('WR_DATA',dw,'wd')]:
                masked=allocate(width)
                cell(f'{name}_mask_{suffix}{i}','$mux',{'A':['0']*width,'B':con[field][j*width:(j+1)*width],'S':active,'Y':masked},{'WIDTH':width})
                port(f'{name}_{suffix}{i}','output',masked)
    require(not any(c['type'].startswith('$mem') for c in module['cells'].values()),'unmatched memory primitive')
    return module,contracts


class NativeImporter(Importer):
    def __init__(self, cut_design, top, original_ports, memories):
        super().__init__(cut_design,top,allow_state=True,allow_port_layouts=True,allow_bit_cells=True,compact_names=True)
        self.original_ports=original_ports
        self.native_memories=memories

    def render(self, outputs):
        require(not self.latches and not self.port_layouts,'native prototype latch/layout unsupported')
        observed=dict(outputs)
        user_outputs=[x for x in outputs if x[0] in self.original_ports]
        memory_inputs=[(n,w) for n,w in self.inputs if n not in self.original_ports]
        self.inputs=[(n,w) for n,w in self.inputs if n in self.original_ports]
        self.ports=self.original_ports
        mem_fields=[]
        for mem in self.native_memories:
            name,aw,dw,rp,wp=[mem[k] for k in ('name','aw','dw','rp','wp')]
            reads=[];writes=[]
            for i in range(rp):
                addr=observed[f'{name}_ra{i}'];out=f'{name}_rd{i}'
                reads.append('{ addr := '+addr.code+', out := '+lean_string(out)+' }')
                self.transition_outputs.append((f'{name}_ra{i}',addr))
            for i in range(wp):
                clock,mask,addr,data=[observed[f'{name}_{suffix}{i}'] for suffix in ('wc','we','wa','wd')]
                en=f'(.extract 0 {mask.code})'
                writes.append('{ clock := '+clock.code+', en := '+en+', addr := '+addr.code+', data := '+data.code+' }')
                full=Expr(dw,f'(.mux {en} (.const (BitVec.ofNat {dw} {2**dw-1})) (.const (BitVec.ofNat {dw} 0)))')
                self.transition_outputs.extend([(f'{name}_wc{i}',clock),(f'{name}_we{i}',full),(f'{name}_wa{i}',addr),(f'{name}_wd{i}',data)])
            init_field = '' if mem.get('init_words') is None else ', init := some [' + ', '.join(f'BitVec.ofNat {dw} {v}' for v in mem['init_words']) + ']'
            mem_fields.append('{ name := '+lean_string(name)+f', addrWidth := {aw}, dataWidth := {dw}, size := {mem["size"]}'+init_field+', writes := ['+', '.join(writes)+'], reads := ['+', '.join(reads)+'] }')
        if 'unconstrainedInit' in self.coverage_reasons:self.coverage_reasons.insert(self.coverage_reasons.index('unconstrainedInit'),'memShape')
        else:self.coverage_reasons.append('memShape')
        code=super().render(user_outputs)
        code=code.replace('  clock :=','  mems := ['+', '.join(mem_fields)+']\n  clock :=',1)
        extra=[(s['register'],s['width']) for s in self.states]+memory_inputs
        view='def transitionView : Module := { name := impl.name, inputs := impl.inputs ++ ['+', '.join('{ name := '+lean_string(n)+f', width := {w} }}' for n,w in extra)+'], wires := impl.wires, outputs := impl.outputs ++ transitionOutputs }\n\n'
        code=code.replace('example : impl.checkErrors',view+'example : impl.checkErrors',1)
        code=code.replace('example : impl.wellWidthedb = true','example : CheckWidth.moduleChecksb transitionView = true',1)
        return code
