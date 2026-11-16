"""Native asynchronous-read / positive-edge-write RAM import profile.

RAM contents are carried by NativeMemory.State.arrays. RD_DATA ports become
synthetic pure-logic inputs which Program.bindReads binds from the native array;
they are never unconstrained environment inputs of the complete program.
The first profile accepts full-depth, uninitialized arrays, one write port, and
read addresses depending only on pre-edge registers / real inputs. Unsupported
shapes are refused rather than silently flattened or abstracted away.
"""
from copy import deepcopy
import re
from .importer import Unsupported, require, parameter, lean_string
from .symbolic import SymbolicImporter


class NativeMemoryImporter:
    def __init__(self, design, top):
        self.original = deepcopy(design)
        self.top = top
        require(set(design.get('modules', {})) == {top}, 'native import needs one flattened module')
        self.physical_ports = list(design['modules'][top]['ports'])
        pure = deepcopy(design)
        module = pure['modules'][top]
        self.memory_cells = []
        self.virtual = []
        for cell_name, cell in list(module.get('cells', {}).items()):
            if cell['type'] != '$mem_v2':
                continue
            aw, dw = parameter(cell,'ABITS'),parameter(cell,'WIDTH')
            size = parameter(cell,'SIZE')
            rp, wp = parameter(cell,'RD_PORTS'),parameter(cell,'WR_PORTS')
            require(size == 1 << aw and parameter(cell,'OFFSET') == 0,'partial-depth native memory is not supported')
            require(aw > 0 and dw > 0 and wp <= 1,'native memory needs positive widths and at most one write port')
            require(set(cell['parameters']['INIT']) <= {'x'},'native initial image needs a separate initialization proof')
            require(parameter(cell,'RD_CLK_ENABLE') == 0,'native profile requires asynchronous reads')
            require(parameter(cell,'RD_TRANSPARENCY_MASK') == 0 and parameter(cell,'RD_COLLISION_X_MASK') == 0,'unsupported RAM transparency/collision mode')
            con = cell['connections']
            require(all(b == '1' for b in con['RD_EN']),'read-enable gating is not supported')
            require(all(b == '0' for b in con['RD_ARST']+con['RD_SRST']),'read-reset gating is not supported')
            if wp:
                require(parameter(cell,'WR_CLK_ENABLE') == 1 and parameter(cell,'WR_CLK_POLARITY') == 1,'RAM write clock must be positive edge')
                require(con['WR_CLK'] == module['ports'].get('clk',{}).get('bits'),'native RAM must use direct common clk')
            ident = str(cell['parameters'].get('MEMID',cell_name)).lstrip('\\')
            require(re.fullmatch(r'[A-Za-z_][A-Za-z0-9_]*',ident) is not None,'unsupported memory identifier')
            index = len(self.memory_cells)
            reads = []
            for r in range(rp):
                name = f'__native_read_{index}_{r}'
                require(name not in module['ports'],'native virtual-port collision')
                data = con['RD_DATA'][r*dw:(r+1)*dw]
                require(len(data)==dw,'native RD_DATA dimensions')
                module['ports'][name] = {'direction':'input','bits':data}
                reads.append((name,con['RD_ADDR'][r*aw:(r+1)*aw]))
                self.virtual.append(name)
            self.memory_cells.append(dict(name=ident,cell=cell,reads=reads,aw=aw,dw=dw,size=size,wp=wp))
            del module['cells'][cell_name]
        require(self.memory_cells,'native profile requires at least one real memory')
        require(len({m['name'] for m in self.memory_cells})==len(self.memory_cells),'duplicate native memory name')
        self.pure = SymbolicImporter(pure,top)

    def build(self):
        text = self.pure.build()
        prefix = text.split('def lintBase',1)[0]
        require(prefix != text,'missing deterministic data/proof boundary')
        prefix = prefix.replace('namespace V2LeanImported','namespace MemCPUImported')
        base_names = {n for n,_ in self.pure.inputs if n not in self.virtual}
        base_names |= {s['register'] for s in self.pure.states}
        memories,reads = [],[]
        self.metadata = []
        for m in self.memory_cells:
            for name,bits in m['reads']:
                expr = self.pure.bus(bits)
                names = set(re.findall(r'\.var "([^"\n]+)"',expr.code))
                require(names <= base_names,f'RAM read address must depend only on old registers/inputs: {names-base_names}')
                reads.append('{ '+f'memory := {lean_string(m["name"])}, out := {lean_string(name)}, addrWidth := {m["aw"]}, dataWidth := {m["dw"]}, addr := {expr.code}'+' }')
            write = 'none'
            if m['wp']:
                con = m['cell']['connections']
                addr,data,mask = (self.pure.bus(con[n]) for n in ['WR_ADDR','WR_DATA','WR_EN'])
                write = 'some { '+f'addr := {addr.code}, data := {data.code}, mask := {mask.code}'+' }'
            memories.append('{ '+f'name := {lean_string(m["name"])}, addrWidth := {m["aw"]}, dataWidth := {m["dw"]}, write := {write}'+' }')
            self.metadata.append(dict(name=m['name'],addr_width=m['aw'],data_width=m['dw'],size=m['size'],read_ports=len(m['reads']),write_ports=m['wp'],initial_contents='arbitrary'))
        return ('import LeanRTL.Core.NativeMemory\n'+prefix+
                'def program : LeanRTL.NativeMemory.Program := { logic := core, memories := ['+
                ',\n    '.join(memories)+'], reads := ['+',\n    '.join(reads)+'] }\n\nend MemCPUImported\n')
