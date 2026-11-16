"""Independent byte-addressed ISA and transaction-effect pipeline oracle."""
from dataclasses import dataclass,field
from pathlib import Path
import importlib.util
p=Path(__file__).resolve().parents[2]/'scripts/model.py'
s=importlib.util.spec_from_file_location('arithmetic_reference',p)
base=importlib.util.module_from_spec(s)
import sys
sys.modules[s.name]=base;s.loader.exec_module(base)
MASK=base.MASK
LOADS={'lb':0,'lh':1,'lw':2,'lbu':4,'lhu':5}
STORES={'sb':0,'sh':1,'sw':2}
OPS=base.OPS+list(LOADS)+list(STORES)+['fence']

def encode(op,rd=1,rs1=0,rs2=0,imm=0):
    if op in LOADS:return (imm&4095)<<20|rs1<<15|LOADS[op]<<12|rd<<7|3
    if op in STORES:return ((imm&4095)>>5)<<25|rs2<<20|rs1<<15|STORES[op]<<12|(imm&31)<<7|35
    if op=='fence':return 0x0000000f
    return base.encode(op,rd,rs1,rs2,imm)

def decode(w):
    opc=w&127;f=w>>12&7;rd=w>>7&31;r1=w>>15&31;r2=w>>20&31
    if opc==3:
        op=next((k for k,v in LOADS.items() if v==f),None)
        return None if op is None else (op,rd,r1,0,base.signed((((w>>20)^2048)-2048)&MASK))
    if opc==35:
        op=next((k for k,v in STORES.items() if v==f),None)
        im=(w>>25<<5)|(w>>7&31);im=(im^2048)-2048
        return None if op is None else (op,0,r1,r2,im)
    if opc==15 and f==0 and rd==0 and r1==0:return ('fence',0,0,0,0)
    return base.decode(w)

def barrier(ins):return ins[0] in LOADS or ins[0] in STORES or ins[0]=='fence'

def effect(rf,pc,mem,ins):
    op,rd,r1,r2,im=ins
    a=rf[r1] if r1 else 0;b=rf[r2] if r2 else 0
    if op=='fence':return (0,0,None,0,0)
    if op not in LOADS and op not in STORES:return (rd,base.calculate(op,a,b,im&MASK,pc),None,0,0)
    addr=(a+im)&MASK
    size=1 if op in ('lb','lbu','sb') else 2 if op in ('lh','lhu','sh') else 4
    cause=(2 if op in STORES else 1) if addr%size else (4 if op in STORES else 3) if addr>=1024 else 0
    if cause:return (0,0,None,cause,addr)
    if op in LOADS:
        v=int.from_bytes(mem[addr:addr+size],'little',signed=op in ('lb','lh'))&MASK
        return (rd,v,None,0,addr)
    return (0,0,(addr,size,b),0,addr)

def apply(rf,pc,mem,e):
    rd,v,store,cause,_=e
    rf=rf.copy();mem=mem.copy()
    if cause:return rf,pc,mem,cause
    if rd:rf[rd]=v
    rf[0]=0
    if store:
        addr,size,data=store
        mem[addr:addr+size]=list((data&((1<<(size*8))-1)).to_bytes(size,'little'))
    return rf,(pc+4)&MASK,mem,0

@dataclass
class Packet:
    word:int
    ins:tuple
    effect:tuple
    pc:int
    address:int

@dataclass
class CPU:
    rf:list=field(default_factory=lambda:[0]*32)
    pc:int=0
    mem:list=field(default_factory=lambda:[0]*1024)
    fault:int=0
    slots:list=field(default_factory=lambda:[None]*5)
    stats:list=field(default_factory=lambda:[0]*12)
    remaining:int=0
    wait:int=0

    def step(self,row):
        rst,valid,word,stalls,delay,dbg,md,dc,*seed=row
        f,d,x,m,w=self.slots
        fire=bool(not rst and not self.fault and w and not(stalls&16))
        ri=w.word if fire else 0;rpc=w.pc if fire else 0
        rd=w.effect[0] if fire else 0;rv=w.effect[1] if fire else 0
        trap=w.effect[3] if fire else 0
        st=w.effect[2] if fire else None
        addr=w.address if fire else 0
        data=((st[2]<<((st[0]&3)*8))&MASK) if st else 0
        mask=(((1<<(st[1]*8))-1)<<((st[0]&3)*8))&MASK if st else 0
        before=[int(fire),ri,rpc,rd,rv,int(st is not None),addr,data,mask,int(trap!=0),trap,
                self.pc,int(self.fault!=0),self.fault,self.rf[dbg] if dbg else 0,
                int.from_bytes(self.mem[4*md:4*md+4],'little'),sum((p is not None)<<i for i,p in enumerate(self.slots)),self.stats[dc] if dc<12 else 0]
        if not rst:
            ticks=[1,fire,fire and not trap and w.ins[0] in LOADS if w else False,st is not None,trap!=0,
                   f is not None and stalls&1,d is not None and stalls&2,x is not None and stalls&4,
                   m is not None and stalls&8,w is not None and stalls&16,m is not None and self.wait!=0,False]
            self.stats=[(v+int(bool(t)))&MASK for v,t in zip(self.stats,ticks)]
        if rst:
            self.stats=[0]*12
            self.rf=[0]+seed[1:];self.pc=0;self.fault=0;self.slots=[None]*5;self.remaining=0;self.wait=0
            return (0,*before)
        if fire:
            self.rf,self.pc,self.mem,self.fault=apply(self.rf,self.pc,self.mem,w.effect)
            if self.fault:
                self.slots=[None]*5;self.remaining=0;self.wait=0
                return (0,*before)
            w=None
        if self.fault:return (0,*before)
        if not(stalls&8):
            if self.wait:self.wait-=1
            elif w is None:w,m=m,None
        if not(stalls&4):
            if self.remaining:self.remaining-=1
            elif m is None:
                m,x=x,None
                self.wait=delay if m and barrier(m.ins) else 0
        if not(stalls&2) and x is None and d is not None:
            locked=any(p and barrier(p.ins) for p in (m,w))
            ins=decode(d)
            blocked=locked or (barrier(ins) and (m is not None or w is not None))
            if blocked:self.stats[11]=(self.stats[11]+1)&MASK
            if not blocked:
                rf,pc,mem=self.rf,self.pc,self.mem
                for p in (w,m):
                    if p:rf,pc,mem,_=apply(rf,pc,mem,p.effect)
                physical_im = d&0xfffff000 if (d&127) in (0x37,0x17) else ins[4] if (d&127)==35 else ((d>>20)^2048)-2048
                physical_addr=((rf[d>>15&31] if d>>15&31 else 0)+physical_im)&MASK
                x=Packet(d,ins,effect(rf,pc,mem,ins),pc,physical_addr)
                self.remaining=2 if ins[0] in ('mul','mulh','mulhsu','mulhu') else 33 if ins[0] in ('div','divu','rem','remu') else 0
                d=None
        if d is None:d,f=f,None
        ready=not(stalls&1) and f is None and decode(word) is not None
        accepted=int(bool(valid and ready))
        if accepted:f=word
        self.slots=[f,d,x,m,w]
        return (accepted,*before)
