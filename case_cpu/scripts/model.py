"""Independent Python ISA arithmetic plus an executable cycle oracle for co-simulation."""
from dataclasses import dataclass, field

MASK=(1<<32)-1
R={"add":(0,0),"sub":(32,0),"sll":(0,1),"slt":(0,2),"sltu":(0,3),
   "xor":(0,4),"srl":(0,5),"sra":(32,5),"or":(0,6),"and":(0,7),
   "mul":(1,0),"mulh":(1,1),"mulhsu":(1,2),"mulhu":(1,3),
   "div":(1,4),"divu":(1,5),"rem":(1,6),"remu":(1,7)}
I={"addi":0,"slti":2,"sltiu":3,"xori":4,"ori":6,"andi":7,
   "slli":1,"srli":5,"srai":5}
OPS=list(R)+list(I)+["lui","auipc"]

def signed(n): return n-(1<<32) if n&(1<<31) else n

def encode(op,rd=1,rs1=0,rs2=0,imm=0):
    if op in R:
        f7,f3=R[op]
        return f7<<25|rs2<<20|rs1<<15|f3<<12|rd<<7|0x33
    if op in I:
        im=(imm&31)|((32<<5) if op=='srai' else 0) if op in ['slli','srli','srai'] else imm&4095
        return im<<20|rs1<<15|I[op]<<12|rd<<7|0x13
    return (imm&0xfffff000)|(rd<<7)|(0x37 if op=='lui' else 0x17)

def decode(w):
    opc=w&127; f3=w>>12&7; f7=w>>25
    if opc==0x33:
        op=next((op for op,pair in R.items() if pair==(f7,f3)),None)
    elif opc==0x13:
        if f3==1: op='slli' if f7==0 else None
        elif f3==5: op={0:'srli',32:'srai'}.get(f7)
        else: op=next((op for op,f in I.items() if f==f3),None)
    else: op={0x37:'lui',0x17:'auipc'}.get(opc)
    if op is None: return None
    im=w&0xfffff000 if opc in (0x37,0x17) else ((w>>20)^0x800)-0x800
    return op,w>>7&31,w>>15&31,w>>20&31,im&MASK

def calculate(op,a,b,im,pc):
    sa,sb=signed(a),signed(b); si=signed(im)
    sh=b&31; shi=im&31
    if op=='add': v=a+b
    elif op=='sub': v=a-b
    elif op=='sll': v=a<<sh
    elif op=='slt': v=int(sa<sb)
    elif op=='sltu': v=int(a<b)
    elif op=='xor': v=a^b
    elif op=='srl': v=a>>sh
    elif op=='sra': v=sa>>sh
    elif op=='or': v=a|b
    elif op=='and': v=a&b
    elif op=='addi': v=a+im
    elif op=='slti': v=int(sa<si)
    elif op=='sltiu': v=int(a<im)
    elif op=='xori': v=a^im
    elif op=='ori': v=a|im
    elif op=='andi': v=a&im
    elif op=='slli': v=a<<shi
    elif op=='srli': v=a>>shi
    elif op=='srai': v=sa>>shi
    elif op=='lui': v=im
    elif op=='auipc': v=pc+im
    elif op=='mul': v=a*b
    elif op=='mulh': v=(sa*sb)>>32
    elif op=='mulhsu': v=(sa*b)>>32
    elif op=='mulhu': v=(a*b)>>32
    elif op in ('div','rem'):
        q=MASK if b==0 else (abs(sa)//abs(sb))*(-1 if (sa<0)!=(sb<0) else 1)
        v=q if op=='div' else (a if b==0 else sa-q*sb)
    elif op=='divu': v=MASK if b==0 else a//b
    elif op=='remu': v=a if b==0 else a%b
    else: raise ValueError(op)
    return v&MASK

def effect(rf,pc,w):
    op,rd,r1,r2,im=decode(w)
    return rd,calculate(op,rf[r1] if r1 else 0,rf[r2] if r2 else 0,im,pc)

def apply(rf,pc,rd,v):
    out=rf.copy()
    if rd: out[rd]=v
    out[0]=0
    return out,(pc+4)&MASK

@dataclass
class CPU:
    rf: list=field(default_factory=lambda:[0]*32)
    pc: int=0
    slots: list=field(default_factory=lambda:[None]*5)
    remaining: int=0

    def step(self,row):
        rst,valid,word,stalls,dbg,*seed=row
        if rst:
            self.rf=[0]+seed[1:]; self.pc=0; self.slots=[None]*5; self.remaining=0
            return (0,)*9
        f,d,x,m,w=self.slots
        retiring=w is not None and not(stalls&16)
        ri,rpc,rv=(w if retiring else (0,0,0))
        before=(int(retiring),ri,rpc,rv,(ri>>7&31) if retiring else 0,
                self.pc, self.rf[dbg] if dbg else 0,
                sum((v is not None)<<i for i,v in enumerate(self.slots)))
        if retiring:
            self.rf,self.pc=apply(self.rf,self.pc,ri>>7&31,rv)
            w=None
        if not(stalls&8) and w is None:
            w,m=m,None
        if not(stalls&4):
            if self.remaining: self.remaining-=1
            elif m is None: m,x=x,None
        if not(stalls&2) and x is None and d is not None:
            rf=self.rf.copy(); projected=self.pc
            for p in [w,m]:
                if p is not None:
                    wi,_,v=p
                    rf,projected=apply(rf,projected,wi>>7&31,v)
            rd,value=effect(rf,projected,d)
            x=(d,projected,value)
            op=decode(d)[0]
            self.remaining=33 if op in ['div','divu','rem','remu'] else (2 if op.startswith('mul') else 0)
            d=None
        if d is None: d,f=f,None
        accepted=bool(valid and not(stalls&1) and f is None and decode(word) is not None)
        if accepted: f=word
        self.slots=[f,d,x,m,w]
        return (int(accepted),)+before
