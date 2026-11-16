import MemNativeLanes
import MemDecode
namespace CaseCPUMem.Source
open LeanRTL MemCPUShallow
open CaseCPU.Bridge (RF readRF writeRF resetRF)
set_option maxRecDepth 65536
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

abbrev Packed := BitVec 174

def pword (p : Packed) : Word := (p >>> 142).setWidth 32
def pcode (p : Packed) : BitVec 6 := (p >>> 136).setWidth 6
def ppc (p : Packed) : Word := (p >>> 104).setWidth 32
def prd (p : Packed) : Reg := (p >>> 99).setWidth 5
def pvalue (p : Packed) : Word := (p >>> 67).setWidth 32
def paddr (p : Packed) : Word := (p >>> 35).setWidth 32
def pdata (p : Packed) : Word := (p >>> 3).setWidth 32
def pfault (p : Packed) : BitVec 3 := p.setWidth 3

def pack (w : Word) (code : BitVec 6) (pc : Word) (rd : Reg)
    (value addr data : Word) (fault : BitVec 3) : Packed :=
  w ++ code ++ pc ++ rd ++ value ++ addr ++ data ++ fault

structure Physical where
  rf : RF
  pc : Word
  fault : BitVec 3
  fi : Word
  di : Word
  x : Packed
  m : Packed
  w : Packed
  fv : Bool
  dv : Bool
  xv : Bool
  mv : Bool
  wv : Bool
  count : BitVec 6
  waitCount : BitVec 4

def physical (r : Env) : Physical := {
  rf := r.lookup "r12" 1024,pc := r.lookup "r13" 32,fault := r.lookup "r14" 3,
  fi := r.lookup "r20" 32,di := r.lookup "r21" 32,
  x := r.lookup "r22" 174,m := r.lookup "r23" 174,w := r.lookup "r24" 174,
  fv := r.lookup "r15" 1 == 1,dv := r.lookup "r16" 1 == 1,
  xv := r.lookup "r17" 1 == 1,mv := r.lookup "r18" 1 == 1,wv := r.lookup "r19" 1 == 1,
  count := r.lookup "r25" 6,waitCount := r.lookup "r26" 4 }

def pins (b : Env) : Raw.Pins := {
  reset := b.lookup "rst" 1 == 1,seed := b.lookup "reg_init" 1024,
  word := b.lookup "insn" 32,valid := b.lookup "insn_valid" 1 == 1,
  sf := b.lookup "stall_fetch" 1 == 1,sd := b.lookup "stall_decode" 1 == 1,
  sx := b.lookup "stall_execute" 1 == 1,sm := b.lookup "stall_memory" 1 == 1,
  sw := b.lookup "stall_writeback" 1 == 1,delay := b.lookup "memory_delay" 4,
  debugReg := b.lookup "debug_reg_addr" 5,debugMem := b.lookup "debug_mem_addr" 8 }

def pinEnv (i : Raw.Pins) (o : Env) : Env := fun n =>
  if n = "clk" then 1 else if n = "rst" then i.reset.toNat else
  if n = "reg_init" then i.seed.toNat else if n = "insn" then i.word.toNat else
  if n = "insn_valid" then i.valid.toNat else if n = "stall_fetch" then i.sf.toNat else
  if n = "stall_decode" then i.sd.toNat else if n = "stall_execute" then i.sx.toNat else
  if n = "stall_memory" then i.sm.toNat else if n = "stall_writeback" then i.sw.toNat else
  if n = "memory_delay" then i.delay.toNat else if n = "debug_reg_addr" then i.debugReg.toNat else
  if n = "debug_mem_addr" then i.debugMem.toNat else o n

def destination (p : Raw.Packet) : Reg :=
  if isStore (Raw.instr p.word).op || (Raw.instr p.word).op == .fence then 0 else (Raw.instr p.word).rd

/-- Redundant RTL opcode/destination fields are related explicitly. Address/data
    lanes used only by memory operations are not constrained for ALU bubbles. -/
structure PacketRel (p : Packed) (q : Raw.Packet) : Prop where
  word : pword p = q.word
  code : pcode p = opCode (Raw.instr q.word).op
  pc : ppc p = q.pc
  rd : prd p = destination q
  value : pvalue p = q.value
  fault : pfault p = q.fault
  addr : (isLoad (Raw.instr q.word).op || isStore (Raw.instr q.word).op) = true → paddr p = q.addr
  data : isStore (Raw.instr q.word).op = true → pdata p = q.data

structure Related (p : Physical) (mem : Memory) (q : Raw.State) : Prop where
  rf : p.rf = q.rf
  pc : p.pc = q.pc
  fault : p.fault = q.fault
  ram : mem = q.mem
  fv : p.fv = q.fv
  dv : p.dv = q.dv
  xv : p.xv = q.xv
  mv : p.mv = q.mv
  wv : p.wv = q.wv
  count : p.count = q.count
  waitCount : p.waitCount = q.waitCount
  fetchWord : q.fv = true → p.fi = q.fi
  decodeWord : q.dv = true → p.di = q.di
  executePacket : q.xv = true → PacketRel p.x q.x
  memoryPacket : q.mv = true → PacketRel p.m q.m
  writebackPacket : q.wv = true → PacketRel p.w q.w

noncomputable def netNext (b : Env) : Physical := {
  rf := V_w371 b,pc := V_w297 b,fault := V_w296 b,
  fi := V_w719 b,di := V_w668 b,x := V_w729 b,m := V_w421 b,w := V_w420 b,
  fv := V_w720 b == 1,dv := V_w669 b == 1,xv := V_w598 b == 1,
  mv := V_w422 b == 1,wv := V_w370 b == 1,count := V_w597 b,waitCount := V_w473 b }

noncomputable def postCommit (b : Env) : Physical := {
  physical b with
    rf := V_next_registers b,pc := V_next_committed_pc b,fault := V_next_fault b,
    fi := V_w280 b,di := V_w279 b,x := V_w278 b,m := V_w277 b,w := V_w276 b,
    fv := V_w285 b == 1,dv := V_w284 b == 1,xv := V_w283 b == 1,
    mv := V_w282 b == 1,wv := V_w281 b == 1,count := V_w275 b,waitCount := V_w274 b }

noncomputable def postMemory (b : Env) : Physical := {
  postCommit b with
    w := V_w414 b,wv := V_w356 b == 1,mv := V_w358 b == 1,
    waitCount := V_w354 b }

noncomputable def postExecute (b : Env) : Physical := {
  postMemory b with
    m := V_w405 b,mv := V_w407 b == 1,xv := V_w409 b == 1,
    count := V_w342 b,waitCount := V_w471 b }

noncomputable def postDispatch (b : Env) : Physical := {
  postExecute b with
    x := V_w727 b,xv := V_w590 b == 1,dv := V_w592 b == 1,count := V_w589 b }

noncomputable def postFetch (b : Env) : Physical := {
  postDispatch b with
    di := V_w602 b,dv := V_w601 b == 1,fv := V_w600 b == 1 }

noncomputable def postAccept (b : Env) : Physical := {
  postFetch b with
    fi := V_w706 b,fv := V_w705 b == 1 }

/-- Pins and undefined-value choices remain universally quantified. Native RAM
    read values are bound by NativeMemory.Program, never passed as free pins. -/
def rtlStep (s : NativeMemory.State) (i : Raw.Pins) (o : Env) : NativeMemory.State :=
  MemCPUImported.program.step s (pinEnv i o)

end CaseCPUMem.Source
