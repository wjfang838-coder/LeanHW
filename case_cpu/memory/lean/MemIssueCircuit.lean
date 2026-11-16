import MemDecodeFields
import MemALUCircuit
import MemStageRefinement
import Forwarding
open LeanRTL MemCPUShallow
open CaseCPU.Bridge (RF readRF writeRF bypass read_write_bypass)
namespace CaseCPUMem.Source
set_option maxRecDepth 65536
set_option maxHeartbeats 12000000
set_option linter.unusedSimpArgs false

def forwardPhysical (p : Physical) (r : Reg) : Word :=
  bypass p.mv (prd p.m) (pvalue p.m) r
    (bypass p.wv (prd p.w) (pvalue p.w) r (readRF p.rf r))

def blockedPhysical (p : Physical) (code : BitVec 6) : Bool :=
  (p.mv && codeBarrier (pcode p.m)) || (p.wv && codeBarrier (pcode p.w)) ||
    (codeBarrier code && (p.mv || p.wv))

theorem running_bit (b : Env) (hz : V_next_fault b = (0#3)) : V_w333 b = (1#1) := by
  simp [V_w333,hz]

theorem issue_candidate (b : Env) (hz : V_next_fault b = (0#3)) :
    (V_w457 b = (1#1)) ↔
      (! (pins b).sd && !(postExecute b).xv && (postExecute b).dv) = true := by
  have hp := running_payloads b hz
  have hd : V_w284 b = b.lookup "r16" 1 := by
    have h := hp.2.2.2.2.2.2.1
    simp only [postCommit,physical] at h
    bv_decide
  simp only [postExecute,postMemory,postCommit,pins,physical,hd,
    V_w457,V_w456,V_w28,V_w430]
  bv_decide

theorem issue_opcode (b : Env) (hz : V_next_fault b = (0#3))
    (hg : V_w457 b = (1#1)) : V_w467 b = codeBits (b.lookup "r21" 32) := by
  simp [V_w467,V_w466,running_bit b hz,hg,decoder_w380]

theorem issue_blocked (b : Env) (hz : V_next_fault b = (0#3))
    (hg : V_w457 b = (1#1)) :
    (V_w565 b = (1#1)) ↔ blockedPhysical (postExecute b) (codeBits (b.lookup "r21" 32)) = true := by
  have hrun := running_bit b hz
  have hop := issue_opcode b hz hg
  simp only [blockedPhysical,postExecute,postMemory,postCommit,pcode,codeBarrier,codeLoad,codeStore,
    V_w565,V_w555,V_w553,V_w542,V_w541,V_w527,V_w526,V_w525,V_w465,V_w454,V_w453,V_w452,V_w451,V_w450,V_w524,V_w523,V_w522,V_w464,V_w449,V_w448,V_w447,V_w424,V_w554,V_w544,V_w543,V_w521,V_w520,V_w519,V_w463,V_w446,V_w445,V_w444,V_w443,V_w442,V_w518,V_w517,V_w516,V_w462,V_w441,V_w440,V_w439,V_w425,V_w564,V_w563,V_w562,V_w561,V_w560,V_w556,V_w550,V_w515,V_w514,V_w513,V_w512,V_w511,V_w559,V_w558,V_w557,V_w549,V_w510,V_w509,V_w508,V_w474,V_w433,hrun,hg,hop,Packed]
  bv_decide

theorem forward_left (b : Env) : V_w499 b =
    forwardPhysical (postExecute b) ((b.lookup "r21" 32 >>> 15).setWidth 5) := by
  simp only [forwardPhysical,postExecute,postMemory,postCommit,physical,prd,pvalue,bypass,
    V_w499,V_w459,V_w435,V_w497,V_w428,V_w461,V_w458,V_w434,V_w438,V_w426,V_w389,V_w35,V_w373,readRF,CaseCPU.Bridge.offset,RF,Reg,CaseCPU.Reg,Word,Packed]
  bv_decide

theorem forward_right (b : Env) : V_w498 b =
    forwardPhysical (postExecute b) ((b.lookup "r21" 32 >>> 20).setWidth 5) := by
  simp only [forwardPhysical,postExecute,postMemory,postCommit,physical,prd,pvalue,bypass,
    V_w498,V_w459,V_w435,V_w496,V_w429,V_w460,V_w458,V_w434,V_w437,V_w427,V_w388,V_w36,V_w374,readRF,CaseCPU.Bridge.offset,RF,Reg,CaseCPU.Reg,Word,Packed]
  bv_decide

theorem immediate_bits (b : Env) :
    ((b.lookup "r21" 32 >>> 31).setWidth 1 ++ V_w323 b) = immediate (b.lookup "r21" 32) := by
  simp only [immediate,V_w323,V_w51,V_w322,V_w265,V_w53,V_w54,Word]
  bv_decide

theorem issue_arguments (b : Env) (hz : V_next_fault b = (0#3))
    (hg : V_w457 b = (1#1)) (hb : V_w565 b ≠ (1#1)) :
    V_w577 b = forwardPhysical (postExecute b) ((b.lookup "r21" 32 >>> 15).setWidth 5) ∧
    V_w574 b = forwardPhysical (postExecute b) ((b.lookup "r21" 32 >>> 20).setWidth 5) ∧
    V_w580 b = immediate (b.lookup "r21" 32) ∧
    V_w659 b = (postExecute b).pc + (if (postExecute b).wv then 4 else 0) +
      (if (postExecute b).mv then 4 else 0) := by
  simp only [V_w577,V_w576,V_w575,V_w574,V_w573,V_w572,V_w580,V_w579,V_w578,
    running_bit b hz,hg,hb,↓reduceIte,forward_left,forward_right,immediate_bits,
    V_w659,V_w658,V_w657,V_w656,V_w615,V_w571,V_w570,V_w569,V_w387,V_w309,postExecute,postMemory,postCommit]
  bv_decide

theorem issue_rd (b : Env) (hz : V_next_fault b = (0#3))
    (hg : V_w457 b = (1#1)) (hb : V_w565 b ≠ (1#1)) : V_w660 b =
    (if codeStore (V_w467 b) || (V_w467 b == (37#6)) then (0#5) else
      (b.lookup "r21" 32 >>> 7).setWidth 5) := by
  simp only [V_w660,V_w634,V_w583,V_w582,V_w581,V_w557,V_w549,V_w510,V_w509,V_w508,V_w474,codeStore,running_bit b hz,hg,hb]
  bv_decide

theorem issue_wait (b : Env) (op : Op) (hc : V_w467 b = opCode op) :
    V_w552 b = BitVec.ofNat 6 (latency op-1) := by
  cases op with
  | alu a => cases a <;> simp [V_w552,V_w547,V_w500,V_w501,V_w502,V_w503,V_w551,V_w548,V_w504,V_w505,V_w506,V_w507,hc,opCode,CaseCPU.Bridge.opCode,latency,CaseCPU.latency]
  | _ => simp [V_w552,V_w547,V_w500,V_w501,V_w502,V_w503,V_w551,V_w548,V_w504,V_w505,V_w506,V_w507,hc,opCode,latency]

def faultForOp (op : Op) (addr : Word) : BitVec 3 :=
  if isLoad op || isStore op then accessFault op addr else 0

theorem issue_fault (b : Env) (hz : V_next_fault b = (0#3))
    (hg : V_w457 b = (1#1)) (hb : V_w565 b ≠ (1#1))
    (op : Op) (hc : V_w467 b = opCode op) :
    V_w725 b = faultForOp op (V_w614 b) := by
  have hrun := running_bit b hz
  cases op with
  | alu a => cases a <;>
      simp only [V_w725,V_w635,V_w568,V_w567,V_w566,V_w556,V_w550,V_w515,V_w514,V_w513,V_w512,V_w511,V_w583,V_w582,V_w581,V_w557,V_w549,V_w510,V_w509,V_w508,V_w724,V_w702,V_w701,V_w700,V_w695,V_w545,V_w670,V_w625,V_w546,V_w723,V_w716,V_w715,V_w714,V_w713,V_w712,V_w722,V_w671,V_w721,V_w711,V_w710,V_w709,V_w708,V_w707,V_w699,hrun,hg,hb,hc,opCode,CaseCPU.Bridge.opCode,faultForOp,isLoad,isStore,Word] <;> bv_decide
  | _ =>
      simp only [V_w725,V_w635,V_w568,V_w567,V_w566,V_w556,V_w550,V_w515,V_w514,V_w513,V_w512,V_w511,V_w583,V_w582,V_w581,V_w557,V_w549,V_w510,V_w509,V_w508,V_w724,V_w702,V_w701,V_w700,V_w695,V_w545,V_w670,V_w625,V_w546,V_w723,V_w716,V_w715,V_w714,V_w713,V_w712,V_w722,V_w671,V_w721,V_w711,V_w710,V_w709,V_w708,V_w707,V_w699,hrun,hg,hb,hc,opCode,faultForOp,isLoad,isStore,accessFault,Word] <;> bv_decide

#print axioms issue_arguments
#print axioms issue_fault

theorem issued_packet (b : Env) (hg : V_w457 b = (1#1)) (hb : V_w565 b ≠ (1#1)) :
    V_w727 b = pack (b.lookup "r21" 32) (V_w467 b) (V_w659 b) (V_w660 b)
      (V_w694 b) (V_w614 b) (V_w574 b) (V_w725 b) := by
  simp only [V_w727,V_w603,V_w588,V_w663,V_w662,V_w703,V_w661,V_w587,V_w726,hg,hb,↓reduceIte,pack,Word,Packed]
  bv_decide

theorem dispatch_state (b : Env) (hz : V_next_fault b = (0#3)) :
    postDispatch b =
      if V_w457 b = (1#1) ∧ V_w565 b ≠ (1#1) then
        {postExecute b with x := V_w727 b,xv := true,dv := false,count := V_w552 b}
      else postExecute b := by
  by_cases hg : V_w457 b = (1#1)
  all_goals by_cases hb : V_w565 b = (1#1)
  all_goals
    simp only [postDispatch,postExecute,postMemory,postCommit,
      V_w589,V_w590,V_w592,V_w591,V_w584,V_w585,V_w586,V_w727,
      V_w603,V_w588,V_w663,V_w662,V_w703,V_w661,V_w587,V_w726,
      running_bit b hz,hg,hb,↓reduceIte,Physical.mk.injEq]
    simp_all
    all_goals simp only [Packed,Word]
    all_goals bv_decide

theorem issue_nonalu_zero (b : Env) (op : Op) (hc : V_w467 b = opCode op)
    (hn : ∀ a, op ≠ .alu a) : V_w694 b = (0#32) := by
  cases op with
  | alu a => exact False.elim (hn a rfl)
  | _ => simp [V_w694,V_w540,V_w530,V_w479,V_w478,V_w529,V_w475,V_w504,V_w528,V_w507,V_w500,V_w481,V_w480,V_w477,V_w476,V_w505,V_w506,V_w501,V_w502,V_w503,V_w684,V_w536,V_w678,V_w534,V_w674,V_w649,V_w630,V_w642,V_w673,V_w651,V_w650,V_w631,V_w628,V_w629,V_w641,V_w653,V_w652,V_w627,V_w677,V_w675,V_w655,V_w654,V_w626,V_w646,V_w676,V_w645,V_w644,V_w683,V_w535,V_w680,V_w679,V_w643,V_w672,V_w618,V_w609,V_w682,V_w619,V_w607,V_w605,V_w681,V_w617,V_w648,V_w693,V_w539,V_w531,V_w486,V_w485,V_w488,V_w487,V_w484,V_w483,V_w482,V_w689,V_w537,V_w686,V_w612,V_w685,V_w640,V_w639,V_w688,V_w620,V_w616,V_w687,V_w647,V_w608,V_w692,V_w538,V_w532,V_w490,V_w489,V_w492,V_w491,V_w691,V_w621,V_w606,V_w611,V_w690,V_w638,V_w637,V_w624,V_w533,V_w494,V_w493,V_w622,V_w604,V_w610,V_w623,V_w495,V_w613,hc,opCode]

@[simp] theorem pword_pack (w : Word) (c : BitVec 6) (pc : Word) (rd : Reg) (v a d : Word) (f : BitVec 3) :
    pword (pack w c pc rd v a d f) = w := by simp only [pword,pack,Word,Packed,Reg];bv_decide
@[simp] theorem pcode_pack (w : Word) (c : BitVec 6) (pc : Word) (rd : Reg) (v a d : Word) (f : BitVec 3) :
    pcode (pack w c pc rd v a d f) = c := by simp only [pcode,pack,Word,Packed,Reg];bv_decide
@[simp] theorem ppc_pack (w : Word) (c : BitVec 6) (pc : Word) (rd : Reg) (v a d : Word) (f : BitVec 3) :
    ppc (pack w c pc rd v a d f) = pc := by simp only [ppc,pack,Word,Packed,Reg];bv_decide
@[simp] theorem prd_pack (w : Word) (c : BitVec 6) (pc : Word) (rd : Reg) (v a d : Word) (f : BitVec 3) :
    prd (pack w c pc rd v a d f) = rd := by simp only [prd,pack,Word,Packed,Reg];bv_decide
@[simp] theorem pvalue_pack (w : Word) (c : BitVec 6) (pc : Word) (rd : Reg) (v a d : Word) (f : BitVec 3) :
    pvalue (pack w c pc rd v a d f) = v := by simp only [pvalue,pack,Word,Packed,Reg];bv_decide
@[simp] theorem paddr_pack (w : Word) (c : BitVec 6) (pc : Word) (rd : Reg) (v a d : Word) (f : BitVec 3) :
    paddr (pack w c pc rd v a d f) = a := by simp only [paddr,pack,Word,Packed,Reg];bv_decide
@[simp] theorem pdata_pack (w : Word) (c : BitVec 6) (pc : Word) (rd : Reg) (v a d : Word) (f : BitVec 3) :
    pdata (pack w c pc rd v a d f) = d := by simp only [pdata,pack,Word,Packed,Reg];bv_decide
@[simp] theorem pfault_pack (w : Word) (c : BitVec 6) (pc : Word) (rd : Reg) (v a d : Word) (f : BitVec 3) :
    pfault (pack w c pc rd v a d f) = f := by simp only [pfault,pack,Word,Packed,Reg];bv_decide

#print axioms dispatch_state
#print axioms issued_packet
end CaseCPUMem.Source
