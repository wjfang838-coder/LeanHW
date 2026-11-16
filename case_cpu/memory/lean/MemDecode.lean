import MemRaw
import DecoderTable
namespace CaseCPUMem.Source
set_option maxRecDepth 20000
set_option maxHeartbeats 8000000
set_option linter.unusedSimpArgs false

def opCode : Op → BitVec 6
  | .alu a => CaseCPU.Bridge.opCode a
  | .lb => 29 | .lh => 30 | .lw => 31 | .lbu => 32 | .lhu => 33
  | .sb => 34 | .sh => 35 | .sw => 36 | .fence => 37

def loadCode (f : BitVec 3) : BitVec 6 :=
  if f = 0 then 29 else if f = 1 then 30 else if f = 2 then 31
  else if f = 4 then 32 else if f = 5 then 33 else 63

def storeCode (f : BitVec 3) : BitVec 6 :=
  if f = 0 then 34 else if f = 1 then 35 else if f = 2 then 36 else 63

def codeBits (w : Word) : BitVec 6 :=
  if w.setWidth 7 = 3 then loadCode ((w >>> 12).setWidth 3)
  else if w.setWidth 7 = 35 then storeCode ((w >>> 12).setWidth 3)
  else if w.setWidth 7 = 15 && (w >>> 12).setWidth 3 = 0 &&
      (w >>> 7).setWidth 5 = 0 && (w >>> 15).setWidth 5 = 0 then 37
  else CaseCPU.Bridge.codeBits w

def decodeCode (w : Word) : BitVec 6 := ((decode w).map (fun i => opCode i.op)).getD 63

theorem slice_nat (w : Word) (n k : Nat) :
    (w >>> n).setWidth k = BitVec.ofNat k (w.toNat/2^n) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth,BitVec.toNat_ushiftRight,Nat.shiftRight_eq_div_pow]

theorem low_nat (w : Word) : w.setWidth 7 = BitVec.ofNat 7 (w.toNat%128) := by
  apply BitVec.eq_of_toNat_eq
  simp [BitVec.toNat_setWidth]

theorem funct_nat (w : Word) : (w >>> 12).setWidth 3 = BitVec.ofNat 3 (w.toNat/4096%8) := by
  rw [slice_nat]
  apply BitVec.eq_of_toNat_eq
  simp

theorem bits_decode (w : Word) : codeBits w = decodeCode w := by
  have hf : w.toNat/4096%8=0 ∨ w.toNat/4096%8=1 ∨ w.toNat/4096%8=2 ∨
      w.toNat/4096%8=3 ∨ w.toNat/4096%8=4 ∨ w.toNat/4096%8=5 ∨
      w.toNat/4096%8=6 ∨ w.toNat/4096%8=7 := by omega
  have opc (n : Nat) (hn : n < 128) :
      w.setWidth 7 = BitVec.ofNat 7 n ↔ w.toNat%128 = n := by
    constructor
    · intro h
      have h' := congrArg BitVec.toNat h
      simpa [BitVec.toNat_setWidth,Nat.mod_eq_of_lt hn] using h'
    · intro h; rw [low_nat,h]
  have h3 := opc 3 (by decide)
  have h35 := opc 35 (by decide)
  have h15 := opc 15 (by decide)
  rcases hf with hf | hf | hf | hf | hf | hf | hf | hf
  all_goals by_cases hl : w.toNat%128 = 3
  all_goals by_cases hs : w.toNat%128 = 35
  all_goals by_cases hfc : w.toNat%128 = 15 ∧ w.toNat/4096%8 = 0 ∧
      BitVec.ofNat 5 (w.toNat/128) = (0#5) ∧ BitVec.ofNat 5 (w.toNat/32768) = (0#5)
  all_goals
    have hp3 : (w.setWidth 7 = (3#7)) = (w.toNat%128 = 3) := propext h3
    have hp35 : (w.setWidth 7 = (35#7)) = (w.toNat%128 = 35) := propext h35
    have hp15 : (w.setWidth 7 = (15#7)) = (w.toNat%128 = 15) := propext h15
    simp only [codeBits,funct_nat,slice_nat w 7 5,slice_nat w 15 5,BitVec.ofNat_eq_ofNat,
      hp3,hp35,hp15,decodeCode,decode,hf] at *
    simp_all [loadCode,storeCode,opCode,fromBase,CaseCPU.Bridge.bits_code,
      CaseCPU.Bridge.decodeCode,Option.map_map,Function.comp_def]
  all_goals cases hc : CaseCPU.decode w <;> simp_all [hc,fromBase,opCode]
  all_goals split <;> simp_all [fromBase,opCode]

theorem opCode_ne_invalid (op : Op) : opCode op ≠ (63#6) := by
  cases op with
  | alu a => cases a <;> decide +kernel
  | _ => decide +kernel

theorem decode_some (w : Word) (h : (decode w).isSome = true) : decode w = some (Raw.instr w) := by
  cases hd : decode w <;> simp_all [Raw.instr]

theorem instruction_code (w : Word) (h : (decode w).isSome = true) :
    codeBits w = opCode (Raw.instr w).op := by
  rw [bits_decode,decodeCode,decode_some w h]
  rfl

theorem code_legal (w : Word) : (codeBits w != (63#6)) = (decode w).isSome := by
  rw [bits_decode]
  cases hd : decode w
  · simp [decodeCode,hd]
  · rename_i i
    simp [decodeCode,hd,opCode_ne_invalid]

def codeLoad (c : BitVec 6) : Bool := c == 29 || c == 30 || c == 31 || c == 32 || c == 33

def codeStore (c : BitVec 6) : Bool := c == 34 || c == 35 || c == 36

def codeBarrier (c : BitVec 6) : Bool := codeLoad c || codeStore c || c == 37

theorem code_load (op : Op) : codeLoad (opCode op) = isLoad op := by
  cases op with
  | alu a => cases a <;> rfl
  | _ => rfl

theorem code_store (op : Op) : codeStore (opCode op) = isStore op := by
  cases op with
  | alu a => cases a <;> rfl
  | _ => rfl

theorem code_barrier (op : Op) : codeBarrier (opCode op) = barrier op := by
  cases op with
  | alu a => cases a <;> rfl
  | _ => rfl

#print axioms bits_decode
#print axioms code_legal
end CaseCPUMem.Source
