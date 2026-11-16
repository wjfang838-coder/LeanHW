import LeanSpec
namespace MemoryDiagnosis
open LeanSpec
inductive Ctx where
  | endian | signedHalf | partialStore | resetRam | faultPriority | sampledDelay | haltedYounger | blockedForever
  deriving DecidableEq,Repr
structure Cfg where
  bigEndian : Bool := false
  signHalf : Option Bool := none
  preserveLanes : Option Bool := none
  resetConflict : Bool := true
  alignmentFirst : Option Bool := none
  resampleDelay : Bool := false
  requireYounger : Bool := true
  deadline : Bool := true
  deriving Inhabited

def contexts : List Ctx := [.endian,.signedHalf,.partialStore,.resetRam,.faultPriority,.sampledDelay,.haltedYounger,.blockedForever]
def observations : List (BitVec 32) := [0,1,2,4,0x11,0x44,0x8000,0xffff8000,0xaabbcc11]
def admits (cfg : Cfg) (c : Ctx) (o : BitVec 32) : Bool :=
  match c with
  | .endian => o == (if cfg.bigEndian then 0x11 else 0x44)
  | .signedHalf => cfg.signHalf.isNone || o == (if cfg.signHalf == some true then 0xffff8000 else 0x8000)
  | .partialStore => cfg.preserveLanes.isNone || o == (if cfg.preserveLanes == some true then 0xaabbcc11 else 0x11)
  | .resetRam => o == 0x11 && (!cfg.resetConflict || o == 0)
  | .faultPriority => cfg.alignmentFirst.isNone || o == (if cfg.alignmentFirst == some true then 2 else 4)
  | .sampledDelay => o == (if cfg.resampleDelay then 4 else 1)
  | .haltedYounger => o == 0 && (!cfg.requireYounger || o == 1)
  | .blockedForever => o == 0 && (!cfg.deadline || o == 1)
def draft : Cfg := {}
def consistent : Cfg := {resetConflict := false,requireYounger := false,deadline := false}
def revised : Cfg := {consistent with signHalf := some true,preserveLanes := some true,alignmentFirst := some true}

theorem endian_ambiguity : queryDifference (admits consistent)
    (admits {consistent with bigEndian := true}) observations contexts (fun _ => true) = some .endian := by decide +kernel
theorem delay_ambiguity : queryDifference (admits consistent)
    (admits {consistent with resampleDelay := true}) observations contexts (fun _ => true) = some .sampledDelay := by decide +kernel
theorem signed_half_hole : 1 < (admitSet (admits draft) observations .signedHalf).length := by decide +kernel
theorem partial_store_hole : 1 < (admitSet (admits draft) observations .partialStore).length := by decide +kernel
theorem fault_priority_hole : 1 < (admitSet (admits draft) observations .faultPriority).length := by decide +kernel
theorem reset_contradiction : admitSet (admits draft) observations .resetRam = [] := by decide +kernel
theorem younger_contradiction : admitSet (admits draft) observations .haltedYounger = [] := by decide +kernel
theorem progress_contradiction : admitSet (admits draft) observations .blockedForever = [] := by decide +kernel
theorem revised_determined : determinedEverywhere (admits revised) observations contexts (fun _ => true) = true := by decide +kernel

-- The finite clause projection is not enumeration of all CPU executions.
#eval contexts.map (fun c => (repr c, (admitSet (admits revised) observations c).map BitVec.toNat))
#print axioms revised_determined
end MemoryDiagnosis
