import LeanRTL
namespace Strengthening.BitwiseBridge
theorem xor_mask32 (x : Nat) (hx : x < 4294967296) :
 x ^^^ 4294967295 = 4294967295 - x := by
 have h := congrArg BitVec.toNat (BitVec.xor_allOnes (x := BitVec.ofNat 32 x))
 simpa [BitVec.toNat_xor,BitVec.toNat_allOnes,BitVec.toNat_ofNat,
   BitVec.toNat_not,Nat.mod_eq_of_lt hx] using h
#print axioms xor_mask32
end Strengthening.BitwiseBridge
