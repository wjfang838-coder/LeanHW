import LeanRTL.Core.Refine
/-!
# `Lib/Semantic/BitVecArith` — width-generic `BitVec`/`Nat` bridge facts

Two small, entirely generic `BitVec`↔`Nat` bridges that several semantic combinators and design
proofs share.  They used to live inside `DecodeMod` (the mod-`N` counter combinator), but they are
in no way counter-specific — `ofNat_succ` is a bare `ofNat` successor law and `bv_ne_of_ne` a bare
in-range disequality transport — so they belong in a neutral arithmetic home rather than in one
particular combinator module.  `DecodeMod` re-exports them (see its header), so existing
`DecodeMod.ofNat_succ` / `DecodeMod.bv_ne_of_ne` qualified references keep resolving.
-/

namespace LeanRTL.Lib.Semantic.BitVecArith

/-- Decode disequality from a Nat disequality (generic width, both decodes in range). -/
theorem bv_ne_of_ne {w m n : Nat} (hm : m < 2 ^ w) (hn : n < 2 ^ w) (h : m ≠ n) :
    BitVec.ofNat w m ≠ BitVec.ofNat w n := by
  intro heq
  apply h
  have h' := congrArg BitVec.toNat heq
  rwa [BitVec.toNat_ofNat, BitVec.toNat_ofNat, Nat.mod_eq_of_lt hm, Nat.mod_eq_of_lt hn] at h'

/-- `ofNat`-`w` successor absorbs into the Nat argument: `ofNat w m + 1 = ofNat w (m+1)`.
    Width-generic replacement for the per-width `bv4_succ`/`bv2_succ`/… (`bv_omega`) lemmas. -/
theorem ofNat_succ {w : Nat} (m : Nat) : BitVec.ofNat w m + 1 = BitVec.ofNat w (m + 1) := by
  rw [BitVec.ofNat_add]; rfl

end LeanRTL.Lib.Semantic.BitVecArith
