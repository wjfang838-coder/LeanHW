import LeanRTL.Core.MemSemantics
open LeanRTL
namespace LeanRTL.MemBlock

/-- Equal read addresses in equal physical memories have identical undefined
    events, regardless of stored data. -/
theorem undefined_event_agrees (m : LeanRTL.MemBlock)
    (left right : Spec.Mem m.addrWidth m.dataWidth)
    (a b : Expr m.addrWidth) (e f : Env) (ha : eval a e = eval b f) :
    (readBounded m left a e = none) ↔ (readBounded m right b f = none) := by
  simp only [readBounded, ha]
  split <;> simp

/-- Defined words agree under the memory-state relation; out-of-bounds reads
    both return None. No value is assigned to an undefined read. -/
theorem bounded_read_congr (m : LeanRTL.MemBlock)
    (left right : Spec.Mem m.addrWidth m.dataWidth)
    (a b : Expr m.addrWidth) (e f : Env) (ha : eval a e = eval b f)
    (hm : ∀ address, address.toNat < m.size → left.read address = right.read address) :
    readBounded m left a e = readBounded m right b f := by
  simp only [readBounded, readVal, ha]
  split
  · rename_i h
    rw [hm _ h]
  · rfl

/-- Any shared choice for a corresponding undefined read preserves equality.
    The unknown value is universally quantified, never fixed to a constant. -/
theorem corresponding_unknown_read (m : LeanRTL.MemBlock)
    (left right : Spec.Mem m.addrWidth m.dataWidth)
    (a b : Expr m.addrWidth) (e f : Env) (ha : eval a e = eval b f)
    (hm : ∀ address, address.toNat < m.size → left.read address = right.read address)
    (unknown : BitVec m.dataWidth) :
    (readBounded m left a e).getD unknown = (readBounded m right b f).getD unknown := by
  rw [bounded_read_congr m left right a b e f ha hm]

/-- A single corresponding write preserves equality of every physical word.
    The clock event is supplied by the caller; no clock schedule is assumed. -/
theorem bounded_write_congr (m : LeanRTL.MemBlock)
    (left right : Spec.Mem m.addrWidth m.dataWidth)
    (a b : MemWrite m.addrWidth m.dataWidth) (e f : Env)
    (hen : eval a.en e = eval b.en f)
    (ha : eval b.en f = 1 → eval a.addr e = eval b.addr f)
    (hd : eval b.en f = 1 → eval a.data e = eval b.data f)
    (hm : ∀ address, address.toNat < m.size → left.read address = right.read address)
    (address : BitVec m.addrWidth) (valid : address.toNat < m.size) :
    (writeBounded m a left e).read address = (writeBounded m b right f).read address := by
  by_cases enabled : eval b.en f = 1
  · simp only [writeBounded, writeStep, ha enabled, hd enabled, hen, enabled, if_true]
    split
    · by_cases same : address = eval b.addr f
      · subst address; simp
      · rw [Spec.Mem.read_write_ne _ _ _ _ same, Spec.Mem.read_write_ne _ _ _ _ same]
        exact hm address valid
    · exact hm address valid
  · simpa only [writeBounded, writeStep, hen, if_neg enabled, ite_self] using hm address valid

#print axioms undefined_event_agrees
#print axioms bounded_read_congr
#print axioms corresponding_unknown_read
#print axioms bounded_write_congr

/-- A corresponding ordered sequence of writes preserves the physical-word
    relation. A separate no-collision proof justifies using any port order. -/
theorem bounded_writes_congr (m : LeanRTL.MemBlock)
    (writes : List (MemWrite m.addrWidth m.dataWidth × MemWrite m.addrWidth m.dataWidth))
    (e f : Env)
    (left right : Spec.Mem m.addrWidth m.dataWidth)
    (hc : ∀ p ∈ writes, eval p.1.en e = eval p.2.en f ∧
      (eval p.2.en f = 1 → eval p.1.addr e = eval p.2.addr f ∧ eval p.1.data e = eval p.2.data f))
    (hm : ∀ address, address.toNat < m.size → left.read address = right.read address) :
    ∀ address, address.toNat < m.size →
      (writes.foldl (fun state p => writeBounded m p.1 state e) left).read address =
      (writes.foldl (fun state p => writeBounded m p.2 state f) right).read address := by
  induction writes generalizing left right with
  | nil => exact hm
  | cons p ps ih =>
    have hp := hc p (by simp)
    simp only [List.foldl_cons]
    apply ih
    · intro q hq
      exact hc q (by simp [hq])
    · intro address valid
      exact bounded_write_congr m left right p.1 p.2 e f hp.1
        (fun h => (hp.2 h).1) (fun h => (hp.2 h).2) hm address valid

#print axioms bounded_writes_congr

/-- Two writes whose enabled addresses never collide commute, including
    disabled and out-of-bounds writes. This is the per-port reason a checked
    collision-free group does not acquire behavior from its textual order. -/
theorem bounded_writes_commute (m : LeanRTL.MemBlock)
    (a b : MemWrite m.addrWidth m.dataWidth)
    (mem : Spec.Mem m.addrWidth m.dataWidth) (e : Env)
    (disjoint : eval a.en e = 1 → eval b.en e = 1 → eval a.addr e ≠ eval b.addr e) :
    writeBounded m a (writeBounded m b mem e) e =
      writeBounded m b (writeBounded m a mem e) e := by
  by_cases va : (eval a.addr e).toNat < m.size <;>
    by_cases vb : (eval b.addr e).toNat < m.size <;>
    by_cases ea : eval a.en e = 1 <;>
    by_cases eb : eval b.en e = 1 <;>
    simp only [writeBounded, writeStep, va, vb, ea, eb, if_true, if_false]
  funext address
  simp only [Spec.Mem.write]
  by_cases ha : address = eval a.addr e
  · simp [ha, disjoint ea eb]
  · simp only [ha, if_false]

#print axioms bounded_writes_commute
end LeanRTL.MemBlock
