import LeanRTL.Core.Semantics
import LeanRTL.Core.Spec.Model
/-!
# Addressed-memory semantics — the per-access characterization behind a `MemBlock`

A `MemBlock` (SRAM/RAM array) is deliberately **not** modelled by the whole-design
`Module.simulate` (a register-file Moore model with no array), exactly as F8 latches / F6 async
loads / F11 multi-clock registers are not.  Its behaviour is instead pinned at the *per-access*
level here and validated end-to-end by co-simulation of the emitted `$mem_v2` cell.

The memory's contents are the impl-agnostic function `Spec.Model.Mem aw dw = BitVec aw → BitVec dw`
(with its proven `read_write_eq` / `read_write_ne` laws).  This file lifts those laws to a
`MemBlock`'s `Expr`-valued ports, giving the two facts a design file needs:

* `read_after_write`     — reading the just-written address returns the written data (RAW);
* `read_after_write_ne`  — a write to A leaves any read of B ≠ A unchanged.

Together they are the addressed-access characterization ("reading address A returns the last value
written to A"), stated as a function of the environment the ports are evaluated against.
-/
namespace LeanRTL.MemBlock
open LeanRTL LeanRTL.Spec

/-- Initial contents. Unknown initialization retains an arbitrary caller-supplied
    memory; a complete image fixes every physical word. Values outside the physical
    array remain arbitrary and are never exposed as defined reads by readBounded. The module checker rejects
    incomplete images before extraction. -/
def initialContents (m : LeanRTL.MemBlock) (arbitrary : Mem m.addrWidth m.dataWidth) :
    Mem m.addrWidth m.dataWidth :=
  match m.init with
  | none => arbitrary
  | some words => fun address =>
      if address.toNat < m.size then (words[address.toNat]?).getD 0 else arbitrary address

theorem initial_unconstrained (m : LeanRTL.MemBlock) (arbitrary : Mem m.addrWidth m.dataWidth)
    (h : m.init = none) : initialContents m arbitrary = arbitrary := by
  simp [initialContents, h]

theorem initial_read (m : LeanRTL.MemBlock) (arbitrary : Mem m.addrWidth m.dataWidth)
    (words : List (BitVec m.dataWidth)) (h : m.init = some words) (address : BitVec m.addrWidth)
    (inBounds : address.toNat < m.size) :
    (initialContents m arbitrary).read address = (words[address.toNat]?).getD 0 := by
  simp [initialContents, h, Mem.read, inBounds]

/-- Full-address-space memory contents after one write port fires under cycle environment `e`: the word `data` is
    stored at `addr` when `en` is high, otherwise the contents are unchanged.  For a full-depth memory this is exactly the
    next-state of the emitted `$mem_v2` on a `clock` edge (the edge itself is a co-simulation fact,
    outside this untimed content model — like `Latch.den` / `Reg.aldffDen`).
    For a partial-depth block use writeBounded, which guards the physical address. -/
def writeStep {aw dw : Nat} (wr : MemWrite aw dw) (mem : Mem aw dw) (e : Env) : Mem aw dw :=
  if eval wr.en e = 1 then mem.write (eval wr.addr e) (eval wr.data e) else mem

/-- The value an asynchronous read port produces over contents `mem`: `mem[eval addr]`. -/
def readVal {aw dw : Nat} (mem : Mem aw dw) (addr : Expr aw) (e : Env) : BitVec dw :=
  mem.read (eval addr e)

/-- **Read-after-write (same address).**  When the write port is enabled, reading its address
    immediately afterwards returns exactly the written data — the addressed-access guarantee. -/
theorem read_after_write {aw dw : Nat} (wr : MemWrite aw dw) (mem : Mem aw dw) (e : Env)
    (hen : eval wr.en e = 1) :
    readVal (writeStep wr mem e) wr.addr e = eval wr.data e := by
  rw [readVal, writeStep, if_pos hen]; exact Mem.read_write_eq _ _ _

/-- **Read-after-write (different address).**  A write to `wr.addr` leaves any read of a different
    address `raddr ≠ wr.addr` unchanged — writes are addressed, not global. -/
theorem read_after_write_ne {aw dw : Nat} (wr : MemWrite aw dw) (mem : Mem aw dw) (e : Env)
    (raddr : Expr aw) (hne : eval raddr e ≠ eval wr.addr e) :
    readVal (writeStep wr mem e) raddr e = readVal mem raddr e := by
  rw [readVal, writeStep, readVal]
  split
  · exact Mem.read_write_ne mem (eval wr.addr e) (eval raddr e) (eval wr.data e) hne
  · rfl

/-- **Disabled write is a no-op.**  With `en` low the contents are unchanged, so every read is
    unaffected. -/
theorem read_write_disabled {aw dw : Nat} (wr : MemWrite aw dw) (mem : Mem aw dw) (e : Env)
    (raddr : Expr aw) (hen : eval wr.en e ≠ 1) :
    readVal (writeStep wr mem e) raddr e = readVal mem raddr e := by
  rw [readVal, writeStep, readVal, if_neg hen]


/-- A partial-depth physical read. `none` denotes an undefined out-of-bounds
    result, rather than a zero bitvector or a truncated address. -/
def readBounded (m : LeanRTL.MemBlock) (mem : Mem m.addrWidth m.dataWidth)
    (addr : Expr m.addrWidth) (e : Env) : Option (BitVec m.dataWidth) :=
  if (eval addr e).toNat < m.size then some (readVal mem addr e) else none

/-- A write outside the physical array has no effect. -/
def writeBounded (m : LeanRTL.MemBlock) (wr : MemWrite m.addrWidth m.dataWidth)
    (mem : Mem m.addrWidth m.dataWidth) (e : Env) : Mem m.addrWidth m.dataWidth :=
  if (eval wr.addr e).toNat < m.size then writeStep wr mem e else mem

theorem read_bounded_invalid (m : LeanRTL.MemBlock) (mem : Mem m.addrWidth m.dataWidth)
    (addr : Expr m.addrWidth) (e : Env) (h : ¬ (eval addr e).toNat < m.size) :
    readBounded m mem addr e = none := by simp [readBounded, h]

theorem write_bounded_invalid (m : LeanRTL.MemBlock) (wr : MemWrite m.addrWidth m.dataWidth)
    (mem : Mem m.addrWidth m.dataWidth) (e : Env) (h : ¬ (eval wr.addr e).toNat < m.size) :
    writeBounded m wr mem e = mem := by simp [writeBounded, h]

theorem read_bounded_after_write (m : LeanRTL.MemBlock) (wr : MemWrite m.addrWidth m.dataWidth)
    (mem : Mem m.addrWidth m.dataWidth) (e : Env)
    (hen : eval wr.en e = 1) (haddr : (eval wr.addr e).toNat < m.size) :
    readBounded m (writeBounded m wr mem e) wr.addr e = some (eval wr.data e) := by
  simp only [readBounded, writeBounded, if_pos haddr, read_after_write wr mem e hen]

theorem read_bounded_after_write_ne (m : LeanRTL.MemBlock) (wr : MemWrite m.addrWidth m.dataWidth)
    (mem : Mem m.addrWidth m.dataWidth) (e : Env) (addr : Expr m.addrWidth)
    (hne : eval addr e ≠ eval wr.addr e) :
    readBounded m (writeBounded m wr mem e) addr e = readBounded m mem addr e := by
  simp only [readBounded, writeBounded]
  split
  · split
    · rw [read_after_write_ne wr mem e addr hne]
    · rfl
  · rfl

end LeanRTL.MemBlock
