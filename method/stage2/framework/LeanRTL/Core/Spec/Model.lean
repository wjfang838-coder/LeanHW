/-!
# Spec-layer abstract models (v0.7 M23) — the impl-agnostic wall

Abstract, untimed models for the functional spec layer (layer A).  This file is the
**structural wall** of the two-layer architecture: it imports **nothing** from the impl
side — no `Expr`, no `Module`, no `Env` — so a spec written in these terms *cannot*
mention gates or registers.  (`grep -L 'import' LeanRTL/Spec/Model.lean` is the
machine-checkable impl-agnostic test.)

Each model ships with its proven laws, so per-design refinement proofs reuse them instead
of re-deriving list/function facts.  The refinement bridge (α + `Refines`) that connects
these models to a cycle-accurate `Module` lives in `LeanRTL/Refine.lean` — the one place
allowed to import both layers.
-/

namespace LeanRTL.Spec

/-! ## Queue — the abstract model behind any FIFO -/

abbrev Queue (w : Nat) := List (BitVec w)

namespace Queue
variable {w : Nat}

def enq (q : Queue w) (x : BitVec w) : Queue w := q ++ [x]
def deq (q : Queue w) : Queue w := q.tail
def front (q : Queue w) : Option (BitVec w) := q.head?
def len (q : Queue w) : Nat := q.length

/-- One boundary step of a capacity-`N` FIFO: write `din` (if `wr` and not full), then read (if `rd`
    and not empty).  This is the CLEAN abstract semantics the impl must match. -/
def step (N : Nat) (q : Queue w) (wr rd : Bool) (din : BitVec w) : Queue w :=
  let q1 := if wr && decide (q.length < N) then q.enq din else q
  if rd && !q1.isEmpty then q1.deq else q1

@[simp] theorem len_enq (q : Queue w) (x : BitVec w) : (q.enq x).len = q.len + 1 := by
  simp [enq, len]

@[simp] theorem len_deq (q : Queue w) : (q.deq).len = q.len - 1 := by
  simp [deq, len]

@[simp] theorem front_enq_nil (x : BitVec w) : (Queue.enq [] x).front = some x := rfl

/-- Enqueue never loses the existing front. -/
theorem front_enq (q : Queue w) (x : BitVec w) (h : q ≠ []) : (q.enq x).front = q.front := by
  cases q with
  | nil => exact absurd rfl h
  | cons a as => rfl

/-- A `step` never grows the queue beyond the capacity bound it maintains. -/
theorem step_len_le (N : Nat) (q : Queue w) (wr rd : Bool) (din : BitVec w)
    (h : q.len ≤ N) : (Queue.step N q wr rd din).len ≤ N := by
  have htail : ∀ (l : List (BitVec w)), l.length ≤ N → l.tail.length ≤ N := by
    intro l hl
    have ht : l.tail.length = l.length - 1 := List.length_tail
    omega
  unfold step
  by_cases hA : (wr && decide (q.length < N)) = true
  · have hlt : q.length < N := by
      have h' : wr = true ∧ q.length < N := by simpa using hA
      exact h'.2
    have h1 : (q.enq din).length ≤ N := by
      simp only [enq, List.length_append, List.length_cons, List.length_nil]
      omega
    rw [if_pos hA]
    show (if (rd && !(q.enq din).isEmpty) = true then (q.enq din).deq else q.enq din).len ≤ N
    split
    · exact htail _ h1
    · exact h1
  · rw [if_neg hA]
    show (if (rd && !q.isEmpty) = true then q.deq else q).len ≤ N
    split
    · exact htail _ h
    · exact h

end Queue

/-! ## Mem — the abstract model behind any register file / RAM -/

abbrev Mem (a w : Nat) := BitVec a → BitVec w

namespace Mem
variable {a w : Nat}

def write (m : Mem a w) (addr : BitVec a) (v : BitVec w) : Mem a w :=
  fun x => if x = addr then v else m x

def read (m : Mem a w) (addr : BitVec a) : BitVec w := m addr

def const (v : BitVec w) : Mem a w := fun _ => v

@[simp] theorem read_write_eq (m : Mem a w) (addr : BitVec a) (v : BitVec w) :
    (m.write addr v).read addr = v := by simp [write, read]

theorem read_write_ne (m : Mem a w) (addr x : BitVec a) (v : BitVec w) (h : x ≠ addr) :
    (m.write addr v).read x = m.read x := by simp [write, read, h]

@[simp] theorem read_const (v : BitVec w) (addr : BitVec a) :
    (const (a := a) v).read addr = v := rfl

/-- Writing the value already stored is the identity (useful for idempotence arguments). -/
theorem write_read_self (m : Mem a w) (addr : BitVec a) :
    m.write addr (m.read addr) = m := by
  funext x; by_cases h : x = addr <;> simp [write, read, h]

end Mem

end LeanRTL.Spec
