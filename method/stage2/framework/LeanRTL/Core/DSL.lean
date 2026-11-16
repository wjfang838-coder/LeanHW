import LeanRTL.Core.Syntax
import LeanRTL.Core.Semantics
/-!
# LeanRTL DSL sugar (M10) — arrays, register files, control flow

Agent-facing convenience layer.  Everything here is a **smart constructor that expands to the
existing core** (`Expr.mux`/`Reg`/`Wire`), so it inherits `compile_correct` for free — nothing new
enters the proven compiler core (core invariant: lower to the proven core or provide a separate proof).

* `ifE` / `caseE`      — control flow → nested `mux`.
* `arraySelect`        — combinational array read (address mux).
* `regFile`            — a register-file array (1 sync write port + N combinational read ports)
                         → ordinary `Reg`s + read-`Wire`s.
-/

namespace LeanRTL

/-- `if`-then-else on a 1-bit condition (alias for `mux`). -/
@[inline] def ifE {w : Nat} (c : Expr 1) (t e : Expr w) : Expr w := .mux c t e

/-- Priority case: the first matching condition wins, else `dflt`.  Right-nested `mux` chain. -/
def caseE {w : Nat} (branches : List (Expr 1 × Expr w)) (dflt : Expr w) : Expr w :=
  branches.foldr (fun be acc => .mux be.1 be.2 acc) dflt

/-- Combinational array read: select `elems[idx]` by an `awidth`-bit index, `dflt` if no entry
    matches.  A nested address `mux` over the (statically known) element list. -/
def arraySelect {w awidth : Nat} (idx : Expr awidth) (elems : List (Expr w)) (dflt : Expr w) :
    Expr w :=
  ((List.range elems.length).zip elems).foldr
    (fun ie acc => .mux (.eq idx (.const (BitVec.ofNat awidth ie.1))) ie.2 acc) dflt

/-- A register file: `depth` registers `<name>[i]` of `width` bits, with one synchronous write
    port (write `wdata` into entry `waddr` when `we`) and a set of combinational read ports
    (`readPorts` = list of `(readWireName, readAddr)`).  Expands to ordinary `Reg`s + read-`Wire`s
    — covered by `compile_correct` for free (registers + muxes, nothing new in the proven core).

    Returns `(regs, readWires)` to splice into a `Module`'s `regs`/`wires`. -/
def regFile (name : String) (depth width awidth : Nat)
    (we : Expr 1) (waddr : Expr awidth) (wdata : Expr width)
    (readPorts : List (String × Expr awidth))
    -- with depth > 2^awidth, entries i and i+2^awidth would alias the same address and BOTH
    -- be written every cycle (silently); the auto-param rejects that shape at elaboration
    (_h : depth ≤ 2 ^ awidth := by decide) : List Reg × List Wire :=
  let entryName := fun i => s!"{name}[{i}]"
  let regs := (List.range depth).map (fun i =>
    let self : Expr width := .var (entryName i) width
    let hit  : Expr 1 := .and we (.eq waddr (.const (BitVec.ofNat awidth i)))
    ({ name := entryName i, width := width, next := .mux hit wdata self,
       init := (0 : BitVec width) } : Reg))
  let elems : List (Expr width) := (List.range depth).map (fun i => .var (entryName i) width)
  let wires := readPorts.map (fun rp =>
    ({ name := rp.1, width := width, expr := arraySelect rp.2 elems (.const 0) } : Wire))
  (regs, wires)

/-! ## M16 — proven `eval` laws for the constructors (the "construct → strong proof" payoff)

A design using these gets its per-step / combinational characterization **mechanically**: the
circuit-level mux/case reasoning is discharged here, once, generically.  These are how the DSL
self-evolves *without* proof debt — each new constructor desugars to the proven core and ships its
own `eval` law. -/

/-- The value-level reading of a right-nested `mux` fold (the shape behind `caseE`/`arraySelect`). -/
theorem muxFold_eval {α : Type} {w : Nat} (xs : List α) (cond : α → Expr 1) (val : α → Expr w)
    (dflt : Expr w) (env : Env) :
    eval (xs.foldr (fun x acc => .mux (cond x) (val x) acc) dflt) env =
      xs.foldr (fun x acc => if eval (cond x) env = 1 then eval (val x) env else acc)
        (eval dflt env) := by
  induction xs with
  | nil => rfl
  | cons x xs ih => simp only [List.foldr, eval, ih]

/-- `ifE` is `mux`. -/
@[simp] theorem ifE_eval {w : Nat} (c : Expr 1) (t e : Expr w) (env : Env) :
    eval (ifE c t e) env = if eval c env = 1 then eval t env else eval e env := rfl

/-- `caseE` evaluates to the first matching branch (the priority-case law). -/
theorem caseE_eval {w : Nat} (branches : List (Expr 1 × Expr w)) (dflt : Expr w) (env : Env) :
    eval (caseE branches dflt) env =
      branches.foldr (fun be acc => if eval be.1 env = 1 then eval be.2 env else acc)
        (eval dflt env) :=
  muxFold_eval branches (·.1) (·.2) dflt env

/-- An evolved constructor (M16): a Moore-FSM state-register next-state from a transition table —
    in state `sᵢ` go to `eᵢ` (an `Expr` over inputs/state), else hold.  Desugars to `caseE`, so it
    inherits `compile_correct` AND the `caseE_eval` law for free. -/
def fsmNext {sw : Nat} (stateVar : String) (table : List (BitVec sw × Expr sw)) : Expr sw :=
  caseE (table.map (fun se => ((Expr.eq (.var stateVar sw) (.const se.1)), se.2))) (.var stateVar sw)

/-- The FSM's next-state is exactly the table's priority case over the current state — proven once,
    generically, so a design built with `fsmNext` gets its per-step characterization mechanically. -/
theorem fsmNext_eval {sw : Nat} (stateVar : String) (table : List (BitVec sw × Expr sw)) (env : Env) :
    eval (fsmNext stateVar table) env =
      (table.map (fun se => ((Expr.eq (.var stateVar sw) (.const se.1)), se.2))).foldr
        (fun be acc => if eval be.1 env = 1 then eval be.2 env else acc)
        (eval (.var stateVar sw) env) :=
  caseE_eval _ _ env

/-! ### Round-2 evolution — laws/constructors surfaced by the crypto/ROM/CPU friction reports. -/

/-- `arraySelect` (ROM / LUT lookup) evaluates to the entry whose index matches — the missing
    eval-law that crypto/table designs (K-ROM, S-box) kept hand-rolling. -/
theorem arraySelect_eval {w awidth : Nat} (idx : Expr awidth) (elems : List (Expr w))
    (dflt : Expr w) (env : Env) :
    eval (arraySelect idx elems dflt) env =
      ((List.range elems.length).zip elems).foldr
        (fun ie acc => if eval idx env = BitVec.ofNat awidth ie.1 then eval ie.2 env else acc)
        (eval dflt env) := by
  unfold arraySelect
  rw [muxFold_eval]
  congr 1
  funext ie acc
  show (if eval (Expr.eq idx (.const (BitVec.ofNat awidth ie.1))) env = 1 then _ else _) = _
  simp only [eval]
  by_cases h : eval idx env = BitVec.ofNat awidth ie.1 <;> simp [h]

/-- Width of the shift-count constant used by the rotate constructors: enough bits to hold
    any count up to `w` itself.  (The old fixed width 8 silently truncated `w - n` mod 256
    for `w > 256` — e.g. a SHA-512-class 512-bit rotate-by-1 would shift by 255.) -/
def rotCountWidth (w : Nat) : Nat := w.log2 + 1

/-- Rotate-right by a constant `n ≤ w` within width `w`: `(e >> n) ||| (e << (w-n))`.  Desugars to
    the proven core (`or`/`shr`/`shl`), so `compile_correct` covers it; SHA/AES rotate constantly. -/
def rotateRightE {w : Nat} (e : Expr w) (n : Nat) : Expr w :=
  .or (.shr e (.const (BitVec.ofNat (rotCountWidth w) n)))
      (.shl e (.const (BitVec.ofNat (rotCountWidth w) (w - n))))

/-- Rotate-left by a constant `n ≤ w` within width `w`. -/
def rotateLeftE {w : Nat} (e : Expr w) (n : Nat) : Expr w :=
  .or (.shl e (.const (BitVec.ofNat (rotCountWidth w) n)))
      (.shr e (.const (BitVec.ofNat (rotCountWidth w) (w - n))))

/-- `rotateRightE`'s packaged `eval`-law (matches eval's `ushiftRight`/`shiftLeft`, so it closes by `rfl`). -/
theorem rotrE_eval {w : Nat} (e : Expr w) (n : Nat) (env : Env) :
    eval (rotateRightE e n) env =
      BitVec.ushiftRight (eval e env) (BitVec.ofNat (rotCountWidth w) n).toNat |||
        BitVec.shiftLeft (eval e env) (BitVec.ofNat (rotCountWidth w) (w - n)).toNat := rfl

/-- `rotateLeftE`'s packaged `eval`-law. -/
theorem rotlE_eval {w : Nat} (e : Expr w) (n : Nat) (env : Env) :
    eval (rotateLeftE e n) env =
      BitVec.shiftLeft (eval e env) (BitVec.ofNat (rotCountWidth w) n).toNat |||
        BitVec.ushiftRight (eval e env) (BitVec.ofNat (rotCountWidth w) (w - n)).toNat := rfl

/-- The rotate count constants are exact (no truncation) for all `n ≤ w`: the count width
    always accommodates `w` itself. -/
theorem rotCount_exact (w n : Nat) (h : n ≤ w) :
    (BitVec.ofNat (rotCountWidth w) n).toNat = n := by
  have hw : w < 2 ^ rotCountWidth w := Nat.lt_log2_self
  rw [BitVec.toNat_ofNat]
  exact Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt h hw)

end LeanRTL
