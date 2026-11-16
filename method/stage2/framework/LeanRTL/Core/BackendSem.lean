import LeanRTL.Core.Compiler
import LeanRTL.Core.Semantics
/-!
# Denotational semantics of the emitted RTLIL (for compiler-correctness, M6)

A net valuation `σ : Nat → Bool` assigns a logic level to every net id.  `busDen σ w b`
reads a `Bus` (LSB-first) as a `BitVec w` (width-explicit via `BitVec.ofNat`, so there are
no dependent-width casts).  `cellHolds σ c` says σ satisfies one emitted cell's BitVec
relation.  These let us state and prove `⟦e⟧ = ⟦compileExpr e⟧` (see `CompilerCorrect.lean`).
-/
namespace LeanRTL.BackendSem
open LeanRTL LeanRTL.Backend

/-- Value of a single physical bit under a net valuation. -/
def bitDen (σ : Nat → Bool) : Bit → Bool
  | .net n => σ n
  | .one   => true
  | _      => false      -- zero/x/z ↦ false; combinational `compileExpr` never emits x/z

/-- Interpret a LSB-first list of bits as a natural number. -/
def bitsToNat : List Bool → Nat
  | []      => 0
  | b :: bs => (if b then 1 else 0) + 2 * bitsToNat bs

/-- Natural-number value of a bus under σ. -/
def busValNat (σ : Nat → Bool) (b : Bus) : Nat := bitsToNat (b.map (bitDen σ))

/-- Width-explicit bit-vector value of a bus (truncates/zero-extends to `w`). -/
def busDen (σ : Nat → Bool) (w : Nat) (b : Bus) : BitVec w := BitVec.ofNat w (busValNat σ b)

/-- A named port's bus on a cell (empty if absent). -/
def conn (c : Cell) (k : String) : Bus := (c.connections.lookup k).getD []

/-- Whether a cell parameter is the 32-bit-binary encoding of 1 (used for signedness). -/
def cellSigned (c : Cell) (k : String) : Bool := c.parameters.lookup k == some (binStr32 1)

/-- σ satisfies one emitted cell: its output bus denotes the cell's BitVec function of its
    inputs.  Only the cell types `compileExpr` emits are constrained; anything else is `True`. -/
def cellHolds (σ : Nat → Bool) (c : Cell) : Prop :=
  let A := conn c "A"; let B := conn c "B"; let S := conn c "S"; let Y := conn c "Y"
  let wY := Y.length; let wA := A.length
  match c.type with
  | "$not" => busDen σ wY Y = ~~~ busDen σ wY A
  | "$and" => busDen σ wY Y = busDen σ wY A &&& busDen σ wY B
  | "$or"  => busDen σ wY Y = busDen σ wY A ||| busDen σ wY B
  | "$xor" => busDen σ wY Y = busDen σ wY A ^^^ busDen σ wY B
  | "$add" => busDen σ wY Y = busDen σ wY A + busDen σ wY B
  | "$sub" => busDen σ wY Y = busDen σ wY A - busDen σ wY B
  | "$mul" => busDen σ wY Y = busDen σ wY A * busDen σ wY B
  | "$div" => busDen σ wY Y = busDen σ wY A / busDen σ wY B
  | "$mod" => busDen σ wY Y = busDen σ wY A % busDen σ wY B
  | "$shl" => busDen σ wY Y = (busDen σ wY A).shiftLeft (busValNat σ B)
  | "$shr" => busDen σ wY Y = (busDen σ wY A).ushiftRight (busValNat σ B)
  | "$sshr"=> busDen σ wY Y = (busDen σ wY A).sshiftRight (busValNat σ B)
  | "$eq"  => busDen σ 1 Y = (if busDen σ wA A = busDen σ wA B then 1 else 0)
  | "$lt"  => if cellSigned c "A_SIGNED"
              then busDen σ 1 Y = (if (busDen σ wA A).toInt < (busDen σ wA B).toInt then 1 else 0)
              else busDen σ 1 Y = (if busDen σ wA A < busDen σ wA B then 1 else 0)
  | "$mux" => busDen σ wY Y = (if busDen σ 1 S = 1 then busDen σ wY B else busDen σ wY A)
  | _      => True

/-- σ satisfies every cell in a list. -/
def ConsistentCells (σ : Nat → Bool) (cs : List Cell) : Prop := ∀ c ∈ cs, cellHolds σ c

/-- σ reproduces the denotational environment on every bound signal bus. -/
def CEnvOK (σ : Nat → Bool) (cenv : List (String × Bus)) (env : Env) : Prop :=
  ∀ n bus, cenv.lookup n = some bus → busDen σ bus.length bus = env.lookup n bus.length

/-- Every `var` in `e` is bound in `cenv` at the right width. -/
def WidthOK (cenv : List (String × Bus)) : {w : Nat} → Expr w → Prop
  | _, .const _      => True
  | _, .var n w      => ∃ bus, cenv.lookup n = some bus ∧ bus.length = w
  | _, .not a        => WidthOK cenv a
  | _, .and a b      => WidthOK cenv a ∧ WidthOK cenv b
  | _, .or a b       => WidthOK cenv a ∧ WidthOK cenv b
  | _, .xor a b      => WidthOK cenv a ∧ WidthOK cenv b
  | _, .add a b      => WidthOK cenv a ∧ WidthOK cenv b
  | _, .sub a b      => WidthOK cenv a ∧ WidthOK cenv b
  | _, .mul a b      => WidthOK cenv a ∧ WidthOK cenv b
  | _, .eq a b       => WidthOK cenv a ∧ WidthOK cenv b
  | _, .ult a b      => WidthOK cenv a ∧ WidthOK cenv b
  | _, .slt a b      => WidthOK cenv a ∧ WidthOK cenv b
  | _, .mux s a b    => WidthOK cenv s ∧ WidthOK cenv a ∧ WidthOK cenv b
  | _, .concat a b   => WidthOK cenv a ∧ WidthOK cenv b
  | _, .zext _ a     => WidthOK cenv a
  | _, .sext _ a     => WidthOK cenv a
  | _, .extract _ a  => WidthOK cenv a
  | _, .slice _ _ a  => WidthOK cenv a
  | _, .shl a b      => WidthOK cenv a ∧ WidthOK cenv b
  | _, .shr a b      => WidthOK cenv a ∧ WidthOK cenv b
  | _, .sshr a b     => WidthOK cenv a ∧ WidthOK cenv b
  | _, .udiv a b     => WidthOK cenv a ∧ WidthOK cenv b
  | _, .umod a b     => WidthOK cenv a ∧ WidthOK cenv b

/-- All net ids in a bus are `< bound`. -/
def BusBelow (bound : Nat) (b : Bus) : Prop := ∀ k, Bit.net k ∈ b → k < bound

/-- Every bound signal's bus lies below `bound`. -/
def EnvBounded (cenv : List (String × Bus)) (bound : Nat) : Prop :=
  ∀ n bus, cenv.lookup n = some bus → BusBelow bound bus

/-- Every net in a cell's connections lies below `bound`. -/
def CellBelow (bound : Nat) (c : Cell) : Prop :=
  ∀ k b, (k, b) ∈ c.connections → BusBelow bound b

/-- Every cell in a list lies below `bound`. -/
def CellsBounded (cs : List Cell) (bound : Nat) : Prop := ∀ c ∈ cs, CellBelow bound c

/-- Extend σ so a freshly-allocated output bus `Y` carries `val`. -/
def setNets (σ : Nat → Bool) (Y : Bus) (val : BitVec Y.length) : Nat → Bool :=
  fun n => match Y.findIdx? (fun x => decide (x = Bit.net n)) with
           | some i => val.getLsbD i
           | none   => σ n

end LeanRTL.BackendSem
