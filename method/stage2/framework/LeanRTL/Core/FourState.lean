import LeanRTL.Core.Syntax

/-! Four-state word expressions. This is a separate semantic domain from `Expr`:
no theorem about the existing two-state cycle model is claimed for these values.
The evaluator retains X and Z; emission is checked against actual HDL separately.
No drive strengths, event scheduling or bidirectional-net fixed point is modeled yet. -/
namespace LeanRTL.FourState

inductive Bit where
  | zero | one | x | z
  deriving DecidableEq, BEq, Repr, Inhabited

def Bit.known : Bit → Bool
  | .zero | .one => true
  | _ => false
def Bit.inv : Bit → Bit
  | .zero => .one
  | .one => .zero
  | _ => .x
def Bit.band : Bit → Bit → Bit
  | .zero, _ | _, .zero => .zero
  | .one, .one => .one
  | _, _ => .x
def Bit.bor : Bit → Bit → Bit
  | .one, _ | _, .one => .one
  | .zero, .zero => .zero
  | _, _ => .x
def Bit.bxor (a b : Bit) : Bit :=
  if a.known && b.known then if a == b then .zero else .one else .x
def Bit.merge (a b : Bit) : Bit := if a == b then a else .x
/-- Equal-strength, ordinary wire resolution, including the undriven Z identity. -/
def Bit.resolve : Bit → Bit → Bit
  | .z, b => b
  | a, .z => a
  | .zero, .zero => .zero
  | .one, .one => .one
  | _, _ => .x
def Bit.char : Bit → Char
  | .zero => '0'
  | .one => '1'
  | .x => 'x'
  | .z => 'z'

structure Value (w : Nat) where
  bit : Fin w → Bit
instance {w : Nat} : CoeFun (Value w) (fun _ => Fin w → Bit) := ⟨Value.bit⟩
def fill {w : Nat} (b : Bit) : Value w := ⟨fun _ => b⟩
def ofBitVec {w : Nat} (v : BitVec w) : Value w :=
  ⟨fun i => if v.getLsbD i.val then .one else .zero⟩
def getBit {w : Nat} (a : Value w) (i : Nat) : Bit :=
  if h : i < w then a ⟨i, h⟩ else .x
def known {w : Nat} (a : Value w) : Bool := (List.finRange w).all (fun i => (a i).known)
def toBitVec {w : Nat} (a : Value w) : BitVec w :=
  (BitVec.ofBoolListLE ((List.finRange w).map (fun i => a i == .one))).setWidth w
def binary {w : Nat} (op : BitVec w → BitVec w → BitVec w) (a b : Value w) : Value w :=
  if known a && known b then ofBitVec (op (toBitVec a) (toBitVec b)) else fill .x
def unsignedDiv {w : Nat} (a b : Value w) : Value w :=
  binary (· / ·) a b
def logicalEq {w : Nat} (a b : Value w) : Bit :=
  if (List.finRange w).any (fun i => (a i).known && (b i).known && a i != b i) then .zero
  else if known a && known b then .one else .x
def relation {w : Nat} (op : BitVec w → BitVec w → Bool) (a b : Value w) : Bit :=
  if known a && known b then if op (toBitVec a) (toBitVec b) then .one else .zero else .x
def mux {w : Nat} (s : Bit) (a b : Value w) : Value w :=
  match s with
  | .one => a
  | .zero => b
  | _ => ⟨fun i => (a i).merge (b i)⟩
def renderValue {w : Nat} (a : Value w) : String :=
  String.ofList ((List.finRange w).reverse.map (fun i => (a i).char))

inductive Expr : Nat → Type where
  | const : {w : Nat} → BitVec w → Expr w
  | fill : {w : Nat} → Bit → Expr w
  | var : String → (w : Nat) → Expr w
  | not : {w : Nat} → Expr w → Expr w
  | and : {w : Nat} → Expr w → Expr w → Expr w
  | or : {w : Nat} → Expr w → Expr w → Expr w
  | xor : {w : Nat} → Expr w → Expr w → Expr w
  | add : {w : Nat} → Expr w → Expr w → Expr w
  | sub : {w : Nat} → Expr w → Expr w → Expr w
  | mul : {w : Nat} → Expr w → Expr w → Expr w
  | udiv : {w : Nat} → Expr w → Expr w → Expr w
  | shl : {w k : Nat} → Expr w → Expr k → Expr w
  | shr : {w k : Nat} → Expr w → Expr k → Expr w
  | sshr : {w k : Nat} → Expr w → Expr k → Expr w
  | eq : {w : Nat} → Expr w → Expr w → Expr 1
  | caseEq : {w : Nat} → Expr w → Expr w → Expr 1
  | ult : {w : Nat} → Expr w → Expr w → Expr 1
  | slt : {w : Nat} → Expr w → Expr w → Expr 1
  | mux : {w : Nat} → Expr 1 → Expr w → Expr w → Expr w
  /-- `$pmux`: only definite-one selectors are active; multiple active bits yield X. -/
  | pmux : {w n : Nat} → Expr w → Expr (w*n) → Expr n → Expr w
  | concat : {a b : Nat} → Expr a → Expr b → Expr (a+b)
  | zext : {w : Nat} → (k : Nat) → Expr w → Expr (w+k)
  | sext : {w : Nat} → (k : Nat) → Expr w → Expr (w+k)
  | extract : {w : Nat} → Nat → Expr w → Expr 1
  | slice : {w : Nat} → (lo len : Nat) → Expr w → Expr len

abbrev Env := String → Nat → Bit
def eval : {w : Nat} → Expr w → Env → Value w
  | _, .const v, _ => ofBitVec v
  | _, .fill b, _ => fill b
  | _, .var n _, e => ⟨fun i => e n i.val⟩
  | _, .not a, e => let a := eval a e; ⟨fun i => (a i).inv⟩
  | _, .and a b, e => let a := eval a e; let b := eval b e; ⟨fun i => (a i).band (b i)⟩
  | _, .or a b, e => let a := eval a e; let b := eval b e; ⟨fun i => (a i).bor (b i)⟩
  | _, .xor a b, e => let a := eval a e; let b := eval b e; ⟨fun i => (a i).bxor (b i)⟩
  | _, .add a b, e => binary (· + ·) (eval a e) (eval b e)
  | _, .sub a b, e => binary (· - ·) (eval a e) (eval b e)
  | _, .mul a b, e => binary (· * ·) (eval a e) (eval b e)
  | _, .udiv a b, e => unsignedDiv (eval a e) (eval b e)
  | _, .shl a b, e =>
    let count := toBitVec (eval b e) |>.toNat
    let a := eval a e
    if known (eval b e) then ⟨fun i => if i.val < count then .zero else getBit a (i.val-count)⟩
    else fill .x
  | w, .shr a b, e =>
    let count := toBitVec (eval b e) |>.toNat
    let a := eval a e
    if known (eval b e) then ⟨fun i => if i.val+count < w then getBit a (i.val+count) else .zero⟩
    else fill .x
  | w, .sshr a b, e =>
    let count := toBitVec (eval b e) |>.toNat
    let a := eval a e
    if known (eval b e) then ⟨fun i => getBit a (min (i.val+count) (w-1))⟩
    else fill .x
  | _, .eq a b, e => fill (logicalEq (eval a e) (eval b e))
  | _, @Expr.caseEq w a b, e =>
    fill (if (List.finRange w).all (fun i => eval a e i == eval b e i) then .one else .zero)
  | _, .ult a b, e => fill (relation (fun x y => x < y) (eval a e) (eval b e))
  | _, .slt a b, e => fill (relation (fun x y => x.toInt < y.toInt) (eval a e) (eval b e))
  | _, .mux s a b, e => mux (getBit (eval s e) 0) (eval a e) (eval b e)
  | w, @Expr.pmux _ n a b s, e =>
    match (List.finRange n).filter (fun i => eval s e i == .one) with
    | [] => eval a e
    | [j] => let b := eval b e; ⟨fun i => getBit b (w*j.val+i.val)⟩
    | _ => fill .x
  | _, @Expr.concat a b hi lo, e =>
    let hi := eval hi e; let lo := eval lo e
    ⟨fun i => if i.val < b then getBit lo i.val else getBit hi (i.val-b)⟩
  | _, @Expr.zext w _ a, e => let a := eval a e; ⟨fun i => if i.val < w then getBit a i.val else .zero⟩
  | _, @Expr.sext w _ a, e => let a := eval a e; ⟨fun i => getBit a (min i.val (w-1))⟩
  | _, .extract i a, e => fill (getBit (eval a e) i)
  | _, .slice lo _ a, e => let a := eval a e; ⟨fun i => getBit a (lo+i.val)⟩

structure Wire where
  name : String
  width : Nat
  expr : Expr width
structure Module where
  name : String
  inputs : List LeanRTL.InPort
  wires : List Wire
  outputs : List Wire

def Expr.valid (scope : List (String × Nat)) : {w : Nat} → Expr w → Bool
  | w, expr => w > 0 && match expr with
    | .const _ | .fill _ => true
    | .var n k => scope.lookup n == some k
    | .not a => a.valid scope
    | .and a b | .or a b | .xor a b | .add a b | .sub a b | .mul a b | .udiv a b
    | .eq a b | .caseEq a b | .ult a b | .slt a b => a.valid scope && b.valid scope
    | .shl a b | .shr a b | .sshr a b => a.valid scope && b.valid scope
    | .mux s a b => s.valid scope && a.valid scope && b.valid scope
    | .pmux a b s => a.valid scope && b.valid scope && s.valid scope
    | .concat a b => a.valid scope && b.valid scope
    | .zext _ a | .sext _ a => a.valid scope
    | @Expr.extract k i a => a.valid scope && i < k
    | @Expr.slice k lo len a => a.valid scope && lo + len ≤ k

def Module.valid (m : Module) : Bool := Id.run do
  let names := m.inputs.map (·.name) ++ m.wires.map (·.name) ++ m.outputs.map (·.name)
  if names.eraseDups.length != names.length then return false
  if !(m.inputs.all (fun p => p.width > 0)) then return false
  let mut scope := m.inputs.map (fun p => (p.name, p.width))
  for wire in m.wires do
    if !wire.expr.valid scope then return false
    scope := (wire.name, wire.width) :: scope
  return m.outputs.all (fun p => p.expr.valid scope)

def valuesEnv (values : List (String × List Bit)) (input : Env) : Env :=
  fun n i => match values.lookup n with
    | some bits => bits.getD i .x
    | none => input n i

/-- Materialize named wires as data. A chain of function-valued environments can
be eta-expanded by the evaluator and recompute all preceding wires on lookup. -/
def Module.wireValues (m : Module) (input : Env) : List (String × List Bit) :=
  m.wires.foldl (fun values w =>
    let value := (List.finRange w.width).map (eval w.expr (valuesEnv values input))
    (w.name, value) :: values) []
def Module.eval (m : Module) (input : Env) : List (String × String) :=
  let values := m.wireValues input
  let env := valuesEnv values input
  m.outputs.map (fun p => (p.name, renderValue (FourState.eval p.expr env)))

theorem resolve_z_left (a : Bit) : Bit.resolve .z a = a := by cases a <;> rfl
theorem resolve_z_right (a : Bit) : Bit.resolve a .z = a := by cases a <;> rfl
theorem resolve_comm (a b : Bit) : Bit.resolve a b = Bit.resolve b a := by cases a <;> cases b <;> rfl
theorem mux_unknown_same {w : Nat} (a : Value w) : mux .x a a = a := by
  cases a with | mk bits =>
   apply congrArg Value.mk
   funext i
   change Bit.merge (bits i) (bits i) = bits i
   cases bits i <;> rfl
theorem eq_known_mismatch {w : Nat} (a b : Value w)
    (h : (List.finRange w).any (fun i => (a i).known && (b i).known && a i != b i) = true) :
    logicalEq a b = .zero := by simp [logicalEq, h]

end LeanRTL.FourState
