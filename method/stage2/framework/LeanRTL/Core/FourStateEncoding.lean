import LeanRTL.Core.FourState
import LeanRTL.Core.Compiler

/-! Explicit two-bit encoding of all four states. Every input code is legal:
00=0, 01=1, 10=X, 11=Z. Equality compares both planes without masking Z or X.
The encoding is injective. FourStateCompilerCorrect and FourStateModuleCorrect
prove general semantic preservation for the compiler below. HDL frontend and
serialization fidelity are separate boundaries. -/
namespace LeanRTL.FourState.Encoding

def encodeBit : Bit → Bool × Bool
  | .zero => (false, false)
  | .one => (false, true)
  | .x => (true, false)
  | .z => (true, true)
def decodeBit (p : Bool × Bool) : Bit :=
  if p.1 then if p.2 then .z else .x else if p.2 then .one else .zero
theorem decode_encode (b : Bit) : decodeBit (encodeBit b) = b := by cases b <;> rfl
theorem encode_decode (p : Bool × Bool) : encodeBit (decodeBit p) = p := by
  rcases p with ⟨a, b⟩
  cases a <;> cases b <;> rfl
theorem encode_injective (a b : Bit) (h : encodeBit a = encodeBit b) : a = b := by
  have := congrArg decodeBit h
  simpa only [decode_encode] using this
theorem planes_equal_iff (a b : Bit) : encodeBit a = encodeBit b ↔ a = b :=
  ⟨encode_injective a b, fun h => congrArg encodeBit h⟩

def encodeValue {w : Nat} (a : Value w) : (Fin w → Bool) × (Fin w → Bool) :=
  (fun i => (encodeBit (a i)).1, fun i => (encodeBit (a i)).2)
def decodeValue {w : Nat} (p : (Fin w → Bool) × (Fin w → Bool)) : Value w :=
  ⟨fun i => decodeBit (p.1 i, p.2 i)⟩
theorem decode_encode_value {w : Nat} (a : Value w) : decodeValue (encodeValue a) = a := by
  cases a with | mk bits =>
    apply congrArg Value.mk
    funext i
    exact decode_encode (bits i)
theorem encode_value_injective {w : Nat} (a b : Value w) (h : encodeValue a = encodeValue b) : a = b := by
  have := congrArg decodeValue h
  simpa only [decode_encode_value] using this
theorem value_planes_equal_iff {w : Nat} (a b : Value w) : encodeValue a = encodeValue b ↔ a = b :=
  ⟨encode_value_injective a b, fun h => congrArg encodeValue h⟩

structure Rails (w : Nat) where
  tag : LeanRTL.Expr w
  data : LeanRTL.Expr w

def zero (w : Nat) : LeanRTL.Expr w := .const 0
def ones (w : Nat) : LeanRTL.Expr w := .const (-1)
def anyBit {w : Nat} (a : LeanRTL.Expr w) : LeanRTL.Expr 1 := .not (.eq a (zero w))
def constant {w : Nat} (b : Bit) : Rails w :=
  let p := encodeBit b
  ⟨if p.1 then ones w else zero w, if p.2 then ones w else zero w⟩
def choose {w : Nat} (s : LeanRTL.Expr 1) (a b : Rails w) : Rails w :=
  ⟨.mux s a.tag b.tag, .mux s a.data b.data⟩
def active {w : Nat} (a : Rails w) : LeanRTL.Expr w := .and (.not a.tag) a.data
def inactive {w : Nat} (a : Rails w) : LeanRTL.Expr w := .and (.not a.tag) (.not a.data)
def strictBinary {w : Nat} (op : LeanRTL.Expr w → LeanRTL.Expr w → LeanRTL.Expr w)
    (a b : Rails w) : Rails w :=
  choose (anyBit (.or a.tag b.tag)) (constant .x) ⟨zero w, op a.data b.data⟩
def compare {w : Nat} (op : LeanRTL.Expr w → LeanRTL.Expr w → LeanRTL.Expr 1)
    (a b : Rails w) : Rails 1 :=
  choose (anyBit (.or a.tag b.tag)) (constant .x) ⟨zero 1, op a.data b.data⟩

def compile : {w : Nat} → FourState.Expr w → Rails w
  | w, .const v => ⟨zero w, .const v⟩
  | _, .fill b => constant b
  | w, .var n _ => ⟨.var ("t__" ++ n) w, .var ("d__" ++ n) w⟩
  | _, .not a => let a := compile a; ⟨a.tag, .and (.not a.tag) (.not a.data)⟩
  | _, .and a b =>
    let a := compile a; let b := compile b
    let one := .and (active a) (active b)
    let zro := .or (inactive a) (inactive b)
    ⟨.not (.or one zro), one⟩
  | _, .or a b =>
    let a := compile a; let b := compile b
    let one := .or (active a) (active b)
    let zro := .and (inactive a) (inactive b)
    ⟨.not (.or one zro), one⟩
  | _, .xor a b =>
    let a := compile a; let b := compile b
    let tag := .or a.tag b.tag
    ⟨tag, .and (.not tag) (.xor a.data b.data)⟩
  | _, .add a b => strictBinary .add (compile a) (compile b)
  | _, .sub a b => strictBinary .sub (compile a) (compile b)
  | _, .mul a b => strictBinary .mul (compile a) (compile b)
  | _, .udiv a b => strictBinary .udiv (compile a) (compile b)
  | _, .shl a b =>
    let a := compile a; let b := compile b
    choose (anyBit b.tag) (constant .x) ⟨.shl a.tag b.data, .shl a.data b.data⟩
  | _, .shr a b =>
    let a := compile a; let b := compile b
    choose (anyBit b.tag) (constant .x) ⟨.shr a.tag b.data, .shr a.data b.data⟩
  | _, .sshr a b =>
    let a := compile a; let b := compile b
    choose (anyBit b.tag) (constant .x) ⟨.sshr a.tag b.data, .sshr a.data b.data⟩
  | _, .eq a b =>
    let a := compile a; let b := compile b
    let unknown := .or a.tag b.tag
    let mismatch := anyBit (.and (.not unknown) (.xor a.data b.data))
    let uncertain := anyBit unknown
    ⟨.and (.not mismatch) uncertain, .and (.not mismatch) (.not uncertain)⟩
  | _, .caseEq a b =>
    let a := compile a; let b := compile b
    ⟨zero 1, .and (.eq a.tag b.tag) (.eq a.data b.data)⟩
  | _, .ult a b => compare .ult (compile a) (compile b)
  | _, .slt a b => compare .slt (compile a) (compile b)
  | _, .mux s a b =>
    let s := compile s; let a := compile a; let b := compile b
    let diff := .or (.xor a.tag b.tag) (.xor a.data b.data)
    let merged : Rails _ := ⟨.or a.tag diff, .and a.data (.not diff)⟩
    choose s.tag merged (choose s.data a b)
  | w, @FourState.Expr.pmux _ n a b s =>
    let a := compile a; let b := compile b; let s := compile s
    let selected := active s
    ((List.range n).foldl (fun (acc : Rails w × LeanRTL.Expr 1) i =>
      let isActive := .extract i selected
      let word : Rails w := ⟨.slice (w*i) w b.tag, .slice (w*i) w b.data⟩
      (choose isActive (choose acc.2 (constant .x) word) acc.1, .or acc.2 isActive))
      (a, zero 1)).1
  | _, .concat a b =>
    let a := compile a; let b := compile b
    ⟨.concat a.tag b.tag, .concat a.data b.data⟩
  | _, .zext k a => let a := compile a; ⟨.zext k a.tag, .zext k a.data⟩
  | _, .sext k a => let a := compile a; ⟨.sext k a.tag, .sext k a.data⟩
  | _, .extract i a => let a := compile a; ⟨.extract i a.tag, .extract i a.data⟩
  | _, .slice lo len a => let a := compile a; ⟨.slice lo len a.tag, .slice lo len a.data⟩

def module (m : FourState.Module) : LeanRTL.Module := {
  name := m.name ++ "_fourstate"
  inputs := m.inputs.flatMap (fun p =>
    [{ name := "t__" ++ p.name, width := p.width }, { name := "d__" ++ p.name, width := p.width }])
  wires := m.wires.flatMap (fun p =>
    let r := compile p.expr
    [{ name := "t__" ++ p.name, width := p.width, expr := r.tag },
     { name := "d__" ++ p.name, width := p.width, expr := r.data }])
  outputs := m.outputs.flatMap (fun p =>
    let r := compile p.expr
    [{ name := "t__" ++ p.name, width := p.width, expr := r.tag },
     { name := "d__" ++ p.name, width := p.width, expr := r.data }])
}

end LeanRTL.FourState.Encoding
