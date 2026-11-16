/-!
# `SpecIR.Val` — the value lattice a specification is allowed to talk in.

A specification coordinate is not "a number". It is one of six things, and the last three are the
whole point of this library:

  * `bits w v`     a determined value, and the prose says so
  * `x w`          explicitly undefined, *declared so* — "the prose says this may be anything"
  * `z w`          high impedance, likewise declared
  * `hole id w`    **undetermined**: the specification does not say, and nobody has asked yet
  * `conv id w v`  a value, supplied by an **identifier's name** rather than by any sentence
  * `stru id w v`  a value, supplied only by a paragraph describing **how the module is built**
  * `conflict id w a b` two concrete readings supported by conflicting document claims

`hole` is a first-class value rather than a `sorry`, so a partial specification still elaborates
and still *runs*. That is what lets the obligations in `SpecIR.Check` be ordinary evaluation: to
find out whether a specification determines its output on some stimulus, run it and look for
holes in the result.

## Why `conv` and `stru` carry a value

The obvious design is to write a hole wherever the text is silent and be done. It is not enough,
and two designs say why.

`rtllm/alu` lists seventeen opcode mnemonics and never states a single result. An extractor asked
for holes will not write seventeen holes — it will write `ADD` as addition, because `ADD` *is*
addition, and it will be right sixteen times. The seventeenth is `LUI`, where the convention and
the reference disagree about which half of the operand survives. `conv` is how a reading records
"I closed this from the name": the value is there, so the object is still runnable and still
comparable, and the coordinate is still *open* for the purpose of asking.

`stru` is the same move for the other source. `alu`'s prose does define `LUI`, in the paragraph
describing the implementation, and defines it wrongly. `pulse_detect`'s prose puts output
generation "inside the always block", which is where the one-cycle delay that fails its testbench
comes from. Neither coordinate is underdetermined; both are determined by the wrong kind of
sentence. A reading that records *which kind* makes them askable without a second reading.

The alternative — extract the prose three times, once with the structural paragraphs removed and
once with the mnemonics opacified, and compare — measures the same thing more honestly and costs
three agent sessions per design instead of one. `specir.ablate` still implements it, and the
`--ablate` mode exists to check these self-reported labels against it. This constructor is the
cheap proxy; that mode is what says whether the proxy is any good.

The distinction between `x` and `hole` is the distinction between "the specification decided not
to constrain this" and "the specification never considered it". Collapsing them is exactly the
mistake that lets a coordinate close silently.
-/

namespace SpecIR

inductive Val where
  | bits (width : Nat) (v : Nat)
  | x    (width : Nat)
  | z    (width : Nat)
  | hole (id : String) (width : Nat)
  | conv (id : String) (width : Nat) (v : Nat)
  | stru (id : String) (width : Nat) (v : Nat)
  | conflict (id : String) (width : Nat) (left right : Nat)
deriving Repr, DecidableEq, Inhabited

/-- Where a coordinate's value came from. `grounded` is the only one that is silence. -/
inductive Source where
  | grounded
  | declared      -- `x` / `z`: the document says "anything" or "floating", and means it
  | hole
  | convention
  | structural
  | conflict
deriving Repr, DecidableEq, Inhabited

def Source.name : Source → String
  | .grounded   => "grounded"
  | .declared   => "declared"
  | .hole       => "hole"
  | .convention => "convention"
  | .structural => "structural"
  | .conflict   => "conflict"

namespace Val

/-- A value is formally determined when its constructor records an explicit decision.

Unlike `isOpen`, this is a proposition intended to occur in theorem statements.  In particular,
declared `x` and `z` values are determined: they express intentional freedom rather than a missing
decision. -/
@[simp] def Determined : Val → Prop
  | .bits _ _   => True
  | .x _        => True
  | .z _        => True
  | .hole _ _   => False
  | .conv _ _ _ => False
  | .stru _ _ _ => False
  | .conflict _ _ _ _ => False

instance (v : Val) : Decidable v.Determined := by
  cases v <;> simp only [Determined] <;> exact inferInstance

def width : Val → Nat
  | .bits w _   => w
  | .x w        => w
  | .z w        => w
  | .hole _ w   => w
  | .conv _ w _ => w
  | .stru _ w _ => w
  | .conflict _ w _ _ => w

def source : Val → Source
  | .bits _ _   => .grounded
  | .x _        => .declared
  | .z _        => .declared
  | .hole _ _   => .hole
  | .conv _ _ _ => .convention
  | .stru _ _ _ => .structural
  | .conflict _ _ _ _ => .conflict

/-- A coordinate is **open** when the document did not settle it: no text at all, or text of the
wrong kind. `x` and `z` are closed — somebody decided. -/
def isOpen (v : Val) : Bool :=
  match v.source with
  | .grounded | .declared => false
  | _                     => true

@[deprecated isOpen (since := "2026-09")]
def isHole : Val → Bool
  | .hole _ _ => true
  | _         => false

/-- The coordinate's name, for the readings that left it open. -/
def openId? : Val → Option String
  | .hole id _   => some id
  | .conv id _ _ => some id
  | .stru id _ _ => some id
  | .conflict id _ _ _ => some id
  | _            => none

def holeId? : Val → Option String := openId?

/-- A determined value, truncated to its declared width. -/
def mk (w v : Nat) : Val := .bits w (v % (2 ^ w))

namespace Determined

/-- Determination is preserved by a conditional when both possible values are determined.

This compositional lemma avoids unfolding a large value-producing expression with `simp`, which
can be prohibitively expensive for generated state machines. -/
theorem ite (c : Prop) [Decidable c] {a b : Val}
    (ha : a.Determined) (hb : b.Determined) :
    (if c then a else b).Determined := by
  by_cases h : c
  · rw [if_pos h]
    exact ha
  · rw [if_neg h]
    exact hb

/-- A total bit-pattern match whose fallback is an explicit `x` is determined whenever its
`bits` branch is determined. -/
theorem matchBitsOrX (v : Val) (fallbackWidth : Nat) (f : Nat → Val)
    (hf : ∀ n, (f n).Determined) :
    (match v with
      | .bits _ n => f n
      | _ => .x fallbackWidth).Determined := by
  cases v <;> first | exact hf _ | trivial

/-- Two-input counterpart of `matchBitsOrX`. -/
theorem matchBits2OrX (a b : Val) (fallbackWidth : Nat)
    (f : Nat → Nat → Val)
    (hf : ∀ leftValue rightValue, (f leftValue rightValue).Determined) :
    (match a, b with
      | .bits _ leftValue, .bits _ rightValue => f leftValue rightValue
      | _, _ => .x fallbackWidth).Determined := by
  cases a <;> cases b <;> first | exact hf _ _ | trivial

end Determined

/-- The natural value, when there is one — including the values a reading supplied from a name or
from a structural paragraph, because those are still what that reading would emit. -/
def nat? : Val → Option Nat
  | .bits _ v   => some v
  | .conv _ _ v => some v
  | .stru _ _ v => some v
  | .conflict _ _ left _ => some left
  | _           => none

end Val

/-- A hardware register's validity is never encoded in its payload bits. -/
structure Register (width : Nat) where
  data : BitVec width := 0
  valid : Bool := false
deriving Repr, DecidableEq, Inhabited

namespace Register

def write {w : Nat} (n : Nat) : Register w := ⟨BitVec.ofNat w n, true⟩

def observe {w : Nat} (r : Register w) : Val :=
  if r.valid then Val.mk w r.data.toNat else .x w

@[simp] theorem observe_determined {w : Nat} (r : Register w) :
    r.observe.Determined := by
  simp only [observe]
  split <;> simp [Val.mk]

end Register

/-! ## Rendering

Values are rendered the way an engineer writes them: 1-bit as a bare digit, narrow words in
binary, wide words in hex. An open coordinate is rendered with its own marker, so a trace table
shows at a glance which cells the document actually paid for:

    `?id`          nothing said
    `~id=32'h…`    said by a name
    `^id=32'h…`    said by a structural paragraph
-/

private def hexDigit (n : Nat) : Char :=
  if n < 10 then Char.ofNat (48 + n) else Char.ofNat (87 + n)

private partial def hexAux (v : Nat) (acc : String) : String :=
  if v == 0 then acc else hexAux (v / 16) (String.singleton (hexDigit (v % 16)) ++ acc)

def toHex (v : Nat) : String := if v == 0 then "0" else hexAux v ""

def toBinPad (v w : Nat) : String :=
  (List.range w).reverse.foldl
    (fun s i => s ++ (if (v >>> i) % 2 == 1 then "1" else "0")) ""

private def lit (w v : Nat) : String :=
  if w == 1 then (if v % 2 == 1 then "1" else "0")
  else if w ≤ 8 then s!"{w}'b{toBinPad v w}"
  else s!"{w}'h{toHex v}"

def Val.render : Val → String
  | .bits w v      => lit w v
  | .x w           => if w == 1 then "x" else s!"{w}'x"
  | .z w           => if w == 1 then "z" else s!"{w}'z"
  | .hole id _     => s!"?{id}"
  | .conv id w v   => s!"~{id}={lit w v}"
  | .stru id w v   => s!"^{id}={lit w v}"
  | .conflict id w left right => s!"!{id}={lit w left}|{lit w right}"

/-- The value a `conv`/`stru` cell committed to, rendered as a Verilog literal.  `none` for a
genuine hole, which has no value to show.  This is what a convention question is *about*: the
answerer is not being asked to invent `r` at `LUI`, they are being asked whether `32'h12340000`
is what the reference actually puts there. -/
def Val.proposed? : Val → Option String
  | .conv _ w v => some (lit w v)
  | .stru _ w v => some (lit w v)
  | .conflict _ w left right => some (lit w left ++ " | " ++ lit w right)
  | _           => none

/-- The value alone, with the provenance marker stripped. This is what the *decided* object should
agree with when a coordinate turns out to have been guessed correctly, and what a report uses to
say how often a convention was right. -/
def Val.bare : Val → String
  | .bits w v      => lit w v
  | .x w           => if w == 1 then "x" else s!"{w}'x"
  | .z w           => if w == 1 then "z" else s!"{w}'z"
  | .hole _ _      => "?"
  | .conv _ w v    => lit w v
  | .stru _ w v    => lit w v
  | .conflict _ w left _ => lit w left

end SpecIR
