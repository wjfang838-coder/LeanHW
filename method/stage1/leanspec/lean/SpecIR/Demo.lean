import SpecIR

/-!
# `SpecIR.Demo` — `alu`, before and after, as a worked example of the T3/T4 obligation.

This is the mechanised form of the diagnosis in `DESIGN.md` §F1.

`rtllm/alu`'s prose lists seventeen opcode mnemonics and says the port `r` "gives out the
result". It never states what any result *is*. leanSpec asked fourteen questions about that
specification and not one of them was about `r`; all fourteen went to flag side-channels the
testbench does not check, while the emitted Verilog computed `LUI` as `{a[31:16], 16'b0}` and
commented that it had done so "as specified". The reference computes `{a[15:0], 16'h0000}` — the
*low* half.

`aluAsGrounded` below is the IR containing exactly what the prose entails: every result is a
`hole`. Nothing had to notice the ambiguity, and nothing had to be clever. The output function
owes a value for every opcode, and the prose supplies none, so eighteen coordinates are open by
arithmetic. That is obligation **T4**.

`aluDecided` is the same IR after the questions are answered, and it is `determined`.
-/

namespace SpecIR.Demo

structure AluIn where
  a    : Nat
  b    : Nat
  aluc : Nat
deriving Repr, Inhabited

def opTable : List (Nat × String) :=
  [(0x20, "ADD"),  (0x21, "ADDU"), (0x22, "SUB"),  (0x23, "SUBU"), (0x24, "AND"),
   (0x25, "OR"),   (0x26, "XOR"),  (0x27, "NOR"),  (0x2a, "SLT"),  (0x2b, "SLTU"),
   (0x00, "SLL"),  (0x02, "SRL"),  (0x03, "SRA"),  (0x04, "SLLV"), (0x06, "SRLV"),
   (0x07, "SRAV"), (0x0f, "LUI")]

def opName (c : Nat) : String :=
  ((opTable.find? (fun p => p.1 == c)).map Prod.snd).getD "unmatched"

def renderAluIn (i : AluIn) : List (String × Val) :=
  [("a", Val.mk 32 i.a), ("b", Val.mk 32 i.b), ("aluc", Val.mk 6 i.aluc)]

/-- The IR carrying exactly what the prose grounds. Every result coordinate is open. -/
def aluAsGrounded : Design Unit AluIn where
  name     := "alu — as the prose grounds it"
  machine  :=
    { init := ()
    , step := fun _ _ => ()
    , out  := fun _ i =>
        [ ("r",        .hole s!"r_on_{opName i.aluc}" 32)
        , ("zero",     .hole "zero_semantics" 1)
        , ("carry",    .hole "carry_semantics" 1)
        , ("negative", .hole "negative_semantics" 1)
        , ("overflow", .hole "overflow_semantics" 1)
        , ("flag",     .hole "flag_semantics" 1) ] }
  renderIn := renderAluIn

/-- One stimulus per opcode, plus an unmatched one: the smallest suite that touches every
coordinate the output function owes a value for. -/
def suite : List (List AluIn) :=
  (opTable.map (fun (c, _) => [({ a := 0x0000_001c, b := 0x0000_0003, aluc := c } : AluIn)]))
  ++ [[{ a := 0x0000_001c, b := 0x0000_0003, aluc := 0x3f }]]

/-! ## After the questions are answered -/

private def w32 : Nat := 4294967296
private def signed32 (v : Nat) : Int :=
  if v ≥ 2147483648 then (Int.ofNat v) - (Int.ofNat w32) else Int.ofNat v
private def unsigned32 (i : Int) : Nat := (i % (Int.ofNat w32)).toNat % w32

def aluResult (i : AluIn) : Option Nat :=
  let a := i.a % w32
  let b := i.b % w32
  match i.aluc with
  | 0x20 => some (unsigned32 (signed32 a + signed32 b))
  | 0x21 => some ((a + b) % w32)
  | 0x22 => some (unsigned32 (signed32 a - signed32 b))
  | 0x23 => some ((a + w32 - b) % w32)
  | 0x24 => some (a &&& b)
  | 0x25 => some (a ||| b)
  | 0x26 => some (a ^^^ b)
  | 0x27 => some ((w32 - 1) - (a ||| b))
  | 0x2a => some (if signed32 a < signed32 b then 1 else 0)
  | 0x2b => some (if a < b then 1 else 0)
  | 0x00 => some ((b <<< a) % w32)
  | 0x02 => some (b >>> a)
  | 0x03 => some (unsigned32 (signed32 b / (2 ^ a)))
  | 0x04 => some ((b <<< (a % 32)) % w32)
  | 0x06 => some (b >>> (a % 32))
  | 0x07 => some (unsigned32 (signed32 b / (2 ^ (a % 32))))
  -- The answer.  LUI takes the LOW half of `a`, not the high half.
  | 0x0f => some (((a % 65536) * 65536) % w32)
  | _    => none

def aluDecided : Design Unit AluIn where
  name     := "alu — decided"
  machine  :=
    { init := ()
    , step := fun _ _ => ()
    , out  := fun _ i =>
        let r := aluResult i
        [ ("r",        match r with | some v => Val.mk 32 v | none => .z 32)
        , ("zero",     match r with | some v => Val.mk 1 (if v == 0 then 1 else 0) | none => .x 1)
        , ("carry",    .z 1)
        , ("negative", match r with | some v => Val.mk 1 (v >>> 31) | none => .z 1)
        , ("overflow", .z 1)
        , ("flag",     if i.aluc == 0x2a then Val.mk 1 (if signed32 i.a < signed32 i.b then 1 else 0)
                       else if i.aluc == 0x2b then Val.mk 1 (if i.a < i.b then 1 else 0)
                       else .z 1) ] }
  renderIn := renderAluIn

end SpecIR.Demo
