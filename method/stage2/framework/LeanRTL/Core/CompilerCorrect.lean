import LeanRTL.Core.BackendSem
/-!
# Compiler correctness (M6): ⟦e⟧ = ⟦compile e⟧  (combinational)
-/
namespace LeanRTL.CompilerCorrect
open LeanRTL LeanRTL.Backend LeanRTL.BackendSem

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-! ## Run-kit -/

@[simp] theorem run_pure {α} (a : α) (s : CState) : (pure a : CM α).run s = (a, s) := rfl

@[simp] theorem run_bind {α β} (x : CM α) (f : α → CM β) (s : CState) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

@[simp] theorem run_map {α β} (f : α → β) (x : CM α) (s : CState) :
    (f <$> x).run s = (f (x.run s).1, (x.run s).2) := rfl

@[simp] theorem run_seqRight {α β} (x : CM α) (y : CM β) (s : CState) :
    (x *> y).run s = y.run (x.run s).2 := rfl

@[simp] theorem run_seqLeft {α β} (x : CM α) (y : CM β) (s : CState) :
    (x <* y).run s = ((x.run s).1, (y.run (x.run s).2).2) := rfl

-- Id-monad reductions, so the inline `not`/`mux` do-blocks fully crunch under simp.
@[simp] theorem id_map' {α β} (f : α → β) (x : Id α) : (f <$> x) = f x := rfl
@[simp] theorem id_bind' {α β} (x : Id α) (f : α → Id β) : (x >>= f) = f x := rfl
@[simp] theorem id_seqRight' {α β} (x : Id α) (y : Id β) : (x *> y) = y := rfl
@[simp] theorem id_pure' {α} (x : α) : (pure x : Id α) = x := rfl

@[simp] theorem fresh_run (w : Nat) (s : CState) :
    (fresh w).run s = ((List.range w).map (fun i => Bit.net (s.nextId + i)),
                       { s with nextId := s.nextId + w }) := rfl

@[simp] theorem emit_run (t : String) (p : List (String × String)) (d : List (String × Dir))
    (cn : List (String × Bus)) (s : CState) :
    (emit t p d cn).run s = ((), { s with
      cells := { name := s!"$auto{s.count}", type := t, parameters := p,
                 portDirections := d, connections := cn, hideName := true } :: s.cells,
      count := s.count + 1 }) := rfl

@[simp] theorem compileExpr_const {w : Nat} (v : BitVec w) (s : CState) :
    (compileExpr (.const v)).run s = (constBits v, s) := rfl

/-- `.and` desugars to: compile both operands, then emit one `$and` cell. -/
theorem compileExpr_and {w : Nat} (a b : Expr w) :
    compileExpr (.and a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitBin "$and" w ba bb) := rfl
theorem compileExpr_or {w : Nat} (a b : Expr w) :
    compileExpr (.or a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitBin "$or" w ba bb) := rfl
theorem compileExpr_xor {w : Nat} (a b : Expr w) :
    compileExpr (.xor a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitBin "$xor" w ba bb) := rfl
theorem compileExpr_add {w : Nat} (a b : Expr w) :
    compileExpr (.add a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitBin "$add" w ba bb) := rfl
theorem compileExpr_sub {w : Nat} (a b : Expr w) :
    compileExpr (.sub a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitBin "$sub" w ba bb) := rfl
theorem compileExpr_mul {w : Nat} (a b : Expr w) :
    compileExpr (.mul a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitBin "$mul" w ba bb) := rfl
theorem compileExpr_udiv {w : Nat} (a b : Expr w) :
    compileExpr (.udiv a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitBin "$div" w ba bb) := rfl
theorem compileExpr_umod {w : Nat} (a b : Expr w) :
    compileExpr (.umod a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitBin "$mod" w ba bb) := rfl
theorem compileExpr_eq {w : Nat} (a b : Expr w) :
    compileExpr (.eq a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitCmp "$eq" w ba bb) := rfl
theorem compileExpr_ult {w : Nat} (a b : Expr w) :
    compileExpr (.ult a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitCmp "$lt" w ba bb) := rfl
theorem compileExpr_slt {w : Nat} (a b : Expr w) :
    compileExpr (.slt a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitCmpSigned "$lt" w ba bb) := rfl
theorem compileExpr_shl {w k : Nat} (a : Expr w) (b : Expr k) :
    compileExpr (.shl a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitShift "$shl" 0 w k ba bb) := rfl
theorem compileExpr_shr {w k : Nat} (a : Expr w) (b : Expr k) :
    compileExpr (.shr a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitShift "$shr" 0 w k ba bb) := rfl
theorem compileExpr_sshr {w k : Nat} (a : Expr w) (b : Expr k) :
    compileExpr (.sshr a b)
      = (compileExpr a >>= fun ba => compileExpr b >>= fun bb => emitShift "$sshr" 1 w k ba bb) := rfl
theorem compileExpr_concat {a b : Nat} (ea : Expr a) (eb : Expr b) :
    compileExpr (.concat ea eb)
      = (compileExpr ea >>= fun bhi => compileExpr eb >>= fun blo => pure (blo ++ bhi)) := rfl
theorem compileExpr_zext {w : Nat} (k : Nat) (a : Expr w) :
    compileExpr (.zext k a)
      = (compileExpr a >>= fun ba => pure (ba ++ List.replicate k Bit.zero)) := rfl
theorem compileExpr_sext {w : Nat} (k : Nat) (a : Expr w) :
    compileExpr (.sext k a)
      = (compileExpr a >>= fun ba => pure (ba ++ List.replicate k (ba.getLastD Bit.zero))) := rfl
theorem compileExpr_extract {w : Nat} (idx : Nat) (a : Expr w) :
    compileExpr (.extract idx a)
      = (compileExpr a >>= fun ba => pure [ba.getD idx Bit.zero]) := rfl
theorem compileExpr_slice {w : Nat} (lo len : Nat) (a : Expr w) :
    compileExpr (.slice lo len a)
      = (compileExpr a >>= fun ba => pure
          ((ba.drop lo).take len
            ++ List.replicate (len - ((ba.drop lo).take len).length) Bit.zero)) := rfl

@[simp] theorem compileExpr_var_some {n : String} {w : Nat} {s : CState} {bus : Bus}
    (h : s.env.lookup n = some bus) :
    (compileExpr (.var n w)).run s = (bus, s) := by
  simp [compileExpr, h] <;> rfl

/-- The bus a `fresh w` would allocate from state `s`. -/
def freshBus (s : CState) (w : Nat) : Bus := (List.range w).map (fun i => Bit.net (s.nextId + i))

@[simp] theorem emitBin_fst (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitBin ty w ba bb).run s).1 = freshBus s w := rfl

@[simp] theorem emitBin_nextId (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitBin ty w ba bb).run s).2.nextId = s.nextId + w := rfl

@[simp] theorem emitBin_count (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitBin ty w ba bb).run s).2.count = s.count + 1 := rfl

@[simp] theorem emitBin_env (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitBin ty w ba bb).run s).2.env = s.env := rfl

/-- The `$<ty>` cell `emitBin` prepends. -/
def binCell (s : CState) (w : Nat) (ty : String) (ba bb : Bus) : Cell :=
  let nm := s!"$auto{s.count}"
  { name := nm, type := ty, parameters := binParams w,
    portDirections := [("A", Dir.input), ("B", Dir.input), ("Y", Dir.output)],
    connections := [("A", ba), ("B", bb), ("Y", freshBus s w)], hideName := true }

@[simp] theorem emitBin_cells (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitBin ty w ba bb).run s).2.cells = binCell s w ty ba bb :: s.cells := rfl

/-- The `$not` cell the unary `.not` case emits (over the post-operand state). -/
def notCell (s : CState) (w : Nat) (ba : Bus) : Cell :=
  let nm := s!"$auto{s.count}"
  { name := nm, type := "$not",
    parameters := [("A_SIGNED", binStr32 0), ("A_WIDTH", binStr32 w), ("Y_WIDTH", binStr32 w)],
    portDirections := [("A", Dir.input), ("Y", Dir.output)],
    connections := [("A", ba), ("Y", freshBus s w)], hideName := true }

@[simp] theorem compileExpr_not_fst {w : Nat} (a : Expr w) (s : CState) :
    ((compileExpr (.not a)).run s).1 = freshBus ((compileExpr a).run s).2 w := rfl
@[simp] theorem compileExpr_not_nextId {w : Nat} (a : Expr w) (s : CState) :
    ((compileExpr (.not a)).run s).2.nextId = ((compileExpr a).run s).2.nextId + w := rfl
@[simp] theorem compileExpr_not_env {w : Nat} (a : Expr w) (s : CState) :
    ((compileExpr (.not a)).run s).2.env = ((compileExpr a).run s).2.env := rfl
@[simp] theorem compileExpr_not_cells {w : Nat} (a : Expr w) (s : CState) :
    ((compileExpr (.not a)).run s).2.cells
      = notCell ((compileExpr a).run s).2 w ((compileExpr a).run s).1
        :: ((compileExpr a).run s).2.cells := rfl

/-! ## Layer 0 — bus denotation toolkit -/

/-- The `i`-th bit of a LSB-first nat is the `i`-th list entry. -/
theorem bitsToNat_testBit (L : List Bool) (i : Nat) :
    (bitsToNat L).testBit i = L.getD i false := by
  induction L generalizing i with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
    cases i with
    | zero => cases b <;> simp [bitsToNat, Nat.testBit_zero, Nat.mul_mod_right]
    | succ j =>
      have : (bitsToNat (b :: bs)) / 2 = bitsToNat bs := by
        cases b <;> simp [bitsToNat] <;> omega
      simp [Nat.testBit_succ, this, ih]

/-- Mapping `bitDen` commutes with `getD` (since `bitDen σ .zero = false`). -/
theorem map_bitDen_getD (σ : Nat → Bool) (b : Bus) (i : Nat) :
    (b.map (bitDen σ)).getD i false = bitDen σ (b.getD i .zero) := by
  induction b generalizing i with
  | nil => simp [bitDen]
  | cons x xs ih => cases i with
    | zero => simp
    | succ j => simpa using ih j

/-- A bus's denotation, bit by bit. -/
theorem busDen_getLsbD (σ : Nat → Bool) (w : Nat) (b : Bus) (i : Nat) :
    (busDen σ w b).getLsbD i = (decide (i < w) && bitDen σ (b.getD i .zero)) := by
  unfold busDen busValNat
  rw [BitVec.getLsbD_ofNat, bitsToNat_testBit, map_bitDen_getD]

/-- Constants denote themselves (independent of σ). -/
theorem busDen_constBits {w : Nat} (σ : Nat → Bool) (v : BitVec w) :
    busDen σ w (constBits v) = v := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  rw [busDen_getLsbD]
  by_cases h : i < w
  · simp only [h, decide_true, Bool.true_and]
    have hc : (constBits v).getD i .zero = (if v.getLsbD i then Bit.one else Bit.zero) := by
      simp [constBits, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h]
    rw [hc]; cases v.getLsbD i <;> simp [bitDen]
  · simp [h]

/-- `bitsToNat` of an `n`-bit list is `< 2^n`. -/
theorem bitsToNat_lt (L : List Bool) : bitsToNat L < 2 ^ L.length := by
  induction L with
  | nil => simp [bitsToNat]
  | cons b bs ih =>
    simp only [bitsToNat, List.length_cons, Nat.pow_succ]
    cases b <;> simp <;> omega

/-- A bus's nat value is bounded by `2^(its length)`. -/
theorem busValNat_lt (σ : Nat → Bool) (b : Bus) : busValNat σ b < 2 ^ b.length := by
  have h := bitsToNat_lt (b.map (bitDen σ))
  simpa [busValNat, List.length_map] using h

/-- When a bus has exactly width `k`, its nat value equals the `toNat` of its `k`-bit denotation. -/
theorem busDen_toNat (σ : Nat → Bool) (b : Bus) (k : Nat) (h : b.length = k) :
    (busDen σ k b).toNat = busValNat σ b := by
  rw [busDen, BitVec.toNat_ofNat, Nat.mod_eq_of_lt (h ▸ busValNat_lt σ b)]

/-- When a bus has width exactly `w`, its `i`-th denotation bit is the denotation of its `i`-th
    list entry (the padding beyond width agrees because out-of-range `getD` is `zero`). -/
theorem busDen_getLsbD_len (σ : Nat → Bool) (w : Nat) (ba : Bus) (h : ba.length = w) (i : Nat) :
    (busDen σ w ba).getLsbD i = bitDen σ (ba.getD i Bit.zero) := by
  rw [busDen_getLsbD]
  by_cases hi : i < w
  · simp [hi]
  · have hnone : ba.getD i Bit.zero = Bit.zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [hnone]; simp [hi, bitDen]

theorem BusBelow_append {n : Nat} {b1 b2 : Bus} (h1 : BusBelow n b1) (h2 : BusBelow n b2) :
    BusBelow n (b1 ++ b2) := by
  intro k hk
  rcases List.mem_append.1 hk with h | h
  · exact h1 k h
  · exact h2 k h

theorem BusBelow_replicate_zero {n k : Nat} : BusBelow n (List.replicate k Bit.zero) := by
  intro j hj
  simp only [List.mem_replicate] at hj
  exact Bit.noConfusion hj.2

/-- Appending zeros doesn't change any `getD` entry (padding agrees with out-of-range default). -/
theorem getD_append_repl_zero (ba : Bus) (k i : Nat) :
    (ba ++ List.replicate k Bit.zero).getD i Bit.zero = ba.getD i Bit.zero := by
  simp only [List.getD_eq_getElem?_getD]
  rcases Nat.lt_or_ge i ba.length with hi | hi
  · rw [List.getElem?_append_left hi]
  · rw [List.getElem?_append_right hi, List.getElem?_eq_none hi, List.getElem?_replicate]
    split <;> rfl

/-- Zero-extension at the bus level denotes `setWidth`. -/
theorem busDen_zext (σ : Nat → Bool) (w k : Nat) (ba : Bus) (h : ba.length = w) :
    busDen σ (w + k) (ba ++ List.replicate k Bit.zero) = (busDen σ w ba).setWidth (w + k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  rw [busDen_getLsbD_len σ (w + k) (ba ++ List.replicate k Bit.zero)
        (by rw [List.length_append, List.length_replicate, h]) i,
      getD_append_repl_zero, BitVec.getLsbD_setWidth, busDen_getLsbD_len σ w ba h i]
  by_cases hi : (i : Nat) < w + k
  · simp [hi]
  · have : ba.getD i Bit.zero = Bit.zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]; rfl
    rw [this]; simp [hi, bitDen]

/-- Single-bit extraction denotes the indexed bit. -/
theorem busDen_extract (σ : Nat → Bool) (w : Nat) (ba : Bus) (h : ba.length = w) (idx : Nat) :
    busDen σ 1 [ba.getD idx Bit.zero] = if (busDen σ w ba).getLsbD idx then 1 else 0 := by
  rw [busDen_getLsbD_len σ w ba h idx]
  simp only [busDen, busValNat, List.map_cons, List.map_nil, bitsToNat, Nat.mul_zero, Nat.add_zero]
  cases bitDen σ (ba.getD idx Bit.zero) <;> rfl

/-- `getD` of an append splits at the first list's length. -/
theorem getD_append (l1 l2 : Bus) (i : Nat) :
    (l1 ++ l2).getD i Bit.zero
      = if i < l1.length then l1.getD i Bit.zero else l2.getD (i - l1.length) Bit.zero := by
  simp only [List.getD_eq_getElem?_getD]
  by_cases hi : i < l1.length
  · rw [List.getElem?_append_left hi]; simp [hi]
  · rw [List.getElem?_append_right (by omega)]; simp [hi]

/-- Bus concatenation (low bus appended before high bus) denotes `BitVec.append`. -/
theorem busDen_concat (σ : Nat → Bool) (a' b' : Nat) (bhi blo : Bus)
    (hhi : bhi.length = a') (hlo : blo.length = b') :
    busDen σ (a' + b') (blo ++ bhi) = busDen σ a' bhi ++ busDen σ b' blo := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  rw [busDen_getLsbD_len σ (a' + b') (blo ++ bhi)
        (by rw [List.length_append, hlo, hhi]; omega) i,
      getD_append, BitVec.getLsbD_append]
  by_cases hi : (i : Nat) < b'
  · rw [busDen_getLsbD_len σ b' blo hlo i]; simp [hi, hlo]
  · rw [busDen_getLsbD_len σ a' bhi hhi (i - b')]; simp [hi, hlo]

/-- The MSB of a width-`w` bus is the denotation of its top list entry. -/
theorem busDen_msb (σ : Nat → Bool) (w : Nat) (ba : Bus) (h : ba.length = w) :
    (busDen σ w ba).msb = bitDen σ (ba.getD (w - 1) Bit.zero) := by
  rw [BitVec.msb_eq_getLsbD_last, busDen_getLsbD_len σ w ba h]

/-- The last bus entry equals the entry at index `length - 1`. -/
theorem getLastD_eq (ba : Bus) (w : Nat) (h : ba.length = w) :
    ba.getLastD Bit.zero = ba.getD (w - 1) Bit.zero := by
  rw [List.getLastD_eq_getLast?, List.getLast?_eq_getElem?, List.getD_eq_getElem?_getD, h]

/-- Sign-extension at the bus level denotes `signExtend`. -/
theorem busDen_sext (σ : Nat → Bool) (w k : Nat) (ba : Bus) (h : ba.length = w) :
    busDen σ (w + k) (ba ++ List.replicate k (ba.getLastD Bit.zero))
      = (busDen σ w ba).signExtend (w + k) := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  rw [busDen_getLsbD_len σ (w + k) (ba ++ List.replicate k (ba.getLastD Bit.zero))
        (by rw [List.length_append, List.length_replicate, h]) i,
      getD_append, BitVec.getLsbD_signExtend]
  by_cases hiw : i < ba.length
  · simp only [hiw, if_true]
    rw [busDen_getLsbD_len σ w ba h i]
    have hw : i < w := h ▸ hiw
    have hwk : i < w + k := by omega
    simp [hw, hwk]
  · simp only [hiw, if_false]
    rw [busDen_msb σ w ba h, ← getLastD_eq ba w h]
    have hw : ¬ i < w := by omega
    by_cases hik : i < w + k
    · have hr : (List.replicate k (ba.getLastD Bit.zero)).getD (i - ba.length) Bit.zero
          = ba.getLastD Bit.zero := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_pos (by omega)]; rfl
      rw [hr]; simp [hw, hik]
    · have hr : (List.replicate k (ba.getLastD Bit.zero)).getD (i - ba.length) Bit.zero = Bit.zero := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate, if_neg (by omega)]; rfl
      rw [hr]; simp [hik, bitDen]

/-- `getD` through `take`/`drop`: the window entry, or zero past the window. -/
theorem getD_take_drop (ba : Bus) (lo len i : Nat) :
    ((ba.drop lo).take len).getD i Bit.zero
      = if i < len then ba.getD (lo + i) Bit.zero else Bit.zero := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_take, List.getElem?_drop]
  by_cases hi : i < len <;> simp [hi]

/-- Slicing (drop `lo`, keep `len`, zero-pad) denotes shift-right then `setWidth`. -/
theorem busDen_slice (σ : Nat → Bool) (w lo len : Nat) (ba : Bus) (h : ba.length = w) :
    busDen σ len ((ba.drop lo).take len
        ++ List.replicate (len - ((ba.drop lo).take len).length) Bit.zero)
      = ((busDen σ w ba) >>> lo).setWidth len := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  have hlen : ((ba.drop lo).take len
      ++ List.replicate (len - ((ba.drop lo).take len).length) Bit.zero).length = len := by
    rw [List.length_append, List.length_replicate, List.length_take]; omega
  rw [busDen_getLsbD_len σ len _ hlen i, BitVec.getLsbD_setWidth, BitVec.getLsbD_ushiftRight,
      busDen_getLsbD_len σ w ba h (lo + i), getD_append]
  by_cases hi : i < len
  · by_cases hs : i < ((ba.drop lo).take len).length
    · rw [if_pos hs, getD_take_drop]; simp [hi]
    · have hrepl : (List.replicate (len - ((ba.drop lo).take len).length) Bit.zero).getD
          (i - ((ba.drop lo).take len).length) Bit.zero = Bit.zero := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
      have hz : ba.getD (lo + i) Bit.zero = Bit.zero := by
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by
          rw [h]; rw [List.length_take, List.length_drop] at hs; omega)]; rfl
      rw [if_neg hs, hrepl, hz]; simp [bitDen]
  · have hrepl : (List.replicate (len - ((ba.drop lo).take len).length) Bit.zero).getD
        (i - ((ba.drop lo).take len).length) Bit.zero = Bit.zero := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_replicate]; split <;> rfl
    rw [if_neg (show ¬ i < ((ba.drop lo).take len).length by rw [List.length_take]; omega), hrepl]
    simp [hi, bitDen]

/-! ## Soundness for leaf expressions -/

/-- `compileExpr` is sound on constants. -/
theorem const_sound {w : Nat} (v : BitVec w) (env : Env) (s : CState) (σ : Nat → Bool) :
    busDen σ w ((compileExpr (.const v)).run s).1 = eval (.const v) env := by
  simp [compileExpr_const, eval, busDen_constBits]

/-- `compileExpr` is sound on bound variables. -/
theorem var_sound {n : String} {w : Nat} {env : Env} {s : CState} {σ : Nat → Bool} {bus : Bus}
    (hb : s.env.lookup n = some bus) (hlen : bus.length = w)
    (hmem : busDen σ bus.length bus = env.lookup n bus.length) :
    busDen σ w ((compileExpr (.var n w)).run s).1 = eval (.var n w) env := by
  rw [compileExpr_var_some hb]
  subst hlen
  simpa [eval, Env.lookup] using hmem

/-! ## Layer 1.5 — frame + σ-extension for the operator induction -/

/-- `busDen` only depends on σ at the nets the bus mentions. -/
theorem busDen_frame (σ σ' : Nat → Bool) (w : Nat) (b : Bus) (n : Nat)
    (hb : BusBelow n b) (hσ : ∀ k, k < n → σ k = σ' k) : busDen σ w b = busDen σ' w b := by
  have hm : b.map (bitDen σ) = b.map (bitDen σ') := by
    apply List.map_congr_left
    intro bit hbit
    cases bit with
    | net k => exact hσ k (hb k hbit)
    | zero => rfl
    | one => rfl
    | x => rfl
    | z => rfl
  simp only [busDen, busValNat, hm]

/-- Extend σ on the fresh range `[base, base+w)` to carry `val` (LSB-first). -/
def setRange (σ : Nat → Bool) (base w : Nat) (val : BitVec w) : Nat → Bool :=
  fun k => if base ≤ k ∧ k < base + w then val.getLsbD (k - base) else σ k

/-- `setRange` leaves all nets below `base` untouched. -/
theorem setRange_lt (σ : Nat → Bool) (base w : Nat) (val : BitVec w) (k : Nat) (h : k < base) :
    setRange σ base w val k = σ k := by
  simp only [setRange]; rw [if_neg (by omega)]

/-- A fresh bus `[base, base+w)` denotes exactly the value `setRange` stored there. -/
theorem setRange_get (σ : Nat → Bool) (base w : Nat) (val : BitVec w) :
    busDen (setRange σ base w val) w ((List.range w).map (fun i => Bit.net (base + i))) = val := by
  apply BitVec.eq_of_getLsbD_eq
  intro i
  rw [busDen_getLsbD]
  by_cases h : i < w
  · have hget : ((List.range w).map (fun i => Bit.net (base + i))).getD i .zero = Bit.net (base + i) := by
      simp [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range, h]
    have hsr : setRange σ base w val (base + i) = val.getLsbD i := by
      simp only [setRange]; rw [if_pos (by omega)]; congr 1; omega
    rw [hget]; simp [bitDen, hsr, h]
  · simp [h]

/-! ## Frame for cell consistency (old cells survive a σ-extension) -/

/-- A successful `lookup` witnesses membership. -/
theorem lookup_mem {l : List (String × Bus)} {k : String} {b : Bus}
    (h : l.lookup k = some b) : (k, b) ∈ l := by
  induction l with
  | nil => simp [List.lookup] at h
  | cons hd tl ih =>
    rcases hd with ⟨k', v⟩
    simp only [List.lookup] at h
    cases hk : k == k' with
    | true =>
      rw [hk] at h
      obtain rfl := eq_of_beq hk
      simp only [Option.some.injEq] at h
      subst h; exact List.mem_cons_self
    | false =>
      rw [hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Every port bus of a bounded cell is bounded. -/
theorem connBusBelow {n : Nat} {c : Cell} (hc : CellBelow n c) (key : String) :
    BusBelow n (conn c key) := by
  unfold conn
  cases h : c.connections.lookup key with
  | none => intro k hk; simp at hk
  | some b => simpa using hc key b (lookup_mem h)

/-- `busValNat` (shift counts) also only depends on σ at the bus's nets. -/
theorem busValNat_frame (σ σ' : Nat → Bool) (b : Bus) (n : Nat)
    (hb : BusBelow n b) (hσ : ∀ k, k < n → σ k = σ' k) : busValNat σ b = busValNat σ' b := by
  have hm : b.map (bitDen σ) = b.map (bitDen σ') := by
    apply List.map_congr_left
    intro bit hbit
    cases bit with
    | net k => exact hσ k (hb k hbit)
    | zero => rfl
    | one => rfl
    | x => rfl
    | z => rfl
  simp only [busValNat, hm]

/-- `cellHolds` only depends on σ at the cell's own nets. -/
theorem cellHolds_frame (σ σ' : Nat → Bool) (c : Cell) (n : Nat)
    (hc : CellBelow n c) (hσ : ∀ k, k < n → σ k = σ' k) : cellHolds σ c = cellHolds σ' c := by
  have e : ∀ (m : Nat) (key : String), busDen σ m (conn c key) = busDen σ' m (conn c key) :=
    fun m key => busDen_frame σ σ' m (conn c key) n (connBusBelow hc key) hσ
  have e2 : ∀ (key : String), busValNat σ (conn c key) = busValNat σ' (conn c key) :=
    fun key => busValNat_frame σ σ' (conn c key) n (connBusBelow hc key) hσ
  unfold cellHolds
  split <;> simp only [e, e2]

/-- A consistent cell list stays consistent under a σ-extension that fixes its nets. -/
theorem ConsistentCells_frame {σ σ' : Nat → Bool} {cs : List Cell} {n : Nat}
    (hcb : CellsBounded cs n) (hσ : ∀ k, k < n → σ k = σ' k) (h : ConsistentCells σ cs) :
    ConsistentCells σ' cs := by
  intro c hc
  rw [← cellHolds_frame σ σ' c n (hcb c hc) hσ]
  exact h c hc

/-! ## Operator soundness, demonstrated end-to-end on a compiled `$and`

For a representative binary operator we show the full pipeline is correct: compiling
`a & b` emits an `$and` cell, and there is a net valuation that (1) satisfies every emitted
cell and (2) makes the output bus denote `va &&& vb`.  This exercises the var lookups, the
fresh-cell emission, and the `setRange` σ-construction together. -/
theorem and_correct (s : CState) (σ₀ : Nat → Bool) (ba bb : Bus) (va vb : BitVec 1)
    (hcells : s.cells = [])
    (ha : s.env.lookup "a" = some ba) (hb : s.env.lookup "b" = some bb)
    (bnda : BusBelow s.nextId ba) (bndb : BusBelow s.nextId bb)
    (hva : busDen σ₀ 1 ba = va) (hvb : busDen σ₀ 1 bb = vb) :
    ∃ σ,
      busDen σ 1 ((compileExpr (.and (.var "a" 1) (.var "b" 1))).run s).1 = va &&& vb ∧
      ConsistentCells σ ((compileExpr (.and (.var "a" 1) (.var "b" 1))).run s).2.cells ∧
      (∀ k, k < s.nextId → σ k = σ₀ k) := by
  -- reduce the compilation: output = fresh Y bus, cells = the one `$and` cell
  simp only [compileExpr_and, run_bind, compileExpr_var_some ha, compileExpr_var_some hb,
             emitBin_fst, emitBin_cells, hcells]
  -- the chosen valuation: σ₀ extended so the fresh output carries va &&& vb
  refine ⟨setRange σ₀ s.nextId 1 (va &&& vb), ?_, ?_, ?_⟩
  · -- output denotes va &&& vb
    simpa [freshBus] using setRange_get σ₀ s.nextId 1 (va &&& vb)
  · -- the single `$and` cell is satisfied
    intro c hc
    simp only [List.mem_singleton] at hc
    subst hc
    have hY : busDen (setRange σ₀ s.nextId 1 (va &&& vb)) 1 (freshBus s 1) = va &&& vb := by
      simpa [freshBus] using setRange_get σ₀ s.nextId 1 (va &&& vb)
    have hA : busDen (setRange σ₀ s.nextId 1 (va &&& vb)) 1 ba = va := by
      rw [busDen_frame (setRange σ₀ s.nextId 1 (va &&& vb)) σ₀ 1 ba s.nextId bnda
            (fun k hk => setRange_lt σ₀ s.nextId 1 (va &&& vb) k hk)]; exact hva
    have hB : busDen (setRange σ₀ s.nextId 1 (va &&& vb)) 1 bb = vb := by
      rw [busDen_frame (setRange σ₀ s.nextId 1 (va &&& vb)) σ₀ 1 bb s.nextId bndb
            (fun k hk => setRange_lt σ₀ s.nextId 1 (va &&& vb) k hk)]; exact hvb
    show busDen (setRange σ₀ s.nextId 1 (va &&& vb)) 1 (freshBus s 1)
         = busDen (setRange σ₀ s.nextId 1 (va &&& vb)) 1 ba
           &&& busDen (setRange σ₀ s.nextId 1 (va &&& vb)) 1 bb
    rw [hY, hA, hB]
  · -- the valuation extends σ₀ on all pre-existing nets
    intro k hk; exact setRange_lt σ₀ s.nextId 1 (va &&& vb) k hk

/-! ## General compiler soundness (single strengthened structural induction)

`Supp` marks the fragment proven general here — constants, signal references, and arbitrarily
nested `&` (the other emitBin operators `or/xor/add/sub/mul` follow the identical pattern, since
they share `emitBin`).  `sound` proves, for every `Supp` expression, that the compiled RTLIL has
a net valuation satisfying all emitted cells whose output bus denotes `eval e`. -/

def Supp : {w : Nat} → Expr w → Prop
  | _, .const _ => True
  | _, .var _ _ => True
  | _, .not a   => Supp a
  | _, .and a b => Supp a ∧ Supp b
  | _, .or a b  => Supp a ∧ Supp b
  | _, .xor a b => Supp a ∧ Supp b
  | _, .add a b => Supp a ∧ Supp b
  | _, .sub a b => Supp a ∧ Supp b
  | _, .mul a b => Supp a ∧ Supp b
  | _, .udiv a b => Supp a ∧ Supp b
  | _, .umod a b => Supp a ∧ Supp b
  | _, .eq a b  => Supp a ∧ Supp b
  | _, .ult a b => Supp a ∧ Supp b
  | _, .slt a b => Supp a ∧ Supp b
  | _, .shl a b => Supp a ∧ Supp b
  | _, .shr a b => Supp a ∧ Supp b
  | _, .sshr a b => Supp a ∧ Supp b
  | _, .mux sg a b => Supp sg ∧ Supp a ∧ Supp b
  | _, .zext _ a => Supp a
  | _, .extract _ a => Supp a
  | _, .concat ea eb => Supp ea ∧ Supp eb
  | _, .sext _ a => Supp a
  | _, .slice _ _ a => Supp a

theorem BusBelow_mono {n m : Nat} {b : Bus} (h : BusBelow n b) (hnm : n ≤ m) : BusBelow m b :=
  fun k hk => Nat.lt_of_lt_of_le (h k hk) hnm

theorem EnvBounded_mono {cenv n m} (h : EnvBounded cenv n) (hnm : n ≤ m) : EnvBounded cenv m :=
  fun nm bus hl => BusBelow_mono (h nm bus hl) hnm

theorem CellBelow_mono {n m : Nat} {c : Cell} (h : CellBelow n c) (hnm : n ≤ m) : CellBelow m c :=
  fun k b hb => BusBelow_mono (h k b hb) hnm

theorem CellsBounded_mono {cs n m} (h : CellsBounded cs n) (hnm : n ≤ m) : CellsBounded cs m :=
  fun c hc => CellBelow_mono (h c hc) hnm

theorem CEnvOK_frame {σ σ' cenv env n} (hb : EnvBounded cenv n) (hσ : ∀ k, k < n → σ k = σ' k)
    (h : CEnvOK σ cenv env) : CEnvOK σ' cenv env := by
  intro nm bus hl
  rw [← busDen_frame σ σ' bus.length bus n (hb nm bus hl) hσ]
  exact h nm bus hl

theorem BusBelow_freshBus (s : CState) (w : Nat) : BusBelow (s.nextId + w) (freshBus s w) := by
  intro k hk
  simp only [freshBus, List.mem_map, List.mem_range] at hk
  obtain ⟨i, hi, hik⟩ := hk
  injection hik with hik; omega

theorem CellBelow_binCell {m : Nat} {s w ty ba bb} (ha : BusBelow m ba) (hb : BusBelow m bb)
    (hy : BusBelow m (freshBus s w)) : CellBelow m (binCell s w ty ba bb) := by
  intro k b hmem
  simp only [binCell, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
             Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption

theorem CellBelow_notCell {m : Nat} {s w ba} (ha : BusBelow m ba)
    (hy : BusBelow m (freshBus s w)) : CellBelow m (notCell s w ba) := by
  intro k b hmem
  simp only [notCell, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
             Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption

/-- The comparison cell (`$eq`/`$lt`) emitted by `emitCmp`/`emitCmpSigned`. -/
def cmpCell (s : CState) (w : Nat) (ty : String) (sgn : Nat) (ba bb : Bus) : Cell :=
  let nm := s!"$auto{s.count}"
  { name := nm, type := ty,
    parameters := [("A_SIGNED", binStr32 sgn), ("B_SIGNED", binStr32 sgn),
                   ("A_WIDTH", binStr32 w), ("B_WIDTH", binStr32 w), ("Y_WIDTH", binStr32 1)],
    portDirections := [("A", Dir.input), ("B", Dir.input), ("Y", Dir.output)],
    connections := [("A", ba), ("B", bb), ("Y", freshBus s 1)], hideName := true }

@[simp] theorem emitCmp_fst (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitCmp ty w ba bb).run s).1 = freshBus s 1 := rfl
@[simp] theorem emitCmp_nextId (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitCmp ty w ba bb).run s).2.nextId = s.nextId + 1 := rfl
@[simp] theorem emitCmp_env (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitCmp ty w ba bb).run s).2.env = s.env := rfl
@[simp] theorem emitCmp_cells (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitCmp ty w ba bb).run s).2.cells = cmpCell s w ty 0 ba bb :: s.cells := rfl
@[simp] theorem emitCmpS_fst (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitCmpSigned ty w ba bb).run s).1 = freshBus s 1 := rfl
@[simp] theorem emitCmpS_nextId (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitCmpSigned ty w ba bb).run s).2.nextId = s.nextId + 1 := rfl
@[simp] theorem emitCmpS_env (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitCmpSigned ty w ba bb).run s).2.env = s.env := rfl
@[simp] theorem emitCmpS_cells (ty : String) (w : Nat) (ba bb : Bus) (s : CState) :
    ((emitCmpSigned ty w ba bb).run s).2.cells = cmpCell s w ty 1 ba bb :: s.cells := rfl

theorem CellBelow_cmpCell {m : Nat} {s w ty sgn ba bb} (ha : BusBelow m ba) (hb : BusBelow m bb)
    (hy : BusBelow m (freshBus s 1)) : CellBelow m (cmpCell s w ty sgn ba bb) := by
  intro k b hmem
  simp only [cmpCell, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
             Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption

/-- The shift cell (`$shl`/`$shr`/`$sshr`) emitted by `emitShift`. -/
def shiftCell (s : CState) (aSigned w k : Nat) (ty : String) (ba bb : Bus) : Cell :=
  let nm := s!"$auto{s.count}"
  { name := nm, type := ty,
    parameters := [("A_SIGNED", binStr32 aSigned), ("B_SIGNED", binStr32 0),
                   ("A_WIDTH", binStr32 w), ("B_WIDTH", binStr32 k), ("Y_WIDTH", binStr32 w)],
    portDirections := [("A", Dir.input), ("B", Dir.input), ("Y", Dir.output)],
    connections := [("A", ba), ("B", bb), ("Y", freshBus s w)], hideName := true }

@[simp] theorem emitShift_fst (ty : String) (aSigned w k : Nat) (ba bb : Bus) (s : CState) :
    ((emitShift ty aSigned w k ba bb).run s).1 = freshBus s w := rfl
@[simp] theorem emitShift_nextId (ty : String) (aSigned w k : Nat) (ba bb : Bus) (s : CState) :
    ((emitShift ty aSigned w k ba bb).run s).2.nextId = s.nextId + w := rfl
@[simp] theorem emitShift_env (ty : String) (aSigned w k : Nat) (ba bb : Bus) (s : CState) :
    ((emitShift ty aSigned w k ba bb).run s).2.env = s.env := rfl
@[simp] theorem emitShift_cells (ty : String) (aSigned w k : Nat) (ba bb : Bus) (s : CState) :
    ((emitShift ty aSigned w k ba bb).run s).2.cells = shiftCell s aSigned w k ty ba bb :: s.cells :=
  rfl

theorem CellBelow_shiftCell {m : Nat} {s aSigned w k ty ba bb} (ha : BusBelow m ba)
    (hb : BusBelow m bb) (hy : BusBelow m (freshBus s w)) :
    CellBelow m (shiftCell s aSigned w k ty ba bb) := by
  intro i b hmem
  simp only [shiftCell, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
             Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption

/-- The `$mux` cell emitted by the `.mux` case (Yosys `$mux`: `Y = S ? B : A`). -/
def muxCell (s : CState) (w : Nat) (bs ba bb : Bus) : Cell :=
  let nm := s!"$auto{s.count}"
  { name := nm, type := "$mux", parameters := [("WIDTH", binStr32 w)],
    portDirections := [("A", Dir.input), ("B", Dir.input), ("S", Dir.input), ("Y", Dir.output)],
    connections := [("A", bb), ("B", ba), ("S", bs), ("Y", freshBus s w)], hideName := true }

@[simp] theorem compileExpr_mux_fst {w : Nat} (sg : Expr 1) (a b : Expr w) (st : CState) :
    ((compileExpr (.mux sg a b)).run st).1
      = freshBus ((compileExpr b).run ((compileExpr a).run
          ((compileExpr sg).run st).2).2).2 w := rfl
@[simp] theorem compileExpr_mux_nextId {w : Nat} (sg : Expr 1) (a b : Expr w) (st : CState) :
    ((compileExpr (.mux sg a b)).run st).2.nextId
      = ((compileExpr b).run ((compileExpr a).run ((compileExpr sg).run st).2).2).2.nextId + w := rfl
@[simp] theorem compileExpr_mux_env {w : Nat} (sg : Expr 1) (a b : Expr w) (st : CState) :
    ((compileExpr (.mux sg a b)).run st).2.env
      = ((compileExpr b).run ((compileExpr a).run ((compileExpr sg).run st).2).2).2.env := rfl
@[simp] theorem compileExpr_mux_cells {w : Nat} (sg : Expr 1) (a b : Expr w) (st : CState) :
    ((compileExpr (.mux sg a b)).run st).2.cells
      = muxCell ((compileExpr b).run ((compileExpr a).run ((compileExpr sg).run st).2).2).2 w
          ((compileExpr sg).run st).1
          ((compileExpr a).run ((compileExpr sg).run st).2).1
          ((compileExpr b).run ((compileExpr a).run ((compileExpr sg).run st).2).2).1
        :: ((compileExpr b).run ((compileExpr a).run ((compileExpr sg).run st).2).2).2.cells := rfl

theorem CellBelow_muxCell {m : Nat} {s w bs ba bb} (hs : BusBelow m bs) (ha : BusBelow m ba)
    (hb : BusBelow m bb) (hy : BusBelow m (freshBus s w)) : CellBelow m (muxCell s w bs ba bb) := by
  intro i b hmem
  simp only [muxCell, List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false,
             Prod.mk.injEq] at hmem
  rcases hmem with ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ | ⟨_, rfl⟩ <;> assumption

/-- `compileExpr` never changes the name→bus environment. -/
theorem compileExpr_env {w : Nat} (e : Expr w) (s : CState) :
    ((compileExpr e).run s).2.env = s.env := by
  induction e generalizing s with
  | const v => rfl
  | var n w =>
    cases h : s.env.lookup n with
    | some bus => rw [compileExpr_var_some h]
    | none => simp [compileExpr, h]
  | not a iha => rw [compileExpr_not_env]; exact iha s
  | and a b iha ihb => rw [compileExpr_and]; simp only [run_bind, emitBin_env]; rw [ihb, iha]
  | or a b iha ihb => rw [compileExpr_or]; simp only [run_bind, emitBin_env]; rw [ihb, iha]
  | xor a b iha ihb => rw [compileExpr_xor]; simp only [run_bind, emitBin_env]; rw [ihb, iha]
  | add a b iha ihb => rw [compileExpr_add]; simp only [run_bind, emitBin_env]; rw [ihb, iha]
  | sub a b iha ihb => rw [compileExpr_sub]; simp only [run_bind, emitBin_env]; rw [ihb, iha]
  | mul a b iha ihb => rw [compileExpr_mul]; simp only [run_bind, emitBin_env]; rw [ihb, iha]
  | udiv a b iha ihb => rw [compileExpr_udiv]; simp only [run_bind, emitBin_env]; rw [ihb, iha]
  | umod a b iha ihb => rw [compileExpr_umod]; simp only [run_bind, emitBin_env]; rw [ihb, iha]
  | eq a b iha ihb => rw [compileExpr_eq]; simp only [run_bind, emitCmp_env]; rw [ihb, iha]
  | ult a b iha ihb => rw [compileExpr_ult]; simp only [run_bind, emitCmp_env]; rw [ihb, iha]
  | slt a b iha ihb => rw [compileExpr_slt]; simp only [run_bind, emitCmpS_env]; rw [ihb, iha]
  | shl a b iha ihb => rw [compileExpr_shl]; simp only [run_bind, emitShift_env]; rw [ihb, iha]
  | shr a b iha ihb => rw [compileExpr_shr]; simp only [run_bind, emitShift_env]; rw [ihb, iha]
  | sshr a b iha ihb => rw [compileExpr_sshr]; simp only [run_bind, emitShift_env]; rw [ihb, iha]
  | mux sg a b ihs iha ihb => simp only [compileExpr_mux_env]; rw [ihb, iha, ihs]
  | concat ea eb ihea iheb =>
    rw [compileExpr_concat]; simp only [run_bind, run_pure]; rw [iheb, ihea]
  | zext k a iha => rw [compileExpr_zext]; simp only [run_bind, run_pure]; exact iha s
  | sext k a iha => rw [compileExpr_sext]; simp only [run_bind, run_pure]; exact iha s
  | extract idx a iha => rw [compileExpr_extract]; simp only [run_bind, run_pure]; exact iha s
  | slice lo len a iha => rw [compileExpr_slice]; simp only [run_bind, run_pure]; exact iha s

/-- The compiled output bus of a `Supp` expression has length equal to its declared width.
    (For the cell-emitting operators the output is a `freshBus`, so this is immediate; only the
    leaf cases consult `WidthOK`.) -/
theorem compileExpr_len {w : Nat} (e : Expr w) :
    Supp e → ∀ (s : CState), WidthOK s.env e → ((compileExpr e).run s).1.length = w := by
  induction e with
  | const v => intro _ s _; simp [compileExpr_const, constBits]
  | var n w => intro _ s hwf; obtain ⟨bus, hl, hlen⟩ := hwf; rw [compileExpr_var_some hl]; exact hlen
  | not a iha => intro _ s _; simp [compileExpr_not_fst, freshBus]
  | and a b iha ihb => intro _ s _; rw [compileExpr_and]; simp [run_bind, emitBin_fst, freshBus]
  | or a b iha ihb => intro _ s _; rw [compileExpr_or]; simp [run_bind, emitBin_fst, freshBus]
  | xor a b iha ihb => intro _ s _; rw [compileExpr_xor]; simp [run_bind, emitBin_fst, freshBus]
  | add a b iha ihb => intro _ s _; rw [compileExpr_add]; simp [run_bind, emitBin_fst, freshBus]
  | sub a b iha ihb => intro _ s _; rw [compileExpr_sub]; simp [run_bind, emitBin_fst, freshBus]
  | mul a b iha ihb => intro _ s _; rw [compileExpr_mul]; simp [run_bind, emitBin_fst, freshBus]
  | udiv a b iha ihb => intro _ s _; rw [compileExpr_udiv]; simp [run_bind, emitBin_fst, freshBus]
  | umod a b iha ihb => intro _ s _; rw [compileExpr_umod]; simp [run_bind, emitBin_fst, freshBus]
  | eq a b iha ihb => intro _ s _; rw [compileExpr_eq]; simp [run_bind, emitCmp_fst, freshBus]
  | ult a b iha ihb => intro _ s _; rw [compileExpr_ult]; simp [run_bind, emitCmp_fst, freshBus]
  | slt a b iha ihb => intro _ s _; rw [compileExpr_slt]; simp [run_bind, emitCmpS_fst, freshBus]
  | shl a b iha ihb => intro _ s _; rw [compileExpr_shl]; simp [run_bind, emitShift_fst, freshBus]
  | shr a b iha ihb => intro _ s _; rw [compileExpr_shr]; simp [run_bind, emitShift_fst, freshBus]
  | sshr a b iha ihb => intro _ s _; rw [compileExpr_sshr]; simp [run_bind, emitShift_fst, freshBus]
  | mux sg a b ihs iha ihb => intro _ s _; simp [compileExpr_mux_fst, freshBus]
  | zext k a iha =>
    intro hsupp s hwf
    rw [compileExpr_zext]
    simp only [run_bind, run_pure, List.length_append, List.length_replicate]
    rw [iha hsupp s hwf]
  | extract idx a iha => intro _ s _; rw [compileExpr_extract]; simp [run_bind, run_pure]
  | concat ea eb ihea iheb =>
    intro hsupp s hwf
    obtain ⟨hsea, hseb⟩ := hsupp
    obtain ⟨hwea, hweb⟩ := hwf
    rw [compileExpr_concat]
    simp only [run_bind, run_pure, List.length_append]
    rw [iheb hseb ((compileExpr ea).run s).2 (by rw [compileExpr_env ea s]; exact hweb),
        ihea hsea s hwea]
    omega
  | sext k a iha =>
    intro hsupp s hwf
    rw [compileExpr_sext]
    simp only [run_bind, run_pure, List.length_append, List.length_replicate]
    rw [iha hsupp s hwf]
  | slice lo len a iha =>
    intro _ s _
    rw [compileExpr_slice]
    simp only [run_bind, run_pure, List.length_append, List.length_replicate, List.length_take]
    omega

set_option maxHeartbeats 1000000 in
theorem sound {w : Nat} (e : Expr w) (env : Env) :
    Supp e → ∀ (s : CState) (σ₀ : Nat → Bool),
      WidthOK s.env e → CEnvOK σ₀ s.env env → EnvBounded s.env s.nextId →
      ConsistentCells σ₀ s.cells → CellsBounded s.cells s.nextId →
      ∃ σ : Nat → Bool,
        (∀ k, k < s.nextId → σ k = σ₀ k) ∧
        ConsistentCells σ ((compileExpr e).run s).2.cells ∧
        CellsBounded ((compileExpr e).run s).2.cells ((compileExpr e).run s).2.nextId ∧
        BusBelow ((compileExpr e).run s).2.nextId ((compileExpr e).run s).1 ∧
        s.nextId ≤ ((compileExpr e).run s).2.nextId ∧
        ((compileExpr e).run s).2.env = s.env ∧
        busDen σ w ((compileExpr e).run s).1 = eval e env := by
  induction e with
  | const v =>
    intro _ s σ₀ _ _ _ hcons hcb
    refine ⟨σ₀, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [compileExpr_const] using hcons
    · simpa only [compileExpr_const] using hcb
    · simp only [compileExpr_const]
      intro k hk
      simp only [constBits, List.mem_map, List.mem_range] at hk
      obtain ⟨i, _, hik⟩ := hk
      split at hik <;> exact Bit.noConfusion hik
    · simp only [compileExpr_const]; exact Nat.le_refl _
    · simp only [compileExpr_const]
    · simp [compileExpr_const, eval, busDen_constBits]
  | var n w =>
    intro _ s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨bus, hl, hlen⟩ := hwf
    subst hlen
    refine ⟨σ₀, fun _ _ => rfl, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · simpa only [compileExpr_var_some hl] using hcons
    · simpa only [compileExpr_var_some hl] using hcb
    · simp only [compileExpr_var_some hl]; exact hbnd n bus hl
    · simp only [compileExpr_var_some hl]; exact Nat.le_refl _
    · simp only [compileExpr_var_some hl]
    · simp only [compileExpr_var_some hl]; exact hmem n bus hl
  | @and w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    simp only [compileExpr_and, run_bind, emitBin_fst, emitBin_cells, emitBin_nextId, emitBin_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId w (busDen σb w RA.1 &&& busDen σb w RB.1) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId w _ k hk
    have hYval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 &&& busDen σb w RB.1)) w
        (freshBus RB.2 w) = busDen σb w RA.1 &&& busDen σb w RB.1 := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w (busDen σb w RA.1 &&& busDen σb w RB.1)
    have hAval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 &&& busDen σb w RB.1)) w RA.1
        = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 &&& busDen σb w RB.1)) w RB.1
        = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w (busDen σb w RA.1 &&& busDen σb w RB.1),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId w _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = busDen _ (freshBus RB.2 w).length RA.1 &&& busDen _ (freshBus RB.2 w).length RB.1
        rw [hflen, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_binCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      simp only [eval]
      rw [hYval, hAv, valb]
  | @or w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    simp only [compileExpr_or, run_bind, emitBin_fst, emitBin_cells, emitBin_nextId, emitBin_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId w (busDen σb w RA.1 ||| busDen σb w RB.1) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId w _ k hk
    have hYval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 ||| busDen σb w RB.1)) w
        (freshBus RB.2 w) = busDen σb w RA.1 ||| busDen σb w RB.1 := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w (busDen σb w RA.1 ||| busDen σb w RB.1)
    have hAval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 ||| busDen σb w RB.1)) w RA.1
        = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 ||| busDen σb w RB.1)) w RB.1
        = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w (busDen σb w RA.1 ||| busDen σb w RB.1),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId w _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = busDen _ (freshBus RB.2 w).length RA.1 ||| busDen _ (freshBus RB.2 w).length RB.1
        rw [hflen, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_binCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      simp only [eval]
      rw [hYval, hAv, valb]
  | @xor w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    simp only [compileExpr_xor, run_bind, emitBin_fst, emitBin_cells, emitBin_nextId, emitBin_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId w (busDen σb w RA.1 ^^^ busDen σb w RB.1) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId w _ k hk
    have hYval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 ^^^ busDen σb w RB.1)) w
        (freshBus RB.2 w) = busDen σb w RA.1 ^^^ busDen σb w RB.1 := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w (busDen σb w RA.1 ^^^ busDen σb w RB.1)
    have hAval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 ^^^ busDen σb w RB.1)) w RA.1
        = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 ^^^ busDen σb w RB.1)) w RB.1
        = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w (busDen σb w RA.1 ^^^ busDen σb w RB.1),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId w _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = busDen _ (freshBus RB.2 w).length RA.1 ^^^ busDen _ (freshBus RB.2 w).length RB.1
        rw [hflen, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_binCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      simp only [eval]
      rw [hYval, hAv, valb]
  | @add w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    simp only [compileExpr_add, run_bind, emitBin_fst, emitBin_cells, emitBin_nextId, emitBin_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId w (busDen σb w RA.1 + busDen σb w RB.1) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId w _ k hk
    have hYval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 + busDen σb w RB.1)) w
        (freshBus RB.2 w) = busDen σb w RA.1 + busDen σb w RB.1 := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w (busDen σb w RA.1 + busDen σb w RB.1)
    have hAval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 + busDen σb w RB.1)) w RA.1
        = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 + busDen σb w RB.1)) w RB.1
        = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w (busDen σb w RA.1 + busDen σb w RB.1),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId w _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = busDen _ (freshBus RB.2 w).length RA.1 + busDen _ (freshBus RB.2 w).length RB.1
        rw [hflen, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_binCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      simp only [eval]
      rw [hYval, hAv, valb]
  | @sub w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    simp only [compileExpr_sub, run_bind, emitBin_fst, emitBin_cells, emitBin_nextId, emitBin_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId w (busDen σb w RA.1 - busDen σb w RB.1) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId w _ k hk
    have hYval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 - busDen σb w RB.1)) w
        (freshBus RB.2 w) = busDen σb w RA.1 - busDen σb w RB.1 := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w (busDen σb w RA.1 - busDen σb w RB.1)
    have hAval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 - busDen σb w RB.1)) w RA.1
        = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 - busDen σb w RB.1)) w RB.1
        = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w (busDen σb w RA.1 - busDen σb w RB.1),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId w _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = busDen _ (freshBus RB.2 w).length RA.1 - busDen _ (freshBus RB.2 w).length RB.1
        rw [hflen, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_binCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      simp only [eval]
      rw [hYval, hAv, valb]
  | @mul w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    simp only [compileExpr_mul, run_bind, emitBin_fst, emitBin_cells, emitBin_nextId, emitBin_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId w (busDen σb w RA.1 * busDen σb w RB.1) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId w _ k hk
    have hYval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 * busDen σb w RB.1)) w
        (freshBus RB.2 w) = busDen σb w RA.1 * busDen σb w RB.1 := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w (busDen σb w RA.1 * busDen σb w RB.1)
    have hAval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 * busDen σb w RB.1)) w RA.1
        = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 * busDen σb w RB.1)) w RB.1
        = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w (busDen σb w RA.1 * busDen σb w RB.1),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId w _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = busDen _ (freshBus RB.2 w).length RA.1 * busDen _ (freshBus RB.2 w).length RB.1
        rw [hflen, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_binCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      simp only [eval]
      rw [hYval, hAv, valb]
  | @udiv w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    simp only [compileExpr_udiv, run_bind, emitBin_fst, emitBin_cells, emitBin_nextId, emitBin_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId w (busDen σb w RA.1 / busDen σb w RB.1) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId w _ k hk
    have hYval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 / busDen σb w RB.1)) w
        (freshBus RB.2 w) = busDen σb w RA.1 / busDen σb w RB.1 := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w (busDen σb w RA.1 / busDen σb w RB.1)
    have hAval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 / busDen σb w RB.1)) w RA.1
        = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 / busDen σb w RB.1)) w RB.1
        = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w (busDen σb w RA.1 / busDen σb w RB.1),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId w _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = busDen _ (freshBus RB.2 w).length RA.1 / busDen _ (freshBus RB.2 w).length RB.1
        rw [hflen, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_binCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      simp only [eval]
      rw [hYval, hAv, valb]
  | @umod w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    simp only [compileExpr_umod, run_bind, emitBin_fst, emitBin_cells, emitBin_nextId, emitBin_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId w (busDen σb w RA.1 % busDen σb w RB.1) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId w _ k hk
    have hYval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 % busDen σb w RB.1)) w
        (freshBus RB.2 w) = busDen σb w RA.1 % busDen σb w RB.1 := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w (busDen σb w RA.1 % busDen σb w RB.1)
    have hAval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 % busDen σb w RB.1)) w RA.1
        = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId w (busDen σb w RA.1 % busDen σb w RB.1)) w RB.1
        = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w (busDen σb w RA.1 % busDen σb w RB.1),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId w _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = busDen _ (freshBus RB.2 w).length RA.1 % busDen _ (freshBus RB.2 w).length RB.1
        rw [hflen, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_binCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      simp only [eval]
      rw [hYval, hAv, valb]
  | @not w a iha =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsupp s σ₀ hwf hmem hbnd hcons hcb
    simp only [compileExpr_not_fst, compileExpr_not_cells, compileExpr_not_nextId,
               compileExpr_not_env]
    generalize hGA : (compileExpr a).run s = RA at *
    have hframe : ∀ k, k < RA.2.nextId →
        setRange σa RA.2.nextId w (~~~ busDen σa w RA.1) k = σa k :=
      fun k hk => setRange_lt σa RA.2.nextId w _ k hk
    have hYval : busDen (setRange σa RA.2.nextId w (~~~ busDen σa w RA.1)) w (freshBus RA.2 w)
        = ~~~ busDen σa w RA.1 := by
      simpa [freshBus] using setRange_get σa RA.2.nextId w (~~~ busDen σa w RA.1)
    have hAval : busDen (setRange σa RA.2.nextId w (~~~ busDen σa w RA.1)) w RA.1 = busDen σa w RA.1 :=
      busDen_frame _ _ w RA.1 RA.2.nextId bba hframe
    refine ⟨setRange σa RA.2.nextId w (~~~ busDen σa w RA.1), ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σa RA.2.nextId w _ k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RA.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RA.2 w).length (freshBus RA.2 w)
             = ~~~ busDen _ (freshBus RA.2 w).length RA.1
        rw [hflen, hYval, hAval]
      · exact ConsistentCells_frame cba (fun k hk => (hframe k hk).symm) cca c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_notCell (BusBelow_mono bba (Nat.le_add_right _ _)) (BusBelow_freshBus RA.2 w)
      · exact CellsBounded_mono cba (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RA.2 w
    · exact Nat.le_trans moa (Nat.le_add_right _ _)
    · exact eva
    · simp only [eval]
      rw [hYval, vala]
  | @eq w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a hsa s hwa
    simp only [compileExpr_eq, run_bind, emitCmp_fst, emitCmp_cells, emitCmp_nextId, emitCmp_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId 1 (if busDen σb w RA.1 = busDen σb w RB.1 then 1 else 0) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId 1 _ k hk
    have hYval : busDen (setRange σb RB.2.nextId 1
          (if busDen σb w RA.1 = busDen σb w RB.1 then 1 else 0)) 1 (freshBus RB.2 1)
        = (if busDen σb w RA.1 = busDen σb w RB.1 then 1 else 0) := by
      simpa [freshBus] using setRange_get σb RB.2.nextId 1
        (if busDen σb w RA.1 = busDen σb w RB.1 then 1 else 0)
    have hAval : busDen (setRange σb RB.2.nextId 1
          (if busDen σb w RA.1 = busDen σb w RB.1 then 1 else 0)) w RA.1 = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId 1
          (if busDen σb w RA.1 = busDen σb w RB.1 then 1 else 0)) w RB.1 = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId 1 (if busDen σb w RA.1 = busDen σb w RB.1 then 1 else 0),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId 1 _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · show busDen _ 1 (freshBus RB.2 1)
             = if busDen _ RA.1.length RA.1 = busDen _ RA.1.length RB.1 then 1 else 0
        rw [hlenA, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_cmpCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 1)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 1
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · simp only [eval]
      rw [hYval]
      have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      rw [hAv, valb]
  | @ult w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a hsa s hwa
    simp only [compileExpr_ult, run_bind, emitCmp_fst, emitCmp_cells, emitCmp_nextId, emitCmp_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId 1 (if busDen σb w RA.1 < busDen σb w RB.1 then 1 else 0) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId 1 _ k hk
    have hYval : busDen (setRange σb RB.2.nextId 1
          (if busDen σb w RA.1 < busDen σb w RB.1 then 1 else 0)) 1 (freshBus RB.2 1)
        = (if busDen σb w RA.1 < busDen σb w RB.1 then 1 else 0) := by
      simpa [freshBus] using setRange_get σb RB.2.nextId 1
        (if busDen σb w RA.1 < busDen σb w RB.1 then 1 else 0)
    have hAval : busDen (setRange σb RB.2.nextId 1
          (if busDen σb w RA.1 < busDen σb w RB.1 then 1 else 0)) w RA.1 = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId 1
          (if busDen σb w RA.1 < busDen σb w RB.1 then 1 else 0)) w RB.1 = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId 1 (if busDen σb w RA.1 < busDen σb w RB.1 then 1 else 0),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId 1 _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · show busDen _ 1 (freshBus RB.2 1)
             = if busDen _ RA.1.length RA.1 < busDen _ RA.1.length RB.1 then 1 else 0
        rw [hlenA, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_cmpCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 1)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 1
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · simp only [eval]
      rw [hYval]
      have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      rw [hAv, valb]
  | @slt w a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun k hk => (exa k hk).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a hsa s hwa
    simp only [compileExpr_slt, run_bind, emitCmpS_fst, emitCmpS_cells, emitCmpS_nextId, emitCmpS_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ k, k < RB.2.nextId →
        setRange σb RB.2.nextId 1 (if (busDen σb w RA.1).toInt < (busDen σb w RB.1).toInt then 1 else 0) k = σb k :=
      fun k hk => setRange_lt σb RB.2.nextId 1 _ k hk
    have hYval : busDen (setRange σb RB.2.nextId 1
          (if (busDen σb w RA.1).toInt < (busDen σb w RB.1).toInt then 1 else 0)) 1 (freshBus RB.2 1)
        = (if (busDen σb w RA.1).toInt < (busDen σb w RB.1).toInt then 1 else 0) := by
      simpa [freshBus] using setRange_get σb RB.2.nextId 1
        (if (busDen σb w RA.1).toInt < (busDen σb w RB.1).toInt then 1 else 0)
    have hAval : busDen (setRange σb RB.2.nextId 1
          (if (busDen σb w RA.1).toInt < (busDen σb w RB.1).toInt then 1 else 0)) w RA.1 = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId 1
          (if (busDen σb w RA.1).toInt < (busDen σb w RB.1).toInt then 1 else 0)) w RB.1 = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId 1 (if (busDen σb w RA.1).toInt < (busDen σb w RB.1).toInt then 1 else 0),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro k hk
      rw [setRange_lt σb RB.2.nextId 1 _ k (Nat.lt_of_lt_of_le hk (Nat.le_trans moa mob)),
          exb k (Nat.lt_of_lt_of_le hk moa), exa k hk]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · show busDen _ 1 (freshBus RB.2 1)
             = if (busDen _ RA.1.length RA.1).toInt < (busDen _ RA.1.length RB.1).toInt then 1 else 0
        rw [hlenA, hYval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun k hk => (hframe k hk).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_cmpCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 1)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 1
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · simp only [eval]
      rw [hYval]
      have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      rw [hAv, valb]
  | @mux w sg a b ihs iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hss, hsa, hsb⟩ := hsupp
    obtain ⟨hws, hwa, hwb⟩ := hwf
    obtain ⟨σs, exs, ccs, cbs, bbs, mos, evs, vals⟩ := ihs hss s σ₀ hws hmem hbnd hcons hcb
    have hwa' : WidthOK ((compileExpr sg).run s).2.env a := by rw [evs]; exact hwa
    have hmema : CEnvOK σs ((compileExpr sg).run s).2.env env := by
      rw [evs]; exact CEnvOK_frame hbnd (fun i hi => (exs i hi).symm) hmem
    have hbnda : EnvBounded ((compileExpr sg).run s).2.env ((compileExpr sg).run s).2.nextId := by
      rw [evs]; exact EnvBounded_mono hbnd mos
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ :=
      iha hsa ((compileExpr sg).run s).2 σs hwa' hmema hbnda ccs cbs
    have hwb' : WidthOK ((compileExpr a).run ((compileExpr sg).run s).2).2.env b := by
      rw [eva, evs]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run ((compileExpr sg).run s).2).2.env env := by
      rw [eva, evs]; exact CEnvOK_frame hbnd
        (fun i hi => ((exa i (Nat.lt_of_lt_of_le hi mos)).trans (exs i hi)).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run ((compileExpr sg).run s).2).2.env
        ((compileExpr a).run ((compileExpr sg).run s).2).2.nextId := by
      rw [eva, evs]; exact EnvBounded_mono hbnd (Nat.le_trans mos moa)
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run ((compileExpr sg).run s).2).2 σa hwb' hmemb hbndb cca cba
    simp only [compileExpr_mux_fst, compileExpr_mux_cells, compileExpr_mux_nextId,
               compileExpr_mux_env]
    generalize hGS : (compileExpr sg).run s = RS at *
    generalize hGA : (compileExpr a).run RS.2 = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have exbs : ∀ i, i < RS.2.nextId → σb i = σs i :=
      fun i hi => (exb i (Nat.lt_of_lt_of_le hi moa)).trans (exa i hi)
    have hframe : ∀ i, i < RB.2.nextId →
        setRange σb RB.2.nextId w
          (if busDen σb 1 RS.1 = 1 then busDen σb w RA.1 else busDen σb w RB.1) i = σb i :=
      fun i hi => setRange_lt σb RB.2.nextId w _ i hi
    have hYval : busDen (setRange σb RB.2.nextId w
          (if busDen σb 1 RS.1 = 1 then busDen σb w RA.1 else busDen σb w RB.1)) w (freshBus RB.2 w)
        = (if busDen σb 1 RS.1 = 1 then busDen σb w RA.1 else busDen σb w RB.1) := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w
        (if busDen σb 1 RS.1 = 1 then busDen σb w RA.1 else busDen σb w RB.1)
    have hSval : busDen (setRange σb RB.2.nextId w
          (if busDen σb 1 RS.1 = 1 then busDen σb w RA.1 else busDen σb w RB.1)) 1 RS.1
        = busDen σb 1 RS.1 :=
      busDen_frame _ _ 1 RS.1 RB.2.nextId
        (BusBelow_mono bbs (Nat.le_trans moa mob)) hframe
    have hAval : busDen (setRange σb RB.2.nextId w
          (if busDen σb 1 RS.1 = 1 then busDen σb w RA.1 else busDen σb w RB.1)) w RA.1
        = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBval : busDen (setRange σb RB.2.nextId w
          (if busDen σb 1 RS.1 = 1 then busDen σb w RA.1 else busDen σb w RB.1)) w RB.1
        = busDen σb w RB.1 :=
      busDen_frame _ _ w RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w
        (if busDen σb 1 RS.1 = 1 then busDen σb w RA.1 else busDen σb w RB.1),
        ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [setRange_lt σb RB.2.nextId w _ i
            (Nat.lt_of_lt_of_le hi (Nat.le_trans mos (Nat.le_trans moa mob))),
          exb i (Nat.lt_of_lt_of_le hi (Nat.le_trans mos moa)),
          exa i (Nat.lt_of_lt_of_le hi mos), exs i hi]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = if busDen _ 1 RS.1 = 1 then busDen _ (freshBus RB.2 w).length RA.1
               else busDen _ (freshBus RB.2 w).length RB.1
        rw [hflen, hYval, hSval, hAval, hBval]
      · exact ConsistentCells_frame cbb (fun i hi => (hframe i hi).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_muxCell (BusBelow_mono bbs (Nat.le_trans (Nat.le_trans moa mob)
            (Nat.le_add_right _ _)))
          (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans mos (Nat.le_trans moa mob)) (Nat.le_add_right _ _)
    · rw [evb, eva, evs]
    · simp only [eval]
      rw [hYval]
      have hSv : busDen σb 1 RS.1 = eval sg env := by
        rw [busDen_frame σb σs 1 RS.1 RS.2.nextId bbs exbs]; exact vals
      have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      rw [hSv, hAv, valb]
  | @concat a b ea eb iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsea, hseb⟩ := hsupp
    obtain ⟨hwea, hweb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsea s σ₀ hwea hmem hbnd hcons hcb
    have hweb' : WidthOK ((compileExpr ea).run s).2.env eb := by rw [eva]; exact hweb
    have hmemb : CEnvOK σa ((compileExpr ea).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun i hi => (exa i hi).symm) hmem
    have hbndb : EnvBounded ((compileExpr ea).run s).2.env ((compileExpr ea).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hseb ((compileExpr ea).run s).2 σa hweb' hmemb hbndb cca cba
    have hlenA : ((compileExpr ea).run s).1.length = a := compileExpr_len ea hsea s hwea
    have hlenB : ((compileExpr eb).run ((compileExpr ea).run s).2).1.length = b :=
      compileExpr_len eb hseb _ hweb'
    simp only [compileExpr_concat, run_bind, run_pure]
    generalize hGA : (compileExpr ea).run s = RA at *
    generalize hGB : (compileExpr eb).run RA.2 = RB at *
    refine ⟨σb, ?_, ccb, cbb, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [exb i (Nat.lt_of_lt_of_le hi moa), exa i hi]
    · exact BusBelow_append bbb (BusBelow_mono bba mob)
    · exact Nat.le_trans moa mob
    · rw [evb, eva]
    · simp only [eval]
      rw [busDen_concat σb a b RA.1 RB.1 hlenA hlenB]
      have hAv : busDen σb a RA.1 = eval ea env := by
        rw [busDen_frame σb σa a RA.1 RA.2.nextId bba exb]; exact vala
      rw [hAv, valb]
  | @zext w k a iha =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsupp s σ₀ hwf hmem hbnd hcons hcb
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a hsupp s hwf
    simp only [compileExpr_zext, run_bind, run_pure]
    generalize hGA : (compileExpr a).run s = RA at *
    refine ⟨σa, exa, cca, cba, ?_, moa, eva, ?_⟩
    · exact BusBelow_append bba BusBelow_replicate_zero
    · simp only [eval]
      rw [busDen_zext σa w k RA.1 hlenA, vala]
  | @sext w k a iha =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsupp s σ₀ hwf hmem hbnd hcons hcb
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a hsupp s hwf
    simp only [compileExpr_sext, run_bind, run_pure]
    generalize hGA : (compileExpr a).run s = RA at *
    refine ⟨σa, exa, cca, cba, ?_, moa, eva, ?_⟩
    · apply BusBelow_append bba
      intro j hj
      simp only [List.mem_replicate] at hj
      obtain ⟨_, hjeq⟩ := hj
      rw [getLastD_eq RA.1 w hlenA] at hjeq
      rcases Nat.lt_or_ge (w - 1) RA.1.length with hidx | hidx
      · refine bba j ?_
        rw [hjeq, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
        exact List.getElem_mem hidx
      · exfalso
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hidx] at hjeq
        exact Bit.noConfusion hjeq
    · simp only [eval]
      rw [busDen_sext σa w k RA.1 hlenA, vala]
  | @extract w idx a iha =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsupp s σ₀ hwf hmem hbnd hcons hcb
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a hsupp s hwf
    simp only [compileExpr_extract, run_bind, run_pure]
    generalize hGA : (compileExpr a).run s = RA at *
    refine ⟨σa, exa, cca, cba, ?_, moa, eva, ?_⟩
    · intro j hj
      simp only [List.mem_singleton] at hj
      rcases Nat.lt_or_ge idx RA.1.length with hidx | hidx
      · refine bba j ?_
        rw [hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hidx]
        exact List.getElem_mem hidx
      · exfalso
        rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none hidx] at hj
        exact Bit.noConfusion hj
    · simp only [eval]
      rw [busDen_extract σa w RA.1 hlenA idx, vala]
  | @slice w lo len a iha =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsupp s σ₀ hwf hmem hbnd hcons hcb
    have hlenA : ((compileExpr a).run s).1.length = w := compileExpr_len a hsupp s hwf
    simp only [compileExpr_slice, run_bind, run_pure]
    generalize hGA : (compileExpr a).run s = RA at *
    refine ⟨σa, exa, cca, cba, ?_, moa, eva, ?_⟩
    · apply BusBelow_append _ BusBelow_replicate_zero
      intro j hj
      exact bba j (List.mem_of_mem_drop (List.mem_of_mem_take hj))
    · simp only [eval]
      rw [busDen_slice σa w lo len RA.1 hlenA, vala]
  | @shl w k a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun i hi => (exa i hi).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    have hlenB : ((compileExpr b).run ((compileExpr a).run s).2).1.length = k :=
      compileExpr_len b hsb _ hwb'
    simp only [compileExpr_shl, run_bind, emitShift_fst, emitShift_cells, emitShift_nextId,
               emitShift_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ i, i < RB.2.nextId →
        setRange σb RB.2.nextId w ((busDen σb w RA.1).shiftLeft (busValNat σb RB.1)) i = σb i :=
      fun i hi => setRange_lt σb RB.2.nextId w _ i hi
    have hYval : busDen (setRange σb RB.2.nextId w
          ((busDen σb w RA.1).shiftLeft (busValNat σb RB.1))) w (freshBus RB.2 w)
        = (busDen σb w RA.1).shiftLeft (busValNat σb RB.1) := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w
        ((busDen σb w RA.1).shiftLeft (busValNat σb RB.1))
    have hAval : busDen (setRange σb RB.2.nextId w
          ((busDen σb w RA.1).shiftLeft (busValNat σb RB.1))) w RA.1 = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBnat : busValNat (setRange σb RB.2.nextId w
          ((busDen σb w RA.1).shiftLeft (busValNat σb RB.1))) RB.1 = busValNat σb RB.1 :=
      busValNat_frame _ σb RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w ((busDen σb w RA.1).shiftLeft (busValNat σb RB.1)),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [setRange_lt σb RB.2.nextId w _ i (Nat.lt_of_lt_of_le hi (Nat.le_trans moa mob)),
          exb i (Nat.lt_of_lt_of_le hi moa), exa i hi]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = (busDen _ (freshBus RB.2 w).length RA.1).shiftLeft (busValNat _ RB.1)
        rw [hflen, hYval, hAval, hBnat]
      · exact ConsistentCells_frame cbb (fun i hi => (hframe i hi).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_shiftCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · simp only [eval]
      rw [hYval]
      have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      have hBv : busValNat σb RB.1 = (eval b env).toNat := by
        rw [← valb]; exact (busDen_toNat σb RB.1 k hlenB).symm
      rw [hAv, hBv]
  | @shr w k a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun i hi => (exa i hi).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    have hlenB : ((compileExpr b).run ((compileExpr a).run s).2).1.length = k :=
      compileExpr_len b hsb _ hwb'
    simp only [compileExpr_shr, run_bind, emitShift_fst, emitShift_cells, emitShift_nextId,
               emitShift_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ i, i < RB.2.nextId →
        setRange σb RB.2.nextId w ((busDen σb w RA.1).ushiftRight (busValNat σb RB.1)) i = σb i :=
      fun i hi => setRange_lt σb RB.2.nextId w _ i hi
    have hYval : busDen (setRange σb RB.2.nextId w
          ((busDen σb w RA.1).ushiftRight (busValNat σb RB.1))) w (freshBus RB.2 w)
        = (busDen σb w RA.1).ushiftRight (busValNat σb RB.1) := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w
        ((busDen σb w RA.1).ushiftRight (busValNat σb RB.1))
    have hAval : busDen (setRange σb RB.2.nextId w
          ((busDen σb w RA.1).ushiftRight (busValNat σb RB.1))) w RA.1 = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBnat : busValNat (setRange σb RB.2.nextId w
          ((busDen σb w RA.1).ushiftRight (busValNat σb RB.1))) RB.1 = busValNat σb RB.1 :=
      busValNat_frame _ σb RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w ((busDen σb w RA.1).ushiftRight (busValNat σb RB.1)),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [setRange_lt σb RB.2.nextId w _ i (Nat.lt_of_lt_of_le hi (Nat.le_trans moa mob)),
          exb i (Nat.lt_of_lt_of_le hi moa), exa i hi]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = (busDen _ (freshBus RB.2 w).length RA.1).ushiftRight (busValNat _ RB.1)
        rw [hflen, hYval, hAval, hBnat]
      · exact ConsistentCells_frame cbb (fun i hi => (hframe i hi).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_shiftCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · simp only [eval]
      rw [hYval]
      have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      have hBv : busValNat σb RB.1 = (eval b env).toNat := by
        rw [← valb]; exact (busDen_toNat σb RB.1 k hlenB).symm
      rw [hAv, hBv]
  | @sshr w k a b iha ihb =>
    intro hsupp s σ₀ hwf hmem hbnd hcons hcb
    obtain ⟨hsa, hsb⟩ := hsupp
    obtain ⟨hwa, hwb⟩ := hwf
    obtain ⟨σa, exa, cca, cba, bba, moa, eva, vala⟩ := iha hsa s σ₀ hwa hmem hbnd hcons hcb
    have hwb' : WidthOK ((compileExpr a).run s).2.env b := by rw [eva]; exact hwb
    have hmemb : CEnvOK σa ((compileExpr a).run s).2.env env := by
      rw [eva]; exact CEnvOK_frame hbnd (fun i hi => (exa i hi).symm) hmem
    have hbndb : EnvBounded ((compileExpr a).run s).2.env ((compileExpr a).run s).2.nextId := by
      rw [eva]; exact EnvBounded_mono hbnd moa
    obtain ⟨σb, exb, ccb, cbb, bbb, mob, evb, valb⟩ :=
      ihb hsb ((compileExpr a).run s).2 σa hwb' hmemb hbndb cca cba
    have hlenB : ((compileExpr b).run ((compileExpr a).run s).2).1.length = k :=
      compileExpr_len b hsb _ hwb'
    simp only [compileExpr_sshr, run_bind, emitShift_fst, emitShift_cells, emitShift_nextId,
               emitShift_env]
    generalize hGA : (compileExpr a).run s = RA at *
    generalize hGB : (compileExpr b).run RA.2 = RB at *
    have hframe : ∀ i, i < RB.2.nextId →
        setRange σb RB.2.nextId w ((busDen σb w RA.1).sshiftRight (busValNat σb RB.1)) i = σb i :=
      fun i hi => setRange_lt σb RB.2.nextId w _ i hi
    have hYval : busDen (setRange σb RB.2.nextId w
          ((busDen σb w RA.1).sshiftRight (busValNat σb RB.1))) w (freshBus RB.2 w)
        = (busDen σb w RA.1).sshiftRight (busValNat σb RB.1) := by
      simpa [freshBus] using setRange_get σb RB.2.nextId w
        ((busDen σb w RA.1).sshiftRight (busValNat σb RB.1))
    have hAval : busDen (setRange σb RB.2.nextId w
          ((busDen σb w RA.1).sshiftRight (busValNat σb RB.1))) w RA.1 = busDen σb w RA.1 :=
      busDen_frame _ _ w RA.1 RB.2.nextId (BusBelow_mono bba mob) hframe
    have hBnat : busValNat (setRange σb RB.2.nextId w
          ((busDen σb w RA.1).sshiftRight (busValNat σb RB.1))) RB.1 = busValNat σb RB.1 :=
      busValNat_frame _ σb RB.1 RB.2.nextId bbb hframe
    refine ⟨setRange σb RB.2.nextId w ((busDen σb w RA.1).sshiftRight (busValNat σb RB.1)),
            ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro i hi
      rw [setRange_lt σb RB.2.nextId w _ i (Nat.lt_of_lt_of_le hi (Nat.le_trans moa mob)),
          exb i (Nat.lt_of_lt_of_le hi moa), exa i hi]
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · have hflen : (freshBus RB.2 w).length = w := by simp [freshBus]
        show busDen _ (freshBus RB.2 w).length (freshBus RB.2 w)
             = (busDen _ (freshBus RB.2 w).length RA.1).sshiftRight (busValNat _ RB.1)
        rw [hflen, hYval, hAval, hBnat]
      · exact ConsistentCells_frame cbb (fun i hi => (hframe i hi).symm) ccb c hc
    · intro c hc
      rcases List.mem_cons.1 hc with rfl | hc
      · exact CellBelow_shiftCell (BusBelow_mono bba (Nat.le_trans mob (Nat.le_add_right _ _)))
          (BusBelow_mono bbb (Nat.le_add_right _ _)) (BusBelow_freshBus RB.2 w)
      · exact CellsBounded_mono cbb (Nat.le_add_right _ _) c hc
    · exact BusBelow_freshBus RB.2 w
    · exact Nat.le_trans (Nat.le_trans moa mob) (Nat.le_add_right _ _)
    · rw [evb, eva]
    · simp only [eval]
      rw [hYval]
      have hAv : busDen σb w RA.1 = eval a env := by
        rw [busDen_frame σb σa w RA.1 RA.2.nextId bba exb]; exact vala
      have hBv : busValNat σb RB.1 = (eval b env).toNat := by
        rw [← valb]; exact (busDen_toNat σb RB.1 k hlenB).symm
      rw [hAv, hBv]

/-- Every combinational `Expr` is in the supported fragment. -/
theorem supp_all {w : Nat} (e : Expr w) : Supp e := by
  induction e with
  | const _ => trivial
  | var _ _ => trivial
  | not _ iha => exact iha
  | zext _ _ iha => exact iha
  | sext _ _ iha => exact iha
  | extract _ _ iha => exact iha
  | slice _ _ _ iha => exact iha
  | mux _ _ _ ihs iha ihb => exact ⟨ihs, iha, ihb⟩
  | _ => exact ⟨by assumption, by assumption⟩

/-- **Combinational compiler correctness (M6a).**  For *every* combinational expression `e`, the
    RTLIL produced by `compileExpr` admits a net valuation `σ` under which (a) all emitted cells
    hold and (b) the output bus denotes the denotational meaning `eval e`.  This closes the
    `⟦·⟧` ↔ RTLIL trust gap for the entire combinational `Expr` algebra (all 23 constructors),
    depending only on the standard logical axioms. -/
theorem compile_correct {w : Nat} (e : Expr w) (env : Env) (s : CState) (σ₀ : Nat → Bool)
    (hwf : WidthOK s.env e) (hmem : CEnvOK σ₀ s.env env) (hbnd : EnvBounded s.env s.nextId)
    (hcons : ConsistentCells σ₀ s.cells) (hcb : CellsBounded s.cells s.nextId) :
    ∃ σ : Nat → Bool,
      busDen σ w ((compileExpr e).run s).1 = eval e env ∧
      ConsistentCells σ ((compileExpr e).run s).2.cells := by
  obtain ⟨σ, _, hcc, _, _, _, _, hval⟩ := sound e env (supp_all e) s σ₀ hwf hmem hbnd hcons hcb
  exact ⟨σ, hval, hcc⟩

end LeanRTL.CompilerCorrect
