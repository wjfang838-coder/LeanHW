import LeanRTL.Core.Coverage
import Std.Data.TreeMap.Lemmas
namespace LeanRTL.CheckWidth
def widthOKbMap (ws : Std.TreeMap String Nat) : {w : Nat} → Expr w → Bool
  | _, .const _      => true
  | _, .var n w      => ws[n]? == some w
  | _, .not a        => widthOKbMap ws a
  | _, .and a b      => widthOKbMap ws a && widthOKbMap ws b
  | _, .or a b       => widthOKbMap ws a && widthOKbMap ws b
  | _, .xor a b      => widthOKbMap ws a && widthOKbMap ws b
  | _, .add a b      => widthOKbMap ws a && widthOKbMap ws b
  | _, .sub a b      => widthOKbMap ws a && widthOKbMap ws b
  | _, .mul a b      => widthOKbMap ws a && widthOKbMap ws b
  | _, .shl a b      => widthOKbMap ws a && widthOKbMap ws b
  | _, .shr a b      => widthOKbMap ws a && widthOKbMap ws b
  | _, .sshr a b     => widthOKbMap ws a && widthOKbMap ws b
  | _, .udiv a b     => widthOKbMap ws a && widthOKbMap ws b
  | _, .umod a b     => widthOKbMap ws a && widthOKbMap ws b
  | _, .eq a b       => widthOKbMap ws a && widthOKbMap ws b
  | _, .ult a b      => widthOKbMap ws a && widthOKbMap ws b
  | _, .slt a b      => widthOKbMap ws a && widthOKbMap ws b
  | _, .mux s a b    => widthOKbMap ws s && widthOKbMap ws a && widthOKbMap ws b
  | _, .concat a b   => widthOKbMap ws a && widthOKbMap ws b
  | _, .zext _ a     => widthOKbMap ws a
  | _, .sext _ a     => widthOKbMap ws a
  | _, .extract _ a  => widthOKbMap ws a
  | _, .slice _ _ a  => widthOKbMap ws a


def LookupAgrees (m : Std.TreeMap String Nat) (ws : List (String × Nat)) : Prop :=
  ∀ n, m[n]? = ws.lookup n

theorem agrees_insert {m : Std.TreeMap String Nat} {ws : List (String × Nat)}
    (h : LookupAgrees m ws) (name : String) (width : Nat) :
    LookupAgrees (m.insert name width) ((name, width) :: ws) := by
  intro n
  by_cases hn : name = n
  · subst n; simp
  · have hc : compare name n ≠ .eq := by intro he; exact hn (Std.LawfulEqCmp.eq_of_compare he)
    have hb : (n == name) = false := by simp [Ne.symm hn]
    simp [Std.TreeMap.getElem?_insert, List.lookup_cons, h n, hc, hb]

def widthMap (ws : List (String × Nat)) : Std.TreeMap String Nat :=
  ws.foldr (fun p acc => acc.insert p.1 p.2) {}

theorem widthMap_agrees (ws : List (String × Nat)) : LookupAgrees (widthMap ws) ws := by
  induction ws with
  | nil => intro n; simp [widthMap, List.lookup]
  | cons p ps ih => exact agrees_insert ih p.1 p.2

theorem widthOKbMap_eq {m : Std.TreeMap String Nat} {ws : List (String × Nat)}
    (h : LookupAgrees m ws) {w : Nat} (e : Expr w) : widthOKbMap m e = widthOKb ws e := by
  induction e <;> simp_all [widthOKbMap, widthOKb, LookupAgrees]

def wiresOKbMap (m : Std.TreeMap String Nat) : List Wire → Bool
  | [] => true
  | w :: rest => widthOKbMap m w.expr && wiresOKbMap (m.insert w.name w.width) rest

theorem wiresOKbMap_eq (wires : List Wire) {m : Std.TreeMap String Nat} {ws : List (String × Nat)}
    (h : LookupAgrees m ws) : wiresOKbMap m wires = wiresOKb ws wires := by
  induction wires generalizing m ws with
  | nil => rfl
  | cons w rest ih => simp only [wiresOKbMap, wiresOKb, widthOKbMap_eq h, ih (agrees_insert h w.name w.width)]

def wellWidthedbMap (m : Module) : Bool :=
  let base := widthMap (setupWidths m)
  let full := widthMap (fullWidths m)
  wiresOKbMap base m.wires && m.regs.all (fun r => widthOKbMap full r.next)
    && m.outputs.all (fun o => widthOKbMap full o.expr)

theorem wellWidthedbMap_eq (m : Module) : wellWidthedbMap m = m.wellWidthedb := by
  simp [wellWidthedbMap, Module.wellWidthedb, wiresOKbMap_eq _ (widthMap_agrees _), widthOKbMap_eq (widthMap_agrees _)]

def moduleChecksbMap (m : Module) : Bool :=
  m.regs.all (fun r => r.asyncReset.isNone)
    && m.regs.all (fun r => r.asyncLoad.isNone)
    && m.regs.all (fun r => r.clockNet.isNone)
    && m.mems.isEmpty
    && wellWidthedbMap m

theorem moduleChecksbMap_eq (m : Module) : moduleChecksbMap m = moduleChecksb m := by
  simp [moduleChecksbMap, moduleChecksb, wellWidthedbMap_eq, Module.wellWidthedb, Bool.and_assoc]
end LeanRTL.CheckWidth

