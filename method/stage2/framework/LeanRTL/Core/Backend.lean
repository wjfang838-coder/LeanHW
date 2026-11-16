import Lean.Data.Json
import LeanRTL.Core.Syntax
/-!
# RTLIL JSON model and emitter

A small Lean model of the subset of Yosys' RTLIL-JSON format that LeanRTL produces,
plus a renderer to `Lean.Json`.  The shape here was checked against real
`yosys -p "... write_json"` output:

* net signals are JSON integers (we allocate ids starting at 2);
* constant bits are the JSON *strings* `"0" "1" "x" "z"`;
* cell/port widths are 32-bit binary strings (e.g. width 1 -> `"00...0001"`).
-/

namespace LeanRTL.Backend

open Lean (Json)

/-- A single physical bit: either a wire (net id) or a constant logic level. -/
inductive Bit where
  | net : Nat → Bit
  | zero | one | x | z
  deriving Repr, DecidableEq, Inhabited

/-- A bus is a list of bits, **LSB first** (Yosys convention). -/
abbrev Bus := List Bit

def Bit.toJson : Bit → Json
  | .net n => Json.num (.fromNat n)
  | .zero  => Json.str "0"
  | .one   => Json.str "1"
  | .x     => Json.str "x"
  | .z     => Json.str "z"

inductive Dir where
  | input | output | inout
  deriving Repr, DecidableEq, Inhabited

def Dir.toStr : Dir → String
  | .input => "input" | .output => "output" | .inout => "inout"

structure Port where
  name : String
  dir  : Dir
  bits : Bus
  deriving Repr, Inhabited

structure Cell where
  name           : String
  type           : String
  parameters     : List (String × String) := []
  portDirections : List (String × Dir)    := []
  connections    : List (String × Bus)    := []
  hideName       : Bool := true
  deriving Repr, Inhabited

structure NetName where
  name     : String
  bits     : Bus
  hideName : Bool := false
  /-- RTLIL wire attributes as `(name, value)` pairs, e.g. `("init", "00000000")` for a
      power-on value.  Values are RTLIL constant bit-strings (MSB first).  Default `[]` keeps
      every existing `NetName` literal unchanged. -/
  attrs    : List (String × String) := []
  deriving Repr, Inhabited

structure Module where
  name     : String
  ports    : List Port
  cells    : List Cell    := []
  netnames : List NetName := []
  portLayouts : List PortLayout := []
  deriving Repr, Inhabited

structure Design where
  modules : List Module
  deriving Repr, Inhabited

/-- Encode a natural number as a 32-bit binary string, MSB first (the RTLIL param format). -/
def binStr32 (n : Nat) : String :=
  String.ofList (((List.range 32).reverse).map (fun i => if n.testBit i then '1' else '0'))

/-! ## Rendering to `Lean.Json` -/

def busJson (b : Bus) : Json := Json.arr (b.map Bit.toJson |>.toArray)

def boolNum (b : Bool) : Json := Json.num (.fromNat (if b then 1 else 0))

def layoutFields (layouts : List PortLayout) (name : String) : List (String × Json) :=
  match layouts.find? (fun p => p.name == name) with
  | none => []
  | some p => [("signed", boolNum p.signed), ("offset", Json.num (.fromInt p.offset)), ("upto", boolNum p.upto)]

def portJson (p : Port) (layouts : List PortLayout := []) : String × Json :=
  (p.name, Json.mkObj ([("direction", Json.str p.dir.toStr), ("bits", busJson p.bits)] ++ layoutFields layouts p.name))

def cellJson (c : Cell) : String × Json :=
  (c.name, Json.mkObj [
    ("hide_name", boolNum c.hideName),
    ("type", Json.str c.type),
    ("parameters", Json.mkObj (c.parameters.map (fun (k, v) => (k, Json.str v)))),
    ("port_directions", Json.mkObj (c.portDirections.map (fun (k, d) => (k, Json.str d.toStr)))),
    ("connections", Json.mkObj (c.connections.map (fun (k, b) => (k, busJson b))))
  ])

def netnameJson (n : NetName) (layouts : List PortLayout := []) : String × Json :=
  (n.name, Json.mkObj ([("hide_name", boolNum n.hideName), ("bits", busJson n.bits),
    ("attributes", Json.mkObj (n.attrs.map (fun (k, v) => (k, Json.str v))))] ++ layoutFields layouts n.name))

def moduleJson (m : Module) : String × Json :=
  (m.name, Json.mkObj [
    ("attributes", Json.mkObj []),
    ("ports", Json.mkObj (m.ports.map (fun p => portJson p m.portLayouts))),
    ("cells", Json.mkObj (m.cells.map cellJson)),
    ("netnames", Json.mkObj (m.netnames.map (fun n => netnameJson n m.portLayouts)))
  ])

def Design.toJson (d : Design) : Json :=
  Json.mkObj [
    ("creator", Json.str "LeanRTL"),
    ("modules", Json.mkObj (d.modules.map moduleJson))
  ]

/-! ## Order-preserving renderer

`Lean.Json.mkObj` stores object fields in a key-sorted `RBNode`, so `Json.pretty`/`compress`
emit keys alphabetically — which **destroys the port declaration order**.  Yosys reads a
module's port order from the `ports` object order, and many testbenches instantiate the DUT
*positionally* (`dut u(clk, rst, a, b, c)`), so a sorted `module dut(a, b, c, clk, rst)` binds
the wrong nets.  The renderer below emits every object in **insertion order** (leaf arrays and
scalars still go through `Json.compress`, which preserves array order and escapes correctly),
so the emitted RTLIL keeps the declaration order the compiler built. -/

private def escKey (s : String) : String := (Json.str s).compress

/-- Render an ordered association list of pre-rendered field strings as a JSON object. -/
private def objOrd (fields : List (String × String)) : String :=
  "{" ++ String.intercalate "," (fields.map (fun (k, v) => escKey k ++ ":" ++ v)) ++ "}"

private def portOrd (layouts : List PortLayout) (p : Port) : String × String :=
  (p.name, objOrd ([("direction", escKey p.dir.toStr), ("bits", (busJson p.bits).compress)] ++
    (layoutFields layouts p.name).map (fun (k, v) => (k, v.compress))))

private def cellOrd (c : Cell) : String × String :=
  (c.name, objOrd [
    ("hide_name", (boolNum c.hideName).compress),
    ("type", escKey c.type),
    ("parameters", objOrd (c.parameters.map (fun (k, v) => (k, escKey v)))),
    ("port_directions", objOrd (c.portDirections.map (fun (k, dir) => (k, escKey dir.toStr)))),
    ("connections", objOrd (c.connections.map (fun (k, b) => (k, (busJson b).compress))))
  ])

private def netnameOrd (layouts : List PortLayout) (n : NetName) : String × String :=
  (n.name, objOrd ([("hide_name", (boolNum n.hideName).compress), ("bits", (busJson n.bits).compress),
    ("attributes", objOrd (n.attrs.map (fun (k, v) => (k, escKey v))))] ++
    (layoutFields layouts n.name).map (fun (k, v) => (k, v.compress))))

private def moduleOrd (m : Module) : String × String :=
  (m.name, objOrd [
    ("attributes", "{}"),
    ("ports", objOrd (m.ports.map (portOrd m.portLayouts))),
    ("cells", objOrd (m.cells.map cellOrd)),
    ("netnames", objOrd (m.netnames.map (netnameOrd m.portLayouts)))
  ])

/-- RTLIL JSON ready for `yosys read_json`, with **port/cell/net order preserved** (unlike a
    key-sorting `Json.pretty`), so positionally-instantiated DUTs bind the right nets. -/
def Design.render (d : Design) : String :=
  objOrd [("creator", escKey "LeanRTL"), ("modules", objOrd (d.modules.map moduleOrd))]

end LeanRTL.Backend
