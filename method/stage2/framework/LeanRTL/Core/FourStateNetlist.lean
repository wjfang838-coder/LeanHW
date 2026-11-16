import LeanRTL.Core.FourStateResolved

namespace LeanRTL.FourState.Resolved

structure Net where
  name : String
  width : Nat
  port : Option String := none
  drivers : List (Expr width)

inductive Node where
  | wire : Wire → Node
  | net : Net → Node

def Net.externalName (n : Net) : String := "__external_" ++ n.port.getD n.name

def Net.base (n : Net) : Expr n.width :=
  if n.port.isSome then .var n.externalName n.width else .fill .z

def Net.lower (n : Net) : Wire :=
  { name := n.name, width := n.width, expr := n.drivers.foldl resolveExpr n.base }

def Net.eval (n : Net) (env : Env) : Value n.width :=
  n.drivers.foldl (fun v e => resolveValue v (FourState.eval e env)) (FourState.eval n.base env)

def Node.lower : Node → Wire
  | .wire w => w
  | .net n => n.lower

def Node.eval (n : Node) (env : Env) : Value n.lower.width :=
  match n with
  | .wire w => FourState.eval w.expr env
  | .net n => n.eval env

structure Netlist where
  name : String
  inputs : List LeanRTL.InPort
  nodes : List Node
  outputs : List Wire
  portOrder : List String := []

def Netlist.nets (m : Netlist) : List Net :=
  m.nodes.filterMap (fun n => match n with | .net n => some n | _ => none)

def Netlist.outputWires (m : Netlist) : List Wire :=
  m.outputs ++ m.nets.filterMap (fun n => n.port.map (fun port =>
    {name := port, width := n.width, expr := .var n.name n.width}))

def Netlist.lower (m : Netlist) : FourState.Module :=
  { name := m.name, inputs := m.inputs ++ m.nets.filterMap (fun n => n.port.map (fun _ =>
      {name := n.externalName, width := n.width})),
    wires := m.nodes.map Node.lower, outputs := m.outputWires }

def Netlist.portNames (m : Netlist) : List String :=
  m.inputs.map (·.name) ++ m.outputs.map (·.name) ++ m.nets.filterMap (·.port)

def Netlist.valid (m : Netlist) : Bool := m.lower.valid &&
  (m.portOrder.isEmpty || (m.portOrder.length == m.portNames.length &&
    m.portOrder.eraseDups.length == m.portOrder.length && m.portOrder.all m.portNames.contains))

def Node.step (input : Env) (values : List (String × List Bit)) (n : Node) :=
  (n.lower.name, (List.finRange n.lower.width).map (n.eval (valuesEnv values input))) :: values

def Netlist.wireValues (m : Netlist) (input : Env) := m.nodes.foldl (Node.step input) []

def Netlist.eval (m : Netlist) (input : Env) : List (String × String) :=
  let env := valuesEnv (m.wireValues input) input
  m.outputWires.map (fun w => (w.name, renderValue (FourState.eval w.expr env)))

theorem fold_resolution_correct {w : Nat} (drivers : List (Expr w)) (base : Expr w) (env : Env) :
    FourState.eval (drivers.foldl resolveExpr base) env =
      drivers.foldl (fun v e => resolveValue v (FourState.eval e env)) (FourState.eval base env) := by
  induction drivers generalizing base with
  | nil => rfl
  | cons d ds ih => simp only [List.foldl_cons, ih, resolve_expr_correct]

theorem node_correct (n : Node) (env : Env) : FourState.eval n.lower.expr env = n.eval env := by
  cases n with
  | wire w => rfl
  | net n => exact fold_resolution_correct n.drivers n.base env

theorem wire_values_correct (m : Netlist) (input : Env) : m.lower.wireValues input = m.wireValues input := by
  simp only [FourState.Module.wireValues, Netlist.lower, Netlist.wireValues, List.foldl_map]
  congr 1
  funext values n
  simp only [Function.comp_def, Node.step, node_correct]

theorem netlist_correct (m : Netlist) (input : Env) : m.lower.eval input = m.eval input := by
  simp only [FourState.Module.eval, Netlist.eval, wire_values_correct]
  rfl

theorem encoded_netlist_correct (m : Netlist) (hv : Encoding.encodingValid m.lower = true)
    (env : LeanRTL.Env) :
    Encoding.decodeOutputPairs m.lower.outputs
      ((Encoding.module m.lower).outputs?eval (fun _ => 0) env) =
      some (m.eval (Encoding.decodedEnv env)) := by
  rw [Encoding.module_correct_decoded m.lower hv env, netlist_correct]

/-- Physical wire drivers remain separate HDL assignments; input values supplied
under externalName are the external drive, not an already resolved input wire. -/
def emit (m : Netlist) : String := Id.run do
  let used := m.name :: (m.inputs.map (·.name) ++ m.outputWires.map (·.name) ++ m.nodes.map (·.lower.name))
  let pfx := String.ofList (List.replicate (1 + (used.map String.length).foldl max 0) '_')
  let mut state : Nat × List (String × Nat × String) := (0, [])
  let mut assignments : List String := []
  for node in m.nodes do
    match node with
    | .wire w =>
      let (rhs, next) := (Verilog.emitCore pfx w.expr).run state
      state := next
      assignments := assignments ++ [s!"  assign {Verilog.escV w.name} = {rhs};"]
    | .net n =>
      if let some port := n.port then
        assignments := assignments ++ [s!"  assign {Verilog.escV n.name} = {Verilog.escV port};"]
      for driver in n.drivers do
        let (rhs, next) := (Verilog.emitCore pfx driver).run state
        state := next
        assignments := assignments ++ [s!"  assign {Verilog.escV (n.port.getD n.name)} = {rhs};"]
  for w in m.outputs do
    let (rhs, next) := (Verilog.emitCore pfx w.expr).run state
    state := next
    assignments := assignments ++ [s!"  assign {Verilog.escV w.name} = {rhs};"]
  let ports := m.inputs.map (fun p => (p.name, s!"input wire {Verilog.rangeC p.width}{Verilog.escV p.name}")) ++
    m.outputs.map (fun p => (p.name, s!"output wire {Verilog.rangeC p.width}{Verilog.escV p.name}")) ++
    m.nets.filterMap (fun n => n.port.map (fun p => (p, s!"inout wire {Verilog.rangeC n.width}{Verilog.escV p}")))
  let ordered := if m.portOrder.isEmpty then ports.map (·.2) else
    m.portOrder.map (fun name => (ports.lookup name).getD "")
  let decls := m.nodes.map (fun n => s!"  wire {Verilog.rangeC n.lower.width}{Verilog.escV n.lower.name};")
  let temps := state.2.reverse.map (fun (n,w,rhs) => s!"  wire {Verilog.rangeC w}{n} = {rhs};")
  return String.intercalate "\n" ([s!"module {Verilog.escV m.name} (", String.intercalate ",\n" ordered, ");"] ++
    decls ++ temps ++ assignments ++ ["endmodule", ""])

end LeanRTL.FourState.Resolved
