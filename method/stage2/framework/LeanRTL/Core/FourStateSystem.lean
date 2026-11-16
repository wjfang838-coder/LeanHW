import LeanRTL.Core.FourStateNetlist
import LeanRTL.Core.FourStateClocked

/-! A resolved combinational network connected to fixed-read NBA processes.
Hierarchy is elaborated by the frontend into uniquely named signals. External
drives remain distinct from physical inout observations. -/
namespace LeanRTL.FourState.Resolved

structure System where
  network : Netlist
  states : List LeanRTL.InPort
  processes : List NBA.Process
  portOrder : List String
  signedPorts : List String := []
  scalarPorts : List String := []

def System.inputs (s : System) : List LeanRTL.InPort :=
  s.network.inputs.filter (fun p => !(s.states.any (fun r => r.name == p.name)))

/-- The already defined clocked model with resolution lowered to expressions. -/
def System.lower (s : System) : NBA.Clocked :=
  let inputs := s.inputs ++ s.network.nets.filterMap (fun n => n.port.map (fun _ =>
    {name := n.externalName, width := n.width}))
  { name := s.network.name, inputs, states := s.states,
    wires := s.network.lower.wires, outputs := s.network.outputWires,
    processes := s.processes,
    portOrder := inputs.map (·.name) ++ s.network.outputWires.map (·.name) }

def System.valid (s : System) : Bool :=
  let names := s.inputs.map (·.name) ++ s.network.outputs.map (·.name) ++ s.network.nets.filterMap (·.port)
  let widths := s.inputs.map (fun p => (p.name,p.width)) ++ s.network.outputWires.map (fun p => (p.name,p.width))
  s.network.valid && s.lower.valid &&
    s.portOrder.eraseDups == s.portOrder && s.portOrder.length == names.length && s.portOrder.all names.contains &&
    s.signedPorts.eraseDups == s.signedPorts && s.signedPorts.all names.contains &&
    s.scalarPorts.eraseDups == s.scalarPorts && s.scalarPorts.all (fun n => widths.lookup n == some 1)

def System.initial (s : System) : NBA.Snapshot := s.lower.initial

def System.wireSnapshot (s : System) (state : NBA.Snapshot) (input : Env) : NBA.Snapshot :=
  s.network.wireValues (valuesEnv state input) ++ state

theorem system_wire_snapshot_correct (s : System) (state : NBA.Snapshot) (input : Env) :
    s.lower.wireSnapshot state input = s.wireSnapshot state input := by
  change s.network.lower.wireValues (valuesEnv state input) ++ state = _
  rw [wire_values_correct]
  rfl

def System.step (s : System) (state : NBA.Snapshot) (before after : Env) : NBA.Snapshot :=
  let values := s.wireSnapshot state after
  let read := valuesEnv values after
  s.states.map fun (reg : LeanRTL.InPort) =>
    let old : Value reg.width := ⟨fun i => read reg.name i.val⟩
    let next := match s.processes.find? (fun p => reg.name ∈ p.targets) with
      | some p => if p.fired before after then NBA.execute p.body reg.name read old else old
      | none => old
    (reg.name, (List.finRange reg.width).map next)

theorem system_step_correct (s : System) (state : NBA.Snapshot) (before after : Env) :
    s.lower.step state before after = s.step state before after := by
  unfold NBA.Clocked.step System.step
  rw [system_wire_snapshot_correct]
  rfl

def System.observe (s : System) (state : NBA.Snapshot) (input : Env) : List (String × String) :=
  let values := s.wireSnapshot state input
  let read := valuesEnv values input
  s.network.outputWires.map fun o => (o.name, renderValue (eval o.expr read))

theorem system_observe_correct (s : System) (state : NBA.Snapshot) (input : Env) :
    s.lower.observe state input = s.observe state input := by
  unfold NBA.Clocked.observe System.observe
  rw [system_wire_snapshot_correct]
  rfl

/-- Emit physical nets and registers directly; state never becomes an input port. -/
def System.emit (s : System) : String := Id.run do
  let signed (n : String) := if n ∈ s.signedPorts then "signed " else ""
  let range (n : String) (w : Nat) := if n ∈ s.scalarPorts then "" else s!"[{w-1}:0] "
  let mut lines := [s!"module {Verilog.escV s.network.name} ({String.intercalate ", " (s.portOrder.map Verilog.escV)});"]
  for p in s.inputs do
    lines := lines ++ [s!"input wire {signed p.name}{range p.name p.width}{Verilog.escV p.name};"]
  for p in s.network.outputs do
    lines := lines ++ [s!"output wire {signed p.name}{range p.name p.width}{Verilog.escV p.name};"]
  for n in s.network.nets do
    if let some p := n.port then
      lines := lines ++ [s!"inout wire {signed p}{range p n.width}{Verilog.escV p};"]
  for p in s.states do
    lines := lines ++ [s!"reg [{p.width-1}:0] {Verilog.escV p.name};"]
  for node in s.network.nodes do
    let w := node.lower
    lines := lines ++ [s!"wire [{w.width-1}:0] {Verilog.escV w.name};"]
    match node with
    | .wire w => lines := lines ++ [s!"assign {Verilog.escV w.name} = {Timed.inlineExpr w.expr};"]
    | .net n =>
      if let some port := n.port then
        lines := lines ++ [s!"assign {Verilog.escV n.name} = {Verilog.escV port};"]
      for driver in n.drivers do
        lines := lines ++ [s!"assign {Verilog.escV (n.port.getD n.name)} = {Timed.inlineExpr driver};"]
  for w in s.network.outputs do
    lines := lines ++ [s!"assign {Verilog.escV w.name} = {Timed.inlineExpr w.expr};"]
  for p in s.processes do
    let events := p.events.map fun e => s!"{if e.positive then "posedge" else "negedge"} {Verilog.escV e.name}"
    lines := lines ++ [s!"always @({String.intercalate " or " events}) {NBA.emitStatement p.body}"]
  return String.intercalate "\n" (lines ++ ["endmodule", ""])

end LeanRTL.FourState.Resolved
