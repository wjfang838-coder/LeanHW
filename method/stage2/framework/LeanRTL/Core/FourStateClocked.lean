import LeanRTL.Core.FourStateNBA
import LeanRTL.Core.FourStateTimed

namespace LeanRTL.FourState.NBA

structure Edge where
  name : String
  positive : Bool

def posedge : Bit → Bit → Bool
  | .zero, .one | .zero, .x | .zero, .z | .x, .one | .z, .one => true
  | _, _ => false

def negedge : Bit → Bit → Bool
  | .one, .zero | .one, .x | .one, .z | .x, .zero | .z, .zero => true
  | _, _ => false

structure Process where
  events : List Edge
  targets : List String
  body : Stmt

def Process.fired (p : Process) (before after : Env) : Bool :=
  p.events.any fun edge =>
    (if edge.positive then posedge else negedge) (before edge.name 0) (after edge.name 0)

structure Clocked where
  name : String
  inputs : List LeanRTL.InPort
  states : List LeanRTL.InPort
  wires : List FourState.Wire
  outputs : List FourState.Wire
  processes : List Process
  portOrder : List String
  signedPorts : List String := []

abbrev Snapshot := List (String × List Bit)

def Clocked.combinational (m : Clocked) : FourState.Module :=
  { name := m.name, inputs := m.inputs ++ m.states, wires := m.wires, outputs := m.outputs }

def Clocked.valid (m : Clocked) : Bool :=
  let states := m.states.map (fun s => (s.name,s.width))
  let inputs := m.inputs.map (fun s => (s.name,s.width))
  let names := m.inputs.map (·.name) ++ m.outputs.map (·.name)
  m.combinational.valid &&
    m.portOrder.length == names.length && m.portOrder.eraseDups == m.portOrder &&
    m.portOrder.all (fun n => n ∈ names) &&
    m.signedPorts.eraseDups == m.signedPorts && m.signedPorts.all (fun n => n ∈ names) &&
    m.states.all (fun s => (m.processes.filter (fun p => s.name ∈ p.targets)).length == 1) &&
    m.processes.all (fun p => !p.events.isEmpty && p.targets.eraseDups == p.targets &&
      (writeNames p.body).all (fun n => n ∈ p.targets) &&
      p.targets.all (fun n => states.lookup n |>.isSome) &&
      p.events.all (fun e => inputs.lookup e.name == some 1) &&
      stmtValid (Source.allScope m.combinational) states p.body)

def Clocked.initial (m : Clocked) : Snapshot :=
  m.states.map fun s => (s.name, List.replicate s.width .x)

def Clocked.wireSnapshot (m : Clocked) (state : Snapshot) (input : Env) : Snapshot :=
  let read := valuesEnv state input
  m.combinational.wireValues read ++ state

/-- One externally supplied input transition, followed by settled NBA commit.
Only direct input edge controls are accepted by the frontend. Each state belongs
to one process; all processes read the same pre-commit state. -/
def Clocked.step (m : Clocked) (state : Snapshot) (before after : Env) : Snapshot :=
  let values := m.wireSnapshot state after
  let read := valuesEnv values after
  m.states.map fun (s : LeanRTL.InPort) =>
    let old : Value s.width := ⟨fun i => read s.name i.val⟩
    let next := match m.processes.find? (fun p => s.name ∈ p.targets) with
      | some p => if p.fired before after then execute p.body s.name read old else old
      | none => old
    (s.name, (List.finRange s.width).map next)

def Clocked.observe (m : Clocked) (state : Snapshot) (input : Env) : List (String × String) :=
  let values := m.wireSnapshot state input
  let read := valuesEnv values input
  m.outputs.map fun o => (o.name, renderValue (eval o.expr read))

mutual
  partial def emitStatement (stmt : Stmt) : String :=
    match stmt with
    | .skip => ";"
    | @Stmt.write k target lo rhs =>
      s!"{Verilog.escV target}[{lo+k-1}:{lo}] <= {Timed.inlineExpr rhs};"
    | .seq a b => s!"begin\n{emitStatement a}\n{emitStatement b}\nend"
    | .ite condition yes no => s!"if ({Timed.inlineExpr condition}) {emitStatement yes} else {emitStatement no}"
    | .cases selector arms => s!"case ({Timed.inlineExpr selector})\n{emitArms arms}\nendcase"
  partial def emitArms {k : Nat} (arms : Arms k) : String :=
    match arms with
    | .default stmt => s!"default: {emitStatement stmt}"
    | .arm labels stmt rest =>
      s!"{String.intercalate ", " (labels.map Timed.inlineExpr)}: {emitStatement stmt}\n{emitArms rest}"
end

def Clocked.emit (m : Clocked) : String := Id.run do
  let mut lines := [s!"module {Verilog.escV m.name} ({String.intercalate ", " (m.portOrder.map Verilog.escV)});"]
  for p in m.inputs do
    lines := lines ++ [s!"input wire {if p.name ∈ m.signedPorts then "signed " else ""}[{p.width-1}:0] {Verilog.escV p.name};"]
  for p in m.outputs do
    lines := lines ++ [s!"output wire {if p.name ∈ m.signedPorts then "signed " else ""}[{p.width-1}:0] {Verilog.escV p.name};"]
  for p in m.states do
    lines := lines ++ [s!"reg [{p.width-1}:0] {Verilog.escV p.name};"]
  for p in m.wires do
    lines := lines ++ [s!"wire [{p.width-1}:0] {Verilog.escV p.name};",
      s!"assign {Verilog.escV p.name} = {Timed.inlineExpr p.expr};"]
  for p in m.outputs do
    lines := lines ++ [s!"assign {Verilog.escV p.name} = {Timed.inlineExpr p.expr};"]
  for p in m.processes do
    let events := p.events.map fun e => s!"{if e.positive then "posedge" else "negedge"} {Verilog.escV e.name}"
    lines := lines ++ [s!"always @({String.intercalate " or " events}) {emitStatement p.body}"]
  return String.intercalate "\n" (lines ++ ["endmodule", ""])

end LeanRTL.FourState.NBA
