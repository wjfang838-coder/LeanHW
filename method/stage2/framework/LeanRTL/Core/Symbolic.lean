import LeanRTL.Core.Coverage

/-! Symbolic interpretation of actual LeanRTL data. Choices are universal in a
certificate. Uninitialized registers are not silently initialized to zero.
The full-cycle view and explicit-edge view share expressions and state metadata.
-/
namespace LeanRTL.Symbolic

structure Module where
  core : LeanRTL.Module
  choices : List InPort := []

abbrev Values := List (String × Nat)
abbrev Oracle := String → Nat

def Module.valid (m : Module) : Bool :=
  m.core.wellWidthedb && m.core.checkErrors.isEmpty &&
  m.core.latches.isEmpty && m.core.mems.isEmpty &&
  m.choices.all (fun p => m.core.inputs.any (fun q => p.name == q.name && p.width == q.width)) &&
  (m.choices.map (·.name)).eraseDups == m.choices.map (·.name)

def Module.inputs (m : Module) : List InPort :=
  m.core.inputs.filter fun p => !(m.choices.any (fun q => p.name == q.name))

/-- One active edge per row is valid only for a single, uniformly edged clock.
Per-register clocks and mixed edges must use the explicit event interpreter. -/
def Module.cycleValid (m : Module) : Bool :=
  m.valid && m.core.reset.isNone &&
  (m.core.regs.isEmpty || m.core.clock.isSome) &&
  m.core.regs.all (fun r => r.clockNet.isNone) &&
  (m.core.regs.map (·.negedge)).eraseDups.length <= 1

/-- Control cones cannot contain state feedback or internal nondeterministic
clocks. Such circuits need a delta/event scheduler, not this sampled adapter. -/
def Module.controlsSupported (m : Module) : Bool :=
  let pure := m.core.wires.foldl (fun known w =>
    if w.expr.varRefs.all (fun p => p.1 ∈ known) then w.name :: known else known)
    ((m.inputs ++ m.choices).map (·.name))
  m.core.reset.isNone &&
  (match m.core.clock with | none => true | some n => n ∈ m.inputs.map (·.name)) &&
  m.core.regs.all (fun r =>
    (match r.clockNet with | none => true | some c => c.varRefs.all (fun p => p.1 ∈ pure)) &&
    (match r.asyncReset with | none => true | some (n,_,_) => n ∈ pure) &&
    (match r.asyncLoad with
     | none => true
     | some (n,_,v) => n ∈ pure && v.varRefs.all (fun p => p.1 ∈ pure)))

def Module.initial (m : Module) (o : Oracle) : Values :=
  m.core.regs.map fun r =>
    (r.name, if r.emitInit then r.init.toNat else (BitVec.ofNat r.width (o r.name)).toNat)

def Module.inputEnv (m : Module) (i : Values) (o : Oracle) : Env :=
  fun n => if m.choices.any (fun p => p.name == n) then o n else Env.ofList i n

def Module.environment (m : Module) (s i : Values) (o : Oracle) : Env :=
  evalWires m.core.wires (cycleEnv (Env.ofList s) (m.inputEnv i o) (m.core.regs.map (·.name)))

def active (e : Env) (n : String) (high : Bool) : Bool :=
  ((e n % 2) != 0) == high

/-- Asynchronous controls affect the sampled observation even between edges. -/
def Module.settle (m : Module) (s i : Values) (o : Oracle) : Values :=
  let e := m.environment s i o
  m.core.regs.map fun r =>
    let old := Env.ofList s r.name
    let loaded := match r.asyncLoad with
      | some (n, hi, v) => if active e n hi then (eval v e).toNat else old
      | none => old
    let value := match r.asyncReset with
      | some (n, hi, v) => if active e n hi then v.toNat else loaded
      | none => loaded
    (r.name, value)

def Module.outputs (m : Module) (s i : Values) (o : Oracle) : List (String × Nat × Nat) :=
  let e := m.environment (m.settle s i o) i o
  m.core.outputs.map fun p => (p.name, p.width, (eval p.expr e).toNat)

def Module.next (m : Module) (s i : Values) (o : Oracle) : Values :=
  let e := m.environment (m.settle s i o) i o
  let rst := match m.core.reset with | none => false | some n => active e n true
  let stepped := m.core.regs.map fun r =>
    (r.name, if rst then r.init.toNat else (eval r.next e).toNat)
  m.settle stepped i o

/-- Explicit edge controls use previous and current physical input levels. -/
def Module.edgeNext (m : Module) (s before after : Values) (o : Oracle) : Values :=
  let e0 := m.environment s before o
  let e1 := m.environment (m.settle s after o) after o
  let stepped := m.core.regs.map fun r =>
    let clock (e : Env) := match r.clockNet with
      | some c => (eval c e).toNat != 0
      | none => match m.core.clock with | some n => e n % 2 != 0 | none => false
    let fired := if r.negedge then clock e0 && !clock e1 else !clock e0 && clock e1
    (r.name, if fired then (eval r.next e1).toNat else Env.ofList s r.name)
  m.settle stepped after o

end LeanRTL.Symbolic
