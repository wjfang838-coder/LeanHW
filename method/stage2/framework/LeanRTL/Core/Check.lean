import LeanRTL.Core.Syntax
import Std.Data.TreeSet.Basic
import Std.Data.TreeMap.Lemmas
/-!
# Module well-formedness checker (name / width / wire-order lint)

The compiler is total: an unbound `var` silently compiles to a *floating* net, a
wrongly-widthed `var` silently produces a width-mismatched bus, and a wire referencing a
*later* wire silently evaluates against the outer environment (usually 0).  All three are
authoring footguns that used to surface only at layer 5/7 (or worse, not at all).

`Module.checkErrors` finds them at extraction time and names them precisely, so the CLI can
refuse to emit a netlist for a malformed module.  Purely additive — nothing in the proven
pipeline changes; this is a lint in front of it.
-/

namespace LeanRTL

/-- Every `var` reference in an expression, with the width the expression demands. -/
def Expr.varRefs : {w : Nat} → Expr w → List (String × Nat)
  | _, .const _      => []
  | _, .var n w      => [(n, w)]
  | _, .not a        => a.varRefs
  | _, .and a b      => a.varRefs ++ b.varRefs
  | _, .or a b       => a.varRefs ++ b.varRefs
  | _, .xor a b      => a.varRefs ++ b.varRefs
  | _, .add a b      => a.varRefs ++ b.varRefs
  | _, .sub a b      => a.varRefs ++ b.varRefs
  | _, .mul a b      => a.varRefs ++ b.varRefs
  | _, .shl a b      => a.varRefs ++ b.varRefs
  | _, .shr a b      => a.varRefs ++ b.varRefs
  | _, .sshr a b     => a.varRefs ++ b.varRefs
  | _, .udiv a b     => a.varRefs ++ b.varRefs
  | _, .umod a b     => a.varRefs ++ b.varRefs
  | _, .eq a b       => a.varRefs ++ b.varRefs
  | _, .ult a b      => a.varRefs ++ b.varRefs
  | _, .slt a b      => a.varRefs ++ b.varRefs
  | _, .mux s a b    => s.varRefs ++ a.varRefs ++ b.varRefs
  | _, .concat a b   => a.varRefs ++ b.varRefs
  | _, .zext _ a     => a.varRefs
  | _, .sext _ a     => a.varRefs
  | _, .extract _ a  => a.varRefs
  | _, .slice _ _ a  => a.varRefs

/-- Check one expression's references against a scope of `(name, width)` bindings. -/
private def checkExpr (scope : List (String × Nat)) (ctx : String) {w : Nat} (e : Expr w) :
    List String :=
  e.varRefs.filterMap fun (n, wid) =>
    match scope.lookup n with
    | none => some s!"{ctx}: reference to unknown signal '{n}' (would compile to a floating net)"
    | some dw =>
      if dw = wid then none
      else some s!"{ctx}: '{n}' referenced at width {wid} but declared at width {dw}"

private def dupErrorsGo (seen : Std.TreeSet String) : List String → List String
  | [] => []
  | n :: ns =>
    if seen.contains n then s!"duplicate signal name '{n}'" :: dupErrorsGo seen ns
    else dupErrorsGo (seen.insert n) ns

private def dupErrors (names : List String) : List String := dupErrorsGo {} names

/-- Declarations available before checking combinational wires. -/
def Module.baseNameWidths (m : Module) : List (String × Nat) :=
  (m.inputs.map (fun p => (p.name, p.width)) ++ m.regs.map (fun r => (r.name, r.width))
    ++ m.latches.map (fun l => (l.name, l.width))
    ++ m.mems.flatMap (fun mem => mem.reads.map (fun rd => (rd.out, mem.dataWidth)))).reverse

/-- All declared signal widths, with the most recent wire first. -/
def Module.allNameWidths (m : Module) : List (String × Nat) :=
  m.wires.foldl (fun acc wr => (wr.name, wr.width) :: acc) m.baseNameWidths

private def checkWireNames (scope : List (String × Nat)) : List Wire → List String
  | [] => []
  | wr :: rest => checkExpr scope s!"wire '{wr.name}'" wr.expr ++
      checkWireNames ((wr.name, wr.width) :: scope) rest

private def checkControl (scope : List (String × Nat)) (context net : String) : List String :=
  match scope.lookup net with
  | some 1 => []
  | some width => [s!"{context}: '{net}' has width {width} (need 1)"]
  | none => [s!"{context}: '{net}' is not a known signal"]

private def checkRegNames (scope : List (String × Nat)) (r : Reg) : List String :=
  checkExpr scope s!"reg '{r.name}'.next" r.next ++
  (match r.asyncReset with
   | some (net, _, _) => checkControl scope s!"reg '{r.name}' asyncReset" net
   | none => []) ++
  (if r.asyncReset.isSome && r.asyncLoad.isSome then
    [s!"reg '{r.name}': asyncReset and asyncLoad on the same register is unsupported"] else []) ++
  (match r.clockNet with
   | some e => checkExpr scope s!"reg '{r.name}'.clockNet" e
   | none => []) ++
  (match r.asyncLoad with
   | some (net, _, value) => checkExpr scope s!"reg '{r.name}'.asyncLoad" value ++
       checkControl scope s!"reg '{r.name}' asyncLoad" net
   | none => [])

/-- All well-formedness errors of a module (empty ⇔ well-formed):
    * every `var` reference — in wires, register next-states, `asyncLoad` values, `clockNet`
      expressions, latch enable/data cones, outputs, and memory port cones — resolves to an
      input / register / latch / wire / mem-read-out of the SAME width;
    * each wire references only inputs, registers, latches, and *earlier* wires (topological order);
    * no duplicate signal names across inputs / registers / latches / wires / mem-read-outs;
    * each register's `asyncReset` / `asyncLoad` net is a known 1-bit signal;
    * no register combines `asyncReset` with `asyncLoad` — that pair has no correct lowering
      (the asyncReset's `$adff` is not matched by the `$aldff` rewrite, so the load would be
      silently dropped);
    * declared `clock` / `reset` nets are 1-bit input ports. -/
def Module.checkErrors (m : Module) : List String :=
  let scope := m.allNameWidths
  let portNames := m.inputs.map (·.name) ++ m.outputs.map (·.name)
  dupErrors (scope.map (·.1)) ++
  dupErrors (m.portLayouts.map (·.name)) ++
  m.portLayouts.flatMap (fun layout => if portNames.contains layout.name then [] else
    [s!"port layout '{layout.name}' does not name a declared port"]) ++
  (if !m.portOrder.isEmpty &&
      (m.portOrder.length != portNames.length || !portNames.all (fun n => m.portOrder.contains n)) then
    ["portOrder must be a permutation of the declared ports"] else []) ++
  checkWireNames m.baseNameWidths m.wires ++
  m.regs.flatMap (checkRegNames scope) ++
  m.latches.flatMap (fun l => checkExpr scope s!"latch '{l.name}'.enable" l.enable ++
    checkExpr scope s!"latch '{l.name}'.d" l.d) ++
  m.outputs.flatMap (fun o => checkExpr scope s!"output '{o.name}'" o.expr) ++
  m.mems.flatMap (fun mem =>
    (if mem.size == 0 || mem.size > 2 ^ mem.addrWidth || mem.size >= 2 ^ 31 then
      [s!"mem '{mem.name}': size must be positive and fit the address width and signed 32-bit SIZE parameter"] else []) ++
    (match mem.init with
     | none => []
     | some words => if words.length = mem.size then [] else
         [s!"mem '{mem.name}': initial image must contain exactly {mem.size} words"]) ++
    mem.writes.flatMap (fun wp =>
    checkExpr scope s!"mem '{mem.name}' write.clock" wp.clock ++
    checkExpr scope s!"mem '{mem.name}' write.en" wp.en ++
    checkExpr scope s!"mem '{mem.name}' write.addr" wp.addr ++
    checkExpr scope s!"mem '{mem.name}' write.data" wp.data) ++
    mem.reads.flatMap (fun rp => checkExpr scope s!"mem '{mem.name}' read.addr" rp.addr)) ++
  [("clock", m.clock), ("reset", m.reset)].flatMap (fun (field, net) =>
    match net with
    | some name => checkControl (m.inputs.map (fun p => (p.name, p.width))) field name
    | none => [])


namespace CheckScope
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


end CheckScope

private def checkExprMap (scope : Std.TreeMap String Nat) (ctx : String) {w : Nat} (e : Expr w) :
    List String :=
  e.varRefs.filterMap fun (n, wid) =>
    match scope[n]? with
    | none => some s!"{ctx}: reference to unknown signal '{n}' (would compile to a floating net)"
    | some dw =>
      if dw = wid then none
      else some s!"{ctx}: '{n}' referenced at width {wid} but declared at width {dw}"

private def checkControlMap (scope : Std.TreeMap String Nat) (context net : String) : List String :=
  match scope[net]? with
  | some 1 => []
  | some width => [s!"{context}: '{net}' has width {width} (need 1)"]
  | none => [s!"{context}: '{net}' is not a known signal"]

private def checkRegNamesMap (scope : Std.TreeMap String Nat) (r : Reg) : List String :=
  checkExprMap scope s!"reg '{r.name}'.next" r.next ++
  (match r.asyncReset with
   | some (net, _, _) => checkControlMap scope s!"reg '{r.name}' asyncReset" net
   | none => []) ++
  (if r.asyncReset.isSome && r.asyncLoad.isSome then
    [s!"reg '{r.name}': asyncReset and asyncLoad on the same register is unsupported"] else []) ++
  (match r.clockNet with
   | some e => checkExprMap scope s!"reg '{r.name}'.clockNet" e
   | none => []) ++
  (match r.asyncLoad with
   | some (net, _, value) => checkExprMap scope s!"reg '{r.name}'.asyncLoad" value ++
       checkControlMap scope s!"reg '{r.name}' asyncLoad" net
   | none => [])

private theorem checkExprMap_eq {m : Std.TreeMap String Nat} {ws : List (String × Nat)}
    (h : CheckScope.LookupAgrees m ws) (ctx : String) {w : Nat} (e : Expr w) :
    checkExprMap m ctx e = checkExpr ws ctx e := by
  change (∀ n, m[n]? = ws.lookup n) at h
  simp only [checkExprMap, checkExpr, h]

private theorem checkControlMap_eq {m : Std.TreeMap String Nat} {ws : List (String × Nat)}
    (h : CheckScope.LookupAgrees m ws) (ctx net : String) :
    checkControlMap m ctx net = checkControl ws ctx net := by
  change (∀ n, m[n]? = ws.lookup n) at h
  simp only [checkControlMap, checkControl, h]

private theorem checkRegNamesMap_eq {m : Std.TreeMap String Nat} {ws : List (String × Nat)}
    (h : CheckScope.LookupAgrees m ws) :
    checkRegNamesMap m = checkRegNames ws := by
  funext r
  simp only [checkRegNamesMap, checkRegNames, checkExprMap_eq h, checkControlMap_eq h]

private def checkWireNamesMap (scope : Std.TreeMap String Nat) : List Wire → List String
  | [] => []
  | wr :: rest => checkExprMap scope s!"wire '{wr.name}'" wr.expr ++
      checkWireNamesMap (scope.insert wr.name wr.width) rest

private theorem checkWireNamesMap_eq (wires : List Wire)
    {m : Std.TreeMap String Nat} {ws : List (String × Nat)}
    (h : CheckScope.LookupAgrees m ws) :
    checkWireNamesMap m wires = checkWireNames ws wires := by
  induction wires generalizing m ws with
  | nil => rfl
  | cons w rest ih =>
    simp only [checkWireNamesMap, checkWireNames, checkExprMap_eq h,
      ih (CheckScope.agrees_insert h w.name w.width)]

def Module.checkErrorsMap (m : Module) : List String :=
  let scope := CheckScope.widthMap m.allNameWidths
  let portNames := m.inputs.map (·.name) ++ m.outputs.map (·.name)
  dupErrors (m.allNameWidths.map (·.1)) ++
  dupErrors (m.portLayouts.map (·.name)) ++
  m.portLayouts.flatMap (fun layout => if portNames.contains layout.name then [] else
    [s!"port layout '{layout.name}' does not name a declared port"]) ++
  (if !m.portOrder.isEmpty &&
      (m.portOrder.length != portNames.length || !portNames.all (fun n => m.portOrder.contains n)) then
    ["portOrder must be a permutation of the declared ports"] else []) ++
  checkWireNamesMap (CheckScope.widthMap m.baseNameWidths) m.wires ++
  m.regs.flatMap (checkRegNamesMap scope) ++
  m.latches.flatMap (fun l => checkExprMap scope s!"latch '{l.name}'.enable" l.enable ++
    checkExprMap scope s!"latch '{l.name}'.d" l.d) ++
  m.outputs.flatMap (fun o => checkExprMap scope s!"output '{o.name}'" o.expr) ++
  m.mems.flatMap (fun mem =>
    (if mem.size == 0 || mem.size > 2 ^ mem.addrWidth || mem.size >= 2 ^ 31 then
      [s!"mem '{mem.name}': size must be positive and fit the address width and signed 32-bit SIZE parameter"] else []) ++
    (match mem.init with
     | none => []
     | some words => if words.length = mem.size then [] else
         [s!"mem '{mem.name}': initial image must contain exactly {mem.size} words"]) ++
    mem.writes.flatMap (fun wp =>
    checkExprMap scope s!"mem '{mem.name}' write.clock" wp.clock ++
    checkExprMap scope s!"mem '{mem.name}' write.en" wp.en ++
    checkExprMap scope s!"mem '{mem.name}' write.addr" wp.addr ++
    checkExprMap scope s!"mem '{mem.name}' write.data" wp.data) ++
    mem.reads.flatMap (fun rp => checkExprMap scope s!"mem '{mem.name}' read.addr" rp.addr)) ++
  [("clock", m.clock), ("reset", m.reset)].flatMap (fun (field, net) =>
    match net with
    | some name => checkControlMap (CheckScope.widthMap (m.inputs.map (fun p => (p.name, p.width)))) field name
    | none => [])

theorem Module.checkErrorsMap_eq (m : Module) : m.checkErrorsMap = m.checkErrors := by
  simp only [Module.checkErrorsMap, Module.checkErrors,
    checkWireNamesMap_eq _ (CheckScope.widthMap_agrees _),
    checkRegNamesMap_eq (CheckScope.widthMap_agrees _),
    checkExprMap_eq (CheckScope.widthMap_agrees _),
    checkControlMap_eq (CheckScope.widthMap_agrees _)]

/-- Every instance-output net name a parent declares (`"<inst>.<port>"`). -/
def Parent.instOutNames (p : Parent) : List (String × Nat) :=
  p.insts.flatMap (fun inst => inst.child.outputs.map (fun o => (inst.instName ++ "." ++ o.name, o.width)))

/-- Does any instance's input map reference an instance-output net **not declared by an earlier
    instance** — i.e. a self- or forward-reference (legal instance-level feedback)?

    `compileParentM` (Core/Compiler.lean) branches on this: `false` ⇒ the byte-identical single-pass
    lowering (the pre-M34a path); `true` ⇒ the two-pass lowering that pre-registers every instance
    output before compiling any input cone, so feedback references resolve to real nets.  The whole
    pre-M34a corpus is forward-only, so this returns `false` for it (single-pass ⇒ byte-identical). -/
def Parent.hasForwardInstRef (p : Parent) : Bool := Id.run do
  let allOuts := p.instOutNames.map (·.1)
  let mut declared : List String := []
  for inst in p.insts do
    for (_, ae) in inst.ins do
      for (n, _) in ae.2.varRefs do
        if allOuts.contains n && !declared.contains n then
          return true
    declared := declared ++ inst.child.outputs.map (fun o => inst.instName ++ "." ++ o.name)
  return false

/-- Well-formedness errors of a hierarchical parent: instance input maps and parent outputs may
    reference parent inputs and **any** instance's output (`"<inst>.<port>"`).

    Since M34a the two-pass `compileParentM` pre-registers every instance's output nets before
    compiling any input cone, so an instance input may reference a *later* instance's output — legal
    instance-level feedback through registers.  The scope is therefore the parent inputs plus *all*
    instance outputs, not just earlier ones (the old declaration-order lint is relaxed exactly to
    what the two-pass provably handles).  A genuine bit-level combinational instance loop is still a
    malformed netlist, but it is not detectable here without per-child comb-path analysis; it is
    caught downstream by Yosys `hierarchy -check` logic-loop detection and co-simulation — as with
    any whole-netlist structural property on the flat path.  Genuinely-unknown references (typos,
    signals that are neither a parent input nor any instance output) and width mismatches are still
    rejected. -/
def Parent.checkErrors (p : Parent) : List String := Id.run do
  let mut errs : List String := dupErrors (p.inputs.map (·.name) ++ p.insts.map (·.instName))
  let scope : List (String × Nat) := p.inputs.map (fun pt => (pt.name, pt.width)) ++ p.instOutNames
  for inst in p.insts do
    errs := errs ++ inst.child.checkErrors.map (s!"child '{inst.child.name}': " ++ ·)
    let childIns := inst.child.inputs.map (fun q => (q.name, q.width))
    for (port, ae) in inst.ins do
      match childIns.lookup port with
      | none => errs := errs ++ [s!"inst '{inst.instName}': no input port '{port}' on child '{inst.child.name}'"]
      | some dw =>
        if dw ≠ ae.1 then
          errs := errs ++ [s!"inst '{inst.instName}.{port}': mapped expression has width {ae.1}, port needs {dw}"]
      errs := errs ++ checkExpr scope s!"inst '{inst.instName}.{port}'" ae.2
  for o in p.outputs do
    errs := errs ++ checkExpr scope s!"output '{o.name}'" o.expr
  return errs

end LeanRTL
