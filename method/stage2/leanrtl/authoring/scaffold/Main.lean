import Lean.Data.Json
import LeanRTL
import LeanRTL.Core.Check
import LeanRTL.Core.Coverage
import LeanRTL.BlindRegistry
import LeanRTL.BlindParamRegistry
import LeanRTL.Core.ProcVerilog
/-!
# `leanrtl` command-line interface (blind workspace)

```
leanrtl list                         -- list extractable modules
leanrtl check <Name>                 -- well-formedness lint (names / widths / wire order)
leanrtl extract <Name>               -- print RTLIL JSON to stdout
leanrtl extract <Name> -o <path>     -- write RTLIL JSON to a file
leanrtl extract <Name> --N <k,…>     -- RTLIL JSON of a ParamModule at one parameter vector
leanrtl sim <Name>                   -- simulate (stdin: cycles of `name=value …`)
leanrtl vverilog <Name>              -- procedural next-state SystemVerilog (F9)
leanrtl pverilog <Name>              -- parametric SystemVerilog for a ParamModule (F2)
```

`pverilog` / `extract --N` are the **F2** route and are not a variant of `vverilog`.  F4's
`Module.params` (`Core/Syntax.lean`) fixes header bindability and claims nothing about the body;
F2's `paramMeta.gen : List Nat → Module` generates the whole module per parameter vector.  A design
reached through one is not evidence about the other, and the two are reported as separate emit
routes.

The `--N` vector is given in `paramMeta.params` declaration order — `--N 16,8` for
`params := [("DATA_WIDTH", 16), ("NUM_TAPS", 8)]`.  A vector of the wrong length is an error and
not a silent pad: `gen` would build a module at parameters nobody asked for, and the RTLIL gold
that the parametric emission is anchored against would then certify the wrong instance.

`LeanRTL/BlindParamRegistry.lean` is written by `harness/stage.py` for every arm, empty where no
design declares a `paramMeta`, so this import resolves in a workspace of any benchmark.
-/

open LeanRTL

def findModuleAll? (name : String) : Option Module :=
  blindRegistry.lookup name
def findParentAll? (name : String) : Option Parent :=
  blindParentRegistry.lookup name
def allNamesAll : List String :=
  blindRegistry.map (·.1) ++ blindParentRegistry.map (·.1)

/-- Well-formedness errors for a registered name (module or parent). -/
def checkErrorsOf (name : String) : Option (List String) :=
  match findModuleAll? name with
  | some m => some m.checkErrors
  | none   => (findParentAll? name).map (·.checkErrors)

/-- Run the lint; print errors (if any) to stderr.  Returns `true` iff clean. -/
def lint (name : String) : IO Bool := do
  match checkErrorsOf name with
  | none => IO.eprintln s!"leanrtl: unknown module '{name}'"; return false
  | some [] => return true
  | some errs =>
      IO.eprintln s!"leanrtl: module '{name}' is not well-formed:"
      for e in errs do IO.eprintln s!"  - {e}"
      return false

/-- Parse one input cycle of space-separated `name=value` decimal pairs. -/
def parseCycle (line : String) : Except String (List (String × Nat)) := do
  let mut out : List (String × Nat) := []
  for tok in line.splitOn " " do
    if tok.isEmpty then continue
    match tok.splitOn "=" with
    | [k, v] =>
      match v.toNat? with
      | some n => out := out ++ [(k, n)]
      | none => throw tok
    | _ => throw tok
  return out

def fmtCycle (outs : List (String × Nat)) : String :=
  String.intercalate " " (outs.map (fun (k, v) => s!"{k}={v}"))

/-- Reference simulation from the Lean denotational semantics.  Reads input cycles from
    stdin (one cycle per line as `name=value …`) and prints output cycles likewise. -/
def sim (name : String) : IO UInt32 := do
  let simFn? : Option (List (List (String × Nat)) → List (List (String × Nat))) :=
    match findModuleAll? name with
    | some m => some m.simulateFast
    | none   => (findParentAll? name).map (·.simulateSeq)
  match simFn? with
  | none      => IO.eprintln s!"leanrtl: unknown module '{name}'"; return 1
  | some simFn =>
      if !(← lint name) then return 1
      let raw ← (← IO.getStdin).readToEnd
      let mut cycles : List (List (String × Nat)) := []
      for line in (raw.replace "\r" "").splitOn "\n" do
        match parseCycle line with
        | .ok c => if !c.isEmpty then cycles := cycles ++ [c]
        | .error tok =>
            IO.eprintln s!"leanrtl: malformed input token '{tok}' (expected name=decimal)"
            return 1
      for r in simFn cycles do IO.println (fmtCycle r)
      return 0

def extract (name : String) (path : Option String) : IO UInt32 := do
  let json? : Option String :=
    match findModuleAll? name with
    | some m => some m.toRtlilJson
    | none   => (findParentAll? name).map (·.toRtlilJson)
  match json? with
  | none      => IO.eprintln s!"leanrtl: unknown module '{name}'"; return 1
  | some json =>
      if !(← lint name) then return 1
      match path with
      | some p => IO.FS.writeFile p json
                  IO.eprintln s!"leanrtl: wrote {p}"
      | none   => IO.println json
      return 0

/-- Emit procedural SystemVerilog (F9): register next-state computed inside the clocked
    `always` block with mux decision-trees as `if/else` statements.

    `order`, when non-empty, overrides the header's port order (see `Module.portOrder`).  The
    header is non-ANSI, so this reorders the parenthesis list only — every direction and width is
    still declared by name below it, and the RTLIL the emission is checked against is unchanged.
    It is here so a declared order recorded outside Lean (a contract's `ports` list) can reach the
    emitter without the module literal being rewritten.  A non-permutation is rejected.

    `clocked` renders a `Module.stepDelay` design's always block off a clock edge instead of the
    delay.  Yosys cannot read a delay-driven `always`, so this is the form the equivalence miter
    checks; the harness then ships the delay form only after verifying the two differ by exactly
    that one line.  On a module with no `stepDelay` the flag changes nothing. -/
def vverilog (name : String) (order : List String := []) (clocked : Bool := false) : IO UInt32 := do
  match findModuleAll? name with
  | none => IO.eprintln s!"leanrtl: unknown module '{name}'"; return 1
  | some m =>
      if !(← lint name) then return 1
      let m := if order.isEmpty then m else { m with portOrder := order }
      match ProcVerilog.emitProcVerilog m (forceClocked := clocked) with
      | some v => IO.println v; return 0
      | none =>
          if !order.isEmpty then
            let decl := (m.inputs.map (·.name)) ++ (m.outputs.map (·.name))
            if order.length ≠ decl.length || !decl.all (fun p => order.contains p) then
              IO.eprintln s!"leanrtl: --port-order is not a permutation of '{name}' ports ({String.intercalate ", " decl})"
              return 1
          IO.eprintln s!"leanrtl: '{name}' has an unsupported shape for procedural (F9) emission"
          return 1

/-- Emit genuinely **parametric** SystemVerilog (F2) for a ParamModule registered via a
    `paramMeta : ParamMeta` in the design file.

    This is not `vverilog` with parameters bolted on.  `vverilog` renders one elaborated `Module`;
    this renders `paramMeta.gen`'s whole family as a single module with real `parameter`
    declarations, so the testbench's own override of the parameter is what selects the circuit.

    The emitter derives every width and constant by fitting `gen` over a grid of parameter vectors
    and then **verifying** the fit at held-out vectors.  When it cannot — when a parameter changes
    the module's structure rather than its widths, or a width is not multilinear-plus-`$clog2` in
    the parameters — it refuses and says which thing it could not express.  That refusal goes to
    stderr with a non-zero exit, so a design gets a reason rather than a plausible module that was
    never checked. -/
def pverilog (name : String) : IO UInt32 := do
  match LeanRTL.Designs.Param.findParamMeta? name with
  | none =>
      IO.eprintln s!"leanrtl: '{name}' is not a registered ParamModule (define `paramMeta : ParamMeta` in your design file)"
      return 1
  | some pm =>
      match LeanRTL.Designs.Param.emitParamVerilog pm with
      | .ok v => IO.println v; return 0
      | .error why =>
          IO.eprintln s!"leanrtl: cannot emit '{name}' parametrically:"
          for line in why.splitOn "\n" do IO.eprintln s!"  - {line}"
          return 1

/-- Extract `gen <vector>` of a ParamModule to RTLIL JSON via the VERIFIED compiler (the per-vector
    gold the parametric emission is anchored to).  The vector is in `paramMeta.params` declaration
    order and must have exactly that length. -/
def extractParamN (name : String) (ns : List Nat) (path : Option String) : IO UInt32 := do
  match LeanRTL.Designs.Param.findParamMeta? name with
  | none =>
      IO.eprintln s!"leanrtl: '{name}' is not a registered ParamModule (define `paramMeta : ParamMeta` in your design file)"
      return 1
  | some pm =>
      if ns.length ≠ pm.params.length then
        IO.eprintln s!"leanrtl: '{name}' declares {pm.params.length} parameter(s) \
({String.intercalate ", " pm.names}); --N was given {ns.length} value(s)"
        return 1
      let m := pm.gen ns
      match m.checkErrors with
      | [] =>
        let json := m.toRtlilJson
        match path with
        | some p => IO.FS.writeFile p json; IO.eprintln s!"leanrtl: wrote {p}"
        | none   => IO.println json
        return 0
      | errs =>
        IO.eprintln s!"leanrtl: '{name}' @ N={ns} is not well-formed:"
        for e in errs do IO.eprintln s!"  - {e}"
        return 1

/-- Said next to every GREEN coverage verdict.

    "semantic coverage: full" and "the emitted artifact was proved equivalent" are both one green
    line in a log, and they are not the same claim — an author reported reading the first as the
    second.  This one is about the Lean design: which constructs `Module.step` models, hence which
    whole-design theorems are available to STATE.  It is not itself a proof, and it says nothing
    about the Verilog `emit` writes, which is a separate artifact certified by a separate
    equivalence miter and reported by that command's own `equivalence=` token. -/
private def modelNotArtifact : String :=
  "  (a claim about this Lean design, not a proof and not about any emitted Verilog: the "
    ++ "whole-design theorems APPLY, which is not the same as one having been proved, and the "
    ++ "artifact `emit` writes is certified separately — see that command's `equivalence=`.)"

/-- Semantic-coverage verdict for a leaf module: whether the whole-design simulate theorems
    apply, and — if not — which out-of-model constructs are responsible.

    The middle case is the one worth reading carefully.  `Module.step` / `Module.simulate` never
    read `Reg.asyncReset`, so a design whose *only* out-of-model construct is an async reset still
    gets every whole-design theorem, transported along `Module.eraseArst_simulate`.
    `semanticCoverage` keeps reporting `.asyncReset` — honestly, the reset edge itself is not
    modelled — which used to be read as "async reset costs the whole-design theorem" and pushed
    authors into declaring a synchronous reset the reference did not have.

    That middle case splits in two, and the split is what an author needs to see.  If the reset is
    *also folded in-band* (`next = mux (rst_n == 0) 0 …`, the synchronous spelling of the same
    reset), then `Reg.arstFolded_arstDen` proves the `$adff`'s denotation IS the plain next-state,
    so the cycle model reproduces the reset on reset-ACTIVE edges too and nothing is scoped away
    but the sub-cycle response.  Fold and declaration are complements: the fold buys the theorem
    its reset-active edges, the declaration buys the Verilog its `negedge rst_n`.  Only when the
    fold is absent is the whole-design theorem genuinely scoped to the reset-inactive segment, and
    then the fix is to add the fold — never to drop the declaration. -/
def printCoverage (name : String) : IO Unit := do
  match findModuleAll? name with
  | none   => pure ()
  | some m =>
      match m.semanticCoverage with
      | .full =>
          IO.println s!"{name}: semantic coverage: full (whole-design simulate theorems apply)"
          IO.println modelNotArtifact
      | .perRegister reasons =>
          if m.coveredModuloArstb then
            if m.arstFoldedb then
              IO.println s!"{name}: semantic coverage: full MODULO the asynchronous reset EDGE — the whole-design simulate theorems DO apply, and are NOT scoped: the reset is also folded in-band, so every clock edge is covered, reset-active edges included:"
              IO.println s!"  - Module.eraseArst_simulate : {name}.simulate = {name}.eraseArst.simulate (proved outright; step never reads asyncReset)"
              IO.println s!"  - Module.arstFolded_arstDen : every register's $adff denotation IS its plain next-state here, so the cycle model already computes the reset value on a reset-active edge"
              IO.println s!"  - coveredModuloArst_moduleChecks : discharges CheckWidth.moduleChecksb on the erased twin from `by decide` facts about {name} itself"
              IO.println s!"  This is the intended shape for an active-low `rst_n`.  Only the reset's response BETWEEN edges is out of model:"
            else
              IO.println s!"{name}: semantic coverage: full MODULO the asynchronous reset — the whole-design simulate theorems DO apply, scoped to the reset-inactive segment:"
              IO.println s!"  - Module.eraseArst_simulate : {name}.simulate = {name}.eraseArst.simulate (proved outright; step never reads asyncReset)"
              IO.println s!"  - coveredModuloArst_moduleChecks : discharges CheckWidth.moduleChecksb on the erased twin from `by decide` facts about {name} itself"
              IO.println s!"  To REMOVE that scoping, fold the same reset in-band as well — write each `next` as `.mux (.eq (.var \"<rstPort>\" 1) (.const <activeLevel>)) (.const <rstVal>) <normal>` and KEEP the asyncReset declaration.  `Module.arstFoldedb` then reads true and the theorems cover reset-active edges too."
              IO.println s!"  Do NOT downgrade to a synchronous reset to regain them.  Only the reset EDGE is out of model:"
          else
            IO.println s!"{name}: semantic coverage: per-register/per-access — whole-design simulate theorems do NOT apply:"
          for r in reasons do
            IO.println s!"  - {r.describe}"
          -- Only on the branch that reads green.  The per-register verdict is nobody's idea of a
          -- certificate, so the caveat would be noise there; the `modulo the async reset` one is
          -- worded to sound like one and needs it exactly as much as `.full` does.
          if m.coveredModuloArstb then IO.println modelNotArtifact

/-- Print the module's Verilog `parameter` declarations, one `NAME=VALUE` per line.

    The F9 emitter renders these itself, but the `write_verilog` fallback route builds its Verilog
    from RTLIL, which has no representation for a parameter — so the harness reads them from here
    and injects them into that route's output (re-running the equivalence miter afterwards). -/
def params (name : String) : IO UInt32 := do
  match findModuleAll? name with
  | none => IO.eprintln s!"leanrtl: unknown module '{name}'"; return 1
  | some m =>
      for (n, v) in m.params do IO.println s!"{n}={v}"
      return 0

/-- The parameter vectors `check` sweeps for a design that declares a `paramMeta`.

    Wider than the grid `f9_emit.py::param_vectors` anchors at, and deliberately so.  The anchor
    grid is a SAT cost — each vector is a full equivalence miter against the compiler's netlist —
    so it moves one parameter at a time and only downward.  This grid costs a `checkErrors` call,
    which is a fold over the module's expression trees, so it can afford to move parameters UP as
    well and to move them ALL AT ONCE.

    That difference is the point.  A grader's testbench does not politely halve one parameter: the
    CVDP matrix design is swept at `2,2,2,2,8` and `3,3,3,3,…` while its defaults are `4,4,4,4,…`,
    every parameter moved together to values the anchor never visits.  A generator that is
    ill-formed there passes every gate the workspace has and fails every vector the grader runs. -/
def sweepVectors (defaults : List Nat) : List (List Nat) :=
  let shrink := fun (v : Nat) => if v ≥ 4 then max 2 (v / 2) else v + 1
  let idxs := List.range defaults.length
  let down := idxs.filterMap fun i =>
    let alt := shrink defaults[i]!
    if alt == defaults[i]! then none else some (defaults.set i alt)
  let up := idxs.filterMap fun i =>
    let alt := defaults[i]! * 2
    if alt == defaults[i]! then none else some (defaults.set i alt)
  let vs := [defaults] ++ down ++ up ++ [defaults.map shrink, defaults.map (· * 2)]
  vs.foldl (fun acc v => if acc.contains v then acc else acc ++ [v]) []

/-- Report whether the design's generator is well-formed away from its declared defaults.

    Printed by `check`, unconditionally, for every design that declares a `paramMeta`.  It is a
    report and not a verdict: a spec may legitimately constrain its parameters (a width required to
    be a multiple of four, a depth required to be a power of two), and a generator that is ill-formed
    outside that range is not wrong.  What would be wrong is not knowing — every proof in the file,
    and `check`, `sim`, `cosim` and `extract` without `--N`, run at the DEFAULT vector and at no
    other, so before this line existed a workspace could not tell an author anything at all about
    the instances the grader actually builds. -/
def paramSweepReport (name : String) : IO Unit := do
  match LeanRTL.Designs.Param.findParamMeta? name with
  | none    => pure ()
  | some pm =>
      let defaults := pm.defaults
      let vecs := sweepVectors defaults
      let mut bad : List (List Nat) := []
      for v in vecs do
        if !(pm.gen v).checkErrors.isEmpty then bad := bad ++ [v]
      IO.println s!"{name}: parameter sweep ({String.intercalate ", " pm.names}): \
{vecs.length - bad.length}/{vecs.length} vector(s) well-formed"
      if !bad.isEmpty then
        IO.println s!"  NOT well-formed at: \
{String.intercalate "  " (bad.map (fun v => String.intercalate "," (v.map toString)))}"
        IO.println "  A spec that constrains its parameters makes this expected.  Otherwise it is \
a bug the default vector cannot show you: your proofs, and every command here without --N, run \
only at the defaults, while the grader instantiates the module at values of its own choosing."

def check (name : String) : IO UInt32 := do
  if (checkErrorsOf name).isNone then
    IO.eprintln s!"leanrtl: unknown module '{name}'"; return 1
  if (← lint name) then
    IO.println s!"{name}: well-formed"
    printCoverage name
    paramSweepReport name
    return 0
  else return 1

/-- `check` at ONE parameter vector: is `gen <vector>` a well-formed module? -/
def checkAtN (name : String) (ns : List Nat) : IO UInt32 := do
  match LeanRTL.Designs.Param.findParamMeta? name with
  | none =>
      IO.eprintln s!"leanrtl: '{name}' is not a registered ParamModule (define `paramMeta : ParamMeta` in your design file)"
      return 1
  | some pm =>
      if ns.length ≠ pm.params.length then
        IO.eprintln s!"leanrtl: '{name}' declares {pm.params.length} parameter(s) \
({String.intercalate ", " pm.names}); --N was given {ns.length} value(s)"
        return 1
      match (pm.gen ns).checkErrors with
      | []   => IO.println s!"{name} @ N={ns}: well-formed"; return 0
      | errs =>
          IO.eprintln s!"leanrtl: '{name}' @ N={ns} is not well-formed:"
          for e in errs do IO.eprintln s!"  - {e}"
          return 1

/-- `sim` at ONE parameter vector.

    The command an author needs and did not have.  A parametric design's whole risk is that its
    generator is right at the defaults and wrong somewhere else — that is not a hypothetical class,
    it is where the parameter subset's residual failures live — and until this existed there was no
    way to run the thing at another vector and look at the outputs.  Same stdin format as `sim`. -/
def simAtN (name : String) (ns : List Nat) : IO UInt32 := do
  match LeanRTL.Designs.Param.findParamMeta? name with
  | none =>
      IO.eprintln s!"leanrtl: '{name}' is not a registered ParamModule (define `paramMeta : ParamMeta` in your design file)"
      return 1
  | some pm =>
      if ns.length ≠ pm.params.length then
        IO.eprintln s!"leanrtl: '{name}' declares {pm.params.length} parameter(s) \
({String.intercalate ", " pm.names}); --N was given {ns.length} value(s)"
        return 1
      let m := pm.gen ns
      match m.checkErrors with
      | e :: _ => IO.eprintln s!"leanrtl: '{name}' @ N={ns} is not well-formed: {e}"; return 1
      | [] =>
        let raw ← (← IO.getStdin).readToEnd
        let mut cycles : List (List (String × Nat)) := []
        for line in (raw.replace "\r" "").splitOn "\n" do
          match parseCycle line with
          | .ok c => if !c.isEmpty then cycles := cycles ++ [c]
          | .error tok =>
              IO.eprintln s!"leanrtl: malformed input token '{tok}' (expected name=decimal)"
              return 1
        for r in m.simulateFast cycles do IO.println (fmtCycle r)
        return 0

def usage : String :=
  "usage:\n  leanrtl list\n  leanrtl check <Name>\n  leanrtl check <Name> --N <k1,k2,…>            (well-formedness of a ParamModule at one vector)\n  leanrtl extract <Name> [-o <path>]\n  leanrtl extract <Name> --N <k1,k2,…> [-o <path>]   (ParamModule at one parameter vector, in paramMeta.params order)\n  leanrtl vverilog <Name> [--port-order a,b,c] [--clocked]\n  leanrtl pverilog <Name>                       (parametric SystemVerilog for a ParamModule)\n  leanrtl params <Name>\n  leanrtl sim <Name>   (reads input cycles on stdin, writes output cycles)\n  leanrtl sim <Name> --N <k1,k2,…>              (the same, on a ParamModule at one parameter vector)"

/-- Parse `--N`'s comma-separated parameter vector.  `none` on any non-numeric field, so a typo is
    an error rather than a silently shortened vector. -/
def parseNVec (s : String) : Option (List Nat) :=
  let fields := ((s.replace " " "").splitOn ",").filter (!·.isEmpty)
  if fields.isEmpty then none else fields.mapM (·.toNat?)

/-- Parse `vverilog`'s optional flags into `(portOrder, clocked)`.  Either flag may appear, in
    either order; anything else is `none` so the caller prints usage rather than silently ignoring
    a misspelt flag and emitting the default rendering. -/
def parseVverilogFlags : List String → Option (List String × Bool)
  | [] => some ([], false)
  | "--clocked" :: rest => (parseVverilogFlags rest).map (fun (o, _) => (o, true))
  | "--port-order" :: o :: rest =>
      -- Port names contain no spaces, so stripping them all is a safe way to accept `a, b, c`.
      (parseVverilogFlags rest).map (fun (_, c) =>
        (((o.replace " " "").splitOn ",").filter (!·.isEmpty), c))
  | _ => none

def main (args : List String) : IO UInt32 := do
  match args with
  | ["list"] =>
      for n in allNamesAll do IO.println n
      return 0
  | ["check", name] => check name
  | ["check", name, "--N", nstr] =>
      match parseNVec nstr with
      | none => IO.eprintln s!"leanrtl: --N expects a comma-separated list of natural numbers, got '{nstr}'"; return 1
      | some ns => checkAtN name ns
  | ["sim", name] => sim name
  | ["sim", name, "--N", nstr] =>
      match parseNVec nstr with
      | none => IO.eprintln s!"leanrtl: --N expects a comma-separated list of natural numbers, got '{nstr}'"; return 1
      | some ns => simAtN name ns
  | ["params", name] => params name
  | "vverilog" :: name :: rest =>
      match parseVverilogFlags rest with
      | some (order, clocked) => vverilog name order clocked
      | none => IO.eprintln usage; return 1
  | ["pverilog", name] => pverilog name
  | "extract" :: name :: rest =>
      match rest with
      -- ParamModule instance: `extract <Name> --N <k1,k2,…> [-o <path>]`
      | "--N" :: nstr :: more =>
          match parseNVec nstr with
          | none => IO.eprintln s!"leanrtl: --N expects a comma-separated list of natural numbers, got '{nstr}'"; return 1
          | some ns =>
            match more with
            | [] => extractParamN name ns none
            | ["-o", path] => extractParamN name ns (some path)
            | _ => IO.eprintln usage; return 1
      | [] => extract name none
      | ["-o", path] => extract name (some path)
      | _ => IO.eprintln usage; return 1
  | _ => IO.eprintln usage; return 1
