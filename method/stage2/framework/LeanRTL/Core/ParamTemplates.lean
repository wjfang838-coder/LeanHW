import LeanRTL.Core.ParamBackend
/-!
# Archived per-design parametric templates.

Eighteen hand-written Verilog emitters, one per benchmark design.  They are **not** the generic
parametric route and were never reachable from it: each one renders a specific design's ports,
widths and body from a `Cfg` its author filled in.  `emitGenericVerilog` in
`LeanRTL.Core.ParamBackend` is the route a design takes on its own merits; this file is what that
route was standing in for before it could express more than one parameter.

They live here, and not in `ParamBackend.lean`, for one reason: `harness/stage.py::install_authoring`
copies `framework/LeanRTL/Core/` **whole** into every blind author's workspace, and the workspace
sanitizer redacts design *names* only.  So a template like the FIR one below — which spells out the
port names and the exact width formulas of a benchmark design — was arriving in the workspace of the
author who was supposed to derive it.  `install_authoring` now excludes this file by name.

Kept, not deleted: the earlier CVDP round's `param_draw` numbers were produced through these
emitters, and an archived workspace still carries the file they were produced with.  Deleting them
would make that round unreproducible.  Nothing in the live pipeline calls anything here.

`LegacyMeta` below is the single-parameter `ParamMeta` these were written against, frozen so the
bodies compile verbatim.  The live `ParamMeta` carries `params : List (String × Nat)` and
`gen : List Nat → Module`; converting eighteen archived templates to it would be eighteen chances
to silently change what an earlier round emitted.
-/
namespace LeanRTL.Designs.Param
open LeanRTL

/-! ## Emit classes

The width-uniform (affine) class is emitted by structural SSA over two sentinel widths.  The two
*harder* F2 classes — **count / generate-loop** (structure scales with a count) and **memory-depth**
(a `2^ADDR`-deep array) — cannot be emitted that way: at two sentinel counts the module is a
*different* structure (a different number of registers), so the SSA differ-by-shape trick breaks.
They instead get **parametric-template** emitters that mirror the Lean recursion with a Verilog
`generate`/`for` loop (count class) or a `reg […] mem [0:DEPTH-1]` array (memory-depth class).

Each template is *configured* by the design's port/param names (read below), and — crucially — is
**not trusted**: it is validated per-`N` by the same Yosys equivalence miter against the design's
*verified* `compile (gen N)` RTLIL path.  So the guarantee is identical to the affine class; only the
emission mechanism differs. -/

/-- Config for the **count / generate-loop** class: a pipelined reduction of `nsParam` elements,
    each `widthParam` bits, packed into one flattened input bus (CVDP `cascaded_adder`). -/
structure CascadeCfg where
  /-- Verilog element-width parameter, e.g. `"IN_DATA_WIDTH"`. -/
  widthParam   : String
  /-- Verilog element-count parameter, e.g. `"IN_DATA_NS"`. -/
  nsParam      : String
  /-- Default element width. -/
  widthDefault : Nat
  /-- Default element count. -/
  nsDefault    : Nat

/-- Config for the **memory-depth** class: a synchronous LIFO/stack whose depth is `2^addrParam`,
    each word `dataParam` bits (CVDP `sync_lifo`). -/
structure MemLifoCfg where
  /-- Verilog data-width parameter, e.g. `"DATA_WIDTH"`. -/
  dataParam    : String
  /-- Verilog address-width parameter (depth `= 2^addrParam`), e.g. `"ADDR_WIDTH"`. -/
  addrParam    : String
  /-- Default data width. -/
  dataDefault  : Nat
  /-- Default address width. -/
  addrDefault  : Nat

/-- Config for the **memory-depth (raw-count) + feedthrough** class: a synchronous FILO/stack whose
    depth is an arbitrary count `depthParam` (not a power of two), each word `dataParam` bits, with a
    same-cycle push+pop feedthrough edge case (CVDP `FILO_RTL`). -/
structure FiloCfg where
  /-- Verilog data-width parameter, e.g. `"DATA_WIDTH"`. -/
  dataParam    : String
  /-- Verilog depth parameter (a raw count), e.g. `"FILO_DEPTH"`. -/
  depthParam   : String
  /-- Default data width. -/
  dataDefault  : Nat
  /-- Default depth. -/
  depthDefault : Nat

/-- Config for the **FIR / packed-dual-bus generate-loop** class: an element-wise signed multiply of
    `tapsParam` data samples (`dataParam` bits) by `tapsParam` coefficients (`coeffParam` bits) in
    reversed order, summed to a `(dataParam+coeffParam)+$clog2(tapsParam)`-bit output (CVDP
    `low_pass_filter`). -/
structure FirCfg where
  /-- Verilog data-width parameter, e.g. `"DATA_WIDTH"`. -/
  dataParam    : String
  /-- Verilog coefficient-width parameter, e.g. `"COEFF_WIDTH"`. -/
  coeffParam   : String
  /-- Verilog tap-count parameter, e.g. `"NUM_TAPS"`. -/
  tapsParam    : String
  /-- Default data width. -/
  dataDefault  : Nat
  /-- Default coefficient width. -/
  coeffDefault : Nat
  /-- Default tap count. -/
  tapsDefault  : Nat

/-- Config for the **combinational bit-permutation** class: `sel`-selected chunk-reversal of a
    `dataParam`-bit word into `2^sel` reversed sections (CVDP `nbit_swizzling`). -/
structure SwizzleCfg where
  /-- Verilog data-width parameter, e.g. `"DATA_WIDTH"`. -/
  dataParam    : String
  /-- Default data width. -/
  dataDefault  : Nat

/-- Config for the **packed parametric ports (QAM16 mapper)** class: the port *itself* is an
    `nParam`-element packed bus (`bits : N*IN_WIDTH`; `I`,`Q : (N+N/2)*OUT_WIDTH`), and the per-element
    map/interpolate is a `generate` loop over the `N/2` symbol pairs (CVDP `qam16_mapper_interpolated`).
    `IN_WIDTH`/`OUT_WIDTH` are fixed (4/3), so only `N` is swept. -/
structure QamMapCfg where
  /-- Verilog symbol-count parameter, e.g. `"N"`. -/
  nParam    : String
  /-- Default symbol count. -/
  nDefault  : Nat

/-- Config for the **packed parametric ports (QAM16 demapper)** class: the ports are packed I/Q input
    buses (`I`,`Q : (N+N/2)*IN_WIDTH`) demapped to `bits : N*OUT_WIDTH` plus a global `error_flag`
    reduced over the `N/2` pairs (CVDP `qam16_demapper_interpolated`).  `IN_WIDTH`/`OUT_WIDTH` fixed
    (3/4). -/
structure QamDemapCfg where
  /-- Verilog symbol-count parameter, e.g. `"N"`. -/
  nParam    : String
  /-- Default symbol count. -/
  nDefault  : Nat
  /-- Error threshold (a `parameter ERROR_THRESHOLD`), matching the design's error-detection law. -/
  threshold : Nat

/-- Config for the **value-dependent generate (LFSR)** class: a `WIDTH`-parallel PRBS generator/checker
    whose feedback tap `cur[POLY_LENGTH − POLY_TAP] ⊕ cur[0]` selects a bit at an index that is a
    *function of the parameter value* (CVDP `cvdp_prbs_gen`).  Four parameters
    `CHECK_MODE/POLY_LENGTH/POLY_TAP/WIDTH`; only one is swept per registry key (the others held at
    these defaults for the per-`N` miter). -/
structure PrbsCfg where
  modeParam   : String
  lenParam    : String
  tapParam    : String
  widthParam  : String
  modeDefault : Nat
  lenDefault  : Nat
  tapDefault  : Nat
  widthDefault : Nat

/-- Config for the **iterative multi-cycle divider** class: a `WIDTH`-bit restoring divider that takes
    `WIDTH` clocks (one dividend bit per cycle).  The finish comparison `cnt == WIDTH-1` is a
    *value-dependent* (`N`-valued) constant, so the affine width-uniform emitter cannot emit it; this
    template mirrors the Lean `impl`'s FF set (`state`,`cnt`,`divisor_r`,`quotient`,`remainder`,
    `valid`) and its restoring-division step, and the per-`N` miter anchors it to `compile (impl N)`
    (CVDP `restoring_division`). -/
structure RestoreDivCfg where
  /-- Verilog data-width parameter, e.g. `"WIDTH"`. -/
  widthParam   : String
  /-- Default data width. -/
  widthDefault : Nat

/-- Config for the **iterative bubble-sort** class (CVDP `sorting_engine`): an `N`-element ×
    `WIDTH`-bit `reg [WIDTH-1:0] arr[0:N-1]` array sorted over `N*(N-1)` compare-swap cycles by an
    `IDLE/SORTING/DONE` FSM.  Two parameters (`N` structural, `WIDTH` data); the two registry keys
    sample the two axes for the per-`N` miter, both emitting the same 2-parameter module. -/
structure SortCfg where
  /-- Verilog element-count parameter, e.g. `"N"`. -/
  nParam      : String
  /-- Verilog element-width parameter, e.g. `"WIDTH"`. -/
  widthParam  : String
  /-- Default element count. -/
  nDefault    : Nat
  /-- Default element width. -/
  widthDefault : Nat

/-- Config for the **fall-through queue** class (CVDP AGENTIC `queue`): a `depthParam`-deep,
    `dataParam`-wide first-word-fall-through queue whose storage shifts down on a read, with a
    fill-level pointer `queue_wadr` (`$clog2(DEPTH+1)` bits), async active-low reset `rst_ni`,
    synchronous clear `clr_i`, clock-enable `ena_i`, and programmable almost-empty / almost-full
    thresholds compared against clamped "_CHECK" localparams. -/
structure QueueCfg where
  /-- Verilog depth parameter (a raw entry count), e.g. `"DEPTH"`. -/
  depthParam   : String
  /-- Verilog data-width parameter, e.g. `"DBITS"`. -/
  dataParam    : String
  /-- Verilog almost-empty threshold parameter, e.g. `"ALMOST_EMPTY_THRESHOLD"`. -/
  aeParam      : String
  /-- Verilog almost-full threshold parameter, e.g. `"ALMOST_FULL_THRESHOLD"`
      (its default is the symbolic `depthParam`). -/
  afParam      : String
  /-- Default depth. -/
  depthDefault : Nat
  /-- Default data width. -/
  dataDefault  : Nat
  /-- Default almost-empty threshold. -/
  aeDefault    : Nat

/-- Config for the **universal shift register** class (CVDP AGENTIC `universal_shift_register`): an
    `N`-bit register with Hold / Shift / Rotate / Parallel-Load modes selected by `mode_sel[1:0]` and
    a direction `shift_dir`, async active-high reset `rst`, plus a combinational `serial_out`.  The
    shift/rotate insert bit is at position `N-1` (a *function of the width*), so the affine SSA
    emitter cannot express it; this template renders `{serial_in, q[N-1:1]}` &c. symbolically. -/
structure ShiftRegCfg where
  /-- Verilog width parameter, e.g. `"N"`. -/
  widthParam   : String
  /-- Default width. -/
  widthDefault : Nat

/-- Config for the **configurable signed comparator** class (CVDP AGENTIC `signed_comparator`):
    five parameters, ALL of which change behaviour — `DATA_WIDTH` (operand width),
    `REGISTER_OUTPUT` (a *structural* toggle: `generate`-selected registered vs combinational
    output stage, async active-low `rst_n` when registered), `ENABLE_TOLERANCE`/`TOLERANCE`
    (a value-dependent `|a<<S − b<<S| ≤ TOLERANCE` equality window on the exact `(W+1)`-bit
    difference), and `SHIFT_LEFT` (a value-dependent pre-shift).  The affine SSA emitter can
    express none of the last four (constants whose *value* is the parameter), so this template
    renders them symbolically.  Each registry key fixes four axes at these defaults and sweeps
    the fifth for the per-`N` miter (queue/prbs precedent). -/
structure ComparatorCfg where
  /-- Verilog data-width parameter (`"DATA_WIDTH"`). -/
  dwParam    : String
  /-- Verilog registered-output toggle parameter (`"REGISTER_OUTPUT"`). -/
  regParam   : String
  /-- Verilog tolerance-enable parameter (`"ENABLE_TOLERANCE"`). -/
  etParam    : String
  /-- Verilog tolerance-bound parameter (`"TOLERANCE"`). -/
  tolParam   : String
  /-- Verilog pre-shift parameter (`"SHIFT_LEFT"`). -/
  shParam    : String
  /-- Default data width. -/
  dwDefault  : Nat
  /-- Default registered-output toggle. -/
  regDefault : Nat
  /-- Default tolerance enable. -/
  etDefault  : Nat
  /-- Default tolerance bound. -/
  tolDefault : Nat
  /-- Default pre-shift. -/
  shDefault  : Nat

/-- Config for the **direct-mapped cache** class (CVDP AGENTIC `direct_map_cache`): four swept
    parameters (`CACHE_SIZE`, `DATA_WIDTH`, `TAG_WIDTH`, `OFFSET_WIDTH`), a `$clog2`-derived
    `INDEX_WIDTH` localparam the hidden harness probes off the DUT, flat tag/valid/dirty stores
    (dynamic part-select field addressing mirroring the Lean shift/mask registers), and one
    `CACHE_SIZE·2^(OFFSET_WIDTH-1)`-deep data array mirroring the Lean `MemBlock`.  Each registry
    key fixes three axes at these defaults and sweeps the fourth for the per-`N` miter
    (comparator precedent). -/
structure DmCacheCfg where
  /-- Verilog line-count parameter (`"CACHE_SIZE"`). -/
  csParam   : String
  /-- Verilog data-width parameter (`"DATA_WIDTH"`). -/
  dwParam   : String
  /-- Verilog tag-width parameter (`"TAG_WIDTH"`). -/
  twParam   : String
  /-- Verilog offset-width parameter (`"OFFSET_WIDTH"`). -/
  owParam   : String
  /-- Default line count. -/
  csDefault : Nat
  /-- Default data width. -/
  dwDefault : Nat
  /-- Default tag width. -/
  twDefault : Nat
  /-- Default offset width. -/
  owDefault : Nat

/-- Config for the **fixed-bus APB peripheral** class (CVDP `cvdp_copilot_apb_gpio`): an APB GPIO
    whose GPIO-side ports/registers are `widthParam` bits while the APB side is FIXED-width
    (`pwdata`/`prdata` 32, `paddr` 6) — a *sub-32 sentinel* shape the affine emitter cannot sample
    at `N = 64/65` (the `pwdata[N-1:0]` field select and the `N→32` zero-extension are only
    Verilog-legal for `N ≤ 32`), plus an active-LOW async reset behind a `nrst` wire (the affine
    emitter renders neither wires nor low-active resets).  Scope: `widthParam ≤ 32`. -/
structure ApbGpioCfg where
  /-- Verilog GPIO-width parameter, e.g. `"GPIO_WIDTH"`. -/
  widthParam   : String
  /-- Default GPIO width. -/
  widthDefault : Nat

/-- Config for the **decimator + peak detector** class (CVDP
    `advanced_decimator_with_adaptive_peak_detection`): three swept parameters (`N` sample count,
    `DATA_WIDTH`, `DEC_FACTOR` a divisor of `N`), packed parametric ports
    (`data_in : DATA_WIDTH*N`, `data_out : DATA_WIDTH*(N/DEC_FACTOR)`), a 1-cycle input pipeline
    with async active-high reset, a value-indexed decimation select
    (`reg_data[i*DEC_FACTOR*DATA_WIDTH +: DATA_WIDTH]`), and a signed peak reduction over the
    `N/DEC_FACTOR` decimated samples. -/
structure DecimPeakCfg where
  /-- Verilog sample-count parameter (`"N"`). -/
  nParam     : String
  /-- Verilog data-width parameter (`"DATA_WIDTH"`). -/
  dwParam    : String
  /-- Verilog decimation-factor parameter (`"DEC_FACTOR"`). -/
  decParam   : String
  /-- Default sample count. -/
  nDefault   : Nat
  /-- Default data width. -/
  dwDefault  : Nat
  /-- Default decimation factor. -/
  decDefault : Nat

/-- Which parametric emitter to use for a `ParamModule`. -/
inductive EmitClass where
  /-- Width-uniform: affine-width structural SSA over two sentinel widths (the original F2 class). -/
  | affine
  /-- Count / generate-loop: a Verilog `for`-loop reduction mirroring the Lean `List.range` fold. -/
  | cascade (cfg : CascadeCfg)
  /-- Memory-depth: a parametric `reg […] mem [0:2^ADDR-1]` stack mirroring the Lean register array. -/
  | memLifo (cfg : MemLifoCfg)
  /-- Memory-depth (raw count) + feedthrough: a parametric FILO stack (CVDP `FILO_RTL`). -/
  | filo (cfg : FiloCfg)
  /-- FIR / packed-dual-bus generate-loop: element-wise signed MAC (CVDP `low_pass_filter`). -/
  | fir (cfg : FirCfg)
  /-- Combinational `sel`-selected chunk-reversal (CVDP `nbit_swizzling`). -/
  | swizzle (cfg : SwizzleCfg)
  /-- Combinational `sel`-selected chunk-reversal **plus** a binary→Gray `gray_out` output
      (`gray_out = data_out ^ (data_out >> 1)`) — CVDP AGENTIC `nbit_swizzling`. -/
  | swizzleGray (cfg : SwizzleCfg)
  /-- Packed parametric ports: QAM16 mapper generate-loop over `N/2` pairs (CVDP `qam16_mapper`). -/
  | qamMap (cfg : QamMapCfg)
  /-- Packed parametric ports: QAM16 demapper generate-loop + error reduction (CVDP `qam16_demapper`). -/
  | qamDemap (cfg : QamDemapCfg)
  /-- Value-dependent generate: `WIDTH`-parallel LFSR with a value-indexed feedback tap (CVDP `prbs`). -/
  | prbs (cfg : PrbsCfg)
  /-- Iterative multi-cycle restoring divider, `WIDTH` clocks (CVDP `restoring_division`). -/
  | restoreDiv (cfg : RestoreDivCfg)
  /-- Iterative bubble-sort: `reg [WIDTH-1:0] arr[0:N-1]` + `IDLE/SORTING/DONE` FSM (CVDP `sorting_engine`). -/
  | sort (cfg : SortCfg)
  /-- Fall-through queue: shift-on-read `reg [DBITS-1:0] queue_data[0:DEPTH-1]` + fill pointer,
      async active-low reset, programmable almost-empty/full (CVDP AGENTIC `queue`). -/
  | queue (cfg : QueueCfg)
  /-- Universal shift register: `N`-bit Hold/Shift/Rotate/Load register with an `N-1`-indexed
      insert bit + combinational `serial_out` (CVDP AGENTIC `universal_shift_register`). -/
  | shiftReg (cfg : ShiftRegCfg)
  /-- Configurable signed comparator: 5-parameter `gt/lt/eq` with pre-shift, tolerance window,
      and a `generate`-selected registered/combinational output stage (CVDP AGENTIC
      `signed_comparator`). -/
  | comparator (cfg : ComparatorCfg)
  /-- Direct-mapped cache: 4-parameter tag/valid/dirty stores + data array + `$clog2` localparam
      (CVDP AGENTIC `direct_map_cache`). -/
  | dmCache (cfg : DmCacheCfg)
  /-- Fixed-bus APB GPIO peripheral: `N`-bit GPIO registers behind a fixed 32-bit APB data bus,
      active-low async reset, latched W1C edge interrupts (CVDP `cvdp_copilot_apb_gpio`). -/
  | apbGpio (cfg : ApbGpioCfg)
  /-- Decimator + signed peak detector: packed parametric ports, value-indexed decimation select,
      1-cycle pipeline (CVDP `advanced_decimator_with_adaptive_peak_detection`). -/
  | decimPeak (cfg : DecimPeakCfg)


/-- The single-parameter `ParamMeta` the archived templates below were written against.

    Frozen deliberately.  Every field here was a field of `ParamMeta` before it grew a parameter
    *list*; keeping the old shape under a new name is what lets the eighteen bodies stay
    byte-identical to the ones that produced the earlier round's artifacts. -/
structure LegacyMeta where
  /-- Registry key = emitted Verilog module name (`gen defaultN |>.name`). -/
  key       : String
  /-- Verilog parameter name, e.g. `"DATA_WIDTH"`. -/
  paramName : String
  /-- Parameter default value (the CVDP default). -/
  defaultN  : Nat
  /-- The width generator. -/
  gen       : Nat → Module
  /-- Which per-design template to use. -/
  cls       : EmitClass

/-! ## Archived two-sample (single-parameter) affine emitter.

The original width-inference stack: instantiate `gen` at `N = 64` and `N = 65`, read each
port/register/subexpression width, and recover `w(N) = s*N + b` from the two samples.  It is kept
intact, in its own namespace, because `EmitClass.affine` dispatches to it and four designs in the
earlier round were emitted through it.  The live replacement is `emitGenericVerilog`, which fits a
parameter *vector* and refuses what it cannot verify instead of warning about it. -/
namespace Legacy

/-! ## Affine width strings -/

/-- Symbolic width expression `s·N + b` (with `PN` the parameter name), from the two samples
    `w0 = w(64)`, `w1 = w(65)`.  Uniform-class widths are affine, so `s = w1 - w0`. -/
def widthExpr (pn : String) (w0 w1 : Nat) : String :=
  let s : Int := (w1 : Int) - (w0 : Int)
  let b : Int := (w0 : Int) - s * 64
  if s == 0 then toString b
  else
    let coeff := if s == 1 then pn else s!"{s}*{pn}"
    if b == 0 then coeff
    else if b > 0 then s!"{coeff}+{b}"
    else s!"{coeff}-{-b}"

/-- A port/wire range `[width-1:0]`, or empty for a 1-bit scalar. -/
def rangeOf (pn : String) (w0 w1 : Nat) : String :=
  if w0 == 1 && w1 == 1 then ""
  else s!"[{widthExpr pn w0 w1}-1:0] "

/-! ## Width-explicit SSA expression emitter -/

/-- The width index of an `Expr` (its result bit-width). -/
def ewidth {w : Nat} (_ : Expr w) : Nat := w

/-- Emitter state: fresh-net counter and accumulated `wire` declarations (reversed). -/
abbrev EM := StateM (Nat × List String)

/-- Is `s` already a simple Verilog identifier (safe to bit-select / replicate)? -/
def isIdent (s : String) : Bool :=
  s.length > 0 && !(s.get 0).isDigit && s.all (fun c => c.isAlphanum || c == '_')

/-- Bind `rhs` (a Verilog expression built from operand nets) to a fresh net of the given
    affine width `(w0,w1)`; returns the fresh net name. -/
def freshNet (pn : String) (w0 w1 : Nat) (rhs : String) : EM String := do
  let (n, decls) ← get
  let nm := s!"_t{n}"
  set (n + 1, s!"  wire {rangeOf pn w0 w1}{nm} = {rhs};" :: decls)
  return nm

/-- Force `s` (of affine width `(w0,w1)`) to be an identifier net, materialising a wire if it is a
    literal/compound expression (so it can be bit-selected or replicated). -/
def ensureNet (pn : String) (w0 w1 : Nat) (s : String) : EM String :=
  if isIdent s then return s else freshNet pn w0 w1 s

/-- Emit an `Expr` as width-explicit SSA over two structurally-identical samples `e0` (at `N=64`)
    and `e1` (at `N=65`); returns the net (or literal, for a leaf) holding its value. -/
partial def emitExpr (pn : String) : {w0 w1 : Nat} → Expr w0 → Expr w1 → EM String
  | w0, w1, e0, e1 =>
    match e0, e1 with
    | .const v, _ => return toString v.toNat
    | .var n _, _ => return n
    | .not a0, .not a1 => do
        let x ← emitExpr pn a0 a1; freshNet pn w0 w1 s!"(~{x})"
    | .and a0 b0, .and a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"({x} & {y})"
    | .or a0 b0, .or a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"({x} | {y})"
    | .xor a0 b0, .xor a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"({x} ^ {y})"
    | .add a0 b0, .add a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"({x} + {y})"
    | .sub a0 b0, .sub a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"({x} - {y})"
    | .mul a0 b0, .mul a1 b1 => do
        -- LeanRTL `mul` has operand width = result width, so the operand nets are already full
        -- width; an unsigned product mod 2^w equals the (sign-extended) exact product's low w bits.
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"({x} * {y})"
    | .shl a0 b0, .shl a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"({x} << {y})"
    | .shr a0 b0, .shr a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"({x} >> {y})"
    | .sshr a0 b0, .sshr a1 b1 => do
        -- arithmetic right shift: `$signed(net)` is self-determined at the net's (full) width `w`,
        -- and the result is also width `w`, so no truncation.
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"($signed({x}) >>> {y})"
    | .udiv a0 b0, .udiv a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"({x} / {y})"
    | .umod a0 b0, .umod a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn w0 w1 s!"({x} % {y})"
    | .eq a0 b0, .eq a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn 1 1 s!"({x} == {y})"
    | .ult a0 b0, .ult a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1; freshNet pn 1 1 s!"({x} < {y})"
    | .slt a0 b0, .slt a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1
        freshNet pn 1 1 s!"($signed({x}) < $signed({y}))"
    | .mux s0 a0 b0, .mux s1 a1 b1 => do
        let s ← emitExpr pn s0 s1; let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1
        freshNet pn w0 w1 s!"({s} ? {x} : {y})"
    | .concat a0 b0, .concat a1 b1 => do
        let x ← emitExpr pn a0 a1; let y ← emitExpr pn b0 b1
        freshNet pn w0 w1 ("{" ++ x ++ ", " ++ y ++ "}")
    | .zext k0 _a0, .zext k1 a1 => do
        -- zero-extend by `k`: `{ {k{1'b0}}, a }`.
        let x ← ensureNet pn (ewidth a1) (ewidth a1) (← emitExpr pn _a0 a1)
        freshNet pn w0 w1 ("{ {" ++ widthExpr pn k0 k1 ++ "{1'b0}}, " ++ x ++ " }")
    | .sext k0 a0, .sext k1 a1 => do
        -- sign-extend by `k`: replicate the MSB `a[wa-1]`.
        let wa0 := ewidth a0; let wa1 := ewidth a1
        let x ← ensureNet pn wa0 wa1 (← emitExpr pn a0 a1)
        freshNet pn w0 w1 ("{ {" ++ widthExpr pn k0 k1 ++ "{" ++ x ++ "["
          ++ widthExpr pn wa0 wa1 ++ "-1]}}, " ++ x ++ " }")
    | .extract i _a0, .extract _ a1 => do
        let x ← ensureNet pn (ewidth a1) (ewidth a1) (← emitExpr pn _a0 a1)
        freshNet pn 1 1 s!"{x}[{i}]"
    | .slice lo len _a0, .slice _ _ a1 => do
        let x ← ensureNet pn (ewidth a1) (ewidth a1) (← emitExpr pn _a0 a1)
        freshNet pn w0 w1 s!"{x}[{lo + len - 1}:{lo}]"
    | _, _ => return "/* emit: unsupported-shape */"

/-! ## Module emission (sequential, single-clock, async or sync reset) -/

/-- Is `name` the name of some register in `m`? -/
def isRegName (m : Module) (name : String) : Bool := m.regs.any (·.name == name)

/-- The async-reset net (active-high) shared by the registers, if any. -/
def asyncResetNet (m : Module) : Option String :=
  m.regs.findSome? (fun r => r.asyncReset.map (·.1))

/-- Run the SSA emitter for one `Expr` pair starting the fresh-net counter at `start`; returns the
    final net, the wire declarations, and the next counter value (threaded so nets are unique
    across every register/output cone in the module). -/
def runExpr (pn : String) (start : Nat) {w0 w1 : Nat} (e0 : Expr w0) (e1 : Expr w1) :
    String × List String × Nat :=
  let (net, (n, decls)) := (emitExpr pn e0 e1).run (start, [])
  (net, decls.reverse, n)

/-- Do two structurally-identical samples carry the *same* constant values?  A `false` means a
    constant's value depends on `N` (out of the width-uniform scope). -/
partial def sameConsts : {w0 w1 : Nat} → Expr w0 → Expr w1 → Bool
  | _, _, e0, e1 =>
    match e0, e1 with
    | .const v0, .const v1 => v0.toNat == v1.toNat
    | .var _ _, .var _ _ => true
    | .not a0, .not a1 => sameConsts a0 a1
    | .and a0 b0, .and a1 b1 | .or a0 b0, .or a1 b1 | .xor a0 b0, .xor a1 b1
    | .add a0 b0, .add a1 b1 | .sub a0 b0, .sub a1 b1 | .mul a0 b0, .mul a1 b1
    | .shl a0 b0, .shl a1 b1 | .shr a0 b0, .shr a1 b1 | .sshr a0 b0, .sshr a1 b1
    | .udiv a0 b0, .udiv a1 b1 | .umod a0 b0, .umod a1 b1
    | .eq a0 b0, .eq a1 b1 | .ult a0 b0, .ult a1 b1 | .slt a0 b0, .slt a1 b1 =>
        sameConsts a0 a1 && sameConsts b0 b1
    | .mux s0 a0 b0, .mux s1 a1 b1 => sameConsts s0 s1 && sameConsts a0 a1 && sameConsts b0 b1
    | .concat a0 b0, .concat a1 b1 => sameConsts a0 a1 && sameConsts b0 b1
    | .zext _ a0, .zext _ a1 | .sext _ a0, .sext _ a1
    | .extract _ a0, .extract _ a1 | .slice _ _ a0, .slice _ _ a1 => sameConsts a0 a1
    | _, _ => true

/-- Emit the full parametric SystemVerilog for one width-uniform ParamModule. -/
def emitAffineVerilog (pm : LegacyMeta) : String := Id.run do
  let pn := pm.paramName
  let m0 := pm.gen 64
  let m1 := pm.gen 65
  let clk := m0.clock
  let arst := asyncResetNet m0
  -- Port declarations.
  let inDecls := (m0.inputs.zip m1.inputs).map (fun (p, p1) =>
    if some p.name == clk || some p.name == arst then s!"  input  {p.name}"
    else s!"  input  {rangeOf pn p.width p1.width}{p.name}")
  let outDecls := (m0.outputs.zip m1.outputs).map (fun (o, o1) =>
    let reg := if isRegName m0 o.name then "reg " else ""
    s!"  output {reg}{rangeOf pn o.width o1.width}{o.name}")
  let portList := String.intercalate ",\n" (inDecls ++ outDecls)
  -- Internal registers (not exposed as an output port).
  let internalRegs := (m0.regs.zip m1.regs).filterMap (fun (r, r1) =>
    if m0.outputs.any (·.name == r.name) then none
    else some s!"  reg    {rangeOf pn r.width r1.width}{r.name};")
  -- Each register's next-state cone as SSA wires, ending in `<name>_next`.
  let mut body : List String := []
  let mut warn : String := ""
  let mut ctr : Nat := 0
  for (r, r1) in m0.regs.zip m1.regs do
    let (net, decls, ctr') := runExpr pn ctr r.next r1.next
    ctr := ctr'
    body := body ++ decls ++ [s!"  wire {rangeOf pn r.width r1.width}{r.name}_next = {net};"]
    -- N-uniformity guard: a constant whose *value* depends on N (e.g. a `2^N-1` mask) is outside
    -- this emitter's width-uniform scope; flag it honestly rather than emit the N=64 value silently.
    if !(sameConsts r.next r1.next) then
      warn := "// WARNING: non-uniform (N-dependent) constant value detected — out of scope\n"
  -- Combinational (non-reg-backed) outputs.
  let mut combOuts : List String := []
  for (o, o1) in m0.outputs.zip m1.outputs do
    if !(isRegName m0 o.name) then
      let (net, decls, ctr') := runExpr pn ctr o.expr o1.expr
      ctr := ctr'
      combOuts := combOuts ++ decls ++ [s!"  assign {o.name} = {net};"]
      if !(sameConsts o.expr o1.expr) then
        warn := "// WARNING: non-uniform (N-dependent) constant value detected — out of scope\n"
  -- Sequential process.
  let sens := match clk, arst with
    | some c, some a => s!"@(posedge {c} or posedge {a})"
    | some c, none   => s!"@(posedge {c})"
    | none, _        => "@(*)"
  let resetAssigns := String.intercalate " " (m0.regs.map (fun r => s!"{r.name} <= {r.init.toNat};"))
  let normalAssigns := String.intercalate "\n      " (m0.regs.map (fun r => s!"{r.name} <= {r.name}_next;"))
  let always :=
    match arst with
    | some a =>
      s!"  always {sens} begin\n    if ({a}) begin {resetAssigns} end\n    else begin\n      {normalAssigns}\n    end\n  end"
    | none =>
      s!"  always {sens} begin\n      {normalAssigns}\n  end"
  -- Assemble.  A purely combinational module (no registers) has no clocked process.
  let proc := if m0.regs.isEmpty then [] else [always]
  let lines : List String :=
    [ warn ++ s!"module {m0.name} #(parameter {pn} = {pm.defaultN}) (",
      portList,
      ");" ] ++ internalRegs ++ body ++ combOuts ++ proc ++ ["endmodule", ""]
  return String.intercalate "\n" lines

end Legacy

/-! ## Count / generate-loop class emitter (`cascade`)

Emits genuinely two-parameter SystemVerilog for the pipelined-reduction shape: an unrolled Verilog
`for` loop sums `nsParam` elements of `widthParam` bits out of the flattened input, mirroring the
Lean `List.range NS` fold.  The output width `widthParam + $clog2(nsParam)` is emitted symbolically
(so Yosys/icarus recompute it per override), and the reset is the design's async active-low `rst_n`.
Port names are read from the (verified) module so nothing but the *shape* is templated; correctness
is anchored per-`(W,NS)` by the equivalence miter against `compile (impl W NS)`. -/
def emitCascadeVerilog (pm : LegacyMeta) (cfg : CascadeCfg) : String :=
  let m      := pm.gen 64
  let name   := m.name
  let ins    := m.inputs.map (·.name)
  let outs   := m.outputs.map (·.name)
  let clk    := ins.getD 0 "clk"
  let rstn   := ins.getD 1 "rst_n"
  let ivalid := ins.getD 2 "i_valid"
  let idata  := ins.getD 3 "i_data"
  let ovalid := outs.getD 0 "o_valid"
  let odata  := outs.getD 1 "o_data"
  let W      := cfg.widthParam
  let NS     := cfg.nsParam
  String.intercalate "\n"
    [ s!"module {name} #(parameter {W} = {cfg.widthDefault}, parameter {NS} = {cfg.nsDefault}) (",
      s!"  input  {clk},",
      s!"  input  {rstn},",
      s!"  input  {ivalid},",
      s!"  input  [{W}*{NS}-1:0] {idata},",
      s!"  output reg {ovalid},",
      s!"  output reg [{W}+$clog2({NS})-1:0] {odata}",
      ");",
      s!"  localparam OW = {W} + $clog2({NS});",
      s!"  reg [{W}*{NS}-1:0] data_reg;",
      "  reg valid_reg;",
      "  integer k;",
      "  reg [OW-1:0] sum_comb;",
      "  always @(*) begin",
      "    sum_comb = 0;",
      s!"    for (k = 0; k < {NS}; k = k + 1)",
      s!"      sum_comb = sum_comb + data_reg[k*{W} +: {W}];",
      "  end",
      s!"  always @(posedge {clk} or negedge {rstn}) begin",
      s!"    if (!{rstn}) begin",
      s!"      data_reg <= 0; valid_reg <= 0; {odata} <= 0; {ovalid} <= 0;",
      "    end else begin",
      s!"      data_reg <= {idata};",
      s!"      valid_reg <= {ivalid};",
      s!"      {odata} <= sum_comb;",
      s!"      {ovalid} <= valid_reg;",
      "    end",
      "  end",
      "endmodule", "" ]

/-! ## Memory-depth class emitter (`memLifo`)

Emits a genuinely parametric synchronous LIFO whose depth is `2^ADDR`.  The storage is a Verilog
memory array `reg [DW-1:0] mem [0:2^ADDR-1]` (Yosys keeps it parametric and re-elaborates per
override), and the top-of-stack pointer / full / empty logic is `ADDR`-parametric.  This mirrors the
Lean `impl`, whose memory is a `List` of `2^ADDR` registers with a list-induction read-select proof
(RAM.lean pattern) — so the array never blows up a SAT solver.  Validated per-`N` by the miter
against `compile (impl N)`. -/
def emitMemLifoVerilog (pm : LegacyMeta) (cfg : MemLifoCfg) : String :=
  let m     := pm.gen cfg.addrDefault
  let name  := m.name
  let ins   := m.inputs.map (·.name)
  let outs  := m.outputs.map (·.name)
  let clk   := ins.getD 0 "clock"
  let rst   := ins.getD 1 "reset"
  let wen   := ins.getD 2 "write_en"
  let ren   := ins.getD 3 "read_en"
  let din   := ins.getD 4 "data_in"
  let empt  := outs.getD 0 "empty"
  let ful   := outs.getD 1 "full"
  let dout  := outs.getD 2 "data_out"
  let DW    := cfg.dataParam
  let AW    := cfg.addrParam
  String.intercalate "\n"
    [ s!"module {name} #(parameter {DW} = {cfg.dataDefault}, parameter {AW} = {cfg.addrDefault}) (",
      s!"  input  {clk},",
      s!"  input  {rst},",
      s!"  input  {wen},",
      s!"  input  {ren},",
      s!"  input  [{DW}-1:0] {din},",
      s!"  output {empt},",
      s!"  output {ful},",
      s!"  output reg [{DW}-1:0] {dout}",
      ");",
      s!"  localparam DEPTH = (1 << {AW});",
      s!"  reg [{DW}-1:0] mem [0:DEPTH-1];",
      s!"  reg [{AW}:0] top;",
      "  integer i;",
      -- read/write indices masked to AW bits (= top mod 2^AW), mirroring the Lean `slice 0 AW`.
      s!"  wire [{AW}-1:0] widx  = top[{AW}-1:0];",
      s!"  wire [{AW}:0]   topm1 = top - 1;",
      s!"  wire [{AW}-1:0] ridx  = topm1[{AW}-1:0];",
      s!"  assign {empt} = (top == 0);",
      s!"  assign {ful}  = (top == DEPTH);",
      s!"  always @(posedge {clk}) begin",
      s!"    if ({rst}) begin",
      "      top <= 0;",
      s!"      {dout} <= 0;",
      "      for (i = 0; i < DEPTH; i = i + 1) mem[i] <= 0;",
      "    end else begin",
      s!"      if ({wen} && !(top == DEPTH)) begin",
      s!"        {emitGuardedArrayWrite "mem" "widx" "DEPTH" din}",
      "        top <= top + 1;",
      s!"      end else if ({ren} && !(top == 0)) begin",
      s!"        {dout} <= mem[ridx];",
      "        top <= top - 1;",
      "      end",
      "    end",
      "  end",
      "endmodule", "" ]

/-! ## FILO class emitter (`filo`) — raw-count depth + feedthrough

Like `memLifo`, but the depth `FILO_DEPTH` is a raw count (not a power of two), so the pointer is
`PW = $clog2(FILO_DEPTH+1)` bits and the physical array is sized to the pointer's full range
`CAP = 2^PW` (matching the Lean `impl`, whose `cap D` array keeps every index in range so the miter's
`equiv_induct` never hits an out-of-bounds read).  `full` compares the pointer to the raw count `D`.
The `feed` branch (empty & push & pop) passes `data_in` straight to `data_out` with no store,
priority feed ≻ push ≻ pop.  Reset is folded synchronously in-band (the `sync_lifo` path).  Anchored
per-`N` by the equivalence miter against `compile (impl DW D)`. -/
def emitFiloVerilog (pm : LegacyMeta) (cfg : FiloCfg) : String :=
  let m     := pm.gen cfg.depthDefault
  let name  := m.name
  let ins   := m.inputs.map (·.name)
  let outs  := m.outputs.map (·.name)
  let clk   := ins.getD 0 "clk"
  let rst   := ins.getD 1 "reset"
  let push  := ins.getD 2 "push"
  let pop   := ins.getD 3 "pop"
  let din   := ins.getD 4 "data_in"
  let dout  := outs.getD 0 "data_out"
  let ful   := outs.getD 1 "full"
  let empt  := outs.getD 2 "empty"
  let DW    := cfg.dataParam
  let D     := cfg.depthParam
  String.intercalate "\n"
    [ s!"module {name} #(parameter {DW} = {cfg.dataDefault}, parameter {D} = {cfg.depthDefault}) (",
      s!"  input  {clk},",
      s!"  input  {rst},",
      s!"  input  {push},",
      s!"  input  {pop},",
      s!"  input  [{DW}-1:0] {din},",
      s!"  output reg [{DW}-1:0] {dout},",
      s!"  output {ful},",
      s!"  output {empt}",
      ");",
      s!"  localparam PW  = $clog2({D}+1);",
      s!"  localparam CAP = (1 << PW);",
      s!"  reg [{DW}-1:0] mem [0:CAP-1];",
      s!"  reg [PW-1:0] top;",
      "  integer i;",
      s!"  wire feed  = {push} & {pop} & (top == 0);",
      s!"  wire cpush = {push} & (top != {D});",
      s!"  wire cpop  = {pop}  & (top != 0);",
      s!"  assign {ful}  = (top == {D});",
      s!"  assign {empt} = (top == 0);",
      s!"  always @(posedge {clk}) begin",
      s!"    if ({rst}) begin",
      "      top <= 0;",
      s!"      {dout} <= 0;",
      "      for (i = 0; i < CAP; i = i + 1) mem[i] <= 0;",
      "    end else begin",
      "      if (feed) begin",
      s!"        {dout} <= {din};",
      "      end else if (cpush) begin",
      s!"        {emitGuardedArrayWrite "mem" "top" "CAP" din}",
      "        top <= top + 1;",
      "      end else if (cpop) begin",
      s!"        {dout} <= mem[top-1];",
      "        top <= top - 1;",
      "      end",
      "    end",
      "  end",
      "endmodule", "" ]

/-! ## FIR class emitter (`fir`) — packed dual-bus element-wise signed MAC

Emits a genuinely three-parameter SystemVerilog FIR: register both packed input buses (`data_in`,
`coeffs`) when `valid_in` (sync reset), then combinationally multiply each `DATA_WIDTH`-bit signed
sample by the **reverse-order** `COEFF_WIDTH`-bit signed coefficient and sum, sign-extending every
product to the `NBW_MULT+$clog2(NUM_TAPS)` output width so nothing truncates.  `valid_out` is the
registered `valid_in`.  Mirrors the Lean `impl`'s `List.range NUM_TAPS` fold; anchored per-`N` by the
equivalence miter against `compile (impl …)`. -/
def emitFirVerilog (pm : LegacyMeta) (cfg : FirCfg) : String :=
  let m      := pm.gen cfg.dataDefault
  let name   := m.name
  let ins    := m.inputs.map (·.name)
  let outs   := m.outputs.map (·.name)
  let clk    := ins.getD 0 "clk"
  let rst    := ins.getD 1 "reset"
  let din    := ins.getD 2 "data_in"
  let vin    := ins.getD 3 "valid_in"
  let coef   := ins.getD 4 "coeffs"
  let dout   := outs.getD 0 "data_out"
  let vout   := outs.getD 1 "valid_out"
  let DW     := cfg.dataParam
  let CW     := cfg.coeffParam
  let NT     := cfg.tapsParam
  String.intercalate "\n"
    [ s!"module {name} #(parameter {DW} = {cfg.dataDefault}, parameter {CW} = {cfg.coeffDefault}, parameter {NT} = {cfg.tapsDefault}) (",
      s!"  input  {clk},",
      s!"  input  {rst},",
      s!"  input  [{DW}*{NT}-1:0] {din},",
      s!"  input  {vin},",
      s!"  input  [{CW}*{NT}-1:0] {coef},",
      s!"  output reg [{DW}+{CW}+$clog2({NT})-1:0] {dout},",
      s!"  output reg {vout}",
      ");",
      s!"  localparam OW = {DW} + {CW} + $clog2({NT});",
      s!"  reg [{DW}*{NT}-1:0] data_reg;",
      s!"  reg [{CW}*{NT}-1:0] coeff_reg;",
      "  integer k;",
      s!"  reg signed [{DW}-1:0] d_k;",
      s!"  reg signed [{CW}-1:0] c_k;",
      "  reg signed [OW-1:0] acc;",
      -- data_out is COMBINATIONAL (the registered-input MAC): a second dff stage would read one
      -- delta late under cocotb's edge-sampled model.  Only the inputs and `valid` are registered.
      -- `acc` MUST be a signed accumulator: adding into the unsigned output port would evaluate the
      -- signed products in an unsigned context and zero-extend them.
      "  always @(*) begin",
      "    acc = 0;",
      s!"    for (k = 0; k < {NT}; k = k + 1) begin",
      s!"      d_k = data_reg [k*{DW} +: {DW}];",
      s!"      c_k = coeff_reg[({NT}-1-k)*{CW} +: {CW}];",
      "      acc = acc + $signed(d_k) * $signed(c_k);",
      "    end",
      s!"    {dout} = acc;",
      "  end",
      s!"  always @(posedge {clk}) begin",
      s!"    if ({rst}) begin",
      "      data_reg <= 0; coeff_reg <= 0;",
      s!"      {vout} <= 0;",
      "    end else begin",
      s!"      if ({vin}) begin",
      s!"        data_reg  <= {din};",
      s!"        coeff_reg <= {coef};",
      "      end",
      s!"      {vout} <= {vin};",
      "    end",
      "  end",
      "endmodule", "" ]

/-! ## Swizzle class emitter (`swizzle`) — combinational `sel`-selected chunk-reversal

Emits combinational SystemVerilog that reverses `data_in` in `2^sel` equal chunks (sel 0..3): a
per-`sel` `for` loop maps output bit `i` to input bit `(i/K)*K + (K-1 - i%K)` with chunk size
`K = DATA_WIDTH >> sel`, mirroring the Lean `impl`.  Anchored per-`N` by the combinational
equivalence miter against `compile (impl DATA_WIDTH)`. -/
def emitSwizzleVerilog (pm : LegacyMeta) (cfg : SwizzleCfg) : String :=
  let m    := pm.gen cfg.dataDefault
  let name := m.name
  let ins  := m.inputs.map (·.name)
  let outs := m.outputs.map (·.name)
  let din  := ins.getD 0 "data_in"
  let sel  := ins.getD 1 "sel"
  let dout := outs.getD 0 "data_out"
  let W    := cfg.dataParam
  let loopFor (k : String) : String :=
    s!"for (i = 0; i < {W}; i = i + 1) {dout}[(i/({k}))*({k}) + (({k})-1 - i%({k}))] = {din}[i];"
  String.intercalate "\n"
    [ s!"module {name} #(parameter {W} = {cfg.dataDefault}) (",
      s!"  input  [{W}-1:0] {din},",
      s!"  input  [1:0] {sel},",
      s!"  output reg [{W}-1:0] {dout}",
      ");",
      "  integer i;",
      "  always @(*) begin",
      s!"    case ({sel})",
      s!"      2'd0: {loopFor W}",
      s!"      2'd1: {loopFor s!"{W}/2"}",
      s!"      2'd2: {loopFor s!"{W}/4"}",
      s!"      2'd3: {loopFor s!"{W}/8"}",
      s!"      default: {dout} = {din};",
      "    endcase",
      "  end",
      "endmodule", "" ]

/-! ## Packed-parametric-port class emitter (`qamMap`) — QAM16 mapper generate-loop

Emits genuinely packed-array parametric ports: `bits : N*IN_WIDTH`, `I`/`Q : (N+N/2)*OUT_WIDTH`, with a
`generate` loop over the `N/2` symbol pairs.  For each pair the two symbols' MSB/LSB 2-bit codes are
mapped by the QAM amplitude law `2m−3` (`(code<<1)-3` in `OUT_WIDTH` bits) and the interpolated middle
element is `⌊(a+b)/2⌋` (signed add in `OUT_WIDTH+1` bits, arithmetic `>>> 1`), each element assigned
into its `OUT_WIDTH`-bit slice with element 0 in the most-significant slice — mirroring the Lean
`impl`'s OR-of-shifted-placements.  `IN_WIDTH`/`OUT_WIDTH` are fixed `parameter`s (4/3) so only `N` is
swept; anchored per-`N` by the combinational equivalence miter against `compile (impl N)`. -/
def emitQamMapVerilog (pm : LegacyMeta) (cfg : QamMapCfg) : String :=
  let m    := pm.gen cfg.nDefault
  let name := m.name
  let ins  := m.inputs.map (·.name)
  let outs := m.outputs.map (·.name)
  let bits := ins.getD 0 "bits"
  let iOut := outs.getD 0 "I"
  let qOut := outs.getD 1 "Q"
  let N    := cfg.nParam
  String.intercalate "\n"
    [ s!"module {name} #(parameter {N} = {cfg.nDefault}, parameter IN_WIDTH = 4, parameter OUT_WIDTH = 3) (",
      s!"  input  [{N}*IN_WIDTH-1:0] {bits},",
      s!"  output [({N}+{N}/2)*OUT_WIDTH-1:0] {iOut},",
      s!"  output [({N}+{N}/2)*OUT_WIDTH-1:0] {qOut}",
      ");",
      s!"  localparam T = {N} + {N}/2;",
      "  genvar gi;",
      "  generate",
      s!"    for (gi = 0; gi < {N}/2; gi = gi + 1) begin : pair",
      -- symbol 2*gi and 2*gi+1 (symbol 0 in the most-significant input slice)
      s!"      wire [1:0] msb_a = {bits}[({N}-1-(2*gi))*IN_WIDTH + IN_WIDTH-1 -: 2];",
      s!"      wire [1:0] lsb_a = {bits}[({N}-1-(2*gi))*IN_WIDTH + 1 -: 2];",
      s!"      wire [1:0] msb_b = {bits}[({N}-1-(2*gi+1))*IN_WIDTH + IN_WIDTH-1 -: 2];",
      s!"      wire [1:0] lsb_b = {bits}[({N}-1-(2*gi+1))*IN_WIDTH + 1 -: 2];",
      "      wire [OUT_WIDTH-1:0] mI_a = (msb_a << 1) - 3;",
      "      wire [OUT_WIDTH-1:0] mI_b = (msb_b << 1) - 3;",
      "      wire [OUT_WIDTH-1:0] mQ_a = (lsb_a << 1) - 3;",
      "      wire [OUT_WIDTH-1:0] mQ_b = (lsb_b << 1) - 3;",
      "      wire signed [OUT_WIDTH:0] sumI = $signed(mI_a) + $signed(mI_b);",
      "      wire signed [OUT_WIDTH:0] sumQ = $signed(mQ_a) + $signed(mQ_b);",
      "      wire [OUT_WIDTH-1:0] interpI = sumI >>> 1;",
      "      wire [OUT_WIDTH-1:0] interpQ = sumQ >>> 1;",
      s!"      assign {iOut}[(T-1-(3*gi))*OUT_WIDTH   +: OUT_WIDTH] = mI_a;",
      s!"      assign {iOut}[(T-1-(3*gi+1))*OUT_WIDTH +: OUT_WIDTH] = interpI;",
      s!"      assign {iOut}[(T-1-(3*gi+2))*OUT_WIDTH +: OUT_WIDTH] = mI_b;",
      s!"      assign {qOut}[(T-1-(3*gi))*OUT_WIDTH   +: OUT_WIDTH] = mQ_a;",
      s!"      assign {qOut}[(T-1-(3*gi+1))*OUT_WIDTH +: OUT_WIDTH] = interpQ;",
      s!"      assign {qOut}[(T-1-(3*gi+2))*OUT_WIDTH +: OUT_WIDTH] = mQ_b;",
      "    end",
      "  endgenerate",
      "endmodule", "" ]

/-! ## Packed-parametric-port class emitter (`qamDemap`) — QAM16 demapper generate-loop + error fold

The dual of `qamMap`: packed I/Q input buses (`(N+N/2)*IN_WIDTH`, `IN_WIDTH = 3`) are demapped to
`bits : N*OUT_WIDTH` (`OUT_WIDTH = 4`) by recovering each mapped sample's 2-bit code
`code = (sample+3) >> 1` (the inverse of `2m−3`), packing the `I`-code as the symbol's MSBs and the
`Q`-code as its LSBs.  A global `error_flag` is the OR over the `N/2` pairs of
`|⌊(a+b)/2⌋ − interp| > ERROR_THRESHOLD` for both I and Q (mapped samples `a,b` at pair positions
`3i,3i+2`, interpolated sample at `3i+1`).  Anchored per-`N` by the combinational equivalence miter
against `compile (impl N)`. -/
def emitQamDemapVerilog (pm : LegacyMeta) (cfg : QamDemapCfg) : String :=
  let m    := pm.gen cfg.nDefault
  let name := m.name
  let ins  := m.inputs.map (·.name)
  let outs := m.outputs.map (·.name)
  let iIn  := ins.getD 0 "I"
  let qIn  := ins.getD 1 "Q"
  let bits := outs.getD 0 "bits"
  let eflg := outs.getD 1 "error_flag"
  let N    := cfg.nParam
  String.intercalate "\n"
    [ s!"module {name} #(parameter {N} = {cfg.nDefault}, parameter IN_WIDTH = 3, parameter OUT_WIDTH = 4, parameter ERROR_THRESHOLD = {cfg.threshold}) (",
      s!"  input  [({N}+{N}/2)*IN_WIDTH-1:0] {iIn},",
      s!"  input  [({N}+{N}/2)*IN_WIDTH-1:0] {qIn},",
      s!"  output [{N}*OUT_WIDTH-1:0] {bits},",
      s!"  output {eflg}",
      ");",
      s!"  localparam T = {N} + {N}/2;",
      -- per-pair error terms OR-reduced into a single flag
      s!"  wire [{N}/2-1:0] err_terms;",
      "  genvar gi;",
      "  generate",
      s!"    for (gi = 0; gi < {N}/2; gi = gi + 1) begin : pair",
      -- mapped samples a=pos 3gi, b=pos 3gi+2; interpolated=pos 3gi+1 (element 0 in the MSB slice).
      -- Samples are held UNSIGNED (raw bits); `$signed(...)` is applied where signed math is meant, so
      -- the code path is 3-bit wrap-around (matching the Lean `impl`) and the error path is signed.
      s!"      wire [IN_WIDTH-1:0] a_i = {iIn}[(T-1-(3*gi))*IN_WIDTH   +: IN_WIDTH];",
      s!"      wire [IN_WIDTH-1:0] p_i = {iIn}[(T-1-(3*gi+1))*IN_WIDTH +: IN_WIDTH];",
      s!"      wire [IN_WIDTH-1:0] b_i = {iIn}[(T-1-(3*gi+2))*IN_WIDTH +: IN_WIDTH];",
      s!"      wire [IN_WIDTH-1:0] a_q = {qIn}[(T-1-(3*gi))*IN_WIDTH   +: IN_WIDTH];",
      s!"      wire [IN_WIDTH-1:0] p_q = {qIn}[(T-1-(3*gi+1))*IN_WIDTH +: IN_WIDTH];",
      s!"      wire [IN_WIDTH-1:0] b_q = {qIn}[(T-1-(3*gi+2))*IN_WIDTH +: IN_WIDTH];",
      -- expected interpolation avg = floor((a+b)/2) in IN_WIDTH+1 bits, deviation vs actual
      "      wire signed [IN_WIDTH:0] avgI = ($signed(a_i) + $signed(b_i)) >>> 1;",
      "      wire signed [IN_WIDTH:0] avgQ = ($signed(a_q) + $signed(b_q)) >>> 1;",
      "      wire signed [IN_WIDTH:0] devI = avgI - $signed(p_i);",
      "      wire signed [IN_WIDTH:0] devQ = avgQ - $signed(p_q);",
      "      wire [IN_WIDTH:0] absI = devI[IN_WIDTH] ? (-devI) : devI;",
      "      wire [IN_WIDTH:0] absQ = devQ[IN_WIDTH] ? (-devQ) : devQ;",
      s!"      assign err_terms[gi] = (absI > ERROR_THRESHOLD) | (absQ > ERROR_THRESHOLD);",
      -- demap the two mapped samples -> symbols 2gi, 2gi+1: code = ((sample+3) mod 2^IN_WIDTH)[hi:hi-1],
      -- i.e. the inverse of the mapper's 2m-3, done in unsigned IN_WIDTH-bit wrap (matching `impl`).
      "      wire [IN_WIDTH-1:0] spIa = a_i + 3;  wire [1:0] codeIa = spIa[IN_WIDTH-1:IN_WIDTH-2];",
      "      wire [IN_WIDTH-1:0] spQa = a_q + 3;  wire [1:0] codeQa = spQa[IN_WIDTH-1:IN_WIDTH-2];",
      "      wire [IN_WIDTH-1:0] spIb = b_i + 3;  wire [1:0] codeIb = spIb[IN_WIDTH-1:IN_WIDTH-2];",
      "      wire [IN_WIDTH-1:0] spQb = b_q + 3;  wire [1:0] codeQb = spQb[IN_WIDTH-1:IN_WIDTH-2];",
      s!"      assign {bits}[({N}-1-(2*gi))*OUT_WIDTH   +: OUT_WIDTH] = " ++ "{codeIa, codeQa};",
      s!"      assign {bits}[({N}-1-(2*gi+1))*OUT_WIDTH +: OUT_WIDTH] = " ++ "{codeIb, codeQb};",
      "    end",
      "  endgenerate",
      s!"  assign {eflg} = |err_terms;",
      "endmodule", "" ]

/-! ## Value-dependent generate class emitter (`prbs`) — LFSR with a value-indexed feedback tap

Emits a `WIDTH`-parallel PRBS generator/checker whose feedback bit `cur[POLY_LENGTH − POLY_TAP] ⊕
cur[0]` selects a register bit at an index that is a **function of the parameter value** — the
value-dependent F2 subclass (not merely a scaled width).  A combinational `for` loop unrolls the
`WIDTH` sub-steps of the shift/insert, mirroring the Lean `impl`'s `List.range WIDTH` fold; the clocked
block registers `lfsr`/`data_out` with a synchronous all-ones reset, and `CHECK_MODE` selects the
generator (`outbits`) or checker (`data_in ⊕ outbits`) output.  Sequential equivalence miter anchors it
per-`N` to `compile (impl …)`. -/
def emitPrbsVerilog (pm : LegacyMeta) (cfg : PrbsCfg) : String :=
  let m    := pm.gen cfg.widthDefault
  let name := m.name
  let ins  := m.inputs.map (·.name)
  let outs := m.outputs.map (·.name)
  let clk  := ins.getD 0 "clk"
  let rst  := ins.getD 1 "rst"
  let din  := ins.getD 2 "data_in"
  let dout := outs.getD 0 "data_out"
  let CM   := cfg.modeParam
  let L    := cfg.lenParam
  let P    := cfg.tapParam
  let W    := cfg.widthParam
  String.intercalate "\n"
    [ s!"module {name} #(parameter {CM} = {cfg.modeDefault}, parameter {L} = {cfg.lenDefault}, parameter {P} = {cfg.tapDefault}, parameter {W} = {cfg.widthDefault}) (",
      s!"  input  {clk},",
      s!"  input  {rst},",
      s!"  input  [{W}-1:0] {din},",
      s!"  output reg [{W}-1:0] {dout}",
      ");",
      s!"  reg [{L}-1:0] lfsr;",
      s!"  reg [{L}-1:0] cur;",
      s!"  reg [{W}-1:0] outbits;",
      "  reg xa;",
      "  integer i;",
      "  always @(*) begin",
      "    cur = lfsr;",
      "    outbits = 0;",
      s!"    for (i = 0; i < {W}; i = i + 1) begin",
      -- value-dependent tap: index POLY_LENGTH-POLY_TAP is a function of the parameter values
      s!"      xa = cur[{L}-{P}] ^ cur[0];",
      "      outbits[i] = xa;",
      "      cur = cur >> 1;",
      s!"      cur[{L}-1] = xa;",
      "    end",
      "  end",
      s!"  always @(posedge {clk}) begin",
      s!"    if ({rst}) begin",
      s!"      lfsr <= " ++ "{" ++ s!"{L}" ++ "{1'b1}};",
      s!"      {dout} <= " ++ "{" ++ s!"{W}" ++ "{1'b1}};",
      "    end else begin",
      "      lfsr <= cur;",
      s!"      if ({CM} == 0) {dout} <= outbits;",
      s!"      else {dout} <= {din} ^ outbits;",
      "    end",
      "  end",
      "endmodule", "" ]

/-! ## Iterative divider class emitter (`restoreDiv`) — multi-cycle restoring division

Emits a `WIDTH`-bit restoring divider that consumes one dividend bit per clock over `WIDTH` cycles.
The FSM (`IDLE`/`RUN`/`FIN`) and the FF set (`state`,`cnt`,`divisor_r`,`quotient`,`remainder`,`valid`)
mirror the Lean `impl` register-for-register, and each register's next-state is the same in-band
(active-**low** synchronous) reset + restoring-division step proved ∀N in `RestoreDiv.next_correct`.
The `N+1`-bit shift/compare intermediate (`remsh`,`dext`) and the value-dependent finish comparison
`cnt == WIDTH-1` are emitted symbolically (so Yosys/icarus re-elaborate them per override); the
per-`N` sequential equivalence miter anchors the emission to `compile (impl N)`. -/
def emitRestoreDivVerilog (pm : LegacyMeta) (cfg : RestoreDivCfg) : String :=
  let m     := pm.gen cfg.widthDefault
  let name  := m.name
  let ins   := m.inputs.map (·.name)
  let clk   := ins.getD 0 "clk"
  let rst   := ins.getD 1 "rst"
  let start := ins.getD 2 "start"
  let dvd   := ins.getD 3 "dividend"
  let dvs   := ins.getD 4 "divisor"
  let W     := cfg.widthParam
  String.intercalate "\n"
    [ s!"module {name} #(parameter {W} = {cfg.widthDefault}) (",
      s!"  input  {clk},",
      s!"  input  {rst},",
      s!"  input  {start},",
      s!"  input  [{W}-1:0] {dvd},",
      s!"  input  [{W}-1:0] {dvs},",
      s!"  output reg [{W}-1:0] quotient,",
      s!"  output reg [{W}-1:0] remainder,",
      s!"  output reg valid",
      ");",
      "  localparam IDLE = 2'd0, RUN = 2'd1, FIN = 2'd2;",
      "  reg [1:0] state;",
      s!"  reg [{W}-1:0] cnt;",
      s!"  reg [{W}-1:0] divisor_r;",
      -- one restoring-division step (combinational), matching the Lean `remStep`/`quoStep`:
      s!"  wire            nextbit  = quotient[{W}-1];",
      s!"  wire [{W}:0]    remsh    = " ++ "{remainder, nextbit};",
      s!"  wire [{W}:0]    dext     = " ++ "{1'b0, divisor_r};",
      "  wire            ge       = (remsh >= dext);",
      "  wire [" ++ W ++ ":0]    remw     = ge ? (remsh - dext) : remsh;",
      s!"  wire [{W}-1:0]  rem_step = remw[{W}-1:0];",
      s!"  wire [{W}-1:0]  quo_step = (quotient << 1) | ge;",
      s!"  always @(posedge {clk}) begin",
      s!"    if (!{rst}) begin",
      "      state <= IDLE; cnt <= 0; divisor_r <= 0; quotient <= 0; remainder <= 0; valid <= 0;",
      "    end else begin",
      "      case (state)",
      "        IDLE: begin",
      "          valid <= 0;",
      s!"          if ({start}) begin quotient <= {dvd}; remainder <= 0; divisor_r <= {dvs}; cnt <= 0; state <= RUN; end",
      "        end",
      "        RUN: begin",
      "          remainder <= rem_step; quotient <= quo_step; cnt <= cnt + 1; valid <= 0;",
      s!"          if (cnt == {W}-1) state <= FIN; else state <= RUN;",
      "        end",
      "        FIN: begin state <= IDLE; valid <= 1; end",
      "        default: begin state <= IDLE; valid <= 0; end",
      "      endcase",
      "    end",
      "  end",
      "endmodule", "" ]

/-! ## Bubble-sort class emitter (`sort`) — iterative compare-swap over a parametric array

Emits a two-parameter (`N`, `WIDTH`) `sorting_engine` whose FF set mirrors `Param.Sorter.impl WIDTH N`
register-for-register: the `N`-element `arr` array, the `IDLE/SORTING/DONE` FSM (`state`), the 16-bit
`cnt` / 8-bit `pos` (the exact fixed widths of the Lean `impl`, so the per-`N` `equiv_induct` miter
lines up), the registered `done` pulse and the packed `out_data` latch.  The compare-swap writes
`min`/`max` of the `(arr[pos], arr[pos+1])` pair — guarded by `pos < N-1` so it matches the Lean
`impl` (whose edge entries `arr[0]`/`arr[N-1]` carry only the lower/upper term) even for the
unreachable `pos ≥ N-1` states the miter's induction may explore.  Synchronous active-high `rst`
folded in-band (the `impl`'s `reset = none` path). -/
def emitSortVerilog (pm : LegacyMeta) (cfg : SortCfg) : String :=
  let m     := pm.gen cfg.nDefault
  let name  := m.name
  let N     := cfg.nParam
  let W     := cfg.widthParam
  String.intercalate "\n"
    [ s!"module {name} #(parameter {N} = {cfg.nDefault}, parameter {W} = {cfg.widthDefault}) (",
      "  input  clk,",
      "  input  rst,",
      "  input  start,",
      s!"  input  [{N}*{W}-1:0] in_data,",
      "  output reg done,",
      s!"  output reg [{N}*{W}-1:0] out_data",
      ");",
      s!"  reg [{W}-1:0] arr [0:{N}-1];",
      "  reg [1:0]  state;",
      "  reg [15:0] cnt;",
      "  reg [7:0]  pos;",
      "  integer i;",
      "  always @(posedge clk) begin",
      "    if (rst) begin",
      "      state <= 0; cnt <= 0; pos <= 0; done <= 0; out_data <= 0;",
      s!"      for (i = 0; i < {N}; i = i + 1) arr[i] <= 0;",
      "    end else begin",
      "      done <= (state == 2'd2);",
      "      if (state == 2'd2)",
      s!"        for (i = 0; i < {N}; i = i + 1) out_data[i*{W} +: {W}] <= arr[i];",
      "      case (state)",
      "        2'd0: begin",
      "          if (start) begin",
      s!"            for (i = 0; i < {N}; i = i + 1) arr[i] <= in_data[i*{W} +: {W}];",
      "            cnt <= 0; pos <= 0; state <= 2'd1;",
      "          end",
      "        end",
      "        2'd1: begin",
      s!"          if (pos < {N}-1) begin",
      s!"            {emitGuardedArrayWrite "arr" "pos"   N "(arr[pos] < arr[pos+1]) ? arr[pos]   : arr[pos+1]"}",
      s!"            {emitGuardedArrayWrite "arr" "pos+1" N "(arr[pos] < arr[pos+1]) ? arr[pos+1] : arr[pos]"}",
      "          end",
      s!"          pos <= (pos == {N}-2) ? 0 : pos + 1;",
      "          cnt <= cnt + 1;",
      s!"          if (cnt == {N}*({N}-1)-1) state <= 2'd2;",
      "        end",
      "        2'd2: state <= 2'd0;",
      "        default: state <= 2'd0;",
      "      endcase",
      "    end",
      "  end",
      "endmodule", "" ]

/-! ## Fall-through queue class emitter (`queue`) — shift-on-read storage + fill pointer

Emits a genuinely four-parameter (`DEPTH`, `DBITS`, `ALMOST_EMPTY_THRESHOLD`,
`ALMOST_FULL_THRESHOLD`) first-word-fall-through queue mirroring `Param.QueueFwft.impl`
register-for-register: the `DEPTH`-entry `queue_data` array (yosys `memory` splits it back into the
per-word FFs `queue_data[i]`, matching the Lean register names for the miter's induction), the
`$clog2(DEPTH+1)`-bit fill pointer `queue_wadr`, async active-low `rst_ni` (a real
`always @(posedge clk_i or negedge rst_ni)`, the gold side's `$adff` on `nrst = ~rst_ni`),
synchronous `clr_i`, clock-enable `ena_i`, and the `{we_i,re_i}` operation case (write at pointer /
shift down + zero-fill tail / shift + insert at the vacated slot with the empty write-through
special case).  Status outputs are combinational functions of the pointer; the almost thresholds
are clamped to `[0, DEPTH]` by "_CHECK" localparams (mirroring the Lean `aeEff`/`afEff`) and
compared at pointer width so nothing truncates.  Anchored per-`N` on every parameter axis by the
sequential equivalence miter against `compile (impl DBITS DEPTH AET AFT)`. -/
def emitQueueVerilog (pm : LegacyMeta) (cfg : QueueCfg) : String :=
  let m    := pm.gen pm.defaultN
  let ins  := m.inputs.map (·.name)
  let outs := m.outputs.map (·.name)
  let clk  := ins.getD 0 "clk_i"
  let rstn := ins.getD 1 "rst_ni"
  let clr  := ins.getD 2 "clr_i"
  let ena  := ins.getD 3 "ena_i"
  let we   := ins.getD 4 "we_i"
  let din  := ins.getD 5 "d_i"
  let re   := ins.getD 6 "re_i"
  let q    := outs.getD 0 "q_o"
  let empt := outs.getD 1 "empty_o"
  let ful  := outs.getD 2 "full_o"
  let aemp := outs.getD 3 "almost_empty_o"
  let aful := outs.getD 4 "almost_full_o"
  let D    := cfg.depthParam
  let DW   := cfg.dataParam
  let AE   := cfg.aeParam
  let AF   := cfg.afParam
  String.intercalate "\n"
    [ s!"module {m.name} #(",
      s!"  parameter integer {D} = {cfg.depthDefault},",
      s!"  parameter integer {DW} = {cfg.dataDefault},",
      s!"  parameter integer {AE} = {cfg.aeDefault},",
      s!"  parameter integer {AF} = {D}",
      ") (",
      s!"  input  wire            {clk},",
      s!"  input  wire            {rstn},",
      s!"  input  wire            {clr},",
      s!"  input  wire            {ena},",
      s!"  input  wire            {we},",
      s!"  input  wire [{DW}-1:0] {din},",
      s!"  input  wire            {re},",
      s!"  output wire [{DW}-1:0] {q},",
      s!"  output wire            {empt},",
      s!"  output wire            {ful},",
      s!"  output wire            {aemp},",
      s!"  output wire            {aful}",
      ");",
      s!"  localparam integer PW = $clog2({D}+1);",
      s!"  localparam integer FULL_THRESHOLD = {D};",
      s!"  localparam integer {AE}_CHECK =",
      s!"      ({AE} < 0) ? 0 : ({AE} > {D}) ? {D} : {AE};",
      s!"  localparam integer {AF}_CHECK =",
      s!"      ({AF} < 0) ? 0 : ({AF} > {D}) ? {D} : {AF};",
      "",
      s!"  reg [{DW}-1:0] queue_data [0:{D}-1];",
      "  reg [PW-1:0]    queue_wadr;",
      "  integer n;",
      "",
      "  // fill-level pointer",
      s!"  always @(posedge {clk} or negedge {rstn})",
      s!"    if      (!{rstn}) queue_wadr <= " ++ "{PW{1'b0}};",
      s!"    else if ( {clr} ) queue_wadr <= " ++ "{PW{1'b0}};",
      s!"    else if ( {ena} )",
      s!"      case (" ++ "{" ++ s!"{we}, {re}" ++ "})",
      "        2'b01  : queue_wadr <= queue_wadr - 1'b1;   // read: one entry drained",
      "        2'b10  : queue_wadr <= queue_wadr + 1'b1;   // write: one entry added",
      -- simultaneous read+write: net-zero when non-empty (one out, one in), but an empty-queue
      -- write-through (queue_wadr == 0) has nothing to read out, so it genuinely adds an entry
      -- (0->1) -- the transition that lets full_o reach DEPTH after DEPTH writes.
      "        2'b11  : if (queue_wadr == " ++ "{PW{1'b0}}" ++ ") queue_wadr <= queue_wadr + 1'b1;  // simultaneous on empty: +1 (else holds)",
      "        default: ;                                  // idle: unchanged",
      "      endcase",
      "",
      "  // fall-through storage",
      s!"  always @(posedge {clk} or negedge {rstn})",
      s!"    if (!{rstn})",
      s!"      for (n = 0; n < {D}; n = n + 1) queue_data[n] <= " ++ "{" ++ DW ++ "{1'b0}};",
      s!"    else if ({clr})",
      s!"      for (n = 0; n < {D}; n = n + 1) queue_data[n] <= " ++ "{" ++ DW ++ "{1'b0}};",
      s!"    else if ({ena})",
      s!"      case (" ++ "{" ++ s!"{we}, {re}" ++ "})",
      -- The in-range guards on the two dynamic-index writes make the out-of-bounds no-op EXPLICIT:
      -- simulation semantics are unchanged (an OOB array write is already a no-op in iverilog),
      -- but yosys truncates a memory write address to $clog2(DEPTH) bits, so for power-of-two
      -- depths an unguarded full-queue write (queue_wadr = DEPTH) would alias onto word 0 in the
      -- elaborated netlist — diverging from `compile (impl …)`'s exact per-word pointer compare
      -- and failing the per-N miter (caught at DEPTH = 2 and 8).
      s!"        2'b10  : if (queue_wadr < {D}) queue_data[queue_wadr] <= {din};",
      "        2'b01  : begin",
      s!"                   for (n = 0; n < {D}-1; n = n + 1) queue_data[n] <= queue_data[n+1];",
      s!"                   queue_data[{D}-1] <= " ++ "{" ++ DW ++ "{1'b0}};",
      "                 end",
      "        2'b11  : begin",
      s!"                   for (n = 0; n < {D}-1; n = n + 1) queue_data[n] <= queue_data[n+1];",
      s!"                   queue_data[{D}-1] <= " ++ "{" ++ DW ++ "{1'b0}};",
      s!"                   if (queue_wadr == " ++ "{PW{1'b0}}" ++ s!") queue_data[0] <= {din};",
      s!"                   else if (queue_wadr - 1'b1 < {D}) queue_data[queue_wadr - 1'b1] <= {din};",
      "                 end",
      "        default: ;",
      "      endcase",
      "",
      s!"  wire [PW-1:0] almost_empty_check = {AE}_CHECK[PW-1:0];",
      s!"  wire [PW-1:0] almost_full_check  = {AF}_CHECK[PW-1:0];",
      "",
      s!"  assign {q}    = queue_data[0];",
      s!"  assign {empt} = (queue_wadr == " ++ "{PW{1'b0}});",
      s!"  assign {ful}  = (queue_wadr == FULL_THRESHOLD[PW-1:0]);",
      s!"  assign {aemp} = (queue_wadr <= almost_empty_check);",
      s!"  assign {aful} = (queue_wadr >= almost_full_check);",
      "endmodule", "" ]

/-! ## Swizzle+Gray class emitter (`swizzleGray`) — chunk-reversal + binary→Gray second output

Like `emitSwizzleVerilog`, but the module carries a second combinational output `gray_out`, the
standard binary→Gray transform of the reversed `data_out` (`gray_out = data_out ^ (data_out >> 1)`,
so `gray_out[MSB] = data_out[MSB]`, `gray_out[j] = data_out[j+1] ^ data_out[j]`).  Mirrors
`Param.NbitSwizzlingGray.impl` (whose `data_out` reuses `NbitSwizzling.outExpr` and whose `gray_out`
is `.xor dataOut (.shr dataOut 1)`); anchored per-`N` by the combinational equivalence miter against
`compile (impl DATA_WIDTH)`. -/
def emitSwizzleGrayVerilog (pm : LegacyMeta) (cfg : SwizzleCfg) : String :=
  let m    := pm.gen cfg.dataDefault
  let name := m.name
  let ins  := m.inputs.map (·.name)
  let outs := m.outputs.map (·.name)
  let din  := ins.getD 0 "data_in"
  let sel  := ins.getD 1 "sel"
  let dout := outs.getD 0 "data_out"
  let gout := outs.getD 1 "gray_out"
  let W    := cfg.dataParam
  let loopFor (k : String) : String :=
    s!"for (i = 0; i < {W}; i = i + 1) {dout}[(i/({k}))*({k}) + (({k})-1 - i%({k}))] = {din}[i];"
  String.intercalate "\n"
    [ s!"module {name} #(parameter {W} = {cfg.dataDefault}) (",
      s!"  input  [{W}-1:0] {din},",
      s!"  input  [1:0] {sel},",
      s!"  output reg [{W}-1:0] {dout},",
      s!"  output [{W}-1:0] {gout}",
      ");",
      "  integer i;",
      "  always @(*) begin",
      s!"    case ({sel})",
      s!"      2'd0: {loopFor W}",
      s!"      2'd1: {loopFor s!"{W}/2"}",
      s!"      2'd2: {loopFor s!"{W}/4"}",
      s!"      2'd3: {loopFor s!"{W}/8"}",
      s!"      default: {dout} = {din};",
      "    endcase",
      "  end",
      s!"  assign {gout} = {dout} ^ ({dout} >> 1);",
      "endmodule", "" ]

/-! ## Universal shift register class emitter (`shiftReg`) — width-indexed insert bit

Emits an `N`-bit universal shift register whose shift/rotate insert bit is at index `N-1` (a
*function of the width*, out of the affine SSA scope).  The `always @(posedge clk or posedge rst)`
block mirrors `Param.UniversalShiftReg.gen` register-for-register: async active-high reset to 0, then
a `case (mode_sel)` of Hold / Shift / Rotate / Parallel-Load using symbolic `{serial_in, q[N-1:1]}`
concatenations; `serial_out` is the combinational `shift_dir ? q[N-1] : q[0]`.  The per-`N`
sequential equivalence miter anchors it to `compile (gen N)`. -/
def emitShiftRegVerilog (pm : LegacyMeta) (cfg : ShiftRegCfg) : String :=
  let m    := pm.gen cfg.widthDefault
  let name := m.name
  let ins  := m.inputs.map (·.name)
  let clk  := ins.getD 0 "clk"
  let rst  := ins.getD 1 "rst"
  let mode := ins.getD 2 "mode_sel"
  let dir  := ins.getD 3 "shift_dir"
  let sin  := ins.getD 4 "serial_in"
  let pin  := ins.getD 5 "parallel_in"
  let W    := cfg.widthParam
  String.intercalate "\n"
    [ s!"module {name} #(parameter {W} = {cfg.widthDefault}) (",
      s!"  input  {clk},",
      s!"  input  {rst},",
      s!"  input  [1:0] {mode},",
      s!"  input  {dir},",
      s!"  input  {sin},",
      s!"  input  [{W}-1:0] {pin},",
      s!"  output reg [{W}-1:0] q,",
      "  output serial_out",
      ");",
      s!"  always @(posedge {clk} or posedge {rst}) begin",
      s!"    if ({rst})",
      "      q <= {" ++ s!"{W}" ++ "{1'b0}};",
      "    else",
      s!"      case ({mode})",
      "        2'b00: q <= q;",
      s!"        2'b01: q <= {dir} " ++ "? {q[" ++ s!"{W}" ++ "-2:0], " ++ s!"{sin}" ++ "} : {" ++ s!"{sin}" ++ ", q[" ++ s!"{W}" ++ "-1:1]};",
      s!"        2'b10: q <= {dir} " ++ "? {q[" ++ s!"{W}" ++ "-2:0], q[" ++ s!"{W}" ++ "-1]} : {q[0], q[" ++ s!"{W}" ++ "-1:1]};",
      s!"        2'b11: q <= {pin};",
      "        default: q <= q;",
      "      endcase",
      "  end",
      s!"  assign serial_out = {dir} ? q[{W}-1] : q[0];",
      "endmodule", "" ]

/-! ## Configurable signed comparator class emitter (`comparator`)

Emits the genuinely 5-parameter comparator: symbolic pre-shift (`<<< SHIFT_LEFT`), an exact
`(DATA_WIDTH+1)`-bit signed difference (explicit sign-extension concats, so it never wraps), a
tolerance window compared against `TOLERANCE` truncated to `DATA_WIDTH+1` bits (mirroring the Lean
`BitVec.ofNat (N+1) tol`), and a `generate`-selected output stage: `REGISTER_OUTPUT != 0` gives
`always @(posedge clk or negedge rst_n)` registers clearing to 0, else pure combinational drive.
Anchored per-configuration by the equivalence miter against `compile (impl …)` on each parameter
axis (five axis keys + a dev-TB-configuration width sweep in the registry). -/
def emitComparatorVerilog (pm : LegacyMeta) (cfg : ComparatorCfg) : String :=
  let m    := pm.gen cfg.dwDefault
  let name := m.name
  let ins  := m.inputs.map (·.name)
  let outs := m.outputs.map (·.name)
  let clk  := ins.getD 0 "clk"
  let rstn := ins.getD 1 "rst_n"
  let en   := ins.getD 2 "enable"
  let byp  := ins.getD 3 "bypass"
  let a    := ins.getD 4 "a"
  let b    := ins.getD 5 "b"
  let gt   := outs.getD 0 "gt"
  let lt   := outs.getD 1 "lt"
  let eq   := outs.getD 2 "eq"
  let DW   := cfg.dwParam
  let RO   := cfg.regParam
  let ET   := cfg.etParam
  let TOL  := cfg.tolParam
  let SH   := cfg.shParam
  String.intercalate "\n"
    [ s!"module {name} #(",
      s!"  parameter integer {DW} = {cfg.dwDefault},",
      s!"  parameter integer {RO} = {cfg.regDefault},",
      s!"  parameter integer {ET} = {cfg.etDefault},",
      s!"  parameter integer {TOL} = {cfg.tolDefault},",
      s!"  parameter integer {SH} = {cfg.shDefault}",
      ") (",
      s!"  input  wire {clk},",
      s!"  input  wire {rstn},",
      s!"  input  wire {en},",
      s!"  input  wire {byp},",
      s!"  input  wire signed [{DW}-1:0] {a},",
      s!"  input  wire signed [{DW}-1:0] {b},",
      s!"  output reg  {gt},",
      s!"  output reg  {lt},",
      s!"  output reg  {eq}",
      ");",
      -- TOLERANCE truncated to DW+1 bits, exactly the Lean `BitVec.ofNat (N+1) tol`.
      s!"  localparam [{DW}:0] TOL_T = {TOL};",
      s!"  wire signed [{DW}-1:0] a_shifted = {a} <<< {SH};",
      s!"  wire signed [{DW}-1:0] b_shifted = {b} <<< {SH};",
      -- exact (DW+1)-bit signed difference: explicit sign-extension, never wraps.
      s!"  wire signed [{DW}:0] diff = " ++ "{a_shifted[" ++ DW ++ "-1], a_shifted} - {b_shifted["
        ++ DW ++ "-1], b_shifted};",
      s!"  wire signed [{DW}:0] abs_diff = diff[{DW}] ? (-diff) : diff;",
      s!"  wire eq_tolerance = ({ET} != 0) && ($unsigned(abs_diff) <= TOL_T);",
      s!"  wire gt_c = {byp} ? 1'b0 : ({en} ? (eq_tolerance ? 1'b0 : (a_shifted > b_shifted)) : 1'b0);",
      s!"  wire lt_c = {byp} ? 1'b0 : ({en} ? (eq_tolerance ? 1'b0 : (a_shifted < b_shifted)) : 1'b0);",
      s!"  wire eq_c = {byp} ? 1'b1 : ({en} ? (eq_tolerance ? 1'b1 : (a_shifted == b_shifted)) : 1'b0);",
      "  generate",
      s!"    if ({RO} != 0) begin : g_registered",
      s!"      always @(posedge {clk} or negedge {rstn}) begin",
      s!"        if (!{rstn}) begin",
      s!"          {gt} <= 1'b0; {lt} <= 1'b0; {eq} <= 1'b0;",
      "        end else begin",
      s!"          {gt} <= gt_c; {lt} <= lt_c; {eq} <= eq_c;",
      "        end",
      "      end",
      "    end else begin : g_combinational",
      "      always @(*) begin",
      s!"        {gt} = gt_c; {lt} = lt_c; {eq} = eq_c;",
      "      end",
      "    end",
      "  endgenerate",
      "endmodule", "" ]

/-! ## Direct-mapped cache class emitter (`dmCache`)

Mirrors `Param/DirectMapCache.impl` exactly: priority `rst ≻ enable ≻ offset[0] ≻ operation`
(rendered golden-idiom `if (rst) … else if (enable) …` so an `x` on `enable` *holds* instead of
poisoning state), flat tag/valid/dirty vectors updated by dynamic part-select (the Lean shift/mask
registers), one data array mirroring the `$mem_v2`, registered outputs, combinational `error`.
The hidden harness reads `INDEX_WIDTH` off the DUT — emitted as a `$clog2` localparam.  Anchored
per parameter tuple by the equivalence miter against `compile (impl CS DW TW OW)`. -/
def emitDmCacheVerilog (pm : LegacyMeta) (cfg : DmCacheCfg) : String :=
  let m     := pm.gen pm.defaultN
  let name  := m.name
  let CS    := cfg.csParam
  let DW    := cfg.dwParam
  let TW    := cfg.twParam
  let OW    := cfg.owParam
  String.intercalate "\n"
    [ s!"module {name} #(",
      s!"  parameter {CS} = {cfg.csDefault},",
      s!"  parameter {DW} = {cfg.dwDefault},",
      s!"  parameter {TW} = {cfg.twDefault},",
      s!"  parameter {OW} = {cfg.owDefault}",
      ") (",
      "  input  clk,",
      "  input  rst,",
      "  input  enable,",
      s!"  input  [$clog2({CS})-1:0] index,",
      s!"  input  [{OW}-1:0] offset,",
      "  input  comp,",
      "  input  write,",
      s!"  input  [{TW}-1:0] tag_in,",
      s!"  input  [{DW}-1:0] data_in,",
      "  input  valid_in,",
      "  output reg hit,",
      "  output reg dirty,",
      s!"  output reg [{TW}-1:0] tag_out,",
      s!"  output reg [{DW}-1:0] data_out,",
      "  output reg valid,",
      "  output error",
      ");",
      s!"  localparam INDEX_WIDTH = $clog2({CS});",
      s!"  localparam WORD_SEL    = {OW} - 1;",
      s!"  localparam MEM_DEPTH   = {CS} * (1 << WORD_SEL);",
      "",
      s!"  reg [{CS}*{TW}-1:0] tags;",
      s!"  reg [{CS}-1:0] valid_bits;",
      s!"  reg [{CS}-1:0] dirty_bits;",
      s!"  reg [{DW}-1:0] data_mem [0:MEM_DEPTH-1];",
      "",
      "  wire off0 = offset[0];",
      "  assign error = off0;",
      s!"  wire [{TW}-1:0] tag_sel = tags[index*{TW} +: {TW}];",
      "  wire valid_sel = valid_bits[index];",
      "  wire dirty_sel = dirty_bits[index];",
      "  wire tag_match = (tag_sel == tag_in);",
      "  wire hitc = tag_match & valid_sel;",
      "  wire ok = enable & ~off0;",
      "  wire aw_fire = ok & write & ~comp;",
      "  wire cw_fire = ok & write & comp & hitc;",
      s!"  wire [INDEX_WIDTH+WORD_SEL-1:0] mem_addr = \{index, offset[{OW}-1:1]};",
      s!"  wire [{DW}-1:0] mem_rd = data_mem[mem_addr];",
      s!"  wire [{DW}-1:0] gdata = valid_sel ? mem_rd : \{{DW}\{1'b0}};",
      "",
      "  always @(posedge clk) begin",
      "    if (rst) begin",
      "      hit <= 1'b0; dirty <= 1'b0; valid <= 1'b0;",
      s!"      tag_out <= \{{TW}\{1'b0}};",
      s!"      data_out <= \{{DW}\{1'b0}};",
      s!"      tags <= \{{CS}*{TW}\{1'b0}};",
      s!"      valid_bits <= \{{CS}\{1'b0}};",
      s!"      dirty_bits <= \{{CS}\{1'b0}};",
      "    end else if (enable) begin",
      "      if (off0) begin",
      "        hit <= 1'b0; dirty <= 1'b0; valid <= 1'b0;",
      s!"        tag_out <= \{{TW}\{1'b0}};",
      s!"        data_out <= \{{DW}\{1'b0}};",
      "      end else begin",
      "        if (comp) hit <= hitc; else hit <= 1'b0;",
      "        if (aw_fire) begin",
      "          valid <= valid_in;",
      "          dirty <= 1'b0;",
      "          tag_out <= tag_in;",
      "          data_out <= data_in;",
      s!"          tags[index*{TW} +: {TW}] <= tag_in;",
      "          valid_bits[index] <= valid_in;",
      "          dirty_bits[index] <= 1'b0;",
      "        end else begin",
      "          valid <= valid_sel;",
      "          tag_out <= tag_sel;",
      "          if (cw_fire) begin",
      "            dirty <= 1'b1;",
      "            dirty_bits[index] <= 1'b1;",
      "            data_out <= data_in;",
      "          end else begin",
      "            dirty <= dirty_sel;",
      "            data_out <= gdata;",
      "          end",
      "        end",
      "      end",
      "    end",
      "  end",
      "",
      "  // data array write (either write kind; never during reset)",
      "  always @(posedge clk) begin",
      "    if (!rst && (aw_fire || cw_fire)) begin",
      "      if (mem_addr < MEM_DEPTH) data_mem[mem_addr] <= data_in;",
      "    end",
      "  end",
      "endmodule", "" ]

/-! ## Fixed-bus APB GPIO class emitter (`apbGpio`)

Emits the parametric APB GPIO peripheral mirroring `Param.ApbGpio.impl` register-for-register:
nine `GPIO_WIDTH`-bit registers (five APB-writable config/data registers, a two-stage `gpio_in`
synchroniser plus one edge-history tap, and the interrupt-state register), async active-low
`preset_n` (`$adff`), a combinational word-address read decode onto the fixed 32-bit `prdata`,
and the testbench-pinned interrupt semantics: level mode (`int_type = 0`) *follows*
`(sync2 ^ pol) & en` (`pol = 0` ⇒ active-high); edge mode (`int_type = 1`) *latches* the
enable-gated edge pulse (`pol = 0` ⇒ rising, `1` ⇒ falling) with write-1-to-clear at word
address 6 (a same-cycle new edge wins over the clear).  Scope: `GPIO_WIDTH ≤ 32` (fixed APB
data bus).  Anchored per-`N` by the sequential equivalence miter against `compile (impl N)`. -/
def emitApbGpioVerilog (pm : LegacyMeta) (cfg : ApbGpioCfg) : String :=
  let m  := pm.gen cfg.widthDefault
  let W  := cfg.widthParam
  String.intercalate "\n"
    [ s!"module {m.name} #(",
      s!"  parameter integer {W} = {cfg.widthDefault}",
      ") (",
      "  input  wire        pclk,",
      "  input  wire        preset_n,",
      "  input  wire        psel,",
      "  input  wire [5:0]  paddr,",
      "  input  wire        penable,",
      "  input  wire        pwrite,",
      "  input  wire [31:0] pwdata,",
      s!"  input  wire [{W}-1:0] gpio_in,",
      "  output wire [31:0] prdata,",
      "  output wire        pready,",
      "  output wire        pslverr,",
      s!"  output wire [{W}-1:0] gpio_out,",
      s!"  output wire [{W}-1:0] gpio_enable,",
      s!"  output wire [{W}-1:0] gpio_int,",
      "  output wire        comb_int",
      ");",
      s!"  reg [{W}-1:0] reg_dout;",
      s!"  reg [{W}-1:0] reg_dout_en;",
      s!"  reg [{W}-1:0] reg_int_en;",
      s!"  reg [{W}-1:0] reg_int_type;",
      s!"  reg [{W}-1:0] reg_int_pol;",
      s!"  reg [{W}-1:0] gpio_in_sync1;",
      s!"  reg [{W}-1:0] gpio_in_sync2;",
      s!"  reg [{W}-1:0] gpio_in_sync2_d;",
      s!"  reg [{W}-1:0] reg_int_state;",
      "",
      "  // APB write qualifier (stateless slave: pready == 1, no wait states)",
      "  wire wr_en = psel & penable & pwrite;",
      s!"  wire [{W}-1:0] wdata = pwdata[{W}-1:0];",
      "",
      "  // interrupt condition vectors (bitwise over the pins)",
      "  //   level: pol = 0 -> active-high, pol = 1 -> active-low",
      "  //   edge : pol = 0 -> rising,      pol = 1 -> falling",
      s!"  wire [{W}-1:0] level_act = gpio_in_sync2 ^ reg_int_pol;",
      s!"  wire [{W}-1:0] edge_det  = (~reg_int_pol & (~gpio_in_sync2_d & gpio_in_sync2))",
      s!"                           | ( reg_int_pol & ( gpio_in_sync2_d & ~gpio_in_sync2));",
      "  // write-1-to-clear mask for the latched (edge-mode) interrupt bits",
      s!"  wire [{W}-1:0] clear_mask = (wr_en && (paddr == 6'd6)) ? wdata : " ++ "{" ++ W ++ "{1'b0}};",
      "",
      "  always @(posedge pclk or negedge preset_n) begin",
      "    if (!preset_n) begin",
      "      reg_dout        <= 0; reg_dout_en     <= 0; reg_int_en    <= 0;",
      "      reg_int_type    <= 0; reg_int_pol     <= 0; gpio_in_sync1 <= 0;",
      "      gpio_in_sync2   <= 0; gpio_in_sync2_d <= 0; reg_int_state <= 0;",
      "    end else begin",
      "      if (wr_en && (paddr == 6'd1)) reg_dout     <= wdata;",
      "      if (wr_en && (paddr == 6'd2)) reg_dout_en  <= wdata;",
      "      if (wr_en && (paddr == 6'd3)) reg_int_en   <= wdata;",
      "      if (wr_en && (paddr == 6'd4)) reg_int_type <= wdata;",
      "      if (wr_en && (paddr == 6'd5)) reg_int_pol  <= wdata;",
      "      // two-stage input synchroniser + edge-history tap",
      "      gpio_in_sync1   <= gpio_in;",
      "      gpio_in_sync2   <= gpio_in_sync1;",
      "      gpio_in_sync2_d <= gpio_in_sync2;",
      "      // per bit: edge mode latches (W1C, capture beats clear); level mode follows",
      "      reg_int_state <=",
      "          ( reg_int_type & ((reg_int_state & ~clear_mask) | (edge_det & reg_int_en)))",
      "        | (~reg_int_type & (level_act & reg_int_en));",
      "    end",
      "  end",
      "",
      "  // combinational word-address read decode (undefined address -> 0)",
      s!"  reg [{W}-1:0] rd_sel;",
      "  always @(*) begin",
      "    case (paddr)",
      "      6'd0:    rd_sel = gpio_in_sync2;",
      "      6'd1:    rd_sel = reg_dout;",
      "      6'd2:    rd_sel = reg_dout_en;",
      "      6'd3:    rd_sel = reg_int_en;",
      "      6'd4:    rd_sel = reg_int_type;",
      "      6'd5:    rd_sel = reg_int_pol;",
      "      6'd6:    rd_sel = reg_int_state;",
      "      default: rd_sel = {" ++ W ++ "{1'b0}};",
      "    endcase",
      "  end",
      "",
      "  assign prdata      = rd_sel;   // implicit zero-extension onto the 32-bit APB bus",
      "  assign pready      = 1'b1;",
      "  assign pslverr     = 1'b0;",
      "  assign gpio_out    = reg_dout;",
      "  assign gpio_enable = reg_dout_en;",
      "  assign gpio_int    = reg_int_state;",
      "  assign comb_int    = |reg_int_state;",
      "endmodule", "" ]

/-! ## Decimator + peak class emitter (`decimPeak`)

Emits the 3-parameter decimator/peak module mirroring `Param.DecimPeak.impl`: a 1-cycle input
pipeline (`reg_data ← data_in`, `valid_out ← valid_in`, async active-high `reset`), a
combinational decimation loop selecting `reg_data[i*DEC_FACTOR*DATA_WIDTH +: DATA_WIDTH]` into
`data_out[i*DATA_WIDTH +: DATA_WIDTH]` (the tb model's LSB-side selection — NB the NL's worked
example shows the opposite, MSB-side, selection; the tb is the oracle), and a signed peak
reduction initialised with decimated sample 0.  Anchored per-config to `compile (impl N W DEC)`
by the sequential equivalence miter (one registry key per parameter axis). -/
def emitDecimPeakVerilog (pm : LegacyMeta) (cfg : DecimPeakCfg) : String :=
  let m   := pm.gen pm.defaultN
  let NP  := cfg.nParam
  let WP  := cfg.dwParam
  let DP  := cfg.decParam
  String.intercalate "\n"
    [ s!"module {m.name} #(",
      s!"  parameter integer {NP} = {cfg.nDefault},",
      s!"  parameter integer {WP} = {cfg.dwDefault},",
      s!"  parameter integer {DP} = {cfg.decDefault}",
      ") (",
      "  input  wire clk,",
      "  input  wire reset,",
      "  input  wire valid_in,",
      s!"  input  wire [{WP}*{NP}-1:0] data_in,",
      "  output reg  valid_out,",
      s!"  output reg [{WP}*({NP}/{DP})-1:0] data_out,",
      s!"  output reg signed [{WP}-1:0] peak_value",
      ");",
      s!"  localparam integer M = {NP} / {DP};",
      "",
      s!"  reg [{WP}*{NP}-1:0] reg_data;",
      "",
      "  // 1-cycle input pipeline, asynchronous active-high reset",
      "  always @(posedge clk or posedge reset) begin",
      "    if (reset) begin",
      "      reg_data  <= 0;",
      "      valid_out <= 1'b0;",
      "    end else begin",
      "      reg_data  <= data_in;",
      "      valid_out <= valid_in;",
      "    end",
      "  end",
      "",
      "  integer i;",
      "  // decimation: keep the sample at LSB offset i*DEC_FACTOR for each output slot i",
      "  always @(*) begin",
      "    for (i = 0; i < M; i = i + 1)",
      s!"      data_out[i*{WP} +: {WP}] = reg_data[i*{DP}*{WP} +: {WP}];",
      "  end",
      "",
      "  // signed peak over the decimated samples (initialise with sample 0)",
      "  always @(*) begin",
      s!"    peak_value = $signed(reg_data[0 +: {WP}]);",
      "    for (i = 1; i < M; i = i + 1)",
      s!"      if (peak_value < $signed(reg_data[i*{DP}*{WP} +: {WP}]))",
      s!"        peak_value = $signed(reg_data[i*{DP}*{WP} +: {WP}]);",
      "  end",
      "endmodule", "" ]

/-- Dispatch to the right parametric emitter for a `ParamModule`, by its declared `EmitClass`. -/
def emitTemplateVerilog (pm : LegacyMeta) : String :=
  match pm.cls with
  | .affine          => Legacy.emitAffineVerilog pm
  | .cascade cfg     => emitCascadeVerilog pm cfg
  | .memLifo cfg     => emitMemLifoVerilog pm cfg
  | .filo cfg        => emitFiloVerilog pm cfg
  | .fir cfg         => emitFirVerilog pm cfg
  | .swizzle cfg     => emitSwizzleVerilog pm cfg
  | .swizzleGray cfg => emitSwizzleGrayVerilog pm cfg
  | .qamMap cfg      => emitQamMapVerilog pm cfg
  | .qamDemap cfg    => emitQamDemapVerilog pm cfg
  | .prbs cfg        => emitPrbsVerilog pm cfg
  | .restoreDiv cfg  => emitRestoreDivVerilog pm cfg
  | .sort cfg        => emitSortVerilog pm cfg
  | .queue cfg       => emitQueueVerilog pm cfg
  | .shiftReg cfg    => emitShiftRegVerilog pm cfg
  | .comparator cfg  => emitComparatorVerilog pm cfg
  | .dmCache cfg     => emitDmCacheVerilog pm cfg
  | .apbGpio cfg     => emitApbGpioVerilog pm cfg
  | .decimPeak cfg   => emitDecimPeakVerilog pm cfg

end LeanRTL.Designs.Param
