# Frozen specification proof bridge

`FrozenSpecBridge.lean` is an optional module for the `data_all` frozen-specification runner.
It imports the **frozen copy** of `SpecIR.Machine` and the same `LeanRTL.Core.Semantics` used
by the implementation. It is outside the ordinary `LeanRTL` library glob so that the existing
framework remains independent of SpecIR.

The runner must compile a fixed theorem with exactly this target:

```lean
theorem frozen_equivalence :
    FrozenSpecBridge.Equivalent SpecIR.Gen.spec LeanRTL.Blind.CaseName.impl := by
  -- The author's proof body goes here.
```

This target means:

1. The frozen design uses `SpecIR.Timebase.fullCycle`.
2. Every inhabitant of the frozen input type renders only concrete bit values.
3. For **every finite input list**, the frozen `Design.trace` equals the wrapped actual
   LeanRTL module's trace, including all cycle numbers, rendered inputs, output port names,
   output widths and `Val` constructors. Both observations occur before the transition.

The author cannot substitute a new specification, supply a custom input/output adapter,
select an output subset, add a reset prefix, change the latency, or restrict input values.
The module wrapper's input encoding is mechanically obtained from the frozen `renderIn`.
Its state is the actual simulator's register association list; its transition/output
expressions are exactly those of `Module.simulate`. The theorem `design_trace_simulate`
proves this binding, and `Equivalent.simulate` transports an accepted strict proof to the
existing executable simulator.

For sequential designs, construct a `FrozenSpecBridge.Certificate` with these fields:

```lean
{ fullCycle := ...
  concreteInputs := ...
  relation := fun specState rtlRegisters => ...
  init := ...
  step := ...
  observe := ... }
```

`Certificate.equivalent` lifts the initialization, all-input transition preservation and
complete observation equality obligations to arbitrary finite traces. A relation may carry
invariants, but initialization and preservation prevent it from imposing an unproved
reachability or input assumption. Public helpers are `Registers`, `initial`, `inputValues`,
`environment`, `next`, `outputs`, and `design`.

The runner should compile the implementation and perform real preproof emission **before**
soliciting this proof. It should wrap the proof body in a runner-controlled theorem target,
recheck frozen dependency hashes, audit the final theorem's actual axioms, and bind the
same implementation module to the final emitter invocation. The bridge is a theorem about
Lean cycle semantics; emitter gates and native benchmark evaluation remain separate.

## Staging and compilation

Copy this module as `FrozenSpecBridge.lean` in the staged Lean project. Copy the frozen
SpecIR dependencies as `SpecIR.lean` and `SpecIR/*.lean`. Copy the frozen composed entry
`part1/<bench>/<key>/lean/decided.lean` as `Frozen.lean`, preserving its bytes; it already
imports SpecIR and defines `SpecIR.Gen.spec`. Build these modules before compiling the
runner-controlled final theorem, which imports `Frozen`, `FrozenSpecBridge`, and the
assembled implementation module.

Repository validation, using the already-built matching Lean/SpecIR libraries:

```sh
LEAN_PATH="$PWD/.lake/build/lib/lean:$PWD/specir/.lake/build/lib/lean" \
  lean -o /tmp/FrozenSpecBridge.olean method/stage2/framework/FrozenSpecBridge.lean
```

Validated using Lean 4.29.0. Kernel dependency audit of `Certificate.equivalent`,
`run_eq_simulate`, `design_trace_simulate`, `Equivalent.simulate`, and
`Equivalent.initial_concrete` reports only `propext` and `Quot.sound`. There are no
admitted proofs or target axioms. These checks must be repeated against the actual frozen
SpecIR dependency version staged for each run.

## Scope and unsupported cases

`Val.x`, `Val.z`, holes and other partial constructors are retained in strict equality.
They do not compare equal to a concrete `Val.bits`. In particular an undefined initial
output is a real obstruction to proving strict equivalence with this two-state simulator;
`Equivalent.initial_concrete` is a checked necessary condition. Choosing an arbitrary
initial value establishes, at most, a separate refinement result and cannot satisfy this
runner's target.

The frozen input type's complete domain matters. A field typed `Nat` is not automatically
restricted to its rendered port width. If the specification's transition depends on high
bits discarded by `renderIn`, physical inputs cannot carry that information; narrowing
that field's domain would change the frozen target.

This bridge only proves the existing cycle semantics. It does not establish asynchronous
sub-cycle reset responses, arbitrary event schedules, a half-cycle interpretation,
latches, memory behavior absent from `Module.simulate`, or unsupported multiple clocks.
The runner must retain and inspect the framework's semantic coverage and emitter checks;
a passing cycle theorem alone cannot justify claiming those behaviors were proved.
