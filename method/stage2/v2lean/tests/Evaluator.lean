import LeanRTL.Core.Semantics

open LeanRTL

-- Materializing the data table before constructing an Env prevents partial
-- application of an Env-returning function from rebuilding it per lookup.
-- The generated evaluator still implements exactly the reference semantics.
example (wires : List Wire) (base : Env) :
    wireValuesEnv (wires.foldl (evalWireMemoStep base) []) base = evalWires wires base :=
  evalWiresFast_eq wires base
