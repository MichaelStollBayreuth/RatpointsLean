/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Ratpoints.Fast.Search
import Ratpoints.Model.FastCli

/-!
# The executable `ratpoints-lean`

The root of the Lake target `ratpoints-lean` (prototype: the search on byte-array masks).
-/

/-- The command-line program `ratpoints-lean`, on `Ratpoints.FastMask.fastPoints`. -/
public def main (args : List String) : IO UInt32 := do
  match Ratpoints.FastCli.readArgs args with
  | .error e =>
    IO.eprintln e
    return 1
  | .ok a =>
    let out ← IO.getStdout
    for p in Ratpoints.FastMask.fastPoints a.coeffs a.H a.bLow a.bHigh do
      out.putStrLn (Ratpoints.FastCli.pointLine p)
    return 0
