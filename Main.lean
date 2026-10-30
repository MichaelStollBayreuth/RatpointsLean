/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Ratpoints.Fast.Cli

/-!
# The executable `ratpoints-lean`

The root of the Lake target `ratpoints-lean`. It imports only the fast search and the model, so
that the program does not depend on Mathlib or on the proofs.
-/

/-- The command-line program `ratpoints-lean`, `Ratpoints.FastCli.main`. -/
public def main (args : List String) : IO UInt32 := Ratpoints.FastCli.main args
