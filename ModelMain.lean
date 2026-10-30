/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Ratpoints.Model.Cli

/-!
# The executable `ratpoints-model`

The root of the Lake target `ratpoints-model`, the program of the faithful model of `ratpoints`
(`Ratpoints.Cli.main`), with the command line of `ratpoints` and its options, against which
`scripts/difftest.py` runs. It imports only the model.
-/

/-- The command-line program `ratpoints-model`, `Ratpoints.Cli.main`. -/
public def main (args : List String) : IO UInt32 := Ratpoints.Cli.main args
