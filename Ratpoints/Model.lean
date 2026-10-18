/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.BruteForce
public import Ratpoints.Model.Candidate
public import Ratpoints.Model.Cli
public import Ratpoints.Model.Constants
public import Ratpoints.Model.Delivery
public import Ratpoints.Model.Denominators
public import Ratpoints.Model.Double
public import Ratpoints.Model.FindPoints
public import Ratpoints.Model.FirstStage
public import Ratpoints.Model.Packing
public import Ratpoints.Model.Params
public import Ratpoints.Model.Rows
public import Ratpoints.Model.Setup
public import Ratpoints.Model.Sieve
public import Ratpoints.Model.Sturm
public import Ratpoints.Model.Tables

/-!
# The executable model of ratpoints

The model mirrors the hardware-independent structure of the C code of ratpoints function by
function: the same loops, tables, bit arrays of 64-bit words and index arithmetic. It is plain
executable code on Lean core and `Std`: no Mathlib, no contracts, no experimental options
(`scripts/check_layout.py` checks the imports and the options). The contracts and their proofs
are in `Ratpoints.Proof`. A component with a loop is a definition of type `Id α` that its
callers bind with `←`.

The docstring of every public declaration that models C code names that code in a paragraph of
the form ``C: `find_points.c:812-845` `` (lines at the ratpoints commit the project pins), which
`scripts/correspondence.py` reads; `correspondence/README.md` describes the record.
-/
