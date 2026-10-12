/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Bits
public import Ratpoints.Proof.BruteForce
public import Ratpoints.Proof.Divisors
public import Ratpoints.Proof.FindPoints
public import Ratpoints.Proof.Forbidden
public import Ratpoints.Proof.Jacobi
public import Ratpoints.Proof.JacobiTables
public import Ratpoints.Proof.Params
public import Ratpoints.Proof.Setup
public import Ratpoints.Proof.Sieve
public import Ratpoints.Proof.Sturm
public import Ratpoints.Proof.Tables
public import Ratpoints.Proof.TwoAdic
public import Ratpoints.Proof.Valuation
public import Ratpoints.Proof.Words

/-!
# The proofs

The contract of each component of the model as a theorem, the link to the mathematics, and the
main theorems, which say that the model finds exactly the points of the specification for every
well-formed choice of the sieving parameters.
-/
