/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Bisection
public import Ratpoints.Proof.BitRange
public import Ratpoints.Proof.Bits
public import Ratpoints.Proof.Bounds
public import Ratpoints.Proof.BruteForce
public import Ratpoints.Proof.Cli
public import Ratpoints.Proof.CliNumbers
public import Ratpoints.Proof.CompositeRows
public import Ratpoints.Proof.Containers
public import Ratpoints.Proof.Delivery
public import Ratpoints.Proof.DeliveryCount
public import Ratpoints.Proof.Denominators
public import Ratpoints.Proof.Divisors
public import Ratpoints.Proof.Double
public import Ratpoints.Proof.FindPoints
public import Ratpoints.Proof.FirstStage
public import Ratpoints.Proof.Forbidden
public import Ratpoints.Proof.Jacobi
public import Ratpoints.Proof.JacobiTables
public import Ratpoints.Proof.Moduli
public import Ratpoints.Proof.Order
public import Ratpoints.Proof.Output
public import Ratpoints.Proof.Packing
public import Ratpoints.Proof.Params
public import Ratpoints.Proof.PrimeRows
public import Ratpoints.Proof.Reductions
public import Ratpoints.Proof.Region
public import Ratpoints.Proof.Rounding
public import Ratpoints.Proof.RowStore
public import Ratpoints.Proof.Rows
public import Ratpoints.Proof.Scan
public import Ratpoints.Proof.SearchDens
public import Ratpoints.Proof.SetBits
public import Ratpoints.Proof.Setup
public import Ratpoints.Proof.Shapes
public import Ratpoints.Proof.Sieve
public import Ratpoints.Proof.Sift
public import Ratpoints.Proof.Stages
public import Ratpoints.Proof.Sturm
public import Ratpoints.Proof.SturmCounts
public import Ratpoints.Proof.SturmCoverage
public import Ratpoints.Proof.SturmRegion
public import Ratpoints.Proof.SturmSigns
public import Ratpoints.Proof.Tables
public import Ratpoints.Proof.TwoAdic
public import Ratpoints.Proof.Valuation
public import Ratpoints.Proof.Words

/-!
# The proofs

The contract of each component of the model as a theorem, the link to the mathematics, and the
main theorems, which say that the model finds exactly the points of the specification for every
well-formed choice of the sieving parameters, in the order in which ratpoints finds them, that the
search with a callback delivers them to it as the C code does, and what the program prints.
-/
