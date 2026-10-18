/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Spec.Basic
public import Ratpoints.Spec.Order
public import Ratpoints.Spec.Region

/-!
# The specification

The specification of ratpoints: the binary form of the polynomial, the predicate "is a normalized
point of height at most `H`" and the finite set of these points, with their basic API
(`Ratpoints.Spec.Basic`), the list of these points in the order in which ratpoints finds them
(`Ratpoints.Spec.Order`), and the values of the doubles that bound the search intervals and the
search intervals that ratpoints accepts (`Ratpoints.Spec.Region`). It depends on Mathlib only, so
that it can be read without the model.
-/
