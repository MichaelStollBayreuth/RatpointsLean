/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.List.Basic

/-!
# A product of factors that are `u` or `1`

A candidate for `Mathlib.Algebra.BigOperators.Group.List.Basic`, next to `List.prod_map_ite`: the
product over a list of `u` for the entries that pass a test and `1` for the others is `u` to the
number of the entries that pass.

## Main statements

* `List.prod_map_ite_eq_pow`: the product of `u` or `1` over a list is a power of `u`.
-/

@[expose] public section

namespace List

theorem prod_map_ite_eq_pow {α M : Type*} [CommMonoid M] (p : α → Bool) (u : M) (l : List α) :
    (l.map fun x ↦ if p x = true then u else 1).prod = u ^ (l.filter p).length := by
  induction l with
  | nil => simp
  | cons x l ih => cases h : p x <;> simp [h, ih, pow_succ, mul_comm]

end List

end
