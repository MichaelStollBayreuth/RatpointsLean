/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Field.Basic

/-!
# The quotient of two integers in an ordered field

A candidate for `Mathlib.Algebra.Order.Field.Basic`: in a linearly ordered field the quotient of
two integers is at most the numerator in absolute value (`abs_intCast_div_intCast_le_abs`), also
for the denominator `0`, by which the quotient is `0`; the field form of `Int.abs_ediv_le_abs`.

## Main statements

* `abs_intCast_div_intCast_le_abs`: `|x / z| ≤ |x|` for integers `x` and `z`.
-/

@[expose] public section

theorem abs_intCast_div_intCast_le_abs {α : Type*} [Field α] [LinearOrder α]
    [IsStrictOrderedRing α] (x z : ℤ) : |(x : α) / z| ≤ |(x : α)| := by
  rcases eq_or_ne z 0 with rfl | hz
  · simp
  rw [abs_div, ← Int.cast_abs (a := z)]
  exact div_le_self (abs_nonneg _) (mod_cast Int.one_le_abs hz)

end
