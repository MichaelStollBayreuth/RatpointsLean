/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Field.ZMod

/-!
# Squares modulo a prime

A candidate for `Mathlib.Algebra.Field.ZMod`: an integer `u` such that `u x ^ 2 + p t` is a square
for an `x` prime to the prime `p` is a square modulo `p`
(`ZMod.isSquare_intCast_of_isSquare_mul_sq_add`).

## Main statements

* `ZMod.isSquare_intCast_of_isSquare_mul_sq_add`: `IsSquare (u x ^ 2 + p t)` with `p ∤ x` makes `u`
  a square modulo `p`.
-/

@[expose] public section

namespace ZMod

/-- An integer `u` such that `u x ^ 2 + p t` is a square, for an `x` prime to the prime `p`, is a
square modulo `p`, since `x` is a unit there. -/
theorem isSquare_intCast_of_isSquare_mul_sq_add {p : ℕ} [Fact p.Prime] {u x t : ℤ}
    (hx : ¬(p : ℤ) ∣ x) (h : IsSquare (u * x ^ 2 + p * t)) : IsSquare (u : ZMod p) := by
  obtain ⟨z, hz⟩ := h
  have hz' := congr(($hz : ZMod p))
  push_cast at hz'
  rw [natCast_self, zero_mul, add_zero] at hz'
  have hx0 : (x : ZMod p) ^ 2 ≠ 0 := pow_ne_zero _ (by rwa [Ne, intCast_zmod_eq_zero_iff_dvd])
  rw [eq_div_of_mul_eq hx0 hz']
  exact (IsSquare.mul_self _).div (IsSquare.sq _)

end ZMod

end
