/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Group.Even
public import Mathlib.Algebra.Group.Units.Defs

/-!
# A square times an even power of a unit

A candidate for `Mathlib.Algebra.Group.Even`, next to `IsSquare.mul` and `IsSquare.div`: in a
commutative monoid, `y ^ 2 = v u ^ D` with `u` a unit and `D` even makes `v` a square, as for the
value `v = f(a / b)` of a polynomial when `y ^ 2 = f(a / b) b ^ D` is the value of a binary form of
even degree `D` at `(a, b)`. The file imports `Mathlib.Algebra.Group.Units.Defs` as well, since
`Mathlib.Algebra.Group.Even` does not know units.

## Main statements

* `IsUnit.isSquare_of_sq_eq_mul_pow`: `y ^ 2 = v u ^ D` with `u` a unit and `D` even makes `v` a
  square.
-/

@[expose] public section

/-- `y ^ 2 = v u ^ D` with `u` a unit and `D` even makes `v` a square: `v = (y u⁻¹ ^ (D / 2)) ^ 2`.
Mathlib has `IsSquare.mul` and, in a group, `IsSquare.div`. -/
theorem IsUnit.isSquare_of_sq_eq_mul_pow {M : Type*} [CommMonoid M] {y v u : M} (hu : IsUnit u)
    {D : ℕ} (hD : Even D) (h : y ^ 2 = v * u ^ D) : IsSquare v := by
  obtain ⟨u, rfl⟩ := hu
  obtain ⟨k, rfl⟩ := hD
  refine ⟨y * ↑u⁻¹ ^ k, ?_⟩
  calc v = v * (↑u * ↑u⁻¹) ^ (k + k) := by rw [Units.mul_inv, one_pow, mul_one]
    _ = v * ↑u ^ (k + k) * ↑u⁻¹ ^ (k + k) := by rw [mul_pow, mul_assoc]
    _ = y * ↑u⁻¹ ^ k * (y * ↑u⁻¹ ^ k) := by rw [← h, mul_mul_mul_comm, ← pow_add, sq]

end
