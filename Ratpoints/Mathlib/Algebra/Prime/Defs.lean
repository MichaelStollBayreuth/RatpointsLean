/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Prime.Defs

/-!
# A prime that divides no factor of a product

A candidate for `Mathlib.Algebra.Prime.Defs`, next to `Prime.dvd_or_dvd` and
`Prime.dvd_of_dvd_pow`: a prime that divides none of `x`, `a` and `y` does not divide `x a ^ n y`.

## Main statements

* `Prime.not_dvd_mul_pow_mul`: a prime that divides none of the factors of `x a ^ n y` does not
  divide it.
-/

@[expose] public section

/-- A prime that divides none of `x`, `a` and `y` does not divide `x a ^ n y`. -/
theorem Prime.not_dvd_mul_pow_mul {M : Type*} [CommMonoidWithZero M] {p x a y : M}
    (hp : Prime p) (hx : ¬p ∣ x) (ha : ¬p ∣ a) (hy : ¬p ∣ y) (n : ℕ) : ¬p ∣ x * a ^ n * y :=
  fun h ↦ (hp.dvd_or_dvd h).elim (fun h ↦ (hp.dvd_or_dvd h).elim hx
    fun h ↦ ha (hp.dvd_of_dvd_pow h)) hy

end
