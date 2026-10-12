/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Int.GCD

/-!
# A divisor of `b` and an integer prime to `b`

A candidate for `Mathlib.Data.Int.GCD`, next to `Int.gcd_eq_one_of_gcd_mul_right_eq_one_left`: a
natural number `p ≠ 1` that divides `b` does not divide an integer `a` with `gcd(a, b) = 1`, as for
a prime that divides the denominator of a normalized fraction `a / b`.

## Main statements

* `Int.not_natCast_dvd_of_gcd_eq_one`: `p ≠ 1` and `p ∣ b` give `¬p ∣ a` for `gcd(a, b) = 1`.
-/

@[expose] public section

namespace Int

/-- A natural number `p ≠ 1` that divides `b` does not divide an integer `a` with `gcd(a, b) = 1`,
since it would divide the gcd. -/
theorem not_natCast_dvd_of_gcd_eq_one {a : ℤ} {b p : ℕ} (hp : p ≠ 1) (hab : a.gcd b = 1)
    (hpb : p ∣ b) : ¬(p : ℤ) ∣ a := fun ha ↦
  hp (Nat.dvd_one.mp (hab ▸ dvd_gcd ha (natCast_dvd_natCast.mpr hpb)))

end Int

end
