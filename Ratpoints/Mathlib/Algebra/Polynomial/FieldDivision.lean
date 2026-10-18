/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.FieldDivision

/-!
# Remainders by constant multiples, and the quotient by `X - x` at `x`

Candidates for `Mathlib.Algebra.Polynomial.FieldDivision`: over a commutative ring, the quotient of
`p` by `X - x` takes the value `p'(x)` at `x` (`Polynomial.eval_divByMonic_X_sub_C`); over a field,
the remainder of `p` by `q` is the polynomial `r` of degree below that of `q` with `q ∣ p - r`
(`Polynomial.mod_eq_of_dvd_sub_of_degree_lt`); a constant factor of the dividend comes out of the
remainder (`Polynomial.C_mul_mod`), and a nonzero constant factor of the divisor does not change it
(`Polynomial.mod_C_mul`).
-/

@[expose] public section

namespace Polynomial

/-- The quotient of `p` by `X - x` takes the value `p'(x)` at `x`, so that at a root `x` of `p`,
`p = (X - x) q` with `q(x) = p'(x)`. -/
theorem eval_divByMonic_X_sub_C {R : Type*} [CommRing R] (p : R[X]) (x : R) :
    (p /ₘ (X - C x)).eval x = p.derivative.eval x := by
  simpa using congr(eval x $(divByMonic_add_X_sub_C_mul_derivative_divByMonic_eq_derivative p x))

variable {K : Type*} [Field K]

/-- The remainder `p % q` is the `r` of degree below that of `q` with `q ∣ p - r`. -/
theorem mod_eq_of_dvd_sub_of_degree_lt {p q r : K[X]} (hq : q ≠ 0) (h : q ∣ p - r)
    (hr : r.degree < q.degree) : p % q = r := by
  rwa [mod_eq_of_dvd_sub h, mod_eq_self_iff hq]

/-- A constant factor of the dividend comes out of the remainder. -/
theorem C_mul_mod (c : K) (p q : K[X]) : C c * p % q = C c * (p % q) := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  rcases eq_or_ne c 0 with rfl | hc
  · simp
  refine mod_eq_of_dvd_sub_of_degree_lt hq ⟨C c * (p / q), ?_⟩
    ((degree_C_mul hc).trans_lt (degree_mod_lt p hq))
  rw [← mul_sub, EuclideanDomain.mod_eq_sub_mul_div]
  ring

/-- A nonzero constant factor of the divisor does not change the remainder. -/
theorem mod_C_mul {c : K} (hc : c ≠ 0) (p q : K[X]) : p % (C c * q) = p % q := by
  rcases eq_or_ne q 0 with rfl | hq
  · simp
  refine mod_eq_of_dvd_sub_of_degree_lt (mul_ne_zero (C_ne_zero.mpr hc) hq)
    ⟨C c⁻¹ * (p / q), ?_⟩ (by rw [degree_C_mul hc]; exact degree_mod_lt p hq)
  rw [EuclideanDomain.mod_eq_sub_mul_div, sub_sub_cancel, mul_mul_mul_comm, ← C_mul,
    mul_inv_cancel₀ hc, C_1, one_mul]

end Polynomial

end
