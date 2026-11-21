/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.RingTheory.Multiplicity

/-!
# The multiplicity of `p` in a power of `p` times an element prime to `p`

A candidate for `Mathlib.RingTheory.Multiplicity`, next to `multiplicity_eq_of_dvd_of_not_dvd`:
the multiplicity of `p` in `p ^ m b'` with `p ∤ b'` is `m`, for any `p ≠ 0` in a monoid with zero
with left cancellation.

## Main statements

* `multiplicity_eq_of_eq_pow_mul_of_not_dvd`: the multiplicity of `p ≠ 0` in `p ^ m b'` with
  `p ∤ b'` is `m`.
-/

@[expose] public section

/-- The multiplicity of `p` in `b = p ^ m b'` with `p ∤ b'` is `m`, for any `p ≠ 0`, since
`p ^ (m + 1) ∣ p ^ m b'` would give `p ∣ b'` by cancelling `p ^ m`. Compare
`multiplicity_eq_of_dvd_of_not_dvd`, which takes `p ^ m ∣ b` and `p ^ (m + 1) ∤ b`, and
`multiplicity_base_pow_mul`, which gives `multiplicity p (p ^ k n) = multiplicity p n + k` over `ℕ`
for `1 < p` and `n ≠ 0`. -/
theorem multiplicity_eq_of_eq_pow_mul_of_not_dvd {α : Type*} [MonoidWithZero α]
    [IsLeftCancelMulZero α] {p b b' : α} {m : ℕ} (hp : p ≠ 0) (hb : b = p ^ m * b')
    (hb' : ¬p ∣ b') : multiplicity p b = m := by
  subst hb
  refine multiplicity_eq_of_dvd_of_not_dvd (dvd_mul_right _ _) ?_
  rwa [pow_succ, mul_dvd_mul_iff_left (pow_ne_zero m hp)]

end
