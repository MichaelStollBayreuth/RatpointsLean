/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.PadicValNat

/-!
# The valuation of a power of `p` times a number prime to `p`

A candidate for `Mathlib.Data.Nat.PadicValNat`, next to `Nat.maxPowDvdDiv_of_pow_mul_eq` and
`padicValNat_base_pow_mul`: the valuation of `p ^ m b'` with `p ∤ b'` is `m`, for any `p ≠ 0`.

## Main statements

* `padicValNat_eq_of_eq_pow_mul_of_not_dvd`: `v_p(p ^ m b') = m` for `p ≠ 0` and `p ∤ b'`.
-/

@[expose] public section

/-- The valuation of `b = p ^ m b'` with `p ∤ b'` is `m`, for any `p ≠ 0` (for `p = 1` the
hypothesis `p ∤ b'` fails): the first component of `Nat.maxPowDvdDiv_of_pow_mul_eq`. Compare
`padicValNat_base_pow_mul`, `v_p(p ^ k n) = v_p(n) + k` for `1 < p` and `n ≠ 0`. -/
theorem padicValNat_eq_of_eq_pow_mul_of_not_dvd {p b b' m : ℕ} (hp : p ≠ 0) (hb : b = p ^ m * b')
    (hb' : ¬p ∣ b') : padicValNat p b = m := by
  have hb0 : b ≠ 0 := hb ▸ mul_ne_zero (pow_ne_zero m hp) fun h ↦ hb' (h ▸ dvd_zero p)
  rw [← Nat.fst_maxPowDvdDiv, Nat.maxPowDvdDiv_of_pow_mul_eq hb0 hb.symm hb']

end
