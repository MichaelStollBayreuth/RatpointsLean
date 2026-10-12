/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Basic

/-!
# The valuation of a power of `p` times a unit at `p`, and of a square

Candidates for `Mathlib.NumberTheory.Padics.PadicVal.Basic`: the valuation of `p ^ m b'` with
`p ∤ b'` for any `p > 1` (`padicValNat_eq_of_eq_pow_mul_of_not_dvd`), a nonzero integer as the
power of `p` of its valuation times an integer prime to `p` (`Int.exists_eq_pow_padicValNat_mul`),
the `p`-adic valuation of the integer `p ^ n` (`padicValInt_prime_pow`, the integer form of
`padicValNat.prime_pow`), and a square that is a power of `p` times a unit at `p`, whose exponent is
even and whose unit part is a square (`Int.even_and_isSquare_of_sq_eq_pow_mul`).

## Main statements

* `padicValNat_eq_of_eq_pow_mul_of_not_dvd`: `v_p(p ^ m b') = m` for `p > 1` and `p ∤ b'`.
* `Int.exists_eq_pow_padicValNat_mul`: a nonzero integer is `p ^ v_p(|n|)` times an integer prime
  to `p`.
* `padicValInt_prime_pow`: `v_p(p ^ n) = n` for the integer `p ^ n`.
* `Int.even_and_isSquare_of_sq_eq_pow_mul`: `y ^ 2 = p ^ v u` with `p ∤ u` makes `v` even and `u` a
  square.
-/

@[expose] public section

/-- The valuation of `b = p ^ m b'` with `p ∤ b'` is `m`, for any `p > 1`: `p ^ m` divides `b` and
`p ^ (m + 1)` does not. Compare `padicValNat.prime_pow` and `padicValNat_mul_pow_left`, which take a
prime `p`. -/
theorem padicValNat_eq_of_eq_pow_mul_of_not_dvd {p b b' m : ℕ} (hp : 1 < p) (hb : b = p ^ m * b')
    (hb' : ¬p ∣ b') : padicValNat p b = m := by
  have hpm : p ^ m ≠ 0 := pow_ne_zero m (Nat.ne_zero_of_lt hp)
  have hb0 : b ≠ 0 := hb ▸ mul_ne_zero hpm fun h ↦ hb' (h ▸ dvd_zero p)
  refine le_antisymm (Nat.le_of_lt_succ (Nat.lt_of_not_le fun h ↦ hb' ?_))
    ((padicValNat_dvd_iff_le_of_ne_one hp.ne' hb0).mp ⟨b', hb⟩)
  have := (padicValNat_dvd_iff_le_of_ne_one hp.ne' hb0).mpr h
  rwa [hb, pow_succ, Nat.mul_dvd_mul_iff_left (Nat.pos_of_ne_zero hpm)] at this

/-- A nonzero integer is `p ^ v_p(|n|)` times an integer prime to `p`. -/
theorem Int.exists_eq_pow_padicValNat_mul {p : ℕ} [hp : Fact p.Prime] {n : ℤ} (hn : n ≠ 0) :
    ∃ r, n = (p : ℤ) ^ padicValNat p n.natAbs * r ∧ ¬(p : ℤ) ∣ r := by
  obtain ⟨r, hr⟩ : (p : ℤ) ^ padicValNat p n.natAbs ∣ n :=
    Int.natCast_dvd.mpr pow_padicValNat_dvd
  refine ⟨r, hr, fun ⟨s, hs⟩ ↦ pow_succ_padicValNat_not_dvd (p := p) (Int.natAbs_ne_zero.mpr hn)
    (Int.natCast_dvd.mp ⟨s, by rw [Nat.cast_pow, pow_succ, mul_assoc, ← hs, ← hr]⟩)⟩

theorem padicValInt_prime_pow {p : ℕ} [Fact p.Prime] (n : ℕ) :
    padicValInt p ((p : ℤ) ^ n) = n := by
  rw [← Nat.cast_pow, padicValInt.of_nat, padicValNat.prime_pow]

/-- **A square with a known power of `p`.** If `y ^ 2 = p ^ v u` with `p ∤ u`, then `v` is even, by
the valuations at `p`, and `u` is the square of `y / p ^ (v / 2)`. -/
theorem Int.even_and_isSquare_of_sq_eq_pow_mul {p : ℕ} [hp : Fact p.Prime] {y u : ℤ} {v : ℕ}
    (h : y ^ 2 = (p : ℤ) ^ v * u) (hu : ¬(p : ℤ) ∣ u) : Even v ∧ IsSquare u := by
  have hu0 : u ≠ 0 := fun h0 ↦ hu (h0 ▸ dvd_zero _)
  have hp0 : (p : ℤ) ≠ 0 := mod_cast hp.out.ne_zero
  have hy0 : y ≠ 0 := by
    rintro rfl
    exact mul_ne_zero (pow_ne_zero v hp0) hu0 (by simpa using h.symm)
  have hval := congr(padicValInt p $h)
  rw [sq, padicValInt.mul hy0 hy0, padicValInt.mul (pow_ne_zero _ hp0) hu0,
    padicValInt.eq_zero_of_not_dvd hu, padicValInt_prime_pow] at hval
  obtain ⟨k, rfl⟩ : Even v := ⟨padicValInt p y, by lia⟩
  refine ⟨⟨k, rfl⟩, ?_⟩
  obtain ⟨z, rfl⟩ : (p : ℤ) ^ k ∣ y :=
    (Int.pow_dvd_pow_iff two_ne_zero).mp ⟨u, by rw [h, ← pow_mul, Nat.mul_comm, two_mul]⟩
  refine ⟨z, (mul_left_cancel₀ (pow_ne_zero (k + k) hp0) ?_).symm⟩
  rw [← h, pow_add]
  ring

end
