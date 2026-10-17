/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.SmoothNumbers

import Ratpoints.Mathlib.Data.Nat.Factors

/-!
# The rough part of a number

A candidate for `Mathlib.NumberTheory.SmoothNumbers`: the part `w` of a number `n` at the primes
from `q` on, `n = k w` with a `q`-smooth `k` (`Nat.smoothNumbers`) and a `q`-rough `w`, all of
whose prime factors are at least `q`. It is the product of the prime factors of `n ≠ 0` from `q`
on, and dividing the part at the primes from the prime `p` on by the power of `p` leaves the part
from `p + 1` on, which is the part from the next prime on. Mathlib's `Nat.roughNumbersUpTo` says
"rough" for "not smooth", a different notion.

## Main definitions

* `Nat.IsRoughPart`: the part of a number at the primes from a bound on.

## Main statements

* `Nat.IsRoughPart.eq_prod_filter`: the part of `n ≠ 0` at the primes from `q` on is the product of
  its prime factors from `q` on.
* `Nat.IsRoughPart.succ`, `Nat.IsRoughPart.of_le_of_forall`: the part at the primes from the next
  prime on.
-/

@[expose] public section

namespace Nat

/-- `w` is the part of `n` at the primes from `q` on, its `q`-rough part: `n = k w` with a
`q`-smooth `k` (every prime factor of `k` below `q`) and every prime factor of `w` at least `q`;
for `n ≠ 0` it is the product of the prime factors of `n` from `q` on, with multiplicity
(`Nat.IsRoughPart.eq_prod_filter`). -/
def IsRoughPart (q n w : ℕ) : Prop :=
  ∃ k ∈ q.smoothNumbers, n = k * w ∧ ∀ p, p.Prime → p ∣ w → q ≤ p

theorem IsRoughPart.ne_zero {q n w : ℕ} (h : IsRoughPart q n w) (hn : n ≠ 0) : w ≠ 0 := by
  obtain ⟨k, -, rfl, -⟩ := h
  exact right_ne_zero_of_mul hn

/-- The part of `n ≠ 0` at the primes from `q` on is the product of its prime factors from `q` on,
with multiplicity. -/
theorem IsRoughPart.eq_prod_filter {q n w : ℕ} (h : IsRoughPart q n w) (hn : n ≠ 0) :
    w = (n.primeFactorsList.filter (q ≤ ·)).prod := by
  obtain ⟨k, hk, rfl, hw⟩ := h
  rw [prod_filter_primeFactorsList_mul_of_forall (left_ne_zero_of_mul hn) fun p hp ↦ ?_,
    prod_filter_primeFactorsList_eq_self (right_ne_zero_of_mul hn) fun p hp ↦ ?_]
  · simpa using hw p (prime_of_mem_primeFactorsList hp) (dvd_of_mem_primeFactorsList hp)
  · simpa using mem_smoothNumbers'.mp hk p (prime_of_mem_primeFactorsList hp)
      (dvd_of_mem_primeFactorsList hp)

/-- Dividing the part `p ^ v m`, `p ∤ m`, of `n` at the primes from the prime `p` on by `p ^ v`
leaves the part of `n` at the primes from `p + 1` on. -/
theorem IsRoughPart.succ {p n v m : ℕ} (h : IsRoughPart p n (p ^ v * m)) (hp : p.Prime)
    (hpm : ¬p ∣ m) :
    IsRoughPart (p + 1) n m := by
  obtain ⟨k, hk, hn, hw⟩ := h
  refine ⟨p ^ v * k, pow_mul_mem_smoothNumbers hp.ne_zero v hk, by rw [hn]; ring,
    fun q hq hqm ↦ ?_⟩
  exact (hw q hq (hqm.mul_left _)).lt_of_ne fun h ↦ hpm (h ▸ hqm)

/-- The part of `n` at the primes from `q` on is its part from `q' ≥ q` on when no prime lies
between them. -/
theorem IsRoughPart.of_le_of_forall {q q' n w : ℕ} (h : IsRoughPart q n w) (hqq : q ≤ q')
    (hno : ∀ p, p.Prime → q ≤ p → q' ≤ p) :
    IsRoughPart q' n w := by
  obtain ⟨k, hk, hn, hw⟩ := h
  exact ⟨k, smoothNumbers_mono hqq hk, hn, fun p hp hpw ↦ hno p hp (hw p hp hpw)⟩

end Nat

end
