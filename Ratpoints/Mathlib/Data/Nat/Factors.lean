/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Factors

import Mathlib.Data.Nat.GCD.BigOperators

/-!
# The part of a number with its prime factors in a set

Candidates for `Mathlib.Data.Nat.Factors`: the product of the prime factors of `n` that pass a test
`p`, `(n.primeFactorsList.filter p).prod`, the part of `n` with its prime factors in a set (as
`Nat.prod_mem_factoredNumbers` has it), is multiplicative, a divisor of `n`, `1` when no prime
factor passes and `n` when all do; for the test `(·.Coprime m)` it is `Nat.coprimePart n m`, the
largest divisor of `n ≠ 0` prime to `m`.

## Main definitions

* `Nat.coprimePart`: the product of the prime factors of `n`, with multiplicity, that are prime to
  `m`.

## Main statements

* `Nat.prod_filter_primeFactorsList_mul`: the part of `a b` is the product of the parts of `a` and
  `b`; `Nat.prod_filter_primeFactorsList_mul_of_forall`: a factor `a` without a prime factor that
  passes leaves the part of `b` as it is.
* `Nat.prod_filter_primeFactorsList_eq_one`, `Nat.prod_filter_primeFactorsList_eq_self`: the part is
  `1` when no prime factor passes, and `n` when all do.
* `Nat.prod_filter_primeFactorsList_dvd`: the part divides `n`.
* `Nat.coprimePart_dvd`, `Nat.coprime_coprimePart`, `Nat.dvd_coprimePart_of_dvd`: the part of `n`
  prime to `m` divides `n`, is prime to `m`, and every divisor of `n ≠ 0` prime to `m` divides it,
  so that it is the largest divisor of `n` prime to `m`.

## Implementation notes

`Nat.coprime_coprimePart` and `Nat.dvd_coprimePart_of_dvd` use `Nat.coprime_list_prod_left_iff` and
`Nat.coprime_list_prod_right_iff` of `Mathlib.Data.Nat.GCD.BigOperators`, which
`Mathlib.Data.Nat.Factors` does not import.
-/

@[expose] public section

namespace Nat

theorem prod_filter_primeFactorsList_mul (p : ℕ → Bool) {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    ((a * b).primeFactorsList.filter p).prod =
      (a.primeFactorsList.filter p).prod * (b.primeFactorsList.filter p).prod := by
  rw [((perm_primeFactorsList_mul ha hb).filter p).prod_eq, List.filter_append, List.prod_append]

theorem prod_filter_primeFactorsList_eq_one {p : ℕ → Bool} {n : ℕ}
    (h : ∀ q ∈ n.primeFactorsList, p q = false) : (n.primeFactorsList.filter p).prod = 1 := by
  rw [List.filter_eq_nil_iff.mpr fun q hq ↦ by simp [h q hq], List.prod_nil]

theorem prod_filter_primeFactorsList_eq_self {p : ℕ → Bool} {n : ℕ} (hn : n ≠ 0)
    (h : ∀ q ∈ n.primeFactorsList, p q = true) : (n.primeFactorsList.filter p).prod = n := by
  rw [List.filter_eq_self.mpr h, prod_primeFactorsList hn]

/-- Multiplying by a number without a prime factor that passes the test keeps the part of a number
with its prime factors passing it. -/
theorem prod_filter_primeFactorsList_mul_of_forall {p : ℕ → Bool} {a b : ℕ} (ha : a ≠ 0)
    (h : ∀ q ∈ a.primeFactorsList, p q = false) :
    ((a * b).primeFactorsList.filter p).prod = (b.primeFactorsList.filter p).prod := by
  rcases eq_or_ne b 0 with rfl | hb
  · simp
  rw [prod_filter_primeFactorsList_mul p ha hb, prod_filter_primeFactorsList_eq_one h, one_mul]

theorem prod_filter_primeFactorsList_dvd (p : ℕ → Bool) (n : ℕ) :
    (n.primeFactorsList.filter p).prod ∣ n := by
  rcases eq_or_ne n 0 with rfl | hn
  · exact dvd_zero _
  · exact List.filter_sublist.prod_dvd_prod.trans (prod_primeFactorsList hn).dvd

/-- The product of the prime factors of `n`, with multiplicity, that are prime to `m`: for `n ≠ 0`
the largest divisor of `n` prime to `m` (`Nat.dvd_coprimePart_of_dvd`). -/
def coprimePart (n m : ℕ) : ℕ :=
  (n.primeFactorsList.filter (·.Coprime m)).prod

theorem coprimePart_eq (n m : ℕ) :
    n.coprimePart m = (n.primeFactorsList.filter (·.Coprime m)).prod :=
  rfl

theorem coprimePart_dvd (n m : ℕ) : n.coprimePart m ∣ n :=
  prod_filter_primeFactorsList_dvd _ n

theorem coprime_coprimePart (n m : ℕ) : Coprime (n.coprimePart m) m :=
  coprime_list_prod_left_iff.mpr fun q hq ↦ by simpa using List.of_mem_filter hq

/-- **The largest divisor prime to `m`.** Every divisor of `n ≠ 0` prime to `m` divides
`Nat.coprimePart n m`, since it is prime to the other prime factors of `n`, which divide `m`. -/
theorem dvd_coprimePart_of_dvd {n m d : ℕ} (hn : n ≠ 0) (hd : d ∣ n) (hdm : Coprime d m) :
    d ∣ n.coprimePart m := by
  refine Coprime.dvd_of_dvd_mul_right (n := (n.primeFactorsList.filter
    fun q ↦ !decide (q.Coprime m)).prod) (coprime_list_prod_right_iff.mpr fun q hq ↦ ?_) ?_
  · have hq' := List.of_mem_filter hq
    simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hq'
    exact hdm.coprime_dvd_right (not_not.mp ((Nat.Prime.coprime_iff_not_dvd
      (prime_of_mem_primeFactorsList (List.mem_of_mem_filter hq))).not.mp hq'))
  · rwa [coprimePart_eq, ← List.prod_append, (List.filter_append_perm _ _).prod_eq,
      prod_primeFactorsList hn]

end Nat

end
