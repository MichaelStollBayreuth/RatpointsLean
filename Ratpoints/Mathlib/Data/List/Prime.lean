/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.Prime

/-!
# A prime that divides no factor of a product of powers of primes

A candidate for `Mathlib.Data.List.Prime`, next to `Prime.not_dvd_prod` and
`mem_list_primes_of_dvd_prod`: in a cancellative commutative monoid with zero whose only unit is
`1`, a prime that is none of the primes `f x` does not divide the product of their powers
`f x ^ e x`.

## Main statements

* `Prime.not_dvd_prod_map_pow`: a prime other than the primes of a list of prime powers does not
  divide their product.
-/

@[expose] public section

variable {M α : Type*} [CommMonoidWithZero M] [IsCancelMulZero M] [Subsingleton Mˣ]

/-- A prime `p` that is none of the primes `f x`, for `x` in the list `l`, does not divide the
product of the powers `f x ^ e x`. -/
theorem Prime.not_dvd_prod_map_pow {p : M} (hp : Prime p) {l : List α} {f : α → M} {e : α → ℕ}
    (hl : ∀ x ∈ l, Prime (f x) ∧ f x ≠ p) : ¬p ∣ (l.map fun x ↦ f x ^ e x).prod :=
  hp.not_dvd_prod fun _ ha hd ↦ by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
    exact (hl x hx).2 ((prime_dvd_prime_iff_eq hp (hl x hx).1).mp (hp.dvd_of_dvd_pow hd)).symm

end
