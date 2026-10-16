/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Prime.Defs

/-!
# A number below the square of its least prime factor

A candidate for `Mathlib.Data.Nat.Prime.Defs`, next to `Nat.minFac_sq_le_self`: a number other than
`0` and `1` below `p ^ 2` whose prime factors are all at least `p` is a prime.

## Main statements

* `Nat.prime_of_lt_mul_self`: a number `n ∉ {0, 1}` below `p ^ 2` with no prime factor below `p`
  is a prime.
-/

@[expose] public section

namespace Nat

/-- A number `n ∉ {0, 1}` below `p ^ 2` whose prime factors are all at least `p` is a prime: a
composite `n` has `minFac n ^ 2 ≤ n` (`Nat.minFac_sq_le_self`). -/
theorem prime_of_lt_mul_self {n p : ℕ} (hn0 : n ≠ 0) (hn1 : n ≠ 1) (hlt : n < p * p)
    (h : ∀ q, q.Prime → q ∣ n → p ≤ q) : n.Prime := by
  by_contra hnp
  have h1 := minFac_sq_le_self (Nat.pos_of_ne_zero hn0) hnp
  lia [mul_self_le_mul_self (h _ (minFac_prime hn1) (minFac_dvd n))]

end Nat

end
