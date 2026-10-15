/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Sieve

/-!
# The contracts of the packing

The packing of the numerators of each class of the denominators modulo 64 into one class modulo a
power of 2 reads, of each sieve entry, an odd modulus `1 < p ≤ Ratpoints.maxPrimeEven` with its
reciprocal, the inverse of `Ratpoints.rbaLength` modulo `p` and the bias, the least multiple of `p`
from `Ratpoints.rowBias` on, as `examine_prime`, `make_power` and `make_modulus` set them
(`Ratpoints.Sieve.SieveEntry.Packable`); the sieve entry of a modulus has them
(`Ratpoints.makeModulus?_spec`).

## Main definitions

* `Ratpoints.Sieve.SieveEntry.Packable`: the fields of a sieve entry that the row offsets of the
  packing read.

## Main statements

* `Ratpoints.Sieve.rowBias_le_mul_div_and_mul_div_lt`: the bias of a modulus.

## Implementation notes

The file uses Lean core and `Std` only, so that the contracts of the sieve, in files without
Mathlib, can use it. The proofs never use the values of the constants.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The fields of the sieve entries -/

/-- The bias `m ⌈Ratpoints.rowBias / m⌉ = m ((rowBias + m - 1) / m)` of a modulus `m > 0`, as
`examine_prime`, `make_power` and `make_modulus` compute it, lies from `Ratpoints.rowBias` to below
`Ratpoints.rowBias + m`. -/
theorem rowBias_le_mul_div_and_mul_div_lt {m : Nat} (hm : 0 < m) :
    rowBias ≤ m * ((rowBias + m - 1) / m) ∧ m * ((rowBias + m - 1) / m) < rowBias + m := by
  generalize rowBias = R
  have h1 := Nat.div_add_mod (R + m - 1) m
  have h2 := Nat.mod_lt (R + m - 1) hm
  constructor <;> lia

/-- The fields of a sieve entry that the row offsets of the packing read: an odd modulus
`1 < p ≤ Ratpoints.maxPrimeEven` with its reciprocal, the inverse `rbainv < p` of
`Ratpoints.rbaLength` modulo `p`, and the bias, a multiple of `p` from `Ratpoints.rowBias` to below
`Ratpoints.rowBias + p`, as `examine_prime`, `make_power` and `make_modulus` set them. -/
structure SieveEntry.Packable (e : SieveEntry) : Prop where
  /-- The modulus is above 1. -/
  one_lt : 1 < e.p
  /-- The modulus is odd. -/
  odd : e.p % 2 = 1
  /-- The modulus is at most `Ratpoints.maxPrimeEven`. -/
  le_maxPrimeEven : e.p ≤ maxPrimeEven
  /-- The reciprocal is that of the modulus. -/
  magic_eq : e.magic = Sieve.magic e.p
  /-- `rbainv` is the inverse of `Ratpoints.rbaLength` modulo the modulus. -/
  rbainv_mul_mod : e.rbainv * rbaLength % e.p = 1
  /-- `rbainv` is below the modulus. -/
  rbainv_lt : e.rbainv < e.p
  /-- The bias is a multiple of the modulus. -/
  bias_mod : e.bias % e.p = 0
  /-- The bias is at least `Ratpoints.rowBias`. -/
  rowBias_le_bias : rowBias ≤ e.bias
  /-- The bias is below `Ratpoints.rowBias + p`. -/
  bias_lt : e.bias < rowBias + e.p

end Sieve

end Ratpoints

end
