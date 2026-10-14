/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Tables

import Ratpoints.Proof.Bits

/-!
# The contracts of the stages of the sieve

The reductions by a reciprocal (`Ratpoints.Sieve.mulMod`, `Ratpoints.Sieve.mulDiv`) compute the
remainder and the quotient where the C code relies on them: with the reciprocal
`Ratpoints.Sieve.magic p`, which exceeds `2 ^ 64 / p` by less than `1`, for every `u` with
`u p < 2 ^ 64`, and so for the values at most `Ratpoints.mulModLimit` and the moduli up to
`2 ^ 32`.

## Main statements

* `Ratpoints.Sieve.magic_mul_eq`: `magic p · p = 2 ^ 64 + δ` with `δ < p`.
* `Ratpoints.Sieve.mulMod_magic`, `Ratpoints.Sieve.mulDiv_magic`: with the reciprocal
  `Ratpoints.Sieve.magic p`, the reductions give `u % p` and `u / p` for `u p < 2 ^ 64`;
  `Ratpoints.Sieve.sub_mulDiv_magic_mul`: the remainder as `u - RP_MULDIV(u) p`.
* `Ratpoints.mul_lt_two_pow_64_of_le_mulModLimit`: `u p < 2 ^ 64` for `u ≤ Ratpoints.mulModLimit`
  and `p ≤ 2 ^ 32`.

## Implementation notes

The file uses Lean core and `Std` only. The proofs use only the fact on the constants that `decide`
checks next to them, that `Ratpoints.mulModLimit < 2 ^ 32`, never their values.
-/

@[expose] public section

namespace Ratpoints

/-- A value at most `Ratpoints.mulModLimit` times a modulus `p ≤ 2 ^ 32` is below `2 ^ 64`, where
the reductions by a reciprocal are exact (`Ratpoints.Sieve.mulMod_magic`,
`Ratpoints.Sieve.mulDiv_magic`); this reads off only `Ratpoints.mulModLimit_lt_two_pow_32`. -/
theorem mul_lt_two_pow_64_of_le_mulModLimit {u p : Nat} (hu : u ≤ mulModLimit)
    (hp : p ≤ 2 ^ 32) : u * p < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (Nat.lt_of_le_of_lt hu mulModLimit_lt_two_pow_32)
    hp (Nat.two_pow_pos 32)) (by decide)

namespace Sieve

/-! ### The reductions by a reciprocal -/

/-- The reciprocal of `p > 0` exceeds `2 ^ 64 / p` by less than `1`: `magic p · p = 2 ^ 64 + δ` with
`δ < p`. -/
theorem magic_mul_eq {p : Nat} (hp : 0 < p) :
    magic p * p = 2 ^ 64 + (p - 1 - (2 ^ 64 - 1) % p) := by
  have h1 := Nat.div_add_mod (2 ^ 64 - 1) p
  have h2 := Nat.mod_lt (2 ^ 64 - 1) hp
  simp only [magic]
  grind

/-- `RP_MULMOD` with the reciprocal of `p` computes the remainder of every `u` with `u p < 2 ^ 64`,
since `magic p` exceeds `2 ^ 64 / p` by less than `1`. -/
theorem mulMod_magic {u p : Nat} (hp : 0 < p) (hu : u * p < 2 ^ 64) :
    mulMod u p (magic p) = u % p :=
  Nat.mul_mod_mul_div_eq_mod hp (magic_mul_eq hp)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left u (by lia)) hu)

/-- `RP_MULDIV` with the reciprocal of `p` computes the quotient of every `u` with
`u p < 2 ^ 64`. -/
theorem mulDiv_magic {u p : Nat} (hp : 0 < p) (hu : u * p < 2 ^ 64) :
    mulDiv u (magic p) = u / p := by
  rw [mulDiv, Nat.mul_comm]
  exact Nat.mul_div_eq_div_of_mul_eq_add hp (magic_mul_eq hp)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left u (by lia)) hu)

/-- The remainder `u - RP_MULDIV(u) p`, as the Jacobi test by tables of the C code takes it
(`find_points.c:755`), is `u % p` for `u p < 2 ^ 64`. -/
theorem sub_mulDiv_magic_mul {u p : Nat} (hp : 0 < p) (hu : u * p < 2 ^ 64) :
    u - mulDiv u (magic p) * p = u % p := by
  rw [mulDiv_magic hp hu, Nat.mod_eq_sub_div_mul]

end Sieve

end Ratpoints

end
