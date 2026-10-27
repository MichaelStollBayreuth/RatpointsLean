/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Sieve

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers

/-!
# The reductions by a reciprocal and of the row indices

The high half of the product of two 64-bit words from the products of their 32-bit halves
(`Ratpoints.Sieve.mulHi`) is the high half of the product of natural numbers
(`Ratpoints.Sieve.toNat_mulHi`), so that the reductions by a reciprocal on 64-bit words
(`Ratpoints.Sieve.mulMod`, `Ratpoints.Sieve.mulDiv`) compute the remainder and the quotient where
the C code relies on them: with the reciprocal `Ratpoints.Sieve.magic p`, which exceeds `2 ^ 64 / p`
by less than `1`, for every `u` with `u p < 2 ^ 64`, and so for the values at most
`Ratpoints.mulModLimit` and the moduli up to `2 ^ 32`; the quotient for `p ≥ 2`, since the
reciprocal `2 ^ 64` of `1` wraps to `0` on a word, as in the C code. So does the remainder of a
value of either sign (`Ratpoints.Sieve.modMul`), and the helper `mod` of the C code
(`Ratpoints.Sieve.modLong`) is the Euclidean `%` for every integer. The first two stages of the
sieve reduce the sums of a word number and the offset of a row modulo the moduli of their sieve
specs, by a multiplication with the reciprocal when the test `small` says that the word numbers of
the piece allow it and by the helper `mod` otherwise; for a sieve spec whose offset lies in the
range that the packing gives it (`Ratpoints.Sieve.SieveSpec.Fits`), both give the Euclidean
remainder.

## Main definitions

* `Ratpoints.Sieve.SieveSpec.Wraps`: the row of a sieve spec repeats its first bit arrays after the
  first `p`, where the chunked first stage reads it.
* `Ratpoints.Sieve.SieveSpec.Fits`: a sieve spec of a modulus `0 < p ≤ Ratpoints.maxPrimeEven` with
  an offset from `Ratpoints.rowBias` to below `Ratpoints.rowBias + 2 p`, the end `p` and a row
  that repeats its first bit arrays.
* `Ratpoints.Sieve.SmallFits`: when the test `small` holds, the word numbers lie between
  `-Ratpoints.rowBias` and `Ratpoints.rowBias - 2 Ratpoints.maxPrimeEven`.
* `Ratpoints.Sieve.StageFits`: what the stages of the sieve need of their moduli, the reciprocals
  and the test `small`.

## Main statements

* `Ratpoints.maxPrimeEven_le_two_pow_10`, `Ratpoints.maxPrimeEven_le_two_pow_32`: the moduli are
  below `2 ^ 10`, and so below `2 ^ 32`; `Ratpoints.maxPrimeEven_le_sixty_four_mul_modWords`: they
  fit the bit arrays of `Ratpoints.modWords` words.
* `Ratpoints.rowBias_le_two_pow_31`: `Ratpoints.rowBias`, the lower bound of the bias of a modulus
  (the multiple of the modulus in an offset), is at most `2 ^ 31`.
* `Ratpoints.mul_lt_two_pow_64_of_le_mulModLimit`: `u p < 2 ^ 64` for `u ≤ Ratpoints.mulModLimit`
  and `p ≤ 2 ^ 32`.
* `Ratpoints.mul_le_mulModLimit_of_le_div`, `Ratpoints.mul_lt_two_pow_63`: the products of
  `fill_bp_list` and of `class_offsets` are `long`s, those of the first branch of `fill_bp_list` at
  most `Ratpoints.mulModLimit`.
* `Ratpoints.rbaLength_eq`, `Ratpoints.rbaLength_pos`, `Ratpoints.natCast_rbaLength_pos`,
  `Ratpoints.natCast_rbaLength_dvd_two_pow`: the width `Ratpoints.rbaLength` of the bit arrays is
  `64 Ratpoints.rbaPack`, positive, and divides `2 ^ n` for `n ≥ Ratpoints.rbaShift`.
* `Ratpoints.Sieve.toNat_mulHi`: `Ratpoints.Sieve.mulHi a b` is `⌊a b / 2 ^ 64⌋`.
* `Ratpoints.Sieve.mulMod_eq`, `Ratpoints.Sieve.mulDiv_eq`: the reductions on 64-bit words are those
  of the macros on natural numbers reduced modulo `2 ^ 64`.
* `Ratpoints.Sieve.magic_mul_eq`: `magic p · p = 2 ^ 64 + δ` with `δ < p`.
* `Ratpoints.Sieve.mulMod_magic`, `Ratpoints.Sieve.mulDiv_magic`: with the reciprocal
  `Ratpoints.Sieve.magic p`, the reductions give `u % p` and, for `p ≥ 2`, `u / p` for
  `u p < 2 ^ 64`; `Ratpoints.Sieve.mulMod_magic_of_le_mulModLimit`: the remainder of the values at
  most `Ratpoints.mulModLimit` modulo `p ≤ 2 ^ 32`.
* `Ratpoints.Sieve.modMul_magic`: `mod_mul` gives the Euclidean `a % p` for `|a| p < 2 ^ 64`.
* `Ratpoints.Sieve.modLong_eq_emod`: the helper `mod` of the C code is the Euclidean `%`.
* `Ratpoints.Sieve.SieveSpec.Fits.ite_modMul_modLong_eq_emod_of_natAbs_le`: the reduction by
  `mod_mul` under the test `small` and by the helper `mod` otherwise is the Euclidean remainder of
  a value at most `Ratpoints.mulModLimit` in absolute value under `small`.
* `Ratpoints.Sieve.SieveSpec.Fits.ite_modMul_modLong_eq_emod`,
  `Ratpoints.Sieve.SieveSpec.Fits.ite_modMul_modLong_add_eq_emod`,
  `Ratpoints.Sieve.SieveSpec.Fits.ite_mulMod_modLong_eq_toNat_emod`: the first row index of the
  first stage one row at a time, the start of a row of the chunked first stage and the row index of
  the second stage are the Euclidean remainders of `-w0 - offset`, of `w0 + offset` and of
  `i + offset`.

## Implementation notes

The file uses Lean core and `Std` only, so that the contracts of the sieve, in files without
Mathlib, can use it. The proofs use only the facts on the constants that `decide` checks next to
them, that `Ratpoints.rbaPack > 0`, that `Ratpoints.mulModLimit < 2 ^ 32`, that
`Ratpoints.maxBitsInPrime ≤ 10` and that `2 Ratpoints.rowBias - 1 ≤ Ratpoints.mulModLimit`, never
their values; `Ratpoints.rowBias` is generalized before `lia`, which otherwise fails on its value
with a deep recursion of the kernel. `Ratpoints.mul_lt_two_pow_63` and
`Ratpoints.rowBias_le_two_pow_31` (through `Ratpoints.Sieve.SieveEntry.PackedFor.lt_two_pow_32`)
discharge range obligations of the `long`s that the Deviation paragraphs of the model cite, and no
contract uses them.
-/

@[expose] public section

namespace Ratpoints

/-! ### The moduli -/

/-- The moduli below `Ratpoints.maxPrimeEven` are below `2 ^ 10`, since `maxBitsInPrime ≤ 10`
(`Ratpoints.maxBitsInPrime_le_ten`), as the comment on Horner's rule in `examine_power` assumes
(`find_points.c:2286-2287`). -/
theorem maxPrimeEven_le_two_pow_10 : maxPrimeEven ≤ 2 ^ 10 :=
  Nat.pow_le_pow_right Nat.two_pos maxBitsInPrime_le_ten

/-- The moduli, below `Ratpoints.maxPrimeEven`, are below `2 ^ 32`, the bound under which the
reductions by a reciprocal of the values at most `Ratpoints.mulModLimit` are exact
(`Ratpoints.mul_lt_two_pow_64_of_le_mulModLimit`) and the helper `mod` keeps its values `long`s
(`Ratpoints.fitsLong_sixteen_mul`, `Ratpoints.fitsLong_add_sixteen_mul`). -/
theorem maxPrimeEven_le_two_pow_32 : maxPrimeEven ≤ 2 ^ 32 :=
  Nat.le_trans maxPrimeEven_le_two_pow_10 (by decide)

/-- A prime power below `Ratpoints.maxPrimeEven`, the moduli of the parameters, fits the
`Ratpoints.modWords` words of the bit arrays of its tables and of the patterns of its rows. -/
theorem maxPrimeEven_le_sixty_four_mul_modWords : maxPrimeEven ≤ 64 * modWords :=
  Nat.le_mul_add_sub_one_div _ (by decide)

/-- `Ratpoints.rowBias` is at most `2 ^ 31`, since `2 rowBias - 1 ≤ Ratpoints.mulModLimit < 2 ^ 32`
(`Ratpoints.two_mul_rowBias_sub_one_le_mulModLimit`, `Ratpoints.mulModLimit_lt_two_pow_32`): the
bound of the offsets of the rows (`Ratpoints.Sieve.SieveEntry.PackedFor.lt_two_pow_32`). -/
theorem rowBias_le_two_pow_31 : rowBias ≤ 2 ^ 31 := by
  have := two_mul_rowBias_sub_one_le_mulModLimit
  have := mulModLimit_lt_two_pow_32
  generalize rowBias = R at *
  generalize mulModLimit = L at *
  lia

/-- A value at most `Ratpoints.mulModLimit` times a modulus `p ≤ 2 ^ 32` is below `2 ^ 64`, where
the reductions by a reciprocal are exact (`Ratpoints.Sieve.mulMod_magic`,
`Ratpoints.Sieve.mulDiv_magic`); this reads off only `Ratpoints.mulModLimit_lt_two_pow_32`. -/
theorem mul_lt_two_pow_64_of_le_mulModLimit {u p : Nat} (hu : u ≤ mulModLimit)
    (hp : p ≤ 2 ^ 32) : u * p < 2 ^ 64 :=
  Nat.lt_of_lt_of_le (Nat.mul_lt_mul_of_lt_of_le (Nat.lt_of_le_of_lt hu mulModLimit_lt_two_pow_32)
    hp (Nat.two_pow_pos 32)) (by decide)

/-- The products `x d p` of `fill_bp_list` and `class_offsets` that a reduction by the reciprocal
of a modulus `p ≤ Ratpoints.maxPrimeEven` takes, for `x ≤ 2 ^ 10` and `d < p`, are below `2 ^ 64`,
where it is exact. -/
theorem mul_mul_lt_two_pow_64 {x d p : Nat} (hx : x ≤ 2 ^ 10) (hd : d < p)
    (hp : p ≤ maxPrimeEven) : x * d * p < 2 ^ 64 := by
  have := maxPrimeEven_le_two_pow_10
  calc x * d * p ≤ 2 ^ 10 * 2 ^ 10 * 2 ^ 10 :=
        Nat.mul_le_mul (Nat.mul_le_mul hx (by lia)) (by lia)
    _ < 2 ^ 64 := by decide

/-- The products `b dinv` of the first branch of `fill_bp_list`, for
`b ≤ Ratpoints.mulModLimit / Ratpoints.maxPrimeEven` and `dinv < p ≤ Ratpoints.maxPrimeEven`, are at
most `Ratpoints.mulModLimit`, so `long`s that the reduction by the reciprocal of `p` reduces
exactly. -/
theorem mul_le_mulModLimit_of_le_div {b d p : Nat} (hb : b ≤ mulModLimit / maxPrimeEven)
    (hd : d < p) (hp : p ≤ maxPrimeEven) : b * d ≤ mulModLimit :=
  Nat.le_trans (Nat.mul_le_mul hb (Nat.le_trans (Nat.le_of_lt hd) hp)) (Nat.div_mul_le_self _ _)

/-- The products `x d` of the other branches of `fill_bp_list`, `(b mod p) dinv`, and of
`class_offsets`, `a₀ rinv`, for `x ≤ 2 ^ 10` and `d < p ≤ Ratpoints.maxPrimeEven`, are `long`s. -/
theorem mul_lt_two_pow_63 {x d p : Nat} (hx : x ≤ 2 ^ 10) (hd : d < p) (hp : p ≤ maxPrimeEven) :
    x * d < 2 ^ 63 := by
  calc x * d ≤ 2 ^ 10 * 2 ^ 10 := Nat.mul_le_mul hx (by lia [maxPrimeEven_le_two_pow_10])
    _ < 2 ^ 63 := by decide

theorem mod_le_two_pow_10 (b : Nat) {p : Nat} (hp : 0 < p) (hpm : p ≤ maxPrimeEven) :
    b % p ≤ 2 ^ 10 :=
  Nat.le_of_lt (Nat.lt_of_lt_of_le (Nat.mod_lt _ hp) (Nat.le_trans hpm maxPrimeEven_le_two_pow_10))

/-! ### The width of the bit arrays -/

theorem rbaLength_eq : rbaLength = 64 * rbaPack := rfl

theorem rbaLength_pos : 0 < rbaLength := rbaLength_eq ▸ Nat.mul_pos (by decide) rbaPack_pos

theorem natCast_rbaLength_pos : (0 : Int) < rbaLength := Int.natCast_pos.mpr rbaLength_pos

/-- The width `Ratpoints.rbaLength = 2 ^ Ratpoints.rbaShift` of the bit arrays divides `2 ^ n` for
`n ≥ Ratpoints.rbaShift`. -/
theorem natCast_rbaLength_dvd_two_pow {n : Nat} (hn : rbaShift ≤ n) : (rbaLength : Int) ∣ 2 ^ n :=
  rbaLength_eq_two_pow_rbaShift ▸ mod_cast Nat.pow_dvd_pow 2 hn

namespace Sieve

/-! ### The high half of a product -/

-- The high half of the product of `2 ^ 32 a₁ + a₀` and `2 ^ 32 b₁ + b₀` from the four products of
-- the halves, as `Ratpoints.Sieve.mulHi` adds them: the high product, the high halves of the two
-- middle products, and the carry of the high half of the low product with the low halves of the
-- middle products.
private theorem mul_div_two_pow_64_eq (a0 a1 b0 b1 : Nat) :
    (2 ^ 32 * a1 + a0) * (2 ^ 32 * b1 + b0) / 2 ^ 64 =
      a1 * b1 + a0 * b1 / 2 ^ 32 + a1 * b0 / 2 ^ 32 +
        (a0 * b0 / 2 ^ 32 + a0 * b1 % 2 ^ 32 + a1 * b0 % 2 ^ 32) / 2 ^ 32 := by
  have e : (2 ^ 32 * a1 + a0) * (2 ^ 32 * b1 + b0) =
      2 ^ 64 * (a1 * b1) + 2 ^ 32 * (a0 * b1 + a1 * b0) + a0 * b0 := by
    simp only [Nat.add_mul, Nat.mul_add]
    lia
  rw [e]
  generalize a0 * b0 = P0, a0 * b1 = P1, a1 * b0 = P2, a1 * b1 = P3
  lia

-- A product of two halves of 32 bits is at most `(2 ^ 32 - 1) ^ 2`.
private theorem mul_le_of_lt_two_pow_32 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    x * y ≤ 2 ^ 64 - 2 ^ 33 + 1 :=
  Nat.le_trans (Nat.mul_le_mul (Nat.le_sub_one_of_lt hx) (Nat.le_sub_one_of_lt hy)) (by decide)

-- The partial sums of `Ratpoints.Sieve.mulHi` stay below `2 ^ 64`, for products of 32-bit halves.
private theorem sum_halves_mod {P0 P1 P2 P3 : Nat} (h0 : P0 ≤ 2 ^ 64 - 2 ^ 33 + 1)
    (h1 : P1 ≤ 2 ^ 64 - 2 ^ 33 + 1) (h2 : P2 ≤ 2 ^ 64 - 2 ^ 33 + 1)
    (h3 : P3 ≤ 2 ^ 64 - 2 ^ 33 + 1) :
    (((P3 % 2 ^ 64 + P1 % 2 ^ 64 / 2 ^ 32) % 2 ^ 64 + P2 % 2 ^ 64 / 2 ^ 32) % 2 ^ 64 +
        ((P0 % 2 ^ 64 / 2 ^ 32 + P1 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64 + P2 % 2 ^ 64 % 2 ^ 32) % 2 ^ 64 /
          2 ^ 32) % 2 ^ 64 =
      P3 + P1 / 2 ^ 32 + P2 / 2 ^ 32 + (P0 / 2 ^ 32 + P1 % 2 ^ 32 + P2 % 2 ^ 32) / 2 ^ 32 := by
  rw [Nat.mod_eq_of_lt (a := P0) (by lia), Nat.mod_eq_of_lt (a := P1) (by lia),
    Nat.mod_eq_of_lt (a := P2) (by lia), Nat.mod_eq_of_lt (a := P3) (by lia),
    Nat.mod_eq_of_lt (a := P3 + P1 / 2 ^ 32) (by lia),
    Nat.mod_eq_of_lt (a := P3 + P1 / 2 ^ 32 + P2 / 2 ^ 32) (by lia),
    Nat.mod_eq_of_lt (a := P0 / 2 ^ 32 + P1 % 2 ^ 32) (by lia),
    Nat.mod_eq_of_lt (a := P0 / 2 ^ 32 + P1 % 2 ^ 32 + P2 % 2 ^ 32) (by lia),
    Nat.mod_eq_of_lt (by lia)]

/-- The high half of the product of two 64-bit words from the products of their 32-bit halves is
the high half of the product of natural numbers: no partial sum wraps. -/
theorem toNat_mulHi (a b : UInt64) : (mulHi a b).toNat = a.toNat * b.toNat / 2 ^ 64 := by
  have e := mul_div_two_pow_64_eq (a.toNat % 2 ^ 32) (a.toNat / 2 ^ 32) (b.toNat % 2 ^ 32)
    (b.toNat / 2 ^ 32)
  rw [Nat.div_add_mod, Nat.div_add_mod] at e
  have ha1 : a.toNat / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul a.toNat_lt
  have hb1 : b.toNat / 2 ^ 32 < 2 ^ 32 := Nat.div_lt_of_lt_mul b.toNat_lt
  have ha0 := Nat.mod_lt a.toNat (Nat.two_pow_pos 32)
  have hb0 := Nat.mod_lt b.toNat (Nat.two_pow_pos 32)
  simp only [mulHi, UInt64.toNat_add, UInt64.toNat_mul, UInt64.toNat_shiftRight_32,
    UInt64.toNat_and_0xffffffff]
  rw [e]
  exact sum_halves_mod (mul_le_of_lt_two_pow_32 ha0 hb0) (mul_le_of_lt_two_pow_32 ha0 hb1)
    (mul_le_of_lt_two_pow_32 ha1 hb0) (mul_le_of_lt_two_pow_32 ha1 hb1)

/-! ### The reductions by a reciprocal -/

/-- `RP_MULMOD` on 64-bit words is the macro on natural numbers: the product `m u` reduced modulo
`2 ^ 64`, as the product of `unsigned long`s wraps, times `p` as an `unsigned long`, shifted right
by 64 bits. -/
theorem mulMod_eq (u p m : Nat) : mulMod u p m = m * u % 2 ^ 64 * (p % 2 ^ 64) / 2 ^ 64 := by
  simp [mulMod, toNat_mulHi, UInt64.toNat_mul, Nat.mul_mod]

theorem mulDiv_eq (u m : Nat) : mulDiv u m = u % 2 ^ 64 * (m % 2 ^ 64) / 2 ^ 64 := by
  simp [mulDiv, toNat_mulHi]

/-- The reciprocal of `p > 0` exceeds `2 ^ 64 / p` by less than `1`: `magic p · p = 2 ^ 64 + δ` with
`δ < p`. -/
theorem magic_mul_eq {p : Nat} (hp : 0 < p) :
    magic p * p = 2 ^ 64 + (p - 1 - (2 ^ 64 - 1) % p) := by
  have h1 := Nat.div_add_mod (2 ^ 64 - 1) p
  have h2 := Nat.mod_lt (2 ^ 64 - 1) hp
  simp only [magic]
  grind

/-- The reciprocal of a modulus `p ≥ 2` is an `unsigned long`; that of `1`, no modulus, is
`2 ^ 64`, which wraps to `0` in the C code. -/
theorem magic_lt_two_pow_64 {p : Nat} (hp : 1 < p) : magic p < 2 ^ 64 := by
  simp only [magic]
  lia [Nat.div_le_div_left (a := 2 ^ 64 - 1) hp (by decide)]

/-- `RP_MULMOD` with the reciprocal of `p` computes the remainder of every `u` with `u p < 2 ^ 64`,
since `magic p` exceeds `2 ^ 64 / p` by less than `1`. -/
theorem mulMod_magic {u p : Nat} (hp : 0 < p) (hu : u * p < 2 ^ 64) :
    mulMod u p (magic p) = u % p := by
  rcases Nat.eq_zero_or_pos u with rfl | hu0
  · simp [mulMod_eq]
  rw [mulMod_eq, Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_left p hu0) hu)]
  exact Nat.mul_mod_mul_div_eq_mod_of_mul_eq_add hp (magic_mul_eq hp)
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left u (by lia)) hu)

/-- `RP_MULDIV` with the reciprocal of `p ≥ 2` computes the quotient of every `u` with
`u p < 2 ^ 64`. For `p = 1` the reciprocal `2 ^ 64` wraps to `0`, as in the C code. -/
theorem mulDiv_magic {u p : Nat} (hp : 1 < p) (hu : u * p < 2 ^ 64) :
    mulDiv u (magic p) = u / p := by
  have hu' : u < 2 ^ 64 := Nat.lt_of_le_of_lt (Nat.le_mul_of_pos_right u (by lia)) hu
  rw [mulDiv_eq, Nat.mod_eq_of_lt hu', Nat.mod_eq_of_lt (magic_lt_two_pow_64 hp), Nat.mul_comm]
  exact Nat.mul_div_eq_div_of_mul_eq_add (by lia) (magic_mul_eq (by lia))
    (Nat.lt_of_le_of_lt (Nat.mul_le_mul_left u (by lia)) hu)

/-- `RP_MULMOD` with the reciprocal of a modulus `0 < p ≤ 2 ^ 32` computes the remainder of every
`u ≤ Ratpoints.mulModLimit` (`Ratpoints.mul_lt_two_pow_64_of_le_mulModLimit`). -/
theorem mulMod_magic_of_le_mulModLimit {u p : Nat} (hp : 0 < p) (hp32 : p ≤ 2 ^ 32)
    (hu : u ≤ mulModLimit) : mulMod u p (magic p) = u % p :=
  mulMod_magic hp (mul_lt_two_pow_64_of_le_mulModLimit hu hp32)

/-- `mod_mul` with the reciprocal of `p` computes the Euclidean remainder of every `a` with
`|a| p < 2 ^ 64`: the remainder of `|a|`, and its complement for a negative `a`. -/
theorem modMul_magic {a : Int} {p : Nat} (hp : 0 < p) (ha : a.natAbs * p < 2 ^ 64) :
    modMul a p (magic p) = a % p := by
  have h : (if a < 0 then -a else a).toNat = a.natAbs := by split <;> lia
  simp only [modMul, h, mulMod_magic hp ha]
  have h1 := Nat.div_add_mod a.natAbs p
  have hs := Nat.mod_lt a.natAbs hp
  generalize a.natAbs / p = k, a.natAbs % p = s at h1 hs
  refine ((Int.emod_eq_iff (b := p) (by lia)).mpr ⟨by split <;> lia, by split <;> lia, ?_⟩).symm
  by_cases ha0 : a < 0
  · split
    · exact ⟨k + 1, by grind⟩
    · exact ⟨k, by grind⟩
  · simp only [ha0, false_and, ↓reduceIte]
    exact ⟨-k, by grind⟩

/-! ### The helper `mod` -/

-- A rung of the ladder of `mod` on a residue modulo `n = 2 m`: a conditional subtraction of `m`
-- (`Int.emod_eq_ite_of_lt_two_mul`).
private theorem ite_le_emod_sub_eq_emod (a m : Int) {n : Int} (hm : 0 < m) (hn : n = 2 * m) :
    (if m ≤ a % n then a % n - m else a % n) = a % m := by
  rw [← Int.emod_eq_ite_of_lt_two_mul (Int.emod_nonneg _ (by lia))
      (hn ▸ Int.emod_lt_of_pos _ (by lia)),
    Int.emod_emod_of_dvd _ (hn ▸ Int.dvd_mul_left 2 m)]

-- `mod` for `-16 b ≤ a < 16 b`: `16 b` added to a negative `a`, then the ladder of conditional
-- subtractions.
private theorem modLong_eq_emod_of_le_of_lt {a b : Int} (hb : 0 < b) (h0 : -(16 * b) ≤ a)
    (h1 : a < 16 * b) : modLong a b = a % b := by
  simp only [modLong, Int.not_lt.mpr h0, Int.not_le.mpr h1, and_false, ↓reduceIte]
  have hy : (if a < 0 then a + 16 * b else a) % b = a % b := by split <;> simp
  have h2 : 0 ≤ (if a < 0 then a + 16 * b else a) := by split <;> lia
  have h3 : (if a < 0 then a + 16 * b else a) < 2 * (8 * b) := by split <;> lia
  generalize (if a < 0 then a + 16 * b else a) = y at hy h2 h3 ⊢
  rw [← hy, ← Int.emod_eq_ite_of_lt_two_mul h2 h3,
    ite_le_emod_sub_eq_emod y (4 * b) (by lia) (by lia),
    ite_le_emod_sub_eq_emod y (2 * b) (by lia) (by lia), ite_le_emod_sub_eq_emod y b hb rfl]

/-- The helper `mod` of the C code is the Euclidean `%`, for every integer `a` and every `b ≥ 0`;
that its values stay `long`s is `Ratpoints.fitsLong_sixteen_mul`, `Ratpoints.fitsLong_neg` and
`Ratpoints.fitsLong_add_sixteen_mul`. -/
theorem modLong_eq_emod (a : Int) {b : Int} (hb : 0 ≤ b) : modLong a b = a % b := by
  rcases Int.lt_or_eq_of_le hb with hb | rfl
  · rcases Int.lt_or_le a (-(16 * b)) with h | h
    · grind [modLong, Int.tmod_eq_emod, Int.emod_nonneg a (Int.ne_of_gt hb),
        Int.emod_lt_of_pos a hb]
    rcases Int.lt_or_le a (16 * b) with h' | h'
    · exact modLong_eq_emod_of_le_of_lt hb h h'
    · grind [modLong, Int.tmod_eq_emod_of_nonneg]
  · simp [modLong]

/-! ### The row indices of the first two stages -/

/-- The row of the sieve spec `s` repeats its first `p` bit arrays in the `Ratpoints.chunk - 1` bit
arrays after them: word `κ < Ratpoints.rbaPack` of bit array `x < p + chunk - 1` is word `κ` of bit
array `x mod p`, the copies that the chunked first stage reads past the first `p` bit arrays from a
start below `p` (`Ratpoints.Sieve.andRowsChunked`). -/
def SieveSpec.Wraps (s : SieveSpec) : Prop :=
  ∀ x < s.p + chunk - 1, ∀ κ < rbaPack, s.row[rbaPack * x + κ]! = s.row[rbaPack * (x % s.p) + κ]!

/-- A sieve spec whose modulus `p` and offset lie in the range that the packing of the numerators
gives them (`Ratpoints.Sieve.classOffsets`) and whose row has the copies of its first bit arrays
with the end `p`, as the run sets them up (`Ratpoints.Sieve.setRows`): `0 < p ≤
Ratpoints.maxPrimeEven`, the offset a residue below `2 p` plus `Ratpoints.rowBias`, so that under
the test `small` the sums of a word number and the offset that the first two stages reduce are at
most `Ratpoints.mulModLimit` in absolute value
(`Ratpoints.Sieve.SieveSpec.Fits.ite_modMul_modLong_eq_emod`,
`Ratpoints.Sieve.SieveSpec.Fits.ite_modMul_modLong_add_eq_emod`,
`Ratpoints.Sieve.SieveSpec.Fits.ite_mulMod_modLong_eq_toNat_emod`), and the row repeating its first
bit arrays (`Ratpoints.Sieve.SieveSpec.Wraps`) where the chunked first stage reads it. -/
structure SieveSpec.Fits (s : SieveSpec) : Prop where
  /-- The modulus is positive. -/
  pos : 0 < s.p
  /-- The modulus is at most `Ratpoints.maxPrimeEven`. -/
  le_maxPrimeEven : s.p ≤ maxPrimeEven
  /-- The offset is at least `Ratpoints.rowBias`. -/
  rowBias_le : rowBias ≤ s.offset
  /-- The offset is below `Ratpoints.rowBias + 2 p`. -/
  lt_rowBias_add : s.offset < rowBias + 2 * s.p
  /-- The end of the walk of the chunked first stage through the row is the modulus. -/
  stop_eq : s.stop = s.p
  /-- The row repeats its first bit arrays after the first `p`. -/
  wraps : s.Wraps

/-- When the test `small` of `Ratpoints.Sieve.siftPiece` holds, the word numbers from `lo` to `hi`
lie between `-Ratpoints.rowBias` and `Ratpoints.rowBias - 2 Ratpoints.maxPrimeEven`: the hypothesis
under which the first two stages may reduce by a multiplication. -/
def SmallFits (small : Bool) (lo hi : Int) : Prop :=
  small = true → -rowBias ≤ lo ∧ hi ≤ rowBias - 2 * maxPrimeEven

/-- The test `small` of a piece, as `Ratpoints.Sieve.siftPiece` computes it, says what
`Ratpoints.Sieve.SmallFits` asks of its word numbers. -/
theorem smallFits_decide (w0 : Int) (n : Nat) :
    SmallFits (decide (-rowBias ≤ w0 ∧ w0 + n ≤ rowBias - 2 * maxPrimeEven)) w0 (w0 + n) :=
  of_decide_eq_true

theorem SmallFits.mono {small : Bool} {lo hi lo' hi' : Int} (h : SmallFits small lo hi)
    (hlo : lo ≤ lo') (hhi : hi' ≤ hi) : SmallFits small lo' hi' :=
  fun hs ↦ ⟨Int.le_trans (h hs).1 hlo, Int.le_trans hhi (h hs).2⟩

/-- What the stages of the sieve need of the moduli `specs` with their reciprocals `mgs`, for the
word numbers from `lo` to `hi`: the sieve specs in the range of the packing, the reciprocals of
their moduli in the same order, and the test `small` of `Ratpoints.Sieve.SmallFits`. -/
structure StageFits (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (lo hi : Int) :
    Prop where
  /-- The sieve specs are in the range of the packing. -/
  fits : ∀ s ∈ specs, s.Fits
  /-- The reciprocals are those of the moduli, in the same order. -/
  magics : mgs = specs.map (magic ·.p)
  /-- The test `small` fits the word numbers. -/
  smallFits : SmallFits small lo hi

theorem StageFits.mono {specs : List SieveSpec} {mgs : List Nat} {small : Bool}
    {lo hi lo' hi' : Int} (h : StageFits specs mgs small lo hi) (hlo : lo ≤ lo') (hhi : hi' ≤ hi) :
    StageFits specs mgs small lo' hi' :=
  ⟨h.fits, h.magics, h.smallFits.mono hlo hhi⟩

/-- The first `k` of the moduli, with their reciprocals. -/
theorem stageFits_take {specs : List SieveSpec} {mgs : List Nat} {small : Bool} {lo hi : Int}
    (h : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p)) (hs : SmallFits small lo hi)
    (k : Nat) : StageFits (specs.take k) (mgs.take k) small lo hi :=
  ⟨fun s hs ↦ h.1 s (List.mem_of_mem_take hs), by rw [h.2, List.map_take], hs⟩

/-- The moduli after the first `k`, with their reciprocals. -/
theorem stageFits_drop {specs : List SieveSpec} {mgs : List Nat} {small : Bool} {lo hi : Int}
    (h : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p)) (hs : SmallFits small lo hi)
    (k : Nat) : StageFits (specs.drop k) (mgs.drop k) small lo hi :=
  ⟨fun s hs ↦ h.1 s (List.mem_of_mem_drop hs), by rw [h.2, List.map_drop], hs⟩

/-- For a word number `-Ratpoints.rowBias ≤ w0 ≤ Ratpoints.rowBias - 2 Ratpoints.maxPrimeEven`, the
value `-w0 - offset` that the first stage reduces is at most `Ratpoints.mulModLimit` in absolute
value. -/
theorem SieveSpec.Fits.natAbs_neg_sub_le {s : SieveSpec} (hs : s.Fits) {w0 : Int}
    (h0 : -rowBias ≤ w0) (h1 : w0 ≤ rowBias - 2 * maxPrimeEven) :
    (-w0 - s.offset).natAbs ≤ mulModLimit := by
  have := two_mul_rowBias_sub_one_le_mulModLimit
  have := hs.le_maxPrimeEven
  have := hs.rowBias_le
  have := hs.lt_rowBias_add
  generalize rowBias = R at *
  lia

/-- For a word number `-Ratpoints.rowBias ≤ i < Ratpoints.rowBias - 2 Ratpoints.maxPrimeEven`, the
value `i + offset` that the second stage reduces lies between `0` and `Ratpoints.mulModLimit`. -/
theorem SieveSpec.Fits.add_nonneg_and_toNat_le {s : SieveSpec} (hs : s.Fits) {i : Int}
    (h0 : -rowBias ≤ i) (h1 : i < rowBias - 2 * maxPrimeEven) :
    0 ≤ i + s.offset ∧ (i + s.offset).toNat ≤ mulModLimit := by
  have := two_mul_rowBias_sub_one_le_mulModLimit
  have := hs.le_maxPrimeEven
  have := hs.rowBias_le
  have := hs.lt_rowBias_add
  generalize rowBias = R at *
  lia

/-- The reduction of `a` modulo the modulus of a sieve spec in the range of the packing, by
`mod_mul` under the test `small` and by the helper `mod` otherwise, is the Euclidean remainder, for
`|a| ≤ Ratpoints.mulModLimit` under `small`. -/
theorem SieveSpec.Fits.ite_modMul_modLong_eq_emod_of_natAbs_le {s : SieveSpec} (hs : s.Fits)
    {small : Bool} {a : Int} (h : small = true → a.natAbs ≤ mulModLimit) :
    (if small then modMul a s.p (magic s.p) else modLong a s.p) = a % s.p := by
  cases small with
  | false => exact modLong_eq_emod _ (Int.natCast_nonneg _)
  | true => exact modMul_magic hs.pos (mul_lt_two_pow_64_of_le_mulModLimit (h rfl)
      (Nat.le_trans hs.le_maxPrimeEven maxPrimeEven_le_two_pow_32))

/-- The index of the first row of the first stage over a piece from the word number `w0` on, by
`mod_mul` under the test `small` and by the helper `mod` otherwise, is the Euclidean remainder of
`-w0 - offset`. -/
theorem SieveSpec.Fits.ite_modMul_modLong_eq_emod {s : SieveSpec} (hs : s.Fits) {small : Bool}
    {w0 : Int} {n : Nat} (h : SmallFits small w0 (w0 + n)) :
    (if small then modMul (-w0 - s.offset) s.p (magic s.p) else modLong (-w0 - s.offset) s.p) =
      (-w0 - s.offset) % s.p :=
  hs.ite_modMul_modLong_eq_emod_of_natAbs_le fun hsm ↦
    hs.natAbs_neg_sub_le (h hsm).1 (by lia [(h hsm).2])

/-- The start of the row of the chunked first stage at the first word number `w0` of a piece, by
`mod_mul` under the test `small` and by the helper `mod` otherwise, is the Euclidean remainder of
`w0 + offset`. -/
theorem SieveSpec.Fits.ite_modMul_modLong_add_eq_emod {s : SieveSpec} (hs : s.Fits) {small : Bool}
    {w0 : Int} (h : SmallFits small w0 w0) :
    (if small then modMul (w0 + s.offset) s.p (magic s.p) else modLong (w0 + s.offset) s.p) =
      (w0 + s.offset) % s.p :=
  hs.ite_modMul_modLong_eq_emod_of_natAbs_le fun hsm ↦ by
    rw [← Int.natAbs_neg, Int.neg_add, ← Int.sub_eq_add_neg]
    exact hs.natAbs_neg_sub_le (h hsm).1 (h hsm).2

/-- The row index of the second stage at the word number `i`, by a multiplication with the
reciprocal under the test `small` and by the helper `mod` otherwise, is the Euclidean remainder of
`i + offset`. -/
theorem SieveSpec.Fits.ite_mulMod_modLong_eq_toNat_emod {s : SieveSpec} (hs : s.Fits)
    {small : Bool} {i : Int} (h : SmallFits small i (i + 1)) :
    (if small then mulMod (i + s.offset).toNat s.p (magic s.p)
      else (modLong (i + s.offset) s.p).toNat) = ((i + s.offset) % s.p).toNat := by
  cases small with
  | false => rw [modLong_eq_emod _ (Int.natCast_nonneg _)]; rfl
  | true =>
    have ⟨h0, h1⟩ := hs.add_nonneg_and_toNat_le (h rfl).1 (by lia [(h rfl).2])
    simp only [↓reduceIte]
    rw [mulMod_magic_of_le_mulModLimit hs.pos
      (Nat.le_trans hs.le_maxPrimeEven maxPrimeEven_le_two_pow_32) h1,
      Int.toNat_emod h0 (Int.natCast_nonneg _), Int.toNat_natCast]

end Sieve

end Ratpoints

end
