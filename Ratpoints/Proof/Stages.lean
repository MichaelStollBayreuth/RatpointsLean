/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Sieve
public import Std.WP

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Words
import Std.Tactic.Do

/-!
# The contracts of the stages of the sieve

The reductions by a reciprocal (`Ratpoints.Sieve.mulMod`, `Ratpoints.Sieve.mulDiv`) compute the
remainder and the quotient where the C code relies on them: with the reciprocal
`Ratpoints.Sieve.magic p`, which exceeds `2 ^ 64 / p` by less than `1`, for every `u` with
`u p < 2 ^ 64`, and so for the values at most `Ratpoints.mulModLimit` and the moduli up to
`2 ^ 32`. The test for common factors on the 64-bit words of the C code
(`Ratpoints.Sieve.relprime`) decides whether a numerator is prime to the denominator, and none of
its operations leaves the range of a `long`. The contracts of the loops are `@[spec]` theorems
proved with `vcgen`, the program logic of Lean core, with loop invariants that are named
definitions.

## Main definitions

* `Ratpoints.Sieve.RelprimeOddInvariant`: the invariant of the loop of the binary algorithm.

## Main statements

* `Ratpoints.Sieve.magic_mul_eq`: `magic p · p = 2 ^ 64 + δ` with `δ < p`.
* `Ratpoints.Sieve.mulMod_magic`, `Ratpoints.Sieve.mulDiv_magic`: with the reciprocal
  `Ratpoints.Sieve.magic p`, the reductions give `u % p` and `u / p` for `u p < 2 ^ 64`;
  `Ratpoints.Sieve.sub_mulDiv_magic_mul`: the remainder as `u - RP_MULDIV(u) p`.
* `Ratpoints.mul_lt_two_pow_64_of_le_mulModLimit`: `u p < 2 ^ 64` for `u ≤ Ratpoints.mulModLimit`
  and `p ≤ 2 ^ 32`.
* `Ratpoints.Sieve.relprimeOdd_spec`, `Ratpoints.Sieve.relprime_spec`: the binary algorithm
  decides whether `gcd(m, n) = 1` for odd positive words `m` and `n`, and for words
  `m > -2 ^ 63` and `n ≥ 1`.

## Implementation notes

The file uses Lean core and `Std` only. The proofs use only the fact on the constants that `decide`
checks next to them, that `Ratpoints.mulModLimit < 2 ^ 32`, never their values. The words of the
test for common factors are read as natural numbers by `Int64.toNatClampNeg`, which is faithful on
the non-negative words that the binary algorithm keeps; the facts on words that are not about the
model are in `Ratpoints.Proof.Bits`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

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

/-! ### The test for common factors -/

/-- The invariant of the loop of `Ratpoints.Sieve.relprimeOdd`, whose state is `(m, n)`: both words
are odd as natural numbers (`Int64.toNatClampNeg`), and so positive, they have the gcd `g` of the
operands, and `m = n` at the exit. -/
def RelprimeOddInvariant (g : Nat) : Std.WP.WhileInvariant (Int64 × Int64) Prop :=
  .mk fun exit s ↦ s.1.toNatClampNeg % 2 = 1 ∧ s.2.toNatClampNeg % 2 = 1 ∧
    Nat.gcd s.1.toNatClampNeg s.2.toNatClampNeg = g ∧ (exit = true → s.1 = s.2)

/-- In the loop of `Ratpoints.Sieve.relprimeOdd`, from `m ≠ n`, the absolute value of the difference
is a word other than `0`, whose lowest set bit `RP_CTZL` may look for. -/
theorem RelprimeOddInvariant.toUInt64_ne_zero {g k : Nat} {m n : Int64} (hmn : (n != m) = true)
    (h : m.toNatClampNeg + n.toNatClampNeg = k ∧ m.toNatClampNeg % 2 = 1 ∧
      n.toNatClampNeg % 2 = 1 ∧ Nat.gcd m.toNatClampNeg n.toNatClampNeg = g ∧
      (false = true → m = n)) :
    ¬((m - n ^^^ (m - n) >>> 63) - (m - n) >>> 63).toUInt64 = 0 :=
  Int64.toUInt64_ne_zero_of_pos (Int64.xor_shiftRight_63_sub_pos
    (Int64.le_of_lt ((Int64.toNatClampNeg_pos_iff m).mp (by lia)))
    (Int64.le_of_lt ((Int64.toNatClampNeg_pos_iff n).mp (by lia))) (bne_iff_ne.mp hmn).symm)

/-- A step of the loop of `Ratpoints.Sieve.relprimeOdd` from `m ≠ n`, in the shape of the
verification condition: `n` becomes the smaller of the two and `m` the odd part of their distance
`d`, which keep what the loop keeps, and their sum, the measure, decreases. -/
theorem RelprimeOddInvariant.shiftRight_min {g k t : Nat} {m n d : Int64} (hmn : (n != m) = true)
    (h : m.toNatClampNeg + n.toNatClampNeg = k ∧ m.toNatClampNeg % 2 = 1 ∧
      n.toNatClampNeg % 2 = 1 ∧ Nat.gcd m.toNatClampNeg n.toNatClampNeg = g ∧
      (false = true → m = n))
    (hd : d = (m - n ^^^ (m - n) >>> 63) - (m - n) >>> 63)
    (ht : t = d.toUInt64.toBitVec.ctz.toNat) :
    (d >>> Int64.ofNat t).toNatClampNeg + (n + (m - n &&& (m - n) >>> 63)).toNatClampNeg < k ∧
      (d >>> Int64.ofNat t).toNatClampNeg % 2 = 1 ∧
      (n + (m - n &&& (m - n) >>> 63)).toNatClampNeg % 2 = 1 ∧
      Nat.gcd (d >>> Int64.ofNat t).toNatClampNeg (n + (m - n &&& (m - n) >>> 63)).toNatClampNeg =
        g ∧ (false = true → d >>> Int64.ofNat t = n + (m - n &&& (m - n) >>> 63)) := by
  obtain ⟨rfl, hm, hn, rfl, -⟩ := h
  have hm0 := Int64.le_of_lt ((Int64.toNatClampNeg_pos_iff m).mp (by lia))
  have hn0 := Int64.le_of_lt ((Int64.toNatClampNeg_pos_iff n).mp (by lia))
  have hd0 : 0 < d := hd ▸ Int64.xor_shiftRight_63_sub_pos hm0 hn0 (bne_iff_ne.mp hmn).symm
  have h1 := Int64.two_pow_ctz_mul_toNatClampNeg_shiftRight hd0
  rw [hd, Int64.toNatClampNeg_xor_shiftRight_63_sub hm0 hn0, ← hd, ← ht] at h1
  rw [Int64.toNatClampNeg_add_and_shiftRight_63 hm0 hn0, ht]
  exact ⟨Nat.add_min_lt_add_of_two_pow_mul_eq (by lia) (by lia) (ht ▸ h1),
    Int64.toNatClampNeg_shiftRight_ctz_mod_two hd0, by rw [Nat.min_def]; split <;> assumption,
    Nat.gcd_min_eq_gcd_of_two_pow_mul_eq hm hn (ht ▸ h1), nofun⟩

theorem RelprimeOddInvariant.exit {g k : Nat} {m n : Int64} (hmn : ¬(n != m) = true)
    (h : m.toNatClampNeg + n.toNatClampNeg = k ∧ m.toNatClampNeg % 2 = 1 ∧
      n.toNatClampNeg % 2 = 1 ∧ Nat.gcd m.toNatClampNeg n.toNatClampNeg = g ∧
      (false = true → m = n)) :
    m.toNatClampNeg % 2 = 1 ∧ n.toNatClampNeg % 2 = 1 ∧
      Nat.gcd m.toNatClampNeg n.toNatClampNeg = g ∧ (True → m = n) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, fun _ ↦ (bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hmn)).symm⟩

/-- At the exit of the loop of `Ratpoints.Sieve.relprimeOdd`, `m = n` is the gcd `g`. -/
theorem RelprimeOddInvariant.post {g : Nat} {m n : Int64}
    (h : m.toNatClampNeg % 2 = 1 ∧ n.toNatClampNeg % 2 = 1 ∧
      Nat.gcd m.toNatClampNeg n.toNatClampNeg = g ∧ (True → m = n)) :
    (m == 1) = decide (g = 1) := by
  obtain ⟨-, -, rfl, h⟩ := h
  rw [← h trivial, Nat.gcd_self, Bool.beq_eq_decide_eq, decide_eq_decide,
    Int64.toNatClampNeg_eq_one_iff]

/-- The loop ends, since the sum of the two values decreases, and it ends at `m = n = gcd(m, n)`;
no operation leaves the range of a `long`, since the values stay positive. -/
@[spec]
theorem relprimeOdd_spec (m n : Int64) :
    ⦃ m.toNatClampNeg % 2 = 1 ∧ n.toNatClampNeg % 2 = 1 ⦄ relprimeOdd m n
      ⦃ fun r ↦ r = decide (Nat.gcd m.toNatClampNeg n.toNatClampNeg = 1) ⦄ := by
  vcgen [relprimeOdd] invariants
  · RelprimeOddInvariant (Nat.gcd m.toNatClampNeg n.toNatClampNeg)
  · Std.WP.Variant.ofMeasure fun s : Int64 × Int64 ↦ s.1.toNatClampNeg + s.2.toNatClampNeg
  all_goals simp only [RelprimeOddInvariant, Std.WP.WhileInvariant.mk_apply,
    Std.WP.Variant.evalsTo_ofMeasure, Std.WP.Variant.evalsBelow_ofMeasure_nat,
    Std.WP.Assertion.NondetFun.evalsTo_pure, Lean.Order.meet_prop_eq_and,
    Lean.Order.ofProp_prop_eq] at *
  all_goals first
    | exact ⟨‹_ ∧ _›.1, ‹_ ∧ _›.2, trivial, nofun⟩
    | exact RelprimeOddInvariant.post ‹_›
    | exact RelprimeOddInvariant.toUInt64_ne_zero ‹_› ‹_›
    | exact RelprimeOddInvariant.shiftRight_min ‹_› ‹_› rfl ‹_›
    | exact RelprimeOddInvariant.exit ‹_› ‹_›

-- A numerator `m ≠ 0` other than `-2 ^ 63` by its absolute value, a positive word, which has the
-- gcd of `m` with the positive word `n`.
private theorem ite_neg_pos_and_gcd_eq {m n : Int64} (h : Int64.minValue < m ∧ 0 < n)
    (hm : ¬(m == 0) = true) :
    0 < (if m < 0 then -m else m) ∧ 0 < n ∧
      Int.gcd m.toInt n.toInt =
        Nat.gcd (if m < 0 then -m else m).toNatClampNeg n.toNatClampNeg := by
  have h1 := Int64.toNatClampNeg_ite_neg h.1
  refine ⟨(Int64.toNatClampNeg_pos_iff _).mp ?_, h.2, ?_⟩
  · rw [h1, Int.natAbs_pos, ← Int64.toInt_zero, Ne, Int64.toInt_inj]
    exact fun h' ↦ hm (beq_iff_eq.mpr h')
  · rw [h1, Int64.toNatClampNeg_eq_natAbs (Int64.le_of_lt h.2)]
    rfl

-- The numerator `0`, prime to the positive word `n` when `n = 1`.
private theorem beq_one_eq_decide_gcd {m n : Int64} (h : Int64.minValue < m ∧ 0 < n)
    (hm : (m == 0) = true) : (n == 1) = decide (Int.gcd m.toInt n.toInt = 1) := by
  rw [beq_iff_eq.mp hm, Int64.toInt_zero, Int.gcd_zero_left, ← Int64.toNatClampNeg_eq_natAbs
    (Int64.le_of_lt h.2), Bool.beq_eq_decide_eq, decide_eq_decide, Int64.toNatClampNeg_eq_one_iff]

-- Two even positive words, which are not coprime.
private theorem false_eq_decide_gcd {m n x : Int64}
    (hx : 0 < x ∧ 0 < n ∧ Int.gcd m.toInt n.toInt = Nat.gcd x.toNatClampNeg n.toNatClampNeg)
    (hxe : (x &&& 1 == 0) = true) (hne : (n &&& 1 == 0) = true) :
    false = decide (Int.gcd m.toInt n.toInt = 1) := by
  have h1 := (Int64.and_one_eq_zero_iff (Int64.le_of_lt hx.1)).mp (beq_iff_eq.mp hxe)
  have h2 := (Int64.and_one_eq_zero_iff (Int64.le_of_lt hx.2.1)).mp (beq_iff_eq.mp hne)
  refine (decide_eq_false fun h ↦ ?_).symm
  have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
  rw [← hx.2.2, h] at this
  lia

-- The odd parts of two positive words.
private theorem toNatClampNeg_shiftRight_mod_two {m n x : Int64} {s t : Nat}
    (hx : 0 < x ∧ 0 < n ∧ Int.gcd m.toInt n.toInt = Nat.gcd x.toNatClampNeg n.toNatClampNeg)
    (ht : t = x.toUInt64.toBitVec.ctz.toNat) (hs : s = n.toUInt64.toBitVec.ctz.toNat) :
    (x >>> Int64.ofNat t).toNatClampNeg % 2 = 1 ∧ (n >>> Int64.ofNat s).toNatClampNeg % 2 = 1 :=
  by subst ht hs; exact ⟨Int64.toNatClampNeg_shiftRight_ctz_mod_two hx.1,
    Int64.toNatClampNeg_shiftRight_ctz_mod_two hx.2.1⟩

-- An odd positive word and the odd part of a positive word.
private theorem toNatClampNeg_mod_two_of_and_one {m n x : Int64} {s : Nat}
    (hx : 0 < x ∧ 0 < n ∧ Int.gcd m.toInt n.toInt = Nat.gcd x.toNatClampNeg n.toNatClampNeg)
    (hxo : ¬(x &&& 1 == 0) = true) (hs : s = n.toUInt64.toBitVec.ctz.toNat) :
    x.toNatClampNeg % 2 = 1 ∧ (n >>> Int64.ofNat s).toNatClampNeg % 2 = 1 := by
  have := (not_congr (Int64.and_one_eq_zero_iff (Int64.le_of_lt hx.1))).mp
    (fun h ↦ hxo (beq_iff_eq.mpr h))
  exact ⟨by lia, hs ▸ Int64.toNatClampNeg_shiftRight_ctz_mod_two hx.2.1⟩

-- The odd parts of a positive word and of an odd positive word have the gcd of the two words.
private theorem eq_decide_gcd_of_shiftRight {m n x : Int64} {s t : Nat} {r : Bool}
    (hx : 0 < x ∧ 0 < n ∧ Int.gcd m.toInt n.toInt = Nat.gcd x.toNatClampNeg n.toNatClampNeg)
    (hno : ¬(n &&& 1 == 0) = true)
    (hr : r = decide
      (Nat.gcd (x >>> Int64.ofNat t).toNatClampNeg (n >>> Int64.ofNat s).toNatClampNeg = 1))
    (ht : t = x.toUInt64.toBitVec.ctz.toNat) (hs : s = n.toUInt64.toBitVec.ctz.toNat) :
    r = decide (Int.gcd m.toInt n.toInt = 1) := by
  subst ht hs hr
  have := (not_congr (Int64.and_one_eq_zero_iff (Int64.le_of_lt hx.2.1))).mp
    (fun h ↦ hno (beq_iff_eq.mpr h))
  rw [hx.2.2, decide_eq_decide, Nat.gcd_comm, Nat.gcd_eq_of_two_pow_mul_eq
    (Int64.two_pow_ctz_mul_toNatClampNeg_shiftRight hx.2.1)
    (Int64.toNatClampNeg_shiftRight_ctz_mod_two hx.1), Nat.gcd_comm,
    Nat.gcd_eq_of_two_pow_mul_eq (Int64.two_pow_ctz_mul_toNatClampNeg_shiftRight hx.1) (by lia)]

-- An odd positive word and the odd part of a positive word have the gcd of the two words.
private theorem eq_decide_gcd_of_shiftRight_right {m n x : Int64} {s : Nat} {r : Bool}
    (hx : 0 < x ∧ 0 < n ∧ Int.gcd m.toInt n.toInt = Nat.gcd x.toNatClampNeg n.toNatClampNeg)
    (hxo : ¬(x &&& 1 == 0) = true)
    (hr : r = decide (Nat.gcd x.toNatClampNeg (n >>> Int64.ofNat s).toNatClampNeg = 1))
    (hs : s = n.toUInt64.toBitVec.ctz.toNat) :
    r = decide (Int.gcd m.toInt n.toInt = 1) := by
  subst hs hr
  have := (not_congr (Int64.and_one_eq_zero_iff (Int64.le_of_lt hx.1))).mp
    (fun h ↦ hxo (beq_iff_eq.mpr h))
  rw [hx.2.2, decide_eq_decide, Nat.gcd_comm, Nat.gcd_eq_of_two_pow_mul_eq
    (Int64.two_pow_ctz_mul_toNatClampNeg_shiftRight hx.2.1) (by lia), Nat.gcd_comm]

/-- The binary algorithm decides whether the numerator `m` is prime to the denominator `n ≥ 1`, for
`m` other than `-2 ^ 63`, whose negation would leave the range of a `long`; no operation leaves
it. -/
@[spec]
theorem relprime_spec (m n : Int64) :
    ⦃ Int64.minValue < m ∧ 0 < n ⦄ relprime m n
      ⦃ fun r ↦ r = decide (Int.gcd m.toInt n.toInt = 1) ⦄ := by
  vcgen [relprime]
  -- at reducible transparency, so that an alternative that does not fit fails at once instead of
  -- unfolding the operations on the words
  all_goals with_reducible first
    | exact beq_one_eq_decide_gcd ‹_› ‹_›
    | exact Int64.toUInt64_ne_zero_of_pos ‹_ ∧ 0 < n›.2
    | exact Int64.toUInt64_ne_zero_of_pos (ite_neg_pos_and_gcd_eq ‹_› ‹_›).1
    | exact false_eq_decide_gcd (ite_neg_pos_and_gcd_eq ‹_› ‹_›) ‹_› ‹_›
    | exact eq_decide_gcd_of_shiftRight (ite_neg_pos_and_gcd_eq ‹_› ‹_›) ‹_› ‹_› ‹_› ‹_›
    | exact eq_decide_gcd_of_shiftRight_right (ite_neg_pos_and_gcd_eq ‹_› ‹_›) ‹_› ‹_› ‹_›
    | exact toNatClampNeg_shiftRight_mod_two (ite_neg_pos_and_gcd_eq ‹_› ‹_›) ‹_› ‹_›
    | exact toNatClampNeg_mod_two_of_and_one (ite_neg_pos_and_gcd_eq ‹_› ‹_›) ‹_› ‹_›

end Sieve

end Ratpoints

end
