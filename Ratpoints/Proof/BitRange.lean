/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Setup
public import Ratpoints.Proof.Packing

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Reductions
import Ratpoints.Proof.Words

/-!
# The bits of an interval of numerators and the longs of the packing

`numerators_to_bits` turns an interval of numerators into the bits of the packing of a class, whose
bit `j` stands for the numerator `a₀ + 2 ^ k j` (`Ratpoints.Sieve.NumClass.numerator`), on the
`long`s of the C code (`Ratpoints.Sieve.numeratorsToBits`): in both its forms it gives
`⌈(low - a₀) / 2 ^ k⌉` and `⌊(high - a₀) / 2 ^ k⌋`, the split form for all ends and the plain form
when the differences `a₀ - low` and `high - a₀` are `long`s, with no overflow, since the arithmetic
shift of a `long` is the floor of its quotient by `2 ^ k` and its and with the mask `2 ^ k - 1` the
Euclidean remainder. For the numerators `-H, …, H` of a height bound `H < 2 ^ 63`, in the form that
the C code takes for them, a numerator of the class lies in the interval exactly when its bit lies
between the two bits, and the numerators of these bits, in increasing order, are those of
`-H, …, H` in the class `a₀ mod 2 ^ k`. The values that the C code holds in `long`s for the packing
stay in range (`Ratpoints.fitsLong`): the offsets of the rows, the first and the last bit of the bit
arrays of `-H, …, H`, the numerators of their bits, and the sums of a word number and an offset that
the first two stages reduce outside the test `small`; the products of `fill_bp_list` and of
`class_offsets` are bounded in `Ratpoints.Proof.Packing`.

## Main statements

* `Ratpoints.Sieve.toInt_numeratorsToBits`, `Ratpoints.Sieve.toInt_numeratorsToBits_height`: the
  bits of the numerators of an interval, in both forms, and those of `-H, …, H`.
* `Ratpoints.Sieve.le_numerator_and_numerator_le_iff`,
  `Ratpoints.Sieve.map_range_numerator_eq_filter_numerators`: the numerator of a bit lies in an
  interval exactly when the bit lies between its bits, and the numerators of the bits of `-H, …, H`
  are those of `-H, …, H` in the class of the packing, in increasing order.
* `Ratpoints.Sieve.SieveEntry.PackedFor.lt_two_pow_63`: the offsets of the rows are `long`s.
* `Ratpoints.Sieve.neg_two_pow_le_rbaLength_mul_ediv`,
  `Ratpoints.Sieve.rbaLength_mul_ediv_add_one_le_two_pow`: the first bit of the bit array of a bit
  `lo ≥ -2 ^ (63 - k)` and the bit after the bit array of a bit `hi < 2 ^ (63 - k)` lie in
  `[-2 ^ (63 - k), 2 ^ (63 - k)]`, for `k ≤ 6`.
* `Ratpoints.Sieve.NumClass.fitsLong_numerator`: the numerators of the bits of the bit arrays of
  `-H, …, H` are `long`s.
* `Ratpoints.Sieve.fitsLong_neg_sub_and_fitsLong_add`: the values `-w_low - offset` and
  `i + offset` that the first two stages reduce by the helper `mod` are `long`s.

## Implementation notes

The file uses Lean core and `Std` only, so that the contracts of the sieve, in files without
Mathlib, can use it. The proofs use only the facts on the constants that `decide` checks next to
them, never their values: that `Ratpoints.rbaLength = 2 ^ Ratpoints.rbaShift` with
`Ratpoints.rbaShift < 32`, that `Ratpoints.rbaPack > 0`, that `Ratpoints.maxBitsInPrime ≤ 10` and
that `2 Ratpoints.rowBias - 1 ≤ Ratpoints.mulModLimit < 2 ^ 32`; the facts on words, natural
numbers and integers that are not about the model are in `Ratpoints.Proof.Bits`.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The bits of the numerators -/

theorem toInt_numeratorsToBits_false {low high : Int64} {cl : NumClass} (hcl : cl.WF)
    (h1 : cl.a0 - low.toInt < 2 ^ 63) (h2 : -2 ^ 63 ≤ high.toInt - cl.a0) :
    (numeratorsToBits low high cl false).1.toInt = -((cl.a0 - low.toInt) / 2 ^ cl.k) ∧
      (numeratorsToBits low high cl false).2.toInt = (high.toInt - cl.a0) / 2 ^ cl.k := by
  have ha : cl.a0 < 2 ^ 63 :=
    Nat.lt_trans hcl.a0_lt (Nat.pow_lt_pow_right (by decide) (by have := hcl.k_le; lia))
  have hk : cl.k < 64 := by have := hcl.k_le; lia
  have hm : (0 : Int) < 2 ^ cl.k := Int.pow_pos (by decide)
  have := low.toInt_lt
  have := high.toInt_lt
  have ha' := Int64.toInt_ofNat_of_lt ha
  have e1 : (Int64.ofNat cl.a0 - low).toInt = cl.a0 - low.toInt := by
    rw [Int64.toInt_sub_of_lt] <;> lia
  have e2 : (high - Int64.ofNat cl.a0).toInt = high.toInt - cl.a0 := by
    rw [Int64.toInt_sub_of_lt] <;> lia
  simp only [numeratorsToBits, Nat.toInt64, Bool.false_eq_true, ↓reduceIte]
  rw [Int64.toInt_neg_of_lt, Int64.toInt_shiftRight_ofNat _ hk, Int64.toInt_shiftRight_ofNat _ hk,
    e1, e2, Int.shiftRight_eq_div_pow, Int.shiftRight_eq_div_pow]
  · exact ⟨rfl, rfl⟩
  · rw [Int64.toInt_shiftRight_ofNat _ hk, e1, Int.shiftRight_eq_div_pow]
    exact Int.neg_two_pow_63_lt_ediv (by lia) hm

-- The facts on the stride `m = 2 ^ k`, `k ≤ 6`, and the residue `a₀ < m` of a class that the split
-- form of `numerators_to_bits` needs: `1 ≤ m ≤ 64`, `a₀ < m`, and the words of `a₀` and of `m - 1`.
private theorem stride_facts {k a0 : Nat} (hk : k ≤ 6) (ha : a0 < 2 ^ k) :
    (1 : Int) ≤ 2 ^ k ∧ (2 : Int) ^ k ≤ 64 ∧ (a0 : Int) < 2 ^ k ∧
      (Int64.ofNat a0).toInt = a0 ∧ (Int64.ofNat (2 ^ k - 1)).toInt = 2 ^ k - 1 := by
  have h64 : 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hk
  have := Nat.one_le_two_pow (n := k)
  refine ⟨mod_cast this, mod_cast h64, mod_cast ha, Int64.toInt_ofNat_of_lt (by
    have : 2 ^ 6 < 2 ^ 63 := by decide
    lia), Int64.toInt_ofNat_two_pow_sub_one (by lia)⟩

-- The low end of the split form: the multiple of `2 ^ k` in `x`, shifted, and the carry
-- `⌈(x mod 2 ^ k - a₀) / 2 ^ k⌉`, with no overflow.
private theorem toInt_shiftRight_add_shiftRight_add (x : Int64) {k a0 : Nat} (hk : k ≤ 6)
    (ha : a0 < 2 ^ k) :
    (x >>> Int64.ofNat k + ((x &&& Int64.ofNat (2 ^ k - 1)) - Int64.ofNat a0 +
      Int64.ofNat (2 ^ k - 1)) >>> Int64.ofNat k).toInt =
        x.toInt / 2 ^ k + (x.toInt % 2 ^ k - a0 + (2 ^ k - 1)) / 2 ^ k := by
  obtain ⟨hm, h64, ha', hA, hM⟩ := stride_facts hk ha
  have hl := Int.emod_lt_of_pos x.toInt (by lia : (0 : Int) < 2 ^ k)
  have hl0 := Int.emod_nonneg x.toInt (by lia : (2 : Int) ^ k ≠ 0)
  have e1 := Int64.toInt_and_ofNat_two_pow_sub_one x (by lia : k < 63)
  have e2 : ((x &&& Int64.ofNat (2 ^ k - 1)) - Int64.ofNat a0).toInt = x.toInt % 2 ^ k - a0 := by
    rw [Int64.toInt_sub_of_lt] <;> lia
  have e3 : ((x &&& Int64.ofNat (2 ^ k - 1)) - Int64.ofNat a0 + Int64.ofNat (2 ^ k - 1)).toInt =
      x.toInt % 2 ^ k - a0 + (2 ^ k - 1) := by
    rw [Int64.toInt_add_of_lt] <;> lia
  have hc := Int.sub_add_sub_one_ediv_mem hl0 hl (Int.natCast_nonneg a0) ha'
  have hb := Int.ediv_add_mem x.le_toInt x.toInt_lt hm (by lia) hc.2 fun h ↦ by
    rw [h] at hl ha' ⊢
    lia
  rw [Int64.toInt_add_of_lt] <;>
    simp only [Int64.toInt_shiftRight_ofNat _ (by lia : k < 64), e3, Int.shiftRight_eq_div_pow,
      Int.natCast_pow, Int.cast_ofNat_Int, hb.1, hb.2]

-- The high end of the split form: the multiple of `2 ^ k` in `x`, shifted, and the carry
-- `⌊(x mod 2 ^ k - a₀) / 2 ^ k⌋`, with no overflow.
private theorem toInt_shiftRight_add_shiftRight (x : Int64) {k a0 : Nat} (hk : k ≤ 6)
    (ha : a0 < 2 ^ k) :
    (x >>> Int64.ofNat k + ((x &&& Int64.ofNat (2 ^ k - 1)) - Int64.ofNat a0) >>>
      Int64.ofNat k).toInt = x.toInt / 2 ^ k + (x.toInt % 2 ^ k - a0) / 2 ^ k := by
  obtain ⟨hm, h64, ha', hA, -⟩ := stride_facts hk ha
  have hh := Int.emod_lt_of_pos x.toInt (by lia : (0 : Int) < 2 ^ k)
  have hh0 := Int.emod_nonneg x.toInt (by lia : (2 : Int) ^ k ≠ 0)
  have f1 := Int64.toInt_and_ofNat_two_pow_sub_one x (by lia : k < 63)
  have f2 : ((x &&& Int64.ofNat (2 ^ k - 1)) - Int64.ofNat a0).toInt = x.toInt % 2 ^ k - a0 := by
    rw [Int64.toInt_sub_of_lt] <;> lia
  have hc := Int.sub_ediv_mem hh0 hh (Int.natCast_nonneg a0) ha'
  have hb := Int.ediv_add_mem x.le_toInt x.toInt_lt hm hc.1 (by lia) fun h ↦ by
    rw [h] at hh ha' ⊢
    lia
  rw [Int64.toInt_add_of_lt] <;>
    simp only [Int64.toInt_shiftRight_ofNat _ (by lia : k < 64), f2, Int.shiftRight_eq_div_pow,
      Int.natCast_pow, Int.cast_ofNat_Int, hb.1, hb.2]

theorem toInt_numeratorsToBits_true {low high : Int64} {cl : NumClass} (hcl : cl.WF) :
    (numeratorsToBits low high cl true).1.toInt = -((cl.a0 - low.toInt) / 2 ^ cl.k) ∧
      (numeratorsToBits low high cl true).2.toInt = (high.toInt - cl.a0) / 2 ^ cl.k := by
  have hm : (0 : Int) < 2 ^ cl.k := Int.pow_pos (by decide)
  simp only [numeratorsToBits, Nat.toInt64, ↓reduceIte, Int64.one_shiftLeft_sub_one hcl.k_le,
    toInt_shiftRight_add_shiftRight_add _ hcl.k_le hcl.a0_lt,
    toInt_shiftRight_add_shiftRight _ hcl.k_le hcl.a0_lt]
  exact ⟨Int.ediv_add_emod_sub_add_sub_one_ediv _ _ hm, Int.ediv_add_emod_sub_ediv _ _ hm⟩

/-- The bits of the numerators `low, …, high` in the packing of a class with `k ≤ 6` and
`a₀ < 2 ^ k`, from `⌈(low - a₀) / 2 ^ k⌉` to `⌊(high - a₀) / 2 ^ k⌋`, in either form: the split one
for all ends, the plain one when the differences `a₀ - low` and `high - a₀` are `long`s, so that no
operation leaves the range of a `long`. -/
theorem toInt_numeratorsToBits {low high : Int64} {cl : NumClass} (hcl : cl.WF) {split : Bool}
    (hplain : split = false → cl.a0 - low.toInt < 2 ^ 63 ∧ -2 ^ 63 ≤ high.toInt - cl.a0) :
    (numeratorsToBits low high cl split).1.toInt = -((cl.a0 - low.toInt) / 2 ^ cl.k) ∧
      (numeratorsToBits low high cl split).2.toInt = (high.toInt - cl.a0) / 2 ^ cl.k := by
  cases split with
  | false => exact toInt_numeratorsToBits_false hcl (hplain rfl).1 (hplain rfl).2
  | true => exact toInt_numeratorsToBits_true hcl

/-- The bits of the numerators `-H, …, H` of a height bound `H < 2 ^ 63` in the packing of a class,
in the form of `numerators_to_bits` that `sift` takes, the split one for `H > 2 ^ 63 - 65`: from
`⌈(-H - a₀) / 2 ^ k⌉` to `⌊(H - a₀) / 2 ^ k⌋`. -/
theorem toInt_numeratorsToBits_height {H : Nat} (hH : H < 2 ^ 63) {cl : NumClass} (hcl : cl.WF) :
    (numeratorsToBits (-H.toInt64) H.toInt64 cl (decide (2 ^ 63 - 65 < H))).1.toInt =
        -((cl.a0 + H : Int) / 2 ^ cl.k) ∧
      (numeratorsToBits (-H.toInt64) H.toInt64 cl (decide (2 ^ 63 - 65 < H))).2.toInt =
        ((H : Int) - cl.a0) / 2 ^ cl.k := by
  have ha : cl.a0 < 64 :=
    Nat.lt_of_lt_of_le hcl.a0_lt (Nat.pow_le_pow_right (n := 2) (by decide) hcl.k_le)
  have hl : (-H.toInt64).toInt = -H := Int64.toInt_neg_ofNat_of_le (by lia)
  have hh : H.toInt64.toInt = H := Int64.toInt_ofNat_of_lt hH
  have := toInt_numeratorsToBits hcl (low := -H.toInt64) (high := H.toInt64)
    (split := decide (2 ^ 63 - 65 < H)) fun h ↦ by
      simp only [decide_eq_false_iff_not, Nat.not_lt] at h
      rw [hl, hh]
      constructor <;> lia
  rwa [hl, hh, Int.sub_neg] at this

/-- The numerator of bit `t` of a class lies in `lo, …, hi` exactly when `t` lies between the bits
of `numerators_to_bits` (`Ratpoints.Sieve.toInt_numeratorsToBits`). -/
theorem le_numerator_and_numerator_le_iff (cl : NumClass) (lo hi t : Int) :
    (lo ≤ cl.numerator t ∧ cl.numerator t ≤ hi) ↔
      (-((cl.a0 - lo) / 2 ^ cl.k) ≤ t ∧ t ≤ (hi - cl.a0) / 2 ^ cl.k) := by
  have hk : (0 : Int) < 2 ^ cl.k := Int.pow_pos (by decide)
  rw [NumClass.numerator, Int.neg_le_iff, Int.le_ediv_iff_mul_le hk, Int.le_ediv_iff_mul_le hk]
  constructor <;> intro h <;> constructor <;> lia

/-- The numerators of `-H, …, H` that are `a₀` modulo `m`, for `a₀ < m`, in increasing order:
`r - H, r + m - H, …`, for the residue `r` of `a₀ + H` modulo `m`. -/
theorem filter_numerators_emod_eq {a0 m : Nat} (ha : a0 < m) (H : Nat) :
    (BruteForce.numerators H).filter (fun a ↦ a % (m : Int) == (a0 : Int)) =
      (List.range ((2 * H + 1 + (m - 1 - (a0 + H) % m)) / m)).map
        fun j ↦ (((a0 + H) % m + m * j : Nat) : Int) - H := by
  simp only [BruteForce.numerators, List.filter_map]
  rw [List.filter_congr (q := fun i ↦ i % m == (a0 + H) % m) fun i _ ↦ by
    rw [Function.comp_apply, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact_mod_cast Int.sub_emod_eq_iff ha,
    List.filter_range_mod_eq (Nat.mod_lt _ (by lia)), List.map_map]
  rfl

-- The numerators `a₀ + m (lo + i)` of the bits from `lo = -q` to `hi = ⌊(H - a₀) / m⌋`, for
-- `a₀ + H = m q + r` with `r < m`, are `r - H, r + m - H, …`, as many as there are numerators of
-- `-H, …, H` that are `r - H` modulo `m`.
private theorem map_range_eq_map_range {a0 H m q r : Nat} (hm : 0 < m) (hr : r < m)
    (hA : m * q + r = a0 + H) :
    (List.range (((H : Int) - a0) / m + 1 - -(q : Int)).toNat).map
        (fun i : Nat ↦ (a0 : Int) + m * (-(q : Int) + i)) =
      (List.range ((2 * H + 1 + (m - 1 - r)) / m)).map fun j ↦ ((r + m * j : Nat) : Int) - H := by
  have hA' : (a0 + H : Int) = m * q + r := mod_cast hA.symm
  have hm0 : (m : Int) ≠ 0 := by lia
  have e1 : ((H : Int) - a0) = (2 * H - r : Int) + (-(q : Int)) * m := by rw [Int.neg_mul]; lia
  have h2 : (((2 * H + 1 + (m - 1 - r)) / m : Nat) : Int) = (2 * H - r : Int) / m + 1 := by
    rw [Int.natCast_ediv, show ((2 * H + 1 + (m - 1 - r) : Nat) : Int) = (2 * H - r : Int) + 1 * m
      by lia, Int.add_mul_ediv_right _ _ hm0]
  have hlen : (((H : Int) - a0) / m + 1 - -(q : Int)).toNat = (2 * H + 1 + (m - 1 - r)) / m := by
    rw [e1, Int.add_mul_ediv_right _ _ hm0]
    lia
  rw [hlen]
  refine List.map_congr_left fun j _ ↦ ?_
  simp only [Int.mul_add, Int.mul_neg]
  push_cast
  lia

/-- The numerators of `-H, …, H` that are `a₀` modulo the stride `2 ^ k` of a class, in increasing
order, are those of the bits from `lo = ⌈(-H - a₀) / 2 ^ k⌉` to `hi = ⌊(H - a₀) / 2 ^ k⌋`. -/
theorem map_range_numerator_eq_filter_numerators {cl : NumClass} (hcl : cl.WF) {H : Nat}
    {lo hi : Int} (hlo : lo = -((cl.a0 + H : Int) / 2 ^ cl.k))
    (hhi : hi = ((H : Int) - cl.a0) / 2 ^ cl.k) :
    (List.range (hi + 1 - lo).toNat).map (fun i : Nat ↦ cl.numerator (lo + i)) =
      (BruteForce.numerators H).filter fun a ↦ a % 2 ^ cl.k == (cl.a0 : Int) := by
  have hk : (2 : Int) ^ cl.k = ((2 ^ cl.k : Nat) : Int) := by push_cast; rfl
  rw [hk, filter_numerators_emod_eq hcl.a0_lt H]
  simp only [NumClass.numerator, hlo, hhi, hk]
  exact map_range_eq_map_range (Nat.two_pow_pos _) (Nat.mod_lt _ (Nat.two_pow_pos _))
    (Nat.div_add_mod _ _)


/-! ### The longs of the offsets and of the bit ranges -/

/-- The offsets of the rows are `long`s, below `Ratpoints.rowBias + 2 p ≤ 2 ^ 31 + 2 ^ 11`. -/
theorem SieveEntry.PackedFor.lt_two_pow_63 {e : SieveEntry} {cl : NumClass} {off : Nat}
    (h : e.PackedFor cl off) : off < 2 ^ 63 := by
  have := h.lt_rowBias_add
  have := Nat.le_trans h.le_maxPrimeEven maxPrimeEven_le_two_pow_10
  have := rowBias_le_two_pow_31
  generalize rowBias = R at *
  lia

/-- The width `Ratpoints.rbaLength = 2 ^ Ratpoints.rbaShift` of the bit arrays times
`2 ^ (63 - k - rbaShift)` is `2 ^ (63 - k)`, for a stride `2 ^ k`, `k ≤ 6`. -/
theorem rbaLength_mul_two_pow {k : Nat} (hk : k ≤ 6) :
    (rbaLength : Int) * 2 ^ (63 - k - rbaShift) = 2 ^ (63 - k) := by
  have hs := rbaShift_lt_thirty_two
  rw [rbaLength_eq_two_pow_rbaShift, Int.natCast_pow, Int.cast_ofNat_Int, ← Int.pow_add]
  congr 1
  lia

/-- The first bit `Ratpoints.rbaLength ⌊lo / Ratpoints.rbaLength⌋` of the bit array of the bit
`lo ≥ -2 ^ (63 - k)` is at least `-2 ^ (63 - k)`, for a stride `2 ^ k`, `k ≤ 6`, since
`Ratpoints.rbaLength` divides `2 ^ (63 - k)`. -/
theorem neg_two_pow_le_rbaLength_mul_ediv {k : Nat} (hk : k ≤ 6) {lo : Int}
    (hlo : -2 ^ (63 - k) ≤ lo) : -2 ^ (63 - k) ≤ rbaLength * (lo / rbaLength) := by
  have hT := rbaLength_mul_two_pow hk
  have h1 : -2 ^ (63 - k - rbaShift) ≤ lo / rbaLength :=
    (Int.le_ediv_iff_mul_le natCast_rbaLength_pos).mpr (by
      rw [Int.neg_mul, Int.mul_comm, hT]; exact hlo)
  calc -2 ^ (63 - k) = (rbaLength : Int) * -2 ^ (63 - k - rbaShift) := by rw [Int.mul_neg, hT]
    _ ≤ rbaLength * (lo / rbaLength) :=
      Int.mul_le_mul_of_nonneg_left h1 (Int.le_of_lt natCast_rbaLength_pos)

/-- The bit `Ratpoints.rbaLength (⌊hi / Ratpoints.rbaLength⌋ + 1)` after the bit array of the bit
`hi < 2 ^ (63 - k)` is at most `2 ^ (63 - k)`, for a stride `2 ^ k`, `k ≤ 6`, since
`Ratpoints.rbaLength` divides `2 ^ (63 - k)`. -/
theorem rbaLength_mul_ediv_add_one_le_two_pow {k : Nat} (hk : k ≤ 6) {hi : Int}
    (hhi : hi < 2 ^ (63 - k)) : rbaLength * (hi / rbaLength + 1) ≤ 2 ^ (63 - k) := by
  have hT := rbaLength_mul_two_pow hk
  have h2 : hi / rbaLength < 2 ^ (63 - k - rbaShift) :=
    (Int.ediv_lt_iff_lt_mul natCast_rbaLength_pos).mpr (by rw [Int.mul_comm, hT]; exact hhi)
  calc (rbaLength : Int) * (hi / rbaLength + 1) ≤ rbaLength * 2 ^ (63 - k - rbaShift) :=
        Int.mul_le_mul_of_nonneg_left (by lia) (Int.le_of_lt natCast_rbaLength_pos)
    _ = 2 ^ (63 - k) := hT

/-- The numerators of the bits of the bit arrays from `⌊lo / Ratpoints.rbaLength⌋` to
`⌊hi / Ratpoints.rbaLength⌋`, for the bits `lo, hi` of the numerators `-H, …, H` of a height bound
`H < 2 ^ 63` in the packing of a class (`Ratpoints.Sieve.toInt_numeratorsToBits_height`), are
`long`s: the extraction computes them, and the first numerators of the words, as `long`s. -/
theorem NumClass.fitsLong_numerator {cl : NumClass} (hcl : cl.WF) {H : Nat} (hH : H < 2 ^ 63)
    {j : Int} (hj : rbaLength * (-((cl.a0 + H : Int) / 2 ^ cl.k) / rbaLength) ≤ j)
    (hj' : j < rbaLength * (((H : Int) - cl.a0) / 2 ^ cl.k / rbaLength + 1)) :
    fitsLong (cl.numerator j) = true := by
  have hm : (0 : Int) < 2 ^ cl.k := Int.pow_pos (by decide)
  have hkT : (2 : Int) ^ cl.k * 2 ^ (63 - cl.k) = 2 ^ 63 := by
    rw [← Int.pow_add]; congr 1; have := hcl.k_le; lia
  have ha : (cl.a0 : Int) < 2 ^ cl.k := mod_cast hcl.a0_lt
  have hlo : -2 ^ (63 - cl.k) ≤ -((cl.a0 + H : Int) / 2 ^ cl.k) :=
    Int.neg_le_neg (Int.lt_add_one_iff.mp ((Int.ediv_lt_iff_lt_mul hm).mpr (by
      rw [Int.add_mul, Int.mul_comm (2 ^ (63 - cl.k)), hkT]; lia)))
  have hhi : ((H : Int) - cl.a0) / 2 ^ cl.k < 2 ^ (63 - cl.k) :=
    (Int.ediv_lt_iff_lt_mul hm).mpr (by rw [Int.mul_comm, hkT]; lia)
  have h3 := Int.mul_le_mul_of_nonneg_left
    (Int.le_trans (neg_two_pow_le_rbaLength_mul_ediv hcl.k_le hlo) hj) (Int.le_of_lt hm)
  have h4 := Int.mul_le_mul_of_nonneg_left (Int.le_sub_one_of_lt
    (Int.lt_of_lt_of_le hj' (rbaLength_mul_ediv_add_one_le_two_pow hcl.k_le hhi))) (Int.le_of_lt hm)
  rw [Int.mul_neg, hkT] at h3
  rw [Int.mul_sub, hkT] at h4
  simp only [fitsLong, NumClass.numerator, Bool.and_eq_true]
  constructor <;> lia

theorem sixty_four_le_rbaLength : 64 ≤ rbaLength :=
  Nat.le_mul_of_pos_right 64 rbaPack_pos

/-- A word number `w` with `-2 ^ 63 ≤ Ratpoints.rbaLength w ≤ 2 ^ 63`, the word numbers of the bit
arrays of the numerators of a height bound below `2 ^ 63`
(`Ratpoints.Sieve.neg_two_pow_le_rbaLength_mul_ediv`,
`Ratpoints.Sieve.rbaLength_mul_ediv_add_one_le_two_pow`), minus or plus an offset below `2 ^ 32` is
a `long`: the values `-w_low - offset` and `i + offset` that the first two stages reduce by the
helper `mod` outside the test `small`. -/
theorem fitsLong_neg_sub_and_fitsLong_add {w : Int} {off : Nat} (hw : -2 ^ 63 ≤ rbaLength * w)
    (hw' : rbaLength * w ≤ 2 ^ 63) (hoff : off < 2 ^ 32) :
    fitsLong (-w - off) = true ∧ fitsLong (w + off) = true := by
  have hR : (64 : Int) ≤ rbaLength := mod_cast sixty_four_le_rbaLength
  simp only [fitsLong, Bool.and_eq_true, decide_eq_true_eq]
  rcases Int.lt_or_le w 0 with h | h
  · have := Int.mul_le_mul_of_nonpos_right hR (Int.le_of_lt h)
    constructor <;> constructor <;> lia
  · have := Int.mul_le_mul_of_nonneg_right hR h
    constructor <;> constructor <;> lia

end Sieve

end Ratpoints

end
