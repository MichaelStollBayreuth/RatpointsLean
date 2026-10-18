/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Setup
public import Ratpoints.Proof.Packing

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers

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
`class_offsets` are bounded in `Ratpoints.Proof.Reductions`. The ranges of the numerators that the
bounds of the search intervals give for a denominator are stated here too, on Lean core.

## Main definitions

* `Ratpoints.Sieve.IntervalBounds.Represents`, `Ratpoints.Sieve.RangesFor`,
  `Ratpoints.Sieve.inRanges`: the range of the numerators that the bounds of a search interval give
  for a denominator, the ranges of the search intervals of a run, and the membership in them, the
  interface between the bounds of the search intervals (`Ratpoints.Proof.Bounds`) and the sieve of
  one denominator (`Ratpoints.Sieve.sift_spec`).

## Main statements

* `Ratpoints.Sieve.toInt_numeratorsToBits`, `Ratpoints.Sieve.toInt_numeratorsToBits_height`: the
  bits of the numerators of an interval, in both forms, and those of `-H, …, H`.
* `Ratpoints.Sieve.NumClass.le_numerator_and_numerator_le_iff`,
  `Ratpoints.Sieve.NumClass.WF.map_range_numerator_eq_filter_numerators`: the numerator of a bit
  lies in an interval exactly when the bit lies between its bits, and the numerators of the bits of
  `-H, …, H` are those of `-H, …, H` in the class of the packing, in increasing order.
* `Ratpoints.Sieve.SieveEntry.PackedFor.lt_two_pow_32`: the offsets of the rows are below
  `2 ^ 32`, so `long`s.
* `Ratpoints.Sieve.neg_two_pow_le_rbaLength_mul_ediv`,
  `Ratpoints.Sieve.rbaLength_mul_ediv_add_one_le_two_pow`: the first bit of the bit array of a bit
  `lo ≥ -2 ^ (63 - k)` and the bit after the bit array of a bit `hi < 2 ^ (63 - k)` lie in
  `[-2 ^ (63 - k), 2 ^ (63 - k)]`, for `k ≤ 6`.
* `Ratpoints.Sieve.NumClass.fitsLong_numerator`: the numerators of the bits of the bit arrays of
  `-H, …, H` are `long`s.
* `Ratpoints.Sieve.fitsLong_neg_sub_and_fitsLong_add`: the values `-w_low - offset` and
  `i + offset` that the first two stages reduce by the helper `mod` are `long`s.
* `Ratpoints.Sieve.flatMap_flatMap_filter_eq_flatMap_filter_inRanges`: for ranges that increase and
  are strictly apart, the points of the elements of an increasing list, range after range, are those
  of the elements in one of the ranges.

## Implementation notes

The file uses Lean core and `Std` only, so that the contracts of the sieve, in files without
Mathlib, can use it. The proofs use only the facts on the constants that `decide` checks next to
them, never their values: that `Ratpoints.rbaLength = 2 ^ Ratpoints.rbaShift` with
`Ratpoints.rbaShift < 32`, that `Ratpoints.rbaPack > 0`, that `Ratpoints.maxBitsInPrime ≤ 10` and
that `2 Ratpoints.rowBias - 1 ≤ Ratpoints.mulModLimit < 2 ^ 32`; the facts on words that are not
about the model are in `Ratpoints.Proof.Bits`, those on natural numbers and integers in
`Ratpoints.Proof.Containers`.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The bits of the numerators -/

theorem toInt_numeratorsToBits_false {low high : Int64} {cl : NumClass} (hcl : cl.WF)
    (h1 : cl.a0 - low.toInt < 2 ^ 63) (h2 : -2 ^ 63 ≤ high.toInt - cl.a0) :
    (numeratorsToBits low high cl false).1.toInt = -((cl.a0 - low.toInt) / 2 ^ cl.k) ∧
      (numeratorsToBits low high cl false).2.toInt = (high.toInt - cl.a0) / 2 ^ cl.k := by
  have ha : cl.a0 < 2 ^ 63 := Nat.lt_trans hcl.a0_lt_sixty_four (by decide)
  have hk : cl.k < 64 := by lia [hcl.k_le]
  have hm : (0 : Int) < 2 ^ cl.k := Int.pow_pos (by decide)
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
    exact Int.lt_ediv_of_neg (by decide) (by lia) hm

-- The facts on the stride `m = 2 ^ k`, `k ≤ 6`, and the residue `a₀ < m` of a class that the split
-- form of `numerators_to_bits` needs: `1 ≤ m ≤ 64`, `a₀ < m`, and the words of `a₀` and of `m - 1`.
private theorem stride_facts {k a0 : Nat} (hk : k ≤ 6) (ha : a0 < 2 ^ k) :
    (1 : Int) ≤ 2 ^ k ∧ (2 : Int) ^ k ≤ 64 ∧ (a0 : Int) < 2 ^ k ∧
      (Int64.ofNat a0).toInt = a0 ∧ (Int64.ofNat (2 ^ k - 1)).toInt = 2 ^ k - 1 := by
  have h64 : 2 ^ k ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hk
  have := Nat.one_le_two_pow (n := k)
  refine ⟨mod_cast this, mod_cast h64, mod_cast ha, Int64.toInt_ofNat_of_lt (by lia),
    Int64.toInt_ofNat_two_pow_sub_one (by lia)⟩

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
  have e2 : ((x &&& Int64.ofNat (2 ^ k - 1)) - Int64.ofNat a0).toInt = x.toInt % 2 ^ k - a0 := by
    rw [Int64.toInt_sub_of_lt] <;> lia [Int64.toInt_and_ofNat_two_pow_sub_one x (by lia : k < 63)]
  have e3 : ((x &&& Int64.ofNat (2 ^ k - 1)) - Int64.ofNat a0 + Int64.ofNat (2 ^ k - 1)).toInt =
      x.toInt % 2 ^ k - a0 + (2 ^ k - 1) := by
    rw [Int64.toInt_add_of_lt] <;> lia
  have hc := Int.sub_add_sub_one_ediv_nonneg_and_le_one hl0 hl (Int.natCast_nonneg a0) ha'
  have hb := Int.neg_two_pow_63_le_ediv_add_and_ediv_add_lt_two_pow_63 x.le_toInt x.toInt_lt hm
    (by lia) hc.2 fun h ↦ by
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
  have f2 : ((x &&& Int64.ofNat (2 ^ k - 1)) - Int64.ofNat a0).toInt = x.toInt % 2 ^ k - a0 := by
    rw [Int64.toInt_sub_of_lt] <;> lia [Int64.toInt_and_ofNat_two_pow_sub_one x (by lia : k < 63)]
  have hc := Int.neg_one_le_sub_ediv_and_sub_ediv_nonpos hh0 hh (Int.natCast_nonneg a0) ha'
  have hb := Int.neg_two_pow_63_le_ediv_add_and_ediv_add_lt_two_pow_63 x.le_toInt x.toInt_lt hm
    hc.1 (by lia) fun h ↦ by
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
  have hl : (-H.toInt64).toInt = -H := Int64.toInt_neg_ofNat_of_le (by lia)
  have hh : H.toInt64.toInt = H := Int64.toInt_ofNat_of_lt hH
  have := toInt_numeratorsToBits hcl (low := -H.toInt64) (high := H.toInt64)
    (split := decide (2 ^ 63 - 65 < H)) fun h ↦ by
      simp only [decide_eq_false_iff_not, Nat.not_lt] at h
      rw [hl, hh]
      constructor <;> lia [hcl.a0_lt_sixty_four]
  rwa [hl, hh, Int.sub_neg] at this

/-- The numerator of bit `t` of a class lies in `lo, …, hi` exactly when `t` lies between the bits
of `numerators_to_bits` (`Ratpoints.Sieve.toInt_numeratorsToBits`). -/
theorem NumClass.le_numerator_and_numerator_le_iff (cl : NumClass) (lo hi t : Int) :
    (lo ≤ cl.numerator t ∧ cl.numerator t ≤ hi) ↔
      (-((cl.a0 - lo) / 2 ^ cl.k) ≤ t ∧ t ≤ (hi - cl.a0) / 2 ^ cl.k) := by
  have hk : (0 : Int) < 2 ^ cl.k := Int.pow_pos (by decide)
  rw [numerator, Int.neg_le_iff, Int.le_ediv_iff_mul_le hk, Int.le_ediv_iff_mul_le hk]
  constructor <;> intro h <;> constructor <;> lia

/-- The bits from `⌈(lo - a₀) / 2 ^ k⌉` to `⌊(hi - a₀) / 2 ^ k⌋` of the packing of a class, for
`-H ≤ lo` and `hi ≤ H`, are those of the numerators `-H, …, H`
(`Ratpoints.Sieve.toInt_numeratorsToBits_height`) whose numerators lie in `lo, …, hi`
(`Ratpoints.Sieve.NumClass.le_numerator_and_numerator_le_iff`). -/
theorem NumClass.map_range_eq_filter_map_range (cl : NumClass) {H : Nat} {lo hi : Int}
    (hlo : -(H : Int) ≤ lo) (hhi : hi ≤ H) :
    (List.range ((hi - cl.a0) / 2 ^ cl.k + 1 - -((cl.a0 - lo) / 2 ^ cl.k)).toNat).map
        (fun i : Nat ↦ -((cl.a0 - lo) / 2 ^ cl.k) + i) =
      ((List.range (((H : Int) - cl.a0) / 2 ^ cl.k + 1 -
        -((cl.a0 + H : Int) / 2 ^ cl.k)).toNat).map
          fun i : Nat ↦ -((cl.a0 + H : Int) / 2 ^ cl.k) + i).filter
        fun j ↦ decide (lo ≤ cl.numerator j ∧ cl.numerator j ≤ hi) := by
  have hm : (0 : Int) < 2 ^ cl.k := Int.pow_pos (by decide)
  have h1 : (cl.a0 - lo) / 2 ^ cl.k ≤ (cl.a0 + H : Int) / 2 ^ cl.k := Int.ediv_le_ediv hm (by lia)
  have h2 : (hi - cl.a0) / 2 ^ cl.k ≤ ((H : Int) - cl.a0) / 2 ^ cl.k :=
    Int.ediv_le_ediv hm (by lia)
  rw [List.filter_congr fun j _ ↦
      decide_eq_decide.mpr (cl.le_numerator_and_numerator_le_iff lo hi j),
    List.filter_map_range_eq_map_range_of_le (by lia) (by lia)]

end Sieve

namespace BruteForce

/-- The numerators of `-H, …, H` that are `a₀` modulo `m`, for `a₀ < m`, in increasing order:
`r - H, r + m - H, …`, for the residue `r` of `a₀ + H` modulo `m`. -/
theorem filter_numerators_emod_eq {a0 m : Nat} (ha : a0 < m) (H : Nat) :
    (numerators H).filter (fun a ↦ a % (m : Int) == (a0 : Int)) =
      (List.range ((2 * H + 1 + (m - 1 - (a0 + H) % m)) / m)).map
        fun j : Nat ↦ ((a0 : Int) + H) % m + m * j - H := by
  simp only [numerators, List.filter_map]
  rw [List.filter_congr (q := fun i ↦ i % m == (a0 + H) % m) fun i _ ↦ by
    rw [Function.comp_apply, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq]
    exact_mod_cast Int.natCast_sub_natCast_emod_eq_iff ha,
    List.filter_range_mod_eq (Nat.mod_lt _ (by lia)), List.map_map]
  simp

end BruteForce

namespace Sieve

-- The numerators `a₀ + m (lo + i)` of the bits from `lo = -q` to `hi = ⌊(H - a₀) / m⌋`, for
-- `a₀ + H = m q + r` with `r < m`, are `r - H, r + m - H, …`, as many as there are numerators of
-- `-H, …, H` that are `r - H` modulo `m`.
private theorem map_range_eq_map_range {a0 H m q r : Nat} (hm : 0 < m) (hr : r < m)
    (hA : m * q + r = a0 + H) :
    (List.range (((H : Int) - a0) / m + 1 - -(q : Int)).toNat).map
        (fun i : Nat ↦ (a0 : Int) + m * (-(q : Int) + i)) =
      (List.range ((2 * H + 1 + (m - 1 - r)) / m)).map fun j : Nat ↦ (r : Int) + m * j - H := by
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
  lia

/-- The numerators of `-H, …, H` that are `a₀` modulo the stride `2 ^ k` of a class, in increasing
order, are those of the bits from `lo = ⌈(-H - a₀) / 2 ^ k⌉` to `hi = ⌊(H - a₀) / 2 ^ k⌋`. -/
theorem NumClass.WF.map_range_numerator_eq_filter_numerators {cl : NumClass} (hcl : cl.WF)
    {H : Nat} {lo hi : Int} (hlo : lo = -((cl.a0 + H : Int) / 2 ^ cl.k))
    (hhi : hi = ((H : Int) - cl.a0) / 2 ^ cl.k) :
    (List.range (hi + 1 - lo).toNat).map (fun i : Nat ↦ cl.numerator (lo + i)) =
      (BruteForce.numerators H).filter fun a ↦ a % 2 ^ cl.k == (cl.a0 : Int) := by
  have hk : (2 : Int) ^ cl.k = ((2 ^ cl.k : Nat) : Int) := by push_cast; rfl
  rw [hk, BruteForce.filter_numerators_emod_eq hcl.a0_lt H]
  simp only [numerator, hlo, hhi, hk]
  have := map_range_eq_map_range (r := (cl.a0 + H) % 2 ^ cl.k) (Nat.two_pow_pos _)
    (Nat.mod_lt _ (Nat.two_pow_pos _)) (Nat.div_add_mod _ _)
  rwa [Int.natCast_emod, Int.natCast_add] at this

/-! ### The longs of the offsets and of the bit ranges -/

/-- The offsets of the rows are below `Ratpoints.rowBias + 2 p ≤ 2 ^ 31 + 2 ^ 11 < 2 ^ 32`, so
`long`s, and in the range that `Ratpoints.Sieve.fitsLong_neg_sub_and_fitsLong_add` takes. -/
theorem SieveEntry.PackedFor.lt_two_pow_32 {e : SieveEntry} {cl : NumClass} {off : Nat}
    (h : e.PackedFor cl off) : off < 2 ^ 32 := by
  have := h.lt_rowBias_add
  have := Nat.le_trans h.le_maxPrimeEven maxPrimeEven_le_two_pow_10
  have := rowBias_le_two_pow_31
  generalize rowBias = R at *
  lia

/-- The width `Ratpoints.rbaLength = 2 ^ Ratpoints.rbaShift` of the bit arrays divides `2 ^ n` for
`n ≥ Ratpoints.rbaShift`. -/
theorem natCast_rbaLength_dvd_two_pow {n : Nat} (hn : rbaShift ≤ n) : (rbaLength : Int) ∣ 2 ^ n :=
  rbaLength_eq_two_pow_rbaShift ▸ mod_cast Nat.pow_dvd_pow 2 hn

/-- The first bit `Ratpoints.rbaLength ⌊lo / Ratpoints.rbaLength⌋` of the bit array of the bit
`lo ≥ -2 ^ (63 - k)` is at least `-2 ^ (63 - k)`, for a stride `2 ^ k`, `k ≤ 6`, since
`Ratpoints.rbaLength` divides `2 ^ (63 - k)`. -/
theorem neg_two_pow_le_rbaLength_mul_ediv {k : Nat} (hk : k ≤ 6) {lo : Int}
    (hlo : -2 ^ (63 - k) ≤ lo) : -2 ^ (63 - k) ≤ rbaLength * (lo / rbaLength) :=
  Int.neg_le_mul_ediv_of_dvd natCast_rbaLength_pos
    (natCast_rbaLength_dvd_two_pow (by lia [rbaShift_lt_thirty_two])) hlo

/-- The bit `Ratpoints.rbaLength (⌊hi / Ratpoints.rbaLength⌋ + 1)` after the bit array of the bit
`hi < 2 ^ (63 - k)` is at most `2 ^ (63 - k)`, for a stride `2 ^ k`, `k ≤ 6`, since
`Ratpoints.rbaLength` divides `2 ^ (63 - k)`. -/
theorem rbaLength_mul_ediv_add_one_le_two_pow {k : Nat} (hk : k ≤ 6) {hi : Int}
    (hhi : hi < 2 ^ (63 - k)) : rbaLength * (hi / rbaLength + 1) ≤ 2 ^ (63 - k) :=
  Int.mul_ediv_add_one_le_of_dvd natCast_rbaLength_pos
    (natCast_rbaLength_dvd_two_pow (by lia [rbaShift_lt_thirty_two])) hhi

/-- The numerators of the bits of the bit arrays from `⌊lo / Ratpoints.rbaLength⌋` to
`⌊hi / Ratpoints.rbaLength⌋`, for the bits `lo, hi` of the numerators `-H, …, H` of a height bound
`H < 2 ^ 63` in the packing of a class (`Ratpoints.Sieve.toInt_numeratorsToBits_height`), are
`long`s: the extraction computes them, and the first numerators of the words, as `long`s. -/
theorem NumClass.fitsLong_numerator {cl : NumClass} (hcl : cl.WF) {H : Nat} (hH : H < 2 ^ 63)
    {j : Int} (hj : rbaLength * (-((cl.a0 + H : Int) / 2 ^ cl.k) / rbaLength) ≤ j)
    (hj' : j < rbaLength * (((H : Int) - cl.a0) / 2 ^ cl.k / rbaLength + 1)) :
    fitsLong (cl.numerator j) = true := by
  have hm : (0 : Int) < 2 ^ cl.k := Int.pow_pos (by decide)
  have hkT : (2 : Int) ^ cl.k * 2 ^ (63 - cl.k) = 2 ^ 63 :=
    Int.pow_mul_pow_sub 2 (by lia [hcl.k_le])
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
  · constructor <;> constructor <;> lia [Int.mul_le_mul_of_nonpos_right hR (Int.le_of_lt h)]
  · constructor <;> constructor <;> lia [Int.mul_le_mul_of_nonneg_right hR h]

/-! ### The numerator ranges of the search intervals -/

/-- The bounds `bd` of a search interval give, for the denominator `b` and the height bound `H`, the
range of the numerators `lo, …, hi` (empty when `hi < lo`), as `Ratpoints.Sieve.intervalBits`
reads them for every class with `k ≤ 6` and `a₀ < 2 ^ k` (`Ratpoints.Sieve.NumClass.WF`): the code
`2` only when the range lies above `H`, the code `1` only when it lies below `-H`, and otherwise the
bits of the numerators from `max lo (-H)` to `min hi H` in the packing of the class
(`Ratpoints.Sieve.toInt_numeratorsToBits`). For the bounds of a search interval `[l, u]` and a
denominator up to the largest one, `lo = ⌈b l⌉` and `hi = ⌊b u⌋`. -/
structure IntervalBounds.Represents (bd : IntervalBounds) (b H : Nat) (lo hi : Int) : Prop where
  /-- The code `2` only for a range above `H`. -/
  two : ∀ cl : NumClass, cl.WF → (intervalBits b.toInt64 bd H.toInt64 cl).1 = 2 → (H : Int) < lo
  /-- The code `1` only for a range below `-H`. -/
  one : ∀ cl : NumClass, cl.WF → (intervalBits b.toInt64 bd H.toInt64 cl).1 = 1 → hi < -H
  /-- Otherwise the bits of the numerators of the range within `-H, …, H`. -/
  bits : ∀ cl : NumClass, cl.WF → (intervalBits b.toInt64 bd H.toInt64 cl).1 ≠ 1 →
    (intervalBits b.toInt64 bd H.toInt64 cl).1 ≠ 2 →
    (intervalBits b.toInt64 bd H.toInt64 cl).2.1.toInt = -((cl.a0 - max lo (-H)) / 2 ^ cl.k) ∧
      (intervalBits b.toInt64 bd H.toInt64 cl).2.2.toInt = (min hi H - cl.a0) / 2 ^ cl.k

/-- The bounds `iv` of the search intervals of a run give, for the denominator `b` and the height
bound `H`, the ranges of the numerators `rs`, one for each interval in turn
(`Ratpoints.Sieve.IntervalBounds.Represents`), each with `lo ≤ hi + 1`, increasing and strictly
apart: what the loop of `Ratpoints.Sieve.sift` over the intervals needs, which returns at the first
interval above `H`. -/
structure RangesFor (iv : Array IntervalBounds) (b H : Nat) (rs : List (Int × Int)) : Prop where
  /-- One range for each interval. -/
  length_eq : iv.size = rs.length
  /-- Each interval gives its range. -/
  represents : ∀ p ∈ iv.toList.zip rs, p.1.Represents b H p.2.1 p.2.2
  /-- Each range is empty at most by one. -/
  le_add_one : ∀ r ∈ rs, r.1 ≤ r.2 + 1
  /-- The ranges are increasing and strictly apart. -/
  pairwise : rs.Pairwise fun r s ↦ r.2 < s.1

/-- Whether the integer `a` lies in one of the ranges `lo, …, hi` of `rs`. -/
def inRanges (rs : List (Int × Int)) (a : Int) : Bool :=
  rs.any fun r ↦ decide (r.1 ≤ a ∧ a ≤ r.2)

/-- The bounds `cur` of a search interval at the position `pref.length` of the array `iv` give the
range of the numerators at that position of the ranges `rs` of `iv`. -/
theorem RangesFor.represents_of_eq_append_cons {iv : Array IntervalBounds} {b H : Nat}
    {rs : List (Int × Int)} (h : RangesFor iv b H rs) {pref suff : List IntervalBounds}
    {cur : IntervalBounds} (hl : ForIn.toList iv = pref ++ cur :: suff) :
    ∃ hk : pref.length < rs.length, cur.Represents b H rs[pref.length].1 rs[pref.length].2 := by
  rw [Std.Internal.ForIn.toList_array] at hl
  have hk : pref.length < rs.length := by
    rw [← h.length_eq, ← Array.length_toList, hl]
    simp
  have hz : pref.length < (iv.toList.zip rs).length := by simp [h.length_eq, hk]
  refine ⟨hk, ?_⟩
  simpa [List.getElem_zip, hl] using h.represents _ (List.getElem_mem hz)

/-- The ranges of the search intervals from the position `k` on lie above a number `x` below the
first numerator of the range at `k`: they are increasing and strictly apart, and each is empty at
most by one. -/
theorem RangesFor.lt_fst_of_mem_drop {iv : Array IntervalBounds} {b H : Nat}
    {rs : List (Int × Int)} (h : RangesFor iv b H rs) {k : Nat} (hk : k < rs.length) {x : Int}
    (hx : x < rs[k].1) : ∀ rg ∈ rs.drop k, x < rg.1 := by
  intro rg hrg
  have hp := h.pairwise.sublist (List.drop_sublist k rs)
  rw [List.drop_eq_getElem_cons hk, List.pairwise_cons] at hp
  rw [List.drop_eq_getElem_cons hk] at hrg
  rcases List.mem_cons.mp hrg with rfl | hrg
  · exact hx
  · lia [hp.1 rg hrg, h.le_add_one _ (List.getElem_mem hk)]

/-- The points of the elements of an increasing list `l` in each of the ranges `rs`, which are
increasing and strictly apart, that pass `q`, range after range, are those of the elements of `l`
in one of the ranges (`Ratpoints.Sieve.inRanges`) that pass `q`
(`List.flatMap_filter_eq_filter_any`). -/
theorem flatMap_flatMap_filter_eq_flatMap_filter_inRanges {l : List Int}
    (hl : l.Pairwise (· < ·)) {rs : List (Int × Int)} (hrs : rs.Pairwise fun r s ↦ r.2 < s.1)
    (q : Int → Bool) (g : Int → List (Int × Int × Int)) :
    (rs.flatMap fun rg ↦ (l.filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g) =
      (l.filter fun a ↦ inRanges rs a && q a).flatMap g := by
  rw [← List.flatMap_assoc, List.flatMap_filter_eq_filter_any hl hrs]
  rfl

end Sieve

end Ratpoints

end
