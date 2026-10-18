/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Rat.Floor
public import Ratpoints.Proof.BitRange
public import Ratpoints.Spec.Region

import Ratpoints.Mathlib.Data.List.Pairwise

/-!
# The search region in the proofs

The search intervals of the model, pairs of doubles (`Ratpoints.Double`), over the values of their
ends (`Ratpoints.domainValues`) and their bits (`Ratpoints.domainBits`); a rational number in one of
a list of intervals over values (`Ratpoints.InIntervals`); and the ranges of the numerators of a
denominator `b` that a list of intervals gives within `-H, …, H`
(`Ratpoints.Sieve.numeratorRanges`), with the ends `⌈b l⌉` and `⌊b u⌋` clamped, which the bounds of
the search intervals of a run give to the sieve of one denominator (`Ratpoints.Sieve.RangesFor`).

## Main definitions

* `Ratpoints.domainValues`, `Ratpoints.domainBits`: the values and the bits of the ends of the
  search intervals of the model.
* `Ratpoints.InIntervals`: a rational number in one of a list of intervals.
* `Ratpoints.Sieve.lowNumerator`, `Ratpoints.Sieve.highNumerator`,
  `Ratpoints.Sieve.numeratorRanges`: the ranges of the numerators of a denominator in a list of
  intervals.

## Main statements

* `Ratpoints.Sieve.inRanges_numeratorRanges`: a numerator `|a| ≤ H` lies in one of the ranges
  exactly when `a / b` lies in one of the intervals.
* `Ratpoints.Sieve.pairwise_numeratorRanges`, `Ratpoints.Sieve.le_add_one_of_mem_numeratorRanges`:
  the ranges of search intervals are increasing and strictly apart, each empty at most by one.
-/

@[expose] public section

namespace Ratpoints

/-- The values of the ends of the search intervals `dom` of the model (`Ratpoints.doubleValue`). -/
abbrev domainValues (dom : List (Double × Double)) : List (WithBotTop ℚ × WithBotTop ℚ) :=
  dom.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)

/-- The bits of the ends of the search intervals `dom` of the model. -/
abbrev domainBits (dom : List (Double × Double)) : List (UInt64 × UInt64) :=
  dom.map fun i ↦ (i.1.bits, i.2.bits)

/-- The rational number `x` lies in one of the intervals `D`, over the values of their ends. -/
def InIntervals (D : List (WithBotTop ℚ × WithBotTop ℚ)) (x : ℚ) : Prop :=
  ∃ i ∈ D, i.1 ≤ (x : WithBotTop ℚ) ∧ (x : WithBotTop ℚ) ≤ i.2

instance instDecidablePredInIntervals (D : List (WithBotTop ℚ × WithBotTop ℚ)) :
    DecidablePred (InIntervals D) :=
  fun _ ↦ inferInstanceAs (Decidable (∃ _ ∈ D, _))

namespace Sieve

/-- The least numerator of the denominator `b` in an interval with the lower end `x`, within
`-H, …, H + 1`: `⌈b x⌉` clamped, `-H` for `x = ⊥` and `H + 1` for `x = ⊤`. -/
def lowNumerator (b H : ℕ) (x : WithBotTop ℚ) : ℤ :=
  WithBotTop.rec (motive := fun _ ↦ ℤ) (-H) (fun q ↦ max (-H) (min ⌈(b : ℚ) * q⌉ (H + 1)))
    (H + 1) x

/-- The largest numerator of the denominator `b` in an interval with the upper end `x`, within
`-H - 1, …, H`: `⌊b x⌋` clamped, `-H - 1` for `x = ⊥` and `H` for `x = ⊤`. -/
def highNumerator (b H : ℕ) (x : WithBotTop ℚ) : ℤ :=
  WithBotTop.rec (motive := fun _ ↦ ℤ) (-H - 1) (fun q ↦ max (-H - 1) (min ⌊(b : ℚ) * q⌋ H)) H x

/-- The ranges of the numerators of the denominator `b` in the intervals `D`, within `-H, …, H`
but for the clamps: an integer `|a| ≤ H` lies in the range of an interval exactly when `a / b`
lies in the interval (`Ratpoints.Sieve.inRanges_numeratorRanges`). -/
def numeratorRanges (b H : ℕ) (D : List (WithBotTop ℚ × WithBotTop ℚ)) : List (ℤ × ℤ) :=
  D.map fun i ↦ (lowNumerator b H i.1, highNumerator b H i.2)

theorem lowNumerator_le_iff {b H : ℕ} (hb : 0 < b) {a : ℤ} (ha : a.natAbs ≤ H)
    (x : WithBotTop ℚ) : lowNumerator b H x ≤ a ↔ x ≤ (((a : ℚ) / b : ℚ) : WithBotTop ℚ) := by
  induction x using WithBotTop.rec with
  | bot => simp only [lowNumerator, WithBotTop.rec_bot, bot_le, iff_true]; lia
  | top => simp only [lowNumerator, WithBotTop.rec_top, top_le_iff, WithBotTop.coe_ne_top,
      iff_false, not_le]; lia
  | coe q =>
    simp only [lowNumerator, WithBotTop.rec_coe, WithBotTop.coe_le_coe]
    rw [le_div_iff₀ (mod_cast hb), mul_comm, ← Int.ceil_le]
    constructor <;> intro h <;> lia

theorem le_highNumerator_iff {b H : ℕ} (hb : 0 < b) {a : ℤ} (ha : a.natAbs ≤ H)
    (x : WithBotTop ℚ) : a ≤ highNumerator b H x ↔ (((a : ℚ) / b : ℚ) : WithBotTop ℚ) ≤ x := by
  induction x using WithBotTop.rec with
  | bot => simp only [highNumerator, WithBotTop.rec_bot, le_bot_iff, WithBotTop.coe_ne_bot,
      iff_false, not_le]; lia
  | top => simp only [highNumerator, WithBotTop.rec_top, le_top, iff_true]; lia
  | coe q =>
    simp only [highNumerator, WithBotTop.rec_coe, WithBotTop.coe_le_coe]
    rw [div_le_iff₀ (mod_cast hb), mul_comm, ← Int.le_floor]
    constructor <;> intro h <;> lia

theorem inRanges_numeratorRanges {b H : ℕ} (hb : 0 < b) {a : ℤ} (ha : a.natAbs ≤ H)
    (D : List (WithBotTop ℚ × WithBotTop ℚ)) :
    inRanges (numeratorRanges b H D) a = decide (InIntervals D (a / b)) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  simp only [inRanges, numeratorRanges, List.any_map, List.any_eq_true, Function.comp_apply,
    decide_eq_true_eq, InIntervals]
  exact exists_congr fun i ↦ and_congr_right fun _ ↦
    and_congr (lowNumerator_le_iff hb ha _) (le_highNumerator_iff hb ha _)

theorem neg_le_lowNumerator (b H : ℕ) (x : WithBotTop ℚ) : -(H : ℤ) ≤ lowNumerator b H x := by
  induction x using WithBotTop.rec <;>
    simp only [lowNumerator, WithBotTop.rec_bot, WithBotTop.rec_top, WithBotTop.rec_coe] <;> lia

theorem lowNumerator_le (b H : ℕ) (x : WithBotTop ℚ) : lowNumerator b H x ≤ H + 1 := by
  induction x using WithBotTop.rec <;>
    simp only [lowNumerator, WithBotTop.rec_bot, WithBotTop.rec_top, WithBotTop.rec_coe] <;> lia

theorem neg_sub_one_le_highNumerator (b H : ℕ) (x : WithBotTop ℚ) :
    -(H : ℤ) - 1 ≤ highNumerator b H x := by
  induction x using WithBotTop.rec <;>
    simp only [highNumerator, WithBotTop.rec_bot, WithBotTop.rec_top, WithBotTop.rec_coe] <;> lia

theorem highNumerator_le (b H : ℕ) (x : WithBotTop ℚ) : highNumerator b H x ≤ H := by
  induction x using WithBotTop.rec <;>
    simp only [highNumerator, WithBotTop.rec_bot, WithBotTop.rec_top, WithBotTop.rec_coe] <;> lia

/-- The range of an interval `[l, u]` with `l ≤ u` is empty at most by one: `⌈b l⌉ ≤ ⌊b u⌋ + 1`,
and the clamps keep it. -/
theorem lowNumerator_le_highNumerator_add_one {l u : WithBotTop ℚ} (h : l ≤ u) (b H : ℕ) :
    lowNumerator b H l ≤ highNumerator b H u + 1 := by
  have h1 := neg_sub_one_le_highNumerator b H u
  have h2 := lowNumerator_le b H l
  induction l using WithBotTop.rec with
  | bot => simp only [lowNumerator, WithBotTop.rec_bot]; lia
  | top => rw [top_le_iff.mp h]; simp [lowNumerator, highNumerator]
  | coe p =>
    induction u using WithBotTop.rec with
    | bot => exact absurd h (by simp)
    | top => simp only [highNumerator, WithBotTop.rec_top]; lia
    | coe q =>
      have hpq : (b : ℚ) * p ≤ b * q := mul_le_mul_of_nonneg_left (WithBotTop.coe_le_coe.mp h)
        (Nat.cast_nonneg _)
      have := (Int.ceil_le_ceil hpq).trans (Int.ceil_le_floor_add_one ((b : ℚ) * q))
      simp only [lowNumerator, highNumerator, WithBotTop.rec_coe]
      lia

/-- The range of an interval ending below the start of another ends below the start of its range:
`⌊b u⌋ < ⌈b l⌉` for `u < l`, and the clamps keep it. -/
theorem highNumerator_lt_lowNumerator {u l : WithBotTop ℚ} (h : u < l) {b : ℕ} (hb : 0 < b)
    (H : ℕ) : highNumerator b H u < lowNumerator b H l := by
  have h1 := neg_le_lowNumerator b H l
  have h2 := highNumerator_le b H u
  induction u using WithBotTop.rec with
  | bot => simp only [highNumerator, WithBotTop.rec_bot]; lia
  | top => exact absurd h (by simp)
  | coe p =>
    induction l using WithBotTop.rec with
    | bot => exact absurd h (by simp)
    | top => simp only [lowNumerator, WithBotTop.rec_top]; lia
    | coe q =>
      have hpq : (b : ℚ) * p < b * q := mul_lt_mul_of_pos_left (WithBotTop.coe_lt_coe.mp h)
        (mod_cast hb)
      have : ⌊(b : ℚ) * p⌋ < ⌈(b : ℚ) * q⌉ := Int.cast_lt.mp
        ((Int.floor_le _).trans_lt (hpq.trans_le (Int.le_ceil _)))
      simp only [lowNumerator, highNumerator, WithBotTop.rec_coe]
      lia

theorem le_add_one_of_mem_numeratorRanges {D : List (WithBotTop ℚ × WithBotTop ℚ)}
    (hD : ∀ i ∈ D, i.1 ≤ i.2) (b H : ℕ) : ∀ r ∈ numeratorRanges b H D, r.1 ≤ r.2 + 1 := by
  simp only [numeratorRanges, List.mem_map]
  rintro _ ⟨i, hi, rfl⟩
  exact lowNumerator_le_highNumerator_add_one (hD i hi) b H

theorem pairwise_numeratorRanges {D : List (WithBotTop ℚ × WithBotTop ℚ)}
    (hD : AreSearchIntervals D) {b : ℕ} (hb : 0 < b) (H : ℕ) :
    (numeratorRanges b H D).Pairwise fun r s ↦ r.2 < s.1 :=
  List.pairwise_map.mpr ((List.pairwise_of_isChain_of_le hD.1 hD.2).imp
    fun h ↦ highNumerator_lt_lowNumerator h hb H)

end Sieve

end Ratpoints

end
