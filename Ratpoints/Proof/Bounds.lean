/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.FindPoints
public import Ratpoints.Proof.Region

import Mathlib.Data.Nat.Cast.Field
import Ratpoints.Mathlib.Algebra.Order.Field.Basic
import Ratpoints.Mathlib.Data.Rat.Floor
import Ratpoints.Proof.Bits
import Ratpoints.Proof.Rounding

/-!
# The bounds of the search intervals

What the library makes of the search intervals of the caller before the Sturm step
(`Ratpoints.searchIntervals`): it refuses them exactly when the specification says
(`Ratpoints.IntervalsWF`), keeps them as they are, and for none takes the default interval
`[-h, h]`, which holds `a / b` for every numerator `|a| ≤ H` and every denominator `b ≥ 1`; and the
bounds of the search intervals of a run (`Ratpoints.Sieve.exactBounds`), which give, for each
denominator up to the largest, the ranges of the numerators `⌈b l⌉, …, ⌊b u⌋` of the intervals
(`Ratpoints.Sieve.numeratorRanges`, `Ratpoints.Sieve.RangesFor`) to the sieve of one denominator.

The ends of the bounds are those of `exact_end`: `±m 2 ^ (-s)` with the value of the double, or
capped for a tiny end or one beyond `2 ^ 63`, with the same numerators for every denominator
`1 ≤ b < 2 ^ 63` (`Ratpoints.Sieve.lowNumerator_eq_and_highNumerator_eq_run_exactEnd`);
`exact_scale` computes `min (2 ^ 64 - 1) ⌊(b m + r) / 2 ^ s⌋` on two words
(`Ratpoints.Sieve.toNat_exactScale`), so that `interval_bits_exact` gives the clamped numerators of
the ends (`Ratpoints.Sieve.toInt_intervalBitsExact`); and the forms `(b M + C) >> s` of `end_form`
are exact on the `long`s (`Ratpoints.Sieve.lowNumerator_of_endForm`,
`Ratpoints.Sieve.highNumerator_of_endForm`), so that `interval_bits` on an interval taken inline
gives them too (`Ratpoints.Sieve.IntervalBounds.represents_of_fast`).

## Main definitions

* `Ratpoints.Sieve.IsExactMantissa`, `Ratpoints.Sieve.IsEnd`, `Ratpoints.Sieve.ExactEnd.value`: the
  mantissa and the ends that `exact_end` makes, and the value of an end.
* `Ratpoints.Sieve.intervalBoundsOf`: the bounds of one search interval, the body of the loop of
  `Ratpoints.Sieve.exactBounds`.

## Main statements

* `Ratpoints.run_searchIntervals_eq_none_iff`: the refusal of the search intervals is the negation
  of `Ratpoints.IntervalsWF`.
* `Ratpoints.run_searchIntervals_of_ne_nil`, `Ratpoints.exists_run_searchIntervals_nil`: the search
  intervals of the caller, or the default interval, which holds every `a / b` of the search.
* `Ratpoints.Sieve.toNat_exactScale`,
  `Ratpoints.Sieve.lowNumerator_eq_and_highNumerator_eq_run_exactEnd`: `exact_scale` and the ends of
  `exact_end`.
* `Ratpoints.Sieve.represents_intervalBoundsOf`: the bounds of one search interval give the range of
  its numerators, on both paths of `interval_bits`.
* `Ratpoints.Sieve.rangesFor_run_exactBounds`: the bounds of the search intervals give the ranges
  of the numerators of every denominator up to the largest.
-/

@[expose] public section

namespace Ratpoints

-- A loop over a list that stops with `some r` at the first element satisfying `p`.
private theorem forIn_list_done_eq {α β : Type} (l : List α) (p : α → Bool) (r : β) :
    (forIn (m := Id) l ((none : Option β), ()) fun a _ ↦
      if p a = true then pure (ForInStep.done (some r, ()))
      else pure (ForInStep.yield (none, ()))) =
      pure (if l.any p then some r else none, ()) := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [List.forIn_cons]
    by_cases h : p a = true
    · simp [h]
    · simp [h, ih]

theorem run_searchIntervals_eq {H : ℕ} {domain : List (Double × Double)} (h : domain ≠ []) :
    Id.run (searchIntervals H domain) = if (List.range domain.length).any (fun n ↦
      !domain[n]!.1.le domain[n]!.2 || decide (0 < n) && !domain[n - 1]!.2.lt domain[n]!.1)
      then none else some domain := by
  simp only [searchIntervals, List.isEmpty_iff, h, ↓reduceIte,
    Std.Legacy.Range.forIn_eq_forIn_range', List.size_toArray, List.getElem!_toArray]
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
    ← List.range_eq_range']
  rw [forIn_list_done_eq]
  split <;> rfl

theorem intervalsWF_domainBits_iff_getElem (domain : List (Double × Double)) :
    IntervalsWF (domainBits domain) ↔ ∀ n (hn : n < domain.length),
      domain[n].1.le domain[n].2 = true ∧
        (∀ h : 0 < n, domain[n - 1].2.lt domain[n].1 = true) := by
  simp only [IntervalsWF, AreSearchIntervals, List.isChain_iff_getElem, Double.le_eq_true_iff',
    Double.lt_eq_true_iff', domainBits, List.map_map, List.forall_mem_iff_getElem,
    List.getElem_map, List.length_map, Function.comp_apply]
  constructor
  · intro ⟨h1, h2, h3⟩ n hn
    refine ⟨⟨(h1 n hn).1, (h1 n hn).2, h2 n hn⟩, fun h ↦ ?_⟩
    have := h3 (n - 1) (by lia)
    simp only [show n - 1 + 1 = n by lia] at this
    exact ⟨(h1 (n - 1) (by lia)).2, (h1 n hn).1, this⟩
  · intro h
    refine ⟨fun n hn ↦ ⟨(h n hn).1.1, (h n hn).1.2.1⟩, fun n hn ↦ (h n hn).1.2.2, fun i hi ↦ ?_⟩
    simpa using ((h (i + 1) hi).2 (by lia)).2.2

-- The test of `Ratpoints.searchIntervals` on the `n`-th interval fails exactly when the
-- characterization of `Ratpoints.IntervalsWF` by `Ratpoints.intervalsWF_domainBits_iff_getElem`
-- fails at `n`.
private theorem bad_eq_true_iff {domain : List (Double × Double)} {n : ℕ} (hn : n < domain.length) :
    (!domain[n]!.1.le domain[n]!.2 || decide (0 < n) && !domain[n - 1]!.2.lt domain[n]!.1) = true ↔
      ¬ (domain[n].1.le domain[n].2 = true ∧
        ∀ h : 0 < n, domain[n - 1].2.lt domain[n].1 = true) := by
  rw [getElem!_pos domain n hn]
  by_cases h0 : 0 < n
  · rw [getElem!_pos domain (n - 1) (by lia)]
    cases domain[n].1.le domain[n].2 <;> simp [h0]
  · simp [h0]

theorem run_searchIntervals_eq_none_iff (H : ℕ) (domain : List (Double × Double)) :
    Id.run (searchIntervals H domain) = none ↔ ¬ IntervalsWF (domainBits domain) := by
  rcases eq_or_ne domain [] with rfl | h
  · simp [searchIntervals, IntervalsWF, AreSearchIntervals]
  rw [run_searchIntervals_eq h, intervalsWF_domainBits_iff_getElem]
  simp only [ite_eq_left_iff, reduceCtorEq, imp_false, not_not, List.any_eq_true, List.mem_range,
    not_forall]
  exact exists_congr fun n ↦ ⟨fun ⟨hn, hb⟩ ↦ ⟨hn, (bad_eq_true_iff hn).mp hb⟩,
    fun ⟨hn, hb⟩ ↦ ⟨hn, (bad_eq_true_iff hn).mpr hb⟩⟩

theorem run_searchIntervals_of_ne_nil (H : ℕ) {domain : List (Double × Double)}
    (h : domain ≠ []) (hwf : IntervalsWF (domainBits domain)) :
    Id.run (searchIntervals H domain) = some domain := by
  have hn := mt (run_searchIntervals_eq_none_iff H domain).mp (not_not.mpr hwf)
  simpa [run_searchIntervals_eq h] using hn

/-- The interval `[-h, h]` for a finite double `h ≥ H` is well formed and holds `a / b` for every
numerator `|a| ≤ H` and denominator `b ≥ 1`. -/
theorem intervalsWF_and_inIntervals_neg {h : Double} {H : ℕ} (hf : h.isFinite = true)
    (hv : (H : ℚ) ≤ h.toRat) :
    IntervalsWF (domainBits [(h.neg, h)]) ∧
      ∀ (a : ℤ) (b : ℕ), 0 < b → a.natAbs ≤ H →
        InIntervals (domainValues [(h.neg, h)]) (a / b) := by
  have hn := Double.isNaN_eq_false_of_isFinite hf
  simp only [domainValues, domainBits, List.map_cons, List.map_nil,
    Double.doubleValue_eq_toRat hf, Double.doubleValue_eq_toRat (by rwa [Double.isFinite_neg]),
    Double.toRat_neg]
  refine ⟨⟨fun i hi ↦ ?_, fun i hi ↦ ?_, .singleton _⟩, fun a b hb ha ↦ ?_⟩
  · simp only [List.mem_singleton] at hi
    rw [hi, ← Double.isNaN_eq_false_iff, ← Double.isNaN_eq_false_iff, Double.isNaN_neg]
    exact ⟨hn, hn⟩
  · simp only [List.map_cons, List.map_nil, List.mem_singleton] at hi
    rw [hi, Double.doubleValue_eq_toRat hf,
      Double.doubleValue_eq_toRat (by rwa [Double.isFinite_neg]),
      Double.toRat_neg, WithBotTop.coe_le_coe]
    linarith [Nat.cast_nonneg (α := ℚ) H]
  · refine ⟨_, List.mem_singleton_self _, ?_⟩
    have ha' : |(a : ℚ)| ≤ H := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast ha
    have hab : |(a : ℚ) / b| ≤ H := by
      simpa using (abs_intCast_div_intCast_le_abs (α := ℚ) a b).trans ha'
    simp only [WithBotTop.coe_le_coe]
    constructor <;> linarith [abs_le.mp hab]

theorem exists_run_searchIntervals_nil {H : ℕ} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) :
    ∃ dom, Id.run (searchIntervals H []) = some dom ∧ IntervalsWF (domainBits dom) ∧
      ∀ (a : ℤ) (b : ℕ), 0 < b → a.natAbs ≤ H → InIntervals (domainValues dom) (a / b) := by
  obtain ⟨hf, hv⟩ := Double.isFinite_and_le_toRat_ofInt64_nextUp hH hH63
  exact ⟨_, rfl, intervalsWF_and_inIntervals_neg hf hv⟩

/-- The caller's search intervals are well formed when `Ratpoints.searchIntervals` does not refuse
them. -/
theorem intervalsWF_of_run_searchIntervals_eq_some {H : ℕ} {domain dom : List (Double × Double)}
    (h : Id.run (searchIntervals H domain) = some dom) : IntervalsWF (domainBits domain) :=
  not_not.mp (mt (run_searchIntervals_eq_none_iff H domain).mpr (by simp [h]))

/-- The search intervals that `Ratpoints.searchIntervals` returns for `1 ≤ H < 2 ^ 63` are well
formed: the caller's, which it refuses otherwise, or the default interval. -/
theorem intervalsWF_run_searchIntervals {H : ℕ} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63)
    {domain : List (Double × Double)} :
    ∀ dom ∈ Id.run (searchIntervals H domain), IntervalsWF (domainBits dom) := by
  intro dom (h : Id.run (searchIntervals H domain) = some dom)
  rcases eq_or_ne domain [] with rfl | hn
  · obtain ⟨dom', h', hwf, -⟩ := exists_run_searchIntervals_nil hH hH63
    rw [h, Option.some.injEq] at h'
    exact h' ▸ hwf
  · have hwf := intervalsWF_of_run_searchIntervals_eq_some h
    rw [run_searchIntervals_of_ne_nil H hn hwf, Option.some.injEq] at h
    exact h ▸ hwf

namespace Sieve

/-- `exact_scale`: `min (2 ^ 64 - 1) ⌊(b m + r) / 2 ^ s⌋` whenever `b m + r` fits 128 bits, with the
end `±m 2 ^ (-s)` and its rounding `r = rh 2 ^ 64 + rl`. -/
theorem toNat_exactScale {b : Int64} {e : ExactEnd} (hs : e.s ≤ 127)
    (h : b.toUInt64.toNat * e.m.toNat + (e.rh.toNat * 2 ^ 64 + e.rl.toNat) < 2 ^ 128) :
    (exactScale b e).toNat = min (2 ^ 64 - 1)
      ((b.toUInt64.toNat * e.m.toNat + (e.rh.toNat * 2 ^ 64 + e.rl.toNat)) / 2 ^ e.s) := by
  have hP := toNat_hi_mul_add_lo h
  simp only [exactScale]
  generalize mulHi b.toUInt64 e.m + e.rh + (if b.toUInt64 * e.m + e.rl < e.rl then 1 else 0) = hi
    at hP
  generalize b.toUInt64 * e.m + e.rl = lo at hP
  rw [← hP]
  rcases Nat.eq_zero_or_pos e.s with h0 | h0
  · simp only [h0, ↓reduceIte]
    exact toNat_ite_bne_zero (by simp)
  by_cases h64 : e.s < 64
  · simp only [h0.ne', h64, ↓reduceIte]
    exact toNat_ite_bne_zero (UInt64.toNat_shift_words_of_lt hi lo h0 h64)
  · simp only [h0.ne', h64, ↓reduceIte]
    exact toNat_ite_bne_zero (by rw [UInt64.toNat_zero, Nat.zero_mul, Nat.zero_add,
      UInt64.toNat_shift_words_of_le hi lo (by lia) hs])

/-- `ldexp(f, 53)` of a double `1/2 ≤ f < 1`, the fraction of `frexp`, is exact. -/
theorem toRat_ldexp_mantDig {f : Double} (hf : f.isFinite = true) (hlo : 1 / 2 ≤ f.toRat)
    (hhi : f.toRat < 1) : (f.ldexp (Double.mantDig : ℤ)).toRat = f.toRat * 2 ^ 53 := by
  have hpos : 0 < f.toRat := by linarith
  have h53 : (2 : ℚ) ^ ((Double.mantDig : ℕ) : ℤ) = 2 ^ 53 := rfl
  have e2 : (2 : ℚ) ^ 53 ≤ 2 ^ (1023 : ℤ) := by
    rw [← zpow_natCast]; exact zpow_le_zpow_right₀ (by norm_num) (by norm_num)
  obtain ⟨-, -, hv⟩ := Double.ldexp_exact (n := (Double.mantDig : ℤ)) hf hpos.ne'
    (by
      rw [abs_of_pos hpos, h53]
      exact (zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)).trans (by linarith))
    (by
      rw [abs_of_pos hpos, h53]
      exact (mul_lt_of_lt_one_left (by positivity) hhi).trans_le e2)
  rw [hv, h53]

/-- `(unsigned long)ldexp(f, 53)` of a double `1/2 ≤ f < 1` is `f 2 ^ 53`, an integer. -/
theorem toNat_toUInt64_ldexp_mantDig {f : Double} (hf : f.isFinite = true)
    (hlo : 1 / 2 ≤ f.toRat) (hhi : f.toRat < 1) :
    ((f.ldexp (Double.mantDig : ℤ)).toUInt64.toNat : ℚ) = f.toRat * 2 ^ 53 := by
  have hv := toRat_ldexp_mantDig hf hlo hhi
  have hg0 : 0 ≤ (f.ldexp (Double.mantDig : ℤ)).toRat := by rw [hv]; linarith
  have hg52 : 2 ^ 52 ≤ (f.ldexp (Double.mantDig : ℤ)).toRat := by rw [hv]; linarith
  rw [Double.toNat_toUInt64 hg0 (by rw [hv]; linarith), ← Double.toRat_eq_natCast_floor hg52, hv]

-- The mantissa `m₀ = (unsigned long)ldexp(f, 53)` and the exponent `ex` of `frexp(ax) = (f, ex)`
-- for a finite double `ax > 0`, as `exact_end` makes them: `m₀ 2 ^ (ex - 53) = ax` with
-- `2 ^ 52 ≤ m₀ < 2 ^ 53`.
private theorem spec_toUInt64_ldexp_frexp {ax : Double} (hf : ax.isFinite = true)
    (hs : ax.signBit = false) (h0 : ax.toRat ≠ 0) :
    ((ax.frexp.1.ldexp (Double.mantDig : ℤ)).toUInt64.toNat : ℚ) * 2 ^ (ax.frexp.2 - 53) =
        ax.toRat ∧ 2 ^ 52 ≤ (ax.frexp.1.ldexp (Double.mantDig : ℤ)).toUInt64.toNat ∧
      (ax.frexp.1.ldexp (Double.mantDig : ℤ)).toUInt64.toNat < 2 ^ 53 := by
  obtain ⟨hf1, -, hv1, hlo, hhi⟩ := Double.toRat_frexp_mul_zpow_eq_and_bounds hf h0
  have hax : 0 < ax.toRat := lt_of_le_of_ne (Double.toRat_nonneg hs) (Ne.symm h0)
  have hpos : 0 < ax.frexp.1.toRat :=
    (mul_pos_iff_of_pos_right (zpow_pos two_pos _)).mp (hv1 ▸ hax)
  rw [abs_of_pos hpos] at hlo hhi
  have hm := toNat_toUInt64_ldexp_mantDig hf1 hlo hhi
  generalize (ax.frexp.1.ldexp (Double.mantDig : ℤ)).toUInt64.toNat = m0 at hm ⊢
  refine ⟨?_, ?_, ?_⟩
  · rw [hm, mul_assoc, ← zpow_natCast, ← zpow_add₀ two_ne_zero, ← hv1]
    congr 2; push_cast; ring
  · exact_mod_cast (show (2 : ℚ) ^ 52 ≤ m0 by rw [hm]; linarith)
  · exact_mod_cast (show (m0 : ℚ) < 2 ^ 53 by rw [hm]; linarith)

/-- The mantissa and the exponent `(m, s)` of `exact_end` for an end of absolute value `v > 0`:
`s ≤ 127`, `0 < m < 2 ^ 63`, and `m 2 ^ (-s) = v`, or `s` capped at `127` for a tiny
`v < 2 ^ (-75)` with `m < 2 ^ 53`, where `⌊b v⌋ = 0` and `⌈b v⌉ = 1` for every `b < 2 ^ 63`, as for
`m 2 ^ (-127)`. -/
def IsExactMantissa (v : ℚ) (ms : UInt64 × ℕ) : Prop :=
  ms.2 ≤ 127 ∧ 0 < ms.1.toNat ∧ ms.1.toNat < 2 ^ 63 ∧
    ((ms.1.toNat : ℚ) / 2 ^ ms.2 = v ∨ ms.2 = 127 ∧ ms.1.toNat < 2 ^ 53 ∧ v < 2 ^ (-75 : ℤ))

theorem isExactMantissa_of_eq {v : ℚ} {m : UInt64} {s : ℕ} (hs : s ≤ 127) (h0 : 0 < m.toNat)
    (h63 : m.toNat < 2 ^ 63) (hv : (m.toNat : ℚ) / 2 ^ s = v) : IsExactMantissa v (m, s) :=
  ⟨hs, h0, h63, .inl hv⟩

theorem isExactMantissa_cap {v : ℚ} {m : UInt64} {s : ℤ} (hs : 127 < s) (h0 : 0 < m.toNat)
    (h53 : m.toNat < 2 ^ 53) (hv : (m.toNat : ℚ) / 2 ^ s = v) :
    IsExactMantissa v (m, (127 : ℤ).toNat) := by
  refine ⟨by simp, h0, by lia, .inr ⟨rfl, h53, ?_⟩⟩
  rw [← hv, div_lt_iff₀ (zpow_pos two_pos _), ← zpow_add₀ two_ne_zero]
  calc (m.toNat : ℚ) < 2 ^ 53 := mod_cast h53
    _ = 2 ^ (53 : ℤ) := rfl
    _ ≤ 2 ^ (-75 + s) := zpow_le_zpow_right₀ (by norm_num) (by lia)

-- `m / 2 ^ z` for `2 ^ z ∣ m` scaled by `2 ^ (s - z)` is `m` scaled by `2 ^ s`.
private theorem natCast_div_two_pow_div_zpow {m z : ℕ} (hdvd : 2 ^ z ∣ m) (s : ℤ) :
    ((m / 2 ^ z : ℕ) : ℚ) / 2 ^ (s - z) = m / 2 ^ s := by
  rw [Nat.cast_div hdvd (by positivity), div_div, Nat.cast_pow, Nat.cast_ofNat, ← zpow_natCast,
    ← zpow_add₀ two_ne_zero, add_sub_cancel]

-- The mantissa of `exact_end` for `s₀ = 53 - ex > 0`: its trailing zero bits dropped, at most
-- `s₀` of them, and the exponent capped at `127`.
private theorem isExactMantissa_shiftRight {m0 : UInt64} {s0 : ℤ} {v : ℚ}
    (h52 : 2 ^ 52 ≤ m0.toNat) (h53 : m0.toNat < 2 ^ 53) (hv : (m0.toNat : ℚ) / 2 ^ s0 = v)
    (hs0 : 0 < s0) :
    IsExactMantissa v (if 127 < s0 - min (m0.toBitVec.ctz.toNat : ℤ) s0 then
        (m0 >>> (min (m0.toBitVec.ctz.toNat : ℤ) s0).toNat.toUInt64, (127 : ℤ).toNat)
      else (m0 >>> (min (m0.toBitVec.ctz.toNat : ℤ) s0).toNat.toUInt64,
        (s0 - min (m0.toBitVec.ctz.toNat : ℤ) s0).toNat)) := by
  have hc : m0.toBitVec.ctz.toNat < 64 :=
    UInt64.toNat_ctz_lt fun h ↦ by rw [h] at h52; simp at h52
  have hdvd := (Nat.pow_dvd_pow 2 (show (min (m0.toBitVec.ctz.toNat : ℤ) s0).toNat ≤
    m0.toBitVec.ctz.toNat by lia)).trans UInt64.two_pow_ctz_dvd
  have hz0 : 0 ≤ min (m0.toBitVec.ctz.toNat : ℤ) s0 := by lia
  have hzc : min (m0.toBitVec.ctz.toNat : ℤ) s0 ≤ m0.toBitVec.ctz.toNat := min_le_left _ _
  have hzs : min (m0.toBitVec.ctz.toNat : ℤ) s0 ≤ s0 := min_le_right _ _
  generalize min (m0.toBitVec.ctz.toNat : ℤ) s0 = z at hdvd hz0 hzc hzs ⊢
  have hm1 : (m0 >>> z.toNat.toUInt64).toNat = m0.toNat / 2 ^ z.toNat :=
    UInt64.toNat_shiftRight_toUInt64 _ (by lia)
  have hpos : 0 < m0.toNat / 2 ^ z.toNat := Nat.div_pos (Nat.le_of_dvd (by lia) hdvd)
    (Nat.two_pow_pos _)
  have hle : m0.toNat / 2 ^ z.toNat ≤ m0.toNat := Nat.div_le_self _ _
  have hv1 := Int.toNat_of_nonneg hz0 ▸ (natCast_div_two_pow_div_zpow hdvd s0).trans hv
  split_ifs with h127
  · exact isExactMantissa_cap h127 (by rw [hm1]; lia) (by rw [hm1]; lia) (by rw [hm1]; exact hv1)
  · refine isExactMantissa_of_eq (by lia) (by rw [hm1]; lia) (by rw [hm1]; lia) ?_
    rw [hm1, ← zpow_natCast, Int.toNat_of_nonneg (by lia)]
    exact hv1

-- The mantissa of `exact_end` for `s₀ = 53 - ex ≤ 0`: shifted up by `-s₀`, the exponent `0`.
private theorem isExactMantissa_shiftLeft {m0 : UInt64} {s0 : ℤ} {v : ℚ}
    (h52 : 2 ^ 52 ≤ m0.toNat) (hv : (m0.toNat : ℚ) / 2 ^ s0 = v) (h63 : v < 2 ^ 63)
    (hs0 : s0 < 0) :
    IsExactMantissa v (m0 <<< (-s0).toNat.toUInt64, Int.toNat 0) := by
  have hv' : (m0.toNat * 2 ^ (-s0).toNat : ℕ) = v := by
    rw [← hv, div_eq_mul_inv, ← zpow_neg]; push_cast
    rw [← zpow_natCast, Int.toNat_of_nonneg (by lia)]
  have h63' : m0.toNat * 2 ^ (-s0).toNat < 2 ^ 63 := by rw [← hv'] at h63; exact_mod_cast h63
  have hk : 2 ^ (52 + (-s0).toNat) < 2 ^ 63 := by
    rw [Nat.pow_add]; exact lt_of_le_of_lt (Nat.mul_le_mul_right _ h52) h63'
  have hk' : (-s0).toNat < 11 := by lia [(Nat.pow_lt_pow_iff_right Nat.one_lt_two).mp hk]
  have hm : (m0 <<< (-s0).toNat.toUInt64).toNat = m0.toNat * 2 ^ (-s0).toNat := by
    rw [UInt64.toNat_shiftLeft, Nat.toUInt64_eq, UInt64.toNat_ofNat',
      Nat.mod_eq_of_lt (show (-s0).toNat < 2 ^ 64 by lia),
      Nat.mod_eq_of_lt (show (-s0).toNat < 64 by lia),
      Nat.shiftLeft_eq, Nat.mod_eq_of_lt (by lia)]
  refine isExactMantissa_of_eq (by simp) (by rw [hm]; positivity) (by rw [hm]; exact h63') ?_
  rw [hm, Int.toNat_zero, pow_zero, div_one]; exact hv'

/-- The mantissa and the exponent that `exact_end` makes for the absolute value of a finite end
`x ≠ 0` with `|x| < 2 ^ 63`. -/
theorem isExactMantissa_run_exactMantissa {x : Double} (ha : x.fabs.lt .twoPow63 = true)
    (h0 : x.toRat ≠ 0) : IsExactMantissa |x.toRat| (Id.run (exactMantissa x.fabs)) := by
  obtain ⟨hf, h63⟩ := Double.isFinite_and_abs_lt_of_lt ha
  obtain ⟨hv, h52, h53⟩ := spec_toUInt64_ldexp_frexp (by rwa [Double.isFinite_fabs])
    (Double.signBit_fabs x) (by rw [Double.toRat_fabs]; exact abs_ne_zero.mpr h0)
  rw [← Double.toRat_fabs] at h63 ⊢
  rw [show x.fabs.frexp.2 - 53 = -(53 - x.fabs.frexp.2) by ring, zpow_neg, ← div_eq_mul_inv] at hv
  simp only [exactMantissa]
  generalize (x.fabs.frexp.1.ldexp (Double.mantDig : ℤ)).toUInt64 = m0 at hv h52 h53 ⊢
  generalize 53 - x.fabs.frexp.2 = s0 at hv ⊢
  have hm0 : m0 ≠ 0 := fun h ↦ by rw [h] at h52; simp at h52
  simp only [hm0, ↓reduceIte]
  by_cases hs0 : 0 < s0
  · simp only [hs0, ↓reduceIte, Id.run_bind, run_ctz hm0, show ¬s0 - min
      (m0.toBitVec.ctz.toNat : ℤ) s0 < 0 by lia]
    exact isExactMantissa_shiftRight h52 h53 hv hs0
  · rcases lt_or_eq_of_le (not_lt.mp hs0) with hs1 | hs1
    · simp only [hs0, hs1, ↓reduceIte, show ¬(127 : ℤ) < 0 by decide]
      exact isExactMantissa_shiftLeft h52 hv h63 hs1
    · simp only [hs1, lt_irrefl, ↓reduceIte, show ¬(127 : ℤ) < 0 by decide]
      exact isExactMantissa_of_eq (by simp) (by lia) (by lia) (by simpa [hs1] using hv)

-- The rounding `rh 2 ^ 64 + rl` that `exact_end` writes: `2 ^ s - 1` when the end wants `b |x|`
-- rounded up, and `0` otherwise.
private theorem toNat_rounding (up : Bool) {s : ℕ} (hs : s ≤ 127) :
    (if up then (if s < 64 then (((1 : UInt64) <<< s.toUInt64) - 1, (0 : UInt64))
      else (~~~0, ((1 : UInt64) <<< (s - 64).toUInt64) - 1)) else (0, 0)).2.toNat * 2 ^ 64 +
      (if up then (if s < 64 then (((1 : UInt64) <<< s.toUInt64) - 1, (0 : UInt64))
      else (~~~0, ((1 : UInt64) <<< (s - 64).toUInt64) - 1)) else (0, 0)).1.toNat =
      if up then 2 ^ s - 1 else 0 := by
  cases up
  · simp
  by_cases h64 : s < 64
  · simp only [↓reduceIte, h64, UInt64.toNat_one_shiftLeft_sub_one h64, UInt64.toNat_zero,
      Nat.zero_mul, Nat.zero_add]
  · simp only [↓reduceIte, h64, UInt64.toNat_one_shiftLeft_sub_one (show s - 64 < 64 by lia),
      UInt64.toNat_not, UInt64.toNat_zero]
    have : 2 ^ s = 2 ^ (s - 64) * 2 ^ 64 := by rw [← Nat.pow_add]; congr 1; lia
    rw [Nat.sub_mul]; lia [Nat.one_le_two_pow (n := s - 64)]

theorem m_run_exactEnd (x : Double) (lower : Bool) : (Id.run (exactEnd x lower)).m =
    (if x.fabs.lt .twoPow63 then Id.run (exactMantissa x.fabs)
      else ((1 : UInt64) <<< 63, 0)).1 := by
  simp only [exactEnd]; split <;> simp_all

theorem s_run_exactEnd (x : Double) (lower : Bool) : (Id.run (exactEnd x lower)).s =
    (if x.fabs.lt .twoPow63 then Id.run (exactMantissa x.fabs)
      else ((1 : UInt64) <<< 63, 0)).2 := by
  simp only [exactEnd]; split <;> simp_all

theorem neg_run_exactEnd (x : Double) (lower : Bool) :
    (Id.run (exactEnd x lower)).neg = x.lt .zero := by
  simp only [exactEnd]; split <;> rfl

theorem rounding_run_exactEnd {x : Double} {lower : Bool}
    (hs : (Id.run (exactEnd x lower)).s ≤ 127) :
    (Id.run (exactEnd x lower)).rh.toNat * 2 ^ 64 + (Id.run (exactEnd x lower)).rl.toNat =
      if lower != x.lt .zero then 2 ^ (Id.run (exactEnd x lower)).s - 1 else 0 := by
  revert hs
  simp only [exactEnd]
  split <;> exact fun hs ↦ toNat_rounding _ hs

theorem run_exactMantissa_fabs_of_toRat_eq_zero {x : Double} (h : x.toRat = 0) :
    Id.run (exactMantissa x.fabs) = (0, 0) := by
  replace h : x.fabs.toRat = 0 := by rw [Double.toRat_fabs, h, abs_zero]
  have hz := Double.isZero_eq_true_iff.mpr h
  have hm : (x.fabs.frexp.1.ldexp (Double.mantDig : ℤ)).toUInt64 = 0 := by
    simp only [Double.frexp, Double.ldexp, hz, Bool.or_true, ↓reduceIte]
    apply UInt64.toNat_inj.mp
    rw [Double.toNat_toUInt64 (by rw [h]) (by rw [h]; norm_num), h]; simp
  simp only [exactMantissa, hm, ↓reduceIte]
  rfl

/-- The value `±m 2 ^ (-s)` of an end of a search interval as `exact_end` makes it. -/
def ExactEnd.value (e : ExactEnd) : ℚ := (if e.neg then -1 else 1) * ((e.m.toNat : ℚ) / 2 ^ e.s)

theorem lowNumerator_eq_and_highNumerator_eq_of_ceil_eq_of_floor_eq {b H : ℕ} {q q' : ℚ}
    (hc : ⌈(b : ℚ) * q⌉ = ⌈(b : ℚ) * q'⌉) (hf : ⌊(b : ℚ) * q⌋ = ⌊(b : ℚ) * q'⌋) :
    lowNumerator b H (q : WithBotTop ℚ) = lowNumerator b H (q' : WithBotTop ℚ) ∧
      highNumerator b H (q : WithBotTop ℚ) = highNumerator b H (q' : WithBotTop ℚ) := by
  simp only [lowNumerator, highNumerator, WithBotTop.rec_coe, hc, hf, and_self]

theorem lowNumerator_eq_and_highNumerator_eq_of_two_pow_le {b H : ℕ} (hb : 1 ≤ b)
    (hH : H < 2 ^ 63) {x : WithBotTop ℚ} (hx : (((2 ^ 63 : ℚ)) : WithBotTop ℚ) ≤ x) :
    lowNumerator b H x = H + 1 ∧ highNumerator b H x = H := by
  induction x using WithBotTop.rec with
  | bot => exact absurd hx (by simp)
  | top => simp [lowNumerator, highNumerator]
  | coe q =>
    have hq := WithBotTop.coe_le_coe.mp hx
    have h1 : (H : ℚ) + 1 ≤ b * q := by
      have : (H : ℚ) + 1 ≤ 2 ^ 63 := mod_cast hH
      linarith [le_mul_of_one_le_left (by linarith : (0 : ℚ) ≤ q)
        (show (1 : ℚ) ≤ b from mod_cast hb)]
    have h4 : (H : ℤ) + 1 ≤ ⌈(b : ℚ) * q⌉ := Int.le_ceil_iff.mpr (by push_cast; linarith)
    have h5 : (H : ℤ) ≤ ⌊(b : ℚ) * q⌋ := Int.le_floor.mpr (by push_cast; linarith)
    simp only [lowNumerator, highNumerator, WithBotTop.rec_coe]
    constructor <;> lia

theorem lowNumerator_eq_and_highNumerator_eq_of_le_neg_two_pow {b H : ℕ} (hb : 1 ≤ b)
    (hH : H < 2 ^ 63) {x : WithBotTop ℚ} (hx : x ≤ (((-2 ^ 63 : ℚ)) : WithBotTop ℚ)) :
    lowNumerator b H x = -H ∧ highNumerator b H x = -H - 1 := by
  induction x using WithBotTop.rec with
  | bot => simp [lowNumerator, highNumerator]
  | top => exact absurd hx (by simp)
  | coe q =>
    have hq := WithBotTop.coe_le_coe.mp hx
    have h1 : b * q ≤ -(H : ℚ) - 1 := by
      have : (H : ℚ) + 1 ≤ 2 ^ 63 := mod_cast hH
      linarith [mul_le_of_one_le_left (by linarith : q ≤ 0) (show (1 : ℚ) ≤ b from mod_cast hb)]
    have h4 : ⌈(b : ℚ) * q⌉ ≤ -(H : ℤ) - 1 := Int.ceil_le.mpr (by push_cast; linarith)
    have h5 : ⌊(b : ℚ) * q⌋ ≤ -(H : ℤ) - 1 := (Int.floor_le_ceil _).trans h4
    simp only [lowNumerator, highNumerator, WithBotTop.rec_coe]
    constructor <;> lia

theorem value_run_exactEnd_of_lt_eq_false {x : Double} (lower : Bool)
    (ha : x.fabs.lt .twoPow63 = false) :
    (Id.run (exactEnd x lower)).value = if x.lt .zero then -2 ^ 63 else 2 ^ 63 := by
  simp only [ExactEnd.value, m_run_exactEnd, s_run_exactEnd, neg_run_exactEnd, ha,
    Bool.false_eq_true, ↓reduceIte]
  rw [show ((1 : UInt64) <<< 63).toNat = 2 ^ 63 from rfl]
  split_ifs <;> norm_num

/-- The numerators of the end `x` of a search interval with `|x| ≥ 2 ^ 63` (an infinity included)
are those of `exact_end`'s `±2 ^ 63`: beyond the height bound on the side of its sign. -/
theorem lowNumerator_eq_and_highNumerator_eq_run_exactEnd_of_lt_eq_false {x : Double}
    (hx : x.isNaN = false) (lower : Bool) (ha : x.fabs.lt .twoPow63 = false) {b H : ℕ} (hb : 1 ≤ b)
    (hH : H < 2 ^ 63) :
    lowNumerator b H (doubleValue x.bits) =
        lowNumerator b H ((Id.run (exactEnd x lower)).value : WithBotTop ℚ) ∧
      highNumerator b H (doubleValue x.bits) =
        highNumerator b H ((Id.run (exactEnd x lower)).value : WithBotTop ℚ) := by
  rw [value_run_exactEnd_of_lt_eq_false lower ha]
  rcases Double.le_doubleValue_or_of_lt_eq_false hx ha with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · simp only [h1, Bool.false_eq_true, ↓reduceIte]
    obtain ⟨e1, e2⟩ := lowNumerator_eq_and_highNumerator_eq_of_two_pow_le hb hH h2
    obtain ⟨e3, e4⟩ := lowNumerator_eq_and_highNumerator_eq_of_two_pow_le hb hH le_rfl
    exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩
  · simp only [h1, ↓reduceIte]
    obtain ⟨e1, e2⟩ := lowNumerator_eq_and_highNumerator_eq_of_le_neg_two_pow hb hH h2
    obtain ⟨e3, e4⟩ := lowNumerator_eq_and_highNumerator_eq_of_le_neg_two_pow hb hH le_rfl
    exact ⟨e1.trans e3.symm, e2.trans e4.symm⟩

/-- A tiny end `0 < |q| < 2 ^ (-75)` has the numerators of `exact_end`'s `±m 2 ^ (-127)` with
`0 < m < 2 ^ 53` and the same sign, for every denominator `1 ≤ b < 2 ^ 63`: `b |q|` and
`b m 2 ^ (-127)` lie strictly between `0` and `1`. -/
theorem lowNumerator_eq_and_highNumerator_eq_of_abs_lt {b H : ℕ} (hb : 1 ≤ b) (hb63 : b < 2 ^ 63)
    {q : ℚ} {neg : Bool} {m : ℕ} (hq : q ≠ 0) (hq75 : |q| < 2 ^ (-75 : ℤ))
    (hneg : neg = true ↔ q < 0) (hm0 : 0 < m) (hm : m < 2 ^ 53) :
    lowNumerator b H (q : WithBotTop ℚ) =
        lowNumerator b H (((if neg then -1 else 1) * ((m : ℚ) / 2 ^ 127) : ℚ) : WithBotTop ℚ) ∧
      highNumerator b H (q : WithBotTop ℚ) =
        highNumerator b H (((if neg then -1 else 1) * ((m : ℚ) / 2 ^ 127) : ℚ) : WithBotTop ℚ) := by
  have hb63' : (b : ℚ) < 2 ^ 63 := mod_cast hb63
  have hb0 : (0 : ℚ) < b := by positivity
  have hv : 0 < (m : ℚ) / 2 ^ 127 := by positivity
  have h1 : |(b : ℚ) * q| < 1 := by
    rw [abs_mul, abs_of_pos hb0]
    calc (b : ℚ) * |q| < 2 ^ 63 * 2 ^ (-75 : ℤ) :=
          mul_lt_mul'' hb63' hq75 (by positivity) (abs_nonneg _)
      _ < 1 := by norm_num
  have h2 : |(b : ℚ) * ((if neg then -1 else 1) * ((m : ℚ) / 2 ^ 127))| < 1 := by
    rw [abs_mul, abs_of_pos hb0, Double.abs_sign_mul _ hv.le]
    calc (b : ℚ) * ((m : ℚ) / 2 ^ 127) < 2 ^ 63 * (2 ^ 53 / 2 ^ 127) :=
          mul_lt_mul'' hb63' (by gcongr; exact_mod_cast hm) (by positivity) hv.le
      _ < 1 := by norm_num
  have hs : (b : ℚ) * q < 0 ↔ (b : ℚ) * ((if neg then -1 else 1) * ((m : ℚ) / 2 ^ 127)) < 0 := by
    rw [mul_neg_iff, mul_neg_iff, ← hneg]
    cases neg <;> simp [hb0, hv, hv.le, not_lt.mpr hb0.le]
  have h := Rat.ceil_eq_and_floor_eq_of_abs_lt_one (mul_ne_zero hb0.ne' hq) h1
    (mul_ne_zero hb0.ne' (by split_ifs <;> positivity)) h2 hs
  exact lowNumerator_eq_and_highNumerator_eq_of_ceil_eq_of_floor_eq h.1 h.2

-- A rational number `q` is its absolute value times the sign that the flag `neg` of `q < 0` gives.
private theorem sign_mul_abs {q : ℚ} {neg : Bool} (h : neg = true ↔ q < 0) :
    (if neg then -1 else 1) * |q| = q := by
  cases neg
  · simp only [Bool.false_eq_true, false_iff, not_lt] at h; simp [abs_of_nonneg h]
  · simp [abs_of_neg (h.mp rfl)]

/-- The numerators of the end `x` of a search interval with `|x| < 2 ^ 63` are those of the value
of `exact_end`, exact unless capped for a tiny `x`, for every denominator `1 ≤ b < 2 ^ 63`. -/
theorem lowNumerator_eq_and_highNumerator_eq_run_exactEnd_of_lt_eq_true {x : Double} (lower : Bool)
    (ha : x.fabs.lt .twoPow63 = true) {b H : ℕ} (hb : 1 ≤ b) (hb63 : b < 2 ^ 63) :
    lowNumerator b H (doubleValue x.bits) =
        lowNumerator b H ((Id.run (exactEnd x lower)).value : WithBotTop ℚ) ∧
      highNumerator b H (doubleValue x.bits) =
        highNumerator b H ((Id.run (exactEnd x lower)).value : WithBotTop ℚ) := by
  obtain ⟨hf, habs⟩ := Double.isFinite_and_abs_lt_of_lt ha
  have hneg := Double.lt_zero_eq_true_iff_toRat hf
  rw [Double.doubleValue_eq_toRat hf]
  simp only [ExactEnd.value, m_run_exactEnd, s_run_exactEnd, neg_run_exactEnd, ha, ↓reduceIte]
  by_cases h0 : x.toRat = 0
  · rw [run_exactMantissa_fabs_of_toRat_eq_zero h0, h0]
    simp
  have hm := isExactMantissa_run_exactMantissa ha h0
  generalize Id.run (exactMantissa x.fabs) = ms at hm ⊢
  obtain ⟨-, hm0, -, hv | ⟨hs, hm53, h75⟩⟩ := hm
  · rw [hv, sign_mul_abs hneg]; exact ⟨rfl, rfl⟩
  · rw [hs]; exact lowNumerator_eq_and_highNumerator_eq_of_abs_lt hb hb63 h0 h75 hneg hm0 hm53

/-- The numerators of the end `x` of a search interval, not a NaN, are those of the value of
`exact_end`, for every denominator `1 ≤ b < 2 ^ 63` and height bound `H < 2 ^ 63`. -/
theorem lowNumerator_eq_and_highNumerator_eq_run_exactEnd {x : Double} (hx : x.isNaN = false)
    (lower : Bool) {b H : ℕ} (hb : 1 ≤ b) (hb63 : b < 2 ^ 63) (hH : H < 2 ^ 63) :
    lowNumerator b H (doubleValue x.bits) =
        lowNumerator b H ((Id.run (exactEnd x lower)).value : WithBotTop ℚ) ∧
      highNumerator b H (doubleValue x.bits) =
        highNumerator b H ((Id.run (exactEnd x lower)).value : WithBotTop ℚ) := by
  cases ha : x.fabs.lt .twoPow63
  · exact lowNumerator_eq_and_highNumerator_eq_run_exactEnd_of_lt_eq_false hx lower ha hb hH
  · exact lowNumerator_eq_and_highNumerator_eq_run_exactEnd_of_lt_eq_true lower ha hb hb63

/-- The end `e` of a search interval, at its lower end if `lower`, is one that `exact_end` makes:
`s ≤ 127`, `m ≤ 2 ^ 63`, and the rounding `2 ^ s - 1` when the end wants `b |x|` rounded up. -/
def IsEnd (e : ExactEnd) (lower : Bool) : Prop :=
  e.s ≤ 127 ∧ e.m.toNat ≤ 2 ^ 63 ∧
    e.rh.toNat * 2 ^ 64 + e.rl.toNat = if lower != e.neg then 2 ^ e.s - 1 else 0

theorem isEnd_run_exactEnd (x : Double) (lower : Bool) :
    IsEnd (Id.run (exactEnd x lower)) lower := by
  have hs : (Id.run (exactEnd x lower)).s ≤ 127 ∧ (Id.run (exactEnd x lower)).m.toNat ≤ 2 ^ 63 := by
    rw [m_run_exactEnd, s_run_exactEnd]
    cases ha : x.fabs.lt .twoPow63
    · exact ⟨by simp, by simp⟩
    simp only [↓reduceIte]
    by_cases h0 : x.toRat = 0
    · rw [run_exactMantissa_fabs_of_toRat_eq_zero h0]; simp
    · obtain ⟨hs, -, hm, -⟩ := isExactMantissa_run_exactMantissa ha h0
      exact ⟨hs, hm.le⟩
  exact ⟨hs.1, hs.2, by rw [rounding_run_exactEnd hs.1, neg_run_exactEnd]⟩

theorem ceil_mul_div_two_pow (B m s : ℕ) :
    ⌈(B : ℚ) * ((m : ℚ) / 2 ^ s)⌉ = (((B * m + (2 ^ s - 1)) / 2 ^ s : ℕ) : ℤ) := by
  rw [← mul_div_assoc, ← Nat.cast_mul, show ((2 : ℚ) ^ s) = ((2 ^ s : ℕ) : ℚ) by push_cast; rfl,
    ← Int.cast_natCast (B * m),
    Rat.ceil_intCast_div_natCast_eq_add_sub_one_div _ (Nat.two_pow_pos s)]
  push_cast [Nat.cast_sub Nat.one_le_two_pow, add_sub_assoc]
  rfl

theorem floor_mul_div_two_pow (B m s : ℕ) :
    ⌊(B : ℚ) * ((m : ℚ) / 2 ^ s)⌋ = ((B * m / 2 ^ s : ℕ) : ℤ) := by
  rw [← mul_div_assoc, ← Nat.cast_mul, show ((2 : ℚ) ^ s) = ((2 ^ s : ℕ) : ℚ) by push_cast; rfl,
    ← Int.cast_natCast (B * m), Rat.floor_intCast_div_natCast]
  push_cast; rfl

theorem toNat_exactScale_of_isEnd {e : ExactEnd} {lower : Bool} (he : IsEnd e lower) {B : ℕ}
    (hB : B < 2 ^ 63) : (exactScale B.toInt64 e).toNat = min (2 ^ 64 - 1)
      (if lower != e.neg then (B * e.m.toNat + (2 ^ e.s - 1)) / 2 ^ e.s
        else B * e.m.toNat / 2 ^ e.s) := by
  obtain ⟨hs, hm, hr⟩ := he
  have hB' := Nat.toNat_toUInt64_toInt64 hB
  have h127 : 2 ^ e.s ≤ 2 ^ 127 := Nat.pow_le_pow_right Nat.zero_lt_two hs
  rw [toNat_exactScale hs, hB', hr]
  · split <;> simp
  · rw [hB', hr]
    split <;> lia [Nat.mul_le_mul hB.le hm]

theorem lowNumerator_value_of_not_neg {e : ExactEnd} (hn : e.neg = false) (B H : ℕ) :
    lowNumerator B H (e.value : WithBotTop ℚ) =
      max (-(H : ℤ)) (min (((B * e.m.toNat + (2 ^ e.s - 1)) / 2 ^ e.s : ℕ) : ℤ) (H + 1)) := by
  simp only [lowNumerator, WithBotTop.rec_coe, ExactEnd.value, hn, Bool.false_eq_true, ↓reduceIte,
    one_mul, ceil_mul_div_two_pow]

theorem lowNumerator_value_of_neg {e : ExactEnd} (hn : e.neg = true) (B H : ℕ) :
    lowNumerator B H (e.value : WithBotTop ℚ) =
      max (-(H : ℤ)) (min (-((B * e.m.toNat / 2 ^ e.s : ℕ) : ℤ)) (H + 1)) := by
  simp only [lowNumerator, WithBotTop.rec_coe, ExactEnd.value, hn, ↓reduceIte, neg_one_mul,
    mul_neg, Int.ceil_neg, floor_mul_div_two_pow]

theorem highNumerator_value_of_not_neg {e : ExactEnd} (hn : e.neg = false) (B H : ℕ) :
    highNumerator B H (e.value : WithBotTop ℚ) =
      max (-(H : ℤ) - 1) (min ((B * e.m.toNat / 2 ^ e.s : ℕ) : ℤ) H) := by
  simp only [highNumerator, WithBotTop.rec_coe, ExactEnd.value, hn, Bool.false_eq_true,
    ↓reduceIte, one_mul, floor_mul_div_two_pow]

theorem highNumerator_value_of_neg {e : ExactEnd} (hn : e.neg = true) (B H : ℕ) :
    highNumerator B H (e.value : WithBotTop ℚ) =
      max (-(H : ℤ) - 1) (min (-(((B * e.m.toNat + (2 ^ e.s - 1)) / 2 ^ e.s : ℕ) : ℤ)) H) := by
  simp only [highNumerator, WithBotTop.rec_coe, ExactEnd.value, hn, ↓reduceIte, neg_one_mul,
    mul_neg, Int.floor_neg, ceil_mul_div_two_pow]

/-- `interval_bits_exact` at a lower end `x ≥ 0`: the code `2` exactly when `⌈b x⌉ > h`, and
otherwise `⌈b x⌉`. -/
theorem lowNumerator_exact_of_not_neg {e : ExactEnd} (he : IsEnd e true) (hn : e.neg = false)
    {B H : ℕ} (hB : B < 2 ^ 63) (hH : H < 2 ^ 63) :
    (H.toInt64.toUInt64 < exactScale B.toInt64 e ↔
        (H : ℤ) < lowNumerator B H (e.value : WithBotTop ℚ)) ∧
      (exactScale B.toInt64 e ≤ H.toInt64.toUInt64 →
        (exactScale B.toInt64 e).toInt64.toInt = lowNumerator B H (e.value : WithBotTop ℚ)) := by
  have ht := toNat_exactScale_of_isEnd he hB
  simp only [hn, Bool.bne_false, ↓reduceIte] at ht
  rw [lowNumerator_value_of_not_neg hn, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
    Nat.toNat_toUInt64_toInt64 hH, ht]
  generalize (B * e.m.toNat + (2 ^ e.s - 1)) / 2 ^ e.s = Q at ht ⊢
  refine ⟨by lia, fun h ↦ ?_⟩
  rw [UInt64.toInt_toInt64_of_lt (by rw [ht]; lia), ht]; lia

/-- `interval_bits_exact` at a lower end `x < 0`: `⌈b x⌉ = -⌊b |x|⌋`, clipped to `-h`. -/
theorem lowNumerator_exact_of_neg {e : ExactEnd} (he : IsEnd e true) (hn : e.neg = true)
    {B H : ℕ} (hB : B < 2 ^ 63) (hH : H < 2 ^ 63) :
    (if H.toInt64.toUInt64 ≤ exactScale B.toInt64 e then -H.toInt64
      else -(exactScale B.toInt64 e).toInt64).toInt =
        lowNumerator B H (e.value : WithBotTop ℚ) := by
  have ht := toNat_exactScale_of_isEnd he hB
  simp only [hn, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at ht
  rw [lowNumerator_value_of_neg hn]
  split_ifs with h <;> rw [UInt64.le_iff_toNat_le, Nat.toNat_toUInt64_toInt64 hH, ht] at h
  · generalize B * e.m.toNat / 2 ^ e.s = Q at ht h ⊢
    rw [Int64.toInt_neg_of_lt (by rw [Int64.toInt_ofNat_of_lt hH]; lia),
      Int64.toInt_ofNat_of_lt hH]; lia
  · have h' : (exactScale B.toInt64 e).toNat < 2 ^ 63 := by rw [ht]; lia
    rw [Int64.toInt_neg_of_lt (by rw [UInt64.toInt_toInt64_of_lt h']; lia),
      UInt64.toInt_toInt64_of_lt h', ht]
    generalize B * e.m.toNat / 2 ^ e.s = Q at ht h ⊢
    lia

/-- `interval_bits_exact` at an upper end `x ≥ 0`: `⌊b x⌋`, clipped to `h`. -/
theorem highNumerator_exact_of_not_neg {e : ExactEnd} (he : IsEnd e false) (hn : e.neg = false)
    {B H : ℕ} (hB : B < 2 ^ 63) (hH : H < 2 ^ 63) :
    (if H.toInt64.toUInt64 ≤ exactScale B.toInt64 e then H.toInt64
      else (exactScale B.toInt64 e).toInt64).toInt =
        highNumerator B H (e.value : WithBotTop ℚ) := by
  have ht := toNat_exactScale_of_isEnd he hB
  simp only [hn, bne_self_eq_false, Bool.false_eq_true, ↓reduceIte] at ht
  rw [highNumerator_value_of_not_neg hn]
  split_ifs with h <;> rw [UInt64.le_iff_toNat_le, Nat.toNat_toUInt64_toInt64 hH, ht] at h
  · generalize B * e.m.toNat / 2 ^ e.s = Q at ht h ⊢
    rw [Int64.toInt_ofNat_of_lt hH]; lia
  · rw [UInt64.toInt_toInt64_of_lt (by rw [ht]; lia), ht]
    generalize B * e.m.toNat / 2 ^ e.s = Q at ht h ⊢
    lia

/-- `interval_bits_exact` at an upper end `x < 0`: the code `1` exactly when `⌊b x⌋ < -h`, and
otherwise `⌊b x⌋ = -⌈b |x|⌉`. -/
theorem highNumerator_exact_of_neg {e : ExactEnd} (he : IsEnd e false) (hn : e.neg = true)
    {B H : ℕ} (hB : B < 2 ^ 63) (hH : H < 2 ^ 63) :
    (H.toInt64.toUInt64 < exactScale B.toInt64 e ↔
        highNumerator B H (e.value : WithBotTop ℚ) < -(H : ℤ)) ∧
      (exactScale B.toInt64 e ≤ H.toInt64.toUInt64 →
        (-(exactScale B.toInt64 e).toInt64).toInt =
          highNumerator B H (e.value : WithBotTop ℚ)) := by
  have ht := toNat_exactScale_of_isEnd he hB
  simp only [hn, Bool.false_bne, ↓reduceIte] at ht
  rw [highNumerator_value_of_neg hn, UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le,
    Nat.toNat_toUInt64_toInt64 hH, ht]
  generalize (B * e.m.toNat + (2 ^ e.s - 1)) / 2 ^ e.s = Q at ht ⊢
  refine ⟨by lia, fun h ↦ ?_⟩
  have h' : (exactScale B.toInt64 e).toNat < 2 ^ 63 := by rw [ht]; lia
  rw [Int64.toInt_neg_of_lt (by rw [UInt64.toInt_toInt64_of_lt h']; lia),
    UInt64.toInt_toInt64_of_lt h', ht]
  lia

-- The lower end of `interval_bits_exact`: none (the code `2`) exactly when `⌈b l⌉ > h`, and
-- otherwise `⌈b l⌉` clipped to `-h`.
private theorem lowerOpt_spec {e : ExactEnd} (he : IsEnd e true) {B H : ℕ} (hB : B < 2 ^ 63)
    (hH : H < 2 ^ 63) {o : Option Int64}
    (ho : o = if e.neg then some (if H.toInt64.toUInt64 ≤ exactScale B.toInt64 e then -H.toInt64
        else -(exactScale B.toInt64 e).toInt64)
      else if H.toInt64.toUInt64 < exactScale B.toInt64 e then none
      else some (exactScale B.toInt64 e).toInt64) :
    (o = none ↔ (H : ℤ) < lowNumerator B H (e.value : WithBotTop ℚ)) ∧
      ∀ l, o = some l → l.toInt = lowNumerator B H (e.value : WithBotTop ℚ) := by
  cases hn : e.neg <;> simp only [hn, Bool.false_eq_true, ↓reduceIte] at ho <;> subst ho
  · obtain ⟨h1, h2⟩ := lowNumerator_exact_of_not_neg he hn hB hH
    split_ifs with h
    · exact ⟨iff_of_true rfl (h1.mp h), nofun⟩
    · exact ⟨iff_of_false nofun (mt h1.mpr h),
        fun l hl ↦ Option.some.inj hl ▸ h2 (UInt64.not_lt.mp h)⟩
  · refine ⟨iff_of_false nofun fun h ↦ ?_, fun l hl ↦ Option.some.inj hl ▸
      lowNumerator_exact_of_neg he hn hB hH⟩
    lia [lowNumerator_value_of_neg hn B H]

-- The upper end of `interval_bits_exact`: the code `1` exactly when `⌊b u⌋ < -h`, and otherwise
-- `⌊b u⌋` clipped to `h`.
private theorem upperBits_spec {e : ExactEnd} (he : IsEnd e false) {B H : ℕ} (hB : B < 2 ^ 63)
    (hH : H < 2 ^ 63) :
    ((e.neg && decide (H.toInt64.toUInt64 < exactScale B.toInt64 e)) = true ↔
        highNumerator B H (e.value : WithBotTop ℚ) < -(H : ℤ)) ∧
      ((e.neg && decide (H.toInt64.toUInt64 < exactScale B.toInt64 e)) = false →
        (if e.neg then -(exactScale B.toInt64 e).toInt64
          else if H.toInt64.toUInt64 ≤ exactScale B.toInt64 e then H.toInt64
          else (exactScale B.toInt64 e).toInt64).toInt =
            highNumerator B H (e.value : WithBotTop ℚ)) := by
  cases hn : e.neg
  · exact ⟨iff_of_false nofun (by lia [highNumerator_value_of_not_neg hn B H]),
      fun _ ↦ highNumerator_exact_of_not_neg he hn hB hH⟩
  · obtain ⟨h1, h2⟩ := highNumerator_exact_of_neg he hn hB hH
    simp only [Bool.true_and, decide_eq_true_eq, decide_eq_false_iff_not, ↓reduceIte]
    exact ⟨h1, fun h ↦ h2 (UInt64.not_lt.mp h)⟩

/-- The bits of the range `L, …, U` of numerators within `-H - 1, …, H + 1` in the packing of a
class, in the form of `numerators_to_bits` that the sieve takes for the height bound `H`, the plain
one for `H ≤ 2 ^ 63 - 65`. -/
theorem toInt_numeratorsToBits_of_range {l h : Int64} {cl : NumClass} (hcl : cl.WF) {H : ℕ}
    (hH : H < 2 ^ 63) {L U : ℤ} (hl : l.toInt = L) (hh : h.toInt = U) (hL : -(H : ℤ) ≤ L)
    (hU : -(H : ℤ) - 1 ≤ U) (hUH : U ≤ H) :
    (numeratorsToBits l h cl (decide (9223372036854775807 - 64 < H.toInt64))).1.toInt =
        -((cl.a0 - max L (-H)) / 2 ^ cl.k) ∧
      (numeratorsToBits l h cl (decide (9223372036854775807 - 64 < H.toInt64))).2.toInt =
        (min U H - cl.a0) / 2 ^ cl.k := by
  rw [max_eq_left hL, min_eq_left hUH, ← hl, ← hh]
  refine toInt_numeratorsToBits hcl fun hs ↦ ?_
  rw [decide_eq_false_iff_not, Int64.lt_iff_toInt_lt, Int64.toInt_ofNat_of_lt hH,
    show (9223372036854775807 - 64 : Int64).toInt = 9223372036854775743 by decide] at hs
  rw [hl, hh]; constructor <;> lia [hcl.a0_lt_sixty_four]

/-- `interval_bits_exact` gives the range of the numerators of the ends: the code `2` only above
`H`, the code `1` only below `-H`, and otherwise the bits of the range within `-H, …, H`. -/
theorem toInt_intervalBitsExact {bd : IntervalBounds} (hl : IsEnd bd.low true)
    (hu : IsEnd bd.up false) {B H : ℕ} (hBH : B ≤ H) (hH : H < 2 ^ 63) {cl : NumClass}
    (hcl : cl.WF) :
    ((intervalBitsExact B.toInt64 bd H.toInt64 cl).1 = 2 →
        (H : ℤ) < lowNumerator B H (bd.low.value : WithBotTop ℚ)) ∧
      ((intervalBitsExact B.toInt64 bd H.toInt64 cl).1 = 1 →
        highNumerator B H (bd.up.value : WithBotTop ℚ) < -H) ∧
      ((intervalBitsExact B.toInt64 bd H.toInt64 cl).1 ≠ 1 →
        (intervalBitsExact B.toInt64 bd H.toInt64 cl).1 ≠ 2 →
        (intervalBitsExact B.toInt64 bd H.toInt64 cl).2.1.toInt =
            -((cl.a0 - max (lowNumerator B H (bd.low.value : WithBotTop ℚ)) (-H)) / 2 ^ cl.k) ∧
          (intervalBitsExact B.toInt64 bd H.toInt64 cl).2.2.toInt =
            (min (highNumerator B H (bd.up.value : WithBotTop ℚ)) H - cl.a0) / 2 ^ cl.k) := by
  have hB : B < 2 ^ 63 := by lia
  simp only [intervalBitsExact]
  generalize ho : (if bd.low.neg then _ else _ : Option Int64) = o
  obtain ⟨h1, h2⟩ := lowerOpt_spec hl hB hH ho.symm
  obtain ⟨h3, h4⟩ := upperBits_spec hu hB hH
  cases o with
  | none => exact ⟨fun _ ↦ h1.mp rfl, nofun, fun _ h ↦ absurd rfl h⟩
  | some l =>
    cases hc : (bd.up.neg && decide (H.toInt64.toUInt64 < exactScale B.toInt64 bd.up))
    · simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨nofun, nofun, fun _ _ ↦ toInt_numeratorsToBits_of_range hcl hH (h2 l rfl) (h4 hc)
        (neg_le_lowNumerator ..) (neg_sub_one_le_highNumerator ..)
        (highNumerator_le ..)⟩
    · simp only [↓reduceIte]
      exact ⟨nofun, fun _ ↦ h3.mp hc, fun h _ ↦ absurd rfl h⟩

/-- The form `(b M + C) >> sh` of an end on the `long`s, without overflow: the floor of
`(b M + C) / 2 ^ sh`. -/
theorem toInt_mul_add_shiftRight {B : ℕ} (hB : B < 2 ^ 63) {M C : Int64} {s : ℕ} (hs : s < 64)
    (h1 : -2 ^ 63 ≤ B * M.toInt) (h2 : B * M.toInt < 2 ^ 63)
    (h3 : -2 ^ 63 ≤ B * M.toInt + C.toInt) (h4 : B * M.toInt + C.toInt < 2 ^ 63) :
    ((B.toInt64 * M + C) >>> s.toInt64).toInt = (B * M.toInt + C.toInt) / 2 ^ s := by
  have hB' : B.toInt64.toInt = B := Int64.toInt_ofNat_of_lt hB
  have hm : (B.toInt64 * M).toInt = B * M.toInt := by
    rw [Int64.toInt_mul_of_lt (by rw [hB']; lia) (by rw [hB']; lia), hB']
  rw [Nat.toInt64, Int64.toInt_shiftRight_ofNat _ hs,
    Int64.toInt_add_of_lt (by rw [hm]; lia) (by rw [hm]; lia), hm, Int.shiftRight_eq_div_pow]
  push_cast; rfl

theorem toInt_ite_neg_toInt64 {e : ExactEnd} (hm : e.m.toNat < 2 ^ 63) :
    (if e.neg then -e.m.toInt64 else e.m.toInt64).toInt =
      (if e.neg then -1 else 1) * (e.m.toNat : ℤ) := by
  have h := UInt64.toInt_toInt64_of_lt hm
  split_ifs
  · rw [Int64.toInt_neg_of_lt (by rw [h]; lia), h]; ring
  · rw [h]; ring

theorem natCast_mul_value {e : ExactEnd} (B : ℕ) :
    (B : ℚ) * e.value = (((B : ℤ) * ((if e.neg then -1 else 1) * (e.m.toNat : ℤ)) : ℤ) : ℚ) /
      2 ^ e.s := by
  simp only [ExactEnd.value]
  split_ifs <;> push_cast <;> ring

/-- The form `(b M + C) >> s` of an end with `C ≥ 0`, without overflow for `b` up to the largest
denominator by the guard of `end_form`, on the `long`s: the floor of `(b (±m) + C) / 2 ^ s`. -/
theorem toInt_form {e : ExactEnd} {B bHigh : ℕ} {C : Int64} (hs : e.s < 64) (hB1 : 1 ≤ B)
    (hB : B ≤ bHigh) (hB63 : B < 2 ^ 63) (hC : 0 ≤ C.toInt)
    (hg : (e.m.toNat : ℤ) * bHigh + C.toInt ≤ 2 ^ 63 - 1) :
    ((B.toInt64 * (if e.neg then -e.m.toInt64 else e.m.toInt64) + C) >>> e.s.toInt64).toInt =
      (B * ((if e.neg then -1 else 1) * e.m.toNat) + C.toInt) / 2 ^ e.s := by
  have hm : e.m.toNat < 2 ^ 63 := by
    have := Nat.mul_le_mul_left e.m.toNat (hB1.trans hB); lia
  have hBm : (B : ℤ) * e.m.toNat ≤ e.m.toNat * bHigh := by
    rw [mul_comm]; exact_mod_cast Nat.mul_le_mul_left _ hB
  have hM := toInt_ite_neg_toInt64 hm
  rw [toInt_mul_add_shiftRight hB63 hs, hM]
  all_goals rw [hM]
  all_goals split_ifs <;> lia

/-- The guard `m ≤ (LONG_MAX - c) / b_high` of `end_form` on the `long`s: `m b_high + c` is a
`long`. -/
theorem mul_add_le_of_le_toUInt64_div {m : UInt64} {c : Int64} {bHigh : ℕ} (hc0 : 0 ≤ c.toInt)
    (hb : 0 < bHigh) (hb63 : bHigh < 2 ^ 63)
    (h : m ≤ ((9223372036854775807 - c) / bHigh.toInt64).toUInt64) :
    (m.toNat : ℤ) * bHigh + c.toInt ≤ 2 ^ 63 - 1 := by
  have hct := c.toInt_lt
  have hK : (9223372036854775807 : Int64).toInt = 2 ^ 63 - 1 := by decide
  have hs : (9223372036854775807 - c).toInt = 2 ^ 63 - 1 - c.toInt := by
    rw [Int64.toInt_sub_of_lt (by rw [hK]; lia) (by rw [hK]; lia), hK]
  have hd := Int64.toInt_div_ofNat (a := 9223372036854775807 - c) (by rw [hs]; lia) hb63
  rw [hs] at hd
  have h1 : 0 ≤ (2 ^ 63 - 1 - c.toInt) / (bHigh : ℤ) := Int.ediv_nonneg (by lia) (by lia)
  rw [UInt64.le_iff_toNat_le] at h
  have h' : (m.toNat : ℤ) ≤ (2 ^ 63 - 1 - c.toInt) / bHigh := by
    rw [← hd, ← Int64.natCast_toNat_toUInt64 (by rw [hd]; exact h1)]; exact_mod_cast h
  lia [(Int.le_ediv_iff_mul_le (by lia)).mp h']

/-- The form `(b (±m) + 2 ^ s - 1) >> s` of a lower end with `s < 64` and the guard of `end_form`,
clamped to `-H, …, H + 1`, is the least numerator of the end. -/
theorem lowNumerator_of_form {e : ExactEnd} {H bHigh B : ℕ} (hH : H < 2 ^ 63) (hbH : bHigh ≤ H)
    (hB1 : 1 ≤ B) (hB : B ≤ bHigh) (hs : e.s < 64)
    (hg : e.m ≤ ((9223372036854775807 - (((1 : UInt64) <<< e.s.toUInt64) - 1).toInt64) /
      bHigh.toInt64).toUInt64) :
    max (-(H : ℤ)) (min ((B.toInt64 * (if e.neg then -e.m.toInt64 else e.m.toInt64) +
        (((1 : UInt64) <<< e.s.toUInt64) - 1).toInt64) >>> e.s.toInt64).toInt (H + 1)) =
      lowNumerator B H (e.value : WithBotTop ℚ) := by
  have hc := UInt64.toInt_toInt64_one_shiftLeft_sub_one hs
  have hC : 0 ≤ ((((1 : UInt64) <<< e.s.toUInt64) - 1).toInt64).toInt := by
    rw [hc]; lia [Nat.one_le_two_pow (n := e.s)]
  rw [toInt_form hs hB1 hB (by lia) hC (mul_add_le_of_le_toUInt64_div hC (by lia) (by lia) hg), hc,
    lowNumerator, WithBotTop.rec_coe, natCast_mul_value,
    show (2 : ℚ) ^ e.s = ((2 ^ e.s : ℕ) : ℚ) by push_cast; rfl,
    Rat.ceil_intCast_div_natCast_eq_add_sub_one_div _ (Nat.two_pow_pos e.s)]
  push_cast [add_sub_assoc]
  rfl

theorem toInt_const_shiftRight_zero {B : ℕ} (hB : B < 2 ^ 63) {C : Int64} :
    ((B.toInt64 * 0 + C) >>> (0 : ℕ).toInt64).toInt = C.toInt := by
  have := C.toInt_lt; have := C.le_toInt
  rw [toInt_mul_add_shiftRight hB (by decide)] <;> simp <;> lia

/-- An end whose magnitude, rounded down, `exact_scale` at `b = 1` finds at least `H`, has
`⌊b |x|⌋ ≥ H` for every denominator `b ≥ 1`. -/
theorem le_mul_div_of_le_exactScale_one {e : ExactEnd} {lower : Bool} (he : IsEnd e lower)
    (hr : (lower != e.neg) = false) {H B : ℕ} (hH : H < 2 ^ 63) (hB1 : 1 ≤ B)
    (ht : H.toInt64.toUInt64 ≤ exactScale 1 e) : H ≤ B * e.m.toNat / 2 ^ e.s := by
  have h1 := toNat_exactScale_of_isEnd he (B := 1) (by decide)
  simp only [hr, Bool.false_eq_true, ↓reduceIte, Nat.one_mul] at h1
  rw [show (1 : Int64) = (1 : ℕ).toInt64 from rfl, UInt64.le_iff_toNat_le,
    Nat.toNat_toUInt64_toInt64 hH, h1] at ht
  lia [Nat.div_le_div_right (c := 2 ^ e.s) (Nat.le_mul_of_pos_left e.m.toNat hB1)]

/-- The form `(0, -H, 0)` of a lower end `x ≤ -H`, clamped, is the least numerator `-H`. -/
theorem lowNumerator_of_le_exactScale_one {e : ExactEnd} (he : IsEnd e true) {H B : ℕ}
    (hH : H < 2 ^ 63) (hB1 : 1 ≤ B) (hB63 : B < 2 ^ 63) (hn : e.neg = true)
    (ht : H.toInt64.toUInt64 ≤ exactScale 1 e) :
    max (-(H : ℤ)) (min ((B.toInt64 * 0 + -H.toInt64) >>> (0 : ℕ).toInt64).toInt (H + 1)) =
      lowNumerator B H (e.value : WithBotTop ℚ) := by
  have h := le_mul_div_of_le_exactScale_one he (by simp [hn]) hH hB1 (B := B) ht
  rw [toInt_const_shiftRight_zero hB63,
    Int64.toInt_neg_of_lt (by rw [Int64.toInt_ofNat_of_lt hH]; lia), Int64.toInt_ofNat_of_lt hH,
    lowNumerator_value_of_neg hn]
  generalize B * e.m.toNat / 2 ^ e.s = Q at h ⊢
  lia

/-- The form of a lower end, clamped to `-H, …, H + 1`, is the least numerator of the end: the
constant `-H` for an end `x ≤ -H`, which `exact_scale` at `b = 1` finds, and `⌈b x⌉` for an end
with a short mantissa. -/
theorem lowNumerator_of_endForm {e : ExactEnd} (he : IsEnd e true) {H bHigh B : ℕ}
    (hH : H < 2 ^ 63) (hbH : bHigh ≤ H) (hB1 : 1 ≤ B) (hB : B ≤ bHigh) {f : Int64 × Int64 × ℕ}
    (hf : endForm e true H.toInt64 bHigh.toInt64 = some f) :
    max (-(H : ℤ)) (min ((B.toInt64 * f.1 + f.2.1) >>> f.2.2.toInt64).toInt (H + 1)) =
      lowNumerator B H (e.value : WithBotTop ℚ) := by
  simp only [endForm] at hf
  by_cases h1 : (e.neg == true && decide (H.toInt64.toUInt64 ≤ exactScale 1 e)) = true
  · simp only [h1, ↓reduceIte, Option.some.injEq] at hf
    subst hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    exact lowNumerator_of_le_exactScale_one he hH hB1 (by lia) h1.1 h1.2
  simp only [h1, Bool.false_eq_true, ↓reduceIte, Bool.true_and] at hf
  by_cases hs : e.s < 64
  · by_cases hg : e.m ≤ ((9223372036854775807 - (((1 : UInt64) <<< e.s.toUInt64) - 1).toInt64) /
        bHigh.toInt64).toUInt64
    · simp only [hs, hg, decide_true, Bool.and_self, ↓reduceIte, Option.some.injEq] at hf
      subst hf
      exact lowNumerator_of_form hH hbH hB1 hB hs hg
    · simp only [hs, hg, decide_true, decide_false, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte, reduceCtorEq] at hf
  · simp [hs] at hf

/-- The form `(b (±m)) >> s` of an upper end with `s < 64` and the guard of `end_form`, clamped to
`-H - 1, …, H`, is the largest numerator of the end. -/
theorem highNumerator_of_form {e : ExactEnd} {H bHigh B : ℕ} (hH : H < 2 ^ 63) (hbH : bHigh ≤ H)
    (hB1 : 1 ≤ B) (hB : B ≤ bHigh) (hs : e.s < 64)
    (hg : e.m ≤ ((9223372036854775807 - 0) / bHigh.toInt64).toUInt64) :
    max (-(H : ℤ) - 1) (min ((B.toInt64 * (if e.neg then -e.m.toInt64 else e.m.toInt64) + 0) >>>
        e.s.toInt64).toInt H) = highNumerator B H (e.value : WithBotTop ℚ) := by
  rw [toInt_form hs hB1 hB (by lia) (by simp) (mul_add_le_of_le_toUInt64_div (by simp) (by lia)
    (by lia) hg), Int64.toInt_zero, add_zero, highNumerator, WithBotTop.rec_coe, natCast_mul_value,
    show (2 : ℚ) ^ e.s = ((2 ^ e.s : ℕ) : ℚ) by push_cast; rfl, Rat.floor_intCast_div_natCast]
  push_cast
  rfl

/-- The form `(0, H, 0)` of an upper end `x ≥ H`, clamped, is the largest numerator `H`. -/
theorem highNumerator_of_le_exactScale_one {e : ExactEnd} (he : IsEnd e false) {H B : ℕ}
    (hH : H < 2 ^ 63) (hB1 : 1 ≤ B) (hB63 : B < 2 ^ 63) (hn : e.neg = false)
    (ht : H.toInt64.toUInt64 ≤ exactScale 1 e) :
    max (-(H : ℤ) - 1) (min ((B.toInt64 * 0 + H.toInt64) >>> (0 : ℕ).toInt64).toInt H) =
      highNumerator B H (e.value : WithBotTop ℚ) := by
  have h := le_mul_div_of_le_exactScale_one he (by simp [hn]) hH hB1 (B := B) ht
  rw [toInt_const_shiftRight_zero hB63, Int64.toInt_ofNat_of_lt hH,
    highNumerator_value_of_not_neg hn]
  generalize B * e.m.toNat / 2 ^ e.s = Q at h ⊢
  lia

/-- The form of an upper end, clamped to `-H - 1, …, H`, is the largest numerator of the end: the
constant `H` for an end `x ≥ H`, which `exact_scale` at `b = 1` finds, and `⌊b x⌋` for an end with
a short mantissa. -/
theorem highNumerator_of_endForm {e : ExactEnd} (he : IsEnd e false) {H bHigh B : ℕ}
    (hH : H < 2 ^ 63) (hbH : bHigh ≤ H) (hB1 : 1 ≤ B) (hB : B ≤ bHigh) {f : Int64 × Int64 × ℕ}
    (hf : endForm e false H.toInt64 bHigh.toInt64 = some f) :
    max (-(H : ℤ) - 1) (min ((B.toInt64 * f.1 + f.2.1) >>> f.2.2.toInt64).toInt H) =
      highNumerator B H (e.value : WithBotTop ℚ) := by
  simp only [endForm] at hf
  by_cases h1 : (e.neg == false && decide (H.toInt64.toUInt64 ≤ exactScale 1 e)) = true
  · simp only [h1, ↓reduceIte, Option.some.injEq, Bool.false_eq_true] at hf
    subst hf
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h1
    exact highNumerator_of_le_exactScale_one he hH hB1 (by lia) h1.1 h1.2
  simp only [h1, Bool.false_eq_true, ↓reduceIte, Bool.false_and] at hf
  by_cases hs : e.s < 64
  · by_cases hg : e.m ≤ ((9223372036854775807 - 0) / bHigh.toInt64).toUInt64
    · simp only [hs, hg, decide_true, Bool.and_self, ↓reduceIte, Option.some.injEq] at hf
      subst hf
      exact highNumerator_of_form hH hbH hB1 hB hs hg
    · simp only [hs, hg, decide_true, decide_false, Bool.and_false, Bool.false_eq_true,
        ↓reduceIte, reduceCtorEq] at hf
  · simp [hs] at hf

/-- The bits of `interval_bits` on an interval taken inline, from the values `lo ≤ H` and
`hi ≥ -H` of the forms of its ends clipped to `-H, …, H`: those of the least numerator `L` and the
largest numerator `U`. -/
theorem toInt_numeratorsToBits_clip {lo hi : Int64} {H : ℕ} (hH : H ≤ 2 ^ 63 - 65) {L U : ℤ}
    (hL : max (-(H : ℤ)) (min lo.toInt (H + 1)) = L) (hU : max (-(H : ℤ) - 1) (min hi.toInt H) = U)
    (h1 : lo.toInt ≤ H) (h2 : -(H : ℤ) ≤ hi.toInt) {cl : NumClass} (hcl : cl.WF) :
    (numeratorsToBits (if lo < -H.toInt64 then -H.toInt64 else lo)
        (if H.toInt64 < hi then H.toInt64 else hi) cl false).1.toInt =
          -((cl.a0 - max L (-H)) / 2 ^ cl.k) ∧
      (numeratorsToBits (if lo < -H.toInt64 then -H.toInt64 else lo)
        (if H.toInt64 < hi then H.toInt64 else hi) cl false).2.toInt =
          (min U H - cl.a0) / 2 ^ cl.k := by
  have hHt : H.toInt64.toInt = H := Int64.toInt_ofNat_of_lt (by lia)
  have hHn : (-H.toInt64).toInt = -H := by rw [Int64.toInt_neg_of_lt (by lia), hHt]
  have hl : (if lo < -H.toInt64 then -H.toInt64 else lo).toInt = L := by
    split_ifs with h <;> rw [Int64.lt_iff_toInt_lt, hHn] at h
    · rw [hHn]; lia
    · lia
  have hh : (if H.toInt64 < hi then H.toInt64 else hi).toInt = U := by
    split_ifs with h <;> rw [Int64.lt_iff_toInt_lt, hHt] at h
    · rw [hHt]; lia
    · lia
  have := hcl.a0_lt_sixty_four
  obtain ⟨e1, e2⟩ := toInt_numeratorsToBits_false hcl (by rw [hl]; lia) (by rw [hh]; lia)
  rw [e1, e2, hl, hh, max_eq_left (by lia), min_eq_left (by lia)]
  exact ⟨rfl, rfl⟩

theorem IntervalBounds.Represents.of_forall {bd : IntervalBounds} {b H : ℕ} {lo hi : ℤ}
    (h : ∀ cl : NumClass, cl.WF → ((intervalBits b.toInt64 bd H.toInt64 cl).1 = 2 → (H : ℤ) < lo) ∧
      ((intervalBits b.toInt64 bd H.toInt64 cl).1 = 1 → hi < -H) ∧
      ((intervalBits b.toInt64 bd H.toInt64 cl).1 ≠ 1 →
        (intervalBits b.toInt64 bd H.toInt64 cl).1 ≠ 2 →
        (intervalBits b.toInt64 bd H.toInt64 cl).2.1.toInt = -((cl.a0 - max lo (-H)) / 2 ^ cl.k) ∧
          (intervalBits b.toInt64 bd H.toInt64 cl).2.2.toInt = (min hi H - cl.a0) / 2 ^ cl.k)) :
    bd.Represents b H lo hi :=
  ⟨fun cl hcl ↦ (h cl hcl).1, fun cl hcl ↦ (h cl hcl).2.1, fun cl hcl ↦ (h cl hcl).2.2⟩

/-- The bounds `bd` of an interval taken inline give the range `L, …, U` of the numerators, from the
forms of its ends clamped to the least numerator `L` and the largest numerator `U`: in
`interval_bits`, the code `2` only above `H`, the code `1` only below `-H`, and otherwise the bits
of `L, …, U`. -/
theorem IntervalBounds.represents_of_fast {bd : IntervalBounds} (hfast : bd.fast = true) {B H : ℕ}
    (hH : H ≤ 2 ^ 63 - 65) {L U : ℤ}
    (hL : max (-(H : ℤ)) (min ((B.toInt64 * bd.lM + bd.lC) >>> bd.lsh.toInt64).toInt (H + 1)) = L)
    (hU : max (-(H : ℤ) - 1) (min ((B.toInt64 * bd.uM + bd.uC) >>> bd.ush.toInt64).toInt H) = U) :
    bd.Represents B H L U := by
  refine .of_forall fun cl hcl ↦ ?_
  have hHt : H.toInt64.toInt = H := Int64.toInt_ofNat_of_lt (by lia)
  have hHn : (-H.toInt64).toInt = -H := by rw [Int64.toInt_neg_of_lt (by lia), hHt]
  simp only [intervalBits, hfast, ↓reduceIte]
  generalize (B.toInt64 * bd.lM + bd.lC) >>> bd.lsh.toInt64 = lo at hL
  generalize (B.toInt64 * bd.uM + bd.uC) >>> bd.ush.toInt64 = hi at hU
  by_cases h1 : H.toInt64 < lo
  · simp only [h1, ↓reduceIte]
    rw [Int64.lt_iff_toInt_lt, hHt] at h1
    exact ⟨fun _ ↦ by lia, nofun, fun _ h ↦ absurd rfl h⟩
  by_cases h2 : hi < -H.toInt64
  · simp only [h1, h2, ↓reduceIte]
    rw [Int64.lt_iff_toInt_lt, hHn] at h2
    exact ⟨nofun, fun _ ↦ by lia, fun h _ ↦ absurd rfl h⟩
  simp only [h1, h2, ↓reduceIte]
  rw [Int64.lt_iff_toInt_lt, hHt] at h1
  rw [Int64.lt_iff_toInt_lt, hHn] at h2
  exact ⟨nofun, nofun, fun _ _ ↦ toInt_numeratorsToBits_clip hH hL hU (by lia) (by lia) hcl⟩

/-- The bounds of the search interval `i` that `Ratpoints.Sieve.exactBounds` makes for the height
bound `height` and the largest denominator `bHigh`: the body of its loop. -/
def intervalBoundsOf (height bHigh : Int64) (i : Double × Double) : IntervalBounds :=
  let low := Id.run (exactEnd i.1 true)
  let up := Id.run (exactEnd i.2 false)
  match (if height ≤ 9223372036854775807 - 64 then
      (endForm low true height bHigh).bind fun lf ↦ (endForm up false height bHigh).map (lf, ·)
      else none) with
  | some ((lM, lC, lsh), (uM, uC, ush)) => { lM, lC, uM, uC, lsh, ush, fast := true, low, up }
  | none =>
    { lM := 0, lC := 0, uM := 0, uC := -9223372036854775808, lsh := 0, ush := 0, fast := false,
      low, up }

theorem toList_run_exactBounds (dom : List (Double × Double)) (height bHigh : Int64) :
    (Id.run (exactBounds dom height bHigh)).toList = dom.map (intervalBoundsOf height bHigh) := by
  have : Id.run (exactBounds dom height bHigh) = Id.run (forIn dom #[] fun x s ↦
      pure (ForInStep.yield (s.push (intervalBoundsOf height bHigh x)))) := rfl
  rw [this, List.forIn_pure_yield_eq_foldl, Id.run_pure, List.foldl_push_eq_append]
  simp

/-- An interval that is not taken inline has the forms of an empty one, and `interval_bits` goes to
`interval_bits_exact` for it. -/
theorem intervalBits_eq_intervalBitsExact (low up : ExactEnd) {B H : ℕ} (hB : B < 2 ^ 63)
    (hH : H < 2 ^ 63) (cl : NumClass) :
    intervalBits B.toInt64 ⟨0, 0, 0, -9223372036854775808, 0, 0, false, low, up⟩ H.toInt64 cl =
      intervalBitsExact B.toInt64 ⟨0, 0, 0, -9223372036854775808, 0, 0, false, low, up⟩ H.toInt64
        cl := by
  have hHt : H.toInt64.toInt = H := Int64.toInt_ofNat_of_lt hH
  have h1 : ¬ H.toInt64 < (B.toInt64 * 0 + 0) >>> (0 : ℕ).toInt64 := by
    rw [Int64.lt_iff_toInt_lt, toInt_const_shiftRight_zero hB, hHt, Int64.toInt_zero]; lia
  have h2 : (B.toInt64 * 0 + -9223372036854775808) >>> (0 : ℕ).toInt64 < -H.toInt64 := by
    rw [Int64.lt_iff_toInt_lt, toInt_const_shiftRight_zero hB,
      Int64.toInt_neg_of_lt (a := H.toInt64) (by rw [hHt]; lia), hHt,
      show (-9223372036854775808 : Int64).toInt = -2 ^ 63 by decide]
    lia
  simp only [intervalBits, h1, h2, ↓reduceIte, Bool.false_eq_true]

-- The forms of both ends of an interval taken inline, for a height bound `H ≤ 2 ^ 63 - 65`.
private theorem forms_of_eq_some {low up : ExactEnd} {H bHigh : ℕ} (hH : H < 2 ^ 63)
    {f : (Int64 × Int64 × ℕ) × Int64 × Int64 × ℕ}
    (h : (if H.toInt64 ≤ 9223372036854775807 - 64 then
      (endForm low true H.toInt64 bHigh.toInt64).bind fun lf ↦
        (endForm up false H.toInt64 bHigh.toInt64).map (lf, ·) else none) = some f) :
    H ≤ 2 ^ 63 - 65 ∧ endForm low true H.toInt64 bHigh.toInt64 = some f.1 ∧
      endForm up false H.toInt64 bHigh.toInt64 = some f.2 := by
  split_ifs at h with hK
  obtain ⟨lf, hfl, hm⟩ := Option.bind_eq_some_iff.mp h
  obtain ⟨uf, hfu, rfl⟩ := Option.map_eq_some_iff.mp hm
  rw [Int64.le_iff_toInt_le, Int64.toInt_ofNat_of_lt hH,
    show (9223372036854775807 - 64 : Int64).toInt = 2 ^ 63 - 65 by decide] at hK
  exact ⟨by lia, hfl, hfu⟩

/-- The bounds of a search interval `[l, u]` give, for the denominator `1 ≤ B ≤ bHigh ≤ H < 2 ^ 63`,
the range of the numerators `⌈B l⌉, …, ⌊B u⌋` of the values of `exact_end`, clamped, in both
paths of `interval_bits`. -/
theorem represents_intervalBoundsOf (l u : Double) {H bHigh B : ℕ} (hH : H < 2 ^ 63)
    (hbH : bHigh ≤ H) (hB1 : 1 ≤ B) (hB : B ≤ bHigh) :
    (intervalBoundsOf H.toInt64 bHigh.toInt64 (l, u)).Represents B H
      (lowNumerator B H ((Id.run (exactEnd l true)).value : WithBotTop ℚ))
      (highNumerator B H ((Id.run (exactEnd u false)).value : WithBotTop ℚ)) := by
  have hl := isEnd_run_exactEnd l true
  have hu := isEnd_run_exactEnd u false
  simp only [intervalBoundsOf]
  generalize Id.run (exactEnd l true) = low at hl ⊢
  generalize Id.run (exactEnd u false) = up at hu ⊢
  split
  · rename_i lM lC lsh uM uC ush hfs
    obtain ⟨hK, hfl, hfu⟩ := forms_of_eq_some hH hfs
    have hL := lowNumerator_of_endForm hl hH hbH hB1 hB hfl
    have hU := highNumerator_of_endForm hu hH hbH hB1 hB hfu
    exact IntervalBounds.represents_of_fast (bd := ⟨lM, lC, uM, uC, lsh, ush, true, low, up⟩) rfl hK
      hL hU
  · exact .of_forall fun cl hcl ↦ by
      rw [intervalBits_eq_intervalBitsExact low up (by lia) hH cl]
      exact toInt_intervalBitsExact hl hu (by lia) hH hcl

theorem areSearchIntervals_domainValues {dom : List (Double × Double)}
    (hdom : IntervalsWF (domainBits dom)) : AreSearchIntervals (domainValues dom) := by
  have := hdom.2
  simp only [domainBits, List.map_map] at this
  exact this

/-- The bounds of well-formed search intervals for `H < 2 ^ 63` and the largest denominator
`bHigh ≤ H` give, for every denominator `1 ≤ b ≤ bHigh`, the ranges of the numerators of the
intervals (`Ratpoints.Sieve.numeratorRanges`). -/
theorem rangesFor_run_exactBounds {dom : List (Double × Double)}
    (hdom : IntervalsWF (domainBits dom)) {H bHigh : ℕ} (hH : H < 2 ^ 63) (hbHigh : bHigh ≤ H)
    {b : ℕ} (hb : 0 < b) (hbb : b ≤ bHigh) :
    RangesFor (Id.run (exactBounds dom H.toInt64 bHigh.toInt64)) b H
      (numeratorRanges b H (domainValues dom)) := by
  have hD := areSearchIntervals_domainValues hdom
  refine ⟨?_, ?_, le_add_one_of_mem_numeratorRanges hD.1 b H, pairwise_numeratorRanges hD hb H⟩
  · rw [← Array.length_toList, toList_run_exactBounds]; simp [numeratorRanges]
  · rw [toList_run_exactBounds]
    simp only [numeratorRanges, domainValues, List.map_map, List.zip_map', List.mem_map]
    rintro _ ⟨⟨l, u⟩, hi, rfl⟩
    have hn := hdom.1 (l.bits, u.bits) (List.mem_map_of_mem hi)
    rw [← Double.isNaN_eq_false_iff, ← Double.isNaN_eq_false_iff] at hn
    have hlo := (lowNumerator_eq_and_highNumerator_eq_run_exactEnd hn.1 true hb (by lia) hH).1
    have hhi := (lowNumerator_eq_and_highNumerator_eq_run_exactEnd hn.2 false hb (by lia) hH).2
    simp only [Function.comp_apply]
    rw [hlo, hhi]
    exact represents_intervalBoundsOf l u hH hbHigh hb hbb

end Sieve

end Ratpoints

end
