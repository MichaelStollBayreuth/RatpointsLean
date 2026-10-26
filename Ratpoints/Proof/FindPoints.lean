/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Choice
public import Ratpoints.Proof.Region
public import Ratpoints.Proof.SearchDens
public import Ratpoints.Proof.Setup

import Ratpoints.Mathlib.Data.List.Nodup
import Ratpoints.Proof.Bounds
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Correction
import Ratpoints.Proof.Delivery
import Ratpoints.Proof.Denominators
import Ratpoints.Proof.Params
import Ratpoints.Proof.Sieve
import Ratpoints.Proof.Tables
import Ratpoints.Proof.TwoAdic
import Std.Tactic.Do

/-!
# The search delivers the points of a sound sieve

The search of the polynomial that the set-up hands on delivers to the callback, for every value of
the options of the sieve, the points at infinity followed, for the denominators from `bLow` to
`bHigh` that the loop of its shape visits in its order (`Ratpoints.searchDens`), by the points of
the check with the flags of the search of the numerators `a` with `a / b` in the search intervals
over the values of their ends (`Ratpoints.InIntervals`) that a test of the sieve lets through
(`Ratpoints.searchList`), none when the Sturm step has left no interval, and it returns when the
callback stops the search; the test, the sieve with the moduli of the block of each denominator,
depends neither on the callback nor on the flags of the output, but on the search intervals, which
the estimate of the run reads, and with it the choice of the moduli and the decisions of the
correction, and it lets the numerator of every point through (`Ratpoints.IsSoundTest`), also when
the search takes one of its exits, where the curve has no points
(`Ratpoints.exists_isSoundTest_run_searchPoints`), for well-formed search intervals. So the search
with a callback delivers the list that the search with the appending callback returns
(`Ratpoints.run_searchPoints_eq_deliver`), and without `RATPOINTS_NO_CHECK` that list is the
brute-force reference over the candidate `(1, 0)` and the denominators of the search with the
numerators in the search intervals, mapped by `Ratpoints.Sieve.swapPoint` when the flag of the
reversal is set, without the points with `y < 0` under `RATPOINTS_NO_Y`
(`Ratpoints.searchList_of_noCheck_eq_false`): the points of the reference with the denominators from
`bLow` to `bHigh` in another order, except where the shape visits the denominators in increasing
order, every shape but that of the divisors of the leading coefficient times squares
(`Ratpoints.perm_filter_bruteForce_append_flatMap_searchDens`), filtered by the search intervals;
without the flag of the reversal they lie in the search region
(`Ratpoints.mem_region_of_mem_searchList`). What `Ratpoints.findPoints` and
`Ratpoints.findPointsWith` return, and their refusals, are in `Ratpoints.Proof.Output`.

## Main definitions

* `Ratpoints.searchList`, `Ratpoints.IsSoundTest`: the points that the search delivers for a test of
  the numerators, and a test that lets the numerator of every point through.
* `Ratpoints.Sieve.IsSoundRun`: what the run of the search needs of its arguments.
* `Ratpoints.SievingInfoEntries`, `Ratpoints.SievingInfoInvariant`: what the loop over the moduli of
  `Ratpoints.sievingInfoOf`, the sieve entries of given moduli, which the search does not call, has
  made before a return, and its invariant.
* `Ratpoints.IsSievingInfoOf`: what the result of `Ratpoints.sievingInfoOf` gives a run.

## Main statements

* `Ratpoints.searchList_of_noCheck_eq_false`: without `RATPOINTS_NO_CHECK`, the points that the
  search delivers for a sound test are those of the brute-force reference with the numerators in
  the search intervals, mapped after a reversal, without those with `y < 0` under `RATPOINTS_NO_Y`.
* `Ratpoints.exists_eq_of_mem_searchList_of_noCheck`, `Ratpoints.nodup_searchList_of_noCheck`:
  under `RATPOINTS_NO_CHECK`, the search delivers distinct triples `(x, 0, z)` of normalized pairs
  `(x, z)` of height at most `H` (`Ratpoints.IsNormalizedPair`), whatever the test;
  `Ratpoints.map_searchList_sublist`: the points that it delivers without `RATPOINTS_NO_CHECK` and
  with `RATPOINTS_NO_Y`, with `y` replaced by `0`, are a sublist of them, for the same test.
* `Ratpoints.mem_region_of_mem_searchList`, `Ratpoints.searchList_nil`: without the flag of the
  reversal, the points that the search delivers lie in the search region; for no search interval
  they are the points at infinity.
* `Ratpoints.exists_isSoundTest_run_sieveRun`: the run of the shape that the search chooses, with
  sound arguments, a well-formed first decision and the bounds of well-formed search intervals,
  delivers the points of the numerators in the search intervals that a sound test lets through.
* `Ratpoints.sievingInfoOf_spec`: for well-formed parameters, the sieve entries that
  `Ratpoints.sievingInfoOf` makes are those of the moduli, in their order, are sound, have the
  fields that the packing reads and the tables of inverses of their factors, and hold the
  reciprocals of their moduli, which it returns in the order of the entries, those of the third
  stage having the shape that it needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), its forbidden
  divisors are among those that the loops of the tables and of the further primes may record, and
  the store of the tables of rows that it returns fits the entries
  (`Ratpoints.Sieve.RowStore.Fits`); when it returns none, the curve has no points.
* `Ratpoints.run_searchPoints_flags`: the bits of the flags and the search intervals that the
  search writes back do not depend on the callback.
* `Ratpoints.exists_isSoundTest_run_searchPoints`: for `1 ≤ H < 2 ^ 63` and the degree of the
  polynomial, there is a sound test for which the search, with any callback, flags and delivery
  whose flag of the stop is clear and the print channel that prints nothing, gives the data and the
  count of the delivery of the points of `Ratpoints.searchList` for the denominators from
  `bLow ≥ 1` to `bHigh ≤ H` and the values of well-formed search intervals, none when the Sturm step
  has left no interval.
* `Ratpoints.run_searchPoints_eq_deliver`: the search with a callback gives the data and the count
  of the delivery of the list of the search with the appending callback;
  `Ratpoints.exists_isSoundTest_run_searchPoints_appendPoint`: the search with the appending
  callback gives the list of `Ratpoints.searchList`, for every choice of the flags.

## Proof

The run delivers, over the denominators of the listing of its shape that pass its tests, the points
of the numerators that pass the class word and survive the entries of the first three stages of the
decision of the block of the denominator (`Ratpoints.Sieve.exists_run_sieveRun_eq_deliver`), the
numerators of each denominator lying in the ranges that the bounds of well-formed search intervals
give for it (`Ratpoints.Sieve.rangesFor_run_exactBounds`), which are those with `a / b` in the
intervals (`Ratpoints.Sieve.inRanges_numeratorRanges`). This test is sound: every numerator of a
point passes the word of the class of its denominator and survives the sieve entries, when they are
sound (`Ratpoints.Sieve.classBit_and_survives_of_ne_nil`), and every denominator of a point passes
the filter and the tests of the shape that `Ratpoints.Sieve.runSetup` chooses: the squares for odd
degree and `|c_d| = 1` (`Ratpoints.isSquare_of_sq_eq_binaryForm_of_odd`,
`Ratpoints.Sieve.squaresDens_eq_filter`), the divisors with their valuation test
(`Ratpoints.Sieve.run_denInfoTest_of_sq_eq`), the words with the forbidden divisors and the Jacobi
test (`Ratpoints.Sieve.toList_run_wordsDens`, `Ratpoints.Sieve.getLsbD_denBits_and_all_of_sq_eq`,
`Ratpoints.Sieve.run_wordsTest_of_sq_eq`), and every denominator, by the class test
(`Ratpoints.Sieve.getElem!_twoAdic_ne_zero`). The result of the choice of the moduli is what the run
needs (`Ratpoints.sievingInfo_spec`), and when the choice exits, the curve has no points; when the
search takes the 2-adic exit, no class of the denominators admits a numerator, so that the curve has
no points either (`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`).

## Implementation notes

The search is proved by cases on the values of its components, the classes and the word of the
2-adic information, the 2-adic exit and the result of the choice of the moduli, which do not depend
on the callback or the flags, so that the test of the sieve is chosen after them; the data and the
count of the search along its paths, for these values, are proved with `vcgen`, which reads the
components through private specifications `⦃True⦄ x ⦃fun r ↦ r = Id.run x⦄`, so that its
verification conditions speak of their values. The contract of the sieve entries of given moduli
(`Ratpoints.sievingInfoOf_spec`), which the search does not call, is proved with `vcgen` as well,
with the loop invariant `Ratpoints.SievingInfoInvariant`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

open BruteForce Sieve

/-! ### The points at infinity and the points of a denominator -/

namespace BruteForce

theorem horner_scaledCoeffs_one_zero (c : List ℤ) (d : ℕ) :
    horner (scaledCoeffs c d 0) 1 = c.getD d 0 := by
  rw [horner_scaledCoeffs, Finset.sum_range_succ, Finset.sum_eq_zero fun k hk ↦ by
    rw [zero_pow (by lia [Finset.mem_range.mp hk])]; simp]
  simp

/-- The points at infinity of the brute-force reference, those of the candidate `(1, 0)`, are those
of the value `F(1, 0)`: `c_d` for even `d` and `0` for odd `d`. -/
theorem pointsOfDen_zero_singleton_one (c : List ℤ) (d : ℕ) :
    pointsOfDen c d 0 [1] = pointsAbove 1 0 (c.getD d 0 * if d % 2 = 1 then 0 else 1) := by
  simp [pointsOfDen_singleton, horner_scaledCoeffs_one_zero]

end BruteForce

namespace Sieve

theorem survives_of_mem_pointsOfDen {c : List ℤ} {entries : List SieveEntry}
    (hent : ∀ e ∈ entries, e.IsSound c) {b : ℕ} {xs : List ℤ} {q : ℤ × ℤ × ℤ}
    (hq : q ∈ pointsOfDen c (BruteForce.degree c) b xs) : survives entries b q.1 = true := by
  obtain ⟨x, y, z⟩ := q
  obtain ⟨-, rfl, hg, hy⟩ := mem_pointsOfDen_iff.mp hq
  rw [horner_scaledCoeffs_mul] at hy
  exact List.all_eq_true.mpr fun e he ↦ (hent e he).admits_of_sq_eq hg hy

/-- Without `RATPOINTS_NO_CHECK`, for odd `d` or `c_d ≠ 0`, the points at infinity that the search
delivers are those of the candidate `(1, 0)` of the brute-force reference, mapped by
`Ratpoints.Sieve.swapPoint` after a reversal, without the point with `y < 0` under
`RATPOINTS_NO_Y` (`Ratpoints.Sieve.pointsAtInfinityList_of_noCheck_eq_false`). -/
theorem pointsAtInfinityList_eq_filter_map_pointsOfDen {fl : CheckFlags} (hc : fl.noCheck = false)
    {c : List ℤ} {d : ℕ} (h : d % 2 = 1 ∨ c.getD d 0 ≠ 0) :
    pointsAtInfinityList c d fl = ((pointsOfDen c d 0 [1]).map
      (if fl.reversed then swapPoint else id)).filter fun p ↦ !fl.noY || 0 ≤ p.2.1 := by
  rw [pointsAtInfinityList_of_noCheck_eq_false hc h, pointsOfDen_zero_singleton_one]

/-- When the brute-force reference has no point at infinity, for even `d` and `c_d` not a square,
the search delivers none, whatever the flags. -/
theorem pointsAtInfinityList_eq_nil_of_pointsOfDen_eq_nil {c : List ℤ} {d : ℕ}
    (h : pointsOfDen c d 0 [1] = []) (fl : CheckFlags) :
    pointsAtInfinityList c d fl = [] := by
  rw [pointsOfDen_zero_singleton_one] at h
  refine ite_eq_right fun hs ↦ absurd h ?_
  by_cases hd : d % 2 = 1
  · simp [hd, pointsAbove]
  · simp only [hd, Bool.or_eq_true, beq_iff_eq, false_or, Setup.isSquare, Bool.and_eq_true,
      decide_eq_true_eq] at hs
    simp only [hd, ↓reduceIte, Int.mul_one, pointsAbove, hs, and_self]
    split_ifs <;> simp

/-- The class word of the denominator `b` and sound sieve entries let the numerator of every point
over `b` through (`Ratpoints.Sieve.classBit_twoAdic_of_sq_eq`,
`Ratpoints.Sieve.survives_of_mem_pointsOfDen`). -/
theorem classBit_and_survives_of_ne_nil {c : List ℤ} {entries : List SieveEntry}
    (hent : ∀ e ∈ entries, e.IsSound c) {b : ℕ} {a : ℤ} (h : pointsOfDen c (degree c) b [a] ≠ []) :
    classBit (Id.run (twoAdic c (degree c)))[b % 64]! a = true ∧
      survives entries b a = true := by
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hx, -, hg, hy⟩ := mem_pointsOfDen_iff.mp hq
  obtain rfl := List.mem_singleton.mp hx
  exact ⟨classBit_twoAdic_of_sq_eq hg (hy.trans (horner_scaledCoeffs_mul c _ _)),
    survives_of_mem_pointsOfDen hent hq⟩

end Sieve

/-! ### The points that the search delivers -/

/-- The points that the search of the polynomial with the coefficient list `c`, of its degree,
delivers for the height `H`, the denominators from `bLow` to `bHigh`, the search intervals `D` over
the values of their ends and the flags `fl` of the check, for the test `S b a` of the numerators
`a` over the denominators `b` of the search: the points at infinity
(`Ratpoints.Sieve.pointsAtInfinityList`), then, for the denominators `b` of the search in the order
of its loop (`Ratpoints.searchDens`), the points of the check with the flags
(`Ratpoints.Sieve.checkNumWith`) of the numerators `-H, …, H` with `a / b` in one of the intervals
(`Ratpoints.InIntervals`) that pass `S b`. For every value of the options of the sieve the test of
the sieve is one that lets the numerator of every point through (`Ratpoints.IsSoundTest`,
`Ratpoints.exists_isSoundTest_run_searchPoints`). -/
def searchList (c : List ℤ) (H bLow bHigh : ℕ) (D : List (WithBotTop ℚ × WithBotTop ℚ))
    (S : ℕ → ℤ → Bool) (fl : CheckFlags) : List (ℤ × ℤ × ℤ) :=
  pointsAtInfinityList c (degree c) fl ++ (searchDens c (degree c) bLow bHigh).flatMap
    fun b : ℕ ↦ ((numerators H).filter fun a : ℤ ↦ decide (InIntervals D (a / b)) && S b a).flatMap
      (checkNumWith (scaledCoeffs c (degree c) b) (if degree c % 2 = 1 then b else 1) b fl)

/-- A test `S b a` of the numerators `a` of `-H, …, H` over the denominators `b` from `bLow` to
`bHigh` of the search (`Ratpoints.searchDens`) that lets the numerator of every point of the curve
`y ^ 2 = F(x, z)` with the coefficient list `c` through. -/
def IsSoundTest (c : List ℤ) (H bLow bHigh : ℕ) (S : ℕ → ℤ → Bool) : Prop :=
  ∀ b ∈ searchDens c (degree c) bLow bHigh, ∀ a ∈ numerators H,
    pointsOfDen c (degree c) b [a] ≠ [] → S b a = true

/-- Without `RATPOINTS_NO_CHECK`, for a sound test and `c` of positive degree, the points that the
search delivers are those of the brute-force reference over the candidate `(1, 0)` and the
denominators of the search with the numerators `a` of `-H, …, H` with `a / b` in one of the search
intervals, in this order, mapped by `Ratpoints.Sieve.swapPoint` after a reversal, without those
with `y < 0` under `RATPOINTS_NO_Y`: a sound test leaves out only numerators without points
(`Ratpoints.BruteForce.pointsOfDen_filter_of_ne`). -/
theorem searchList_of_noCheck_eq_false {c : List ℤ} {H bLow bHigh : ℕ} {S : ℕ → ℤ → Bool}
    (hS : IsSoundTest c H bLow bHigh S) (hc : 0 < degree c)
    (D : List (WithBotTop ℚ × WithBotTop ℚ)) {fl : CheckFlags} (hn : fl.noCheck = false) :
    searchList c H bLow bHigh D S fl = ((pointsOfDen c (degree c) 0 [1] ++
      (searchDens c (degree c) bLow bHigh).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b
        ((numerators H).filter fun a : ℤ ↦ decide (InIntervals D (a / b)))).map
          (if fl.reversed then swapPoint else id)).filter fun p ↦ !fl.noY || 0 ≤ p.2.1 := by
  rw [searchList, pointsAtInfinityList_eq_filter_map_pointsOfDen hn
    (.inr (getD_degree_ne_zero_of_pos hc)), List.map_append, List.filter_append, List.map_flatMap,
    List.filter_flatMap]
  congr 1
  refine List.flatMap_congr fun b hb ↦ ?_
  rw [flatMap_checkNumWith_of_noCheck_eq_false hn, ← List.filter_filter, pointsOfDen_filter,
    pointsOfDen_filter_of_ne fun a ha hne ↦ hS b hb a ha hne, pointsOfDen_filter]

/-- With the test that lets no numerator through, and no point at infinity, the search delivers
nothing. -/
theorem searchList_false {c : List ℤ} (H bLow bHigh : ℕ) (D : List (WithBotTop ℚ × WithBotTop ℚ))
    {fl : CheckFlags} (h : pointsAtInfinityList c (degree c) fl = []) :
    searchList c H bLow bHigh D (fun _ _ ↦ false) fl = [] := by
  simp [searchList, h]

/-- The points that the search delivers are those of the search without the flag of the
reversal, mapped by `Ratpoints.Sieve.swapPoint` when it is set. -/
theorem searchList_eq_map (c : List ℤ) (H bLow bHigh : ℕ) (D : List (WithBotTop ℚ × WithBotTop ℚ))
    (S : ℕ → ℤ → Bool) (fl : CheckFlags) :
    searchList c H bLow bHigh D S fl = (searchList c H bLow bHigh D S
      { fl with reversed := false }).map (if fl.reversed then swapPoint else id) := by
  simp only [searchList, List.map_append, List.map_flatMap, ← pointsAtInfinityList_eq_map,
    ← checkNumWith_eq_map]

-- The map of the reversal keeps the triples `(x, 0, z)` of normalized pairs `(x, z)`.
private theorem exists_map_eq_of_isNormalizedPair {H : ℕ} {x z : ℤ} (h : IsNormalizedPair H x z)
    (rev : Bool) :
    ∃ x' z', (if rev then swapPoint else id) (x, 0, z) = (x', 0, z') ∧
      IsNormalizedPair H x' z' := by
  cases rev
  · exact ⟨x, z, rfl, h⟩
  · exact ⟨_, _, swapPoint_fst_zero_snd (x, 0, z), IsNormalizedPair.swapPoint h⟩

/-- Under `RATPOINTS_NO_CHECK`, the search with the denominators from `bLow ≥ 1` to `bHigh ≤ H`
delivers triples `(x, 0, z)` of pairs `(x, z)` of normalized points of height at most `H`
(`Ratpoints.IsNormalizedPair`): the survivors `(a, 0, b)` of the numerators `a` prime to the
denominators `b` of the search and the point `(1, 0, 0)` at infinity, mapped after a reversal
(`Ratpoints.IsNormalizedPair.swapPoint`). -/
theorem exists_eq_of_mem_searchList_of_noCheck {c : List ℤ} {H bLow bHigh : ℕ}
    {D : List (WithBotTop ℚ × WithBotTop ℚ)} {S : ℕ → ℤ → Bool} {fl : CheckFlags}
    (hc : fl.noCheck = true) (hH : 1 ≤ H) (hbLow : 1 ≤ bLow) (hbH : bHigh ≤ H)
    {q : ℤ × ℤ × ℤ} (hq : q ∈ searchList c H bLow bHigh D S fl) :
    ∃ x z, q = (x, 0, z) ∧ IsNormalizedPair H x z := by
  simp only [searchList, List.mem_append, List.mem_flatMap, List.mem_filter,
    mem_checkNumWith_of_noCheck hc] at hq
  rcases hq with hq | ⟨b, hb, a, ⟨ha, -⟩, hg, rfl⟩
  · rw [eq_of_mem_pointsAtInfinityList_of_noCheck hc hq]
    exact exists_map_eq_of_isNormalizedPair ⟨rfl, .inr ⟨rfl, rfl⟩, by simpa using hH, by lia⟩ _
  · have hb' := le_and_le_of_mem_searchDens hbLow hb
    exact exists_map_eq_of_isNormalizedPair ⟨hg, .inl (by lia), mem_numerators_iff.mp ha,
      by lia⟩ _

/-- Without the flag of the reversal, a point that the search delivers is at infinity, or its
denominator lies from `bLow ≥ 1` to `bHigh` and its `x / z` in one of the search intervals. -/
theorem mem_region_of_mem_searchList {c : List ℤ} {H bLow bHigh : ℕ}
    {D : List (WithBotTop ℚ × WithBotTop ℚ)} {S : ℕ → ℤ → Bool} {fl : CheckFlags}
    (hr : fl.reversed = false) (hbLow : 1 ≤ bLow) {q : ℤ × ℤ × ℤ}
    (hq : q ∈ searchList c H bLow bHigh D S fl) :
    q.2.2 = 0 ∨ bLow ≤ q.2.2 ∧ q.2.2 ≤ bHigh ∧ InIntervals D (q.1 / q.2.2) := by
  simp only [searchList, List.mem_append, List.mem_flatMap, List.mem_filter, Bool.and_eq_true,
    decide_eq_true_eq] at hq
  rcases hq with hq | ⟨b, hb, a, ⟨-, ha, -⟩, hq⟩
  · exact .inl (snd_snd_eq_zero_of_mem_pointsAtInfinityList hr hq)
  · obtain ⟨h1, h2⟩ := fst_eq_and_snd_snd_eq_of_mem_checkNumWith hr hq
    have := le_and_le_of_mem_searchDens hbLow hb
    refine .inr ⟨by lia, by lia, ?_⟩
    rw [h1, h2]
    exact_mod_cast ha

/-- Without search intervals, the search delivers its points at infinity only. -/
theorem searchList_nil (c : List ℤ) (H bLow bHigh : ℕ) (S : ℕ → ℤ → Bool) (fl : CheckFlags) :
    searchList c H bLow bHigh [] S fl = pointsAtInfinityList c (degree c) fl := by
  simp [searchList, InIntervals]

-- Under `RATPOINTS_NO_CHECK` and without the flag of the reversal, the survivors `(a, 0, b)` that
-- the search delivers are distinct pairs over distinct denominators `b ≥ 1`
-- (`Ratpoints.nodup_searchDens`), the point `(1, 0, 0)` at infinity apart.
private theorem nodup_searchList_of_noCheck_of_reversed_eq_false {c : List ℤ} {H bLow bHigh : ℕ}
    (hbLow : 1 ≤ bLow) (hb : 1 ≤ bHigh) (D : List (WithBotTop ℚ × WithBotTop ℚ))
    (S : ℕ → ℤ → Bool) {fl : CheckFlags} (hc : fl.noCheck = true) (hr : fl.reversed = false) :
    (searchList c H bLow bHigh D S fl).Nodup := by
  have hmem {b : ℕ} {a : ℤ} {q : ℤ × ℤ × ℤ} (hq : q ∈ checkNumWith (scaledCoeffs c (degree c) b)
      (if degree c % 2 = 1 then b else 1) b fl a) : q = (a, 0, (b : ℤ)) := by
    simpa [hr] using ((mem_checkNumWith_of_noCheck hc).mp hq).2
  refine List.Nodup.append ?_ ((nodup_searchDens c hb).flatMap (fun b _ ↦ ?_)
    (fun q ↦ q.2.2.toNat) fun b _ q hq ↦ ?_) fun q hq hq' ↦ ?_
  · rw [pointsAtInfinityList_of_noCheck_eq_true hc]
    split_ifs <;> simp
  · refine ((nodup_numerators H).filter _).flatMap (fun a _ ↦ ?_) (fun q ↦ q.1)
      fun a _ q hq ↦ by rw [hmem hq]
    rw [checkNumWith_of_noCheck_eq_true hc]
    split_ifs <;> simp
  · obtain ⟨a, -, hq⟩ := List.mem_flatMap.mp hq
    simp [hmem hq]
  · obtain ⟨b, hb, a, -, hq'⟩ := by simpa only [List.mem_flatMap] using hq'
    have h1 := (le_and_le_of_mem_searchDens hbLow hb).1
    have h2 : q = (1, 0, 0) := by simpa [hr] using eq_of_mem_pointsAtInfinityList_of_noCheck hc hq
    rw [hmem hq', Prod.mk.injEq, Prod.mk.injEq] at h2
    lia

/-- Under `RATPOINTS_NO_CHECK`, the points that the search delivers are distinct: the survivors
`(a, 0, b)` are distinct pairs over distinct denominators `b ≥ 1` (`Ratpoints.nodup_searchDens`),
the point at infinity apart, and the map of the reversal is injective on the normalized pairs
(`Ratpoints.Sieve.swapPoint_inj`). -/
theorem nodup_searchList_of_noCheck {c : List ℤ} {H bLow bHigh : ℕ} (hH : 1 ≤ H)
    (hbLow : 1 ≤ bLow) (hb : 1 ≤ bHigh) (hbH : bHigh ≤ H) (D : List (WithBotTop ℚ × WithBotTop ℚ))
    (S : ℕ → ℤ → Bool) {fl : CheckFlags} (hc : fl.noCheck = true) :
    (searchList c H bLow bHigh D S fl).Nodup := by
  have hc' : ({ fl with reversed := false } : CheckFlags).noCheck = true := hc
  rw [searchList_eq_map]
  refine (nodup_searchList_of_noCheck_of_reversed_eq_false hbLow hb D S hc' rfl).map_on
    fun q hq q' hq' h ↦ ?_
  obtain ⟨x, z, rfl, hn⟩ := exists_eq_of_mem_searchList_of_noCheck hc' hH hbLow hbH hq
  obtain ⟨x', z', rfl, hn'⟩ := exists_eq_of_mem_searchList_of_noCheck hc' hH hbLow hbH hq'
  cases hr : fl.reversed <;> simp only [hr, Bool.false_eq_true, ↓reduceIte, id] at h
  exacts [h, (swapPoint_inj hn.2.1 hn'.2.1).mp h]

/-- Without `RATPOINTS_NO_CHECK` and with `RATPOINTS_NO_Y`, the points that the search delivers,
with `y` replaced by `0`, are a sublist of those that it delivers under `RATPOINTS_NO_CHECK` with
the same test: each numerator gives at most its point with `y ≥ 0` in the one case and its survivor
in the other (`Ratpoints.Sieve.map_checkNumWith_sublist`). -/
theorem map_searchList_sublist (c : List ℤ) (H bLow bHigh : ℕ)
    (D : List (WithBotTop ℚ × WithBotTop ℚ)) (S : ℕ → ℤ → Bool) (rev noY : Bool) :
    ((searchList c H bLow bHigh D S ⟨rev, false, true⟩).map fun q ↦ (q.1, 0, q.2.2)).Sublist
      (searchList c H bLow bHigh D S ⟨rev, true, noY⟩) := by
  simp only [searchList, List.map_append, List.map_flatMap]
  rw [map_pointsAtInfinityList _ _ _ noY]
  exact .append_left (.flatMap_right _ fun b _ ↦ .flatMap_right _ fun a _ ↦
    map_checkNumWith_sublist ..) _

-- A curve without points of height at most `H` has no points at infinity and none over the
-- denominators of `1, …, H` in its reference.
private theorem pointsOfDen_eq_nil_of_forall_not_isPoint {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (h : ∀ q, ¬IsPoint c H q) :
    pointsOfDen c (degree c) 0 [1] = [] ∧
      ∀ b ∈ List.range' 1 H, pointsOfDen c (degree c) b (numerators H) = [] := by
  have hb : bruteForce c H = [] :=
    List.eq_nil_iff_forall_not_mem.mpr fun q hq ↦ h q (mem_bruteForce_iff.mp hq)
  rwa [bruteForce_eq_append c hH, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at hb

/-- On a curve without points of height at most `H`, the test that lets no numerator through is
sound, for the denominators from `bLow ≥ 1` to `bHigh ≤ H`. -/
theorem isSoundTest_false_of_forall_not_isPoint {c : List ℤ} {H bLow bHigh : ℕ} (hH : 1 ≤ H)
    (hbLow : 1 ≤ bLow) (hbH : bHigh ≤ H) (h : ∀ q, ¬IsPoint c H q) :
    IsSoundTest c H bLow bHigh fun _ _ ↦ false := fun b hb _ ha hne ↦
  have hb' := le_and_le_of_mem_searchDens hbLow hb
  absurd ((pointsOfDen_eq_nil_of_forall_not_isPoint hH h).2 b
    (List.mem_range'_1.mpr ⟨by lia, by lia⟩)) (pointsOfDen_ne_nil_of_mem ha hne)

/-- On a curve without points of height at most `H`, the search delivers no point at infinity,
whatever the flags. -/
theorem pointsAtInfinityList_eq_nil_of_forall_not_isPoint {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (h : ∀ q, ¬IsPoint c H q) (fl : CheckFlags) :
    pointsAtInfinityList c (degree c) fl = [] :=
  pointsAtInfinityList_eq_nil_of_pointsOfDen_eq_nil
    (pointsOfDen_eq_nil_of_forall_not_isPoint hH h).1 fl

/-! ### The run in each shape -/

namespace Sieve

/-- What the run of the search needs of its arguments for the curve `y ^ 2 = F(x, z)` with the
coefficient list `c`: sound sieve entries (`Ratpoints.Sieve.SieveEntry.IsSound`), each with no
factors counted of the shape that the third stage needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`),
all of them with their tables of inverses and the row offsets of the packings of the classes `cls`
(`Ratpoints.Sieve.OffsetsFor`), since a correction may move the cut points, the reciprocals of the
moduli in the order of the entries, classes that pack the words of the 2-adic information
(`Ratpoints.Sieve.twoAdic`), the word `db` of the classes that admit a numerator
(`Ratpoints.Sieve.denBits`), and a store of the tables of rows that fits all the entries
(`Ratpoints.Sieve.RowStore.Fits`). -/
structure IsSoundRun (c : List ℤ) (entries : List SieveEntry) (magics : Array ℕ)
    (cls : Vector NumClass 64) (offsets : Array ℕ) (db : UInt64) (store : RowStore) : Prop where
  /-- The sieve entries are sound. -/
  isSound : ∀ e ∈ entries, e.IsSound c
  /-- An entry with no factors counted has the shape that the third stage needs. -/
  isPrimeEntry_of_nf : ∀ e ∈ entries, e.nf = 0 → e.IsPrimeEntry
  /-- The reciprocals of the moduli, in the order of the entries. -/
  magics_eq : magics.toList = entries.map fun e ↦ magic e.p
  /-- The sieve entries have their tables of inverses. -/
  hasInverses : ∀ e ∈ entries, ∀ f ∈ e.factors, f.HasInverses e.p
  /-- The classes with a pattern have their row offsets for all the entries. -/
  offsetsFor : OffsetsFor cls entries offsets
  /-- The classes pack the words of the 2-adic information. -/
  packs : ∀ b < 64, cls[b]!.Packs (Id.run (twoAdic c (degree c)))[b]!
  /-- The word of the classes that admit a numerator. -/
  db_eq : db = denBits (Id.run (twoAdic c (degree c)))
  /-- The store of the tables of rows fits all the entries. -/
  fits : store.Fits entries

/-- The class test of a sound run on the denominator `b` is the test of the word of its class in
the 2-adic information. -/
theorem IsSoundRun.bits_bne_zero {c : List ℤ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    {store : RowStore} (h : IsSoundRun c entries magics cls offsets db store) (b : ℕ) :
    (cls[b % 64]!.bits != 0) = ((Id.run (twoAdic c (degree c)))[b % 64]! != 0) :=
  (h.packs _ (Nat.mod_lt _ (by decide))).bits_bne_zero

/-- The bits of the word `db` of a sound run are those of its classes with a pattern. -/
theorem IsSoundRun.getLsbD_db {c : List ℤ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    {store : RowStore} (h : IsSoundRun c entries magics cls offsets db store) {j : ℕ}
    (hj : j < 64) :
    db.toBitVec.getLsbD j = (cls[j]!.bits != 0) := by
  rw [h.db_eq, getLsbD_denBits, decide_eq_true hj, Bool.true_and, (h.packs j hj).bits_bne_zero]

-- The shape of every denominator.
private theorem exists_dens_eq_filter_all {c : List ℤ} {H : ℕ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    {store : RowStore} (hrun : IsSoundRun c entries magics cls offsets db store)
    (bLow bHigh : ℕ) :
    ∃ p : ℕ → Bool, Id.run (Shape.all.dens db bLow bHigh) =
        (List.range' bLow (bHigh + 1 - bLow)).filter p ∧
      ∀ b ∈ List.range' bLow (bHigh + 1 - bLow), pointsOfDen c (degree c) b (numerators H) ≠ [] →
        p b = true ∧ Id.run (Shape.all.keep cls b) = true :=
  ⟨fun _ ↦ true, by simp [Shape.dens], fun b _ h ↦
    ⟨rfl, by simpa [Shape.keep, hrun.bits_bne_zero b] using getElem!_twoAdic_ne_zero h⟩⟩

-- The square shape, for odd degree and `|c_d| = 1`.
private theorem exists_dens_eq_filter_squares {c : List ℤ} {H : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} {store : RowStore} (hrun : IsSoundRun c entries magics cls offsets db store)
    (hd : degree c % 2 = 1) (hc : (c.getD (degree c) 0).natAbs = 1) {bLow : ℕ} (hbLow : 1 ≤ bLow)
    (bHigh : ℕ) :
    ∃ p : ℕ → Bool, Id.run (Shape.squares.dens db bLow bHigh) =
        (List.range' bLow (bHigh + 1 - bLow)).filter p ∧
      ∀ b ∈ List.range' bLow (bHigh + 1 - bLow), pointsOfDen c (degree c) b (numerators H) ≠ [] →
        p b = true ∧ Id.run (Shape.squares.keep cls b) = true := by
  refine ⟨fun b ↦ Nat.sqrt b * Nat.sqrt b == b, by simp [Shape.dens, squaresDens_eq_filter hbLow],
    fun b _ h ↦ ⟨?_, by simpa [Shape.keep, hrun.bits_bne_zero b] using getElem!_twoAdic_ne_zero h⟩⟩
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil h
  obtain ⟨r, rfl⟩ := isSquare_of_sq_eq_binaryForm_of_odd hd (Int.isUnit_iff_natAbs_eq.mpr hc) hg hy
  simp [Nat.sqrt_eq]

-- The divisor shape, for odd degree when the divisor set-up succeeds.
private theorem exists_dens_eq_filter_squares1 {c : List ℤ} {H : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} {store : RowStore} (hrun : IsSoundRun c entries magics cls offsets db store)
    (hd : degree c % 2 = 1) {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow) {info : List Setup.DenInfo}
    {divisors : List ℕ} (hs : Id.run (Setup.setupUs1 c (degree c) bHigh) = some (info, divisors)) :
    ∃ p : ℕ → Bool, Id.run ((Shape.squares1 info divisors).dens db bLow bHigh) =
      (squares1Dens divisors bLow bHigh).filter p ∧
      ∀ b ∈ squares1Dens divisors bLow bHigh, pointsOfDen c (degree c) b (numerators H) ≠ [] →
        p b = true ∧ Id.run ((Shape.squares1 info divisors).keep cls b) = true := by
  refine ⟨fun _ ↦ true, by simp [Shape.dens], fun b hb h ↦ ⟨rfl, ?_⟩⟩
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil h
  have hb0 : b ≠ 0 := by lia [(le_and_le_of_mem_squares1Dens hbLow hb).1]
  simp [Shape.keep, hrun.bits_bne_zero b, getElem!_twoAdic_ne_zero h,
    run_denInfoTest_of_sq_eq hd hs hb0 hg hy]

-- The word shape, for even degree, with the forbidden divisors and the Jacobi test up to the
-- largest denominator `bHigh`.
private theorem exists_dens_eq_filter_words {c : List ℤ} {H : ℕ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    {store : RowStore} (hrun : IsSoundRun c entries magics cls offsets db store)
    (hd : degree c % 2 = 0) {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow) {forb : List ForbiddenEntry}
    {forbVal : List ForbiddenVal} (hforb : ∀ e ∈ forb, IsForbiddenEntry c (degree c) bHigh e)
    (hval : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) bHigh e) (useJacobi : Bool) :
    ∃ p : ℕ → Bool, Id.run ((Shape.words forb forbVal useJacobi
        (if useJacobi then Id.run (jacobiSetup (c.getD (degree c) 0) bHigh) else none)
        (c.getD (degree c) 0)).dens db bLow bHigh) =
        (List.range' bLow (bHigh + 1 - bLow)).filter p ∧
      ∀ b ∈ List.range' bLow (bHigh + 1 - bLow), pointsOfDen c (degree c) b (numerators H) ≠ [] →
        p b = true ∧ Id.run ((Shape.words forb forbVal useJacobi
          (if useJacobi then Id.run (jacobiSetup (c.getD (degree c) 0) bHigh) else none)
          (c.getD (degree c) 0)).keep cls b) = true := by
  obtain rfl := hrun.db_eq
  refine ⟨fun b ↦ (denBits (Id.run (twoAdic c (degree c)))).toBitVec.getLsbD (b % 64) &&
    forb.all fun e ↦ b % e.p != 0, ?_, fun _ hb h ↦ ?_⟩
  · simpa [Shape.dens] using toList_run_wordsDens (fun e he ↦ (hforb e he).prime.pos)
      (fun e he ↦ (hforb e he).words_eq) bLow bHigh
  have hb' := List.mem_range'_1.mp hb
  obtain ⟨_, _, _, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil h
  exact ⟨getLsbD_denBits_and_all_of_sq_eq hd hforb (by lia) (by lia) hg hy,
    run_wordsTest_of_sq_eq hd hval _ (by lia) (by lia) hg hy⟩

end Sieve

/-! ### What `Ratpoints.sievingInfoOf` computes -/

/-- What the loop of `Ratpoints.sievingInfoOf` over the moduli has made after the moduli `pref`,
before a return: the sieve entries `entries` of the moduli `pref`, in their order, each made by
`Ratpoints.makeModulus?` (`Ratpoints.IsModulusEntry`) with the reference to its table of rows and
the kind of its builder of its position (`Ratpoints.Sieve.SieveEntry.refInit`), that of one of the
first `Ratpoints.numPrimes` primes of the table having the shape that the third stage of the sieve
needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), and the store `store` of the tables of rows as
the loop of the tables and the tables of these entries make it
(`Ratpoints.Sieve.RowStore.MadeFor`). -/
structure SievingInfoEntries (c : List ℤ) (pref : List ℕ) (entries : Array SieveEntry)
    (store : RowStore) : Prop where
  /-- The entries are those of the moduli `pref`, in their order. -/
  map_p : entries.toList.map (·.p) = pref
  /-- Each entry is made by `Ratpoints.makeModulus?`. -/
  isModulusEntry : ∀ e ∈ entries, IsModulusEntry c e.p e
  /-- Each entry has the reference and the kind of builder of its position. -/
  refInit : ∀ n (h : n < entries.size),
    (entries[n].ref, entries[n].init) = SieveEntry.refInit n entries[n].factors
  /-- The entry of one of the first `Ratpoints.numPrimes` primes has the shape that the third stage
  needs. -/
  isPrimeEntry : ∀ e ∈ entries, ∀ pn < numPrimes, primeTable[pn]! = e.p → e.IsPrimeEntry
  /-- The store is made for the entries. -/
  madeFor : store.MadeFor c (degree c) entries.toList

/-- The invariant of the loop of `Ratpoints.sievingInfoOf` over the moduli, after the moduli `pref`
and with the moduli `suff` still to come, on the result of an early return, the sieve entries made
and the store of the tables of rows: before a return, what the loop has made
(`Ratpoints.SievingInfoEntries`); a result, which is `none` and comes when the curve has no points
at all, only at the end. -/
def SievingInfoInvariant (c : List ℤ) (pref suff : List ℕ)
    (st : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore)) × Array SieveEntry × RowStore) : Prop :=
  st.1.elim (SievingInfoEntries c pref st.2.1 st.2.2) fun r ↦ suff = [] ∧ r = none ∧
    ∀ H q, ¬IsPoint c H q

/-- The loop of `Ratpoints.sievingInfoOf` starts with the store of the loop of the tables, which
holds the rows of `0` of the primes and no others (`Ratpoints.Sieve.PrimeStore`). -/
theorem sievingInfoInvariant_empty (c : List ℤ) (suff : List ℕ) {store : RowStore}
    (h : PrimeStore store) : SievingInfoInvariant c [] suff (none, #[], store) :=
  ⟨rfl, nofun, nofun, nofun, RowStore.madeFor_nil c (degree c) h.1 h.2⟩

-- The sieve entry of one of the first `numPrimes` primes of the table with the prime as its only
-- factor, with the table of the reference, and the reciprocal of the prime has the shape that the
-- third stage needs.
private theorem isPrimeEntry_of_factors_eq {c : List ℤ} {e : SieveEntry} {pn : ℕ}
    (hpn : pn < numPrimes) (hm : primeTable[pn]! = e.p)
    (h : e.factors = [.prime (examinePrime c (degree c) e.p)]) (hmg : e.magic = magic e.p) :
    e.IsPrimeEntry :=
  isPrimeEntry_examinePrime c (degree c)
    (hm ▸ prime_getElem!_primeTable (hpn.trans_le numPrimes_le_size_primeTable))
    (hm ▸ (getElem!_primeTable_lt_maxPrimeEven hpn).le.trans maxPrimeEven_le_two_pow_32) h rfl hmg

-- The prime factors of a sieve entry made by `Ratpoints.makeModulus?` are positive.
private theorem IsModulusEntry.pos_of_prime_mem {c : List ℤ} {m : ℕ} {s : SieveEntry}
    (h : IsModulusEntry c m s) (t : Entry) (ht : .prime t ∈ s.factors) : 0 < t.p :=
  (h.buildable _ ht).1

/-- The references and the kinds of builder of the entries are those of
`Ratpoints.Sieve.SieveEntry.refInit` at their positions also after the next entry `e`, made at the
position `entries.size`, is pushed. -/
theorem refInit_push {entries : Array SieveEntry}
    (h : ∀ n (hn : n < entries.size),
      (entries[n].ref, entries[n].init) = SieveEntry.refInit n entries[n].factors)
    {e : SieveEntry} (he : (e.ref, e.init) = SieveEntry.refInit entries.size e.factors) :
    ∀ n (hn : n < (entries.push e).size),
      ((entries.push e)[n].ref, (entries.push e)[n].init) =
        SieveEntry.refInit n (entries.push e)[n].factors :=
  Array.forall_getElem_push
    (P := fun n (s : SieveEntry) ↦ (s.ref, s.init) = SieveEntry.refInit n s.factors) h he

/-- The step of the loop of `Ratpoints.sievingInfoOf` at a modulus `m`, whose sieve entry
`Ratpoints.makeModulus?` makes at the position `entries.size` (`Ratpoints.makeModulus?_spec`), with
its tables of rows and those of its factors added to the store
(`Ratpoints.Sieve.SieveEntry.addTables`): the entry of one of the first `Ratpoints.numPrimes` primes
of the table has the shape that the third stage needs, and the store is made for the entries with
`e` (`Ratpoints.Sieve.RowStore.MadeFor.addTables`). -/
theorem SievingInfoInvariant.push {c : List ℤ} {m : ℕ} {pref suff : List ℕ}
    {o : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore))}
    {entries : Array SieveEntry} {store : RowStore} {r : Option SieveEntry} {e : SieveEntry}
    (h : SievingInfoInvariant c pref (m :: suff) (o, entries, store))
    (hr : (∀ s, r = some s → IsModulusEntry c m s ∧
          (s.ref, s.init) = SieveEntry.refInit entries.size s.factors ∧
          ∀ pn < numPrimes, primeTable[pn]! = m →
            s.factors = [.prime (examinePrime c (degree c) m)]) ∧
      (r = none → ∀ H q, ¬IsPoint c H q))
    (he : r = some e) :
    SievingInfoInvariant c (pref ++ [m]) suff (none, entries.push e, e.addTables store) := by
  cases o with
  | some _ => exact absurd h.1 (List.cons_ne_nil _ _)
  | none =>
    obtain ⟨hme, href, hf⟩ := hr.1 e he
    obtain rfl := hme.p_eq
    have hmd := h.madeFor.addTables
      (SieveEntry.refFits_of_refInit_eq href fun _ ↦ hme.p_eq_modulus) hme.pos_of_prime_mem
    refine ⟨by simp [h.map_p], Array.forall_mem_push.mpr ⟨hme, h.isModulusEntry⟩,
      refInit_push h.refInit href, Array.forall_mem_push.mpr ⟨fun pn hpn hm ↦
        isPrimeEntry_of_factors_eq hpn hm (hf pn hpn hm) hme.packable.magic_eq, h.isPrimeEntry⟩, ?_⟩
    rwa [Array.toList_push]

/-- What the search needs of the result of `Ratpoints.sievingInfoOf` for the parameters `P`: the
sieve entries `entries` are those of the moduli, in their order, sound
(`Ratpoints.Sieve.SieveEntry.IsSound`), with the fields that the packing reads
(`Ratpoints.Sieve.SieveEntry.Packable`) and the tables of inverses of their factors
(`Ratpoints.Sieve.Factor.HasInverses`), those of the third stage of the shape that it needs
(`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`); `magics` holds the reciprocals of their moduli, in
their order; the forbidden divisors are among those that the loops of the tables and of the further
primes may record (`Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`); and the
store of the tables of rows fits the entries (`Ratpoints.Sieve.RowStore.Fits`). -/
structure IsSievingInfoOf (c : List ℤ) (H : ℕ) (P : Params) (entries : List SieveEntry)
    (magics : Array ℕ) (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal)
    (store : RowStore) : Prop where
  /-- The sieve entries are sound, with the fields that the packing reads and the tables of inverses
  of their factors. -/
  isSound : ∀ e ∈ entries, e.IsSound c ∧ e.Packable ∧ ∀ f ∈ e.factors, f.HasInverses e.p
  /-- The reciprocals of the moduli, in the order of the entries. -/
  magics_eq : magics.toList = entries.map fun e ↦ magic e.p
  /-- The entries are those of the moduli, in their order. -/
  map_p : entries.map (·.p) = P.moduli
  /-- The entries of the third stage have the shape that it needs. -/
  isPrimeEntry : ∀ e ∈ entries.drop P.sp2, e.IsPrimeEntry
  /-- The forbidden divisors tested with words are sound. -/
  isForbiddenEntry : ∀ e ∈ forb, IsForbiddenEntry c (degree c) H e
  /-- The forbidden divisors tested by their valuations are sound. -/
  isForbiddenVal : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e
  /-- The store of the tables of rows fits the entries. -/
  fits : store.Fits entries

/-- The early return of the loop of `Ratpoints.sievingInfoOf` at a modulus whose sieve entry is
none: the curve has no points. -/
theorem sievingInfoInvariant_some_none {c : List ℤ} {m : ℕ} {pref : List ℕ}
    {entries : Array SieveEntry} {store : RowStore} {r x : Option SieveEntry} {n : ℕ}
    (hr : (∀ s, r = some s → IsModulusEntry c m s ∧
          (s.ref, s.init) = SieveEntry.refInit n s.factors ∧ ∀ pn < numPrimes, primeTable[pn]! = m →
            s.factors = [.prime (examinePrime c (degree c) m)]) ∧
      (r = none → ∀ H q, ¬IsPoint c H q))
    (hx : ∀ e, x = some e → False) (he : r = x) :
    SievingInfoInvariant c pref [] (some none, entries, store) :=
  ⟨rfl, rfl, hr.2 (he.trans (Option.eq_none_iff_forall_ne_some.mpr hx))⟩

/-- The end of the loop of `Ratpoints.sievingInfoOf` after an early return. -/
theorem SievingInfoInvariant.post_some {c : List ℤ} {H : ℕ} {P : Params} {pref : List ℕ}
    {o : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore))}
    {entries : Array SieveEntry} {store : RowStore}
    {r : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal × RowStore)}
    (h : SievingInfoInvariant c pref [] (o, entries, store)) (ho : o = some r) :
    (∀ entries magics forb forbVal store, r = some (entries, magics, forb, forbVal, store) →
        IsSievingInfoOf c H P entries magics forb forbVal store) ∧
      (r = none → ∀ H q, ¬IsPoint c H q) := by
  subst ho
  obtain ⟨-, rfl, h⟩ := h
  exact ⟨nofun, fun _ ↦ h⟩

-- The sieve entries of the moduli of well-formed parameters, in their order, of which those of the
-- first `numPrimes` primes of the table have the shape that the third stage needs: those of the
-- third stage have it.
private theorem forall_mem_drop_isPrimeEntry {P : Params} (hP : P.WF) {entries : List SieveEntry}
    (hmap : entries.map (·.p) = P.moduli)
    (h : ∀ e ∈ entries, ∀ pn < numPrimes, primeTable[pn]! = e.p → e.IsPrimeEntry) :
    ∀ e ∈ entries.drop P.sp2, e.IsPrimeEntry := fun e he ↦
  have ⟨pn, hpn, hm⟩ := hP.exists_getElem!_primeTable_eq_of_mem_drop
    (hmap ▸ List.map_drop ▸ List.mem_map_of_mem he)
  h e (List.mem_of_mem_drop he) pn hpn hm

/-- The store made for the sieve entries of a run by `Ratpoints.makeModulus?`, each with the
reference and the kind of builder of its position, fits them, for the rows of the references of the
run (`Ratpoints.Sieve.runRows`, `Ratpoints.IsModulusEntry.rowsFit_runRows`). -/
theorem SievingInfoEntries.fits {c : List ℤ} {pref : List ℕ} {entries : Array SieveEntry}
    {store : RowStore} (h : SievingInfoEntries c pref entries store) : store.Fits entries.toList :=
  ⟨_, h.madeFor.storeHolds, fun n hn ↦ by
    have hn' : n < entries.size := by simpa using hn
    simp only [Array.getElem_toList]
    exact (h.isModulusEntry _ (Array.getElem_mem hn')).rowsFit_runRows (h.refInit n hn')
      (by simp [hn'])⟩

/-- The end of the loop of `Ratpoints.sievingInfoOf` over all the moduli of well-formed parameters,
with forbidden divisors that the loops of the tables and of the further primes may record: the
reciprocals of the sieve entries are those of their moduli, the entries of the moduli of the third
stage are among those of the first `Ratpoints.numPrimes` primes of the table
(`Ratpoints.Params.WF.exists_getElem!_primeTable_eq_of_mem_drop`), and the store fits the entries
(`Ratpoints.SievingInfoEntries.fits`). -/
theorem SievingInfoInvariant.post_none {c : List ℤ} {H : ℕ} {P : Params}
    {o : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore))}
    {entries : Array SieveEntry} {store : RowStore} {forb : List ForbiddenEntry}
    {forbVal : List ForbiddenVal} (hP : P.WF)
    (h : SievingInfoInvariant c P.moduli [] (o, entries, store)) (ho : o = none)
    (hforb : (∀ e ∈ forb, IsForbiddenEntry c (degree c) H e) ∧
      ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e) :
    (∀ entries' magics forb' forbVal' store',
        some (entries.toList, entries.map (·.magic), forb, forbVal, store) =
          some (entries', magics, forb', forbVal', store') →
        IsSievingInfoOf c H P entries' magics forb' forbVal' store') ∧
      (some (entries.toList, entries.map (·.magic), forb, forbVal, store) = none →
        ∀ H q, ¬IsPoint c H q) := by
  subst ho
  refine ⟨fun _ _ _ _ _ h' ↦ ?_, nofun⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'
  have hent (e : SieveEntry) (he : e ∈ entries.toList) :=
    h.isModulusEntry e (Array.mem_toList_iff.mp he)
  refine ⟨fun e he ↦ ⟨(hent e he).isSound, (hent e he).packable, (hent e he).hasInverses⟩, ?_,
    h.map_p, forall_mem_drop_isPrimeEntry hP h.map_p fun e he ↦
      h.isPrimeEntry e (Array.mem_toList_iff.mp he), hforb.1, hforb.2, h.fits⟩
  rw [Array.toList_map]
  exact List.map_congr_left fun e he ↦ (hent e he).packable.magic_eq

-- The exit of the loop of the tables in `Ratpoints.sievingInfoOf`: the curve has no points.
private theorem post_of_run_examinePrimes_eq {c : List ℤ} {u checkDenom : Bool} {P : Params}
    {H : ℕ} {x : Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal × RowStore)}
    (hn : P.examined ≤ numPrimes)
    (hx : ∀ tables ba val store, x = some (tables, ba, val, store) → False)
    (he : Id.run (examinePrimes c (degree c) u checkDenom P.examined P.maxForbidden H) = x) :
    (∀ entries magics forb forbVal store,
        (none : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
          RowStore)) = some (entries, magics, forb, forbVal, store) →
        IsSievingInfoOf c H P entries magics forb forbVal store) ∧
      ((none : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
        RowStore)) = none → ∀ H q, ¬IsPoint c H q) :=
  ⟨nofun, fun _ ↦ not_isPoint_of_run_examinePrimes_eq_none
    (he.trans (Option.eq_none_iff_forall_ne_some.mpr fun ⟨t, b, v, s⟩ h ↦ hx t b v s h)) hn⟩

-- The forbidden divisors that the loop of the tables records, as lists.
private theorem forall_mem_toList_isForbiddenEntry_and_isForbiddenVal {c : List ℤ} {d : ℕ}
    {u checkDenom : Bool} {n maxForbidden H : ℕ} {tables : Array Entry}
    {ba : Array ForbiddenEntry} {val : Array ForbiddenVal} {store : RowStore}
    (h : Id.run (examinePrimes c d u checkDenom n maxForbidden H) = some (tables, ba, val, store))
    (hn : n ≤ numPrimes) :
    (∀ e ∈ ba.toList, IsForbiddenEntry c d H e) ∧ ∀ e ∈ val.toList, IsForbiddenVal c d H e :=
  ⟨fun _ he ↦ isForbiddenEntry_of_run_examinePrimes_eq_some h hn (Array.mem_toList_iff.mp he),
    fun _ he ↦ isForbiddenVal_of_run_examinePrimes_eq_some h hn (Array.mem_toList_iff.mp he)⟩

-- The loop of the tables, as a value for the contract of `Ratpoints.sievingInfoOf`.
private theorem examinePrimes_value (c : List ℤ) (d : ℕ) (u checkDenom : Bool)
    (n maxForbidden bHigh : ℕ) :
    ⦃ True ⦄ examinePrimes c d u checkDenom n maxForbidden bHigh
    ⦃ fun r ↦ r = Id.run (examinePrimes c d u checkDenom n maxForbidden bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

attribute [local irreducible] SievingInfoInvariant in
/-- For well-formed parameters, what `Ratpoints.sievingInfoOf` computes serves the search
(`Ratpoints.IsSievingInfoOf`): the sieve entries are those of the moduli, in their order, and are
sound (`Ratpoints.SievingInfoInvariant.push`, the tables of the loop of the tables being those of
the reference, `Ratpoints.makeModulus?_spec`), have the fields that the packing reads
(`Ratpoints.Sieve.SieveEntry.Packable`) and the tables of inverses of their factors
(`Ratpoints.Sieve.Factor.HasInverses`), and hold the reciprocals of their moduli, which are the
reciprocals returned, in the order of the entries, those of the third stage having the shape that it
needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`); the forbidden divisors are among those that the
loop of the tables and the loop of the further primes may record
(`Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`), with the switch of the
forbidden divisors on or off; and the store of the tables of rows that the loop of the tables and
the loop over the moduli make fits the entries (`Ratpoints.Sieve.RowStore.Fits`); the largest
denominator `bHigh` of the search bounds the forbidden divisors. When it returns none, the curve has
no points of any height, none modulo a prime of the loop of the tables
(`Ratpoints.Sieve.not_isPoint_of_run_examinePrimes_eq_none`) or modulo a prime examined for a
modulus. -/
@[spec]
theorem sievingInfoOf_spec (c : List ℤ) (u checkDenom : Bool) (P : Params) (bHigh : ℕ) :
    ⦃ P.WF ⦄ sievingInfoOf c (degree c) u checkDenom P bHigh
    ⦃ fun r ↦ (∀ entries magics forb forbVal store,
        r = some (entries, magics, forb, forbVal, store) →
          IsSievingInfoOf c bHigh P entries magics forb forbVal store) ∧
      (r = none → ∀ H q, ¬IsPoint c H q) ⦄ := by
  vcgen [sievingInfoOf, examinePrimes_value] invariants
  · fun pref suff st ↦ SievingInfoInvariant c pref suff st
  · fun pref suff st ↦ SievingInfoInvariant c pref suff st
  all_goals try dsimp only at *
  all_goals try obtain rfl := ‹_ = Id.run (examinePrimes _ _ _ _ _ _ _)›
  all_goals have hP := ‹P.WF›
  all_goals first
    | exact sievingInfoInvariant_empty c _
        (primeStore_of_run_examinePrimes_eq_some ‹_› hP.examined_le)
    | exact SievingInfoInvariant.post_some ‹_› ‹_›
    | exact SievingInfoInvariant.post_none hP ‹_› ‹_› ‹_›
    | exact SievingInfoInvariant.post_none hP ‹_› ‹_›
        (forall_mem_toList_isForbiddenEntry_and_isForbiddenVal ‹_› hP.examined_le)
    | exact SievingInfoInvariant.push ‹_› ‹_› ‹_›
    | exact sievingInfoInvariant_some_none ‹_› ‹_› ‹_›
    | exact ⟨getElem_eq_examinePrime_of_run_examinePrimes_eq_some ‹_› hP.examined_le,
        hP.modulus _ (by simp [‹P.moduli = _›])⟩
    | exact ⟨fun _ ↦ isForbiddenEntry_of_run_examinePrimes_eq_some ‹_› hP.examined_le,
        fun _ ↦ isForbiddenVal_of_run_examinePrimes_eq_some ‹_› hP.examined_le⟩
    | exact post_of_run_examinePrimes_eq hP.examined_le ‹_› ‹_›

/-! ### The search -/

-- The shape that `Ratpoints.Sieve.runSetup` chooses from the flags of the search lists the
-- denominators of the search from `bLow` to `bHigh` that a filter lets through, and lets every
-- denominator of a point through.
private theorem exists_dens_eq_filter_runSetup {c : List ℤ} {H bLow bHigh : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} {store : RowStore} (hrun : IsSoundRun c entries magics cls offsets db store)
    (hbLow : 1 ≤ bLow) {us1 : Option (List Setup.DenInfo × List ℕ)}
    (hus1 : (if degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1 then
      Id.run (Setup.setupUs1 c (degree c) bHigh) else none) = us1)
    {checkDenom useJacobi : Bool} {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hforb : ∀ e ∈ forb, IsForbiddenEntry c (degree c) bHigh e)
    (hval : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) bHigh e)
    (hcd : checkDenom = true → degree c % 2 = 0) (dom : List (Double × Double)) :
    ∃ p : ℕ → Bool, Id.run ((Id.run (runSetup (degree c % 2 == 1 &&
        (c.getD (degree c) 0).natAbs == 1) us1 checkDenom useJacobi forb forbVal
        (c.getD (degree c) 0) H bHigh dom)).1.dens db bLow bHigh) =
        (searchDens c (degree c) bLow bHigh).filter p ∧
      ∀ b ∈ searchDens c (degree c) bLow bHigh, pointsOfDen c (degree c) b (numerators H) ≠ [] →
        p b = true ∧ Id.run ((Id.run (runSetup (degree c % 2 == 1 &&
          (c.getD (degree c) 0).natAbs == 1) us1 checkDenom useJacobi forb forbVal
          (c.getD (degree c) 0) H bHigh dom)).1.keep cls b) = true := by
  rw [searchDens, hus1, fst_run_runSetup]
  rcases Nat.mod_two_eq_zero_or_one (degree c) with hd | hd
  · obtain rfl : us1 = none := by rw [← hus1, hd]; rfl
    rw [hd]
    cases checkDenom
    · exact exists_dens_eq_filter_all hrun bLow bHigh
    · exact exists_dens_eq_filter_words hrun hd hbLow hforb hval _
  by_cases hc : (c.getD (degree c) 0).natAbs = 1
  · obtain rfl : us1 = none := by rw [← hus1, hd, hc]; rfl
    rw [hd, hc]
    exact exists_dens_eq_filter_squares hrun hd hc hbLow bHigh
  rw [hd, beq_eq_false_iff_ne.mpr hc, Bool.and_false]
  rcases us1 with _ | ⟨info, divisors⟩
  · obtain rfl : checkDenom = false := by cases checkDenom <;> simp_all
    exact exists_dens_eq_filter_all hrun bLow bHigh
  · exact exists_dens_eq_filter_squares1 hrun hd hbLow (Option.ite_none_right_eq_some.mp hus1).2

-- The denominators of the search from `bLow ≥ 1` are distinct: there are none for `bHigh = 0`.
private theorem nodup_searchDens_of_one_le {c : List ℤ} {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow) :
    (searchDens c (degree c) bLow bHigh).Nodup := by
  rcases Nat.eq_zero_or_pos bHigh with rfl | hb
  · have h : searchDens c (degree c) bLow 0 = [] := List.eq_nil_iff_forall_not_mem.mpr fun b hb ↦
      absurd (le_and_le_of_mem_searchDens hbLow hb) (by lia)
    exact h ▸ List.nodup_nil
  · exact nodup_searchDens c hb

-- The points of the numerators in the ranges of the bounds of the search intervals `dom` that pass
-- the tests `T` and `T'`, over the denominators of the search that the filters `p` and `k` let
-- through, are those of the numerators `a` with `a / b` in the intervals that pass all four tests.
private theorem flatMap_filter_filter_inRanges {c : List ℤ} {H bLow : ℕ} (hbLow : 1 ≤ bLow)
    (bHigh : ℕ) (dom : List (Double × Double)) (p k : ℕ → Bool) (T T' : ℕ → ℤ → Bool)
    {α : Type} (g : ℕ → ℤ → List α) :
    (((searchDens c (degree c) bLow bHigh).filter p).filter k).flatMap (fun b ↦
        ((numerators H).filter fun a ↦ inRanges (numeratorRanges b H (domainValues dom)) a &&
          T b a && T' b a).flatMap (g b)) =
      (searchDens c (degree c) bLow bHigh).flatMap fun b : ℕ ↦ ((numerators H).filter fun a : ℤ ↦
        decide (InIntervals (domainValues dom) (a / b)) && (p b && k b && T b a && T' b a)).flatMap
          (g b) := by
  rw [List.filter_filter, List.flatMap_filter_flatMap_filter]
  refine List.flatMap_congr fun b hb ↦ congr(List.flatMap _ $(List.filter_congr fun a ha ↦ ?_))
  rw [inRanges_numeratorRanges (by lia [(le_and_le_of_mem_searchDens hbLow hb).1])
    (natAbs_le_of_mem_numerators ha)]
  ac_rfl

/-- The run of the shape that `Ratpoints.Sieve.runSetup` chooses, with sound arguments
(`Ratpoints.Sieve.IsSoundRun`), a well-formed first decision (`Ratpoints.Sieve.DecisionWF`), pieces
of at least one bit array, the height below `2 ^ 63`, the denominators from `bLow ≥ 1` to
`bHigh ≤ H` and well-formed search intervals `dom`, delivers, with any callback, flags of the check
and delivery whose flag is clear, the points of the check with the flags of the numerators in the
search intervals that pass a test of the sieve over the denominators of the search
(`Ratpoints.Sieve.exists_run_sieveRun_eq_deliver`, `Ratpoints.Sieve.rangesFor_run_exactBounds`,
`Ratpoints.Sieve.inRanges_numeratorRanges`); the test, which depends neither on the callback nor on
the flags, but on the search intervals, which the decisions of the blocks read
(`Ratpoints.Sieve.blockDecision`), is sound (`Ratpoints.IsSoundTest`): the shape lets every
denominator of a point through, and the class words and the sound entries of every block every
numerator of a point (`Ratpoints.Sieve.classBit_and_survives_of_ne_nil`). -/
theorem exists_isSoundTest_run_sieveRun {c : List ℤ} {H A bLow bHigh : ℕ} {s : SieveOptions}
    {P : Params} {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64}
    {offsets : Array ℕ} {db : UInt64} {store : RowStore}
    (hrun : IsSoundRun c entries magics cls offsets db store)
    (hdec : DecisionWF entries P.sp1 ⟨0, P.sp2, P.sp3⟩) (hH63 : H < 2 ^ 63) (hA : 1 ≤ A)
    (hbLow : 1 ≤ bLow) (hbH : bHigh ≤ H) {us1 : Option (List Setup.DenInfo × List ℕ)}
    (hus1 : (if degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1 then
      Id.run (Setup.setupUs1 c (degree c) bHigh) else none) = us1)
    {checkDenom useJacobi : Bool} {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hforb : ∀ e ∈ forb, IsForbiddenEntry c (degree c) bHigh e)
    (hval : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) bHigh e)
    (hcd : checkDenom = true → degree c % 2 = 0) (dom : List (Double × Double))
    (hdom : IntervalsWF (domainBits dom)) :
    ∃ S, IsSoundTest c H bLow bHigh S ∧ ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
      (fl : CheckFlags) (r : Delivery σ), r.quit = false →
        (Id.run (sieveRun process c (degree c) H A fl s P entries magics cls offsets db
          (Id.run (runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) us1
            checkDenom useJacobi forb forbVal (c.getD (degree c) 0) H bHigh dom)).1
          (Id.run (runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) us1
            checkDenom useJacobi forb forbVal (c.getD (degree c) 0) H bHigh dom)).2
          bLow bHigh store r)).1 =
        r.deliver process ((searchDens c (degree c) bLow bHigh).flatMap fun b : ℕ ↦
          ((numerators H).filter fun a : ℤ ↦ decide (InIntervals (domainValues dom) (a / b)) &&
            S b a).flatMap (checkNumWith (scaledCoeffs c (degree c) b)
              (if degree c % 2 = 1 then b else 1) b fl)) := by
  obtain ⟨p, hdens, hkeep⟩ := exists_dens_eq_filter_runSetup hrun hbLow hus1 hforb hval hcd dom
  have hff := forbFits_fst_run_runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1)
    us1 checkDenom useJacobi forbVal (c.getD (degree c) 0) H bHigh dom hforb
  generalize (Id.run (runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) us1
    checkDenom useJacobi forb forbVal (c.getD (degree c) 0) H bHigh dom)).1 = shape
    at hdens hkeep hff ⊢
  obtain ⟨sp3At, hsp⟩ := exists_run_sieveRun_eq_deliver c (degree c) H A s P entries magics cls
    offsets db shape _ bLow bHigh store hA (fun e he ↦ ⟨hrun.isPrimeEntry_of_nf e he,
      hrun.hasInverses e he⟩) hrun.magics_eq hrun.offsetsFor (fun _ ↦ hrun.getLsbD_db) hdec hff
    (hdens ▸ (nodup_searchDens_of_one_le hbLow).filter p) hbLow (by lia) hH63 hrun.fits
  refine ⟨fun b a ↦ p b && Id.run (shape.keep cls b) &&
      classBit (Id.run (twoAdic c (degree c)))[b % 64]! a && survives (entries.take (sp3At b)) b a,
    fun b hb a ha hne ↦ ?_, fun process fl r hr ↦ ?_⟩
  · have := hkeep b hb (pointsOfDen_ne_nil_of_mem ha hne)
    have := classBit_and_survives_of_ne_nil (entries := entries.take (sp3At b))
      (fun e he ↦ hrun.isSound e (List.mem_of_mem_take he)) hne
    simp_all
  rw [snd_run_runSetup, hsp process fl r hr _ (fun b ↦ numeratorRanges b H (domainValues dom))
    hrun.packs (fun b hb1 hb2 ↦ rangesFor_run_exactBounds hdom hH63 hbH (by lia) hb2), hdens]
  exact congr(r.deliver process $(flatMap_filter_filter_inRanges hbLow bHigh dom p _ _ _ _))

-- The classes after `class_offsets`, with the entries whose inverses of the strides it sets, the
-- other fields unchanged, and its row offsets, make a sound run with the word of the classes that
-- admit a numerator and the store of the tables of rows that fits the entries.
private theorem isSoundRun_of_map {c : List ℤ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls cls' : Vector NumClass 64} {offsets : Array ℕ} {store : RowStore}
    {dinv : SieveEntry → Array ℕ}
    (hent : ∀ e ∈ entries, e.IsSound c ∧ e.Packable ∧ ∀ f ∈ e.factors, f.HasInverses e.p)
    (hnf : ∀ e ∈ entries, e.nf = 0 → e.IsPrimeEntry)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p)
    (hcls : ∀ b < 64, cls[b]!.Packs (Id.run (twoAdic c (degree c)))[b]!)
    (hbits : ∀ b < 64, cls'[b]!.bits = cls[b]!.bits ∧ cls'[b]!.k = cls[b]!.k ∧
      cls'[b]!.a0 = cls[b]!.a0)
    (hoff : OffsetsFor cls' (entries.map fun e ↦ { e with dinv := dinv e }) offsets)
    (hs : store.Fits entries) :
    IsSoundRun c (entries.map fun e ↦ { e with dinv := dinv e }) magics cls' offsets
      (denBits (Id.run (twoAdic c (degree c)))) store := by
  refine ⟨fun e he ↦ ?_, fun e he ↦ ?_, by simp [hmg], fun e he ↦ ?_, hoff,
    fun b hb ↦ (hcls b hb).congr (hbits b hb).1 (hbits b hb).2.1 (hbits b hb).2.2, rfl,
    hs.map_dinv dinv⟩ <;> obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  · exact ⟨(hent e' he').1.pos, (hent e' he').1.admits_of_sq_eq⟩
  · exact hnf e' he'
  · exact (hent e' he').2.2

-- The classes, the entries and the row offsets of the search after `class_offsets`, in the array
-- of `num_packings` rows, make a sound run with a well-formed first decision, for a result of the
-- choice of the moduli as its contract gives it (`Ratpoints.sievingInfo_spec`,
-- `Ratpoints.Sieve.numClasses_spec`, `Ratpoints.Sieve.numPackings_spec`,
-- `Ratpoints.Sieve.classOffsets_spec`).
private theorem isSoundRun_of_run_classOffsets {c : List ℤ} {bHigh : ℕ} {si : SievingInfo}
    (hi : IsSievingInfo c bHigh si) {cls : Vector NumClass 64} {db : UInt64}
    (hnc : (cls, db) = Id.run (numClasses (Id.run (twoAdic c (degree c))))) {n : ℕ}
    (hn : n = Id.run (numPackings cls)) {cls' : Vector NumClass 64} {entries' : List SieveEntry}
    {offsets : Array ℕ} (hco : (cls', entries', offsets) =
      Id.run (classOffsets cls si.entries (Array.replicate (n * max si.entries.length 1) 0))) :
    IsSoundRun c entries' si.magics cls' offsets db si.store ∧
      DecisionWF entries' si.params.sp1 ⟨0, si.params.sp2, si.params.sp3⟩ := by
  obtain ⟨rfl, rfl⟩ : cls = (Id.run (numClasses _)).1 ∧ db = (Id.run (numClasses _)).2 := by
    rw [← hnc]; exact ⟨rfl, rfl⟩
  have hcls (b : ℕ) (hb : b < 64) :=
    packs_getElem!_fst_run_numClasses (Id.run (twoAdic c (degree c))) hb
  have hn' : n = max 1 (firstKeys _ 64) :=
    hn.trans (Std.WP.Id.of_run_eq_wp rfl _ ((numPackings_spec _).le_wp fun b hb ↦ (hcls b hb).1))
  have hsize : firstKeys (Id.run (numClasses (Id.run (twoAdic c (degree c))))).1 64 *
      si.entries.length ≤ (Array.replicate (n * max si.entries.length 1) (0 : ℕ)).size := by
    rw [Array.size_replicate, hn']
    exact Nat.mul_le_mul (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  obtain ⟨hbits, ⟨f, hf⟩, hoff⟩ := Std.WP.Id.of_run_eq_wp rfl _
    ((classOffsets_spec _ si.entries _).le_wp ⟨fun e he ↦ (hi.isSound e he).2.1,
      fun b hb ↦ (hcls b hb).1, hsize⟩)
  rw [← hco] at hbits hf hoff
  simp only at hbits hf hoff
  subst hf
  rw [snd_run_numClasses]
  exact ⟨isSoundRun_of_map hi.isSound hi.isPrimeEntry_of_nf hi.magics_eq hcls hbits hoff hi.fits,
    hi.decisionWF.map_dinv f⟩

-- The shape of the run that `Ratpoints.searchPoints` hands to the choice of the moduli, for the
-- classes `cls` and the word `db` of the 2-adic information.
private def searchShapeArgs (c : List ℤ) (d H : ℕ) (s : SieveOptions) (bLow bHigh : ℕ)
    (domain : List (Double × Double)) (cls : Vector NumClass 64) (db : UInt64) : ShapeArgs where
  useSquares := d % 2 == 1 && (c.getD d 0).natAbs == 1
  divisors := (if (d % 2 == 1 && (c.getD d 0).natAbs != 1) = true then
    Id.run (Setup.setupUs1 c d bHigh) else none).map (·.2)
  useJacobi := d % 2 == 0 && !Setup.isSquare (c.getD d 0) && s.jacobi
  H := H
  bLow := bLow
  bHigh := bHigh
  domain := domain
  db := db
  cls := cls
  arraySize := arraySizeAt (if s.arraySize ≤ 0 then 0 else s.arraySize.toNat) H

-- The components of the search, as values for its contract.
private theorem setupUs1_value (c : List ℤ) (d bHigh : ℕ) :
    ⦃ True ⦄ Setup.setupUs1 c d bHigh ⦃ fun r ↦ r = Id.run (Setup.setupUs1 c d bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem twoAdic_value (c : List ℤ) (d : ℕ) :
    ⦃ True ⦄ twoAdic c d ⦃ fun r ↦ r = Id.run (twoAdic c d) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem numClasses_value (nb : Vector UInt64 64) :
    ⦃ True ⦄ numClasses nb ⦃ fun r ↦ r = Id.run (numClasses nb) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem meanBitsPerWord_value (a : ShapeArgs) :
    ⦃ True ⦄ meanBitsPerWord a ⦃ fun r ↦ r = Id.run (meanBitsPerWord a) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem sievingInfo_value (c : List ℤ) (d : ℕ) (u checkDenom mayExtend : Bool)
    (s : SieveOptions) (a : ShapeArgs) (bpw : Float) :
    ⦃ True ⦄ sievingInfo c d u checkDenom mayExtend s a bpw
    ⦃ fun r ↦ r = Id.run (sievingInfo c d u checkDenom mayExtend s a bpw) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem sieving_value {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (c : List ℤ)
    (d H : ℕ) (s : SieveOptions) (P : Params) (fl : CheckFlags) (useSquares : Bool)
    (us1 : Option (List Setup.DenInfo × List ℕ)) (checkDenom useJacobi : Bool)
    (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal) (entries : List SieveEntry)
    (magics : Array ℕ) (cls : Vector NumClass 64) (db : UInt64) (store : RowStore)
    (bLow bHigh : ℕ) (domain : List (Double × Double)) (r : Delivery σ) :
    ⦃ True ⦄ sieving process c d H s P fl useSquares us1 checkDenom useJacobi forb forbVal entries
      magics cls db store bLow bHigh domain r
    ⦃ fun r' ↦ r'.1 = (Id.run (sieving process c d H s P fl useSquares us1 checkDenom useJacobi
        forb forbVal entries magics cls db store bLow bHigh domain r)).1 ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem chooseAndSearch_value {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
    (c : List ℤ) (d : ℕ) (s : SieveOptions) (mayExtend : Bool) (fl : CheckFlags)
    (us1 : Option (List Setup.DenInfo × List ℕ)) (a : ShapeArgs) (bpw : Float) (sturmEmpty : Bool)
    (r : Delivery σ) :
    ⦃ True ⦄ chooseAndSearch process c d s mayExtend fl us1 a bpw sturmEmpty r
    ⦃ fun r' ↦ r' = Id.run (chooseAndSearch process c d s mayExtend fl us1 a bpw sturmEmpty r) ⦄ :=
  ⟨fun _ ↦ rfl⟩

-- The delivery after the choice of the moduli and the search after it, along its paths for the
-- result `si` of the choice: the delivery as it came after the exit of the choice, else that of the
-- points at infinity, followed, unless the callback has stopped the search or the Sturm step has
-- left no interval, by the sieving.
private theorem chooseAndSearch_spec_paths {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
    (c : List ℤ) (d : ℕ) (s : SieveOptions) (mayExtend : Bool) (fl : CheckFlags)
    (us1 : Option (List Setup.DenInfo × List ℕ)) (a : ShapeArgs) (bpw : Float) (sturmEmpty : Bool)
    (r : Delivery σ) (si : Except ℕ SievingInfo)
    (hsi : Id.run (sievingInfo c d (Setup.useCLong c d) (d % 2 == 0) mayExtend s a bpw) = si) :
    ⦃ True ⦄ chooseAndSearch process c d s mayExtend fl us1 a bpw sturmEmpty r
    ⦃ fun out ↦ out = match (generalizing := false) si with
        | .error _ => r
        | .ok si => if (pointsAtInfinity process c d fl r).quit || sturmEmpty then
            pointsAtInfinity process c d fl r else
            (Id.run (sieving process c d a.H s si.params fl a.useSquares us1 si.checkDenom
              a.useJacobi si.forb si.forbVal si.entries si.magics a.cls a.db si.store a.bLow a.bHigh
              a.domain (pointsAtInfinity process c d fl r))).1 ⦄ := by
  rcases si with p | si <;>
  · vcgen [chooseAndSearch, sievingInfo_value, sieving_value]
    all_goals subst_vars
    all_goals simp_all

-- The data and the count of the search, with the print channel that prints nothing, which it does
-- not read, along its paths, for the classes and the word of the 2-adic information and the 2-adic
-- exit `ex`: the
-- delivery as it came after the 2-adic exit, else that of the choice of the moduli and the search
-- after it (`Ratpoints.chooseAndSearch`) with the shape of the run of the search.
private theorem searchPoints_spec_paths {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
    (c : List ℤ) (d H : ℕ) (s : SieveOptions) (mayExtend : Bool) (fl : CheckFlags)
    (bLow bHigh : ℕ) (dom : List (Double × Double)) (sturmEmpty : Bool) (r : Delivery σ)
    {cls : Vector NumClass 64} {db : UInt64} (ex : Bool)
    (hcd : Id.run (numClasses (Id.run (twoAdic c d))) = (cls, db))
    (hex : (db == 0 && !(d % 2 == 1 || Setup.isSquare (c.getD d 0))) = ex) :
    ⦃ True ⦄ searchPoints process c d H s mayExtend fl bLow bHigh dom sturmEmpty (fun _ s ↦ s) r
    ⦃ fun out ↦ (out.info, out.total) = (fun r' : Delivery σ ↦ (r'.info, r'.total))
        (if ex then r else (Id.run (chooseAndSearch process c d s mayExtend fl
          (if (d % 2 == 1 && (c.getD d 0).natAbs != 1) = true then
            Id.run (Setup.setupUs1 c d bHigh) else none)
          (searchShapeArgs c d H s bLow bHigh dom cls db)
          (Id.run (meanBitsPerWord (searchShapeArgs c d H s bLow bHigh dom cls db))) sturmEmpty
          r))) ⦄ := by
  vcgen [searchPoints, setupUs1_value, twoAdic_value, numClasses_value, meanBitsPerWord_value,
    chooseAndSearch_value]
  all_goals subst_vars
  all_goals obtain ⟨rfl, rfl⟩ :=
    Prod.mk.inj (‹((_ : Vector NumClass 64), (_ : UInt64)) = _›.trans hcd)
  all_goals simp only [searchShapeArgs] at *
  all_goals split_ifs <;> rfl

-- `Ratpoints.searchPoints_spec_paths` with `Ratpoints.chooseAndSearch_spec_paths`, as an equation,
-- for the result `si` of the choice of the moduli.
private theorem run_searchPoints_paths {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
    (c : List ℤ) (d H : ℕ) (s : SieveOptions) (mayExtend : Bool) (fl : CheckFlags)
    (bLow bHigh : ℕ) (dom : List (Double × Double)) (sturmEmpty : Bool) (r : Delivery σ)
    {cls : Vector NumClass 64} {db : UInt64} (ex : Bool) (si : Except ℕ SievingInfo)
    (hcd : Id.run (numClasses (Id.run (twoAdic c d))) = (cls, db))
    (hex : (db == 0 && !(d % 2 == 1 || Setup.isSquare (c.getD d 0))) = ex)
    (hsi : Id.run (sievingInfo c d (Setup.useCLong c d) (d % 2 == 0) mayExtend s
      (searchShapeArgs c d H s bLow bHigh dom cls db)
      (Id.run (meanBitsPerWord (searchShapeArgs c d H s bLow bHigh dom cls db)))) = si) :
    ((Id.run (searchPoints process c d H s mayExtend fl bLow bHigh dom sturmEmpty (fun _ s ↦ s)
        r)).info,
      (Id.run (searchPoints process c d H s mayExtend fl bLow bHigh dom sturmEmpty (fun _ s ↦ s)
        r)).total) =
      (fun r' : Delivery σ ↦ (r'.info, r'.total))
        (if ex then r else match (generalizing := false) si with
        | .error _ => r
        | .ok si => if (pointsAtInfinity process c d fl r).quit || sturmEmpty then
            pointsAtInfinity process c d fl r else
            (Id.run (sieving process c d H s si.params fl (d % 2 == 1 && (c.getD d 0).natAbs == 1)
              (if (d % 2 == 1 && (c.getD d 0).natAbs != 1) = true then
                Id.run (Setup.setupUs1 c d bHigh) else none) si.checkDenom
              (d % 2 == 0 && !Setup.isSquare (c.getD d 0) && s.jacobi) si.forb si.forbVal si.entries
              si.magics cls db si.store bLow bHigh dom
              (pointsAtInfinity process c d fl r))).1) := by
  rw [Std.WP.Id.of_run_eq_wp rfl (fun out : Outcome σ ↦ (out.info, out.total) = _)
    ((searchPoints_spec_paths process c d H s mayExtend fl bLow bHigh dom sturmEmpty r ex hcd
      hex).le_wp trivial)]
  cases ex
  · simp only [Bool.false_eq_true, ↓reduceIte]
    rw [Std.WP.Id.of_run_eq_wp rfl (fun out : Delivery σ ↦ out = _)
      ((chooseAndSearch_spec_paths process c d s mayExtend fl _ _ _ sturmEmpty r si hsi).le_wp
        trivial)]
    rfl
  · rfl

/-- The bits of the flags of the search that the program reads after it, which do not depend on the
callback: the flag of the reversal as it came, the squares for odd degree and `|c_d| = 1`, and the
success of the divisor set-up up to the largest denominator `bHigh` for odd degree and
`|c_d| ≠ 1`; and the search intervals as they came, those that the Sturm step leaves. -/
theorem run_searchPoints_flags {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (c : List ℤ)
    (d H : ℕ) (s : SieveOptions) (mayExtend : Bool) (fl : CheckFlags) (bLow bHigh : ℕ)
    (domain : List (Double × Double)) (sturmEmpty : Bool) (print : String → σ → σ)
    (r : Delivery σ) :
    (Id.run (searchPoints process c d H s mayExtend fl bLow bHigh domain sturmEmpty print
        r)).reversed = fl.reversed ∧
      (Id.run (searchPoints process c d H s mayExtend fl bLow bHigh domain sturmEmpty print
        r)).useSquares = (d % 2 == 1 && (c.getD d 0).natAbs == 1) ∧
      (Id.run (searchPoints process c d H s mayExtend fl bLow bHigh domain sturmEmpty print
        r)).useSquares1 = (if (d % 2 == 1 && (c.getD d 0).natAbs != 1) = true then
          Id.run (Setup.setupUs1 c d bHigh) else none).isSome ∧
      (Id.run (searchPoints process c d H s mayExtend fl bLow bHigh domain sturmEmpty print
        r)).domain = domain := by
  refine Std.WP.Id.of_run_eq_wp rfl _ ((?_ : ⦃ True ⦄ searchPoints process c d H s mayExtend fl
    bLow bHigh domain sturmEmpty print r ⦃ fun out ↦ out.reversed = fl.reversed ∧
      out.useSquares = (d % 2 == 1 && (c.getD d 0).natAbs == 1) ∧ out.useSquares1 =
        (if (d % 2 == 1 && (c.getD d 0).natAbs != 1) = true then
          Id.run (Setup.setupUs1 c d bHigh) else none).isSome ∧
      out.domain = domain ⦄).le_wp trivial)
  vcgen [searchPoints, setupUs1_value, twoAdic_value, numClasses_value, meanBitsPerWord_value,
    chooseAndSearch_value]
  all_goals simp_all

-- The contract of the choice of the moduli (`Ratpoints.sievingInfo_spec`) as a statement about its
-- result, for the options of the sieve as the search normalizes them.
private theorem run_sievingInfo_spec (c : List ℤ) (u mayExtend : Bool) (s : SieveOptions)
    (a : ShapeArgs) (bpw : Float) :
    (∀ p, Id.run (sievingInfo c (degree c) u (degree c % 2 == 0) mayExtend s.normalize a bpw) =
        .error p → ∀ H q, ¬IsPoint c H q) ∧
      ∀ si, Id.run (sievingInfo c (degree c) u (degree c % 2 == 0) mayExtend s.normalize a bpw) =
        .ok si → IsSievingInfo c a.bHigh si :=
  Std.WP.Id.of_run_eq_wp rfl _ ((sievingInfo_spec c u _ mayExtend s.normalize a bpw).le_wp
    ⟨s.numPrimes_normalize_le, s.maxForbidden_normalize_nonneg, fun h ↦ by simpa using h⟩)

-- After the exits, the sieving with a result of the choice of the moduli as its contract gives it
-- delivers the points of the denominators of the search from `bLow` to `bHigh` in the well-formed
-- search intervals `dom` for a sound test of the sieve, whatever the callback and the flags.
private theorem exists_isSoundTest_run_sieving {c : List ℤ} {H : ℕ} (s : SieveOptions)
    (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow) (hbH : bHigh ≤ H)
    {dom : List (Double × Double)} (hdom : IntervalsWF (domainBits dom))
    {cls : Vector NumClass 64} {db : UInt64}
    (hcd : Id.run (numClasses (Id.run (twoAdic c (degree c)))) = (cls, db)) {si : SievingInfo}
    (hi : IsSievingInfo c bHigh si) (useJacobi : Bool) :
    ∃ S, IsSoundTest c H bLow bHigh S ∧ ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
      (fl : CheckFlags) (r : Delivery σ), r.quit = false → (Id.run (sieving process c (degree c) H
        s si.params fl (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1)
        (if (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1) = true then
          Id.run (Setup.setupUs1 c (degree c) bHigh) else none)
        si.checkDenom useJacobi si.forb si.forbVal si.entries si.magics cls db si.store bLow bHigh
        dom r)).1 = r.deliver process ((searchDens c (degree c) bLow bHigh).flatMap fun b : ℕ ↦
          ((numerators H).filter fun a : ℤ ↦ decide (InIntervals (domainValues dom) (a / b)) &&
            S b a).flatMap (checkNumWith (scaledCoeffs c (degree c) b)
              (if degree c % 2 = 1 then b else 1) b fl)) :=
  have h := isSoundRun_of_run_classOffsets hi hcd.symm rfl rfl
  exists_isSoundTest_run_sieveRun h.1 h.2 hH63 (si.params.one_le_arraySizeAt hH) hbLow hbH rfl
    hi.isForbiddenEntry hi.isForbiddenVal hi.checkDenom_eq dom hdom

-- At an exit of the search, on a curve without points, the test that lets no numerator through.
private theorem exists_isSoundTest_of_forall_not_isPoint {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {mayExtend : Bool} (hH : 1 ≤ H) {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow) (hbH : bHigh ≤ H)
    {dom : List (Double × Double)} {sturmEmpty : Bool} {D : List (WithBotTop ℚ × WithBotTop ℚ)}
    (hno : ∀ q, ¬IsPoint c H q)
    (h : ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (fl : CheckFlags) (r : Delivery σ),
      ((Id.run (searchPoints process c (degree c) H s mayExtend fl bLow bHigh dom sturmEmpty
          (fun _ s ↦ s) r)).info,
        (Id.run (searchPoints process c (degree c) H s mayExtend fl bLow bHigh dom sturmEmpty
          (fun _ s ↦ s) r)).total) = (r.info, r.total)) :
    ∃ S, IsSoundTest c H bLow bHigh S ∧ ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
      (fl : CheckFlags) (r : Delivery σ), r.quit = false →
        ((Id.run (searchPoints process c (degree c) H s mayExtend fl bLow bHigh dom sturmEmpty
            (fun _ s ↦ s) r)).info,
          (Id.run (searchPoints process c (degree c) H s mayExtend fl bLow bHigh dom sturmEmpty
            (fun _ s ↦ s) r)).total) =
        ((r.deliver process (searchList c H bLow bHigh D S fl)).info,
          (r.deliver process (searchList c H bLow bHigh D S fl)).total) :=
  ⟨_, isSoundTest_false_of_forall_not_isPoint hH hbLow hbH hno, fun process fl r _ ↦ by
    rw [h, searchList_false H bLow bHigh D
      (pointsAtInfinityList_eq_nil_of_forall_not_isPoint hH hno fl), Delivery.deliver_nil]⟩

-- On the path of the search through the sieving, for a result `si` of the choice of the moduli:
-- the points at infinity, then, unless the callback has stopped the search or the Sturm step has
-- left no interval, those of the sieving for a sound test.
private theorem exists_isSoundTest_run_searchPoints_of_eq_ok {c : List ℤ} {H : ℕ}
    (s : SieveOptions) (mayExtend : Bool) (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {bLow bHigh : ℕ}
    (hbLow : 1 ≤ bLow) (hbH : bHigh ≤ H) {dom : List (Double × Double)}
    (hdom : IntervalsWF (domainBits dom)) (sturmEmpty : Bool) {cls : Vector NumClass 64}
    {db : UInt64} (hcd : Id.run (numClasses (Id.run (twoAdic c (degree c)))) = (cls, db))
    (hex : (db == 0 && !(degree c % 2 == 1 || Setup.isSquare (c.getD (degree c) 0))) = false)
    {si : SievingInfo} (hsi : Id.run (sievingInfo c (degree c) (Setup.useCLong c (degree c))
      (degree c % 2 == 0) mayExtend s.normalize
      (searchShapeArgs c (degree c) H s.normalize bLow bHigh dom cls db)
      (Id.run (meanBitsPerWord (searchShapeArgs c (degree c) H s.normalize bLow bHigh dom cls
        db)))) = .ok si) :
    ∃ S, IsSoundTest c H bLow bHigh S ∧ ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
      (fl : CheckFlags) (r : Delivery σ), r.quit = false →
        ((Id.run (searchPoints process c (degree c) H s.normalize mayExtend fl bLow bHigh dom
            sturmEmpty (fun _ s ↦ s) r)).info,
          (Id.run (searchPoints process c (degree c) H s.normalize mayExtend fl bLow bHigh dom
            sturmEmpty (fun _ s ↦ s) r)).total) =
        ((r.deliver process (searchList c H bLow bHigh
            (if sturmEmpty then [] else domainValues dom) S fl)).info,
          (r.deliver process (searchList c H bLow bHigh
            (if sturmEmpty then [] else domainValues dom) S fl)).total) := by
  obtain ⟨S, hS, hrun⟩ := exists_isSoundTest_run_sieving s.normalize hH hH63 hbLow hbH hdom hcd
    ((run_sievingInfo_spec c _ mayExtend s _ _).2 si hsi) _
  refine ⟨S, hS, fun process fl r hr ↦ ?_⟩
  rw [run_searchPoints_paths process c _ H _ mayExtend fl bLow bHigh dom sturmEmpty r _ _ hcd hex
    hsi]
  cases sturmEmpty
  · simp only [Bool.false_eq_true, ↓reduceIte, Bool.or_false]
    rw [searchList, ← Delivery.ite_quit_eq_deliver_append process
      (pointsAtInfinity_eq_deliver process _ _ fl hr) (hrun process fl _)]
  · simp [searchList_nil, ← pointsAtInfinity_eq_deliver process _ _ fl hr]

/-- For options of the sieve as the search normalizes them, `1 ≤ H < 2 ^ 63`, the denominators from
`bLow ≥ 1` to the largest denominator `bHigh ≤ H` and well-formed search intervals `dom`, there is
a sound test of the numerators (`Ratpoints.IsSoundTest`) for which the search of the polynomial with
the coefficient list `c`, of its degree, with any callback, flags of the check and delivery whose
flag is clear and the print channel that prints nothing, gives the data and the count of the
delivery of the points of `Ratpoints.searchList` for the values of `dom`, or for no interval when
the Sturm step has left none (`sturmEmpty`): the test is that of the sieve with the moduli that the
choice gives each block (`Ratpoints.sievingInfo_spec`, `Ratpoints.exists_isSoundTest_run_sieveRun`),
which depends neither on the callback nor on the flags, but on the search intervals, which the
estimate of the run reads, and with it the choice and the decisions of the correction, the points at
infinity come first (`Ratpoints.Sieve.pointsAtInfinity_eq_deliver`), and the search returns after
them when the callback has stopped it or the Sturm step has left no interval
(`Ratpoints.searchList_nil`); when the search takes the 2-adic exit or an exit of the choice of the
moduli, the curve has no points (`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`,
`Ratpoints.sievingInfo_spec`), so that the test that lets no numerator through is sound and there
is no point at infinity. -/
theorem exists_isSoundTest_run_searchPoints {c : List ℤ} {H : ℕ} (s : SieveOptions)
    (mayExtend : Bool) (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow)
    (hbH : bHigh ≤ H) {dom : List (Double × Double)} (hdom : IntervalsWF (domainBits dom))
    (sturmEmpty : Bool) :
    ∃ S, IsSoundTest c H bLow bHigh S ∧ ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
      (fl : CheckFlags) (r : Delivery σ), r.quit = false →
        ((Id.run (searchPoints process c (degree c) H s.normalize mayExtend fl bLow bHigh dom
            sturmEmpty (fun _ s ↦ s) r)).info,
          (Id.run (searchPoints process c (degree c) H s.normalize mayExtend fl bLow bHigh dom
            sturmEmpty (fun _ s ↦ s) r)).total) =
        ((r.deliver process (searchList c H bLow bHigh
            (if sturmEmpty then [] else domainValues dom) S fl)).info,
          (r.deliver process (searchList c H bLow bHigh
            (if sturmEmpty then [] else domainValues dom) S fl)).total) := by
  rcases hcd : Id.run (numClasses (Id.run (twoAdic c (degree c)))) with ⟨cls, db⟩
  rcases hex : (db == 0 && !(degree c % 2 == 1 || Setup.isSquare (c.getD (degree c) 0)))
  · rcases hsi : Id.run (sievingInfo c (degree c) (Setup.useCLong c (degree c)) (degree c % 2 == 0)
      mayExtend s.normalize (searchShapeArgs c (degree c) H s.normalize bLow bHigh dom cls db)
      (Id.run (meanBitsPerWord (searchShapeArgs c (degree c) H s.normalize bLow bHigh dom cls
        db)))) with p | si
    · exact exists_isSoundTest_of_forall_not_isPoint hH hbLow hbH
        ((run_sievingInfo_spec c _ mayExtend s _ _).1 p hsi H) fun process fl r ↦
          run_searchPoints_paths process c _ H _ mayExtend fl bLow bHigh dom sturmEmpty r _ _ hcd
            hex hsi
    exact exists_isSoundTest_run_searchPoints_of_eq_ok s mayExtend hH hH63 hbLow hbH hdom
      sturmEmpty hcd hex hsi
  have hdb : denBits (Id.run (twoAdic c (degree c))) = 0 := by
    rw [← snd_run_numClasses, hcd]; simpa using (Bool.and_eq_true _ _).mp hex |>.1
  exact exists_isSoundTest_of_forall_not_isPoint hH hbLow hbH (not_isPoint_of_denBits_eq_zero hdb H)
    fun process fl r ↦ run_searchPoints_paths process c _ H _ mayExtend fl bLow bHigh dom
      sturmEmpty r _ _ hcd hex rfl

/-! ### The protocol of the search -/

/-- For options of the sieve as the search normalizes them, `1 ≤ H < 2 ^ 63`, the denominators from
`bLow ≥ 1` to `bHigh ≤ H` and well-formed search intervals, the search of the polynomial with the
coefficient list `c`, of its degree, with a callback, flags of the check, the print channel that
prints nothing and a delivery whose flag is clear, gives the data and the count of the delivery
(`Ratpoints.Delivery.deliver`) of the list of the points that the search with the appending callback
(`Ratpoints.appendPoint`) gives for the same flags from the empty array: both deliver the points of
`Ratpoints.searchList` for the test of the sieve
(`Ratpoints.exists_isSoundTest_run_searchPoints`). -/
theorem run_searchPoints_eq_deliver {c : List ℤ} {H : ℕ} (s : SieveOptions) (mayExtend : Bool)
    (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow) (hbH : bHigh ≤ H)
    {dom : List (Double × Double)} (hdom : IntervalsWF (domainBits dom)) (sturmEmpty : Bool)
    {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (fl : CheckFlags) {r : Delivery σ}
    (hr : r.quit = false) :
    ((Id.run (searchPoints process c (degree c) H s.normalize mayExtend fl bLow bHigh dom sturmEmpty
        (fun _ s ↦ s) r)).info,
      (Id.run (searchPoints process c (degree c) H s.normalize mayExtend fl bLow bHigh dom
        sturmEmpty (fun _ s ↦ s) r)).total) =
      let r' := r.deliver process (Id.run (searchPoints appendPoint c (degree c) H s.normalize
        mayExtend fl bLow bHigh dom sturmEmpty (fun _ s ↦ s) ⟨#[], 0, false⟩)).info.toList
      (r'.info, r'.total) := by
  obtain ⟨S, -, hS⟩ :=
    exists_isSoundTest_run_searchPoints (c := c) s mayExtend hH hH63 hbLow hbH hdom sturmEmpty
  have h := congr(Prod.fst $(hS appendPoint fl ⟨#[], 0, false⟩ rfl))
  simp only [Delivery.deliver_appendPoint, List.toArray] at h
  rw [hS process fl r hr, h]
  simp

/-- For options of the sieve as the search normalizes them, `1 ≤ H < 2 ^ 63`, the denominators from
`bLow ≥ 1` to `bHigh ≤ H` and well-formed search intervals `dom`, the search with the appending
callback gives the list of `Ratpoints.searchList` for the values of `dom`, or for no interval when
the Sturm step has left none (`sturmEmpty`), and a sound test of the sieve, for every choice of the
flags (`Ratpoints.exists_isSoundTest_run_searchPoints`). -/
theorem exists_isSoundTest_run_searchPoints_appendPoint {c : List ℤ} {H : ℕ} (s : SieveOptions)
    (mayExtend : Bool) (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow)
    (hbH : bHigh ≤ H) {dom : List (Double × Double)} (hdom : IntervalsWF (domainBits dom))
    (sturmEmpty : Bool) :
    ∃ S, IsSoundTest c H bLow bHigh S ∧ ∀ fl : CheckFlags,
      (Id.run (searchPoints appendPoint c (degree c) H s.normalize mayExtend fl bLow bHigh dom
        sturmEmpty (fun _ s ↦ s) ⟨#[], 0, false⟩)).info.toList =
      searchList c H bLow bHigh (if sturmEmpty then [] else domainValues dom) S fl := by
  obtain ⟨S, hS, hrun⟩ :=
    exists_isSoundTest_run_searchPoints (c := c) s mayExtend hH hH63 hbLow hbH hdom sturmEmpty
  refine ⟨S, hS, fun fl ↦ ?_⟩
  simpa [Delivery.deliver_appendPoint] using
    congr(($(hrun appendPoint fl ⟨#[], 0, false⟩ rfl)).1.toList)

end Ratpoints

end
