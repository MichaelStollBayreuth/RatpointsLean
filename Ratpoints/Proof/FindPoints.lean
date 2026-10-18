/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Forbidden
public import Ratpoints.Proof.Moduli
public import Ratpoints.Proof.Region
public import Ratpoints.Proof.Setup
public import Ratpoints.Proof.Stages
public import Ratpoints.Spec.Order

import Ratpoints.Mathlib.Data.List.Basic
import Ratpoints.Mathlib.Data.List.Nodup
import Ratpoints.Proof.Bounds
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
import Ratpoints.Proof.Denominators
import Ratpoints.Proof.Order
import Ratpoints.Proof.Params
import Ratpoints.Proof.Shapes
import Ratpoints.Proof.Sieve
import Ratpoints.Proof.Sift
import Ratpoints.Proof.Tables
import Ratpoints.Proof.TwoAdic
import Std.Tactic.Do

/-!
# The search delivers the points of a sound sieve

The search of the polynomial that the set-up hands on delivers to the callback, for well-formed
parameters, the points at infinity followed, for the denominators that the loop of its shape visits
in its order (`Ratpoints.searchDens`), by the points of the check with the flags of the search of
the numerators `a` with `a / b` in the search intervals over the values of their ends
(`Ratpoints.InIntervals`) that a test of the sieve lets through (`Ratpoints.searchList`), and it
returns when the callback stops the search; the test does not depend on the callback, the flags or
the search intervals, and it lets the numerator of every point through (`Ratpoints.IsSoundTest`),
also when the search takes one of its exits, where the curve has no points
(`Ratpoints.exists_isSoundTest_run_searchPoints`). The search intervals are those of a search
without intervals, the default interval `[-h, h]`, which holds every `a / b` of the search
(`Ratpoints.exists_run_searchIntervals_nil`). So the search with a callback delivers the list that
the search with the appending callback returns (`Ratpoints.run_searchPoints_eq_deliver`), and
without `RATPOINTS_NO_CHECK` that list is the brute-force reference over the candidate `(1, 0)` and
the denominators of the search with the numerators in the search intervals, mapped by
`Ratpoints.Sieve.swapPoint` when the flag of the reversal is set, without the points with `y < 0`
under `RATPOINTS_NO_Y` (`Ratpoints.searchList_of_noCheck_eq_false`): for the default interval, the
points of the reference in another order, except where the shape visits the denominators in
increasing order, every shape but that of the divisors of the leading coefficient times squares
(`Ratpoints.perm_bruteForce_append_flatMap_searchDens`). What `Ratpoints.findPoints` and
`Ratpoints.findPointsWith` return, and their refusals, are in `Ratpoints.Proof.Output`.

## Main definitions

* `Ratpoints.Sieve.SieveEntry.IsSound`: a sieve entry with a positive modulus that admits the
  numerator of every point.
* `Ratpoints.searchDens`: the denominators of the search, in the order of its loop.
* `Ratpoints.searchList`, `Ratpoints.IsSoundTest`: the points that the search delivers for a test of
  the numerators, and a test that lets the numerator of every point through.
* `Ratpoints.Sieve.IsSoundRun`: what the run of the search needs of its arguments.
* `Ratpoints.SievingInfoEntries`, `Ratpoints.SievingInfoInvariant`: what the loop over the moduli of
  `Ratpoints.sievingInfo` has made before a return, and its invariant.
* `Ratpoints.IsSievingInfo`: what the search needs of the result of `Ratpoints.sievingInfo`.

## Main statements

* `Ratpoints.perm_bruteForce_append_flatMap_searchDens`: the points at infinity and those of the
  denominators of the search are a permutation of the brute-force reference;
  `Ratpoints.append_flatMap_searchDens_eq_bruteForce`: they are the reference when the denominators
  of the search are `1, …, H` (`Ratpoints.searchDens_eq_range'`).
* `Ratpoints.searchDens_eq_searchDenominators`: the denominators of the search are those of the
  specification of the order.
* `Ratpoints.searchList_of_noCheck_eq_false`: without `RATPOINTS_NO_CHECK`, the points that the
  search delivers for a sound test are those of the brute-force reference with the numerators in
  the search intervals, mapped after a reversal, without those with `y < 0` under `RATPOINTS_NO_Y`.
* `Ratpoints.exists_eq_of_mem_searchList_of_noCheck`, `Ratpoints.nodup_searchList_of_noCheck`:
  under `RATPOINTS_NO_CHECK`, the search delivers distinct triples `(x, 0, z)` of normalized pairs
  `(x, z)` of height at most `H` (`Ratpoints.IsNormalizedPair`), whatever the test;
  `Ratpoints.map_searchList_sublist`: the points that it delivers without `RATPOINTS_NO_CHECK` and
  with `RATPOINTS_NO_Y`, with `y` replaced by `0`, are a sublist of them, for the same test.
* `Ratpoints.exists_isSoundTest_run_sieveRun`: the run of the shape that the search chooses, with
  sound arguments and the bounds of well-formed search intervals, delivers the points of the
  numerators in the search intervals that a sound test lets through.
* `Ratpoints.sievingInfo_spec`: for well-formed parameters, the sieve entries that
  `Ratpoints.sievingInfo` makes are those of the moduli, in their order, are sound, have the fields
  that the packing reads and the tables of inverses of their factors, and hold the reciprocals of
  their moduli, which it returns in the order of the entries, those of the third stage having the
  shape that it needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), its forbidden divisors are among
  those that the loops of the tables and of the further primes may record, and the store of the
  tables of rows that it returns fits the entries (`Ratpoints.Sieve.RowStore.Fits`); when it returns
  none, the curve has no points.
* `Ratpoints.run_searchPoints_flags`: the bits of the flags that the search writes back do not
  depend on the callback.
* `Ratpoints.exists_isSoundTest_run_searchPoints`: for well-formed parameters, `1 ≤ H < 2 ^ 63` and
  the degree of the polynomial, there is a sound test for which the search, with any callback, flags
  and delivery whose flag of the stop is clear, gives the data and the count of the delivery of the
  points of `Ratpoints.searchList` for the values of the default search interval.
* `Ratpoints.run_searchPoints_eq_deliver`: the search with a callback gives the data and the count
  of the delivery of the list of the search with the appending callback.

## Proof

The run of a shape delivers, over the list `l` that its list filters, the points of the numerators
that pass the filter, the tests of the shape, the class word and the sieve entries
(`Ratpoints.Sieve.run_sieveRun_of_eq_filter`), for pieces of at least one bit array, sieve entries
and their reciprocals, of which those of the first two stages have their tables of inverses, the row
offsets of the packings of the classes, which pack the words of the 2-adic information, and a store
of the tables of their rows that fits them, and those of the third stage the shape that it needs
(`Ratpoints.Sieve.IsSoundRun`), and denominators and a height below `2 ^ 63`, the numerators of each
denominator lying in the ranges that the bounds of well-formed search intervals give for it
(`Ratpoints.Sieve.rangesFor_run_exactBounds`), which are those with `a / b` in the intervals
(`Ratpoints.Sieve.inRanges_numeratorRanges`). This test is sound: every numerator of a point passes
the word of the class of its denominator and survives the sieve entries, when they are sound
(`Ratpoints.Sieve.classBit_and_survives_of_ne_nil`), and every denominator of a point passes the
filter and the tests of the shape that `Ratpoints.Sieve.runSetup` chooses: the squares for odd
degree and `|c_d| = 1` (`Ratpoints.isSquare_of_sq_eq_binaryForm_of_odd`,
`Ratpoints.Sieve.squaresDens_eq_filter`), the divisors with their valuation test
(`Ratpoints.Sieve.run_denInfoTest_of_sq_eq`), the words with the forbidden divisors and the Jacobi
test (`Ratpoints.Sieve.toList_run_wordsDens`, `Ratpoints.Sieve.getLsbD_denBits_and_all_of_sq_eq`,
`Ratpoints.Sieve.run_wordsTest_of_sq_eq`), and every denominator, by the class test
(`Ratpoints.Sieve.getElem!_twoAdic_ne_zero`). The divisor shape visits each denominator of a point
once (`Ratpoints.exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd`,
`Ratpoints.Setup.mem_iff_of_setupUs1_eq_some`, `Ratpoints.Sieve.mem_squares1Dens_iff`,
`Ratpoints.Sieve.nodup_squares1Dens`), so that its list gives a permutation of the reference
(`List.perm_flatMap_of_nodup`). Without `RATPOINTS_NO_CHECK`, the points at infinity delivered are
those of the candidate `(1, 0)` of the reference for odd degree or `c_d ≠ 0`, mapped and filtered
(`Ratpoints.Sieve.pointsAtInfinityList_eq_filter_map_pointsOfDen`), and the check with the flags
gives the points of the reference, mapped and filtered
(`Ratpoints.Sieve.flatMap_checkNumWith_of_noCheck_eq_false`). In the search, the pieces have at
least one bit array (`Ratpoints.Params.one_le_arraySizeAt`), and the height, the largest
denominator, is below `2 ^ 63` by the refusals of `Ratpoints.findPoints`; the tables of the loop of
the tables are those of the reference
(`Ratpoints.Sieve.getElem_eq_examinePrime_of_run_examinePrimes_eq_some`), so that the sieve entries
that the loop over the moduli of well-formed parameters makes are sound, have the tables of inverses
of their factors and the fields that the packing reads, and hold the reciprocals of their moduli,
which it returns in their order, and those of the moduli of the third stage, primes among the first
`Ratpoints.numPrimes` of the table, have the prime with the table of the reference as their only
factor (`Ratpoints.makeModulus?_spec`, `Ratpoints.SievingInfoInvariant.push`,
`Ratpoints.Sieve.isPrimeEntry_examinePrime`); each entry has the reference to its table of rows and
the kind of its builder of its position, so that the store that the loop of the tables starts
(`Ratpoints.Sieve.primeStore_of_run_examinePrimes_eq_some`) and the tables of rows of the entries
complete holds the rows of the references of the run (`Ratpoints.Sieve.runRows`,
`Ratpoints.Sieve.RowStore.MadeFor`), which every entry fits (`Ratpoints.SievingInfoEntries.fits`),
also with the inverses of the strides (`Ratpoints.Sieve.RowStore.Fits.map_dinv`); and the forbidden
divisors are those that the loops of the tables and of the further primes may record
(`Ratpoints.Sieve.isForbiddenEntry_of_run_examinePrimes_eq_some`, `Ratpoints.Sieve.forbidden_spec`
and their counterparts for the valuations), with the switch of the forbidden divisors on or off; the
classes that `Ratpoints.Sieve.numClasses` makes pack the words of the 2-adic information, with
`den_bits` the word of `Ratpoints.Sieve.denBits` (`Ratpoints.Sieve.snd_run_numClasses`), and
`Ratpoints.Sieve.classOffsets`, in the array of `Ratpoints.Sieve.numPackings` rows, gives each class
with a pattern its row offsets and the entries the inverses of the strides
(`Ratpoints.Sieve.numClasses_spec`, `Ratpoints.Sieve.classOffsets_spec`). The points at infinity
come first (`Ratpoints.Sieve.pointsAtInfinity_eq_deliver`), and the search returns after them when
the callback has stopped it, which the delivery of the whole list accounts for
(`Ratpoints.Delivery.deliver_of_quit`). When the search takes the exit of the loop of the tables or
of a modulus, the curve has no points (`Ratpoints.Sieve.not_isPoint_of_run_examinePrimes_eq_none`,
`Ratpoints.makeModulus?_spec`), and when it takes the 2-adic exit, no class of the denominators
admits a numerator, the word `den_bits` of the classes being that of `Ratpoints.Sieve.denBits`
(`Ratpoints.Sieve.snd_run_numClasses`), so that the curve has no points either
(`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`): the reference is empty, the test that lets no
numerator through is sound, and there is no point at infinity to deliver, whatever the flags
(`Ratpoints.Sieve.pointsAtInfinityList_eq_nil_of_pointsOfDen_eq_nil`).

## Implementation notes

The search is proved by cases on the values of its components, the classes and the word of the
2-adic information, the 2-adic exit and the result of `Ratpoints.sievingInfo`, which do not depend
on the callback or the flags, so that the test of the sieve is chosen before them; the data and the
count of the search along its paths, for these values, are proved with `vcgen`, which reads the
components through private specifications `⦃True⦄ x ⦃fun r ↦ r = Id.run x⦄`, so that its
verification conditions speak of their values. The run of the shape that `Ratpoints.Sieve.runSetup`
chooses is handled by cases in one lemma. The exits use only that the denominators of the search lie
in `1, …, H`, so that the contract of the search does not rest on the permutation of the reference
(`Ratpoints.perm_bruteForce_append_flatMap_searchDens`), which the theorems on
`Ratpoints.findPoints` use. The contract of `Ratpoints.sievingInfo` is proved with `vcgen` as well,
with the loop invariant `Ratpoints.SievingInfoInvariant`, reading the loop of the tables through
such a private specification and the further primes and the sieve entries of the moduli through
their contracts.
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

/-- A sieve entry that lets the numerator of every point of the curve `y ^ 2 = F(x, z)` with the
coefficient list `c` through: its modulus is positive, and its row of the denominator `b` admits the
numerator `a` of every triple `(a, y, b)` with `gcd(a, b) = 1` and `y ^ 2 = F(a, b)`. For
well-formed parameters, the search makes only such entries (`Ratpoints.sievingInfo_spec`). -/
structure SieveEntry.IsSound (c : List ℤ) (e : SieveEntry) : Prop where
  /-- The modulus is positive. -/
  pos : 0 < e.p
  /-- The row of the denominator of every point admits its numerator. -/
  admits_of_sq_eq {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    e.admits b a = true

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

/-! ### The denominators of the search -/

/-- The denominators of the search of the polynomial with the coefficient list `c` of degree `d`,
for the height `H`, in the order of its loop: the divisors of the leading coefficient times squares
(`Ratpoints.Sieve.squares1Dens`) when `d` is odd, `|c_d| ≠ 1` and the divisor set-up succeeds
(`Ratpoints.Setup.setupUs1`), and `1, …, H` otherwise, of which the other shapes visit, in this
order, those that their tests let through (`Ratpoints.Sieve.Shape`). -/
def searchDens (c : List ℤ) (d H : ℕ) : List ℕ :=
  match if d % 2 == 1 && (c.getD d 0).natAbs != 1 then Id.run (Setup.setupUs1 c d H) else none with
  | some (_, divisors) => squares1Dens divisors 1 H
  | none => List.range' 1 H

/-- The denominators of the search are `1, …, H` when it does not use the divisor shape: for even
degree, for `|c_d| = 1`, and when the divisor set-up fails. -/
theorem searchDens_eq_range' {c : List ℤ} {d H : ℕ}
    (h : d % 2 = 0 ∨ (c.getD d 0).natAbs = 1 ∨ Id.run (Setup.setupUs1 c d H) = none) :
    searchDens c d H = List.range' 1 H := by
  rcases h with h | h | h
  · simp [searchDens, h]
  · simp only [searchDens, h, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  · simp [searchDens, h]

-- The denominators of the search are `1, …, H` or, for odd degree, those of the divisor shape.
private theorem searchDens_eq_range'_or (c : List ℤ) (d H : ℕ) :
    searchDens c d H = List.range' 1 H ∨ ∃ info divisors, d % 2 = 1 ∧
      Id.run (Setup.setupUs1 c d H) = some (info, divisors) ∧
        searchDens c d H = squares1Dens divisors 1 H := by
  rw [searchDens]
  split
  · rename_i h
    obtain ⟨hcond, hs⟩ := Option.ite_none_right_eq_some.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact .inr ⟨_, _, hcond.1, hs, rfl⟩
  · exact .inl rfl

-- The reference with its points at infinity apart.
private theorem bruteForce_eq_append (c : List ℤ) {H : ℕ} (hH : 1 ≤ H) :
    bruteForce c H = pointsOfDen c (degree c) 0 [1] ++
      (List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H) := by
  simp [bruteForce, hH, List.range'_eq_map_range, Nat.add_comm, List.flatMap_map,
    BruteForce.degree_eq]

-- The divisors of the set-up for odd degree are positive.
private theorem pos_of_mem_of_setupUs1_eq_some {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (hd : degree c % 2 = 1) {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) H) = some (info, divisors)) {s : ℕ}
    (hs' : s ∈ divisors) : 0 < s :=
  Nat.pos_of_ne_zero ((Setup.mem_iff_of_setupUs1_eq_some hs
    (getD_degree_ne_zero_of_pos (by lia)) hH).mp hs').1.ne_zero

-- The divisor shape of a successful set-up for odd degree lists each denominator once.
private theorem nodup_squares1Dens_of_setupUs1_eq_some {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (hd : degree c % 2 = 1) {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) H) = some (info, divisors)) :
    (squares1Dens divisors 1 H).Nodup :=
  have hc : c.getD (degree c) 0 ≠ 0 := getD_degree_ne_zero_of_pos (by lia)
  nodup_squares1Dens (Setup.nodup_of_setupUs1_eq_some hs hc)
    (fun _ hs' ↦ ((Setup.mem_iff_of_setupUs1_eq_some hs hc hH).mp hs').1) 1 H

-- The divisor shape over `1, …, H` lists denominators of `1, …, H`.
private theorem mem_range'_of_mem_squares1Dens {divisors : List ℕ} {H b : ℕ}
    (hb : b ∈ squares1Dens divisors 1 H) : b ∈ List.range' 1 H :=
  have := le_and_le_of_mem_squares1Dens le_rfl hb
  List.mem_range'_1.mpr ⟨this.1, by lia⟩

-- The denominators of the search lie in `1, …, H`.
private theorem mem_range'_of_mem_searchDens {c : List ℤ} {H b : ℕ}
    (hb : b ∈ searchDens c (degree c) H) : b ∈ List.range' 1 H := by
  obtain h | ⟨_, _, -, -, h⟩ := searchDens_eq_range'_or c (degree c) H
  · rwa [h] at hb
  · exact mem_range'_of_mem_squares1Dens (h ▸ hb)

/-- The denominators of the search are distinct: `1, …, H`, or for odd degree the products of the
distinct squarefree divisors of the set-up with squares (`Ratpoints.Sieve.nodup_squares1Dens`). -/
theorem nodup_searchDens (c : List ℤ) {H : ℕ} (hH : 1 ≤ H) :
    (searchDens c (degree c) H).Nodup := by
  obtain h | ⟨info, divisors, hd, hs, h⟩ := searchDens_eq_range'_or c (degree c) H
  · exact h ▸ List.nodup_range'
  · exact h ▸ nodup_squares1Dens_of_setupUs1_eq_some hH hd hs

/-- The denominators of the search of the polynomial with the coefficient list `c` of its degree are
those of the specification of the order (`Ratpoints.searchDenominators`), for `H ≥ 1`: the divisor
set-up succeeds exactly when the specification takes the divisor shape, with the divisors of
`Ratpoints.binaryDivisors` (`Ratpoints.Setup.map_snd_run_setupUs1`). -/
theorem searchDens_eq_searchDenominators (c : List ℤ) {H : ℕ} (hH : 1 ≤ H) :
    searchDens c (degree c) H = searchDenominators maxDivisors c H := by
  rw [searchDens, searchDenominators]
  by_cases hd : degree c % 2 = 1 ∧ (c.getD (degree c) 0).natAbs ≠ 1
  · have hs := Setup.map_snd_run_setupUs1 (getD_degree_ne_zero_of_pos (c := c) (by lia)) hH
    rw [ite_eq_left (show (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1) = true by
      simpa using hd)]
    simp only [hd.1, hd.2, true_and, ne_eq, not_false_eq_true]
    rcases h : Id.run (Setup.setupUs1 c (degree c) H) with _ | ⟨info, divs⟩ <;> rw [h] at hs <;>
      split_ifs at hs ⊢
    · simp at hs
    · rfl
    · simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      exact squares1Dens_one_eq_filter (fun e he ↦ pos_of_mem_binaryDivisors he) H
    · simp at hs
  · rw [ite_eq_right (by simpa using hd), ite_eq_right (by tauto)]

/-- The divisor shape visits each denominator of a point once, so that it gives a permutation of
the points of the denominators `1, …, H`: the denominator of every point is `s k ^ 2` with `s`
squarefree and dividing `c_d`, so one of the divisors of the set-up, and the shape lists each such
product once (`List.perm_flatMap_of_nodup`). -/
theorem perm_flatMap_squares1Dens {c : List ℤ} {H : ℕ} (hH : 1 ≤ H) (hd : degree c % 2 = 1)
    {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) H) = some (info, divisors)) :
    ((squares1Dens divisors 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).Perm
      ((List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)) := by
  have hc : c.getD (degree c) 0 ≠ 0 := getD_degree_ne_zero_of_pos (by lia)
  have hmem (s : ℕ) := Setup.mem_iff_of_setupUs1_eq_some hs hc hH (s := s)
  refine List.perm_flatMap_of_nodup List.nodup_range'
    (nodup_squares1Dens_of_setupUs1_eq_some hH hd hs) (fun _ ↦ mem_range'_of_mem_squares1Dens)
    fun b hb hne ↦ ?_
  have hb' := List.mem_range'_1.mp hb
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil hne
  obtain ⟨s, k, hsq, hdvd, hbsk⟩ := exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd hd hg hy
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hbsk; lia
  have hsb : s ≤ s * k * k := by
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right s (Nat.mul_pos hk hk)
  exact (mem_squares1Dens_iff (fun _ ↦ pos_of_mem_of_setupUs1_eq_some hH hd hs) le_rfl).mpr
    ⟨hb'.1, by lia, s, (hmem s).mpr ⟨hsq, hdvd, by lia⟩, k, hbsk⟩

/-- The points at infinity and those of the denominators of the search are a permutation of the
brute-force reference (`Ratpoints.perm_flatMap_squares1Dens`). -/
theorem perm_bruteForce_append_flatMap_searchDens (c : List ℤ) {H : ℕ} (hH : 1 ≤ H) :
    (pointsOfDen c (degree c) 0 [1] ++ (searchDens c (degree c) H).flatMap fun b : ℕ ↦
      pointsOfDen c (degree c) b (numerators H)).Perm (bruteForce c H) := by
  rw [bruteForce_eq_append c hH]
  refine .append_left _ ?_
  obtain h | ⟨info, divisors, hd, hs, h⟩ := searchDens_eq_range'_or c (degree c) H
  · rw [h]
  · rw [h]
    exact perm_flatMap_squares1Dens hH hd hs

theorem append_flatMap_searchDens_eq_bruteForce {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (hs : searchDens c (degree c) H = List.range' 1 H) :
    pointsOfDen c (degree c) 0 [1] ++ (searchDens c (degree c) H).flatMap
      (fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)) = bruteForce c H := by
  rw [hs, bruteForce_eq_append c hH]

/-! ### The points that the search delivers -/

/-- The points that the search of the polynomial with the coefficient list `c`, of its degree,
delivers for the height `H`, the search intervals `D` over the values of their ends and the flags
`fl` of the check, for the test `S b a` of the numerators `a` over the denominators `b` of the
search: the points at infinity (`Ratpoints.Sieve.pointsAtInfinityList`), then, for the denominators
`b` of the search in the order of its loop (`Ratpoints.searchDens`), the points of the check with
the flags (`Ratpoints.Sieve.checkNumWith`) of the numerators `-H, …, H` with `a / b` in one of the
intervals (`Ratpoints.InIntervals`) that pass `S b`. For well-formed parameters the test of the
sieve is one that lets the numerator of every point through (`Ratpoints.IsSoundTest`,
`Ratpoints.exists_isSoundTest_run_searchPoints`). -/
def searchList (c : List ℤ) (H : ℕ) (D : List (WithBotTop ℚ × WithBotTop ℚ)) (S : ℕ → ℤ → Bool)
    (fl : CheckFlags) : List (ℤ × ℤ × ℤ) :=
  pointsAtInfinityList c (degree c) fl ++ (searchDens c (degree c) H).flatMap fun b : ℕ ↦
    ((numerators H).filter fun a : ℤ ↦ decide (InIntervals D (a / b)) && S b a).flatMap
      (checkNumWith (scaledCoeffs c (degree c) b) (if degree c % 2 = 1 then b else 1) b fl)

/-- A test `S b a` of the numerators `a` of `-H, …, H` over the denominators `b` of the search
(`Ratpoints.searchDens`) that lets the numerator of every point of the curve `y ^ 2 = F(x, z)` with
the coefficient list `c` through. -/
def IsSoundTest (c : List ℤ) (H : ℕ) (S : ℕ → ℤ → Bool) : Prop :=
  ∀ b ∈ searchDens c (degree c) H, ∀ a ∈ numerators H, pointsOfDen c (degree c) b [a] ≠ [] →
    S b a = true

/-- Without `RATPOINTS_NO_CHECK`, for a sound test and `c` of positive degree, the points that the
search delivers are those of the brute-force reference over the candidate `(1, 0)` and the
denominators of the search with the numerators `a` of `-H, …, H` with `a / b` in one of the search
intervals, in this order, mapped by `Ratpoints.Sieve.swapPoint` after a reversal, without those
with `y < 0` under `RATPOINTS_NO_Y`: a sound test leaves out only numerators without points
(`Ratpoints.BruteForce.pointsOfDen_filter_of_ne`). -/
theorem searchList_of_noCheck_eq_false {c : List ℤ} {H : ℕ} {S : ℕ → ℤ → Bool}
    (hS : IsSoundTest c H S) (hc : 0 < degree c) (D : List (WithBotTop ℚ × WithBotTop ℚ))
    {fl : CheckFlags} (hn : fl.noCheck = false) :
    searchList c H D S fl = ((pointsOfDen c (degree c) 0 [1] ++
      (searchDens c (degree c) H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b
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
theorem searchList_false {c : List ℤ} (H : ℕ) (D : List (WithBotTop ℚ × WithBotTop ℚ))
    {fl : CheckFlags} (h : pointsAtInfinityList c (degree c) fl = []) :
    searchList c H D (fun _ _ ↦ false) fl = [] := by
  simp [searchList, h]

/-- The points that the search delivers are those of the search without the flag of the
reversal, mapped by `Ratpoints.Sieve.swapPoint` when it is set. -/
theorem searchList_eq_map (c : List ℤ) (H : ℕ) (D : List (WithBotTop ℚ × WithBotTop ℚ))
    (S : ℕ → ℤ → Bool) (fl : CheckFlags) :
    searchList c H D S fl = (searchList c H D S { fl with reversed := false }).map
      (if fl.reversed then swapPoint else id) := by
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

/-- Under `RATPOINTS_NO_CHECK`, the search delivers triples `(x, 0, z)` of pairs `(x, z)` of
normalized points of height at most `H` (`Ratpoints.IsNormalizedPair`): the survivors `(a, 0, b)`
of the numerators `a` prime to the denominators `b` of the search and the point `(1, 0, 0)` at
infinity, mapped after a reversal (`Ratpoints.IsNormalizedPair.swapPoint`). -/
theorem exists_eq_of_mem_searchList_of_noCheck {c : List ℤ} {H : ℕ}
    {D : List (WithBotTop ℚ × WithBotTop ℚ)} {S : ℕ → ℤ → Bool} {fl : CheckFlags}
    (hc : fl.noCheck = true) (hH : 1 ≤ H) {q : ℤ × ℤ × ℤ} (hq : q ∈ searchList c H D S fl) :
    ∃ x z, q = (x, 0, z) ∧ IsNormalizedPair H x z := by
  simp only [searchList, List.mem_append, List.mem_flatMap, List.mem_filter,
    mem_checkNumWith_of_noCheck hc] at hq
  rcases hq with hq | ⟨b, hb, a, ⟨ha, -⟩, hg, rfl⟩
  · rw [eq_of_mem_pointsAtInfinityList_of_noCheck hc hq]
    exact exists_map_eq_of_isNormalizedPair ⟨rfl, .inr ⟨rfl, rfl⟩, by simpa using hH, by lia⟩ _
  · have hb' := List.mem_range'_1.mp (mem_range'_of_mem_searchDens hb)
    exact exists_map_eq_of_isNormalizedPair ⟨hg, .inl (by lia), mem_numerators_iff.mp ha,
      by lia⟩ _

-- Under `RATPOINTS_NO_CHECK` and without the flag of the reversal, the survivors `(a, 0, b)` that
-- the search delivers are distinct pairs over distinct denominators `b ≥ 1`
-- (`Ratpoints.nodup_searchDens`), the point `(1, 0, 0)` at infinity apart.
private theorem nodup_searchList_of_noCheck_of_reversed_eq_false {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (D : List (WithBotTop ℚ × WithBotTop ℚ)) (S : ℕ → ℤ → Bool) {fl : CheckFlags}
    (hc : fl.noCheck = true) (hr : fl.reversed = false) :
    (searchList c H D S fl).Nodup := by
  have hmem {b : ℕ} {a : ℤ} {q : ℤ × ℤ × ℤ} (hq : q ∈ checkNumWith (scaledCoeffs c (degree c) b)
      (if degree c % 2 = 1 then b else 1) b fl a) : q = (a, 0, (b : ℤ)) := by
    simpa [hr] using ((mem_checkNumWith_of_noCheck hc).mp hq).2
  refine List.Nodup.append ?_ ((nodup_searchDens c hH).flatMap (fun b _ ↦ ?_)
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
    have h1 := (List.mem_range'_1.mp (mem_range'_of_mem_searchDens hb)).1
    have h2 : q = (1, 0, 0) := by simpa [hr] using eq_of_mem_pointsAtInfinityList_of_noCheck hc hq
    rw [hmem hq', Prod.mk.injEq, Prod.mk.injEq] at h2
    lia

/-- Under `RATPOINTS_NO_CHECK`, the points that the search delivers are distinct: the survivors
`(a, 0, b)` are distinct pairs over distinct denominators `b ≥ 1` (`Ratpoints.nodup_searchDens`),
the point at infinity apart, and the map of the reversal is injective on the normalized pairs
(`Ratpoints.Sieve.swapPoint_inj`). -/
theorem nodup_searchList_of_noCheck {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (D : List (WithBotTop ℚ × WithBotTop ℚ)) (S : ℕ → ℤ → Bool) {fl : CheckFlags}
    (hc : fl.noCheck = true) :
    (searchList c H D S fl).Nodup := by
  have hc' : ({ fl with reversed := false } : CheckFlags).noCheck = true := hc
  rw [searchList_eq_map]
  refine (nodup_searchList_of_noCheck_of_reversed_eq_false hH D S hc' rfl).map_on
    fun q hq q' hq' h ↦ ?_
  obtain ⟨x, z, rfl, hn⟩ := exists_eq_of_mem_searchList_of_noCheck hc' hH hq
  obtain ⟨x', z', rfl, hn'⟩ := exists_eq_of_mem_searchList_of_noCheck hc' hH hq'
  cases hr : fl.reversed <;> simp only [hr, Bool.false_eq_true, ↓reduceIte, id] at h
  exacts [h, (swapPoint_inj hn.2.1 hn'.2.1).mp h]

/-- Without `RATPOINTS_NO_CHECK` and with `RATPOINTS_NO_Y`, the points that the search delivers,
with `y` replaced by `0`, are a sublist of those that it delivers under `RATPOINTS_NO_CHECK` with
the same test: each numerator gives at most its point with `y ≥ 0` in the one case and its survivor
in the other (`Ratpoints.Sieve.map_checkNumWith_sublist`). -/
theorem map_searchList_sublist (c : List ℤ) (H : ℕ) (D : List (WithBotTop ℚ × WithBotTop ℚ))
    (S : ℕ → ℤ → Bool) (rev noY : Bool) :
    ((searchList c H D S ⟨rev, false, true⟩).map fun q ↦ (q.1, 0, q.2.2)).Sublist
      (searchList c H D S ⟨rev, true, noY⟩) := by
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
sound. -/
theorem isSoundTest_false_of_forall_not_isPoint {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (h : ∀ q, ¬IsPoint c H q) :
    IsSoundTest c H fun _ _ ↦ false := fun b hb _ ha hne ↦
  absurd ((pointsOfDen_eq_nil_of_forall_not_isPoint hH h).2 b (mem_range'_of_mem_searchDens hb))
    (pointsOfDen_ne_nil_of_mem ha hne)

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
coefficient list `c`: sound sieve entries (`Ratpoints.Sieve.SieveEntry.IsSound`), those of the first
two stages, the first `sp2`, with their tables of inverses and the row offsets of the packings of
the classes `cls` (`Ratpoints.Sieve.OffsetsFor`), those of the third stage of the shape that it
needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), the reciprocals of the moduli in the order of the
entries, classes that pack the words of the 2-adic information (`Ratpoints.Sieve.twoAdic`), the word
`db` of the classes that admit a numerator (`Ratpoints.Sieve.denBits`), and a store of the tables of
rows that fits the entries of the first two stages (`Ratpoints.Sieve.RowStore.Fits`). -/
structure IsSoundRun (c : List ℤ) (sp2 : ℕ) (entries : List SieveEntry) (magics : Array ℕ)
    (cls : Vector NumClass 64) (offsets : Array ℕ) (db : UInt64) (store : RowStore) : Prop where
  /-- The sieve entries are sound. -/
  isSound : ∀ e ∈ entries, e.IsSound c
  /-- The sieve entries of the third stage have the shape that it needs. -/
  isPrimeEntry : ∀ e ∈ entries.drop sp2, e.IsPrimeEntry
  /-- The reciprocals of the moduli, in the order of the entries. -/
  magics_eq : magics.toList = entries.map fun e ↦ magic e.p
  /-- The sieve entries of the first two stages have their tables of inverses. -/
  hasInverses : ∀ e ∈ entries.take sp2, ∀ f ∈ e.factors, f.HasInverses e.p
  /-- The classes with a pattern have their row offsets for the first two stages. -/
  offsetsFor : OffsetsFor cls (entries.take sp2) offsets
  /-- The classes pack the words of the 2-adic information. -/
  packs : ∀ b < 64, cls[b]!.Packs (Id.run (twoAdic c (degree c)))[b]!
  /-- The word of the classes that admit a numerator. -/
  db_eq : db = denBits (Id.run (twoAdic c (degree c)))
  /-- The store of the tables of rows fits the sieve entries of the first two stages. -/
  fits : store.Fits (entries.take sp2)

/-- The class test of a sound run on the denominator `b` is the test of the word of its class in
the 2-adic information. -/
theorem IsSoundRun.bits_bne_zero {c : List ℤ} {sp2 : ℕ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    {store : RowStore} (h : IsSoundRun c sp2 entries magics cls offsets db store) (b : ℕ) :
    (cls[b % 64]!.bits != 0) = ((Id.run (twoAdic c (degree c)))[b % 64]! != 0) :=
  (h.packs _ (Nat.mod_lt _ (by decide))).bits_bne_zero

/-- The bits of the word `db` of a sound run are those of its classes with a pattern. -/
theorem IsSoundRun.getLsbD_db {c : List ℤ} {sp2 : ℕ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    {store : RowStore} (h : IsSoundRun c sp2 entries magics cls offsets db store) {j : ℕ}
    (hj : j < 64) :
    db.toBitVec.getLsbD j = (cls[j]!.bits != 0) := by
  rw [h.db_eq, getLsbD_denBits, decide_eq_true hj, Bool.true_and, (h.packs j hj).bits_bne_zero]

-- The shape of every denominator.
private theorem exists_dens_eq_filter_all {c : List ℤ} {H sp2 : ℕ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    {store : RowStore} (hrun : IsSoundRun c sp2 entries magics cls offsets db store) :
    ∃ p : ℕ → Bool, Id.run (Shape.all.dens db 1 H) = (List.range' 1 H).filter p ∧
      ∀ b ∈ List.range' 1 H, pointsOfDen c (degree c) b (numerators H) ≠ [] →
        p b = true ∧ Id.run (Shape.all.keep cls b) = true :=
  ⟨fun _ ↦ true, by simp [Shape.dens], fun b _ h ↦
    ⟨rfl, by simpa [Shape.keep, hrun.bits_bne_zero b] using getElem!_twoAdic_ne_zero h⟩⟩

-- The square shape, for odd degree and `|c_d| = 1`.
private theorem exists_dens_eq_filter_squares {c : List ℤ} {H sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} {store : RowStore} (hrun : IsSoundRun c sp2 entries magics cls offsets db store)
    (hd : degree c % 2 = 1) (hc : (c.getD (degree c) 0).natAbs = 1) :
    ∃ p : ℕ → Bool, Id.run (Shape.squares.dens db 1 H) = (List.range' 1 H).filter p ∧
      ∀ b ∈ List.range' 1 H, pointsOfDen c (degree c) b (numerators H) ≠ [] →
        p b = true ∧ Id.run (Shape.squares.keep cls b) = true := by
  refine ⟨fun b ↦ Nat.sqrt b * Nat.sqrt b == b, by simp [Shape.dens, squaresDens_eq_filter le_rfl],
    fun b _ h ↦ ⟨?_, by simpa [Shape.keep, hrun.bits_bne_zero b] using getElem!_twoAdic_ne_zero h⟩⟩
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil h
  obtain ⟨r, rfl⟩ := isSquare_of_sq_eq_binaryForm_of_odd hd (Int.isUnit_iff_natAbs_eq.mpr hc) hg hy
  simp [Nat.sqrt_eq]

-- The divisor shape, for odd degree when the divisor set-up succeeds.
private theorem exists_dens_eq_filter_squares1 {c : List ℤ} {H sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} {store : RowStore} (hrun : IsSoundRun c sp2 entries magics cls offsets db store)
    (hd : degree c % 2 = 1) {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) H) = some (info, divisors)) :
    ∃ p : ℕ → Bool, Id.run ((Shape.squares1 info divisors).dens db 1 H) =
      (squares1Dens divisors 1 H).filter p ∧
      ∀ b ∈ squares1Dens divisors 1 H, pointsOfDen c (degree c) b (numerators H) ≠ [] →
        p b = true ∧ Id.run ((Shape.squares1 info divisors).keep cls b) = true := by
  refine ⟨fun _ ↦ true, by simp [Shape.dens], fun b hb h ↦ ⟨rfl, ?_⟩⟩
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil h
  have hb0 : b ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (List.mem_range'_1.mp (mem_range'_of_mem_squares1Dens hb)).1
  simp [Shape.keep, hrun.bits_bne_zero b, getElem!_twoAdic_ne_zero h,
    run_denInfoTest_of_sq_eq hd hs hb0 hg hy]

-- The word shape, for even degree.
private theorem exists_dens_eq_filter_words {c : List ℤ} {H sp2 : ℕ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    {store : RowStore} (hrun : IsSoundRun c sp2 entries magics cls offsets db store)
    (hd : degree c % 2 = 0) {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hforb : ∀ e ∈ forb, IsForbiddenEntry c (degree c) H e)
    (hval : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e) (useJacobi : Bool) :
    ∃ p : ℕ → Bool, Id.run ((Shape.words forb forbVal useJacobi
        (if useJacobi then Id.run (jacobiSetup (c.getD (degree c) 0) H) else none)
        (c.getD (degree c) 0)).dens db 1 H) = (List.range' 1 H).filter p ∧
      ∀ b ∈ List.range' 1 H, pointsOfDen c (degree c) b (numerators H) ≠ [] →
        p b = true ∧ Id.run ((Shape.words forb forbVal useJacobi
          (if useJacobi then Id.run (jacobiSetup (c.getD (degree c) 0) H) else none)
          (c.getD (degree c) 0)).keep cls b) = true := by
  obtain rfl := hrun.db_eq
  refine ⟨fun b ↦ (denBits (Id.run (twoAdic c (degree c)))).toBitVec.getLsbD (b % 64) &&
    forb.all fun e ↦ b % e.p != 0, ?_, fun _ hb h ↦ ?_⟩
  · simpa [Shape.dens] using toList_run_wordsDens (fun e he ↦ (hforb e he).prime.pos)
      (fun e he ↦ (hforb e he).words_eq) 1 H
  have hb' := List.mem_range'_1.mp hb
  obtain ⟨_, _, _, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil h
  exact ⟨getLsbD_denBits_and_all_of_sq_eq hd hforb (by lia) (by lia) hg hy,
    run_wordsTest_of_sq_eq hd hval _ (by lia) (by lia) hg hy⟩

end Sieve

/-! ### What `Ratpoints.sievingInfo` computes -/

/-- What the loop of `Ratpoints.sievingInfo` over the moduli has made after the moduli `pref`,
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

/-- The invariant of the loop of `Ratpoints.sievingInfo` over the moduli, after the moduli `pref`
and with the moduli `suff` still to come, on the result of an early return, the sieve entries made
and the store of the tables of rows: before a return, what the loop has made
(`Ratpoints.SievingInfoEntries`); a result, which is `none` and comes when the curve has no points
of height at most `H`, only at the end. -/
def SievingInfoInvariant (c : List ℤ) (H : ℕ) (pref suff : List ℕ)
    (st : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore)) × Array SieveEntry × RowStore) : Prop :=
  st.1.elim (SievingInfoEntries c pref st.2.1 st.2.2) fun r ↦ suff = [] ∧ r = none ∧
    ∀ q, ¬IsPoint c H q

/-- The loop of `Ratpoints.sievingInfo` starts with the store of the loop of the tables, which holds
the rows of `0` of the primes and no others (`Ratpoints.Sieve.PrimeStore`). -/
theorem sievingInfoInvariant_empty (c : List ℤ) (H : ℕ) (suff : List ℕ) {store : RowStore}
    (h : PrimeStore store) : SievingInfoInvariant c H [] suff (none, #[], store) :=
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

/-- A sieve entry made by `Ratpoints.makeModulus?` is sound. -/
theorem IsModulusEntry.isSound {c : List ℤ} {m : ℕ} {s : SieveEntry} (h : IsModulusEntry c m s) :
    s.IsSound c :=
  ⟨Nat.zero_lt_of_lt h.packable.one_lt, fun hab hy ↦ h.admits_of_sq_eq hab hy⟩

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

/-- The step of the loop of `Ratpoints.sievingInfo` at a modulus `m`, whose sieve entry
`Ratpoints.makeModulus?` makes at the position `entries.size` (`Ratpoints.makeModulus?_spec`), with
its tables of rows and those of its factors added to the store
(`Ratpoints.Sieve.SieveEntry.addTables`): the entry of one of the first `Ratpoints.numPrimes` primes
of the table has the shape that the third stage needs, and the store is made for the entries with
`e` (`Ratpoints.Sieve.RowStore.MadeFor.addTables`). -/
theorem SievingInfoInvariant.push {c : List ℤ} {H m : ℕ} {pref suff : List ℕ}
    {o : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore))}
    {entries : Array SieveEntry} {store : RowStore} {r : Option SieveEntry} {e : SieveEntry}
    (h : SievingInfoInvariant c H pref (m :: suff) (o, entries, store))
    (hr : (∀ s, r = some s → IsModulusEntry c m s ∧
          (s.ref, s.init) = SieveEntry.refInit entries.size s.factors ∧
          ∀ pn < numPrimes, primeTable[pn]! = m →
            s.factors = [.prime (examinePrime c (degree c) m)]) ∧
      (r = none → ∀ H q, ¬IsPoint c H q))
    (he : r = some e) :
    SievingInfoInvariant c H (pref ++ [m]) suff (none, entries.push e, e.addTables store) := by
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

/-- What the search needs of the result of `Ratpoints.sievingInfo` for the parameters `P`: the sieve
entries `entries` are those of the moduli, in their order, sound
(`Ratpoints.Sieve.SieveEntry.IsSound`), with the fields that the packing reads
(`Ratpoints.Sieve.SieveEntry.Packable`) and the tables of inverses of their factors
(`Ratpoints.Sieve.Factor.HasInverses`), those of the third stage of the shape that it needs
(`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`); `magics` holds the reciprocals of their moduli, in
their order; the forbidden divisors are among those that the loops of the tables and of the further
primes may record (`Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`); and the
store of the tables of rows fits the entries (`Ratpoints.Sieve.RowStore.Fits`). -/
structure IsSievingInfo (c : List ℤ) (H : ℕ) (P : Params) (entries : List SieveEntry)
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

/-- The early return of the loop of `Ratpoints.sievingInfo` at a modulus whose sieve entry is none:
the curve has no points. -/
theorem sievingInfoInvariant_some_none {c : List ℤ} {H m : ℕ} {pref : List ℕ}
    {entries : Array SieveEntry} {store : RowStore} {r x : Option SieveEntry} {n : ℕ}
    (hr : (∀ s, r = some s → IsModulusEntry c m s ∧
          (s.ref, s.init) = SieveEntry.refInit n s.factors ∧ ∀ pn < numPrimes, primeTable[pn]! = m →
            s.factors = [.prime (examinePrime c (degree c) m)]) ∧
      (r = none → ∀ H q, ¬IsPoint c H q))
    (hx : ∀ e, x = some e → False) (he : r = x) :
    SievingInfoInvariant c H pref [] (some none, entries, store) :=
  ⟨rfl, rfl, hr.2 (he.trans (Option.eq_none_iff_forall_ne_some.mpr hx)) H⟩

/-- The end of the loop of `Ratpoints.sievingInfo` after an early return. -/
theorem SievingInfoInvariant.post_some {c : List ℤ} {H : ℕ} {P : Params} {pref : List ℕ}
    {o : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore))}
    {entries : Array SieveEntry} {store : RowStore}
    {r : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal × RowStore)}
    (h : SievingInfoInvariant c H pref [] (o, entries, store)) (ho : o = some r) :
    (∀ entries magics forb forbVal store, r = some (entries, magics, forb, forbVal, store) →
        IsSievingInfo c H P entries magics forb forbVal store) ∧
      (r = none → ∀ q, ¬IsPoint c H q) := by
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

/-- The end of the loop of `Ratpoints.sievingInfo` over all the moduli of well-formed parameters,
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
    (h : SievingInfoInvariant c H P.moduli [] (o, entries, store)) (ho : o = none)
    (hforb : (∀ e ∈ forb, IsForbiddenEntry c (degree c) H e) ∧
      ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e) :
    (∀ entries' magics forb' forbVal' store',
        some (entries.toList, entries.map (·.magic), forb, forbVal, store) =
          some (entries', magics, forb', forbVal', store') →
        IsSievingInfo c H P entries' magics forb' forbVal' store') ∧
      (some (entries.toList, entries.map (·.magic), forb, forbVal, store) = none →
        ∀ q, ¬IsPoint c H q) := by
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

-- The exit of the loop of the tables in `Ratpoints.sievingInfo`: the curve has no points.
private theorem post_of_run_examinePrimes_eq {c : List ℤ} {u checkDenom : Bool} {P : Params}
    {H : ℕ} {x : Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal × RowStore)}
    (hn : P.examined ≤ numPrimes)
    (hx : ∀ tables ba val store, x = some (tables, ba, val, store) → False)
    (he : Id.run (examinePrimes c (degree c) u checkDenom P.examined P.maxForbidden H) = x) :
    (∀ entries magics forb forbVal store,
        (none : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
          RowStore)) = some (entries, magics, forb, forbVal, store) →
        IsSievingInfo c H P entries magics forb forbVal store) ∧
      ((none : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
        RowStore)) = none → ∀ q, ¬IsPoint c H q) :=
  ⟨nofun, fun _ ↦ not_isPoint_of_run_examinePrimes_eq_none
    (he.trans (Option.eq_none_iff_forall_ne_some.mpr fun ⟨t, b, v, s⟩ h ↦ hx t b v s h)) hn H⟩

-- The forbidden divisors that the loop of the tables records, as lists.
private theorem forall_mem_toList_isForbiddenEntry_and_isForbiddenVal {c : List ℤ} {d : ℕ}
    {u checkDenom : Bool} {n maxForbidden H : ℕ} {tables : Array Entry}
    {ba : Array ForbiddenEntry} {val : Array ForbiddenVal} {store : RowStore}
    (h : Id.run (examinePrimes c d u checkDenom n maxForbidden H) = some (tables, ba, val, store))
    (hn : n ≤ numPrimes) :
    (∀ e ∈ ba.toList, IsForbiddenEntry c d H e) ∧ ∀ e ∈ val.toList, IsForbiddenVal c d H e :=
  ⟨fun _ he ↦ isForbiddenEntry_of_run_examinePrimes_eq_some h hn (Array.mem_toList_iff.mp he),
    fun _ he ↦ isForbiddenVal_of_run_examinePrimes_eq_some h hn (Array.mem_toList_iff.mp he)⟩

-- The loop of the tables, as a value for the contract of `Ratpoints.sievingInfo`.
private theorem examinePrimes_value (c : List ℤ) (d : ℕ) (u checkDenom : Bool)
    (n maxForbidden bHigh : ℕ) :
    ⦃ True ⦄ examinePrimes c d u checkDenom n maxForbidden bHigh
    ⦃ fun r ↦ r = Id.run (examinePrimes c d u checkDenom n maxForbidden bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

attribute [local irreducible] SievingInfoInvariant in
/-- For well-formed parameters, what `Ratpoints.sievingInfo` computes serves the search
(`Ratpoints.IsSievingInfo`): the sieve entries are those of the moduli, in their order, and are
sound (`Ratpoints.SievingInfoInvariant.push`, the tables of the loop of the tables being those of
the reference, `Ratpoints.makeModulus?_spec`), have the fields that the packing reads
(`Ratpoints.Sieve.SieveEntry.Packable`) and the tables of inverses of their factors
(`Ratpoints.Sieve.Factor.HasInverses`), and hold the reciprocals of their moduli, which are the
reciprocals returned, in the order of the entries, those of the third stage having the shape that it
needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`); the forbidden divisors are among those that the
loop of the tables and the loop of the further primes may record
(`Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`), with the switch of the
forbidden divisors on or off; and the store of the tables of rows that the loop of the tables and
the loop over the moduli make fits the entries (`Ratpoints.Sieve.RowStore.Fits`). When it returns
none, the curve has no points, none modulo a prime of the loop of the tables
(`Ratpoints.Sieve.not_isPoint_of_run_examinePrimes_eq_none`) or modulo a prime examined for a
modulus. -/
@[spec]
theorem sievingInfo_spec (c : List ℤ) (u checkDenom : Bool) (P : Params) (H : ℕ) :
    ⦃ P.WF ⦄ sievingInfo c (degree c) u checkDenom P H
    ⦃ fun r ↦ (∀ entries magics forb forbVal store,
        r = some (entries, magics, forb, forbVal, store) →
          IsSievingInfo c H P entries magics forb forbVal store) ∧
      (r = none → ∀ q, ¬IsPoint c H q) ⦄ := by
  vcgen [sievingInfo, examinePrimes_value] invariants
  · fun pref suff st ↦ SievingInfoInvariant c H pref suff st
  · fun pref suff st ↦ SievingInfoInvariant c H pref suff st
  all_goals try dsimp only at *
  all_goals try obtain rfl := ‹_ = Id.run (examinePrimes _ _ _ _ _ _ _)›
  all_goals have hP := ‹P.WF›
  all_goals first
    | exact sievingInfoInvariant_empty c H _
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

-- `Ratpoints.sievingInfo_spec` as a plain statement.
private theorem run_sievingInfo_spec {c : List ℤ} {u checkDenom : Bool} {P : Params} {H : ℕ}
    (hP : P.WF) :
    (∀ entries magics forb forbVal store, Id.run (sievingInfo c (degree c) u checkDenom P H) =
        some (entries, magics, forb, forbVal, store) →
          IsSievingInfo c H P entries magics forb forbVal store) ∧
      (Id.run (sievingInfo c (degree c) u checkDenom P H) = none → ∀ q, ¬IsPoint c H q) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((sievingInfo_spec c u checkDenom P H).le_wp hP)

/-! ### The search -/

-- The shape that `Ratpoints.Sieve.runSetup` chooses from the flags of the search lists the
-- denominators of the search that a filter lets through, and lets every denominator of a point
-- through.
private theorem exists_dens_eq_filter_runSetup {c : List ℤ} {H sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} {store : RowStore} (hrun : IsSoundRun c sp2 entries magics cls offsets db store)
    {us1 : Option (List Setup.DenInfo × List ℕ)}
    (hus1 : (if degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1 then
      Id.run (Setup.setupUs1 c (degree c) H) else none) = us1)
    {checkDenom useJacobi : Bool} {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hforb : ∀ e ∈ forb, IsForbiddenEntry c (degree c) H e)
    (hval : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e)
    (hcd : checkDenom = true → degree c % 2 = 0) (dom : List (Double × Double)) :
    ∃ p : ℕ → Bool, Id.run ((Id.run (runSetup (degree c % 2 == 1 &&
        (c.getD (degree c) 0).natAbs == 1) us1 checkDenom useJacobi forb forbVal
        (c.getD (degree c) 0) H H dom)).1.dens db 1 H) = (searchDens c (degree c) H).filter p ∧
      ∀ b ∈ searchDens c (degree c) H, pointsOfDen c (degree c) b (numerators H) ≠ [] →
        p b = true ∧ Id.run ((Id.run (runSetup (degree c % 2 == 1 &&
          (c.getD (degree c) 0).natAbs == 1) us1 checkDenom useJacobi forb forbVal
          (c.getD (degree c) 0) H H dom)).1.keep cls b) = true := by
  rw [searchDens, hus1, fst_run_runSetup]
  rcases Nat.mod_two_eq_zero_or_one (degree c) with hd | hd
  · obtain rfl : us1 = none := by rw [← hus1, hd]; rfl
    rw [hd]
    cases checkDenom
    · exact exists_dens_eq_filter_all hrun
    · exact exists_dens_eq_filter_words hrun hd hforb hval _
  by_cases hc : (c.getD (degree c) 0).natAbs = 1
  · obtain rfl : us1 = none := by rw [← hus1, hd, hc]; rfl
    rw [hd, hc]
    exact exists_dens_eq_filter_squares hrun hd hc
  rw [hd, beq_eq_false_iff_ne.mpr hc, Bool.and_false]
  rcases us1 with _ | ⟨info, divisors⟩
  · obtain rfl : checkDenom = false := by cases checkDenom <;> simp_all
    exact exists_dens_eq_filter_all hrun
  · exact exists_dens_eq_filter_squares1 hrun hd (Option.ite_none_right_eq_some.mp hus1).2

/-- The run of the shape that `Ratpoints.Sieve.runSetup` chooses, with sound arguments
(`Ratpoints.Sieve.IsSoundRun`), pieces of at least one bit array, the height below `2 ^ 63` and
the bounds of well-formed search intervals `dom`, delivers, with any callback, flags of the check
and delivery whose flag is clear, the points of the check with the flags of the numerators in the
search intervals that pass a test of the sieve over the denominators of the search
(`Ratpoints.Sieve.run_sieveRun_of_eq_filter`, `Ratpoints.Sieve.rangesFor_run_exactBounds`,
`Ratpoints.Sieve.inRanges_numeratorRanges`); the test, which does not depend on the callback, the
flags or the search intervals, is sound (`Ratpoints.IsSoundTest`): the shape lets every denominator
of a point through, and the class words and the sound entries every numerator of a point
(`Ratpoints.Sieve.classBit_and_survives_of_ne_nil`). -/
theorem exists_isSoundTest_run_sieveRun {c : List ℤ} {H A sp1 sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} {store : RowStore} (hrun : IsSoundRun c sp2 entries magics cls offsets db store)
    (hH63 : H < 2 ^ 63) (hA : 1 ≤ A) {us1 : Option (List Setup.DenInfo × List ℕ)}
    (hus1 : (if degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1 then
      Id.run (Setup.setupUs1 c (degree c) H) else none) = us1)
    {checkDenom useJacobi : Bool} {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hforb : ∀ e ∈ forb, IsForbiddenEntry c (degree c) H e)
    (hval : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e)
    (hcd : checkDenom = true → degree c % 2 = 0) (dom : List (Double × Double))
    (hdom : IntervalsWF (domainBits dom)) :
    ∃ S, IsSoundTest c H S ∧ ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (fl : CheckFlags)
      (r : Delivery σ), r.quit = false →
        Id.run (sieveRun process c (degree c) H A fl sp1 sp2 entries magics cls offsets db
          (Id.run (runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) us1
            checkDenom useJacobi forb forbVal (c.getD (degree c) 0) H H dom)).1
          (Id.run (runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) us1
            checkDenom useJacobi forb forbVal (c.getD (degree c) 0) H H dom)).2 1 H store r) =
        r.deliver process ((searchDens c (degree c) H).flatMap fun b : ℕ ↦
          ((numerators H).filter fun a : ℤ ↦ decide (InIntervals (domainValues dom) (a / b)) &&
            S b a).flatMap (checkNumWith (scaledCoeffs c (degree c) b)
              (if degree c % 2 = 1 then b else 1) b fl)) := by
  obtain ⟨p, hdens, hkeep⟩ := exists_dens_eq_filter_runSetup hrun hus1 hforb hval hcd dom
  rw [snd_run_runSetup]
  generalize (Id.run (runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) us1
    checkDenom useJacobi forb forbVal (c.getD (degree c) 0) H H dom)).1 = shape at hdens hkeep ⊢
  refine ⟨fun b a ↦ p b && Id.run (shape.keep cls b) &&
      classBit (Id.run (twoAdic c (degree c)))[b % 64]! a && survives entries b a,
    fun b hb a ha hne ↦ ?_, fun process fl r hr ↦ ?_⟩
  · have := hkeep b hb (pointsOfDen_ne_nil_of_mem ha hne)
    have := classBit_and_survives_of_ne_nil hrun.isSound hne
    simp_all
  rw [run_sieveRun_of_eq_filter process hA hrun.isPrimeEntry hrun.magics_eq hrun.hasInverses
    hrun.offsetsFor (fun _ ↦ hrun.getLsbD_db) hrun.packs (rs := fun b ↦ numeratorRanges b H
      (domainValues dom)) (fun b hb1 hb2 ↦ rangesFor_run_exactBounds hdom hH63 le_rfl (by lia) hb2)
    le_rfl hH63 hH63 hrun.fits hdens hr]
  refine congrArg _ (List.flatMap_congr fun b hb ↦ congrArg (List.flatMap _)
    (List.filter_congr fun a ha ↦ ?_))
  rw [inRanges_numeratorRanges (by lia [(List.mem_range'_1.mp (mem_range'_of_mem_searchDens hb)).1])
    (natAbs_le_of_mem_numerators ha)]
  dsimp only
  ac_rfl

-- The classes after `class_offsets`, with the entries whose inverses of the strides it sets, the
-- other fields unchanged, and its row offsets, make a sound run with the word of the classes that
-- admit a numerator and the store of the tables of rows that fits the entries.
private theorem isSoundRun_of_map {c : List ℤ} {sp2 : ℕ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls cls' : Vector NumClass 64} {offsets : Array ℕ} {store : RowStore}
    {dinv : SieveEntry → Array ℕ}
    (hent : ∀ e ∈ entries, e.IsSound c ∧ e.Packable ∧ ∀ f ∈ e.factors, f.HasInverses e.p)
    (hes : ∀ e ∈ entries.drop sp2, e.IsPrimeEntry)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p)
    (hcls : ∀ b < 64, cls[b]!.Packs (Id.run (twoAdic c (degree c)))[b]!)
    (hbits : ∀ b < 64, cls'[b]!.bits = cls[b]!.bits ∧ cls'[b]!.k = cls[b]!.k ∧
      cls'[b]!.a0 = cls[b]!.a0)
    (hoff : OffsetsFor cls' (entries.map fun e ↦ { e with dinv := dinv e }) offsets)
    (hs : store.Fits entries) :
    IsSoundRun c sp2 (entries.map fun e ↦ { e with dinv := dinv e }) magics cls' offsets
      (denBits (Id.run (twoAdic c (degree c)))) store := by
  refine ⟨fun e he ↦ ?_, fun e he ↦ ?_, by simp [hmg], fun e he ↦ ?_, hoff.take sp2,
    fun b hb ↦ (hcls b hb).congr (hbits b hb).1 (hbits b hb).2.1 (hbits b hb).2.2, rfl,
    (hs.map_dinv dinv).take sp2⟩
  · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact ⟨(hent e' he').1.pos, (hent e' he').1.admits_of_sq_eq⟩
  · rw [← List.map_drop] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact hes e' he'
  · rw [← List.map_take] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact (hent e' (List.mem_of_mem_take he')).2.2

-- The classes, the entries and the row offsets of the search after `class_offsets`, in the array
-- of `num_packings` rows, make a sound run (`Ratpoints.sievingInfo_spec`,
-- `Ratpoints.Sieve.numClasses_spec`, `Ratpoints.Sieve.numPackings_spec`,
-- `Ratpoints.Sieve.classOffsets_spec`).
private theorem isSoundRun_of_run_classOffsets {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF)
    {u cd : Bool}
    {r : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal × RowStore)}
    {entries : List SieveEntry} {magics : Array ℕ} {forb : List ForbiddenEntry}
    {forbVal : List ForbiddenVal} {store : RowStore}
    (hr : r = Id.run (sievingInfo c (degree c) u cd P H))
    (hs : r = some (entries, magics, forb, forbVal, store)) {nb : Vector UInt64 64}
    (hnb : nb = Id.run (twoAdic c (degree c))) {cls : Vector NumClass 64} {db : UInt64}
    (hnc : (cls, db) = Id.run (numClasses nb)) {n : ℕ} (hn : n = Id.run (numPackings cls))
    {cls' : Vector NumClass 64} {entries' : List SieveEntry} {offsets : Array ℕ}
    (hco : (cls', entries', offsets) =
      Id.run (classOffsets cls entries (Array.replicate (n * max entries.length 1) 0))) :
    IsSoundRun c P.sp2 entries' magics cls' offsets db store := by
  have hi := (run_sievingInfo_spec hP).1 _ _ _ _ _ (hr.symm.trans hs)
  subst hnb
  obtain ⟨rfl, rfl⟩ : cls = (Id.run (numClasses _)).1 ∧ db = (Id.run (numClasses _)).2 := by
    rw [← hnc]; exact ⟨rfl, rfl⟩
  have hcls (b : ℕ) (hb : b < 64) :=
    packs_getElem!_fst_run_numClasses (Id.run (twoAdic c (degree c))) hb
  have hn' : n = max 1 (firstKeys _ 64) :=
    hn.trans (Std.WP.Id.of_run_eq_wp rfl _ ((numPackings_spec _).le_wp fun b hb ↦ (hcls b hb).1))
  have hsize : firstKeys (Id.run (numClasses (Id.run (twoAdic c (degree c))))).1 64 *
      entries.length ≤ (Array.replicate (n * max entries.length 1) (0 : ℕ)).size := by
    rw [Array.size_replicate, hn']
    exact Nat.mul_le_mul (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  obtain ⟨hbits, ⟨f, hf⟩, hoff⟩ := Std.WP.Id.of_run_eq_wp rfl _
    ((classOffsets_spec _ entries _).le_wp ⟨fun e he ↦ (hi.isSound e he).2.1,
      fun b hb ↦ (hcls b hb).1, hsize⟩)
  rw [← hco] at hbits hf hoff
  simp only at hbits hf hoff
  subst hf
  rw [snd_run_numClasses]
  exact isSoundRun_of_map hi.isSound hi.isPrimeEntry hi.magics_eq hcls hbits hoff hi.fits

-- The components of the search, as values for its contract.
private theorem setupUs1_value (c : List ℤ) (d bHigh : ℕ) :
    ⦃ True ⦄ Setup.setupUs1 c d bHigh ⦃ fun r ↦ r = Id.run (Setup.setupUs1 c d bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem twoAdic_value (c : List ℤ) (d : ℕ) :
    ⦃ True ⦄ twoAdic c d ⦃ fun r ↦ r = Id.run (twoAdic c d) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem sievingInfo_value (c : List ℤ) (d : ℕ) (u checkDenom : Bool) (P : Params)
    (bHigh : ℕ) :
    ⦃ True ⦄ sievingInfo c d u checkDenom P bHigh
    ⦃ fun r ↦ r = Id.run (sievingInfo c d u checkDenom P bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem runSetup_value (useSquares : Bool) (us1 : Option (List Setup.DenInfo × List ℕ))
    (checkDenom useJacobi : Bool) (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal)
    (lcf : ℤ) (H bHigh : ℕ) (domain : List (Double × Double)) :
    ⦃ True ⦄ runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf H bHigh domain
    ⦃ fun r ↦ r = Id.run (runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf H bHigh
        domain) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem numClasses_value (nb : Vector UInt64 64) :
    ⦃ True ⦄ numClasses nb ⦃ fun r ↦ r = Id.run (numClasses nb) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem numPackings_value (cls : Vector NumClass 64) :
    ⦃ True ⦄ numPackings cls ⦃ fun r ↦ r = Id.run (numPackings cls) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem classOffsets_value (cls : Vector NumClass 64) (es : List SieveEntry)
    (offsets : Array ℕ) :
    ⦃ True ⦄ classOffsets cls es offsets ⦃ fun r ↦ r = Id.run (classOffsets cls es offsets) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem sieving_value {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (c : List ℤ)
    (d H : ℕ) (P : Params) (fl : CheckFlags) (useSquares : Bool)
    (us1 : Option (List Setup.DenInfo × List ℕ)) (checkDenom useJacobi : Bool)
    (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal) (entries : List SieveEntry)
    (magics : Array ℕ) (cls : Vector NumClass 64) (db : UInt64) (store : RowStore)
    (r : Delivery σ) :
    ⦃ True ⦄ sieving process c d H P fl useSquares us1 checkDenom useJacobi forb forbVal entries
      magics cls db store r
    ⦃ fun r' ↦ r' = Id.run (sieving process c d H P fl useSquares us1 checkDenom useJacobi forb
        forbVal entries magics cls db store r) ⦄ :=
  ⟨fun _ ↦ rfl⟩

-- The data and the count of the search along its paths, for the classes and the word of the 2-adic
-- information, the 2-adic exit `ex` and the result of `Ratpoints.sievingInfo`: the delivery as it
-- came after the 2-adic exit and the exit of `Ratpoints.sievingInfo`, else that of the points at
-- infinity, followed, unless the callback has stopped the search, by the sieving.
private theorem searchPoints_spec_paths {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
    (c : List ℤ) (d H : ℕ) (P : Params) (fl : CheckFlags) (r : Delivery σ)
    {cls : Vector NumClass 64} {db : UInt64} (ex : Bool)
    (si : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal × RowStore))
    (hcd : Id.run (numClasses (Id.run (twoAdic c d))) = (cls, db))
    (hex : (db == 0 && !(d % 2 == 1 || Setup.isSquare (c.getD d 0))) = ex)
    (hsi : Id.run (sievingInfo c d (Setup.useCLong c d) (d % 2 == 0) P H) = si) :
    ⦃ True ⦄ searchPoints process c d H P fl r
    ⦃ fun out ↦ (out.info, out.total) = (fun r' : Delivery σ ↦ (r'.info, r'.total))
        (if ex then r else
        match (generalizing := false) si with
        | none => r
        | some (entries, magics, forb, forbVal, store) =>
          if (pointsAtInfinity process c d fl r).quit then pointsAtInfinity process c d fl r else
          Id.run (sieving process c d H P fl (d % 2 == 1 && (c.getD d 0).natAbs == 1)
            (if (d % 2 == 1 && (c.getD d 0).natAbs != 1) = true then
              Id.run (Setup.setupUs1 c d H) else none)
            (if forb.isEmpty && forbVal.isEmpty &&
              !(d % 2 == 0 && !Setup.isSquare (c.getD d 0) && P.jacobi) then false else d % 2 == 0)
            (d % 2 == 0 && !Setup.isSquare (c.getD d 0) && P.jacobi) forb forbVal entries magics cls
            db store (pointsAtInfinity process c d fl r))) ⦄ := by
  rcases si with _ | ⟨entries, magics, forb, forbVal, store⟩ <;>
  · vcgen [searchPoints, setupUs1_value, twoAdic_value, numClasses_value, sievingInfo_value,
      sieving_value]
    all_goals subst_vars
    all_goals simp only [hcd, hsi, Option.some.injEq, Prod.mk.injEq, reduceCtorEq] at *
    all_goals casesm* _ ∧ _
    all_goals subst_vars
    all_goals first
      | (rename_i h; exact (h _ _ _ _ _ ⟨rfl, rfl, rfl, rfl, rfl⟩).elim)
      | simp_all only [↓reduceIte, Bool.false_eq_true, and_self]

-- `Ratpoints.searchPoints_spec_paths` as an equation.
private theorem run_searchPoints_paths {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)
    (c : List ℤ) (d H : ℕ) (P : Params) (fl : CheckFlags) (r : Delivery σ)
    {cls : Vector NumClass 64} {db : UInt64} (ex : Bool)
    (si : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal × RowStore))
    (hcd : Id.run (numClasses (Id.run (twoAdic c d))) = (cls, db))
    (hex : (db == 0 && !(d % 2 == 1 || Setup.isSquare (c.getD d 0))) = ex)
    (hsi : Id.run (sievingInfo c d (Setup.useCLong c d) (d % 2 == 0) P H) = si) :
    ((Id.run (searchPoints process c d H P fl r)).info,
      (Id.run (searchPoints process c d H P fl r)).total) =
      (fun r' : Delivery σ ↦ (r'.info, r'.total))
        (if ex then r else
        match (generalizing := false) si with
        | none => r
        | some (entries, magics, forb, forbVal, store) =>
          if (pointsAtInfinity process c d fl r).quit then pointsAtInfinity process c d fl r else
          Id.run (sieving process c d H P fl (d % 2 == 1 && (c.getD d 0).natAbs == 1)
            (if (d % 2 == 1 && (c.getD d 0).natAbs != 1) = true then
              Id.run (Setup.setupUs1 c d H) else none)
            (if forb.isEmpty && forbVal.isEmpty &&
              !(d % 2 == 0 && !Setup.isSquare (c.getD d 0) && P.jacobi) then false else d % 2 == 0)
            (d % 2 == 0 && !Setup.isSquare (c.getD d 0) && P.jacobi) forb forbVal entries magics cls
            db store (pointsAtInfinity process c d fl r))) :=
  Std.WP.Id.of_run_eq_wp rfl (fun out : Outcome σ ↦ (out.info, out.total) = _)
    ((searchPoints_spec_paths process c d H P fl r ex si hcd hex hsi).le_wp trivial)

/-- The bits of the flags of the search that the program reads after it, which do not depend on the
callback: the flag of the reversal as it came, the squares for odd degree and `|c_d| = 1`, and the
success of the divisor set-up for odd degree and `|c_d| ≠ 1`. -/
theorem run_searchPoints_flags {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (c : List ℤ)
    (d H : ℕ) (P : Params) (fl : CheckFlags) (r : Delivery σ) :
    (Id.run (searchPoints process c d H P fl r)).reversed = fl.reversed ∧
      (Id.run (searchPoints process c d H P fl r)).useSquares =
        (d % 2 == 1 && (c.getD d 0).natAbs == 1) ∧
      (Id.run (searchPoints process c d H P fl r)).useSquares1 =
        (if (d % 2 == 1 && (c.getD d 0).natAbs != 1) = true then
          Id.run (Setup.setupUs1 c d H) else none).isSome := by
  refine Std.WP.Id.of_run_eq_wp rfl _ ((?_ : ⦃ True ⦄ searchPoints process c d H P fl r
    ⦃ fun out ↦ out.reversed = fl.reversed ∧ out.useSquares = (d % 2 == 1 &&
      (c.getD d 0).natAbs == 1) ∧ out.useSquares1 = (if (d % 2 == 1 &&
        (c.getD d 0).natAbs != 1) = true then Id.run (Setup.setupUs1 c d H) else none).isSome ⦄
          ).le_wp trivial)
  vcgen [searchPoints, setupUs1_value, twoAdic_value, numClasses_value, sievingInfo_value,
    sieving_value]
  all_goals simp_all

-- After the exits, the sieving delivers the points of the denominators of the search in the default
-- search interval `dom` for a sound test of the sieve, whatever the callback and the flags.
private theorem exists_isSoundTest_run_sieving {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF)
    (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {dom : List (Double × Double)}
    (hdom : Id.run (searchIntervals H []) = some dom) {cls : Vector NumClass 64} {db : UInt64}
    (hcd : Id.run (numClasses (Id.run (twoAdic c (degree c)))) = (cls, db))
    {entries : List SieveEntry} {magics : Array ℕ} {forb : List ForbiddenEntry}
    {forbVal : List ForbiddenVal} {store : RowStore}
    (hsi : Id.run (sievingInfo c (degree c) (Setup.useCLong c (degree c)) (degree c % 2 == 0) P H) =
      some (entries, magics, forb, forbVal, store)) (useJacobi : Bool) :
    ∃ S, IsSoundTest c H S ∧ ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (fl : CheckFlags)
      (r : Delivery σ), r.quit = false → Id.run (sieving process c (degree c) H P fl
        (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1)
        (if (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1) = true then
          Id.run (Setup.setupUs1 c (degree c) H) else none)
        (if forb.isEmpty && forbVal.isEmpty && !useJacobi then false else degree c % 2 == 0)
        useJacobi forb forbVal entries magics cls db store r) =
        r.deliver process ((searchDens c (degree c) H).flatMap fun b : ℕ ↦
          ((numerators H).filter fun a : ℤ ↦ decide (InIntervals (domainValues dom) (a / b)) &&
            S b a).flatMap (checkNumWith (scaledCoeffs c (degree c) b)
              (if degree c % 2 = 1 then b else 1) b fl)) := by
  have hi := (run_sievingInfo_spec hP).1 _ _ _ _ _ hsi
  have hwf : IntervalsWF (domainBits ((Id.run (searchIntervals H [])).getD [])) := by
    obtain ⟨dom', h', hwf, -⟩ := exists_run_searchIntervals_nil hH hH63
    simpa [h'] using hwf
  have hget : dom = (Id.run (searchIntervals H [])).getD [] := by rw [hdom]; rfl
  rw [hget]
  exact exists_isSoundTest_run_sieveRun (isSoundRun_of_run_classOffsets hP rfl hsi rfl hcd.symm rfl
    rfl) hH63 (P.one_le_arraySizeAt hH) rfl hi.isForbiddenEntry hi.isForbiddenVal
    (by split <;> simp) _ hwf

-- At an exit of the search, on a curve without points, the test that lets no numerator through.
private theorem exists_isSoundTest_of_forall_not_isPoint {c : List ℤ} {H : ℕ} {P : Params}
    (hH : 1 ≤ H) {D : List (WithBotTop ℚ × WithBotTop ℚ)} (hno : ∀ q, ¬IsPoint c H q)
    (h : ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (fl : CheckFlags) (r : Delivery σ),
      ((Id.run (searchPoints process c (degree c) H P fl r)).info,
        (Id.run (searchPoints process c (degree c) H P fl r)).total) = (r.info, r.total)) :
    ∃ S, IsSoundTest c H S ∧ ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (fl : CheckFlags)
      (r : Delivery σ), r.quit = false →
        ((Id.run (searchPoints process c (degree c) H P fl r)).info,
          (Id.run (searchPoints process c (degree c) H P fl r)).total) =
        ((r.deliver process (searchList c H D S fl)).info,
          (r.deliver process (searchList c H D S fl)).total) :=
  ⟨_, isSoundTest_false_of_forall_not_isPoint hH hno, fun process fl r _ ↦ by
    rw [h, searchList_false H D (pointsAtInfinityList_eq_nil_of_forall_not_isPoint hH hno fl),
      Delivery.deliver_nil]⟩

/-- For well-formed parameters, `1 ≤ H < 2 ^ 63` and the default search interval `dom` of a search
without search intervals (`Ratpoints.searchIntervals`), there is a sound test of the numerators
(`Ratpoints.IsSoundTest`) for which the search of the polynomial with the coefficient list `c`, of
its degree, with any callback, flags of the check and delivery whose flag is clear, gives the data
and the count of the delivery of the points of `Ratpoints.searchList` for the values of `dom`: the
test is that of the sieve, which does not depend on the callback, the flags or the search intervals
(`Ratpoints.exists_isSoundTest_run_sieveRun`), the points at infinity come first
(`Ratpoints.Sieve.pointsAtInfinity_eq_deliver`), and the search returns after them when the callback
has stopped it; when the search takes the 2-adic exit or the exit of `Ratpoints.sievingInfo`, the
curve has no points (`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`,
`Ratpoints.sievingInfo_spec`), so that the test that lets no numerator through is sound and there is
no point at infinity. -/
theorem exists_isSoundTest_run_searchPoints {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF)
    (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) {dom : List (Double × Double)}
    (hdom : Id.run (searchIntervals H []) = some dom) :
    ∃ S, IsSoundTest c H S ∧ ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (fl : CheckFlags)
      (r : Delivery σ), r.quit = false →
        ((Id.run (searchPoints process c (degree c) H P fl r)).info,
          (Id.run (searchPoints process c (degree c) H P fl r)).total) =
        ((r.deliver process (searchList c H (domainValues dom) S fl)).info,
          (r.deliver process (searchList c H (domainValues dom) S fl)).total) := by
  rcases hcd : Id.run (numClasses (Id.run (twoAdic c (degree c)))) with ⟨cls, db⟩
  rcases hex : (db == 0 && !(degree c % 2 == 1 || Setup.isSquare (c.getD (degree c) 0)))
  · rcases hsi : Id.run (sievingInfo c (degree c) (Setup.useCLong c (degree c))
      (degree c % 2 == 0) P H) with _ | ⟨entries, magics, forb, forbVal, store⟩
    · exact exists_isSoundTest_of_forall_not_isPoint hH ((run_sievingInfo_spec hP).2 hsi)
        fun process fl r ↦ run_searchPoints_paths process c _ H P fl r _ _ hcd hex hsi
    obtain ⟨S, hS, hrun⟩ := exists_isSoundTest_run_sieving hP hH hH63 hdom hcd hsi _
    refine ⟨S, hS, fun process fl r hr ↦ ?_⟩
    rw [searchList, ← Delivery.ite_quit_eq_deliver_append process
      (pointsAtInfinity_eq_deliver process _ _ fl hr) (hrun process fl _)]
    exact run_searchPoints_paths process c _ H P fl r _ _ hcd hex hsi
  have hdb : denBits (Id.run (twoAdic c (degree c))) = 0 := by
    rw [← snd_run_numClasses, hcd]; simpa using (Bool.and_eq_true _ _).mp hex |>.1
  exact exists_isSoundTest_of_forall_not_isPoint hH (not_isPoint_of_denBits_eq_zero hdb H)
    fun process fl r ↦ run_searchPoints_paths process c _ H P fl r _ _ hcd hex rfl

/-! ### The protocol of the search -/

/-- For well-formed parameters and `1 ≤ H < 2 ^ 63`, the search of the polynomial with the
coefficient list `c`, of its degree, with a callback, flags of the check and a delivery whose flag
is clear, gives the data and the count of the delivery (`Ratpoints.Delivery.deliver`) of the list of
the points that the search with the appending callback (`Ratpoints.appendPoint`) gives for the same
flags from the empty array: both deliver the points of `Ratpoints.searchList` for the test of the
sieve (`Ratpoints.exists_isSoundTest_run_searchPoints`). -/
theorem run_searchPoints_eq_deliver {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF) (hH : 1 ≤ H)
    (hH63 : H < 2 ^ 63) {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (fl : CheckFlags)
    {r : Delivery σ} (hr : r.quit = false) :
    ((Id.run (searchPoints process c (degree c) H P fl r)).info,
      (Id.run (searchPoints process c (degree c) H P fl r)).total) =
      let r' := r.deliver process
        (Id.run (searchPoints appendPoint c (degree c) H P fl ⟨#[], 0, false⟩)).info.toList
      (r'.info, r'.total) := by
  obtain ⟨dom, hdom, -⟩ := exists_run_searchIntervals_nil hH hH63
  obtain ⟨S, -, hS⟩ := exists_isSoundTest_run_searchPoints (c := c) hP hH hH63 hdom
  have h := congr(Prod.fst $(hS appendPoint fl ⟨#[], 0, false⟩ rfl))
  simp only [Delivery.deliver_appendPoint, List.toArray] at h
  rw [hS process fl r hr, h]
  simp

end Ratpoints

end
