/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.FindPoints

import Ratpoints.Proof.Bounds
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Order
import Ratpoints.Proof.Sieve
import Ratpoints.Proof.Sift
import Ratpoints.Proof.Tables

/-!
# The output of the search and the refusals

`Ratpoints.findPointsWith` searches the polynomial that the reversal check of the normalized options
hands on, on the search intervals of `Ratpoints.searchIntervals`, unless it refuses the input
(`Ratpoints.findPointsWith_eq_ok_iff`); its refusals and the bits of the flags that it writes back
do not depend on the callback, and for well-formed parameters it gives the data and the count of the
delivery (`Ratpoints.Delivery.deliver`) of the list that `Ratpoints.findPoints`, its instance with
the appending callback, returns: the protocol of the delivery
(`Ratpoints.map_findPointsWith_eq_map_findPoints`). That list is the list of the points that the
search of the polynomial searched delivers on its search intervals for a sound test of the sieve,
which does not depend on the options of the output
(`Ratpoints.exists_searchList_of_findPoints_eq_ok`); without `RATPOINTS_NO_CHECK` it is the
brute-force reference of the polynomial searched, over the candidate `(1, 0)` and the denominators
of the search with the numerators in the search intervals, mapped back after a reversal, without the
points with `y < 0` under `RATPOINTS_NO_Y` (`Ratpoints.exists_eq_of_findPoints_eq_ok`). The search
intervals are the caller's, or the default interval, which holds the `x / z` of every point: the
list is that of the points of the specification in the search region (`Ratpoints.InRegion`) in the
order of `Ratpoints.orderedPoints`, so that it holds exactly these points, those with `y ≥ 0` under
`RATPOINTS_NO_Y`, each once. Under `RATPOINTS_NO_CHECK` it holds triples `(x, 0, z)` of normalized
pairs `(x, z)` of height at most `H` in the search region, each once, among them those of all the
points in it, and the list of the search with `RATPOINTS_NO_CHECK` cleared and `RATPOINTS_NO_Y` set,
with `y` replaced by `0`, is a sublist of it. `Ratpoints.findPoints` refuses exactly the inputs that
the program refuses: with the Sturm step on, those with fewer than two or more than
`Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or more, which is
not a `long`, the binary forms `Φ_c` that are not squarefree and search intervals that are not well
formed (`Ratpoints.IntervalsWF`); without it, instead of the forms that are not squarefree, those
that the test of the leading zeros and, for the whole box (`Ratpoints.IsFullBox`), the reversal
check refuse. Comparator certifies the protocol, the membership, the order, the absence of
duplicates, the three statements under `RATPOINTS_NO_CHECK` and both refusal theorems
(`comparator/Challenge.lean`).

## Main statements

* `Ratpoints.findPointsWith_eq_ok_iff`, `Ratpoints.findPointsWith_eq_error_iff`,
  `Ratpoints.exists_findPoints_eq_error_iff`: what `Ratpoints.findPointsWith` returns, and its
  refusals, which do not depend on the callback.
* `Ratpoints.map_findPointsWith_eq_map_findPoints`: for well-formed parameters, the data and the
  count of `Ratpoints.findPointsWith` are those of the delivery of the list of
  `Ratpoints.findPoints`; `Ratpoints.map_findPointsWith_flags`: the bits of the flags written back
  do not depend on the callback.
* `Ratpoints.info_total_eq_of_findPointsWith_eq_ok`: for well-formed parameters, the data and the
  count of a successful search with a callback are those of the delivery of the list of
  `Ratpoints.findPoints`; `Ratpoints.exists_findPointsWith_eq_ok_of_findPoints_eq_ok`: the search
  with a callback succeeds when `Ratpoints.findPoints` does.
* `Ratpoints.exists_searchList_of_findPoints_eq_ok`: the list of `Ratpoints.findPoints` is that of
  the search on its search intervals with a sound test of the sieve, the same for every choice of
  the options of the output.
* `Ratpoints.exists_eq_of_findPoints_eq_ok`: without `RATPOINTS_NO_CHECK`, it is the reference of
  the polynomial searched on its search intervals, mapped back after a reversal, filtered under
  `RATPOINTS_NO_Y`; `Ratpoints.eq_filter_bruteForce_of_findPoints_eq_ok_of_reverse_eq_false`: the
  reference in the search region of the options without the options of the output, when the options
  forbid the reversal and the denominators of the search are those of the range.
* `Ratpoints.exists_eq_filter_inRegion_of_findPoints_eq_ok`: without `RATPOINTS_NO_CHECK`, the list
  is that of the reference of the polynomial searched over the denominators of its search up to the
  largest, mapped back after a reversal, filtered by the search region of the options and under
  `RATPOINTS_NO_Y`.
* `Ratpoints.eq_orderedPoints_of_findPoints_eq_ok`: without `RATPOINTS_NO_CHECK`, the list is
  `Ratpoints.orderedPoints`, filtered under `RATPOINTS_NO_Y` and by the search region.
* `Ratpoints.perm_filter_bruteForce_of_findPoints_eq_ok`: without `RATPOINTS_NO_CHECK`, the list is
  a permutation of the reference in the search region, filtered under `RATPOINTS_NO_Y`.
* `Ratpoints.mem_iff_isPoint_of_findPoints_eq_ok`: without `RATPOINTS_NO_CHECK`, a triple lies in
  the list exactly when it is a normalized point of height at most `H` in the search region, with
  `y ≥ 0` under `RATPOINTS_NO_Y`.
* `Ratpoints.nodup_of_findPoints_eq_ok`: for every option, the list has no duplicates.
* `Ratpoints.toFinset_eq_filter_points_of_findPoints_eq_ok`: without the options of the output, its
  set of elements is that of the points in the search region.
* `Ratpoints.exists_eq_of_mem_of_findPoints_eq_ok_of_noCheck`,
  `Ratpoints.mem_of_isPoint_of_findPoints_eq_ok_of_noCheck`,
  `Ratpoints.map_sublist_of_findPoints_eq_ok_of_noCheck`: under `RATPOINTS_NO_CHECK`, the list holds
  triples `(x, 0, z)` of normalized pairs of height at most `H` in the search region, among them
  `(x, 0, z)` for every point `(x, y, z)` in it, and the list of the search with
  `RATPOINTS_NO_CHECK` cleared and `RATPOINTS_NO_Y` set, with `y` replaced by `0`, is a sublist of
  it.
* `Ratpoints.exists_findPoints_eq_error_iff_of_sturm_nonneg`: with the Sturm step on,
  `Ratpoints.findPoints` refuses exactly the inputs with fewer than two or more than
  `Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or more, the forms
  that are not squarefree and search intervals that are not well formed.
* `Ratpoints.exists_findPoints_eq_error_iff_of_sturm_neg`: without it, those with fewer than two or
  more than `Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or
  more, a degree `d` with `d + 2 ≤ 2 ⌈n / 2⌉`, when the reversal is allowed and the search region is
  the whole box an even degree with `c₀ = c₁ = 0`, and search intervals that are not well formed.

## Proof

`Ratpoints.findPoints` and `Ratpoints.findPointsWith` run the search on the polynomial that the
reversal check hands on, with its degree (`Ratpoints.Setup.degree_eq_of_reversal_eq_ok`), which is
positive after the refusals (`Ratpoints.Setup.one_le_of_reversal_eq_ok`), and its flag of the
reversal, with the options of the output as the flags of the check, the normalized range of the
denominators (`Ratpoints.Options.normalize`) and the search intervals, which are well formed
(`Ratpoints.wf_of_run_searchIntervals_eq_some`; `Ratpoints.exists_isSoundTest_run_searchPoints`,
`Ratpoints.run_searchPoints_eq_deliver`, `Ratpoints.searchList_of_noCheck_eq_false`); the binary
form of a reversed polynomial is that of `c` with `x` and `z` exchanged
(`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`), so that its reference, mapped back, is a
permutation of that of `c` (`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`), and a reversal comes
only for the whole box (`Ratpoints.isFullBox_of_reversal_normalize_eq_ok`). The search intervals of
the search hold, of the numerators of a denominator, exactly those in the caller's intervals: they
are the caller's (`Ratpoints.run_searchIntervals_of_ne_nil`), or the default interval, which holds
every `a / b` of the search (`Ratpoints.exists_run_searchIntervals_nil`); the filter by the
caller's intervals and the denominators from the normalized `bLow` on is the filter by the search
region of the options (`Ratpoints.inRegion_ite_swapPoint_iff`,
`Ratpoints.map_append_flatMap_filter_eq_filter_inRegion`), which holds the points at infinity and
those of the denominators up to the largest of the search
(`Ratpoints.eq_zero_or_le_toNat_bHigh_normalize_of_inRegion`,
`Ratpoints.perm_map_append_flatMap_searchDens`). In the terms of the specification of the order,
the reversal check hands on the polynomial of `Ratpoints.searchedPoly`
(`Ratpoints.searchedPoly_eq_of_reversal_eq_ok`), the denominators of the search are those of
`Ratpoints.searchDenominators` up to the largest denominator
(`Ratpoints.searchDens_eq_filter_searchDenominators`), and the reference finds over a denominator,
and over the candidate `(1, 0)`, the points of `Ratpoints.pointsWithDen`
(`Ratpoints.pointsOfDen_eq_pointsWithDen`, `Ratpoints.pointsOfDen_zero_eq_pointsWithDen`). Under
`RATPOINTS_NO_CHECK` the search delivers, for the same sound test of the sieve, the survivors of the
numerators prime to the denominators of the search in its search intervals
(`Ratpoints.exists_eq_of_mem_searchList_of_noCheck`, `Ratpoints.mem_region_of_mem_searchList`,
distinct by `Ratpoints.nodup_searchList_of_noCheck`), of which the points with `y ≥ 0` that the
search delivers without it are a sublist (`Ratpoints.map_searchList_sublist`). Of the refusals, the
heights that are not `long`s are those of `2 ^ 63` or more (`Ratpoints.fitsLong_natCast`), and the
test of the leading zeros and that of the reversal check stand for `Z ^ 2 ∣ Φ_c` and `X ^ 2 ∣ Φ_c`
(`Ratpoints.not_squarefree_binaryFormPoly_of_lt`,
`Ratpoints.Setup.not_squarefree_binaryFormPoly_of_reversal_eq_error`), the refusal of the search
intervals is the negation of `Ratpoints.IntervalsWF` (`Ratpoints.run_searchIntervals_eq_none_iff`),
and after them the remainder chain of the polynomial searched is none exactly when `Φ_c` is not
squarefree (`Ratpoints.Sturm.run_chain_eq_none_iff_of_reversal_eq_ok`).
-/
@[expose] public section

namespace Ratpoints

open BruteForce Sieve

/-! ### The search with a callback -/

/-- `Ratpoints.findPointsWith` returns the outcome `out` exactly when it refuses none of its inputs,
in the order of the program, and `out` is the outcome of the search of the polynomial `c'` of degree
`d'` that the reversal check of the normalized options hands on, with the flag of the reversal and
the options of the output, the normalized range of the denominators and the search intervals of
`Ratpoints.searchIntervals`, from the data `info`, the count `0` and the flag of the stop clear. -/
theorem findPointsWith_eq_ok_iff {c : List ℤ} {H : ℕ} {P : Params} {o : Options} {σ : Type}
    {process : ℤ → ℤ → ℤ → σ → Answer σ} {info : σ} {out : Outcome σ} :
    findPointsWith c H P o process info = .ok out ↔ ∃ c' d' rev dom, c.length ≤ maxDegree + 1 ∧
      2 ≤ c.length ∧ 1 ≤ H ∧ H < 2 ^ 63 ∧ c.length / 2 ≤ (degree c + 1) / 2 ∧
      Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', d', rev) ∧
      Id.run (searchIntervals H o.domain) = some dom ∧
      ¬(0 ≤ o.sturm ∧ Id.run (Sturm.chain c' d') = none) ∧
      out = Id.run (searchPoints process c' d' H P ⟨rev, o.noCheck, o.noY⟩
        (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat dom ⟨info, 0, false⟩) := by
  rw [findPointsWith, ← BruteForce.degree_eq]
  simp only [fitsLong_natCast, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  split_ifs with h1 h2 h3 h4
  any_goals (simp only [false_iff]; lia)
  split <;> rename_i hr
  · simp [hr]
  rename_i c' d' rev
  split <;> rename_i hsi
  · simp [hr, hsi]
  rename_i dom
  split_ifs with h5 <;> rw [o.sturm_normalize_nonneg_iff H] at h5
  · simp_all
  · simp only [Except.ok.injEq]
    exact ⟨fun h ↦ ⟨c', d', rev, dom, by lia, by lia, by lia, by lia, by lia, hr, hsi, h5, h.symm⟩,
      fun ⟨_, _, _, _, _, _, _, _, _, hr', hsi', _, h⟩ ↦ by simp_all⟩

/-- The refusals of `Ratpoints.findPointsWith` do not depend on the callback or its data. -/
theorem findPointsWith_eq_error_iff {c : List ℤ} {H : ℕ} {P : Params} {o : Options} {σ σ' : Type}
    {process : ℤ → ℤ → ℤ → σ → Answer σ} {info : σ} {process' : ℤ → ℤ → ℤ → σ' → Answer σ'}
    {info' : σ'} {e : Refusal} :
    findPointsWith c H P o process info = .error e ↔
      findPointsWith c H P o process' info' = .error e := by
  simp only [findPointsWith]
  split_ifs
  any_goals simp
  split
  · simp
  split
  · simp
  split_ifs <;> simp

/-- `Ratpoints.findPoints` refuses an input exactly when `Ratpoints.findPointsWith` with the
appending callback does. -/
theorem exists_findPoints_eq_error_iff {c : List ℤ} {H : ℕ} {P : Params} {o : Options} :
    (∃ e, findPoints c H P o = .error e) ↔
      ∃ e, findPointsWith c H P o appendPoint #[] = .error e := by
  rw [findPoints]
  rcases findPointsWith c H P o appendPoint #[] <;> simp [Except.map]

/-- For well-formed parameters and every option, `Ratpoints.findPointsWith` with a callback and its
data gives, besides the bits of the flags written back, the data and the count of the delivery
(`Ratpoints.Delivery.deliver`) of the list that `Ratpoints.findPoints` returns, from the data, the
count `0` and the flag of the stop clear, and it refuses the same inputs with the same errors: the
calls of the callback are those of the points of that list, in its order, up to and including the
first that stops the search (`Ratpoints.run_searchPoints_eq_deliver`); comparator certifies this
(`comparator/Challenge.lean`). -/
theorem map_findPointsWith_eq_map_findPoints {P : Params} (hP : P.WF) (c : List ℤ) (H : ℕ)
    (o : Options) {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (info : σ) :
    (findPointsWith c H P o process info).map (fun out ↦ (out.info, out.total)) =
      (findPoints c H P o).map (fun L ↦
        let r := Delivery.deliver process ⟨info, 0, false⟩ L
        (r.info, r.total)) := by
  rcases h : findPointsWith c H P o appendPoint #[] with e | out
  · rw [findPoints, h, findPointsWith_eq_error_iff.mpr h]
    rfl
  obtain ⟨c', d', rev, dom, h1, h2, hH, hH63, hl, hr, hsi, hs, rfl⟩ := findPointsWith_eq_ok_iff.mp h
  obtain rfl := Setup.degree_eq_of_reversal_eq_ok rfl hr
  rw [findPoints, h, findPointsWith_eq_ok_iff.mpr
    ⟨c', _, rev, dom, h1, h2, hH, hH63, hl, hr, hsi, hs, rfl⟩]
  exact congr(Except.ok $(run_searchPoints_eq_deliver hP hH hH63
    (o.one_le_toNat_bLow_normalize H) (o.toNat_bHigh_normalize_le H)
    (wf_of_run_searchIntervals_eq_some hH hH63 hsi) process _ rfl))

/-- The bits of the flags that `Ratpoints.findPointsWith` writes back do not depend on the callback
or its data (`Ratpoints.run_searchPoints_flags`). -/
theorem map_findPointsWith_flags (c : List ℤ) (H : ℕ) (P : Params) (o : Options) {σ σ' : Type}
    (process : ℤ → ℤ → ℤ → σ → Answer σ) (info : σ) (process' : ℤ → ℤ → ℤ → σ' → Answer σ')
    (info' : σ') :
    (findPointsWith c H P o process info).map (fun out ↦
      (out.reversed, out.useSquares, out.useSquares1)) =
      (findPointsWith c H P o process' info').map (fun out ↦
        (out.reversed, out.useSquares, out.useSquares1)) := by
  simp only [findPointsWith]
  split_ifs
  any_goals rfl
  split
  · rfl
  split
  · rfl
  split_ifs
  · rfl
  simp only [Except.map, run_searchPoints_flags]

/-- For well-formed parameters, the data and the count of a successful search with a callback are
those of the delivery of the points of `Ratpoints.findPoints` to it, by the protocol of the
delivery (`Ratpoints.map_findPointsWith_eq_map_findPoints`). -/
theorem info_total_eq_of_findPointsWith_eq_ok {σ : Type} {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {process : ℤ → ℤ → ℤ → σ → Answer σ} {info : σ} {r : Outcome σ}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (hr : findPointsWith c H P o process info = .ok r)
    (hL : findPoints c H P o = .ok L) :
    r.info = (Delivery.deliver process ⟨info, 0, false⟩ L).info ∧
      r.total = (Delivery.deliver process ⟨info, 0, false⟩ L).total := by
  simpa [hr, hL, Except.map] using map_findPointsWith_eq_map_findPoints hP c H o process info

/-- The search with a callback succeeds when `Ratpoints.findPoints` does: the refusals of
`Ratpoints.findPointsWith` do not depend on the callback
(`Ratpoints.findPointsWith_eq_error_iff`). -/
theorem exists_findPointsWith_eq_ok_of_findPoints_eq_ok {σ : Type} {c : List ℤ} {H : ℕ}
    {P : Params} {o : Options} (process : ℤ → ℤ → ℤ → σ → Answer σ) (info : σ)
    {L : List (ℤ × ℤ × ℤ)} (hL : findPoints c H P o = .ok L) :
    ∃ r, findPointsWith c H P o process info = .ok r := by
  rcases h : findPointsWith c H P o process info with _ | r
  · rw [findPoints, findPointsWith_eq_error_iff.mp h] at hL
    simp [Except.map] at hL
  · exact ⟨r, rfl⟩

/-! ### The output of `Ratpoints.findPoints` -/

/-- For well-formed parameters, the list that `Ratpoints.findPoints` returns is that of the points
that the search of the polynomial `c'` that the reversal check of the normalized options hands on
delivers (`Ratpoints.searchList`), with its flag of the reversal and the options of the output, the
normalized range of the denominators and the values of the search intervals `dom` of
`Ratpoints.searchIntervals`, for a sound test of the sieve (`Ratpoints.IsSoundTest`) that does not
depend on the options of the output: with the other options unchanged, `Ratpoints.findPoints`
returns the list of the search with this test for every choice of them
(`Ratpoints.exists_isSoundTest_run_searchPoints_appendPoint`). The polynomial searched has a
positive degree, since the refusals leave a degree `d ≥ 1`
(`Ratpoints.Setup.one_le_of_reversal_eq_ok`); the search intervals of the caller are well formed,
and with the Sturm step on the remainder chain of the polynomial searched is not none. -/
theorem exists_searchList_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) :
    ∃ c' rev S dom, Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev) ∧
      0 < degree c' ∧ 1 ≤ H ∧ H < 2 ^ 63 ∧ IntervalsWF (domainBits o.domain) ∧
      ¬(0 ≤ o.sturm ∧ Id.run (Sturm.chain c' (degree c')) = none) ∧
      Id.run (searchIntervals H o.domain) = some dom ∧
      IsSoundTest c' H (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat S ∧
      L = searchList c' H (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat (domainValues dom)
        S ⟨rev, o.noCheck, o.noY⟩ ∧
      ∀ noCheck noY : Bool, findPoints c H P { o with noCheck, noY } =
        .ok (searchList c' H (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat
          (domainValues dom) S ⟨rev, noCheck, noY⟩) := by
  obtain ⟨out, hout, rfl⟩ : ∃ out, findPointsWith c H P o appendPoint #[] = .ok out ∧
      L = out.info.toList := by
    rcases h' : findPointsWith c H P o appendPoint #[] <;> simp_all [findPoints, Except.map]
  obtain ⟨c', d', rev, dom, h1, h2, hH, hH63, hl, hr, hsi, hs, rfl⟩ :=
    findPointsWith_eq_ok_iff.mp hout
  obtain rfl := Setup.degree_eq_of_reversal_eq_ok rfl hr
  obtain ⟨S, hS, hS'⟩ := exists_isSoundTest_run_searchPoints_appendPoint (c := c') hP hH hH63
    (o.one_le_toNat_bLow_normalize H) (o.toNat_bHigh_normalize_le H)
    (wf_of_run_searchIntervals_eq_some hH hH63 hsi)
  refine ⟨c', rev, S, dom, hr, Setup.one_le_of_reversal_eq_ok hr (by lia), hH, hH63,
    intervalsWF_of_run_searchIntervals_eq_some hsi, hs, hsi, hS, hS' _, fun noCheck noY ↦ ?_⟩
  rw [findPoints, findPointsWith_eq_ok_iff (o := { o with noCheck, noY }).mpr
    ⟨c', _, rev, dom, h1, h2, hH, hH63, hl, hr, hsi, hs, rfl⟩]
  exact congr(Except.ok $(hS' _))

/-- Without `RATPOINTS_NO_CHECK`, for well-formed parameters, the list that `Ratpoints.findPoints`
returns is that of the brute-force reference of the polynomial `c'` that the reversal check of the
normalized options hands on, over the candidate `(1, 0)` and the denominators of its search
(`Ratpoints.searchDens`) in the normalized range with the numerators `a` with `a / b` in the search
intervals `dom` of `Ratpoints.searchIntervals`, in this order, mapped back by
`Ratpoints.Sieve.swapPoint` after a reversal, without the points with `y < 0` under `RATPOINTS_NO_Y`
(`Ratpoints.searchList_of_noCheck_eq_false`). -/
theorem exists_eq_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = false) :
    ∃ c' rev dom, Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev) ∧
      1 ≤ H ∧ H < 2 ^ 63 ∧ IntervalsWF (domainBits o.domain) ∧
      ¬(0 ≤ o.sturm ∧ Id.run (Sturm.chain c' (degree c')) = none) ∧
      Id.run (searchIntervals H o.domain) = some dom ∧
      L = ((pointsOfDen c' (degree c') 0 [1] ++
        (searchDens c' (degree c') (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat).flatMap
          fun b : ℕ ↦ pointsOfDen c' (degree c') b
            ((numerators H).filter fun a : ℤ ↦ decide (InIntervals (domainValues dom) (a / b)))).map
        (if rev then swapPoint else id)).filter fun p ↦ !o.noY || 0 ≤ p.2.1 := by
  obtain ⟨c', rev, S, dom, hr, hd, hH, hH63, hwf, hst, hsi, hS, rfl, -⟩ :=
    exists_searchList_of_findPoints_eq_ok hP h
  exact ⟨c', rev, dom, hr, hH, hH63, hwf, hst, hsi, searchList_of_noCheck_eq_false hS hd _ hc⟩

/-! ### The search region of the options -/

/-- The search region of the options is the whole box when the reversal check of the normalized
options reverses the polynomial. -/
theorem isFullBox_of_reversal_normalize_eq_ok {o : Options} {H : ℕ} {c c' : List ℤ} {d d' : ℕ}
    (h : Setup.reversal (o.normalize H).reverse c d = .ok (c', d', true)) :
    IsFullBox o.domain o.bLow o.bHigh H := by
  have : (o.normalize H).reverse = true := by
    cases hr : (o.normalize H).reverse
    · simp [hr, Setup.reversal_false] at h
    · rfl
  exact (by simpa [o.reverse_normalize H] using this : _ ∧ _).2

/-- A point of the candidate `(1, 0)` of the brute-force reference, mapped back by
`Ratpoints.Sieve.swapPoint` after a reversal, which comes only for the whole box, lies in the
search region of the options: it stays at infinity without a reversal, and becomes `(0, y, 1)`
after one. -/
theorem inRegion_ite_swapPoint_of_mem_pointsOfDen_zero {o : Options} {H : ℕ} {rev : Bool}
    (hb : rev = true → IsFullBox o.domain o.bLow o.bHigh H) (hH : 1 ≤ H) {c : List ℤ} {d : ℕ}
    {p : ℤ × ℤ × ℤ} (hp : p ∈ pointsOfDen c d 0 [1]) :
    InRegion (domainValues o.domain) o.bLow o.bHigh ((if rev then swapPoint else id) p) := by
  obtain ⟨h1, h0, -⟩ := mem_pointsOfDen_iff.mp hp
  cases rev
  · exact .inl h0
  · have hf := hb rfl
    obtain ⟨x, y, z⟩ := p
    obtain rfl : x = 1 := List.mem_singleton.mp h1
    obtain rfl : z = 0 := h0
    exact inRegion_of_isFullBox (List.map_eq_nil_iff.mpr hf.1) (by simpa [IsFullBox] using hf)
      (by simp [swapPoint]) (by simpa [swapPoint] using hH)

/-- A triple `(a, y, b)` with `1 ≤ b ≤ bHigh` for the normalized `bHigh` and `|a| ≤ H`, mapped back
by `Ratpoints.Sieve.swapPoint` after a reversal, which comes only for the whole box, lies in the
search region of the options exactly when `b` is at least the normalized `bLow` and `a / b` lies in
the caller's search intervals, when there are some. -/
theorem inRegion_ite_swapPoint_iff {o : Options} {H : ℕ} {rev : Bool}
    (hb : rev = true → IsFullBox o.domain o.bLow o.bHigh H) {b : ℕ} (hb1 : 1 ≤ b)
    (hbB : b ≤ (o.normalize H).bHigh.toNat) {p : ℤ × ℤ × ℤ} (hz : p.2.2 = b) (hx : |p.1| ≤ H) :
    InRegion (domainValues o.domain) o.bLow o.bHigh ((if rev then swapPoint else id) p) ↔
      (o.normalize H).bLow.toNat ≤ b ∧
        (o.domain = [] ∨ InIntervals (domainValues o.domain) (p.1 / b)) := by
  have hbH := o.toNat_bHigh_normalize_le H
  have hl := o.bLow_normalize_le_iff H (z := b) (by lia)
  cases rev
  · have hh := o.lt_one_or_le_bHigh_of_le (H := H) (z := b) (by lia) (by lia)
    simp [inRegion_iff, hz, ← hl, hh, show b ≠ 0 by lia]
  · obtain ⟨hd, h1, -⟩ := hb rfl
    refine iff_of_true (inRegion_of_isFullBox (List.map_eq_nil_iff.mpr hd)
      (by simpa [IsFullBox] using hb rfl) ?_ ?_) ⟨by lia, .inl hd⟩ <;>
    · simp only [↓reduceIte, swapPoint]
      split_ifs <;> lia [abs_le.mp hx]

/-- The points at infinity and the points of the denominators `b` of `l`, within
`1, …, bHigh` for the normalized `bHigh`, from the normalized `bLow` on and with the numerators `a`
with `a / b` in the caller's search intervals, when there are some, mapped back after a reversal,
are those of all the denominators of `l` in the search region of the options
(`Ratpoints.inRegion_ite_swapPoint_iff`), the whole box after a reversal. -/
theorem map_append_flatMap_filter_eq_filter_inRegion {o : Options} {H : ℕ} {rev : Bool}
    (hb : rev = true → IsFullBox o.domain o.bLow o.bHigh H) (hH : 1 ≤ H) {c : List ℤ} {d : ℕ}
    {l : List ℕ} (hl : ∀ b ∈ l, 1 ≤ b ∧ b ≤ (o.normalize H).bHigh.toNat) :
    (pointsOfDen c d 0 [1] ++ (l.filter ((o.normalize H).bLow.toNat ≤ ·)).flatMap fun b : ℕ ↦
      pointsOfDen c d b ((numerators H).filter fun a : ℤ ↦
        decide (o.domain = [] ∨ InIntervals (domainValues o.domain) (a / b)))).map
      (if rev then swapPoint else id) =
    ((pointsOfDen c d 0 [1] ++ l.flatMap fun b : ℕ ↦ pointsOfDen c d b (numerators H)).map
      (if rev then swapPoint else id)).filter
        (InRegion (domainValues o.domain) o.bLow o.bHigh) := by
  rw [List.filter_map, List.filter_append, List.filter_flatMap, List.flatMap_filter]
  simp only [Function.comp_def]
  rw [List.filter_eq_self.mpr fun p hp ↦
    decide_eq_true (inRegion_ite_swapPoint_of_mem_pointsOfDen_zero hb hH hp)]
  refine congr(List.map _ (_ ++ $(List.flatMap_congr fun b hb' ↦ ?_)))
  have key {q : ℤ × ℤ × ℤ} (hq : q ∈ pointsOfDen c d b (numerators H)) :=
    have ⟨hx, hz, _⟩ := mem_pointsOfDen_iff.mp hq
    inRegion_ite_swapPoint_iff hb (hl b hb').1 (hl b hb').2 hz (mem_numerators_iff.mp hx)
  rw [pointsOfDen_filter]
  by_cases h : (o.normalize H).bLow.toNat ≤ b
  · simp only [h, decide_true, ↓reduceIte]
    exact List.filter_congr fun q hq ↦ by simp [key hq, h]
  · simp only [h, decide_false, Bool.false_eq_true, ↓reduceIte]
    exact (List.filter_eq_nil_iff.mpr fun q hq hq' ↦ h ((key hq).mp (of_decide_eq_true hq')).1).symm

/-- The points at infinity and the points of the denominators of the search from `1` to the
normalized `bHigh` of the polynomial `c'` that the reversal check of the normalized options hands
on, mapped back after a reversal, are a permutation of the brute-force reference of `c` restricted
to the points at infinity and the denominators up to the normalized `bHigh`
(`Ratpoints.perm_filter_bruteForce_append_flatMap_searchDens`,
`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`), which is `H` after a reversal. -/
theorem perm_map_append_flatMap_searchDens {o : Options} {H : ℕ} {c c' : List ℤ} {rev : Bool}
    (hr : Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev))
    (hH : 1 ≤ H) :
    ((pointsOfDen c' (degree c') 0 [1] ++
      (searchDens c' (degree c') 1 (o.normalize H).bHigh.toNat).flatMap fun b : ℕ ↦
        pointsOfDen c' (degree c') b (numerators H)).map (if rev then swapPoint else id)).Perm
      ((bruteForce c H).filter fun p : ℤ × ℤ × ℤ ↦
        p.2.2 = 0 ∨ 1 ≤ p.2.2 ∧ p.2.2 ≤ (o.normalize H).bHigh.toNat) := by
  have hp := (perm_filter_bruteForce_append_flatMap_searchDens c' le_rfl
    (o.one_le_toNat_bHigh_normalize hH) (o.toNat_bHigh_normalize_le H)).map
      (if rev then swapPoint else id)
  cases rev
  · obtain ⟨rfl, -⟩ := Setup.eq_of_reversal_eq_ok_false hr
    simpa using hp
  · have hB : H ≤ (o.normalize H).bHigh.toNat := by
      have := (isFullBox_of_reversal_normalize_eq_ok hr).2.2
      rw [o.toNat_bHigh_normalize H, denominatorBound]
      split_ifs <;> lia
    rw [filter_bruteForce_eq_self c hB]
    rw [Nat.cast_one, filter_bruteForce_eq_self c' hB] at hp
    exact hp.trans (perm_map_swapPoint_bruteForce (Setup.binaryForm_eq_of_reversal_eq_ok rfl hr) H)

/-- A triple with a denominator from `0` to `H` in the search region of the options is at infinity
or has a denominator from `1` to the normalized largest denominator. -/
theorem eq_zero_or_le_toNat_bHigh_normalize_of_inRegion {o : Options}
    {D : List (WithBotTop ℚ × WithBotTop ℚ)} {H : ℕ} {p : ℤ × ℤ × ℤ} (hz : 0 ≤ p.2.2)
    (hzH : p.2.2 ≤ H) (h : InRegion D o.bLow o.bHigh p) :
    p.2.2 = 0 ∨ 1 ≤ p.2.2 ∧ p.2.2 ≤ (o.normalize H).bHigh.toNat := by
  rcases h with h0 | ⟨-, hb, -⟩
  · exact .inl h0
  · rcases hz.eq_or_lt with h0 | h1
    exacts [.inl h0.symm, .inr ⟨h1, o.le_toNat_bHigh_normalize_of_le hzH hb⟩]

/-- The points of the brute-force reference at infinity or with a denominator up to the normalized
largest denominator that pass a test `t` and lie in the search region of the options are those of
the reference that do: the region holds no others
(`Ratpoints.eq_zero_or_le_toNat_bHigh_normalize_of_inRegion`). -/
theorem filter_filter_bruteForce_eq {o : Options} (D : List (WithBotTop ℚ × WithBotTop ℚ))
    (c : List ℤ) (H : ℕ) (t : ℤ × ℤ × ℤ → Bool) :
    ((bruteForce c H).filter fun p : ℤ × ℤ × ℤ ↦
      p.2.2 = 0 ∨ 1 ≤ p.2.2 ∧ p.2.2 ≤ (o.normalize H).bHigh.toNat).filter
        (fun p ↦ t p && InRegion D o.bLow o.bHigh p) =
      (bruteForce c H).filter fun p ↦ t p && InRegion D o.bLow o.bHigh p := by
  rw [List.filter_filter]
  refine List.filter_congr fun p hp ↦ ?_
  obtain ⟨-, -, hz, -, hzH⟩ := mem_bruteForce_iff.mp hp
  by_cases hR : InRegion D o.bLow o.bHigh p
  · simp only [decide_eq_true hR, Bool.and_true, decide_eq_true
      (eq_zero_or_le_toNat_bHigh_normalize_of_inRegion (by lia) hzH hR)]
  · simp only [decide_eq_false hR, Bool.and_false, Bool.false_and]

/-! ### The search region of the caller -/

-- The search intervals of a search are the caller's, or the default interval when the caller gives
-- none.
private theorem eq_nil_or_eq_of_run_searchIntervals_eq_some {H : ℕ}
    {domain dom : List (Double × Double)} (h : Id.run (searchIntervals H domain) = some dom) :
    domain = [] ∨ dom = domain := by
  refine (eq_or_ne domain []).imp id fun hn ↦ ?_
  rw [run_searchIntervals_of_ne_nil H hn (intervalsWF_of_run_searchIntervals_eq_some h)] at h
  exact (Option.some.inj h).symm

-- For `1 ≤ H < 2 ^ 63` and a denominator `b > 0`, the numerators `a` of `-H, …, H` with `a / b` in
-- the search intervals of a search are those with `a / b` in the caller's intervals, when there are
-- some: the default interval holds every such `a / b` (`Ratpoints.exists_run_searchIntervals_nil`).
private theorem filter_numerators_eq_of_run_searchIntervals_eq_some {H : ℕ} (hH : 1 ≤ H)
    (hH63 : H < 2 ^ 63) {domain dom : List (Double × Double)}
    (h : Id.run (searchIntervals H domain) = some dom) {b : ℕ} (hb : 0 < b) :
    (numerators H).filter (fun a : ℤ ↦ decide (InIntervals (domainValues dom) (a / b))) =
      (numerators H).filter fun a : ℤ ↦
        decide (domain = [] ∨ InIntervals (domainValues domain) (a / b)) := by
  rcases eq_or_ne domain [] with rfl | hn
  · obtain ⟨dom', h', -, hall⟩ := exists_run_searchIntervals_nil hH hH63
    obtain rfl : dom' = dom := Option.some.inj (h'.symm.trans h)
    exact List.filter_congr fun a ha ↦ by simp [hall a b hb (natAbs_le_of_mem_numerators ha)]
  · rw [run_searchIntervals_of_ne_nil H hn (intervalsWF_of_run_searchIntervals_eq_some h)] at h
    obtain rfl := Option.some.inj h
    simp [hn]

/-- Without `RATPOINTS_NO_CHECK`, for well-formed parameters, the list that `Ratpoints.findPoints`
returns is the brute-force reference of the polynomial `c'` that the reversal check of the
normalized options hands on, over the candidate `(1, 0)` and the denominators of its search with
the numerators `a` with `a / b` in the caller's search intervals, when there are some, in this
order, mapped back after a reversal, without the points with `y < 0` under `RATPOINTS_NO_Y`: the
search intervals of the search are the caller's, or the default interval, which holds every `a / b`
of the search (`Ratpoints.exists_eq_of_findPoints_eq_ok`,
`Ratpoints.exists_run_searchIntervals_nil`). -/
theorem exists_eq_filter_inIntervals_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = false) :
    ∃ c' rev, Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev) ∧
      1 ≤ H ∧ L = ((pointsOfDen c' (degree c') 0 [1] ++
        (searchDens c' (degree c') (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat).flatMap
          fun b : ℕ ↦ pointsOfDen c' (degree c') b ((numerators H).filter fun a : ℤ ↦
            decide (o.domain = [] ∨ InIntervals (domainValues o.domain) (a / b)))).map
        (if rev then swapPoint else id)).filter fun p ↦ !o.noY || 0 ≤ p.2.1 := by
  obtain ⟨c', rev, dom, hr, hH, hH63, -, -, hsi, rfl⟩ := exists_eq_of_findPoints_eq_ok hP h hc
  refine ⟨c', rev, hr, hH, congr(List.filter _ (List.map _ (_ ++
    $(List.flatMap_congr fun b hb ↦ ?_))))⟩
  rw [filter_numerators_eq_of_run_searchIntervals_eq_some hH hH63 hsi
    (by lia [o.one_le_toNat_bLow_normalize H,
      le_and_le_of_mem_searchDens (o.one_le_toNat_bLow_normalize H) hb])]

/-- Without `RATPOINTS_NO_CHECK`, for well-formed parameters, the list that `Ratpoints.findPoints`
returns is the brute-force reference of the polynomial `c'` that the reversal check of the
normalized options hands on, over the candidate `(1, 0)` and the denominators of its search from `1`
to the normalized largest denominator, in this order, mapped back after a reversal, filtered by the
search region of the options (`Ratpoints.InRegion`) and under `RATPOINTS_NO_Y` by `y ≥ 0`
(`Ratpoints.map_append_flatMap_filter_eq_filter_inRegion`). -/
theorem exists_eq_filter_inRegion_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF)
    (h : findPoints c H P o = .ok L) (hc : o.noCheck = false) :
    ∃ c' rev, Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev) ∧
      1 ≤ H ∧ L = ((pointsOfDen c' (degree c') 0 [1] ++
        (searchDens c' (degree c') 1 (o.normalize H).bHigh.toNat).flatMap fun b : ℕ ↦
          pointsOfDen c' (degree c') b (numerators H)).map (if rev then swapPoint else id)).filter
        fun p ↦ (!o.noY || 0 ≤ p.2.1) && InRegion (domainValues o.domain) o.bLow o.bHigh p := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_filter_inIntervals_of_findPoints_eq_ok hP h hc
  have hb : rev = true → IsFullBox o.domain o.bLow o.bHigh H := by
    rintro rfl
    exact isFullBox_of_reversal_normalize_eq_ok hr
  refine ⟨c', rev, hr, hH, ?_⟩
  rw [searchDens_eq_filter c' (o.one_le_toNat_bLow_normalize H)
    (o.one_le_toNat_bHigh_normalize hH), map_append_flatMap_filter_eq_filter_inRegion hb hH
      fun b hb' ↦ le_and_le_of_mem_searchDens le_rfl hb', List.filter_filter]

/-- Without the options of the output, when the options forbid the reversal and the denominators of
the search are `bLow, …, bHigh` for the normalized range (`Ratpoints.searchDens_eq_range'`: even
degree, `|c_d| = 1`, or the divisor set-up fails), the list that `Ratpoints.findPoints` returns is
the brute-force reference in the search region of the options. -/
theorem eq_filter_bruteForce_of_findPoints_eq_ok_of_reverse_eq_false {c : List ℤ} {H : ℕ}
    {P : Params} {o : Options} {L : List (ℤ × ℤ × ℤ)}
    (hP : P.WF) (h : findPoints c H P o = .ok L) (hc : o.noCheck = false) (hy : o.noY = false)
    (ho : o.reverse = false)
    (hs : searchDens c (degree c) (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat =
      List.range' (o.normalize H).bLow.toNat
        ((o.normalize H).bHigh.toNat + 1 - (o.normalize H).bLow.toNat)) :
    L = (bruteForce c H).filter
      (InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow
        o.bHigh) := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_filter_inIntervals_of_findPoints_eq_ok hP h hc
  rw [o.reverse_normalize H, ho, Bool.false_and, Setup.reversal_false] at hr
  obtain ⟨rfl, -, rfl⟩ := by simpa using hr.symm
  have hB := o.toNat_bHigh_normalize_le H
  rw [hs, List.range'_eq_filter_range' (o.one_le_toNat_bLow_normalize H),
    map_append_flatMap_filter_eq_filter_inRegion (rev := false) nofun hH fun b hb ↦ by
      lia [List.mem_range'_1.mp hb],
    ← Nat.add_sub_cancel (n := (o.normalize H).bHigh.toNat) (m := 1),
    ← filter_bruteForce_eq_append c' hH le_rfl hB]
  simpa [hy] using filter_filter_bruteForce_eq (o := o) _ c' H fun _ ↦ true

/-- Without `RATPOINTS_NO_CHECK`, for well-formed parameters, the list that `Ratpoints.findPoints`
returns is a permutation of the brute-force reference in the search region of the options
(`Ratpoints.InRegion`), without the points with `y < 0` under `RATPOINTS_NO_Y`: the search region
holds the points at infinity and those with a denominator up to the largest of the search
(`Ratpoints.eq_zero_or_le_toNat_bHigh_normalize_of_inRegion`), whose points the search gives
(`Ratpoints.perm_map_append_flatMap_searchDens`). -/
theorem perm_filter_bruteForce_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF)
    (h : findPoints c H P o = .ok L) (hc : o.noCheck = false) :
    L.Perm ((bruteForce c H).filter fun p ↦ (!o.noY || 0 ≤ p.2.1) &&
      InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow o.bHigh
        p) := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_filter_inRegion_of_findPoints_eq_ok hP h hc
  exact ((perm_map_append_flatMap_searchDens hr hH).filter _).trans
    (.of_eq (filter_filter_bruteForce_eq _ c H _))

/-- Without `RATPOINTS_NO_CHECK`, for well-formed parameters, the list that `Ratpoints.findPoints`
returns is `Ratpoints.orderedPoints` for the switch of the reversal of the normalized options and
the largest denominator of the search (`Ratpoints.denominatorBound`), the points in the order of the
specification, those in the search region of the options (`Ratpoints.InRegion`), without those with
`y < 0` under `RATPOINTS_NO_Y`; comparator certifies this (`comparator/Challenge.lean`). -/
theorem eq_orderedPoints_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF)
    (h : findPoints c H P o = .ok L) (hc : o.noCheck = false) :
    L = (orderedPoints maxDivisors (o.reverse && IsFullBox o.domain o.bLow o.bHigh H) c H
        (denominatorBound o.bHigh H)).filter fun p ↦ (!o.noY || 0 ≤ p.2.1) &&
      InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow o.bHigh
        p := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_filter_inRegion_of_findPoints_eq_ok hP h hc
  have hB := o.toNat_bHigh_normalize_le H
  rw [orderedPoints, searchedPoly_eq_of_reversal_eq_ok (o.reverse_normalize H ▸ hr),
    ← o.toNat_bHigh_normalize H]
  dsimp only
  rw [List.flatMap_cons, pointsOfDen_zero_eq_pointsWithDen c' hH,
    searchDens_one_eq_searchDenominators c' (o.one_le_toNat_bHigh_normalize hH),
    List.flatMap_congr fun b hb ↦ (le_and_le_of_mem_searchDenominators hb).elim
      fun h1 h2 ↦ pointsOfDen_eq_pointsWithDen c' h1 (h2.trans hB)]
  cases rev
  · simp only [Bool.false_eq_true, ↓reduceIte, List.map_id]
  · rfl

/-- The brute-force reference of the polynomial that the reversal check hands on, mapped back after
a reversal, has no duplicates: it is a permutation of the reference of `c` after a reversal
(`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`). -/
theorem nodup_map_bruteForce_of_reversal_eq_ok {allow rev : Bool} {c c' : List ℤ} {d' : ℕ}
    (hr : Setup.reversal allow c (degree c) = .ok (c', d', rev)) (H : ℕ) :
    ((bruteForce c' H).map (if rev then swapPoint else id)).Nodup := by
  cases rev
  · simpa using nodup_bruteForce c' H
  · exact (perm_map_swapPoint_bruteForce (Setup.binaryForm_eq_of_reversal_eq_ok rfl hr)
      H).nodup_iff.mpr (nodup_bruteForce c H)

/-! ### The main theorems -/

/-- Without `RATPOINTS_NO_CHECK`, for well-formed parameters and the other options, a triple lies in
the list that `Ratpoints.findPoints` returns exactly when it is a normalized point of height at most
`H` in the search region of the options (`Ratpoints.InRegion`), with `y ≥ 0` under `RATPOINTS_NO_Y`;
comparator certifies this (`comparator/Challenge.lean`). -/
theorem mem_iff_isPoint_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF)
    (h : findPoints c H P o = .ok L) (hc : o.noCheck = false) {p : ℤ × ℤ × ℤ} :
    p ∈ L ↔ IsPoint c H p ∧ (o.noY = true → 0 ≤ p.2.1) ∧
      InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow o.bHigh
        p := by
  rw [(perm_filter_bruteForce_of_findPoints_eq_ok hP h hc).mem_iff, List.mem_filter,
    mem_bruteForce_iff]
  cases o.noY <;> simp

/-- For well-formed parameters and every option, the list that `Ratpoints.findPoints` returns has
no duplicates: without `RATPOINTS_NO_CHECK` it is a sublist of a permutation of the brute-force
reference, filtered under `RATPOINTS_NO_Y` and by the search region, and under
`RATPOINTS_NO_CHECK` the survivors are distinct (`Ratpoints.nodup_searchList_of_noCheck`);
comparator certifies this (`comparator/Challenge.lean`). -/
theorem nodup_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) :
    L.Nodup := by
  obtain ⟨c', rev, S, dom, hr, hd, hH, -, -, -, -, hS, rfl, -⟩ :=
    exists_searchList_of_findPoints_eq_ok hP h
  have hbL := o.one_le_toNat_bLow_normalize H
  have hbH := o.one_le_toNat_bHigh_normalize (H := H) hH
  cases hc : o.noCheck
  · rw [searchList_of_noCheck_eq_false hS hd _ rfl]
    refine .filter _ (.sublist (.map _ (.append_left (.flatMap_right _
      (g := fun b : ℕ ↦ pointsOfDen c' (degree c') b (numerators H)) fun b _ ↦ ?_) _)) ?_)
    · rw [pointsOfDen_filter]
      exact List.filter_sublist
    · refine ((perm_filter_bruteForce_append_flatMap_searchDens c' hbL hbH
        (o.toNat_bHigh_normalize_le H)).map _).nodup_iff.mpr (.sublist (.map _ List.filter_sublist)
          (nodup_map_bruteForce_of_reversal_eq_ok hr H))
  · exact nodup_searchList_of_noCheck hH hbL hbH (o.toNat_bHigh_normalize_le H) _ S rfl

/-- Without the options of the output, the set of the elements of the list that
`Ratpoints.findPoints` returns is the set of the points in the search region of the options. -/
theorem toFinset_eq_filter_points_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF)
    (h : findPoints c H P o = .ok L) (hc : o.noCheck = false) (hy : o.noY = false) :
    L.toFinset = (points c H).filter
      (InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow
        o.bHigh) := by
  rw [List.toFinset_eq_of_perm _ _ (perm_filter_bruteForce_of_findPoints_eq_ok hP h hc),
    List.toFinset_filter, toFinset_bruteForce]
  simp [hy]

/-! ### `RATPOINTS_NO_CHECK` -/

/-- Under `RATPOINTS_NO_CHECK`, for well-formed parameters, every triple of the list that
`Ratpoints.findPoints` returns is `(x, 0, z)` for the pair `(x, z)` of a normalized point of height
at most `H` in the search region of the options, whether it is a point or not: `x` prime to `z`,
`z > 0` or `(x, z) = (1, 0)`, `|x| ≤ H`, `z ≤ H` and `(x, 0, z)` in the search region
(`Ratpoints.exists_eq_of_mem_searchList_of_noCheck`, `Ratpoints.mem_region_of_mem_searchList`), the
search intervals being the caller's or the default one; comparator certifies this
(`comparator/Challenge.lean`). -/
theorem exists_eq_of_mem_of_findPoints_eq_ok_of_noCheck {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = true) {q : ℤ × ℤ × ℤ} (hq : q ∈ L) :
    ∃ x z : ℤ, q = (x, 0, z) ∧ Int.gcd x z = 1 ∧ (0 < z ∨ z = 0 ∧ x = 1) ∧ |x| ≤ H ∧ z ≤ H ∧
      InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow o.bHigh
        q := by
  obtain ⟨c', rev, S, dom, hr, -, hH, -, -, -, hsi, -, rfl, -⟩ :=
    exists_searchList_of_findPoints_eq_ok hP h
  have hbL := o.one_le_toNat_bLow_normalize H
  obtain ⟨x, z, rfl, hn⟩ := exists_eq_of_mem_searchList_of_noCheck hc hH hbL
    (o.toNat_bHigh_normalize_le H) hq
  refine ⟨x, z, rfl, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, ?_⟩
  cases rev
  · rcases mem_region_of_mem_searchList rfl hbL hq with h0 | ⟨h1, h2, h3⟩
    · exact .inl h0
    · refine .inr ⟨(o.bLow_normalize_le_iff H (by lia)).mp h1,
        o.lt_one_or_le_bHigh_of_le h2 hn.2.2.2, ?_⟩
      rcases eq_nil_or_eq_of_run_searchIntervals_eq_some hsi with hd | rfl
      · exact .inl (List.map_eq_nil_iff.mpr hd)
      · exact .inr h3
  · have hb := isFullBox_of_reversal_normalize_eq_ok hr
    exact inRegion_of_isFullBox (by simp [hb.1]) (by simpa [IsFullBox] using hb)
      (by rcases hn.2.1 with h0 | h0 <;> lia) hn.2.2.2

/-- Under `RATPOINTS_NO_CHECK`, for well-formed parameters, the list `L'` that
`Ratpoints.findPoints` returns for the same input with `RATPOINTS_NO_CHECK` cleared and
`RATPOINTS_NO_Y` set, with `y` replaced by `0`, is a sublist of the list `L` that it returns: both
searches run with the same test of the sieve and the same search region, so that the points come in
the same order among the survivors (`Ratpoints.map_searchList_sublist`); comparator certifies this
(`comparator/Challenge.lean`). -/
theorem map_sublist_of_findPoints_eq_ok_of_noCheck {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L L' : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = true)
    (h' : findPoints c H P { o with noCheck := false, noY := true } = .ok L') :
    (L'.map fun q ↦ (q.1, 0, q.2.2)).Sublist L := by
  obtain ⟨c', rev, S, dom, -, -, -, -, -, -, -, -, rfl, hall⟩ :=
    exists_searchList_of_findPoints_eq_ok hP h
  obtain rfl := Except.ok.inj (h'.symm.trans (hall false true))
  rw [hc]
  exact map_searchList_sublist c' H _ _ _ S rev o.noY

/-- Under `RATPOINTS_NO_CHECK`, for well-formed parameters, the list that `Ratpoints.findPoints`
returns has the triple `(x, 0, z)` of every normalized point `(x, y, z)` of height at most `H` in
the search region of the options: the point `(x, |y|, z)` is in the list of the search with
`RATPOINTS_NO_CHECK` cleared and `RATPOINTS_NO_Y` set
(`Ratpoints.map_sublist_of_findPoints_eq_ok_of_noCheck`); comparator certifies this
(`comparator/Challenge.lean`). -/
theorem mem_of_isPoint_of_findPoints_eq_ok_of_noCheck {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF)
    (h : findPoints c H P o = .ok L) (hc : o.noCheck = true) {p : ℤ × ℤ × ℤ}
    (hp : IsPoint c H p)
    (hr : InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow
      o.bHigh p) :
    (p.1, 0, p.2.2) ∈ L := by
  obtain ⟨c', rev, S, dom, -, -, -, -, -, -, -, -, -, hall⟩ :=
    exists_searchList_of_findPoints_eq_ok hP h
  have hp' := (mem_iff_isPoint_of_findPoints_eq_ok (o := { o with noCheck := false, noY := true })
    hP (hall false true) rfl (p := (p.1, |p.2.1|, p.2.2))).mpr
      ⟨by simpa [IsPoint, sq_abs] using hp, fun _ ↦ abs_nonneg _, hr⟩
  exact (map_sublist_of_findPoints_eq_ok_of_noCheck hP h hc (hall false true)).subset
    (List.mem_map.mpr ⟨_, hp', rfl⟩)

/-! ### The refusals -/

/-- With the Sturm step on (`0 ≤ o.sturm`, as in a run of the program without options),
`Ratpoints.findPoints` refuses exactly the inputs with fewer than two or more than
`Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or more, which is
not a `long` (`Ratpoints.fitsLong_natCast`), the binary forms `Ratpoints.binaryFormPoly c` that are
not squarefree, and search intervals that are not well formed (`Ratpoints.IntervalsWF`), for all
parameters, whether the reversal is allowed or not; comparator certifies this
(`comparator/Challenge.lean`). -/
theorem exists_findPoints_eq_error_iff_of_sturm_nonneg {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} (hs : 0 ≤ o.sturm) :
    (∃ e, findPoints c H P o = .error e) ↔
      c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        ¬ Squarefree (binaryFormPoly c) ∨
        ¬ IntervalsWF (o.domain.map fun i ↦ (i.1.bits, i.2.bits)) := by
  rw [exists_findPoints_eq_error_iff, findPointsWith, BruteForce.degree_eq]
  simp only [fitsLong_natCast, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  split_ifs with h1 h2 h3 h4
  · simp [h1]
  · simp [h2]
  · grind
  · simp [not_squarefree_binaryFormPoly_of_lt h4]
  simp only [h1, h2, not_or.mp h3, false_or]
  split <;> rename_i hr
  · exact iff_of_true ⟨_, rfl⟩ (.inl (Setup.not_squarefree_binaryFormPoly_of_reversal_eq_error hr))
  rename_i c' d' rev
  split <;> rename_i hsi
  · exact iff_of_true ⟨_, rfl⟩ (.inr ((run_searchIntervals_eq_none_iff H o.domain).mp hsi))
  have hwf := intervalsWF_of_run_searchIntervals_eq_some hsi
  rw [← Sturm.run_chain_eq_none_iff_of_reversal_eq_ok (by lia) (by lia) hr]
  split_ifs <;> simp_all [o.sturm_normalize_nonneg_iff H]

/-- The reversal check of the normalized options refuses exactly when the reversal is allowed, the
search region is the whole box (`Ratpoints.IsFullBox`), the degree is even and `c₀ = c₁ = 0`. -/
theorem exists_reversal_normalize_eq_error_iff {o : Options} {H : ℕ} {c : List ℤ} {d : ℕ} :
    (∃ e, Setup.reversal (o.normalize H).reverse c d = .error e) ↔
      o.reverse = true ∧ IsFullBox o.domain o.bLow o.bHigh H ∧ d % 2 = 0 ∧ c.getD 0 0 = 0 ∧
        c.getD 1 0 = 0 := by
  rw [Setup.exists_reversal_eq_error_iff, o.reverse_normalize H, Bool.and_eq_true,
    decide_eq_true_eq, and_assoc]

/-- Without the Sturm step (`o.sturm < 0`, the option `-s` of the program), `Ratpoints.findPoints`
refuses, besides the coefficient lists of fewer than two or more than `Ratpoints.maxDegree + 1`
entries and the height bound `0` or one of `2 ^ 63` or more, which is not a `long`
(`Ratpoints.fitsLong_natCast`), exactly the forms whose leading zeros lower `⌈n / 2⌉`, for `n + 1`
coefficients, that is `d + 2 ≤ 2 ⌈n / 2⌉` for the degree `d`, those of even degree with
`c₀ = c₁ = 0` when the reversal is allowed and the search region is the whole box
(`Ratpoints.IsFullBox`), forms that are not squarefree, but not all of them, and search intervals
that are not well formed (`Ratpoints.IntervalsWF`); comparator certifies this
(`comparator/Challenge.lean`), so that a `Ratpoints.findPoints` that refused every input under `-s`
would not pass. -/
theorem exists_findPoints_eq_error_iff_of_sturm_neg {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} (hs : o.sturm < 0) :
    (∃ e, findPoints c H P o = .error e) ↔
      c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        degree c + 2 ≤ 2 * (c.length / 2) ∨
        o.reverse = true ∧ IsFullBox o.domain o.bLow o.bHigh H ∧ degree c % 2 = 0 ∧
          c.getD 0 0 = 0 ∧ c.getD 1 0 = 0 ∨
        ¬ IntervalsWF (o.domain.map fun i ↦ (i.1.bits, i.2.bits)) := by
  rw [exists_findPoints_eq_error_iff, findPointsWith, BruteForce.degree_eq]
  simp only [fitsLong_natCast, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  split_ifs with h1 h2 h3 h4
  · simp [h1]
  · simp [h2]
  · grind
  · simp only [Except.error.injEq, exists_eq', true_iff]
    lia
  simp only [h1, h2, not_or.mp h3, false_or, show ¬ degree c + 2 ≤ 2 * (c.length / 2) by lia]
  split <;> rename_i hr
  · exact iff_of_true ⟨_, rfl⟩ (.inl (exists_reversal_normalize_eq_error_iff.mp ⟨_, hr⟩))
  split <;> rename_i hsi
  · exact iff_of_true ⟨_, rfl⟩ (.inr ((run_searchIntervals_eq_none_iff H o.domain).mp hsi))
  split_ifs with h5
  · exact absurd ((o.sturm_normalize_nonneg_iff H).mp h5.1) hs.not_ge
  simp only [exists_false, false_iff, not_or, not_and, not_not]
  refine ⟨fun h1 h2 h3 h4 h5 ↦ ?_, intervalsWF_of_run_searchIntervals_eq_some hsi⟩
  obtain ⟨e, he⟩ := exists_reversal_normalize_eq_error_iff.mpr ⟨h1, h2, h3, h4, h5⟩
  simp only [hr, reduceCtorEq] at he

/-! ### The axioms of the main theorems -/

/--
info: 'Ratpoints.perm_filter_bruteForce_of_findPoints_eq_ok' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms perm_filter_bruteForce_of_findPoints_eq_ok

/--
info: 'Ratpoints.mem_iff_isPoint_of_findPoints_eq_ok' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms mem_iff_isPoint_of_findPoints_eq_ok

/--
info: 'Ratpoints.nodup_of_findPoints_eq_ok' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms nodup_of_findPoints_eq_ok

/--
info: 'Ratpoints.toFinset_eq_filter_points_of_findPoints_eq_ok' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toFinset_eq_filter_points_of_findPoints_eq_ok

/--
info: 'Ratpoints.exists_findPoints_eq_error_iff_of_sturm_nonneg' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_findPoints_eq_error_iff_of_sturm_nonneg

/--
info: 'Ratpoints.eq_orderedPoints_of_findPoints_eq_ok' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms eq_orderedPoints_of_findPoints_eq_ok

/--
info: 'Ratpoints.exists_findPoints_eq_error_iff_of_sturm_neg' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_findPoints_eq_error_iff_of_sturm_neg

/--
info: 'Ratpoints.map_findPointsWith_eq_map_findPoints' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms map_findPointsWith_eq_map_findPoints

/--
info: 'Ratpoints.exists_eq_of_mem_of_findPoints_eq_ok_of_noCheck' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_eq_of_mem_of_findPoints_eq_ok_of_noCheck

/--
info: 'Ratpoints.mem_of_isPoint_of_findPoints_eq_ok_of_noCheck' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mem_of_isPoint_of_findPoints_eq_ok_of_noCheck

/--
info: 'Ratpoints.map_sublist_of_findPoints_eq_ok_of_noCheck' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms map_sublist_of_findPoints_eq_ok_of_noCheck

end Ratpoints

end
