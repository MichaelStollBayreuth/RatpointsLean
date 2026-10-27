/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.FindPoints
public import Ratpoints.Proof.SturmRegion

import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Order
import Ratpoints.Proof.Sieve
import Ratpoints.Proof.Tables

/-!
# The output of the search and the refusals

`Ratpoints.findPointsWith` searches the polynomial that the reversal check of the normalized options
hands on, on the search intervals that the Sturm step leaves of those of
`Ratpoints.searchIntervals`, unless it refuses the input or the Sturm step returns before the search
(`Ratpoints.findPointsWith_eq_ok_iff`); its refusals and the bits of the flags and the search
intervals that it writes back do not depend on the callback, and for every value of the options of
the sieve it gives the data and the count of the delivery (`Ratpoints.Delivery.deliver`) of the list
that `Ratpoints.findPoints`, its instance with the appending callback, returns: the protocol of the
delivery (`Ratpoints.map_findPointsWith_eq_map_findPoints`). That list is the list of the points
that the search of the polynomial searched delivers on its search region after the Sturm step
(`Ratpoints.searchRegion`) for a sound test of the sieve, which does not depend on the options of
the output (`Ratpoints.exists_searchList_of_findPoints_eq_ok`); without `RATPOINTS_NO_CHECK` it is
the brute-force reference of the polynomial searched, over the candidate `(1, 0)` and the
denominators of the search with the numerators in that region, mapped back after a reversal, without
the points with `y < 0` under `RATPOINTS_NO_Y` (`Ratpoints.exists_eq_of_findPoints_eq_ok`). Assuming
Sturm's theorem (`Ratpoints.SturmTheorem`) when the Sturm step is on, the region holds the `x / z`
of every point in the search region of the options, and lies inside it: the list is that of the
points of the specification in the search region (`Ratpoints.InRegion`) in the order of
`Ratpoints.orderedPoints`, so that it holds exactly these points, those with `y ≥ 0` under
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

* `Ratpoints.findPointsWith_eq`: the search with a callback and the print channel that prints
  nothing, as the refusals in the order of the program followed by the search.
* `Ratpoints.findPointsWith_eq_ok_iff`, `Ratpoints.findPointsWith_eq_error_iff`,
  `Ratpoints.exists_findPoints_eq_error_iff`: what `Ratpoints.findPointsWith` returns, and its
  refusals, which do not depend on the callback.
* `Ratpoints.map_findPointsWith_eq_map_findPoints`: for every value of the options of the sieve, the
  data and the count of `Ratpoints.findPointsWith` are those of the delivery of the list of
  `Ratpoints.findPoints`; `Ratpoints.map_findPointsWith_flags`: the bits of the flags and the search
  intervals written back do not depend on the callback.
* `Ratpoints.info_total_eq_of_findPointsWith_eq_ok`: for every value of the options of the sieve,
  the data and the count of a successful search with a callback are those of the delivery of the
  list of `Ratpoints.findPoints`; `Ratpoints.exists_findPointsWith_eq_ok_of_findPoints_eq_ok`: the
  search with a callback succeeds when `Ratpoints.findPoints` does.
* `Ratpoints.exists_searchList_of_findPoints_eq_ok`: the list of `Ratpoints.findPoints` is that of
  the search on its search region with a sound test of the sieve, the same for every choice of the
  options of the output.
* `Ratpoints.exists_eq_of_findPoints_eq_ok`: without `RATPOINTS_NO_CHECK`, it is the reference of
  the polynomial searched on its search region, mapped back after a reversal, filtered under
  `RATPOINTS_NO_Y`.
* `Ratpoints.exists_eq_filter_inRegion_of_findPoints_eq_ok`: assuming Sturm's theorem when the
  Sturm step is on, without `RATPOINTS_NO_CHECK`, the list is that of the reference of the
  polynomial searched over the denominators of its search up to the largest, mapped back after a
  reversal, filtered by the search region of the options and under `RATPOINTS_NO_Y`.
* `Ratpoints.eq_orderedPoints_of_findPoints_eq_ok`: assuming Sturm's theorem when the Sturm step is
  on, without `RATPOINTS_NO_CHECK`, the list is `Ratpoints.orderedPoints`, filtered under
  `RATPOINTS_NO_Y` and by the search region;
  `Ratpoints.eq_filter_bruteForce_of_findPoints_eq_ok_of_reverse_eq_false`: the reference in the
  search region of the options without the options of the output, when the options forbid the
  reversal and the denominators of the search are those of the range.
* `Ratpoints.perm_filter_bruteForce_of_findPoints_eq_ok`: assuming Sturm's theorem when the Sturm
  step is on, without `RATPOINTS_NO_CHECK`, the list is a permutation of the reference in the
  search region, filtered under `RATPOINTS_NO_Y`.
* `Ratpoints.mem_iff_isPoint_of_findPoints_eq_ok`: assuming Sturm's theorem when the Sturm step is
  on, without `RATPOINTS_NO_CHECK`, a triple lies in the list exactly when it is a normalized point
  of height at most `H` in the search region, with `y ≥ 0` under `RATPOINTS_NO_Y`.
* `Ratpoints.toFinset_eq_filter_points_of_findPoints_eq_ok`: assuming Sturm's theorem when the
  Sturm step is on, without the options of the output, its set of elements is that of the points in
  the search region.
* `Ratpoints.findPoints_sturm_neg_eq_ok`: assuming Sturm's theorem when the Sturm step is on,
  without `RATPOINTS_NO_CHECK`, the Sturm step changes only the speed.
* `Ratpoints.nodup_of_findPoints_eq_ok`: for every option, the list has no duplicates.
* `Ratpoints.exists_eq_of_mem_of_findPoints_eq_ok_of_noCheck`,
  `Ratpoints.mem_of_isPoint_of_findPoints_eq_ok_of_noCheck`,
  `Ratpoints.map_sublist_of_findPoints_eq_ok_of_noCheck`: under `RATPOINTS_NO_CHECK`, the list holds
  triples `(x, 0, z)` of normalized pairs of height at most `H` in the search region, among them,
  assuming Sturm's theorem when the Sturm step is on, `(x, 0, z)` for every point `(x, y, z)` in it,
  and the list of the search with `RATPOINTS_NO_CHECK` cleared and `RATPOINTS_NO_Y` set, with `y`
  replaced by `0`, is a sublist of it.
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
denominators (`Ratpoints.Options.normalize`) and the search intervals of the Sturm step, which are
well formed (`Ratpoints.wf_of_run_searchIntervals_eq_some`, `Ratpoints.run_sturmRegion_subset`;
`Ratpoints.exists_isSoundTest_run_searchPoints`, `Ratpoints.run_searchPoints_eq_deliver`,
`Ratpoints.searchList_of_noCheck_eq_false`); the binary form of a reversed polynomial is that of `c`
with `x` and `z` exchanged (`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`), so that its
reference, mapped back, is a permutation of that of `c`
(`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`), and a reversal comes only for the whole box
(`Ratpoints.isFullBox_of_reversal_normalize_eq_ok`). In the terms of the specification of the order,
the reversal check hands on the polynomial of `Ratpoints.searchedPoly`
(`Ratpoints.searchedPoly_eq_of_reversal_eq_ok`), the denominators of the search are those of
`Ratpoints.searchDenominators` up to the largest denominator
(`Ratpoints.searchDens_one_eq_searchDenominators`, `Ratpoints.searchDens_eq_filter`), and the
reference finds over a denominator, and over the candidate `(1, 0)`, the points of
`Ratpoints.pointsWithDen` (`Ratpoints.pointsOfDen_eq_pointsWithDen`,
`Ratpoints.pointsOfDen_zero_eq_pointsWithDen`). Under `RATPOINTS_NO_CHECK` the search delivers, for
the same sound test of the sieve, the survivors of the numerators prime to the denominators of the
search in its search region (`Ratpoints.exists_eq_of_mem_searchList_of_noCheck`,
`Ratpoints.mem_region_of_mem_searchList`, `Ratpoints.searchRegion_subset`, distinct by
`Ratpoints.nodup_searchList_of_noCheck`), of which the points with `y ≥ 0` that the search delivers
without it are a sublist (`Ratpoints.map_searchList_sublist`). Of the refusals, the heights that are
not `long`s are those of `2 ^ 63` or more (`Ratpoints.fitsLong_natCast`), and the test of the
leading zeros and that of the reversal check stand for `Z ^ 2 ∣ Φ_c` and `X ^ 2 ∣ Φ_c`
(`Ratpoints.not_squarefree_binaryFormPoly_of_lt`,
`Ratpoints.Setup.not_squarefree_binaryFormPoly_of_reversal_eq_error`), the refusal of the search
intervals is the negation of `Ratpoints.IntervalsWF` (`Ratpoints.run_searchIntervals_eq_none_iff`),
and after them the Sturm step refuses exactly when the remainder chain of the polynomial searched is
none (`Ratpoints.run_sturmRegion_eq_error_iff`), that is when `Φ_c` is not squarefree
(`Ratpoints.Sturm.run_chain_eq_none_iff_of_reversal_eq_ok`). Assuming Sturm's theorem when the Sturm
step is on, the search region after it holds, of the numerators of the points of a denominator,
exactly those in the caller's search intervals (`Ratpoints.searchRegion_covers`,
`Ratpoints.searchRegion_subset`, `Ratpoints.elim_searchRegion_pointsOfDen_filter`), and when it
returns before the search the polynomial searched has no points at infinity
(`Ratpoints.elim_searchRegion_pointsOfDen_zero`); the filter by the caller's intervals and the
denominators from the normalized `bLow` on is the filter by the search region of the options
(`Ratpoints.inRegion_ite_swapPoint_iff`, `Ratpoints.map_append_flatMap_filter_eq_filter_inRegion`),
which holds the points at infinity and those of the denominators up to the largest of the search
(`Ratpoints.eq_zero_or_le_toNat_bHigh_normalize_of_inRegion`,
`Ratpoints.perm_map_append_flatMap_searchDens`). The search without the Sturm step refuses no other
inputs, so that it returns the same list (`Ratpoints.findPoints_sturm_neg_eq_ok`).
-/
@[expose] public section

namespace Ratpoints

open BruteForce Sieve

/-! ### The search with a callback -/

/-- `Ratpoints.findPointsWith` with the print channel that prints nothing, as the refusals in the
order of the program followed by the search: the report of the library prints nothing, and a refusal
gives back its error alone. -/
theorem findPointsWith_eq (c : List ℤ) (H : ℕ) (s : SieveOptions) (o : Options) {σ : Type}
    (process : ℤ → ℤ → ℤ → σ → Answer σ) (info : σ) :
    findPointsWith c H s o process info =
      if maxDegree + 1 < c.length then .error .tooManyCoefficients
      else if c.length < 2 then .error .tooFewCoefficients
      else if H = 0 ∨ !fitsLong H then .error .incorrectHeight
      else if (BruteForce.degree c + 1) / 2 < c.length / 2 then .error .notSquarefree
      else match Setup.reversal (o.normalize H).reverse c (BruteForce.degree c) with
        | .error e => .error e
        | .ok (c', d', rev) => match Id.run (searchIntervals H o.domain) with
          | none => .error .badArgs
          | some dom => match Id.run (sturmRegion c' d' (o.normalize H).sturm dom) with
            | .error e => .error e
            | .ok none => .ok ⟨info, 0, rev, false, false, [], 0, 0, 0⟩
            | .ok (some (dom', empty)) => .ok (Id.run (searchPoints process c' d' H s.normalize
                (decide (s.numPrimes < 0)) ⟨rev, o.noCheck, o.noY⟩ (o.normalize H).bLow.toNat
                (o.normalize H).bHigh.toNat dom' empty (fun _ s ↦ s) ⟨info, 0, false⟩)) := by
  simp only [findPointsWith, findPointsVerbose]
  split_ifs <;> try rfl
  simp only [findPointsWork]
  rcases Setup.reversal (o.normalize H).reverse c (BruteForce.degree c) with _ | ⟨c', d', rev⟩
  · rfl
  rcases hsi : Id.run (searchIntervals H o.domain) with _ | dom
  · simp [hsi, Except.mapError]
  rcases hst : Id.run (sturmRegion c' d' (o.normalize H).sturm dom) with e | _ | ⟨dom', empty⟩ <;>
    simp [hsi, hst, Except.mapError]

/-- `Ratpoints.findPointsWith` returns the outcome `out` exactly when it refuses none of its inputs,
in the order of the program, and `out` is either, when the Sturm step returns before the search
(`find_points.c:4889`), the data `info` with the count `0`, the flag of the reversal and no search
intervals, or the outcome of the search of the polynomial `c'` of degree `d'` that the reversal
check of the normalized options hands on, with the flag of the reversal and the options of the
output, the normalized range of the denominators and the search intervals that the Sturm step
leaves of those of `Ratpoints.searchIntervals`, from the data `info`, the count `0` and the flag of
the stop clear. -/
theorem findPointsWith_eq_ok_iff {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options} {σ : Type}
    {process : ℤ → ℤ → ℤ → σ → Answer σ} {info : σ} {out : Outcome σ} :
    findPointsWith c H s o process info = .ok out ↔ ∃ c' d' rev dom, c.length ≤ maxDegree + 1 ∧
      2 ≤ c.length ∧ 1 ≤ H ∧ H < 2 ^ 63 ∧ c.length / 2 ≤ (degree c + 1) / 2 ∧
      Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', d', rev) ∧
      Id.run (searchIntervals H o.domain) = some dom ∧
      (Id.run (sturmRegion c' d' (o.normalize H).sturm dom) = .ok none ∧
          out = ⟨info, 0, rev, false, false, [], 0, 0, 0⟩ ∨
        ∃ dom' empty, Id.run (sturmRegion c' d' (o.normalize H).sturm dom) =
          .ok (some (dom', empty)) ∧
          out = Id.run (searchPoints process c' d' H s.normalize (decide (s.numPrimes < 0))
            ⟨rev, o.noCheck, o.noY⟩ (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat dom'
            empty (fun _ s ↦ s) ⟨info, 0, false⟩)) := by
  rw [findPointsWith_eq, ← BruteForce.degree_eq]
  simp only [fitsLong_natCast, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  split_ifs with h1 h2 h3 h4
  any_goals lia
  split <;> rename_i hr
  · simp [hr]
  rename_i c' d' rev
  rcases Id.run (searchIntervals H o.domain) with _ | dom
  · simp [hr]
  rcases hst : Id.run (sturmRegion c' d' (o.normalize H).sturm dom) with e | _ | ⟨dom', empty⟩
  · simp [hr, hst]
  all_goals have h5 : 1 ≤ H ∧ H < 9223372036854775808 := by lia
  all_goals simp [-Bool.exists_bool, hr, hst, Nat.le_of_not_lt h1, Nat.le_of_not_lt h2, h5,
    Nat.le_of_not_lt h4, eq_comm]

/-- The refusals of `Ratpoints.findPointsWith` do not depend on the callback or its data. -/
theorem findPointsWith_eq_error_iff {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options}
    {σ σ' : Type} {process : ℤ → ℤ → ℤ → σ → Answer σ} {info : σ}
    {process' : ℤ → ℤ → ℤ → σ' → Answer σ'}
    {info' : σ'} {e : Refusal} :
    findPointsWith c H s o process info = .error e ↔
      findPointsWith c H s o process' info' = .error e := by
  rw [findPointsWith_eq, findPointsWith_eq]
  split_ifs <;> try simp
  rcases Setup.reversal (o.normalize H).reverse c (BruteForce.degree c) with _ | ⟨c', d', rev⟩
  · simp
  rcases Id.run (searchIntervals H o.domain) with _ | dom
  · simp
  rcases hst : Id.run (sturmRegion c' d' (o.normalize H).sturm dom) with e | _ | ⟨dom', empty⟩ <;>
    simp [hst]

/-- `Ratpoints.findPoints` refuses an input exactly when `Ratpoints.findPointsWith` with the
appending callback does. -/
theorem exists_findPoints_eq_error_iff {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options} :
    (∃ e, findPoints c H s o = .error e) ↔
      ∃ e, findPointsWith c H s o appendPoint #[] = .error e := by
  rw [findPoints]
  rcases findPointsWith c H s o appendPoint #[] <;> simp [Except.map]

/-- For every option, `Ratpoints.findPointsWith` with a callback and its
data gives, besides the bits of the flags and the search intervals written back, the data and the
count of the delivery (`Ratpoints.Delivery.deliver`) of the list that `Ratpoints.findPoints`
returns, from the data, the count `0` and the flag of the stop clear, and it refuses the same inputs
with the same errors: the calls of the callback are those of the points of that list, in its order,
up to and including the first that stops the search (`Ratpoints.run_searchPoints_eq_deliver`); when
the Sturm step returns before the search, there are no calls and no points; comparator certifies
this (`comparator/Challenge.lean`). -/
theorem map_findPointsWith_eq_map_findPoints (c : List ℤ) (H : ℕ) (s : SieveOptions)
    (o : Options) {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (info : σ) :
    (findPointsWith c H s o process info).map (fun out ↦ (out.info, out.total)) =
      (findPoints c H s o).map (fun L ↦
        let r := Delivery.deliver process ⟨info, 0, false⟩ L
        (r.info, r.total)) := by
  rcases h : findPointsWith c H s o appendPoint #[] with e | out
  · rw [findPoints, h, findPointsWith_eq_error_iff.mpr h]
    rfl
  obtain ⟨c', d', rev, dom, h1, h2, hH, hH63, hl, hr, hsi, hst⟩ := findPointsWith_eq_ok_iff.mp h
  obtain rfl := Setup.degree_eq_of_reversal_eq_ok rfl hr
  rcases hst with ⟨hst, rfl⟩ | ⟨dom', empty, hst, rfl⟩
  · rw [findPoints, h, findPointsWith_eq_ok_iff.mpr
      ⟨c', _, rev, dom, h1, h2, hH, hH63, hl, hr, hsi, .inl ⟨hst, rfl⟩⟩]
    rfl
  · have hwf := (run_sturmRegion_subset (o.sturm_normalize_le H)
      (wf_of_run_searchIntervals_eq_some hH hH63 hsi) hst).1
    rw [findPoints, h, findPointsWith_eq_ok_iff.mpr
      ⟨c', _, rev, dom, h1, h2, hH, hH63, hl, hr, hsi, .inr ⟨dom', empty, hst, rfl⟩⟩]
    exact congr(Except.ok $(run_searchPoints_eq_deliver s (decide (s.numPrimes < 0)) hH hH63
      (o.one_le_toNat_bLow_normalize H) (o.toNat_bHigh_normalize_le H) hwf empty process _ rfl))

/-- The bits of the flags and the search intervals that `Ratpoints.findPointsWith` writes back do
not depend on the callback or its data (`Ratpoints.run_searchPoints_flags`). -/
theorem map_findPointsWith_flags (c : List ℤ) (H : ℕ) (s : SieveOptions) (o : Options) {σ σ' : Type}
    (process : ℤ → ℤ → ℤ → σ → Answer σ) (info : σ) (process' : ℤ → ℤ → ℤ → σ' → Answer σ')
    (info' : σ') :
    (findPointsWith c H s o process info).map (fun out ↦
      (out.reversed, out.useSquares, out.useSquares1, out.domain)) =
      (findPointsWith c H s o process' info').map (fun out ↦
        (out.reversed, out.useSquares, out.useSquares1, out.domain)) := by
  rw [findPointsWith_eq, findPointsWith_eq]
  split_ifs <;> try rfl
  rcases Setup.reversal (o.normalize H).reverse c (BruteForce.degree c) with _ | ⟨c', d', rev⟩
  · rfl
  rcases Id.run (searchIntervals H o.domain) with _ | dom
  · rfl
  rcases hst : Id.run (sturmRegion c' d' (o.normalize H).sturm dom) with e | _ | ⟨dom', empty⟩ <;>
    simp [hst, Except.map, run_searchPoints_flags]

/-- For every value of the options of the sieve, the data and the count of a successful search with
a callback are those of the delivery of the points of `Ratpoints.findPoints` to it, by the protocol
of the delivery (`Ratpoints.map_findPointsWith_eq_map_findPoints`). -/
theorem info_total_eq_of_findPointsWith_eq_ok {σ : Type} {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {process : ℤ → ℤ → ℤ → σ → Answer σ} {info : σ} {r : Outcome σ}
    {L : List (ℤ × ℤ × ℤ)} (hr : findPointsWith c H s o process info = .ok r)
    (hL : findPoints c H s o = .ok L) :
    r.info = (Delivery.deliver process ⟨info, 0, false⟩ L).info ∧
      r.total = (Delivery.deliver process ⟨info, 0, false⟩ L).total := by
  simpa [hr, hL, Except.map] using map_findPointsWith_eq_map_findPoints c H s o process info

/-- The search with a callback succeeds when `Ratpoints.findPoints` does: the refusals of
`Ratpoints.findPointsWith` do not depend on the callback
(`Ratpoints.findPointsWith_eq_error_iff`). -/
theorem exists_findPointsWith_eq_ok_of_findPoints_eq_ok {σ : Type} {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} (process : ℤ → ℤ → ℤ → σ → Answer σ) (info : σ)
    {L : List (ℤ × ℤ × ℤ)} (hL : findPoints c H s o = .ok L) :
    ∃ r, findPointsWith c H s o process info = .ok r := by
  rcases h : findPointsWith c H s o process info with _ | r
  · rw [findPoints, findPointsWith_eq_error_iff.mp h] at hL
    simp [Except.map] at hL
  · exact ⟨r, rfl⟩

/-! ### The output of `Ratpoints.findPoints` -/

-- The list of `Ratpoints.findPoints` for the outcome of a successful search with the appending
-- callback: none when the Sturm step returns before the search, else the list of the search.
private theorem findPoints_eq_ok_of_findPointsWith {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options}
    {out : Outcome (Array (ℤ × ℤ × ℤ))} (h : findPointsWith c H s o appendPoint #[] = .ok out) :
    findPoints c H s o = .ok out.info.toList := by
  simp [findPoints, h, Except.map]

-- After the refusals, the list of `Ratpoints.findPoints` for every choice of the options of the
-- output, by the result `r` of the Sturm step: none when it returns before the search, else the
-- list of the search with the appending callback.
private theorem findPoints_eq_ok_elim {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options}
    {c' : List ℤ} {rev : Bool} {dom : List (Double × Double)} (h1 : c.length ≤ maxDegree + 1)
    (h2 : 2 ≤ c.length) (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) (hl : c.length / 2 ≤ (degree c + 1) / 2)
    (hr : Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev))
    (hsi : Id.run (searchIntervals H o.domain) = some dom)
    {r : Option (List (Double × Double) × Bool)}
    (hst : Id.run (sturmRegion c' (degree c') (o.normalize H).sturm dom) = .ok r)
    (noCheck noY : Bool) :
    findPoints c H s { o with noCheck, noY } = .ok (r.elim [] fun x ↦
      (Id.run (searchPoints appendPoint c' (degree c') H s.normalize (decide (s.numPrimes < 0))
        ⟨rev, noCheck, noY⟩ (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat x.1 x.2
          (fun _ s ↦ s) ⟨#[], 0, false⟩)).info.toList) := by
  rcases r with _ | ⟨dom', empty⟩
  · exact findPoints_eq_ok_of_findPointsWith (out := ⟨#[], 0, rev, false, false, [], 0, 0, 0⟩)
      (findPointsWith_eq_ok_iff.mpr ⟨c', _, rev, dom, h1, h2, hH, hH63, hl, hr, hsi,
        .inl ⟨hst, rfl⟩⟩)
  · exact findPoints_eq_ok_of_findPointsWith (findPointsWith_eq_ok_iff.mpr
      ⟨c', _, rev, dom, h1, h2, hH, hH63, hl, hr, hsi, .inr ⟨dom', empty, hst, rfl⟩⟩)

-- The result of the Sturm step of a successful search, with the search intervals on which the
-- search runs, which are well formed.
private theorem exists_run_sturmRegion_eq_ok {c : List ℤ} {d H : ℕ} {o : Options}
    {dom : List (Double × Double)} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63)
    (hsi : Id.run (searchIntervals H o.domain) = some dom) {p : Prop}
    {q : List (Double × Double) → Bool → Prop}
    (hst : Id.run (sturmRegion c d (o.normalize H).sturm dom) = .ok none ∧ p ∨
      ∃ dom' empty, Id.run (sturmRegion c d (o.normalize H).sturm dom) =
        .ok (some (dom', empty)) ∧ q dom' empty) :
    ∃ r, Id.run (sturmRegion c d (o.normalize H).sturm dom) = .ok r ∧ ∃ dom₀ empty₀,
      IntervalsWF (domainBits dom₀) ∧ ∀ x ∈ r, x = (dom₀, empty₀) := by
  have hwf := wf_of_run_searchIntervals_eq_some hH hH63 hsi
  rcases hst with ⟨hst, -⟩ | ⟨dom', empty, hst, -⟩
  exacts [⟨_, hst, dom, false, hwf, nofun⟩,
    ⟨_, hst, dom', empty, (run_sturmRegion_subset (o.sturm_normalize_le H) hwf hst).1,
      fun _ h ↦ (Option.some.inj h).symm⟩]

-- After the refusals, the list of `Ratpoints.findPoints` for every choice of the options of the
-- output is that of `Ratpoints.searchList` on the search region, for a test `S` for which the
-- search on the intervals on which it runs gives the list of `Ratpoints.searchList`.
private theorem findPoints_eq_ok_searchList {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options}
    {c' : List ℤ} {rev : Bool} {dom : List (Double × Double)} (h1 : c.length ≤ maxDegree + 1)
    (h2 : 2 ≤ c.length) (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) (hl : c.length / 2 ≤ (degree c + 1) / 2)
    (hr : Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev))
    (hsi : Id.run (searchIntervals H o.domain) = some dom)
    {r : Option (List (Double × Double) × Bool)}
    (hst : Id.run (sturmRegion c' (degree c') (o.normalize H).sturm dom) = .ok r)
    {dom₀ : List (Double × Double)} {empty₀ : Bool} (hr₀ : ∀ x ∈ r, x = (dom₀, empty₀))
    {S : ℕ → ℤ → Bool} (hS : ∀ fl : CheckFlags, (Id.run (searchPoints appendPoint c' (degree c')
      H s.normalize (decide (s.numPrimes < 0)) fl (o.normalize H).bLow.toNat
        (o.normalize H).bHigh.toNat dom₀ empty₀ (fun _ s ↦ s) ⟨#[], 0, false⟩)).info.toList =
        searchList c' H (o.normalize H).bLow.toNat
          (o.normalize H).bHigh.toNat (if empty₀ then [] else domainValues dom₀) S fl)
    (noCheck noY : Bool) :
    findPoints c H s { o with noCheck, noY } =
      .ok ((searchRegion c' (degree c') H o).elim [] fun D ↦ searchList c' H
        (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat D S ⟨rev, noCheck, noY⟩) := by
  rw [findPoints_eq_ok_elim h1 h2 hH hH63 hl hr hsi hst,
    searchRegion_eq_of_run_sturmRegion_eq hsi hst]
  rcases r with _ | x
  · rfl
  · obtain rfl := hr₀ x rfl
    exact congr(Except.ok $(hS _))

/-- For every value of the options of the sieve, the list that `Ratpoints.findPoints` returns is
that of the points that the search of the polynomial `c'` that the reversal check of the normalized
options hands on delivers (`Ratpoints.searchList`), with its flag of the reversal and the options of
the output, the normalized range of the denominators and the search region after the Sturm step
(`Ratpoints.searchRegion`), none at all when the Sturm step returns before the search, for a sound
test of the sieve (`Ratpoints.IsSoundTest`) that does not depend on the options of the output: with
the other options unchanged, `Ratpoints.findPoints` returns the list of the search with this test
for every choice of them (`Ratpoints.exists_isSoundTest_run_searchPoints`). The polynomial searched
has a positive degree, since the refusals leave a degree `d ≥ 1`
(`Ratpoints.Setup.one_le_of_reversal_eq_ok`); the search intervals of the caller are well formed,
and the Sturm step does not refuse. -/
theorem exists_searchList_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (h : findPoints c H s o = .ok L) :
    ∃ c' rev S, Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev) ∧
      0 < degree c' ∧ 1 ≤ H ∧ H < 2 ^ 63 ∧ IntervalsWF (domainBits o.domain) ∧
      ¬(0 ≤ o.sturm ∧ Id.run (Sturm.chain c' (degree c')) = none) ∧
      IsSoundTest c' H (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat S ∧
      L = (searchRegion c' (degree c') H o).elim [] (fun D ↦ searchList c' H
        (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat D S ⟨rev, o.noCheck, o.noY⟩) ∧
      ∀ noCheck noY : Bool, findPoints c H s { o with noCheck, noY } =
        .ok ((searchRegion c' (degree c') H o).elim [] fun D ↦ searchList c' H
          (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat D S ⟨rev, noCheck, noY⟩) := by
  obtain ⟨out, hout, rfl⟩ : ∃ out, findPointsWith c H s o appendPoint #[] = .ok out ∧
      L = out.info.toList := by
    rcases h' : findPointsWith c H s o appendPoint #[] <;> simp_all [findPoints, Except.map]
  obtain ⟨c', d', rev, dom, h1, h2, hH, hH63, hl, hr, hsi, hst⟩ := findPointsWith_eq_ok_iff.mp hout
  obtain rfl := Setup.degree_eq_of_reversal_eq_ok rfl hr
  obtain ⟨r, hst, dom₀, empty₀, hwf, hr₀⟩ := exists_run_sturmRegion_eq_ok hH hH63 hsi hst
  obtain ⟨S, hS, hS'⟩ := exists_isSoundTest_run_searchPoints_appendPoint (c := c') s
    (decide (s.numPrimes < 0)) hH hH63
    (o.one_le_toNat_bLow_normalize H) (o.toNat_bHigh_normalize_le H) hwf empty₀
  have key := findPoints_eq_ok_searchList (s := s) h1 h2 hH hH63 hl hr hsi hst hr₀ hS'
  exact ⟨c', rev, S, hr, Setup.one_le_of_reversal_eq_ok hr (by lia), hH, hH63,
    intervalsWF_of_run_searchIntervals_eq_some hsi,
    not_nonneg_and_chain_eq_none_of_run_sturmRegion_eq_ok hst, hS,
    Except.ok.inj ((findPoints_eq_ok_of_findPointsWith hout).symm.trans (key o.noCheck o.noY)),
    key⟩

/-- Without `RATPOINTS_NO_CHECK`, for every value of the options of the sieve, the list that
`Ratpoints.findPoints` returns is that of the brute-force reference of the polynomial `c'` that the
reversal check of the normalized options hands on, over the candidate `(1, 0)` and the denominators
of its search (`Ratpoints.searchDens`) with the numerators `a` with `a / b` in the search region
after the Sturm step (`Ratpoints.searchRegion`), in this order, mapped back by
`Ratpoints.Sieve.swapPoint` after a reversal, without the points with `y < 0` under `RATPOINTS_NO_Y`
(`Ratpoints.searchList_of_noCheck_eq_false`); none when the Sturm step returns before the search. -/
theorem exists_eq_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (h : findPoints c H s o = .ok L)
    (hc : o.noCheck = false) :
    ∃ c' rev, Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev) ∧
      1 ≤ H ∧ H < 2 ^ 63 ∧ IntervalsWF (domainBits o.domain) ∧
      ¬(0 ≤ o.sturm ∧ Id.run (Sturm.chain c' (degree c')) = none) ∧
      L = (searchRegion c' (degree c') H o).elim [] fun D ↦
        ((pointsOfDen c' (degree c') 0 [1] ++
          (searchDens c' (degree c') (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat).flatMap
            fun b : ℕ ↦ pointsOfDen c' (degree c') b
              ((numerators H).filter fun a : ℤ ↦ decide (InIntervals D (a / b)))).map
          (if rev then swapPoint else id)).filter fun p ↦ !o.noY || 0 ≤ p.2.1 := by
  obtain ⟨c', rev, S, hr, hd, hH, hH63, hwf, hst, hS, rfl, -⟩ :=
    exists_searchList_of_findPoints_eq_ok h
  refine ⟨c', rev, hr, hH, hH63, hwf, hst, ?_⟩
  rcases searchRegion c' (degree c') H o with _ | D
  · rfl
  · exact searchList_of_noCheck_eq_false hS hd D hc

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
    exact inRegion_of_isFullBox (by simpa [IsFullBox] using hf) (by simp [swapPoint])
      (by simpa [swapPoint] using hH)

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
    refine iff_of_true (inRegion_of_isFullBox (by simpa [IsFullBox] using hb rfl) ?_ ?_)
      ⟨by lia, .inl hd⟩ <;>
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

/-! ### Assuming Sturm's theorem -/

-- `Option.elim` with `[]` moved inside a filter, a map, an append and a `List.flatMap`.
private theorem elim_nil_filter_map_append_flatMap {α β γ δ : Type*} (r : Option α) (A : List β)
    (l : List γ) (G : α → γ → List β) (s : β → δ) (q : δ → Bool) :
    (r.elim [] fun D ↦ ((A ++ l.flatMap (G D)).map s).filter q) =
      (((r.elim [] fun _ ↦ A) ++ l.flatMap fun b ↦ r.elim [] fun D ↦ G D b).map s).filter q := by
  cases r <;> simp

/-- When the Sturm step returns before the search, the polynomial searched has no points at
infinity: it does so only for even degree and a leading coefficient that is not a square
(`Ratpoints.searchRegion_eq_none`). -/
theorem elim_searchRegion_pointsOfDen_zero {c : List ℤ} {d H : ℕ} {o : Options}
    (hdom : IntervalsWF (domainBits o.domain))
    (hc : ¬(0 ≤ o.sturm ∧ Id.run (Sturm.chain c d) = none)) :
    (searchRegion c d H o).elim [] (fun _ ↦ pointsOfDen c d 0 [1]) = pointsOfDen c d 0 [1] := by
  rcases h : searchRegion c d H o with _ | D
  · obtain ⟨hd, hs⟩ := searchRegion_eq_none hdom hc h
    refine (List.eq_nil_iff_forall_not_mem.mpr fun p hp ↦ ?_).symm
    rw [pointsOfDen_zero_singleton_one, mem_pointsAbove_iff] at hp
    have hy : p.2.1 ^ 2 = c.getD d 0 := by simpa [hd] using hp.2.2
    exact (Setup.isSquare_eq_false_iff _).mp hs ⟨p.2.1, by rw [← hy, sq]⟩
  · rfl

/-- Assuming Sturm's theorem when the step is on, the points of the denominator `b ≥ 1` of the
polynomial `c` of degree `0 < d < 2 ^ 57` with the numerators `a` with `a / b` in the search region
after the Sturm step, none when it returns before the search, are those with `a / b` in the
caller's search intervals, when there are some (`Ratpoints.searchRegion_covers`,
`Ratpoints.searchRegion_subset`): on a point, `F(a, b) = y ^ 2 ≥ 0`. -/
theorem elim_searchRegion_pointsOfDen_filter {c : List ℤ} {d H : ℕ} {o : Options}
    (hS : 0 ≤ o.sturm → SturmTheorem) (hdom : IntervalsWF (domainBits o.domain))
    (hd : d = degree c) (hd0 : 0 < d) (hd57 : d < 2 ^ 57) (hH : 1 ≤ H) (hH63 : H < 2 ^ 63)
    (hc : ¬(0 ≤ o.sturm ∧ Id.run (Sturm.chain c d) = none)) {b : ℕ} (hb : 0 < b) :
    (searchRegion c d H o).elim [] (fun D ↦ pointsOfDen c d b ((numerators H).filter
      fun a : ℤ ↦ decide (InIntervals D (a / b)))) =
      pointsOfDen c d b ((numerators H).filter fun a : ℤ ↦
        decide (o.domain = [] ∨ InIntervals (domainValues o.domain) (a / b))) := by
  have key {p : ℤ × ℤ × ℤ} (hp : p ∈ pointsOfDen c d b (numerators H))
      (hx : o.domain = [] ∨ InIntervals (domainValues o.domain) (p.1 / b)) :
      ∃ D, searchRegion c d H o = some D ∧ InIntervals D (p.1 / b) := by
    obtain ⟨hx', -, -, hy⟩ := mem_pointsOfDen_iff.mp hp
    subst hd
    rw [← BruteForce.degree_eq, horner_scaledCoeffs_mul] at hy
    exact searchRegion_covers hS hdom rfl hd0 hd57 hH hH63 hc hb
      (by lia [Int.abs_eq_natAbs p.1, mem_numerators_iff.mp hx']) (hy ▸ sq_nonneg _) hx
  rw [pointsOfDen_filter]
  rcases h : searchRegion c d H o with _ | D
  · exact (List.filter_eq_nil_iff.mpr fun p hp hx ↦ by
      simpa [h] using key hp (of_decide_eq_true hx)).symm
  · rw [Option.elim_some, pointsOfDen_filter]
    refine List.filter_congr fun p hp ↦ decide_eq_decide.mpr
      ⟨fun hx ↦ searchRegion_subset hdom h _ hx, fun hx ↦ ?_⟩
    obtain ⟨D', hD', hin⟩ := key hp hx
    rw [h, Option.some.injEq] at hD'
    exact hD' ▸ hin

-- The coefficient list of a successful search has at most `maxDegree + 1` entries and a positive
-- degree.
private theorem length_le_and_one_le_degree_of_findPoints_eq_ok {c : List ℤ} {H : ℕ}
    {s : SieveOptions}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (h : findPoints c H s o = .ok L) :
    c.length ≤ maxDegree + 1 ∧ 1 ≤ degree c := by
  obtain ⟨out, hout⟩ : ∃ out, findPointsWith c H s o appendPoint #[] = .ok out := by
    rcases h' : findPointsWith c H s o appendPoint #[] <;> simp_all [findPoints, Except.map]
  obtain ⟨-, -, -, -, h1, h2, -, -, hl, -⟩ := findPointsWith_eq_ok_iff.mp hout
  exact ⟨h1, by lia⟩

/-- Assuming Sturm's theorem when the Sturm step is on, without `RATPOINTS_NO_CHECK`, for every
value of the options of the sieve, the list that `Ratpoints.findPoints` returns is the brute-force
reference of the polynomial `c'` that the reversal check of the normalized options hands
on, over the candidate `(1, 0)` and the denominators of its search with the numerators `a` with
`a / b` in the caller's search intervals, when there are some, in this order, mapped back after a
reversal, without the points with `y < 0` under `RATPOINTS_NO_Y`: the search region after the Sturm
step holds exactly these numerators of the points (`Ratpoints.exists_eq_of_findPoints_eq_ok`,
`Ratpoints.elim_searchRegion_pointsOfDen_zero`,
`Ratpoints.elim_searchRegion_pointsOfDen_filter`). -/
theorem exists_eq_filter_inIntervals_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hS : 0 ≤ o.sturm → SturmTheorem)
    (h : findPoints c H s o = .ok L) (hc : o.noCheck = false) :
    ∃ c' rev, Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev) ∧
      1 ≤ H ∧ L = ((pointsOfDen c' (degree c') 0 [1] ++
        (searchDens c' (degree c') (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat).flatMap
          fun b : ℕ ↦ pointsOfDen c' (degree c') b ((numerators H).filter fun a : ℤ ↦
            decide (o.domain = [] ∨ InIntervals (domainValues o.domain) (a / b)))).map
        (if rev then swapPoint else id)).filter fun p ↦ !o.noY || 0 ≤ p.2.1 := by
  obtain ⟨h1, hd⟩ := length_le_and_one_le_degree_of_findPoints_eq_ok h
  obtain ⟨c', rev, hr, hH, hH63, hwf, hst, rfl⟩ := exists_eq_of_findPoints_eq_ok h hc
  refine ⟨c', rev, hr, hH, ?_⟩
  rw [elim_nil_filter_map_append_flatMap, elim_searchRegion_pointsOfDen_zero hwf hst]
  refine congr(List.filter _ (List.map _ (_ ++ $(List.flatMap_congr fun b hb ↦ ?_))))
  exact elim_searchRegion_pointsOfDen_filter hS hwf rfl (Setup.one_le_of_reversal_eq_ok hr hd)
    (by lia [Setup.degree_le_of_reversal_eq_ok hr, degree_le_length_sub_one c,
      maxDegree_lt_two_pow_57]) hH hH63 hst
    (by lia [o.one_le_toNat_bLow_normalize H,
      le_and_le_of_mem_searchDens (o.one_le_toNat_bLow_normalize H) hb])

/-- Assuming Sturm's theorem when the Sturm step is on, without `RATPOINTS_NO_CHECK`, for every
value of the options of the sieve, the list that `Ratpoints.findPoints` returns is the brute-force
reference of the polynomial `c'` that the reversal check of the normalized options hands
on, over the candidate `(1, 0)` and the denominators of its search from `1` to the normalized
largest denominator, in this order, mapped back after a reversal, filtered by the search region of
the options (`Ratpoints.InRegion`) and under `RATPOINTS_NO_Y` by `y ≥ 0`
(`Ratpoints.map_append_flatMap_filter_eq_filter_inRegion`). -/
theorem exists_eq_filter_inRegion_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hS : 0 ≤ o.sturm → SturmTheorem)
    (h : findPoints c H s o = .ok L) (hc : o.noCheck = false) :
    ∃ c' rev, Setup.reversal (o.normalize H).reverse c (degree c) = .ok (c', degree c', rev) ∧
      1 ≤ H ∧ L = ((pointsOfDen c' (degree c') 0 [1] ++
        (searchDens c' (degree c') 1 (o.normalize H).bHigh.toNat).flatMap fun b : ℕ ↦
          pointsOfDen c' (degree c') b (numerators H)).map (if rev then swapPoint else id)).filter
        fun p ↦ (!o.noY || 0 ≤ p.2.1) && InRegion (domainValues o.domain) o.bLow o.bHigh p := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_filter_inIntervals_of_findPoints_eq_ok hS h hc
  have hb : rev = true → IsFullBox o.domain o.bLow o.bHigh H := by
    rintro rfl
    exact isFullBox_of_reversal_normalize_eq_ok hr
  refine ⟨c', rev, hr, hH, ?_⟩
  rw [searchDens_eq_filter c' _ (o.one_le_toNat_bLow_normalize H),
    map_append_flatMap_filter_eq_filter_inRegion hb hH
      fun b hb' ↦ le_and_le_of_mem_searchDens le_rfl hb', List.filter_filter]

/-- Assuming Sturm's theorem when the Sturm step is on, without the options of the output, when the
options forbid the reversal and the denominators of the search are `bLow, …, bHigh` for the
normalized range (`Ratpoints.searchDens_eq_range'`: even degree, `|c_d| = 1`, or the divisor set-up
fails), the list that `Ratpoints.findPoints` returns is the brute-force reference in the search
region of the options. -/
theorem eq_filter_bruteForce_of_findPoints_eq_ok_of_reverse_eq_false {c : List ℤ} {H : ℕ}
    {s : SieveOptions} {o : Options} {L : List (ℤ × ℤ × ℤ)} (hS : 0 ≤ o.sturm → SturmTheorem)
    (h : findPoints c H s o = .ok L) (hc : o.noCheck = false) (hy : o.noY = false)
    (ho : o.reverse = false)
    (hs : searchDens c (degree c) (o.normalize H).bLow.toNat (o.normalize H).bHigh.toNat =
      List.range' (o.normalize H).bLow.toNat
        ((o.normalize H).bHigh.toNat + 1 - (o.normalize H).bLow.toNat)) :
    L = (bruteForce c H).filter
      (InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow
        o.bHigh) := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_filter_inIntervals_of_findPoints_eq_ok hS h hc
  rw [o.reverse_normalize H, ho, Bool.false_and, Setup.reversal_false] at hr
  obtain ⟨rfl, -, rfl⟩ := by simpa using hr.symm
  have hB := o.toNat_bHigh_normalize_le H
  rw [hs, List.range'_eq_filter_range' (o.one_le_toNat_bLow_normalize H),
    map_append_flatMap_filter_eq_filter_inRegion (rev := false) nofun hH fun b hb ↦ by
      lia [List.mem_range'_1.mp hb],
    ← Nat.add_sub_cancel (n := (o.normalize H).bHigh.toNat) (m := 1),
    ← filter_bruteForce_eq_append c' hH le_rfl hB]
  simpa [hy] using filter_filter_bruteForce_eq (o := o) _ c' H fun _ ↦ true

/-- Assuming Sturm's theorem when the Sturm step is on, without `RATPOINTS_NO_CHECK`, for every
value of the options of the sieve, the list that `Ratpoints.findPoints` returns is a permutation of
the brute-force reference in the search region of the options (`Ratpoints.InRegion`),
without the points with `y < 0` under `RATPOINTS_NO_Y`: the search region holds the points at
infinity and those with a denominator up to the largest of the search
(`Ratpoints.eq_zero_or_le_toNat_bHigh_normalize_of_inRegion`), whose points the search gives
(`Ratpoints.perm_map_append_flatMap_searchDens`). -/
theorem perm_filter_bruteForce_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hS : 0 ≤ o.sturm → SturmTheorem)
    (h : findPoints c H s o = .ok L) (hc : o.noCheck = false) :
    L.Perm ((bruteForce c H).filter fun p ↦ (!o.noY || 0 ≤ p.2.1) &&
      InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow o.bHigh
        p) := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_filter_inRegion_of_findPoints_eq_ok hS h hc
  exact ((perm_map_append_flatMap_searchDens hr hH).filter _).trans
    (.of_eq (filter_filter_bruteForce_eq _ c H _))

/-- Assuming Sturm's theorem when the Sturm step is on, without `RATPOINTS_NO_CHECK`, for every
value of the options of the sieve, the list that `Ratpoints.findPoints` returns is
`Ratpoints.orderedPoints` for the switch of the reversal of the normalized options and the
largest denominator of the search (`Ratpoints.denominatorBound`), the points in the order of the
specification, those in the search region of the options (`Ratpoints.InRegion`), without those with
`y < 0` under `RATPOINTS_NO_Y`; comparator certifies this (`comparator/Challenge.lean`). -/
theorem eq_orderedPoints_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hS : 0 ≤ o.sturm → SturmTheorem)
    (h : findPoints c H s o = .ok L) (hc : o.noCheck = false) :
    L = (orderedPoints maxDivisors (o.reverse && IsFullBox o.domain o.bLow o.bHigh H) c H
        (denominatorBound o.bHigh H)).filter fun p ↦ (!o.noY || 0 ≤ p.2.1) &&
      InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow o.bHigh
        p := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_filter_inRegion_of_findPoints_eq_ok hS h hc
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

/-- Assuming Sturm's theorem when the Sturm step is on, without `RATPOINTS_NO_CHECK`, for every
value of the options of the sieve and the other options, a triple lies in the list that
`Ratpoints.findPoints` returns exactly when it is a normalized point of height at most `H`
in the search region of the options (`Ratpoints.InRegion`), with `y ≥ 0` under `RATPOINTS_NO_Y`;
comparator certifies this (`comparator/Challenge.lean`). -/
theorem mem_iff_isPoint_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hS : 0 ≤ o.sturm → SturmTheorem)
    (h : findPoints c H s o = .ok L) (hc : o.noCheck = false) {p : ℤ × ℤ × ℤ} :
    p ∈ L ↔ IsPoint c H p ∧ (o.noY = true → 0 ≤ p.2.1) ∧
      InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow o.bHigh
        p := by
  rw [(perm_filter_bruteForce_of_findPoints_eq_ok hS h hc).mem_iff, List.mem_filter,
    mem_bruteForce_iff]
  cases o.noY <;> simp

/-- For every option, the list that `Ratpoints.findPoints` returns has
no duplicates: without `RATPOINTS_NO_CHECK` it is a sublist of a permutation of the brute-force
reference, filtered under `RATPOINTS_NO_Y` and by the search region, and under
`RATPOINTS_NO_CHECK` the survivors are distinct (`Ratpoints.nodup_searchList_of_noCheck`);
comparator certifies this (`comparator/Challenge.lean`). -/
theorem nodup_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (h : findPoints c H s o = .ok L) :
    L.Nodup := by
  obtain ⟨c', rev, S, hr, hd, hH, -, -, -, hS, rfl, -⟩ := exists_searchList_of_findPoints_eq_ok h
  have hbL := o.one_le_toNat_bLow_normalize H
  have hbH := o.one_le_toNat_bHigh_normalize (H := H) hH
  rcases searchRegion c' (degree c') H o with _ | D
  · exact List.nodup_nil
  rw [Option.elim_some]
  cases hc : o.noCheck
  · rw [searchList_of_noCheck_eq_false hS hd D rfl]
    refine .filter _ (.sublist (.map _ (.append_left (.flatMap_right _
      (g := fun b : ℕ ↦ pointsOfDen c' (degree c') b (numerators H)) fun b _ ↦ ?_) _)) ?_)
    · rw [pointsOfDen_filter]
      exact List.filter_sublist
    · refine ((perm_filter_bruteForce_append_flatMap_searchDens c' hbL hbH
        (o.toNat_bHigh_normalize_le H)).map _).nodup_iff.mpr (.sublist (.map _ List.filter_sublist)
          (nodup_map_bruteForce_of_reversal_eq_ok hr H))
  · exact nodup_searchList_of_noCheck hH hbL (o.toNat_bHigh_normalize_le H) D S rfl

/-- Assuming Sturm's theorem when the Sturm step is on, without the options of the output, the set
of the elements of the list that `Ratpoints.findPoints` returns is the set of the points in the
search region of the options. -/
theorem toFinset_eq_filter_points_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hS : 0 ≤ o.sturm → SturmTheorem)
    (h : findPoints c H s o = .ok L) (hc : o.noCheck = false) (hy : o.noY = false) :
    L.toFinset = (points c H).filter
      (InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow
        o.bHigh) := by
  rw [List.toFinset_eq_of_perm _ _ (perm_filter_bruteForce_of_findPoints_eq_ok hS h hc),
    List.toFinset_filter, toFinset_bruteForce]
  simp [hy]

/-! ### `RATPOINTS_NO_CHECK` -/

/-- Under `RATPOINTS_NO_CHECK`, for every value of the options of the sieve, every triple of the
list that `Ratpoints.findPoints` returns is `(x, 0, z)` for the pair `(x, z)` of a
normalized point of height at most `H` in the search region of the options, whether it is a point or
not: `x` prime to `z`, `z > 0` or `(x, z) = (1, 0)`, `|x| ≤ H`, `z ≤ H` and `(x, 0, z)` in the
search region (`Ratpoints.exists_eq_of_mem_searchList_of_noCheck`,
`Ratpoints.mem_region_of_mem_searchList`, `Ratpoints.searchRegion_subset`); comparator certifies
this (`comparator/Challenge.lean`). -/
theorem exists_eq_of_mem_of_findPoints_eq_ok_of_noCheck {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (h : findPoints c H s o = .ok L)
    (hc : o.noCheck = true) {q : ℤ × ℤ × ℤ} (hq : q ∈ L) :
    ∃ x z : ℤ, q = (x, 0, z) ∧ Int.gcd x z = 1 ∧ (0 < z ∨ z = 0 ∧ x = 1) ∧ |x| ≤ H ∧ z ≤ H ∧
      InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow o.bHigh
        q := by
  obtain ⟨c', rev, S, hr, -, hH, -, hwf, -, -, rfl, -⟩ := exists_searchList_of_findPoints_eq_ok h
  rcases hreg : searchRegion c' (degree c') H o with _ | D
  · simp [hreg] at hq
  rw [hreg, Option.elim_some] at hq
  have hbL := o.one_le_toNat_bLow_normalize H
  obtain ⟨x, z, rfl, hn⟩ := exists_eq_of_mem_searchList_of_noCheck hc hH hbL
    (o.toNat_bHigh_normalize_le H) hq
  refine ⟨x, z, rfl, hn.1, hn.2.1, hn.2.2.1, hn.2.2.2, ?_⟩
  cases rev
  · rcases mem_region_of_mem_searchList rfl hbL hq with h0 | ⟨h1, h2, h3⟩
    · exact .inl h0
    · refine .inr ⟨(o.bLow_normalize_le_iff H (by lia)).mp h1,
        o.lt_one_or_le_bHigh_of_le h2 hn.2.2.2, ?_⟩
      exact (searchRegion_subset hwf hreg _ h3).imp List.map_eq_nil_iff.mpr id
  · have hb := isFullBox_of_reversal_normalize_eq_ok hr
    exact inRegion_of_isFullBox (by simpa [IsFullBox] using hb)
      (by rcases hn.2.1 with h0 | h0 <;> lia) hn.2.2.2

/-- Under `RATPOINTS_NO_CHECK`, for every value of the options of the sieve, the list `L'` that
`Ratpoints.findPoints` returns for the same input with `RATPOINTS_NO_CHECK` cleared and
`RATPOINTS_NO_Y` set, with `y` replaced by `0`, is a sublist of the list `L` that it returns: both
searches run with the same test of the sieve and the same search region, so that the points come in
the same order among the survivors (`Ratpoints.map_searchList_sublist`); comparator certifies this
(`comparator/Challenge.lean`). -/
theorem map_sublist_of_findPoints_eq_ok_of_noCheck {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {L L' : List (ℤ × ℤ × ℤ)} (h : findPoints c H s o = .ok L)
    (hc : o.noCheck = true)
    (h' : findPoints c H s { o with noCheck := false, noY := true } = .ok L') :
    (L'.map fun q ↦ (q.1, 0, q.2.2)).Sublist L := by
  obtain ⟨c', rev, S, -, -, -, -, -, -, -, rfl, hall⟩ := exists_searchList_of_findPoints_eq_ok h
  obtain rfl := Except.ok.inj (h'.symm.trans (hall false true))
  rw [hc]
  rcases searchRegion c' (degree c') H o with _ | D
  · exact List.Sublist.slnil
  · exact map_searchList_sublist c' H _ _ D S rev o.noY

/-- Assuming Sturm's theorem when the Sturm step is on, under `RATPOINTS_NO_CHECK`, for well-formed
parameters, the list that `Ratpoints.findPoints` returns has the triple `(x, 0, z)` of every
normalized point `(x, y, z)` of height at most `H` in the search region of the options: the point
`(x, |y|, z)` is in the list of the search with `RATPOINTS_NO_CHECK` cleared and `RATPOINTS_NO_Y`
set (`Ratpoints.map_sublist_of_findPoints_eq_ok_of_noCheck`); comparator certifies this
(`comparator/Challenge.lean`). -/
theorem mem_of_isPoint_of_findPoints_eq_ok_of_noCheck {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hS : 0 ≤ o.sturm → SturmTheorem)
    (h : findPoints c H s o = .ok L) (hc : o.noCheck = true) {p : ℤ × ℤ × ℤ}
    (hp : IsPoint c H p)
    (hr : InRegion (o.domain.map fun i ↦ (doubleValue i.1.bits, doubleValue i.2.bits)) o.bLow
      o.bHigh p) :
    (p.1, 0, p.2.2) ∈ L := by
  obtain ⟨c', rev, S, -, -, -, -, -, -, -, -, hall⟩ := exists_searchList_of_findPoints_eq_ok h
  have hp' := (mem_iff_isPoint_of_findPoints_eq_ok (o := { o with noCheck := false, noY := true })
    hS (hall false true) rfl (p := (p.1, |p.2.1|, p.2.2))).mpr
      ⟨by simpa [IsPoint, sq_abs] using hp, fun _ ↦ abs_nonneg _, hr⟩
  exact (map_sublist_of_findPoints_eq_ok_of_noCheck h hc (hall false true)).subset
    (List.mem_map.mpr ⟨_, hp', rfl⟩)

/-! ### The refusals -/

/-- With the Sturm step on (`0 ≤ o.sturm`, as in a run of the program without options),
`Ratpoints.findPoints` refuses exactly the inputs with fewer than two or more than
`Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or more, which is
not a `long` (`Ratpoints.fitsLong_natCast`), the binary forms `Ratpoints.binaryFormPoly c` that are
not squarefree, and search intervals that are not well formed (`Ratpoints.IntervalsWF`), for all
parameters, whether the reversal is allowed or not; comparator certifies this
(`comparator/Challenge.lean`). -/
theorem exists_findPoints_eq_error_iff_of_sturm_nonneg {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} (hs : 0 ≤ o.sturm) :
    (∃ e, findPoints c H s o = .error e) ↔
      c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        ¬ Squarefree (binaryFormPoly c) ∨
        ¬ IntervalsWF (o.domain.map fun i ↦ (i.1.bits, i.2.bits)) := by
  rw [exists_findPoints_eq_error_iff, findPointsWith_eq, BruteForce.degree_eq]
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
  have := run_sturmRegion_eq_error_iff c' d' (o.normalize H).sturm ‹_›
  split <;> rename_i hst <;> simp_all [o.sturm_normalize_nonneg_iff H]

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
coefficients, that is `d + 2 ≤ 2 ⌈n / 2⌉` for the degree `d`, and those of even degree with
`c₀ = c₁ = 0` when the reversal is allowed and the search region is the whole box
(`Ratpoints.IsFullBox`), all of them forms that are not squarefree, but not all such forms; and the
search intervals that are not well formed (`Ratpoints.IntervalsWF`); comparator certifies this
(`comparator/Challenge.lean`), so that a `Ratpoints.findPoints` that refused every input under `-s`
would not pass. -/
theorem exists_findPoints_eq_error_iff_of_sturm_neg {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} (hs : o.sturm < 0) :
    (∃ e, findPoints c H s o = .error e) ↔
      c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        degree c + 2 ≤ 2 * (c.length / 2) ∨
        o.reverse = true ∧ IsFullBox o.domain o.bLow o.bHigh H ∧ degree c % 2 = 0 ∧
          c.getD 0 0 = 0 ∧ c.getD 1 0 = 0 ∨
        ¬ IntervalsWF (o.domain.map fun i ↦ (i.1.bits, i.2.bits)) := by
  rw [exists_findPoints_eq_error_iff, findPointsWith_eq, BruteForce.degree_eq]
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
  rw [run_sturmRegion_of_neg _ _ ((o.sturm_normalize_neg_iff H).mpr hs)]
  simp only [reduceCtorEq, exists_false, false_iff, not_or, not_and, not_not]
  refine ⟨fun h1 h2 h3 h4 h5 ↦ ?_, intervalsWF_of_run_searchIntervals_eq_some hsi⟩
  obtain ⟨e, he⟩ := exists_reversal_normalize_eq_error_iff.mpr ⟨h1, h2, h3, h4, h5⟩
  simp only [hr, reduceCtorEq] at he

/-! ### The Sturm step changes only the speed -/

-- The search without the Sturm step refuses only inputs that the search with the options `o`
-- refuses: its refusals other than those of `o` are forms that are not squarefree
-- (`Ratpoints.not_squarefree_binaryFormPoly_of_lt`,
-- `Ratpoints.not_squarefree_binaryFormPoly_of_getD_zero`).
private theorem exists_findPoints_eq_error_of_sturm_neg {c : List ℤ} {H : ℕ} {s : SieveOptions}
    {o : Options} (he : ∃ e, findPoints c H s { o with sturm := -1 } = .error e) :
    ∃ e, findPoints c H s o = .error e := by
  have hd := (exists_findPoints_eq_error_iff_of_sturm_neg (o := { o with sturm := -1 })
    (by simp)).mp he
  rcases lt_or_ge o.sturm 0 with hs | hs
  · exact (exists_findPoints_eq_error_iff_of_sturm_neg hs).mpr hd
  · have h1 (h : degree c + 2 ≤ 2 * (c.length / 2)) : ¬ Squarefree (binaryFormPoly c) :=
      not_squarefree_binaryFormPoly_of_lt (by lia)
    have h2 := not_squarefree_binaryFormPoly_of_getD_zero (c := c)
    exact (exists_findPoints_eq_error_iff_of_sturm_nonneg hs).mpr (by tauto)

/-- Assuming Sturm's theorem when the Sturm step is on, without `RATPOINTS_NO_CHECK`, the Sturm step
changes only the speed of the search: the search without it returns the same list. -/
theorem findPoints_sturm_neg_eq_ok {c : List ℤ} {H : ℕ} {s : SieveOptions} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hS : 0 ≤ o.sturm → SturmTheorem)
    (hc : o.noCheck = false) (h : findPoints c H s o = .ok L) :
    findPoints c H s { o with sturm := -1 } = .ok L := by
  rcases h' : findPoints c H s { o with sturm := -1 } with e | L'
  · obtain ⟨e', he'⟩ := exists_findPoints_eq_error_of_sturm_neg ⟨e, h'⟩
    simp [he'] at h
  · rw [eq_orderedPoints_of_findPoints_eq_ok (fun h ↦ absurd h (by simp)) h' hc,
      eq_orderedPoints_of_findPoints_eq_ok hS h hc]

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
