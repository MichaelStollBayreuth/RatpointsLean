/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.FindPoints

import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Delivery
import Ratpoints.Proof.Setup
import Ratpoints.Proof.Tables

/-!
# The output of the search and the refusals

`Ratpoints.findPointsWith` searches the polynomial that the reversal check hands on, unless it
refuses the input (`Ratpoints.findPointsWith_eq_ok_iff`); its refusals and the bits of the flags
that it writes back do not depend on the callback, and for well-formed parameters it gives the data
and the count of the delivery (`Ratpoints.Delivery.deliver`) of the list that
`Ratpoints.findPoints`, its instance with the appending callback, returns: the protocol of the
delivery (`Ratpoints.map_findPointsWith_eq_map_findPoints`). That list is the list of the points
that the search of the polynomial searched delivers for a sound test of the sieve, which does not
depend on the options of the output (`Ratpoints.exists_searchList_of_findPoints_eq_ok`); without
`RATPOINTS_NO_CHECK` it is the brute-force reference of the polynomial searched, over the candidate
`(1, 0)` and the denominators of the search, mapped back after a reversal, without the points with
`y < 0` under `RATPOINTS_NO_Y` (`Ratpoints.exists_eq_of_findPoints_eq_ok`), so that it holds
exactly the points of the specification, those with `y ≥ 0` under `RATPOINTS_NO_Y`, each once.
Under `RATPOINTS_NO_CHECK` it holds triples `(x, 0, z)` of normalized pairs `(x, z)` of height at
most `H`, each once, among them those of all the points, and the list of the search with
`RATPOINTS_NO_CHECK` cleared and `RATPOINTS_NO_Y` set, with `y` replaced by `0`, is a sublist of
it. `Ratpoints.findPoints` refuses exactly the inputs that the program refuses: with the Sturm step
on, those with fewer than two or more than `Ratpoints.maxDegree + 1` coefficients, the height bound
`0` or one of `2 ^ 63` or more, which is not a `long`, and the binary forms `Φ_c` that are not
squarefree; without it, instead of the last, those that the test of the leading zeros and the
reversal check refuse. Comparator certifies the protocol, the membership, the absence of
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
* `Ratpoints.exists_searchList_of_findPoints_eq_ok`: the list of `Ratpoints.findPoints` is that of
  the search with a sound test of the sieve, the same for every choice of the options of the output.
* `Ratpoints.exists_eq_of_findPoints_eq_ok`: without `RATPOINTS_NO_CHECK`, it is the reference of
  the polynomial searched, mapped back after a reversal, filtered under `RATPOINTS_NO_Y`;
  `Ratpoints.eq_bruteForce_of_findPoints_eq_ok_of_reverse_eq_false`: the reference itself without
  the options of the output, when the options forbid the reversal and the denominators of the search
  are `1, …, H`.
* `Ratpoints.perm_bruteForce_of_findPoints_eq_ok`: without the options of the output, the list is a
  permutation of the reference.
* `Ratpoints.mem_iff_isPoint_of_findPoints_eq_ok`: without `RATPOINTS_NO_CHECK`, a triple lies in
  the list exactly when it is a normalized point of height at most `H`, with `y ≥ 0` under
  `RATPOINTS_NO_Y`.
* `Ratpoints.nodup_of_findPoints_eq_ok`: for every option, the list has no duplicates.
* `Ratpoints.toFinset_eq_points_of_findPoints_eq_ok`: without the options of the output, its set of
  elements is `Ratpoints.points`.
* `Ratpoints.exists_eq_of_mem_of_findPoints_eq_ok_of_noCheck`,
  `Ratpoints.mem_of_isPoint_of_findPoints_eq_ok_of_noCheck`,
  `Ratpoints.map_sublist_of_findPoints_eq_ok_of_noCheck`: under `RATPOINTS_NO_CHECK`, the list holds
  triples `(x, 0, z)` of normalized pairs of height at most `H`, among them `(x, 0, z)` for every
  point `(x, y, z)`, and the list of the search with `RATPOINTS_NO_CHECK` cleared and
  `RATPOINTS_NO_Y` set, with `y` replaced by `0`, is a sublist of it.
* `Ratpoints.exists_findPoints_eq_error_iff_of_sturm_nonneg`: with the Sturm step on,
  `Ratpoints.findPoints` refuses exactly the inputs with fewer than two or more than
  `Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or more, and the
  forms that are not squarefree.
* `Ratpoints.exists_findPoints_eq_error_iff_of_sturm_neg`: without it, those with fewer than two or
  more than `Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or
  more, a degree `d` with `d + 2 ≤ 2 ⌈n / 2⌉`, and, when the reversal is allowed, an even degree
  with `c₀ = c₁ = 0`.

## Proof

`Ratpoints.findPoints` and `Ratpoints.findPointsWith` run the search on the polynomial that the
reversal check hands on, with its degree (`Ratpoints.Setup.degree_eq_of_reversal_eq_ok`), which is
positive after the refusals (`Ratpoints.Setup.one_le_of_reversal_eq_ok`), and its flag of the
reversal, with the options of the output as the flags of the check
(`Ratpoints.exists_isSoundTest_run_searchPoints`, `Ratpoints.run_searchPoints_eq_deliver`,
`Ratpoints.searchList_of_noCheck_eq_false`); the binary form of a reversed polynomial is that of `c`
with `x` and `z` exchanged (`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`), so that its
reference, mapped back, is a permutation of that of `c`
(`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`). Under `RATPOINTS_NO_CHECK` the search delivers,
for the same sound test of the sieve, the survivors of the numerators prime to the denominators of
the search (`Ratpoints.exists_eq_of_mem_searchList_of_noCheck`, distinct by
`Ratpoints.nodup_searchList_of_noCheck`), of which the points with `y ≥ 0` that the search delivers
without it are a sublist (`Ratpoints.map_searchList_sublist`). Of the refusals, the heights that are
not `long`s are those of `2 ^ 63` or more (`Ratpoints.fitsLong_natCast`), and the test of the
leading zeros and that of the reversal check stand for `Z ^ 2 ∣ Φ_c` and `X ^ 2 ∣ Φ_c`
(`Ratpoints.not_squarefree_binaryFormPoly_of_lt`,
`Ratpoints.Setup.not_squarefree_binaryFormPoly_of_reversal_eq_error`), and after them the remainder
chain of the polynomial searched is none exactly when `Φ_c` is not squarefree
(`Ratpoints.Sturm.run_chain_eq_none_iff_of_reversal_eq_ok`).
-/
@[expose] public section

namespace Ratpoints

open BruteForce Sieve

/-! ### The search with a callback -/

/-- `Ratpoints.findPointsWith` returns the outcome `out` exactly when it refuses none of its inputs,
in the order of the program, and `out` is the outcome of the search of the polynomial `c'` of degree
`d'` that the reversal check hands on, with the flag of the reversal and the options of the output,
from the data `info`, the count `0` and the flag of the stop clear. -/
theorem findPointsWith_eq_ok_iff {c : List ℤ} {H : ℕ} {P : Params} {o : Options} {σ : Type}
    {process : ℤ → ℤ → ℤ → σ → Answer σ} {info : σ} {out : Outcome σ} :
    findPointsWith c H P o process info = .ok out ↔ ∃ c' d' rev, c.length ≤ maxDegree + 1 ∧
      2 ≤ c.length ∧ 1 ≤ H ∧ H < 2 ^ 63 ∧ c.length / 2 ≤ (degree c + 1) / 2 ∧
      Setup.reversal o.reverse c (degree c) = .ok (c', d', rev) ∧
      ¬(0 ≤ o.sturm ∧ Id.run (Sturm.chain c' d') = none) ∧
      out = Id.run (searchPoints process c' d' H P ⟨rev, o.noCheck, o.noY⟩ ⟨info, 0, false⟩) := by
  rw [findPointsWith, ← BruteForce.degree_eq]
  simp only [fitsLong_natCast, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  split_ifs with h1 h2 h3 h4
  any_goals (simp only [false_iff]; lia)
  split <;> rename_i hr
  · simp [hr]
  rename_i c' d' rev
  split_ifs with h5
  · simp_all
  · simp only [Except.ok.injEq]
    exact ⟨fun h ↦ ⟨c', d', rev, by lia, by lia, by lia, by lia, by lia, hr, h5, h.symm⟩,
      fun ⟨_, _, _, _, _, _, _, _, hr', _, h⟩ ↦ by simp_all⟩

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
first that stops the search (`Ratpoints.run_searchPoints_eq_deliver`). -/
theorem map_findPointsWith_eq_map_findPoints {P : Params} (hP : P.WF) (c : List ℤ) (H : ℕ)
    (o : Options) {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (info : σ) :
    (findPointsWith c H P o process info).map (fun out ↦ (out.info, out.total)) =
      (findPoints c H P o).map (fun L ↦
        let r := Delivery.deliver process ⟨info, 0, false⟩ L
        (r.info, r.total)) := by
  rcases h : findPointsWith c H P o appendPoint #[] with e | out
  · rw [findPoints, h, findPointsWith_eq_error_iff.mpr h]
    rfl
  · obtain ⟨c', d', rev, h1, h2, hH, hH63, hl, hr, hs, rfl⟩ := findPointsWith_eq_ok_iff.mp h
    obtain rfl := Setup.degree_eq_of_reversal_eq_ok rfl hr
    rw [findPoints, h, findPointsWith_eq_ok_iff.mpr ⟨c', _, rev, h1, h2, hH, hH63, hl, hr, hs, rfl⟩]
    exact congr(Except.ok $(run_searchPoints_eq_deliver hP hH hH63 process _ rfl))

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
  split_ifs
  · rfl
  simp only [Except.map, run_searchPoints_flags]

/-! ### The output of `Ratpoints.findPoints` -/

/-- For well-formed parameters, the list that `Ratpoints.findPoints` returns is that of the points
that the search of the polynomial `c'` that the reversal check hands on delivers
(`Ratpoints.searchList`), with its flag of the reversal and the options of the output, for a sound
test of the sieve (`Ratpoints.IsSoundTest`) that does not depend on the options of the output:
with the other options unchanged, `Ratpoints.findPoints` returns the list of the search with this
test for every choice of them (`Ratpoints.exists_isSoundTest_run_searchPoints`). The polynomial
searched has a positive degree, since the refusals leave a degree `d ≥ 1`
(`Ratpoints.Setup.one_le_of_reversal_eq_ok`). -/
theorem exists_searchList_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) :
    ∃ c' rev S, Setup.reversal o.reverse c (degree c) = .ok (c', degree c', rev) ∧
      0 < degree c' ∧ 1 ≤ H ∧ IsSoundTest c' H S ∧ L = searchList c' H S ⟨rev, o.noCheck, o.noY⟩ ∧
      ∀ noCheck noY : Bool, findPoints c H P { o with noCheck, noY } =
        .ok (searchList c' H S ⟨rev, noCheck, noY⟩) := by
  obtain ⟨out, hout, rfl⟩ : ∃ out, findPointsWith c H P o appendPoint #[] = .ok out ∧
      L = out.info.toList := by
    rcases h' : findPointsWith c H P o appendPoint #[] <;> simp_all [findPoints, Except.map]
  obtain ⟨c', d', rev, h1, h2, hH, hH63, hl, hr, hs, rfl⟩ := findPointsWith_eq_ok_iff.mp hout
  obtain rfl := Setup.degree_eq_of_reversal_eq_ok rfl hr
  obtain ⟨S, hS, hrun⟩ := exists_isSoundTest_run_searchPoints (c := c') hP hH hH63
  have key (fl : CheckFlags) : (Id.run (searchPoints appendPoint c' (degree c') H P fl
      ⟨#[], 0, false⟩)).info.toList = searchList c' H S fl := by
    simpa using congr(($(hrun appendPoint fl ⟨#[], 0, false⟩ rfl)).1.toList)
  refine ⟨c', rev, S, hr, Setup.one_le_of_reversal_eq_ok hr (by lia), hH, hS, key _,
    fun noCheck noY ↦ ?_⟩
  rw [findPoints, findPointsWith_eq_ok_iff (o := { o with noCheck, noY }).mpr
    ⟨c', _, rev, h1, h2, hH, hH63, hl, hr, hs, rfl⟩]
  exact congr(Except.ok $(key _))

/-- Without `RATPOINTS_NO_CHECK`, for well-formed parameters, the list that `Ratpoints.findPoints`
returns is that of the brute-force reference of the polynomial `c'` that the reversal check hands
on, over the candidate `(1, 0)` and the denominators of its search (`Ratpoints.searchDens`), in this
order, mapped back by `Ratpoints.Sieve.swapPoint` after a reversal, without the points with `y < 0`
under `RATPOINTS_NO_Y` (`Ratpoints.searchList_of_noCheck_eq_false`); also when the search takes an
exit, since the curve has no points then. -/
theorem exists_eq_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = false) :
    ∃ c' rev, Setup.reversal o.reverse c (degree c) = .ok (c', degree c', rev) ∧ 1 ≤ H ∧
      L = ((pointsOfDen c' (degree c') 0 [1] ++ (searchDens c' (degree c') H).flatMap
        fun b : ℕ ↦ pointsOfDen c' (degree c') b (numerators H)).map
          (if rev then swapPoint else id)).filter fun p ↦ !o.noY || 0 ≤ p.2.1 := by
  obtain ⟨c', rev, S, hr, hd, hH, hS, rfl, -⟩ := exists_searchList_of_findPoints_eq_ok hP h
  exact ⟨c', rev, hr, hH, searchList_of_noCheck_eq_false hS hd hc⟩

-- The points of the polynomial that the reversal check hands on, mapped back after a reversal, are
-- a permutation of the brute-force reference of `c`
-- (`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`).
private theorem perm_bruteForce_of_reversal_eq_ok {allow rev : Bool} {c c' : List ℤ} {H : ℕ}
    (hr : Setup.reversal allow c (degree c) = .ok (c', degree c', rev)) (hH : 1 ≤ H) :
    (((pointsOfDen c' (degree c') 0 [1] ++ (searchDens c' (degree c') H).flatMap
      fun b : ℕ ↦ pointsOfDen c' (degree c') b (numerators H)).map
        (if rev then swapPoint else id))).Perm (bruteForce c H) := by
  have hp := (perm_bruteForce_append_flatMap_searchDens c' hH).map (if rev then swapPoint else id)
  cases rev
  · simpa [(Setup.eq_of_reversal_eq_ok_false hr).1] using hp
  · exact hp.trans (perm_map_swapPoint_bruteForce (Setup.binaryForm_eq_of_reversal_eq_ok rfl hr) H)

/-- Without the options of the output, when the options forbid the reversal and the denominators of
the search are `1, …, H` (`Ratpoints.searchDens_eq_range'`: even degree, `|c_d| = 1`, or the divisor
set-up fails), the list that `Ratpoints.findPoints` returns is the brute-force reference itself. -/
theorem eq_bruteForce_of_findPoints_eq_ok_of_reverse_eq_false {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = false) (hy : o.noY = false) (ho : o.reverse = false)
    (hs : searchDens c (degree c) H = List.range' 1 H) :
    L = bruteForce c H := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_of_findPoints_eq_ok hP h hc
  rw [ho, Setup.reversal_false] at hr
  cases hr
  simpa [hy] using append_flatMap_searchDens_eq_bruteForce hH hs

/-- Without the options of the output, for well-formed parameters, the list that
`Ratpoints.findPoints` returns is a permutation of the brute-force reference: the search gives the
reference of the polynomial searched in the order of its denominators
(`Ratpoints.perm_bruteForce_append_flatMap_searchDens`), and after a reversal the binary form of the
polynomial searched is that of `c` with `x` and `z` exchanged
(`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`), so that its reference, mapped back, is a
permutation of that of `c` (`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`). -/
theorem perm_bruteForce_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = false) (hy : o.noY = false) :
    L.Perm (bruteForce c H) := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_of_findPoints_eq_ok hP h hc
  simpa [hy] using perm_bruteForce_of_reversal_eq_ok hr hH

/-! ### The main theorems -/

/-- Without `RATPOINTS_NO_CHECK`, for well-formed parameters and the other options, a triple lies in
the list that `Ratpoints.findPoints` returns exactly when it is a normalized point of height at most
`H`, with `y ≥ 0` under `RATPOINTS_NO_Y`; comparator certifies this
(`comparator/Challenge.lean`). -/
theorem mem_iff_isPoint_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = false) {p : ℤ × ℤ × ℤ} :
    p ∈ L ↔ IsPoint c H p ∧ (o.noY = true → 0 ≤ p.2.1) := by
  obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_of_findPoints_eq_ok hP h hc
  rw [List.mem_filter, (perm_bruteForce_of_reversal_eq_ok hr hH).mem_iff, mem_bruteForce_iff]
  cases o.noY <;> simp

/-- For well-formed parameters and every option, the list that `Ratpoints.findPoints` returns has
no duplicates: without `RATPOINTS_NO_CHECK` it is a permutation of the brute-force reference,
filtered under `RATPOINTS_NO_Y`, and under `RATPOINTS_NO_CHECK` the survivors are distinct
(`Ratpoints.nodup_searchList_of_noCheck`); comparator certifies this
(`comparator/Challenge.lean`). -/
theorem nodup_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) : L.Nodup := by
  cases hc : o.noCheck
  · obtain ⟨c', rev, hr, hH, rfl⟩ := exists_eq_of_findPoints_eq_ok hP h hc
    exact ((perm_bruteForce_of_reversal_eq_ok hr hH).nodup_iff.mpr (nodup_bruteForce c H)).filter _
  · obtain ⟨c', rev, S, -, -, hH, -, rfl, -⟩ := exists_searchList_of_findPoints_eq_ok hP h
    exact nodup_searchList_of_noCheck hH S hc

theorem toFinset_eq_points_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = false) (hy : o.noY = false) :
    L.toFinset = points c H :=
  (List.toFinset_eq_of_perm _ _ (perm_bruteForce_of_findPoints_eq_ok hP h hc hy)).trans
    (toFinset_bruteForce c H)

/-! ### `RATPOINTS_NO_CHECK` -/

/-- Under `RATPOINTS_NO_CHECK`, for well-formed parameters, every triple of the list that
`Ratpoints.findPoints` returns is `(x, 0, z)` for the pair `(x, z)` of a normalized point of height
at most `H`, whether it is a point or not: `x` prime to `z`, `z > 0` or `(x, z) = (1, 0)`,
`|x| ≤ H` and `z ≤ H` (`Ratpoints.exists_eq_of_mem_searchList_of_noCheck`); comparator certifies
this (`comparator/Challenge.lean`). -/
theorem exists_eq_of_mem_of_findPoints_eq_ok_of_noCheck {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = true) {q : ℤ × ℤ × ℤ} (hq : q ∈ L) :
    ∃ x z : ℤ, q = (x, 0, z) ∧ Int.gcd x z = 1 ∧ (0 < z ∨ z = 0 ∧ x = 1) ∧ |x| ≤ H ∧ z ≤ H := by
  obtain ⟨c', rev, S, -, -, hH, -, rfl, -⟩ := exists_searchList_of_findPoints_eq_ok hP h
  exact exists_eq_of_mem_searchList_of_noCheck hc hH hq

/-- Under `RATPOINTS_NO_CHECK`, for well-formed parameters, the list `L'` that
`Ratpoints.findPoints` returns for the same input with `RATPOINTS_NO_CHECK` cleared and
`RATPOINTS_NO_Y` set, with `y` replaced by `0`, is a sublist of the list `L` that it returns: both
searches run with the same test of the sieve, so that the points come in the same order among the
survivors (`Ratpoints.map_searchList_sublist`); comparator certifies this
(`comparator/Challenge.lean`). -/
theorem map_sublist_of_findPoints_eq_ok_of_noCheck {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L L' : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = true)
    (h' : findPoints c H P { o with noCheck := false, noY := true } = .ok L') :
    (L'.map fun q ↦ (q.1, 0, q.2.2)).Sublist L := by
  obtain ⟨c', rev, S, -, -, -, -, rfl, hall⟩ := exists_searchList_of_findPoints_eq_ok hP h
  obtain rfl := Except.ok.inj (h'.symm.trans (hall false true))
  rw [hc]
  exact map_searchList_sublist c' H S rev o.noY

/-- Under `RATPOINTS_NO_CHECK`, for well-formed parameters, the list that `Ratpoints.findPoints`
returns has the triple `(x, 0, z)` of every normalized point `(x, y, z)` of height at most `H`: the
point `(x, |y|, z)` is in the list of the search with `RATPOINTS_NO_CHECK` cleared and
`RATPOINTS_NO_Y` set (`Ratpoints.map_sublist_of_findPoints_eq_ok_of_noCheck`); comparator certifies
this (`comparator/Challenge.lean`). -/
theorem mem_of_isPoint_of_findPoints_eq_ok_of_noCheck {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (hc : o.noCheck = true) {p : ℤ × ℤ × ℤ} (hp : IsPoint c H p) : (p.1, 0, p.2.2) ∈ L := by
  obtain ⟨c', rev, S, -, -, -, -, -, hall⟩ := exists_searchList_of_findPoints_eq_ok hP h
  have hp' : (p.1, |p.2.1|, p.2.2) ∈ searchList c' H S ⟨rev, false, true⟩ :=
    (mem_iff_isPoint_of_findPoints_eq_ok hP (hall false true) rfl).mpr
      ⟨by simpa [IsPoint, sq_abs] using hp, fun _ ↦ abs_nonneg _⟩
  exact (map_sublist_of_findPoints_eq_ok_of_noCheck hP h hc (hall false true)).subset
    (List.mem_map.mpr ⟨_, hp', rfl⟩)

/-! ### The refusals -/

/-- With the Sturm step on (`0 ≤ o.sturm`, as in a run of the program without options),
`Ratpoints.findPoints` refuses exactly the inputs with fewer than two or more than
`Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or more, which is
not a `long` (`Ratpoints.fitsLong_natCast`), and the binary forms `Ratpoints.binaryFormPoly c` that
are not squarefree, for all parameters, whether the reversal is allowed or not; comparator certifies
this (`comparator/Challenge.lean`). -/
theorem exists_findPoints_eq_error_iff_of_sturm_nonneg {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} (hs : 0 ≤ o.sturm) :
    (∃ e, findPoints c H P o = .error e) ↔
      c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        ¬ Squarefree (binaryFormPoly c) := by
  rw [exists_findPoints_eq_error_iff, findPointsWith]
  rw [BruteForce.degree_eq]
  simp only [fitsLong_natCast, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  split_ifs with h1 h2 h3 h4
  · simp [h1]
  · simp [h2]
  · grind
  · simp [not_squarefree_binaryFormPoly_of_lt h4]
  simp only [h1, h2, not_or.mp h3, false_or]
  split <;> rename_i hr
  · exact iff_of_true ⟨_, rfl⟩ (Setup.not_squarefree_binaryFormPoly_of_reversal_eq_error hr)
  · rw [← Sturm.run_chain_eq_none_iff_of_reversal_eq_ok (by lia) (by lia) hr]
    split_ifs <;> simp_all

/-- Without the Sturm step (`o.sturm < 0`, the option `-s` of the program), `Ratpoints.findPoints`
refuses, besides the coefficient lists of fewer than two or more than `Ratpoints.maxDegree + 1`
entries and the height bound `0` or one of `2 ^ 63` or more, which is not a `long`
(`Ratpoints.fitsLong_natCast`), exactly the forms whose leading zeros lower `⌈n / 2⌉`, for `n + 1`
coefficients, that is `d + 2 ≤ 2 ⌈n / 2⌉` for the degree `d`, and, when the reversal is allowed,
those of even degree with `c₀ = c₁ = 0`: forms that are not squarefree, but not all of them;
comparator certifies this (`comparator/Challenge.lean`), so that a `Ratpoints.findPoints` that
refused every input under `-s` would not pass. -/
theorem exists_findPoints_eq_error_iff_of_sturm_neg {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} (hs : o.sturm < 0) :
    (∃ e, findPoints c H P o = .error e) ↔
      c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        degree c + 2 ≤ 2 * (c.length / 2) ∨
        o.reverse = true ∧ degree c % 2 = 0 ∧ c.getD 0 0 = 0 ∧ c.getD 1 0 = 0 := by
  rw [exists_findPoints_eq_error_iff, findPointsWith]
  rw [BruteForce.degree_eq]
  simp only [fitsLong_natCast, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  split_ifs with h1 h2 h3 h4
  · simp [h1]
  · simp [h2]
  · grind
  · simp only [Except.error.injEq, exists_eq', true_iff]
    lia
  simp only [h1, h2, not_or.mp h3, false_or, show ¬ degree c + 2 ≤ 2 * (c.length / 2) by lia,
    ← Setup.exists_reversal_eq_error_iff]
  split <;> rename_i hr <;> simp [hr, hs.not_ge]

/-! ### The axioms of the main theorems -/

/--
info: 'Ratpoints.perm_bruteForce_of_findPoints_eq_ok' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms perm_bruteForce_of_findPoints_eq_ok

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
info: 'Ratpoints.toFinset_eq_points_of_findPoints_eq_ok' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toFinset_eq_points_of_findPoints_eq_ok

/--
info: 'Ratpoints.exists_findPoints_eq_error_iff_of_sturm_nonneg' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_findPoints_eq_error_iff_of_sturm_nonneg

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
