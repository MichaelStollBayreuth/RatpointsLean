/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.FindPoints
public import Ratpoints.Spec.Basic

import Ratpoints.Mathlib.Data.List.Basic
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Params
import Ratpoints.Proof.Sieve
import Ratpoints.Proof.Tables

/-!
# The plain sieve finds exactly the points

For well-formed parameters, `Ratpoints.findPoints c H P` returns the list of the brute-force
reference on every input that it does not refuse (`Ratpoints.findPoints_eq_ok_bruteForce`), so
that the list it returns holds exactly the points of the specification, each once; comparator
certifies the membership, the absence of duplicates and the refusals
(`comparator/Challenge.lean`).

## Main statements

* `Ratpoints.mem_iff_isPoint_of_findPoints_eq_ok`: a triple lies in the list that
  `Ratpoints.findPoints` returns exactly when it is a normalized point of height at most `H`.
* `Ratpoints.nodup_of_findPoints_eq_ok`: the list has no duplicates.
* `Ratpoints.toFinset_eq_points_of_findPoints_eq_ok`: its set of elements is `Ratpoints.points`.
* `Ratpoints.exists_findPoints_eq_error_iff`: `Ratpoints.findPoints` refuses exactly the inputs
  with fewer than two or more than `Ratpoints.maxDegree + 1` coefficients and the height bound
  `0`.

## Proof

By the contract of the denominators (`Ratpoints.Sieve.toList_run_sieveRun`), the sieve returns
the part of the reference with `z ≥ 1`, the numerators of each denominator filtered by the
survivor test; every numerator over which the exact check finds a point survives
(`Ratpoints.Sieve.survives_of_mem_pointsOfDen`), so the filter changes nothing
(`Ratpoints.BruteForce.pointsOfDen_filter_of_ne`); and the points at infinity are those of the
candidate `(1, 0)` of the reference (`Ratpoints.Sieve.pointsAtInfinity_eq_pointsOfDen`).
-/

@[expose] public section

namespace Ratpoints

open BruteForce Sieve

/-! ### Sound filters and the points at infinity -/

namespace BruteForce

theorem pointsOfDen_filter_of_ne {c : List ℤ} {d : ℕ} {z : ℤ} {xs : List ℤ}
    {keep : ℤ → Bool} (h : ∀ x ∈ xs, pointsOfDen c d z [x] ≠ [] → keep x) :
    pointsOfDen c d z (xs.filter keep) = pointsOfDen c d z xs := by
  simp only [pointsOfDen_singleton] at h
  exact List.flatMap_filter_of_ne h

theorem horner_scaledCoeffs_one_zero (c : List ℤ) (d : ℕ) :
    horner (scaledCoeffs c d 0) 1 = c.getD d 0 := by
  rw [horner_scaledCoeffs, Finset.sum_range_succ, Finset.sum_eq_zero fun k hk ↦ by
    rw [zero_pow (by have := Finset.mem_range.mp hk; lia)]; simp]
  simp

end BruteForce

namespace Sieve

/-- Every modulus of well-formed parameters is a prime of the table
(`Ratpoints.prime_of_mem_primeTable`), so that `Ratpoints.Sieve.admits_examinePrime_of_sq_eq`
applies to each. -/
theorem survives_of_mem_pointsOfDen {c : List ℤ} {P : Params} (hP : P.WF) {b : ℕ}
    {xs : List ℤ} {q : ℤ × ℤ × ℤ} (hq : q ∈ pointsOfDen c (BruteForce.degree c) b xs) :
    survives (P.moduli.map (examinePrime c (BruteForce.degree c))) b q.1 = true := by
  obtain ⟨x, y, z⟩ := q
  obtain ⟨-, rfl, hg, hy⟩ := mem_pointsOfDen_iff.mp hq
  rw [horner_scaledCoeffs_mul] at hy
  simp only [survives, List.all_map, List.all_eq_true, Function.comp_apply]
  exact fun p hp ↦ admits_examinePrime_of_sq_eq
    (prime_of_mem_primeTable (hP.mem_primeTable p hp)) hg hy

theorem pointsAtInfinity_eq_pointsOfDen (c : List ℤ) (d : ℕ) :
    pointsAtInfinity c d = pointsOfDen c d 0 [1] := by
  simp only [pointsAtInfinity, pointsOfDen_singleton, Int.gcd_one_left, ↓reduceIte,
    horner_scaledCoeffs_one_zero]
  split_ifs <;> simp [pointsAbove]

end Sieve

/-! ### The main theorems -/

/-- By `Ratpoints.Sieve.toList_run_sieveRun`, the sieve gives the reference with the numerators of
each denominator filtered by the survivor test, which changes nothing
(`Ratpoints.Sieve.survives_of_mem_pointsOfDen`, `Ratpoints.BruteForce.pointsOfDen_filter_of_ne`).
-/
theorem findPoints_eq_ok_bruteForce {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF)
    (hc2 : 2 ≤ c.length) (hcmax : c.length ≤ maxDegree + 1) (hH : H ≠ 0) :
    findPoints c H P = .ok (bruteForce c H) := by
  simp only [findPoints, bruteForce, Nat.not_lt.mpr hcmax, Nat.not_lt.mpr hc2, hH,
    Nat.one_le_iff_ne_zero.mpr hH, ↓reduceIte, pointsAtInfinity_eq_pointsOfDen, toList_run_sieveRun]
  congr 3
  funext j
  refine pointsOfDen_filter_of_ne fun x _ hx ↦ ?_
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hx
  obtain rfl : q.1 = x := List.mem_singleton.mp (mem_pointsOfDen_iff.mp hq).1
  exact survives_of_mem_pointsOfDen hP hq

/-- `Ratpoints.findPoints` refuses exactly the inputs with fewer than two or more than
`Ratpoints.maxDegree + 1` coefficients and the height bound `0`; comparator certifies this
(`comparator/Challenge.lean`). -/
theorem exists_findPoints_eq_error_iff {c : List ℤ} {H : ℕ} {P : Params} :
    (∃ e, findPoints c H P = .error e) ↔ c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 := by
  simp only [findPoints]
  split_ifs <;> simp_all

theorem eq_bruteForce_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P = .ok L) : L = bruteForce c H := by
  by_cases hc : 2 ≤ c.length ∧ c.length ≤ maxDegree + 1 ∧ H ≠ 0
  · rw [findPoints_eq_ok_bruteForce hP hc.1 hc.2.1 hc.2.2] at h
    exact (Except.ok.inj h).symm
  · obtain ⟨e, he⟩ : ∃ e, findPoints c H P = .error e :=
      exists_findPoints_eq_error_iff.mpr (by lia)
    cases he.symm.trans h

/-- For well-formed parameters, a triple lies in the list that `Ratpoints.findPoints` returns
exactly when it is a normalized point of height at most `H`; comparator certifies this
(`comparator/Challenge.lean`). -/
theorem mem_iff_isPoint_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P = .ok L) {p : ℤ × ℤ × ℤ} :
    p ∈ L ↔ IsPoint c H p := by
  rw [eq_bruteForce_of_findPoints_eq_ok hP h, mem_bruteForce_iff]

/-- For well-formed parameters, the list that `Ratpoints.findPoints` returns has no duplicates;
comparator certifies this (`comparator/Challenge.lean`). -/
theorem nodup_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {L : List (ℤ × ℤ × ℤ)}
    (hP : P.WF) (h : findPoints c H P = .ok L) : L.Nodup :=
  eq_bruteForce_of_findPoints_eq_ok hP h ▸ nodup_bruteForce c H

theorem toFinset_eq_points_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P = .ok L) :
    L.toFinset = points c H := by
  rw [eq_bruteForce_of_findPoints_eq_ok hP h, toFinset_bruteForce]

/-! ### The axioms of the main theorems -/

/--
info: 'Ratpoints.findPoints_eq_ok_bruteForce' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms findPoints_eq_ok_bruteForce

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
info: 'Ratpoints.exists_findPoints_eq_error_iff' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms exists_findPoints_eq_error_iff

end Ratpoints

end
