/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Ratpoints.Model.FindPoints
public import Ratpoints.Spec.Basic

import Ratpoints.Mathlib.Data.List.Basic
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Params
import Ratpoints.Proof.Sieve
import Ratpoints.Proof.Tables
import Ratpoints.Proof.Words

/-!
# The sieve finds exactly the points

The points at infinity and the run of the denominators give the list of the brute-force reference
of any polynomial with its degree, mapped by `Ratpoints.Sieve.swapPoint` when the flag of the
reversal is set (`Ratpoints.Sieve.pointsAtInfinity_append_toList_run_sieveRun`); so does the search
of the polynomial that the set-up hands on, for well-formed parameters, also when it takes the exit
(`Ratpoints.run_searchPoints`). So `Ratpoints.findPoints c H P` returns the list of the reference
on every input that it does not refuse (`Ratpoints.findPoints_eq_ok_bruteForce`), and the list it
returns holds exactly the points of the specification, each once; comparator certifies the
membership, the absence of duplicates and the refusals (`comparator/Challenge.lean`).

## Main statements

* `Ratpoints.Sieve.pointsAtInfinity_append_toList_run_sieveRun`: for moduli that are primes, the
  points at infinity and the run of the denominators give the list of `Ratpoints.bruteForce`, with
  the flag of the reversal clear, and that list mapped by `Ratpoints.Sieve.swapPoint` when it is
  set.
* `Ratpoints.run_searchPoints`: for well-formed parameters, `H ≥ 1` and the degree of the
  polynomial, the search gives the same list, also when it takes the exit.
* `Ratpoints.findPoints_eq_ok_bruteForce`: for well-formed parameters, `Ratpoints.findPoints`
  returns the list of `Ratpoints.bruteForce` on every input that it does not refuse;
  `Ratpoints.eq_bruteForce_of_findPoints_eq_ok`: every list that it returns is that list.
* `Ratpoints.mem_iff_isPoint_of_findPoints_eq_ok`: a triple lies in the list that
  `Ratpoints.findPoints` returns exactly when it is a normalized point of height at most `H`.
* `Ratpoints.nodup_of_findPoints_eq_ok`: the list has no duplicates.
* `Ratpoints.toFinset_eq_points_of_findPoints_eq_ok`: its set of elements is `Ratpoints.points`.
* `Ratpoints.exists_findPoints_eq_error_iff`: `Ratpoints.findPoints` refuses exactly the inputs
  with fewer than two or more than `Ratpoints.maxDegree + 1` coefficients and the height bound
  `0`.

## Proof

By the contract of the denominators (`Ratpoints.Sieve.toList_run_sieveRun`), for pieces of at least
one bit array and moduli that are primes, hence positive, the run returns the part of the reference
with `z ≥ 1`, the numerators of each denominator filtered by the survivor test, mapped when the flag
of the reversal is set; every numerator over which the exact check finds a point survives
(`Ratpoints.Sieve.survives_of_mem_pointsOfDen`), so the filter changes nothing
(`Ratpoints.BruteForce.pointsOfDen_filter_of_ne`); and the points at infinity are those of the
candidate `(1, 0)` of the reference (`Ratpoints.Sieve.pointsAtInfinity_eq_pointsOfDen`), mapped when
the flag is set (`Ratpoints.Sieve.pointsAtInfinity_eq_map`). In the search, the pieces have at least
one bit array (`Ratpoints.Params.one_le_arraySizeAt`) and the moduli of well-formed parameters are
primes (`Ratpoints.Params.WF.prime_of_mem`); a table that the search makes is that of the reference
(`Ratpoints.Sieve.eq_examinePrime_of_examinePrime?_eq_some`), and when the search takes the exit,
the curve has no points (`Ratpoints.Sieve.not_isPoint_of_examinePrime?_eq_none`), so the reference
is empty. `Ratpoints.findPoints` runs the search with the flag clear.
-/

@[expose] public section

namespace Ratpoints

open BruteForce Sieve

/-! ### Sound filters, the points at infinity and the run -/

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

theorem survives_of_mem_pointsOfDen {c : List ℤ} {ms : List ℕ} (hms : ∀ p ∈ ms, p.Prime) {b : ℕ}
    {xs : List ℤ} {q : ℤ × ℤ × ℤ} (hq : q ∈ pointsOfDen c (BruteForce.degree c) b xs) :
    survives (ms.map (examinePrime c (BruteForce.degree c))) b q.1 = true := by
  obtain ⟨x, y, z⟩ := q
  obtain ⟨-, rfl, hg, hy⟩ := mem_pointsOfDen_iff.mp hq
  rw [horner_scaledCoeffs_mul] at hy
  simp only [survives, List.all_map, List.all_eq_true, Function.comp_apply]
  exact fun p hp ↦ admits_examinePrime_of_sq_eq (hms p hp) hg hy

theorem pointsAtInfinity_eq_pointsOfDen (c : List ℤ) (d : ℕ) :
    pointsAtInfinity c d false = pointsOfDen c d 0 [1] := by
  simp only [pointsAtInfinity, pointsOfDen_singleton, Int.gcd_one_left, reduceCtorEq, ↓reduceIte,
    horner_scaledCoeffs_one_zero]
  split_ifs <;> simp [pointsAbove]

theorem pointsAtInfinity_eq_map (c : List ℤ) (d : ℕ) (rev : Bool) :
    pointsAtInfinity c d rev =
      if rev then (pointsAtInfinity c d false).map swapPoint else pointsAtInfinity c d false := by
  cases rev <;> simp [pointsAtInfinity, pointsAbove, apply_ite (List.map swapPoint), swapPoint]

-- The survivor test of the tables of primes keeps every numerator over which the exact check finds
-- a point, so that filtering by it changes nothing.
private theorem pointsOfDen_filter_survives (c : List ℤ) {ms : List ℕ} (hms : ∀ p ∈ ms, p.Prime)
    (b : ℕ) (xs : List ℤ) :
    pointsOfDen c (degree c) b (xs.filter (survives (ms.map (examinePrime c (degree c))) b)) =
      pointsOfDen c (degree c) b xs :=
  pointsOfDen_filter_of_ne fun _ _ hx ↦
    have ⟨_, hq⟩ := List.exists_mem_of_ne_nil _ hx
    (List.mem_singleton.mp (mem_pointsOfDen_iff.mp hq).1) ▸ survives_of_mem_pointsOfDen hms hq

/-- By the contract of the run (`Ratpoints.Sieve.toList_run_sieveRun`), for pieces of at least one
bit array and moduli that are primes, hence positive, the run gives the reference with the
numerators of each denominator filtered by the survivor test, which changes nothing
(`Ratpoints.Sieve.survives_of_mem_pointsOfDen`, `Ratpoints.BruteForce.pointsOfDen_filter_of_ne`);
the points at infinity are those of the candidate `(1, 0)` of the reference
(`Ratpoints.Sieve.pointsAtInfinity_eq_pointsOfDen`); both are mapped by `Ratpoints.Sieve.swapPoint`
when the flag of the reversal is set (`Ratpoints.Sieve.pointsAtInfinity_eq_map`). -/
theorem pointsAtInfinity_append_toList_run_sieveRun (c : List ℤ) {H A : ℕ} {ms : List ℕ}
    (hms : ∀ p ∈ ms, p.Prime) (hA : 1 ≤ A) (hH : 1 ≤ H) (rev : Bool) :
    pointsAtInfinity c (degree c) rev ++
        (Id.run (sieveRun c (degree c) H A rev (ms.map (examinePrime c (degree c))))).toList =
      if rev then (bruteForce c H).map swapPoint else bruteForce c H := by
  rw [toList_run_sieveRun c _ H rev hA (List.forall_mem_map.mpr fun _ hq ↦ (hms _ hq).pos),
    pointsAtInfinity_eq_map, pointsAtInfinity_eq_pointsOfDen]
  simp only [pointsOfDen_filter_survives c hms]
  cases rev <;> simp [bruteForce, hH, BruteForce.degree_eq]

end Sieve

/-! ### The search -/

-- A curve without points modulo a prime has an empty reference.
private theorem bruteForce_eq_nil_of_examinePrime?_eq_none {c : List ℤ} {d p : ℕ} {u : Bool}
    (h : examinePrime? c d p u = none) (hp : p.Prime) (hd : d = degree c) (H : ℕ) :
    bruteForce c H = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun q hq ↦
    not_isPoint_of_examinePrime?_eq_none h hp hd H q (mem_bruteForce_iff.mp hq)

/-- The tables that the search makes are those of the reference
(`Ratpoints.Sieve.eq_examinePrime_of_examinePrime?_eq_some`), on which the points at infinity and
the run give the reference (`Ratpoints.Sieve.pointsAtInfinity_append_toList_run_sieveRun`); when the
search takes the exit, the curve has no points
(`Ratpoints.Sieve.not_isPoint_of_examinePrime?_eq_none`), so that the reference is empty. -/
theorem run_searchPoints {c : List ℤ} {d H : ℕ} {P : Params} (hP : P.WF) (hH : 1 ≤ H)
    (hd : d = degree c) (rev : Bool) :
    Id.run (searchPoints c d H P rev) =
      if rev then (bruteForce c H).map swapPoint else bruteForce c H := by
  subst hd
  simp only [searchPoints]
  split <;> rename_i hm
  · obtain ⟨_, hp, he⟩ := List.exists_mem_of_mapM_eq_none hm
    simp [bruteForce_eq_nil_of_examinePrime?_eq_none he (hP.prime_of_mem hp) rfl H]
  · rw [List.eq_map_of_mapM_eq_some (fun _ _ _ ↦ eq_examinePrime_of_examinePrime?_eq_some) hm]
    exact pointsAtInfinity_append_toList_run_sieveRun c (fun _ ↦ hP.prime_of_mem)
      (P.one_le_arraySizeAt hH) hH rev

/-! ### The main theorems -/

/-- `Ratpoints.findPoints` runs the search with the flag of the reversal clear, which gives the
reference (`Ratpoints.run_searchPoints`). -/
theorem findPoints_eq_ok_bruteForce {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF)
    (hc2 : 2 ≤ c.length) (hcmax : c.length ≤ maxDegree + 1) (hH : H ≠ 0) :
    findPoints c H P = .ok (bruteForce c H) := by
  simp only [findPoints, hcmax.not_gt, hc2.not_gt, hH, ↓reduceIte, Bool.false_eq_true,
    run_searchPoints hP (Nat.one_le_iff_ne_zero.mpr hH) (BruteForce.degree_eq c) false]

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
  · exact Except.ok.inj (h.symm.trans (findPoints_eq_ok_bruteForce hP hc.1 hc.2.1 hc.2.2))
  · obtain ⟨e, he⟩ : ∃ e, findPoints c H P = .error e :=
      exists_findPoints_eq_error_iff.mpr (by lia)
    cases he.symm.trans h

/-- For well-formed parameters, a triple lies in the list that `Ratpoints.findPoints` returns
exactly when it is a normalized point of height at most `H`; comparator certifies this
(`comparator/Challenge.lean`). -/
theorem mem_iff_isPoint_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P = .ok L) {p : ℤ × ℤ × ℤ} :
    p ∈ L ↔ IsPoint c H p :=
  eq_bruteForce_of_findPoints_eq_ok hP h ▸ mem_bruteForce_iff

/-- For well-formed parameters, the list that `Ratpoints.findPoints` returns has no duplicates;
comparator certifies this (`comparator/Challenge.lean`). -/
theorem nodup_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {L : List (ℤ × ℤ × ℤ)}
    (hP : P.WF) (h : findPoints c H P = .ok L) : L.Nodup :=
  eq_bruteForce_of_findPoints_eq_ok hP h ▸ nodup_bruteForce c H

theorem toFinset_eq_points_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P = .ok L) :
    L.toFinset = points c H :=
  eq_bruteForce_of_findPoints_eq_ok hP h ▸ toFinset_bruteForce c H

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
