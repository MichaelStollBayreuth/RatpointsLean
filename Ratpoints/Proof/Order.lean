/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.BruteForce
public import Ratpoints.Model.Setup
public import Ratpoints.Spec.Order

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Algebra.Order.Ring.Abs
import Ratpoints.Mathlib.Data.List.Basic
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Setup

/-!
# The order of the points: the specification and the model

The pieces of the search that the specification of the order (`Ratpoints.orderedPoints`) spells
out, in the terms of the model: the reversal check hands on the polynomial of
`Ratpoints.searchedPoly`; the denominators of `Ratpoints.searchDenominators` lie in `1, …, H`; and
the points of the brute-force reference over a denominator, and over the candidate `(1, 0)`, are
those of `Ratpoints.pointsWithDen`. That the denominators of the search are those of
`Ratpoints.searchDenominators` (`Ratpoints.searchDens_eq_searchDenominators`), since the divisor
set-up succeeds exactly when ratpoints factors `|c_d|` completely and finds fewer than
`Ratpoints.maxDivisors` divisors (`Ratpoints.Setup.map_snd_run_setupUs1`), is in
`Ratpoints.Proof.FindPoints`, and `Ratpoints.eq_orderedPoints_of_findPoints_eq_ok`, which puts the
pieces together, in `Ratpoints.Proof.Output`.

## Main statements

* `Ratpoints.searchedPoly_eq_of_reversal_eq_ok`: the polynomial searched.
* `Ratpoints.pointsOfDen_eq_pointsWithDen`, `Ratpoints.pointsOfDen_zero_eq_pointsWithDen`: the
  points of a denominator and the points at infinity.
* `Ratpoints.le_and_le_of_mem_searchDenominators`: the denominators lie in `1, …, H`.
-/

@[expose] public section

namespace Ratpoints

open BruteForce

/-! ### The polynomial searched -/

/-- The polynomial that the reversal check hands on, and whether it is reversed, are those of
`Ratpoints.searchedPoly`. -/
theorem searchedPoly_eq_of_reversal_eq_ok {allow rev : Bool} {c c' : List ℤ} {d' : ℕ}
    (h : Setup.reversal allow c (degree c) = .ok (c', d', rev)) :
    searchedPoly allow c = (c', rev) := by
  rw [Setup.reversal] at h
  rw [searchedPoly]
  split_ifs at h <;> simp only [Except.ok.injEq, Prod.mk.injEq] at h <;>
    obtain ⟨rfl, -, rfl⟩ := h <;>
    simp_all [Setup.isSquare_eq_true_iff, Setup.isSquare_eq_false_iff]

/-! ### The denominators -/

theorem pos_of_mem_binaryDivisors {n H e : ℕ} (he : e ∈ binaryDivisors n H) : 0 < e := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp (List.mem_filter.mp he).1
  exact List.prod_pos fun p hp ↦ (Nat.prime_of_mem_primeFactorsList
    (List.mem_dedup.mp ((List.mem_sublists.mp hl).subset hp))).pos

theorem le_and_le_of_mem_searchDenominators {maxDiv H b : ℕ} {c : List ℤ}
    (hb : b ∈ searchDenominators maxDiv c H) : 1 ≤ b ∧ b ≤ H := by
  rw [searchDenominators] at hb
  split_ifs at hb
  · obtain ⟨hb, hbH⟩ := List.mem_filter.mp hb
    obtain ⟨e, he, k, hk, rfl⟩ := by simpa using hb
    exact ⟨Nat.mul_pos (pos_of_mem_binaryDivisors he) (Nat.pow_pos (by lia)), by simpa using hbH⟩
  · exact ⟨(List.mem_range'_1.mp hb).1, by lia [List.mem_range'_1.mp hb]⟩

/-! ### The points of a denominator -/

/-- The points of the brute-force reference with the denominator `1 ≤ z ≤ H` are those of
`Ratpoints.pointsWithDen`, in the same order. -/
theorem pointsOfDen_eq_pointsWithDen (c : List ℤ) {H z : ℕ} (hz : 0 < z) (hzH : z ≤ H) :
    pointsOfDen c (degree c) z (numerators H) = pointsWithDen c H z :=
  List.flatMap_congr fun x hx ↦ by
    rw [← BruteForce.degree_eq, horner_scaledCoeffs_mul]
    exact ite_pointsAbove_eq_filter (.inl (by lia)) (mem_numerators_iff.mp hx) (by lia)

/-- The points at infinity of the brute-force reference, those of the candidate `(1, 0)`, are
those of `Ratpoints.pointsWithDen` with the denominator `0`, for `H ≥ 1`: the numerators other than
`1` give none. -/
theorem pointsOfDen_zero_eq_pointsWithDen (c : List ℤ) {H : ℕ} (hH : 1 ≤ H) :
    pointsOfDen c (degree c) 0 [1] = pointsWithDen c H 0 := by
  have h1 : (numerators H).filter (· == 1) = [1] := by
    rw [List.filter_beq, List.count_eq_one_of_mem (nodup_numerators H)
      (mem_numerators_iff.mpr (by simpa using hH)), List.replicate_one]
  refine .trans ?_ (List.flatMap_filter_of_ne (l := numerators H) (p := (· == 1)) fun x _ hx ↦ ?_)
  · rw [h1, List.flatMap_singleton, pointsOfDen, List.flatMap_singleton, ← BruteForce.degree_eq,
      horner_scaledCoeffs_mul]
    exact ite_pointsAbove_eq_filter (.inr ⟨Nat.cast_zero, rfl⟩) (by simpa using hH) (by simp)
  · obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ hx
    obtain ⟨hqL, hqP⟩ := List.mem_filter.mp hq
    have hn := (of_decide_eq_true hqP).2.2.1
    have : q.1 = x ∧ q.2.2 = 0 := by split_ifs at hqL <;> simp at hqL <;> grind
    simp only [this.2, lt_self_iff_false, true_and, false_or] at hn
    simpa [← this.1] using hn

end Ratpoints

end
