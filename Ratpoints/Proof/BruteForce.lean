/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.BruteForce
public import Ratpoints.Spec.Basic

import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Tactic.Ring
import Ratpoints.Mathlib.Data.List.Basic

/-!
# The brute-force reference finds exactly the points

`Ratpoints.bruteForce c H` lists every normalized point of height at most `H` on
`y ^ 2 = F(x, z)`, and nothing else, each once: the theorem of stage B, which comparator certifies
(`comparator/Challenge.lean`).

## Main statements

* `Ratpoints.mem_bruteForce_iff`: a triple lies in `Ratpoints.bruteForce c H` exactly when it is a
  normalized point of height at most `H`.
* `Ratpoints.nodup_bruteForce`: the list has no duplicates.
* `Ratpoints.toFinset_bruteForce`: its set of elements is `Ratpoints.points c H`.

## Proof

The evaluation of the model, Horner's rule on the products `cₖ z^(d - k)` with one more factor `z`
for odd `d`, is `Ratpoints.binaryForm` (`Ratpoints.BruteForce.horner_scaledCoeffs_mul`); `v` is
the square of `y` exactly when the model's test of `⌊√v⌋` succeeds and `y = ±⌊√v⌋`
(`Ratpoints.BruteForce.mem_pointsAbove_iff`); and the candidates are the pairs that the
normalization allows. The triples of different candidates differ in `x` or in `z`, so the list has
no duplicates.
-/

@[expose] public section

namespace Ratpoints

namespace BruteForce

theorem degree_eq (c : List ℤ) : degree c = Ratpoints.degree c := rfl

theorem horner_eq_sum (w : List ℤ) (x : ℤ) :
    horner w x = ∑ k ∈ Finset.range w.length, w.getD k 0 * x ^ k := by
  induction w with
  | nil => rfl
  | cons a w ih =>
    simp only [horner, List.foldr_cons, List.length_cons, Finset.sum_range_succ',
      List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one] at ih ⊢
    rw [ih, Finset.mul_sum, add_comm]
    congr 1
    exact Finset.sum_congr rfl fun k _ ↦ by ring

theorem horner_scaledCoeffs (c : List ℤ) (d : ℕ) (x z : ℤ) :
    horner (scaledCoeffs c d z) x =
      ∑ k ∈ Finset.range (d + 1), c.getD k 0 * z ^ (d - k) * x ^ k := by
  rw [horner_eq_sum, scaledCoeffs, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  simp [List.getD_eq_getElem?_getD, List.getElem?_range (Finset.mem_range.mp hk)]

theorem horner_scaledCoeffs_mul (c : List ℤ) (x z : ℤ) :
    horner (scaledCoeffs c (degree c) z) x * (if degree c % 2 = 1 then z else 1) =
      binaryForm c x z := by
  rw [horner_scaledCoeffs, binaryForm, Finset.sum_mul, degree_eq]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk : k ≤ Ratpoints.degree c := Finset.mem_range_succ_iff.mp hk
  split_ifs with h
  · rw [h, show Ratpoints.degree c + 1 - k = Ratpoints.degree c - k + 1 by lia, pow_succ]
    ring
  · rw [show Ratpoints.degree c % 2 = 0 by lia, add_zero]
    ring

-- The test of `pointsAbove` says that `v` is a square.
private theorem sqrt_mul_self_iff (v : ℤ) :
    (0 ≤ v ∧ v.toNat.sqrt * v.toNat.sqrt = v.toNat) ↔ Int.sqrt v * Int.sqrt v = v := by
  simp only [Int.sqrt]
  constructor
  · intro ⟨hv, h⟩
    rw [← Nat.cast_mul, h, Int.toNat_of_nonneg hv]
  · intro h
    refine ⟨h ▸ mul_self_nonneg _, ?_⟩
    lia

private theorem sq_eq_iff (b v : ℤ) :
    b ^ 2 = v ↔ Int.sqrt v * Int.sqrt v = v ∧ (b = Int.sqrt v ∨ b = -Int.sqrt v) := by
  constructor
  · rintro rfl
    rw [sq, Int.sqrt_eq]
    exact ⟨Int.natAbs_mul_self' b, Int.natAbs_eq b⟩
  · rintro ⟨h, rfl | rfl⟩ <;> simpa [sq] using h

theorem mem_pointsAbove_iff {x z v : ℤ} {p : ℤ × ℤ × ℤ} :
    p ∈ pointsAbove x z v ↔ p.1 = x ∧ p.2.2 = z ∧ p.2.1 ^ 2 = v := by
  obtain ⟨a, b, e⟩ := p
  rw [sq_eq_iff, ← sqrt_mul_self_iff]
  simp only [pointsAbove]
  split_ifs with h h0
  · simp only [List.mem_singleton, Prod.mk.injEq, Int.sqrt, h0]
    grind
  · simp only [List.mem_cons, List.not_mem_nil, Prod.mk.injEq, Int.sqrt, h]
    grind
  · simp [h]

theorem mem_pointsOfDen_iff {c : List ℤ} {d : ℕ} {z : ℤ} {xs : List ℤ} {p : ℤ × ℤ × ℤ} :
    p ∈ pointsOfDen c d z xs ↔ p.1 ∈ xs ∧ p.2.2 = z ∧ Int.gcd p.1 z = 1 ∧
      p.2.1 ^ 2 = horner (scaledCoeffs c d z) p.1 * (if d % 2 = 1 then z else 1) := by
  simp only [pointsOfDen, List.mem_flatMap]
  constructor
  · intro ⟨x, hx, h⟩
    by_cases hg : Int.gcd x z = 1
    · simp only [hg, ↓reduceIte] at h
      obtain ⟨rfl, rfl, hy⟩ := mem_pointsAbove_iff.mp h
      exact ⟨hx, rfl, hg, hy⟩
    · simp [hg] at h
  · rintro ⟨hx, rfl, hg, hy⟩
    refine ⟨p.1, hx, ?_⟩
    simp only [hg, ↓reduceIte]
    exact mem_pointsAbove_iff.mpr ⟨rfl, rfl, hy⟩

theorem exists_sq_eq_of_pointsOfDen_ne_nil {c : List ℤ} {b : ℕ} {xs : List ℤ}
    (h : pointsOfDen c (degree c) b xs ≠ []) :
    ∃ a ∈ xs, ∃ y : ℤ, Int.gcd a b = 1 ∧ y ^ 2 = binaryForm c a b := by
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hx, -, hg, hy⟩ := mem_pointsOfDen_iff.mp hq
  exact ⟨q.1, hx, q.2.1, hg, hy.trans (horner_scaledCoeffs_mul c _ _)⟩

theorem pointsOfDen_filter_of_ne {c : List ℤ} {d : ℕ} {z : ℤ} {xs : List ℤ} {keep : ℤ → Bool}
    (h : ∀ x ∈ xs, pointsOfDen c d z [x] ≠ [] → keep x) :
    pointsOfDen c d z (xs.filter keep) = pointsOfDen c d z xs :=
  List.flatMap_filter_of_ne (by simpa [pointsOfDen] using h)

theorem mem_numerators_iff {x : ℤ} {H : ℕ} : x ∈ numerators H ↔ |x| ≤ H := by
  simp only [numerators, List.mem_map, List.mem_range, abs_le]
  exact ⟨fun ⟨i, hi, h⟩ ↦ by lia, fun h ↦ ⟨(x + H).toNat, by lia, by lia⟩⟩

theorem nodup_pointsAbove (x z v : ℤ) : (pointsAbove x z v).Nodup := by
  simp only [pointsAbove]
  split_ifs with h h0
  · simp
  · simp only [List.nodup_cons, List.mem_singleton, Prod.mk.injEq, List.not_mem_nil,
      not_false_eq_true, List.nodup_nil, and_true]
    lia
  · simp

theorem nodup_numerators (H : ℕ) : (numerators H).Nodup :=
  List.nodup_range.map fun _ _ h ↦ by lia

theorem nodup_pointsOfDen (c : List ℤ) (d : ℕ) (z : ℤ) {xs : List ℤ} (hxs : xs.Nodup) :
    (pointsOfDen c d z xs).Nodup := by
  rw [pointsOfDen, List.nodup_flatMap]
  refine ⟨fun x _ ↦ ?_, hxs.pairwise_of_forall_ne fun a _ b _ hab p ha hb ↦ hab ?_⟩
  · by_cases hg : Int.gcd x z = 1 <;> simp only [hg, ↓reduceIte]
    exacts [nodup_pointsAbove .., List.nodup_nil]
  · have key (x : ℤ) (h : p ∈ if Int.gcd x z = 1 then
        pointsAbove x z (horner (scaledCoeffs c d z) x * if d % 2 = 1 then z else 1) else []) :
        p.1 = x := by
      by_cases hg : Int.gcd x z = 1 <;> simp only [hg, ↓reduceIte] at h
      exacts [(mem_pointsAbove_iff.mp h).1, absurd h List.not_mem_nil]
    rw [← key a ha, ← key b hb]

end BruteForce

open BruteForce in
/-- The brute-force reference lists exactly the normalized points of height at most `H`, for every
coefficient list and every height; comparator certifies this (`comparator/Challenge.lean`). -/
theorem mem_bruteForce_iff {c : List ℤ} {H : ℕ} {p : ℤ × ℤ × ℤ} :
    p ∈ bruteForce c H ↔ IsPoint c H p := by
  obtain ⟨x, y, z⟩ := p
  simp only [bruteForce, List.mem_append, List.mem_ite_nil_right, List.mem_flatMap,
    List.mem_range, mem_pointsOfDen_iff, horner_scaledCoeffs_mul, mem_numerators_iff,
    List.mem_singleton, IsPoint, Nat.cast_add, Nat.cast_one]
  constructor
  · rintro (⟨hH, rfl, rfl, -, hy⟩ | ⟨j, hj, hx, rfl, hg, hy⟩)
    · exact ⟨hy, rfl, .inr ⟨rfl, rfl⟩, by simpa using hH, by lia⟩
    · exact ⟨hy, hg, .inl (by lia), hx, by lia⟩
  · rintro ⟨hy, hg, hz | ⟨rfl, rfl⟩, hx, hzH⟩
    · obtain ⟨j, rfl⟩ : ∃ j : ℕ, z = j + 1 := ⟨(z - 1).toNat, by lia⟩
      exact .inr ⟨j, by lia, hx, rfl, hg, hy⟩
    · exact .inl ⟨by simpa using hx, rfl, rfl, by simp, hy⟩

open BruteForce in
/-- The brute-force reference lists each point once; comparator certifies this
(`comparator/Challenge.lean`). -/
theorem nodup_bruteForce (c : List ℤ) (H : ℕ) : (bruteForce c H).Nodup := by
  have hz {z : ℤ} {xs : List ℤ} {p : ℤ × ℤ × ℤ} (h : p ∈ pointsOfDen c (degree c) z xs) :
      p.2.2 = z :=
    (mem_pointsOfDen_iff.mp h).2.1
  simp only [bruteForce]
  refine List.Nodup.append ?_ ?_ fun p h1 h2 ↦ ?_
  · split_ifs
    exacts [nodup_pointsOfDen _ _ _ (List.nodup_singleton 1), List.nodup_nil]
  · rw [List.nodup_flatMap]
    refine ⟨fun j _ ↦ nodup_pointsOfDen _ _ _ (nodup_numerators H),
      List.nodup_range.pairwise_of_forall_ne fun a _ b _ hab p ha hb ↦ hab ?_⟩
    have := (hz ha).symm.trans (hz hb)
    lia
  · split_ifs at h1
    · obtain ⟨j, -, hj⟩ := List.mem_flatMap.mp h2
      have := (hz h1).symm.trans (hz hj)
      lia
    · exact List.not_mem_nil h1

theorem toFinset_bruteForce (c : List ℤ) (H : ℕ) : (bruteForce c H).toFinset = points c H :=
  Finset.ext fun _ ↦ by simp [mem_bruteForce_iff]

/-! ### The axioms of the main theorems -/

/--
info: 'Ratpoints.mem_bruteForce_iff' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms mem_bruteForce_iff

/--
info: 'Ratpoints.nodup_bruteForce' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms nodup_bruteForce

/--
info: 'Ratpoints.toFinset_bruteForce' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toFinset_bruteForce

end Ratpoints

end
