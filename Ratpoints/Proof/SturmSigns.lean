/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.SignVariations
public import Ratpoints.Proof.Setup

import Mathlib.Data.List.GetD
import Mathlib.Tactic.Field
import Ratpoints.Proof.Containers

/-!
# The signs of the chain of the Sturm step

The signs that the Sturm step computes, in the terms of Mathlib: the Horner value of
`Ratpoints.Sturm.evalSign` is `2 ^ (e deg)` times the value of the polynomial of the row at
`n / 2 ^ e` (`Ratpoints.Sturm.hornerValue_eq_eval`), so that `Ratpoints.Sturm.evalSign` computes its
sign (`Ratpoints.Sturm.run_evalSign_eq_sign_eval`); the count of `Ratpoints.Sturm.signsAt` at a
point where `f` and `f'` do not both vanish is the number of sign variations
(`List.signVariations`) of the signs of the rows there
(`Ratpoints.Sturm.run_signsAt_eq_signVariations`); and the counts of
`Ratpoints.Sturm.countsAtInfinity` are the numbers of sign variations of the signs of the leading
coefficients, negated for odd degree at `-∞`
(`Ratpoints.Sturm.run_countsAtInfinity_eq_signVariations`). The rows of a chain as positive
multiples of the entries of Mathlib's Sturm sequence of `f` and `f'`, and with them the signs and
the counts of the Sturm step as those of the real polynomial, come with stage H.

## Main statements

* `Ratpoints.Sturm.hornerValue_eq_eval`, `Ratpoints.Sturm.run_evalSign_eq_sign_eval`: the value and
  the sign of a row at a dyadic number.
* `Ratpoints.Sturm.signCount_eq_signVariations`, `Ratpoints.Sturm.count_eq_signVariations`,
  `Ratpoints.Sturm.run_signsAt_eq_signVariations`: the count of the signs at a midpoint.
* `Ratpoints.Sturm.countP_ne_eq_signVariations`,
  `Ratpoints.Sturm.run_countsAtInfinity_eq_signVariations`: the counts at `±∞`.
-/

@[expose] public section

namespace Ratpoints

namespace Sturm

open Polynomial

/-- The Horner value after `j` steps, `∑ c_(deg - i) n ^ (j - i) 2 ^ (e i)` over `i ≤ j`. -/
theorem hornerValue_eq_sum (row : Array ℤ) (n : ℤ) (e j : ℕ) :
    hornerValue row n e j =
      ∑ i ∈ Finset.range (j + 1), row[row.size - 1 - i]! * n ^ (j - i) * 2 ^ (e * i) := by
  induction j with
  | zero => simp [hornerValue]
  | succ j ih =>
    rw [hornerValue, ih, Finset.sum_range_succ _ (j + 1), Finset.sum_mul,
      show row.size - 2 - j = row.size - 1 - (j + 1) by lia, Nat.sub_self, pow_zero, mul_one]
    congr 1
    refine Finset.sum_congr rfl fun i hi ↦ ?_
    rw [show j + 1 - i = j - i + 1 by lia [Finset.mem_range.mp hi], pow_succ]
    ring

/-- The Horner value of `Ratpoints.Sturm.evalSign` is `2 ^ (e deg)` times the value of the
polynomial of the row at `n / 2 ^ e`. -/
theorem hornerValue_eq_eval (row : Array ℤ) (n : ℤ) (e : ℕ) (h : row.size ≠ 0) :
    (hornerValue row n e (row.size - 1) : ℚ) =
      2 ^ (e * (row.size - 1)) * (poly row.toList).eval ((n : ℚ) / 2 ^ e) := by
  rw [hornerValue_eq_sum, poly, eval_finsetSum, Finset.mul_sum, Array.length_toList,
    show row.size = row.size - 1 + 1 by lia, ← Finset.sum_range_reflect]
  push_cast
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have hi := Finset.mem_range.mp hi
  simp only [eval_mul, eval_C, eval_pow, eval_X]
  rw [List.getD_eq_getElem _ _ (by simp; lia), Array.getElem_toList, ← getElem!_pos row _ (by lia),
    div_pow, show e * (row.size - 1) = e * (row.size - 1 - i) + e * i by
      rw [← Nat.mul_add]; congr 1; lia, pow_add, ← pow_mul,
    show row.size - 1 - (row.size - 1 - i) = i by lia]
  field

/-- `Ratpoints.Sturm.evalSign` computes the sign of the value of the polynomial of the row at
`num / 2 ^ denexp`. -/
theorem run_evalSign_eq_sign_eval {row : Array ℤ} (h : row.size ≠ 0) (num : Int64) {denexp : Int64}
    (h0 : 0 ≤ denexp.toInt) (hd : denexp.toInt * row.size < 2 ^ 63) :
    Id.run (evalSign row num denexp) =
      (SignType.sign ((poly row.toList).eval ((num.toInt : ℚ) / 2 ^ denexp.toInt.toNat)) : ℤ) := by
  rw [run_evalSign num h0 hd, Int.sign_eq_sign, ← sign_intCast (α := ℚ),
    hornerValue_eq_eval _ _ _ h, sign_mul, sign_pos (by positivity), one_mul]

/-- The sign changes that `Ratpoints.Sturm.signsAt` counts after a sign `s ≠ 0` in a list of signs
are the sign variations of `s` followed by the list. -/
theorem signCount_eq_signVariations {s : ℤ} (hs : s = -1 ∨ s = 1) {l : List ℤ}
    (hl : ∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1) : signCount s l = (s :: l).signVariations := by
  induction l generalizing s with
  | nil => simp [signCount]
  | cons t l ih =>
    have hl' : ∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1 := fun t ht ↦ hl t (by simp [ht])
    rcases hl t (by simp) with rfl | rfl | rfl <;> rcases hs with rfl | rfl <;>
      simp [signCount, ih (.inl rfl) hl', ih (.inr rfl) hl',
        List.signVariations_cons_cons_of_ne_zero]

/-- The count of `Ratpoints.Sturm.signsAt` from the signs `s0` and `s1` of `f` and `f'`, not both
zero, and the signs of the further rows: the sign variations of all of them. -/
theorem count_eq_signVariations {s0 s1 : ℤ} (h0 : s0 = -1 ∨ s0 = 0 ∨ s0 = 1)
    (h1 : s1 = -1 ∨ s1 = 0 ∨ s1 = 1) (h01 : s0 ≠ 0 ∨ s1 ≠ 0) {l : List ℤ}
    (hl : ∀ t ∈ l, t = -1 ∨ t = 0 ∨ t = 1) :
    (if s0 * s1 = -1 then 1 else 0) + signCount (if s1 = 0 then s0 else s1) l =
      (s0 :: s1 :: l).signVariations := by
  rcases h0 with rfl | rfl | rfl <;> rcases h1 with rfl | rfl | rfl <;>
    simp_all [signCount_eq_signVariations, List.signVariations_cons_cons_of_ne_zero, add_comm]

/-- The number of neighbours that differ in a sequence of nonzero signs is its number of sign
variations. -/
theorem countP_ne_eq_signVariations (s : ℕ → ℤ) {k : ℕ} (hs : ∀ n ≤ k, s n = -1 ∨ s n = 1) :
    (List.range k).countP (fun n ↦ s n != s (n + 1)) =
      ((List.range (k + 1)).map s).signVariations := by
  induction k generalizing s with
  | zero => simp
  | succ k ih =>
    have ih' := ih (fun n ↦ s (n + 1)) fun n hn ↦ hs (n + 1) (by lia)
    have hR (t : ℕ → ℤ) (m : ℕ) : (List.range (m + 1)).map t =
        t 0 :: (List.range m).map fun n ↦ t (n + 1) := by
      rw [List.range_succ_eq_map, List.map_cons, List.map_map]; rfl
    have hL : (List.range (k + 1)).countP (fun n ↦ s n != s (n + 1)) =
        (List.range k).countP (fun n ↦ s (n + 1) != s (n + 1 + 1)) +
          if s 0 != s 1 then 1 else 0 := by
      rw [List.range_succ_eq_map, List.countP_cons, List.countP_map]; rfl
    rw [hL, ih', hR s (k + 1), hR (fun n ↦ s (n + 1)) k,
      List.signVariations_cons_cons_of_ne_zero]
    · rcases hs 0 (by lia) with h0 | h0 <;> rcases hs 1 (by lia) with h1 | h1 <;> simp [h0, h1]
    · rcases hs 0 (by lia) with h0 | h0 <;> simp [h0]
    · rcases hs 1 (by lia) with h1 | h1 <;> simp [h1]

/-- The counts of `Ratpoints.Sturm.countsAtInfinity` for rows with nonzero leading coefficients:
the sign variations of the signs of the rows `0, …, k` at `+∞` and at `-∞`. -/
theorem run_countsAtInfinity_eq_signVariations {rows : Array (Array ℤ)} {k : ℕ}
    (h : ∀ n ≤ k, rows[n]!.back! ≠ 0) :
    Id.run (countsAtInfinity rows k) = (((List.range (k + 1)).map (signAtTop rows)).signVariations,
      ((List.range (k + 1)).map (signAtBot rows)).signVariations) := by
  have ht (n : ℕ) (hn : n ≤ k) : signAtTop rows n = -1 ∨ signAtTop rows n = 1 := by
    have := h n hn
    rw [Array.back!_eq_getElem!] at this
    rcases Int.lt_or_gt_of_ne this with h' | h'
    · exact .inl (Int.sign_eq_neg_one_of_neg h')
    · exact .inr (Int.sign_eq_one_of_pos h')
  have hb (n : ℕ) (hn : n ≤ k) : signAtBot rows n = -1 ∨ signAtBot rows n = 1 := by
    simp only [signAtBot]; rcases ht n hn with h' | h' <;> split_ifs <;> simp [h']
  rw [run_countsAtInfinity, countP_ne_eq_signVariations _ ht, countP_ne_eq_signVariations _ hb]

/-- `Ratpoints.Sturm.evalSign` returns a sign. -/
theorem run_evalSign_eq_neg_one_or_eq_zero_or_eq_one (row : Array ℤ) (num denexp : Int64) :
    Id.run (evalSign row num denexp) = -1 ∨ Id.run (evalSign row num denexp) = 0 ∨
      Id.run (evalSign row num denexp) = 1 := by
  simp only [evalSign, Id.run_bind, Id.run_pure]
  exact (Int.sign_trichotomy _).elim (.inr ∘ .inr) (·.elim (.inr ∘ .inl) .inl)

/-- The count of `Ratpoints.Sturm.signsAt` at a point where `f` and `f'` do not both vanish is the
number of sign variations of the signs of the rows `0, …, k` of the chain there. -/
theorem run_signsAt_eq_signVariations {rows : Array (Array ℤ)} {k : ℕ} (hk : 1 ≤ k)
    {nm dem : Int64}
    (h01 : Id.run (evalSign rows[0]! nm dem) ≠ 0 ∨ Id.run (evalSign rows[1]! nm dem) ≠ 0) :
    Id.run (signsAt rows k nm dem) = (Id.run (evalSign rows[0]! nm dem),
      Id.run (evalSign rows[1]! nm dem),
      ((List.range (k + 1)).map fun n ↦ Id.run (evalSign rows[n]! nm dem)).signVariations) := by
  have hl : (List.range (k + 1)).map (fun n ↦ Id.run (evalSign rows[n]! nm dem)) =
      Id.run (evalSign rows[0]! nm dem) :: Id.run (evalSign rows[1]! nm dem) ::
        (List.range' 2 (k - 1)).map fun n ↦ Id.run (evalSign rows[n]! nm dem) := by
    rw [show k + 1 = k - 1 + 1 + 1 by lia, List.range_eq_range', List.range'_succ,
      List.range'_succ]
    rfl
  rw [run_signsAt, hl, count_eq_signVariations (run_evalSign_eq_neg_one_or_eq_zero_or_eq_one ..)
    (run_evalSign_eq_neg_one_or_eq_zero_or_eq_one ..) h01 fun t ht ↦ ?_]
  obtain ⟨n, -, rfl⟩ := List.mem_map.mp ht
  exact run_evalSign_eq_neg_one_or_eq_zero_or_eq_one ..

end Sturm

end Ratpoints

end
