/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Squarefree

/-!
# The squarefree part of a natural number is unique

A candidate for `Mathlib.Data.Nat.Squarefree`: `d k ^ 2 = d' k' ^ 2` with `d` and `d'` squarefree
and `k' ≠ 0` forces `d = d'`, the uniqueness that complements `Nat.sq_mul_squarefree_of_pos`.

## Main statements

* `Nat.eq_of_mul_sq_eq_mul_sq`: squarefree numbers times squares agree only for equal squarefree
  parts.
-/

@[expose] public section

namespace Nat

/-- **The squarefree part is unique**: `d k ^ 2 = d' k' ^ 2` with `d`, `d'` squarefree and
`k' ≠ 0` gives `d = d'`, since `d d'` is then a square
(`Squarefree.associated_of_isSquare_mul`). -/
theorem eq_of_mul_sq_eq_mul_sq {d d' k k' : ℕ} (hd : Squarefree d) (hd' : Squarefree d')
    (hk' : k' ≠ 0) (h : d * k ^ 2 = d' * k' ^ 2) : d = d' := by
  have hsq : IsSquare (d * d') := by
    obtain ⟨w, hw⟩ : k' ∣ d * k := (Nat.pow_dvd_pow_iff two_ne_zero).mp
      ⟨d * d', by rw [mul_pow, sq d, mul_assoc, h]; ring⟩
    refine ⟨w, Nat.eq_of_mul_eq_mul_right (pow_pos (Nat.pos_of_ne_zero hk') 2) ?_⟩
    calc d * d' * k' ^ 2 = d * (d * k ^ 2) := by rw [h]; ring
      _ = (d * k) ^ 2 := by ring
      _ = w * w * k' ^ 2 := by rw [hw]; ring
  exact associated_iff_eq.mp (hd.associated_of_isSquare_mul hd' hsq)

end Nat

end
