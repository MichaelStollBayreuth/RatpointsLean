/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Basic

/-!
# Residues of integers and squares in `ZMod n`

Candidates for `Mathlib.Data.ZMod.Basic`: the cast to `ZMod n` of the least non-negative residue
of an integer (`ZMod.natCast_toNat_emod`, which is `ZMod.natCast_toNat` without its hypothesis
`0 ≤ z`), and a residue that is a square in `ZMod n` as the residue of the square of a natural
number below `n` (`ZMod.exists_eq_mul_self_mod_of_isSquare`), and for odd `n` and a residue other
than `0` as that of the square of a number from `1` to `n / 2`
(`ZMod.isSquare_natCast_iff_exists_mul_self_mod_eq`).
-/

@[expose] public section

namespace ZMod

/-- The cast to `ZMod n` of the least non-negative residue of `a` modulo `n` is the cast of `a`;
`ZMod.natCast_toNat` without its hypothesis `0 ≤ z`. -/
theorem natCast_toNat_emod {n : ℕ} [NeZero n] (a : ℤ) : ((a % n).toNat : ZMod n) = a := by
  rw [natCast_toNat _ (Int.emod_nonneg _ (mod_cast NeZero.ne n)), intCast_mod]

/-- A residue `v < n` that is a square in `ZMod n` is the residue of the square of a natural number
below `n`. -/
theorem exists_eq_mul_self_mod_of_isSquare {n v : ℕ} [NeZero n] (hv : v < n)
    (h : IsSquare (v : ZMod n)) : ∃ s < n, v = s * s % n := by
  obtain ⟨z, hz⟩ := h
  refine ⟨z.val, z.val_lt, ?_⟩
  rw [← Nat.mod_eq_of_lt hv, ← natCast_eq_natCast_iff', hz, Nat.cast_mul, natCast_zmod_val]

/-- Modulo an odd `n`, a residue `0 < v < n` is a square exactly when it is the square of one of
`1, …, n / 2`, since `x` and `n - x` have the same square. -/
theorem isSquare_natCast_iff_exists_mul_self_mod_eq {n v : ℕ} [NeZero n] (hn : n % 2 = 1)
    (hv0 : v ≠ 0) (hv : v < n) :
    IsSquare (v : ZMod n) ↔ ∃ x, 1 ≤ x ∧ x ≤ n / 2 ∧ x * x % n = v := by
  refine ⟨fun h ↦ ?_, fun ⟨x, _, _, hx⟩ ↦ ⟨x, by rw [← hx, natCast_mod, Nat.cast_mul]⟩⟩
  obtain ⟨s, hs, rfl⟩ := exists_eq_mul_self_mod_of_isSquare hv h
  have hs0 : s ≠ 0 := by rintro rfl; simp at hv0
  rcases Nat.lt_or_ge (n / 2) s with h2 | h2
  · refine ⟨n - s, by lia, by lia, ?_⟩
    rw [← natCast_eq_natCast_iff', Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hs.le, natCast_self,
      zero_sub, neg_mul_neg]
  · exact ⟨s, by lia, h2, rfl⟩

end ZMod

end
