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
number below `n` (`ZMod.exists_eq_mul_self_mod_of_isSquare`).
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

end ZMod

end
