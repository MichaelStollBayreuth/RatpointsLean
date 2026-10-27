/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Rat.Floor

/-!
# The ceiling of a quotient, and of small rationals

Candidates for `Mathlib.Data.Rat.Floor`: the ceiling of `n / d` for an integer `n` and a positive
natural number `d` is `(n + d - 1) / d` (`Rat.ceil_intCast_div_natCast_eq_add_sub_one_div`), the
form next to `Rat.ceil_intCast_div_natCast` that rounds up by the integer division; and two
nonzero rationals strictly between `-1` and `1` of the same sign have the same ceiling and the same
floor (`Rat.ceil_eq_and_floor_eq_of_abs_lt_one`).

## Main statements

* `Rat.ceil_intCast_div_natCast_eq_add_sub_one_div`: `⌈n / d⌉ = (n + d - 1) / d` for `d > 0`.
* `Rat.ceil_eq_and_floor_eq_of_abs_lt_one`: the ceilings and the floors of two nonzero rationals of
  the same sign strictly between `-1` and `1`.
-/

@[expose] public section

namespace Rat

/-- The ceiling of `n / d` for `d > 0` by the integer division, rounded up: `(n + d - 1) / d`, where
`Rat.ceil_intCast_div_natCast` has `-((-n) / d)` for every `d`. -/
theorem ceil_intCast_div_natCast_eq_add_sub_one_div (n : ℤ) {d : ℕ} (hd : 0 < d) :
    ⌈(n : ℚ) / d⌉ = (n + d - 1) / d := by
  have h : (0 : ℤ) < d := mod_cast hd
  have h' : (0 : ℚ) < d := mod_cast hd
  refine le_antisymm (Int.ceil_le.mpr ?_) ?_
  · rw [div_le_iff₀ h']
    have := Int.lt_ediv_add_one_mul_self (n + d - 1) h
    exact_mod_cast (by lia : n ≤ (n + d - 1) / d * d)
  · have := Int.le_ceil ((n : ℚ) / d)
    rw [div_le_iff₀ h'] at this
    have h3 : n ≤ ⌈(n : ℚ) / d⌉ * d := mod_cast this
    exact Int.lt_add_one_iff.mp ((Int.ediv_lt_iff_lt_mul h).mpr (by lia))

/-- Two nonzero rationals of the same sign strictly between `-1` and `1` have the same ceiling and
the same floor: `1` and `0` when positive, `0` and `-1` when negative. -/
theorem ceil_eq_and_floor_eq_of_abs_lt_one {p p' : ℚ} (hp : p ≠ 0) (hp1 : |p| < 1) (hp' : p' ≠ 0)
    (hp1' : |p'| < 1) (hs : p < 0 ↔ p' < 0) : ⌈p⌉ = ⌈p'⌉ ∧ ⌊p⌋ = ⌊p'⌋ := by
  rw [abs_lt] at hp1 hp1'
  rcases lt_or_gt_of_ne hp with h | h
  · have h' := hs.mp h
    have e1 : ⌊p⌋ = -1 := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    have e2 : ⌊p'⌋ = -1 := Int.floor_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    exact ⟨(Int.ceil_eq_zero_iff.mpr ⟨hp1.1, h.le⟩).trans
      (Int.ceil_eq_zero_iff.mpr ⟨hp1'.1, h'.le⟩).symm, e1.trans e2.symm⟩
  · have h' : 0 < p' := lt_of_le_of_ne (not_lt.mp (mt hs.mpr h.not_gt)) (Ne.symm hp')
    have e1 : ⌈p⌉ = 1 := Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    have e2 : ⌈p'⌉ = 1 := Int.ceil_eq_iff.mpr ⟨by push_cast; linarith, by push_cast; linarith⟩
    exact ⟨e1.trans e2.symm, (Int.floor_eq_zero_iff.mpr ⟨h.le, hp1.2⟩).trans
      (Int.floor_eq_zero_iff.mpr ⟨h'.le, hp1'.2⟩).symm⟩

end Rat

end
