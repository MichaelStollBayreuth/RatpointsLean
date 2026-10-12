/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Ring.Finset

/-!
# Divisibility of a sum with one exceptional term

A candidate for `Mathlib.Algebra.BigOperators.Ring.Finset`, next to `Finset.dvd_sum`: when `a`
divides every term of a sum but one, it divides the sum exactly when it divides that term.

## Main statements

* `Finset.dvd_sum_iff_of_dvd`: `a ∣ ∑ i ∈ s, f i ↔ a ∣ f j` when `a` divides every other term.
-/

@[expose] public section

namespace Finset

/-- When `a` divides every term of a sum but `f j`, it divides the sum exactly when it divides
`f j`; compare `Finset.dvd_sum`. -/
theorem dvd_sum_iff_of_dvd {ι R : Type*} [NonUnitalRing R] {s : Finset ι} {f : ι → R} {a : R}
    {j : ι} (hj : j ∈ s) (h : ∀ i ∈ s, i ≠ j → a ∣ f i) : a ∣ ∑ i ∈ s, f i ↔ a ∣ f j := by
  classical
  rw [← add_sum_erase s f hj, dvd_add_left (dvd_sum fun i hi ↦
    h i (mem_of_mem_erase hi) (ne_of_mem_erase hi))]

end Finset

end
