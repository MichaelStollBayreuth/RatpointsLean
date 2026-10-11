/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.Squarefree.Basic
public import Ratpoints.Spec.Basic

import Mathlib.Data.List.DropRight
import Mathlib.Data.List.GetD
import Ratpoints.Mathlib.Algebra.Polynomial.Homogenize

/-!
# The set-up of a search: the polynomial of a coefficient list

The C code works with the polynomial `f = ∑ cᵢ Xⁱ` of the coefficient list `c` and its degree
`d`, the refusals speak about the binary form `Φ_c` of degree `N = 2 ⌈n / 2⌉`
(`Ratpoints.binaryFormPoly`), where `n + 1` is the length of `c`. `Φ_c` is the homogenization of
`f` of degree `N`, so it is squarefree exactly when `f` is squarefree and `N ≤ d + 1`: the two
conditions that the C code tests, the second when it drops the leading zeros, the first with the
remainder chain of its Sturm step.

## Main definitions

* `Ratpoints.poly`: the polynomial `f = ∑ cᵢ Xⁱ` over `ℚ` of a coefficient list `c`.

## Main statements

* `Ratpoints.getD_degree_ne_zero_of_pos`, `Ratpoints.natDegree_poly`: the entry of `c` at a
  positive degree is not zero, and the degree of `f` is `Ratpoints.degree c`.
* `Ratpoints.binaryFormPoly_eq_homogenize`: `Φ_c` is the homogenization of `f` of degree `N`.
* `Ratpoints.squarefree_binaryFormPoly_iff`: `Φ_c` is squarefree if and only if `f` is squarefree
  and `N ≤ d + 1`.
* `Ratpoints.not_squarefree_binaryFormPoly_of_lt`,
  `Ratpoints.not_squarefree_binaryFormPoly_of_getD_zero`: a drop of `⌈n / 2⌉` by the leading
  zeros, and `c₀ = c₁ = 0`, leave a form that is not squarefree.
-/

@[expose] public section

namespace Ratpoints

open Polynomial

/-- The polynomial `f = ∑ cᵢ Xⁱ` over `ℚ` with the coefficient list `c`, constant term first, which
the C code works with; `Ratpoints.binaryFormPoly c` is its homogenization of degree `2 ⌈n / 2⌉`
(`Ratpoints.binaryFormPoly_eq_homogenize`). -/
noncomputable def poly (c : List ℤ) : ℚ[X] :=
  ∑ i ∈ Finset.range c.length, C (c.getD i 0 : ℚ) * X ^ i

@[simp]
theorem coeff_poly (c : List ℤ) (i : ℕ) : (poly c).coeff i = c.getD i 0 := by
  simp only [poly, finsetSum_coeff, coeff_C_mul_X_pow, Finset.sum_ite_eq, Finset.mem_range]
  split_ifs with h
  · rfl
  · rw [List.getD_eq_default _ _ (not_lt.mp h), Int.cast_zero]

theorem getD_degree_ne_zero_of_pos {c : List ℤ} (h : 0 < degree c) : c.getD (degree c) 0 ≠ 0 := by
  have hd : degree c = (c.rdropWhile (· == 0)).length - 1 := by simp [degree, List.rdropWhile]
  have hne : c.rdropWhile (· == 0) ≠ [] := fun h0 ↦ by simp [hd, h0] at h
  have hlt : degree c < (c.rdropWhile (· == 0)).length := by lia
  have hp := List.rdropWhile_prefix (· == 0) c
  rw [List.getD_eq_getElem _ _ (hlt.trans_le hp.length_le), ← hp.getElem hlt]
  simpa [hd, List.getLast_eq_getElem] using List.rdropWhile_last_not _ _ hne

theorem natDegree_poly (c : List ℤ) : (poly c).natDegree = degree c := by
  refine le_antisymm (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_) ?_
  · rw [coeff_poly, getD_eq_zero_of_degree_lt hi, Int.cast_zero]
  · rcases (degree c).eq_zero_or_pos with h | h
    · simp [h]
    · exact le_natDegree_of_ne_zero (by simpa using getD_degree_ne_zero_of_pos h)

theorem binaryFormPoly_eq_homogenize (c : List ℤ) :
    binaryFormPoly c = (poly c).homogenize (2 * (c.length / 2)) := by
  rw [binaryFormPoly, poly, homogenize_finsetSum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [homogenize_C_mul, homogenize_X_pow (by have := Finset.mem_range.mp hi; lia), mul_assoc]

/-- The binary form `Ratpoints.binaryFormPoly c` is squarefree exactly when the polynomial
`Ratpoints.poly c` is squarefree and the degree `2 ⌈n / 2⌉` of the form, `n + 1` the length of `c`,
exceeds the degree of the polynomial by at most one: the two conditions that the C code tests, the
second when it drops the leading zeros, the first with the remainder chain of its Sturm step. -/
theorem squarefree_binaryFormPoly_iff (c : List ℤ) :
    Squarefree (binaryFormPoly c) ↔ Squarefree (poly c) ∧ 2 * (c.length / 2) ≤ degree c + 1 := by
  have := degree_le_length_sub_one c
  rw [binaryFormPoly_eq_homogenize, squarefree_homogenize_iff (by rw [natDegree_poly]; lia),
    natDegree_poly]

/-- When the leading zeros of `c` lower `⌈n / 2⌉`, for `n + 1` the length of `c`, the square of the
second variable divides the binary form `Ratpoints.binaryFormPoly c`. -/
theorem not_squarefree_binaryFormPoly_of_lt {c : List ℤ} (h : (degree c + 1) / 2 < c.length / 2) :
    ¬ Squarefree (binaryFormPoly c) := by
  rw [squarefree_binaryFormPoly_iff]
  lia

/-- With `c₀ = c₁ = 0`, the square of the first variable divides the binary form
`Ratpoints.binaryFormPoly c`, whatever the degree, the zero polynomial included. -/
theorem not_squarefree_binaryFormPoly_of_getD_zero {c : List ℤ} (h0 : c.getD 0 0 = 0)
    (h1 : c.getD 1 0 = 0) : ¬ Squarefree (binaryFormPoly c) := by
  have hX : X ^ 2 ∣ poly c := X_pow_dvd_iff.mpr fun d hd ↦ by
    obtain rfl | rfl : d = 0 ∨ d = 1 := by lia
    · rw [coeff_poly, h0, Int.cast_zero]
    · rw [coeff_poly, h1, Int.cast_zero]
  rw [squarefree_binaryFormPoly_iff]
  exact fun h ↦ not_isUnit_X (h.1 X (by rwa [← sq]))

end Ratpoints

end
