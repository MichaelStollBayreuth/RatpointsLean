/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Algebra.Polynomial.Homogenize
public import Mathlib.Algebra.Squarefree.Basic
public import Ratpoints.Proof.Sturm
public import Ratpoints.Spec.Basic

import Mathlib.Data.List.DropRight
import Mathlib.Data.List.GetD
import Mathlib.FieldTheory.Perfect
import Ratpoints.Mathlib.Algebra.Polynomial.Homogenize
import Ratpoints.Mathlib.RingTheory.Coprime.Basic
import Ratpoints.Proof.Bits

/-!
# The set-up of a search: the polynomial of a coefficient list and the remainder chain

The C code works with the polynomial `f = ∑ cᵢ Xⁱ` of the coefficient list `c` and its degree
`d`, the refusals speak about the binary form `Φ_c` of degree `N = 2 ⌈n / 2⌉`
(`Ratpoints.binaryFormPoly`), where `n + 1` is the length of `c`. `Φ_c` is the homogenization of
`f` of degree `N`, so it is squarefree exactly when `f` is squarefree and `N ≤ d + 1`: the two
conditions that the C code tests, the second when it drops the leading zeros, the first with the
remainder chain of its Sturm step. The rows of the chain, as polynomials over `ℚ`, form a
generalized Sturm sequence, along which the coprimality of `f` and `f'` passes down to the last two
rows, so that the chain detects a repeated factor of `f`.

## Main definitions

* `Ratpoints.poly`: the polynomial `f = ∑ cᵢ Xⁱ` over `ℚ` of a coefficient list `c`.

## Main statements

* `Ratpoints.getD_degree_ne_zero_of_pos`, `Ratpoints.natDegree_poly`: the entry of `c` at a
  positive degree is not zero, and the degree of `f` is `Ratpoints.degree c`.
* `Ratpoints.poly_take_of_degree_lt`: the entries of `c` above its degree do not change `f`.
* `Ratpoints.binaryFormPoly_eq_homogenize`: `Φ_c` is the homogenization of `f` of degree `N`.
* `Ratpoints.squarefree_binaryFormPoly_iff`: `Φ_c` is squarefree if and only if `f` is squarefree
  and `N ≤ d + 1`.
* `Ratpoints.not_squarefree_binaryFormPoly_of_lt`,
  `Ratpoints.not_squarefree_binaryFormPoly_of_getD_zero`: a drop of `⌈n / 2⌉` by the leading
  zeros, and `c₀ = c₁ = 0`, leave a form that is not squarefree.
* `Ratpoints.Sturm.IsChain.exists_mul_eq`, `Ratpoints.Sturm.IsChain.natDegree_lt`: three
  consecutive rows `s_k`, `s_(k+1)`, `s_(k+2)` of a remainder chain satisfy
  `A s_k = Q s_(k+1) - g s_(k+2)` with integers `A, g > 0`, and the degrees decrease from `f'` on.
* `Ratpoints.Sturm.run_chain_eq_none_iff`: for `d ≥ 1` and `c_d ≠ 0`, the remainder chain of the
  model is `none` exactly when the polynomial of `c₀, …, c_d` is not squarefree.
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

/-- The entries of `c` above its degree are zero, so dropping them does not change the polynomial
`Ratpoints.poly c`; with `n = d + 1` for the degree `d` of `c`, this turns the polynomial of
`Ratpoints.Sturm.run_chain_eq_none_iff` into `Ratpoints.poly c`. -/
theorem poly_take_of_degree_lt {c : List ℤ} {n : ℕ} (h : degree c < n) :
    poly (c.take n) = poly c := by
  ext i
  simp only [coeff_poly, List.getD_eq_getElem?_getD, List.getElem?_take]
  split_ifs with hi
  · rfl
  · rw [← List.getD_eq_getElem?_getD, getD_eq_zero_of_degree_lt (by lia)]
    simp

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

/-! ### The polynomial of an array -/

theorem coeff_poly_toList (a : Array ℤ) (i : ℕ) : (poly a.toList).coeff i = a[i]! := by
  simp [Array.getElem!_eq_getD]

theorem natDegree_poly_toList {a : Array ℤ} (h : a.back! ≠ 0) :
    (poly a.toList).natDegree = a.size - 1 := by
  have := Array.size_ne_zero_of_back!_ne h
  refine natDegree_eq_of_le_of_coeff_ne_zero (natDegree_le_iff_coeff_eq_zero.mpr fun i hi ↦ ?_) ?_
  · rw [coeff_poly_toList, getElem!_neg a i (by lia)]
    simp
  · rw [coeff_poly_toList, ← Array.back!_eq_getElem!]
    exact Int.cast_ne_zero.mpr h

private theorem poly_toList_eq_zero_of_size_eq_zero {a : Array ℤ} (h : a.size = 0) :
    poly a.toList = 0 := by
  simp [poly, h]

-- The scaled subtraction of a reduction step, from its coefficients.
private theorem poly_toList_eq_C_mul_sub_C_mul_X_pow_mul {t a b : Array ℤ} {w v : ℤ} {e : ℕ}
    (h : ∀ i, t[i]! = w * a[i]! - v * if e ≤ i then b[i - e]! else 0) :
    poly t.toList = C (w : ℚ) * poly a.toList - C (v : ℚ) * X ^ e * poly b.toList :=
  Polynomial.ext fun i ↦ by
    rw [coeff_poly_toList, h, coeff_sub, coeff_C_mul, mul_assoc, coeff_C_mul, coeff_X_pow_mul',
      coeff_poly_toList, coeff_poly_toList]
    split_ifs <;> simp

-- A constant other than `0` is coprime to every polynomial.
private theorem isCoprime_poly_toList_of_size_eq_one {a : Array ℤ} (h1 : a.size = 1)
    (h : a.back! ≠ 0) (p : ℚ[X]) : IsCoprime p (poly a.toList) := by
  rw [eq_C_of_natDegree_eq_zero (p := poly a.toList) (by rw [natDegree_poly_toList h, h1]),
    coeff_poly_toList]
  rw [Array.back!_eq_getElem!, h1] at h
  exact isCoprime_one_right.of_isCoprime_of_dvd_right
    (isUnit_C.mpr (Int.cast_ne_zero.mpr h).isUnit).dvd

namespace Sturm

/-! ### The steps of the chain as polynomials -/

private theorem exists_poly_reduceOnce {s t : Array ℤ} (hle : s.size ≤ t.size)
    (hs : s.back! ≠ 0) :
    ∃ u v : ℤ, 0 < u ∧ poly (reduceOnce s t).toList =
      C (u : ℚ) * poly t.toList - C (v : ℚ) * X ^ (t.size - s.size) * poly s.toList := by
  obtain ⟨u, v, hu, h⟩ := exists_getElem!_reduceOnce hle hs
  exact ⟨u, v, hu, poly_toList_eq_C_mul_sub_C_mul_X_pow_mul h⟩

-- The full reduction of `t` by `s` is `A t - Q s` with an integer `A > 0`.
private theorem exists_poly_fullReduce {s : Array ℤ} (hs : s.back! ≠ 0) (t : Array ℤ) :
    ∃ A : ℤ, 0 < A ∧ ∃ Q : ℚ[X],
      poly (fullReduce s t).toList = C (A : ℚ) * poly t.toList - Q * poly s.toList := by
  fun_induction fullReduce s t with
  | case1 t hle h0 =>
    obtain ⟨u, v, hu, h⟩ := exists_poly_reduceOnce hle hs
    rw [poly_toList_eq_zero_of_size_eq_zero h0] at h
    exact ⟨u, hu, C (v : ℚ) * X ^ (t.size - s.size), by
      rw [poly_toList_eq_zero_of_size_eq_zero rfl, h]⟩
  | case2 t hle h0 ih =>
    obtain ⟨A, hA, Q, hQ⟩ := ih
    obtain ⟨u, v, hu, h⟩ := exists_poly_reduceOnce hle hs
    refine ⟨A * u, Int.mul_pos hA hu, C (A : ℚ) * C (v : ℚ) * X ^ (t.size - s.size) + Q, ?_⟩
    rw [hQ, h, Int.cast_mul, C_mul]
    ring
  | case3 t => exact ⟨1, Int.one_pos, 0, by simp⟩

-- `g` times the normalized remainder is `-t`, for the gcd `g` of the entries of `-t`.
private theorem mul_poly_normalize (t : Array ℤ) :
    C ((content (t.map Neg.neg) : ℤ) : ℚ) * poly (normalize t).toList = -poly t.toList :=
  Polynomial.ext fun i ↦ by
    rw [coeff_C_mul, coeff_poly_toList, coeff_neg, coeff_poly_toList, ← Int.cast_mul,
      mul_getElem!_normalize, Int.cast_neg]

-- A full reduction that leaves nothing: `s`, not constant, divides `t`.
private theorem not_isCoprime_of_fullReduce_eq_empty {s t : Array ℤ} (hs : s.back! ≠ 0)
    (h2 : 2 ≤ s.size) (h : fullReduce s t = #[]) :
    ¬ IsCoprime (poly t.toList) (poly s.toList) := fun hc ↦ by
  obtain ⟨A, hA, Q, hQ⟩ := exists_poly_fullReduce hs t
  rw [h, poly_toList_eq_zero_of_size_eq_zero rfl, eq_comm, sub_eq_zero] at hQ
  have hu := hc.isUnit_of_dvd' ((isUnit_C.mpr (Int.cast_ne_zero.mpr hA.ne').isUnit).dvd_mul_left.mp
    ⟨Q, by rw [hQ, mul_comm]⟩) dvd_rfl
  have := natDegree_eq_zero_of_isUnit hu
  rw [natDegree_poly_toList hs] at this
  lia

/-! ### Remainder chains -/

theorem IsChain.poly_getElem!_zero {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) : poly ch[0]!.toList = poly (c.take (d + 1)) :=
  Polynomial.ext fun i ↦ by
    rw [coeff_poly_toList, h.getElem!_zero, coeff_poly, List.getD_eq_getElem?_getD,
      List.getElem?_take]
    split_ifs with hi
    · rw [Array.getElem!_map_range _ hi, List.getD_eq_getElem?_getD]
    · rw [getElem!_neg _ i (by simpa using hi)]
      simp

theorem IsChain.poly_getElem!_one {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) : poly ch[1]!.toList = derivative (poly ch[0]!.toList) :=
  Polynomial.ext fun n ↦ by
    rw [coeff_derivative, coeff_poly_toList, coeff_poly_toList, h.getElem!_zero, h.getElem!_one]
    by_cases hn : n < d
    · rw [Array.getElem!_map_range _ hn, Array.getElem!_map_range _ (by lia)]
      push_cast
      ring
    · rw [getElem!_neg _ n (by simpa using hn), getElem!_neg _ (n + 1) (by simpa using hn)]
      simp

/-- Three consecutive rows `s_k`, `s_(k+1)`, `s_(k+2)` of a remainder chain satisfy
`A s_k = Q s_(k+1) - g s_(k+2)` with integers `A, g > 0`, the relation of a generalized Sturm
sequence. -/
theorem IsChain.exists_mul_eq {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)} (h : IsChain c d ch)
    {k : ℕ} (hk : k + 2 < ch.size) :
    ∃ A g : ℤ, 0 < A ∧ 0 < g ∧ ∃ Q : ℚ[X], C (A : ℚ) * poly ch[k]!.toList =
      Q * poly ch[k + 1]!.toList - C (g : ℚ) * poly ch[k + 2]!.toList := by
  obtain ⟨A, hA, Q, hQ⟩ := exists_poly_fullReduce (h.back!_ne_zero (k + 1) (by lia)) ch[k]!
  have h2 := h.back!_ne_zero (k + 2) hk
  rw [h.getElem!_add_two k hk] at h2 ⊢
  refine ⟨A, _, hA, Int.natCast_pos.mpr (Nat.pos_of_ne_zero (content_map_neg_ne_zero h2)), Q, ?_⟩
  rw [mul_poly_normalize, hQ]
  ring

theorem IsChain.natDegree_lt {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)} (h : IsChain c d ch)
    {k : ℕ} (hk : k + 2 < ch.size) :
    (poly ch[k + 2]!.toList).natDegree < (poly ch[k + 1]!.toList).natDegree := by
  rw [natDegree_poly_toList (h.back!_ne_zero _ hk),
    natDegree_poly_toList (h.back!_ne_zero _ (by lia))]
  have := h.size_lt k hk
  have := Array.size_ne_zero_of_back!_ne (h.back!_ne_zero _ hk)
  lia

-- Coprimality goes down a remainder chain.
private theorem IsChain.isCoprime_iff {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) {k : ℕ} (hk : k + 1 < ch.size) :
    IsCoprime (poly ch[k]!.toList) (poly ch[k + 1]!.toList) ↔
      IsCoprime (poly ch[0]!.toList) (poly ch[1]!.toList) := by
  induction k with
  | zero => rfl
  | succ k ih =>
    obtain ⟨A, g, hA, hg, Q, hQ⟩ := h.exists_mul_eq (k := k) hk
    rw [isCoprime_iff_of_mul_eq_mul_sub_mul (isUnit_C.mpr (Int.cast_ne_zero.mpr hA.ne').isUnit)
      (isUnit_C.mpr (Int.cast_ne_zero.mpr hg.ne').isUnit) hQ]
    exact ih (by lia)

private theorem IsChain.isCoprime_back!_iff {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) : IsCoprime (poly ch[ch.size - 2]!.toList) (poly ch.back!.toList) ↔
      IsCoprime (poly ch[0]!.toList) (poly ch[1]!.toList) := by
  have := h.two_le_size
  rw [Array.back!_eq_getElem!, show ch.size - 1 = ch.size - 2 + 1 by lia]
  exact h.isCoprime_iff (by lia)

private theorem IsChain.squarefree_iff {c : List ℤ} {d : ℕ} {ch : Array (Array ℤ)}
    (h : IsChain c d ch) :
    Squarefree (poly ch[0]!.toList) ↔ IsCoprime (poly ch[0]!.toList) (poly ch[1]!.toList) := by
  rw [h.poly_getElem!_one]
  exact PerfectField.separable_iff_squarefree.symm

/-- For the coefficients `c₀, …, c_d` of a polynomial `f` of degree `d ≥ 1`, the remainder chain is
`none`, where `sturm.c` returns `-1`, exactly when `f` is not squarefree over `ℚ`; for the degree
`d` of `c`, `f` is `Ratpoints.poly c` (`Ratpoints.poly_take_of_degree_lt`). -/
theorem run_chain_eq_none_iff {c : List ℤ} {d : ℕ} (hd : 1 ≤ d) (hc : c.getD d 0 ≠ 0) :
    Id.run (chain c d) = none ↔ ¬ Squarefree (poly (c.take (d + 1))) := by
  have hres := isChainResult_run_chain hd hc
  generalize Id.run (chain c d) = res at hres ⊢
  cases res with
  | none =>
    obtain ⟨ch, h, h2, h0⟩ := hres
    rw [← h.poly_getElem!_zero, h.squarefree_iff, ← h.isCoprime_back!_iff]
    exact iff_of_true rfl (not_isCoprime_of_fullReduce_eq_empty
      (h.back!_ne_zero _ (by have := h.two_le_size; lia)) h2 h0)
  | some ch =>
    obtain ⟨h, h1⟩ := hres
    rw [← h.poly_getElem!_zero, h.squarefree_iff, ← h.isCoprime_back!_iff]
    exact iff_of_false (Option.some_ne_none ch) (not_not.mpr (isCoprime_poly_toList_of_size_eq_one
      h1 (h.back!_ne_zero _ (by have := h.two_le_size; lia)) _))

end Sturm

end Ratpoints

end
