/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Polynomial.Derivative
public import Mathlib.Analysis.Polynomial.Order

import Mathlib.Topology.Algebra.Polynomial
import Ratpoints.Mathlib.Algebra.Polynomial.FieldDivision

/-!
# The signs of a polynomial near a point

Candidates for `Mathlib.Analysis.Polynomial.Order`: over a linearly ordered normed field with the
order topology, such as `ℝ`, a polynomial keeps a nonzero sign near a point
(`Polynomial.eventually_sign_eval_eq`), near a root `x` where its derivative does not vanish it has
the sign of `(y - x) p'(x)` at `y` (`Polynomial.eventually_sign_eval_eq_sign_sub_mul`), and just
right of a point `x` where it or its derivative does not vanish it has the sign of `p(x)`, or of
`p'(x)` when `p(x) = 0`, and just left of `x` that of `p(x)`, or of `-p'(x)` when `p(x) = 0`
(`Polynomial.eventually_sign_eval_nhdsGT`, `Polynomial.eventually_sign_eval_nhdsLT`). By the
intermediate value theorem, opposite signs of a real polynomial at two points give a root between
them (`Polynomial.exists_isRoot_of_eval_mul_eval_neg`), a negative sign just right of the left end
of an interval without a root holds on the whole interval
(`Polynomial.eval_neg_of_forall_not_isRoot`), and a nonzero real polynomial of degree `n` changes
its sign at most `n` times along increasing points
(`Polynomial.length_le_natDegree_add_one_of_isChain`).

## Implementation notes

The file imports its sibling `Mathlib.Analysis.Polynomial.Order`, the sibling's private import
`Mathlib.Topology.Algebra.Polynomial` for the continuity of polynomials, and, publicly,
`Mathlib.Algebra.Polynomial.Derivative`, which the statements just right and just left of a point
name and the sibling's public imports lack.

The lemmas that rest on the intermediate value theorem are stated over `ℝ`, as the sibling's are:
they need a conditionally complete, densely ordered field.

The signs just right and just left of a point are stated by the case distinction on `p(x) = 0`,
without a definition of their own; compare `Polynomial.signRight` of
`Mathlib.Analysis.Polynomial.SignRight`, the sign just right of a point as a limit, over `ℝ` and for
every `p`, with `Polynomial.signRight_of_eval_ne_zero` and `Polynomial.signRight_of_eval_eq_zero`;
the statements here hold over every linearly ordered normed field with the order topology and on
both sides of the point.
-/

@[expose] public section

open Filter Topology

namespace Polynomial

section OrderTopology

variable {𝕜 : Type*} [NormedField 𝕜] [LinearOrder 𝕜] [OrderTopology 𝕜]

/-- Near a point where it does not vanish, a polynomial keeps its sign. -/
theorem eventually_sign_eval_eq {p : 𝕜[X]} {x : 𝕜} (h : p.eval x ≠ 0) :
    ∀ᶠ y in 𝓝 x, SignType.sign (p.eval y) = SignType.sign (p.eval x) := by
  rcases h.lt_or_gt with hlt | hgt
  · filter_upwards [p.continuous.continuousAt.eventually_lt continuousAt_const hlt] with y hy
    rw [sign_neg hy, sign_neg hlt]
  · filter_upwards [continuousAt_const.eventually_lt p.continuous.continuousAt hgt] with y hy
    rw [sign_pos hy, sign_pos hgt]

variable [IsStrictOrderedRing 𝕜]

/-- Near a root `x` of `p` with `p'(x) ≠ 0`, `p(y)` has the sign of `(y - x) p'(x)`. -/
theorem eventually_sign_eval_eq_sign_sub_mul {p : 𝕜[X]} {x : 𝕜} (h0 : p.eval x = 0)
    (h : p.derivative.eval x ≠ 0) : ∀ᶠ y in 𝓝 x,
      SignType.sign (p.eval y) = SignType.sign (y - x) * SignType.sign (p.derivative.eval x) := by
  filter_upwards [eventually_sign_eval_eq (eval_divByMonic_X_sub_C p x ▸ h)] with y hy
  rw [← eval_divByMonic_X_sub_C, ← hy]
  nth_rw 1 [← mul_divByMonic_eq_iff_isRoot.mpr h0]
  simp [sign_mul]

/-- Just right of a point `x` where `p(x) ≠ 0` or `p'(x) ≠ 0`, a polynomial `p` has the sign of
`p(x)`, or of `p'(x)` when `p(x) = 0`. -/
theorem eventually_sign_eval_nhdsGT {p : 𝕜[X]} {x : 𝕜}
    (h : p.eval x ≠ 0 ∨ p.derivative.eval x ≠ 0) :
    ∀ᶠ y in 𝓝[>] x, SignType.sign (p.eval y) =
      if p.eval x = 0 then SignType.sign (p.derivative.eval x) else SignType.sign (p.eval x) := by
  split_ifs with h0
  · filter_upwards [nhdsWithin_le_nhds (eventually_sign_eval_eq_sign_sub_mul h0
      (h.resolve_left (not_not.mpr h0))), self_mem_nhdsWithin] with y hy hyx
    rw [hy, sign_pos (sub_pos.mpr (Set.mem_Ioi.mp hyx)), one_mul]
  · exact nhdsWithin_le_nhds (eventually_sign_eval_eq h0)

/-- Just left of a point `x` where `p(x) ≠ 0` or `p'(x) ≠ 0`, a polynomial `p` has the sign of
`p(x)`, or of `-p'(x)` when `p(x) = 0`. -/
theorem eventually_sign_eval_nhdsLT {p : 𝕜[X]} {x : 𝕜}
    (h : p.eval x ≠ 0 ∨ p.derivative.eval x ≠ 0) :
    ∀ᶠ y in 𝓝[<] x, SignType.sign (p.eval y) =
      if p.eval x = 0 then -SignType.sign (p.derivative.eval x) else SignType.sign (p.eval x) := by
  split_ifs with h0
  · filter_upwards [nhdsWithin_le_nhds (eventually_sign_eval_eq_sign_sub_mul h0
      (h.resolve_left (not_not.mpr h0))), self_mem_nhdsWithin] with y hy hyx
    rw [hy, sign_neg (sub_neg.mpr (Set.mem_Iio.mp hyx)), neg_one_mul]
  · exact nhdsWithin_le_nhds (eventually_sign_eval_eq h0)

end OrderTopology

/-- A real polynomial with values of opposite signs at `a < b` has a root strictly between. -/
theorem exists_isRoot_of_eval_mul_eval_neg {p : ℝ[X]} {a b : ℝ} (hab : a < b)
    (h : p.eval a * p.eval b < 0) : ∃ z ∈ Set.Ioo a b, p.IsRoot z := by
  rcases mul_neg_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · exact intermediate_value_Ioo' hab.le p.continuous.continuousOn ⟨hb, ha⟩
  · exact intermediate_value_Ioo hab.le p.continuous.continuousOn ⟨ha, hb⟩

/-- An interval `(l, r)` without a root of a real polynomial `p`, on which `p` is negative just
right of `l`, holds no `x` with `p(x) ≥ 0`. -/
theorem eval_neg_of_forall_not_isRoot {p : ℝ[X]} {l r : ℝ}
    (hroot : ∀ x, l < x → x < r → ¬ p.IsRoot x) (hneg : ∀ᶠ y in 𝓝[>] l, p.eval y < 0)
    {x : ℝ} (hlx : l < x) (hxr : x < r) : p.eval x < 0 := by
  by_contra! hx
  have hx' : 0 < p.eval x := lt_of_le_of_ne hx (Ne.symm (hroot x hlx hxr))
  obtain ⟨y, hy, hyl, hyx⟩ := (hneg.and (Ioo_mem_nhdsGT hlx)).exists
  obtain ⟨z, hz, hz0⟩ := exists_isRoot_of_eval_mul_eval_neg hyx (mul_neg_of_neg_of_pos hy hx')
  exact hroot z (hyl.trans hz.1) (hz.2.trans hxr) hz0

-- The roots of `p` in the gaps of a strictly increasing list of points at which the signs of `p`
-- alternate: one in each gap, all above the first point.
private theorem exists_roots_of_isChain {p : ℝ[X]} {l : List ℝ} {x : ℝ}
    (hl : (x :: l).IsChain fun a b ↦ a < b ∧ p.eval a * p.eval b < 0) :
    ∃ rs : List ℝ, rs.length = l.length ∧ rs.Nodup ∧ ∀ r ∈ rs, x < r ∧ p.IsRoot r := by
  induction l generalizing x with
  | nil => exact ⟨[], rfl, .nil, by simp⟩
  | cons y l ih =>
    rw [List.isChain_cons_cons] at hl
    obtain ⟨rs, hlen, hnd, hrs⟩ := ih hl.2
    obtain ⟨z, hz, hz0⟩ := exists_isRoot_of_eval_mul_eval_neg hl.1.1 hl.1.2
    refine ⟨z :: rs, by simp [hlen], .cons (fun hm ↦ lt_asymm hz.2 (hrs z hm).1) hnd, ?_⟩
    simp only [List.mem_cons, forall_eq_or_imp]
    exact ⟨⟨hz.1, hz0⟩, fun r hr ↦ ⟨hl.1.1.trans (hrs r hr).1, (hrs r hr).2⟩⟩

/-- A nonzero real polynomial `p` of degree `n` changes its sign at most `n` times along a strictly
increasing list of points. -/
theorem length_le_natDegree_add_one_of_isChain {p : ℝ[X]} (hp : p ≠ 0) {l : List ℝ}
    (hl : l.IsChain fun a b ↦ a < b ∧ p.eval a * p.eval b < 0) : l.length ≤ p.natDegree + 1 := by
  rcases l with _ | ⟨x, l⟩
  · simp
  obtain ⟨rs, hlen, hnd, hrs⟩ := exists_roots_of_isChain hl
  have h1 : rs.toFinset ⊆ p.roots.toFinset := fun r hr ↦ by
    simpa [mem_roots hp] using (hrs r (List.mem_toFinset.mp hr)).2
  have h2 := (Finset.card_le_card h1).trans (p.roots.toFinset_card_le.trans (card_roots' p))
  rw [List.toFinset_card_of_nodup hnd, hlen] at h2
  simpa using h2

end Polynomial

end
