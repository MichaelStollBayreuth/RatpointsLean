/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Basic.Sign.Defs
public import Mathlib.Topology.Algebra.Order.Polynomial

/-!
# The signs of a polynomial near infinity

Candidates for `Mathlib.Topology.Algebra.Order.Polynomial`: over a linearly ordered field, a nonzero
polynomial has, far right, the sign of its leading coefficient and, far left, that sign times
`(-1) ^ deg` (`Polynomial.eventually_atTop_sign_eval`, `Polynomial.eventually_atBot_sign_eval`).

## Implementation notes

The file imports its sibling `Mathlib.Topology.Algebra.Order.Polynomial`, with the limits of
polynomials at infinity, and, publicly, `Mathlib.Basic.Sign.Defs`, since the statements name
`SignType.sign` and the sibling's public imports lack it.
-/

@[expose] public section

open Filter

namespace Polynomial

variable {𝕜 : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]

/-- Far right, a nonzero polynomial has the sign of its leading coefficient. -/
theorem eventually_atTop_sign_eval {p : 𝕜[X]} (hp : p ≠ 0) :
    ∀ᶠ x in atTop, SignType.sign (p.eval x) = SignType.sign p.leadingCoeff := by
  by_cases hd : p.degree ≤ 0
  · rw [eq_C_of_degree_le_zero hd]
    simp
  have hd' : 0 < p.degree := not_le.mp hd
  rcases (leadingCoeff_ne_zero.mpr hp).lt_or_gt with hlt | hgt
  · filter_upwards [(tendsto_atBot_of_leadingCoeff_nonpos hd' hlt.le).eventually_lt_atBot 0]
      with x hx
    rw [sign_neg hx, sign_neg hlt]
  · filter_upwards [(tendsto_atTop_of_leadingCoeff_nonneg hd' hgt.le).eventually_gt_atTop 0]
      with x hx
    rw [sign_pos hx, sign_pos hgt]

/-- Far left, a nonzero polynomial has the sign of `(-1) ^ deg` times its leading coefficient. -/
theorem eventually_atBot_sign_eval {p : 𝕜[X]} (hp : p ≠ 0) :
    ∀ᶠ x in atBot, SignType.sign (p.eval x) =
      SignType.sign ((-1) ^ p.natDegree * p.leadingCoeff) := by
  have h := eventually_atTop_sign_eval (p := p.comp (-X)) (comp_neg_X_eq_zero_iff.not.mpr hp)
  rw [comp_neg_X_leadingCoeff_eq] at h
  filter_upwards [tendsto_neg_atBot_atTop.eventually h] with x hx
  simpa [eval_comp] using hx

end Polynomial

end
