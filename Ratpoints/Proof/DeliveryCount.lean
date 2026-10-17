/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.BigOperators.Group.Finset.Defs
public import Mathlib.Data.Fintype.Basic
public import Ratpoints.Model.Delivery

import Mathlib.Algebra.BigOperators.Fin
import Ratpoints.Proof.Delivery

/-!
# The count of the delivery of a list of points

The count of the reference of the delivery of a search, `Ratpoints.Delivery.deliver`: the calls
that it makes are those of the points of a prefix of the list, before each of which the flag of
the stop is clear (`Ratpoints.Delivery.exists_prefix_deliver_eq`), and the count grows by the sum
of the values that these calls return.

## Main statements

* `Ratpoints.Delivery.total_deliver_eq_sum`,
  `Ratpoints.Delivery.exists_prefix_total_deliver_eq_sum`: on a prefix before each of whose points
  the flag is clear, and so for the delivery of every list, the count grows by the sum of the
  values that the calls return.
-/

@[expose] public section

namespace Ratpoints.Delivery

variable {σ : Type} (process : Int → Int → Int → σ → Answer σ)

/-- On a list before each of whose points the flag is clear, the count grows by the sum of the
values that the calls return, the call of the `k`-th point made on the delivery of the first `k`
points. -/
theorem total_deliver_eq_sum {r : Delivery σ} {M : List (Int × Int × Int)}
    (h : ∀ m < M.length, (r.deliver process (M.take m)).quit = false) :
    (r.deliver process M).total = r.total + ∑ k : Fin M.length,
      (process M[k].1 M[k].2.2 M[k].2.1 (r.deliver process (M.take k)).info).weight := by
  induction M generalizing r with
  | nil => simp
  | cons p M ih =>
    have h0 : r.quit = false := h 0 (by simp)
    have h' (m : ℕ) (hm : m < M.length) :
        ((r.call process p.1 p.2.2 p.2.1).deliver process (M.take m)).quit = false := by
      simpa [deliver_cons_of_quit_eq_false process h0] using h (m + 1) (by simpa using hm)
    rw [deliver_cons_of_quit_eq_false process h0, ih h']
    -- `congr(…)` rejects the step: its holes have the types `Fin (M.length + 1)` and
    -- `Fin (p :: M).length`, which agree only by unfolding `List.length`.
    refine .trans ?_ (congrArg (r.total + ·) (Fin.sum_univ_succ (n := M.length) _).symm)
    simp [call, deliver_cons_of_quit_eq_false process h0, add_assoc]

/-- The count of the delivery of `L` is the count at the start plus the sum of the values that the
calls return, the calls of the points of a prefix `M` of `L` before each of which the flag is
clear, and after which it is set unless `M` is all of `L`; the call of the `k`-th point is made on
the delivery of the first `k` points. -/
theorem exists_prefix_total_deliver_eq_sum (r : Delivery σ) (L : List (Int × Int × Int)) :
    ∃ M, M <+: L ∧ (∀ m < M.length, (r.deliver process (M.take m)).quit = false) ∧
      (M ≠ L → (r.deliver process M).quit = true) ∧
      (r.deliver process L).total = r.total + ∑ k : Fin M.length,
        (process M[k].1 M[k].2.2 M[k].2.1 (r.deliver process (M.take k)).info).weight := by
  obtain ⟨M, hML, hL, hM, hq⟩ := exists_prefix_deliver_eq process r L
  exact ⟨M, hML, hM, hq, hL ▸ total_deliver_eq_sum process hM⟩

end Ratpoints.Delivery

end
