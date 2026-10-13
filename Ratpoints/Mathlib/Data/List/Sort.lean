/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.Sort

/-!
# The entries of a sorted list below a bound come first

A candidate for `Mathlib.Data.List.Sort`: in a list that is pairwise related by `≤`, the entries
below a bound `t` are its first entries, so entry `i` is below `t` when `i` is below their number.

## Main statements

* `List.getElem_lt_of_lt_length_filter`: entry `i` of a list pairwise related by `≤` is below `t`
  when `i` is below the number of entries below `t`.
-/

@[expose] public section

namespace List

/-- In a list that is pairwise related by `≤`, the entries below `t` come first: entry `i` is below
`t` when `i` is below the number of entries below `t`, since an entry `x ≥ t` leaves only entries
`≥ t` after it. -/
theorem getElem_lt_of_lt_length_filter {α : Type*} [Preorder α] [DecidableLT α] {l : List α}
    (hl : l.Pairwise (· ≤ ·)) {t : α} {i : ℕ} (hi : i < (l.filter (· < t)).length) :
    l[i]'(hi.trans_le (length_filter_le _ _)) < t := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x l ih =>
    have hx : x < t := by
      by_contra hxt
      rw [filter_eq_nil_iff.mpr fun y hy ↦ ?_] at hi
      · exact absurd hi (Nat.not_lt_zero i)
      rcases mem_cons.mp hy with rfl | hy
      · simpa using hxt
      · simpa using fun hyt ↦ hxt (((pairwise_cons.mp hl).1 y hy).trans_lt hyt)
    cases i with
    | zero => exact hx
    | succ i =>
      rw [filter_cons_of_pos (by simpa using hx), length_cons] at hi
      exact ih (pairwise_cons.mp hl).2 (by lia)

end List

end
