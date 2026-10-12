/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.Pairwise

/-!
# A member of a list that is pairwise related, related to one of its entries

A candidate for `Mathlib.Data.List.Pairwise`: in a list `l₁ ++ b :: l₂` that is pairwise related by
an asymmetric relation `R`, as a strictly increasing list is by `<`, a member `a` with `R a b` lies
in `l₁`.

## Main statements

* `List.mem_of_mem_append_cons_of_rel`: a member `a` of `l₁ ++ b :: l₂`, pairwise related by an
  asymmetric `R`, with `R a b` is a member of `l₁`.
-/

@[expose] public section

namespace List

/-- A member `a` with `R a b` of the list `l₁ ++ b :: l₂`, pairwise related by the asymmetric
relation `R`, is a member of `l₁`: it is not `b`, and `R b x` for the members `x` of `l₂`. -/
theorem mem_of_mem_append_cons_of_rel {α : Type*} {R : α → α → Prop} [Std.Asymm R]
    {l₁ l₂ : List α} {a b : α} (h : (l₁ ++ b :: l₂).Pairwise R) (ha : a ∈ l₁ ++ b :: l₂)
    (hab : R a b) : a ∈ l₁ := by
  rcases mem_append.mp ha with ha | ha
  · exact ha
  · rcases mem_cons.mp ha with rfl | ha
    · exact absurd hab (Std.Irrefl.irrefl a)
    · exact absurd hab (Std.Asymm.asymm _ _ ((pairwise_cons.mp (pairwise_append.mp h).2.1).1 a ha))

end List

end
