/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Mathlib.Data.List.Basic

/-!
# Lemmas on lists

Candidates for Mathlib's lemmas on lists, about the notions of core: filtering a list before
`List.flatMap f` changes nothing when every element `x` with `f x ≠ []` passes the filter, the
counterpart of `Finset.prod_filter_of_ne`, next to `List.flatMap_congr`; and a list without
duplicates, mapped by a function that is injective on it, is a permutation of every list without
duplicates whose members are the images.

## Main statements

* `List.flatMap_filter_of_ne`: a filter before `List.flatMap` that changes nothing.
* `List.perm_map_of_nodup`: the map of a list without duplicates by a function injective on it is
  a permutation of every list without duplicates with the same members.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-- Filtering the list `l` by `p` before `List.flatMap f` changes nothing when every element `x`
of `l` with `f x ≠ []` satisfies `p`; compare `Finset.prod_filter_of_ne`. -/
theorem flatMap_filter_of_ne {l : List α} {p : α → Bool} {f : α → List β}
    (h : ∀ x ∈ l, f x ≠ [] → p x) : (l.filter p).flatMap f = l.flatMap f := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    have ih := ih fun y hy ↦ h y (.tail _ hy)
    by_cases hp : p x
    · simp [hp, ih]
    · have hf : f x = [] := by_contra fun hf ↦ hp (h x (.head _) hf)
      simp [hp, ih, hf]

/-- A list without duplicates, mapped by a function that is injective on it, is a permutation of
every list without duplicates whose members are exactly the images; compare
`List.perm_ext_iff_of_nodup`. -/
theorem perm_map_of_nodup {l : List α} {l' : List β} {f : α → β} (hl : l.Nodup) (hl' : l'.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (h : ∀ b, b ∈ l' ↔ ∃ a ∈ l, f a = b) :
    (l.map f).Perm l' :=
  (perm_ext_iff_of_nodup (Pairwise.map _ (fun a b ⟨ha, hb, hab⟩ e ↦ hab (hf a ha b hb e))
    (Pairwise.and_mem.1 hl)) hl').mpr fun b ↦ by rw [mem_map, h]

end List

end
