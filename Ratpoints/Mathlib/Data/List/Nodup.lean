/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Mathlib.Data.List.Nodup

/-!
# Permutations from the maps of lists without duplicates

A candidate for `Mathlib.Data.List.Nodup`, next to `List.Nodup.map_on`: a list without duplicates,
mapped by a function that is injective on it, is a permutation of every list without duplicates
whose members are the images.

## Main statements

* `List.perm_map_of_nodup`: the map of a list without duplicates by a function injective on it is
  a permutation of every list without duplicates with the same members.
-/

@[expose] public section

namespace List

variable {α β : Type*}

/-- A list without duplicates, mapped by a function that is injective on it, is a permutation of
every list without duplicates whose members are exactly the images; compare
`List.perm_ext_iff_of_nodup` and `List.Nodup.map_on`. -/
theorem perm_map_of_nodup {l : List α} {l' : List β} {f : α → β} (hl : l.Nodup) (hl' : l'.Nodup)
    (hf : ∀ x ∈ l, ∀ y ∈ l, f x = f y → x = y) (h : ∀ b, b ∈ l' ↔ ∃ a ∈ l, f a = b) :
    (l.map f).Perm l' :=
  (perm_ext_iff_of_nodup (hl.map_on hf) hl').mpr fun b ↦ by rw [mem_map, h]

end List

end
