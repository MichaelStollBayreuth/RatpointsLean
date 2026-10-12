/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.Basic

/-!
# Lemmas on lists

Candidates for Mathlib's lemmas on lists, about the notions of core: filtering a list before
`List.flatMap f` changes nothing when every element `x` with `f x ≠ []` passes the filter, the
counterpart of `Finset.prod_filter_of_ne`, next to `List.flatMap_congr`, and so a list without
duplicates within another one without duplicates that holds every `x` with `f x ≠ []` gives a
permutation of its `List.flatMap f`; and `List.mapM f` in the monad `Option`, for which core has
only the lemmas of every monad: when it gives a list, that list is the map of every function that
agrees with `f` wherever `f` gives a value, and when it gives none, `f` gives none at a member.

## Main statements

* `List.flatMap_filter_of_ne`: a filter before `List.flatMap` that changes nothing.
* `List.perm_flatMap_of_nodup`: the `List.flatMap` of a list without duplicates of members of `l`,
  in any order, that holds every member with a nonempty image.
* `List.eq_map_of_mapM_eq_some`, `List.exists_mem_of_mapM_eq_none`: the two results of
  `List.mapM` in the monad `Option`.
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

/-- A list `l'` without duplicates whose members lie in the list `l` without duplicates, and which
holds every member `x` of `l` with `f x ≠ []`, gives a permutation of `l.flatMap f`, whatever the
order of `l'`: `l'` is a permutation of the members of `l` that it holds
(`List.perm_ext_iff_of_nodup`), and the others give nothing (`List.flatMap_filter_of_ne`). -/
theorem perm_flatMap_of_nodup {l l' : List α} {f : α → List β} (hl : l.Nodup)
    (hl' : l'.Nodup) (hsub : l' ⊆ l) (h : ∀ x ∈ l, f x ≠ [] → x ∈ l') :
    (l'.flatMap f).Perm (l.flatMap f) := by
  classical
  have hp : l'.Perm (l.filter (· ∈ l')) :=
    (perm_ext_iff_of_nodup hl' (hl.filter _)).mpr fun x ↦ by simpa using fun hx ↦ hsub hx
  rw [← flatMap_filter_of_ne (p := (· ∈ l')) fun x hx hf ↦ decide_eq_true (h x hx hf)]
  exact hp.flatMap_right f

theorem eq_map_of_mapM_eq_some {f : α → Option β} {g : α → β} {l : List α} {l' : List β}
    (hfg : ∀ a ∈ l, ∀ b, f a = some b → b = g a) (h : l.mapM f = some l') : l' = l.map g := by
  induction l generalizing l' with
  | nil => simpa [eq_comm] using h
  | cons a l ih => cases ha : f a <;> cases hl : l.mapM f <;> grind

theorem exists_mem_of_mapM_eq_none {f : α → Option β} {l : List α} (h : l.mapM f = none) :
    ∃ a ∈ l, f a = none := by
  induction l with
  | nil => nomatch h
  | cons a l ih => cases ha : f a <;> cases hl : l.mapM f <;> simp_all

end List

end
