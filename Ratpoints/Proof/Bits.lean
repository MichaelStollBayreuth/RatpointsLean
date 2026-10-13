/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Std.Internal.ForIn.Lemmas

/-!
# Lemmas on core types for the contracts

Lemmas on vectors, arrays, lists, ranges, natural numbers, integers and 64-bit words that the
contracts of the model need and Lean core lacks, under their names in the namespaces of Lean core:
the entries of a vector after `Vector.set!` and after a fold of `Vector.set!` over consecutive
positions, the entries of an array made by a map over a range, the last entry and the entries of an
array after `Array.push`, `Array.pop` and `Array.map`, the elements of `List.range n` that pass a
test which fails from some position on, the integers of a range that lie in a smaller one or between
two bounds, the gcd of the absolute values of a list of integers as a left fold, the length of the
list of a range and the position of the cursor of a loop over it, the cursor of a loop over an array
as one of its entries, the bound `y < (n + 1) k` for `y < n k`, the residues modulo `p` of the
integers from `a` on, exact quotients of integers, the bits of the word `~~~0` and of the masks
`~~~0 <<< n` and `~~~0 >>> n`, the lowest bit and the lowest set bit of a word, the word
`x &&& (x - 1)`, which is `x` with its lowest set bit cleared, the bits of a word set one at a time,
at their own positions or at others, the 64 bits of two words from a position within the first, the
bits of a word and-ed in turn with the words of a list, the numerators and the denominators of the
set bits of a list of words, read in turn, the numbers of a range between two bounds, the odd part
of a number below `2 ^ 64` by the lowest set bit of its word, bit 1 of odd numbers, the gcd of half
an even number with an odd one, a residue below `2 q` modulo `q` by one subtraction, the estimate
of a quotient by Barrett's reduction, the bounds of a step of Horner's rule and of a power of a
number below a power of 2, the entries of an array of Booleans after a fold of
`setIfInBounds · true`, the absolute value of the step of the cofactors of the extended Euclidean
algorithm, and the divisors of the gcd of `b` and a residue `f ≡ a (mod b)`.

## Main statements

* `Vector.getElem!_fold_set!`: the entries of a vector after a fold of `Vector.set!` over the
  positions `base, …, base + k - 1`.
* `UInt64.getLsbD_allOnes_shiftLeft`, `UInt64.getLsbD_allOnes_shiftRight`: the bits of the masks.
* `UInt64.getLsbD_and_sub_one`, `UInt64.toNat_and_sub_one_lt`: for `x ≠ 0`, `x &&& (x - 1)` is `x`
  with its lowest set bit cleared, and smaller than `x`.
* `UInt64.getLsbD_fold_or_one_shiftLeft`, `UInt64.getLsbD_fold_or_one_shiftLeft_comp`: the bits of
  a word set one at a time, at their own positions or at the positions that a function gives.
* `UInt64.getLsbD_shiftRight_or_shiftLeft`: the 64 bits from position `r` on of the 128 bits of two
  words, for `0 < r < 64`.
* `List.filter_range_eq_of_le`, `List.filter_range_succ_eq_append`: the elements of `List.range n`
  that pass a test which fails from `k` on are those of `List.range k`, followed by the next one
  that passes it.
* `List.filter_map_range_eq_map_range`: of the integers `s, …, s + m - 1`, those from `s + k₁` to
  `s + m - 1 - k₂`; `List.filter_map_range_eq_map_range'`: those from `lo` to `hi`.
* `List.flatMap_range_map_filter`: the integers `a + 64 y + t` of the positions `t` of the blocks
  `y < m` that pass a test, in increasing order, are those of `a, …, a + 64 m - 1` that pass a test
  `p`, when the first test is `p` on these integers: the numerators of the set bits of words.
* `List.flatMap_range'_map_filter`: the same for the natural numbers `64 w + t` of the blocks
  `w = w0, …, w0 + n - 1`: the denominators of the set bits of words.
* `List.filter_range'_le_and_le`: of a range that covers `lo, …, hi`, the numbers from `lo` to
  `hi`.
* `Std.Legacy.Range.length_toList`: the list of `[a:b]` has `b - a` entries.
* `Std.Legacy.Range.length_eq_of_toList_eq_append_cons`,
  `Std.Legacy.Range.lt_of_toList_eq_append_cons`: the position of the cursor of a loop over
  `[0:m]`; `Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons`,
  `Std.Legacy.Range.length_add_length_add_one_of_toList_eq_append_cons`: that of a loop over
  `[a:m]`, and the lengths of the lists before and after it.
* `Array.getElem!_pop`, `Array.getElem!_pop_of_back!_eq`: the entries of an array without its last
  entry, the same as before when that entry is the default value.
* `Array.getElem!_mem`: an entry in range of an array is a member of it.
* `Array.getElem!_foldl_setIfInBounds`, `Array.any_id_eq_true_of_getElem!_eq_true`: the entries of
  an array of Booleans that a fold of `setIfInBounds · true` marks, and an array with a true entry.
* `Array.forall_mem_toList_push`: a property of the members of the list of an array after a push.
* `Array.mem_of_forIn_toList_eq_append_cons`: the cursor of a loop over an array is one of its
  entries.
* `List.foldl_gcd_natAbs_dvd_natAbs`: the gcd of the absolute values of the entries of a list, as a
  left fold, divides each of them.
* `Int.toNat_add_emod_of_lt`, `Int.toNat_add_add_emod`: the residues modulo `p` of `a + j` before
  and from the first multiple of `p` from `a` on.
* `UInt64.getLsbD_foldl_and`: the bits of a word and-ed in turn with the words of a list.
* `UInt64.two_pow_ctz_mul_shiftRight_ofNat`, `UInt64.shiftRight_ctz_ofNat_mod_two`: a number
  `0 < b < 2 ^ 64` is `2 ^ t` times the odd number `b >>> t`, for the position `t` of the lowest
  set bit of the word `b`.
* `Nat.and_two_ne_zero_iff`, `Nat.and_and_two_ne_zero_iff`: bit 1 of odd numbers says whether they
  are `3 (mod 4)`; `Nat.gcd_div_two_of_mod_two`: halving an even number keeps its gcd with an odd
  one; `Nat.mod_eq_ite_of_lt_two_mul`: a residue below `2 q` modulo `q` by one subtraction.
* `Nat.mul_sub_one_div_div_mul_le`, `Nat.lt_mul_sub_one_div_div_add_two_mul`: Barrett's estimate
  `⌊u ⌊(N - 1) / p⌋ / N⌋` of `⌊u / p⌋` for `u < N` is the quotient or one less.
* `Nat.mul_add_lt_mul_of_lt`, `Nat.pow_lt_two_pow_of_lt`: a step of Horner's rule multiplies a bound
  by `p`, and `p ^ n < 2 ^ N` for `p < 2 ^ b` and `b n ≤ N`.
* `Int.natAbs_sub_mul_of_mul_nonpos`: `|a - q b| = |a| + q |b|` for `a b ≤ 0` and `q ≥ 0`.
* `Int.dvd_natAbs_of_dvd_gcd`: a divisor of the gcd of `f ≡ a (mod b)` and `b` divides `a`.

## Implementation notes

The file uses Lean core and `Std` only, so that the `grind` calls of the proofs see only the lemmas
of core, untouched by the updates of Mathlib.
-/

@[expose] public section

universe u v

/-! ### Vectors -/

namespace Vector

theorem getElem!_set! {α : Type u} [Inhabited α] {n : Nat} {xs : Vector α n} {i j : Nat} {x : α}
    (hj : j < n) : (xs.set! i x)[j]! = if i = j then x else xs[j]! := by
  rw [getElem!_pos (xs.set! i x) j hj, getElem!_pos xs j hj, getElem_set! hj]

/-- Setting the entries `base, …, base + k - 1` one after the other, entry `base + l` to `g l` of
its value. -/
theorem getElem!_fold_set! {α : Type u} [Inhabited α] {n : Nat} {xs : Vector α n}
    {base k : Nat} (g : Nat → α → α) {y : Nat} (hy : y < n) :
    (Nat.fold k (fun l _ v ↦ v.set! (base + l) (g l v[base + l]!)) xs)[y]! =
      if base ≤ y ∧ y < base + k then g (y - base) xs[y]! else xs[y]! := by
  induction k with
  | zero => grind
  | succ k ih => grind [Nat.fold_succ, getElem!_set!]

end Vector

/-! ### Arrays -/

namespace Array

theorem getElem!_map_range {α : Type u} [Inhabited α] (f : Nat → α) {n j : Nat} (hj : j < n) :
    ((Array.range n).map f)[j]! = f j := by
  simp [hj]

theorem getElem!_mem {α : Type u} [Inhabited α] {xs : Array α} {i : Nat} (h : i < xs.size) :
    xs[i]! ∈ xs := by
  rw [getElem!_pos xs i h]
  exact Array.getElem_mem h

theorem size_pop_lt_of_back?_eq_some {α : Type u} {xs : Array α} {x : α}
    (h : xs.back? = some x) : xs.pop.size < xs.size := by
  grind

theorem back!_eq_getElem! {α : Type u} [Inhabited α] {xs : Array α} :
    xs.back! = xs[xs.size - 1]! :=
  rfl

theorem back!_ne_of_back?_ne {α : Type u} [Inhabited α] {xs : Array α} {a : α}
    (hs : xs.size ≠ 0) (h : xs.back? ≠ some a) : xs.back! ≠ a := by
  grind [back!_eq_back?]

theorem size_ne_zero_of_back!_ne {α : Type u} [Inhabited α] {xs : Array α}
    (h : xs.back! ≠ default) : xs.size ≠ 0 := by
  grind [back!_eq_getElem!]

theorem back!_map {α : Type u} {β : Type v} [Inhabited α] [Inhabited β] {f : α → β}
    (hf : f default = default) (xs : Array α) : (xs.map f).back! = f xs.back! := by
  grind [back!_eq_getElem!]

theorem back!_map_range {α : Type u} [Inhabited α] (f : Nat → α) {n : Nat} (hn : n ≠ 0) :
    ((Array.range n).map f).back! = f (n - 1) := by
  grind [back!_eq_getElem!, getElem!_map_range]

theorem getElem!_push_lt {α : Type u} [Inhabited α] {xs : Array α} {x : α} {i : Nat}
    (h : i < xs.size) : (xs.push x)[i]! = xs[i]! := by
  grind

theorem getElem!_push_eq {α : Type u} [Inhabited α] {xs : Array α} {x : α} :
    (xs.push x)[xs.size]! = x := by
  simp

theorem getElem!_map {α : Type u} {β : Type v} [Inhabited α] [Inhabited β] {f : α → β}
    (hf : f default = default) (xs : Array α) (i : Nat) : (xs.map f)[i]! = f xs[i]! := by
  grind

theorem getElem!_pop {α : Type u} [Inhabited α] {xs : Array α} {i : Nat} :
    xs.pop[i]! = if i < xs.size - 1 then xs[i]! else default := by
  grind

theorem getElem!_pop_of_back!_eq {α : Type u} [Inhabited α] {xs : Array α} (h : xs.back! = default)
    (i : Nat) : xs.pop[i]! = xs[i]! := by
  grind [getElem!_pop, back!_eq_getElem!]

/-- The entries of an array of Booleans that a fold of `setIfInBounds · true` over the list `l`
marks: entry `t` in range is set when it was set before or one of the positions `f i` is `t`. -/
theorem getElem!_foldl_setIfInBounds {α : Type u} (l : List α) (f : α → Nat) (w : Array Bool)
    {t : Nat} (ht : t < w.size) :
    (l.foldl (fun w i ↦ w.setIfInBounds (f i) true) w)[t]! = (w[t]! || l.any (f · == t)) := by
  induction l generalizing w with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih _ (by simpa using ht), List.any_cons, getElem!_pos w t ht,
      getElem!_pos (w.setIfInBounds (f j) true) t (by simpa using ht),
      Array.getElem_setIfInBounds ht]
    grind

/-- A property of the members of the list of an array holds after a push of a member that has it:
`Array.forall_mem_push` for the members of the list, as invariants of loops state them. -/
theorem forall_mem_toList_push {α : Type u} {xs : Array α} {x : α} {P : α → Prop}
    (h : ∀ y ∈ xs.toList, P y) (hx : P x) : ∀ y ∈ (xs.push x).toList, P y := by
  rw [Array.toList_push]
  exact List.forall_mem_append.mpr ⟨h, List.forall_mem_singleton.mpr hx⟩

/-- `xs[i]! = true` gives a true entry of `xs`, since `xs[i]!` is `false` out of range. -/
theorem any_id_eq_true_of_getElem!_eq_true {xs : Array Bool} {i : Nat} (h : xs[i]! = true) :
    xs.any id = true := by
  by_cases hi : i < xs.size
  · exact Array.any_eq_true.mpr ⟨i, hi, by simpa [getElem!_pos xs i hi] using h⟩
  · simp [getElem!_neg xs i hi] at h

/-- The cursor of a loop over the array `xs` is an entry of `xs`. -/
theorem mem_of_forIn_toList_eq_append_cons {α : Type u} {xs : Array α} {pref suff : List α}
    {cur : α} (hl : ForIn.toList xs = pref ++ cur :: suff) : cur ∈ xs := by
  rw [Std.Internal.ForIn.toList_array] at hl
  exact Array.mem_toList_iff.mp (hl ▸ by simp)

end Array

/-! ### Lists -/

namespace List

theorem filter_range_eq_of_le {p : Nat → Bool} {k n : Nat} (hk : k ≤ n)
    (hz : ∀ j ≥ k, j < n → p j = false) :
    (range n).filter p = (range k).filter p := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hk
  rw [range_add, filter_append, append_right_eq_self, filter_eq_nil_iff]
  grind

theorem filter_range_succ_eq_append {p : Nat → Bool} {k c : Nat} (hk : k ≤ c) (hc : p c = true)
    (hz : ∀ j ≥ k, j < c → p j = false) :
    (range (c + 1)).filter p = (range k).filter p ++ [c] := by
  rw [range_succ, filter_append, filter_range_eq_of_le hk hz]
  simp [hc]

/-- Of the integers `s, …, s + m - 1`, those from `s + k₁` to `s + m - 1 - k₂`: the `m - k₁ - k₂`
integers from `s + k₁` on; for `m ≤ k₁ + k₂` there are none, and the truncated subtraction gives
`0`. -/
theorem filter_map_range_eq_map_range (s : Int) (k₁ k₂ m : Nat) :
    ((range m).map fun k : Nat ↦ s + k).filter (fun a ↦ decide (s + k₁ ≤ a ∧ a + k₂ < s + m)) =
      (range (m - k₁ - k₂)).map fun k : Nat ↦ s + k₁ + k := by
  by_cases hm : k₁ + k₂ ≤ m
  · obtain ⟨j, rfl⟩ : ∃ j, m = k₁ + j + k₂ := ⟨m - k₁ - k₂, by lia⟩
    rw [range_add, range_add, map_append, map_append, filter_append, filter_append,
      filter_eq_nil_iff.mpr, filter_eq_self.mpr, filter_eq_nil_iff.mpr]
    · simp [Function.comp_def, Int.add_assoc, show k₁ + j + k₂ - k₁ - k₂ = j by lia]
    all_goals grind
  · rw [Nat.sub_sub, Nat.sub_eq_zero_of_le (by lia), range_zero, map_nil, filter_eq_nil_iff]
    grind

/-- Of the integers `s, …, s + m - 1`, those from `lo` to `hi`: the integers from
`s + (lo - s).toNat`, the larger of `s` and `lo`, on, as many as `m` less the truncated differences
`(lo - s).toNat` and `(s + m - 1 - hi).toNat`. -/
theorem filter_map_range_eq_map_range' (s lo hi : Int) (m : Nat) :
    ((range m).map fun k : Nat ↦ s + k).filter (fun a ↦ decide (lo ≤ a ∧ a ≤ hi)) =
      (range (m - (lo - s).toNat - (s + m - 1 - hi).toNat)).map
        fun k : Nat ↦ s + (lo - s).toNat + k := by
  rw [← filter_map_range_eq_map_range]
  exact filter_congr fun a ha ↦ by
    obtain ⟨k, hk, rfl⟩ := mem_map.mp ha
    have := mem_range.mp hk
    lia

/-- The positions `t` of the blocks `y < m` that pass the test `g y`, read as the integers
`a + 64 y + t`, in increasing order, are the integers `a, …, a + 64 m - 1` that pass `p`, when
`g y t` is `t < 64` and `p (a + 64 y + t)`: for `g y` the bits of a word `y`, the numerators of the
set bits of `m` words. -/
theorem flatMap_range_map_filter {g : Nat → Nat → Bool} {a : Int} {p : Int → Bool} {m : Nat}
    (hg : ∀ y < m, ∀ t, g y t = (decide (t < 64) && p (a + 64 * y + t))) :
    (range m).flatMap (fun y ↦ ((range 64).filter (g y)).map fun t : Nat ↦ a + 64 * y + t) =
      ((range (64 * m)).map fun k : Nat ↦ a + k).filter p := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [range_succ (n := m), flatMap_append, ih fun y hy ↦ hg y (by lia), Nat.mul_succ, range_add,
      map_append, map_map, filter_append, flatMap_singleton]
    congr 1
    rw [filter_map]
    congr 1
    · exact funext fun t ↦ by simp [Int.add_assoc]
    · exact filter_congr fun t ht ↦ by
        rw [hg m (Nat.lt_succ_self m) t, decide_eq_true (mem_range.mp ht), Bool.true_and]
        simp [Int.add_assoc]

/-- The positions `t < 64` of the blocks `w = w0, …, w0 + n - 1` that pass the test `g w`, read as
the numbers `64 w + t`, in increasing order, are the numbers `64 w0, …, 64 (w0 + n) - 1` that pass
`p`, when `g w t` is `p (64 w + t)`: for `g w` the bits of a word `w`, the numbers of the set bits
of `n` words; `List.flatMap_range_map_filter` for natural numbers and blocks from `w0` on. -/
theorem flatMap_range'_map_filter {g : Nat → Nat → Bool} {p : Nat → Bool} {w0 n : Nat}
    (hg : ∀ w, w0 ≤ w → w < w0 + n → ∀ t < 64, g w t = p (64 * w + t)) :
    (range' w0 n).flatMap (fun w ↦ ((range 64).filter (g w)).map (64 * w + ·)) =
      (range' (64 * w0) (64 * n)).filter p := by
  induction n generalizing w0 with
  | zero => simp
  | succ n ih =>
    rw [range'_succ, flatMap_cons, ih fun w hw hw' ↦ hg w (by lia) (by lia),
      Nat.mul_add_one 64 w0, show 64 * (n + 1) = 64 + 64 * n by lia,
      ← range'_append_1, filter_append, range'_eq_map_range (s := 64 * w0), filter_map]
    exact congrArg (· ++ _) (congrArg (map _) (filter_congr fun t ht ↦
      hg w0 (Nat.le_refl w0) (by lia) t (mem_range.mp ht)))

/-- Of the numbers `a, …, a + n - 1`, which cover `lo, …, hi`, those from `lo` to `hi` are the
numbers `lo, …, hi`. -/
theorem filter_range'_le_and_le {a n lo hi : Nat} (ha : a ≤ lo) (hn : hi < a + n) :
    (range' a n).filter (fun b ↦ decide (lo ≤ b) && decide (b ≤ hi)) = range' lo (hi + 1 - lo) := by
  rcases Nat.lt_or_ge (hi + 1) lo with h | h
  · rw [Nat.sub_eq_zero_of_le (Nat.le_of_lt h), range'_zero, filter_eq_nil_iff]
    intro b _
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    lia
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le ha
  obtain ⟨k, rfl⟩ : ∃ k, n = m + (hi + 1 - (a + m)) + k := ⟨n - m - (hi + 1 - (a + m)), by lia⟩
  rw [← range'_append_1, ← range'_append_1, filter_append, filter_append,
    (filter_eq_nil_iff (l := range' a m)).mpr fun b hb ↦ by simp at hb ⊢; lia,
    (filter_eq_nil_iff (l := range' (a + (m + (hi + 1 - (a + m)))) k)).mpr fun b hb ↦ by
      simp at hb ⊢; lia,
    filter_eq_self.mpr fun b hb ↦ by simp at hb ⊢; lia, nil_append, append_nil]

theorem foldl_gcd_natAbs_dvd (l : List Int) (g : Nat) :
    l.foldl (fun g a ↦ g.gcd a.natAbs) g ∣ g := by
  induction l generalizing g with
  | nil => exact Nat.dvd_refl g
  | cons a l ih => exact Nat.dvd_trans (ih _) (Nat.gcd_dvd_left ..)

theorem foldl_gcd_natAbs_one (l : List Int) : l.foldl (fun g a ↦ g.gcd a.natAbs) 1 = 1 :=
  Nat.dvd_one.mp (foldl_gcd_natAbs_dvd l 1)

theorem foldl_gcd_natAbs_dvd_natAbs {l : List Int} (g : Nat) {x : Int} (hx : x ∈ l) :
    l.foldl (fun g a ↦ g.gcd a.natAbs) g ∣ x.natAbs := by
  induction l generalizing g with
  | nil => cases hx
  | cons a l ih =>
    rcases mem_cons.mp hx with rfl | hx
    · exact Nat.dvd_trans (foldl_gcd_natAbs_dvd l _) (Nat.gcd_dvd_right ..)
    · exact ih _ hx

end List

/-! ### Ranges -/

namespace Std.Legacy.Range

theorem length_toList (a b : Nat) : (ForIn.toList [a:b]).length = b - a := by
  simp [size]

/-- The form of `List.eq_of_range'_eq_append_cons` for the list `ForIn.toList [a:m]` of a loop over
`[a:m]`, in which the verification conditions state the cursor: the cursor is `a` plus the length of
the list before it. -/
theorem add_length_eq_of_toList_eq_append_cons {a m cur : Nat} {pref suff : List Nat}
    (h : ForIn.toList [a:m] = pref ++ cur :: suff) : a + pref.length = cur := by
  simp only [Std.Internal.ForIn.toList_range, List.range'_eq_append_iff] at h
  obtain ⟨k, -, rfl, h⟩ := h
  simpa using (List.range'_eq_cons_iff.mp h.symm).1

/-- The form of `List.eq_of_range'_eq_append_cons` for the list `ForIn.toList [0:m]` of a loop over
`[0:m]`, in which the verification conditions state the cursor: the cursor is the length of the list
before it. -/
theorem length_eq_of_toList_eq_append_cons {m cur : Nat} {pref suff : List Nat}
    (h : ForIn.toList [0:m] = pref ++ cur :: suff) : pref.length = cur :=
  (Nat.zero_add _).symm.trans (add_length_eq_of_toList_eq_append_cons h)

/-- The form of `List.mem_of_range'_eq_append_cons` for the list `ForIn.toList [0:m]` of a loop over
`[0:m]`: the cursor is below `m`. -/
theorem lt_of_toList_eq_append_cons {m cur : Nat} {pref suff : List Nat}
    (h : ForIn.toList [0:m] = pref ++ cur :: suff) : cur < m := by
  have : cur ∈ ForIn.toList [0:m] := by simp [h]
  simpa using this

/-- The form of `List.length_of_range'_eq_append_cons` for the list `ForIn.toList [a:m]` of a loop
over `[a:m]`: the lists before and after the cursor have `m - a - 1` entries together. -/
theorem length_add_length_add_one_of_toList_eq_append_cons {a m cur : Nat} {pref suff : List Nat}
    (h : ForIn.toList [a:m] = pref ++ cur :: suff) : pref.length + suff.length + 1 = m - a := by
  rw [← length_toList, h, List.length_append, List.length_cons, Nat.add_assoc]

end Std.Legacy.Range

/-! ### Natural numbers -/

namespace Nat

/-- Barrett's estimate `⌊u ⌊(N - 1) / p⌋ / N⌋` of the quotient `⌊u / p⌋` is at most it: its
product with `p` is at most `u`. -/
theorem mul_sub_one_div_div_mul_le (u N p : Nat) : u * ((N - 1) / p) / N * p ≤ u := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  have h1 := Nat.mul_le_mul_right p (Nat.div_mul_le_self (u * ((N - 1) / p)) N)
  have h2 := Nat.mul_le_mul_left u (Nat.div_mul_le_self (N - 1) p)
  have h3 : u * (N - 1) ≤ u * N := Nat.mul_le_mul_left u (Nat.sub_le N 1)
  refine Nat.le_of_mul_le_mul_right (c := N) ?_ hN
  grind

/-- Barrett's estimate `q = ⌊u ⌊(N - 1) / p⌋ / N⌋` of the quotient `⌊u / p⌋` for `u < N` is at
least it less one: `u < (q + 2) p`. -/
theorem lt_mul_sub_one_div_div_add_two_mul {u N p : Nat} (hp : 0 < p) (hu : u < N) :
    u < (u * ((N - 1) / p) / N + 2) * p := by
  generalize hm : (N - 1) / p = m
  generalize hq : u * m / N = q
  have h2 : u * m < (q + 1) * N := by
    have := Nat.lt_div_mul_add (a := u * m) (b := N) (by lia)
    rw [hq] at this
    lia
  have h4 : N ≤ (m + 1) * p := by
    have := Nat.lt_div_mul_add (a := N - 1) (b := p) hp
    rw [hm] at this
    lia
  have h2p := Nat.mul_lt_mul_of_pos_right h2 hp
  have h4u := Nat.mul_le_mul_left u h4
  have hup := Nat.mul_lt_mul_of_pos_right hu hp
  exact Nat.lt_of_mul_lt_mul_right (a := N) (by grind)

/-- One step of Horner's rule with an argument and a coefficient below `p` multiplies a bound on
the accumulator by `p`. -/
theorem mul_add_lt_mul_of_lt {s a c P p : Nat} (hs : s < P) (ha : a < p) (hc : c < p) :
    s * a + c < P * p :=
  calc s * a + c < s * p + p :=
        Nat.add_lt_add_of_le_of_lt (Nat.mul_le_mul_left s (Nat.le_of_lt ha)) hc
    _ = (s + 1) * p := (Nat.succ_mul s p).symm
    _ ≤ P * p := Nat.mul_le_mul_right p hs

theorem pow_lt_two_pow_of_lt {p b n N : Nat} (hp : p < 2 ^ b) (hn : b * n ≤ N) (hn0 : n ≠ 0) :
    p ^ n < 2 ^ N :=
  calc p ^ n < (2 ^ b) ^ n := Nat.pow_lt_pow_left hp hn0
    _ = 2 ^ (b * n) := (Nat.pow_mul 2 b n).symm
    _ ≤ 2 ^ N := Nat.pow_le_pow_right (by decide) hn

theorem lt_add_one_mul_of_lt_mul {y n k : Nat} (h : y < n * k) : y < (n + 1) * k :=
  Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right k (Nat.le_succ n))

/-- A residue `a < 2 q` modulo `q` by one conditional subtraction. -/
theorem mod_eq_ite_of_lt_two_mul {a q : Nat} (h : a < 2 * q) :
    a % q = if q ≤ a then a - q else a := by
  split
  · rw [Nat.mod_eq_sub_mod ‹_›, Nat.mod_eq_of_lt (by lia)]
  · exact Nat.mod_eq_of_lt (by lia)

/-- The bits of `x &&& k` for `k < 2 ^ n` are those of the residue of `x` modulo `2 ^ n`. -/
theorem and_eq_mod_two_pow_and {x k n : Nat} (hk : k < 2 ^ n) : x &&& k = x % 2 ^ n &&& k := by
  rw [← Nat.mod_eq_of_lt (Nat.lt_of_le_of_lt Nat.and_le_right hk), Nat.and_mod_two_pow,
    Nat.mod_eq_of_lt hk]

/-- Bit 1 of an odd number is set exactly when it is `3 (mod 4)`. -/
theorem and_two_ne_zero_iff {q : Nat} (hq : q % 2 = 1) : (q &&& 2 != 0) = true ↔ q % 4 = 3 := by
  rw [and_eq_mod_two_pow_and (n := 2) (by decide : 2 < 2 ^ 2)]
  obtain h | h : q % 4 = 1 ∨ q % 4 = 3 := by lia
  all_goals simp [h]

/-- Bit 1 of two odd numbers is set in both exactly when both are `3 (mod 4)`. -/
theorem and_and_two_ne_zero_iff {n m : Nat} (hn : n % 2 = 1) (hm : m % 2 = 1) :
    (n &&& m &&& 2 != 0) = true ↔ n % 4 = 3 ∧ m % 4 = 3 := by
  rw [and_eq_mod_two_pow_and (n := 2) (by decide : 2 < 2 ^ 2), Nat.and_mod_two_pow]
  obtain h | h : n % 4 = 1 ∨ n % 4 = 3 := by lia
  all_goals obtain h' | h' : m % 4 = 1 ∨ m % 4 = 3 := by lia
  all_goals simp [h, h']

/-- Halving an even `x` keeps its gcd with an odd `y`. -/
theorem gcd_div_two_of_mod_two {x y : Nat} (hx : x % 2 = 0) (hy : y % 2 = 1) :
    gcd (x / 2) y = gcd x y := by
  have h2 : Coprime 2 y := by rw [Coprime, Nat.gcd_rec, hy]; rfl
  conv => rhs; rw [← Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hx)]
  exact (Coprime.gcd_mul_left_cancel _ h2).symm

end Nat

/-! ### Integers -/

namespace Int

/-- Before the first multiple of `p` from `a` on: for `r = (-a) mod p` and `j < r`, the residue of
`a + j` modulo `p` is `p - r + j`. -/
theorem toNat_add_emod_of_lt {a : Int} {p j : Nat} (hp : 0 < p)
    (hj : j < ((-a) % (p : Int)).toNat) :
    ((a + j) % (p : Int)).toNat = p - ((-a) % (p : Int)).toNat + j := by
  have := emod_nonneg (-a) (b := p) (by lia)
  have := emod_lt_of_pos (-a) (b := p) (by lia)
  have := mul_ediv_add_emod (-a) p
  have key : a + j = (p - (-a) % p + j) + p * (-((-a) / p) - 1) := by
    rw [Int.mul_sub, Int.mul_neg, Int.mul_one]
    lia
  rw [key, add_mul_emod_self_left, emod_eq_of_lt (by lia) (by lia)]
  lia

/-- From the first multiple of `p` from `a` on: for `r = (-a) mod p` and `i < p`, the residue of
`a + r + k p + i` modulo `p` is `i`. -/
theorem toNat_add_add_emod {a : Int} {p i k : Nat} (hi : i < p) :
    ((a + ((((-a) % (p : Int)).toNat + k * p + i : Nat) : Int)) % (p : Int)).toNat = i := by
  have := mul_ediv_add_emod (-a) p
  have hR : (((-a) % (p : Int)).toNat : Int) = (-a) % p :=
    toNat_of_nonneg (emod_nonneg _ (by lia))
  have key : a + ((((-a) % (p : Int)).toNat + k * p + i : Nat) : Int) =
      i + p * (k - (-a) / p) := by
    push_cast
    rw [hR, Int.mul_sub, Int.mul_comm (p : Int) k]
    lia
  rw [key, add_mul_emod_self_left, emod_eq_of_lt (by lia) (by lia)]
  simp

theorem ediv_mul_eq_ediv_mul_of_dvd {a b g : Int} (ha : g ∣ a) (hb : g ∣ b) :
    a / g * b = b / g * a := by
  rw [← Int.mul_ediv_assoc' _ ha, ← Int.mul_ediv_assoc' _ hb, Int.mul_comm]

theorem ediv_ne_zero_of_dvd {a b : Int} (hb : b ∣ a) (ha : a ≠ 0) : a / b ≠ 0 := fun h ↦
  ha (Int.eq_zero_of_ediv_eq_zero hb h)

/-- For integers `a` and `b` of opposite signs, or one of them `0`, and `q ≥ 0`,
`|a - q b| = |a| + q |b|`: the step of the cofactors of the extended Euclidean algorithm. -/
theorem natAbs_sub_mul_of_mul_nonpos {a b : Int} (h : a * b ≤ 0) (q : Nat) :
    (a - q * b).natAbs = a.natAbs + q * b.natAbs := by
  rcases Int.lt_trichotomy b 0 with hb | rfl | hb
  · have ha : 0 ≤ a := Int.not_lt.mp fun ha ↦ Int.not_le.mpr (Int.mul_pos_of_neg_of_neg ha hb) h
    have hq : (q : Int) * b ≤ 0 :=
      Int.mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg q) (Int.le_of_lt hb)
    apply Int.ofNat_inj.mp
    rw [Int.natCast_add, Int.natCast_mul, Int.natAbs_of_nonneg (by lia), Int.natAbs_of_nonneg ha,
      Int.ofNat_natAbs_of_nonpos (Int.le_of_lt hb), Int.mul_neg]
    lia
  · simp
  · have ha : a ≤ 0 := Int.not_lt.mp fun ha ↦ Int.not_le.mpr (Int.mul_pos ha hb) h
    have hq : 0 ≤ (q : Int) * b := Int.mul_nonneg (Int.natCast_nonneg q) (Int.le_of_lt hb)
    apply Int.ofNat_inj.mp
    rw [Int.natCast_add, Int.natCast_mul, Int.ofNat_natAbs_of_nonpos (by lia),
      Int.ofNat_natAbs_of_nonpos ha, Int.natAbs_of_nonneg (Int.le_of_lt hb)]
    lia

/-- A divisor of the gcd of `f ≡ a (mod b)` and `b` divides `a`. -/
theorem dvd_natAbs_of_dvd_gcd {a : Int} {b f q : Nat} (h : (f : Int) % b = a % b)
    (hq : q ∣ Nat.gcd f b) : q ∣ a.natAbs := by
  have h1 : (q : Int) ∣ a - f := Int.dvd_trans
    (Int.natCast_dvd_natCast.mpr (Nat.dvd_trans hq (Nat.gcd_dvd_right f b)))
    (Int.dvd_of_emod_eq_zero (Int.emod_eq_emod_iff_emod_sub_eq_zero.mp h.symm))
  have h2 : (q : Int) ∣ f := Int.natCast_dvd_natCast.mpr (Nat.dvd_trans hq (Nat.gcd_dvd_left f b))
  exact Int.ofNat_dvd_left.mp (by simpa using Int.dvd_add h1 h2)

end Int

/-! ### Words -/

namespace UInt64

theorem getLsbD_allOnes (t : Nat) : (~~~0 : UInt64).toBitVec.getLsbD t = decide (t < 64) := by
  simp only [UInt64.toBitVec_not, UInt64.toBitVec_zero, BitVec.not_zero, BitVec.getLsbD_allOnes]

theorem getLsbD_allOnes_shiftLeft (n : UInt64) (t : Nat) :
    ((~~~0 : UInt64) <<< n).toBitVec.getLsbD t =
      (decide (t < 64) && decide (n.toNat % 64 ≤ t)) := by
  simp only [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_not, UInt64.toBitVec_zero, BitVec.not_zero,
    BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, BitVec.getLsbD_allOnes, BitVec.toNat_umod,
    UInt64.toNat_toBitVec, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]
  grind

theorem getLsbD_allOnes_shiftRight (n : UInt64) (t : Nat) :
    ((~~~0 : UInt64) >>> n).toBitVec.getLsbD t = decide (n.toNat % 64 + t < 64) := by
  simp only [UInt64.toBitVec_shiftRight, UInt64.toBitVec_not, UInt64.toBitVec_zero, BitVec.not_zero,
    BitVec.ushiftRight_eq', BitVec.getLsbD_ushiftRight, BitVec.getLsbD_allOnes, BitVec.toNat_umod,
    UInt64.toNat_toBitVec, BitVec.ofNat_eq_ofNat, BitVec.toNat_ofNat]

theorem and_one_eq_zero_iff (x : UInt64) : x &&& 1 = 0 ↔ x.toBitVec.getLsbD 0 = false := by
  simp only [← UInt64.toBitVec_inj, UInt64.toBitVec_and, UInt64.toBitVec_one, UInt64.toBitVec_zero,
    BitVec.and_one_eq_setWidth_ofBool_getLsbD]
  cases x.toBitVec.getLsbD 0 <;> decide

theorem toNat_ctz_lt {x : UInt64} (hx : x ≠ 0) : x.toBitVec.ctz.toNat < 64 := by
  simpa [BitVec.lt_def] using BitVec.ctz_lt_iff_ne_zero.mpr (UInt64.toBitVec_ne_of_ne hx)

theorem getLsbD_ctz {x : UInt64} (hx : x ≠ 0) : x.toBitVec.getLsbD x.toBitVec.ctz.toNat = true :=
  BitVec.getLsbD_true_ctz_of_ne_zero (UInt64.toBitVec_ne_of_ne hx)

theorem ne_ctz_of_and_one_eq_zero {w a : UInt64} {t : Nat} (hw : w ≠ 0)
    (ha : a.toBitVec = w.toBitVec >>> t) (h : a &&& 1 = 0) : t ≠ w.toBitVec.ctz.toNat := by
  rintro rfl
  rw [and_one_eq_zero_iff, ha, BitVec.getLsbD_ushiftRight, Nat.add_zero, getLsbD_ctz hw] at h
  exact Bool.noConfusion h

theorem eq_ctz_of_and_one_ne_zero {w a : UInt64} {t : Nat} (ha : a.toBitVec = w.toBitVec >>> t)
    (ht : t ≤ w.toBitVec.ctz.toNat) (h : ¬a &&& 1 = 0) : t = w.toBitVec.ctz.toNat := by
  rw [and_one_eq_zero_iff, ha, BitVec.getLsbD_ushiftRight, Nat.add_zero] at h
  exact Nat.le_antisymm ht (Nat.not_lt.mp fun hlt ↦ h (BitVec.getLsbD_false_of_lt_ctz hlt))

/-- `x &&& (x - 1)` is `x` with its lowest set bit cleared, since `x - 1 = ~~~(-x)` agrees with `x`
above that bit and has the bit clear. -/
theorem getLsbD_and_sub_one {x : UInt64} (hx : x ≠ 0) (t : Nat) :
    (x &&& (x - 1)).toBitVec.getLsbD t = (x.toBitVec.getLsbD t && t != x.toBitVec.ctz.toNat) := by
  rw [UInt64.toBitVec_and, UInt64.toBitVec_sub, UInt64.toBitVec_one, ← BitVec.not_neg]
  grind [BitVec.getLsbD_neg, BitVec.getLsbD_false_of_lt_ctz, getLsbD_ctz]

theorem toNat_and_sub_one_lt {x : UInt64} (hx : x ≠ 0) : (x &&& (x - 1)).toNat < x.toNat := by
  grind [Nat.and_le_right, UInt64.toNat_sub_of_le, UInt64.pos_iff_ne_zero]

theorem getLsbD_one_shiftLeft {t : Nat} (ht : t < 64) (s : Nat) :
    ((1 : UInt64) <<< t.toUInt64).toBitVec.getLsbD s = decide (s = t) := by
  grind [UInt64.toBitVec_shiftLeft, UInt64.toBitVec_one]

/-- The bits `i < k` for which `c i` holds, set one after the other in the word `0`. -/
theorem getLsbD_fold_or_one_shiftLeft (c : Nat → Bool) {k : Nat} (hk : k ≤ 64) (t : Nat) :
    (Nat.fold k (fun i _ w ↦ if c i then w ||| (1 : UInt64) <<< i.toUInt64 else w)
      0).toBitVec.getLsbD t = (decide (t < k) && c t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.fold_succ]
    grind [UInt64.toBitVec_or, getLsbD_one_shiftLeft]

/-- The bits `f i` for the `i < k` for which `c i` holds, set one after the other in the word `0`,
for `f i < 64`: `UInt64.getLsbD_fold_or_one_shiftLeft` with the bit `f i` at step `i`. -/
theorem getLsbD_fold_or_one_shiftLeft_comp (c : Nat → Bool) (f : Nat → Nat) {k : Nat}
    (hf : ∀ i < k, f i < 64) (t : Nat) :
    (Nat.fold k (fun i _ w ↦ if c i then w ||| (1 : UInt64) <<< (f i).toUInt64 else w)
      0).toBitVec.getLsbD t = decide (∃ i < k, c i = true ∧ f i = t) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.fold_succ]
    have := getLsbD_one_shiftLeft (hf k (Nat.lt_succ_self k)) t
    have := ih fun i hi ↦ hf i (Nat.lt_succ_of_lt hi)
    split <;> grind [UInt64.toBitVec_or]

theorem getLsbD_or_one_shiftLeft (x : UInt64) {n : Nat} (hn : n < 64) (t : Nat) :
    (x ||| 1 <<< UInt64.ofNat n).toBitVec.getLsbD t = (x.toBitVec.getLsbD t || decide (t = n)) := by
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or, ← Nat.toUInt64_eq, getLsbD_one_shiftLeft hn]

/-- For `0 < r < 64`, the word made of the bits of `x` from `r` on and the lowest `r` bits of `y`
above them: the 64 bits from position `r` on of the 128 bits of `x` followed by `y`. -/
theorem getLsbD_shiftRight_or_shiftLeft {r : Nat} (hr0 : r ≠ 0) (hr : r < 64) (x y : UInt64)
    (t : Nat) :
    (x >>> r.toUInt64 ||| y <<< (64 - r).toUInt64).toBitVec.getLsbD t =
      (decide (t < 64) && if r + t < 64 then x.toBitVec.getLsbD (r + t)
        else y.toBitVec.getLsbD (r + t - 64)) := by
  simp [BitVec.ushiftRight_eq', BitVec.shiftLeft_eq']
  grind

/-- The bits of a word and-ed in turn with the words `f a` of the entries `a` of a list. -/
theorem getLsbD_foldl_and {α : Type u} (f : α → UInt64) (l : List α) (init : UInt64) (t : Nat) :
    (l.foldl (fun acc a ↦ acc &&& f a) init).toBitVec.getLsbD t =
      (init.toBitVec.getLsbD t && l.all fun a ↦ (f a).toBitVec.getLsbD t) := by
  induction l generalizing init with
  | nil => simp
  | cons a l ih => simp [ih, Bool.and_assoc]

theorem ofNat_ne_zero_of_lt {b : Nat} (hb0 : 0 < b) (hb : b < UInt64.size) :
    UInt64.ofNat b ≠ 0 :=
  fun h ↦ Nat.ne_of_gt hb0 (by simpa [UInt64.toNat_ofNat_of_lt' hb] using congrArg UInt64.toNat h)

/-- For `0 < b < 2 ^ 64`, `b` is `2 ^ t` times `b >>> t`, for the position `t` of the lowest set
bit of the word `b`, since the bits of `b` below it are clear. -/
theorem two_pow_ctz_mul_shiftRight_ofNat {b : Nat} (hb0 : 0 < b) (hb : b < UInt64.size) :
    2 ^ (UInt64.ofNat b).toBitVec.ctz.toNat * (b >>> (UInt64.ofNat b).toBitVec.ctz.toNat) = b := by
  have hlt := BitVec.lt_def.mp (BitVec.ctz_lt_iff_ne_zero.mpr
    (UInt64.toBitVec_ne_of_ne (ofNat_ne_zero_of_lt hb0 hb)))
  rw [UInt64.toBitVec_ofNat'] at hlt ⊢
  have hmod : b % 2 ^ (BitVec.ofNat 64 b).ctz.toNat = 0 := Nat.eq_of_testBit_eq fun i ↦ by
    have := BitVec.getLsbD_false_of_lt_ctz (x := BitVec.ofNat 64 b) (i := i)
    rw [BitVec.getLsbD_ofNat] at this
    simp only [Nat.testBit_mod_two_pow, Nat.zero_testBit]
    grind
  rw [Nat.shiftRight_eq_div_pow, Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero hmod)]

/-- For `0 < b < 2 ^ 64`, `b >>> t` is odd, for the position `t` of the lowest set bit of the word
`b`. -/
theorem shiftRight_ctz_ofNat_mod_two {b : Nat} (hb0 : 0 < b) (hb : b < UInt64.size) :
    (b >>> (UInt64.ofNat b).toBitVec.ctz.toNat) % 2 = 1 := by
  have ht := BitVec.getLsbD_true_ctz_of_ne_zero
    (UInt64.toBitVec_ne_of_ne (ofNat_ne_zero_of_lt hb0 hb))
  rw [UInt64.toBitVec_ofNat', BitVec.getLsbD_ofNat, Bool.and_eq_true] at ht
  rw [UInt64.toBitVec_ofNat', Nat.shiftRight_eq_div_pow]
  simpa [Nat.testBit_eq_decide_div_mod_eq] using ht.2

end UInt64

end
