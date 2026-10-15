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
positions, the entries of `Vector.ofFn f`, the entries of an array made by a map over a range, the
last entry and the entries of an array after `Array.push`, `Array.pop` and `Array.map`, the elements
of `List.range n` that pass a test which fails from some position on, `List.flatMap` over a filtered
list, the integers of a range that lie in a smaller one or between two bounds, the gcd of the
absolute values of a list of integers as a left fold, the length of the list of a range and the
position of the cursor of a loop over it, the cursor of a loop over an array as one of its entries,
the bound `y < (n + 1) k` for `y < n k`, the residues modulo `p` of the integers from `a` on, the
residue of an integer modulo `p`, below `p` and read off its residue modulo a multiple of `p`, exact
quotients of integers, the bits of the word `~~~0` and of the masks `~~~0 <<< n` and `~~~0 >>> n`,
the lowest bit and the lowest set bit of a word, the word `x &&& (x - 1)`, which is `x` with its
lowest set bit cleared, the bits of a word set one at a time, at their own positions or at others,
the 64 bits of two words from a position within the first, the bits of a word and-ed in turn with
the words of a list, the numerators and the denominators of the set bits of a list of words, read in
turn, the numbers of a range between two bounds, the odd part of a number below `2 ^ 64` by the
lowest set bit of its word, bit 1 of odd numbers, the gcd of half an even number with an odd one, a
residue below `2 q` modulo `q` by one subtraction, the estimate of a quotient by Barrett's
reduction, the bounds of a step of Horner's rule and of a power of a number below a power of 2, the
entries of an array of Booleans after a fold of `setIfInBounds · true`, the absolute value of the
step of the cofactors of the extended Euclidean algorithm, the divisors of the gcd of `b` and a
residue `f ≡ a (mod b)`, the remainder and the quotient by a multiplication with a reciprocal, the
high half of a product from the products of the halves of its factors and the halves of a word, the
gcd of the odd part of a number with an odd one and the step of the binary algorithm for the gcd,
the residue modulo a divisor of `b` of a numerator prime to `b`, C's remainder, which truncates,
made non-negative, the residue of `(a mod p) b` and the bound `|a b| + H ≤ p H` for `|a| ≤ H` and
`b < p`, and, for the signed 64-bit words, the arithmetic shift, the mask `x >>> 63` with the
smaller and the distance of two non-negative words that it gives without a branch, the odd part of a
positive word by the lowest set bit of the word read as unsigned, its lowest bit, the absolute
value, and the words of an integer and of a natural number below `2 ^ 63`. For the rows under a
unit: the residues under a unit `u` with an inverse modulo `q`, zero or not, modulo a divisor of `q`
too, the residue `x i mod q` read with an inverse `i` of `r`, and the residue of `u a` for an
integer `a`.

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
* `Std.Legacy.Range.length_eq_of_toList_eq_append_cons`: the position of the cursor of a loop over
  `[0:m]`; `Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons`,
  `Std.Legacy.Range.lt_of_toList_eq_append_cons`,
  `Std.Legacy.Range.length_add_length_add_one_of_toList_eq_append_cons`: that of a loop over
  `[a:m]`, below `m`, and the lengths of the lists before and after it.
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
* `Int.toNat_emod_lt`, `Int.toNat_emod_mod_of_dvd`: the residue of `a` modulo `p > 0` is below `p`,
  and for `p ∣ m` it is the residue modulo `p` of the residue of `a` modulo `m`.
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
  by `p`, and `p ^ n < 2 ^ N` for `p < 2 ^ b`, `n ≠ 0` and `b n ≤ N`.
* `Int.natAbs_sub_mul_of_mul_nonpos`: `|a - q b| = |a| + q |b|` for `a b ≤ 0` and `q ≥ 0`.
* `Int.dvd_natAbs_of_dvd_gcd`: a divisor of the gcd of `f ≡ a (mod b)` and `b` divides `a`.
* `Nat.mul_mod_mul_div_eq_mod_of_mul_eq_add`, `Nat.mul_div_eq_div_of_mul_eq_add`: the remainder
  and the quotient by a reciprocal `m` of `p` scaled by `N`, for `m p = N + δ` and `u δ < N`.
* `Nat.gcd_eq_of_two_pow_mul_eq`: for `x = 2 ^ t y`, `y` has the gcd of `x` with an odd number;
  `Nat.gcd_min_eq_gcd_of_two_pow_mul_eq`, `Nat.add_min_lt_add_of_two_pow_mul_eq`: the odd part of
  the distance of two odd numbers has with the smaller of the two their gcd and a sum below theirs,
  the step of the binary algorithm for the gcd.
* `Int.toNat_emod_ne_zero_of_gcd_eq_one`: a divisor `p > 1` of `b` does not divide a numerator
  prime to `b`.
* `Int.ite_tmod_lt_zero_eq_emod`, `Int.toNat_emod_mul_emod`: C's remainder, which truncates, made
  non-negative is the Euclidean one, and the residue of `(a mod p) b` as a natural number;
  `Int.toNat_mul_add_natCast_mul_mod`: the shift by a multiple `p H` of `p` keeps the residue of
  `a binv`.
* `Int.natAbs_mul_add_le_mul`: `|a b| + H ≤ p H` for `|a| ≤ H` and `b < p`.
* `Int64.toInt_shiftRight_ofNat`, `Int64.shiftRight_63`: the arithmetic shift of a `long` by
  `k < 64`, and the mask `x >>> 63`, `-1` for a negative `x` and `0` otherwise.
* `Int64.toNatClampNeg_add_and_shiftRight_63`, `Int64.toNatClampNeg_xor_shiftRight_63_sub`: for
  `d = m - n`, `n + (d &&& d >>> 63)` and `(d ^^^ d >>> 63) - d >>> 63` are the smaller and the
  distance of two non-negative `long`s.
* `Int64.two_pow_ctz_mul_toNatClampNeg_shiftRight`, `Int64.toNatClampNeg_shiftRight_ctz_mod_two`: a
  positive `long` `x` is `2 ^ t` times the odd number `x >>> t`, for the position `t` of the lowest
  set bit of the word `x` read as unsigned.
* `Int64.toNatClampNeg_ite_neg`: the absolute value of a `long` other than `-2 ^ 63`.
* `Int64.minValue_lt_ofInt`, `Int64.ofNat_pos`: the word of an integer `|a| < 2 ^ 63` is not
  `-2 ^ 63`, and that of a natural number `0 < n < 2 ^ 63` is positive.
* `Nat.mul_div_two_pow_64_eq`: the high half of a product from the products of the halves of 32
  bits of its factors.
* `Nat.mul_mod_eq_zero_iff_of_mul_mod`, `Nat.mul_mod_eq_mul_mod_of_mul_mod_eq_one`: scaling by a
  unit `u` with an inverse modulo `q` keeps a residue zero or not, and keeps the residue `x i mod q`
  read with an inverse `i` of `r` when `x` and `r` are both scaled.

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

theorem getElem!_ofFn {α : Type u} [Inhabited α] {n : Nat} {f : Fin n → α} {i : Nat} (h : i < n) :
    (ofFn f)[i]! = f ⟨i, h⟩ := by
  rw [getElem!_pos _ i h, getElem_ofFn]

end Vector

/-! ### Arrays -/

namespace Array

theorem getElem!_map_range {α : Type u} [Inhabited α] (f : Nat → α) {n j : Nat} (hj : j < n) :
    ((Array.range n).map f)[j]! = f j := by
  simp [hj]

theorem getElem!_mem {α : Type u} [Inhabited α] {xs : Array α} {i : Nat} (h : i < xs.size) :
    xs[i]! ∈ xs :=
  (getElem!_pos xs i h).symm ▸ getElem_mem h

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
    (h : ∀ y ∈ xs.toList, P y) (hx : P x) : ∀ y ∈ (xs.push x).toList, P y :=
  toList_push ▸ List.forall_mem_append.mpr ⟨h, List.forall_mem_singleton.mpr hx⟩

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

theorem flatMap_filter {α : Type u} {β : Type v} {l : List α} {p : α → Bool} {f : α → List β} :
    (l.filter p).flatMap f = l.flatMap fun a ↦ if p a then f a else [] := by
  induction l with
  | nil => rfl
  | cons a l ih => by_cases h : p a <;> simp [h, ih]

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

/-- The form of `List.mem_of_range'_eq_append_cons` for the list `ForIn.toList [a:m]` of a loop over
`[a:m]`: the cursor is below `m`. -/
theorem lt_of_toList_eq_append_cons {a m cur : Nat} {pref suff : List Nat}
    (h : ForIn.toList [a:m] = pref ++ cur :: suff) : cur < m := by
  have : cur ∈ ForIn.toList [a:m] := by simp [h]
  simp only [Std.Internal.ForIn.toList_range, List.mem_range'_1, size] at this
  lia

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
    _ ≤ 2 ^ N := Nat.pow_le_pow_right Nat.two_pos hn

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

/-- For `m p = N + δ` and `u δ < N`, the product `m u` is `L + N ⌊u / p⌋` for some `L < N` with
`L p = u δ + N (u mod p)`: the product of `u` with a reciprocal `m` of `p` scaled by `N`, rounded
up when `δ ≥ 0` is small. -/
theorem exists_mul_eq_add_mul_div {u p m N δ : Nat} (hp : 0 < p) (hm : m * p = N + δ)
    (hu : u * δ < N) : ∃ L < N, m * u = L + N * (u / p) ∧ L * p = u * δ + N * (u % p) := by
  have hs := Nat.mod_lt u hp
  have hu' := Nat.div_add_mod u p
  generalize u / p = k, u % p = s at hs hu' ⊢
  have h1 : m * u = (k * δ + m * s) + N * k := by grind
  have h2 : (k * δ + m * s) * p = u * δ + N * s := by grind
  have h3 : N * (s + 1) ≤ N * p := Nat.mul_le_mul_left N hs
  exact ⟨k * δ + m * s, Nat.lt_of_mul_lt_mul_right (a := p) (by grind), h1, h2⟩

/-- The remainder by a reciprocal: for `m p = N + δ` and `u δ < N`, the low part `m u mod N` of the
product of `u` with `m`, times `p`, has the high part `u mod p`. -/
theorem mul_mod_mul_div_eq_mod_of_mul_eq_add {u p m N δ : Nat} (hp : 0 < p) (hm : m * p = N + δ)
    (hu : u * δ < N) : m * u % N * p / N = u % p := by
  obtain ⟨L, hL, h1, h2⟩ := exists_mul_eq_add_mul_div hp hm hu
  rw [h1, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hL, h2, Nat.add_mul_div_left _ _ (by lia),
    Nat.div_eq_of_lt hu, Nat.zero_add]

/-- The quotient by a reciprocal: for `m p = N + δ` and `u δ < N`, the high part of the product of
`u` with `m` is `⌊u / p⌋`. -/
theorem mul_div_eq_div_of_mul_eq_add {u p m N δ : Nat} (hp : 0 < p) (hm : m * p = N + δ)
    (hu : u * δ < N) : m * u / N = u / p := by
  obtain ⟨L, hL, h1, -⟩ := exists_mul_eq_add_mul_div hp hm hu
  rw [h1, Nat.add_mul_div_left _ _ (by lia), Nat.div_eq_of_lt hL, Nat.zero_add]

/-- Removing the factors `2` of `x = 2 ^ t y` keeps its gcd with an odd `n`. -/
theorem gcd_eq_of_two_pow_mul_eq {x y n t : Nat} (h : 2 ^ t * y = x) (hn : n % 2 = 1) :
    gcd y n = gcd x n := by
  rw [← h, Coprime.gcd_mul_left_cancel _ (Coprime.pow_left _ ?_)]
  rw [Coprime, Nat.gcd_rec, hn, Nat.gcd_one_left]

/-- The odd part `y` of the distance of two odd numbers `m` and `n` has with the smaller of the two
the gcd of `m` and `n`: the step of the binary algorithm for the gcd. -/
theorem gcd_min_eq_gcd_of_two_pow_mul_eq {m n y t : Nat} (hm : m % 2 = 1) (hn : n % 2 = 1)
    (h : 2 ^ t * y = if m < n then n - m else m - n) : gcd y (min m n) = gcd m n := by
  rw [gcd_eq_of_two_pow_mul_eq h (by lia)]
  by_cases hlt : m < n
  · simp only [hlt, ↓reduceIte, Nat.min_eq_left (Nat.le_of_lt hlt),
      Nat.gcd_sub_self_left (Nat.le_of_lt hlt), Nat.gcd_comm]
  · simp only [hlt, ↓reduceIte, Nat.min_eq_right (Nat.le_of_not_lt hlt),
      Nat.gcd_sub_self_left (Nat.le_of_not_lt hlt)]

/-- A part `y` of the distance of two positive numbers, together with the smaller of the two, is
less than their sum: the measure of the binary algorithm for the gcd decreases. -/
theorem add_min_lt_add_of_two_pow_mul_eq {m n y t : Nat} (hm : 0 < m) (hn : 0 < n)
    (h : 2 ^ t * y = if m < n then n - m else m - n) : y + min m n < m + n := by
  have := Nat.le_mul_of_pos_left y (Nat.two_pow_pos t)
  split at h <;> lia

/-- The high half of the product of `2 ^ 32 a₁ + a₀` and `2 ^ 32 b₁ + b₀` from the four products
of the halves, as `Ratpoints.Sieve.mulHi` adds them: the high product, the high halves of the two
middle products, and the carry of the high half of the low product with the low halves of the
middle products. -/
theorem mul_div_two_pow_64_eq (a0 a1 b0 b1 : Nat) :
    (2 ^ 32 * a1 + a0) * (2 ^ 32 * b1 + b0) / 2 ^ 64 =
      a1 * b1 + a0 * b1 / 2 ^ 32 + a1 * b0 / 2 ^ 32 +
        (a0 * b0 / 2 ^ 32 + a0 * b1 % 2 ^ 32 + a1 * b0 % 2 ^ 32) / 2 ^ 32 := by
  have e : (2 ^ 32 * a1 + a0) * (2 ^ 32 * b1 + b0) =
      2 ^ 64 * (a1 * b1) + 2 ^ 32 * (a0 * b1 + a1 * b0) + a0 * b0 := by
    simp only [Nat.add_mul, Nat.mul_add]
    lia
  rw [e]
  generalize a0 * b0 = P0, a0 * b1 = P1, a1 * b0 = P2, a1 * b1 = P3
  lia

theorem mul_le_of_lt_two_pow_32 {x y : Nat} (hx : x < 2 ^ 32) (hy : y < 2 ^ 32) :
    x * y ≤ 2 ^ 64 - 2 ^ 33 + 1 :=
  Nat.le_trans (Nat.mul_le_mul (Nat.le_sub_one_of_lt hx) (Nat.le_sub_one_of_lt hy)) (by decide)

theorem mul_mod_of_mod_eq_one (a : Nat) {b q : Nat} (h : b % q = 1) : a * b % q = a % q := by
  rw [Nat.mul_mod, h, Nat.mul_one, Nat.mod_mod]

theorem mul_mod_eq_mul_mod_of_mod_eq {a a' : Nat} (b : Nat) {q : Nat} (h : a % q = a' % q) :
    a * b % q = a' * b % q := by
  rw [Nat.mul_mod, h, ← Nat.mul_mod]

/-- Scaling `b` by `u`, with an inverse `v` modulo `q`, keeps it zero modulo `q` or not. -/
theorem mul_mod_eq_zero_iff_of_mul_mod {q u v : Nat} (huv : v * u % q = 1 % q) (b : Nat) :
    u * b % q = 0 ↔ b % q = 0 := by
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [Nat.mul_mod, h, Nat.mul_zero, Nat.zero_mod]⟩
  rw [← Nat.one_mul b, ← Nat.mod_mul_mod, ← huv, Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod, h,
    Nat.mul_zero, Nat.zero_mod]

/-- Scaling `b` by `u`, with an inverse `v` modulo `q`, keeps its residue modulo `q` zero modulo a
divisor `p` of `q` or not. -/
theorem mul_mod_mod_eq_zero_iff_of_mul_mod {p q u v : Nat} (hpq : p ∣ q)
    (huv : v * u % q = 1 % q) (b : Nat) : u * b % q % p = 0 ↔ b % q % p = 0 := by
  rw [Nat.mod_mod_of_dvd _ hpq, Nat.mod_mod_of_dvd _ hpq]
  exact Nat.mul_mod_eq_zero_iff_of_mul_mod
    (by rw [← Nat.mod_mod_of_dvd _ hpq, huv, Nat.mod_mod_of_dvd _ hpq]) b

/-- The residue `x i mod q`, for an inverse `i` of `r` modulo `q`, is unchanged when `x` and `r`
are both scaled by `u`: `x' i' ≡ x i` for `x' ≡ u x`, `r' ≡ u r`, `i r ≡ 1` and `i' r' ≡ 1`. -/
theorem mul_mod_eq_mul_mod_of_mul_mod_eq_one {q u x x' r r' i i' : Nat}
    (hx : x' % q = u * x % q) (hr : r' % q = u * r % q) (hi : i * r % q = 1)
    (hi' : i' * r' % q = 1) : x' * i' % q = x * i % q := by
  calc x' * i' % q = x' * (i' * (i * r)) % q := by
        rw [← Nat.mul_assoc, Nat.mul_mod_of_mod_eq_one _ hi]
    _ = u * x * (i' * (i * r)) % q := Nat.mul_mod_eq_mul_mod_of_mod_eq _ hx
    _ = u * r * (i' * (x * i)) % q := congrArg (· % q) (by ac_rfl)
    _ = r' * (i' * (x * i)) % q := Nat.mul_mod_eq_mul_mod_of_mod_eq _ hr.symm
    _ = x * i * (i' * r') % q := congrArg (· % q) (by ac_rfl)
    _ = x * i % q := Nat.mul_mod_of_mod_eq_one _ hi'

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

theorem toNat_emod_lt (a : Int) {p : Nat} (hp : 0 < p) : (a % (p : Int)).toNat < p :=
  (toNat_lt' hp).mpr (emod_lt_of_pos a (by lia))

theorem toNat_mul_emod (u : Nat) (a : Int) {q : Nat} (hq : 0 < q) :
    ((u * a) % (q : Int)).toNat = u * (a % (q : Int)).toNat % q := by
  have h0 := Int.emod_nonneg a (b := q) (by lia)
  rw [← Int.toNat_natCast (u * (a % (q : Int)).toNat % q)]
  push_cast
  rw [Int.toNat_of_nonneg h0, Int.mul_emod (u : Int) (a % q), Int.emod_emod, ← Int.mul_emod]

theorem toNat_emod_mod_of_dvd (a : Int) {m p : Nat} (hm : 0 < m) (hpm : p ∣ m) :
    (a % (m : Int)).toNat % p = (a % (p : Int)).toNat := by
  have hp : 0 < p := Nat.pos_of_dvd_of_pos hpm hm
  rw [← natCast_inj, natCast_emod, toNat_of_nonneg (emod_nonneg _ (by lia)),
    toNat_of_nonneg (emod_nonneg _ (by lia)), emod_emod_of_dvd _ (natCast_dvd_natCast.mpr hpm)]

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

/-- A divisor `p > 1` of `b` does not divide a numerator `a` prime to `b`. -/
theorem toNat_emod_ne_zero_of_gcd_eq_one {p : Nat} (hp : 1 < p) {a : Int} {b : Nat}
    (hab : gcd a b = 1) (hb : b % p = 0) : (a % (p : Int)).toNat ≠ 0 := by
  intro ha
  have hp0 : (p : Int) ≠ 0 := by lia
  have hpa : (p : Int) ∣ a := dvd_of_emod_eq_zero (by have := emod_nonneg a hp0; lia)
  have hpb : (p : Int) ∣ b := natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hb)
  have := dvd_gcd hpa hpb
  rw [hab, Nat.dvd_one] at this
  lia

/-- C's remainder `a.tmod p`, which truncates, plus `p` if it is negative, is the Euclidean
remainder `a % p`, for `p > 0`. -/
theorem ite_tmod_lt_zero_eq_emod (a : Int) {p : Int} (hp : 0 < p) :
    (if a.tmod p < 0 then a.tmod p + p else a.tmod p) = a % p := by
  grind [tmod_eq_emod, emod_nonneg a (Int.ne_of_gt hp), emod_lt_of_pos a hp, emod_emod_of_dvd]

theorem toNat_emod_mul_emod (a : Int) {p : Nat} (b : Nat) (hp : 0 < p) :
    (a % p * b % p).toNat = (a % p).toNat * b % p := by
  have h := emod_nonneg a (b := p) (by lia)
  apply ofNat_inj.mp
  rw [toNat_of_nonneg (emod_nonneg _ (by lia))]
  push_cast
  rw [toNat_of_nonneg h]

/-- The shift by the multiple `p H` of `p` keeps the residue modulo `p` of `a binv`. -/
theorem toNat_mul_add_natCast_mul_mod {a : Int} {p binv H : Nat} (hp : 0 < p)
    (h : 0 ≤ a * binv + (p * H : Nat)) :
    (a * binv + (p * H : Nat)).toNat % p = (a % p).toNat * binv % p := by
  rw [← toNat_emod_mul_emod a binv hp]
  apply ofNat_inj.mp
  rw [toNat_of_nonneg (emod_nonneg _ (by lia)), natCast_emod, toNat_of_nonneg h, natCast_mul,
    add_mul_emod_self_left]
  conv => rhs; rw [mul_emod, emod_emod, ← mul_emod]

theorem natAbs_mul_add_le_mul {a : Int} {b p H : Nat} (ha : a.natAbs ≤ H) (hb : b < p) :
    (a * b).natAbs + H ≤ p * H := by
  rw [natAbs_mul, natAbs_natCast, Nat.mul_comm p]
  exact Nat.le_trans (Nat.add_le_add_right (Nat.mul_le_mul_right b ha) H) (Nat.mul_le_mul_left H hb)

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

theorem toNat_shiftRight_32 (x : UInt64) : (x >>> 32).toNat = x.toNat / 2 ^ 32 := by
  simp [UInt64.toNat_shiftRight, Nat.shiftRight_eq_div_pow]

theorem toNat_and_0xffffffff (x : UInt64) :
    (x &&& 0xffffffff).toNat = x.toNat % 2 ^ 32 := by
  simpa using Nat.and_two_pow_sub_one_eq_mod x.toNat 32

end UInt64

/-! ### Signed words -/

namespace Int64

/-- The arithmetic shift `>>>` of a `long` by `k < 64` is the shift of its value, the floor of its
quotient by `2 ^ k`. -/
theorem toInt_shiftRight_ofNat (x : Int64) {k : Nat} (hk : k < 64) :
    (x >>> ofNat k).toInt = x.toInt >>> k := by
  rw [toInt, Int64.toBitVec_shiftRight, BitVec.toInt_sshiftRight']
  have h1 : (BitVec.ofNat 64 k).msb = false := by simp [BitVec.msb_eq_decide]; lia
  have h2 : (64#64).msb = false := by decide
  simp [BitVec.smod, h1, h2, Nat.mod_eq_of_lt hk]

/-- The mask `x >>> 63` of a `long` is `-1` for a negative one and `0` otherwise. -/
theorem shiftRight_63 (x : Int64) : x >>> 63 = if x < 0 then -1 else 0 := by
  have h := toInt_shiftRight_ofNat x (k := 63) (by decide)
  rw [Int.shiftRight_eq_div_pow] at h
  have := x.toInt_lt
  have := x.le_toInt
  refine toInt_inj.mp (h.trans ?_)
  split <;> grind [lt_iff_toInt_lt]

theorem and_shiftRight_63 (x : Int64) : x &&& x >>> 63 = if x < 0 then x else 0 := by
  rw [shiftRight_63]
  split <;> simp

theorem xor_shiftRight_63_sub (x : Int64) :
    (x ^^^ x >>> 63) - x >>> 63 = if x < 0 then -x else x := by
  rw [shiftRight_63]
  split <;> simp [not_eq_neg_sub]

theorem sub_lt_zero_iff_of_nonneg {a b : Int64} (ha : 0 ≤ a) (hb : 0 ≤ b) : a - b < 0 ↔ a < b := by
  have := a.toInt_lt
  have := b.toInt_lt
  grind [lt_iff_toInt_lt, le_iff_toInt_le, toInt_sub, Int.bmod_eq_of_le]

/-- `n + (d &&& d >>> 63)` for `d = m - n` is the smaller of two non-negative `long`s `m` and `n`,
without a branch. -/
theorem toNatClampNeg_add_and_shiftRight_63 {m n : Int64} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    (n + (m - n &&& (m - n) >>> 63)).toNatClampNeg = min m.toNatClampNeg n.toNatClampNeg := by
  rw [and_shiftRight_63]
  have := toInt_eq_toNatClampNeg hm
  have := toInt_eq_toNatClampNeg hn
  have := sub_lt_zero_iff_of_nonneg hm hn
  split <;> grind [lt_iff_toInt_lt]

/-- `(d ^^^ d >>> 63) - d >>> 63` for `d = m - n` is the distance of two non-negative `long`s `m`
and `n`, without a branch. -/
theorem toNatClampNeg_xor_shiftRight_63_sub {m n : Int64} (hm : 0 ≤ m) (hn : 0 ≤ n) :
    ((m - n ^^^ (m - n) >>> 63) - (m - n) >>> 63).toNatClampNeg =
      if m.toNatClampNeg < n.toNatClampNeg then n.toNatClampNeg - m.toNatClampNeg
      else m.toNatClampNeg - n.toNatClampNeg := by
  rw [xor_shiftRight_63_sub]
  have := toInt_eq_toNatClampNeg hm
  have := toInt_eq_toNatClampNeg hn
  have := sub_lt_zero_iff_of_nonneg hm hn
  split <;> grind [lt_iff_toInt_lt, Int64.neg_sub, toNatClampNeg_sub_of_le]

theorem xor_shiftRight_63_sub_pos {m n : Int64} (hm : 0 ≤ m) (hn : 0 ≤ n) (h : m ≠ n) :
    (0 : Int64) < (m - n ^^^ (m - n) >>> 63) - (m - n) >>> 63 := by
  have := ofNat_toNatClampNeg m hm
  have := ofNat_toNatClampNeg n hn
  have hne : m.toNatClampNeg ≠ n.toNatClampNeg := fun h' ↦ h (by grind)
  rw [← toNatClampNeg_pos_iff, toNatClampNeg_xor_shiftRight_63_sub hm hn]
  split <;> lia

theorem toNatClampNeg_shiftRight_ofNat {x : Int64} (hx : 0 ≤ x) {k : Nat} (hk : k < 64) :
    (x >>> ofNat k).toNatClampNeg = x.toNatClampNeg >>> k := by
  rw [← toNat_toInt, toInt_shiftRight_ofNat x hk, toInt_eq_toNatClampNeg hx,
    ← Int.natCast_shiftRight, Int.toNat_natCast]

theorem toUInt64_eq_ofNat_toNatClampNeg {x : Int64} (hx : 0 ≤ x) :
    x.toUInt64 = UInt64.ofNat x.toNatClampNeg := by
  rw [← toNat_toUInt64_of_le hx, UInt64.ofNat_toNat]

theorem toUInt64_ne_zero_of_pos {x : Int64} (hx : 0 < x) : x.toUInt64 ≠ 0 := by
  rw [toUInt64_eq_ofNat_toNatClampNeg (Int64.le_of_lt hx)]
  exact UInt64.ofNat_ne_zero_of_lt ((toNatClampNeg_pos_iff x).mpr hx)
    (Nat.lt_trans x.toNatClampNeg_lt (by decide))

/-- A positive `long` `x` is `2 ^ t` times `x >>> t`, for the position `t` of the lowest set bit of
the word `x` read as unsigned. -/
theorem two_pow_ctz_mul_toNatClampNeg_shiftRight {x : Int64} (hx : 0 < x) :
    2 ^ x.toUInt64.toBitVec.ctz.toNat * (x >>> ofNat x.toUInt64.toBitVec.ctz.toNat).toNatClampNeg =
      x.toNatClampNeg := by
  rw [toNatClampNeg_shiftRight_ofNat (Int64.le_of_lt hx)
    (UInt64.toNat_ctz_lt (toUInt64_ne_zero_of_pos hx)), toUInt64_eq_ofNat_toNatClampNeg
    (Int64.le_of_lt hx)]
  exact UInt64.two_pow_ctz_mul_shiftRight_ofNat ((toNatClampNeg_pos_iff x).mpr hx)
    (Nat.lt_trans x.toNatClampNeg_lt (by decide))

/-- A positive `long` `x` shifted right by the position of the lowest set bit of the word `x` read
as unsigned is odd. -/
theorem toNatClampNeg_shiftRight_ctz_mod_two {x : Int64} (hx : 0 < x) :
    (x >>> ofNat x.toUInt64.toBitVec.ctz.toNat).toNatClampNeg % 2 = 1 := by
  rw [toNatClampNeg_shiftRight_ofNat (Int64.le_of_lt hx)
    (UInt64.toNat_ctz_lt (toUInt64_ne_zero_of_pos hx)), toUInt64_eq_ofNat_toNatClampNeg
    (Int64.le_of_lt hx)]
  exact UInt64.shiftRight_ctz_ofNat_mod_two ((toNatClampNeg_pos_iff x).mpr hx)
    (Nat.lt_trans x.toNatClampNeg_lt (by decide))

theorem and_one_beq_zero_iff {x : Int64} (hx : 0 ≤ x) :
    (x &&& 1 == 0) = true ↔ x.toNatClampNeg % 2 = 0 := by
  rw [beq_iff_eq, ← toNat_toUInt64_of_le hx, ← toNat_toBitVec, ← toBitVec_inj, ← BitVec.toNat_inj]
  simp [Nat.and_one_is_mod]

theorem toNatClampNeg_eq_natAbs {x : Int64} (hx : 0 ≤ x) : x.toNatClampNeg = x.toInt.natAbs := by
  have := le_iff_toInt_le.mp hx
  rw [← toNat_toInt]
  lia

/-- The absolute value of a `long` other than `-2 ^ 63`, whose negation would leave the range. -/
theorem toNatClampNeg_ite_neg {x : Int64} (h : minValue < x) :
    (if x < 0 then -x else x).toNatClampNeg = x.toInt.natAbs := by
  split
  · have h1 := lt_iff_toInt_lt.mp h
    have h2 := lt_iff_toInt_lt.mp ‹x < 0›
    rw [toInt_minValue] at h1
    rw [toInt_zero] at h2
    rw [← toNat_toInt, toInt_neg, Int.bmod_eq_of_le (by lia) (by lia)]
    lia
  · exact toNatClampNeg_eq_natAbs (Int64.not_lt.mp ‹_›)

theorem toNatClampNeg_eq_one_iff (x : Int64) : x.toNatClampNeg = 1 ↔ x = 1 := by
  rw [← toNat_toInt, ← toInt_inj, toInt_one]
  lia

theorem minValue_lt_ofInt {a : Int} (ha : a.natAbs < 2 ^ 63) : minValue < ofInt a := by
  rw [lt_iff_toInt_lt, toInt_minValue, toInt_ofInt_of_le (by lia) (by lia)]
  lia

theorem ofNat_pos {n : Nat} (h0 : 0 < n) (h : n < 2 ^ 63) : 0 < ofNat n := by
  rw [lt_iff_toInt_lt, toInt_zero, toInt_ofNat_of_lt h]
  lia

end Int64

end
