/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Std.Internal.ForIn.Lemmas

/-!
# Lemmas on vectors, arrays, lists, ranges and numbers for the contracts

Lemmas on vectors, arrays, lists, ranges, natural numbers and integers that the contracts of the
model need and Lean core lacks, under their names in the namespaces of Lean core: the entries of a
vector after `Vector.set!` and after a fold of `Vector.set!` over consecutive positions, the entries
of `Vector.ofFn f` and of the array of a vector, the entries of an array made by a map over a range
and of the vector of an array, the last entry and the entries of an array after `Array.set!`,
`Array.push`, `Array.pop` and `Array.map`, the order of the images of its members after
`Array.push`, the entries of the concatenation of two arrays and of an array written `k` times one
after the other, the entries of a list after `List.set`, the elements of `List.range n` that pass a
test which fails from some position on, the range below `k ≤ m` as the first part of the range below
`m`, `List.flatMap` over a filtered list, also with the filter moved into an inner `List.flatMap`,
the test of a list by the indices of its entries, the test of a nonempty list that and-s a fixed
Boolean with a test, the tests of a list that agree on its entries, the integers of a range that lie
in a smaller one or between two bounds, the gcd of the absolute values of a list of integers as a
left fold, the length of the list of a range and the position of the cursor of a loop over it, the
cursor of a loop over an array as one of its entries, the bounds `y < (n + 1) k` for `y < n k` and
`n ≤ (n + c - 1) k` for `c, k > 0`, word `κ < k` of block `j` of blocks of `k` words, below `c k`
for `j < c` and modulo `k p` word `κ` of block `j mod p`, the residues modulo `p` of the integers
from `a` on, the residue of a natural number modulo another as an integer, the residue of an integer
modulo `p`, below `p`, read off its residue modulo a multiple of `p` and shifted by a natural
number, exact quotients of integers, the numerators and the denominators of the set bits of a list
of words, read in turn, the numbers of a range between two bounds, bit 1 of odd numbers, the gcd of
half an even number with an odd one, a residue below `2 q` modulo `q` by one subtraction, the
position after another in a ring, the estimate of a quotient by Barrett's reduction, the bounds of a
step of Horner's rule and of a power of a number below a power of 2, the entries of an array of
Booleans after a fold of `setIfInBounds · true`, the absolute value of the step of the cofactors of
the extended Euclidean algorithm, the divisors of the gcd of `b` and a residue `f ≡ a (mod b)`, the
remainder and the quotient by a multiplication with a reciprocal, the high half of a product from
the products of the halves of its factors, the gcd of the odd part of a number with an odd one and
the step of the binary algorithm for the gcd, the residue modulo a divisor of `b` of a numerator
prime to `b`, C's remainder, which truncates, made non-negative, and the residue of `(a mod p) b`
with the bound `|a b| + H ≤ p H` for `|a| ≤ H` and `b < p`. For the rows under a unit: the residues
under a unit `u` with an inverse modulo `q`, zero or not, modulo a divisor of `q` too, the residue
`x i mod q` read with an inverse `i` of `r`, the residue `u (b v mod p)` for an inverse `v` of `u`,
and the residue of `u a` for an integer `a`. For the loops over two lists: the cursor of the second
list of a loop `for x in l, y in l.map f`, and a list whose next element is known. For the classes
of the packing: the residues in a packing of the stride `2 ^ k` dividing 64, the place
`(a - a₀) mod n / m` of a residue `a ≡ a₀ (mod m)` below `n = m P`, and a residue `a + m j` modulo
64. For the rows of offsets: the multiple `m ⌈R / m⌉` of `m > 0`, from `R` to below `R + m`, the
residue `(a y mod p + c) M` of `a` for a multiple `c` of `p` and an inverse `M` of `y`, and the
entries of a vector after `Vector.set`, of an array of `none`s and of an array whose list is a map.
For the residues and the bits of an interval: the numbers of a range in one class modulo `m`, the
multiples of `m` among `N + (m - r)`, a numerator `i - H` in a class modulo `m`, the quotient by
`m > 0` of a number above a negative bound, which stays above it, the quotients of the split form of
`numerators_to_bits`, its carries and their sums with a quotient, in the range of a `long`, the
multiples of a divisor of `N` at or below a number `≥ -N` and above a number `< N`, which lie in
`[-N, N]`, and the product `a ^ m a ^ (n - m) = a ^ n` of integers. The lemmas on 64-bit words are
in `Ratpoints.Proof.Bits`.

## Main statements

* `Vector.getElem!_set!_self`, `Vector.getElem!_set!_ne`: the entries of a vector after
  `Vector.set!`, at the place set and elsewhere.
* `Vector.getElem!_fold_set!`: the entries of a vector after a fold of `Vector.set!` over the
  positions `base, …, base + k - 1`.
* `List.getElem!_set`: the entries of a list after `List.set`.
* `List.filter_range_eq_of_le`, `List.filter_range_succ_eq_append`: the elements of `List.range n`
  that pass a test which fails from `k` on are those of `List.range k`, followed by the next one
  that passes it.
* `List.filter_map_range_eq_map_range`: of the integers `s, …, s + m - 1`, those from `s + k₁` to
  `s + m - 1 - k₂`; `List.filter_map_range_eq_map_range'`: those from `lo` to `hi`;
  `List.filter_map_range_eq_map_range_of_le`: those from `lo` to `hi` within the range, as a range.
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
  `[a:m]`, below `m`, and the lengths of the lists before and after it;
  `Std.Legacy.Range.mem_toList_of_lt`: a number below `m` is in the list of a loop over `[0:m]`.
* `Array.getElem!_pop`, `Array.getElem!_pop_of_back!_eq`: the entries of an array without its last
  entry, the same as before when that entry is the default value.
* `Array.getElem!_set!`: the entries of an array after `Array.set!`.
* `Array.getElem!_append`, `Array.getElem!_fold_append`: the entries of the concatenation of two
  arrays, and of an array written `k` times one after the other.
* `Array.getElem!_mem`: an entry in range of an array is a member of it.
* `Array.getElem!_foldl_setIfInBounds`, `Array.any_id_eq_true_of_getElem!_eq_true`: the entries of
  an array of Booleans that a fold of `setIfInBounds · true` marks, and an array with a true entry.
* `Array.forall_mem_toList_push`: a property of the members of the list of an array after a push;
  `Array.pairwise_map_toList_push`: the order of the images of its members after a push;
  `Array.forall_getElem_push`: a predicate on the indices and the entries of an array after a push.
* `Array.mem_of_forIn_toList_eq_append_cons`: the cursor of a loop over an array is one of its
  entries.
* `List.foldl_gcd_natAbs_dvd_natAbs`: the gcd of the absolute values of the entries of a list, as a
  left fold, divides each of them.
* `List.all_range_length_getElem!`, `List.all_and_left`, `List.all_congr_left`: the test of a list
  by the indices of its entries, the test of a nonempty list that and-s a fixed Boolean with a test,
  and the tests of a list that agree on its entries.
* `Int.toNat_add_emod_of_lt`, `Int.toNat_add_add_emod`: the residues modulo `p` of `a + j` before
  and from the first multiple of `p` from `a` on.
* `Int.toNat_emod_lt`, `Int.toNat_emod_mod_of_dvd`, `Int.toNat_emod_add_mod`: the residue of `a`
  modulo `p > 0` is below `p`, for `p ∣ m` it is the residue modulo `p` of the residue of `a` modulo
  `m`, and that of the residue plus `x` is the residue of `a + x`.
* `Nat.and_two_ne_zero_iff`, `Nat.and_and_two_ne_zero_iff`: bit 1 of odd numbers says whether they
  are `3 (mod 4)`; `Nat.gcd_div_two_of_mod_two`: halving an even number keeps its gcd with an odd
  one; `Nat.mod_eq_ite_of_lt_two_mul`: a residue below `2 q` modulo `q` by one subtraction, and
  `Nat.ite_eq_add_one_mod_add_one`: the position after `a` in a ring of `n + 1` positions.
* `Nat.mul_sub_one_div_div_mul_le`, `Nat.lt_mul_sub_one_div_div_add_two_mul`: Barrett's estimate
  `⌊u ⌊(N - 1) / p⌋ / N⌋` of `⌊u / p⌋` for `u < N` is the quotient or one less.
* `Nat.mul_add_lt_mul_of_lt`, `Nat.pow_lt_two_pow_of_lt`: a step of Horner's rule multiplies a bound
  by `p`, and `p ^ n < 2 ^ N` for `p < 2 ^ b`, `n ≠ 0` and `b n ≤ N`.
* `Nat.mul_add_lt_mul_of_lt_of_lt'`, `Nat.mul_add_mod_mul_of_lt`: word `κ < k` of block `j < c` of
  `c` blocks of `k` words is below `c k`, and modulo `k p` it is word `κ` of block `j mod p`.
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
* `Nat.mul_div_two_pow_64_eq`: the high half of a product from the products of the halves of 32
  bits of its factors.
* `Nat.mul_mod_eq_zero_iff_of_mul_mod`, `Nat.mul_mod_eq_mul_mod_of_mul_mod_eq_one`: scaling by a
  unit `u` with an inverse modulo `q` keeps a residue zero or not, and keeps the residue `x i mod q`
  read with an inverse `i` of `r` when `x` and `r` are both scaled.
* `Nat.sub_mod_div_eq_mod_iff`: the place `(a - a₀) mod n / m` of a residue `a ≡ a₀ (mod m)` below
  `n = m P`, in a packing of stride `m`.
* `Nat.le_mul_add_sub_one_div`, `Nat.mul_add_sub_one_div_lt`: the multiple `m ⌈R / m⌉` of `m > 0`
  lies from `R` to below `R + m`, as the bias of a modulus does.
* `Nat.eq_of_mod_eq_zero_of_le_of_lt`: the multiples of `p` lie `p` apart, as the loop over the
  multiples of `p` of `examine_power` steps through them.
* `List.filter_range_mod_eq`: the numbers below `N` that are `r` modulo `m > r`, `r, r + m, …`.
* `Int.ediv_add_emod_sub_add_sub_one_ediv`, `Int.ediv_add_emod_sub_ediv`: the two ends of the split
  form of `numerators_to_bits`, `⌈(lo - a₀) / m⌉` and `⌊(hi - a₀) / m⌋`.
* `Int.neg_le_mul_ediv_of_dvd`, `Int.mul_ediv_add_one_le_of_dvd`: for a divisor `d > 0` of `N`, the
  multiple of `d` at or below a number `lo ≥ -N` and the one above a number `hi < N` lie in
  `[-N, N]`.
* `List.next?_drop_map`, `List.next?_drop_map_ne_none`: the cursor of the second list of a loop
  `for x in l, y in l.map f`.

## Implementation notes

The file uses Lean core and `Std` only, so that the `grind` calls of the proofs see only the lemmas
of core, untouched by the updates of Mathlib.
-/

@[expose] public section

universe u v w

/-! ### Vectors -/

namespace Vector

theorem getElem!_set! {α : Type u} [Inhabited α] {n : Nat} {xs : Vector α n} {i j : Nat} {x : α}
    (hj : j < n) : (xs.set! i x)[j]! = if i = j then x else xs[j]! := by
  rw [getElem!_pos (xs.set! i x) j hj, getElem!_pos xs j hj, getElem_set! hj]

theorem getElem!_set!_self {α : Type u} [Inhabited α] {n i : Nat} {xs : Vector α n} {x : α}
    (hi : i < n) : (xs.set! i x)[i]! = x := by
  rw [getElem!_set! hi, ite_eq_left rfl]

theorem getElem!_set!_ne {α : Type u} [Inhabited α] {n i j : Nat} {xs : Vector α n} {x : α}
    (h : i ≠ j) : (xs.set! i x)[j]! = xs[j]! := by
  by_cases hj : j < n
  · rw [getElem!_set! hj, ite_eq_right h]
  · rw [getElem!_neg (xs.set! i x) j hj, getElem!_neg xs j hj]

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

theorem getElem!_set {α : Type u} [Inhabited α] {n : Nat} {xs : Vector α n} {i j : Nat}
    {x : α} (hi : i < n) (hj : j < n) : (xs.set i x hi)[j]! = if i = j then x else xs[j]! := by
  rw [getElem!_pos _ j hj, getElem!_pos xs j hj, Vector.getElem_set]

theorem getElem!_toArray {α : Type u} [Inhabited α] {n : Nat} (xs : Vector α n) (i : Nat) :
    xs.toArray[i]! = xs[i]! := by
  by_cases h : i < n
  · rw [getElem!_pos xs.toArray i (by simpa using h), getElem!_pos xs i h]
    rfl
  · rw [getElem!_neg xs.toArray i (by simpa using h), getElem!_neg xs i h]

end Vector

/-! ### Arrays -/

namespace Array

theorem getElem!_set! {α : Type u} [Inhabited α] {xs : Array α} {i j : Nat} {x : α}
    (hj : j < xs.size) : (xs.set! i x)[j]! = if i = j then x else xs[j]! := by
  grind

theorem getElem!_toVector {α : Type u} [Inhabited α] {xs : Array α} (i : Nat) :
    xs.toVector[i]! = xs[i]! :=
  (Vector.getElem!_toArray ..).symm

theorem getElem!_map_range {α : Type u} [Inhabited α] (f : Nat → α) {n j : Nat} (hj : j < n) :
    ((Array.range n).map f)[j]! = f j := by
  simp [hj]

theorem getElem!_append {α : Type u} [Inhabited α] {xs ys : Array α} (i : Nat) :
    (xs ++ ys)[i]! = if i < xs.size then xs[i]! else ys[i - xs.size]! := by
  by_cases h : i < xs.size <;> simp [getElem!_def, Array.getElem?_append, h]

/-- The array `w` written `k` times one after the other has `k` times its size. -/
theorem size_fold_append {α : Type u} (w : Array α) (k : Nat) :
    (Nat.fold k (fun _ _ s ↦ s ++ w) #[]).size = w.size * k := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.fold_succ, Array.size_append, ih, Nat.mul_succ]

/-- Entry `x` of the array `w` written `k` times one after the other is entry `x mod w.size` of
`w`. -/
theorem getElem!_fold_append {α : Type u} [Inhabited α] (w : Array α) {k x : Nat}
    (hx : x < w.size * k) : (Nat.fold k (fun _ _ s ↦ s ++ w) #[])[x]! = w[x % w.size]! := by
  induction k with
  | zero => simp at hx
  | succ k ih =>
    rw [Nat.fold_succ, getElem!_append, size_fold_append]
    split
    · exact ih ‹_›
    · rw [Nat.mul_succ] at hx
      obtain ⟨u, rfl⟩ : ∃ u, x = w.size * k + u := ⟨x - w.size * k, by lia⟩
      rw [Nat.add_sub_cancel_left, Nat.add_comm, Nat.add_mul_mod_self_left,
        Nat.mod_eq_of_lt (by lia)]

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

/-- A predicate on the indices and the entries of `xs` that holds at every index of `xs`, and at
`xs.size` for `a`, holds at every index of `xs.push a`. -/
theorem forall_getElem_push {α : Type u} {P : Nat → α → Prop} {xs : Array α} {a : α}
    (h : ∀ i (hi : i < xs.size), P i xs[i]) (ha : P xs.size a) (i : Nat)
    (hi : i < (xs.push a).size) : P i (xs.push a)[i] := by
  rw [getElem_push]
  split
  · exact h i ‹_›
  · obtain rfl : i = xs.size := by simp at hi; lia
    exact ha

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

/-- The images under `f` of the members of the list of an array after a push of `x` are pairwise
related by `R` exactly when those before are and each of them is related to the image of `x`, as
invariants of loops state the order of the entries. -/
theorem pairwise_map_toList_push {α : Type u} {β : Type v} {R : β → β → Prop} {f : α → β}
    {xs : Array α} {x : α} :
    ((xs.push x).toList.map f).Pairwise R ↔
      (xs.toList.map f).Pairwise R ∧ ∀ y ∈ xs.toList, R (f y) (f x) := by
  simp [List.pairwise_append]

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

theorem getElem!_replicate_none {α : Type u} (n K : Nat) :
    (Array.replicate n (none : Option α))[K]! = none := by
  by_cases h : K < n
  · simp [h]
  · exact getElem!_neg _ K (by simpa using h)

theorem getElem!_of_toList_eq_map {α : Type u} {β : Type v} [Inhabited β] {xs : Array β}
    {l : List α} {f : α → β} (h : xs.toList = l.map f) {n : Nat} (hn : n < l.length) :
    xs[n]! = f l[n] := by
  have hs : n < xs.size := by rwa [← Array.length_toList, h, List.length_map]
  rw [getElem!_pos xs n hs, ← Array.getElem_toList]
  simp only [h, List.getElem_map]

end Array

/-! ### Lists -/

namespace List

theorem getElem!_set {α : Type u} [Inhabited α] {l : List α} {i j : Nat} (h : j < l.length)
    (x : α) : (l.set i x)[j]! = if i = j then x else l[j]! := by
  rw [getElem!_pos _ j (by simpa using h), getElem_set, getElem!_pos l j h]

/-- The numbers below `k ≤ m` come first among those below `m`. -/
theorem range_prefix_range {k m : Nat} (h : k ≤ m) : range k <+: range m := by
  simpa [take_range, Nat.min_eq_left h] using take_prefix k (range m)

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
    lia [mem_range.mp hk]

/-- Of the integers `s, …, s + m - 1`, for `s ≤ lo` and `hi < s + m`, those from `lo` to `hi`. -/
theorem filter_map_range_eq_map_range_of_le {s lo hi : Int} {m : Nat} (h1 : s ≤ lo)
    (h2 : hi < s + m) :
    ((range m).map fun k : Nat ↦ s + k).filter (fun a ↦ decide (lo ≤ a ∧ a ≤ hi)) =
      (range (hi + 1 - lo).toNat).map fun k : Nat ↦ lo + k := by
  have hm : m - (lo - s).toNat - (s + m - 1 - hi).toNat = (hi + 1 - lo).toNat := by lia
  rw [filter_map_range_eq_map_range', hm]
  exact map_congr_left fun k _ ↦ by lia

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

/-- The filter of the outer list of a double `List.flatMap` moved into the filter of the inner
one. -/
theorem flatMap_filter_flatMap_filter {α : Type u} {β : Type v} {γ : Type w} (l : List α)
    (q : α → Bool) (xs : List β) (T : α → β → Bool) (g : α → β → List γ) :
    (l.filter q).flatMap (fun b ↦ (xs.filter (T b)).flatMap (g b)) =
      l.flatMap fun b ↦ (xs.filter fun a ↦ q b && T b a).flatMap (g b) := by
  induction l with
  | nil => rfl
  | cons b l ih => cases h : q b <;> simp [h, ih]

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

/-- The cursor of the second list of a loop `for x in l, y in l.map f`, after the entries `pref` of
`l`, at the entry `a`: the next value is `f a`, and the rest of the list follows. -/
theorem next?_drop_map {α : Type u} {β : Type v} (f : α → β) {l pref suff : List α} {a : α}
    (hl : l = pref ++ a :: suff) {b : β} {rest : List β}
    (h : Std.Stream.next? ((l.map f).drop pref.length) = some (b, rest)) :
    b = f a ∧ rest = (l.map f).drop (pref.length + 1) := by
  subst hl
  rw [map_append, map_cons, drop_left' (length_map ..)] at h
  rw [map_append, map_cons, ← drop_drop, drop_left' (length_map ..)]
  simp only [Std.Stream.next?, Option.some.injEq, Prod.mk.injEq] at h
  exact ⟨h.1.symm, by rw [← h.2]; rfl⟩

/-- The second list of a loop `for x in l, y in l.map f` does not run out before the first. -/
theorem next?_drop_map_ne_none {α : Type u} {β : Type v} (f : α → β) {l pref suff : List α}
    {a : α} (hl : l = pref ++ a :: suff) :
    Std.Stream.next? ((l.map f).drop pref.length) ≠ none := by
  subst hl
  simp [Std.Stream.next?]

theorem eq_cons_of_next?_eq_some {α : Type u} {l l' : List α} {b : α}
    (h : Std.Stream.next? l = some (b, l')) : l = b :: l' := by
  cases l <;> simp_all [Std.Stream.next?]

/-- A test of the entries of a list by their indices is the test of the list. -/
theorem all_range_length_getElem! {α : Type u} [Inhabited α] (l : List α) (P : α → Bool) :
    ((range l.length).all fun i ↦ P l[i]!) = l.all P := by
  rw [Bool.eq_iff_iff, all_eq_true, all_eq_true]
  refine ⟨fun h a ha ↦ ?_, fun h i hi ↦ ?_⟩
  · obtain ⟨i, hi, rfl⟩ := getElem_of_mem ha
    simpa [getElem!_pos l i hi] using h i (mem_range.mpr hi)
  · rw [getElem!_pos l i (mem_range.mp hi)]
    exact h _ (getElem_mem _)

/-- A test of the entries of a nonempty list that and-s a fixed Boolean with a test is the Boolean
and-ed with the test of the list. -/
theorem all_and_left {α : Type u} {l : List α} (hl : l ≠ []) (c : Bool) (P : α → Bool) :
    (l.all fun a ↦ c && P a) = (c && l.all P) := by
  cases c
  · obtain ⟨a, l, rfl⟩ := exists_cons_of_ne_nil hl
    simp
  · simp

theorem all_congr_left {α : Type u} {l : List α} {P Q : α → Bool} (h : ∀ a ∈ l, P a = Q a) :
    l.all P = l.all Q := by
  grind

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

/-- A number below `m` is in the list of a loop over `[0:m]`. -/
theorem mem_toList_of_lt {x m : Nat} (h : x < m) : x ∈ ForIn.toList [0:m] := by
  simp [Std.Internal.ForIn.toList_range, List.mem_range'_1, size, h]

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

/-- Word `κ < k` of block `j < c` of `c` blocks of `k` words is below `c k`: the statement of
Batteries' `Nat.mul_add_lt_mul_of_lt_of_lt`, for the files that use Lean core only. -/
theorem mul_add_lt_mul_of_lt_of_lt' {k c j κ : Nat} (hj : j < c) (hκ : κ < k) :
    k * j + κ < c * k := by
  rw [Nat.mul_comm c]
  lia [Nat.mul_le_mul_left k (show j + 1 ≤ c from hj)]

/-- Word `κ < k` of block `x` is word `κ` of block `x mod p` in the words modulo `k p`. -/
theorem mul_add_mod_mul_of_lt {k x κ p : Nat} (hκ : κ < k) :
    (k * x + κ) % (k * p) = k * (x % p) + κ := by
  rw [Nat.mod_mul, Nat.mul_add_mod, Nat.mod_eq_of_lt hκ, Nat.mul_add_div (Nat.zero_lt_of_lt hκ),
    Nat.div_eq_of_lt hκ, Nat.add_zero, Nat.add_comm]

theorem pow_lt_two_pow_of_lt {p b n N : Nat} (hp : p < 2 ^ b) (hn : b * n ≤ N) (hn0 : n ≠ 0) :
    p ^ n < 2 ^ N :=
  calc p ^ n < (2 ^ b) ^ n := Nat.pow_lt_pow_left hp hn0
    _ = 2 ^ (b * n) := (Nat.pow_mul 2 b n).symm
    _ ≤ 2 ^ N := Nat.pow_le_pow_right Nat.two_pos hn

theorem lt_add_one_mul_of_lt_mul {y n k : Nat} (h : y < n * k) : y < (n + 1) * k :=
  Nat.lt_of_lt_of_le h (Nat.mul_le_mul_right k (Nat.le_succ n))

/-- The first `n` words of `n + c - 1` blocks of `k` words, for `c, k > 0`, lie among them. -/
theorem le_add_sub_one_mul (n : Nat) {c k : Nat} (hc : 0 < c) (hk : 0 < k) :
    n ≤ (n + c - 1) * k :=
  Nat.le_trans (Nat.le_mul_of_pos_right n hk) (Nat.mul_le_mul_right k (by lia))

/-- A residue `a < 2 q` modulo `q` by one conditional subtraction. -/
theorem mod_eq_ite_of_lt_two_mul {a q : Nat} (h : a < 2 * q) :
    a % q = if q ≤ a then a - q else a := by
  split
  · rw [Nat.mod_eq_sub_mod ‹_›, Nat.mod_eq_of_lt (by lia)]
  · exact Nat.mod_eq_of_lt (by lia)

/-- The position after `a ≤ n` in a ring of the positions `0, …, n`, by a test for the last. -/
theorem ite_eq_add_one_mod_add_one {a n : Nat} (h : a ≤ n) :
    (if a = n then 0 else a + 1) = (a + 1) % (n + 1) := by
  split
  · subst a
    simp
  · exact (Nat.mod_eq_of_lt (by lia)).symm

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
  split at h <;> lia [Nat.le_mul_of_pos_left y (Nat.two_pow_pos t)]

/-- The high half of the product of `2 ^ 32 a₁ + a₀` and `2 ^ 32 b₁ + b₀` from the four products of
the halves, as `Ratpoints.Sieve.mulHi` adds them: the high product, the high halves of the two
middle products, and the carry of the high half of the low product with the low halves of the middle
products. -/
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

/-- `u (b v mod p) ≡ b (mod p)` for an inverse `v` of `u` modulo `p`. -/
theorem mul_mul_mod_mod_of_mul_mod_eq_one {p u v : Nat} (b : Nat) (h : v * u % p = 1) :
    u * (b * v % p) % p = b % p := by
  rw [Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_comm u b, Nat.mul_assoc, Nat.mul_comm u v,
    Nat.mul_mod_of_mod_eq_one _ h]

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

theorem le_and_sub_mod_eq_zero_iff {a s m : Nat} (hs : s < m) :
    (s ≤ a ∧ (a - s) % m = 0) ↔ a % m = s := by
  refine ⟨fun ⟨h1, h2⟩ ↦ ?_, fun h ↦ ⟨h ▸ Nat.mod_le a m, ?_⟩⟩
  · rw [← Nat.sub_add_cancel h1, Nat.add_mod, h2, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hs]
  · exact Nat.sub_mod_eq_zero_of_mod_eq (by rw [h, Nat.mod_eq_of_lt hs])

theorem two_pow_dvd_sixty_four {k : Nat} (hk : k ≤ 6) : 2 ^ k ∣ 64 :=
  Nat.pow_dvd_pow_iff_le_right'.mpr hk

theorem two_pow_mul_sixty_four_div {k : Nat} (hk : k ≤ 6) : 2 ^ k * (64 / 2 ^ k) = 64 :=
  Nat.mul_div_cancel' (Nat.pow_dvd_pow_iff_le_right'.mpr hk : 2 ^ k ∣ 2 ^ 6)

theorem sixty_four_div_two_pow {k : Nat} (hk : k ≤ 6) : 64 / 2 ^ k = 2 ^ (6 - k) :=
  Nat.pow_div hk (by decide : 0 < 2)

/-- For a residue `a ≡ a₀ (mod m)` below `n` and `m P = n`, the place `(a - a₀) mod n / m` of `a`
is `t mod P` exactly when `a` is `(a₀ + m t) mod n`. -/
theorem sub_mod_div_eq_mod_iff {a a0 m P t n : Nat} (hm : m * P = n) (ha : a < n)
    (haa : a % m = a0) :
    (a - a0) % n / m = t % P ↔ a = (a0 + m * t) % n := by
  have hm0 : 0 < m := Nat.pos_of_ne_zero (by rintro rfl; lia)
  have hP0 : 0 < P := Nat.pos_of_ne_zero (by rintro rfl; lia)
  have h1 := Nat.div_add_mod a m
  have h2 := Nat.div_add_mod t P
  have h3 : a / m < P := Nat.div_lt_of_lt_mul (by rwa [hm])
  have h4 := Nat.mod_lt t hP0
  have h6 : a0 < m := haa ▸ Nat.mod_lt a hm0
  have hlt : a0 + m * (t % P) < n := by lia [Nat.mul_le_mul_left m h4]
  have h5 : (a0 + m * t) % n = a0 + m * (t % P) := by
    have h7 : m * t = m * (t % P) + n * (t / P) := by grind
    rw [h7, ← Nat.add_assoc, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hlt]
  rw [h5, ← haa, Nat.mod_eq_of_lt (by lia : a - a % m < n)]
  have : a - a % m = m * (a / m) := by lia
  rw [this, Nat.mul_div_cancel_left _ hm0]
  constructor
  · intro h; rw [← h]; lia
  · intro h; exact Nat.eq_of_mul_eq_mul_left hm0 (by lia)

/-- The multiple `m ⌈R / m⌉ = m ((R + m - 1) / m)` of `m > 0` is at least `R`. -/
theorem le_mul_add_sub_one_div (R : Nat) {m : Nat} (hm : 0 < m) : R ≤ m * ((R + m - 1) / m) :=
  (Nat.le_mul_iff_le_right hm).mpr (Nat.le_refl _)

/-- The multiple `m ⌈R / m⌉ = m ((R + m - 1) / m)` of `m > 0` is below `R + m`. -/
theorem mul_add_sub_one_div_lt (R : Nat) {m : Nat} (hm : 0 < m) : m * ((R + m - 1) / m) < R + m :=
  Nat.lt_of_le_of_lt (Nat.mul_div_le _ m) (by lia)

/-- The residue `a y mod p` plus a multiple `c` of `p`, times an inverse `M` of `y` modulo `p`, is
`a` modulo `p`. -/
theorem mul_mod_add_mul_mod_eq_mod {p a y c M : Nat} (hy : y * M % p = 1) (hc : c % p = 0) :
    (a * y % p + c) * M % p = a % p := by
  rw [Nat.add_mul, Nat.add_mod, Nat.mul_mod c, hc, Nat.zero_mul, Nat.zero_mod, Nat.add_zero,
    Nat.mod_mod, Nat.mod_mul_mod, Nat.mul_assoc, Nat.mul_mod_of_mod_eq_one _ hy]

/-- `N + (m - r)` is a multiple of `m` exactly when `N` is `r` modulo `m`, for `r < m`. -/
theorem add_sub_mod_eq_zero_iff {N m r : Nat} (hr : r < m) :
    (N + (m - r)) % m = 0 ↔ N % m = r := by
  have hs := Nat.mod_lt N (by lia : 0 < m)
  have h1 := Nat.div_add_mod N m
  rw [show N + (m - r) = N % m + (m - r) + m * (N / m) by lia, Nat.add_mul_mod_self_left]
  rcases Nat.lt_trichotomy (N % m) r with h | h | h
  · rw [Nat.mod_eq_of_lt (by lia)]
    lia
  · rw [h, Nat.add_sub_cancel' (Nat.le_of_lt hr), Nat.mod_self]
    exact ⟨fun _ ↦ rfl, fun _ ↦ rfl⟩
  · rw [show N % m + (m - r) = N % m - r + m by lia, Nat.add_mod_right, Nat.mod_eq_of_lt (by lia)]
    lia

/-- A multiple `t'` of `p` from the multiple `t` of `p` on and below `t + p` is `t`. -/
theorem eq_of_mod_eq_zero_of_le_of_lt {p t t' : Nat} (ht : t % p = 0) (ht' : t' % p = 0)
    (hle : t ≤ t') (hlt : t' < t + p) : t' = t := by
  lia [Nat.eq_zero_of_dvd_of_lt (Nat.dvd_sub (Nat.dvd_of_mod_eq_zero ht')
    (Nat.dvd_of_mod_eq_zero ht)) (by lia)]

end Nat

/-- The numbers below `N` that are `r` modulo `m`, for `r < m`: `r, r + m, r + 2 m, …`, of which
there are `⌈(N - r) / m⌉`. -/
theorem List.filter_range_mod_eq {m r : Nat} (hr : r < m) (N : Nat) :
    (List.range N).filter (fun i ↦ i % m == r) =
      (List.range ((N + (m - 1 - r)) / m)).map fun j ↦ r + m * j := by
  induction N with
  | zero =>
    rw [List.range_zero, List.filter_nil, Nat.zero_add, Nat.div_eq_of_lt (by lia), List.range_zero,
      List.map_nil]
  | succ N ih =>
    have e : N + 1 + (m - 1 - r) = N + (m - 1 - r) + 1 := by lia
    have e' : N + (m - 1 - r) + 1 = N + (m - r) := by lia
    rw [List.range_succ, List.filter_append, ih, e]
    by_cases hN : N % m = r
    · rw [Nat.succ_div_of_mod_eq_zero (by rw [e']; exact (Nat.add_sub_mod_eq_zero_iff hr).mpr hN),
        List.range_succ, List.map_append]
      simp only [hN, beq_self_eq_true, List.filter_cons_of_pos, List.filter_nil, List.map_cons,
        List.map_nil]
      have h1 := Nat.div_add_mod N m
      rw [show N + (m - 1 - r) = m - 1 + m * (N / m) by lia, Nat.add_mul_div_left _ _ (by lia),
        Nat.div_eq_of_lt (by lia), Nat.zero_add]
      congr 2
      lia
    · rw [Nat.succ_div_of_mod_ne_zero (by rw [e']; exact mt (Nat.add_sub_mod_eq_zero_iff hr).mp hN)]
      simp [hN]

/-! ### Integers -/

namespace Int

/-- Before the first multiple of `p` from `a` on: for `r = (-a) mod p` and `j < r`, the residue of
`a + j` modulo `p` is `p - r + j`. -/
theorem toNat_add_emod_of_lt {a : Int} {p j : Nat} (hp : 0 < p) (hj : j < (-a % (p : Int)).toNat) :
    ((a + j) % (p : Int)).toNat = p - (-a % (p : Int)).toNat + j := by
  have := emod_lt_of_pos (-a) (b := p) (by lia)
  have key : a + j = p - -a % p + j + p * (-(-a / p) - 1) := by
    rw [Int.mul_sub, Int.mul_neg, Int.mul_one]
    lia [mul_ediv_add_emod (-a) p]
  rw [key, add_mul_emod_self_left, emod_eq_of_lt (by lia) (by lia)]
  lia

/-- From the first multiple of `p` from `a` on: for `r = (-a) mod p` and `i < p`, the residue of
`a + r + k p + i` modulo `p` is `i`. -/
theorem toNat_add_add_emod {a : Int} {p i k : Nat} (hi : i < p) :
    ((a + (((-a % (p : Int)).toNat + k * p + i : Nat) : Int)) % (p : Int)).toNat = i := by
  have hR : ((-a % (p : Int)).toNat : Int) = -a % p := toNat_of_nonneg (emod_nonneg _ (by lia))
  have key : a + (((-a % (p : Int)).toNat + k * p + i : Nat) : Int) = i + p * (k - -a / p) := by
    push_cast
    rw [hR, Int.mul_sub, Int.mul_comm (p : Int) k]
    lia [mul_ediv_add_emod (-a) p]
  rw [key, add_mul_emod_self_left, emod_eq_of_lt (by lia) (by lia)]
  simp

theorem toNat_emod_lt (a : Int) {p : Nat} (hp : 0 < p) : (a % (p : Int)).toNat < p :=
  (toNat_lt' hp).mpr (emod_lt_of_pos a (by lia))

@[simp]
theorem toNat_natCast_emod (a b : Nat) : ((a : Int) % (b : Int)).toNat = a % b := by
  rw [← natCast_emod, toNat_natCast]

theorem toNat_emod_add_mod (a : Int) (x : Nat) {p : Nat} (hp : 0 < p) :
    ((a % (p : Int)).toNat + x) % p = ((a + x) % (p : Int)).toNat := by
  rw [← toNat_natCast (((a % (p : Int)).toNat + x) % p)]
  congr 1
  push_cast
  rw [toNat_of_nonneg (emod_nonneg a (by lia)), emod_add_emod]

theorem toNat_mul_emod (u : Nat) (a : Int) {q : Nat} (hq : 0 < q) :
    (u * a % (q : Int)).toNat = u * (a % (q : Int)).toNat % q := by
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
  have hpa : (p : Int) ∣ a := dvd_of_emod_eq_zero (by lia [emod_nonneg a hp0])
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

/-- The residue modulo 64 of `a + m j` from that of `j`. -/
theorem toNat_add_mul_emod_sixty_four (a m : Nat) (j : Int) :
    ((a + m * j) % 64).toNat = (a + m * (j % 64).toNat) % 64 := by
  have h1 : (m : Int) * j = m * (j % 64) + 64 * (m * (j / 64)) := by
    rw [← Int.mul_assoc, Int.mul_comm 64, Int.mul_assoc, ← Int.mul_add, Int.emod_add_mul_ediv]
  have h2 : ((j % 64).toNat : Int) = j % 64 := Int.toNat_of_nonneg (Int.emod_nonneg j (by decide))
  rw [h1, ← h2, ← Int.add_assoc, Int.add_mul_emod_self_left]
  lia

theorem natCast_sub_natCast_emod_eq_iff {i H a0 m : Nat} (ha : a0 < m) :
    ((i : Int) - H) % m = a0 ↔ i % m = (a0 + H) % m := by
  have h1 : (a0 : Int) % m = a0 := Int.emod_eq_of_lt (by lia) (by lia)
  rw [← h1, Int.emod_eq_emod_iff_emod_sub_eq_zero, ← Int.ofNat_inj, Int.natCast_emod,
    Int.natCast_emod, Int.emod_eq_emod_iff_emod_sub_eq_zero]
  simp only [Int.natCast_add]
  rw [show (i : Int) - H - a0 = i - (a0 + H) by lia]

/-- `-⌊x / m⌋ = ⌊(m - 1 - x) / m⌋`, the ceiling of `-x / m`, for `m > 0`. -/
theorem neg_ediv_eq_sub_one_sub_ediv (x : Int) {m : Int} (hm : 0 < m) :
    -(x / m) = (m - 1 - x) / m := by
  have key (n : Int) : n ≤ -(x / m) ↔ n ≤ (m - 1 - x) / m := by
    rw [Int.le_neg_iff, Int.ediv_le_iff_le_mul hm, Int.le_ediv_iff_mul_le hm]
    constructor <;> intro h <;> lia
  exact Int.le_antisymm ((key _).mp (Int.le_refl _)) ((key _).mpr (Int.le_refl _))

/-- `⌊lo / m⌋ + ⌈(lo mod m - a₀) / m⌉ = ⌈(lo - a₀) / m⌉` for `m > 0`: the first bit of the split
form of `numerators_to_bits` (`Ratpoints.Sieve.numeratorsToBits`), from the multiple of `m` in `lo`
and its rest. -/
theorem ediv_add_emod_sub_add_sub_one_ediv (lo a0 : Int) {m : Int} (hm : 0 < m) :
    lo / m + (lo % m - a0 + (m - 1)) / m = -((a0 - lo) / m) := by
  have e1 : a0 - lo = a0 - lo % m + -(lo / m) * m := by lia [Int.emod_add_ediv_mul lo m]
  rw [e1, Int.add_mul_ediv_right _ _ (Int.ne_of_gt hm), Int.neg_add, Int.neg_neg,
    Int.neg_ediv_eq_sub_one_sub_ediv _ hm, Int.add_comm]
  congr 2
  lia

/-- `⌊hi / m⌋ + ⌊(hi mod m - a₀) / m⌋ = ⌊(hi - a₀) / m⌋` for `m > 0`: the last bit of the split form
of `numerators_to_bits` (`Ratpoints.Sieve.numeratorsToBits`). -/
theorem ediv_add_emod_sub_ediv (hi a0 : Int) {m : Int} (hm : 0 < m) :
    hi / m + (hi % m - a0) / m = (hi - a0) / m := by
  have e2 : hi - a0 = hi % m - a0 + hi / m * m := by lia [Int.emod_add_ediv_mul hi m]
  rw [e2, Int.add_mul_ediv_right _ _ (Int.ne_of_gt hm), Int.add_comm]

theorem lt_ediv_of_neg {c z m : Int} (hc : c < 0) (hz : c < z) (hm : 0 < m) : c < z / m := by
  rcases Int.lt_or_le z 0 with h | h
  · exact Int.lt_of_lt_of_le hz (self_le_ediv_of_nonpos_of_nonneg (by lia) (by lia))
  · exact Int.lt_of_lt_of_le hc (ediv_nonneg h (by lia))

theorem neg_two_pow_62_le_ediv_and_ediv_lt_two_pow_62 {z m : Int} (hz : -2 ^ 63 ≤ z)
    (hz' : z < 2 ^ 63) (hm : 2 ≤ m) :
    -2 ^ 62 ≤ z / m ∧ z / m < 2 ^ 62 :=
  ⟨(Int.le_ediv_iff_mul_le (by lia)).mpr (by lia), (Int.ediv_lt_iff_lt_mul (by lia)).mpr (by lia)⟩

/-- The carry `⌈(r - a₀) / m⌉` of the split form of `Ratpoints.Sieve.numeratorsToBits` at the low
end, for `0 ≤ r, a₀ < m`: `0` or `1`. -/
theorem sub_add_sub_one_ediv_nonneg_and_le_one {r a0 m : Int} (hr : 0 ≤ r) (hr' : r < m)
    (ha : 0 ≤ a0) (ha' : a0 < m) :
    0 ≤ (r - a0 + (m - 1)) / m ∧ (r - a0 + (m - 1)) / m ≤ 1 :=
  ⟨Int.ediv_nonneg (by lia) (by lia),
    Int.lt_add_one_iff.mp ((Int.ediv_lt_iff_lt_mul (by lia)).mpr (by lia))⟩

/-- The carry `⌊(r - a₀) / m⌋` of the split form of `Ratpoints.Sieve.numeratorsToBits` at the high
end, for `0 ≤ r, a₀ < m`: `-1` or `0`. -/
theorem neg_one_le_sub_ediv_and_sub_ediv_nonpos {r a0 m : Int} (hr : 0 ≤ r) (hr' : r < m)
    (ha : 0 ≤ a0) (ha' : a0 < m) :
    -1 ≤ (r - a0) / m ∧ (r - a0) / m ≤ 0 :=
  ⟨(Int.le_ediv_iff_mul_le (by lia)).mpr (by lia),
    Int.lt_add_one_iff.mp ((Int.ediv_lt_iff_lt_mul (by lia)).mpr (by lia))⟩

/-- For `m ≥ 1` and `-1 ≤ c ≤ 1`, with `c = 0` when `m = 1`, `z / m + c` is a `long` for a `long`
`z`: an arithmetic shift plus a carry, as in the split form of
`Ratpoints.Sieve.numeratorsToBits`. -/
theorem neg_two_pow_63_le_ediv_add_and_ediv_add_lt_two_pow_63 {z c m : Int} (hz : -2 ^ 63 ≤ z)
    (hz' : z < 2 ^ 63) (hm : 1 ≤ m) (hc : -1 ≤ c) (hc' : c ≤ 1) (h1 : m = 1 → c = 0) :
    -2 ^ 63 ≤ z / m + c ∧ z / m + c < 2 ^ 63 := by
  rcases Int.lt_or_le m 2 with h | h
  · rw [show m = 1 by lia, h1 (by lia), Int.ediv_one]
    lia
  · lia [Int.neg_two_pow_62_le_ediv_and_ediv_lt_two_pow_62 hz hz' h]

/-- The multiple `d ⌊lo / d⌋` of `d > 0` at or below `lo` is at least every multiple `-N ≤ lo` of
`d`. -/
theorem neg_le_mul_ediv_of_dvd {d N lo : Int} (hd : 0 < d) (hdN : d ∣ N) (hlo : -N ≤ lo) :
    -N ≤ d * (lo / d) := by
  obtain ⟨q, rfl⟩ := hdN
  rw [← Int.mul_neg]
  refine Int.mul_le_mul_of_nonneg_left ((Int.le_ediv_iff_mul_le hd).mpr ?_) (Int.le_of_lt hd)
  rwa [Int.neg_mul, Int.mul_comm]

/-- The multiple `d (⌊hi / d⌋ + 1)` of `d > 0` above `hi` is at most every multiple `N > hi` of
`d`. -/
theorem mul_ediv_add_one_le_of_dvd {d N hi : Int} (hd : 0 < d) (hdN : d ∣ N) (hhi : hi < N) :
    d * (hi / d + 1) ≤ N := by
  obtain ⟨q, rfl⟩ := hdN
  refine Int.mul_le_mul_of_nonneg_left (Int.add_one_le_of_lt ?_) (Int.le_of_lt hd)
  exact (Int.ediv_lt_iff_lt_mul hd).mpr (by rwa [Int.mul_comm])

theorem pow_mul_pow_sub (a : Int) {m n : Nat} (h : m ≤ n) : a ^ m * a ^ (n - m) = a ^ n := by
  rw [← Int.pow_add, Nat.add_sub_cancel' h]

end Int

end
