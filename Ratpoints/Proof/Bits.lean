/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

import Std.Internal.ForIn.Lemmas

/-!
# Lemmas on words

Lemmas on vectors, arrays, ranges, integers and 64-bit words that the contracts of the bit arrays
of words need and Lean core lacks, under their names in the namespaces of Lean core: the entries of
a vector after `Vector.set!` and after a fold of `Vector.set!` over consecutive positions, the
entries of an array made by a map over a range, the position of the cursor of a loop over a range,
the residues modulo `p` of the integers from `w0` on, the bits of the word `~~~0` and of the masks
`~~~0 <<< n` and `~~~0 >>> n`, the lowest bit and the lowest set bit of a word, the word
`x &&& (x - 1)`, which is `x` with its lowest set bit cleared, the bits of a word set one at a time,
the 64 bits of two words from a position within the first, and the bits of a word and-ed in turn
with the words of a list.

## Main statements

* `Vector.getElem!_fold_set!`: the entries of a vector after a fold of `Vector.set!` over the
  positions `base, …, base + k - 1`.
* `UInt64.getLsbD_allOnes_shiftLeft`, `UInt64.getLsbD_allOnes_shiftRight`: the bits of the masks.
* `UInt64.getLsbD_and_sub_one`, `UInt64.toNat_and_sub_one_lt`: for `x ≠ 0`, `x &&& (x - 1)` is `x`
  with its lowest set bit cleared, and smaller than `x`.
* `UInt64.getLsbD_fold_or_one_shiftLeft`: the bits of a word set one at a time.
* `UInt64.getLsbD_shiftRight_or_shiftLeft`: the 64 bits from position `r` on of the 128 bits of two
  words, for `0 < r < 64`.
* `Std.Legacy.Range.length_eq_of_toList_eq_append_cons`,
  `Std.Legacy.Range.lt_of_toList_eq_append_cons`: the position of the cursor of a loop over
  `[0:m]`.
* `Int.toNat_add_emod_of_lt`, `Int.toNat_add_add_emod`: the residues modulo `p` of `w0 + j` before
  and from the first multiple of `p` from `w0` on.
* `UInt64.getLsbD_foldl_and`: the bits of a word and-ed in turn with the words of a list.

## Implementation notes

The file uses Lean core only, so that the `grind` calls of the proofs see only the lemmas of core.
-/

@[expose] public section

universe u

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

end Array

/-! ### Ranges -/

namespace Std.Legacy.Range

theorem length_eq_of_toList_eq_append_cons {m cur : Nat} {pref suff : List Nat}
    (h : ForIn.toList [0:m] = pref ++ cur :: suff) : pref.length = cur := by
  simp only [Std.Internal.ForIn.toList_range, List.range'_eq_append_iff] at h
  obtain ⟨k, -, rfl, h⟩ := h
  simpa using (List.range'_eq_cons_iff.mp h.symm).1

theorem lt_of_toList_eq_append_cons {m cur : Nat} {pref suff : List Nat}
    (h : ForIn.toList [0:m] = pref ++ cur :: suff) : cur < m := by
  have : cur ∈ ForIn.toList [0:m] := by simp [h]
  simpa using this

end Std.Legacy.Range

/-! ### Integers -/

namespace Int

/-- Before the first multiple of `p` from `w0` on: for `r = (-w0) mod p` and `j < r`, the residue of
`w0 + j` modulo `p` is `p - r + j`. -/
theorem toNat_add_emod_of_lt {w0 : Int} {p j : Nat} (hp : 0 < p)
    (hj : j < ((-w0) % (p : Int)).toNat) :
    ((w0 + j) % (p : Int)).toNat = p - ((-w0) % (p : Int)).toNat + j := by
  have := emod_nonneg (-w0) (b := p) (by lia)
  have := emod_lt_of_pos (-w0) (b := p) (by lia)
  have := mul_ediv_add_emod (-w0) p
  have key : w0 + j = (p - (-w0) % p + j) + p * (-((-w0) / p) - 1) := by
    rw [Int.mul_sub, Int.mul_neg, Int.mul_one]
    lia
  rw [key, add_mul_emod_self_left, emod_eq_of_lt (by lia) (by lia)]
  lia

/-- From the first multiple of `p` from `w0` on: for `r = (-w0) mod p` and `i < p`, the residue of
`w0 + r + k p + i` modulo `p` is `i`. -/
theorem toNat_add_add_emod {w0 : Int} {p i : Nat} (k : Nat) (hi : i < p) :
    ((w0 + ((((-w0) % (p : Int)).toNat + k * p + i : Nat) : Int)) % (p : Int)).toNat = i := by
  have := mul_ediv_add_emod (-w0) p
  have hR : (((-w0) % (p : Int)).toNat : Int) = (-w0) % p :=
    toNat_of_nonneg (emod_nonneg _ (by lia))
  have key : w0 + ((((-w0) % (p : Int)).toNat + k * p + i : Nat) : Int) =
      i + p * (k - (-w0) / p) := by
    push_cast
    rw [hR, Int.mul_sub, Int.mul_comm (p : Int) k]
    lia
  rw [key, add_mul_emod_self_left, emod_eq_of_lt (by lia) (by lia)]
  simp

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

/-- For `0 < r < 64`, the word made of the bits of `x` from `r` on and the lowest `r` bits of `y`
above them: the 64 bits from position `r` on of the 128 bits of `x` followed by `y`. -/
theorem getLsbD_shiftRight_or_shiftLeft {r : Nat} (hr0 : r ≠ 0) (hr : r < 64) (x y : UInt64)
    (t : Nat) :
    ((x >>> r.toUInt64) ||| (y <<< (64 - r).toUInt64)).toBitVec.getLsbD t =
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

end UInt64

end
