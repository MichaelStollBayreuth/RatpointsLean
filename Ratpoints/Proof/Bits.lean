/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# Lemmas on words

Lemmas on vectors and on 64-bit words that the contracts of the bit arrays of words need and Lean
core lacks, under their names in the namespaces of Lean core: the entries of a vector after
`Vector.set!` and after a fold of `Vector.set!` over consecutive positions, the bits of the masks
`~~~0 <<< n` and `~~~0 >>> n`, the lowest bit and the lowest set bit of a word, and the word
`x &&& (x - 1)`, which is `x` with its lowest set bit cleared.

## Main statements

* `Vector.getElem!_fold_set!`: the entries of a vector after a fold of `Vector.set!` over the
  positions `base, …, base + k - 1`.
* `UInt64.getLsbD_allOnes_shiftLeft`, `UInt64.getLsbD_allOnes_shiftRight`: the bits of the masks.
* `UInt64.getLsbD_and_sub_one`, `UInt64.toNat_and_sub_one_lt`: for `x ≠ 0`, `x &&& (x - 1)` is `x`
  with its lowest set bit cleared, and smaller than `x`.

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

/-! ### Words -/

namespace UInt64

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

end UInt64

end
