/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Sieve
public import Std.WP

import Ratpoints.Proof.Bits
import Std.Tactic.Do

/-!
# The contracts of the bit arrays of words

The lemmas on the operations on the bit arrays of 64-bit words of the model, and the contracts of
its components on words, as `@[spec]` theorems proved with `vcgen`, the program logic of Lean core,
with loop invariants that are named definitions.

## Main statements

* `Ratpoints.Sieve.getElem!_andBitArray`: `Ratpoints.Sieve.andBitArray` ands the words of one bit
  array with the words of a bit array of the row, and leaves the other words as they are.
* `Ratpoints.Sieve.getLsbD_clearLowBits`, `Ratpoints.Sieve.getLsbD_clearHighBits`: which bits the
  masks at the two ends of the numerator range keep.
* `Ratpoints.Sieve.isZeroAt_eq_true_iff`: a bit array is zero when all its words are.
* `Ratpoints.Sieve.ctz_spec`: for a word other than `0`, the loop of `Ratpoints.Sieve.ctz` ends with
  the number of its trailing zeros.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Sieve` does; the lemmas on words that
are not about the model are in `Ratpoints.Proof.Bits`. The proofs use only that
`Ratpoints.rbaPack` is positive, never its value.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

/-! ### The width of the bit arrays -/

theorem rbaLength_eq : rbaLength = 64 * rbaPack := rfl

theorem rbaLength_mul (j : Nat) : rbaLength * j = 64 * (rbaPack * j) := by
  rw [rbaLength_eq, Nat.mul_assoc]

namespace Sieve

/-! ### Operations on bit arrays -/

theorem getElem!_andBitArray {m : Nat} (v : Vector UInt64 m) (j : Nat) (row : Array UInt64)
    (x : Nat) {y : Nat} (hy : y < m) :
    (andBitArray v j row x)[y]! =
      if y / rbaPack = j then v[y]! &&& row[rbaPack * x + y % rbaPack]! else v[y]! := by
  have hiff : rbaPack * j ≤ y ∧ y < rbaPack * j + rbaPack ↔ y / rbaPack = j := by
    have := rbaPack_pos
    rw [Nat.div_eq_iff rbaPack_pos, Nat.mul_comm j]
    lia
  rw [andBitArray, Vector.getElem!_fold_set! (fun κ w ↦ w &&& row[rbaPack * x + κ]!) hy]
  by_cases h : y / rbaPack = j <;> simp only [hiff, h, ↓reduceIte, Nat.mod_def]

theorem getLsbD_clearLowBits {m : Nat} (v : Vector UInt64 m) (s : Nat) {y : Nat} (hy : y < m)
    (t : Nat) :
    ((clearLowBits v s)[y]!).toBitVec.getLsbD t =
      ((v[y]!).toBitVec.getLsbD t && decide (s ≤ 64 * y + t)) := by
  have h := Vector.getElem!_fold_set! (xs := v) (base := 0) (k := s / 64) (fun _ _ ↦ 0) hy
  simp only [Nat.zero_add, Nat.zero_le, true_and] at h
  simp only [clearLowBits, Vector.getElem!_set! hy, h]
  grind [UInt64.toBitVec_zero, UInt64.toBitVec_and, UInt64.getLsbD_allOnes_shiftLeft,
    UInt64.toNat_ofNat', Nat.toUInt64_eq]

theorem getLsbD_clearHighBits {m : Nat} (v : Vector UInt64 m) (j : Nat) {s : Nat}
    (hs : s < rbaLength) {y : Nat} (hy : y < m) (hyj : y < rbaPack * (j + 1)) (t : Nat) :
    ((clearHighBits v j s)[y]!).toBitVec.getLsbD t =
      ((v[y]!).toBitVec.getLsbD t && decide (64 * y + t + s < rbaLength * (j + 1))) := by
  simp only [clearHighBits, Vector.getElem!_fold_set! (fun _ _ ↦ (0 : UInt64)) hy,
    Vector.getElem!_set! hy]
  grind [UInt64.toBitVec_zero, UInt64.toBitVec_and, UInt64.getLsbD_allOnes_shiftRight,
    UInt64.toNat_ofNat', Nat.toUInt64_eq, rbaLength_mul, rbaLength_eq, Nat.mul_succ]

theorem isZeroAt_eq_true_iff {m : Nat} (v : Vector UInt64 m) (pos : Nat) :
    isZeroAt v pos = true ↔ ∀ κ < rbaPack, v[rbaPack * pos + κ]! = 0 := by
  simp [isZeroAt, Nat.all_eq_finRange_all, Fin.forall_iff]

/-! ### The lowest set bit -/

/-- The invariant of the loop of `Ratpoints.Sieve.ctz` on a word `w ≠ 0`: the word is `w`
shifted right by the count, the count is at most the position of the lowest set bit of `w`, and
it is that position at the exit. -/
def CtzInvariant (w : UInt64) : Std.WP.WhileInvariant (UInt64 × Nat) Prop :=
  .mk fun exit s ↦ s.1.toBitVec = w.toBitVec >>> s.2 ∧ s.2 ≤ w.toBitVec.ctz.toNat ∧
    (exit = true → s.2 = w.toBitVec.ctz.toNat)

/-- The loop ends, since the count stays at most the position of the lowest set bit, which is
below 64. -/
@[spec]
theorem ctz_spec (w : UInt64) : ⦃ w ≠ 0 ⦄ ctz w ⦃ fun t ↦ t = w.toBitVec.ctz.toNat ⦄ := by
  vcgen [ctz] invariants
  · CtzInvariant w
  · Std.WP.Variant.ofMeasure fun s : UInt64 × Nat ↦ 64 - s.2
  all_goals simp [CtzInvariant] at *
  all_goals grind [UInt64.ne_ctz_of_and_one_eq_zero, UInt64.eq_ctz_of_and_one_ne_zero,
    UInt64.toNat_ctz_lt, BitVec.shiftRight_add]

end Sieve

end Ratpoints

end
