/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Reductions
public import Ratpoints.Proof.Rows
public import Ratpoints.Proof.SetBits

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers
import Std.Tactic.Do

/-!
# The contracts of the bit arrays of words

The lemmas on the operations on the bit arrays of 64-bit words of the model, on its rows as words,
on the rows under a unit, on the check of a numerator and on the array of a walk through the set
bits of a word, and the contract of the first stage over a piece, as `@[spec]` theorems proved with
`vcgen`, the program logic of Lean core, with loop invariants that are named definitions.

## Main definitions

* `Ratpoints.Sieve.Factor.HasInverses`: what the scaling of the rows by a unit needs of a factor of
  a modulus: its modulus divides the modulus, and its table of inverses inverts its units.
* `Ratpoints.Sieve.SieveSpec.wordAt`, `Ratpoints.Sieve.andWords`: the row word that the first stage
  ands into a word of a piece, at the offset of the row, and the words of a piece after it.
* `Ratpoints.Sieve.SieveSpec.Reads`: the rows of a modulus read a test of the bits.
* `Ratpoints.Sieve.AndRowsFillInvariant`, `Ratpoints.Sieve.AndRowsLoopInvariant`,
  `Ratpoints.Sieve.AndRowsStartInvariant`: the invariants of the loop of the first stage one row at
  a time that sets the bit arrays to the class word, from the last, of its loop over the moduli with
  their reciprocals, and of its loops over the bit arrays of a modulus.
* `Ratpoints.Sieve.WalkWordInvariant`: the invariant of the array that a walk through the set bits
  of a word, lowest first, appends to.

## Main statements

* `Ratpoints.Sieve.getElem!_andBitArray`, `Ratpoints.Sieve.getElem!_loadBitArray`,
  `Ratpoints.Sieve.getElem!_storeBitArray`, `Ratpoints.Sieve.getElem!_fillBitArray`: the operations
  on bit arrays of the first stage set the words of one bit array and leave the other words as they
  are.
* `Ratpoints.Sieve.getLsbD_clearLowBits`, `Ratpoints.Sieve.getLsbD_clearHighBits`: which bits the
  masks at the two ends of the numerator range keep.
* `Ratpoints.Sieve.isZeroAt_eq_true_iff`: a bit array is zero when all its words are.
* `Ratpoints.Sieve.Entry.admits_mod_of_dvd`, `Ratpoints.Sieve.Power.admits_mod_of_dvd`: the row of
  a prime or a prime power reads the residues modulo a multiple of its modulus as those of the
  numbers.
* `Ratpoints.Sieve.SieveEntry.admits_mul`: the row of a sieve entry whose factors have their tables
  of inverses is unchanged when the denominator and the numerator are scaled by a unit.
* `Ratpoints.Sieve.SieveEntry.reads_row`: the closed form of the row of `b / 2 ^ k`
  (`Ratpoints.Sieve.closedRow`) at the offset of the class `a₀ mod 2 ^ k` reads at bit `j` whether
  the row of `b` admits the numerator `a₀ + 2 ^ k j`.
* `Ratpoints.Sieve.getLsbD_andWords`: the words of rows that read tests of the bits, and-ed into a
  word, have the bits of the word that pass all the tests.
* `Ratpoints.Sieve.andWords_append`: and-ing the rows of two lists of moduli one after the other is
  and-ing those of their concatenation.
* `Ratpoints.Sieve.andRows_spec`: after the first stage over a piece from the class word `cw`, with
  moduli in the range of the packing and their reciprocals (`Ratpoints.Sieve.SieveSpec.Fits`) and
  the test `small` of the piece (`Ratpoints.Sieve.SmallFits`), each word of the piece is `cw` and-ed
  with its row words (`Ratpoints.Sieve.andWords`).
* `Ratpoints.Sieve.pointsOfDen_eq_flatMap_checkNum`: the points that the brute-force reference finds
  over a denominator are those of `Ratpoints.Sieve.checkNum` for its numerators, one after the
  other, with the flag of the reversal clear.
* `Ratpoints.Sieve.checkNum_eq_map`, `Ratpoints.Sieve.flatMap_checkNum`: with the flag of the
  reversal set, the check of a numerator gives the points of the check with the flag clear, mapped
  by `Ratpoints.Sieve.swapPoint`, and so do the checks of a list of numerators, one after the
  other.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Sieve` does; the lemmas on words that
are not about the model are in `Ratpoints.Proof.Bits`, the closed form of the rows in
`Ratpoints.Proof.Rows`. The proofs use only that `Ratpoints.rbaPack` and `Ratpoints.chunk` are
positive, never their values. The contract of the chunked first stage is in
`Ratpoints.Proof.FirstStage`, those of the builders of the rows in `Ratpoints.Proof.PrimeRows`,
`Ratpoints.Proof.CompositeRows` and `Ratpoints.Proof.RowStore`. The scaling by a unit needs an
inverse of the unit and the tables of inverses, no primality. The contracts of the second and the
third stage and of the check are in `Ratpoints.Proof.Stages`, those of the walk, of the scan, of one
piece and of one denominator in `Ratpoints.Proof.Sift`. The bit of a number in a word
(`Ratpoints.Sieve.classBit`), the contract of the lowest set bit of a word and the invariant of a
`while` loop over the set bits of a word are in `Ratpoints.Proof.SetBits`, the reductions by a
reciprocal and of the row indices and the positivity of the width `Ratpoints.rbaLength` of the bit
arrays in `Ratpoints.Proof.Reductions`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

/-! ### The width of the bit arrays -/

theorem rbaLength_mul (j : Nat) : rbaLength * j = 64 * (rbaPack * j) := by
  rw [rbaLength_eq, Nat.mul_assoc]

theorem lt_rbaLength_mul_of_lt {n y t : Nat} (hy : y < n * rbaPack) (ht : t < 64) :
    64 * y + t < rbaLength * n := by
  rw [rbaLength_eq, Nat.mul_assoc, Nat.mul_comm rbaPack n]
  lia

namespace Sieve

universe u

/-! ### Operations on bit arrays -/

/-- Word `y` lies in bit array `j` exactly when `y / rbaPack = j`. -/
theorem rbaPack_mul_le_and_lt_iff {y j : Nat} :
    rbaPack * j ≤ y ∧ y < rbaPack * j + rbaPack ↔ y / rbaPack = j := by
  rw [Nat.div_eq_iff rbaPack_pos, Nat.mul_comm j]
  lia [rbaPack_pos]

theorem getElem!_andBitArray {m : Nat} (v : Vector UInt64 m) (j : Nat) (row : Array UInt64)
    (x : Nat) {y : Nat} (hy : y < m) :
    (andBitArray v j row x)[y]! =
      if y / rbaPack = j then v[y]! &&& row[rbaPack * x + y % rbaPack]! else v[y]! := by
  rw [andBitArray, Vector.getElem!_fold_set! (fun κ w ↦ w &&& row[rbaPack * x + κ]!) hy]
  by_cases h : y / rbaPack = j <;> simp only [rbaPack_mul_le_and_lt_iff, h, ↓reduceIte, Nat.mod_def]

theorem getElem!_loadBitArray {m : Nat} (v : Vector UInt64 m) (j : Nat) (cw : UInt64)
    (row : Array UInt64) (x : Nat) {y : Nat} (hy : y < m) :
    (loadBitArray v j cw row x)[y]! =
      if y / rbaPack = j then cw &&& row[rbaPack * x + y % rbaPack]! else v[y]! := by
  rw [loadBitArray, Vector.getElem!_fold_set! (fun κ _ ↦ cw &&& row[rbaPack * x + κ]!) hy]
  by_cases h : y / rbaPack = j <;> simp only [rbaPack_mul_le_and_lt_iff, h, ↓reduceIte, Nat.mod_def]

theorem getElem!_storeBitArray {m k : Nat} (v : Vector UInt64 m) (y' : Nat)
    (regs : Vector UInt64 k) (j : Nat) {y : Nat} (hy : y < m) :
    (storeBitArray v y' regs j)[y]! =
      if y / rbaPack = y' then regs[rbaPack * j + y % rbaPack]! else v[y]! := by
  rw [storeBitArray, Vector.getElem!_fold_set! (fun κ _ ↦ regs[rbaPack * j + κ]!) hy]
  by_cases h : y / rbaPack = y' <;>
    simp only [rbaPack_mul_le_and_lt_iff, h, ↓reduceIte, Nat.mod_def]

theorem getElem!_fillBitArray {m : Nat} (v : Vector UInt64 m) (y' : Nat) (cw : UInt64) {y : Nat}
    (hy : y < m) : (fillBitArray v y' cw)[y]! = if y / rbaPack = y' then cw else v[y]! := by
  rw [fillBitArray, Vector.getElem!_fold_set! (fun _ _ ↦ cw) hy]
  by_cases h : y / rbaPack = y' <;> simp only [rbaPack_mul_le_and_lt_iff, h, ↓reduceIte]

theorem getLsbD_clearLowBits {m : Nat} (v : Vector UInt64 m) (s : Nat) {y : Nat} (hy : y < m)
    (t : Nat) :
    (clearLowBits v s)[y]!.toBitVec.getLsbD t =
      (v[y]!.toBitVec.getLsbD t && decide (s ≤ 64 * y + t)) := by
  have h := Vector.getElem!_fold_set! (xs := v) (base := 0) (k := s / 64) (fun _ _ ↦ 0) hy
  simp only [Nat.zero_add, Nat.zero_le, true_and] at h
  simp only [clearLowBits, Vector.getElem!_set! hy, h]
  grind [UInt64.toBitVec_zero, UInt64.toBitVec_and, UInt64.getLsbD_allOnes_shiftLeft,
    UInt64.toNat_ofNat', Nat.toUInt64_eq]

theorem getLsbD_clearHighBits {m : Nat} (v : Vector UInt64 m) (j : Nat) {s : Nat}
    (hs : s < rbaLength) {y : Nat} (hy : y < m) (hyj : y < rbaPack * (j + 1)) (t : Nat) :
    (clearHighBits v j s)[y]!.toBitVec.getLsbD t =
      (v[y]!.toBitVec.getLsbD t && decide (64 * y + t + s < rbaLength * (j + 1))) := by
  simp only [clearHighBits, Vector.getElem!_fold_set! (fun _ _ ↦ (0 : UInt64)) hy,
    Vector.getElem!_set! hy]
  grind [UInt64.toBitVec_zero, UInt64.toBitVec_and, UInt64.getLsbD_allOnes_shiftRight,
    UInt64.toNat_ofNat', Nat.toUInt64_eq, rbaLength_mul, rbaLength_eq, Nat.mul_succ]

theorem isZeroAt_eq_true_iff {m : Nat} (v : Vector UInt64 m) (pos : Nat) :
    isZeroAt v pos = true ↔ ∀ κ < rbaPack, v[rbaPack * pos + κ]! = 0 := by
  simp [isZeroAt, Nat.all_eq_finRange_all, Fin.forall_iff]

/-! ### The rows as words -/

theorem SieveEntry.admits_congr (e : SieveEntry) (b : Nat) {a a' : Int} (h : a % e.p = a' % e.p) :
    e.admits b a = e.admits b a' := by
  simp [SieveEntry.admits, h]

theorem SieveEntry.admits_add_mul (e : SieveEntry) (b : Nat) (a k : Int) :
    e.admits b (a + e.p * k) = e.admits b a :=
  e.admits_congr b (Int.add_mul_emod_self_left a e.p k)

theorem SieveEntry.admits_mod (e : SieveEntry) (b : Nat) : e.admits (b % e.p) = e.admits b :=
  funext fun _ ↦ by simp [SieveEntry.admits]

theorem getLsbD_window (E : Array UInt64) (s t : Nat) :
    (window E s).toBitVec.getLsbD t =
      (decide (t < 64) && E[(s + t) / 64]!.toBitVec.getLsbD ((s + t) % 64)) := by
  rw [window]
  split
  · grind
  · rw [UInt64.getLsbD_shiftRight_or_shiftLeft ‹s % 64 ≠ 0› (Nat.mod_lt s (by decide))]
    grind

/-! ### The rows under a unit -/

theorem Entry.admits_mod_of_dvd (e : Entry) {m : Nat} (h : e.p ∣ m) (b : Nat) (a : Int) :
    e.admits (b % m) (a % m) = e.admits b a := by
  simp only [Entry.admits, Nat.mod_mod_of_dvd b h,
    Int.emod_emod_of_dvd a (Int.natCast_dvd_natCast.mpr h)]

theorem Power.admits_mod_of_dvd (pw : Power) {m : Nat} (h : pw.m ∣ m) (b : Nat) (a : Int) :
    pw.admits (b % m) (a % m) = pw.admits b a := by
  simp only [Power.admits, Nat.mod_mod_of_dvd b h,
    Int.emod_emod_of_dvd a (Int.natCast_dvd_natCast.mpr h)]

/-- What the scaling of the rows by a unit needs of a factor of the modulus `P` of a sieve entry:
the modulus of the factor divides `P`, and its table of inverses inverts the residues at which its
row reads it, the nonzero residues of a prime and the units of a prime power `p ^ e`, whose prime
divides it (`Ratpoints.Sieve.SieveEntry.admits_mul`). -/
def Factor.HasInverses : Factor → Nat → Prop
  | .prime t, P => t.p ∣ P ∧ ∀ r < t.p, r ≠ 0 → t.inverses[r]! * r % t.p = 1
  | .power pw, P => pw.p ∣ pw.m ∧ pw.m ∣ P ∧
      ∀ x < pw.m, x % pw.p ≠ 0 → pw.inv[x]! * x % pw.m = 1

theorem Factor.HasInverses.modulus_dvd {f : Factor} {P : Nat} (hf : f.HasInverses P) :
    f.modulus ∣ P := by
  cases f with
  | prime t => exact hf.1
  | power pw => exact hf.2.1

/-- The row of a prime `q > 0` whose table inverts the nonzero residues is unchanged when the
denominator and the numerator are scaled by a unit `u` modulo `q`. -/
theorem Entry.admits_mul {t : Entry} (hq : 0 < t.p)
    (hinv : ∀ r < t.p, r ≠ 0 → t.inverses[r]! * r % t.p = 1) {u v : Nat}
    (huv : v * u % t.p = 1 % t.p) (b : Nat) (a : Int) :
    t.admits (u * b) (u * a) = t.admits b a := by
  have hzb := Nat.mul_mod_eq_zero_iff_of_mul_mod huv b
  have hx := Int.toNat_emod_lt a hq
  have hzx := Nat.mul_mod_eq_zero_iff_of_mul_mod huv (a % (t.p : Int)).toNat
  rw [Nat.mod_eq_of_lt hx] at hzx
  simp only [Entry.admits, Int.toNat_mul_emod u a hq]
  by_cases hb : b % t.p = 0
  · simp only [hb, hzb.mpr hb, ↓reduceIte]
    rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, hzx]
  · simp only [hb, mt hzb.mp hb, ↓reduceIte]
    rw [Nat.mul_mod_eq_mul_mod_of_mul_mod_eq_one (by rw [Nat.mod_mod]) (by rw [Nat.mod_mod,
      Nat.mul_mod_mod]) (hinv _ (Nat.mod_lt b hq) hb) (hinv _ (Nat.mod_lt _ hq) (mt hzb.mp hb))]

/-- The row of a prime power `p ^ e` with `p ∣ p ^ e`, whose table inverts its units, is unchanged
when the denominator and the numerator are scaled by a unit `u` modulo `p ^ e`. -/
theorem Power.admits_mul {pw : Power} (hm : 0 < pw.m) (hpm : pw.p ∣ pw.m)
    (hinv : ∀ x < pw.m, x % pw.p ≠ 0 → pw.inv[x]! * x % pw.m = 1) {u v : Nat}
    (huv : v * u % pw.m = 1 % pw.m) (b : Nat) (a : Int) :
    pw.admits (u * b) (u * a) = pw.admits b a := by
  have hzb := Nat.mul_mod_mod_eq_zero_iff_of_mul_mod hpm huv b
  have hx := Int.toNat_emod_lt a hm
  have hzx := Nat.mul_mod_mod_eq_zero_iff_of_mul_mod hpm huv (a % (pw.m : Int)).toNat
  rw [Nat.mod_eq_of_lt hx] at hzx
  have hm1 : u * b % pw.m % pw.m = u * (b % pw.m) % pw.m := by rw [Nat.mod_mod, Nat.mul_mod_mod]
  simp only [Power.admits, Int.toNat_mul_emod u a hm]
  by_cases hb : b % pw.m % pw.p = 0
  · simp only [hb, hzb.mpr hb, ne_eq, not_true_eq_false, ↓reduceIte]
    by_cases ha : (a % (pw.m : Int)).toNat % pw.p = 0
    · simp [ha, hzx.mpr ha]
    · rw [Nat.mul_mod_eq_mul_mod_of_mul_mod_eq_one hm1 (Nat.mod_mod _ _) (hinv _ hx ha)
        (hinv _ (Nat.mod_lt _ hm) (mt hzx.mp ha))]
      simp only [bne_iff_ne.mpr ha, bne_iff_ne.mpr (mt hzx.mp ha), Bool.true_and]
  · simp only [hb, mt hzb.mp hb, ne_eq, not_false_eq_true, ↓reduceIte]
    rw [Nat.mul_mod_eq_mul_mod_of_mul_mod_eq_one (Nat.mod_mod _ _) hm1
      (hinv _ (Nat.mod_lt b hm) hb) (hinv _ (Nat.mod_lt _ hm) (mt hzb.mp hb))]

theorem Factor.HasInverses.admits_mod {f : Factor} {P : Nat} (hf : f.HasInverses P) (b : Nat)
    (a : Int) : f.admits (b % P) (a % P) = f.admits b a := by
  cases f with
  | prime t => exact Entry.admits_mod_of_dvd t hf.1 b a
  | power pw => exact Power.admits_mod_of_dvd pw hf.2.1 b a

/-- The row of a factor of a modulus `P > 0` with its tables of inverses is unchanged when the
denominator and the numerator are scaled by a unit `u` modulo `P`. -/
theorem Factor.HasInverses.admits_mul {f : Factor} {P : Nat} (hf : f.HasInverses P) (hP : 0 < P)
    {u v : Nat} (huv : v * u % P = 1) (b : Nat) (a : Int) :
    f.admits (u * b) (u * a) = f.admits b a := by
  cases f with
  | prime t =>
    exact Entry.admits_mul (Nat.pos_of_dvd_of_pos hf.1 hP) hf.2
      (by rw [← Nat.mod_mod_of_dvd _ hf.1, huv]) b a
  | power pw =>
    exact Power.admits_mul (Nat.pos_of_dvd_of_pos hf.2.1 hP) hf.1 hf.2.2
      (by rw [← Nat.mod_mod_of_dvd _ hf.2.1, huv]) b a

/-- The row of a sieve entry whose factors have their tables of inverses is unchanged when the
denominator and the numerator are scaled by a unit `u` modulo the modulus, with an inverse `v`. -/
theorem SieveEntry.admits_mul {e : SieveEntry} (he : ∀ f ∈ e.factors, f.HasInverses e.p)
    {u v : Nat} (huv : v * u % e.p = 1) (b : Nat) (a : Int) :
    e.admits (u * b) (u * a) = e.admits b a := by
  rcases Nat.eq_zero_or_pos e.p with h0 | hP
  · rw [h0, Nat.mod_zero] at huv
    rw [Nat.eq_one_of_mul_eq_one_left huv, Nat.one_mul, Int.natCast_one, Int.one_mul]
  · rw [SieveEntry.admits, SieveEntry.admits, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
    refine forall₂_congr fun f hf ↦ ?_
    rw [(he f hf).admits_mod, (he f hf).admits_mul hP huv, (he f hf).admits_mod]

/-! ### One piece -/

/-- The word of the row of `s` that the first stage ands into word `y` of the piece from the word
number `w0` on: word `y % rbaPack` of bit array `(w0 + offset + y / rbaPack) mod p` of the row, for
the number `rbaPack` of words of a bit array (`Ratpoints.rbaPack`). -/
def SieveSpec.wordAt (s : SieveSpec) (w0 : Int) (y : Nat) : UInt64 :=
  s.row[rbaPack * ((w0 + s.offset + (y / rbaPack : Nat)) % (s.p : Int)).toNat + y % rbaPack]!

/-- Word `κ < Ratpoints.rbaPack` of the row of `s` for the word number `i` is word `κ` of bit array
`(i + offset) mod p`. -/
theorem SieveSpec.wordAt_of_lt (s : SieveSpec) (i : Int) {κ : Nat} (hκ : κ < rbaPack) :
    s.wordAt i κ = s.row[rbaPack * ((i + s.offset) % (s.p : Int)).toNat + κ]! := by
  simp [SieveSpec.wordAt, Nat.div_eq_of_lt hκ, Nat.mod_eq_of_lt hκ]

/-- The row word of word `κ` of bit array `pos` of a piece from the word number `w0` on is the row
word of word `κ` of the bit array with the word number `w0 + pos`. -/
theorem SieveSpec.wordAt_rbaPack_mul_add (s : SieveSpec) (w0 : Int) (pos : Nat) {κ : Nat}
    (hκ : κ < rbaPack) : s.wordAt w0 (rbaPack * pos + κ) = s.wordAt (w0 + pos) κ := by
  simp only [SieveSpec.wordAt, Nat.mul_add_div rbaPack_pos, Nat.div_eq_of_lt hκ, Nat.mul_add_mod,
    Nat.add_zero, Int.natCast_zero, Int.add_zero, Int.add_right_comm w0]

-- The position in the row of bit `t` of the row word of word `y` is congruent modulo `p` to the
-- numerator of bit `t` of word `y`.
private theorem emod_wordIndex (p : Nat) (hp : 0 < p) (w0 : Int) (y t : Nat) :
    (64 * ((rbaPack * ((w0 + (y / rbaPack : Nat)) % (p : Int)).toNat + y % rbaPack : Nat) : Int) +
        t) % p = (rbaLength * w0 + 64 * y + t) % p := by
  have hy := Nat.div_add_mod y rbaPack
  generalize y / rbaPack = q at hy ⊢
  generalize y % rbaPack = k at hy ⊢
  subst hy
  have hu : (((w0 + q) % (p : Int)).toNat : Int) = (w0 + q) - p * ((w0 + q) / p) := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg _ (by lia)), Int.emod_def]
  have key : (64 * ((rbaPack * ((w0 + q) % (p : Int)).toNat + k : Nat) : Int) + t) =
      (rbaLength * w0 + 64 * (rbaPack * q + k : Nat) + t) +
        p * (-(64 * rbaPack * ((w0 + q) / p))) := by
    push_cast
    rw [hu, rbaLength_eq]
    push_cast
    grind
  rw [key, Int.add_mul_emod_self_left]

/-- Bit `t` of the row word of word `y` of a piece from the word number `w0` on, in the closed form
of the row of the denominator `b` with the offset `off` and any start and end, is the bit of the
numerator `rbaLength (w0 + off) + 64 y + t` in the row of `b`. -/
theorem SieveSpec.getLsbD_wordAt_mk (e : SieveEntry) (b : Nat) (hp : 0 < e.p) (off st stop : Nat)
    (w0 : Int) (y t : Nat) :
    (wordAt ⟨e.p, off, closedRow e.admits e.p b, st, stop⟩ w0 y).toBitVec.getLsbD t =
      (decide (t < 64) && e.admits b (rbaLength * (w0 + off) + 64 * y + t)) := by
  have hu : ((w0 + off + (y / rbaPack : Nat)) % (e.p : Int)).toNat < e.p + chunk - 1 := by
    lia [Int.toNat_emod_lt (w0 + off + (y / rbaPack : Nat)) hp, chunk_pos]
  rw [wordAt,
    getLsbD_closedRow _ _ _ (Nat.mul_add_lt_mul_of_lt_of_lt' hu (Nat.mod_lt y rbaPack_pos)),
    e.admits_congr b (emod_wordIndex e.p hp _ y t)]

/-- The rows of the sieve spec `s` read the test `f` of the bits: bit `t` of the row word of word
`y` of a piece from the word number `i` on is `f` at the bit `rbaLength i + 64 y + t`. -/
def SieveSpec.Reads (s : SieveSpec) (f : Int → Bool) : Prop :=
  ∀ (i : Int) (y t : Nat), (s.wordAt i y).toBitVec.getLsbD t =
    (decide (t < 64) && f (rbaLength * i + 64 * y + t))

/-- The closed form of the row of the residue `bp` of the denominator `b` divided by the stride
`2 ^ k` (`2 ^ k bp ≡ b`), with any start and end, read at the offset `off` of the class
`a₀ mod 2 ^ k` (`off 2 ^ k Ratpoints.rbaLength ≡ a₀`), reads at bit `j` whether the row of `b`
admits the numerator `a₀ + 2 ^ k j`, when `2 ^ k` has an inverse `v` modulo `p` and the factors of
the entry have their tables of inverses: the rows are unchanged when the denominator and the
numerator are scaled by the unit `2 ^ k` (`Ratpoints.Sieve.SieveEntry.admits_mul`). -/
theorem SieveEntry.reads_row {e : SieveEntry} (he : ∀ f ∈ e.factors, f.HasInverses e.p)
    (hp : 0 < e.p) {k a0 off bp b v st stop : Nat} (hv : v * 2 ^ k % e.p = 1)
    (hoff : off * (2 ^ k * rbaLength) % e.p = a0 % e.p) (hbp : 2 ^ k * bp % e.p = b % e.p) :
    SieveSpec.Reads ⟨e.p, off, closedRow e.admits e.p bp, st, stop⟩ fun j ↦
      e.admits b (a0 + 2 ^ k * j) := by
  intro i y t
  rw [SieveSpec.getLsbD_wordAt_mk e bp hp, ← e.admits_mul he hv, ← e.admits_mod, hbp,
    e.admits_mod]
  refine congrArg (decide (t < 64) && ·) (e.admits_congr b ?_)
  have h' : ((off * (2 ^ k * rbaLength) : Nat) : Int) % e.p = (a0 : Int) % e.p := by
    rw [← Int.natCast_emod, ← Int.natCast_emod, hoff]
  have key : ((2 ^ k : Nat) : Int) * (rbaLength * (i + off) + 64 * y + t) =
      ((off * (2 ^ k * rbaLength) : Nat) : Int) + 2 ^ k * (rbaLength * i + 64 * y + t) := by
    push_cast
    grind
  rw [key, Int.add_emod_eq_add_emod_right _ h']

theorem classBit_rbaLength_mul_add (cw : UInt64) (w0 : Int) (y : Nat) {t : Nat} (ht : t < 64) :
    classBit cw (rbaLength * w0 + 64 * y + t) = cw.toBitVec.getLsbD t := by
  have h : (rbaLength : Int) * w0 + 64 * y + t = t + 64 * (rbaPack * w0 + y) := by
    rw [rbaLength_eq, Int.natCast_mul, Int.mul_assoc]
    lia
  rw [classBit_eq, h, Int.add_mul_emod_self_left, Int.emod_eq_of_lt (by lia) (by lia)]
  rfl

/-- The word `cw` and-ed in turn with the words of the rows `specs` at word `y` of a piece from the
word number `w0` on (`Ratpoints.Sieve.SieveSpec.wordAt`): word `y` of the piece after the first
stage from the class word `cw`, or, with `w0` the word number of a bit array and `y` one of its
words, that word after the second stage from its word `cw` in a copy of the bit array. -/
def andWords (specs : List SieveSpec) (cw : UInt64) (w0 : Int) (y : Nat) : UInt64 :=
  specs.foldl (fun acc s ↦ acc &&& s.wordAt w0 y) cw

theorem andWords_append (l₁ l₂ : List SieveSpec) (cw : UInt64) (w0 : Int) (y : Nat) :
    andWords (l₁ ++ l₂) cw w0 y = andWords l₂ (andWords l₁ cw w0 y) w0 y :=
  List.foldl_append ..

@[simp]
theorem andWords_zero (l : List SieveSpec) (w0 : Int) (y : Nat) : andWords l 0 w0 y = 0 := by
  induction l with
  | nil => rfl
  | cons s l ih => simpa [andWords] using ih

theorem andWords_concat (l : List SieveSpec) (s : SieveSpec) (cw : UInt64) (w0 : Int) (y : Nat) :
    andWords (l ++ [s]) cw w0 y = andWords l cw w0 y &&& s.wordAt w0 y := by
  simp [andWords]

theorem andWords_rbaPack_mul_add (specs : List SieveSpec) (x : UInt64) (w0 : Int) (pos : Nat)
    {κ : Nat} (hκ : κ < rbaPack) :
    andWords specs x w0 (rbaPack * pos + κ) = andWords specs x (w0 + pos) κ := by
  simp only [andWords, SieveSpec.wordAt_rbaPack_mul_add _ _ _ hκ]

/-- The words of rows that read the tests `sf.2` of the bits (`Ratpoints.Sieve.SieveSpec.Reads`),
and-ed into the word `cw`, have bit `t` set when `cw` has it and all the tests pass at the bit
`rbaLength w0 + 64 y + t`. -/
theorem getLsbD_andWords {sfs : List (SieveSpec × (Int → Bool))} (h : ∀ sf ∈ sfs, sf.1.Reads sf.2)
    (cw : UInt64) (w0 : Int) (y t : Nat) :
    (andWords (sfs.map Prod.fst) cw w0 y).toBitVec.getLsbD t =
      (cw.toBitVec.getLsbD t && sfs.all (·.2 (rbaLength * w0 + 64 * y + t))) := by
  rw [andWords, UInt64.getLsbD_foldl_and, List.all_map]
  grind [SieveSpec.Reads, List.all_eq_true]

/-- The reciprocals of the moduli `specs` that a loop over the moduli and their reciprocals in step
has still to read after the moduli `pref`, before it has gone through all of them, are those after
the first `pref.length`: the next is that of the next modulus, and the cursor moves on. -/
theorem eq_magic_and_of_next?_eq_some {specs pref suff : List SieveSpec} {s : SieveSpec}
    {mgs rest rest' : List Nat} {mg : Nat} (hmg : mgs = specs.map (magic ·.p))
    (hs : specs = pref ++ s :: suff)
    (hrest : pref.length < specs.length → rest = mgs.drop pref.length)
    (hnext : Std.Stream.next? rest = some (mg, rest')) :
    mg = magic s.p ∧
      ((pref ++ [s]).length < specs.length → rest' = mgs.drop (pref ++ [s]).length) := by
  rw [hrest (by simp [hs]), hmg] at hnext
  obtain ⟨rfl, h⟩ := List.next?_drop_map _ hs hnext
  exact ⟨rfl, fun _ ↦ by rw [h, hmg, List.length_append, List.length_singleton]⟩

/-- The reciprocals of a loop over the moduli and their reciprocals in step do not run out before
the moduli. -/
theorem next?_ne_none_of_lt {specs pref suff : List SieveSpec} {s : SieveSpec} {mgs rest : List Nat}
    (hmg : mgs = specs.map (magic ·.p)) (hs : specs = pref ++ s :: suff)
    (hrest : pref.length < specs.length → rest = mgs.drop pref.length) :
    Std.Stream.next? rest ≠ none := by
  rw [hrest (by simp [hs]), hmg]
  exact List.next?_drop_map_ne_none _ hs

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over the moduli and, in step with them,
their reciprocals `mgs`, whose state is the piece and the reciprocals still to come: after the
moduli `pref`, the reciprocals still to come are those after the first `pref.length`, and the first
`k` words of the piece, all its `n rbaPack` words in the loop, are the class word `cw` and-ed with
their row words (`Ratpoints.Sieve.andWords`). -/
def AndRowsLoopInvariant {m : Nat} (cw : UInt64) (w0 : Int) (k : Nat) (mgs : List Nat)
    (pref : List SieveSpec) (st : Vector UInt64 m × List Nat) : Prop :=
  st.2 = mgs.drop pref.length ∧ ∀ y < k, st.1[y]! = andWords pref cw w0 y

/-- The invariant of the loops of `Ratpoints.Sieve.andRows` over the bit arrays for the modulus
`s` after the moduli `pref`: the words of the bit arrays below `c` are and-ed with the row of `s`
as well, the others not yet. -/
def AndRowsRowInvariant {m : Nat} (cw : UInt64) (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (s : SieveSpec) (c : Nat) (surv : Vector UInt64 m) : Prop :=
  ∀ y < n * rbaPack, surv[y]! =
    if y / rbaPack < c then andWords pref cw w0 y &&& s.wordAt w0 y else andWords pref cw w0 y

/-- The residue `r` of `-w0 - offset` modulo `p` that `Ratpoints.Sieve.andRows` computes with the
reciprocal `mg` of the cursor, by `Ratpoints.Sieve.modMul` under the test `small` and by
`Ratpoints.Sieve.modLong` otherwise: the first stage ands bit array `p - r + j` of the row of `s`
into bit array `j` of a piece from the word number `w0` on, for `j < r`. -/
abbrev andRowsStart (small : Bool) (w0 : Int) (s : SieveSpec) (mg : Nat) : Nat :=
  (if small then modMul (-w0 - s.offset) s.p mg else modLong (-w0 - s.offset) s.p).toNat

/-- `Ratpoints.Sieve.AndRowsRowInvariant` for the modulus `s` with the bit arrays below `c` done,
and `r`, the index that the loops over the bit arrays use, is the residue of `-(w0 + offset)`
modulo `p > 0`: the invariant of each loop over the bit arrays, with the `c` of that loop. -/
def AndRowsStartInvariant {m : Nat} (cw : UInt64) (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (s : SieveSpec) (r c : Nat) (surv : Vector UInt64 m) : Prop :=
  (0 < s.p ∧ r = ((-(w0 + s.offset)) % (s.p : Int)).toNat) ∧
    AndRowsRowInvariant cw w0 n pref s c surv

/-- The invariant of the loops of `Ratpoints.Sieve.andRows` over the bit arrays before the first
whole period of the row of `s`, with the reciprocal `mg` of the cursor: the bit arrays `done` are
done. -/
abbrev AndRowsHeadInvariant {m : Nat} (small : Bool) (cw : UInt64) (w0 : Int) (n : Nat)
    (pref : List SieveSpec) (s : SieveSpec) (mg : Nat) (done : List Nat) (surv : Vector UInt64 m) :
    Prop :=
  AndRowsStartInvariant cw w0 n pref s (andRowsStart small w0 s mg) done.length surv

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over the whole periods of the row of
`s`, with the reciprocal `mg` of the cursor: the bit arrays before the first whole period and the
periods `done` are done. -/
abbrev AndRowsPeriodInvariant {m : Nat} (small : Bool) (cw : UInt64) (w0 : Int) (n : Nat)
    (pref : List SieveSpec) (s : SieveSpec) (mg : Nat) (done : List Nat) (surv : Vector UInt64 m) :
    Prop :=
  AndRowsStartInvariant cw w0 n pref s (andRowsStart small w0 s mg)
    (andRowsStart small w0 s mg + done.length * s.p) surv

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over one whole period of the row of `s`,
with the reciprocal `mg` of the cursor, after the periods `periods`: the bit arrays `done` of the
current period are done too. -/
abbrev AndRowsPacketInvariant {m : Nat} (small : Bool) (cw : UInt64) (w0 : Int) (n : Nat)
    (pref : List SieveSpec) (s : SieveSpec) (mg : Nat) (periods done : List Nat)
    (surv : Vector UInt64 m) : Prop :=
  AndRowsStartInvariant cw w0 n pref s (andRowsStart small w0 s mg)
    (andRowsStart small w0 s mg + periods.length * s.p + done.length) surv

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over the bit arrays after the last whole
period of the row of `s`, with the reciprocal `mg` of the cursor: the bit arrays before them and
the bit arrays `done` are done. -/
abbrev AndRowsTailInvariant {m : Nat} (small : Bool) (cw : UInt64) (w0 : Int) (n : Nat)
    (pref : List SieveSpec) (s : SieveSpec) (mg : Nat) (done : List Nat) (surv : Vector UInt64 m) :
    Prop :=
  AndRowsStartInvariant cw w0 n pref s (andRowsStart small w0 s mg)
    (andRowsStart small w0 s mg + (n - andRowsStart small w0 s mg) / s.p * s.p + done.length) surv

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` that sets the bit arrays of the piece to
the class word `cw`, from the last: after `c` steps, the words of the last `c` of the `n` bit arrays
are `cw`. -/
def AndRowsFillInvariant {m : Nat} (cw : UInt64) (n c : Nat) (surv : Vector UInt64 m) : Prop :=
  ∀ y < n * rbaPack, n - c ≤ y / rbaPack → surv[y]! = cw

theorem andRowsFillInvariant_zero {m : Nat} (cw : UInt64) (n : Nat) (surv : Vector UInt64 m) :
    AndRowsFillInvariant cw n ([] : List Nat).length surv := fun y hy h ↦ by
  simp only [List.length_nil, Nat.sub_zero] at h
  lia [(Nat.div_lt_iff_lt_mul rbaPack_pos).mpr hy]

/-- A step of the loop of `Ratpoints.Sieve.andRows` that sets the bit arrays to the class word:
bit array `n - 1 - cur` set. -/
theorem AndRowsFillInvariant.append_fillBitArray {n cur : Nat} {cw : UInt64}
    {done suff : List Nat} {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsFillInvariant cw n done.length surv)
    (hl : ForIn.toList [0:n] = done ++ cur :: suff) :
    AndRowsFillInvariant cw n (done ++ [cur]).length (fillBitArray surv (n - 1 - cur) cw) := by
  have := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  intro y hy hy'
  rw [getElem!_fillBitArray _ _ _ (Nat.lt_add_one_mul_of_lt_mul hy)]
  rw [List.length_append, List.length_singleton] at hy'
  split
  · rfl
  · exact h y hy (by lia)

/-- After the bit arrays are all set to the class word, the loop over the moduli starts with no
moduli. -/
theorem AndRowsFillInvariant.andRowsLoopInvariant {m n : Nat} {cw : UInt64} {w0 : Int}
    {mgs : List Nat} {surv : Vector UInt64 m}
    (h : AndRowsFillInvariant cw n (ForIn.toList [0:n]).length surv) :
    AndRowsLoopInvariant cw w0 (n * rbaPack) mgs [] (surv, Std.toStream mgs) :=
  ⟨rfl, fun y hy ↦ h y hy (by simp)⟩

theorem AndRowsLoopInvariant.getElem!_eq {m n : Nat} {cw : UInt64} {w0 : Int} {mgs : List Nat}
    {pref : List SieveSpec} {st : Vector UInt64 m × List Nat}
    (h : AndRowsLoopInvariant cw w0 (n * rbaPack) mgs pref st) {y : Nat}
    (hy : y < n * rbaPack) : st.1[y]! = andWords pref cw w0 y :=
  h.2 y hy

/-- The reciprocals do not run out before the moduli. -/
theorem AndRowsLoopInvariant.next?_ne_none {m k n : Nat} {cw : UInt64} {w0 : Int} {small : Bool}
    {specs pref suff : List SieveSpec} {s : SieveSpec} {mgs rest : List Nat}
    {surv : Vector UInt64 m}
    (pre : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small w0 (w0 + n))
    (hs : specs = pref ++ s :: suff) (h : AndRowsLoopInvariant cw w0 k mgs pref (surv, rest)) :
    Std.Stream.next? rest ≠ none :=
  next?_ne_none_of_lt pre.2.1 hs fun _ ↦ h.1

/-- The index of the first row of the first stage, as `Ratpoints.Sieve.andRows` computes it with the
reciprocal `mg` of the cursor, is the residue of `-(w0 + offset)`
(`Ratpoints.Sieve.SieveSpec.Fits.ite_modMul_modLong_eq_emod`), since `mg` is the reciprocal of the
modulus. -/
theorem AndRowsLoopInvariant.andRowsHeadInvariant {m n : Nat} {cw : UInt64} {w0 : Int}
    {small : Bool} {specs pref suff : List SieveSpec} {s : SieveSpec} {mgs rest rest' : List Nat}
    {mg : Nat} {surv : Vector UInt64 m}
    (pre : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small w0 (w0 + n))
    (hs : specs = pref ++ s :: suff)
    (h : AndRowsLoopInvariant cw w0 (n * rbaPack) mgs pref (surv, rest))
    (hnext : Std.Stream.next? rest = some (mg, rest')) :
    AndRowsHeadInvariant small cw w0 n pref s mg [] surv := by
  obtain ⟨rfl, -⟩ := eq_magic_and_of_next?_eq_some pre.2.1 hs (fun _ ↦ h.1) hnext
  have hfit := pre.1 s (by simp [hs])
  refine ⟨⟨hfit.pos, ?_⟩, fun y hy ↦ by simp [h.2 y hy]⟩
  rw [andRowsStart, hfit.ite_modMul_modLong_eq_emod pre.2.2, Int.neg_add, Int.sub_eq_add_neg]

/-- After the bit arrays of the modulus `s` are all done, the cursor moves on. -/
theorem AndRowsLoopInvariant.push {m n c : Nat} {cw : UInt64} {w0 : Int}
    {mgs rest rest' : List Nat} {pref : List SieveSpec} {s : SieveSpec} {r mg : Nat}
    {surv surv' : Vector UInt64 m}
    (h : AndRowsLoopInvariant cw w0 (n * rbaPack) mgs pref (surv, rest))
    (hnext : Std.Stream.next? rest = some (mg, rest'))
    (h' : AndRowsStartInvariant cw w0 n pref s r c surv') (hc : n ≤ c) :
    AndRowsLoopInvariant cw w0 (n * rbaPack) mgs (pref ++ [s]) (surv', rest') := by
  refine ⟨?_, fun y hy ↦ ?_⟩
  · change rest' = mgs.drop (pref ++ [s]).length
    rw [List.length_append, List.length_singleton, ← List.drop_drop, ← show rest = _ from h.1,
      List.eq_cons_of_next?_eq_some hnext]
    rfl
  · have : y / rbaPack < c := Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul rbaPack_pos).mpr hy) hc
    simp [h'.2 y hy, this, andWords_concat]

theorem AndRowsStartInvariant.of_eq {m n : Nat} {cw : UInt64} {w0 : Int} {pref : List SieveSpec}
    {s : SieveSpec} {r c c' : Nat} {surv : Vector UInt64 m}
    (h : AndRowsStartInvariant cw w0 n pref s r c surv) (hc : c = c') :
    AndRowsStartInvariant cw w0 n pref s r c' surv :=
  hc ▸ h

/-- One step of the loops of `Ratpoints.Sieve.andRows` for the modulus `s`: bit array `c` and-ed
with bit array `(w0 + offset + c) mod p` of the row. -/
theorem AndRowsRowInvariant.add_one_andBitArray {n : Nat} {cw : UInt64} {w0 : Int}
    {pref : List SieveSpec} {s : SieveSpec} {c x : Nat} {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsRowInvariant cw w0 n pref s c surv)
    (hx : ((w0 + s.offset + c) % (s.p : Int)).toNat = x) :
    AndRowsRowInvariant cw w0 n pref s (c + 1) (andBitArray surv c s.row x) := by
  intro y hy
  rw [getElem!_andBitArray _ _ _ _ (Nat.lt_add_one_mul_of_lt_mul hy), h y hy]
  by_cases hyc : y / rbaPack = c
  · subst hyc
    simp only [SieveSpec.wordAt, hx, ite_true, Nat.lt_irrefl, ite_false, Nat.lt_succ_self]
  · simp only [hyc, ite_false]
    split <;> split <;> first | rfl | lia

theorem AndRowsStartInvariant.add_append_andBitArray {n m : Nat} {cw : UInt64} {w0 : Int}
    {pref : List SieveSpec} {s : SieveSpec} {r c0 x : Nat} {done suff : List Nat} {cur : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsStartInvariant cw w0 n pref s r (c0 + done.length) surv)
    (hl : ForIn.toList [0:m] = done ++ cur :: suff)
    (hx : ((w0 + s.offset + ((c0 + cur : Nat) : Int)) % (s.p : Int)).toNat = x) :
    AndRowsStartInvariant cw w0 n pref s r (c0 + (done ++ [cur]).length)
      (andBitArray surv (c0 + cur) s.row x) := by
  have := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have h2 : AndRowsRowInvariant cw w0 n pref s (c0 + cur) surv := this ▸ h.2
  exact ⟨h.1, by simpa [this, Nat.add_assoc] using h2.add_one_andBitArray hx⟩

/-- The loops of `Ratpoints.Sieve.andRows` before the first whole period: bit array `cur` is and-ed
with bit array `p - r + cur` of the row, for `r = -(w0 + offset) mod p`. -/
theorem AndRowsStartInvariant.append_andBitArray_sub {n m : Nat} {cw : UInt64} {w0 : Int}
    {pref : List SieveSpec} {s : SieveSpec} {r : Nat} {done suff : List Nat} {cur : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsStartInvariant cw w0 n pref s r done.length surv)
    (hl : ForIn.toList [0:m] = done ++ cur :: suff) (hm : m ≤ r) :
    AndRowsStartInvariant cw w0 n pref s r (done ++ [cur]).length
      (andBitArray surv cur s.row (s.p - r + cur)) := by
  have := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hx := Int.toNat_add_emod_of_lt (a := w0 + s.offset) (j := cur) h.1.1 (by rw [← h.1.2]; lia)
  rw [← h.1.2] at hx
  simpa using AndRowsStartInvariant.add_append_andBitArray (c0 := 0)
    (h.of_eq (Nat.zero_add _).symm) hl (by simpa using hx)

/-- The loop of `Ratpoints.Sieve.andRows` over one whole period: bit array `r + k p + i` is and-ed
with bit array `i` of the row, for `r = -(w0 + offset) mod p`. -/
theorem AndRowsStartInvariant.append_andBitArray_period {n mk : Nat} {cw : UInt64} {w0 : Int}
    {pref : List SieveSpec} {s : SieveSpec} {r : Nat} {periods suffK done suff : List Nat}
    {k i : Nat} {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsStartInvariant cw w0 n pref s r (r + periods.length * s.p + done.length) surv)
    (hlk : ForIn.toList [0:mk] = periods ++ k :: suffK)
    (hl : ForIn.toList [0:s.p] = done ++ i :: suff) :
    AndRowsStartInvariant cw w0 n pref s r (r + periods.length * s.p + (done ++ [i]).length)
      (andBitArray surv (r + k * s.p + i) s.row i) := by
  have hk := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hlk
  have hx := Int.toNat_add_add_emod (a := w0 + s.offset) (k := k)
    (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
  rw [← h.1.2] at hx
  rw [hk] at h ⊢
  exact h.add_append_andBitArray hl hx

/-- The loop of `Ratpoints.Sieve.andRows` after the last whole period: bit array
`r + ⌊(n - r) / p⌋ p + i` is and-ed with bit array `i` of the row, for
`r = -(w0 + offset) mod p`. -/
theorem AndRowsStartInvariant.append_andBitArray_tail {n : Nat} {cw : UInt64} {w0 : Int}
    {pref : List SieveSpec} {s : SieveSpec} {r : Nat} {done suff : List Nat} {i : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsStartInvariant cw w0 n pref s r (r + (n - r) / s.p * s.p + done.length) surv)
    (hl : ForIn.toList [0:(n - r) % s.p] = done ++ i :: suff) :
    AndRowsStartInvariant cw w0 n pref s r (r + (n - r) / s.p * s.p + (done ++ [i]).length)
      (andBitArray surv (r + (n - r) / s.p * s.p + i) s.row i) := by
  have hi := Nat.lt_of_lt_of_le (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
    (Nat.le_of_lt (Nat.mod_lt _ h.1.1))
  have hx := Int.toNat_add_add_emod (a := w0 + s.offset) (k := (n - r) / s.p) hi
  rw [← h.1.2] at hx
  exact h.add_append_andBitArray hl hx

/- The invariants are irreducible from here on, so that each alternative of the dispatch of the
verification conditions of `Ratpoints.Sieve.andRows` below fails fast on the conditions of the
other loops. -/
attribute [local irreducible] AndRowsFillInvariant AndRowsLoopInvariant AndRowsStartInvariant

attribute [local simp] Nat.div_add_mod' in
/-- Each modulus `s` has its row read at the offset of `s` (`Ratpoints.Sieve.SieveSpec.wordAt`): the
loops over the bit arrays start at the index `r` of the residue of `-(w0 + offset)`, which the
reduction by the reciprocal of the cursor gives under the test `small`
(`Ratpoints.Sieve.SieveSpec.Fits.ite_modMul_modLong_eq_emod`); the reciprocals run in step with the
moduli and do not run out before them. -/
@[spec]
theorem andRows_spec (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (cw : UInt64)
    (w0 : Int) (n : Nat) (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small w0 (w0 + n) ⦄
    andRows specs mgs small cw w0 n surv
    ⦃ fun surv' ↦ ∀ y < n * rbaPack, surv'[y]! = andWords specs cw w0 y ⦄ := by
  vcgen [andRows] invariants
  | inv1 => fun done _ surv ↦ AndRowsFillInvariant cw n done.length surv
  | inv2 => fun l _ ↦ AndRowsLoopInvariant cw w0 (n * rbaPack) mgs l
  | inv3 l s _ _ _ _ _ mg _ _ _ => fun d _ ↦ AndRowsHeadInvariant small cw w0 n l s mg d
  | inv4 l s _ _ _ _ _ mg _ _ _ => fun d _ ↦ AndRowsHeadInvariant small cw w0 n l s mg d
  | inv5 l s _ _ _ _ _ mg _ _ _ _ _ => fun d _ ↦ AndRowsPeriodInvariant small cw w0 n l s mg d
  | inv6 l s _ _ _ _ _ mg _ _ _ _ _ _ _ => fun d _ ↦ AndRowsTailInvariant small cw w0 n l s mg d
  | inv7 l s _ _ _ _ _ mg _ _ _ _ _ periods _ _ _ _ _ => fun d _ ↦
      AndRowsPacketInvariant small cw w0 n l s mg periods d
  all_goals first
    | solve_by_elim [andRowsFillInvariant_zero,
        AndRowsFillInvariant.append_fillBitArray, AndRowsFillInvariant.andRowsLoopInvariant]
    | exact AndRowsLoopInvariant.getElem!_eq ‹_› ‹_›
    | exact absurd ‹_› (AndRowsLoopInvariant.next?_ne_none ‹_› ‹_› ‹_›)
    | exact AndRowsLoopInvariant.andRowsHeadInvariant ‹_› ‹_› ‹_› ‹_›
    | exact AndRowsStartInvariant.append_andBitArray_sub ‹_› ‹_› (by lia)
    | exact AndRowsStartInvariant.append_andBitArray_period ‹_› ‹_› ‹_›
    | exact AndRowsStartInvariant.append_andBitArray_tail ‹_› ‹_›
    | exact AndRowsLoopInvariant.push ‹_› ‹_› ‹_› (by simp [Nat.add_assoc] <;> lia)
    | exact AndRowsStartInvariant.of_eq ‹_› (by simp [Nat.add_mul, Nat.add_assoc]; done)

/-! ### The check of a numerator and the set bits of a word -/

theorem pointsOfDen_eq_flatMap_checkNum (c : List Int) (d : Nat) (b : Int) (xs : List Int) :
    BruteForce.pointsOfDen c d b xs =
      xs.flatMap (checkNum (BruteForce.scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b false) :=
  rfl

theorem checkNum_eq_map (w : List Int) (f b : Int) (rev : Bool) (a : Int) :
    checkNum w f b rev a = (checkNum w f b false a).map (if rev then swapPoint else id) := by
  cases rev <;> simp [checkNum, apply_ite (List.map swapPoint)]

theorem flatMap_checkNum (w : List Int) (f b : Int) (rev : Bool) (xs : List Int) :
    xs.flatMap (checkNum w f b rev) =
      (xs.flatMap (checkNum w f b false)).map (if rev then swapPoint else id) :=
  List.map_flatMap ▸ congrArg (List.flatMap · xs) (funext (checkNum_eq_map w f b rev))

/-- The property of the array `out` of a walk through the set bits of the word `x0`, lowest first,
that appends the list `g t` of each set bit `t` to the array `out0`, after the set bits below `k`:
`out` is `out0` followed by the lists of the set bits `t < k` of `x0`, in increasing order. In
`Ratpoints.Sieve.walkWord`, `g t` is the list of the points that `Ratpoints.Sieve.acceptedPoints`
gives for the numerator of bit `t` (the test of a candidate, then the exact check); in
`Ratpoints.Sieve.wordsDens`, the list of the denominator of bit `t` alone. -/
def WalkWordInvariant {β : Type u} (g : Nat → List β) (x0 : UInt64) (out0 : Array β) (k : Nat)
    (out : Array β) : Prop :=
  out.toList = out0.toList ++ ((List.range k).filter (x0.toBitVec.getLsbD ·)).flatMap g

/-- `Ratpoints.Sieve.WalkWhileInvariant` for `Ratpoints.Sieve.WalkWordInvariant` as the invariant of
the `while` loop of `Ratpoints.Sieve.walkWord`, whose state has the word first. -/
def WalkWordWhileInvariant {β : Type u} (g : Nat → List β) (x0 : UInt64) (out0 : Array β) :
    Std.WP.WhileInvariant (UInt64 × Array β) Prop :=
  .mk fun exit s ↦ WalkWhileInvariant x0 (WalkWordInvariant g x0 out0) exit (s.2, s.1)

theorem walkWordInvariant_zero {β : Type u} (g : Nat → List β) (x0 : UInt64) (out0 : Array β) :
    WalkWordInvariant g x0 out0 0 out0 := by
  simp [WalkWordInvariant]

theorem WalkWordInvariant.append_ctz {β : Type u} {g : Nat → List β} {x0 x : UInt64}
    {out0 out : Array β} {k : Nat} (h : WalkWordInvariant g x0 out0 k out)
    (hx : ClearedBelow x0 k x) (hx0 : x ≠ 0) :
    WalkWordInvariant g x0 out0 (x.toBitVec.ctz.toNat + 1)
      (out ++ (g x.toBitVec.ctz.toNat).toArray) := by
  simp only [WalkWordInvariant] at h ⊢
  simp [h, hx.filter_range_succ_ctz hx0]

theorem WalkWordInvariant.toList_eq {β : Type u} {g : Nat → List β} {x0 x : UInt64}
    {out0 out : Array β} (h : WalkWhileInvariant x0 (WalkWordInvariant g x0 out0) true (out, x)) :
    out.toList = out0.toList ++ ((List.range 64).filter (x0.toBitVec.getLsbD ·)).flatMap g := by
  obtain ⟨k, hcl, hout⟩ := h.exists_clearedBelow_zero
  rw [hout, hcl.filter_range_of_eq_zero]

end Sieve

end Ratpoints

end
