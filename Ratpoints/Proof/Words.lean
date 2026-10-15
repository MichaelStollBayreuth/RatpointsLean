/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Sieve
public import Ratpoints.Proof.SetBits
public import Std.WP

import Ratpoints.Proof.Bits
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
* `Ratpoints.Sieve.WalkWordInvariant`: the invariant of the array that a walk through the set bits
  of a word, lowest first, appends to.

## Main statements

* `Ratpoints.Sieve.getElem!_andBitArray`: `Ratpoints.Sieve.andBitArray` ands the words of one bit
  array with the words of a bit array of the row, and leaves the other words as they are.
* `Ratpoints.Sieve.getLsbD_clearLowBits`, `Ratpoints.Sieve.getLsbD_clearHighBits`: which bits the
  masks at the two ends of the numerator range keep.
* `Ratpoints.Sieve.isZeroAt_eq_true_iff`: a bit array is zero when all its words are.
* `Ratpoints.Sieve.SieveEntry.getLsbD_row`: bit `t` of word `j` of the row of a denominator in words
  says whether the row admits the numerator `64 j + t`.
* `Ratpoints.Sieve.SieveEntry.get_rows`, `Ratpoints.Sieve.SieveEntry.row_mod`: the thunk of a
  residue gives its row, and the row of `b` is the row of `b mod p`.
* `Ratpoints.Sieve.Entry.admits_mod_of_dvd`, `Ratpoints.Sieve.Power.admits_mod_of_dvd`: the row of
  a prime or a prime power reads the residues modulo a multiple of its modulus as those of the
  numbers.
* `Ratpoints.Sieve.SieveEntry.admits_mul`: the row of a sieve entry whose factors have their tables
  of inverses is unchanged when the denominator and the numerator are scaled by a unit.
* `Ratpoints.Sieve.andWords_append`: and-ing the rows of two lists of moduli one after the other is
  and-ing those of their concatenation.
* `Ratpoints.Sieve.andRows_spec`: after the first stage over a piece with the rows of a denominator
  `b` from the class word `cw`, bit `t` of word `y` of the piece is bit `t` of `cw` and the survivor
  test of the numerator `rbaLength w0 + 64 y + t`, whose bit in `cw` is bit `t`
  (`Ratpoints.Sieve.classBit_rbaLength_mul_add`).
* `Ratpoints.Sieve.pointsOfDen_eq_flatMap_checkNum`: the points that the brute-force reference finds
  over a denominator are those of `Ratpoints.Sieve.checkNum` for its numerators, one after the
  other, with the flag of the reversal clear.
* `Ratpoints.Sieve.checkNum_eq_map`, `Ratpoints.Sieve.flatMap_checkNum`: with the flag of the
  reversal set, the check of a numerator gives the points of the check with the flag clear, mapped
  by `Ratpoints.Sieve.swapPoint`, and so do the checks of a list of numerators, one after the
  other.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Sieve` does; the lemmas on words that
are not about the model are in `Ratpoints.Proof.Bits`. The proofs use only that `Ratpoints.rbaPack`
is positive, never its value. The scaling by a unit needs an inverse of the unit and the tables of
inverses, no primality. The contracts of the second and the third stage and of the check are in
`Ratpoints.Proof.Stages`, those of the walk, of the scan, of one piece and of one denominator in
`Ratpoints.Proof.Sift`. The bit of a numerator in a class word, the contract of the lowest set bit
of a word and the invariant of a `while` loop over the set bits of a word are in
`Ratpoints.Proof.SetBits`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

/-! ### The width of the bit arrays -/

theorem rbaLength_eq : rbaLength = 64 * rbaPack := rfl

theorem rbaLength_pos : 0 < rbaLength := rbaLength_eq ▸ Nat.mul_pos (by decide) rbaPack_pos

theorem natCast_rbaLength_pos : (0 : Int) < rbaLength := Int.natCast_pos.mpr rbaLength_pos

theorem rbaLength_mul (j : Nat) : rbaLength * j = 64 * (rbaPack * j) := by
  rw [rbaLength_eq, Nat.mul_assoc]

theorem lt_rbaLength_mul_of_lt {n y t : Nat} (hy : y < n * rbaPack) (ht : t < 64) :
    64 * y + t < rbaLength * n := by
  rw [rbaLength_eq, Nat.mul_assoc, Nat.mul_comm rbaPack n]
  lia

namespace Sieve

universe u

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

theorem getLsbD_packedPattern (pat : Array Bool) (p : Nat) {i : Nat}
    (hi : i < 64 * (p / 64 + 2)) :
    (packedPattern pat p)[i / 64]!.toBitVec.getLsbD (i % 64) = pat[i % p]! := by
  rw [packedPattern, Array.getElem!_map_range _ (by lia),
    UInt64.getLsbD_fold_or_one_shiftLeft _ (Nat.le_refl 64), Nat.div_add_mod]
  simp [Nat.mod_lt]

theorem getLsbD_window (E : Array UInt64) (s t : Nat) :
    (window E s).toBitVec.getLsbD t =
      (decide (t < 64) && E[(s + t) / 64]!.toBitVec.getLsbD ((s + t) % 64)) := by
  rw [window]
  split
  · grind
  · rw [UInt64.getLsbD_shiftRight_or_shiftLeft ‹s % 64 ≠ 0› (Nat.mod_lt s (by decide))]
    grind

/-- The hypothesis `s < p` keeps the 64 positions read within the packed words. -/
theorem getLsbD_window_packedPattern (pat : Array Bool) {p s : Nat} (hs : s < p) (t : Nat) :
    (window (packedPattern pat p) s).toBitVec.getLsbD t =
      (decide (t < 64) && pat[(s + t) % p]!) := by
  grind [getLsbD_window, getLsbD_packedPattern]

theorem SieveEntry.getLsbD_row (e : SieveEntry) (b : Nat) {j : Nat} (hj : j < e.p * rbaPack)
    (t : Nat) :
    (e.row b)[j]!.toBitVec.getLsbD t = (decide (t < 64) && e.admits b (64 * j + t)) := by
  have hp : 0 < e.p := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hj
  simp only [SieveEntry.row, Array.getElem!_map_range _ hj,
    Array.getElem!_map_range _ (Nat.mod_lt _ hp), getLsbD_window_packedPattern _ (Nat.mod_lt _ hp)]
  exact congrArg (decide (t < 64) && ·) (e.admits_congr b (by simp))

theorem SieveEntry.get_rows (e : SieveEntry) {r : Nat} (hr : r < e.p) : e.rows[r]!.get = e.row r :=
  congrArg Thunk.get (Array.getElem!_map_range _ hr)

theorem SieveEntry.row_mod (e : SieveEntry) (b : Nat) : e.row (b % e.p) = e.row b := by
  simp [SieveEntry.row, SieveEntry.admits_mod]

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
number `w0` on: word `y % rbaPack` of bit array `(w0 + y / rbaPack) mod p` of the row, for the
number `rbaPack` of words of a bit array (`Ratpoints.rbaPack`). -/
def SieveSpec.wordAt (s : SieveSpec) (w0 : Int) (y : Nat) : UInt64 :=
  s.row[rbaPack * ((w0 + (y / rbaPack : Nat)) % (s.p : Int)).toNat + y % rbaPack]!

/-- Word `κ < Ratpoints.rbaPack` of the row of `s` for the word number `i` is word `κ` of bit array
`i mod p`. -/
theorem SieveSpec.wordAt_of_lt (s : SieveSpec) (i : Int) {κ : Nat} (hκ : κ < rbaPack) :
    s.wordAt i κ = s.row[rbaPack * (i % (s.p : Int)).toNat + κ]! := by
  simp [SieveSpec.wordAt, Nat.div_eq_of_lt hκ, Nat.mod_eq_of_lt hκ]

/-- The row word of word `κ` of bit array `pos` of a piece from the word number `w0` on is the row
word of word `κ` of the bit array with the word number `w0 + pos`. -/
theorem SieveSpec.wordAt_rbaPack_mul_add (s : SieveSpec) (w0 : Int) (pos : Nat) {κ : Nat}
    (hκ : κ < rbaPack) : s.wordAt w0 (rbaPack * pos + κ) = s.wordAt (w0 + pos) κ := by
  simp only [SieveSpec.wordAt, Nat.mul_add_div rbaPack_pos, Nat.div_eq_of_lt hκ, Nat.mul_add_mod,
    Nat.add_zero, Int.natCast_zero, Int.add_zero]

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

theorem SieveSpec.getLsbD_wordAt_mk (e : SieveEntry) (b : Nat) (hp : 0 < e.p) (w0 : Int)
    (y t : Nat) :
    (wordAt ⟨e.p, e.row b⟩ w0 y).toBitVec.getLsbD t =
      (decide (t < 64) && e.admits b (rbaLength * w0 + 64 * y + t)) := by
  have hu : ((w0 + (y / rbaPack : Nat)) % (e.p : Int)).toNat < e.p := by
    have := Int.emod_lt_of_pos (w0 + (y / rbaPack : Nat)) (b := e.p) (by lia)
    lia
  have hj : rbaPack * ((w0 + (y / rbaPack : Nat)) % (e.p : Int)).toNat + y % rbaPack <
      e.p * rbaPack :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.mod_lt y rbaPack_pos) _)
      (by rw [← Nat.mul_succ, Nat.mul_comm]; exact Nat.mul_le_mul_right _ hu)
  rw [wordAt, SieveEntry.getLsbD_row e b hj, e.admits_congr b (emod_wordIndex e.p hp w0 y t)]

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

theorem getLsbD_andWords_map {entries : List SieveEntry} (b : Nat) (hp : ∀ e ∈ entries, 0 < e.p)
    (cw : UInt64) (w0 : Int) (y t : Nat) :
    (andWords (entries.map fun e ↦ ⟨e.p, e.row b⟩) cw w0 y).toBitVec.getLsbD t =
      (cw.toBitVec.getLsbD t && survives entries b (rbaLength * w0 + 64 * y + t)) := by
  rw [andWords, UInt64.getLsbD_foldl_and, List.all_map, survives]
  grind [SieveSpec.getLsbD_wordAt_mk, List.all_eq_true]

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` that fills the piece with the class
word `cw`: the first `k` words are `cw`. -/
def AndRowsFillInvariant {m : Nat} (cw : UInt64) (k : Nat) (surv : Vector UInt64 m) : Prop :=
  ∀ y < k, surv[y]! = cw

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over the moduli: after the moduli
`pref`, the words of the piece are the class word `cw` and-ed with their row words
(`Ratpoints.Sieve.andWords`). -/
def AndRowsInvariant {m : Nat} (cw : UInt64) (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (surv : Vector UInt64 m) : Prop :=
  ∀ y < n * rbaPack, surv[y]! = andWords pref cw w0 y

/-- The invariant of the loops of `Ratpoints.Sieve.andRows` over the bit arrays for the modulus
`s` after the moduli `pref`: the words of the bit arrays below `c` are and-ed with the row of `s`
as well, the others not yet. -/
def AndRowsRowInvariant {m : Nat} (cw : UInt64) (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (s : SieveSpec) (c : Nat) (surv : Vector UInt64 m) : Prop :=
  ∀ y < n * rbaPack, surv[y]! =
    if y / rbaPack < c then andWords pref cw w0 y &&& s.wordAt w0 y else andWords pref cw w0 y

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over the whole periods for the modulus
`s`: the bit arrays before the first whole period and the periods `done` are done. -/
abbrev AndRowsPeriodInvariant {m : Nat} (cw : UInt64) (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (s : SieveSpec) (done : List Nat) (surv : Vector UInt64 m) : Prop :=
  AndRowsRowInvariant cw w0 n pref s (((-w0) % (s.p : Int)).toNat + done.length * s.p) surv

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over one whole period for the modulus
`s`, after the periods `periods`: the bit arrays `done` of the current period are done too. -/
abbrev AndRowsPacketInvariant {m : Nat} (cw : UInt64) (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (s : SieveSpec) (periods done : List Nat) (surv : Vector UInt64 m) : Prop :=
  AndRowsRowInvariant cw w0 n pref s
    (((-w0) % (s.p : Int)).toNat + periods.length * s.p + done.length) surv

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over the bit arrays after the last
whole period for the modulus `s`: the bit arrays before them and the bit arrays `done` are
done. -/
abbrev AndRowsTailInvariant {m : Nat} (cw : UInt64) (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (s : SieveSpec) (done : List Nat) (surv : Vector UInt64 m) : Prop :=
  AndRowsRowInvariant cw w0 n pref s (((-w0) % (s.p : Int)).toNat +
    (n - ((-w0) % (s.p : Int)).toNat) / s.p * s.p + done.length) surv

theorem andRowsFillInvariant_zero {m : Nat} (cw : UInt64) (surv : Vector UInt64 m) :
    AndRowsFillInvariant cw 0 surv :=
  fun _ h ↦ absurd h (Nat.not_lt_zero _)

theorem AndRowsFillInvariant.append_set! {cw : UInt64} {n : Nat} {done suff : List Nat}
    {cur : Nat} {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsFillInvariant cw done.length surv)
    (hl : ForIn.toList [0:n * rbaPack] = done ++ cur :: suff) :
    AndRowsFillInvariant cw (done ++ [cur]).length (surv.set! cur cw) := by
  have := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  intro y hy
  rw [List.length_append, List.length_singleton] at hy
  rw [Vector.getElem!_set! (Nat.lt_add_one_mul_of_lt_mul (by lia))]
  split
  · rfl
  · exact h y (by lia)

theorem andRowsInvariant_nil {m n : Nat} {cw : UInt64} {w0 : Int} {surv : Vector UInt64 m}
    (h : AndRowsFillInvariant cw (ForIn.toList [0:n * rbaPack]).length surv) :
    AndRowsInvariant cw w0 n [] surv :=
  fun y hy ↦ h y (by simpa using hy)

theorem AndRowsInvariant.getElem!_eq {m n : Nat} {cw : UInt64} {w0 : Int} {pref : List SieveSpec}
    {surv : Vector UInt64 m} (h : AndRowsInvariant cw w0 n pref surv) {y : Nat}
    (hy : y < n * rbaPack) : surv[y]! = andWords pref cw w0 y :=
  h y hy

theorem AndRowsInvariant.andRowsRowInvariant {m n : Nat} {cw : UInt64} {w0 : Int}
    {pref : List SieveSpec} {s : SieveSpec} {surv : Vector UInt64 m}
    (h : AndRowsInvariant cw w0 n pref surv) :
    AndRowsRowInvariant cw w0 n pref s 0 surv := by
  intro y hy
  simp [h y hy]

theorem AndRowsRowInvariant.of_eq {m n : Nat} {cw : UInt64} {w0 : Int} {pref : List SieveSpec}
    {s : SieveSpec} {c c' : Nat} {surv : Vector UInt64 m}
    (h : AndRowsRowInvariant cw w0 n pref s c surv)
    (hc : c = c') : AndRowsRowInvariant cw w0 n pref s c' surv :=
  hc ▸ h

theorem AndRowsRowInvariant.andRowsInvariant {m n : Nat} {cw : UInt64} {w0 : Int}
    {pref : List SieveSpec} {s : SieveSpec} {c : Nat} {surv : Vector UInt64 m}
    (h : AndRowsRowInvariant cw w0 n pref s c surv) (hc : n ≤ c) :
    AndRowsInvariant cw w0 n (pref ++ [s]) surv := by
  intro y hy
  have : y / rbaPack < c := Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul rbaPack_pos).mpr hy) hc
  simp [h y hy, this, andWords_concat]

/-- One step of the loops of `Ratpoints.Sieve.andRows` for the modulus `s`: bit array `c` and-ed
with bit array `(w0 + c) mod p` of the row. -/
theorem AndRowsRowInvariant.add_one_andBitArray {n : Nat} {cw : UInt64} {w0 : Int}
    {pref : List SieveSpec} {s : SieveSpec} {c x : Nat} {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsRowInvariant cw w0 n pref s c surv) (hx : ((w0 + c) % (s.p : Int)).toNat = x) :
    AndRowsRowInvariant cw w0 n pref s (c + 1) (andBitArray surv c s.row x) := by
  intro y hy
  rw [getElem!_andBitArray _ _ _ _ (Nat.lt_add_one_mul_of_lt_mul hy), h y hy]
  by_cases hyc : y / rbaPack = c
  · subst hyc
    simp only [SieveSpec.wordAt, hx, ite_true, Nat.lt_irrefl, ite_false, Nat.lt_succ_self]
  · simp only [hyc, ite_false]
    split <;> split <;> first | rfl | lia

theorem AndRowsRowInvariant.add_append_andBitArray {n m : Nat} {cw : UInt64} {w0 : Int}
    {pref : List SieveSpec} {s : SieveSpec} {c0 x : Nat} {done suff : List Nat} {cur : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsRowInvariant cw w0 n pref s (c0 + done.length) surv)
    (hl : ForIn.toList [0:m] = done ++ cur :: suff)
    (hx : ((w0 + ((c0 + cur : Nat) : Int)) % (s.p : Int)).toNat = x) :
    AndRowsRowInvariant cw w0 n pref s (c0 + (done ++ [cur]).length)
      (andBitArray surv (c0 + cur) s.row x) := by
  have := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  simpa [this, Nat.add_assoc] using (h.of_eq (by rw [this])).add_one_andBitArray hx

/-- The loops of `Ratpoints.Sieve.andRows` before the first whole period: bit array `cur` is and-ed
with bit array `p - r + cur` of the row, for `r = (-w0) mod p`. -/
theorem AndRowsRowInvariant.append_andBitArray_sub {specs pref suff : List SieveSpec}
    {s : SieveSpec} {n m : Nat} {cw : UInt64} {w0 : Int} {done suff' : List Nat} {cur : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsRowInvariant cw w0 n pref s done.length surv)
    (hl : ForIn.toList [0:m] = done ++ cur :: suff') (hm : m ≤ ((-w0) % (s.p : Int)).toNat)
    (hp : ∀ s ∈ specs, 0 < s.p) (hs : specs = pref ++ s :: suff) :
    AndRowsRowInvariant cw w0 n pref s (done ++ [cur]).length
      (andBitArray surv cur s.row (s.p - ((-w0) % (s.p : Int)).toNat + cur)) := by
  have hlen := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  simpa [hlen] using (h.of_eq hlen).add_one_andBitArray
    (Int.toNat_add_emod_of_lt (hp s (by simp [hs])) (by lia))

/-- The loop of `Ratpoints.Sieve.andRows` over one whole period: bit array `r + k p + i` is and-ed
with bit array `i` of the row, for `r = (-w0) mod p`. -/
theorem AndRowsRowInvariant.append_andBitArray_period {s : SieveSpec} {pref : List SieveSpec}
    {n mk : Nat} {cw : UInt64} {w0 : Int} {periods suffK done suff : List Nat} {k i : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsPacketInvariant cw w0 n pref s periods done surv)
    (hlk : ForIn.toList [0:mk] = periods ++ k :: suffK)
    (hl : ForIn.toList [0:s.p] = done ++ i :: suff) :
    AndRowsPacketInvariant cw w0 n pref s periods (done ++ [i])
      (andBitArray surv (((-w0) % (s.p : Int)).toNat + k * s.p + i) s.row i) := by
  have hk := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hlk
  rw [AndRowsPacketInvariant, hk] at h ⊢
  exact h.add_append_andBitArray hl
    (Int.toNat_add_add_emod (Std.Legacy.Range.lt_of_toList_eq_append_cons hl))

/-- The loop of `Ratpoints.Sieve.andRows` after the last whole period: bit array
`r + ⌊(n - r) / p⌋ p + i` is and-ed with bit array `i` of the row, for `r = (-w0) mod p`. -/
theorem AndRowsRowInvariant.append_andBitArray_tail {specs pref suff : List SieveSpec}
    {s : SieveSpec} {n : Nat} {cw : UInt64} {w0 : Int} {done suff' : List Nat} {i : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsTailInvariant cw w0 n pref s done surv)
    (hl : ForIn.toList [0:(n - ((-w0) % (s.p : Int)).toNat) % s.p] = done ++ i :: suff')
    (hp : ∀ s ∈ specs, 0 < s.p) (hs : specs = pref ++ s :: suff) :
    AndRowsTailInvariant cw w0 n pref s (done ++ [i])
      (andBitArray surv (((-w0) % (s.p : Int)).toNat +
        (n - ((-w0) % (s.p : Int)).toNat) / s.p * s.p + i) s.row i) :=
  h.add_append_andBitArray hl (Int.toNat_add_add_emod
    (Nat.lt_of_lt_of_le (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
      (Nat.le_of_lt (Nat.mod_lt _ (hp s (by simp [hs]))))))

/- The invariants are irreducible from here on, so that each alternative of the dispatch of the
verification conditions of `Ratpoints.Sieve.andRows` below fails fast on the conditions of the
other loops. -/
attribute [local irreducible] AndRowsFillInvariant AndRowsInvariant AndRowsRowInvariant

-- The contract of `Ratpoints.Sieve.andRows` for rows of positive moduli: each word of the piece
-- is the class word and-ed with its row words.
private theorem andRows_spec_of_pos (specs : List SieveSpec) (cw : UInt64) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ ∀ s ∈ specs, 0 < s.p ⦄ andRows specs cw w0 n surv
    ⦃ AndRowsInvariant cw w0 n specs ⦄ := by
  vcgen [andRows] invariants
  | inv1 => fun done _ ↦ AndRowsFillInvariant cw done.length
  | inv2 => fun pref _ ↦ AndRowsInvariant cw w0 n pref
  | inv3 pref s _ _ _ _ _ => fun done _ ↦ AndRowsRowInvariant cw w0 n pref s done.length
  | inv4 pref s _ _ _ _ _ => fun done _ ↦ AndRowsRowInvariant cw w0 n pref s done.length
  | inv5 pref s _ _ _ _ _ _ _ => fun done _ ↦ AndRowsPeriodInvariant cw w0 n pref s done
  | inv6 pref s _ _ _ _ _ _ _ _ _ => fun done _ ↦ AndRowsTailInvariant cw w0 n pref s done
  | inv7 pref s _ _ _ _ _ _ _ periods _ _ _ _ _ => fun done _ ↦
      AndRowsPacketInvariant cw w0 n pref s periods done
  all_goals first
    | exact AndRowsFillInvariant.append_set! ‹_› ‹_›
    | exact AndRowsRowInvariant.append_andBitArray_sub ‹_› ‹_› (by lia) ‹_› ‹_›
    | exact AndRowsRowInvariant.append_andBitArray_period ‹_› ‹_› ‹_›
    | exact AndRowsRowInvariant.append_andBitArray_tail ‹_› ‹_› ‹_› ‹_›
    | exact AndRowsRowInvariant.andRowsInvariant ‹_›
        (by simp [Nat.add_assoc, Nat.div_add_mod'] <;> lia)
    | exact AndRowsRowInvariant.of_eq ‹_› (by simp [Nat.add_mul, Nat.add_assoc]; done)
    | exact AndRowsInvariant.andRowsRowInvariant ‹_›
    | exact andRowsInvariant_nil ‹_›
    | exact andRowsFillInvariant_zero _ _

/-- The sieve entries and the denominator are quantified in the postcondition, since the program
does not mention them. -/
@[spec]
theorem andRows_spec (specs : List SieveSpec) (cw : UInt64) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ True ⦄ andRows specs cw w0 n surv
    ⦃ fun surv' ↦ ∀ (entries : List SieveEntry) (b : Nat), (∀ e ∈ entries, 0 < e.p) →
        specs = entries.map (fun e ↦ ⟨e.p, e.row b⟩) → ∀ y < n * rbaPack, ∀ t : Nat,
          surv'[y]!.toBitVec.getLsbD t =
            (cw.toBitVec.getLsbD t && survives entries b (rbaLength * w0 + 64 * y + t)) ⦄ :=
  ⟨fun _ entries b hp hspecs y hy t ↦ by
    subst hspecs
    rw [((andRows_spec_of_pos _ cw w0 n surv).le_wp (List.forall_mem_map.mpr hp)).getElem!_eq hy,
      getLsbD_andWords_map b hp]⟩

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
