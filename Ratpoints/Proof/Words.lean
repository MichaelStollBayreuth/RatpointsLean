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

The lemmas on the operations on the bit arrays of 64-bit words of the model and on its rows as
words, and the contracts of its components on words, as `@[spec]` theorems proved with `vcgen`, the
program logic of Lean core, with loop invariants that are named definitions.

## Main statements

* `Ratpoints.Sieve.getElem!_andBitArray`: `Ratpoints.Sieve.andBitArray` ands the words of one bit
  array with the words of a bit array of the row, and leaves the other words as they are.
* `Ratpoints.Sieve.getLsbD_clearLowBits`, `Ratpoints.Sieve.getLsbD_clearHighBits`: which bits the
  masks at the two ends of the numerator range keep.
* `Ratpoints.Sieve.isZeroAt_eq_true_iff`: a bit array is zero when all its words are.
* `Ratpoints.Sieve.ctz_spec`: for a word other than `0`, the loop of `Ratpoints.Sieve.ctz` ends with
  the number of its trailing zeros.
* `Ratpoints.Sieve.Entry.getLsbD_row`: bit `t` of word `j` of the row of a denominator in words says
  whether the row admits the numerator `64 j + t`.
* `Ratpoints.Sieve.Entry.get_rows`, `Ratpoints.Sieve.Entry.row_mod`: the thunk of a residue gives
  its row, and the row of `b` is the row of `b mod p`.
* `Ratpoints.Sieve.andRows_spec`: after the first stage over a piece with the rows of a denominator
  `b`, bit `t` of word `y` of the piece is the survivor test of the numerator
  `rbaLength w0 + 64 y + t`.

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

/-! ### The rows as words -/

theorem Entry.admits_congr (e : Entry) (b : Nat) {a a' : Int} (h : a % e.p = a' % e.p) :
    e.admits b a = e.admits b a' := by
  simp [Entry.admits, h]

theorem Entry.admits_add_mul (e : Entry) (b : Nat) (a k : Int) :
    e.admits b (a + e.p * k) = e.admits b a :=
  e.admits_congr b (Int.add_mul_emod_self_left a e.p k)

theorem Entry.admits_mod (e : Entry) (b : Nat) : e.admits (b % e.p) = e.admits b :=
  funext fun _ ↦ by simp [Entry.admits]

theorem getLsbD_packedPattern (pat : Array Bool) (p : Nat) {i : Nat}
    (hi : i < 64 * (p / 64 + 2)) :
    ((packedPattern pat p)[i / 64]!).toBitVec.getLsbD (i % 64) = pat[i % p]! := by
  rw [packedPattern, Array.getElem!_map_range _ (by lia),
    UInt64.getLsbD_fold_or_one_shiftLeft _ (Nat.le_refl 64), Nat.div_add_mod]
  simp [Nat.mod_lt]

theorem getLsbD_window (E : Array UInt64) (s t : Nat) :
    (window E s).toBitVec.getLsbD t =
      (decide (t < 64) && (E[(s + t) / 64]!).toBitVec.getLsbD ((s + t) % 64)) := by
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

theorem Entry.getLsbD_row (e : Entry) (b : Nat) {j : Nat} (hj : j < e.p * rbaPack) (t : Nat) :
    ((e.row b)[j]!).toBitVec.getLsbD t = (decide (t < 64) && e.admits b (64 * j + t)) := by
  have hp : 0 < e.p := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hj
  simp only [Entry.row, Array.getElem!_map_range _ hj, Array.getElem!_map_range _ (Nat.mod_lt _ hp),
    getLsbD_window_packedPattern _ (Nat.mod_lt _ hp)]
  exact congrArg (decide (t < 64) && ·) (e.admits_congr b (by simp))

theorem Entry.get_rows (e : Entry) {r : Nat} (hr : r < e.p) : (e.rows[r]!).get = e.row r :=
  congrArg Thunk.get (Array.getElem!_map_range _ hr)

theorem Entry.row_mod (e : Entry) (b : Nat) : e.row (b % e.p) = e.row b := by
  simp [Entry.row, Entry.admits_mod]

/-! ### One piece -/

/-- The word of the row of `s` that the first stage ands into word `y` of the piece from the word
number `w0` on: word `y % rbaPack` of bit array `(w0 + y / rbaPack) mod p` of the row, for the
number `rbaPack` of words of a bit array (`Ratpoints.rbaPack`). -/
def SieveSpec.wordAt (s : SieveSpec) (w0 : Int) (y : Nat) : UInt64 :=
  s.row[rbaPack * ((w0 + (y / rbaPack : Nat)) % (s.p : Int)).toNat + y % rbaPack]!

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

theorem SieveSpec.getLsbD_wordAt_mk (e : Entry) (b : Nat) (hp : 0 < e.p) (w0 : Int) (y t : Nat) :
    (wordAt ⟨e.p, e.row b⟩ w0 y).toBitVec.getLsbD t =
      (decide (t < 64) && e.admits b (rbaLength * w0 + 64 * y + t)) := by
  have hu : ((w0 + (y / rbaPack : Nat)) % (e.p : Int)).toNat < e.p := by
    have := Int.emod_lt_of_pos (w0 + (y / rbaPack : Nat)) (b := e.p) (by lia)
    lia
  have hj : rbaPack * ((w0 + (y / rbaPack : Nat)) % (e.p : Int)).toNat + y % rbaPack <
      e.p * rbaPack :=
    Nat.lt_of_lt_of_le (Nat.add_lt_add_left (Nat.mod_lt y rbaPack_pos) _)
      (by rw [← Nat.mul_succ, Nat.mul_comm]; exact Nat.mul_le_mul_right _ hu)
  rw [wordAt, Entry.getLsbD_row e b hj, e.admits_congr b (emod_wordIndex e.p hp w0 y t)]

/-- The word `y` of a piece from the word number `w0` on after the first stage with the rows
`specs`: all ones, and-ed in turn with the row words of `y`
(`Ratpoints.Sieve.SieveSpec.wordAt`). -/
def andWords (specs : List SieveSpec) (w0 : Int) (y : Nat) : UInt64 :=
  specs.foldl (fun acc s ↦ acc &&& s.wordAt w0 y) (~~~0)

theorem getLsbD_andWords_map (entries : List Entry) (b : Nat) (hp : ∀ e ∈ entries, 0 < e.p)
    (w0 : Int) (y t : Nat) :
    (andWords (entries.map fun e ↦ ⟨e.p, e.row b⟩) w0 y).toBitVec.getLsbD t =
      (decide (t < 64) && survives entries b (rbaLength * w0 + 64 * y + t)) := by
  rw [andWords, UInt64.getLsbD_foldl_and, UInt64.getLsbD_allOnes, List.all_map, survives]
  grind [SieveSpec.getLsbD_wordAt_mk, List.all_eq_true]

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` that fills the piece: the first `k`
words are all ones. -/
def AndRowsFillInvariant {m : Nat} (k : Nat) (surv : Vector UInt64 m) : Prop :=
  ∀ y < k, surv[y]! = ~~~0

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over the moduli: after the moduli
`pref`, the words of the piece are their and (`Ratpoints.Sieve.andWords`). -/
def AndRowsInvariant {m : Nat} (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (surv : Vector UInt64 m) : Prop :=
  ∀ y < n * rbaPack, surv[y]! = andWords pref w0 y

/-- The invariant of the loops of `Ratpoints.Sieve.andRows` over the bit arrays for the modulus
`s` after the moduli `pref`: the words of the bit arrays below `c` are and-ed with the row of `s`
as well, the others not yet. -/
def AndRowsRowInvariant {m : Nat} (w0 : Int) (n : Nat) (pref : List SieveSpec) (s : SieveSpec)
    (c : Nat) (surv : Vector UInt64 m) : Prop :=
  ∀ y < n * rbaPack, surv[y]! =
    if y / rbaPack < c then andWords pref w0 y &&& s.wordAt w0 y else andWords pref w0 y

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over the whole periods for the modulus
`s`: the bit arrays before the first whole period and the periods `done` are done. -/
abbrev AndRowsPeriodInvariant {m : Nat} (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (s : SieveSpec) (done : List Nat) (surv : Vector UInt64 m) : Prop :=
  AndRowsRowInvariant w0 n pref s (((-w0) % (s.p : Int)).toNat + done.length * s.p) surv

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over one whole period for the modulus
`s`, after the periods `periods`: the bit arrays `done` of the current period are done too. -/
abbrev AndRowsPacketInvariant {m : Nat} (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (s : SieveSpec) (periods done : List Nat) (surv : Vector UInt64 m) : Prop :=
  AndRowsRowInvariant w0 n pref s
    (((-w0) % (s.p : Int)).toNat + periods.length * s.p + done.length) surv

/-- The invariant of the loop of `Ratpoints.Sieve.andRows` over the bit arrays after the last
whole period for the modulus `s`: the bit arrays before them and the bit arrays `done` are
done. -/
abbrev AndRowsTailInvariant {m : Nat} (w0 : Int) (n : Nat) (pref : List SieveSpec)
    (s : SieveSpec) (done : List Nat) (surv : Vector UInt64 m) : Prop :=
  AndRowsRowInvariant w0 n pref s (((-w0) % (s.p : Int)).toNat +
    (n - ((-w0) % (s.p : Int)).toNat) / s.p * s.p + done.length) surv

theorem andRowsFillInvariant_zero {m : Nat} (surv : Vector UInt64 m) :
    AndRowsFillInvariant 0 surv :=
  fun _ h ↦ absurd h (Nat.not_lt_zero _)

theorem AndRowsFillInvariant.append_set! {n : Nat} {done suff : List Nat} {cur : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)} (h : AndRowsFillInvariant done.length surv)
    (hl : ForIn.toList [0:n * rbaPack] = done ++ cur :: suff) :
    AndRowsFillInvariant (done ++ [cur]).length (surv.set! cur (~~~0)) := by
  have := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  intro y hy
  rw [List.length_append, List.length_singleton] at hy
  rw [Vector.getElem!_set! (by rw [Nat.succ_mul]; lia)]
  split
  · rfl
  · exact h y (by lia)

theorem andRowsInvariant_nil {m n : Nat} {w0 : Int} {surv : Vector UInt64 m}
    (h : AndRowsFillInvariant (ForIn.toList [0:n * rbaPack]).length surv) :
    AndRowsInvariant w0 n [] surv :=
  fun y hy ↦ h y (by simpa using hy)

theorem AndRowsInvariant.getElem!_eq {m n : Nat} {w0 : Int} {pref : List SieveSpec}
    {surv : Vector UInt64 m} (h : AndRowsInvariant w0 n pref surv) {y : Nat}
    (hy : y < n * rbaPack) : surv[y]! = andWords pref w0 y :=
  h y hy

theorem AndRowsInvariant.andRowsRowInvariant {m n : Nat} {w0 : Int} {pref : List SieveSpec}
    {s : SieveSpec} {surv : Vector UInt64 m} (h : AndRowsInvariant w0 n pref surv) :
    AndRowsRowInvariant w0 n pref s 0 surv := by
  intro y hy
  simp [h y hy]

theorem AndRowsRowInvariant.of_eq {m n : Nat} {w0 : Int} {pref : List SieveSpec} {s : SieveSpec}
    {c c' : Nat} {surv : Vector UInt64 m} (h : AndRowsRowInvariant w0 n pref s c surv)
    (hc : c = c') : AndRowsRowInvariant w0 n pref s c' surv :=
  hc ▸ h

theorem AndRowsRowInvariant.andRowsInvariant {m n : Nat} {w0 : Int} {pref : List SieveSpec}
    {s : SieveSpec} {c : Nat} {surv : Vector UInt64 m} (h : AndRowsRowInvariant w0 n pref s c surv)
    (hc : n ≤ c) : AndRowsInvariant w0 n (pref ++ [s]) surv := by
  intro y hy
  have : y / rbaPack < c := Nat.lt_of_lt_of_le ((Nat.div_lt_iff_lt_mul rbaPack_pos).mpr hy) hc
  simp [h y hy, this, andWords, List.foldl_append]

/-- One step of the loops of `Ratpoints.Sieve.andRows` for the modulus `s`: bit array `c` and-ed
with bit array `(w0 + c) mod p` of the row. -/
theorem AndRowsRowInvariant.add_one_andBitArray {n : Nat} {w0 : Int} {pref : List SieveSpec}
    {s : SieveSpec} {c x : Nat} {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsRowInvariant w0 n pref s c surv) (hx : ((w0 + c) % (s.p : Int)).toNat = x) :
    AndRowsRowInvariant w0 n pref s (c + 1) (andBitArray surv c s.row x) := by
  intro y hy
  rw [getElem!_andBitArray _ _ _ _ (by rw [Nat.succ_mul]; lia), h y hy]
  by_cases hyc : y / rbaPack = c
  · subst hyc
    simp only [SieveSpec.wordAt, hx, ite_true, Nat.lt_irrefl, ite_false, Nat.lt_succ_self]
  · simp only [hyc, ite_false]
    split <;> split <;> first | rfl | lia

theorem AndRowsRowInvariant.add_append_andBitArray {n m : Nat} {w0 : Int}
    {pref : List SieveSpec} {s : SieveSpec} {c0 x : Nat} {done suff : List Nat} {cur : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsRowInvariant w0 n pref s (c0 + done.length) surv)
    (hl : ForIn.toList [0:m] = done ++ cur :: suff)
    (hx : ((w0 + ((c0 + cur : Nat) : Int)) % (s.p : Int)).toNat = x) :
    AndRowsRowInvariant w0 n pref s (c0 + (done ++ [cur]).length)
      (andBitArray surv (c0 + cur) s.row x) := by
  have := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  simpa [this, Nat.add_assoc] using (h.of_eq (by rw [this])).add_one_andBitArray hx

/-- The loops before the first whole period: bit array `cur` is and-ed with bit array
`p - r + cur` of the row, for `r = (-w0) mod p`. -/
theorem AndRowsRowInvariant.append_andBitArray_sub {specs pref suff : List SieveSpec}
    {s : SieveSpec} {n m : Nat} {w0 : Int} {done suff' : List Nat} {cur : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsRowInvariant w0 n pref s done.length surv)
    (hl : ForIn.toList [0:m] = done ++ cur :: suff') (hm : m ≤ ((-w0) % (s.p : Int)).toNat)
    (hp : ∀ s ∈ specs, 0 < s.p) (hs : specs = pref ++ s :: suff) :
    AndRowsRowInvariant w0 n pref s (done ++ [cur]).length
      (andBitArray surv cur s.row (s.p - ((-w0) % (s.p : Int)).toNat + cur)) := by
  have hlen := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  simpa [hlen] using (h.of_eq hlen).add_one_andBitArray
    (Int.toNat_add_emod_of_lt (hp s (by simp [hs])) (by lia))

/-- The loop over one whole period: bit array `r + k p + i` is and-ed with bit array `i` of the
row, for `r = (-w0) mod p`. -/
theorem AndRowsRowInvariant.append_andBitArray_period {s : SieveSpec} {pref : List SieveSpec}
    {n mk : Nat} {w0 : Int} {periods suffK done suff : List Nat} {k i : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsPacketInvariant w0 n pref s periods done surv)
    (hlk : ForIn.toList [0:mk] = periods ++ k :: suffK)
    (hl : ForIn.toList [0:s.p] = done ++ i :: suff) :
    AndRowsPacketInvariant w0 n pref s periods (done ++ [i])
      (andBitArray surv (((-w0) % (s.p : Int)).toNat + k * s.p + i) s.row i) := by
  have hk := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hlk
  rw [AndRowsPacketInvariant, hk] at h ⊢
  exact h.add_append_andBitArray hl
    (Int.toNat_add_add_emod _ (Std.Legacy.Range.lt_of_toList_eq_append_cons hl))

/-- The loop after the last whole period: bit array `r + ⌊(n - r) / p⌋ p + i` is and-ed with bit
array `i` of the row, for `r = (-w0) mod p`. -/
theorem AndRowsRowInvariant.append_andBitArray_tail {specs pref suff : List SieveSpec}
    {s : SieveSpec} {n : Nat} {w0 : Int} {done suff' : List Nat} {i : Nat}
    {surv : Vector UInt64 ((n + 1) * rbaPack)}
    (h : AndRowsTailInvariant w0 n pref s done surv)
    (hl : ForIn.toList [0:(n - ((-w0) % (s.p : Int)).toNat) % s.p] = done ++ i :: suff')
    (hp : ∀ s ∈ specs, 0 < s.p) (hs : specs = pref ++ s :: suff) :
    AndRowsTailInvariant w0 n pref s (done ++ [i]) (andBitArray surv (((-w0) % (s.p : Int)).toNat +
      (n - ((-w0) % (s.p : Int)).toNat) / s.p * s.p + i) s.row i) :=
  h.add_append_andBitArray hl (Int.toNat_add_add_emod _
    (Nat.lt_of_lt_of_le (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)
      (Nat.le_of_lt (Nat.mod_lt _ (hp s (by simp [hs]))))))

/- The invariants are irreducible from here on, so that each alternative of the dispatch of the
verification conditions of `Ratpoints.Sieve.andRows` below fails fast on the conditions of the
other loops. -/
attribute [local irreducible] AndRowsFillInvariant AndRowsInvariant AndRowsRowInvariant

-- The contract of `Ratpoints.Sieve.andRows` for rows of positive moduli: each word of the piece
-- is the and of its row words.
private theorem andRows_spec_of_pos (specs : List SieveSpec) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ ∀ s ∈ specs, 0 < s.p ⦄ andRows specs w0 n surv
    ⦃ AndRowsInvariant w0 n specs ⦄ := by
  vcgen [andRows] invariants
  | inv1 => fun done _ ↦ AndRowsFillInvariant done.length
  | inv2 => fun pref _ ↦ AndRowsInvariant w0 n pref
  | inv3 pref s _ _ _ _ _ => fun done _ ↦ AndRowsRowInvariant w0 n pref s done.length
  | inv4 pref s _ _ _ _ _ => fun done _ ↦ AndRowsRowInvariant w0 n pref s done.length
  | inv5 pref s _ _ _ _ _ _ _ => fun done _ ↦ AndRowsPeriodInvariant w0 n pref s done
  | inv6 pref s _ _ _ _ _ _ _ _ _ => fun done _ ↦ AndRowsTailInvariant w0 n pref s done
  | inv7 pref s _ _ _ _ _ _ _ periods _ _ _ _ _ => fun done _ ↦
      AndRowsPacketInvariant w0 n pref s periods done
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
    | exact andRowsFillInvariant_zero _

/-- The tables and the denominator are quantified in the postcondition, since the program does not
mention them. -/
@[spec]
theorem andRows_spec (specs : List SieveSpec) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ True ⦄ andRows specs w0 n surv
    ⦃ fun surv' ↦ ∀ (entries : List Entry) (b : Nat), (∀ e ∈ entries, 0 < e.p) →
        specs = entries.map (fun e ↦ ⟨e.p, e.row b⟩) → ∀ y < n * rbaPack, ∀ t : Nat,
          (surv'[y]!).toBitVec.getLsbD t =
            (decide (t < 64) && survives entries b (rbaLength * w0 + 64 * y + t)) ⦄ :=
  ⟨fun _ entries b hp hspecs y hy t ↦ by
    subst hspecs
    rw [((andRows_spec_of_pos _ w0 n surv).le_wp (List.forall_mem_map.mpr hp)).getElem!_eq hy,
      getLsbD_andWords_map entries b hp]⟩

end Sieve

end Ratpoints

end
