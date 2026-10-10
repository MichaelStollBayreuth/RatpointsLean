/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Sieve
public import Std.WP

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Sieve
import Std.Tactic.Do

/-!
# The contracts of the bit arrays of words

The lemmas on the operations on the bit arrays of 64-bit words of the model, on its rows as words
and on the check of a numerator, and the contracts of its components on words, up to the sieve of
one denominator and the run over the denominators, as `@[spec]` theorems proved with `vcgen`, the
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
* `Ratpoints.Sieve.pointsOfDen_eq_flatMap_checkNum`: the points that the brute-force reference finds
  over a denominator are those of `Ratpoints.Sieve.checkNum` for its numerators, one after the
  other.
* `Ratpoints.Sieve.walkWord_spec`: the walk through the set bits of a word appends the points of the
  numerators of its set bits, in increasing order.
* `Ratpoints.Sieve.scanPiece_spec`: if the bits of a piece are a test `keep` of their numerators,
  the scan of the piece gives the points of its numerators that pass `keep`, in increasing order.
* `Ratpoints.Sieve.siftPiece_spec`: one piece with the rows of a denominator `b` gives the points of
  the survivors among its numerators that the masks at its two ends leave, in increasing order.
* `Ratpoints.Sieve.sift_spec`: the pieces of a denominator `b` give what the brute-force reference
  finds over `b` and the numerators `-H, …, H` that survive the tables;
  `Ratpoints.Sieve.toList_run_sift_eq_checkDen`: these are the points that the plain sieve of `b`
  gives.
* `Ratpoints.Sieve.sieveRun_spec`: the denominators `1, …, H` give the part of the brute-force
  reference with `z ≥ 1`, its numerators filtered by the survivor test;
  `Ratpoints.Sieve.toList_run_sieveRun` states this as an equation.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Sieve` does; the lemmas on words that
are not about the model are in `Ratpoints.Proof.Bits`. The proofs use only that
`Ratpoints.rbaPack` is positive, never its value. The plain equation
`Ratpoints.Sieve.toList_run_sieveRun` lets the files with Mathlib use the result of the run without
the program logic.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

/-! ### The width of the bit arrays -/

theorem rbaLength_eq : rbaLength = 64 * rbaPack := rfl

theorem rbaLength_pos : 0 < rbaLength := rbaLength_eq ▸ Nat.mul_pos (by decide) rbaPack_pos

theorem rbaLength_mul (j : Nat) : rbaLength * j = 64 * (rbaPack * j) := by
  rw [rbaLength_eq, Nat.mul_assoc]

theorem lt_rbaLength_mul_of_lt {n y t : Nat} (hy : y < n * rbaPack) (ht : t < 64) :
    64 * y + t < rbaLength * n := by
  rw [rbaLength_eq, Nat.mul_assoc, Nat.mul_comm rbaPack n]
  lia

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

/-! ### The check of a numerator and the set bits of a word -/

theorem pointsOfDen_eq_flatMap_checkNum (c : List Int) (d : Nat) (b : Int) (xs : List Int) :
    BruteForce.pointsOfDen c d b xs =
      xs.flatMap (checkNum (BruteForce.scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b) :=
  rfl

/-- The invariant of the loop of `Ratpoints.Sieve.walkWord` on the word `x0` after the points
`out0`: the word `x` is `x0` with its bits below some `k ≤ 64` cleared, and the points of the
numerators `a0 + t` of the set bits `t < k` of `x0` have been appended to `out0`. -/
def WalkWordInvariant (w : List Int) (f : Int) (b : Nat) (x0 : UInt64) (a0 : Int)
    (out0 : Array (Int × Int × Int)) (x : UInt64) (out : Array (Int × Int × Int)) : Prop :=
  ∃ k ≤ 64, (∀ t, x.toBitVec.getLsbD t = (x0.toBitVec.getLsbD t && decide (k ≤ t))) ∧
    out.toList = out0.toList ++
      (((List.range k).filter (x0.toBitVec.getLsbD ·)).map fun t : Nat ↦ a0 + t).flatMap
        (checkNum w f b)

/-- `Ratpoints.Sieve.WalkWordInvariant` as the invariant of the `while` loop of
`Ratpoints.Sieve.walkWord`, with the word `0` at the exit. -/
def WalkWordWhileInvariant (w : List Int) (f : Int) (b : Nat) (x0 : UInt64) (a0 : Int)
    (out0 : Array (Int × Int × Int)) :
    Std.WP.WhileInvariant (UInt64 × Array (Int × Int × Int)) Prop :=
  .mk fun exit s ↦ WalkWordInvariant w f b x0 a0 out0 s.1 s.2 ∧ (exit = true → s.1 = 0)

theorem walkWordInvariant_self (w : List Int) (f : Int) (b : Nat) (x0 : UInt64) (a0 : Int)
    (out0 : Array (Int × Int × Int)) : WalkWordInvariant w f b x0 a0 out0 x0 out0 :=
  ⟨0, Nat.zero_le _, fun _ ↦ by simp, by simp⟩

/-- The invariant of `Ratpoints.Sieve.walkWord` after one step: the points of the numerator of the
lowest set bit of `x` appended, and that bit cleared. -/
theorem WalkWordInvariant.and_sub_one {w : List Int} {f : Int} {b : Nat} {x0 x : UInt64}
    {a0 : Int} {out0 out : Array (Int × Int × Int)}
    (h : WalkWordInvariant w f b x0 a0 out0 x out) (hx : x ≠ 0) :
    WalkWordInvariant w f b x0 a0 out0 (x &&& (x - 1))
      (out ++ ⟨checkNum w f b (a0 + x.toBitVec.ctz.toNat)⟩) := by
  obtain ⟨k, hk, hbits, hout⟩ := h
  have hc := UInt64.getLsbD_ctz hx
  rw [hbits, Bool.and_eq_true, decide_eq_true_iff] at hc
  refine ⟨x.toBitVec.ctz.toNat + 1, UInt64.toNat_ctz_lt hx, fun t ↦ ?_, ?_⟩
  · grind [UInt64.getLsbD_and_sub_one, BitVec.getLsbD_false_of_lt_ctz]
  · simp [hout, List.filter_range_succ_eq_append hc.2 hc.1 fun _ _ _ ↦ by
      grind [BitVec.getLsbD_false_of_lt_ctz]]

theorem WalkWordInvariant.toList_eq {w : List Int} {f : Int} {b : Nat} {x0 : UInt64} {a0 : Int}
    {out0 out : Array (Int × Int × Int)} (h : WalkWordInvariant w f b x0 a0 out0 0 out) :
    out.toList = out0.toList ++
      (((List.range 64).filter (x0.toBitVec.getLsbD ·)).map fun t : Nat ↦ a0 + t).flatMap
        (checkNum w f b) := by
  obtain ⟨k, hk, hbits, hout⟩ := h
  rw [hout, List.filter_range_eq_of_le hk fun j hkj _ ↦ by simpa [hkj] using (hbits j).symm]

/- The invariant of the walk is irreducible from here on: the verification conditions of
`Ratpoints.Sieve.walkWord` are closed by its lemmas, never by unfolding it. -/
attribute [local irreducible] WalkWordInvariant

/-- The loop ends, since clearing the lowest set bit makes a word other than `0` smaller. -/
@[spec]
theorem walkWord_spec (w : List Int) (f : Int) (b : Nat) (x : UInt64) (a0 : Int)
    (out : Array (Int × Int × Int)) :
    ⦃ True ⦄ walkWord w f b x a0 out
    ⦃ fun out' ↦ out'.toList = out.toList ++
        (((List.range 64).filter (x.toBitVec.getLsbD ·)).map fun t : Nat ↦ a0 + t).flatMap
          (checkNum w f b) ⦄ := by
  vcgen [walkWord] invariants
  · WalkWordWhileInvariant w f b x a0 out
  · Std.WP.Variant.ofMeasure fun s : UInt64 × Array (Int × Int × Int) ↦ s.1.toNat
  all_goals simp [WalkWordWhileInvariant] at *
  all_goals grind [walkWordInvariant_self, WalkWordInvariant.and_sub_one,
    WalkWordInvariant.toList_eq, UInt64.toNat_and_sub_one_lt]

/-! ### The scan and the extraction -/

/-- The invariant of the loop of `Ratpoints.Sieve.scanPiece` that writes the sentinel into bit
array `n` of `surv`: the words of the piece are those of `surv`, and the first `k` words of bit
array `n` are all ones. -/
def ScanPieceSentinelInvariant {m : Nat} (n : Nat) (surv : Vector UInt64 m) (k : Nat)
    (sv : Vector UInt64 m) : Prop :=
  (∀ y < n * rbaPack, sv[y]! = surv[y]!) ∧ ∀ κ < k, sv[rbaPack * n + κ]! = ~~~0

/-- The invariant of the scan of `Ratpoints.Sieve.scanPiece` at bit array `pos` of the words `sv`,
for a piece of `n` bit arrays from the word number `w0` on: `pos ≤ n`, and `out` holds the points
(`Ratpoints.Sieve.checkNum`) of the numerators `rbaLength w0 + 64 y + t` of the set bits `t` of the
words `y < rbaPack pos`, in increasing order. -/
def ScanPieceInvariant {m : Nat} (sv : Vector UInt64 m) (w : List Int) (f : Int) (b : Nat)
    (w0 : Int) (n pos : Nat) (out : Array (Int × Int × Int)) : Prop :=
  pos ≤ n ∧ out.toList = ((List.range (rbaPack * pos)).flatMap fun y : Nat ↦
    ((List.range 64).filter ((sv[y]!).toBitVec.getLsbD ·)).map fun t : Nat ↦
      rbaLength * w0 + 64 * y + t).flatMap (checkNum w f b)

/-- `Ratpoints.Sieve.ScanPieceInvariant` as the invariant of the scan of
`Ratpoints.Sieve.scanPiece`, with all `n` bit arrays done at the exit. -/
def ScanPieceWhileInvariant {m : Nat} (sv : Vector UInt64 m) (w : List Int) (f : Int) (b : Nat)
    (w0 : Int) (n : Nat) : Std.WP.WhileInvariant (Nat × Array (Int × Int × Int)) Prop :=
  .mk fun exit s ↦ ScanPieceInvariant sv w f b w0 n s.1 s.2 ∧ (exit = true → s.1 = n)

/-- The invariant of the loop of `Ratpoints.Sieve.scanPiece` that steps over the bit arrays that are
zero, from bit array `pos0` on, with the points `out` of the bit arrays before `pos0`: the position
is at least `pos0`, and `Ratpoints.Sieve.ScanPieceInvariant` holds there with `out`, since a bit
array that is zero has no set bits. -/
def ScanPieceZeroInvariant {m : Nat} (sv : Vector UInt64 m) (w : List Int) (f : Int) (b : Nat)
    (w0 : Int) (n pos0 : Nat) (out : Array (Int × Int × Int)) : Std.WP.WhileInvariant Nat Prop :=
  .mk fun _ pos ↦ pos0 ≤ pos ∧ ScanPieceInvariant sv w f b w0 n pos out

/-- The invariant of the loop of `Ratpoints.Sieve.scanPiece` over the words of bit array `pos` of
`sv`, after its first `k` words, with the points `out0` of the bit arrays before it: the numerator
`(w0 + pos) rbaLength + 64 k` of bit `0` of the next word, and the points of the numerators
`(w0 + pos) rbaLength + 64 κ + t` of the set bits `t` of the words `κ < k`, in increasing order,
after `out0`. -/
def ScanPieceExtractInvariant {m : Nat} (sv : Vector UInt64 m) (w : List Int) (f : Int) (b : Nat)
    (w0 : Int) (pos : Nat) (out0 : Array (Int × Int × Int)) (k : Nat)
    (s : Array (Int × Int × Int) × Int) : Prop :=
  s.2 = (w0 + pos) * rbaLength + 64 * k ∧ s.1.toList = out0.toList ++
    ((List.range k).flatMap fun κ ↦
      ((List.range 64).filter ((sv[rbaPack * pos + κ]!).toBitVec.getLsbD ·)).map fun t : Nat ↦
        (w0 + pos) * rbaLength + 64 * κ + t).flatMap (checkNum w f b)

theorem scanPieceSentinelInvariant_zero {m : Nat} (n : Nat) (surv : Vector UInt64 m) :
    ScanPieceSentinelInvariant n surv 0 surv :=
  ⟨fun _ _ ↦ rfl, fun _ h ↦ absurd h (Nat.not_lt_zero _)⟩

theorem ScanPieceSentinelInvariant.append_set! {n : Nat}
    {surv sv : Vector UInt64 ((n + 1) * rbaPack)} {done suff : List Nat} {cur : Nat}
    (h : ScanPieceSentinelInvariant n surv done.length sv)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff) :
    ScanPieceSentinelInvariant n surv (done ++ [cur]).length
      (sv.set! (rbaPack * n + cur) (~~~0)) := by
  have := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have : rbaPack * n = n * rbaPack := Nat.mul_comm _ _
  refine ⟨fun y hy ↦ ?_, fun κ hκ ↦ ?_⟩
  · rw [Vector.getElem!_set! (by rw [Nat.succ_mul]; lia), h.1 y hy]
    grind
  · rw [List.length_append, List.length_singleton] at hκ
    rw [Vector.getElem!_set! (by rw [Nat.succ_mul]; lia)]
    grind [h.2]

/-- A bit array that is zero is not the sentinel, whose words are all ones. -/
theorem ScanPieceSentinelInvariant.ne_of_isZeroAt {m n : Nat} {surv sv : Vector UInt64 m}
    (h : ScanPieceSentinelInvariant n surv rbaPack sv) {pos : Nat} (hz : isZeroAt sv pos = true) :
    pos ≠ n := by
  rintro rfl
  have h0 := (isZeroAt_eq_true_iff sv pos).mp hz 0 rbaPack_pos
  rw [h.2 0 rbaPack_pos] at h0
  exact absurd h0 (by decide)

theorem scanPieceInvariant_zero {m : Nat} (sv : Vector UInt64 m) (w : List Int) (f : Int)
    (b : Nat) (w0 : Int) (n : Nat) : ScanPieceInvariant sv w f b w0 n 0 #[] := by
  simp [ScanPieceInvariant]

theorem ScanPieceInvariant.le {m : Nat} {sv : Vector UInt64 m} {w : List Int} {f : Int} {b : Nat}
    {w0 : Int} {n pos : Nat} {out : Array (Int × Int × Int)}
    (h : ScanPieceInvariant sv w f b w0 n pos out) : pos ≤ n :=
  h.1

/-- Bit array `pos` adds the points of the numerators of the set bits of its words. -/
theorem ScanPieceInvariant.add_one {m : Nat} {sv : Vector UInt64 m} {w : List Int} {f : Int}
    {b : Nat} {w0 : Int} {n pos : Nat} {out out' : Array (Int × Int × Int)}
    (h : ScanPieceInvariant sv w f b w0 n pos out) (hlt : pos < n)
    (hout : out'.toList = out.toList ++ ((List.range rbaPack).flatMap fun κ ↦
      ((List.range 64).filter ((sv[rbaPack * pos + κ]!).toBitVec.getLsbD ·)).map fun t : Nat ↦
        rbaLength * w0 + 64 * (rbaPack * pos + κ : Nat) + t).flatMap (checkNum w f b)) :
    ScanPieceInvariant sv w f b w0 n (pos + 1) out' := by
  refine ⟨hlt, ?_⟩
  rw [hout, h.2, Nat.mul_succ, List.range_add, List.flatMap_append, List.flatMap_map,
    List.flatMap_append]

theorem ScanPieceInvariant.add_one_of_isZeroAt {m : Nat} {sv : Vector UInt64 m} {w : List Int}
    {f : Int} {b : Nat} {w0 : Int} {n pos : Nat} {out : Array (Int × Int × Int)}
    (h : ScanPieceInvariant sv w f b w0 n pos out) (hlt : pos < n) (hz : isZeroAt sv pos = true) :
    ScanPieceInvariant sv w f b w0 n (pos + 1) out := by
  refine h.add_one hlt ?_
  rw [(List.flatMap_eq_nil_iff (l := List.range rbaPack)).mpr fun κ hκ ↦ ?_]
  · simp
  simp [(isZeroAt_eq_true_iff sv pos).mp hz κ (List.mem_range.mp hκ)]

theorem scanPieceExtractInvariant_zero {m : Nat} (sv : Vector UInt64 m) (w : List Int) (f : Int)
    (b : Nat) (w0 : Int) (pos : Nat) (out : Array (Int × Int × Int)) :
    ScanPieceExtractInvariant sv w f b w0 pos out 0 (out, (w0 + pos) * rbaLength) := by
  simp [ScanPieceExtractInvariant]

theorem ScanPieceExtractInvariant.append_singleton {m : Nat} {sv : Vector UInt64 m}
    {w : List Int} {f : Int} {b : Nat} {w0 : Int} {pos : Nat} {out0 r : Array (Int × Int × Int)}
    {done suff : List Nat} {cur : Nat} {s : Array (Int × Int × Int) × Int}
    (h : ScanPieceExtractInvariant sv w f b w0 pos out0 done.length s)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff)
    (hr : r.toList = s.1.toList ++ (((List.range 64).filter
      ((sv[rbaPack * pos + cur]!).toBitVec.getLsbD ·)).map fun t : Nat ↦ s.2 + t).flatMap
        (checkNum w f b)) :
    ScanPieceExtractInvariant sv w f b w0 pos out0 (done ++ [cur]).length (r, s.2 + 64) := by
  have hκ := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨by simp only [h.1, List.length_append, List.length_singleton]; push_cast; lia, ?_⟩
  rw [hr, h.2, h.1, List.length_append, List.length_singleton, hκ, List.range_succ (n := cur),
    List.flatMap_append, List.flatMap_singleton, List.flatMap_append, List.append_assoc]

/-- The words of bit array `pos`, all of them walked through, add the points of their numerators. -/
theorem ScanPieceExtractInvariant.scanPieceInvariant_add_one {m : Nat} {sv : Vector UInt64 m}
    {w : List Int} {f : Int} {b : Nat} {w0 : Int} {n pos : Nat} {out a : Array (Int × Int × Int)}
    {a0 : Int} (hext : ScanPieceExtractInvariant sv w f b w0 pos out rbaPack (a, a0))
    (h : ScanPieceInvariant sv w f b w0 n pos out) (hlt : pos < n) :
    ScanPieceInvariant sv w f b w0 n (pos + 1) a := by
  refine h.add_one hlt ?_
  have key (κ t : Nat) : (w0 + pos) * (rbaLength : Int) + 64 * κ + t =
      rbaLength * w0 + 64 * ((rbaPack * pos + κ : Nat) : Int) + t := by
    push_cast [rbaLength_eq]
    grind
  simpa only [key] using hext.2

/-- At the end of the scan, `out` holds the points of the set bits of the words of the piece, which
are those of `surv`, since the sentinel was written past them. -/
theorem ScanPieceInvariant.toList_eq {m n : Nat} {surv sv : Vector UInt64 m} {w : List Int}
    {f : Int} {b : Nat} {w0 : Int} {out : Array (Int × Int × Int)}
    (h : ScanPieceInvariant sv w f b w0 n n out)
    (hs : ScanPieceSentinelInvariant n surv rbaPack sv) :
    out.toList = ((List.range (n * rbaPack)).flatMap fun y : Nat ↦
      ((List.range 64).filter ((surv[y]!).toBitVec.getLsbD ·)).map fun t : Nat ↦
        rbaLength * w0 + 64 * y + t).flatMap (checkNum w f b) := by
  rw [h.2, Nat.mul_comm rbaPack n]
  exact congrArg (List.flatMap _) <| congrArg List.flatten <| List.map_congr_left fun y hy ↦ by
    rw [hs.1 y (List.mem_range.mp hy)]

/- The invariants are irreducible from here on: the verification conditions of
`Ratpoints.Sieve.scanPiece` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] ScanPieceSentinelInvariant ScanPieceInvariant
  ScanPieceExtractInvariant

-- The contract of `Ratpoints.Sieve.scanPiece` in terms of the set bits of the words of the piece.
private theorem scanPiece_spec_getLsbD (w : List Int) (f : Int) (b : Nat) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ True ⦄ scanPiece w f b w0 n surv
    ⦃ fun out ↦ out.toList = ((List.range (n * rbaPack)).flatMap fun y : Nat ↦
        ((List.range 64).filter ((surv[y]!).toBitVec.getLsbD ·)).map fun t : Nat ↦
          rbaLength * w0 + 64 * y + t).flatMap (checkNum w f b) ⦄ := by
  vcgen [scanPiece] invariants
  | inv1 => fun done _ ↦ ScanPieceSentinelInvariant n surv done.length
  | inv2 sv _ => ScanPieceWhileInvariant sv w f b w0 n
  | inv3 => Std.WP.Variant.ofMeasure fun s : Nat × Array (Int × Int × Int) ↦ n - s.1
  | inv4 sv _ pos0 out _ _ => ScanPieceZeroInvariant sv w f b w0 n pos0 out
  | inv5 => Std.WP.Variant.ofMeasure fun s : Nat ↦ n - s
  | inv6 sv _ _ out _ _ pos _ _ _ => fun done _ ↦
      ScanPieceExtractInvariant sv w f b w0 pos out done.length
  -- the two loops over the words of a bit array first: `simp` would rewrite their ranges
  all_goals first
    | exact scanPieceSentinelInvariant_zero n surv
    | exact ScanPieceSentinelInvariant.append_set! ‹_› ‹_›
    | exact scanPieceExtractInvariant_zero ..
    | exact ScanPieceExtractInvariant.append_singleton ‹_› ‹_› ‹_›
    | simp [ScanPieceWhileInvariant, ScanPieceZeroInvariant] at *
  all_goals grind [scanPieceInvariant_zero, → ScanPieceInvariant.le, ScanPieceInvariant.toList_eq,
    ScanPieceInvariant.add_one_of_isZeroAt, → ScanPieceExtractInvariant.scanPieceInvariant_add_one,
    → ScanPieceSentinelInvariant.ne_of_isZeroAt]

/-- The loop over the zero bit arrays ends at the sentinel at the latest, so that both loops of the
scan end by the measure `n - pos`; the test `keep` is quantified in the postcondition, since the
program does not mention it. -/
@[spec]
theorem scanPiece_spec (w : List Int) (f : Int) (b : Nat) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ True ⦄ scanPiece w f b w0 n surv
    ⦃ fun out ↦ ∀ keep : Int → Bool, (∀ y < n * rbaPack, ∀ t : Nat,
        (surv[y]!).toBitVec.getLsbD t = (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t))) →
      out.toList = (((List.range (n * rbaLength)).map fun k : Nat ↦
        rbaLength * w0 + k).filter keep).flatMap (checkNum w f b) ⦄ :=
  ⟨fun _ keep hkeep ↦ by
    rw [(scanPiece_spec_getLsbD w f b w0 n surv).le_wp trivial,
      UInt64.flatMap_range_map_filter_getLsbD hkeep, rbaLength_eq, Nat.mul_left_comm]⟩

/-! ### The masks and one piece -/

theorem getLsbD_clearHighBits_sub_one {m n s : Nat} (v : Vector UInt64 m) (hs : s < rbaLength)
    {y : Nat} (hy : y < m) (hyn : y < n * rbaPack) (t : Nat) :
    ((clearHighBits v (n - 1) s)[y]!).toBitVec.getLsbD t =
      ((v[y]!).toBitVec.getLsbD t && decide (64 * y + t + s < rbaLength * n)) := by
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hyn)
  rw [getLsbD_clearHighBits v (n - 1) hs hy (by rw [hn, Nat.mul_comm]; exact hyn), hn]

/-- The words `v` of a piece of `n` bit arrays are the words `surv` with the masks at its two ends
applied, as far as the bits `t < 64` of the words `y < n rbaPack` go: bit `t` of word `y` is set in
`v` exactly when it is set in `surv`, `maskLow ≤ 64 y + t` and `64 y + t + maskHigh < rbaLength n`,
for the number `rbaPack` of words of a bit array (`Ratpoints.rbaPack`). -/
def IsMasked {m : Nat} (n maskLow maskHigh : Nat) (surv v : Vector UInt64 m) : Prop :=
  ∀ y < n * rbaPack, ∀ t < 64, (v[y]!).toBitVec.getLsbD t =
    ((surv[y]!).toBitVec.getLsbD t && decide (maskLow ≤ 64 * y + t) &&
      decide (64 * y + t + maskHigh < rbaLength * n))

theorem isMasked_clearHighBits_clearLowBits {n maskHigh : Nat}
    (v : Vector UInt64 ((n + 1) * rbaPack)) (maskLow : Nat) (hH : maskHigh < rbaLength) :
    IsMasked n maskLow maskHigh v (clearHighBits (clearLowBits v maskLow) (n - 1) maskHigh) :=
  fun y hy t _ ↦ by
    have := Nat.lt_of_lt_of_le hy (Nat.mul_le_mul_right rbaPack (Nat.le_succ n))
    rw [getLsbD_clearHighBits_sub_one _ hH this hy, getLsbD_clearLowBits _ _ this]

theorem isMasked_clearLowBits {n maskHigh : Nat} (v : Vector UInt64 ((n + 1) * rbaPack))
    (maskLow : Nat) (hH : maskHigh = 0) : IsMasked n maskLow maskHigh v (clearLowBits v maskLow) :=
  fun y hy t ht ↦ by
    simp [getLsbD_clearLowBits _ _ (Nat.lt_of_lt_of_le hy (Nat.mul_le_mul_right rbaPack
      (Nat.le_succ n))), hH, lt_rbaLength_mul_of_lt hy ht]

theorem isMasked_clearHighBits {n maskLow maskHigh : Nat} (v : Vector UInt64 ((n + 1) * rbaPack))
    (hL : maskLow = 0) (hH : maskHigh < rbaLength) :
    IsMasked n maskLow maskHigh v (clearHighBits v (n - 1) maskHigh) := fun y hy t _ ↦ by
  simp [getLsbD_clearHighBits_sub_one _ hH (Nat.lt_of_lt_of_le hy (Nat.mul_le_mul_right rbaPack
    (Nat.le_succ n))) hy, hL]

theorem isMasked_self {m maskLow maskHigh : Nat} (n : Nat) (v : Vector UInt64 m)
    (hL : maskLow = 0) (hH : maskHigh = 0) : IsMasked n maskLow maskHigh v v := fun y hy t ht ↦ by
  simp [hL, hH, lt_rbaLength_mul_of_lt hy ht]

/-- The points of a piece of `n` bit arrays from the word number `w0` on, given the contracts of its
first stage on the words `surv` (`hand`, as `Ratpoints.Sieve.andRows_spec` states it) and of its
scan on the words `v` (`hout`, as `Ratpoints.Sieve.scanPiece_spec` states it), when `v` is `surv`
with the masks applied: the points of the survivors among the numerators from
`rbaLength w0 + maskLow` to `rbaLength (w0 + n) - 1 - maskHigh`. -/
theorem IsMasked.toList_eq {n : Nat} {w : List Int} {f : Int} {b : Nat} {specs : List SieveSpec}
    {w0 : Int} {maskLow maskHigh : Nat} {surv v : Vector UInt64 ((n + 1) * rbaPack)}
    {out : Array (Int × Int × Int)}
    (hand : ∀ (entries : List Entry) (b : Nat), (∀ e ∈ entries, 0 < e.p) →
      specs = entries.map (fun e ↦ ⟨e.p, e.row b⟩) → ∀ y < n * rbaPack, ∀ t : Nat,
        (surv[y]!).toBitVec.getLsbD t =
          (decide (t < 64) && survives entries b (rbaLength * w0 + 64 * y + t)))
    (h : IsMasked n maskLow maskHigh surv v)
    (hout : ∀ keep : Int → Bool, (∀ y < n * rbaPack, ∀ t : Nat, (v[y]!).toBitVec.getLsbD t =
        (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t))) →
      out.toList = (((List.range (n * rbaLength)).map fun k : Nat ↦
        rbaLength * w0 + k).filter keep).flatMap (checkNum w f b))
    {entries : List Entry} (hp : ∀ e ∈ entries, 0 < e.p)
    (hspecs : specs = entries.map (fun e ↦ ⟨e.p, e.row b⟩)) :
    out.toList = (((List.range (n * rbaLength - maskLow - maskHigh)).map fun k : Nat ↦
      rbaLength * w0 + maskLow + k).filter (survives entries b)).flatMap (checkNum w f b) := by
  rw [hout (fun a ↦ survives entries b a && decide (rbaLength * w0 + maskLow ≤ a ∧
    a + maskHigh < rbaLength * w0 + (n * rbaLength : Nat))) fun y hy t ↦ ?_, ← List.filter_filter,
    List.filter_map_range_eq_map_range]
  by_cases ht : t < 64
  · rw [h y hy t ht, hand entries b hp hspecs y hy t]
    grind
  · simp [ht, BitVec.getLsbD_of_ge _ t (Nat.le_of_not_lt ht)]

/-- The tables are quantified in the postcondition, since the program does not mention them; the
bound on `maskHigh` is that of the high mask (`Ratpoints.Sieve.getLsbD_clearHighBits`), and the
low mask needs none. -/
@[spec]
theorem siftPiece_spec (w : List Int) (f : Int) (b : Nat) (specs : List SieveSpec) (w0 : Int)
    (n maskLow maskHigh : Nat) :
    ⦃ maskHigh < rbaLength ⦄ siftPiece w f b specs w0 n maskLow maskHigh
    ⦃ fun out ↦ ∀ entries : List Entry, (∀ e ∈ entries, 0 < e.p) →
        specs = entries.map (fun e ↦ ⟨e.p, e.row b⟩) →
        out.toList = (((List.range (n * rbaLength - maskLow - maskHigh)).map fun k : Nat ↦
          rbaLength * w0 + maskLow + k).filter (survives entries b)).flatMap
            (checkNum w f b) ⦄ := by
  vcgen [siftPiece]
  all_goals first
    | exact IsMasked.toList_eq ‹_› (isMasked_clearHighBits_clearLowBits _ _ ‹_›) ‹_› ‹_› ‹_›
    | exact IsMasked.toList_eq ‹_› (isMasked_clearLowBits _ _ (Decidable.of_not_not ‹_›)) ‹_› ‹_›
        ‹_›
    | exact IsMasked.toList_eq ‹_› (isMasked_clearHighBits _ (Decidable.of_not_not ‹_›) ‹_›) ‹_›
        ‹_› ‹_›
    | exact IsMasked.toList_eq ‹_› (isMasked_self _ _ (Decidable.of_not_not ‹_›)
        (Decidable.of_not_not ‹_›)) ‹_› ‹_› ‹_›

/-! ### One denominator -/

open BruteForce

-- The low mask of `Ratpoints.Sieve.sift` on the piece from the word number `w0` on: the number of
-- its bits below `-H`, `0` from the second piece on.
private theorem ite_eq_toNat_neg_sub {H : Nat} {w0 : Int} (hw0 : -(H : Int) / rbaLength ≤ w0) :
    (if w0 = -(H : Int) / rbaLength then
      (-(H : Int) - rbaLength * (-(H : Int) / rbaLength)).toNat else 0) =
        (-(H : Int) - rbaLength * w0).toNat := by
  have hR : (0 : Int) < rbaLength := by have := rbaLength_pos; lia
  split
  · subst_vars
    rfl
  · have := Int.lt_mul_ediv_self_add (x := -(H : Int)) hR
    have := Int.mul_le_mul_of_nonneg_left (show -(H : Int) / rbaLength + 1 ≤ w0 by lia)
      (Int.le_of_lt hR)
    rw [Int.mul_add, Int.mul_one] at this
    lia

-- The high mask of `Ratpoints.Sieve.sift` on the last piece: the number of its bits above `H`.
private theorem sub_toNat_emod_eq_toNat_mul_sub (H : Nat) :
    rbaLength - 1 - ((H : Int) % rbaLength).toNat =
      (rbaLength * ((H : Int) / rbaLength + 1) - 1 - H).toNat := by
  have := Int.emod_def (H : Int) rbaLength
  have := Int.emod_lt_of_pos (H : Int) (b := rbaLength) (by have := rbaLength_pos; lia)
  have := Int.emod_nonneg (H : Int) (b := rbaLength) (by have := rbaLength_pos; lia)
  rw [Int.mul_add, Int.mul_one]
  lia

-- The high mask of `Ratpoints.Sieve.sift` on the piece that ends at the word number `w1`: the
-- number of its bits above `H`, `0` for every piece but the last.
private theorem ite_eq_toNat_mul_sub {H : Nat} {w1 : Int} (hw1 : w1 ≤ (H : Int) / rbaLength + 1) :
    (if w1 = (H : Int) / rbaLength + 1 then rbaLength - 1 - ((H : Int) % rbaLength).toNat
      else 0) = (rbaLength * w1 - 1 - H).toNat := by
  split
  · subst_vars
    exact sub_toNat_emod_eq_toNat_mul_sub H
  · have hR : (0 : Int) < rbaLength := by have := rbaLength_pos; lia
    have := Int.mul_ediv_self_le (x := (H : Int)) (Int.ne_of_gt hR)
    have := Int.mul_le_mul_of_nonneg_left (show w1 ≤ (H : Int) / rbaLength by lia)
      (Int.le_of_lt hR)
    lia

/-- The invariant of the loop of `Ratpoints.Sieve.sift` over the pieces, for the height bound `H`,
a test `keep` of the numerators and their points `g`, at the exit of the loop or not: the bit arrays
from that of `-H` up to the word number `w0` are done, and their numerators that lie in `-H, …, H`
and pass `keep` have given their points. -/
structure SiftInvariant (g : Int → List (Int × Int × Int)) (keep : Int → Bool) (H : Nat)
    (exit : Bool) (range : Nat) (w0 w1 : Int) (out : Array (Int × Int × Int)) : Prop where
  /-- The next piece starts at the word number `w0`, not below that of `-H`. -/
  le_w0 : -(H : Int) / rbaLength ≤ w0
  /-- The word number `w0` is at most one past that of `H`. -/
  w0_le : w0 ≤ (H : Int) / rbaLength + 1
  /-- At the exit, `w0` is one past the word number of `H`. -/
  eq_of_exit : exit = true → w0 = (H : Int) / rbaLength + 1
  /-- The next piece ends at the word number `w1`, `range` bit arrays after `w0`. -/
  w1_eq : w1 = w0 + range
  /-- A piece has at least one bit array. -/
  one_le_range : 1 ≤ range
  /-- The points found are those of the numerators of the bit arrays from that of `-H` up to `w0`
  that lie in `-H, …, H` and pass `keep`, in increasing order. -/
  toList_eq : out.toList = ((((List.range ((w0 - -(H : Int) / rbaLength).toNat * rbaLength)).map
    fun k : Nat ↦ rbaLength * (-(H : Int) / rbaLength) + k).filter
      fun a ↦ decide (-(H : Int) ≤ a ∧ a ≤ H)).filter keep).flatMap g

/-- `Ratpoints.Sieve.SiftInvariant` as the invariant of the `while` loop of
`Ratpoints.Sieve.sift`. -/
def SiftWhileInvariant (g : Int → List (Int × Int × Int)) (keep : Int → Bool) (H : Nat) :
    Std.WP.WhileInvariant (Nat × Int × Int × Array (Int × Int × Int)) Prop :=
  .mk fun exit s ↦ SiftInvariant g keep H exit s.1 s.2.1 s.2.2.1 s.2.2.2

theorem siftInvariant_empty (g : Int → List (Int × Int × Int)) (keep : Int → Bool) (H : Nat)
    {A : Nat} (hA : 1 ≤ A) :
    SiftInvariant g keep H false A (-(H : Int) / rbaLength) (-(H : Int) / rbaLength + A) #[] := by
  have hR : (0 : Int) < rbaLength := by have := rbaLength_pos; lia
  have := Int.ediv_le_ediv hR (show -(H : Int) ≤ H by lia)
  exact ⟨Int.le_refl _, by lia, nofun, rfl, hA, by simp⟩

/-- A piece of `r ≥ 1` bit arrays from the word number `w0` on, which ends at
`w1' ≤ H / rbaLength + 1`, with the low mask of `Ratpoints.Sieve.sift` and a high mask `mH`, the
number of its bits above `H`. -/
theorem SiftInvariant.append {g : Int → List (Int × Int × Int)} {keep : Int → Bool}
    {H range r mH : Nat} {w0 w1 w1' : Int} {out pts : Array (Int × Int × Int)}
    (h : SiftInvariant g keep H false range w0 w1 out) (hr : w1' = w0 + r) (hr1 : 1 ≤ r)
    (hw1' : w1' ≤ (H : Int) / rbaLength + 1) (hmH : mH = (rbaLength * w1' - 1 - H).toNat)
    (hpts : pts.toList = (((List.range (r * rbaLength - (if w0 = -(H : Int) / rbaLength then
      (-(H : Int) - rbaLength * (-(H : Int) / rbaLength)).toNat else 0) - mH)).map fun k : Nat ↦
        rbaLength * w0 + ((if w0 = -(H : Int) / rbaLength then
          (-(H : Int) - rbaLength * (-(H : Int) / rbaLength)).toNat else 0 : Nat) : Int) +
            k).filter keep).flatMap g) :
    SiftInvariant g keep H false r w1' (w1' + r) (out ++ pts) := by
  refine ⟨by have := h.le_w0; lia, hw1', nofun, rfl, hr1, ?_⟩
  have hm : (rbaLength : Int) * w1' - 1 - H =
      rbaLength * w0 + ((r * rbaLength : Nat) : Int) - 1 - H := by
    rw [hr, Int.mul_add, Int.natCast_mul, Int.mul_comm (r : Int)]
  rw [ite_eq_toNat_neg_sub h.le_w0, hmH, hm, ← List.filter_map_range_eq_map_range'] at hpts
  have hw : (((w0 - -(H : Int) / rbaLength).toNat : Nat) : Int) = w0 - -(H : Int) / rbaLength :=
    Int.toNat_of_nonneg (by have := h.le_w0; lia)
  have hl : (w1' - -(H : Int) / rbaLength).toNat = (w0 - -(H : Int) / rbaLength).toNat + r := by
    have := h.le_w0
    lia
  have hmap : (List.range (r * rbaLength)).map ((fun k : Nat ↦
      rbaLength * (-(H : Int) / rbaLength) + k) ∘
        fun x ↦ (w0 - -(H : Int) / rbaLength).toNat * rbaLength + x) =
      (List.range (r * rbaLength)).map fun k : Nat ↦ rbaLength * w0 + k :=
    List.map_congr_left fun k _ ↦ by grind
  rw [Array.toList_append, h.toList_eq, hpts, ← List.flatMap_append, ← List.filter_append,
    ← List.filter_append, hl, Nat.add_mul, List.range_add, List.map_append, List.map_map, hmap]

/-- The pieces advance: the measure `H / rbaLength + 1 - w0` of the loop of `Ratpoints.Sieve.sift`
decreases from one piece to the next. -/
theorem SiftInvariant.toNat_sub_lt {g : Int → List (Int × Int × Int)} {keep : Int → Bool}
    {H range : Nat} {w0 w1 : Int} {out : Array (Int × Int × Int)}
    (h : SiftInvariant g keep H false range w0 w1 out) (hw0 : w0 < (H : Int) / rbaLength + 1) :
    ((H : Int) / rbaLength + 1 - w1).toNat < ((H : Int) / rbaLength + 1 - w0).toNat := by
  have := h.w1_eq
  have := h.one_le_range
  lia

/-- The loop ends at the word number one past that of `H`. -/
theorem SiftInvariant.exit_of_not_lt {g : Int → List (Int × Int × Int)} {keep : Int → Bool}
    {H range : Nat} {w0 w1 : Int} {out : Array (Int × Int × Int)}
    (h : SiftInvariant g keep H false range w0 w1 out) (hw0 : ¬w0 < (H : Int) / rbaLength + 1) :
    SiftInvariant g keep H true range w0 w1 out :=
  ⟨h.le_w0, h.w0_le, fun _ ↦ Int.le_antisymm h.w0_le (Int.not_lt.mp hw0), h.w1_eq,
    h.one_le_range, h.toList_eq⟩

theorem _root_.Ratpoints.BruteForce.filter_map_range_eq_numerators {s : Int} {m H : Nat}
    (h1 : s ≤ -(H : Int)) (h2 : (H : Int) < s + m) :
    ((List.range m).map fun k : Nat ↦ s + k).filter (fun a ↦ decide (-(H : Int) ≤ a ∧ a ≤ H)) =
      numerators H := by
  have hm : m - (-(H : Int) - s).toNat - (s + m - 1 - H).toNat = 2 * H + 1 := by lia
  rw [List.filter_map_range_eq_map_range', numerators, hm]
  exact List.map_congr_left fun k _ ↦ by lia

/-- At the exit, the points found are those of the numerators `-H, …, H` that pass `keep`. -/
theorem SiftInvariant.toList_eq_flatMap_filter_numerators {g : Int → List (Int × Int × Int)}
    {keep : Int → Bool} {H range : Nat} {w0 w1 : Int} {out : Array (Int × Int × Int)}
    (h : SiftInvariant g keep H true range w0 w1 out) :
    out.toList = ((numerators H).filter keep).flatMap g := by
  have hR : (0 : Int) < rbaLength := by have := rbaLength_pos; lia
  have hL := Int.mul_ediv_self_le (x := -(H : Int)) (Int.ne_of_gt hR)
  have := Int.lt_mul_ediv_self_add (x := (H : Int)) hR
  have hM : ((((H : Int) / rbaLength + 1 - -(H : Int) / rbaLength).toNat * rbaLength : Nat) :
      Int) = rbaLength * ((H : Int) / rbaLength) + rbaLength -
        rbaLength * (-(H : Int) / rbaLength) := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg (by have := h.le_w0; have := h.eq_of_exit rfl; lia)]
    grind
  rw [h.toList_eq, h.eq_of_exit rfl, filter_map_range_eq_numerators hL (by lia)]

-- The rows of the run, read at the residue `b mod p` of each modulus, are the rows of `b`.
private theorem map_rows_eq_map_row {entries : List Entry} (hp : ∀ e ∈ entries, 0 < e.p)
    (b : Nat) :
    (entries.map fun e ↦ (e.p, e.rows)).map
        (fun x ↦ ({ p := x.1, row := (x.2[b % x.1]!).get } : SieveSpec)) =
      entries.map fun e ↦ ⟨e.p, e.row b⟩ := by
  rw [List.map_map]
  exact List.map_congr_left fun e he ↦ by
    simp only [Function.comp_apply, Entry.get_rows e (Nat.mod_lt b (hp e he)), Entry.row_mod]

-- The contract of `Ratpoints.Sieve.sift` for the rows of the tables `entries`.
open Std.WP Lean.Order in
private theorem sift_spec_map (c : List Int) (d H A b : Nat) (entries : List Entry) (hA : 1 ≤ A)
    (hp : ∀ e ∈ entries, 0 < e.p) :
    ⦃ True ⦄ sift c d H A b (entries.map fun e ↦ (e.p, e.rows))
    ⦃ fun out ↦ out.toList = pointsOfDen c d b ((numerators H).filter (survives entries b)) ⦄ := by
  vcgen [sift] invariants
  · SiftWhileInvariant (checkNum (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b)
      (survives entries b) H
  · .ofMeasure fun s ↦ ((H : Int) / rbaLength + 1 - s.2.1).toNat
  all_goals simp only [SiftWhileInvariant, WhileInvariant.mk_apply, Variant.evalsTo_ofMeasure,
    Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure, meet_prop_eq_and,
    ofProp_prop_eq, ite_true] at *
  all_goals first
    | exact siftInvariant_empty _ _ _ hA
    | exact ‹SiftInvariant _ _ _ true _ _ _ _›.toList_eq_flatMap_filter_numerators
    | exact ‹_ ∧ SiftInvariant _ _ _ false _ _ _ _›.2.exit_of_not_lt ‹_›
    | (have := rbaLength_pos; (try split) <;> lia)
    | obtain ⟨rfl, h⟩ := ‹_ ∧ SiftInvariant _ _ _ false _ _ _ _›
      have hpts := ‹∀ x : List Entry, _›
      specialize hpts entries hp (map_rows_eq_map_row hp b)
      first
        | exact ⟨h.toNat_sub_lt ‹_›,
            h.append h.w1_eq h.one_le_range (by lia) (ite_eq_toNat_mul_sub (by lia)) hpts⟩
        | exact ⟨by lia,
            h.append (by lia) (by lia) (Int.le_refl _) (sub_toNat_emod_eq_toNat_mul_sub H) hpts⟩

/-- The tables are quantified in the postcondition, since the program does not mention them; the
loop over the pieces ends by the measure `H / rbaLength + 1 - w0`, since every piece has at least
one bit array. -/
@[spec]
theorem sift_spec (c : List Int) (d H A b : Nat)
    (rows : List (Nat × Array (Thunk (Array UInt64)))) :
    ⦃ 1 ≤ A ⦄ sift c d H A b rows
    ⦃ fun out ↦ ∀ entries : List Entry, (∀ e ∈ entries, 0 < e.p) →
        rows = entries.map (fun e ↦ (e.p, e.rows)) →
        out.toList = pointsOfDen c d b ((numerators H).filter (survives entries b)) ⦄ :=
  ⟨fun hA entries hp hrows ↦ by
    subst hrows
    exact (sift_spec_map c d H A b entries hA hp).le_wp trivial⟩

/-- Both sides are what the brute-force reference finds over `b` and the numerators `-H, …, H`
that survive the tables (`Ratpoints.Sieve.sift_spec`, `Ratpoints.Sieve.sieveDen_spec`,
`Ratpoints.Sieve.checkDen_spec`). -/
theorem toList_run_sift_eq_checkDen (c : List Int) (d H b : Nat) {A : Nat} (hA : 1 ≤ A)
    {entries : List Entry} (hp : ∀ e ∈ entries, 0 < e.p) :
    (Id.run (sift c d H A b (entries.map fun e ↦ (e.p, e.rows)))).toList =
      (Id.run (checkDen c d H b (Id.run (sieveDen H b entries)))).toList :=
  ((sift_spec_map c d H A b entries hA hp).le_wp trivial).trans
    ((checkDen_spec c d H b _).le_wp trivial _ ((sieveDen_spec H b entries).le_wp trivial)).symm

/-! ### The run -/

/-- The invariant of the loop of `Ratpoints.Sieve.sieveRun` over the denominators: after the
denominators `j + 1`, `j ∈ pref`, the points found are those of the brute-force reference over
these denominators and the numerators that survive the tables `entries`. -/
def SieveRunInvariant (c : List Int) (d H : Nat) (entries : List Entry) (pref : List Nat)
    (out : Array (Int × Int × Int)) : Prop :=
  out.toList = pref.flatMap fun j ↦
    pointsOfDen c d (j + 1 : Nat) ((numerators H).filter (survives entries (j + 1)))

/-- The points of the denominators are the part of the brute-force reference `Ratpoints.bruteForce`
with `z ≥ 1`, its numerators filtered by the survivor test `Ratpoints.Sieve.survives`; the array
size `A ≥ 1` makes the loops over the pieces end, and the moduli are positive, as the first stage
over the rows as words needs (`Ratpoints.Sieve.andRows_spec`). -/
@[spec]
theorem sieveRun_spec (c : List Int) (d H A : Nat) (entries : List Entry) :
    ⦃ 1 ≤ A ∧ ∀ e ∈ entries, 0 < e.p ⦄ sieveRun c d H A entries
    ⦃ fun out ↦ out.toList = (List.range H).flatMap fun j ↦
        pointsOfDen c d (j + 1 : Nat) ((numerators H).filter (survives entries (j + 1))) ⦄ := by
  vcgen [sieveRun] invariants
  · fun pref _ out ↦ SieveRunInvariant c d H entries pref out
  all_goals grind [SieveRunInvariant, List.range_eq_range']

/-- `Ratpoints.Sieve.sieveRun_spec` as an equation, which the files with Mathlib use without the
program logic. -/
theorem toList_run_sieveRun (c : List Int) (d H : Nat) {A : Nat} (hA : 1 ≤ A)
    {entries : List Entry} (hp : ∀ e ∈ entries, 0 < e.p) :
    (Id.run (sieveRun c d H A entries)).toList = (List.range H).flatMap fun j ↦
      pointsOfDen c d (j + 1 : Nat) ((numerators H).filter (survives entries (j + 1))) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((sieveRun_spec c d H A entries).le_wp ⟨hA, hp⟩)

end Sieve

end Ratpoints

end
