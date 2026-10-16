/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Reductions

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers

/-!
# The closed form of the rows

The closed form of a row of words (`Ratpoints.Sieve.closedRow`): for an admission test `adm`, a
modulus `m` and a residue `r`, the `(m + chunk - 1) Ratpoints.rbaPack` words whose word `j` has bit
`t` set exactly when `adm r` admits the numerator `64 j + t`. Every builder of the rows of `init.c`
and of the generators of the headers of the build computes the closed form of its admission test
(`Ratpoints.Proof.PrimeRows`, `Ratpoints.Proof.CompositeRows`), and the tables of rows of a run hold
closed forms (`Ratpoints.Proof.RowStore`). For a test of period `m` the closed form repeats its
first `m` bit arrays in the `Ratpoints.chunk - 1` after them
(`Ratpoints.Sieve.getElem!_closedRow_mod`), the copies that the chunked first stage reads
(`Ratpoints.Sieve.SieveSpec.Wraps`). The words of a forbidden divisor
(`Ratpoints.Sieve.forbiddenRow`) have bit `t` of word `r` clear exactly when `p ∣ 64 r + t`, and the
row of `0` of a prime of the table (`Ratpoints.Sieve.sieves0`) is the closed form of the row of `0`
of every table of the prime, the first `p` of its words those of the forbidden divisor `p`.

The words of a pattern in the shape in which the builders compute them: a word holding a stretch of
bits of a pattern of period `m` (`Ratpoints.Sieve.PatternBits`), and the words of a row that are the
windows of 64 bits of the pattern (`Ratpoints.Sieve.RowWords`), which give the closed form
(`Ratpoints.Sieve.RowWords.toArray_eq_closedRow`). The proofs read the bits of a bit array of words
off the bits of its words (`Ratpoints.Sieve.patBit`); these are the bits that the C code reads with
a shift and a mask (`Ratpoints.Sieve.bitAt_eq_patBit`) and sets one at a time
(`Ratpoints.Sieve.bitAt_setBitAt`).

## Main definitions

* `Ratpoints.Sieve.wordOfBits`: the word of the bits `c t`, `t < 64`.
* `Ratpoints.Sieve.closedRow`: the closed form of a row.
* `Ratpoints.Sieve.PatternBits`, `Ratpoints.Sieve.RowWords`: a word holding a stretch of a periodic
  pattern, and the words of a row that are windows of it.
* `Ratpoints.Sieve.patBit`: bit `x` of an array of words, read off the bits of its word.

## Main statements

* `Ratpoints.Sieve.getLsbD_closedRow`: bit `t` of word `j` of the closed form says whether the test
  admits `64 j + t`.
* `Ratpoints.Sieve.getElem!_closedRow_mod`, `Ratpoints.Sieve.wraps_closedRow`,
  `Ratpoints.Sieve.SieveEntry.wraps_closedRow`: the closed form of a test of period `m` repeats its
  first `m` bit arrays.
* `Ratpoints.Sieve.RowWords.toArray_eq_closedRow`: words of a row that are the windows of a pattern
  are the closed form of a test that reads the pattern.
* `Ratpoints.Sieve.bitAt_eq_patBit`, `Ratpoints.Sieve.bitAt_setBitAt`: the bit of a bit array of
  words that the C code reads, and the bits after one is set.
* `Ratpoints.Sieve.getLsbD_getElem!_forbiddenRow`: the bits of the words of a forbidden divisor.
* `Ratpoints.Sieve.sieves0_eq_closedRow`, `Ratpoints.Sieve.extract_sieves0`: the row of `0` of a
  prime is the closed form of the row of `0` of its table, and its first `p` words are those of the
  forbidden divisor `p`.

## Implementation notes

The file uses Lean core and `Std` only, as the contracts of the sieve do; the proofs use only that
`Ratpoints.rbaPack` and `Ratpoints.chunk` are positive, never their values.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The closed form -/

/-- The word whose bit `t` is `c t` for `t < 64`. -/
def wordOfBits (c : Nat → Bool) : UInt64 :=
  Nat.fold 64 (fun t _ w ↦ if c t then w ||| 1 <<< t.toUInt64 else w) 0

theorem getLsbD_wordOfBits (c : Nat → Bool) (t : Nat) :
    (wordOfBits c).toBitVec.getLsbD t = (decide (t < 64) && c t) :=
  UInt64.getLsbD_fold_or_one_shiftLeft c (Nat.le_refl 64) t

/-- The closed form of the row of the residue `r` for the admission test `adm` of the modulus `m`:
`m + chunk - 1` bit arrays of `Ratpoints.rbaPack` words, for the chunk `Ratpoints.chunk`, word `j`
with bit `t` set exactly when `adm r` admits the numerator `64 j + t`. With the test
`Ratpoints.Sieve.SieveEntry.admits` of a sieve entry, or `Ratpoints.Sieve.Factor.admits` of a
factor, this is the row that ratpoints builds for the residue, `m` bit arrays and the copies of the
first `chunk - 1` of them (`Ratpoints.Sieve.getElem!_closedRow_mod`). -/
def closedRow (adm : Nat → Int → Bool) (m r : Nat) : Array UInt64 :=
  (Array.range ((m + chunk - 1) * rbaPack)).map fun (j : Nat) ↦
    wordOfBits fun (t : Nat) ↦ adm r (64 * j + t)

@[simp]
theorem size_closedRow (adm : Nat → Int → Bool) (m r : Nat) :
    (closedRow adm m r).size = (m + chunk - 1) * rbaPack := by
  simp [closedRow]

theorem getLsbD_closedRow (adm : Nat → Int → Bool) (m r : Nat) {j : Nat}
    (hj : j < (m + chunk - 1) * rbaPack) (t : Nat) :
    (closedRow adm m r)[j]!.toBitVec.getLsbD t = (decide (t < 64) && adm r (64 * j + t)) := by
  rw [closedRow, Array.getElem!_map_range _ hj, getLsbD_wordOfBits]

/-- An array of `(m + chunk - 1) rbaPack` words whose word `j` has bit `t` set exactly when `adm r`
admits `64 j + t` is the closed form. -/
theorem eq_closedRow {adm : Nat → Int → Bool} {m r : Nat} {row : Array UInt64}
    (hs : row.size = (m + chunk - 1) * rbaPack)
    (h : ∀ j < (m + chunk - 1) * rbaPack, ∀ t,
      row[j]!.toBitVec.getLsbD t = (decide (t < 64) && adm r (64 * j + t))) :
    row = closedRow adm m r := by
  refine Array.ext (by simp [hs]) fun j h1 h2 ↦ ?_
  rw [← getElem!_pos row j h1, ← getElem!_pos (closedRow adm m r) j h2]
  exact UInt64.eq_of_getLsbD_eq fun t ↦ by
    rw [h j (hs ▸ h1) t, getLsbD_closedRow adm m r (hs ▸ h1)]

/-- The closed form of a test of period `m > 0` repeats its first `m` bit arrays: word `j` is word
`j mod m rbaPack`. -/
theorem getElem!_closedRow_mod {adm : Nat → Int → Bool} {m r : Nat} (hm : 0 < m)
    (hadm : ∀ a k, adm r (a + m * k) = adm r a) {j : Nat} (hj : j < (m + chunk - 1) * rbaPack) :
    (closedRow adm m r)[j]! = (closedRow adm m r)[j % (m * rbaPack)]! := by
  have hmr : 0 < m * rbaPack := Nat.mul_pos hm rbaPack_pos
  have hlt : j % (m * rbaPack) < (m + chunk - 1) * rbaPack :=
    Nat.lt_of_lt_of_le (Nat.mod_lt _ hmr) (Nat.mul_le_mul_right _ (by lia [chunk_pos]))
  refine UInt64.eq_of_getLsbD_eq fun t ↦ ?_
  rw [getLsbD_closedRow adm m r hj, getLsbD_closedRow adm m r hlt]
  have key : (64 * (j : Int) + t) = 64 * ((j % (m * rbaPack) : Nat) : Int) + t +
      m * (64 * rbaPack * (j / (m * rbaPack) : Nat)) := by
    have hd := Nat.div_add_mod j (m * rbaPack)
    generalize j / (m * rbaPack) = q at hd ⊢
    generalize j % (m * rbaPack) = s at hd ⊢
    subst hd
    push_cast
    lia
  rw [key, hadm]

/-- Word `κ < rbaPack` of bit array `j < c` of `c` bit arrays is below `c rbaPack`. -/
theorem rbaPack_mul_add_lt {c j κ : Nat} (hj : j < c) (hκ : κ < rbaPack) :
    rbaPack * j + κ < c * rbaPack := by
  rw [Nat.mul_comm c]
  lia [Nat.mul_le_mul_left rbaPack (show j + 1 ≤ c from hj)]

/-- Word `κ < rbaPack` of bit array `x` is word `κ` of bit array `x mod p` in the words modulo
`rbaPack p`. -/
theorem rbaPack_mul_add_mod {x κ p : Nat} (hκ : κ < rbaPack) :
    (rbaPack * x + κ) % (rbaPack * p) = rbaPack * (x % p) + κ := by
  rw [Nat.mod_mul, Nat.mul_add_mod, Nat.mod_eq_of_lt hκ, Nat.mul_add_div rbaPack_pos,
    Nat.div_eq_of_lt hκ, Nat.add_zero, Nat.add_comm]

/-- The row of a sieve spec that is the closed form of a test of period `p > 0` repeats its first
`p` bit arrays where the chunked first stage reads it. -/
theorem wraps_closedRow {adm : Nat → Int → Bool} {s : SieveSpec} {r : Nat} (hp : 0 < s.p)
    (hadm : ∀ a k, adm r (a + s.p * k) = adm r a) (hrow : s.row = closedRow adm s.p r) :
    s.Wraps := by
  intro x hx κ hκ
  rw [hrow, getElem!_closedRow_mod hp hadm (rbaPack_mul_add_lt hx hκ),
    getElem!_closedRow_mod hp hadm (rbaPack_mul_add_lt (by lia [Nat.mod_lt x hp, chunk_pos]) hκ),
    Nat.mul_comm s.p, rbaPack_mul_add_mod hκ, rbaPack_mul_add_mod hκ, Nat.mod_mod]

/-- The sieve spec of the closed form of a row of the sieve entry `e`, of a modulus `p > 0`, with
any offset, start and end, repeats its first bit arrays where the chunked first stage reads it. -/
theorem SieveEntry.wraps_closedRow (e : SieveEntry) (hp : 0 < e.p) (off st stop r : Nat) :
    (⟨e.p, off, closedRow e.admits e.p r, st, stop⟩ : SieveSpec).Wraps :=
  Sieve.wraps_closedRow hp (fun a k ↦ by simp [SieveEntry.admits, Int.add_mul_emod_self_left])
    rfl

/-! ### Words of a periodic pattern -/

/-- The word `x` holds `n ≤ 64` bits of the pattern `g` of period `m` from the position `s` on: bit
`t < n` of `x` is the bit of the pattern at `s + t`, and the bits from `n` on are clear. -/
def PatternBits (g : Nat → Bool) (m s n : Nat) (x : UInt64) : Prop :=
  ∀ t, x.toBitVec.getLsbD t = (decide (t < n) && g ((s + t) % m))

theorem PatternBits.congr_left {g : Nat → Bool} {m s s' n : Nat} {x : UInt64}
    (h : PatternBits g m s n x) (hs : s % m = s' % m) : PatternBits g m s' n x := by
  intro t
  rw [h t, Nat.add_mod, hs, ← Nat.add_mod]

/-- The words `0, …, L - 1` of `si` are the windows of the pattern `g` of period `m`: word `j` the
64 bits from the position `64 j` on. -/
def RowWords (g : Nat → Bool) (m L : Nat) {n : Nat} (si : Vector UInt64 n) : Prop :=
  ∀ j < L, PatternBits g m (64 * j) 64 si[j]!

/-- Setting word `L < n` to the window at `64 L` makes one more of the words windows. -/
theorem RowWords.set!_self {g : Nat → Bool} {m L n : Nat} {si : Vector UInt64 n}
    (h : RowWords g m L si) (hL : L < n) {x : UInt64} (hx : PatternBits g m (64 * L) 64 x) :
    RowWords g m (L + 1) (si.set! L x) := by
  intro j hj
  rw [Vector.getElem!_set! (by lia)]
  by_cases hjL : L = j
  · subst hjL
    simpa using hx
  · rw [ite_eq_right hjL]
    exact h j (by lia)

/-- Words that repeat the first `p` words of a row, whose word `j < p` is the window of the pattern
at `64 j`, are windows of the pattern, since `64 j ≡ 64 (j mod p) (mod p)`. -/
theorem RowWords.of_mod {g : Nat → Bool} {p n L : Nat} {si si' : Vector UInt64 n} (hp : 0 < p)
    (h : RowWords g p p si) (h' : ∀ j < L, si'[j]! = si[j % p]!) : RowWords g p L si' := by
  intro j hj
  rw [h' j hj]
  exact (h (j % p) (Nat.mod_lt _ hp)).congr_left (by rw [Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod])

/-- Words of a row of `(m + chunk - 1) rbaPack` words that are the windows of the pattern `g` of
period `m` are the closed form of a test `adm r` that reads the pattern at the residues of the
numerators. -/
theorem RowWords.toArray_eq_closedRow {g : Nat → Bool} {adm : Nat → Int → Bool} {m r : Nat}
    {si : Vector UInt64 ((m + chunk - 1) * rbaPack)}
    (h : RowWords g m ((m + chunk - 1) * rbaPack) si)
    (hg : ∀ N : Nat, g (N % m) = adm r N) : si.toArray = closedRow adm m r :=
  eq_closedRow (by simp) fun j hj t ↦ by
    rw [Vector.getElem!_toArray, h j hj t, hg]
    rfl

/-! ### The bits of a bit array of words -/

/-- Bit `x` of the words `pat`: bit `x mod 64` of word `⌊x / 64⌋`, read off the bits of the word, as
the proofs read the patterns of the rows and the bit arrays of the tables of a prime power
(`Ratpoints.Sieve.bitAt_eq_patBit`). -/
def patBit (pat : Array UInt64) (x : Nat) : Bool := pat[x / 64]!.toBitVec.getLsbD (x % 64)

/-- Setting bit `x` of the words of a pattern, `x` within the words, sets bit `x` of the pattern. -/
theorem patBit_setBitAt {pat : Array UInt64} {x : Nat} (hx : x / 64 < pat.size) (y : Nat) :
    patBit (setBitAt pat x) y = (patBit pat y || decide (y = x)) := by
  simp only [patBit, setBitAt]
  by_cases hq : x / 64 = y / 64
  · have hs : (pat.set! (x / 64) (pat[x / 64]! ||| 1 <<< (x % 64).toUInt64))[y / 64]! =
        pat[x / 64]! ||| 1 <<< (x % 64).toUInt64 := by
      rw [← hq]
      grind
    rw [hs, Nat.toUInt64_eq, UInt64.getLsbD_or_one_shiftLeft _ (Nat.mod_lt _ (by decide)), hq]
    congr 1
    exact decide_eq_decide.mpr ⟨fun h ↦ by lia, fun h ↦ by subst h; rfl⟩
  · have hs : (pat.set! (x / 64) (pat[x / 64]! ||| 1 <<< (x % 64).toUInt64))[y / 64]! =
        pat[y / 64]! := by
      grind
    have : y ≠ x := fun h ↦ hq (by rw [h])
    rw [hs]
    simp [this]

theorem size_setBitAt (pat : Array UInt64) (x : Nat) : (setBitAt pat x).size = pat.size := by
  simp [setBitAt]

/-- Bit `x` of a bit array of words read with the shift and the mask of the C code is the bit of
the pattern. -/
theorem bitAt_eq_patBit (ws : Array UInt64) (x : Nat) : bitAt ws x = patBit ws x := by
  rw [bitAt, patBit, bne, Nat.toUInt64_eq,
    UInt64.shiftRight_and_one_beq_zero _ (Nat.mod_lt _ (by decide)), Bool.not_not]

/-- Setting bit `x` of a bit array of words, `x` within the words, sets bit `x`. -/
theorem bitAt_setBitAt {ws : Array UInt64} {x : Nat} (hx : x / 64 < ws.size) (y : Nat) :
    bitAt (setBitAt ws x) y = (bitAt ws y || decide (y = x)) := by
  rw [bitAt_eq_patBit, bitAt_eq_patBit, patBit_setBitAt hx]

/-! ### The words of a forbidden divisor -/

-- The words of `Ratpoints.Sieve.forbiddenRow` after the bits of the first `k` multiples of `p` are
-- cleared.
private theorem size_fold_modify (p k : Nat) :
    (Nat.fold k (fun i _ row ↦ row.modify (p * i / 64) (· &&& ~~~(1 <<< (p * i % 64).toUInt64)))
      (Array.replicate p (~~~0 : UInt64))).size = p := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.fold_succ, Array.size_modify, ih]

private theorem exists_lt_succ_mul_eq_iff {p k r t : Nat} (ht : t < 64) :
    (∃ i < k + 1, p * i = 64 * r + t) ↔
      (∃ i < k, p * i = 64 * r + t) ∨ (p * k / 64 = r ∧ t = p * k % 64) := by
  rw [Nat.exists_lt_succ_right]
  exact or_congr_right ⟨fun h ↦ ⟨by lia, by lia⟩, fun h ↦ by lia⟩

private theorem getLsbD_fold_modify {p r : Nat} (hr : r < p) (k t : Nat) :
    (Nat.fold k (fun i _ row ↦ row.modify (p * i / 64) (· &&& ~~~(1 <<< (p * i % 64).toUInt64)))
      (Array.replicate p (~~~0 : UInt64)))[r]!.toBitVec.getLsbD t =
      (decide (t < 64) && !decide (∃ i < k, p * i = 64 * r + t)) := by
  induction k with
  | zero =>
    rw [Nat.fold_zero, getElem!_pos _ r (by rwa [Array.size_replicate]),
      Array.getElem_replicate, UInt64.getLsbD_allOnes]
    simp
  | succ k ih =>
    rw [Nat.fold_succ, getElem!_pos _ r (by rwa [Array.size_modify, size_fold_modify]),
      Array.getElem_modify, ← getElem!_pos _ r (by rwa [size_fold_modify])]
    rcases Nat.lt_or_ge t 64 with ht | ht
    · simp only [decide_eq_true ht, Bool.true_and, exists_lt_succ_mul_eq_iff ht]
      split
      · rw [UInt64.toBitVec_and, BitVec.getLsbD_and, ih, UInt64.toBitVec_not, BitVec.getLsbD_not,
          UInt64.getLsbD_one_shiftLeft (Nat.mod_lt _ (by decide))]
        simp [*]
      · rw [ih]
        simp [*]
    · simp [BitVec.getLsbD_of_ge _ _ ht, decide_eq_false (Nat.not_lt.mpr ht)]

-- The multiples `p i`, `i < 64`, of `p` are those among the positions `64 r + t` with `r < p` and
-- `t < 64`.
private theorem exists_lt_mul_eq_iff {p r t : Nat} (hr : r < p) (ht : t < 64) :
    (∃ i < 64, p * i = 64 * r + t) ↔ (64 * r + t) % p = 0 := by
  refine ⟨fun ⟨i, _, h⟩ ↦ h ▸ Nat.mul_mod_right p i, fun h ↦ ⟨(64 * r + t) / p, ?_,
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)⟩⟩
  rw [Nat.div_lt_iff_lt_mul (by lia)]
  lia

theorem size_forbiddenRow (p : Nat) : (forbiddenRow p).size = p :=
  size_fold_modify p 64

/-- Bit `t` of word `r < p` of the words of the forbidden divisor `p` is clear exactly when
`p ∣ 64 r + t`, the multiples `p i` of `p` with `i < 64` being cleared. -/
theorem getLsbD_getElem!_forbiddenRow {p r : Nat} (hr : r < p) (t : Nat) :
    (forbiddenRow p)[r]!.toBitVec.getLsbD t = (decide (t < 64) && (64 * r + t) % p != 0) := by
  rw [forbiddenRow, getLsbD_fold_modify hr]
  rcases Nat.lt_or_ge t 64 with ht | ht
  · by_cases h : (64 * r + t) % p = 0 <;> simp [ht, exists_lt_mul_eq_iff hr ht, h]
  · simp [decide_eq_false (Nat.not_lt.mpr ht)]

/-! ### The row of `0` of a prime -/

theorem size_sieves0 (p : Nat) : (sieves0 p).size = (p + chunk - 1) * rbaPack := by
  rw [sieves0, Array.size_append, Array.size_fold_append, size_forbiddenRow, Array.size_map,
    Array.size_range, Nat.add_sub_assoc chunk_pos, Nat.add_mul, Nat.mul_comm rbaPack]

/-- Word `x` of the row of `0` of the prime `p` is word `x mod p` of the words of the forbidden
divisor `p`. -/
theorem getElem!_sieves0 {p x : Nat} (hx : x < (p + chunk - 1) * rbaPack) :
    (sieves0 p)[x]! = (forbiddenRow p)[x % p]! := by
  rw [sieves0, Array.getElem!_append, Array.size_fold_append, size_forbiddenRow]
  split
  · rw [Array.getElem!_fold_append _ (by rwa [size_forbiddenRow]), size_forbiddenRow]
  · rw [Array.getElem!_map_range _ (by rw [Nat.add_sub_assoc chunk_pos, Nat.add_mul] at hx; lia),
      Nat.sub_mul_mod (by lia)]

/-- The row of `0` of the prime `p = e.p > 0` of the table is the closed form of the row of `0` of
the table `e` of the prime, whatever its entries: bit `t` of word `x` set exactly when
`p ∤ 64 x + t`. -/
theorem sieves0_eq_closedRow (e : Entry) (hp : 0 < e.p) : sieves0 e.p = closedRow e.admits e.p 0 :=
  eq_closedRow (size_sieves0 e.p) fun j hj t ↦ by
    have hc : ((64 * (j : Int) + t) % (e.p : Int)).toNat = (64 * j + t) % e.p := by
      rw [show 64 * (j : Int) + t = ((64 * j + t : Nat) : Int) by push_cast; rfl,
        ← Int.natCast_emod, Int.toNat_natCast]
    rw [getElem!_sieves0 hj, getLsbD_getElem!_forbiddenRow (Nat.mod_lt _ hp), Entry.admits]
    simp only [Nat.zero_mod, ↓reduceIte, hc]
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, ← Nat.add_mod]

/-- The first `p` words of the row of `0` of the prime `p` are the words of the forbidden divisor
`p`. -/
theorem extract_sieves0 (p : Nat) : (sieves0 p).extract 0 p = forbiddenRow p := by
  have hle : p ≤ (p + chunk - 1) * rbaPack :=
    Nat.le_trans (Nat.le_mul_of_pos_right p rbaPack_pos)
      (Nat.mul_le_mul_right _ (by lia [chunk_pos]))
  refine Array.ext (by simp [size_sieves0, size_forbiddenRow, Nat.min_eq_left hle]) fun i h1 h2 ↦ ?_
  have hi : i < p := by rwa [size_forbiddenRow] at h2
  rw [Array.getElem_extract, ← getElem!_pos (sieves0 p) _ (by rw [size_sieves0]; lia),
    getElem!_sieves0 (by lia), Nat.zero_add, Nat.mod_eq_of_lt hi, getElem!_pos]

end Sieve

end Ratpoints

end
