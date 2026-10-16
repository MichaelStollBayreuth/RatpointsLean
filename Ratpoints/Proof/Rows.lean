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
`t` set exactly when `adm r` admits the numerator `64 j + t`. The row of a denominator as words
(`Ratpoints.Sieve.SieveEntry.row`) is the closed form of the admission test of its sieve entry
(`Ratpoints.Sieve.SieveEntry.row_eq_closedRow`), and so are the rows that the builders of `init.c`
and the generators of the headers of the build compute (stage F4). For a test of period `m` the
closed form repeats its first `m` bit arrays in the `Ratpoints.chunk - 1` after them
(`Ratpoints.Sieve.getElem!_closedRow_mod`), the copies that the chunked first stage reads
(`Ratpoints.Sieve.SieveSpec.Wraps`).

The words of a pattern in the shape in which the builders compute them: a word holding a stretch of
bits of a pattern of period `m` (`Ratpoints.Sieve.PatternBits`), and the words of a row that are the
windows of 64 bits of the pattern (`Ratpoints.Sieve.RowWords`), which give the closed form
(`Ratpoints.Sieve.RowWords.toArray_eq_closedRow`).

## Main definitions

* `Ratpoints.Sieve.wordOfBits`: the word of the bits `c t`, `t < 64`.
* `Ratpoints.Sieve.closedRow`: the closed form of a row.
* `Ratpoints.Sieve.PatternBits`, `Ratpoints.Sieve.RowWords`: a word holding a stretch of a periodic
  pattern, and the words of a row that are windows of it.

## Main statements

* `Ratpoints.Sieve.getLsbD_closedRow`: bit `t` of word `j` of the closed form says whether the test
  admits `64 j + t`.
* `Ratpoints.Sieve.getElem!_closedRow_mod`, `Ratpoints.Sieve.wraps_closedRow`,
  `Ratpoints.Sieve.SieveEntry.wraps_closedRow`: the closed form of a test of period `m` repeats its
  first `m` bit arrays.
* `Ratpoints.Sieve.RowWords.toArray_eq_closedRow`: words of a row that are the windows of a pattern
  are the closed form of a test that reads the pattern.

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

/-- The closed forms of two tests that agree at their residues are equal. -/
theorem closedRow_congr {adm adm' : Nat → Int → Bool} {m r r' : Nat}
    (h : ∀ a, adm r a = adm' r' a) : closedRow adm m r = closedRow adm' m r' := by
  simp only [closedRow, h]

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

theorem PatternBits.ext {g : Nat → Bool} {m s n : Nat} {x y : UInt64}
    (hx : PatternBits g m s n x) (hy : PatternBits g m s n y) : x = y :=
  UInt64.eq_of_getLsbD_eq fun t ↦ by rw [hx t, hy t]

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

/-- Words that repeat the first `m rbaPack` words of a row, whose word `j < m rbaPack` is the window
of the pattern at `64 j`, are windows of the pattern, since `m ∣ 64 m rbaPack`. -/
theorem RowWords.of_mod_mul {g : Nat → Bool} {m n L : Nat} {si si' : Vector UInt64 n}
    (hm : 0 < m) (h : RowWords g m (m * rbaPack) si)
    (h' : ∀ j < L, si'[j]! = si[j % (m * rbaPack)]!) : RowWords g m L si' := by
  intro j hj
  rw [h' j hj]
  refine (h _ (Nat.mod_lt _ (Nat.mul_pos hm rbaPack_pos))).congr_left ?_
  rw [Nat.mul_mod, Nat.mod_mod_of_dvd _ (Nat.dvd_mul_right m rbaPack), ← Nat.mul_mod]

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

end Sieve

end Ratpoints

end
