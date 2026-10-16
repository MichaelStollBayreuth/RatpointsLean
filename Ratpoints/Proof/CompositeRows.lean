/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Rows
public import Std.WP

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Words
import Std.Tactic.Do

/-!
# The contracts of the builders of the rows of a prime power and of a product

The contracts of `lay_out_pattern` (`Ratpoints.Sieve.repeatPattern`,
`Ratpoints.Sieve.layOutPattern`), of the builder of the rows of a prime power
(`Ratpoints.Sieve.sieveInitPower`, with the patterns `Ratpoints.Sieve.powerPatternUnit` and
`Ratpoints.Sieve.powerPatternNonunit`), and of the blocks of the builder of the rows of a product
(`Ratpoints.Sieve.productCopy`, `Ratpoints.Sieve.productAnd`), as `@[spec]` theorems proved with
`vcgen`, the program logic of Lean core, with loop invariants that are named definitions: the row of
the residue `b < m` of a prime power `m` is the closed form of the row of `b` of its tables
(`Ratpoints.Sieve.closedRow` of `Ratpoints.Sieve.Power.admits`), stored into the table of rows of
its entry, and the blocks of the rows of the factors of a product, and-ed, are the and of the rows
of the factors.

## Main definitions

* `Ratpoints.Sieve.PatClear`, `Ratpoints.Sieve.PatZero`: a pattern of period `m` with no bits from
  `m` on, and a cleared pattern.
* `Ratpoints.Sieve.RepeatedBits`: the words of the repeated pattern of `lay_out_pattern`.
* `Ratpoints.Sieve.factorWord`, `Ratpoints.Sieve.productWord`: a word of the row of a factor of a
  product read in the blocks of its length, and the and of those of the first factors.

## Main statements

* `Ratpoints.Sieve.repeatPattern_spec`, `Ratpoints.Sieve.layOutPattern_spec`: the pattern repeated
  through the words, and laid out as a row of windows.
* `Ratpoints.Sieve.sieveInitPower_spec`: the rows of a prime power.
* `Ratpoints.Sieve.productCopy_spec`, `Ratpoints.Sieve.productAnd_spec`: the blocks of the rows of
  the factors of a product.
* `Ratpoints.Sieve.toArray_eq_closedRow_of_productWord`: the rows of the factors in closed form,
  and-ed in their blocks, are the closed form of the row of the product.
* `Ratpoints.Sieve.SieveEntry.admits_eq_all`, `Ratpoints.Sieve.SieveEntry.admits_eq_of_factors_eq`:
  the row of a sieve entry whose factors have moduli dividing its modulus is the and of the rows of
  its factors, and that of an entry with one factor of its modulus is the row of the factor.

## Implementation notes

The file uses Lean core and `Std` only, as the contracts of the sieve do. The proofs use only that
`Ratpoints.rbaPack` and `Ratpoints.chunk` are positive, never their values. The bits of the words of
a pattern (`Ratpoints.Sieve.patBit`) are in `Ratpoints.Proof.Rows`, the contracts of the builders of
the rows of a prime in `Ratpoints.Proof.PrimeRows`, and those of the builders through the tables of
rows in `Ratpoints.Proof.RowStore`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The pattern repeated through words -/

/-- The words `pat` hold a pattern of period `m`: their bits from `m` to `64 ⌈m / 64⌉` are clear. -/
def PatClear (m : Nat) (pat : Array UInt64) : Prop :=
  ∀ x, m ≤ x → x < 64 * ((m + 64 - 1) / 64) → patBit pat x = false

/-- The pattern of period `m` in the words `pat`: bit `j` of word `i < ⌈m / 64⌉` the bit of the
pattern at `64 i + j` below `m`, clear from `m` on. -/
def IsPattern (g : Nat → Bool) (m : Nat) (pat : Array UInt64) : Prop :=
  ∀ i < (m + 64 - 1) / 64, ∀ j, pat[i]!.toBitVec.getLsbD j =
    (decide (j < 64) && decide (64 * i + j < m) && g (64 * i + j))

theorem isPattern_patBit {m : Nat} {pat : Array UInt64} (h : PatClear m pat) :
    IsPattern (patBit pat) m pat := by
  intro i hi j
  by_cases hj : j < 64
  · have h1 : patBit pat (64 * i + j) = pat[i]!.toBitVec.getLsbD j := by
      rw [patBit, show (64 * i + j) / 64 = i by lia, show (64 * i + j) % 64 = j by lia]
    by_cases hm : 64 * i + j < m
    · simp [hj, hm, h1]
    · rw [← h1, h (64 * i + j) (by lia) (by lia)]
      simp
  · simp [hj, BitVec.getLsbD_of_ge _ _ (Nat.le_of_not_lt hj)]

/-- The words `rep` below `W` hold the bits of the pattern of period `m` below the bound `L`, and
`0` from `L` on. -/
def RepeatedBits (g : Nat → Bool) (m W L : Nat) {n : Nat} (rep : Vector UInt64 n) : Prop :=
  ∀ w < W, ∀ j, rep[w]!.toBitVec.getLsbD j =
    (decide (j < 64) && decide (64 * w + j < L) && g ((64 * w + j) % m))

theorem RepeatedBits.mono {g : Nat → Bool} {m W L L' n : Nat} {rep : Vector UInt64 n}
    (h : RepeatedBits g m W L rep) (hL : min L (64 * W) = min L' (64 * W)) :
    RepeatedBits g m W L' rep := by
  intro w hw j
  rw [h w hw j]
  by_cases hj : j < 64
  · simp only [hj, decide_true, Bool.true_and]
    congr 1
    exact decide_eq_decide.mpr (by lia)
  · simp [hj]

/-- The first or of word `i` of the copy of the pattern at the offset `o = 64 q + s`, a multiple of
`m`: word `q + i` gets the word shifted left by `s`. -/
theorem RepeatedBits.first {g : Nat → Bool} {m W n o i : Nat} {rep : Vector UInt64 n}
    {pat : Array UInt64} (hpat : IsPattern g m pat) (hmo : m ∣ o) (hi : i < (m + 64 - 1) / 64)
    (hWn : W ≤ n) (h : RepeatedBits g m W (o + min m (64 * i)) rep) :
    RepeatedBits g m W (min (64 * (o / 64 + i + 1)) (o + m))
      (rep.set! (o / 64 + i) (rep[o / 64 + i]! ||| pat[i]! <<< UInt64.ofNat (o % 64))) := by
  intro w hw' j
  have hqs := Nat.div_add_mod o 64
  have hs := Nat.mod_lt o (show 0 < 64 by decide)
  have h64 : 64 * i < m := by lia
  rw [Vector.getElem!_set! (by lia)]
  split
  · rename_i hq
    subst hq
    rw [UInt64.toBitVec_or, BitVec.getLsbD_or, UInt64.getLsbD_shiftLeft_ofNat _ hs,
      h _ hw' j, hpat i hi]
    have key : o % 64 ≤ j → 64 * i + (j - o % 64) < m →
        (64 * (o / 64 + i) + j) % m = 64 * i + (j - o % 64) := fun h1 h2 ↦ by
      obtain ⟨c, hc⟩ := hmo
      rw [show 64 * (o / 64 + i) + j = m * c + (64 * i + (j - o % 64)) by lia,
        Nat.mul_add_mod, Nat.mod_eq_of_lt h2]
    grind
  · rw [h w hw' j]
    grind

/-- The second or of word `i` of the copy at the offset `o = 64 q + s`, `s ≠ 0`: word `q + i + 1`
gets the word shifted right by `64 - s`. -/
theorem RepeatedBits.second {g : Nat → Bool} {m W n o i : Nat} {rep : Vector UInt64 n}
    {pat : Array UInt64} (hpat : IsPattern g m pat) (hmo : m ∣ o) (hi : i < (m + 64 - 1) / 64)
    (hs0 : o % 64 ≠ 0) (hWn : W ≤ n)
    (h : RepeatedBits g m W (min (64 * (o / 64 + i + 1)) (o + m)) rep) :
    RepeatedBits g m W (o + min m (64 * (i + 1)))
      (rep.set! (o / 64 + i + 1)
        (rep[o / 64 + i + 1]! ||| pat[i]! >>> UInt64.ofNat (64 - o % 64))) := by
  intro w hw' j
  have hqs := Nat.div_add_mod o 64
  have hs := Nat.mod_lt o (show 0 < 64 by decide)
  have h64 : 64 * i < m := by lia
  rw [Vector.getElem!_set! (by lia)]
  split
  · rename_i hq
    subst hq
    rw [UInt64.toBitVec_or, BitVec.getLsbD_or, UInt64.getLsbD_shiftRight_ofNat _ (by lia),
      h _ hw' j, hpat i hi]
    have key : j < o % 64 → 64 * i + (64 - o % 64 + j) < m →
        (64 * (o / 64 + i + 1) + j) % m = 64 * i + (64 - o % 64 + j) := fun h1 h2 ↦ by
      obtain ⟨c, hc⟩ := hmo
      rw [show 64 * (o / 64 + i + 1) + j = m * c + (64 * i + (64 - o % 64 + j)) by lia,
        Nat.mul_add_mod, Nat.mod_eq_of_lt h2]
    grind
  · rw [h w hw' j]
    grind

/-- The invariant of the loop of `Ratpoints.Sieve.repeatPattern` over the copies of the pattern:
the offset `o` is a multiple of `m`, the words of `rep` hold the bits below it, and at the exit `o`
has reached `64 W`. -/
def LayOuterInvariant (g : Nat → Bool) (m W : Nat) {n : Nat} :
    Std.WP.WhileInvariant (Vector UInt64 n × Nat) Prop :=
  .mk fun exit s ↦ m ∣ s.2 ∧ RepeatedBits g m W s.2 s.1 ∧ (exit = true → 64 * W ≤ s.2)

/-- The invariant of the loop over the words `i` of the copy at the offset `o`: the words of `rep`
hold the bits below `o + 64 i` (and below `o + m`), and at the exit the copy is done or cut at the
end of the words. -/
def LayInnerInvariant (g : Nat → Bool) (m W o : Nat) {n : Nat} :
    Std.WP.WhileInvariant (Vector UInt64 n × Nat) Prop :=
  .mk fun exit s ↦ s.2 ≤ (m + 64 - 1) / 64 ∧ RepeatedBits g m W (o + min m (64 * s.2)) s.1 ∧
    (exit = true → (m + 64 - 1) / 64 ≤ s.2 ∨ W ≤ o / 64 + s.2)

/-- A word cleared, by the loop that clears the first words of `rep`. -/
theorem RepeatedBits.set!_zero {g : Nat → Bool} {m n cur : Nat} {pref suff : List Nat} {W : Nat}
    {rep : Vector UInt64 n} (hl : ForIn.toList [0:W] = pref ++ cur :: suff)
    (h : RepeatedBits g m pref.length 0 rep) :
    RepeatedBits g m (pref ++ [cur]).length 0 (rep.set! cur 0) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  intro w hw j
  rw [List.length_append, List.length_singleton] at hw
  by_cases hwn : w < n
  · rw [Vector.getElem!_set! hwn]
    split
    · simp
    · exact h w (by lia) j
  · rw [getElem!_neg (rep.set! cur 0) w hwn]
    change (0 : UInt64).toBitVec.getLsbD j = _
    simp

theorem repeatedBits_nil (g : Nat → Bool) (m : Nat) {n : Nat} (rep : Vector UInt64 n) :
    RepeatedBits g m ([] : List Nat).length 0 rep :=
  fun _ h ↦ absurd h (Nat.not_lt_zero _)

theorem layOuterInvariant_init {g : Nat → Bool} {m W n : Nat} {rep : Vector UInt64 n}
    (h : RepeatedBits g m (ForIn.toList [0:W]).length 0 rep) :
    LayOuterInvariant g m W false (rep, 0) :=
  ⟨Nat.dvd_zero m, by simpa using h, nofun⟩

theorem LayOuterInvariant.inner {g : Nat → Bool} {m W o n mb : Nat} {rep : Vector UInt64 n}
    (h : W * 64 - o = mb ∧ LayOuterInvariant g m W false (rep, o)) :
    LayInnerInvariant g m W o false (rep, 0) :=
  ⟨Nat.zero_le _, by simpa using h.2.2.1, nofun⟩

/-- A step of the loop over the words of a copy: the first or, and the second for `s ≠ 0` when it
lies below `W`. -/
theorem LayInnerInvariant.or_shift {m W o n i mb mb' : Nat} {pat : Array UInt64}
    {rep rep0 : Vector UInt64 n} (pre : 0 < m ∧ W ≤ n ∧ PatClear m pat)
    (hout : W * 64 - o = mb' ∧ LayOuterInvariant (patBit pat) m W false (rep0, o))
    (h : (m + 64 - 1) / 64 - i = mb ∧ LayInnerInvariant (patBit pat) m W o false (rep, i))
    (hc : i < (m + 64 - 1) / 64 ∧ o / 64 + i < W) :
    (m + 64 - 1) / 64 - (i + 1) < mb ∧ LayInnerInvariant (patBit pat) m W o false
      (if ¬o % 64 = 0 ∧ o / 64 + i + 1 < W then
        (rep.set! (o / 64 + i) (rep[o / 64 + i]! ||| pat[i]! <<< UInt64.ofNat (o % 64))).set!
          (o / 64 + i + 1)
          ((rep.set! (o / 64 + i) (rep[o / 64 + i]! ||| pat[i]! <<< UInt64.ofNat (o % 64)))[o / 64 +
            i + 1]! ||| pat[i]! >>> UInt64.ofNat (64 - o % 64))
      else rep.set! (o / 64 + i) (rep[o / 64 + i]! ||| pat[i]! <<< UInt64.ofNat (o % 64)),
        i + 1) := by
  have hpat := isPattern_patBit pre.2.2
  have hmo := hout.2.1
  obtain ⟨rfl, -, hr, -⟩ := h
  have h1 := hr.first hpat hmo hc.1 pre.2.1
  refine ⟨by lia, by lia, ?_, nofun⟩
  split
  · exact h1.second hpat hmo hc.1 ‹_ ∧ _›.1 pre.2.1
  · refine h1.mono ?_
    by_cases hs : o % 64 = 0 <;> lia [Nat.div_add_mod o 64]

theorem LayInnerInvariant.exit {g : Nat → Bool} {m W o n i mb : Nat} {rep : Vector UInt64 n}
    (h : (m + 64 - 1) / 64 - i = mb ∧ LayInnerInvariant g m W o false (rep, i))
    (hc : ¬(i < (m + 64 - 1) / 64 ∧ o / 64 + i < W)) :
    LayInnerInvariant g m W o true (rep, i) :=
  ⟨h.2.1, h.2.2.1, fun _ ↦ by lia⟩

/-- The copy at `o` done: the bits below `o + m` are in the words, the offset moves on by `m`. -/
theorem LayOuterInvariant.add {g : Nat → Bool} {m W o n mb : Nat} {rep rep' : Vector UInt64 n}
    {i : Nat} {pat : Array UInt64} {P : Prop} (pre : 0 < m ∧ P ∧ PatClear m pat)
    (h : W * 64 - o = mb ∧ LayOuterInvariant g m W false (rep, o))
    (ho : o < W * 64) (h' : LayInnerInvariant g m W o true (rep', i)) :
    W * 64 - (o + m) < mb ∧ LayOuterInvariant g m W false (rep', o + m) := by
  obtain ⟨rfl, hmo, -, -⟩ := h
  obtain ⟨hi, hr, hex⟩ := h'
  have := Nat.div_add_mod o 64
  have := pre.1
  refine ⟨by lia, Nat.dvd_add hmo (Nat.dvd_refl m), hr.mono ?_, nofun⟩
  rcases hex rfl with h1 | h1 <;> lia

theorem LayOuterInvariant.exit {g : Nat → Bool} {m W o n mb : Nat} {rep : Vector UInt64 n}
    (h : W * 64 - o = mb ∧ LayOuterInvariant g m W false (rep, o)) (ho : ¬o < W * 64) :
    LayOuterInvariant g m W true (rep, o) :=
  ⟨h.2.1, h.2.2.1, fun _ ↦ by lia⟩

theorem LayOuterInvariant.full {g : Nat → Bool} {m W n o : Nat} {rep : Vector UInt64 n}
    (h : LayOuterInvariant g m W true (rep, o)) : RepeatedBits g m W (64 * W) rep :=
  h.2.1.mono (by lia [h.2.2 rfl])

attribute [local irreducible] LayOuterInvariant LayInnerInvariant RepeatedBits in
open Std.WP Lean.Order in
/-- The words of `rep` below `words ≤ modWords + 2` hold the pattern of period `m > 0` of the words
`pat` repeated from `0` on (`Ratpoints.Sieve.RepeatedBits`), for a pattern without bits from `m`
on. -/
@[spec]
theorem repeatPattern_spec (pat : Array UInt64) (m words : Nat)
    (rep : Vector UInt64 (modWords + 2)) :
    ⦃ 0 < m ∧ words ≤ modWords + 2 ∧ PatClear m pat ⦄ repeatPattern pat m words rep
    ⦃ fun rep' ↦ RepeatedBits (patBit pat) m words (64 * words) rep' ⦄ := by
  vcgen [repeatPattern] invariants
  | inv1 => fun done _ rep ↦ RepeatedBits (patBit pat) m done.length 0 rep
  | inv2 => LayOuterInvariant (patBit pat) m words
  | inv3 => Variant.ofMeasure fun s : Vector UInt64 (modWords + 2) × Nat ↦ words * 64 - s.2
  | inv4 _ _ _ o _ _ _ => LayInnerInvariant (patBit pat) m words o
  | inv5 => Variant.ofMeasure fun s : Vector UInt64 (modWords + 2) × Nat ↦ (m + 64 - 1) / 64 - s.2
  all_goals try simp only [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
    Variant.evalsBelow_ofMeasure_nat, meet_prop_eq_and, ofProp_prop_eq] at *
  all_goals first
    | exact repeatedBits_nil _ m rep
    | exact RepeatedBits.set!_zero ‹_› ‹_›
    | exact layOuterInvariant_init ‹_›
    | exact LayOuterInvariant.full ‹_›
    | exact LayOuterInvariant.inner ‹_›
    | exact LayOuterInvariant.add ‹_› ‹_› ‹_› ‹_›
    | exact LayInnerInvariant.or_shift ‹_› ‹_› ‹_› ‹_›
    | exact LayInnerInvariant.exit ‹_› ‹_›
    | exact LayOuterInvariant.exit ‹_› ‹_›

/-! ### The pattern laid out as a row -/

/-- The window of the repeated pattern at the offset `o ≡ 64 x (mod m)`, `o < m`, is the window of
the pattern at `64 x`. -/
theorem PatternBits.window_rep {g : Nat → Bool} {m W n o x : Nat} {rep : Vector UInt64 n}
    (hfull : RepeatedBits g m W (64 * W) rep) (hW : m + 64 ≤ 64 * W) (ho : o < m)
    (hox : o = 64 * x % m) : PatternBits g m (64 * x) 64 (window rep.toArray o) := by
  intro t
  rw [getLsbD_window, Vector.getElem!_toArray]
  by_cases ht : t < 64
  · rw [hfull _ (by lia), show 64 * ((o + t) / 64) + (o + t) % 64 = o + t by lia]
    have : (o + t) % m = (64 * x + t) % m := by rw [hox, Nat.mod_add_mod]
    simp [ht, Nat.mod_lt, this, show o + t < 64 * W by lia]
  · simp [ht]

/-- The invariant of the loop of the words of the row of `Ratpoints.Sieve.layOutPattern`, after the
words below `x`: those words the windows of the pattern, and the offset `o ≡ 64 x (mod m)`. -/
def RowLoopInvariant (g : Nat → Bool) (m x : Nat) {n : Nat} (st : Vector UInt64 n × Nat) : Prop :=
  st.2 = 64 * x % m ∧ RowWords g m x st.1

theorem rowLoopInvariant_init (g : Nat → Bool) (m : Nat) {n : Nat} :
    RowLoopInvariant g m ([] : List Nat).length ((Vector.replicate n 0 : Vector UInt64 n), 0) :=
  ⟨by simp, nofun⟩

/-- A step of the loop of the words of the row: word `cur` the window at the offset, which steps
on by `64 mod m` modulo `m`. -/
theorem RowLoopInvariant.set!_window {m cur o : Nat} {pref suff : List Nat} {pat : Array UInt64}
    {rep : Vector UInt64 (modWords + 2)} {si : Vector UInt64 ((m + chunk - 1) * rbaPack)}
    (pre : 0 < m ∧ m ≤ 64 * modWords ∧ PatClear m pat)
    (hfull : RepeatedBits (patBit pat) m ((m + 64 + 64 - 1) / 64)
      (64 * ((m + 64 + 64 - 1) / 64)) rep)
    (hl : ForIn.toList [0:m * rbaPack] = pref ++ cur :: suff)
    (h : RowLoopInvariant (patBit pat) m pref.length (si, o)) :
    RowLoopInvariant (patBit pat) m (pref ++ [cur]).length
      (si.set! cur (window rep.toArray o),
        if m ≤ o + 64 % m then o + 64 % m - m else o + 64 % m) := by
  have hm := pre.1
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨ho, hsi⟩ := h
  dsimp only at ho hsi
  have hom : o < m := by rw [ho]; exact Nat.mod_lt _ hm
  rw [List.length_append, List.length_singleton]
  refine ⟨?_, ?_⟩
  · dsimp only
    rw [← Nat.mod_eq_ite_of_lt_two_mul (by lia [Nat.mod_lt 64 hm]), ho, Nat.mod_add_mod,
      Nat.add_mod_mod, Nat.mul_add_one]
  · rw [hc] at hsi ho ⊢
    exact hsi.set!_self (Nat.lt_of_lt_of_le hcl
      (Nat.mul_le_mul_right _ (by lia [chunk_pos])))
      (PatternBits.window_rep hfull (by lia) hom ho)

theorem RowLoopInvariant.rowWords {g : Nat → Bool} {m n : Nat} {st : Vector UInt64 n × Nat}
    (h : RowLoopInvariant g m (ForIn.toList [0:m * rbaPack]).length st) :
    RowWords g m (m * rbaPack + ([] : List Nat).length) st.1 := by
  simpa using h.2

/-- A copy of word `k` to word `m rbaPack + k`, the window there being that at `64 k`, since
`m ∣ 64 m rbaPack`. -/
theorem RowWords.set!_copy {g : Nat → Bool} {m cur : Nat} {pref suff : List Nat}
    {si : Vector UInt64 ((m + chunk - 1) * rbaPack)} {P : Prop} (pre : 0 < m ∧ P)
    (hl : ForIn.toList [0:(chunk - 1) * rbaPack] = pref ++ cur :: suff)
    (h : RowWords g m (m * rbaPack + pref.length) si) :
    RowWords g m (m * rbaPack + (pref ++ [cur]).length) (si.set! (m * rbaPack + cur) si[cur]!) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hn : (m + chunk - 1) * rbaPack = m * rbaPack + (chunk - 1) * rbaPack := by
    rw [Nat.add_sub_assoc chunk_pos, Nat.add_mul]
  have := Nat.mul_pos pre.1 rbaPack_pos
  rw [List.length_append, List.length_singleton, hc, ← Nat.add_assoc]
  rw [hc] at h
  refine h.set!_self (by lia) ((h cur (by lia)).congr_left ?_)
  rw [Nat.mul_add, Nat.add_mod, show 64 * (m * rbaPack) % m = 0 by
    rw [Nat.mul_comm m, ← Nat.mul_assoc, Nat.mul_mod_left], Nat.zero_add, Nat.mod_mod]

theorem RowWords.post_copy {g : Nat → Bool} {m n : Nat} {si : Vector UInt64 n}
    (h : RowWords g m (m * rbaPack + (ForIn.toList [0:(chunk - 1) * rbaPack]).length) si) :
    RowWords g m ((m + chunk - 1) * rbaPack) si := by
  rwa [Std.Legacy.Range.length_toList, Nat.sub_zero, ← Nat.add_mul,
    ← Nat.add_sub_assoc chunk_pos] at h

theorem layOutPattern_pre {m : Nat} {pat : Array UInt64}
    (pre : 0 < m ∧ m ≤ 64 * modWords ∧ PatClear m pat) :
    0 < m ∧ (m + 64 + 64 - 1) / 64 ≤ modWords + 2 ∧ PatClear m pat :=
  ⟨pre.1, by have := pre.2.1; lia, pre.2.2⟩

attribute [local irreducible] RowLoopInvariant RepeatedBits in
/-- The row of the pattern of period `0 < m ≤ 64 Ratpoints.modWords` in the words `pat`, without
bits from `m` on, as `lay_out_pattern` lays it out: `m + chunk - 1` bit arrays, word `j` the window
of the pattern at `64 j`. -/
@[spec]
theorem layOutPattern_spec (pat : Array UInt64) (m : Nat) :
    ⦃ 0 < m ∧ m ≤ 64 * modWords ∧ PatClear m pat ⦄ layOutPattern pat m
    ⦃ fun si ↦ RowWords (patBit pat) m ((m + chunk - 1) * rbaPack) si ⦄ := by
  vcgen [layOutPattern] invariants
  | inv1 => fun done _ st ↦ RowLoopInvariant (patBit pat) m done.length st
  | inv2 => fun done _ si ↦ RowWords (patBit pat) m (m * rbaPack + done.length) si
  -- The alternatives match at reducible transparency: with a chunk of 1 and one word of the
  -- pattern a failing alternative otherwise unfolds the sizes into a timeout.
  all_goals first
    | with_reducible exact layOutPattern_pre ‹_›
    | with_reducible exact rowLoopInvariant_init _ m
    | with_reducible exact RowLoopInvariant.rowWords ‹_›
    | with_reducible exact RowWords.post_copy ‹_›
    | with_reducible exact RowWords.set!_copy ‹_› ‹_› ‹_›
    | with_reducible exact RowLoopInvariant.set!_window ‹_› ‹_› ‹_› ‹_›

/-! ### The rows of a prime power -/

/-- The words of a cleared pattern: `Ratpoints.modWords` words, every bit clear. -/
def PatZero (pat : Array UInt64) : Prop := pat.size = modWords ∧ ∀ y, patBit pat y = false

/-- The invariant of the loop of `Ratpoints.Sieve.powerPatternUnit` after the residues below `x`:
the residue `r = x b⁻¹ mod m` and the bits below `x` set where `Ratpoints.Sieve.Power.fsq` has the
bit of `y b⁻¹`. -/
def UnitPatternInvariant (pw : Power) (binv x : Nat) (st : Array UInt64 × Nat) : Prop :=
  st.2 = x * binv % pw.m ∧ st.1.size = modWords ∧
    ∀ y, patBit st.1 y = (decide (y < x) && bitAt pw.fsq (y * binv % pw.m))

theorem unitPatternInvariant_init {pw : Power} {b : Nat} {pat : Array UInt64}
    (pre : 0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m ∧ PatZero pat) :
    UnitPatternInvariant pw pw.inv[b]! ([] : List Nat).length (pat, 0) :=
  ⟨by simp, pre.2.2.2.1, fun y ↦ by rw [pre.2.2.2.2 y]; simp⟩

/-- The bits of the pattern of a unit after the residue `cur`, its bit set when
`Ratpoints.Sieve.Power.fsq` has the bit of `cur b⁻¹`. -/
theorem patBit_ite_setBitAt {pw : Power} {binv cur r : Nat} {pat : Array UInt64}
    (hr : r = cur * binv % pw.m) (hs : cur / 64 < pat.size)
    (hp : ∀ y, patBit pat y = (decide (y < cur) && bitAt pw.fsq (y * binv % pw.m))) (y : Nat) :
    patBit (if bitAt pw.fsq r = true then setBitAt pat cur else pat) y =
      (decide (y < cur + 1) && bitAt pw.fsq (y * binv % pw.m)) := by
  split
  · rw [patBit_setBitAt hs, hp y]
    by_cases hyc : y = cur
    · subst hyc hr
      simp [*]
    · simp [hyc, show (y < cur + 1) = (y < cur) by grind]
  · rw [hp y]
    by_cases hyc : y = cur
    · subst hyc hr
      simp [*]
    · simp [show (y < cur + 1) = (y < cur) by grind]

theorem UnitPatternInvariant.append_ite {pw : Power} {b cur : Nat} {pref suff : List Nat}
    {pat : Array UInt64} {r : Nat}
    (pre : 0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m ∧ PatZero pat)
    (hl : ForIn.toList [0:pw.m] = pref ++ cur :: suff) {pat' : Array UInt64}
    (h : UnitPatternInvariant pw pw.inv[b]! pref.length (pat', r)) :
    UnitPatternInvariant pw pw.inv[b]! (pref ++ [cur]).length
      (if bitAt pw.fsq r = true then Sieve.setBitAt pat' cur else pat',
        if pw.m ≤ r + pw.inv[b]! then r + pw.inv[b]! - pw.m else r + pw.inv[b]!) := by
  obtain ⟨hm, hmw, hb, -⟩ := pre
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨hr, hs, hp⟩ := h
  dsimp only at hr hs hp
  rw [hc] at hr hp
  rw [List.length_append, List.length_singleton, hc]
  refine ⟨?_, ?_, patBit_ite_setBitAt hr (by rw [hs]; lia) hp⟩
  · rw [hr, ← Nat.mod_eq_ite_of_lt_two_mul (by lia [Nat.mod_lt (cur * pw.inv[b]!) hm]),
      Nat.mod_add_mod, Nat.add_one_mul]
  · dsimp only
    split <;> simp [size_setBitAt, hs]

theorem UnitPatternInvariant.setBitAt {pw : Power} {b cur : Nat} {pref suff : List Nat}
    {pat : Array UInt64} {r : Nat}
    (pre : 0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m ∧ PatZero pat)
    (hl : ForIn.toList [0:pw.m] = pref ++ cur :: suff) {pat' : Array UInt64}
    (h : UnitPatternInvariant pw pw.inv[b]! pref.length (pat', r)) (hbit : bitAt pw.fsq r = true) :
    UnitPatternInvariant pw pw.inv[b]! (pref ++ [cur]).length (Sieve.setBitAt pat' cur,
      if pw.m ≤ r + pw.inv[b]! then r + pw.inv[b]! - pw.m else r + pw.inv[b]!) := by
  have := UnitPatternInvariant.append_ite pre hl h
  rwa [ite_eq_left hbit] at this

theorem UnitPatternInvariant.skip {pw : Power} {b cur : Nat} {pref suff : List Nat}
    {pat : Array UInt64} {r : Nat}
    (pre : 0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m ∧ PatZero pat)
    (hl : ForIn.toList [0:pw.m] = pref ++ cur :: suff) {pat' : Array UInt64}
    (h : UnitPatternInvariant pw pw.inv[b]! pref.length (pat', r)) (hbit : ¬bitAt pw.fsq r = true) :
    UnitPatternInvariant pw pw.inv[b]! (pref ++ [cur]).length (pat',
      if pw.m ≤ r + pw.inv[b]! then r + pw.inv[b]! - pw.m else r + pw.inv[b]!) := by
  have := UnitPatternInvariant.append_ite pre hl h
  rwa [ite_eq_right hbit] at this

theorem UnitPatternInvariant.post {pw : Power} {binv : Nat} {st : Array UInt64 × Nat}
    (h : UnitPatternInvariant pw binv (ForIn.toList [0:pw.m]).length st) :
    st.1.size = modWords ∧
      ∀ y, patBit st.1 y = (decide (y < pw.m) && bitAt pw.fsq (y * binv % pw.m)) := by
  simpa using h.2

attribute [local irreducible] UnitPatternInvariant in
/-- The pattern of the row of a unit `b` modulo the prime power `m`, from a cleared pattern: bit
`x < m` set when bit `x b⁻¹ mod m` of `Ratpoints.Sieve.Power.fsq` is, for the inverse of `b` below
`m`. -/
@[spec]
theorem powerPatternUnit_spec (pw : Power) (b : Nat) (pat : Array UInt64) :
    ⦃ 0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m ∧ PatZero pat ⦄
    powerPatternUnit pw b pat
    ⦃ fun pat' ↦ pat'.size = modWords ∧
        ∀ y, patBit pat' y = (decide (y < pw.m) && bitAt pw.fsq (y * pw.inv[b]! % pw.m)) ⦄ := by
  vcgen [powerPatternUnit] invariants
  | inv1 => fun done _ st ↦ UnitPatternInvariant pw pw.inv[b]! done.length st
  all_goals first
    | exact unitPatternInvariant_init ‹_›
    | exact UnitPatternInvariant.post ‹_›
    | exact UnitPatternInvariant.setBitAt ‹_› ‹_› ‹_› ‹_›
    | exact UnitPatternInvariant.skip ‹_› ‹_› ‹_› ‹_›

/-- The invariant of the loop of `Ratpoints.Sieve.powerPatternNonunit` after the residues below
`1 + c`: the bits `1 ≤ y < 1 + c` of the units `y` set where `Ratpoints.Sieve.Power.gsq` has the bit
of `b y⁻¹`. -/
def NonunitPatternInvariant (pw : Power) (b c : Nat) (pat : Array UInt64) : Prop :=
  pat.size = modWords ∧ ∀ y, patBit pat y =
    (decide (1 ≤ y ∧ y < 1 + c) && (y % pw.p != 0 && bitAt pw.gsq (b * pw.inv[y]! % pw.m)))

theorem nonunitPatternInvariant_init {pw : Power} {b : Nat} {pat : Array UInt64}
    (pre : 0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ PatZero pat) :
    NonunitPatternInvariant pw b ([] : List Nat).length pat :=
  ⟨pre.2.2.1, fun y ↦ by rw [pre.2.2.2 y]; simp; lia⟩

theorem NonunitPatternInvariant.setBitAt {pw : Power} {b cur : Nat} {pref suff : List Nat}
    {pat : Array UInt64} (pre : 0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ PatZero pat)
    (hl : ForIn.toList [1:pw.m] = pref ++ cur :: suff) {pat' : Array UInt64}
    (h : NonunitPatternInvariant pw b pref.length pat') (hc0 : ¬cur % pw.p = 0)
    (hbit : bitAt pw.gsq (b * pw.inv[cur]! % pw.m) = true) :
    NonunitPatternInvariant pw b (pref ++ [cur]).length (Sieve.setBitAt pat' cur) := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  refine ⟨by rw [size_setBitAt, h.1], fun y ↦ ?_⟩
  rw [List.length_append, List.length_singleton,
    patBit_setBitAt (by rw [h.1]; have := pre.2.1; lia), h.2 y]
  by_cases hyc : y = cur
  · subst hyc
    simp [*]
    lia
  · simp only [hyc, decide_false, Bool.or_false]
    congr 1
    exact decide_eq_decide.mpr (by lia)

theorem NonunitPatternInvariant.skip {pw : Power} {b cur : Nat} {pref suff : List Nat}
    {pat : Array UInt64} (hl : ForIn.toList [1:pw.m] = pref ++ cur :: suff)
    (h : NonunitPatternInvariant pw b pref.length pat)
    (hbit : cur % pw.p = 0 ∨ ¬bitAt pw.gsq (b * pw.inv[cur]! % pw.m) = true) :
    NonunitPatternInvariant pw b (pref ++ [cur]).length pat := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  refine ⟨h.1, fun y ↦ ?_⟩
  rw [List.length_append, List.length_singleton, h.2 y]
  by_cases hyc : y = cur
  · subst hyc
    rcases hbit with hbit | hbit <;> simp [hbit]
  · congr 1
    exact decide_eq_decide.mpr (by lia)

theorem NonunitPatternInvariant.post {pw : Power} {b : Nat} {pat : Array UInt64} {P Q : Prop}
    (pre : 0 < pw.m ∧ P ∧ Q) (h : NonunitPatternInvariant pw b (ForIn.toList [1:pw.m]).length pat) :
    pat.size = modWords ∧ ∀ y, patBit pat y =
      (decide (1 ≤ y ∧ y < pw.m) && (y % pw.p != 0 && bitAt pw.gsq (b * pw.inv[y]! % pw.m))) := by
  refine ⟨h.1, fun y ↦ ?_⟩
  rw [h.2 y, Std.Legacy.Range.length_toList, Nat.add_sub_cancel' pre.1]

attribute [local irreducible] NonunitPatternInvariant in
/-- The pattern of the row of a residue `b` divisible by `p` modulo the prime power `m`, from a
cleared pattern: bit `x` of a unit `x < m` set when bit `b x⁻¹ mod m` of `Ratpoints.Sieve.Power.gsq`
is. -/
@[spec]
theorem powerPatternNonunit_spec (pw : Power) (b : Nat) (pat : Array UInt64) :
    ⦃ 0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ PatZero pat ⦄ powerPatternNonunit pw b pat
    ⦃ fun pat' ↦ pat'.size = modWords ∧ ∀ y, patBit pat' y = (decide (1 ≤ y ∧ y < pw.m) &&
        (y % pw.p != 0 && bitAt pw.gsq (b * pw.inv[y]! % pw.m))) ⦄ := by
  vcgen [powerPatternNonunit] invariants
  | inv1 => fun done _ pat ↦ NonunitPatternInvariant pw b done.length pat
  all_goals first
    | exact nonunitPatternInvariant_init ‹_›
    | exact NonunitPatternInvariant.post ‹_› ‹_›
    | exact NonunitPatternInvariant.setBitAt ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact NonunitPatternInvariant.skip ‹_› ‹_› (.inl ‹_›)
    | exact NonunitPatternInvariant.skip ‹_› ‹_› (.inr ‹_›)

theorem patZero_replicate : PatZero (Array.replicate modWords 0) := by
  refine ⟨Array.size_replicate .., fun y ↦ ?_⟩
  simp only [patBit]
  by_cases hy : y / 64 < modWords
  · rw [getElem!_pos _ _ (by simpa using hy), Array.getElem_replicate]
    simp
  · rw [getElem!_neg _ _ (by simpa using hy)]
    change (0 : UInt64).toBitVec.getLsbD _ = _
    simp

theorem PatZero.set!_zero {pat : Array UInt64} (h : PatZero pat) (x : Nat) :
    PatZero (pat.set! x 0) := by
  refine ⟨by rw [Array.size_set!, h.1], fun y ↦ ?_⟩
  have hy := h.2 y
  simp only [patBit] at hy ⊢
  by_cases hxy : x = y / 64
  · subst hxy
    by_cases hs : y / 64 < pat.size
    · rw [show (pat.set! (y / 64) 0)[y / 64]! = 0 by grind]
      simp
    · rwa [show (pat.set! (y / 64) 0)[y / 64]! = pat[y / 64]! by grind]
  · rwa [show (pat.set! x 0)[y / 64]! = pat[y / 64]! by grind]

/-- The pattern of a unit `b < m` read at the residue of a numerator is the row of `b` of the prime
power. -/
theorem patBit_mod_eq_admits_of_unit {pw : Power} {b : Nat} {pat : Array UInt64} (hb : b < pw.m)
    (hbp : b % pw.p ≠ 0)
    (hpat : ∀ y, patBit pat y = (decide (y < pw.m) && bitAt pw.fsq (y * pw.inv[b]! % pw.m)))
    (N : Nat) : patBit pat (N % pw.m) = pw.admits b N := by
  have hm : 0 < pw.m := by lia
  have hx : ((N : Int) % (pw.m : Int)).toNat = N % pw.m := by
    rw [← Int.natCast_emod, Int.toNat_natCast]
  rw [hpat, Power.admits]
  simp [hx, Nat.mod_eq_of_lt hb, hbp, Nat.mod_lt _ hm]

/-- The pattern of a residue `b < m` divisible by `p` read at the residue of a numerator is the row
of `b` of the prime power. -/
theorem patBit_mod_eq_admits_of_dvd {pw : Power} {b : Nat} {pat : Array UInt64} (hb : b < pw.m)
    (hbp : ¬b % pw.p ≠ 0)
    (hpat : ∀ y, patBit pat y = (decide (1 ≤ y ∧ y < pw.m) &&
      (y % pw.p != 0 && bitAt pw.gsq (b * pw.inv[y]! % pw.m))))
    (N : Nat) : patBit pat (N % pw.m) = pw.admits b N := by
  have hm : 0 < pw.m := by lia
  have hx : ((N : Int) % (pw.m : Int)).toNat = N % pw.m := by
    rw [← Int.natCast_emod, Int.toNat_natCast]
  rw [hpat, Power.admits]
  simp only [hx, Nat.mod_eq_of_lt hb, hbp, ↓reduceIte]
  rcases Nat.eq_zero_or_pos (N % pw.m) with h0 | h0
  · simp [h0]
  · simp [show 1 ≤ N % pw.m by lia, Nat.mod_lt _ hm]

theorem sieveInitPower_pre_unit {pw : Power} {b : Nat} {pat : Array UInt64}
    (pre : b < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m) (h : PatZero pat) :
    0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m ∧ PatZero pat :=
  ⟨by lia, pre.2.1, pre.2.2, h⟩

theorem sieveInitPower_pre_nonunit {pw : Power} {b : Nat} {pat : Array UInt64}
    (pre : b < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m) (h : PatZero pat) :
    0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ PatZero pat :=
  ⟨by lia, pre.2.1, h⟩

theorem sieveInitPower_pre_layOut_unit {pw : Power} {b : Nat} {pat : Array UInt64}
    (pre : b < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m) {g : Nat → Bool}
    (hpat : pat.size = modWords ∧ ∀ y, patBit pat y = (decide (y < pw.m) && g y)) :
    0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ PatClear pw.m pat :=
  ⟨by lia, pre.2.1, fun y hy _ ↦ by rw [hpat.2 y]; simp; lia⟩

theorem sieveInitPower_pre_layOut_nonunit {pw : Power} {b : Nat} {pat : Array UInt64}
    (pre : b < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m) {g : Nat → Bool}
    (hpat : pat.size = modWords ∧ ∀ y, patBit pat y = (decide (1 ≤ y ∧ y < pw.m) && g y)) :
    0 < pw.m ∧ pw.m ≤ 64 * modWords ∧ PatClear pw.m pat :=
  ⟨by lia, pre.2.1, fun y hy _ ↦ by rw [hpat.2 y]; simp; lia⟩

/-- The row laid out from the pattern of the residue `b` is the closed form of the row of `b`,
and so is what the builder stores. -/
theorem sieveInitPower_post {pw : Power} {ref : EntryRef} {b : Nat} {store : RowStore}
    {pat : Array UInt64} {row : Vector UInt64 ((pw.m + chunk - 1) * rbaPack)}
    (hg : ∀ N : Nat, patBit pat (N % pw.m) = pw.admits b N)
    (hrow : RowWords (patBit pat) pw.m ((pw.m + chunk - 1) * rbaPack) row) :
    (row, store.publish ref b row.toArray).1.toArray = closedRow pw.admits pw.m b ∧
      (row, store.publish ref b row.toArray).2 =
        store.publish ref b (closedRow pw.admits pw.m b) := by
  have h := hrow.toArray_eq_closedRow hg
  exact ⟨h, by rw [← h]⟩

/-- The row of the residue `b < m` of the prime power `m ≤ 64 Ratpoints.modWords` with the tables
`pw`, for the inverse of `b` below `m`, is the closed form of the row of `b` of its tables, and the
builder stores it into the table of rows of the entry `ref`. -/
@[spec]
theorem sieveInitPower_spec (pw : Power) (ref : EntryRef) (b : Nat) (store : RowStore) :
    ⦃ b < pw.m ∧ pw.m ≤ 64 * modWords ∧ pw.inv[b]! < pw.m ⦄ sieveInitPower pw ref b store
    ⦃ fun r ↦ r.1.toArray = closedRow pw.admits pw.m b ∧
        r.2 = store.publish ref b (closedRow pw.admits pw.m b) ⦄ := by
  vcgen [sieveInitPower] invariants
  | inv1 => fun _ _ pat ↦ PatZero pat
  all_goals first
    | exact patZero_replicate
    | exact PatZero.set!_zero ‹_› _
    | exact sieveInitPower_pre_unit ‹_› ‹_›
    | exact sieveInitPower_pre_nonunit ‹_› ‹_›
    | exact sieveInitPower_pre_layOut_unit ‹_› ‹_›
    | exact sieveInitPower_pre_layOut_nonunit ‹_› ‹_›
    | exact sieveInitPower_post (patBit_mod_eq_admits_of_unit ‹_ ∧ _›.1 ‹_› ‹_ ∧ _›.2) ‹_›
    | exact sieveInitPower_post (patBit_mod_eq_admits_of_dvd ‹_ ∧ _›.1 ‹_› ‹_ ∧ _›.2) ‹_›

/-! ### The blocks of the rows of a product -/

/-- Word `y` of the row of factor `i` of the product `e`, read in the blocks of the length `q` of
its modulus: word `y mod rbaPack` of bit array `⌊y / rbaPack⌋ mod q` of the row `frows[i]`. -/
def factorWord (e : SieveEntry) (frows : Array (Array UInt64)) (i y : Nat) : UInt64 :=
  frows[i]![rbaPack * (y / rbaPack % e.factors[i]!.modulus) + y % rbaPack]!

/-- Word `y` of the row of the product `e` after its first `K ≥ 1` factors: the and of their words
(`Ratpoints.Sieve.factorWord`). -/
def productWord (e : SieveEntry) (frows : Array (Array UInt64)) (K y : Nat) : UInt64 :=
  (List.range' 1 (K - 1)).foldl (fun acc i ↦ acc &&& factorWord e frows i y)
    (factorWord e frows 0 y)

theorem productWord_succ (e : SieveEntry) (frows : Array (Array UInt64)) {K : Nat} (hK : 1 ≤ K)
    (y : Nat) :
    productWord e frows (K + 1) y = productWord e frows K y &&& factorWord e frows K y := by
  obtain ⟨K, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by lia⟩
  simp [productWord, List.range'_1_concat, Nat.add_comm 1 K]

/-- The invariant of the loop of `Ratpoints.Sieve.productCopy` over the blocks of the first factor:
the bit arrays below `x`, a multiple of its modulus up to `m`, laid down. -/
def FirstInvariant (e : SieveEntry) (frows : Array (Array UInt64)) {n : Nat} :
    Std.WP.WhileInvariant (Vector UInt64 n × Nat) Prop :=
  .mk fun exit s ↦ s.2 % e.factors[0]!.modulus = 0 ∧ s.2 ≤ e.p ∧ (exit = true → e.p ≤ s.2) ∧
    ∀ y < s.2 * rbaPack, s.1[y]! = factorWord e frows 0 y

theorem firstInvariant_init {e : SieveEntry} {frows : Array (Array UInt64)} {n : Nat}
    (row : Vector UInt64 n) : FirstInvariant e frows false (row, 0) :=
  ⟨Nat.zero_mod _, Nat.zero_le _, nofun, fun y hy ↦ by simp at hy⟩

/-- A copy of bit array `j` of the first factor into bit array `x + j`. -/
theorem FirstInvariant.storeBitArray {e : SieveEntry} {frows : Array (Array UInt64)}
    {n x cur mb : Nat}
    {pref suff : List Nat} {row row0 : Vector UInt64 n}
    (pre : 0 < e.factors[0]!.modulus ∧ e.factors[0]!.modulus ∣ e.p ∧ e.p * rbaPack ≤ n)
    (hinv : e.p - x = mb ∧ FirstInvariant e frows false (row0, x)) (hxm : x < e.p)
    (hl : ForIn.toList [0:e.factors[0]!.modulus] = pref ++ cur :: suff)
    (h : ∀ y < (x + pref.length) * rbaPack, row[y]! = factorWord e frows 0 y) :
    ∀ y < (x + (pref ++ [cur]).length) * rbaPack,
      (Sieve.storeBitArray row (x + cur) frows[0]!.toVector cur)[y]! = factorWord e frows 0 y := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hx0 : x % e.factors[0]!.modulus = 0 := hinv.2.1
  have hxq := Nat.le_of_lt_add_of_dvd (Nat.add_lt_add_right hxm _)
    (Nat.dvd_add (Nat.dvd_of_mod_eq_zero hx0) (Nat.dvd_refl _)) pre.2.1
  intro y hy
  rw [List.length_append, List.length_singleton] at hy
  have hyl := (Nat.div_lt_iff_lt_mul rbaPack_pos).mpr hy
  rw [getElem!_storeBitArray _ _ _ _ (Nat.lt_of_lt_of_le hy
    (Nat.le_trans (Nat.mul_le_mul_right _ (by lia)) pre.2.2))]
  split
  · rename_i hyc
    rw [Array.getElem!_toVector, factorWord, hyc, show (x + cur) % e.factors[0]!.modulus = cur by
      rw [Nat.add_mod, hx0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hcl]]
  · exact h y ((Nat.div_lt_iff_lt_mul rbaPack_pos).mp (by lia))

theorem FirstInvariant.add {e : SieveEntry} {frows : Array (Array UInt64)} {n x mb : Nat}
    {row row0 : Vector UInt64 n}
    (pre : 0 < e.factors[0]!.modulus ∧ e.factors[0]!.modulus ∣ e.p ∧ e.p * rbaPack ≤ n)
    (hinv : e.p - x = mb ∧ FirstInvariant e frows false (row0, x)) (hxm : x < e.p)
    (h : ∀ y < (x + (ForIn.toList [0:e.factors[0]!.modulus]).length) * rbaPack,
      row[y]! = factorWord e frows 0 y) :
    e.p - (x + e.factors[0]!.modulus) < mb ∧
      FirstInvariant e frows false (row, x + e.factors[0]!.modulus) := by
  have hx0 : x % e.factors[0]!.modulus = 0 := hinv.2.1
  have hxq := Nat.le_of_lt_add_of_dvd (Nat.add_lt_add_right hxm _)
    (Nat.dvd_add (Nat.dvd_of_mod_eq_zero hx0) (Nat.dvd_refl _)) pre.2.1
  refine ⟨by lia, by rw [Nat.add_mod_right]; exact hx0, hxq, nofun, fun y hy ↦ h y ?_⟩
  simpa using hy

theorem FirstInvariant.exit {e : SieveEntry} {frows : Array (Array UInt64)} {n x mb : Nat}
    {row : Vector UInt64 n} (h : e.p - x = mb ∧ FirstInvariant e frows false (row, x))
    (hxm : ¬x < e.p) : FirstInvariant e frows true (row, x) :=
  ⟨h.2.1, h.2.2.1, fun _ ↦ by lia, h.2.2.2.2⟩

theorem FirstInvariant.post {e : SieveEntry} {frows : Array (Array UInt64)} {n x : Nat}
    {row : Vector UInt64 n} (h : FirstInvariant e frows true (row, x)) {y : Nat}
    (hy : y < e.p * rbaPack) : row[y]! = factorWord e frows 0 y := by
  obtain ⟨-, hx, hex, hr⟩ := h
  obtain rfl : x = e.p := Nat.le_antisymm hx (hex rfl)
  exact hr y hy

theorem firstInvariant_inner {e : SieveEntry} {frows : Array (Array UInt64)} {n x mb : Nat}
    {row : Vector UInt64 n} (h : e.p - x = mb ∧ FirstInvariant e frows false (row, x)) {y : Nat}
    (hy : y < (x + ([] : List Nat).length) * rbaPack) : row[y]! = factorWord e frows 0 y :=
  h.2.2.2.2 y (by simpa using hy)

attribute [local irreducible] FirstInvariant factorWord in
open Std.WP Lean.Order in
/-- The row of the first factor of the product `e`, of a modulus `q ∣ m = e.p`, laid down in the
blocks of its length: word `y < m rbaPack` of the row is word `y` of the factor read in those blocks
(`Ratpoints.Sieve.factorWord`). -/
@[spec]
theorem productCopy_spec {n : Nat} (row : Vector UInt64 n) (e : SieveEntry)
    (frows : Array (Array UInt64)) :
    ⦃ 0 < e.factors[0]!.modulus ∧ e.factors[0]!.modulus ∣ e.p ∧ e.p * rbaPack ≤ n ⦄
    productCopy row e frows
    ⦃ fun row' ↦ ∀ y < e.p * rbaPack, row'[y]! = factorWord e frows 0 y ⦄ := by
  vcgen [productCopy] invariants
  | inv1 => FirstInvariant e frows
  | inv2 => Variant.ofMeasure fun s : Vector UInt64 n × Nat ↦ e.p - s.2
  | inv3 _ x _ _ _ => fun done _ row ↦ ∀ y < (x + done.length) * rbaPack,
      row[y]! = factorWord e frows 0 y
  all_goals try simp only [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
    Variant.evalsBelow_ofMeasure_nat, meet_prop_eq_and, ofProp_prop_eq] at *
  all_goals first
    | exact firstInvariant_init row
    | exact FirstInvariant.post ‹_› ‹_›
    | exact firstInvariant_inner ‹_› ‹_›
    | exact FirstInvariant.exit ‹_› ‹_›
    | exact FirstInvariant.add ‹_› ‹_› ‹_› ‹_›
    | with_reducible exact FirstInvariant.storeBitArray ‹_› ‹_› ‹_› ‹_› ‹_›

/-- The invariant of the loop of `Ratpoints.Sieve.productAnd` over the blocks of the factor
`i ≥ 1`: the bit arrays below `x`, a multiple of its modulus up to `m`, and-ed with it. -/
def FactorInvariant (e : SieveEntry) (frows : Array (Array UInt64)) (i : Nat) {n : Nat} :
    Std.WP.WhileInvariant (Vector UInt64 n × Nat) Prop :=
  .mk fun exit s ↦ s.2 % e.factors[i]!.modulus = 0 ∧ s.2 ≤ e.p ∧ (exit = true → e.p ≤ s.2) ∧
    ∀ y < e.p * rbaPack, s.1[y]! =
      if y / rbaPack < s.2 then productWord e frows (i + 1) y else productWord e frows i y

theorem productAnd_init {e : SieveEntry} {frows : Array (Array UInt64)} {n : Nat}
    {row : Vector UInt64 n} {P Q : Prop}
    (pre : P ∧ Q ∧ ∀ y < e.p * rbaPack, row[y]! = factorWord e frows 0 y) {y : Nat}
    (hy : y < e.p * rbaPack) : row[y]! = productWord e frows (1 + ([] : List Nat).length) y :=
  pre.2.2 y hy

theorem factorInvariant_init {e : SieveEntry} {frows : Array (Array UInt64)} {n cur : Nat}
    {pref suff : List Nat} {row : Vector UInt64 n}
    (hl : ForIn.toList [1:e.factors.length] = pref ++ cur :: suff)
    (h : ∀ y < e.p * rbaPack, row[y]! = productWord e frows (1 + pref.length) y) :
    FactorInvariant e frows cur false (row, 0) := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  refine ⟨Nat.zero_mod _, Nat.zero_le _, nofun, fun y hy ↦ ?_⟩
  rw [h y hy, hc]
  simp

theorem FactorInvariant.inner {e : SieveEntry} {frows : Array (Array UInt64)} {n i x mb : Nat}
    {row : Vector UInt64 n} (h : e.p - x = mb ∧ FactorInvariant e frows i false (row, x)) (y : Nat)
    (hy : y < e.p * rbaPack) : row[y]! = if y / rbaPack < x + ([] : List Nat).length then
      productWord e frows (i + 1) y else productWord e frows i y :=
  h.2.2.2.2 y hy

/-- An and of bit array `j` of the factor `i` into bit array `x + j`. -/
theorem FactorInvariant.andBitArray {e : SieveEntry} {frows : Array (Array UInt64)}
    {n i x cur mb : Nat} {pref' suff' pref suff : List Nat} {row row0 : Vector UInt64 n}
    (pre : (∀ i < e.factors.length, 0 < e.factors[i]!.modulus ∧ e.factors[i]!.modulus ∣ e.p) ∧
      e.p * rbaPack ≤ n ∧ ∀ y < e.p * rbaPack, row0[y]! = factorWord e frows 0 y)
    (hl' : ForIn.toList [1:e.factors.length] = pref' ++ i :: suff')
    (hinv : e.p - x = mb ∧ FactorInvariant e frows i false (row, x))
    (hl : ForIn.toList [0:e.factors[i]!.modulus] = pref ++ cur :: suff)
    {row' : Vector UInt64 n}
    (h : ∀ y < e.p * rbaPack, row'[y]! = if y / rbaPack < x + pref.length then
      productWord e frows (i + 1) y else productWord e frows i y) :
    ∀ y < e.p * rbaPack, (Sieve.andBitArray row' (x + cur) frows[i]! cur)[y]! =
      if y / rbaPack < x + (pref ++ [cur]).length then productWord e frows (i + 1) y
      else productWord e frows i y := by
  have hi := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl'
  have hil := Std.Legacy.Range.lt_of_toList_eq_append_cons hl'
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hx0 : x % e.factors[i]!.modulus = 0 := hinv.2.1
  intro y hy
  have hyl := (Nat.div_lt_iff_lt_mul rbaPack_pos).mpr hy
  rw [getElem!_andBitArray _ _ _ _ (Nat.lt_of_lt_of_le hy pre.2.1), List.length_append,
    List.length_singleton]
  split
  · rename_i hyc
    rw [h y hy, ite_eq_right (by lia), ite_eq_left (by lia), productWord_succ _ _ (by lia),
      factorWord, hyc, show (x + cur) % e.factors[i]!.modulus = cur by
        rw [Nat.add_mod, hx0, Nat.zero_add, Nat.mod_mod, Nat.mod_eq_of_lt hcl]]
  · rw [h y hy]
    split <;> split <;> first | rfl | lia

theorem FactorInvariant.add {e : SieveEntry} {frows : Array (Array UInt64)} {n i x mb : Nat}
    {pref' suff' : List Nat} {row row0 row' : Vector UInt64 n}
    (pre : (∀ i < e.factors.length, 0 < e.factors[i]!.modulus ∧ e.factors[i]!.modulus ∣ e.p) ∧
      e.p * rbaPack ≤ n ∧ ∀ y < e.p * rbaPack, row0[y]! = factorWord e frows 0 y)
    (hl' : ForIn.toList [1:e.factors.length] = pref' ++ i :: suff')
    (hinv : e.p - x = mb ∧ FactorInvariant e frows i false (row, x)) (hxm : x < e.p)
    (h : ∀ y < e.p * rbaPack, row'[y]! = if y / rbaPack < x +
      (ForIn.toList [0:e.factors[i]!.modulus]).length then productWord e frows (i + 1) y
      else productWord e frows i y) :
    e.p - (x + e.factors[i]!.modulus) < mb ∧
      FactorInvariant e frows i false (row', x + e.factors[i]!.modulus) := by
  have hil := Std.Legacy.Range.lt_of_toList_eq_append_cons hl'
  have hq := pre.1 i hil
  have hx0 : x % e.factors[i]!.modulus = 0 := hinv.2.1
  have hxq := Nat.le_of_lt_add_of_dvd (Nat.add_lt_add_right hxm _)
    (Nat.dvd_add (Nat.dvd_of_mod_eq_zero hx0) (Nat.dvd_refl _)) hq.2
  refine ⟨by lia, by rw [Nat.add_mod_right]; exact hx0, hxq, nofun, fun y hy ↦ ?_⟩
  simpa using h y hy

theorem FactorInvariant.exit {e : SieveEntry} {frows : Array (Array UInt64)} {n i x mb : Nat}
    {row : Vector UInt64 n} (h : e.p - x = mb ∧ FactorInvariant e frows i false (row, x))
    (hxm : ¬x < e.p) : FactorInvariant e frows i true (row, x) :=
  ⟨h.2.1, h.2.2.1, fun _ ↦ by lia, h.2.2.2.2⟩

theorem FactorInvariant.next {e : SieveEntry} {frows : Array (Array UInt64)} {n i x : Nat}
    {pref suff : List Nat} {row : Vector UInt64 n}
    (hl : ForIn.toList [1:e.factors.length] = pref ++ i :: suff)
    (h : FactorInvariant e frows i true (row, x)) :
    ∀ y < e.p * rbaPack, row[y]! = productWord e frows (1 + (pref ++ [i]).length) y := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  obtain ⟨-, hx, hex, hr⟩ := h
  obtain rfl : x = e.p := Nat.le_antisymm hx (hex rfl)
  intro y hy
  have := (Nat.div_lt_iff_lt_mul rbaPack_pos).mpr hy
  rw [hr y hy, ite_eq_left (by lia), List.length_append, List.length_singleton, ← Nat.add_assoc, hc]

theorem productAnd_post {e : SieveEntry} {frows : Array (Array UInt64)} {n : Nat}
    {row : Vector UInt64 n}
    (h : ∀ y < e.p * rbaPack,
      row[y]! = productWord e frows (1 + (ForIn.toList [1:e.factors.length]).length) y)
    {y : Nat} (hy : y < e.p * rbaPack) : row[y]! = productWord e frows e.factors.length y := by
  rw [h y hy, Std.Legacy.Range.length_toList]
  rcases Nat.eq_zero_or_pos e.factors.length with h0 | h0
  · rw [h0]
    rfl
  · congr 1
    lia

attribute [local irreducible] FactorInvariant productWord factorWord Sieve.andBitArray in
open Std.WP Lean.Order in
/-- The rows of the factors `i ≥ 1` of the product `e`, each of a positive modulus `q ∣ m = e.p`,
and-ed into the row in the blocks of their lengths: from the row of the first factor laid down,
word `y < m rbaPack` of the row is the and of the words of all the factors read in their blocks
(`Ratpoints.Sieve.productWord`). -/
@[spec]
theorem productAnd_spec {n : Nat} (row : Vector UInt64 n) (e : SieveEntry)
    (frows : Array (Array UInt64)) :
    ⦃ (∀ i < e.factors.length, 0 < e.factors[i]!.modulus ∧ e.factors[i]!.modulus ∣ e.p) ∧
        e.p * rbaPack ≤ n ∧ ∀ y < e.p * rbaPack, row[y]! = factorWord e frows 0 y ⦄
    productAnd row e frows
    ⦃ fun row' ↦ ∀ y < e.p * rbaPack, row'[y]! = productWord e frows e.factors.length y ⦄ := by
  vcgen [productAnd] invariants
  | inv1 => fun done _ row ↦ ∀ y < e.p * rbaPack, row[y]! = productWord e frows (1 + done.length) y
  | inv2 _ _ i _ _ _ _ => FactorInvariant e frows i
  | inv3 => Variant.ofMeasure fun s : Vector UInt64 n × Nat ↦ e.p - s.2
  | inv4 _ _ i _ _ _ _ _ x _ _ _ => fun done _ row ↦ ∀ y < e.p * rbaPack, row[y]! =
      if y / rbaPack < x + done.length then productWord e frows (i + 1) y
      else productWord e frows i y
  all_goals try simp only [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
    Variant.evalsBelow_ofMeasure_nat, meet_prop_eq_and, ofProp_prop_eq] at *
  all_goals first
    | exact productAnd_init ‹_› ‹_›
    | exact productAnd_post ‹_› ‹_›
    | exact factorInvariant_init ‹_› ‹_›
    | exact FactorInvariant.next ‹_› ‹_›
    | exact FactorInvariant.inner ‹_› _ ‹_›
    | exact FactorInvariant.exit ‹_› ‹_›
    | exact FactorInvariant.add ‹_› ‹_› ‹_› ‹_› ‹_›
    | with_reducible exact FactorInvariant.andBitArray ‹_› ‹_› ‹_› ‹_› ‹_›

/-! ### The closed form of the rows of a product -/

theorem Factor.admits_congr (f : Factor) (b : Nat) {a a' : Int}
    (h : a % (f.modulus : Int) = a' % (f.modulus : Int)) : f.admits b a = f.admits b a' := by
  cases f with
  | prime t => simp only [Factor.modulus] at h; simp [Factor.admits, Entry.admits, h]
  | power pw => simp only [Factor.modulus] at h; simp [Factor.admits, Power.admits, h]

theorem Factor.admits_mod_left (f : Factor) (b : Nat) (a : Int) :
    f.admits (b % f.modulus) a = f.admits b a := by
  cases f <;> simp [Factor.admits, Factor.modulus, Entry.admits, Power.admits]

theorem Factor.admits_mod_of_dvd (f : Factor) {m : Nat} (h : f.modulus ∣ m) (b : Nat) (a : Int) :
    f.admits (b % m) (a % m) = f.admits b a := by
  cases f with
  | prime t => exact Entry.admits_mod_of_dvd t h b a
  | power pw => exact Power.admits_mod_of_dvd pw h b a

/-- A sieve entry whose one factor `f` has the modulus of the entry, as a prime or a prime power is
its own factor (`Ratpoints.makeModulus?`), has the row of the factor. -/
theorem SieveEntry.admits_eq_of_factors_eq {e : SieveEntry} {f : Factor} (he : e.factors = [f])
    (hp : e.p = f.modulus) : e.admits = f.admits :=
  funext fun b ↦ funext fun a ↦ by
    rw [SieveEntry.admits, he, List.all_cons, List.all_nil, Bool.and_true, hp,
      Factor.admits_mod_of_dvd f (Nat.dvd_refl _)]

-- The bits of the words of a row in the blocks of the length `q`: word `j` read at bit array
-- `⌊j / rbaPack⌋ mod q` has the numerators of word `j`, modulo `q`.
private theorem rbaPack_mul_mod_add_mod_eq (q y t : Nat) :
    (64 * (rbaPack * (y / rbaPack % q) + y % rbaPack) + t) % q = (64 * y + t) % q := by
  have hd := Nat.div_add_mod (y / rbaPack) q
  have hy := Nat.div_add_mod y rbaPack
  have : 64 * y + t = 64 * (rbaPack * (y / rbaPack % q) + y % rbaPack) + t +
      q * (64 * rbaPack * (y / rbaPack / q)) := by
    generalize y / rbaPack / q = a at hd
    generalize y / rbaPack % q = c at hd
    generalize y % rbaPack = w at hy
    generalize y / rbaPack = z at hd hy
    subst hy hd
    grind
  rw [this, Nat.add_mul_mod_self_left]

/-- Bit `t` of word `y` of the row of the residue `b mod q` of factor `i` of a product, in closed
form, read in the blocks of the length `q` of its modulus: whether the factor admits `64 y + t`. -/
theorem getLsbD_factorWord {e : SieveEntry} {frows : Array (Array UInt64)} {b i : Nat}
    (hq : 0 < e.factors[i]!.modulus)
    (hf : frows[i]! = closedRow e.factors[i]!.admits e.factors[i]!.modulus
      (b % e.factors[i]!.modulus)) (y t : Nat) :
    (factorWord e frows i y).toBitVec.getLsbD t =
      (decide (t < 64) && e.factors[i]!.admits b (64 * y + t)) := by
  have hj : rbaPack * (y / rbaPack % e.factors[i]!.modulus) + y % rbaPack <
      (e.factors[i]!.modulus + chunk - 1) * rbaPack :=
    Nat.lt_of_lt_of_le (rbaPack_mul_add_lt (Nat.mod_lt _ hq) (Nat.mod_lt _ rbaPack_pos))
      (Nat.mul_le_mul_right _ (by lia [chunk_pos]))
  rw [factorWord, hf, getLsbD_closedRow _ _ _ hj, Factor.admits_mod_left]
  congr 1
  refine Factor.admits_congr _ _ ?_
  have := rbaPack_mul_mod_add_mod_eq e.factors[i]!.modulus y t
  push_cast at this ⊢
  exact_mod_cast this

theorem getLsbD_productWord (e : SieveEntry) (frows : Array (Array UInt64)) {K : Nat} (hK : 1 ≤ K)
    (y t : Nat) : (productWord e frows K y).toBitVec.getLsbD t =
      (List.range K).all fun i ↦ (factorWord e frows i y).toBitVec.getLsbD t := by
  obtain ⟨K, rfl⟩ : ∃ k, K = k + 1 := ⟨K - 1, by lia⟩
  rw [productWord, UInt64.getLsbD_foldl_and, List.range_eq_range', List.range'_succ]
  simp

/-- The row of a sieve entry whose factors have moduli dividing its modulus admits a numerator when
each factor does, the factors reading the residues modulo their own moduli. -/
theorem SieveEntry.admits_eq_all {e : SieveEntry} (h : ∀ f ∈ e.factors, f.modulus ∣ e.p) (b : Nat)
    (a : Int) : e.admits b a = e.factors.all (·.admits b a) := by
  rw [SieveEntry.admits, Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  constructor <;> intro hf f hmem
  · rw [← Factor.admits_mod_of_dvd f (h f hmem)]
    exact hf f hmem
  · rw [Factor.admits_mod_of_dvd f (h f hmem)]
    exact hf f hmem

/-- The row of a product whose words are those of the rows of its factors, in closed form at the
residue `b` modulo their moduli, and-ed in the blocks of their lengths and repeated after the first
`m` bit arrays, is the closed form of the row of `b` of the product: the moduli of the factors
divide `m`, so each factor reads the numerators modulo its own modulus. -/
theorem toArray_eq_closedRow_of_productWord {e : SieveEntry} {frows : Array (Array UInt64)}
    {b : Nat} {row : Vector UInt64 ((e.p + chunk - 1) * rbaPack)} (hL : 1 ≤ e.factors.length)
    (hq : ∀ i < e.factors.length, 0 < e.factors[i]!.modulus ∧ e.factors[i]!.modulus ∣ e.p)
    (hf : ∀ i < e.factors.length, frows[i]! =
      closedRow e.factors[i]!.admits e.factors[i]!.modulus (b % e.factors[i]!.modulus))
    (hrow : ∀ y < (e.p + chunk - 1) * rbaPack,
      row[y]! = productWord e frows e.factors.length (y % (e.p * rbaPack))) :
    row.toArray = closedRow e.admits e.p b := by
  have hdvd : ∀ f ∈ e.factors, f.modulus ∣ e.p := fun f hf ↦ by
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hf
    simpa [getElem!_pos e.factors i hi] using (hq i hi).2
  refine eq_closedRow (by simp) fun j hj t ↦ ?_
  rw [Vector.getElem!_toArray, hrow j hj, getLsbD_productWord _ _ hL,
    SieveEntry.admits_eq_all hdvd, ← List.all_range_length_getElem! e.factors,
    ← List.all_and_left (List.ne_nil_of_length_pos (by rw [List.length_range]; lia))]
  refine List.all_congr_left fun i hi ↦ ?_
  replace hi := List.mem_range.mp hi
  rw [getLsbD_factorWord (hq i hi).1 (hf i hi)]
  congr 1
  refine Factor.admits_congr _ _ ?_
  have hm : e.factors[i]!.modulus ∣ e.p * rbaPack := Nat.dvd_mul_right_of_dvd (hq i hi).2 _
  have : (64 * (j % (e.p * rbaPack)) + t) % e.factors[i]!.modulus =
      (64 * j + t) % e.factors[i]!.modulus := by
    rw [Nat.add_mod, Nat.mul_mod, Nat.mod_mod_of_dvd _ hm, ← Nat.mul_mod, ← Nat.add_mod]
  push_cast at this ⊢
  exact_mod_cast this

end Sieve

end Ratpoints

end
