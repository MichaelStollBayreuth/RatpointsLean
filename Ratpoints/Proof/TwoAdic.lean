/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Defs
public import Ratpoints.Model.Denominators
public import Ratpoints.Proof.Words
public import Ratpoints.Spec.Basic

import Mathlib.Data.Fintype.Parity
import Ratpoints.Mathlib.Data.Int.GCD
import Ratpoints.Mathlib.Data.ZMod.Basic
import Ratpoints.Proof.Bits
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Tables
import Std.Tactic.Do

/-!
# The 2-adic information

The words of the classes of the denominators modulo 64 (`Ratpoints.Sieve.twoAdic`) let the numerator
of every point through, and the word of the classes that admit a numerator
(`Ratpoints.Sieve.denBits`) has the bit of every class whose word is not `0`. The mask of the
squares modulo 64 is checked by `decide`; Horner's rule on words is exact modulo `2 ^ 64` and so
modulo 64, so that the word of `f` (`Ratpoints.Sieve.fsq`) has bit `k` set exactly when `f(k)` is a
square modulo 64, and the word of the reversed polynomial (`Ratpoints.Sieve.gsq`) bit `t` for the
even `t` at which it takes a square value; the loops of `Ratpoints.Sieve.twoAdic` scatter these bits
into the words of the classes. A point `(a, y, b)` with odd `b` has `a ≡ k b (mod 64)` for a `k`
with `f(k)` a square, since `F(a, b) = b ^ D f(k)` modulo 64, and one with even `b` an odd `a` and
`b ≡ t a (mod 64)` for an even `t` at which the reversed polynomial takes a square value; so when
no class admits a numerator, the curve has no points at all, not even at infinity
(`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`).

## Main definitions

* `Ratpoints.Sieve.TwoAdicBits`: the bits of the words of the classes after the scatter of the set
  bits `k < k0` of the word of `f` into the odd classes and of the set bits `t < t0` of the word of
  the reversed polynomial into the even ones, the postcondition of `Ratpoints.Sieve.twoAdic_spec`
  for `k0 = t0 = 64`.

## Main statements

* `Ratpoints.Sieve.squares64_test_iff`: the test of the mask `Ratpoints.Sieve.squares64` is the test
  of the squares modulo 64.
* `Ratpoints.Sieve.getLsbD_fsq_coeffsMod64`, `Ratpoints.Sieve.getLsbD_gsq_coeffsMod64`: the bits of
  the words of `f` and of the reversed polynomial.
* `Ratpoints.Sieve.twoAdic_spec`: bit `a` of the word of the class `b < 64` is set exactly when `b`
  is odd and `a ≡ k b` for a set bit `k` of the word of `f`, or `a < 64` is odd and `b ≡ t a` for a
  set bit `t` of the word of the reversed polynomial; `Ratpoints.Sieve.getLsbD_run_twoAdic` states
  this as a plain statement.
* `Ratpoints.Sieve.classBit_twoAdic_of_sq_eq`: for a point `(a, y, b)`, bit `a mod 64` of the word
  of the class `b mod 64` is set; `Ratpoints.Sieve.getElem!_twoAdic_ne_zero`: so the word of the
  class of the denominator of a point is not `0`.
* `Ratpoints.Sieve.getLsbD_denBits`: bit `j` of `Ratpoints.Sieve.denBits nb` says whether `nb[j]`
  is not `0`.
* `Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`: when no class of the denominators admits a
  numerator, the curve has no points, so that the 2-adic exit of the search is sound.

## Implementation notes

The square values that a point gives in a commutative ring
(`Ratpoints.isSquare_sum_mul_pow_of_sq_eq_binaryForm`,
`Ratpoints.isSquare_sum_mul_pow_sub_of_sq_eq_binaryForm`) are stated in `Ratpoints.Proof.Tables`,
where the square value modulo a prime follows from the first.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The squares modulo 64 and Horner's rule on words -/

theorem squares64_test_iff_of_lt {x : ℕ} (hx : x < 64) :
    ((squares64 >>> UInt64.ofNat x) &&& 1 != 0) = true ↔ IsSquare (x : ZMod 64) := by
  revert x
  decide

/-- The test of the mask of the squares modulo 64 (`Ratpoints.Sieve.squares64`) on the residue
`s mod 64` of a word, as `Ratpoints.Sieve.fsq` and `Ratpoints.Sieve.gsq` make it, is the test of
the squares modulo 64, which `decide` checks for each residue. -/
theorem squares64_test_iff (s : UInt64) :
    ((squares64 >>> (s &&& 0x3f)) &&& 1 != 0) = true ↔ IsSquare (s.toNat : ZMod 64) := by
  have h63 : (0x3f : UInt64).toNat = 2 ^ 6 - 1 := rfl
  have h : s &&& 0x3f = UInt64.ofNat (s.toNat % 64) := by
    apply UInt64.toNat_inj.mp
    rw [UInt64.toNat_and, h63, Nat.and_two_pow_sub_one_eq_mod, UInt64.toNat_ofNat']
    lia
  rw [h, squares64_test_iff_of_lt (Nat.mod_lt _ (by decide)), ZMod.natCast_mod]

/-- Horner's rule on words from the last entry of `l` down, as `Ratpoints.Sieve.fsq` evaluates `f`,
read modulo 64. -/
theorem natCast_toNat_foldr (l : List UInt64) (x : UInt64) :
    ((l.foldr (fun a s ↦ s * x + a) 0).toNat : ZMod 64) =
      ∑ i ∈ Finset.range l.length, ((l.getD i 0).toNat : ZMod 64) * (x.toNat : ZMod 64) ^ i := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.foldr_cons, UInt64.natCast_toNat_mul_add (by decide), ih, List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_succ, pow_zero, mul_one,
      Finset.sum_mul, mul_assoc]

/-- Horner's rule on words from the first entry of `l` on and from the value `s`, as
`Ratpoints.Sieve.gsq` evaluates the reversed polynomial, read modulo 64. -/
theorem natCast_toNat_foldl (l : List UInt64) (x s : UInt64) :
    ((l.foldl (fun s a ↦ s * x + a) s).toNat : ZMod 64) =
      (s.toNat : ZMod 64) * x.toNat ^ l.length + ∑ i ∈ Finset.range l.length,
        ((l.getD i 0).toNat : ZMod 64) * (x.toNat : ZMod 64) ^ (l.length - 1 - i) := by
  induction l generalizing s with
  | nil => simp
  | cons a l ih =>
    rw [List.foldl_cons, ih, UInt64.natCast_toNat_mul_add (by decide), List.length_cons,
      Finset.sum_range_succ']
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_sub_cancel, Nat.sub_zero,
      Nat.sub_sub, Nat.add_comm 1]
    ring

/-! ### The words of `f` and of the reversed polynomial -/

theorem length_toList_coeffsMod64 (c : List ℤ) (d : ℕ) :
    (coeffsMod64 c d).toList.length = d + d % 2 + 1 := by
  simp [coeffsMod64]

theorem natCast_toNat_getD_coeffsMod64 (c : List ℤ) (d i : ℕ) :
    (((coeffsMod64 c d).toList.getD i 0).toNat : ZMod 64) =
      if i ≤ d then (c.getD i 0 : ZMod 64) else 0 := by
  rw [List.getD_eq_getElem?_getD]
  by_cases hi : i < d + d % 2 + 1
  · have h64 : (c.getD i 0 % 64).toNat < 2 ^ 64 := by lia
    simp only [coeffsMod64, Array.toList_map, Array.toList_range, List.getElem?_map,
      List.getElem?_range hi, Option.map_some, Option.getD_some]
    split
    · rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' h64]
      simpa using ZMod.natCast_toNat_emod (n := 64) (c.getD i 0)
    · rfl
  · rw [List.getElem?_eq_none (by simpa [coeffsMod64] using hi)]
    simp [show ¬i ≤ d by lia]

-- A sum over the `D + 1` coefficients modulo 64, the last one zero for odd `d`.
theorem sum_range_coeffsMod64 (c : List ℤ) (d : ℕ) (g : ℕ → ZMod 64) :
    ∑ i ∈ Finset.range (d + d % 2 + 1),
        (((coeffsMod64 c d).toList.getD i 0).toNat : ZMod 64) * g i =
      ∑ i ∈ Finset.range (d + 1), (c.getD i 0 : ZMod 64) * g i := by
  rw [show d + d % 2 + 1 = d + 1 + d % 2 by lia, Finset.sum_range_add,
    Finset.sum_eq_zero (s := Finset.range (d % 2)) fun i _ ↦ by
      rw [natCast_toNat_getD_coeffsMod64]
      simp only [show ¬d + 1 + i ≤ d by lia, ↓reduceIte, zero_mul], add_zero]
  exact Finset.sum_congr rfl fun i hi ↦ by
    rw [natCast_toNat_getD_coeffsMod64]
    simp only [show i ≤ d by simpa [Nat.lt_succ_iff] using hi, ↓reduceIte]

/-- Bit `k` of the word of `f` (`Ratpoints.Sieve.fsq`) for the coefficients modulo 64 is set
exactly when `k < 64` and `f(k) = ∑ cᵢ kⁱ` is a square modulo 64. -/
theorem getLsbD_fsq_coeffsMod64 (c : List ℤ) (d k : ℕ) :
    (fsq (coeffsMod64 c d)).toBitVec.getLsbD k = true ↔ k < 64 ∧
      IsSquare (∑ i ∈ Finset.range (d + 1), (c.getD i 0 : ZMod 64) * (k : ZMod 64) ^ i) := by
  rw [fsq, UInt64.getLsbD_fold_or_one_shiftLeft _ (Nat.le_refl 64), Bool.and_eq_true,
    decide_eq_true_iff]
  refine and_congr_right fun hk ↦ ?_
  rw [squares64_test_iff, ← Array.foldr_toList, natCast_toNat_foldr, length_toList_coeffsMod64,
    Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by lia), sum_range_coeffsMod64]

/-- Bit `t` of the word of the reversed polynomial (`Ratpoints.Sieve.gsq`) for the coefficients
modulo 64 is set exactly when `t < 64` is even and `∑ cᵢ t^(D - i)` is a square modulo 64, for
`D = d + d % 2`. -/
theorem getLsbD_gsq_coeffsMod64 (c : List ℤ) (d t : ℕ) :
    (gsq (coeffsMod64 c d)).toBitVec.getLsbD t = true ↔ t < 64 ∧ t % 2 = 0 ∧
      IsSquare (∑ i ∈ Finset.range (d + 1),
        (c.getD i 0 : ZMod 64) * (t : ZMod 64) ^ (d + d % 2 - i)) := by
  have h : gsq (coeffsMod64 c d) = Nat.fold 32 (fun i _ w ↦ if decide (IsSquare
      (∑ j ∈ Finset.range (d + 1), (c.getD j 0 : ZMod 64) * ((2 * i : ℕ) : ZMod 64) ^
        (d + d % 2 - j))) then w ||| (1 : UInt64) <<< (2 * i).toUInt64 else w) 0 := by
    simp only [gsq]
    congr
    funext i hi w
    refine if_congr ?_ rfl rfl
    rw [decide_eq_true_iff, squares64_test_iff, ← Array.foldl_toList, natCast_toNat_foldl,
      length_toList_coeffsMod64, UInt64.toNat_zero, Nat.cast_zero, zero_mul, zero_add,
      Nat.add_sub_cancel, Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' (by lia),
      sum_range_coeffsMod64]
  rw [h, UInt64.getLsbD_fold_or_one_shiftLeft_comp _ (2 * ·) fun i hi ↦ by lia,
    decide_eq_true_iff]
  constructor
  · rintro ⟨i, hi, hc, rfl⟩
    exact ⟨by lia, by lia, by simpa using hc⟩
  · intro ⟨ht, ht2, hsq⟩
    exact ⟨t / 2, by lia, by simpa [show 2 * (t / 2) = t by lia] using hsq, by lia⟩

/-! ### The scatter -/

/-- The bits of the words `nb` of the classes after the scatter of the set bits `k < k0` of `f` into
the odd classes and of the set bits `t < t0` of `g` into the even ones: bit `a` of the word of the
class `b < 64` is set exactly when `b` is odd and `a = k b mod 64` for a set bit `k < k0` of `f`, or
`a < 64` is odd and `b = t a mod 64` for a set bit `t < t0` of `g`. -/
def TwoAdicBits (f g : UInt64) (k0 t0 : ℕ) (nb : Vector UInt64 64) : Prop :=
  ∀ b < 64, ∀ a, nb[b]!.toBitVec.getLsbD a = true ↔
    (b % 2 = 1 ∧ ∃ k < k0, f.toBitVec.getLsbD k = true ∧ k * b % 64 = a) ∨
      (a % 2 = 1 ∧ a < 64 ∧ ∃ t < t0, g.toBitVec.getLsbD t = true ∧ t * a % 64 = b)

/-- The invariant of the loop of `Ratpoints.Sieve.twoAdic` that scatters the bit `k` of `f` into the
odd classes, from the words `nb0`: after the classes `1, 3, …` of the positions `pref`, the words
are those of `nb0` with bit `k b mod 64` set in the word of each of these classes `b`. -/
def ScatterOddInvariant (nb0 : Vector UInt64 64) (k : ℕ) (pref : List ℕ)
    (nb : Vector UInt64 64) : Prop :=
  ∀ b < 64, ∀ a, nb[b]!.toBitVec.getLsbD a = true ↔
    nb0[b]!.toBitVec.getLsbD a = true ∨ (b % 2 = 1 ∧ b < 2 * pref.length ∧ k * b % 64 = a)

/-- The invariant of the loop of `Ratpoints.Sieve.twoAdic` that scatters the bit `t` of `g` into the
even classes, from the words `nb0`: after the numerators `1, 3, …` of the positions `pref`, the
words are those of `nb0` with bit `a` set in the word of the class `t a mod 64` of each of them. -/
def ScatterEvenInvariant (nb0 : Vector UInt64 64) (t : ℕ) (pref : List ℕ)
    (nb : Vector UInt64 64) : Prop :=
  ∀ b < 64, ∀ a, nb[b]!.toBitVec.getLsbD a = true ↔
    nb0[b]!.toBitVec.getLsbD a = true ∨ (a % 2 = 1 ∧ a < 2 * pref.length ∧ t * a % 64 = b)

theorem twoAdicBits_replicate_zero (f g : UInt64) : TwoAdicBits f g 0 0 (Vector.replicate 64 0) :=
  fun b hb a ↦ by simp [hb]

/-- At the exit of the loop over the set bits of `f`, all of them are scattered into the odd
classes. -/
theorem twoAdicBits_of_walkWhileInvariant_left {f g w : UInt64} {nb : Vector UInt64 64}
    (h : WalkWhileInvariant f (fun k0 ↦ TwoAdicBits f g k0 0) true (nb, w)) :
    TwoAdicBits f g 64 0 nb := by
  obtain ⟨k0, hk, hbits⟩ := h.exists_clearedBelow_zero
  intro b hb a
  rw [hbits b hb a, hk.exists_lt_iff_of_eq_zero]

/-- At the exit of the loop over the set bits of `g`, all of them are scattered into the even
classes. -/
theorem twoAdicBits_of_walkWhileInvariant_right {f g w : UInt64} {nb : Vector UInt64 64}
    (h : WalkWhileInvariant g (TwoAdicBits f g 64) true (nb, w)) :
    TwoAdicBits f g 64 64 nb := by
  obtain ⟨t0, ht, hbits⟩ := h.exists_clearedBelow_zero
  intro b hb a
  rw [hbits b hb a, ht.exists_lt_iff_of_eq_zero]

theorem scatterOddInvariant_nil (nb : Vector UInt64 64) (k : ℕ) :
    ScatterOddInvariant nb k [] nb := by
  simp [ScatterOddInvariant]

theorem scatterEvenInvariant_nil (nb : Vector UInt64 64) (t : ℕ) :
    ScatterEvenInvariant nb t [] nb := by
  simp [ScatterEvenInvariant]

theorem ScatterOddInvariant.set! {nb0 nb : Vector UInt64 64} {k : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:32] = pref ++ cur :: suff)
    (h : ScatterOddInvariant nb0 k pref nb) :
    ScatterOddInvariant nb0 k (pref ++ [cur])
      (nb.set! (2 * cur + 1)
        (nb[2 * cur + 1]! ||| 1 <<< UInt64.ofNat (k * (2 * cur + 1) % 64))) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  intro b hb a
  rw [Vector.getElem!_set! hb]
  split
  · rw [UInt64.getLsbD_or_one_shiftLeft _ (Nat.mod_lt _ (by decide)), Bool.or_eq_true,
      h _ (by lia)]
    grind
  · rw [h b hb a]
    grind

theorem ScatterEvenInvariant.set! {nb0 nb : Vector UInt64 64} {t : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (hl : ForIn.toList [:32] = pref ++ cur :: suff)
    (h : ScatterEvenInvariant nb0 t pref nb) :
    ScatterEvenInvariant nb0 t (pref ++ [cur])
      (nb.set! (t * (2 * cur + 1) % 64)
        (nb[t * (2 * cur + 1) % 64]! ||| 1 <<< UInt64.ofNat (2 * cur + 1))) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  intro b hb a
  rw [Vector.getElem!_set! hb]
  split
  · rw [UInt64.getLsbD_or_one_shiftLeft _ (by lia), Bool.or_eq_true, h _ (by lia)]
    grind
  · rw [h b hb a]
    grind

/-- The scatter of the lowest set bit `k` of `w` into the odd classes, for a word `w` with the bits
of `f` from `k0` on: the bits of the set bits of `f` below `k0` become those of its set bits up to
`k`. -/
theorem TwoAdicBits.of_scatterOddInvariant {f g w : UInt64} {nb0 nb : Vector UInt64 64}
    {k k0 : ℕ} (hw : (w != 0) = true) (hk : k = w.toBitVec.ctz.toNat)
    (hs : ScatterOddInvariant nb0 k (ForIn.toList [:32]) nb) (hcl : ClearedBelow f k0 w)
    (h : TwoAdicBits f g k0 0 nb0) :
    TwoAdicBits f g (w.toBitVec.ctz.toNat + 1) 0 nb := by
  intro b hb a
  rw [hs b hb a, h b hb a, Std.Legacy.Range.length_toList, Nat.sub_zero, hk,
    hcl.exists_lt_succ_iff (by simpa using hw) fun k' ↦ k' * b % 64 = a]
  grind

/-- The scatter of the lowest set bit `t` of `w` into the even classes, for a word `w` with the bits
of `g` from `t0` on: the bits of the set bits of `g` below `t0` become those of its set bits up to
`t`. -/
theorem TwoAdicBits.of_scatterEvenInvariant {f g w : UInt64} {nb0 nb : Vector UInt64 64}
    {t t0 : ℕ} (hw : (w != 0) = true) (ht : t = w.toBitVec.ctz.toNat)
    (hs : ScatterEvenInvariant nb0 t (ForIn.toList [:32]) nb) (hcl : ClearedBelow g t0 w)
    (h : TwoAdicBits f g 64 t0 nb0) :
    TwoAdicBits f g 64 (w.toBitVec.ctz.toNat + 1) nb := by
  intro b hb a
  rw [hs b hb a, h b hb a, Std.Legacy.Range.length_toList, Nat.sub_zero, ht,
    hcl.exists_lt_succ_iff (by simpa using hw) fun t' ↦ t' * a % 64 = b]
  grind

section

/- The invariants are irreducible here: the verification conditions of `Ratpoints.Sieve.twoAdic`
are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] TwoAdicBits ClearedBelow WalkWhileInvariant ScatterOddInvariant
  ScatterEvenInvariant

/-- The loops over the set bits end, since clearing the lowest set bit makes a word other than `0`
smaller. -/
@[spec]
theorem twoAdic_spec (c : List ℤ) (d : ℕ) :
    ⦃ True ⦄ twoAdic c d
    ⦃ fun nb ↦ TwoAdicBits (fsq (coeffsMod64 c d)) (gsq (coeffsMod64 c d)) 64 64 nb ⦄ := by
  vcgen [twoAdic] invariants
  | inv1 => WalkWhileInvariant (fsq (coeffsMod64 c d))
      fun k0 ↦ TwoAdicBits (fsq (coeffsMod64 c d)) (gsq (coeffsMod64 c d)) k0 0
  | inv2 => .ofMeasure fun s : Vector UInt64 64 × UInt64 ↦ s.2.toNat
  | inv3 => WalkWhileInvariant (gsq (coeffsMod64 c d))
      (TwoAdicBits (fsq (coeffsMod64 c d)) (gsq (coeffsMod64 c d)) 64)
  | inv4 => .ofMeasure fun s : Vector UInt64 64 × UInt64 ↦ s.2.toNat
  | inv5 nb _ _ _ _ _ => fun pref _ nb' ↦ ScatterEvenInvariant nb t pref nb'
  | inv6 nb _ _ _ _ _ => fun pref _ nb' ↦ ScatterOddInvariant nb k pref nb'
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals solve_by_elim (maxDepth := 10) [walkWhileInvariant_self, twoAdicBits_replicate_zero,
    twoAdicBits_of_walkWhileInvariant_left, twoAdicBits_of_walkWhileInvariant_right,
    scatterOddInvariant_nil, scatterEvenInvariant_nil, WalkWhileInvariant.and_sub_one,
    TwoAdicBits.of_scatterOddInvariant, TwoAdicBits.of_scatterEvenInvariant,
    ScatterOddInvariant.set!, ScatterEvenInvariant.set!, WalkWhileInvariant.exit, bne_iff_ne.mp]

end

/-- `Ratpoints.Sieve.twoAdic_spec` as a plain statement, which the soundness of the classes uses
without the program logic. -/
theorem getLsbD_run_twoAdic (c : List ℤ) (d : ℕ) {b : ℕ} (hb : b < 64) (a : ℕ) :
    (Id.run (twoAdic c d))[b]!.toBitVec.getLsbD a = true ↔
      (b % 2 = 1 ∧ ∃ k < 64, (fsq (coeffsMod64 c d)).toBitVec.getLsbD k = true ∧ k * b % 64 = a) ∨
        (a % 2 = 1 ∧ a < 64 ∧
          ∃ t < 64, (gsq (coeffsMod64 c d)).toBitVec.getLsbD t = true ∧ t * a % 64 = b) :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((twoAdic_spec c d).le_wp trivial) :
    TwoAdicBits (fsq (coeffsMod64 c d)) (gsq (coeffsMod64 c d)) 64 64 (Id.run (twoAdic c d))) b hb a

/-! ### The classes of a point -/

/-- A point `(a, y, b)` with odd `b` has `a ≡ k b (mod 64)` for a set bit `k` of the word of `f`
(`Ratpoints.Sieve.fsq`), since `f(k)` is a square modulo 64
(`Ratpoints.isSquare_sum_mul_pow_of_sq_eq_binaryForm`). -/
theorem exists_getLsbD_fsq_of_sq_eq {c : List ℤ} {a y : ℤ} {b : ℕ} (hb : b % 2 = 1)
    (hy : y ^ 2 = binaryForm c a b) :
    ∃ k < 64, (fsq (coeffsMod64 c (degree c))).toBitVec.getLsbD k = true ∧
      k * (b % 64) % 64 = (a % 64).toNat := by
  obtain ⟨u, hu⟩ : IsUnit (b : ZMod 64) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow (d := 6) Nat.prime_two (by decide)).mpr (by lia)
  have hk : (a : ZMod 64) = (a * ↑u⁻¹ : ZMod 64) * b := by
    rw [← hu, mul_assoc, Units.inv_mul, mul_one]
  refine ⟨(a * ↑u⁻¹ : ZMod 64).val, ZMod.val_lt _, (getLsbD_fsq_coeffsMod64 _ _ _).mpr
    ⟨ZMod.val_lt _, ?_⟩,
    ((ZMod.natCast_eq_natCast_iff' _ _ _).mp ?_).trans (Nat.mod_eq_of_lt (by lia))⟩
  · rw [ZMod.natCast_zmod_val]
    exact isSquare_sum_mul_pow_of_sq_eq_binaryForm ⟨u, hu⟩ hk hy
  · rw [Nat.cast_mul, ZMod.natCast_zmod_val, ZMod.natCast_mod, ← hk]
    simpa using (ZMod.natCast_toNat_emod (n := 64) a).symm

/-- A point `(a, y, b)` with even `b` has an odd `a`, since `gcd(a, b) = 1`, and `b ≡ t a (mod 64)`
for a set bit `t` of the word of the reversed polynomial (`Ratpoints.Sieve.gsq`), since it takes a
square value at `t` (`Ratpoints.isSquare_sum_mul_pow_sub_of_sq_eq_binaryForm`). -/
theorem exists_getLsbD_gsq_of_sq_eq {c : List ℤ} {a y : ℤ} {b : ℕ} (hb : b % 2 = 0)
    (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    (a % 64).toNat % 2 = 1 ∧ (a % 64).toNat < 64 ∧
      ∃ t < 64, (gsq (coeffsMod64 c (degree c))).toBitVec.getLsbD t = true ∧
        t * (a % 64).toNat % 64 = b % 64 := by
  have ha2 := Int.emod_two_eq_one_of_gcd_eq_one (by lia) hab
  have key : ((a % 64).toNat : ZMod 64) = a := by simpa using ZMod.natCast_toNat_emod (n := 64) a
  obtain ⟨u, hu⟩ : IsUnit ((a % 64).toNat : ZMod 64) :=
    (ZMod.isUnit_natCast_iff_not_dvd_pow (d := 6) Nat.prime_two (by decide)).mpr (by lia)
  have ht : (b : ZMod 64) = (b * ↑u⁻¹ : ZMod 64) * a := by
    rw [← key, ← hu, mul_assoc, Units.inv_mul, mul_one]
  have htb : (b * ↑u⁻¹ : ZMod 64).val * (a % 64).toNat % 64 = b % 64 :=
    (ZMod.natCast_eq_natCast_iff' _ _ _).mp (by rw [Nat.cast_mul, ZMod.natCast_zmod_val, key, ← ht])
  have h2 : (b * ↑u⁻¹ : ZMod 64).val * (a % 64).toNat % 2 = b % 2 := by
    rw [← Nat.mod_mod_of_dvd _ (by decide : 2 ∣ 64), htb, Nat.mod_mod_of_dvd _ (by decide)]
  rw [Nat.mul_mod, show (a % 64).toNat % 2 = 1 by lia, hb] at h2
  refine ⟨by lia, by lia, _, ZMod.val_lt _, (getLsbD_gsq_coeffsMod64 _ _ _).mpr ⟨ZMod.val_lt _,
    by simpa using h2, ?_⟩, htb⟩
  rw [ZMod.natCast_zmod_val]
  exact isSquare_sum_mul_pow_sub_of_sq_eq_binaryForm ⟨u, hu.trans key⟩ ht hy

/-- The 2-adic information lets the numerator `a` of every point `(a, y, b)` through the word of the
class `b mod 64`: `a` or `b` is odd, since `gcd(a, b) = 1`, and `F(a, b)` is a square, so a square
modulo 64; neither `b ≥ 1` nor a degree of a given parity is needed. -/
theorem classBit_twoAdic_of_sq_eq {c : List ℤ} {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) :
    classBit (Id.run (twoAdic c (degree c)))[b % 64]! a = true := by
  rw [classBit_eq, getLsbD_run_twoAdic _ _ (Nat.mod_lt _ (by decide))]
  rcases Nat.mod_two_eq_zero_or_one b with hb | hb
  · exact .inr (exists_getLsbD_gsq_of_sq_eq hb hab hy)
  · exact .inl ⟨by lia, exists_getLsbD_fsq_of_sq_eq hb hy⟩

/-- The word of the class of the denominator of a point is not `0`
(`Ratpoints.Sieve.classBit_twoAdic_of_sq_eq`). -/
theorem getElem!_twoAdic_ne_zero {c : List ℤ} {b : ℕ} {xs : List ℤ}
    (h : BruteForce.pointsOfDen c (degree c) b xs ≠ []) :
    (Id.run (twoAdic c (degree c)))[b % 64]! ≠ 0 := by
  obtain ⟨a, -, y, hg, hy⟩ := BruteForce.exists_sq_eq_of_pointsOfDen_ne_nil h
  intro h0
  simpa [h0] using classBit_twoAdic_of_sq_eq hg hy

/-! ### The classes that admit a numerator -/

theorem getLsbD_denBits (nb : Vector UInt64 64) (j : ℕ) :
    (denBits nb).toBitVec.getLsbD j = (decide (j < 64) && nb[j]! != 0) := by
  have h : denBits nb = Nat.fold 64 (fun i _ w ↦
      if nb[i]! != 0 then w ||| (1 : UInt64) <<< i.toUInt64 else w) 0 := by
    simp only [denBits]
    congr
    funext i hi w
    rw [getElem!_pos nb i hi]
  rw [h, UInt64.getLsbD_fold_or_one_shiftLeft _ (Nat.le_refl 64)]

/-! ### The 2-adic exit -/

/-- When no class of the denominators modulo 64 admits a numerator (`Ratpoints.Sieve.denBits`), the
curve has no normalized point of any height, a point at infinity included: the word of the class of
the denominator `b` of a point `(a, y, b)`, `b = 0` included, has bit `a mod 64` set
(`Ratpoints.Sieve.classBit_twoAdic_of_sq_eq`), so the class has its bit in
`Ratpoints.Sieve.denBits` (`Ratpoints.Sieve.getLsbD_denBits`). So the 2-adic exit of the search
needs no test of the points at infinity: no class admits a numerator only for even degree and `c_d`
not a square modulo 64. -/
theorem not_isPoint_of_denBits_eq_zero {c : List ℤ}
    (h : denBits (Id.run (twoAdic c (degree c))) = 0) (H : ℕ) (q : ℤ × ℤ × ℤ) :
    ¬ IsPoint c H q := by
  intro ⟨hy, hg, hz, _⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, q.2.2 = b := ⟨q.2.2.toNat, by lia⟩
  rw [hb] at hy hg
  have hbit := getLsbD_denBits (Id.run (twoAdic c (degree c))) (b % 64)
  rw [h] at hbit
  have h0 : (Id.run (twoAdic c (degree c)))[b % 64]! = 0 := by simpa [Nat.mod_lt] using hbit.symm
  simpa [h0] using classBit_twoAdic_of_sq_eq hg hy

end Sieve

end Ratpoints

end
