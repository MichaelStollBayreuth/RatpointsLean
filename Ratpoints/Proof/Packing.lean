/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Packing
public import Ratpoints.Proof.SetBits
public import Std.WP

import Ratpoints.Proof.Bits
import Std.Tactic.Do

/-!
# The contracts of the packing

The packing of the numerators of each class of the denominators modulo 64 into one class modulo a
power of 2 (`Ratpoints.Model.Packing`), as `@[spec]` theorems proved with `vcgen`, the program logic
of Lean core, with loop invariants that are named definitions. The class of the word `w` of the
admissible numerators modulo 64 of a class of denominators packs it
(`Ratpoints.Sieve.NumClass.Packs`): its stride `2 ^ k` is that of a packing, `k ≤ 6` and
`k < Ratpoints.numStrides`, every set bit of `w` lies in the class `a₀ mod 2 ^ k`, and its pattern
has the bit of the numerator `a₀ + 2 ^ k t` at `t`, so that the class word lets the numerator of a
bit through exactly when the pattern has the bit, and lets nothing off the class through. The loop
over the 64 classes makes such classes, with no row offsets yet, and the word `den_bits` of the
classes whose word is not `0`. The row offsets of the packings read, of each sieve entry, an odd
modulus `1 < p ≤ Ratpoints.maxPrimeEven` with its reciprocal, the inverse of `Ratpoints.rbaLength`
modulo `p` and the bias, the least multiple of `p` from `Ratpoints.rowBias` on, as `examine_prime`,
`make_power` and `make_modulus` set them (`Ratpoints.Sieve.SieveEntry.Packable`); the sieve entry of
a modulus has them (`Ratpoints.makeModulus?_spec`).

## Main definitions

* `Ratpoints.Sieve.NumClass.numerator`: the numerator `a₀ + 2 ^ k j` of bit `j` of a class.
* `Ratpoints.Sieve.NumClass.WF`, `Ratpoints.Sieve.NumClass.Packs`: the stride and the residue of a
  packing, and a class that packs a word of numerators modulo 64.
* `Ratpoints.Sieve.SieveEntry.Packable`: the fields of a sieve entry that the row offsets of the
  packing read.

## Main statements

* `Ratpoints.Sieve.NumClass.Packs.classBit_bits`,
  `Ratpoints.Sieve.NumClass.Packs.emod_eq_of_classBit`,
  `Ratpoints.Sieve.NumClass.Packs.bits_eq_zero_iff`: the pattern lets bit `j` through exactly when
  the word lets the numerator of `j` through, the word lets nothing off the class through, and the
  pattern is `0` exactly when the word is.
* `Ratpoints.Sieve.getLsbD_classMasks`: the masks of the strides, `0` beyond the seven of `k ≤ 6`.
* `Ratpoints.Sieve.packPattern_spec`, `Ratpoints.Sieve.numClasses_spec`: the packed pattern, and the
  classes of the 64 words with `den_bits`.
* `Ratpoints.Sieve.rowBias_le_mul_div_and_mul_div_lt`: the bias of a modulus.

## Implementation notes

The file uses Lean core and `Std` only, so that the contracts of the sieve, in files without
Mathlib, can use it. The proofs use only the facts on the constants that `decide` checks next to
them, never their values: here that `Ratpoints.numStrides ≥ 1`; that the masks of the strides beyond
`k = 6` are `0` is read with the default of the array. The facts on words, natural numbers and
integers that are not about the model are in `Ratpoints.Proof.Bits`.
-/
@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The classes -/

/-- The numerator of bit `j` in the packing of the class `cl`: `a₀ + 2 ^ k j`. -/
def NumClass.numerator (cl : NumClass) (j : Int) : Int := cl.a0 + 2 ^ cl.k * j

/-- The stride and the residue of a class are those of a packing: the stride exponent below
`Ratpoints.numStrides` and at most 6, the residue below the stride. The keys `2 ^ k + a₀` of such
packings are below `2 ^ Ratpoints.numStrides` and 128. -/
structure NumClass.WF (cl : NumClass) : Prop where
  /-- The stride exponent is below `Ratpoints.numStrides`. -/
  k_lt : cl.k < numStrides
  /-- The stride is at most `2 ^ 6`, the modulus 64 of the 2-adic information. -/
  k_le : cl.k ≤ 6
  /-- The residue is below the stride. -/
  a0_lt : cl.a0 < 2 ^ cl.k

/-- The class `cl` packs the word `w` of the numerators modulo 64 of a class of denominators: its
stride and residue are those of a packing (`Ratpoints.Sieve.NumClass.WF`), every set bit `a < 64`
of `w` is `a₀` modulo `2 ^ k`, and bit `t` of the pattern is bit `(a₀ + 2 ^ k t) mod 64` of `w`. -/
structure NumClass.Packs (cl : NumClass) (w : UInt64) : Prop extends cl.WF where
  /-- Every set bit of the word lies in the class `a₀ mod 2 ^ k`. -/
  mod_eq : ∀ a < 64, w.toBitVec.getLsbD a = true → a % 2 ^ cl.k = cl.a0
  /-- Bit `t` of the pattern is the bit of the numerator of bit `t`. -/
  getLsbD_bits : ∀ t < 64,
    cl.bits.toBitVec.getLsbD t = w.toBitVec.getLsbD ((cl.a0 + 2 ^ cl.k * t) % 64)

/-- The class word lets the numerator of bit `j` of the pattern through exactly when the pattern
has bit `j`. -/
theorem NumClass.Packs.classBit_bits {cl : NumClass} {w : UInt64} (h : cl.Packs w) (j : Int) :
    classBit cl.bits j = classBit w (cl.numerator j) := by
  have hj := Int.emod_lt_of_pos j (by decide : (0 : Int) < 64)
  rw [classBit_eq, classBit_eq, h.getLsbD_bits _ (by lia), NumClass.numerator,
    show ((2 : Int) ^ cl.k) = ((2 ^ cl.k : Nat) : Int) by simp, Int.toNat_add_mul_emod_sixty_four]

/-- A numerator that the class word lets through lies in the class `a₀ mod 2 ^ k`. -/
theorem NumClass.Packs.emod_eq_of_classBit {cl : NumClass} {w : UInt64} (h : cl.Packs w) {a : Int}
    (ha : classBit w a = true) : a % 2 ^ cl.k = cl.a0 := by
  have h64 := Int.emod_lt_of_pos a (by decide : (0 : Int) < 64)
  have h0 : ((a % 64).toNat : Int) = a % 64 := Int.toNat_of_nonneg (Int.emod_nonneg a (by decide))
  have hm := h.mod_eq _ (by lia) ha
  have hd : (2 : Int) ^ cl.k ∣ 64 := mod_cast Nat.two_pow_dvd_sixty_four h.k_le
  rw [← Int.emod_emod_of_dvd a hd, ← h0]
  exact mod_cast hm

theorem NumClass.Packs.bits_eq_zero_iff {cl : NumClass} {w : UInt64} (h : cl.Packs w) :
    cl.bits = 0 ↔ w = 0 := by
  refine ⟨fun hb ↦ Classical.byContradiction fun hw ↦ ?_, fun hw ↦ ?_⟩
  · have hlt := UInt64.toNat_ctz_lt hw
    have hm := h.mod_eq _ hlt (UInt64.getLsbD_ctz hw)
    have hc := Nat.mod_add_div w.toBitVec.ctz.toNat (2 ^ cl.k)
    rw [hm] at hc
    have := h.getLsbD_bits (w.toBitVec.ctz.toNat / 2 ^ cl.k)
      (Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hlt)
    rw [hb, hc, Nat.mod_eq_of_lt hlt, UInt64.getLsbD_ctz hw] at this
    simp at this
  · refine UInt64.toBitVec_inj.mp (BitVec.eq_of_getLsbD_eq fun t ht ↦ ?_)
    simp [h.getLsbD_bits t ht, hw]

/-- `Ratpoints.Sieve.NumClass.Packs` reads only the pattern, the stride and the residue of the
class, not its row offsets. -/
theorem NumClass.Packs.congr {cl cl' : NumClass} {w : UInt64} (h : cl.Packs w)
    (hb : cl'.bits = cl.bits) (hk : cl'.k = cl.k) (ha : cl'.a0 = cl.a0) : cl'.Packs w :=
  ⟨⟨hk ▸ h.k_lt, hk ▸ h.k_le, hk ▸ ha ▸ h.a0_lt⟩, hk ▸ ha ▸ h.mod_eq,
    hb ▸ hk ▸ ha ▸ h.getLsbD_bits⟩

/-! ### The masks of the strides -/

/-- A mask beyond the seven of the strides `k ≤ 6` is read as `0`. -/
theorem getElem!_classMasks_of_lt {k : Nat} (hk : 6 < k) : classMasks[k]! = 0 :=
  getElem!_neg classMasks k (by change ¬k < 7; lia)

/-- Bit `a < 64` of mask `k` is set exactly when `2 ^ k ∣ a` for the seven strides `k ≤ 6`; the
masks beyond them are read as `0`. -/
theorem getLsbD_classMasks (k : Nat) {a : Nat} (ha : a < 64) :
    classMasks[k]!.toBitVec.getLsbD a = (decide (k ≤ 6) && a % 2 ^ k == 0) := by
  by_cases hk : k < 7
  · have h : ∀ k < 7, ∀ a < 64,
        classMasks[k]!.toBitVec.getLsbD a = (decide (k ≤ 6) && a % 2 ^ k == 0) := by decide
    exact h k hk a ha
  · simp [getElem!_classMasks_of_lt (k := k) (by lia), show ¬k ≤ 6 by lia]

theorem getLsbD_classMasks_shiftLeft {k s : Nat} (hk : k ≤ 6) (hs : s < 2 ^ k) (a : Nat) :
    (classMasks[k]! <<< s.toUInt64).toBitVec.getLsbD a = (decide (a < 64) && a % 2 ^ k == s) := by
  have h64 : 2 ^ k ≤ 64 := Nat.pow_le_pow_right (n := 2) (by decide) hk
  have hs' : s.toUInt64.toBitVec.toNat % (64 : BitVec 64).toNat = s := by
    simp [Nat.toUInt64, UInt64.toBitVec_ofNat']
    lia
  rw [UInt64.toBitVec_shiftLeft, BitVec.shiftLeft_eq', BitVec.getLsbD_shiftLeft, BitVec.toNat_umod,
    hs']
  by_cases ha : a < 64
  · have h := Nat.le_and_sub_mod_eq_zero_iff (a := a) hs
    rw [getLsbD_classMasks k (by lia)]
    grind
  · simp [ha]

/-- Every set bit `a < 64` of `w` is `≡ c (mod 2 ^ k)`. -/
def ClassOf (w : UInt64) (c k : Nat) : Prop :=
  ∀ a < 64, w.toBitVec.getLsbD a = true → a % 2 ^ k = c % 2 ^ k

theorem classOf_zero (w : UInt64) (c : Nat) : ClassOf w c 0 := by
  simp [ClassOf, Nat.mod_one]

/-- The test of the loop over the strides of `Ratpoints.Sieve.numClasses` at `k` lets the loop go
on only for `k ≤ 6`, where the masks are not `0`, and when every set bit of `w ≠ 0` is
`≡ c (mod 2 ^ k)`. -/
theorem le_six_and_classOf_of_and_not {w : UInt64} {c k : Nat} (hw : w ≠ 0)
    (h : ¬(w &&& ~~~(classMasks[k]! <<< (c % 2 ^ k).toUInt64) != 0) = true) :
    k ≤ 6 ∧ ClassOf w c k := by
  have h0 := (UInt64.and_not_eq_zero_iff _ _).mp (by simpa using h)
  by_cases hk : k ≤ 6
  · refine ⟨hk, fun a ha hwa ↦ ?_⟩
    have := h0 a hwa
    rw [getLsbD_classMasks_shiftLeft hk (Nat.mod_lt _ (Nat.two_pow_pos k))] at this
    simpa [ha] using this
  · have hc := h0 _ (UInt64.getLsbD_ctz hw)
    simp [getElem!_classMasks_of_lt (k := k) (by lia)] at hc

/-! ### The pattern of a class -/

/-- The invariant of the loop of `Ratpoints.Sieve.packPattern` over the set bits of `w`: the packed
word after the set bits below `n`, bit `t` set exactly when some set bit `j < n` has the place
`t`. -/
def PackInvariant (w : UInt64) (k a0 n : Nat) (packed : UInt64) : Prop :=
  ∀ t, packed.toBitVec.getLsbD t =
    decide (∃ j < n, w.toBitVec.getLsbD j = true ∧ (j - a0) % 64 / 2 ^ k = t)

/-- The invariant of the doubling loop of `Ratpoints.Sieve.packPattern`, from the packed word `p0`
of period `64 / 2 ^ k`: the shift `s = 2 ^ j`, from `64 / 2 ^ k` up to 64, and bit `t` of the word
the bit `t mod (64 / 2 ^ k)` of `p0` below `s`. -/
def DoubleInvariant (k : Nat) (p0 : UInt64) : Std.WP.WhileInvariant (UInt64 × Nat) Prop :=
  .mk fun exit s ↦ (∃ j, s.2 = 2 ^ j ∧ 6 - k ≤ j ∧ j ≤ 6) ∧ (exit = true → 64 ≤ s.2) ∧
    ∀ t, s.1.toBitVec.getLsbD t = (decide (t < s.2) && p0.toBitVec.getLsbD (t % (64 / 2 ^ k)))

theorem packInvariant_zero (w : UInt64) (k a0 : Nat) : PackInvariant w k a0 0 0 := by
  simp [PackInvariant]

theorem PackInvariant.or_shiftLeft {w x packed : UInt64} {k a0 n : Nat}
    (h : PackInvariant w k a0 n packed) (hcl : ClearedBelow w n x) (hx : x ≠ 0) :
    PackInvariant w k a0 (x.toBitVec.ctz.toNat + 1)
      (packed ||| 1 <<< ((x.toBitVec.ctz.toNat - a0) % 64 / 2 ^ k).toUInt64) := by
  intro t
  have ht : (x.toBitVec.ctz.toNat - a0) % 64 / 2 ^ k < 64 :=
    Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (by decide))
  rw [Nat.toUInt64_eq, UInt64.getLsbD_or_one_shiftLeft _ ht, h t, ← Bool.decide_or,
    decide_eq_decide, hcl.exists_lt_succ_iff hx fun j ↦ (j - a0) % 64 / 2 ^ k = t]
  grind

/-- At the exit of the packing loop the packed word has its bits below `64 / 2 ^ k`. -/
theorem WalkWhileInvariant.doubleInvariant {w p0 x : UInt64} {k a0 : Nat} (hk : k ≤ 6)
    (h : WalkWhileInvariant w (PackInvariant w k a0) true (p0, x)) :
    DoubleInvariant k p0 false (p0, 64 / 2 ^ k) := by
  obtain ⟨n, hcl, hp⟩ := h.exists_clearedBelow_zero
  have hP := Nat.two_pow_mul_sixty_four_div hk
  refine ⟨⟨6 - k, Nat.sixty_four_div_two_pow hk, Nat.le_refl _, by lia⟩, nofun, fun t ↦ ?_⟩
  rw [hp t]
  by_cases ht : t < 64 / 2 ^ k
  · simp [ht, Nat.mod_eq_of_lt ht, hp t]
  · simp only [ht, decide_false, Bool.false_and, decide_eq_false_iff_not, not_exists, not_and]
    intro j _ _ hj
    exact ht (hj ▸ Nat.div_lt_of_lt_mul (by rw [hP]; exact Nat.mod_lt _ (by decide)))

/-- One doubling of a pattern of period `P ∣ s`, `2 s ≤ 64`, that fills the bits below `s`: the
pattern now fills the bits below `2 s`. -/
theorem getLsbD_or_shiftLeft_of_dvd {x p0 : UInt64} {s P : Nat} (hPs : P ∣ s) (hs : 2 * s ≤ 64)
    (hs0 : 0 < s) (hx : ∀ t, x.toBitVec.getLsbD t = (decide (t < s) && p0.toBitVec.getLsbD (t % P)))
    (t : Nat) :
    (x ||| x <<< UInt64.ofNat s).toBitVec.getLsbD t =
      (decide (t < 2 * s) && p0.toBitVec.getLsbD (t % P)) := by
  rw [UInt64.getLsbD_or_shiftLeft _ (by lia), hx, hx]
  by_cases h1 : t < s
  · simp [h1, show t < 2 * s by lia, Nat.not_le.mpr h1]
  · have h2 : (t - s) % P = t % P := by
      obtain ⟨q, rfl⟩ := hPs
      rw [Nat.sub_mul_mod (by lia)]
    simp only [h1, decide_false, Bool.false_and, Bool.false_or, h2]
    by_cases h4 : t < 2 * s
    · simp [h4, show t < 64 by lia, show s ≤ t by lia, show t - s < s by lia]
    · simp [h4, show ¬t - s < s by lia]

theorem DoubleInvariant.or_shiftLeft {k s mb : Nat} {p0 packed : UInt64} (hk : k ≤ 6)
    (h : 64 - s = mb ∧ DoubleInvariant k p0 false (packed, s)) (hs : s < 64) :
    64 - 2 * s < mb ∧ DoubleInvariant k p0 false (packed ||| packed <<< UInt64.ofNat s, 2 * s) := by
  obtain ⟨rfl, ⟨j, hj, hj1, hj2⟩, -, hb⟩ := h
  simp only at hj hb
  subst hj
  have hj6 : j < 6 := (Nat.pow_lt_pow_iff_right (by decide : 1 < 2)).mp (by simpa using hs)
  have hPs : 64 / 2 ^ k ∣ 2 ^ j := by
    rw [Nat.sixty_four_div_two_pow hk]
    exact Nat.pow_dvd_pow 2 hj1
  have hj0 := Nat.two_pow_pos j
  have h3 : 2 ^ (j + 1) ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hj6
  rw [Nat.pow_succ] at h3
  have : (2 : Nat) ^ 6 = 64 := rfl
  exact ⟨by lia, ⟨j + 1, by rw [Nat.pow_succ]; lia, by lia, by lia⟩, nofun,
    getLsbD_or_shiftLeft_of_dvd hPs (by lia) hj0 hb⟩

theorem DoubleInvariant.exit {k s mb : Nat} {p0 packed : UInt64} (hs : ¬s < 64)
    (h : 64 - s = mb ∧ DoubleInvariant k p0 false (packed, s)) :
    DoubleInvariant k p0 true (packed, s) :=
  ⟨h.2.1, fun _ ↦ Nat.le_of_not_lt hs, h.2.2.2⟩

/-- The bit of the packed pattern at `t`, read off the set bits of `w`: some set bit `j` has its
place `t mod (64 / 2 ^ k)` exactly when bit `(a0 + 2 ^ k t) mod 64` of `w` is set. -/
theorem exists_getLsbD_sub_mod_div_iff {w : UInt64} {c k t : Nat} (hk : k ≤ 6)
    (hcl : ClassOf w c k) :
    (∃ j < 64, w.toBitVec.getLsbD j = true ∧ (j - c % 2 ^ k) % 64 / 2 ^ k = t % (64 / 2 ^ k)) ↔
      w.toBitVec.getLsbD ((c % 2 ^ k + 2 ^ k * t) % 64) = true := by
  have hm := Nat.two_pow_mul_sixty_four_div hk
  refine ⟨fun ⟨j, hj, hwj, hjt⟩ ↦ ?_, fun h ↦ ?_⟩
  · rwa [← (Nat.sub_mod_div_eq_mod_iff hm hj (hcl j hj hwj)).mp hjt]
  · have hlt := Nat.mod_lt (c % 2 ^ k + 2 ^ k * t) (by decide : 0 < 64)
    exact ⟨_, hlt, h, (Nat.sub_mod_div_eq_mod_iff hm hlt (hcl _ hlt h)).mpr rfl⟩

/-- The packed word at the exit of the loops of `Ratpoints.Sieve.packPattern`. -/
theorem getLsbD_of_doubleInvariant {w p0 x packed : UInt64} {c k s : Nat} (hk : k ≤ 6)
    (hcl : ClassOf w c k)
    (hw : WalkWhileInvariant w (PackInvariant w k (c % 2 ^ k)) true (p0, x))
    (h : DoubleInvariant k p0 true (packed, s)) :
    ∀ t < 64, packed.toBitVec.getLsbD t = w.toBitVec.getLsbD ((c % 2 ^ k + 2 ^ k * t) % 64) := by
  obtain ⟨n, hz, hp⟩ := hw.exists_clearedBelow_zero
  obtain ⟨⟨j, hj, -, hj6⟩, h64, hb⟩ := h
  simp only at hj h64 hb
  have hs : s = 64 := by
    have := h64 trivial
    have : 2 ^ j ≤ 2 ^ 6 := Nat.pow_le_pow_right (by decide) hj6
    lia
  intro t ht
  simp only [hb, hs, ht, decide_true, Bool.true_and]
  rw [hp]
  simp only [hz.exists_lt_iff_of_eq_zero]
  exact Bool.eq_iff_iff.mpr (by simpa using exists_getLsbD_sub_mod_div_iff hk hcl)

attribute [local irreducible] ClassOf PackInvariant DoubleInvariant WalkWhileInvariant in
open Std.WP Lean.Order in
/-- Bit `t` of the packed pattern of `w` for the stride `2 ^ k`, `k ≤ 6`, and the residue
`a₀ = c mod 2 ^ k` of all the set bits of `w` is bit `(a₀ + 2 ^ k t) mod 64` of `w`. -/
@[spec]
theorem packPattern_spec (w : UInt64) (k c : Nat) :
    ⦃ k ≤ 6 ∧ ClassOf w c k ⦄ packPattern w k (c % 2 ^ k)
    ⦃ fun packed ↦ ∀ t < 64,
        packed.toBitVec.getLsbD t = w.toBitVec.getLsbD ((c % 2 ^ k + 2 ^ k * t) % 64) ⦄ := by
  vcgen [packPattern] invariants
  · WalkWhileInvariant w (PackInvariant w k (c % 2 ^ k))
  · Variant.ofMeasure fun s : UInt64 × UInt64 ↦ s.2.toNat
  · by rename_i p0 _ _; exact DoubleInvariant k p0
  · Variant.ofMeasure fun s : UInt64 × Nat ↦ 64 - s.2
  all_goals try simp only [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
    Variant.evalsBelow_ofMeasure_nat, meet_prop_eq_and, ofProp_prop_eq] at *
  all_goals try subst_vars
  all_goals first
    | exact walkWhileInvariant_self (packInvariant_zero _ _ _)
    | exact WalkWhileInvariant.doubleInvariant ‹k ≤ 6 ∧ ClassOf w c k›.1 ‹_›
    | exact getLsbD_of_doubleInvariant ‹k ≤ 6 ∧ ClassOf w c k›.1 ‹k ≤ 6 ∧ ClassOf w c k›.2
        ‹WalkWhileInvariant _ _ _ _› ‹DoubleInvariant _ _ _ _› _ ‹_ < 64›
    | exact DoubleInvariant.or_shiftLeft ‹k ≤ 6 ∧ ClassOf w c k›.1 ‹_› ‹_›
    | exact DoubleInvariant.exit ‹_› ‹_›
    | exact bne_iff_ne.mp ‹_›
    | exact WalkWhileInvariant.and_sub_one ‹_› ‹_› fun _ hcl hk ↦
        hk.or_shiftLeft hcl (bne_iff_ne.mp ‹_›)
    | exact WalkWhileInvariant.exit ‹_› ‹_›

/-! ### The classes of the 64 words -/

/-- A class of the stride `2 ^ k`, `k ≤ 6` and `k < Ratpoints.numStrides`, with the residue
`c mod 2 ^ k` of all the set bits of `w` and the pattern of bit `t` the bit `(a₀ + 2 ^ k t) mod 64`
of `w` packs `w`. -/
theorem packs_mk {w packed : UInt64} {c k : Nat} (hk : k < numStrides) (hk6 : k ≤ 6)
    (hcl : ClassOf w c k)
    (hp : ∀ t < 64,
      packed.toBitVec.getLsbD t = w.toBitVec.getLsbD ((c % 2 ^ k + 2 ^ k * t) % 64)) :
    NumClass.Packs ⟨packed, k, c % 2 ^ k, none⟩ w :=
  ⟨⟨hk, hk6, Nat.mod_lt _ (Nat.two_pow_pos k)⟩, fun a ha hwa ↦ hcl a ha hwa, hp⟩

/-- The class of the word `0`: the stride 1, the residue `0` and the pattern `0`. -/
theorem packs_zero {w : UInt64} (hw : ¬(w != 0) = true) : NumClass.Packs ⟨0, 0, 0, none⟩ w := by
  have hw : w = 0 := by simpa using hw
  subst hw
  exact packs_mk (c := 0) (Nat.lt_of_lt_of_le Nat.zero_lt_one one_le_numStrides) (by decide)
    (classOf_zero 0 0) fun t _ ↦ by simp

/-- The invariant of the loop over the strides of `Ratpoints.Sieve.numClasses` for the word `w` with
its lowest set bit `c`: the stride exponent `k` from 1 up to `Ratpoints.numStrides` and 7, and every
set bit of `w` `≡ c (mod 2 ^ (k - 1))`. -/
def StrideInvariant (w : UInt64) (c : Nat) : Std.WP.WhileInvariant Nat Prop :=
  .mk fun _ k ↦ 1 ≤ k ∧ k ≤ numStrides ∧ k ≤ 7 ∧ ClassOf w c (k - 1)

theorem strideInvariant_one (w : UInt64) (c : Nat) : StrideInvariant w c false 1 :=
  ⟨Nat.le_refl 1, one_le_numStrides, by decide, classOf_zero w c⟩

/-- The loop over the strides goes on at `k`: `k ≤ 6` and every set bit `≡ c (mod 2 ^ k)`. -/
theorem strideInvariant_add_one {w : UInt64} {c k : Nat} (hw : (w != 0) = true)
    (hk : k < numStrides)
    (hb : ¬(w &&& ~~~(classMasks[k]! <<< UInt64.ofNat (c % 2 ^ k)) != 0) = true) :
    StrideInvariant w c false (k + 1) := by
  have := le_six_and_classOf_of_and_not (by simpa using hw) hb
  exact ⟨by lia, by lia, by lia, by simpa using this.2⟩

theorem StrideInvariant.sub_one {w : UInt64} {c k : Nat} (h : StrideInvariant w c true k) :
    k - 1 ≤ 6 ∧ ClassOf w c (k - 1) :=
  ⟨by have := h.2.2.1; lia, h.2.2.2⟩

/-- The class after the loop over the strides packs the word, with the pattern `w` itself for
`k = 1` and with the packed pattern `packed` otherwise. -/
theorem StrideInvariant.packs {w packed : UInt64} {c k : Nat} (h : StrideInvariant w c true k)
    (hp : ∀ t < 64, packed.toBitVec.getLsbD t =
      w.toBitVec.getLsbD ((c % 2 ^ (k - 1) + 2 ^ (k - 1) * t) % 64)) :
    NumClass.Packs ⟨packed, k - 1, c % 2 ^ (k - 1), none⟩ w :=
  packs_mk (by have := h.1; have := h.2.1; lia) h.sub_one.1 h.sub_one.2 hp

theorem StrideInvariant.packs_self {w : UInt64} {c k : Nat} (h : StrideInvariant w c true k)
    (hk : k - 1 = 0) : NumClass.Packs ⟨w, k - 1, c % 2 ^ (k - 1), none⟩ w :=
  h.packs fun t ht ↦ by simp [hk, Nat.mod_one, Nat.mod_eq_of_lt ht]

/-- The invariant of the loop over the classes of `Ratpoints.Sieve.numClasses` after the classes
below `n`: each packs its word and has no row offsets yet, and the word `den_bits` has the bits of
the classes below `n` whose word is not `0`. -/
def NumClassesInvariant (nb : Vector UInt64 64) (n : Nat) (s : Vector NumClass 64 × UInt64) :
    Prop :=
  (∀ b < n, s.1[b]!.Packs nb[b]! ∧ s.1[b]!.offset = none) ∧
    ∀ j, s.2.toBitVec.getLsbD j = (decide (j < n) && nb[j]! != 0)

theorem numClassesInvariant_zero (nb : Vector UInt64 64) :
    NumClassesInvariant nb ([] : List Nat).length (.replicate 64 default, 0) :=
  ⟨nofun, fun _ ↦ by simp⟩

/-- The class `cur` set to `cl`, which packs its word, and its bit put into `den_bits` if its word
is not `0`. -/
theorem NumClassesInvariant.set {nb : Vector UInt64 64} {pref suff : List Nat} {cur : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) {cls : Vector NumClass 64} {db db' : UInt64}
    (h : NumClassesInvariant nb pref.length (cls, db)) {cl : NumClass} (hc : cur < 64)
    (hcl : cl.Packs nb[cur]) (hoff : cl.offset = none)
    (hdb : ∀ j, db'.toBitVec.getLsbD j =
      (db.toBitVec.getLsbD j || decide (j = cur) && nb[cur] != 0)) :
    NumClassesInvariant nb (pref ++ [cur]).length (cls.set cur cl hc, db') := by
  have hn := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton, hn]
  rw [hn] at h
  refine ⟨fun b hb ↦ ?_, fun j ↦ ?_⟩
  · rw [getElem!_pos _ b (by lia), Vector.getElem_set]
    split
    · subst_vars
      rw [getElem!_pos nb _ hc]
      exact ⟨hcl, hoff⟩
    · rw [← getElem!_pos _ b (by lia)]
      exact h.1 b (by lia)
  · rw [hdb, h.2, ← getElem!_pos nb cur hc]
    grind

theorem NumClassesInvariant.set_or {nb : Vector UInt64 64} {pref suff : List Nat} {cur : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) {cls : Vector NumClass 64} {db : UInt64}
    (h : NumClassesInvariant nb pref.length (cls, db)) {cl : NumClass} (hc : cur < 64)
    (hw : (nb[cur] != 0) = true) (hcl : cl.Packs nb[cur]) (hoff : cl.offset = none) :
    NumClassesInvariant nb (pref ++ [cur]).length
      (cls.set cur cl hc, db ||| 1 <<< UInt64.ofNat cur) :=
  h.set hl hc hcl hoff fun j ↦ by rw [UInt64.getLsbD_or_one_shiftLeft _ hc, hw, Bool.and_true]

theorem NumClassesInvariant.set_zero {nb : Vector UInt64 64} {pref suff : List Nat} {cur : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) {cls : Vector NumClass 64} {db : UInt64}
    (h : NumClassesInvariant nb pref.length (cls, db)) (hc : cur < 64)
    (hw : ¬(nb[cur] != 0) = true) :
    NumClassesInvariant nb (pref ++ [cur]).length (cls.set cur ⟨0, 0, 0, none⟩ hc, db) :=
  h.set hl hc (packs_zero hw) rfl fun j ↦ by simp [Bool.eq_false_iff.mpr hw]

theorem NumClassesInvariant.post {nb : Vector UInt64 64} {cls : Vector NumClass 64} {db : UInt64}
    (h : NumClassesInvariant nb (ForIn.toList [:64]).length (cls, db)) :
    (∀ b < 64, cls[b]!.Packs nb[b]! ∧ cls[b]!.offset = none) ∧
      ∀ j, db.toBitVec.getLsbD j = (decide (j < 64) && nb[j]! != 0) := by
  rwa [Std.Legacy.Range.length_toList] at h

attribute [local irreducible] NumClassesInvariant in
open Std.WP Lean.Order in
/-- Each class packs its word of the 2-adic information and has no row offsets yet, and the word
`den_bits` has the bit of each class whose word is not `0`, as `Ratpoints.Sieve.denBits` has. -/
@[spec]
theorem numClasses_spec (nb : Vector UInt64 64) :
    ⦃ True ⦄ numClasses nb
    ⦃ fun r ↦ (∀ b < 64, r.1[b]!.Packs nb[b]! ∧ r.1[b]!.offset = none) ∧
        ∀ j, r.2.toBitVec.getLsbD j = (decide (j < 64) && nb[j]! != 0) ⦄ := by
  vcgen [numClasses] invariants
  · fun pref _ s ↦ NumClassesInvariant nb pref.length s
  · by rename_i hw _; exact (fun {w : UInt64} (_ : (w != 0) = true) ↦ StrideInvariant w a) hw
  · Variant.ofMeasure fun k : Nat ↦ numStrides - k
  all_goals try simp only [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
    Variant.evalsBelow_ofMeasure_nat, meet_prop_eq_and, ofProp_prop_eq] at *
  all_goals try subst_vars
  all_goals first
    | exact numClassesInvariant_zero nb
    | exact NumClassesInvariant.post ‹_›
    | exact bne_iff_ne.mp ‹_›
    | exact strideInvariant_one _ _
    | exact NumClassesInvariant.set_or ‹_› ‹_› _ ‹_› (StrideInvariant.packs_self ‹_› ‹_›) rfl
    | exact StrideInvariant.sub_one ‹_›
    | exact NumClassesInvariant.set_or ‹_› ‹_› _ ‹_› (StrideInvariant.packs ‹_› ‹_›) rfl
    | exact ‹_ ∧ _›.2
    | exact ⟨by lia, strideInvariant_add_one ‹_› ‹_› ‹_›⟩
    | exact NumClassesInvariant.set_zero ‹_› ‹_› _ ‹_›

/-- Each class that `Ratpoints.Sieve.numClasses` makes packs its word of the 2-adic information
(`Ratpoints.Sieve.numClasses_spec`). -/
theorem packs_getElem!_fst_run_numClasses (nb : Vector UInt64 64) {b : Nat} (hb : b < 64) :
    (Id.run (numClasses nb)).1[b]!.Packs nb[b]! :=
  ((Std.WP.Id.of_run_eq_wp rfl _ ((numClasses_spec nb).le_wp trivial)).1 b hb).1

/-! ### The fields of the sieve entries -/

/-- The bias `m ⌈Ratpoints.rowBias / m⌉ = m ((rowBias + m - 1) / m)` of a modulus `m > 0`, as
`examine_prime`, `make_power` and `make_modulus` compute it, lies from `Ratpoints.rowBias` to below
`Ratpoints.rowBias + m`. -/
theorem rowBias_le_mul_div_and_mul_div_lt {m : Nat} (hm : 0 < m) :
    rowBias ≤ m * ((rowBias + m - 1) / m) ∧ m * ((rowBias + m - 1) / m) < rowBias + m := by
  generalize rowBias = R
  have h1 := Nat.div_add_mod (R + m - 1) m
  have h2 := Nat.mod_lt (R + m - 1) hm
  constructor <;> lia

/-- The fields of a sieve entry that the row offsets of the packing read: an odd modulus
`1 < p ≤ Ratpoints.maxPrimeEven` with its reciprocal, the inverse `rbainv < p` of
`Ratpoints.rbaLength` modulo `p`, and the bias, a multiple of `p` from `Ratpoints.rowBias` to below
`Ratpoints.rowBias + p`, as `examine_prime`, `make_power` and `make_modulus` set them. -/
structure SieveEntry.Packable (e : SieveEntry) : Prop where
  /-- The modulus is above 1. -/
  one_lt : 1 < e.p
  /-- The modulus is odd. -/
  odd : e.p % 2 = 1
  /-- The modulus is at most `Ratpoints.maxPrimeEven`. -/
  le_maxPrimeEven : e.p ≤ maxPrimeEven
  /-- The reciprocal is that of the modulus. -/
  magic_eq : e.magic = Sieve.magic e.p
  /-- `rbainv` is the inverse of `Ratpoints.rbaLength` modulo the modulus. -/
  rbainv_mul_mod : e.rbainv * rbaLength % e.p = 1
  /-- `rbainv` is below the modulus. -/
  rbainv_lt : e.rbainv < e.p
  /-- The bias is a multiple of the modulus. -/
  bias_mod : e.bias % e.p = 0
  /-- The bias is at least `Ratpoints.rowBias`. -/
  rowBias_le_bias : rowBias ≤ e.bias
  /-- The bias is below `Ratpoints.rowBias + p`. -/
  bias_lt : e.bias < rowBias + e.p

end Sieve

end Ratpoints

end
