/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Packing
public import Ratpoints.Proof.Reductions
public import Ratpoints.Proof.SetBits

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
classes whose word is not `0`. The number of the packings counts the first class of each key
`2 ^ k + a₀` among the classes with a pattern (`Ratpoints.Sieve.firstKeys`). The row offsets of the
packings read, of each sieve entry, an odd modulus `1 < p ≤ Ratpoints.maxPrimeEven` with its
reciprocal, the inverse of `Ratpoints.rbaLength` modulo `p` and the bias, the least multiple of `p`
from `Ratpoints.rowBias` on, as `examine_prime`, `make_power` and `make_modulus` set them
(`Ratpoints.Sieve.SieveEntry.Packable`), which the sieve entry of a modulus has
(`Ratpoints.makeModulus?_spec`); they give each class with a pattern a row of the array of the
offsets, with the offset of its packing for each sieve entry
(`Ratpoints.Sieve.SieveEntry.PackedFor`): between `Ratpoints.rowBias` and `Ratpoints.rowBias + 2 p`,
`a₀ (2 ^ k Ratpoints.rbaLength)⁻¹` modulo `p`, with the inverse of the stride modulo `p` in the
entry. `fill_bp_list` divides the denominator by the stride modulo each modulus, exactly in each of
its branches, since its products stay below `2 ^ 64 / p`.

## Main definitions

* `Ratpoints.Sieve.NumClass.numerator`: the numerator `a₀ + 2 ^ k j` of bit `j` of a class.
* `Ratpoints.Sieve.NumClass.WF`, `Ratpoints.Sieve.NumClass.Packs`: the stride and the residue of a
  packing, and a class that packs a word of numerators modulo 64.
* `Ratpoints.Sieve.NumClass.key`, `Ratpoints.Sieve.IsFirstKey`, `Ratpoints.Sieve.firstKeys`: the key
  `2 ^ k + a₀` of a packing, and the number of the distinct packings of the classes below `n`.
* `Ratpoints.Sieve.halveIter`, `Ratpoints.Sieve.halveChain`: the halvings modulo an odd modulus.
* `Ratpoints.Sieve.classOffset`: the offset of the row of a class for a sieve entry.
* `Ratpoints.Sieve.SieveEntry.Packable`, `Ratpoints.Sieve.SieveEntry.PackedFor`,
  `Ratpoints.Sieve.OffsetsFor`: the fields of a sieve entry that the row offsets of the packing
  read, the offset of the packing of a class for an entry, and the rows of offsets of all the
  classes with a pattern.

## Main statements

* `Ratpoints.Sieve.NumClass.Packs.classBit_bits`,
  `Ratpoints.Sieve.NumClass.Packs.emod_eq_of_classBit`,
  `Ratpoints.Sieve.NumClass.Packs.bits_eq_zero_iff`: the pattern lets bit `j` through exactly when
  the word lets the numerator of `j` through, the word lets nothing off the class through, and the
  pattern is `0` exactly when the word is; `Ratpoints.Sieve.NumClass.Packs.filter_filter_emod`: so
  the numerators that the word lets through are among those of the class;
  `Ratpoints.Sieve.NumClass.Packs.bits_bne_zero`: the test of the pattern is the test of the word.
* `Ratpoints.Sieve.getLsbD_classMasks`: the masks of the strides, `0` beyond the seven of `k ≤ 6`.
* `Ratpoints.Sieve.packPattern_spec`, `Ratpoints.Sieve.numClasses_spec`: the packed pattern, and the
  classes of the 64 words with `den_bits`.
* `Ratpoints.Sieve.numPackings_spec`: the number of the packings is that of the distinct keys, at
  least 1.
* `Ratpoints.Sieve.classRows_spec`, `Ratpoints.Sieve.classOffsets_spec`: the rows of offsets of the
  classes and the inverses of the strides in the entries.
* `Ratpoints.Sieve.SieveEntry.PackedFor.fits`: the sieve spec of an entry with the offset of the
  packing of a class fits the reductions of the row indices of the first two stages.
* `Ratpoints.Sieve.fillBpList_eq_map`: the residues of the denominator divided by the stride.

## Implementation notes

The file uses Lean core and `Std` only, so that the contracts of the sieve, in files without
Mathlib, can use it. The proofs use only the facts on the constants that `decide` checks next to
them, never their values: here that `Ratpoints.numStrides ≥ 1`, that `Ratpoints.maxBitsInPrime ≤ 10`
(`Ratpoints.maxPrimeEven_le_two_pow_10`) and that `Ratpoints.mulModLimit < 2 ^ 32`; that the masks
of the strides beyond `k = 6` are `0` is read with the default of the array. The facts on words,
natural numbers and integers that are not about the model are in `Ratpoints.Proof.Bits`. The bounds
of the products of `fill_bp_list` and of `class_offsets` are in `Ratpoints.Proof.Reductions`, the
bits of an interval of numerators and the other range lemmas of the `long`s of the packing in
`Ratpoints.Proof.BitRange`.
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

/-- The numerators in the class `a₀ mod 2 ^ k` of a list that the class word `w` and a test `p` let
through are those of the list that they let through, since the class word lets nothing off the
class through. -/
theorem NumClass.Packs.filter_filter_emod {cl : NumClass} {w : UInt64} (h : cl.Packs w)
    (l : List Int) (p : Int → Bool) :
    (l.filter fun a ↦ a % 2 ^ cl.k == (cl.a0 : Int)).filter (fun a ↦ classBit w a && p a) =
      l.filter fun a ↦ classBit w a && p a := by
  rw [List.filter_filter]
  refine List.filter_congr fun a _ ↦ ?_
  cases hc : classBit w a
  · simp
  · simp [h.emod_eq_of_classBit hc]

/-- The test `EXT0(cl->bits)` of the C code on a class that packs the word `w` is the test `w ≠ 0`:
the classes with a pattern are those whose word admits a numerator, the classes of `den_bits`. -/
theorem NumClass.Packs.bits_bne_zero {cl : NumClass} {w : UInt64} (h : cl.Packs w) :
    (cl.bits != 0) = (w != 0) := by
  rw [Bool.eq_iff_iff, bne_iff_ne, bne_iff_ne, ne_eq, ne_eq, h.bits_eq_zero_iff]

/-- `Ratpoints.Sieve.NumClass.Packs` reads only the pattern, the stride and the residue of the
class, not its row offsets. -/
theorem NumClass.Packs.congr {cl cl' : NumClass} {w : UInt64} (h : cl.Packs w)
    (hb : cl'.bits = cl.bits) (hk : cl'.k = cl.k) (ha : cl'.a0 = cl.a0) : cl'.Packs w :=
  ⟨⟨hk ▸ h.k_lt, hk ▸ h.k_le, hk ▸ ha ▸ h.a0_lt⟩, hk ▸ ha ▸ h.mod_eq,
    hb ▸ hk ▸ ha ▸ h.getLsbD_bits⟩

/-- The key `2 ^ k + a₀` of the packing of a class, by which `num_packings` and `class_offsets`
tell the packings apart. -/
def NumClass.key (cl : NumClass) : Nat := 2 ^ cl.k + cl.a0

theorem NumClass.WF.key_lt {cl : NumClass} (h : cl.WF) : cl.key < 2 ^ (cl.k + 1) := by
  have := h.a0_lt
  rw [NumClass.key, Nat.pow_succ]
  lia

theorem NumClass.WF.key_lt_128 {cl : NumClass} (h : cl.WF) : cl.key < 128 := by
  have : 2 ^ (cl.k + 1) ≤ 2 ^ 7 := Nat.pow_le_pow_right (by decide) (by have := h.k_le; lia)
  exact Nat.lt_of_lt_of_le h.key_lt this

theorem NumClass.WF.a0_lt_sixty_four {cl : NumClass} (h : cl.WF) : cl.a0 < 64 :=
  Nat.lt_of_lt_of_le h.a0_lt (Nat.pow_le_pow_right (n := 2) (by decide) h.k_le)

theorem NumClass.WF.key_lt_two_pow_numStrides {cl : NumClass} (h : cl.WF) :
    cl.key < 2 ^ numStrides :=
  Nat.lt_of_lt_of_le h.key_lt (Nat.pow_le_pow_right (by decide) h.k_lt)

theorem NumClass.WF.key_lt_key {cl cl' : NumClass} (h : cl.WF) (hk : cl.k < cl'.k) :
    cl.key < cl'.key :=
  Nat.lt_of_lt_of_le h.key_lt (Nat.le_trans (Nat.pow_le_pow_right (by decide) hk)
    (Nat.le_add_right _ _))

theorem NumClass.WF.k_eq_and_a0_eq {cl cl' : NumClass} (h : cl.WF) (h' : cl'.WF)
    (hk : cl.key = cl'.key) : cl.k = cl'.k ∧ cl.a0 = cl'.a0 := by
  have hkk : cl.k = cl'.k := by
    rcases Nat.lt_trichotomy cl.k cl'.k with hlt | heq | hlt
    · exact absurd hk (Nat.ne_of_lt (h.key_lt_key hlt))
    · exact heq
    · exact absurd hk (Nat.ne_of_gt (h'.key_lt_key hlt))
  simp only [NumClass.key, hkk] at hk
  exact ⟨hkk, by lia⟩

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
    UInt64.getLsbD_or_shiftLeft_of_dvd hPs (by lia) hj0 hb⟩

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
theorem NumClass.packs_mk {w packed : UInt64} {c k : Nat} (hk : k < numStrides) (hk6 : k ≤ 6)
    (hcl : ClassOf w c k)
    (hp : ∀ t < 64,
      packed.toBitVec.getLsbD t = w.toBitVec.getLsbD ((c % 2 ^ k + 2 ^ k * t) % 64)) :
    Packs ⟨packed, k, c % 2 ^ k, none⟩ w :=
  ⟨⟨hk, hk6, Nat.mod_lt _ (Nat.two_pow_pos k)⟩, fun a ha hwa ↦ hcl a ha hwa, hp⟩

/-- The class of the word `0`: the stride 1, the residue `0` and the pattern `0`. -/
theorem NumClass.packs_zero {w : UInt64} (hw : ¬(w != 0) = true) : Packs ⟨0, 0, 0, none⟩ w := by
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
  NumClass.packs_mk (by have := h.1; have := h.2.1; lia) h.sub_one.1 h.sub_one.2 hp

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
  h.set hl hc (NumClass.packs_zero hw) rfl fun j ↦ by simp [Bool.eq_false_iff.mpr hw]

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

/-! ### The number of the packings -/

/-- Whether the class `b` of `cls` is the first with a pattern whose packing has its key. -/
def IsFirstKey (cls : Vector NumClass 64) (b : Nat) : Prop :=
  cls[b]!.bits ≠ 0 ∧ ∀ b' < b, cls[b']!.bits ≠ 0 → cls[b']!.key ≠ cls[b]!.key

instance instDecidableIsFirstKey (cls : Vector NumClass 64) (b : Nat) :
    Decidable (IsFirstKey cls b) :=
  inferInstanceAs (Decidable (_ ∧ ∀ b' < b, _))

/-- The number of the distinct packings of the classes below `n` with a pattern, the classes that
are the first with their key. -/
def firstKeys (cls : Vector NumClass 64) (n : Nat) : Nat :=
  ((List.range n).filter fun b ↦ decide (IsFirstKey cls b)).length

theorem firstKeys_succ (cls : Vector NumClass 64) (n : Nat) :
    firstKeys cls (n + 1) = firstKeys cls n + if IsFirstKey cls n then 1 else 0 := by
  simp only [firstKeys, List.range_succ, List.filter_append, List.length_append]
  by_cases h : IsFirstKey cls n <;> simp [h]

theorem firstKeys_mono (cls : Vector NumClass 64) {m n : Nat} (h : m ≤ n) :
    firstKeys cls m ≤ firstKeys cls n := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le h
  induction d with
  | zero => exact Nat.le_refl _
  | succ d ih => rw [← Nat.add_assoc, firstKeys_succ]; have := ih (Nat.le_add_right m d); lia

/-- The invariant of the loop of `Ratpoints.Sieve.numPackings` after the classes below `n`: the two
words `seen` mark the keys of the classes below `n` with a pattern, and the count is the number of
their distinct packings. -/
def NumPackingsInvariant (cls : Vector NumClass 64) (n : Nat) (s : Array UInt64 × Nat) : Prop :=
  s.1.size = 2 ∧ (∀ K < 128, s.1[K / 64]!.toBitVec.getLsbD (K % 64) =
    decide (∃ b < n, cls[b]!.bits ≠ 0 ∧ cls[b]!.key = K)) ∧ s.2 = firstKeys cls n

theorem numPackingsInvariant_zero (cls : Vector NumClass 64) :
    NumPackingsInvariant cls ([] : List Nat).length (#[0, 0], 0) := by
  refine ⟨rfl, fun K hK ↦ ?_, rfl⟩
  have : (#[0, 0] : Array UInt64)[K / 64]! = 0 := by
    rcases (by lia : K / 64 = 0 ∨ K / 64 = 1) with h | h <;> simp [h]
  simp [this]

theorem NumPackingsInvariant.post {cls : Vector NumClass 64} {seen : Array UInt64} {n : Nat}
    (h : NumPackingsInvariant cls (ForIn.toList [:64]).length (seen, n)) :
    (if 0 < n then n else 1) = max 1 (firstKeys cls 64) := by
  simp only [NumPackingsInvariant, Std.Legacy.Range.length_toList] at h
  rw [h.2.2]
  split <;> lia

/-- A class with a pattern whose key `seen` does not mark is the first with its key, and marking its
key and counting it keeps the invariant. -/
theorem NumPackingsInvariant.mark {cls : Vector NumClass 64} {pref suff : List Nat} {cur : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) (hwf : ∀ b < 64, cls[b]!.WF)
    {seen : Array UInt64} {n : Nat} (h : NumPackingsInvariant cls pref.length (seen, n))
    (hc : cur < 64) (hb : (cls[cur].bits != 0 && seen[(2 ^ cls[cur].k + cls[cur].a0) / 64]! >>>
      UInt64.ofNat ((2 ^ cls[cur].k + cls[cur].a0) % 64) &&& 1 == 0) = true) :
    NumPackingsInvariant cls (pref ++ [cur]).length
      (seen.set! ((2 ^ cls[cur].k + cls[cur].a0) / 64)
        (seen[(2 ^ cls[cur].k + cls[cur].a0) / 64]! |||
          1 <<< UInt64.ofNat ((2 ^ cls[cur].k + cls[cur].a0) % 64)), n + 1) := by
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at *
  simp only [NumPackingsInvariant] at h ⊢
  obtain ⟨hs, hseen, rfl⟩ := h
  have hK := (hwf cur hc).key_lt_128
  rw [getElem!_pos cls cur hc] at hK
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hb
  rw [UInt64.shiftRight_and_one_beq_zero _ (by lia), Bool.not_eq_true', ← NumClass.key,
    hseen _ hK, decide_eq_false_iff_not] at hb
  have hf : IsFirstKey cls cur := by
    simp only [IsFirstKey, getElem!_pos cls cur hc]
    exact ⟨hb.1, fun b hb' h' h'' ↦ hb.2 ⟨b, hb', h', h''⟩⟩
  refine ⟨by simp [hs], fun K hK' ↦ ?_, by simp [firstKeys_succ, hf]⟩
  rw [← NumClass.key, UInt64.getLsbD_getElem!_set!_or_one_shiftLeft hs hK', hseen K hK',
    ← Bool.decide_or, decide_eq_decide, Nat.exists_lt_succ_right, getElem!_pos cls cur hc]
  grind

theorem NumPackingsInvariant.skip {cls : Vector NumClass 64} {pref suff : List Nat} {cur : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) (hwf : ∀ b < 64, cls[b]!.WF)
    {seen : Array UInt64} {n : Nat} (h : NumPackingsInvariant cls pref.length (seen, n))
    (hc : cur < 64) (hb : ¬(cls[cur].bits != 0 && seen[(2 ^ cls[cur].k + cls[cur].a0) / 64]! >>>
      UInt64.ofNat ((2 ^ cls[cur].k + cls[cur].a0) % 64) &&& 1 == 0) = true) :
    NumPackingsInvariant cls (pref ++ [cur]).length (seen, n) := by
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at *
  simp only [NumPackingsInvariant] at h ⊢
  obtain ⟨hs, hseen, rfl⟩ := h
  have hK := (hwf cur hc).key_lt_128
  rw [getElem!_pos cls cur hc] at hK
  simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and] at hb
  rw [UInt64.shiftRight_and_one_beq_zero _ (by lia), Bool.not_eq_true', ← NumClass.key,
    hseen _ hK, decide_eq_false_iff_not, Classical.not_not] at hb
  have hf : ¬IsFirstKey cls cur := by
    simp only [IsFirstKey, getElem!_pos cls cur hc]
    exact fun ⟨h1, h2⟩ ↦ (hb h1).elim fun b ⟨hb', h', h''⟩ ↦ h2 b hb' h' h''
  refine ⟨hs, fun K hK' ↦ ?_, by simp [firstKeys_succ, hf]⟩
  rw [hseen K hK', decide_eq_decide, Nat.exists_lt_succ_right, getElem!_pos cls cur hc]
  grind

attribute [local irreducible] NumPackingsInvariant in
open Std.WP Lean.Order in
/-- The number of the distinct packings of the classes with a pattern, at least 1. -/
@[spec]
theorem numPackings_spec (cls : Vector NumClass 64) :
    ⦃ ∀ b < 64, cls[b]!.WF ⦄ numPackings cls ⦃ fun n ↦ n = max 1 (firstKeys cls 64) ⦄ := by
  vcgen [numPackings] invariants
  · fun pref _ s ↦ NumPackingsInvariant cls pref.length s
  all_goals try simp only at *
  all_goals first
    | exact numPackingsInvariant_zero cls
    | exact NumPackingsInvariant.post ‹_›
    | exact NumPackingsInvariant.mark ‹_› ‹_› ‹_› _ ‹_›
    | exact NumPackingsInvariant.skip ‹_› ‹_› ‹_› _ ‹_›

/-! ### The rows of the packings -/

/-- The offset of the row of the packing of the class `cl` for the `n`-th modulus `p` of the sieve
entries `es`, from the inverse `rinv[n][k]` of `2 ^ k Ratpoints.rbaLength` modulo `p`: the remainder
of `a₀ rinv[n][k]` by a multiplication with the reciprocal of the entry, plus its bias, as
`class_offsets` computes it. -/
def classOffset (es : Array SieveEntry) (rinv : Array (Array Nat)) (cl : NumClass) (n : Nat) :
    Nat :=
  mulMod (cl.a0 * rinv[n]![cl.k]!) es[n]!.p es[n]!.magic + es[n]!.bias

/-- The invariant of the loop of `Ratpoints.Sieve.classRows` over the classes after those below
`m`, for the classes `cls` it starts from: the array of the offsets `o` keeps its size and the table
of the rows `rowOf` its `2 ^ Ratpoints.numStrides` entries; `rows` rows are made, one for each
distinct packing of the classes below `m` with a pattern; the classes `cls'` from `m` on are as they
were; each class below `m` keeps its pattern, stride and residue, and one with a pattern has the row
of its packing, at a position `r np` for some `r < rows`, which the table of the rows holds at its
key and whose `np` offsets are those of the class; and the table holds a row only at the key of a
class below `m` with a pattern. -/
def ClassRowsInvariant (cls : Vector NumClass 64) (es : Array SieveEntry) (rinv : Array (Array Nat))
    (np size m : Nat) (cls' : Vector NumClass 64) (o : Array Nat) (rowOf : Array (Option Nat))
    (rows : Nat) : Prop :=
  o.size = size ∧ rowOf.size = 2 ^ numStrides ∧ rows = firstKeys cls m ∧
    (∀ b < 64, m ≤ b → cls'[b]! = cls[b]!) ∧
    (∀ b < m, cls'[b]!.bits = cls[b]!.bits ∧ cls'[b]!.k = cls[b]!.k ∧ cls'[b]!.a0 = cls[b]!.a0 ∧
      (cls[b]!.bits ≠ 0 → ∃ r < rows, cls'[b]!.offset = some (r * np) ∧
        rowOf[cls[b]!.key]! = some (r * np) ∧
        ∀ n < np, o[r * np + n]! = classOffset es rinv cls[b]! n)) ∧
    ∀ K, rowOf[K]!.isSome → ∃ b < m, cls[b]!.bits ≠ 0 ∧ cls[b]!.key = K

/-- The invariant of the loop of `Ratpoints.Sieve.classRows` that writes the row of the class `cl`
at the position `row` into the array of the offsets `o₀`, after the moduli below `j`: the array
keeps its size, and holds the offsets of the class for these moduli at their positions in the
array. -/
def RowInvariant (es : Array SieveEntry) (rinv : Array (Array Nat)) (cl : NumClass) (row : Nat)
    (o0 : Array Nat) (j : Nat) (o : Array Nat) : Prop :=
  o.size = o0.size ∧ ∀ i, o[i]! =
    if row ≤ i ∧ i < row + j ∧ i < o0.size then classOffset es rinv cl (i - row) else o0[i]!

theorem classRowsInvariant_init (cls : Vector NumClass 64) (es : Array SieveEntry)
    (rinv : Array (Array Nat)) (np : Nat) (offsets : Array Nat) :
    ClassRowsInvariant cls es rinv np offsets.size ([] : List Nat).length cls offsets
      (.replicate (2 ^ numStrides) none) 0 := by
  refine ⟨rfl, by simp, rfl, fun _ _ _ ↦ rfl, nofun, fun K hK ↦ ?_⟩
  simp [Array.getElem!_replicate_none] at hK

theorem ClassRowsInvariant.post {cls : Vector NumClass 64} {es : Array SieveEntry}
    {rinv : Array (Array Nat)} {np : Nat} {offsets : Array Nat} {cls' : Vector NumClass 64}
    {o : Array Nat} {rowOf : Array (Option Nat)} {rows : Nat}
    (h : ClassRowsInvariant cls es rinv np offsets.size (ForIn.toList [:64]).length cls' o rowOf
      rows) :
    o.size = offsets.size ∧ ∀ b < 64, cls'[b]!.bits = cls[b]!.bits ∧ cls'[b]!.k = cls[b]!.k ∧
      cls'[b]!.a0 = cls[b]!.a0 ∧ (¬cls[b]!.bits = 0 →
        ∃ pos, cls'[b]!.offset = some pos ∧
          ∀ n < np, o[pos + n]! = classOffset es rinv cls[b]! n) := by
  rw [Std.Legacy.Range.length_toList] at h
  refine ⟨h.1, fun b hb ↦ ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := h.2.2.2.2.1 b hb
  exact ⟨h1, h2, h3, fun hb0 ↦ (h4 hb0).elim fun _ ⟨_, hr, _, hv⟩ ↦ ⟨_, hr, hv⟩⟩

/-- A class without a pattern is stepped over: it is not the first with its key, and it keeps its
offsets. -/
theorem ClassRowsInvariant.skip {cls : Vector NumClass 64} {es : Array SieveEntry}
    {rinv : Array (Array Nat)} {np size : Nat} {pref suff : List Nat} {cur : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) {cls' : Vector NumClass 64} {o : Array Nat}
    {rowOf : Array (Option Nat)} {rows : Nat}
    (h : ClassRowsInvariant cls es rinv np size pref.length cls' o rowOf rows) (hc : cur < 64)
    (hb : (cls'[cur].bits == 0) = true) :
    ClassRowsInvariant cls es rinv np size (pref ++ [cur]).length cls' o rowOf rows := by
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at *
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  have hcur := h4 cur hc (Nat.le_refl _)
  rw [getElem!_pos cls' cur hc] at hcur
  rw [hcur, beq_iff_eq] at hb
  have hf : ¬IsFirstKey cls cur := fun hf ↦ hf.1 hb
  refine ⟨h1, h2, (by simp [h3, firstKeys_succ, hf]), fun b hb' hb'' ↦ h4 b hb' (by lia),
    fun b hb' ↦ ?_, fun K hK ↦ (h6 K hK).elim fun b ⟨hb', h'⟩ ↦ ⟨b, by lia, h'⟩⟩
  rcases Nat.lt_succ_iff_lt_or_eq.mp hb' with hb' | rfl
  · exact h5 b hb'
  · rw [getElem!_pos cls' b hc, hcur]
    exact ⟨rfl, rfl, rfl, fun h ↦ absurd hb h⟩

/-- A key with a row is the key of an earlier class with a pattern, whose row it is: a class with
that key is not the first with it, and its row holds its offsets, since the earlier class has the
same stride and residue. -/
theorem ClassRowsInvariant.exists_row_of_getElem!_eq_some {cls : Vector NumClass 64}
    {es : Array SieveEntry} {rinv : Array (Array Nat)} {np size cur : Nat}
    (hwf : ∀ b < 64, cls[b]!.WF) {cls' : Vector NumClass 64} {o : Array Nat}
    {rowOf : Array (Option Nat)} {rows : Nat}
    (h : ClassRowsInvariant cls es rinv np size cur cls' o rowOf rows) (hc : cur < 64) {row : Nat}
    (hrow : rowOf[cls[cur]!.key]! = some row) :
    ∃ r < rows, row = r * np ∧ (∀ n < np, o[r * np + n]! = classOffset es rinv cls[cur]! n) ∧
      ¬IsFirstKey cls cur := by
  obtain ⟨b, hbc, hb0, hkey⟩ := h.2.2.2.2.2 cls[cur]!.key (by simp [hrow])
  obtain ⟨r, hr, -, hrow', hv⟩ := (h.2.2.2.2.1 b hbc).2.2.2 hb0
  rw [hkey, hrow, Option.some.injEq] at hrow'
  obtain ⟨hk, ha⟩ := (hwf b (by lia)).k_eq_and_a0_eq (hwf cur hc) hkey
  refine ⟨r, hr, hrow', fun n hn ↦ ?_, fun hf ↦ hf.2 b hbc hb0 hkey⟩
  rw [hv n hn]
  simp only [classOffset, hk, ha]

/-- A class with a pattern whose key has a row already gets that row: an earlier class has its key,
so it is not the first with it, and has the same stride and residue, so the same offsets. -/
theorem ClassRowsInvariant.reuse {cls : Vector NumClass 64} {es : Array SieveEntry}
    {rinv : Array (Array Nat)} {np size : Nat} {pref suff : List Nat} {cur : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) (hwf : ∀ b < 64, cls[b]!.WF)
    {cls' : Vector NumClass 64} {o : Array Nat} {rowOf : Array (Option Nat)} {rows : Nat}
    (h : ClassRowsInvariant cls es rinv np size pref.length cls' o rowOf rows) (hc : cur < 64)
    {row : Nat} (hrow : rowOf[2 ^ cls'[cur].k + cls'[cur].a0]! = some row) :
    ClassRowsInvariant cls es rinv np size (pref ++ [cur]).length
      (cls'.set cur { cls'[cur] with offset := some row } hc) o rowOf rows := by
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at *
  have hcur := h.2.2.2.1 cur hc (Nat.le_refl _)
  rw [getElem!_pos cls' cur hc] at hcur
  rw [hcur, ← NumClass.key] at hrow
  obtain ⟨r, hr, rfl, hv, hf⟩ := h.exists_row_of_getElem!_eq_some hwf hc hrow
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := h
  refine ⟨h1, h2, (by simp [h3, firstKeys_succ, hf]), fun b' hb' hb'' ↦ ?_, fun b' hb' ↦ ?_,
    fun K hK ↦ (h6 K hK).elim fun b ⟨hb', h'⟩ ↦ ⟨b, by lia, h'⟩⟩
  · simp only [Vector.getElem!_set hc hb', show cur ≠ b' by lia, ↓reduceIte]
    exact h4 b' hb' (by lia)
  · rw [Vector.getElem!_set hc (by lia)]
    split <;> rename_i hcb
    · subst hcb
      exact ⟨by simp [hcur], by simp [hcur], by simp [hcur], fun _ ↦ ⟨r, hr, rfl, hrow, hv⟩⟩
    · exact h5 b' (by lia)

theorem rowInvariant_nil (es : Array SieveEntry) (rinv : Array (Array Nat)) (cl : NumClass)
    (row : Nat) (o : Array Nat) : RowInvariant es rinv cl row o ([] : List Nat).length o :=
  ⟨rfl, fun i ↦ by simp only [List.length_nil, Nat.add_zero]; split <;> first | rfl | lia⟩

theorem RowInvariant.set! {es : Array SieveEntry} {rinv : Array (Array Nat)} {cl : NumClass}
    {row np : Nat} {o0 o : Array Nat} {pref suff : List Nat} {n : Nat}
    (hl : ForIn.toList [:np] = pref ++ n :: suff)
    (h : RowInvariant es rinv cl row o0 pref.length o) :
    RowInvariant es rinv cl row o0 (pref ++ [n]).length
      (o.set! (row + n) (classOffset es rinv cl n)) := by
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at *
  obtain ⟨hs, h⟩ := h
  refine ⟨by simp [hs], fun i ↦ ?_⟩
  by_cases hi : row + n = i
  · subst hi
    by_cases hlt : row + n < o0.size
    · rw [Array.getElem!_set!_self _ _ _ (by lia)]
      simp [hlt]
    · rw [Array.set!_eq_setIfInBounds, Array.setIfInBounds_eq_of_size_le (by lia), h]
      simp [hlt]
  · rw [Array.getElem!_set!_ne _ _ _ _ hi, h]
    grind

/-- The class `cur` with a pattern whose key has no row is the first with its key: an earlier class
with its key would have put its row into the table. -/
theorem ClassRowsInvariant.isFirstKey {cls : Vector NumClass 64} {es : Array SieveEntry}
    {rinv : Array (Array Nat)} {np size cur : Nat} {cls' : Vector NumClass 64} {o : Array Nat}
    {rowOf : Array (Option Nat)} {rows : Nat}
    (h : ClassRowsInvariant cls es rinv np size cur cls' o rowOf rows) (hb : cls[cur]!.bits ≠ 0)
    (hnone : rowOf[cls[cur]!.key]! = none) : IsFirstKey cls cur := by
  refine ⟨hb, fun b hb' hb0 hkey ↦ ?_⟩
  obtain ⟨r, -, -, hr, -⟩ := (h.2.2.2.2.1 b hb').2.2.2 hb0
  rw [hkey, hnone] at hr
  simp at hr

private theorem RowInvariant.getElem!_of_lt {es : Array SieveEntry} {rinv : Array (Array Nat)}
    {cl : NumClass} {rows np : Nat} {o0 o : Array Nat}
    (h : RowInvariant es rinv cl (rows * np) o0 np o)
    {r n : Nat} (hr : r < rows) (hn : n < np) : o[r * np + n]! = o0[r * np + n]! := by
  have : (r + 1) * np ≤ rows * np := Nat.mul_le_mul_right np hr
  rw [Nat.succ_mul] at this
  rw [h.2, ite_eq_right (by lia)]

private theorem RowInvariant.getElem!_row {es : Array SieveEntry} {rinv : Array (Array Nat)}
    {cl : NumClass} {rows np : Nat} {o0 o : Array Nat}
    (h : RowInvariant es rinv cl (rows * np) o0 np o)
    (hsize : (rows + 1) * np ≤ o0.size) {n : Nat} (hn : n < np) :
    o[rows * np + n]! = classOffset es rinv cl n := by
  rw [Nat.succ_mul] at hsize
  rw [h.2, ite_eq_left (by lia), Nat.add_sub_cancel_left]

/-- The first class with its key gets the row `rows`, which the array has room for when it has room
for a row for each distinct packing. -/
theorem ClassRowsInvariant.add_one_mul_le {cls : Vector NumClass 64} {es : Array SieveEntry}
    {rinv : Array (Array Nat)} {np size cur : Nat} {cls' : Vector NumClass 64} {o : Array Nat}
    {rowOf : Array (Option Nat)} {rows : Nat}
    (h : ClassRowsInvariant cls es rinv np size cur cls' o rowOf rows) (hf : IsFirstKey cls cur)
    (hcur : cur < 64) (hsize : firstKeys cls 64 * np ≤ size) : (rows + 1) * np ≤ size :=
  Nat.le_trans (Nat.mul_le_mul_right np
    ((by simp [firstKeys_succ, hf, h.2.2.1] : firstKeys cls (cur + 1) = rows + 1) ▸
      firstKeys_mono cls (by lia))) hsize

-- An earlier class keeps its row when the first class `cur` with its key gets the row `rows`: the
-- earlier rows lie below it, and the table of the rows changes only at the new key.
private theorem ClassRowsInvariant.entry_newRow {cls : Vector NumClass 64} {es : Array SieveEntry}
    {rinv : Array (Array Nat)} {np size cur : Nat} {cls' : Vector NumClass 64} {o o' : Array Nat}
    {rowOf : Array (Option Nat)} {rows : Nat} {cl : NumClass}
    (h : ClassRowsInvariant cls es rinv np size cur cls' o rowOf rows) (hf : IsFirstKey cls cur)
    (hrow : RowInvariant es rinv cl (rows * np) o np o') {b : Nat} (hb : b < cur) :
    cls'[b]!.bits = cls[b]!.bits ∧ cls'[b]!.k = cls[b]!.k ∧ cls'[b]!.a0 = cls[b]!.a0 ∧
      (cls[b]!.bits ≠ 0 → ∃ r < rows + 1, cls'[b]!.offset = some (r * np) ∧
        (rowOf.set! cls[cur]!.key (some (rows * np)))[cls[b]!.key]! = some (r * np) ∧
        ∀ n < np, o'[r * np + n]! = classOffset es rinv cls[b]! n) := by
  obtain ⟨e1, e2, e3, e4⟩ := h.2.2.2.2.1 b hb
  refine ⟨e1, e2, e3, fun hb0 ↦ (e4 hb0).elim fun r ⟨hr, ho, hro, hv⟩ ↦
    ⟨r, by lia, ho, ?_, fun n hn ↦ by rw [hrow.getElem!_of_lt hr hn, hv n hn]⟩⟩
  rw [Array.getElem!_set!_ne _ _ _ _ (fun hk ↦ hf.2 b hb hb0 hk.symm), hro]

-- The table of the rows with the row of the class `cur` with a pattern at its key holds a row only
-- at the key of a class up to `cur` with a pattern.
private theorem ClassRowsInvariant.exists_of_isSome_set! {cls : Vector NumClass 64}
    {es : Array SieveEntry} {rinv : Array (Array Nat)} {np size cur : Nat}
    {cls' : Vector NumClass 64} {o : Array Nat} {rowOf : Array (Option Nat)} {rows : Nat}
    (h : ClassRowsInvariant cls es rinv np size cur cls' o rowOf rows) (hb : cls[cur]!.bits ≠ 0)
    (v : Option Nat) (K : Nat) (hK : (rowOf.set! cls[cur]!.key v)[K]!.isSome) :
    ∃ b < cur + 1, cls[b]!.bits ≠ 0 ∧ cls[b]!.key = K := by
  by_cases hk : cls[cur]!.key = K
  · exact ⟨cur, by lia, hb, hk⟩
  · rw [Array.getElem!_set!_ne _ _ _ _ hk] at hK
    exact (h.2.2.2.2.2 K hK).elim fun b ⟨hb', h'⟩ ↦ ⟨b, by lia, h'⟩

/-- A class with a pattern whose key has no row gets a new row, after the rows made so far: it is
the first with its key, and the earlier rows keep their offsets. -/
theorem ClassRowsInvariant.newRow {cls : Vector NumClass 64} {es : Array SieveEntry}
    {rinv : Array (Array Nat)} {np size : Nat} {pref suff : List Nat} {cur : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) (hwf : ∀ b < 64, cls[b]!.WF)
    (hsize : firstKeys cls 64 * np ≤ size) {cls' : Vector NumClass 64} {o : Array Nat}
    {rowOf : Array (Option Nat)} {rows : Nat}
    (h : ClassRowsInvariant cls es rinv np size pref.length cls' o rowOf rows) (hc : cur < 64)
    (hb : ¬(cls'[cur].bits == 0) = true) {x : Option Nat} (hnone : ∀ row, x = some row → False)
    (hx : rowOf[2 ^ cls'[cur].k + cls'[cur].a0]! = x) {o' : Array Nat}
    (hrow : RowInvariant es rinv cls'[cur] (rows * np) o (ForIn.toList [:np]).length o') :
    ClassRowsInvariant cls es rinv np size (pref ++ [cur]).length
      (cls'.set cur { cls'[cur] with offset := some (rows * np) } hc) o'
      (rowOf.set! (2 ^ cls'[cur].k + cls'[cur].a0) (some (rows * np))) (rows + 1) := by
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at *
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at hrow
  have hcur : cls'[cur] = cls[cur]! := getElem!_pos cls' cur hc ▸ h.2.2.2.1 cur hc (Nat.le_refl _)
  rw [hcur, beq_iff_eq] at hb
  rw [hcur] at hrow
  rw [hcur, ← NumClass.key] at hx ⊢
  have hf := h.isFirstKey hb (by cases x <;> first | exact hx | exact absurd rfl (hnone _))
  have hlt := h.add_one_mul_le hf hc hsize
  have hK := (hwf cur hc).key_lt_two_pow_numStrides
  refine ⟨hrow.1.trans h.1, by simp [h.2.1], by simp [h.2.2.1, firstKeys_succ, hf],
    fun b hb' hb'' ↦ ?_, fun b hb' ↦ ?_, h.exists_of_isSome_set! hb _⟩
  · simp only [Vector.getElem!_set hc hb', show cur ≠ b by lia, ↓reduceIte]
    exact h.2.2.2.1 b hb' (by lia)
  · rw [Vector.getElem!_set hc (by lia)]
    split <;> rename_i hcb
    · subst hcb
      exact ⟨rfl, rfl, rfl, fun _ ↦ ⟨rows, by lia, rfl, Array.getElem!_set!_self _ _ _ (h.2.1 ▸ hK),
        fun n hn ↦ hrow.getElem!_row (h.1 ▸ hlt) hn⟩⟩
    · exact h.entry_newRow hf hrow (by lia)

attribute [local irreducible] ClassRowsInvariant RowInvariant in
open Std.WP Lean.Order in
/-- Each class with a pattern gets the row of its packing, whose offset for the `n`-th modulus is
`Ratpoints.Sieve.classOffset`, when the array of the offsets has room for a row of `np` offsets for
each distinct packing; the classes keep their patterns, strides and residues. -/
@[spec]
theorem classRows_spec (cls : Vector NumClass 64) (es : Array SieveEntry)
    (rinv : Array (Array Nat)) (np : Nat) (offsets : Array Nat) :
    ⦃ (∀ b < 64, cls[b]!.WF) ∧ firstKeys cls 64 * np ≤ offsets.size ⦄
    classRows cls es rinv np offsets
    ⦃ fun r ↦ r.2.size = offsets.size ∧ ∀ b < 64, r.1[b]!.bits = cls[b]!.bits ∧
        r.1[b]!.k = cls[b]!.k ∧ r.1[b]!.a0 = cls[b]!.a0 ∧ (¬cls[b]!.bits = 0 →
          ∃ pos, r.1[b]!.offset = some pos ∧
            ∀ n < np, r.2[pos + n]! = classOffset es rinv cls[b]! n) ⦄ := by
  vcgen [classRows] invariants
  · fun pref _ s ↦ ClassRowsInvariant cls es rinv np offsets.size pref.length s.1 s.2.1 s.2.2.1
      s.2.2.2
  · by
      rename_i offs _ rows _ hb _ _ _
      exact fun pref _ o ↦ (fun {cl : NumClass} (_ : ¬(cl.bits == 0) = true) ↦
        RowInvariant es rinv cl (rows * np) offs pref.length o) hb
  all_goals try simp only at *
  all_goals first
    | exact classRowsInvariant_init cls es rinv np offsets
    | exact ClassRowsInvariant.post ‹_›
    | exact ClassRowsInvariant.skip ‹_› ‹_› _ ‹_›
    | exact ClassRowsInvariant.reuse ‹_› ‹_ ∧ _›.1 ‹_› _ ‹_›
    | exact rowInvariant_nil _ _ _ _ _
    | exact ClassRowsInvariant.newRow ‹_› ‹_ ∧ _›.1 ‹_ ∧ _›.2 ‹_› _ ‹_› ‹_› ‹_› ‹_›
    | exact RowInvariant.set! ‹_› ‹_›

/-! ### The offsets of the rows -/

/-- `x` halved `n` times modulo `p` (`Ratpoints.Sieve.halve`). -/
def halveIter (p : Nat) : Nat → Nat → Nat
  | 0, x => x
  | n + 1, x => halve (halveIter p n x) p

/-- The chain of halvings of `x` modulo `p` of `class_offsets`, `x, x / 2, …` modulo `p`, `n` of
them. -/
def halveChain (p n x : Nat) : List Nat := (List.range n).map (halveIter p · x)

theorem halve_lt {x p : Nat} (hx : x < p) : halve x p < p := by
  simp only [halve]
  split <;> lia

theorem two_mul_halve_mod {x p : Nat} (hp : p % 2 = 1) : 2 * halve x p % p = x % p := by
  simp only [halve]
  split
  · rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by lia)), Nat.add_mod_right]
  · rw [Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero (by lia))]

theorem halveIter_lt {x p : Nat} (hx : x < p) (n : Nat) : halveIter p n x < p := by
  induction n with
  | zero => exact hx
  | succ n ih => exact halve_lt ih

/-- Halving `n` times modulo the odd `p` divides by `2 ^ n` modulo `p`. -/
theorem halveIter_mul_two_pow_mod {p : Nat} (hp : p % 2 = 1) (x n : Nat) :
    halveIter p n x * 2 ^ n % p = x % p := by
  induction n with
  | zero => simp [halveIter]
  | succ n ih =>
    rw [halveIter, Nat.pow_succ, Nat.mul_comm (2 ^ n), ← Nat.mul_assoc, Nat.mul_mod,
      Nat.mul_comm _ 2, two_mul_halve_mod hp, ← Nat.mul_mod, ih]

/-- The inverse `x₀` of `L` modulo the odd `p`, halved `k` times, is the inverse of `2 ^ k L`. -/
theorem halveIter_mul_two_pow_mul_mod {p x0 L : Nat} (hp : p % 2 = 1) (hx : x0 * L % p = 1)
    (k : Nat) : halveIter p k x0 * (2 ^ k * L) % p = 1 := by
  rw [← Nat.mul_assoc, Nat.mul_mod, halveIter_mul_two_pow_mod hp, ← Nat.mul_mod, hx]

theorem getElem!_toArray_halveChain (p n x : Nat) {k : Nat} (hk : k < n) :
    (halveChain p n x).toArray[k]! = halveIter p k x := by
  simp [halveChain, hk]

/-- The offset `off` of the row of the packing of the class `cl` for the sieve entry `e` with its
inverses of the strides: `off` lies between `Ratpoints.rowBias` and `Ratpoints.rowBias + 2 p`, it
shifts the rows so that bit `t` of the bit array with the word number `w` stands for the numerator
`a₀ + 2 ^ k (Ratpoints.rbaLength w + t)` (`off 2 ^ k Ratpoints.rbaLength ≡ a₀ (mod p)`), and the
inverse of the stride `2 ^ k` modulo `p` is entry `k` of `dinv`. -/
structure SieveEntry.PackedFor (e : SieveEntry) (cl : NumClass) (off : Nat) : Prop where
  /-- The modulus is positive. -/
  pos : 0 < e.p
  /-- The modulus is at most `Ratpoints.maxPrimeEven`. -/
  le_maxPrimeEven : e.p ≤ maxPrimeEven
  /-- The offset is at least `Ratpoints.rowBias`. -/
  rowBias_le : rowBias ≤ off
  /-- The offset is below `Ratpoints.rowBias + 2 p`. -/
  lt_rowBias_add : off < rowBias + 2 * e.p
  /-- The offset times `2 ^ k Ratpoints.rbaLength` is the residue `a₀` modulo the modulus. -/
  mul_mod : off * (2 ^ cl.k * rbaLength) % e.p = cl.a0 % e.p
  /-- Entry `k` of `dinv` is the inverse of `2 ^ k` modulo the modulus. -/
  dinv_mul_mod : e.dinv[cl.k]! * 2 ^ cl.k % e.p = 1
  /-- Entry `k` of `dinv` is below the modulus. -/
  dinv_lt : e.dinv[cl.k]! < e.p

/-- `Ratpoints.Sieve.SieveEntry.PackedFor` reads only the stride and the residue of the class. -/
theorem SieveEntry.PackedFor.congr {e : SieveEntry} {cl cl' : NumClass} {off : Nat}
    (h : e.PackedFor cl off) (hk : cl'.k = cl.k) (ha : cl'.a0 = cl.a0) : e.PackedFor cl' off :=
  ⟨h.pos, h.le_maxPrimeEven, h.rowBias_le, h.lt_rowBias_add, hk ▸ ha ▸ h.mul_mod,
    hk ▸ h.dinv_mul_mod, hk ▸ h.dinv_lt⟩

/-- The sieve spec of a modulus with the offset of the packing of a class has the modulus and the
offset in the range that the reductions of the row indices need. -/
theorem SieveEntry.PackedFor.fits {e : SieveEntry} {cl : NumClass} {off : Nat}
    (h : e.PackedFor cl off) (row : Array UInt64) : SieveSpec.Fits ⟨e.p, off, row⟩ :=
  ⟨h.pos, h.le_maxPrimeEven, h.rowBias_le, h.lt_rowBias_add⟩

/-- Every class with a pattern among `cls` has a row of offsets in the array `offsets`, at the
position `pos` that it holds, with the offset for the `n`-th sieve entry of `es` at `pos + n`. -/
def OffsetsFor (cls : Vector NumClass 64) (es : List SieveEntry) (offsets : Array Nat) : Prop :=
  ∀ b < 64, cls[b]!.bits ≠ 0 → ∃ pos, cls[b]!.offset = some pos ∧
    ∀ n (h : n < es.length), es[n].PackedFor cls[b]! offsets[pos + n]!

/-- The rows of offsets of the classes for the sieve entries `es` serve the first `k` of them. -/
theorem OffsetsFor.take {cls : Vector NumClass 64} {es : List SieveEntry} {offsets : Array Nat}
    (h : OffsetsFor cls es offsets) (k : Nat) : OffsetsFor cls (es.take k) offsets :=
  fun b hb hb0 ↦
    have ⟨pos, hpos, hn⟩ := h b hb hb0
    ⟨pos, hpos, fun n hn' ↦ by
      rw [List.getElem_take]
      exact hn n (Nat.lt_of_lt_of_le hn' (List.length_take_le' _ _))⟩

/-- The offset that `class_offsets` computes for the class `cl` and the sieve entry `e`, from the
inverse of `2 ^ k Ratpoints.rbaLength` that the halvings give, is that of the packing. -/
theorem SieveEntry.Packable.packedFor {e : SieveEntry} (he : e.Packable) {cl : NumClass}
    (hcl : cl.WF) {kmax : Nat} (hk : cl.k ≤ kmax) :
    SieveEntry.PackedFor { e with dinv := (halveChain e.p (kmax + 1) 1).toArray } cl
      (mulMod (cl.a0 * halveIter e.p cl.k e.rbainv) e.p e.magic + e.bias) := by
  have hp0 : 0 < e.p := Nat.lt_trans Nat.zero_lt_one he.one_lt
  have ha := hcl.a0_lt_sixty_four
  rw [he.magic_eq, mulMod_magic hp0 (mul_mul_lt_two_pow_64 (by lia) (halveIter_lt he.rbainv_lt cl.k)
    he.le_maxPrimeEven)]
  have := Nat.mod_lt (cl.a0 * halveIter e.p cl.k e.rbainv) hp0
  have := he.bias_lt
  have := he.rowBias_le_bias
  have hk' := Nat.lt_succ_of_le hk
  refine ⟨hp0, he.le_maxPrimeEven, by lia, by lia, Nat.mul_mod_add_mul_mod_eq_mod
    (halveIter_mul_two_pow_mul_mod he.odd he.rbainv_mul_mod cl.k) he.bias_mod, ?_, ?_⟩
  · simp only [getElem!_toArray_halveChain _ _ _ hk']
    rw [halveIter_mul_two_pow_mod he.odd, Nat.mod_eq_of_lt he.one_lt]
  · simp only [getElem!_toArray_halveChain _ _ _ hk']
    exact halveIter_lt he.one_lt _

/-! ### The loops of the row offsets -/

/-- The invariant of the loop of `Ratpoints.Sieve.classOffsets` that finds the largest stride
exponent: the classes below `m` with a pattern have stride exponents at most `kmax`. -/
def KmaxInvariant (cls : Vector NumClass 64) (m kmax : Nat) : Prop :=
  ∀ b < m, cls[b]!.bits ≠ 0 → cls[b]!.k ≤ kmax

theorem kmaxInvariant_nil (cls : Vector NumClass 64) : KmaxInvariant cls ([] : List Nat).length 0 :=
  nofun

theorem KmaxInvariant.append_of_le {cls : Vector NumClass 64} {pref suff : List Nat}
    {cur kmax kmax' : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) (h : KmaxInvariant cls pref.length kmax)
    (hc : cur < 64) (hle : kmax ≤ kmax') (hk : cls[cur].bits ≠ 0 → cls[cur].k ≤ kmax') :
    KmaxInvariant cls (pref ++ [cur]).length kmax' := by
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at *
  intro b hb hb0
  rcases Nat.lt_succ_iff_lt_or_eq.mp hb with hb | rfl
  · exact Nat.le_trans (h b hb hb0) hle
  · rw [getElem!_pos cls b hc] at hb0 ⊢
    exact hk hb0

theorem KmaxInvariant.append_of_lt {cls : Vector NumClass 64} {pref suff : List Nat}
    {cur kmax : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) (h : KmaxInvariant cls pref.length kmax)
    (hc : cur < 64) (hb : (cls[cur].bits != 0 && decide (kmax < cls[cur].k)) = true) :
    KmaxInvariant cls (pref ++ [cur]).length cls[cur].k :=
  h.append_of_le hl hc (by simp at hb; lia) fun _ ↦ Nat.le_refl _

theorem KmaxInvariant.append_of_not_lt {cls : Vector NumClass 64} {pref suff : List Nat}
    {cur kmax : Nat}
    (hl : ForIn.toList [:64] = pref ++ cur :: suff) (h : KmaxInvariant cls pref.length kmax)
    (hc : cur < 64) (hb : ¬(cls[cur].bits != 0 && decide (kmax < cls[cur].k)) = true) :
    KmaxInvariant cls (pref ++ [cur]).length kmax :=
  h.append_of_le hl hc (Nat.le_refl _) fun h0 ↦ by simp [h0] at hb; lia

/-- The invariant of the loop over the halvings of `Ratpoints.Sieve.classOffsets` for the modulus
`p` and the inverse `x₀` of `Ratpoints.rbaLength`, after `j` steps: `d` and `x` are `1` and `x₀`
halved `j` times, and the arrays `dinv` and `ri` hold the chains of the halvings so far. -/
def HalvingInvariant (p x0 j : Nat) (s : Nat × Nat × Array Nat × Array Nat) : Prop :=
  s.1 = halveIter p j 1 ∧ s.2.1 = halveIter p j x0 ∧ s.2.2.1.toList = halveChain p j 1 ∧
    s.2.2.2.toList = halveChain p j x0

theorem halvingInvariant_zero (p x0 : Nat) :
    HalvingInvariant p x0 ([] : List Nat).length (1, x0, #[], #[]) :=
  ⟨rfl, rfl, rfl, rfl⟩

theorem HalvingInvariant.push {p x0 : Nat} {pref : List Nat} {cur : Nat}
    {s : Nat × Nat × Array Nat × Array Nat} (h : HalvingInvariant p x0 pref.length s) :
    HalvingInvariant p x0 (pref ++ [cur]).length
      (halve s.1 p, halve s.2.1 p, s.2.2.1.push s.1, s.2.2.2.push s.2.1) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  simp only [HalvingInvariant, List.length_append, List.length_singleton, halveIter, h1, h2,
    Array.toList_push, h3, h4, halveChain, List.range_succ, List.map_append, List.map_cons,
    List.map_nil, and_self]

/-- The invariant of the loop over the sieve entries of `Ratpoints.Sieve.classOffsets` after the
entries `pref`: the entries so far with their inverses of the strides, and the chains of the
halvings of their inverses of `Ratpoints.rbaLength`, for the strides up to `kmax`. -/
def EntriesInvariant (kmax : Nat) (pref : List SieveEntry)
    (s : Array SieveEntry × Array (Array Nat)) : Prop :=
  s.1.toList = pref.map (fun e ↦ { e with dinv := (halveChain e.p (kmax + 1) 1).toArray }) ∧
    s.2.toList = pref.map fun e ↦ (halveChain e.p (kmax + 1) e.rbainv).toArray

theorem entriesInvariant_nil (kmax : Nat) : EntriesInvariant kmax [] (#[], #[]) :=
  ⟨rfl, rfl⟩

theorem EntriesInvariant.push {kmax : Nat} {pref : List SieveEntry} {e : SieveEntry}
    {es' : Array SieveEntry} {rinv : Array (Array Nat)} (h : EntriesInvariant kmax pref (es', rinv))
    {s : Nat × Nat × Array Nat × Array Nat}
    (hs : HalvingInvariant e.p e.rbainv (ForIn.toList [:kmax + 1]).length s) :
    EntriesInvariant kmax (pref ++ [e])
      (es'.push { e with dinv := s.2.2.1 }, rinv.push s.2.2.2) := by
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at hs
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  refine ⟨?_, ?_⟩
  · simp only [Array.toList_push, h1, List.map_append, List.map_cons, List.map_nil]
    rw [← hs.2.2.1, Array.toArray_toList]
  · simp only [Array.toList_push, h2, List.map_append, List.map_cons, List.map_nil]
    rw [← hs.2.2.2, Array.toArray_toList]

/-- The offset of the row of a class for the `n`-th entry, from the arrays that the halvings give,
is that of the packing of the class for that entry with its inverses of the strides. -/
theorem EntriesInvariant.packedFor {kmax : Nat} {es : List SieveEntry} {es' : Array SieveEntry}
    {rinv : Array (Array Nat)} (he : EntriesInvariant kmax es (es', rinv))
    (hes : ∀ e ∈ es, e.Packable) {cl : NumClass} (hcl : cl.WF) (hk : cl.k ≤ kmax) {n : Nat}
    (hn : n < es.length) :
    es'[n]!.PackedFor cl (classOffset es' rinv cl n) := by
  obtain ⟨h1, h2⟩ := he
  simp only at h1 h2
  simp only [classOffset, Array.getElem!_of_toList_eq_map h1 hn,
    Array.getElem!_of_toList_eq_map h2 hn, getElem!_toArray_halveChain _ _ _ (Nat.lt_succ_of_le hk)]
  exact (hes _ (List.getElem_mem hn)).packedFor hcl hk

/-- The classes after `class_offsets` have the rows of their packings for the entries with their
inverses of the strides. -/
theorem classOffsets_post {cls cls' : Vector NumClass 64} {es : List SieveEntry} {kmax : Nat}
    {es' : Array SieveEntry} {rinv : Array (Array Nat)} {size : Nat} {o : Array Nat}
    (hpre : (∀ e ∈ es, e.Packable) ∧ (∀ b < 64, cls[b]!.WF) ∧ firstKeys cls 64 * es.length ≤ size)
    (hk : KmaxInvariant cls (ForIn.toList [:64]).length kmax)
    (he : EntriesInvariant kmax es (es', rinv))
    (hr : o.size = size ∧ ∀ b < 64, cls'[b]!.bits = cls[b]!.bits ∧ cls'[b]!.k = cls[b]!.k ∧
      cls'[b]!.a0 = cls[b]!.a0 ∧ (¬cls[b]!.bits = 0 → ∃ pos, cls'[b]!.offset = some pos ∧
        ∀ n < es.length, o[pos + n]! = classOffset es' rinv cls[b]! n)) :
    (∀ b < 64, cls'[b]!.bits = cls[b]!.bits ∧ cls'[b]!.k = cls[b]!.k ∧ cls'[b]!.a0 = cls[b]!.a0) ∧
      (∃ f : SieveEntry → Array Nat, es'.toList = es.map fun e ↦ { e with dinv := f e }) ∧
      OffsetsFor cls' es'.toList o := by
  rw [Std.Legacy.Range.length_toList] at hk
  obtain ⟨hes, hwf, -⟩ := hpre
  replace hr := hr.2
  refine ⟨fun b hb ↦ ⟨(hr b hb).1, (hr b hb).2.1, (hr b hb).2.2.1⟩, ⟨_, he.1⟩, fun b hb hb0 ↦ ?_⟩
  obtain ⟨h1, h2, h3, h4⟩ := hr b hb
  obtain ⟨pos, hpos, hv⟩ := h4 (h1 ▸ hb0)
  have hn (n : Nat) (h : n < es'.toList.length) : n < es.length := by
    rwa [he.1, List.length_map] at h
  refine ⟨pos, hpos, fun n h ↦ ?_⟩
  rw [hv n (hn n h), Array.getElem_toList, ← getElem!_pos es' n (by simpa using h)]
  exact (he.packedFor hes (hwf b hb) (hk b hb (h1 ▸ hb0)) (hn n h)).congr h2 h3

attribute [local irreducible] KmaxInvariant EntriesInvariant HalvingInvariant in
open Std.WP Lean.Order in
/-- The row offsets of the classes, once the moduli of the run are known: each class with a pattern
gets the row of its packing in the array of the offsets, for the sieve entries with their inverses
of the strides, when the array has room for a row for each distinct packing; the classes keep their
patterns, strides and residues, and the entries are those of the run with the inverses of the
strides. -/
@[spec]
theorem classOffsets_spec (cls : Vector NumClass 64) (es : List SieveEntry) (offsets : Array Nat) :
    ⦃ (∀ e ∈ es, e.Packable) ∧ (∀ b < 64, cls[b]!.WF) ∧
        firstKeys cls 64 * es.length ≤ offsets.size ⦄
    classOffsets cls es offsets
    ⦃ fun r ↦ (∀ b < 64, r.1[b]!.bits = cls[b]!.bits ∧ r.1[b]!.k = cls[b]!.k ∧
          r.1[b]!.a0 = cls[b]!.a0) ∧
        (∃ f : SieveEntry → Array Nat, r.2.1 = es.map fun e ↦ { e with dinv := f e }) ∧
        OffsetsFor r.1 r.2.1 r.2.2 ⦄ := by
  vcgen [classOffsets] invariants
  · fun pref _ kmax ↦ KmaxInvariant cls pref.length kmax
  · by rename_i kmax _; exact fun pref _ s ↦ EntriesInvariant kmax pref s
  · by rename_i e _ _ _ _ _; exact fun pref _ s ↦ HalvingInvariant e.p e.rbainv pref.length s
  all_goals try simp only at *
  all_goals first
    | exact kmaxInvariant_nil cls
    | exact entriesInvariant_nil _
    | exact ‹_ ∧ _›.2
    | exact halvingInvariant_zero _ _
    | exact HalvingInvariant.push ‹_›
    | exact EntriesInvariant.push ‹_› ‹_›
    | exact KmaxInvariant.append_of_lt ‹_› ‹_› _ ‹_›
    | exact KmaxInvariant.append_of_not_lt ‹_› ‹_› _ ‹_›
    | exact classOffsets_post ‹_› ‹_› ‹_› ‹_›

/-! ### The residues of a denominator -/

/-- The first branch of `fill_bp_list`: for `b ≤ Ratpoints.mulModLimit / Ratpoints.maxPrimeEven`
the product `b dinv` is reduced at once, exactly. -/
theorem mulMod_mul_magic {b d p : Nat} (hp : 0 < p) (hpm : p ≤ maxPrimeEven) (hd : d < p)
    (hb : b ≤ mulModLimit / maxPrimeEven) : mulMod (b * d) p (magic p) = b * d % p :=
  mulMod_magic hp (mul_lt_two_pow_64_of_le_mulModLimit (mul_le_mulModLimit_of_le_div hb hd hpm)
    (Nat.le_trans hpm maxPrimeEven_le_two_pow_32))

/-- The second branch of `fill_bp_list`: for `b ≤ Ratpoints.mulModLimit`, `b` is reduced first and
then its product with `dinv`, both exactly. -/
theorem mulMod_mulMod_mul_magic {b d p : Nat} (hp : 0 < p) (hpm : p ≤ maxPrimeEven) (hd : d < p)
    (hb : b ≤ mulModLimit) : mulMod (mulMod b p (magic p) * d) p (magic p) = b * d % p := by
  rw [mulMod_magic hp (mul_lt_two_pow_64_of_le_mulModLimit hb
      (Nat.le_trans hpm maxPrimeEven_le_two_pow_32)),
    mulMod_magic hp (mul_mul_lt_two_pow_64 (mod_le_two_pow_10 b hp hpm) hd hpm), Nat.mod_mul_mod]

/-- The third branch of `fill_bp_list`: `b` reduced by the helper `mod` of the C code, then the
product with `dinv` exactly. -/
theorem mulMod_toNat_modLong_mul_magic {b d p : Nat} (hp : 0 < p) (hpm : p ≤ maxPrimeEven)
    (hd : d < p) : mulMod ((modLong b p).toNat * d) p (magic p) = b * d % p := by
  have : (modLong b p).toNat = b % p := by rw [modLong_eq_emod _ (Int.natCast_nonneg _)]; lia
  rw [this, mulMod_magic hp (mul_mul_lt_two_pow_64 (mod_le_two_pow_10 b hp hpm) hd hpm),
    Nat.mod_mul_mod]

/-- `fill_bp_list` computes `b dinv[k] mod p` for every modulus `0 < p ≤ Ratpoints.maxPrimeEven`
with `dinv[k] < p`, in each of its three branches, with the reciprocals of the moduli. -/
theorem fillBpList_eq_map {b k : Nat} {es : List SieveEntry}
    (hes : ∀ e ∈ es, 0 < e.p ∧ e.p ≤ maxPrimeEven ∧ e.dinv[k]! < e.p) :
    fillBpList b k es (es.map (magic ·.p)) = es.map fun e ↦ b * e.dinv[k]! % e.p := by
  simp only [fillBpList, List.zipWith_map_right, List.zipWith_self]
  split
  · exact List.map_congr_left fun e he ↦ mulMod_mul_magic (hes e he).1 (hes e he).2.1
      (hes e he).2.2 ‹_›
  split
  · exact List.map_congr_left fun e he ↦ mulMod_mulMod_mul_magic (hes e he).1 (hes e he).2.1
      (hes e he).2.2 ‹_›
  · exact List.map_congr_left fun e he ↦ mulMod_toNat_modLong_mul_magic (hes e he).1
      (hes e he).2.1 (hes e he).2.2

end Sieve

end Ratpoints

end
