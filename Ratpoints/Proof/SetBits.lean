/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Candidate
public import Std.WP

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers
import Std.Tactic.Do

/-!
# The set bits of a word

The bit of a numerator or a bit number in a word (`Ratpoints.Sieve.classBit`), the contract of the
loop of the lowest set bit of a word (`Ratpoints.Sieve.ctz`), and the invariant of a `while` loop
that walks through the set bits of a word, lowest first, clearing each with `x &&& (x - 1)`
(`Ratpoints.Sieve.WalkWhileInvariant`), which the walks of the extraction, of the packing of the
classes, of the 2-adic information and of the word shape share.

## Main definitions

* `Ratpoints.Sieve.classBit`: whether a word lets `a` through, bit `a mod 64` of the word.
* `Ratpoints.Sieve.ClearedBelow`: a word with the bits of another below a position cleared.
* `Ratpoints.Sieve.WalkWhileInvariant`: the invariant of a walk through the set bits of a word,
  lowest first.
* `Ratpoints.Sieve.bitNumbers`: the bit numbers of the set bits of some words, in increasing order.

## Main statements

* `Ratpoints.Sieve.ctz_spec`, `Ratpoints.Sieve.run_ctz`: for a word other than `0`, the loop of
  `Ratpoints.Sieve.ctz` ends with the number of its trailing zeros.
* `Ratpoints.Sieve.ClearedBelow.filter_range_succ_ctz`,
  `Ratpoints.Sieve.ClearedBelow.exists_lt_succ_iff`: the set bits of the word up to the lowest set
  bit of the word with the bits below `k` cleared.

## Implementation notes

The file uses Lean core and `Std` only; the lemmas on words that are not about the model are in
`Ratpoints.Proof.Bits`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

universe u

/-! ### The bit of a number in a word -/

/-- Whether the word `cw` lets `a` through: bit `a mod 64` of `cw`. For the 2-adic word of a class
of denominators (`Ratpoints.Sieve.twoAdic`), `a` is a numerator. For the pattern of a class in its
packing (`Ratpoints.Sieve.NumClass.bits`), which `Ratpoints.Sieve.andRows` writes into every word of
a piece, `a` is a bit number: bit `a mod 64` of every word stands for the bits `≡ a (mod 64)`, since
`64` divides `Ratpoints.rbaLength`. `Ratpoints.Sieve.NumClass.Packs.classBit_bits` converts between
the two. -/
def classBit (cw : UInt64) (a : Int) : Bool := cw.toBitVec.getLsbD (a % 64).toNat

theorem classBit_eq (cw : UInt64) (a : Int) : classBit cw a = cw.toBitVec.getLsbD (a % 64).toNat :=
  rfl

@[simp]
theorem classBit_zero (a : Int) : classBit 0 a = false := by
  simp [classBit_eq]

/-! ### The lowest set bit -/

/-- The invariant of the loop of `Ratpoints.Sieve.ctz` on a word `w ≠ 0`: the word is `w` shifted
right by the count, the count is at most the position of the lowest set bit of `w`, and it is that
position at the exit. -/
def CtzInvariant (w : UInt64) : Std.WP.WhileInvariant (UInt64 × Nat) Prop :=
  .mk fun exit s ↦ s.1.toBitVec = w.toBitVec >>> s.2 ∧ s.2 ≤ w.toBitVec.ctz.toNat ∧
    (exit = true → s.2 = w.toBitVec.ctz.toNat)

/-- The loop ends, since the count stays at most the position of the lowest set bit, which is below
64. -/
@[spec]
theorem ctz_spec (w : UInt64) : ⦃ w ≠ 0 ⦄ ctz w ⦃ fun t ↦ t = w.toBitVec.ctz.toNat ⦄ := by
  vcgen [ctz] invariants
  · CtzInvariant w
  · Std.WP.Variant.ofMeasure fun s : UInt64 × Nat ↦ 64 - s.2
  all_goals simp [CtzInvariant] at *
  all_goals grind [UInt64.ne_ctz_of_and_one_eq_zero, UInt64.eq_ctz_of_and_one_ne_zero,
    UInt64.toNat_ctz_lt, BitVec.shiftRight_add]

theorem run_ctz {w : UInt64} (hw : w ≠ 0) : Id.run (ctz w) = w.toBitVec.ctz.toNat :=
  Std.WP.Id.of_run_eq_wp rfl _ ((ctz_spec w).le_wp hw)

/-! ### The walks through the set bits of a word -/

/-- The word `x` is the word `x0` with its bits below `k ≤ 64` cleared. -/
def ClearedBelow (x0 : UInt64) (k : Nat) (x : UInt64) : Prop :=
  k ≤ 64 ∧ ∀ t, x.toBitVec.getLsbD t = (x0.toBitVec.getLsbD t && decide (k ≤ t))

theorem clearedBelow_zero (x0 : UInt64) : ClearedBelow x0 0 x0 :=
  ⟨Nat.zero_le _, fun _ ↦ by simp⟩

/-- The lowest set bit of `x` is a set bit of `x0`, at `k` or above. -/
theorem ClearedBelow.getLsbD_ctz_and_le_ctz {x0 x : UInt64} {k : Nat} (h : ClearedBelow x0 k x)
    (hx : x ≠ 0) :
    x0.toBitVec.getLsbD x.toBitVec.ctz.toNat = true ∧ k ≤ x.toBitVec.ctz.toNat := by
  simpa [h.2] using UInt64.getLsbD_ctz hx

/-- Clearing the lowest set bit of `x` clears the bits of `x0` up to that bit. -/
theorem ClearedBelow.and_sub_one {x0 x : UInt64} {k : Nat} (h : ClearedBelow x0 k x) (hx : x ≠ 0) :
    ClearedBelow x0 (x.toBitVec.ctz.toNat + 1) (x &&& (x - 1)) :=
  ⟨UInt64.toNat_ctz_lt hx, fun t ↦ by grind [h.2 t, h.getLsbD_ctz_and_le_ctz hx,
    UInt64.getLsbD_and_sub_one, BitVec.getLsbD_false_of_lt_ctz]⟩

/-- The set bits of `x0` up to the lowest set bit of `x` are those below `k`, then that bit, since
`x` has the bits of `x0` from `k` on. -/
theorem ClearedBelow.filter_range_succ_ctz {x0 x : UInt64} {k : Nat} (h : ClearedBelow x0 k x)
    (hx : x ≠ 0) :
    (List.range (x.toBitVec.ctz.toNat + 1)).filter (x0.toBitVec.getLsbD ·) =
      (List.range k).filter (x0.toBitVec.getLsbD ·) ++ [x.toBitVec.ctz.toNat] := by
  obtain ⟨hc, hk⟩ := h.getLsbD_ctz_and_le_ctz hx
  exact List.filter_range_succ_eq_append hk hc fun j _ _ ↦ by
    grind [h.2 j, BitVec.getLsbD_false_of_lt_ctz]

theorem ClearedBelow.filter_range_of_eq_zero {x0 : UInt64} {k : Nat} (h : ClearedBelow x0 k 0) :
    (List.range k).filter (x0.toBitVec.getLsbD ·) =
      (List.range 64).filter (x0.toBitVec.getLsbD ·) :=
  (List.filter_range_eq_of_le h.1 fun j hkj _ ↦ by simpa [hkj] using (h.2 j).symm).symm

/-- The set bits `j` of `x0` up to the lowest set bit of `x` that have the property `P` are those
below `k`, which `x` has cleared, and the lowest set bit of `x` if it has the property, a set bit of
`x0` too. -/
theorem ClearedBelow.exists_lt_succ_iff {x0 x : UInt64} {k : Nat} (h : ClearedBelow x0 k x)
    (hx : x ≠ 0) (P : Nat → Prop) :
    (∃ j < x.toBitVec.ctz.toNat + 1, x0.toBitVec.getLsbD j = true ∧ P j) ↔
      (∃ j < k, x0.toBitVec.getLsbD j = true ∧ P j) ∨ P x.toBitVec.ctz.toNat := by
  simpa [and_assoc, or_and_right, exists_or] using
    congrArg (∃ j ∈ ·, P j) (h.filter_range_succ_ctz hx)

theorem ClearedBelow.exists_lt_iff_of_eq_zero {x0 : UInt64} {k : Nat} (h : ClearedBelow x0 k 0)
    (P : Nat → Prop) :
    (∃ j < k, x0.toBitVec.getLsbD j = true ∧ P j) ↔
      ∃ j < 64, x0.toBitVec.getLsbD j = true ∧ P j := by
  simpa [and_assoc] using congrArg (∃ j ∈ ·, P j) h.filter_range_of_eq_zero

/-- The invariant of a `while` loop over the set bits of the word `x0`, lowest first, whose state is
a value of `σ` and the word, for a property `P k` of the value after the set bits below `k`: the
word is `x0` with its bits below some `k` cleared (`Ratpoints.Sieve.ClearedBelow`), the value has
the property `P k`, and the word is `0` at the exit. -/
def WalkWhileInvariant {σ : Type u} (x0 : UInt64) (P : Nat → σ → Prop) :
    Std.WP.WhileInvariant (σ × UInt64) Prop :=
  .mk fun exit s ↦ ∃ k, ClearedBelow x0 k s.2 ∧ P k s.1 ∧ (exit = true → s.2 = 0)

theorem walkWhileInvariant_self {σ : Type u} {x0 : UInt64} {P : Nat → σ → Prop} {s : σ}
    (h : P 0 s) :
    WalkWhileInvariant x0 P false (s, x0) :=
  ⟨0, clearedBelow_zero x0, h, nofun⟩

/-- The invariant after one step, with the lowest set bit of `w` cleared and the value `s'` with
the property `P` up to that bit, in the shape of the verification condition: the measure `w.toNat`
decreases. -/
theorem WalkWhileInvariant.and_sub_one {σ : Type u} {x0 w : UInt64} {P : Nat → σ → Prop}
    {s s' : σ} {mb : Nat} (h : w.toNat = mb ∧ WalkWhileInvariant x0 P false (s, w))
    (hw : (w != 0) = true)
    (hP : ∀ k, ClearedBelow x0 k w → P k s → P (w.toBitVec.ctz.toNat + 1) s') :
    (w &&& w - 1).toNat < mb ∧ WalkWhileInvariant x0 P false (s', w &&& w - 1) := by
  have hw' : w ≠ 0 := by simpa using hw
  obtain ⟨rfl, k, hcl, hs, -⟩ := h
  exact ⟨UInt64.toNat_and_sub_one_lt hw', _, hcl.and_sub_one hw', hP k hcl hs, nofun⟩

theorem WalkWhileInvariant.exit {σ : Type u} {x0 w : UInt64} {P : Nat → σ → Prop} {s : σ}
    {mb : Nat} (hw : ¬(w != 0) = true) (h : w.toNat = mb ∧ WalkWhileInvariant x0 P false (s, w)) :
    WalkWhileInvariant x0 P true (s, w) := by
  obtain ⟨-, k, hcl, hs, -⟩ := h
  exact ⟨k, hcl, hs, fun _ ↦ by simpa using hw⟩

theorem WalkWhileInvariant.exists_clearedBelow_zero {σ : Type u} {x0 w : UInt64}
    {P : Nat → σ → Prop} {s : σ} (h : WalkWhileInvariant x0 P true (s, w)) :
    ∃ k, ClearedBelow x0 k 0 ∧ P k s := by
  obtain ⟨k, hcl, hs, h0⟩ := h
  exact ⟨k, h0 rfl ▸ hcl, hs⟩

/-! ### The bit numbers of the set bits of words -/

/-- The bit numbers `base + 64 κ + t` of the set bits `t` of the words `words κ`, `κ < k`, in
increasing order. -/
def bitNumbers (words : Nat → UInt64) (base : Int) (k : Nat) : List Int :=
  (List.range k).flatMap fun κ ↦
    ((List.range 64).filter ((words κ).toBitVec.getLsbD ·)).map fun t : Nat ↦ base + 64 * κ + t

@[simp]
theorem bitNumbers_zero (words : Nat → UInt64) (base : Int) : bitNumbers words base 0 = [] :=
  rfl

theorem bitNumbers_succ (words : Nat → UInt64) (base : Int) (k : Nat) :
    bitNumbers words base (k + 1) = bitNumbers words base k ++
      ((List.range 64).filter ((words k).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ base + 64 * k + t := by
  rw [bitNumbers, List.range_succ (n := k), List.flatMap_append, List.flatMap_singleton,
    bitNumbers]

theorem bitNumbers_add (words : Nat → UInt64) (base : Int) (k m : Nat) :
    bitNumbers words base (k + m) =
      bitNumbers words base k ++ bitNumbers (words <| k + ·) (base + 64 * k) m := by
  rw [bitNumbers, List.range_add, List.flatMap_append, List.flatMap_map, ← bitNumbers]
  congr 1
  refine congrArg List.flatten (List.map_congr_left fun κ _ ↦ ?_)
  simp only [Int.natCast_add, Int.mul_add, Int.add_assoc]

theorem bitNumbers_prefix (words : Nat → UInt64) (base : Int) {k m : Nat} (h : k ≤ m) :
    bitNumbers words base k <+: bitNumbers words base m := by
  obtain ⟨l, hl⟩ := List.range_prefix_range h
  exact ⟨_, by rw [bitNumbers, bitNumbers, ← hl, List.flatMap_append]⟩

theorem bitNumbers_congr {words words' : Nat → UInt64} {k : Nat} (h : ∀ κ < k, words κ = words' κ)
    (base : Int) : bitNumbers words base k = bitNumbers words' base k :=
  congrArg List.flatten <| List.map_congr_left fun κ hκ ↦ by rw [h κ (List.mem_range.mp hκ)]

theorem bitNumbers_eq_nil {words : Nat → UInt64} {k : Nat} (h : ∀ κ < k, words κ = 0)
    (base : Int) : bitNumbers words base k = [] :=
  List.flatMap_eq_nil_iff.mpr fun κ hκ ↦ by simp [h κ (List.mem_range.mp hκ)]

/-- The bit numbers of the set bits of the words are the numbers `base, …, base + 64 k - 1` that
pass `p`, when bit `t` of word `κ` is `t < 64` and `p (base + 64 κ + t)`. -/
theorem bitNumbers_eq_filter {words : Nat → UInt64} {base : Int} {p : Int → Bool} {k : Nat}
    (h : ∀ κ < k, ∀ t, (words κ).toBitVec.getLsbD t = (decide (t < 64) && p (base + 64 * κ + t))) :
    bitNumbers words base k = ((List.range (64 * k)).map fun j : Nat ↦ base + j).filter p :=
  List.flatMap_range_map_filter h

end Sieve

end Ratpoints

end
