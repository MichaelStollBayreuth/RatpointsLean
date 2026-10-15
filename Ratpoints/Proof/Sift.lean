/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Packing
public import Ratpoints.Proof.Stages

import Ratpoints.Proof.BitRange
import Ratpoints.Proof.Bits
import Ratpoints.Proof.Sieve
import Std.Tactic.Do

/-!
# The contracts of the sieve of one denominator

The contracts of the components of the model on words from the walk through the set bits of a word
on, through the second stage and the extraction of one bit array, the scan of a piece and the bits
of one interval in pieces, up to the sieve of one denominator in the packing of its class, as
`@[spec]` theorems proved with `vcgen`, the program logic of Lean core, with loop invariants that
are named definitions. Up to the bits of one interval, the contracts speak of the bits `j` of the
packing of a class `cl` (`Ratpoints.Sieve.NumClass`), each standing for the numerator
`a₀ + 2 ^ k j` (`Ratpoints.Sieve.NumClass.numerator`), and of the tests of the bits that the rows of
the moduli read at their offsets (`Ratpoints.Sieve.SieveSpec.Reads`); the numerators come in with
the bits of the numerators `-H, …, H` of one denominator.

## Main definitions

* `Ratpoints.Sieve.packedReads`: the rows of the sieve entries for a denominator in the packing of a
  class, with the tests of the bits that they read.

## Main statements

* `Ratpoints.Sieve.walkWord_spec`: the walk through the set bits of a word appends the points of the
  numerators `a0 + step t` of its set bits `t`, in increasing order.
* `Ratpoints.Sieve.siftBitArray_spec`: in either arm of the second stage, one bit array appends the
  points of the numerators of the set bits of its words and-ed with the rows of the moduli of the
  second stage, in increasing order.
* `Ratpoints.Sieve.scanPiece_spec`: if the bits of a piece and-ed with the rows of the second stage
  are a test `keep` of the bits, the scan of the piece gives the points of the numerators of its
  bits that pass `keep`, in increasing order.
* `Ratpoints.Sieve.siftPiece_spec`: one piece with rows that read tests of the bits gives the points
  of the numerators of the bits that the masks at its two ends leave and that pass the pattern of
  the class (`Ratpoints.Sieve.classBit`) and the tests of the rows, in increasing order.
* `Ratpoints.Sieve.siftBits_spec`: the bits from `low` to `high` in pieces give the points of the
  numerators of those that pass the pattern of the class and the tests of the rows.
* `Ratpoints.Sieve.setRows_map`, `Ratpoints.Sieve.reads_of_mem_packedReads`: the rows of the
  residues `b dinv[k] mod p` at the offsets of the class read whether the rows of `b` admit the
  numerators of the bits (`Ratpoints.Sieve.SieveEntry.reads_row`).
* `Ratpoints.Sieve.flatMap_filter_bits_eq`: the bits of `numerators_to_bits` of the height in the
  packing of the class of a class word `w` give the numerators `-H, …, H` that pass `w`.
* `Ratpoints.Sieve.sift_spec`: the pieces of a denominator `0 < b < 2 ^ 63` in the packing of a
  class `cl` of the class word `w`, for `H < 2 ^ 63`, entries of the first two stages with their
  tables of inverses and the row offsets of the packing of `cl`, and entries of the third stage of
  the shape of `Ratpoints.Sieve.SieveEntry.IsPrimeEntry` with the reciprocals of their moduli, give
  what the brute-force reference finds over `b` and the numerators `-H, …, H` that pass `w` and
  survive the sieve entries of all three stages, mapped by `Ratpoints.Sieve.swapPoint` when the flag
  of the reversal is set; `Ratpoints.Sieve.toList_run_sift_eq_checkDen`: these are the points that
  the plain sieve of `b` with all the entries gives whose numerators pass `w`, mapped in the same
  way.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Words`, `Ratpoints.Proof.Stages`,
`Ratpoints.Proof.Packing` and `Ratpoints.Proof.BitRange` do, whose lemmas on bit arrays, rows,
walks, classes and the bits of an interval and whose contracts of the first, the second and the
third stage it builds on. The walk reads the test of a
candidate as its value (`Ratpoints.Sieve.acceptedPoints`), so that the contracts of the walk, of one
bit array, of the scan, of one piece and of one interval need nothing of the numerators and the
denominator; the hypotheses of the test on the words of the C code, `0 < b < 2 ^ 63` and
`|a| ≤ H < 2 ^ 63`, come in with the numerators `-H, …, H` of one denominator
(`Ratpoints.Sieve.acceptedPoints_eq_ite`). The contract of the run over the denominators, which
calls `Ratpoints.Sieve.sift` with the class of each denominator, is in
`Ratpoints.Proof.Denominators`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

universe u

/-! ### The walk through the set bits of a word -/

-- The test of a candidate, as a value for the contract of the walk: the walk's contract speaks of
-- its result, without the hypotheses of `Ratpoints.Sieve.accepted_spec`.
private theorem accepted_value (a : Int) (b : Nat) (checks : Thunk (List CheckSpec)) :
    ⦃ True ⦄ accepted a b checks ⦃ fun r ↦ r = Id.run (accepted a b checks) ⦄ :=
  ⟨fun _ ↦ rfl⟩

/-- `Ratpoints.Sieve.WalkWordInvariant.append_ctz` with the list `l` of the lowest set bit of `x`
given. -/
theorem WalkWordInvariant.append_ctz_of_eq {β : Type u} {g : Nat → List β} {x0 x : UInt64}
    {out0 out : Array β} {k : Nat} {l : List β} (h : WalkWordInvariant g x0 out0 k out)
    (hx : ClearedBelow x0 k x) (hx0 : x ≠ 0) (hl : g x.toBitVec.ctz.toNat = l) :
    WalkWordInvariant g x0 out0 (x.toBitVec.ctz.toNat + 1) (out ++ l.toArray) :=
  hl ▸ h.append_ctz hx hx0

/-- A set bit whose list is empty adds nothing. -/
theorem WalkWordInvariant.ctz_of_eq_nil {β : Type u} {g : Nat → List β} {x0 x : UInt64}
    {out0 out : Array β} {k : Nat} (h : WalkWordInvariant g x0 out0 k out)
    (hx : ClearedBelow x0 k x) (hx0 : x ≠ 0) (hl : g x.toBitVec.ctz.toNat = []) :
    WalkWordInvariant g x0 out0 (x.toBitVec.ctz.toNat + 1) out := by
  simpa using h.append_ctz_of_eq hx hx0 hl

/- The invariants of the walk are irreducible from here on: the verification conditions of
`Ratpoints.Sieve.walkWord` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] WalkWhileInvariant WalkWordInvariant

/-- The loop ends, since clearing the lowest set bit makes a word other than `0` smaller; the test
of a candidate is read as its value, `Ratpoints.Sieve.acceptedPoints`. -/
@[spec]
theorem walkWord_spec (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (checks : Thunk (List CheckSpec)) (x : UInt64) (a0 : Int) (step : Nat)
    (out : Array (Int × Int × Int)) :
    ⦃ True ⦄ walkWord w d b rev checks x a0 step out
    ⦃ fun out' ↦ out'.toList = out.toList ++
        (((List.range 64).filter (x.toBitVec.getLsbD ·)).map fun t : Nat ↦ a0 + step * t).flatMap
          (acceptedPoints w d b rev checks) ⦄ := by
  vcgen [walkWord, accepted_value] invariants
  · WalkWordWhileInvariant (fun t : Nat ↦ acceptedPoints w d b rev checks (a0 + step * t)) x out
  · Std.WP.Variant.ofMeasure fun s : UInt64 × Array (Int × Int × Int) ↦ s.1.toNat
  all_goals simp only [WalkWordWhileInvariant, Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals subst_vars
  all_goals first
    | exact walkWhileInvariant_self (walkWordInvariant_zero ..)
    | exact bne_iff_ne.mp ‹_›
    | exact WalkWhileInvariant.exit ‹_› ‹_›
    | exact WalkWhileInvariant.and_sub_one ‹_› ‹_› fun _ hcl hk ↦
        hk.append_ctz_of_eq hcl (bne_iff_ne.mp ‹_›) (ite_eq_left ‹true = _›.symm)
    | exact WalkWhileInvariant.and_sub_one ‹_› ‹_› fun _ hcl hk ↦
        hk.ctz_of_eq_nil hcl (bne_iff_ne.mp ‹_›) (ite_eq_right ‹_›)
    | grind [WalkWordInvariant.toList_eq, List.flatMap_map]

/-! ### The second stage and the extraction of one bit array -/

/-- The invariant of the loops of `Ratpoints.Sieve.siftBitArray` over the words of the bit array
with the word number `i`, after its first `k` words, for the words `words κ` that the walks go
through, the class `cl` and the points `g a` of a numerator `a`: `out` is `out0` followed by the
points of the numerators of the bits `rbaLength i + 64 κ + t` of the set bits `t` of the words
`κ < k` in the packing of `cl` (`Ratpoints.Sieve.NumClass.numerator`), in increasing order. -/
def SiftBitArrayInvariant (words : Nat → UInt64) (g : Int → List (Int × Int × Int)) (cl : NumClass)
    (i : Int) (out0 : Array (Int × Int × Int)) (k : Nat) (out : Array (Int × Int × Int)) : Prop :=
  out.toList = out0.toList ++ ((List.range k).flatMap fun κ ↦
    ((List.range 64).filter ((words κ).toBitVec.getLsbD ·)).map fun t : Nat ↦
      i * rbaLength + 64 * κ + t).flatMap fun j ↦ g (cl.numerator j)

/-- `Ratpoints.Sieve.SiftBitArrayInvariant` after the words `0, …, k`, with the numerator `a0` of
bit `0` of word `k`, `a₀ + i (rbaLength 2 ^ cl.k) + k (64 2 ^ cl.k)` as the program computes it,
for the stride `2 ^ cl.k` of the class: the invariant of the loop over the words after the first in
the arm of `Ratpoints.Sieve.siftBitArray` that runs the second stage on the whole bit array, which
steps `a0` from one word to the next before it walks through the word, as the C code does. -/
def SiftBitArrayWalkInvariant (words : Nat → UInt64) (g : Int → List (Int × Int × Int))
    (cl : NumClass) (i : Int) (out0 : Array (Int × Int × Int)) (k : Nat)
    (s : Array (Int × Int × Int) × Int) : Prop :=
  s.2 = cl.a0 + i * (rbaLength * 2 ^ cl.k) + k * (64 * 2 ^ cl.k) ∧
    SiftBitArrayInvariant words g cl i out0 (k + 1) s.1

theorem siftBitArrayInvariant_zero (words : Nat → UInt64) (g : Int → List (Int × Int × Int))
    (cl : NumClass) (i : Int) (out : Array (Int × Int × Int)) :
    SiftBitArrayInvariant words g cl i out 0 out := by
  simp [SiftBitArrayInvariant]

-- The numerator of bit `t` of word `κ` as the walk computes it from that of bit `0` of the word.
private theorem numerator_rbaLength_mul_add (cl : NumClass) (i : Int) (κ t : Nat) :
    cl.a0 + i * (rbaLength * 2 ^ cl.k) + κ * (64 * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t =
      cl.numerator (i * rbaLength + 64 * κ + t) := by
  simp only [NumClass.numerator]
  push_cast
  grind

/-- The walk through word `k` from its first numerator
`a₀ + i (rbaLength 2 ^ cl.k) + k (64 2 ^ cl.k)`, for the stride `2 ^ cl.k` of the class, appends the
points of the numerators of its set bits. -/
theorem SiftBitArrayInvariant.succ {words : Nat → UInt64} {g : Int → List (Int × Int × Int)}
    {cl : NumClass} {i : Int} {out0 out r : Array (Int × Int × Int)} {k : Nat}
    (h : SiftBitArrayInvariant words g cl i out0 k out)
    (hr : r.toList = out.toList ++ (((List.range 64).filter ((words k).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + k * (64 * 2 ^ cl.k) +
        (2 ^ cl.k : Nat) * t).flatMap g) :
    SiftBitArrayInvariant words g cl i out0 (k + 1) r := by
  rw [SiftBitArrayInvariant, hr, h, List.range_succ (n := k), List.flatMap_append,
    List.flatMap_singleton, List.flatMap_append, List.append_assoc, List.flatMap_map,
    List.flatMap_map]
  simp only [numerator_rbaLength_mul_add]

theorem SiftBitArrayInvariant.append {words : Nat → UInt64} {g : Int → List (Int × Int × Int)}
    {cl : NumClass} {i : Int} {out0 out r : Array (Int × Int × Int)} {done suff : List Nat}
    {cur : Nat} (h : SiftBitArrayInvariant words g cl i out0 done.length out)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff)
    (hr : r.toList = out.toList ++ (((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + cur * (64 * 2 ^ cl.k) +
        (2 ^ cl.k : Nat) * t).flatMap g) :
    SiftBitArrayInvariant words g cl i out0 (done ++ [cur]).length r := by
  rw [List.length_append, List.length_singleton]
  rw [← Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at hr
  exact h.succ hr

theorem SiftBitArrayInvariant.append_of_eq_zero {words : Nat → UInt64}
    {g : Int → List (Int × Int × Int)} {cl : NumClass} {i : Int}
    {out0 out : Array (Int × Int × Int)} {done suff : List Nat} {cur : Nat}
    (h : SiftBitArrayInvariant words g cl i out0 done.length out)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff) (hz : words cur = 0) :
    SiftBitArrayInvariant words g cl i out0 (done ++ [cur]).length out :=
  h.append hl (by simp [hz])

/-- The walk through the first word, from the first numerator `a₀ + i (rbaLength 2 ^ cl.k)` of the
bit array, starts the invariant of the loop over the other words. -/
theorem siftBitArrayWalkInvariant_zero {words : Nat → UInt64} {g : Int → List (Int × Int × Int)}
    {cl : NumClass} {i : Int} {out r : Array (Int × Int × Int)}
    (hr : r.toList = out.toList ++ (((List.range 64).filter ((words 0).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t).flatMap g) :
    SiftBitArrayWalkInvariant words g cl i out 0 (r, cl.a0 + i * (rbaLength * 2 ^ cl.k)) :=
  ⟨by simp, (siftBitArrayInvariant_zero words g cl i out).succ (by simpa using hr)⟩

/-- The step `64 2 ^ cl.k` to the first numerator of word `cur` of the loop over `[1:rbaPack]`, and
the walk through it from there. -/
theorem SiftBitArrayWalkInvariant.append {words : Nat → UInt64}
    {g : Int → List (Int × Int × Int)} {cl : NumClass} {i : Int} {out0 r : Array (Int × Int × Int)}
    {done suff : List Nat} {cur : Nat} {s : Array (Int × Int × Int) × Int}
    (h : SiftBitArrayWalkInvariant words g cl i out0 done.length s)
    (hl : ForIn.toList [1:rbaPack] = done ++ cur :: suff)
    (hr : r.toList = s.1.toList ++ (((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ s.2 + 64 * 2 ^ cl.k + (2 ^ cl.k : Nat) * t).flatMap g) :
    SiftBitArrayWalkInvariant words g cl i out0 (done ++ [cur]).length
      (r, s.2 + 64 * 2 ^ cl.k) := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have ha : s.2 + 64 * 2 ^ cl.k = cl.a0 + i * (rbaLength * 2 ^ cl.k) + cur * (64 * 2 ^ cl.k) := by
    rw [h.1, ← hc]
    push_cast
    grind
  rw [List.length_append, List.length_singleton]
  refine ⟨ha.trans (by rw [← hc, Nat.add_comm]), ?_⟩
  rw [← hc, Nat.add_comm] at hr ha
  exact h.2.succ (ha ▸ hr)

/-- At the end of the loops of `Ratpoints.Sieve.siftBitArray`, when the words walked through are
those of the copy `nums` and-ed with the rows of the moduli of `specs`
(`Ratpoints.Sieve.andWords`). -/
theorem SiftBitArrayInvariant.toList_eq {words : Nat → UInt64} {g : Int → List (Int × Int × Int)}
    {cl : NumClass} {specs : List SieveSpec} {i : Int} {nums : Vector UInt64 rbaPack}
    {out0 out : Array (Int × Int × Int)} (hw : ∀ κ < rbaPack, words κ = andWords specs nums[κ]! i κ)
    (h : SiftBitArrayInvariant words g cl i out0 (ForIn.toList [0:rbaPack]).length out) :
    out.toList = out0.toList ++ ((List.range rbaPack).flatMap fun κ ↦
      ((List.range 64).filter ((andWords specs nums[κ]! i κ).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ i * rbaLength + 64 * κ + t).flatMap fun j ↦ g (cl.numerator j) := by
  rw [h, Std.Legacy.Range.length_toList]
  exact congrArg (out0.toList ++ ·) <| congrArg (List.flatMap _) <| congrArg List.flatten <|
    List.map_congr_left fun κ hκ ↦ by rw [hw κ (List.mem_range.mp hκ)]

/-- `Ratpoints.Sieve.SiftBitArrayInvariant.toList_eq` for the invariant with the numerator of
bit `0` of the last word, at the end of the loop over the words after the first. -/
theorem SiftBitArrayWalkInvariant.toList_eq {words : Nat → UInt64}
    {g : Int → List (Int × Int × Int)} {cl : NumClass} {specs : List SieveSpec} {i : Int}
    {nums : Vector UInt64 rbaPack} {out0 : Array (Int × Int × Int)}
    {s : Array (Int × Int × Int) × Int} (hw : ∀ κ < rbaPack, words κ = andWords specs nums[κ]! i κ)
    (h : SiftBitArrayWalkInvariant words g cl i out0 (ForIn.toList [1:rbaPack]).length s) :
    s.1.toList = out0.toList ++ ((List.range rbaPack).flatMap fun κ ↦
      ((List.range 64).filter ((andWords specs nums[κ]! i κ).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ i * rbaLength + 64 * κ + t).flatMap fun j ↦ g (cl.numerator j) := by
  have hl : (ForIn.toList [1:rbaPack]).length + 1 = (ForIn.toList [0:rbaPack]).length := by
    simp only [Std.Legacy.Range.length_toList]
    have := rbaPack_pos
    lia
  exact (hl ▸ h.2).toList_eq hw

/-- When the second stage leaves the bit array zero, its words have no set bits. -/
theorem toList_eq_append_of_isZeroAt {specs : List SieveSpec} {g : Int → List (Int × Int × Int)}
    {i : Int} {nums nums' : Vector UInt64 rbaPack} {out : Array (Int × Int × Int)}
    (hw : ∀ κ < rbaPack, nums'[κ]! = andWords specs nums[κ]! i κ)
    (hz : ¬(!isZeroAt nums' 0) = true) :
    out.toList = out.toList ++ ((List.range rbaPack).flatMap fun κ ↦
      ((List.range 64).filter ((andWords specs nums[κ]! i κ).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ i * rbaLength + 64 * κ + t).flatMap g := by
  rw [(List.flatMap_eq_nil_iff (l := List.range rbaPack)).mpr fun κ hκ ↦ ?_]
  · simp
  have hκ' := List.mem_range.mp hκ
  have := (isZeroAt_eq_true_iff nums' 0).mp (by simpa using hz) κ hκ'
  simp_all

/- The invariants are irreducible from here on: the verification conditions of
`Ratpoints.Sieve.siftBitArray` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] SiftBitArrayInvariant SiftBitArrayWalkInvariant

/-- Both arms walk through the set bits of the same words, the words of `nums` and-ed with the rows
of the moduli of `specs` (`Ratpoints.Sieve.secondStage_spec`,
`Ratpoints.Sieve.secondStageWord_spec`), each bit `j` standing for the numerator `a₀ + 2 ^ k j` of
the class `cl`: the arm for one word at a time skips a word that is zero, and the other skips the
walks when the second stage leaves the bit array zero, which lose nothing; each arm has its own
invariant (`Ratpoints.Sieve.SiftBitArrayInvariant`, `Ratpoints.Sieve.SiftBitArrayWalkInvariant`). -/
@[spec]
theorem siftBitArray_spec (useLong : Bool) (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (nums : Vector UInt64 rbaPack) (out : Array (Int × Int × Int)) :
    ⦃ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small i (i + 1) ⦄
    siftBitArray useLong w d b rev specs mgs small checks cl i nums out
    ⦃ fun out' ↦ out'.toList = out.toList ++ ((List.range rbaPack).flatMap fun κ ↦
        ((List.range 64).filter ((andWords specs nums[κ]! i κ).toBitVec.getLsbD ·)).map
          fun t : Nat ↦ i * rbaLength + 64 * κ + t).flatMap
            fun j ↦ acceptedPoints w d b rev checks (cl.numerator j) ⦄ := by
  vcgen [siftBitArray] invariants
  | inv1 => fun done _ ↦ SiftBitArrayInvariant (fun κ ↦ andWords specs nums[κ]! i κ)
      (acceptedPoints w d b rev checks) cl i out done.length
  | inv2 => fun done _ ↦ SiftBitArrayWalkInvariant (fun κ ↦ nums[κ]!)
      (acceptedPoints w d b rev checks) cl i out done.length
  all_goals subst_vars
  all_goals first
    | exact ‹(∀ s ∈ specs, s.Fits) ∧ _›
    | exact Std.Legacy.Range.lt_of_toList_eq_append_cons ‹_›
    | exact siftBitArrayInvariant_zero ..
    | exact siftBitArrayWalkInvariant_zero ‹_›
    | exact SiftBitArrayInvariant.append ‹_› ‹_› ‹_›
    | exact SiftBitArrayWalkInvariant.append ‹_› ‹_› ‹_›
    | exact SiftBitArrayInvariant.append_of_eq_zero ‹_› ‹_› (by simp_all)
    | exact SiftBitArrayInvariant.toList_eq (fun _ _ ↦ rfl) ‹_›
    | exact SiftBitArrayWalkInvariant.toList_eq ‹_› ‹_›
    | exact toList_eq_append_of_isZeroAt ‹_› ‹_›

/-! ### The scan of a piece -/

/-- The invariant of the loop of `Ratpoints.Sieve.scanPiece` that writes the sentinel into bit
array `n` of `surv`: the words of the piece are those of `surv`, and the first `k` words of bit
array `n` are all ones. -/
def ScanPieceSentinelInvariant {m : Nat} (n : Nat) (surv : Vector UInt64 m) (k : Nat)
    (sv : Vector UInt64 m) : Prop :=
  (∀ y < n * rbaPack, sv[y]! = surv[y]!) ∧ ∀ κ < k, sv[rbaPack * n + κ]! = ~~~0

/-- The invariant of the scan of `Ratpoints.Sieve.scanPiece` at bit array `pos` of the words `sv`,
for a piece of `n` bit arrays from the word number `w0` on, the moduli `specs` of the second stage
with their rows and the points `g j` of a bit `j` (in the scan, those of
`Ratpoints.Sieve.acceptedPoints` for its numerator): `pos ≤ n`, and `out` holds the points of the
bits `rbaLength w0 + 64 y + t` of the set bits `t` of the words `y < rbaPack pos` and-ed with the
rows of `specs` (`Ratpoints.Sieve.andWords`), in increasing order. -/
def ScanPieceInvariant {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec)
    (g : Int → List (Int × Int × Int)) (w0 : Int) (n pos : Nat) (out : Array (Int × Int × Int)) :
    Prop :=
  pos ≤ n ∧ out.toList = ((List.range (rbaPack * pos)).flatMap fun y : Nat ↦
    ((List.range 64).filter ((andWords specs sv[y]! w0 y).toBitVec.getLsbD ·)).map fun t : Nat ↦
      rbaLength * w0 + 64 * y + t).flatMap g

/-- `Ratpoints.Sieve.ScanPieceInvariant` as the invariant of the scan of
`Ratpoints.Sieve.scanPiece`, with all `n` bit arrays done at the exit. -/
def ScanPieceWhileInvariant {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec)
    (g : Int → List (Int × Int × Int)) (w0 : Int) (n : Nat) :
    Std.WP.WhileInvariant (Nat × Array (Int × Int × Int)) Prop :=
  .mk fun exit s ↦ ScanPieceInvariant sv specs g w0 n s.1 s.2 ∧ (exit = true → s.1 = n)

/-- The invariant of the loop of `Ratpoints.Sieve.scanPiece` that steps over the bit arrays that are
zero, from bit array `pos0` on, with the points `out` of the bit arrays before `pos0`: the position
is at least `pos0`, and `Ratpoints.Sieve.ScanPieceInvariant` holds there with `out`, since a bit
array that is zero has no set bits. -/
def ScanPieceZeroInvariant {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec)
    (g : Int → List (Int × Int × Int)) (w0 : Int) (n pos0 : Nat) (out : Array (Int × Int × Int)) :
    Std.WP.WhileInvariant Nat Prop :=
  .mk fun _ pos ↦ pos0 ≤ pos ∧ ScanPieceInvariant sv specs g w0 n pos out

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
  · rw [Vector.getElem!_set! (Nat.lt_add_one_mul_of_lt_mul hy), h.1 y hy]
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

theorem scanPieceInvariant_zero {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec)
    (g : Int → List (Int × Int × Int)) (w0 : Int) (n : Nat) :
    ScanPieceInvariant sv specs g w0 n 0 #[] := by
  simp [ScanPieceInvariant]

theorem ScanPieceInvariant.le {m : Nat} {sv : Vector UInt64 m} {specs : List SieveSpec}
    {g : Int → List (Int × Int × Int)} {w0 : Int} {n pos : Nat} {out : Array (Int × Int × Int)}
    (h : ScanPieceInvariant sv specs g w0 n pos out) :
    pos ≤ n :=
  h.1

/-- Bit array `pos` adds the points of the set bits of its words and-ed with the rows. -/
theorem ScanPieceInvariant.add_one {m : Nat} {sv : Vector UInt64 m} {specs : List SieveSpec}
    {g : Int → List (Int × Int × Int)} {w0 : Int} {n pos : Nat} {out out' : Array (Int × Int × Int)}
    (h : ScanPieceInvariant sv specs g w0 n pos out) (hlt : pos < n)
    (hout : out'.toList = out.toList ++ ((List.range rbaPack).flatMap fun κ ↦
      ((List.range 64).filter ((andWords specs sv[rbaPack * pos + κ]! w0
        (rbaPack * pos + κ)).toBitVec.getLsbD ·)).map fun t : Nat ↦
          rbaLength * w0 + 64 * (rbaPack * pos + κ : Nat) + t).flatMap g) :
    ScanPieceInvariant sv specs g w0 n (pos + 1) out' := by
  refine ⟨hlt, ?_⟩
  rw [hout, h.2, Nat.mul_succ, List.range_add, List.flatMap_append, List.flatMap_map,
    List.flatMap_append]

theorem ScanPieceInvariant.add_one_of_isZeroAt {m : Nat} {sv : Vector UInt64 m}
    {specs : List SieveSpec} {g : Int → List (Int × Int × Int)} {w0 : Int} {n pos : Nat}
    {out : Array (Int × Int × Int)} (h : ScanPieceInvariant sv specs g w0 n pos out)
    (hlt : pos < n) (hz : isZeroAt sv pos = true) :
    ScanPieceInvariant sv specs g w0 n (pos + 1) out := by
  refine h.add_one hlt ?_
  rw [(List.flatMap_eq_nil_iff (l := List.range rbaPack)).mpr fun κ hκ ↦ ?_]
  · simp
  simp [(isZeroAt_eq_true_iff sv pos).mp hz κ (List.mem_range.mp hκ)]

/-- Bit array `pos`, copied and passed through `Ratpoints.Sieve.siftBitArray` with its word number
`w0 + pos`, adds the points of the set bits of its words and-ed with the rows. -/
theorem ScanPieceInvariant.add_one_of_siftBitArray {m : Nat} {sv : Vector UInt64 m}
    {specs : List SieveSpec} {g : Int → List (Int × Int × Int)} {w0 : Int} {n pos : Nat}
    {out out' : Array (Int × Int × Int)} (h : ScanPieceInvariant sv specs g w0 n pos out)
    (hlt : pos < n) (hout : out'.toList = out.toList ++ ((List.range rbaPack).flatMap fun κ ↦
      ((List.range 64).filter ((andWords specs
        (Vector.ofFn fun κ : Fin rbaPack ↦ sv[rbaPack * pos + κ]!)[κ]! (w0 + pos)
          κ).toBitVec.getLsbD ·)).map fun t : Nat ↦
            (w0 + pos) * rbaLength + 64 * κ + t).flatMap g) :
    ScanPieceInvariant sv specs g w0 n (pos + 1) out' := by
  refine h.add_one hlt (hout.trans ?_)
  have key (κ t : Nat) : (w0 + pos) * (rbaLength : Int) + 64 * κ + t =
      rbaLength * w0 + 64 * ((rbaPack * pos + κ : Nat) : Int) + t := by
    push_cast [rbaLength_eq]
    grind
  refine congrArg (out.toList ++ ·) <| congrArg (List.flatMap g) <| congrArg List.flatten <|
    List.map_congr_left fun κ hκ ↦ ?_
  have hκ' := List.mem_range.mp hκ
  simp only [Vector.getElem!_ofFn hκ', andWords_rbaPack_mul_add _ _ _ _ hκ', key]

/-- At the end of the scan of `Ratpoints.Sieve.scanPiece`, `out` holds the points of the set bits of
the words of the piece and-ed with the rows, which are those of `surv`, since the sentinel was
written past them. -/
theorem ScanPieceInvariant.toList_eq {m n : Nat} {surv sv : Vector UInt64 m}
    {specs : List SieveSpec} {g : Int → List (Int × Int × Int)} {w0 : Int}
    {out : Array (Int × Int × Int)} (h : ScanPieceInvariant sv specs g w0 n n out)
    (hs : ScanPieceSentinelInvariant n surv rbaPack sv) :
    out.toList = ((List.range (n * rbaPack)).flatMap fun y : Nat ↦
      ((List.range 64).filter ((andWords specs surv[y]! w0 y).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ rbaLength * w0 + 64 * y + t).flatMap g := by
  rw [h.2, Nat.mul_comm rbaPack n]
  exact congrArg (List.flatMap _) <| congrArg List.flatten <| List.map_congr_left fun y hy ↦ by
    rw [hs.1 y (List.mem_range.mp hy)]

/-- What the second stage needs of the bit array `pos < n` of a piece of `n` bit arrays from the
word number `w0` on: the moduli and their reciprocals, and the test `small` of the piece. -/
theorem fits_and_smallFits_add {specs : List SieveSpec} {mgs : List Nat} {small : Bool} {w0 : Int}
    {n pos : Nat}
    (h : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small w0 (w0 + n))
    (hpos : ¬n ≤ pos) :
    (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧
      SmallFits small (w0 + pos) (w0 + pos + 1) :=
  ⟨h.1, h.2.1, h.2.2.mono (by lia) (by lia)⟩

/- The invariants are irreducible from here on: the verification conditions of
`Ratpoints.Sieve.scanPiece` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] ScanPieceSentinelInvariant ScanPieceInvariant

-- The contract of `Ratpoints.Sieve.scanPiece` in terms of the set bits of the words of the piece
-- and-ed with the rows of the second stage.
private theorem scanPiece_spec_getLsbD (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (w0 : Int) (n : Nat) (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small w0 (w0 + n) ⦄
    scanPiece w d b rev specs mgs small checks cl w0 n surv
    ⦃ fun out ↦ out.toList = ((List.range (n * rbaPack)).flatMap fun y : Nat ↦
        ((List.range 64).filter ((andWords specs surv[y]! w0 y).toBitVec.getLsbD ·)).map
          fun t : Nat ↦ rbaLength * w0 + 64 * y + t).flatMap
            fun j ↦ acceptedPoints w d b rev checks (cl.numerator j) ⦄ := by
  vcgen [scanPiece] invariants
  | inv1 => fun done _ ↦ ScanPieceSentinelInvariant n surv done.length
  | inv2 sv _ => ScanPieceWhileInvariant sv specs
      (fun j ↦ acceptedPoints w d b rev checks (cl.numerator j)) w0 n
  | inv3 => Std.WP.Variant.ofMeasure fun s : Nat × Array (Int × Int × Int) ↦ n - s.1
  | inv4 sv _ pos0 out _ _ => ScanPieceZeroInvariant sv specs
      (fun j ↦ acceptedPoints w d b rev checks (cl.numerator j)) w0 n pos0 out
  | inv5 => Std.WP.Variant.ofMeasure fun s : Nat ↦ n - s
  all_goals first
    | exact fits_and_smallFits_add ‹_› ‹_›
    | exact scanPieceSentinelInvariant_zero n surv
    | exact ScanPieceSentinelInvariant.append_set! ‹_› ‹_›
    | simp [ScanPieceWhileInvariant, ScanPieceZeroInvariant] at *
  all_goals first
    | exact ⟨by lia, ScanPieceInvariant.add_one_of_siftBitArray ‹_ ≤ _ ∧ _›.2 ‹_› ‹_›⟩
    | grind [scanPieceInvariant_zero, → ScanPieceInvariant.le, ScanPieceInvariant.toList_eq,
        ScanPieceInvariant.add_one_of_isZeroAt, → ScanPieceSentinelInvariant.ne_of_isZeroAt]

/-- The loop over the zero bit arrays ends at the sentinel at the latest, so that both loops of the
scan end by the measure `n - pos`; the test `keep` is quantified in the postcondition, since the
program does not mention it. -/
@[spec]
theorem scanPiece_spec (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (w0 : Int) (n : Nat) (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small w0 (w0 + n) ⦄
    scanPiece w d b rev specs mgs small checks cl w0 n surv
    ⦃ fun out ↦ ∀ keep : Int → Bool, (∀ y < n * rbaPack, ∀ t : Nat,
        (andWords specs surv[y]! w0 y).toBitVec.getLsbD t =
          (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t))) →
      out.toList = (((List.range (n * rbaLength)).map fun k : Nat ↦
        rbaLength * w0 + k).filter keep).flatMap
          fun j ↦ acceptedPoints w d b rev checks (cl.numerator j) ⦄ :=
  ⟨fun pre keep hkeep ↦ by
    rw [(scanPiece_spec_getLsbD w d b rev specs mgs small checks cl w0 n surv).le_wp pre,
      List.flatMap_range_map_filter hkeep, rbaLength_eq, Nat.mul_left_comm]⟩

/-! ### The masks and one piece -/

@[simp]
theorem survives_append (l₁ l₂ : List SieveEntry) (b : Nat) (a : Int) :
    survives (l₁ ++ l₂) b a = (survives l₁ b a && survives l₂ b a) :=
  List.all_append

theorem getLsbD_clearHighBits_sub_one {m n s : Nat} (v : Vector UInt64 m) (hs : s < rbaLength)
    {y : Nat} (hy : y < m) (hyn : y < n * rbaPack) (t : Nat) :
    (clearHighBits v (n - 1) s)[y]!.toBitVec.getLsbD t =
      (v[y]!.toBitVec.getLsbD t && decide (64 * y + t + s < rbaLength * n)) := by
  have hn : n - 1 + 1 = n := Nat.sub_add_cancel (Nat.pos_of_ne_zero fun h ↦ by simp [h] at hyn)
  rw [getLsbD_clearHighBits v (n - 1) hs hy (by rw [hn, Nat.mul_comm]; exact hyn), hn]

/-- The words `v` of a piece of `n` bit arrays are the words `surv` with the masks at its two ends
applied, as far as the bits `t < 64` of the words `y < n rbaPack` go: bit `t` of word `y` is set in
`v` exactly when it is set in `surv`, `maskLow ≤ 64 y + t` and `64 y + t + maskHigh < rbaLength n`,
for the number `rbaPack` of words of a bit array (`Ratpoints.rbaPack`). -/
def IsMasked {m : Nat} (n maskLow maskHigh : Nat) (surv v : Vector UInt64 m) : Prop :=
  ∀ y < n * rbaPack, ∀ t < 64, v[y]!.toBitVec.getLsbD t =
    (surv[y]!.toBitVec.getLsbD t && decide (maskLow ≤ 64 * y + t) &&
      decide (64 * y + t + maskHigh < rbaLength * n))

theorem isMasked_clearHighBits_clearLowBits {n maskHigh : Nat}
    (v : Vector UInt64 ((n + 1) * rbaPack)) (maskLow : Nat) (hH : maskHigh < rbaLength) :
    IsMasked n maskLow maskHigh v (clearHighBits (clearLowBits v maskLow) (n - 1) maskHigh) :=
  fun y hy t _ ↦ by
    have := Nat.lt_add_one_mul_of_lt_mul hy
    rw [getLsbD_clearHighBits_sub_one _ hH this hy, getLsbD_clearLowBits _ _ this]

theorem isMasked_clearLowBits {n maskHigh : Nat} (v : Vector UInt64 ((n + 1) * rbaPack))
    (maskLow : Nat) (hH : maskHigh = 0) : IsMasked n maskLow maskHigh v (clearLowBits v maskLow) :=
  fun y hy t ht ↦ by
    simp [getLsbD_clearLowBits _ _ (Nat.lt_add_one_mul_of_lt_mul hy), hH,
      lt_rbaLength_mul_of_lt hy ht]

theorem isMasked_clearHighBits {n maskLow maskHigh : Nat} (v : Vector UInt64 ((n + 1) * rbaPack))
    (hL : maskLow = 0) (hH : maskHigh < rbaLength) :
    IsMasked n maskLow maskHigh v (clearHighBits v (n - 1) maskHigh) := fun y hy t _ ↦ by
  simp [getLsbD_clearHighBits_sub_one _ hH (Nat.lt_add_one_mul_of_lt_mul hy) hy, hL]

theorem isMasked_self {m maskLow maskHigh : Nat} (n : Nat) (v : Vector UInt64 m)
    (hL : maskLow = 0) (hH : maskHigh = 0) : IsMasked n maskLow maskHigh v v := fun y hy t ht ↦ by
  simp [hL, hH, lt_rbaLength_mul_of_lt hy ht]

/-- The points of a piece of `n` bit arrays from the word number `w0` on, given the contracts of its
first stage with the first `sp1` moduli of `specs` from the class word `cw` on the words `surv`
(`hand`, as `Ratpoints.Sieve.andRows_spec` states it) and of its scan with the other moduli on the
words `v` (`hout`, as `Ratpoints.Sieve.scanPiece_spec` states it, with the points `g j` of a bit
`j`), when `v` is `surv` with the masks applied and the rows of the moduli read the tests `sf.2` of
the bits (`Ratpoints.Sieve.SieveSpec.Reads`): the points of the bits from `rbaLength w0 + maskLow`
to `rbaLength (w0 + n) - 1 - maskHigh` that pass the class word (`Ratpoints.Sieve.classBit`) and
all the tests. -/
theorem IsMasked.toList_eq {n : Nat} {g : Int → List (Int × Int × Int)} {sp1 : Nat}
    {specs : List SieveSpec} {cw : UInt64} {w0 : Int} {maskLow maskHigh : Nat}
    {surv v : Vector UInt64 ((n + 1) * rbaPack)} {out : Array (Int × Int × Int)}
    (hand : ∀ y < n * rbaPack, surv[y]! = andWords (specs.take sp1) cw w0 y)
    (h : IsMasked n maskLow maskHigh surv v)
    (hout : ∀ keep : Int → Bool, (∀ y < n * rbaPack, ∀ t : Nat,
        (andWords (specs.drop sp1) v[y]! w0 y).toBitVec.getLsbD t =
          (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t))) →
      out.toList = (((List.range (n * rbaLength)).map fun k : Nat ↦
        rbaLength * w0 + k).filter keep).flatMap g)
    {sfs : List (SieveSpec × (Int → Bool))} (hspecs : specs = sfs.map Prod.fst)
    (hsfs : ∀ sf ∈ sfs, sf.1.Reads sf.2) :
    out.toList = (((List.range (n * rbaLength - maskLow - maskHigh)).map fun k : Nat ↦
      rbaLength * w0 + maskLow + k).filter fun j ↦ classBit cw j && sfs.all (·.2 j)).flatMap g := by
  rw [hout (fun j ↦ (classBit cw j && sfs.all (·.2 j)) &&
    decide (rbaLength * w0 + maskLow ≤ j ∧ j + maskHigh < rbaLength * w0 + (n * rbaLength : Nat)))
    fun y hy t ↦ ?_, ← List.filter_filter, List.filter_map_range_eq_map_range]
  by_cases ht : t < 64
  · rw [hspecs, ← List.map_drop, getLsbD_andWords fun sf hsf ↦ hsfs sf (List.mem_of_mem_drop hsf),
      h y hy t ht, hand y hy, hspecs, ← List.map_take,
      getLsbD_andWords fun sf hsf ↦ hsfs sf (List.mem_of_mem_take hsf),
      classBit_rbaLength_mul_add cw w0 y ht, ← List.take_append_drop sp1 sfs, List.all_append,
      List.take_append_drop]
    grind
  · simp [ht, BitVec.getLsbD_of_ge _ t (Nat.le_of_not_lt ht)]

/-- What the first stage of a piece of `n` bit arrays from the word number `w0` on needs of the
first `sp1` moduli and their reciprocals, with the test `small` that `Ratpoints.Sieve.siftPiece`
computes. -/
theorem fits_take {specs : List SieveSpec} {mgs : List Nat} {maskHigh : Nat}
    (h : maskHigh < rbaLength ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p)) (sp1 : Nat)
    (w0 : Int) (n : Nat) :
    (∀ s ∈ specs.take sp1, s.Fits) ∧ mgs.take sp1 = (specs.take sp1).map (magic ·.p) ∧
      SmallFits (decide (-(rowBias : Int) ≤ w0 ∧ w0 + n ≤ (rowBias : Int) - 2 * maxPrimeEven)) w0
        (w0 + n) :=
  ⟨fun s hs ↦ h.2.1 s (List.mem_of_mem_take hs), by rw [h.2.2, List.map_take],
    smallFits_decide w0 n⟩

/-- What the scan of a piece of `n` bit arrays from the word number `w0` on needs of the moduli and
their reciprocals after the first `sp1`, with the test `small` that `Ratpoints.Sieve.siftPiece`
computes. -/
theorem fits_drop {specs : List SieveSpec} {mgs : List Nat} {maskHigh : Nat}
    (h : maskHigh < rbaLength ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p)) (sp1 : Nat)
    (w0 : Int) (n : Nat) :
    (∀ s ∈ specs.drop sp1, s.Fits) ∧ mgs.drop sp1 = (specs.drop sp1).map (magic ·.p) ∧
      SmallFits (decide (-(rowBias : Int) ≤ w0 ∧ w0 + n ≤ (rowBias : Int) - 2 * maxPrimeEven)) w0
        (w0 + n) :=
  ⟨fun s hs ↦ h.2.1 s (List.mem_of_mem_drop hs), by rw [h.2.2, List.map_drop],
    smallFits_decide w0 n⟩

/-- The rows of the moduli, read at their offsets, are given by the tests `sf.2` of the bits that
they read (`Ratpoints.Sieve.SieveSpec.Reads`), quantified in the postcondition since the program
does not mention them; the first `sp1` moduli go to the first stage, the others to the second, with
their reciprocals and the test `small`, which keeps the values that the reductions by the
reciprocals see in range (`Ratpoints.Sieve.SieveSpec.Fits`); the bound on `maskHigh` is that of the
high mask (`Ratpoints.Sieve.getLsbD_clearHighBits`), and the low mask needs none. -/
@[spec]
theorem siftPiece_spec (w : Thunk (List Int)) (d b : Nat) (rev : Bool) (sp1 : Nat)
    (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass)
    (w0 : Int) (n maskLow maskHigh : Nat) :
    ⦃ maskHigh < rbaLength ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ⦄
    siftPiece w d b rev sp1 specs mgs checks cl w0 n maskLow maskHigh
    ⦃ fun out ↦ ∀ sfs : List (SieveSpec × (Int → Bool)), specs = sfs.map Prod.fst →
        (∀ sf ∈ sfs, sf.1.Reads sf.2) →
        out.toList = (((List.range (n * rbaLength - maskLow - maskHigh)).map fun k : Nat ↦
          rbaLength * w0 + maskLow + k).filter fun j ↦
            classBit cl.bits j && sfs.all (·.2 j)).flatMap
              fun j ↦ acceptedPoints w d b rev checks (cl.numerator j) ⦄ := by
  vcgen [siftPiece]
  all_goals first
    | exact fits_take ‹_› sp1 w0 n
    | exact fits_drop ‹_› sp1 w0 n
    | exact IsMasked.toList_eq ‹_› (isMasked_clearHighBits_clearLowBits _ _ ‹_ ∧ _›.1) ‹_› ‹_› ‹_›
    | exact IsMasked.toList_eq ‹_› (isMasked_clearLowBits _ _ (Decidable.of_not_not ‹_›)) ‹_› ‹_›
        ‹_›
    | exact IsMasked.toList_eq ‹_› (isMasked_clearHighBits _ (Decidable.of_not_not ‹_›)
        ‹_ ∧ _›.1) ‹_› ‹_› ‹_›
    | exact IsMasked.toList_eq ‹_› (isMasked_self _ _ (Decidable.of_not_not ‹_›)
        (Decidable.of_not_not ‹_›)) ‹_› ‹_› ‹_›

/-! ### The bits of one interval -/

open BruteForce

-- The low mask of `Ratpoints.Sieve.siftBits` on the piece from the word number `w0` on: the number
-- of its bits below `low`, `0` from the second piece on.
private theorem ite_eq_toNat_sub {low w0 : Int} (hw0 : low / rbaLength ≤ w0) :
    (if w0 = low / rbaLength then (low - rbaLength * (low / rbaLength)).toNat else 0) =
      (low - rbaLength * w0).toNat := by
  have hR := natCast_rbaLength_pos
  split
  · subst_vars
    rfl
  · have := Int.lt_mul_ediv_self_add (x := low) hR
    have := Int.mul_le_mul_of_nonneg_left (show low / rbaLength + 1 ≤ w0 by lia) (Int.le_of_lt hR)
    rw [Int.mul_add, Int.mul_one] at this
    lia

-- The high mask of `Ratpoints.Sieve.siftBits` on the last piece: the number of its bits above
-- `high`.
private theorem sub_toNat_emod_eq_toNat_mul_sub (high : Int) :
    rbaLength - 1 - (high % rbaLength).toNat =
      (rbaLength * (high / rbaLength + 1) - 1 - high).toNat := by
  have := Int.emod_def high rbaLength
  have := Int.emod_lt_of_pos high natCast_rbaLength_pos
  have := Int.emod_nonneg high (Int.ne_of_gt natCast_rbaLength_pos)
  rw [Int.mul_add, Int.mul_one]
  lia

-- The high mask of `Ratpoints.Sieve.siftBits` on the piece that ends at the word number `w1`: the
-- number of its bits above `high`, `0` for every piece but the last.
private theorem ite_eq_toNat_mul_sub {high w1 : Int} (hw1 : w1 ≤ high / rbaLength + 1) :
    (if w1 = high / rbaLength + 1 then rbaLength - 1 - (high % rbaLength).toNat else 0) =
      (rbaLength * w1 - 1 - high).toNat := by
  split
  · subst_vars
    exact sub_toNat_emod_eq_toNat_mul_sub high
  · have hR := natCast_rbaLength_pos
    have := Int.mul_ediv_self_le (x := high) (Int.ne_of_gt hR)
    have := Int.mul_le_mul_of_nonneg_left (show w1 ≤ high / rbaLength by lia) (Int.le_of_lt hR)
    lia

/-- The high mask of a piece of `Ratpoints.Sieve.siftBits` is below `Ratpoints.rbaLength`. -/
theorem ite_sub_toNat_emod_lt (P : Prop) [Decidable P] (high : Int) :
    (if P then rbaLength - 1 - (high % rbaLength).toNat else 0) < rbaLength := by
  have := rbaLength_pos
  split <;> lia

/-- The invariant of the loop of `Ratpoints.Sieve.siftBits` over the pieces, for the bits from
`low` to `high`, a test `keep` of the bits and their points `g`, at the exit of the loop or not:
the bit arrays from that of `low` up to the word number `w0` are done, and their bits that lie in
`low, …, high` and pass `keep` have given their points. -/
structure SiftInvariant (g : Int → List (Int × Int × Int)) (keep : Int → Bool) (low high : Int)
    (exit : Bool) (range : Nat) (w0 w1 : Int) (out : Array (Int × Int × Int)) : Prop where
  /-- The next piece starts at the word number `w0`, not below that of `low`. -/
  le_w0 : low / rbaLength ≤ w0
  /-- The word number `w0` is at most one past that of `high`. -/
  w0_le : w0 ≤ high / rbaLength + 1
  /-- At the exit, `w0` is one past the word number of `high`. -/
  eq_of_exit : exit = true → w0 = high / rbaLength + 1
  /-- The next piece ends at the word number `w1`, `range` bit arrays after `w0`. -/
  w1_eq : w1 = w0 + range
  /-- A piece has at least one bit array. -/
  one_le_range : 1 ≤ range
  /-- The points found are those of the bits of the bit arrays from that of `low` up to `w0` that
  lie in `low, …, high` and pass `keep`, in increasing order. -/
  toList_eq : out.toList = ((((List.range ((w0 - low / rbaLength).toNat * rbaLength)).map
    fun k : Nat ↦ rbaLength * (low / rbaLength) + k).filter
      fun a ↦ decide (low ≤ a ∧ a ≤ high)).filter keep).flatMap g

/-- `Ratpoints.Sieve.SiftInvariant` as the invariant of the `while` loop of
`Ratpoints.Sieve.siftBits`. -/
def SiftWhileInvariant (g : Int → List (Int × Int × Int)) (keep : Int → Bool) (low high : Int) :
    Std.WP.WhileInvariant (Array (Int × Int × Int) × Nat × Int × Int) Prop :=
  .mk fun exit s ↦ SiftInvariant g keep low high exit s.2.1 s.2.2.1 s.2.2.2 s.1

theorem siftInvariant_empty (g : Int → List (Int × Int × Int)) (keep : Int → Bool) {low high : Int}
    (h : low ≤ high) {A : Nat} (hA : 1 ≤ A) :
    SiftInvariant g keep low high false A (low / rbaLength) (low / rbaLength + A) #[] := by
  have := Int.ediv_le_ediv natCast_rbaLength_pos h
  exact ⟨Int.le_refl _, by lia, nofun, rfl, hA, by simp⟩

/-- A piece of `r ≥ 1` bit arrays from the word number `w0` on, which ends at
`w1' ≤ high / rbaLength + 1`, with the low mask of `Ratpoints.Sieve.siftBits` and a high mask `mH`,
the number of its bits above `high`. -/
theorem SiftInvariant.append {g : Int → List (Int × Int × Int)} {keep : Int → Bool}
    {low high : Int} {range r mH : Nat} {w0 w1 w1' : Int} {out pts : Array (Int × Int × Int)}
    (h : SiftInvariant g keep low high false range w0 w1 out) (hr : w1' = w0 + r) (hr1 : 1 ≤ r)
    (hw1' : w1' ≤ high / rbaLength + 1) (hmH : mH = (rbaLength * w1' - 1 - high).toNat)
    (hpts : pts.toList = (((List.range (r * rbaLength - (if w0 = low / rbaLength then
      (low - rbaLength * (low / rbaLength)).toNat else 0) - mH)).map fun k : Nat ↦
        rbaLength * w0 + ((if w0 = low / rbaLength then
          (low - rbaLength * (low / rbaLength)).toNat else 0 : Nat) : Int) + k).filter keep).flatMap
            g) :
    SiftInvariant g keep low high false r w1' (w1' + r) (out ++ pts) := by
  refine ⟨by have := h.le_w0; lia, hw1', nofun, rfl, hr1, ?_⟩
  have hm : (rbaLength : Int) * w1' - 1 - high =
      rbaLength * w0 + ((r * rbaLength : Nat) : Int) - 1 - high := by
    rw [hr, Int.mul_add, Int.natCast_mul, Int.mul_comm (r : Int)]
  rw [ite_eq_toNat_sub h.le_w0, hmH, hm, ← List.filter_map_range_eq_map_range'] at hpts
  have hl : (w1' - low / rbaLength).toNat = (w0 - low / rbaLength).toNat + r := by
    have := h.le_w0
    lia
  have hmap : (List.range (r * rbaLength)).map ((fun k : Nat ↦ rbaLength * (low / rbaLength) + k) ∘
        fun x ↦ (w0 - low / rbaLength).toNat * rbaLength + x) =
      (List.range (r * rbaLength)).map fun k : Nat ↦ rbaLength * w0 + k :=
    List.map_congr_left fun k _ ↦ by have := h.le_w0; grind
  rw [Array.toList_append, h.toList_eq, hpts, ← List.flatMap_append, ← List.filter_append,
    ← List.filter_append, hl, Nat.add_mul, List.range_add, List.map_append, List.map_map, hmap]

/-- The pieces advance: the measure `high / rbaLength + 1 - w0` of the loop of
`Ratpoints.Sieve.siftBits` decreases from one piece to the next. -/
theorem SiftInvariant.toNat_sub_lt {g : Int → List (Int × Int × Int)} {keep : Int → Bool}
    {low high : Int} {range : Nat} {w0 w1 : Int} {out : Array (Int × Int × Int)}
    (h : SiftInvariant g keep low high false range w0 w1 out) (hw0 : w0 < high / rbaLength + 1) :
    (high / rbaLength + 1 - w1).toNat < (high / rbaLength + 1 - w0).toNat := by
  have := h.w1_eq
  have := h.one_le_range
  lia

/-- The loop of `Ratpoints.Sieve.siftBits` ends at the word number one past that of `high`. -/
theorem SiftInvariant.exit_of_not_lt {g : Int → List (Int × Int × Int)} {keep : Int → Bool}
    {low high : Int} {range : Nat} {w0 w1 : Int} {out : Array (Int × Int × Int)}
    (h : SiftInvariant g keep low high false range w0 w1 out)
    (hw0 : ¬w0 < high / rbaLength + 1) : SiftInvariant g keep low high true range w0 w1 out :=
  ⟨h.le_w0, h.w0_le, fun _ ↦ Int.le_antisymm h.w0_le (Int.not_lt.mp hw0), h.w1_eq,
    h.one_le_range, h.toList_eq⟩

/-- At the exit of the loop of `Ratpoints.Sieve.siftBits`, the points found are those of the bits
`low, …, high` that pass `keep`. -/
theorem SiftInvariant.toList_eq_flatMap_filter {g : Int → List (Int × Int × Int)}
    {keep : Int → Bool} {low high : Int} {range : Nat} {w0 w1 : Int}
    {out : Array (Int × Int × Int)} (h : SiftInvariant g keep low high true range w0 w1 out) :
    out.toList = (((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      keep).flatMap g := by
  have hR := natCast_rbaLength_pos
  have hL := Int.mul_ediv_self_le (x := low) (Int.ne_of_gt hR)
  have := Int.lt_mul_ediv_self_add (x := high) hR
  have hM : ((((high / rbaLength + 1 - low / rbaLength).toNat * rbaLength : Nat) : Int)) =
      rbaLength * (high / rbaLength) + rbaLength - rbaLength * (low / rbaLength) := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg (by have := h.le_w0; have := h.eq_of_exit rfl; lia)]
    grind
  rw [h.toList_eq, h.eq_of_exit rfl, List.filter_map_range_eq_map_range_of_le hL (by lia)]

-- A statement about the reading list `sfs` given as the list that the contract of a piece
-- quantifies.
private theorem of_forall_reads {specs : List SieveSpec} {sfs : List (SieveSpec × (Int → Bool))}
    (hspecs : specs = sfs.map Prod.fst) (hsfs : ∀ sf ∈ sfs, sf.1.Reads sf.2)
    {P : List (SieveSpec × (Int → Bool)) → Prop}
    (h : ∀ sfs' : List (SieveSpec × (Int → Bool)), specs = sfs'.map Prod.fst →
      (∀ sf ∈ sfs', sf.1.Reads sf.2) → P sfs') : P sfs :=
  h sfs hspecs hsfs

/-- An empty interval of bits gives no points. -/
theorem toList_empty_eq_of_not_le {g : Int → List (Int × Int × Int)} {keep : Int → Bool}
    {low high : Int} (h : ¬low ≤ high) :
    (#[] : Array (Int × Int × Int)).toList =
      (((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter keep).flatMap g := by
  rw [show (high + 1 - low).toNat = 0 by lia]
  rfl

-- The contract of `Ratpoints.Sieve.siftBits` for the reading list `sfs` of its moduli.
open Std.WP Lean.Order in
private theorem siftBits_spec_reads (w : Thunk (List Int)) (d b A : Nat) (rev : Bool) (sp1 : Nat)
    (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass)
    (low high : Int) {sfs : List (SieveSpec × (Int → Bool))} (hA : 1 ≤ A)
    (hfits : ∀ s ∈ specs, s.Fits) (hmg : mgs = specs.map (magic ·.p))
    (hspecs : specs = sfs.map Prod.fst) (hsfs : ∀ sf ∈ sfs, sf.1.Reads sf.2) :
    ⦃ True ⦄ siftBits w d b A rev sp1 specs mgs checks cl low high
    ⦃ fun out ↦ out.toList = (((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
        fun j ↦ classBit cl.bits j && sfs.all (·.2 j)).flatMap
          fun j ↦ acceptedPoints w d b rev checks (cl.numerator j) ⦄ := by
  vcgen [siftBits] invariants
  · SiftWhileInvariant (fun j ↦ acceptedPoints w d b rev checks (cl.numerator j))
      (fun j ↦ classBit cl.bits j && sfs.all (·.2 j)) low high
  · .ofMeasure fun s ↦ (high / rbaLength + 1 - s.2.2.1).toNat
  all_goals try simp only [SiftWhileInvariant, WhileInvariant.mk_apply, Variant.evalsTo_ofMeasure,
    Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure, meet_prop_eq_and,
    ofProp_prop_eq, ite_true] at *
  all_goals first
    | exact siftInvariant_empty _ _ ‹_› hA
    | exact toList_empty_eq_of_not_le ‹_›
    | exact ‹SiftInvariant _ _ _ _ true _ _ _ _›.toList_eq_flatMap_filter
    | exact ‹_ ∧ SiftInvariant _ _ _ _ false _ _ _ _›.2.exit_of_not_lt ‹_›
    | exact ⟨by have := rbaLength_pos; (try split) <;> lia, hfits, hmg⟩
    | obtain ⟨rfl, h⟩ := ‹_ ∧ SiftInvariant _ _ _ _ false _ _ _ _›
      first
        | exact ⟨h.toNat_sub_lt ‹_›, h.append h.w1_eq h.one_le_range (by lia)
            (ite_eq_toNat_mul_sub (by lia)) (of_forall_reads hspecs hsfs ‹_›)⟩
        | exact ⟨by lia, h.append (by lia) (by lia) (Int.le_refl _)
            (sub_toNat_emod_eq_toNat_mul_sub high) (of_forall_reads hspecs hsfs ‹_›)⟩

/-- The bits from `low` to `high` in pieces of `A ≥ 1` bit arrays, with the moduli `specs` and their
reciprocals, give the points of the numerators of the bits that pass the class word of `cl` and the
tests `sf.2` that the rows of the moduli read (`Ratpoints.Sieve.SieveSpec.Reads`), quantified in
the postcondition since the program does not mention them; an empty interval gives none; the loop
over the pieces ends by the measure `high / rbaLength + 1 - w0`, since every piece has at least one
bit array. -/
@[spec]
theorem siftBits_spec (w : Thunk (List Int)) (d b A : Nat) (rev : Bool) (sp1 : Nat)
    (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass)
    (low high : Int) :
    ⦃ 1 ≤ A ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ⦄
    siftBits w d b A rev sp1 specs mgs checks cl low high
    ⦃ fun out ↦ ∀ sfs : List (SieveSpec × (Int → Bool)), specs = sfs.map Prod.fst →
        (∀ sf ∈ sfs, sf.1.Reads sf.2) →
        out.toList = (((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
          fun j ↦ classBit cl.bits j && sfs.all (·.2 j)).flatMap
            fun j ↦ acceptedPoints w d b rev checks (cl.numerator j) ⦄ :=
  ⟨fun ⟨hA, hfits, hmg⟩ _ hspecs hsfs ↦ (siftBits_spec_reads w d b A rev sp1 specs mgs checks cl
    low high hA hfits hmg hspecs hsfs).le_wp trivial⟩

/-! ### One denominator -/

/-- The rows of the sieve entries `es` for the denominator `b` in the packing of the class `cl`,
with the row offsets from position `pos` of `offsets` on, as `Ratpoints.Sieve.setRows` makes them,
each with the test of the bits that it reads (`Ratpoints.Sieve.SieveSpec.Reads`): whether the row of
`b` admits the numerator of the bit (`Ratpoints.Sieve.SieveEntry.reads_row`). -/
def packedReads (es : List SieveEntry) (b : Nat) (cl : NumClass) (offsets : Array Nat) (pos : Nat) :
    List (SieveSpec × (Int → Bool)) :=
  es.mapIdx fun n e ↦
    (⟨e.p, offsets[pos + n]!, e.row (b * e.dinv[cl.k]! % e.p)⟩, fun j ↦ e.admits b (cl.numerator j))

/-- `Ratpoints.Sieve.setRows` reads the row of the residue `b dinv[k] mod p` of each modulus, the
residue `bp` that `Ratpoints.Sieve.fillBpList` gives (`Ratpoints.Sieve.fillBpList_eq_map`), from the
thunks of the rows of the entries, at the offsets of the class from its position `pos` on. -/
theorem setRows_map {es : List SieveEntry} (hp : ∀ e ∈ es, 0 < e.p) (b : Nat) {cl : NumClass}
    {pos : Nat} (hpos : cl.offset = some pos) (offsets : Array Nat) :
    setRows (es.map fun e ↦ (e.p, e.rows)) (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets =
      (packedReads es b cl offsets pos).map Prod.fst := by
  refine List.ext_getElem (by simp [setRows, packedReads]) fun n h1 h2 ↦ ?_
  have hn : n < es.length := by simpa [packedReads] using h2
  simp [setRows, packedReads, hpos,
    SieveEntry.get_rows _ (Nat.mod_lt _ (hp _ (List.getElem_mem hn)))]

theorem fits_of_mem_packedReads {es : List SieveEntry} {b : Nat} {cl : NumClass}
    {offsets : Array Nat} {pos : Nat}
    (hoff : ∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!) :
    ∀ s ∈ (packedReads es b cl offsets pos).map Prod.fst, s.Fits := by
  intro s hs
  obtain ⟨sf, hsf, rfl⟩ := List.mem_map.mp hs
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hsf
  exact (hoff n hn).fits _

theorem map_magic_packedReads (es : List SieveEntry) (b : Nat) (cl : NumClass) (offsets : Array Nat)
    (pos : Nat) :
    es.map (magic ·.p) = ((packedReads es b cl offsets pos).map Prod.fst).map (magic ·.p) :=
  List.ext_getElem (by simp [packedReads]) fun n _ _ ↦ by simp [packedReads]

/-- `2 ^ k (b dinv mod p) ≡ b (mod p)` for the inverse `dinv` of `2 ^ k` modulo `p`. -/
theorem two_pow_mul_mul_mod_mod {p k b dinv : Nat} (h : dinv * 2 ^ k % p = 1) :
    2 ^ k * (b * dinv % p) % p = b % p := by
  rw [Nat.mul_mod_mod, ← Nat.mul_assoc, Nat.mul_comm (2 ^ k) b, Nat.mul_assoc,
    Nat.mul_comm (2 ^ k) dinv, Nat.mul_mod_of_mod_eq_one _ h]

/-- The rows of `Ratpoints.Sieve.packedReads` read their tests, for entries whose factors have their
tables of inverses and whose offsets are those of the packing of the class. -/
theorem reads_of_mem_packedReads {es : List SieveEntry} {b : Nat} {cl : NumClass}
    {offsets : Array Nat} {pos : Nat} (hinv : ∀ e ∈ es, ∀ f ∈ e.factors, f.HasInverses e.p)
    (hoff : ∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!) :
    ∀ sf ∈ packedReads es b cl offsets pos, sf.1.Reads sf.2 := by
  intro sf hsf
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hsf
  have h := hoff n hn
  exact SieveEntry.reads_row (hinv _ (List.getElem_mem hn)) h.pos h.dinv_mul_mod h.mul_mod
    (two_pow_mul_mul_mod_mod h.dinv_mul_mod)

theorem all_packedReads (es : List SieveEntry) (b : Nat) (cl : NumClass) (offsets : Array Nat)
    (pos : Nat) (j : Int) :
    (packedReads es b cl offsets pos).all (·.2 j) = survives es b (cl.numerator j) := by
  rw [Bool.eq_iff_iff, List.all_eq_true, survives, List.all_eq_true]
  refine ⟨fun h e he ↦ ?_, fun h sf hsf ↦ ?_⟩
  · obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
    simpa [packedReads] using h _ (List.mem_mapIdx.mpr ⟨n, hn, rfl⟩)
  · obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hsf
    exact h _ (List.getElem_mem hn)

theorem _root_.Ratpoints.BruteForce.natAbs_le_of_mem_numerators {H : Nat} {a : Int}
    (h : a ∈ numerators H) : a.natAbs ≤ H := by
  simp only [numerators, List.mem_map, List.mem_range] at h
  lia

/-- For the points of `Ratpoints.Sieve.acceptedPoints` with the thunks of the products and of what
the third stage needs of the entries `es3` of the shape of
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, with the reciprocals of their moduli, for a denominator
`0 < b < 2 ^ 63` and `H < 2 ^ 63`, the numerators `-H, …, H` that pass the class word `w` and
survive the entries of the first two stages give the points that the brute-force reference finds
over those that pass `w` and survive the entries of all three stages, mapped by
`Ratpoints.Sieve.swapPoint` when the flag `rev` of the reversal is set
(`Ratpoints.Sieve.acceptedPoints_eq_ite`, `Ratpoints.Sieve.flatMap_checkNum`,
`Ratpoints.Sieve.pointsOfDen_eq_flatMap_checkNum`). -/
theorem flatMap_acceptedPoints_eq_pointsOfDen {c : List Int} {d b : Nat} {rev : Bool}
    {w : UInt64} {entries es3 : List SieveEntry} (hes : ∀ e ∈ es3, e.IsPrimeEntry) {H : Nat}
    (hb : 0 < b) (hb63 : b < 2 ^ 63) (hH : H < 2 ^ 63) :
    ((numerators H).filter fun a ↦ classBit w a && survives entries b a).flatMap
        (acceptedPoints (.mk fun _ ↦ scaledCoeffs c d b) d b rev
          (.mk fun _ ↦ fillChecks b H es3 (es3.map fun e ↦ magic e.p))) =
      (pointsOfDen c d b ((numerators H).filter fun a ↦
        classBit w a && survives (entries ++ es3) b a)).map (if rev then swapPoint else id) := by
  rw [pointsOfDen_eq_flatMap_checkNum, ← flatMap_checkNum,
    List.flatMap, List.map_congr_left fun a ha ↦ acceptedPoints_eq_ite hes rfl _ _ rev hb hb63
      (natAbs_le_of_mem_numerators (List.mem_filter.mp ha).1) hH, ← List.flatMap,
    ← List.flatMap_filter, List.filter_filter]
  simp only [survives_append, Bool.and_comm (survives es3 b _), Bool.and_assoc]
  rfl

/-- The bits from `⌈(-H - a₀) / 2 ^ k⌉` to `⌊(H - a₀) / 2 ^ k⌋` of the packing of a class `cl` of
the class word `w` (`Ratpoints.Sieve.NumClass.Packs`), with the tests of the rows of the entries
`entries` read in the packing, give the points of the numerators `-H, …, H` that pass `w` and
survive these entries: the numerators of the bits are those of the class among `-H, …, H`
(`Ratpoints.Sieve.map_range_numerator_eq_filter_numerators`), the pattern of the class lets the
numerator of a bit through exactly when `w` does (`Ratpoints.Sieve.NumClass.Packs.classBit_bits`),
and `w` lets nothing off the class through. -/
theorem flatMap_filter_bits_eq {cl : NumClass} {w : UInt64} (hcl : cl.Packs w)
    {entries : List SieveEntry} {b H : Nat} {lo hi : Int}
    (hlo : lo = -((cl.a0 + H : Int) / 2 ^ cl.k))
    (hhi : hi = ((H : Int) - cl.a0) / 2 ^ cl.k) {test : Int → Bool}
    (htest : ∀ j, test j = survives entries b (cl.numerator j)) (g : Int → List (Int × Int × Int)) :
    (((List.range (hi + 1 - lo).toNat).map fun k : Nat ↦ lo + k).filter
        fun j ↦ classBit cl.bits j && test j).flatMap (fun j ↦ g (cl.numerator j)) =
      ((numerators H).filter fun a ↦ classBit w a && survives entries b a).flatMap g := by
  rw [← List.flatMap_map, ← hcl.filter_filter_emod,
    ← map_range_numerator_eq_filter_numerators hcl.toWF hlo hhi]
  simp only [List.filter_map, List.map_map]
  congr 2
  exact List.filter_congr fun j _ ↦ by simp [hcl.classBit_bits, htest]

-- The contract of `Ratpoints.Sieve.sift` for the rows, reciprocals and residues of the sieve
-- entries `entries` in the packing of the class `cl` of the class word `w`.
private theorem sift_spec_map (c : List Int) (d H b : Nat) (rev : Bool) (sp1 : Nat)
    (es3 : List SieveEntry) {A : Nat} {entries : List SieveEntry} {w : UInt64} {cl : NumClass}
    {pos : Nat} (offsets : Array Nat) (hA : 1 ≤ A) (hb : 0 < b) (hb63 : b < 2 ^ 63)
    (hH : H < 2 ^ 63) (hes : ∀ e ∈ es3, e.IsPrimeEntry) (hcl : cl.Packs w)
    (hpos : cl.offset = some pos) (hinv : ∀ e ∈ entries, ∀ f ∈ e.factors, f.HasInverses e.p)
    (hoff : ∀ n (h : n < entries.length), entries[n].PackedFor cl offsets[pos + n]!) :
    ⦃ True ⦄
    sift c d H A b rev sp1 (entries.map fun e ↦ (e.p, e.rows)) (entries.map (magic ·.p))
      (entries.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets es3 (es3.map fun e ↦ magic e.p)
    ⦃ fun out ↦ out.toList = (pointsOfDen c d b ((numerators H).filter fun a ↦
        classBit w a && survives (entries ++ es3) b a)).map (if rev then swapPoint else id) ⦄ := by
  have hp (e : SieveEntry) (he : e ∈ entries) : 0 < e.p := by
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
    exact (hoff n hn).pos
  have hrows := setRows_map hp b hpos offsets
  obtain ⟨hl, hh⟩ := toInt_numeratorsToBits_height hH hcl.toWF
  vcgen [sift]
  · rw [hrows]
    exact ⟨hA, fits_of_mem_packedReads hoff, map_magic_packedReads ..⟩
  · rename_i h
    rw [h _ hrows (reads_of_mem_packedReads hinv hoff),
      flatMap_filter_bits_eq hcl hl hh (all_packedReads entries b cl offsets pos),
      flatMap_acceptedPoints_eq_pointsOfDen hes hb hb63 hH]

/-- The sieve entries of the first two stages, the class word `w` that the class `cl` packs, the
position `pos` of the row offsets of `cl` and what the packing needs of the entries are quantified
in the postcondition, since the program does not mention them: the rows, the reciprocals and the
residues `b dinv[k] mod p` (`Ratpoints.Sieve.fillBpList_eq_map`) of the entries, their tables of
inverses, and the offsets of the packing of `cl` (`Ratpoints.Sieve.SieveEntry.PackedFor`); the test
for common factors on the words of the C code needs `0 < b < 2 ^ 63` and the numerators
`|a| ≤ H < 2 ^ 63` (`Ratpoints.Sieve.accepted_spec`), and the third stage entries of the shape of
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry` with the reciprocals of their moduli. -/
@[spec]
theorem sift_spec (c : List Int) (d H A b : Nat) (rev : Bool) (sp1 : Nat)
    (rows : List (Nat × Array (Thunk (Array UInt64)))) (mgs bp : List Nat) (cl : NumClass)
    (offsets : Array Nat) (es3 : List SieveEntry) (mgs3 : List Nat) :
    ⦃ 1 ≤ A ∧ 0 < b ∧ b < 2 ^ 63 ∧ H < 2 ^ 63 ∧ (∀ e ∈ es3, e.IsPrimeEntry) ∧
        mgs3 = es3.map fun e ↦ magic e.p ⦄
    sift c d H A b rev sp1 rows mgs bp cl offsets es3 mgs3
    ⦃ fun out ↦ ∀ (entries : List SieveEntry) (w : UInt64) (pos : Nat), cl.Packs w →
        cl.offset = some pos → rows = entries.map (fun e ↦ (e.p, e.rows)) →
        mgs = entries.map (magic ·.p) → bp = entries.map (fun e ↦ b * e.dinv[cl.k]! % e.p) →
        (∀ e ∈ entries, ∀ f ∈ e.factors, f.HasInverses e.p) →
        (∀ n (h : n < entries.length), entries[n].PackedFor cl offsets[pos + n]!) →
        out.toList = (pointsOfDen c d b ((numerators H).filter fun a ↦
          classBit w a && survives (entries ++ es3) b a)).map (if rev then swapPoint else id) ⦄ :=
  ⟨fun ⟨hA, hb, hb63, hH, hes, hmg3⟩ _ _ _ hcl hpos hrows hmg hbp hinv hoff ↦ by
    subst hrows hmg hbp hmg3
    exact (sift_spec_map c d H b rev sp1 es3 offsets hA hb hb63 hH hes hcl hpos hinv hoff).le_wp
      trivial⟩

/-- `Ratpoints.Sieve.sift` with the flag `rev` of the reversal, the class `cl` that packs the class
word `w` with its row offsets from position `pos` of `offsets` on, the entries `entries` of the
first two stages with their rows, reciprocals and residues `b dinv[k] mod p`, their tables of
inverses and the offsets of the packing of `cl`, and the entries `es3` of the third, of the shape of
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, with the reciprocals of their moduli, for a denominator
`0 < b < 2 ^ 63` and `H < 2 ^ 63`, gives the points of the plain sieve with all these entries and
its check, the reference of the words, whose numerators pass `w` (`Ratpoints.Sieve.classBit`),
mapped by `Ratpoints.Sieve.swapPoint` when `rev` is set: the plain sieve and its check give what the
brute-force reference finds over `b` and the numerators `-H, …, H` that survive the sieve entries
(`Ratpoints.Sieve.sieveDen_spec`, `Ratpoints.Sieve.checkDen_spec`), and `Ratpoints.Sieve.sift` gives
those of these points whose numerators pass `w`, mapped (`Ratpoints.Sieve.sift_spec`,
`Ratpoints.BruteForce.pointsOfDen_filter`). -/
theorem toList_run_sift_eq_checkDen (c : List Int) (d H b : Nat) (rev : Bool) (sp1 : Nat)
    {A : Nat} (hA : 1 ≤ A) (hb : 0 < b) (hb63 : b < 2 ^ 63) (hH : H < 2 ^ 63)
    {entries es3 : List SieveEntry} {w : UInt64} {cl : NumClass} {pos : Nat} (offsets : Array Nat)
    (hes : ∀ e ∈ es3, e.IsPrimeEntry) (hcl : cl.Packs w) (hpos : cl.offset = some pos)
    (hinv : ∀ e ∈ entries, ∀ f ∈ e.factors, f.HasInverses e.p)
    (hoff : ∀ n (h : n < entries.length), entries[n].PackedFor cl offsets[pos + n]!) :
    (Id.run (sift c d H A b rev sp1 (entries.map fun e ↦ (e.p, e.rows)) (entries.map (magic ·.p))
      (entries.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets es3
        (es3.map fun e ↦ magic e.p))).toList =
      ((Id.run (checkDen c d H b (Id.run (sieveDen H b (entries ++ es3))))).toList.filter
        fun q ↦ classBit w q.1).map (if rev then swapPoint else id) :=
  ((sift_spec_map c d H b rev sp1 es3 offsets hA hb hb63 hH hes hcl hpos hinv hoff).le_wp
    trivial).trans <| by
    rw [← List.filter_filter, pointsOfDen_filter, ← (checkDen_spec c d H b _).le_wp trivial _
      ((sieveDen_spec H b (entries ++ es3)).le_wp trivial)]
    rfl

end Sieve

end Ratpoints

end
