/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Packing
public import Ratpoints.Proof.Stages

import Ratpoints.Proof.Containers
import Std.Tactic.Do

/-!
# The contracts of the scan of a piece

The contracts of the components of the model on words from the walk through the set bits of a word
on, through the second stage and the extraction of one bit array, up to the scan of a piece, as
`@[spec]` theorems proved with `vcgen`, the program logic of Lean core, with loop invariants that
are named definitions. The contracts speak of the bits `j` of the packing of a class `cl`
(`Ratpoints.Sieve.NumClass`), each standing for the numerator `a₀ + 2 ^ k j`
(`Ratpoints.Sieve.NumClass.numerator`), and of the words of the bit arrays and-ed with the rows of
the moduli of the second stage at their offsets (`Ratpoints.Sieve.andWords`); the points of a
numerator are those that the extraction gives for it (`Ratpoints.Sieve.acceptedPoints`).

## Main definitions

* `Ratpoints.Sieve.SiftBitArrayInvariant`, `Ratpoints.Sieve.ScanPieceInvariant`: the points that
  the loops of the extraction of one bit array and of the scan of a piece have found so far.

## Main statements

* `Ratpoints.Sieve.walkWord_spec`: the walk through the set bits of a word appends the points of the
  numerators `a0 + step t` of its set bits `t`, in increasing order.
* `Ratpoints.Sieve.siftBitArrayByWords_spec`, `Ratpoints.Sieve.siftBitArrayWhole_spec`,
  `Ratpoints.Sieve.siftBitArray_spec`: in either arm of the second stage, one bit array appends the
  points of the numerators of the set bits of its words and-ed with the rows of the moduli of the
  second stage, in increasing order.
* `Ratpoints.Sieve.scanPiece_spec`: if the bits of a piece and-ed with the rows of the second stage
  are a test `keep` of the bits, the scan of the piece gives the points of the numerators of its
  bits that pass `keep`, in increasing order.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Words`, `Ratpoints.Proof.Stages` and
`Ratpoints.Proof.Packing` do, whose lemmas on bit arrays, rows, walks and classes and whose
contracts of the second stage and of the test of a candidate it builds on. The walk reads the test
of a candidate as its value (`Ratpoints.Sieve.acceptedPoints`), so that the contracts need nothing
of the numerators and the denominator. The contracts of the pieces, of the bits of one interval and
of the sieve of one denominator are in `Ratpoints.Proof.Sift`.
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

/-- The invariant of the loops of the two arms of `Ratpoints.Sieve.siftBitArray` over the words of
the bit array with the word number `i`, after its first `k` words, for the words `words κ` that the
walks go through, the class `cl` and the points `g a` of a numerator `a`: `out` is `out0` followed
by the points of the numerators of the bits `rbaLength i + 64 κ + t` of the set bits `t` of the
words `κ < k` in the packing of `cl` (`Ratpoints.Sieve.NumClass.numerator`), in increasing order. -/
def SiftBitArrayInvariant (words : Nat → UInt64) (g : Int → List (Int × Int × Int)) (cl : NumClass)
    (i : Int) (out0 : Array (Int × Int × Int)) (k : Nat) (out : Array (Int × Int × Int)) : Prop :=
  out.toList = out0.toList ++ ((List.range k).flatMap fun κ ↦
    ((List.range 64).filter ((words κ).toBitVec.getLsbD ·)).map fun t : Nat ↦
      i * rbaLength + 64 * κ + t).flatMap fun j ↦ g (cl.numerator j)

/-- `Ratpoints.Sieve.SiftBitArrayInvariant` after the words `0, …, k`, with the numerator `a0` of
bit `0` of word `k`, `a₀ + i (rbaLength 2 ^ cl.k) + k (64 2 ^ cl.k)` as the program computes it,
for the stride `2 ^ cl.k` of the class: the invariant of the loop over the words after the first in
the arm of the second stage on the whole bit array (`Ratpoints.Sieve.siftBitArrayWhole`), which
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

/-- At the end of the loops of the two arms of `Ratpoints.Sieve.siftBitArray`, when the words walked
through are those of the copy `nums` and-ed with the rows of the moduli of `specs`
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

/-- `Ratpoints.Sieve.SiftBitArrayInvariant.toList_eq` for the invariant with the numerator of bit
`0` of the last word, at the end of the loop over the words after the first. -/
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
    lia [rbaPack_pos]
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

/- The invariants are irreducible from here on: the verification conditions of the two arms of
`Ratpoints.Sieve.siftBitArray` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] SiftBitArrayInvariant SiftBitArrayWalkInvariant

/-- The arm for one word at a time walks through the set bits of the words of `nums` and-ed with the
rows of the moduli of `specs` (`Ratpoints.Sieve.secondStageWord_spec`), each bit `j` standing for
the numerator `a₀ + 2 ^ k j` of the class `cl`, and skips a word that is zero, which loses
nothing. -/
@[spec]
theorem siftBitArrayByWords_spec (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (nums : Vector UInt64 rbaPack) (out : Array (Int × Int × Int)) :
    ⦃ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small i (i + 1) ⦄
    siftBitArrayByWords w d b rev specs mgs small checks cl i nums out
    ⦃ fun out' ↦ out'.toList = out.toList ++ ((List.range rbaPack).flatMap fun κ ↦
        ((List.range 64).filter ((andWords specs nums[κ]! i κ).toBitVec.getLsbD ·)).map
          fun t : Nat ↦ i * rbaLength + 64 * κ + t).flatMap
            fun j ↦ acceptedPoints w d b rev checks (cl.numerator j) ⦄ := by
  vcgen [siftBitArrayByWords] invariants
  | inv1 => fun done _ ↦ SiftBitArrayInvariant (fun κ ↦ andWords specs nums[κ]! i κ)
      (acceptedPoints w d b rev checks) cl i out done.length
  all_goals subst_vars
  all_goals first
    | exact ‹(∀ s ∈ specs, s.Fits) ∧ _›
    | exact Std.Legacy.Range.lt_of_toList_eq_append_cons ‹_›
    | exact siftBitArrayInvariant_zero ..
    | exact SiftBitArrayInvariant.append ‹_› ‹_› ‹_›
    | exact SiftBitArrayInvariant.append_of_eq_zero ‹_› ‹_› (by simp_all)
    | exact SiftBitArrayInvariant.toList_eq (fun _ _ ↦ rfl) ‹_›

/-- The arm of the second stage on the whole bit array walks through the set bits of the words of
`nums` and-ed with the rows of the moduli of `specs` (`Ratpoints.Sieve.secondStage_spec`), each bit
`j` standing for the numerator `a₀ + 2 ^ k j` of the class `cl`, and skips the walks when the second
stage leaves the bit array zero, which loses nothing. -/
@[spec]
theorem siftBitArrayWhole_spec (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (nums : Vector UInt64 rbaPack) (out : Array (Int × Int × Int)) :
    ⦃ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small i (i + 1) ⦄
    siftBitArrayWhole w d b rev specs mgs small checks cl i nums out
    ⦃ fun out' ↦ out'.toList = out.toList ++ ((List.range rbaPack).flatMap fun κ ↦
        ((List.range 64).filter ((andWords specs nums[κ]! i κ).toBitVec.getLsbD ·)).map
          fun t : Nat ↦ i * rbaLength + 64 * κ + t).flatMap
            fun j ↦ acceptedPoints w d b rev checks (cl.numerator j) ⦄ := by
  vcgen [siftBitArrayWhole] invariants
  | inv1 => fun done _ ↦ SiftBitArrayWalkInvariant (fun κ ↦ nums[κ]!)
      (acceptedPoints w d b rev checks) cl i out done.length
  all_goals first
    | exact siftBitArrayWalkInvariant_zero ‹_›
    | exact SiftBitArrayWalkInvariant.append ‹_› ‹_› ‹_›
    | exact SiftBitArrayWalkInvariant.toList_eq ‹_› ‹_›
    | exact toList_eq_append_of_isZeroAt ‹_› ‹_›

/-- Both arms append the points of the numerators of the set bits of the same words, the words of
`nums` and-ed with the rows of the moduli of `specs`
(`Ratpoints.Sieve.siftBitArrayByWords_spec`, `Ratpoints.Sieve.siftBitArrayWhole_spec`). -/
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
  cases useLong
  · exact siftBitArrayWhole_spec ..
  · exact siftBitArrayByWords_spec ..

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

end Sieve

end Ratpoints

end
