/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Sieve
public import Ratpoints.Proof.Stages
public import Ratpoints.Proof.Words
public import Std.WP

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Sieve
import Std.Tactic.Do

/-!
# The contracts of the sieve of one denominator

The contracts of the components of the model on words from the walk through the set bits of a word
on, through the second stage and the extraction of one bit array and the scan of a piece, up to the
sieve of one denominator from a class word, the numerators modulo 64 from which the first stage
starts, as `@[spec]` theorems proved with `vcgen`, the program logic of Lean core, with loop
invariants that are named definitions.

## Main statements

* `Ratpoints.Sieve.walkWord_spec`: the walk through the set bits of a word appends the points of the
  numerators of its set bits, in increasing order.
* `Ratpoints.Sieve.siftBitArray_spec`: in either arm of the second stage, one bit array appends the
  points of the numerators of the set bits of its words and-ed with the rows of the moduli of the
  second stage, in increasing order.
* `Ratpoints.Sieve.scanPiece_spec`: if the bits of a piece and-ed with the rows of the second stage
  are a test `keep` of their numerators, the scan of the piece gives the points of its numerators
  that pass `keep`, in increasing order.
* `Ratpoints.Sieve.siftPiece_spec`: one piece with the rows of a denominator `b` and a class word
  gives the points of the numerators that the masks at its two ends leave and that pass the class
  word (`Ratpoints.Sieve.classBit`) and survive the entries of the first two stages, in increasing
  order.
* `Ratpoints.Sieve.sift_spec`: the pieces of a denominator `0 < b < 2 ^ 63`, for `H < 2 ^ 63` and
  entries of the third stage of the shape of `Ratpoints.Sieve.SieveEntry.IsPrimeEntry` with the
  reciprocals of their moduli, give what the brute-force reference finds over `b` and the
  numerators `-H, …, H` that pass the class word and survive the sieve entries of all three stages,
  mapped by `Ratpoints.Sieve.swapPoint` when the flag of the reversal is set;
  `Ratpoints.Sieve.toList_run_sift_eq_checkDen`: these are the points that the plain sieve of `b`
  with all the entries gives whose numerators pass the class word, mapped in the same way.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Words` and `Ratpoints.Proof.Stages` do,
whose lemmas on bit arrays, rows and walks and whose contracts of the second and the third stage it
builds on. The walk reads the test of a candidate as its value (`Ratpoints.Sieve.acceptedPoints`),
so that the contracts of the walk, of one bit array, of the scan and of one piece need nothing of
the numerators and the denominator; the hypotheses of the test on the words of the C code,
`0 < b < 2 ^ 63` and `|a| ≤ H < 2 ^ 63`, come in with the numerators `-H, …, H` of one denominator
(`Ratpoints.Sieve.acceptedPoints_eq_ite`). The contract of the run over the denominators, which
calls `Ratpoints.Sieve.sift` with the class word of each denominator, is in
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
    (checks : Thunk (List CheckSpec)) (x : UInt64) (a0 : Int) (out : Array (Int × Int × Int)) :
    ⦃ True ⦄ walkWord w d b rev checks x a0 out
    ⦃ fun out' ↦ out'.toList = out.toList ++
        (((List.range 64).filter (x.toBitVec.getLsbD ·)).map fun t : Nat ↦ a0 + t).flatMap
          (acceptedPoints w d b rev checks) ⦄ := by
  vcgen [walkWord, accepted_value] invariants
  · WalkWordWhileInvariant (fun t : Nat ↦ acceptedPoints w d b rev checks (a0 + t)) x out
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
through and the points `g a` of a numerator `a`: `out` is `out0` followed by the points of the
numerators `rbaLength i + 64 κ + t` of the set bits `t` of the words `κ < k`, in increasing
order. -/
def SiftBitArrayInvariant (words : Nat → UInt64) (g : Int → List (Int × Int × Int)) (i : Int)
    (out0 : Array (Int × Int × Int)) (k : Nat) (out : Array (Int × Int × Int)) : Prop :=
  out.toList = out0.toList ++ ((List.range k).flatMap fun κ ↦
    ((List.range 64).filter ((words κ).toBitVec.getLsbD ·)).map fun t : Nat ↦
      i * rbaLength + 64 * κ + t).flatMap g

/-- `Ratpoints.Sieve.SiftBitArrayInvariant` with the numerator `a0` of bit `0` of the next word, the
invariant of the loop over the words in the arm of `Ratpoints.Sieve.siftBitArray` that runs the
second stage on the whole bit array. -/
def SiftBitArrayWalkInvariant (words : Nat → UInt64) (g : Int → List (Int × Int × Int)) (i : Int)
    (out0 : Array (Int × Int × Int)) (k : Nat) (s : Array (Int × Int × Int) × Int) : Prop :=
  s.2 = i * rbaLength + 64 * k ∧ SiftBitArrayInvariant words g i out0 k s.1

theorem siftBitArrayInvariant_zero (words : Nat → UInt64) (g : Int → List (Int × Int × Int))
    (i : Int) (out : Array (Int × Int × Int)) : SiftBitArrayInvariant words g i out 0 out := by
  simp [SiftBitArrayInvariant]

theorem SiftBitArrayInvariant.append {words : Nat → UInt64} {g : Int → List (Int × Int × Int)}
    {i : Int} {out0 out r : Array (Int × Int × Int)} {done suff : List Nat} {cur : Nat}
    (h : SiftBitArrayInvariant words g i out0 done.length out)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff)
    (hr : r.toList = out.toList ++ (((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ i * rbaLength + 64 * cur + t).flatMap g) :
    SiftBitArrayInvariant words g i out0 (done ++ [cur]).length r := by
  rw [SiftBitArrayInvariant, hr, h, List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl, List.range_succ (n := cur),
    List.flatMap_append, List.flatMap_singleton, List.flatMap_append, List.append_assoc]

theorem SiftBitArrayInvariant.append_of_eq_zero {words : Nat → UInt64}
    {g : Int → List (Int × Int × Int)} {i : Int} {out0 out : Array (Int × Int × Int)}
    {done suff : List Nat} {cur : Nat} (h : SiftBitArrayInvariant words g i out0 done.length out)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff) (hz : words cur = 0) :
    SiftBitArrayInvariant words g i out0 (done ++ [cur]).length out :=
  h.append hl (by simp [hz])

theorem siftBitArrayWalkInvariant_zero (words : Nat → UInt64) (g : Int → List (Int × Int × Int))
    (i : Int) (out : Array (Int × Int × Int)) :
    SiftBitArrayWalkInvariant words g i out 0 (out, i * rbaLength) :=
  ⟨by simp, siftBitArrayInvariant_zero words g i out⟩

theorem SiftBitArrayWalkInvariant.append {words : Nat → UInt64}
    {g : Int → List (Int × Int × Int)} {i : Int} {out0 r : Array (Int × Int × Int)}
    {done suff : List Nat} {cur : Nat} {s : Array (Int × Int × Int) × Int}
    (h : SiftBitArrayWalkInvariant words g i out0 done.length s)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff)
    (hr : r.toList = s.1.toList ++
      (((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map fun t : Nat ↦ s.2 + t).flatMap
        g) :
    SiftBitArrayWalkInvariant words g i out0 (done ++ [cur]).length (r, s.2 + 64) := by
  have hκ := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨by simp only [h.1, List.length_append, List.length_singleton]; push_cast; lia,
    h.2.append hl ?_⟩
  rw [hr, h.1, hκ]

/-- At the end of the loops of `Ratpoints.Sieve.siftBitArray`, when the words walked through are
those of the copy `nums` and-ed with the rows of the moduli of `specs`
(`Ratpoints.Sieve.andWords`). -/
theorem SiftBitArrayInvariant.toList_eq {words : Nat → UInt64} {g : Int → List (Int × Int × Int)}
    {specs : List SieveSpec} {i : Int} {nums : Vector UInt64 rbaPack}
    {out0 out : Array (Int × Int × Int)} (hw : ∀ κ < rbaPack, words κ = andWords specs nums[κ]! i κ)
    (h : SiftBitArrayInvariant words g i out0 (ForIn.toList [0:rbaPack]).length out) :
    out.toList = out0.toList ++ ((List.range rbaPack).flatMap fun κ ↦
      ((List.range 64).filter ((andWords specs nums[κ]! i κ).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ i * rbaLength + 64 * κ + t).flatMap g := by
  rw [h, Std.Legacy.Range.length_toList]
  exact congrArg (out0.toList ++ ·) <| congrArg (List.flatMap g) <| congrArg List.flatten <|
    List.map_congr_left fun κ hκ ↦ by rw [hw κ (List.mem_range.mp hκ)]

/-- `Ratpoints.Sieve.SiftBitArrayInvariant.toList_eq` for the invariant with the numerator of the
next word. -/
theorem SiftBitArrayWalkInvariant.toList_eq {words : Nat → UInt64}
    {g : Int → List (Int × Int × Int)} {specs : List SieveSpec} {i : Int}
    {nums : Vector UInt64 rbaPack} {out0 : Array (Int × Int × Int)}
    {s : Array (Int × Int × Int) × Int} (hw : ∀ κ < rbaPack, words κ = andWords specs nums[κ]! i κ)
    (h : SiftBitArrayWalkInvariant words g i out0 (ForIn.toList [0:rbaPack]).length s) :
    s.1.toList = out0.toList ++ ((List.range rbaPack).flatMap fun κ ↦
      ((List.range 64).filter ((andWords specs nums[κ]! i κ).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ i * rbaLength + 64 * κ + t).flatMap g :=
  h.2.toList_eq hw

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
`Ratpoints.Sieve.secondStageWord_spec`): the arm for one word at a time skips a word that is zero,
and the other skips the walks when the second stage leaves the bit array zero, which lose nothing;
each arm has its own invariant (`Ratpoints.Sieve.SiftBitArrayInvariant`,
`Ratpoints.Sieve.SiftBitArrayWalkInvariant`). -/
@[spec]
theorem siftBitArray_spec (useLong : Bool) (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (specs : List SieveSpec) (checks : Thunk (List CheckSpec)) (i : Int)
    (nums : Vector UInt64 rbaPack) (out : Array (Int × Int × Int)) :
    ⦃ True ⦄ siftBitArray useLong w d b rev specs checks i nums out
    ⦃ fun out' ↦ out'.toList = out.toList ++ ((List.range rbaPack).flatMap fun κ ↦
        ((List.range 64).filter ((andWords specs nums[κ]! i κ).toBitVec.getLsbD ·)).map
          fun t : Nat ↦ i * rbaLength + 64 * κ + t).flatMap
            (acceptedPoints w d b rev checks) ⦄ := by
  vcgen [siftBitArray] invariants
  | inv1 => fun done _ ↦ SiftBitArrayInvariant (fun κ ↦ andWords specs nums[κ]! i κ)
      (acceptedPoints w d b rev checks) i out done.length
  | inv2 => fun done _ ↦ SiftBitArrayWalkInvariant (fun κ ↦ nums[κ]!)
      (acceptedPoints w d b rev checks) i out done.length
  all_goals subst_vars
  all_goals first
    | exact Std.Legacy.Range.lt_of_toList_eq_append_cons ‹_›
    | exact siftBitArrayInvariant_zero ..
    | exact siftBitArrayWalkInvariant_zero ..
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
with their rows and the points `g a` of a numerator `a` (in the scan, those of
`Ratpoints.Sieve.acceptedPoints`): `pos ≤ n`, and `out` holds the points of the numerators
`rbaLength w0 + 64 y + t` of the set bits `t` of the words `y < rbaPack pos` and-ed with the rows of
`specs` (`Ratpoints.Sieve.andWords`), in increasing order. -/
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

/-- Bit array `pos` adds the points of the numerators of the set bits of its words and-ed with the
rows. -/
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
`w0 + pos`, adds the points of the numerators of the set bits of its words and-ed with the rows. -/
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

/- The invariants are irreducible from here on: the verification conditions of
`Ratpoints.Sieve.scanPiece` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] ScanPieceSentinelInvariant ScanPieceInvariant

-- The contract of `Ratpoints.Sieve.scanPiece` in terms of the set bits of the words of the piece
-- and-ed with the rows of the second stage.
private theorem scanPiece_spec_getLsbD (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (specs : List SieveSpec) (checks : Thunk (List CheckSpec)) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ True ⦄ scanPiece w d b rev specs checks w0 n surv
    ⦃ fun out ↦ out.toList = ((List.range (n * rbaPack)).flatMap fun y : Nat ↦
        ((List.range 64).filter ((andWords specs surv[y]! w0 y).toBitVec.getLsbD ·)).map
          fun t : Nat ↦ rbaLength * w0 + 64 * y + t).flatMap
            (acceptedPoints w d b rev checks) ⦄ := by
  vcgen [scanPiece] invariants
  | inv1 => fun done _ ↦ ScanPieceSentinelInvariant n surv done.length
  | inv2 sv _ => ScanPieceWhileInvariant sv specs (acceptedPoints w d b rev checks) w0 n
  | inv3 => Std.WP.Variant.ofMeasure fun s : Nat × Array (Int × Int × Int) ↦ n - s.1
  | inv4 sv _ pos0 out _ _ =>
      ScanPieceZeroInvariant sv specs (acceptedPoints w d b rev checks) w0 n pos0 out
  | inv5 => Std.WP.Variant.ofMeasure fun s : Nat ↦ n - s
  all_goals first
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
    (specs : List SieveSpec) (checks : Thunk (List CheckSpec)) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    ⦃ True ⦄ scanPiece w d b rev specs checks w0 n surv
    ⦃ fun out ↦ ∀ keep : Int → Bool, (∀ y < n * rbaPack, ∀ t : Nat,
        (andWords specs surv[y]! w0 y).toBitVec.getLsbD t =
          (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t))) →
      out.toList = (((List.range (n * rbaLength)).map fun k : Nat ↦
        rbaLength * w0 + k).filter keep).flatMap (acceptedPoints w d b rev checks) ⦄ :=
  ⟨fun _ keep hkeep ↦ by
    rw [(scanPiece_spec_getLsbD w d b rev specs checks w0 n surv).le_wp trivial,
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
words `v` (`hout`, as `Ratpoints.Sieve.scanPiece_spec` states it, with the points `g a` of a
numerator `a`), when `v` is `surv` with the masks applied: the points of the numerators from
`rbaLength w0 + maskLow` to `rbaLength (w0 + n) - 1 - maskHigh` that pass the class word
(`Ratpoints.Sieve.classBit`) and survive all the entries of `specs`. -/
theorem IsMasked.toList_eq {n : Nat} {g : Int → List (Int × Int × Int)} {b sp1 : Nat}
    {specs : List SieveSpec} {cw : UInt64} {w0 : Int} {maskLow maskHigh : Nat}
    {surv v : Vector UInt64 ((n + 1) * rbaPack)} {out : Array (Int × Int × Int)}
    (hand : ∀ (entries : List SieveEntry) (b : Nat), (∀ e ∈ entries, 0 < e.p) →
      specs.take sp1 = entries.map (fun e ↦ ⟨e.p, e.row b⟩) → ∀ y < n * rbaPack, ∀ t : Nat,
        surv[y]!.toBitVec.getLsbD t =
          (cw.toBitVec.getLsbD t && survives entries b (rbaLength * w0 + 64 * y + t)))
    (h : IsMasked n maskLow maskHigh surv v)
    (hout : ∀ keep : Int → Bool, (∀ y < n * rbaPack, ∀ t : Nat,
        (andWords (specs.drop sp1) v[y]! w0 y).toBitVec.getLsbD t =
          (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t))) →
      out.toList = (((List.range (n * rbaLength)).map fun k : Nat ↦
        rbaLength * w0 + k).filter keep).flatMap g)
    {entries : List SieveEntry} (hp : ∀ e ∈ entries, 0 < e.p)
    (hspecs : specs = entries.map (fun e ↦ ⟨e.p, e.row b⟩)) :
    out.toList = (((List.range (n * rbaLength - maskLow - maskHigh)).map fun k : Nat ↦
      rbaLength * w0 + maskLow + k).filter fun a ↦ classBit cw a && survives entries b a).flatMap
        g := by
  rw [hout (fun a ↦ (classBit cw a && survives entries b a) &&
    decide (rbaLength * w0 + maskLow ≤ a ∧ a + maskHigh < rbaLength * w0 + (n * rbaLength : Nat)))
    fun y hy t ↦ ?_, ← List.filter_filter, List.filter_map_range_eq_map_range]
  by_cases ht : t < 64
  · rw [hspecs, ← List.map_drop, getLsbD_andWords_map b (fun e he ↦ hp e (List.mem_of_mem_drop he)),
      h y hy t ht, hand (entries.take sp1) b (fun e he ↦ hp e (List.mem_of_mem_take he))
        (by rw [hspecs, List.map_take]) y hy t, classBit_rbaLength_mul_add cw w0 y ht,
      ← List.take_append_drop sp1 entries, survives_append, List.take_append_drop]
    grind
  · simp [ht, BitVec.getLsbD_of_ge _ t (Nat.le_of_not_lt ht)]

/-- The sieve entries are quantified in the postcondition, since the program does not mention them,
and the first `sp1` of them go to the first stage, the others to the second; the bound on
`maskHigh` is that of the high mask (`Ratpoints.Sieve.getLsbD_clearHighBits`), and the low mask
needs none. -/
@[spec]
theorem siftPiece_spec (w : Thunk (List Int)) (d b : Nat) (rev : Bool) (sp1 : Nat)
    (specs : List SieveSpec) (checks : Thunk (List CheckSpec)) (cw : UInt64) (w0 : Int)
    (n maskLow maskHigh : Nat) :
    ⦃ maskHigh < rbaLength ⦄ siftPiece w d b rev sp1 specs checks cw w0 n maskLow maskHigh
    ⦃ fun out ↦ ∀ entries : List SieveEntry, (∀ e ∈ entries, 0 < e.p) →
        specs = entries.map (fun e ↦ ⟨e.p, e.row b⟩) →
        out.toList = (((List.range (n * rbaLength - maskLow - maskHigh)).map fun k : Nat ↦
          rbaLength * w0 + maskLow + k).filter fun a ↦
            classBit cw a && survives entries b a).flatMap (acceptedPoints w d b rev checks) ⦄ := by
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
  have hR := natCast_rbaLength_pos
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
  have := Int.emod_lt_of_pos (H : Int) natCast_rbaLength_pos
  have := Int.emod_nonneg (H : Int) (Int.ne_of_gt natCast_rbaLength_pos)
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
  · have hR := natCast_rbaLength_pos
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
  have hR := natCast_rbaLength_pos
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

/-- The loop of `Ratpoints.Sieve.sift` ends at the word number one past that of `H`. -/
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

/-- At the exit of the loop of `Ratpoints.Sieve.sift`, the points found are those of the numerators
`-H, …, H` that pass `keep`. -/
theorem SiftInvariant.toList_eq_flatMap_filter_numerators {g : Int → List (Int × Int × Int)}
    {keep : Int → Bool} {H range : Nat} {w0 w1 : Int} {out : Array (Int × Int × Int)}
    (h : SiftInvariant g keep H true range w0 w1 out) :
    out.toList = ((numerators H).filter keep).flatMap g := by
  have hR := natCast_rbaLength_pos
  have hL := Int.mul_ediv_self_le (x := -(H : Int)) (Int.ne_of_gt hR)
  have := Int.lt_mul_ediv_self_add (x := (H : Int)) hR
  have hM : ((((H : Int) / rbaLength + 1 - -(H : Int) / rbaLength).toNat * rbaLength : Nat) :
      Int) = rbaLength * ((H : Int) / rbaLength) + rbaLength -
        rbaLength * (-(H : Int) / rbaLength) := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg (by have := h.le_w0; have := h.eq_of_exit rfl; lia)]
    grind
  rw [h.toList_eq, h.eq_of_exit rfl, filter_map_range_eq_numerators hL (by lia)]

-- The rows of the run, read at the residue `b mod p` of each modulus, are the rows of `b`.
private theorem map_rows_eq_map_row {entries : List SieveEntry} (hp : ∀ e ∈ entries, 0 < e.p)
    (b : Nat) :
    (entries.map fun e ↦ (e.p, e.rows)).map (fun x ↦ (⟨x.1, x.2[b % x.1]!.get⟩ : SieveSpec)) =
      entries.map fun e ↦ ⟨e.p, e.row b⟩ := by
  rw [List.map_map]
  exact List.map_congr_left fun e he ↦ by
    simp only [Function.comp_apply, SieveEntry.get_rows e (Nat.mod_lt b (hp e he)),
      SieveEntry.row_mod]

-- A statement about every list of sieve entries of positive moduli whose rows of `b` are those
-- that the run reads from the rows of `entries` holds for `entries`.
private theorem of_forall_map_rows {entries : List SieveEntry} (hp : ∀ e ∈ entries, 0 < e.p)
    {b : Nat} {P : List SieveEntry → Prop} (h : ∀ es : List SieveEntry, (∀ e ∈ es, 0 < e.p) →
      (entries.map fun e ↦ (e.p, e.rows)).map (fun x ↦ (⟨x.1, x.2[b % x.1]!.get⟩ : SieveSpec)) =
        es.map (fun e ↦ ⟨e.p, e.row b⟩) → P es) : P entries :=
  h entries hp (map_rows_eq_map_row hp b)

theorem _root_.Ratpoints.BruteForce.natAbs_le_of_mem_numerators {H : Nat} {a : Int}
    (h : a ∈ numerators H) : a.natAbs ≤ H := by
  simp only [numerators, List.mem_map, List.mem_range] at h
  lia

/-- At the exit of the loop of `Ratpoints.Sieve.sift`, for the points of
`Ratpoints.Sieve.acceptedPoints` with the thunks of the products and of what the third stage needs
of the entries `es3` of the shape of `Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, with the reciprocals
of their moduli, for a denominator `0 < b < 2 ^ 63` and `H < 2 ^ 63`, and the numerators that pass
the class word and survive the entries of the first two stages: the points that the brute-force
reference finds over the numerators `-H, …, H` that pass the class word and survive the entries of
all three stages, mapped by `Ratpoints.Sieve.swapPoint` when the flag `rev` of the reversal is set
(`Ratpoints.Sieve.acceptedPoints_eq_ite`, `Ratpoints.Sieve.flatMap_checkNum`,
`Ratpoints.Sieve.pointsOfDen_eq_flatMap_checkNum`). -/
theorem SiftInvariant.toList_eq_pointsOfDen {c : List Int} {d b : Nat} {rev : Bool} {cw : UInt64}
    {entries es3 : List SieveEntry} (hes : ∀ e ∈ es3, e.IsPrimeEntry) {H range : Nat}
    {w0 w1 : Int} {out : Array (Int × Int × Int)} (hb : 0 < b) (hb63 : b < 2 ^ 63)
    (hH : H < 2 ^ 63)
    (h : SiftInvariant (acceptedPoints (.mk fun _ ↦ scaledCoeffs c d b) d b rev
      (.mk fun _ ↦ fillChecks b H es3 (es3.map fun e ↦ magic e.p)))
        (fun a ↦ classBit cw a && survives entries b a) H true range w0 w1 out) :
    out.toList = (pointsOfDen c d b ((numerators H).filter fun a ↦
      classBit cw a && survives (entries ++ es3) b a)).map (if rev then swapPoint else id) := by
  rw [h.toList_eq_flatMap_filter_numerators, pointsOfDen_eq_flatMap_checkNum, ← flatMap_checkNum,
    List.flatMap, List.map_congr_left fun a ha ↦ acceptedPoints_eq_ite hes rfl _ _ rev hb hb63
      (natAbs_le_of_mem_numerators (List.mem_filter.mp ha).1) hH, ← List.flatMap,
    ← List.flatMap_filter, List.filter_filter]
  simp only [survives_append, Bool.and_comm (survives es3 b _), Bool.and_assoc]
  rfl

-- The contract of `Ratpoints.Sieve.sift` for the rows of the sieve entries `entries`.
open Std.WP Lean.Order in
private theorem sift_spec_map (c : List Int) (d H b : Nat) (rev : Bool) (sp1 : Nat)
    (es3 : List SieveEntry) (cw : UInt64) {A : Nat} {entries : List SieveEntry} (hA : 1 ≤ A)
    (hb : 0 < b) (hb63 : b < 2 ^ 63) (hH : H < 2 ^ 63) (hp : ∀ e ∈ entries, 0 < e.p)
    (hes : ∀ e ∈ es3, e.IsPrimeEntry) :
    ⦃ True ⦄
    sift c d H A b rev sp1 (entries.map fun e ↦ (e.p, e.rows)) es3 (es3.map fun e ↦ magic e.p) cw
    ⦃ fun out ↦ out.toList = (pointsOfDen c d b ((numerators H).filter fun a ↦
        classBit cw a && survives (entries ++ es3) b a)).map (if rev then swapPoint else id) ⦄ := by
  vcgen [sift] invariants
  · SiftWhileInvariant (acceptedPoints (.mk fun _ ↦ scaledCoeffs c d b) d b rev
      (.mk fun _ ↦ fillChecks b H es3 (es3.map fun e ↦ magic e.p)))
      (fun a ↦ classBit cw a && survives entries b a) H
  · .ofMeasure fun s ↦ ((H : Int) / rbaLength + 1 - s.2.1).toNat
  all_goals simp only [SiftWhileInvariant, WhileInvariant.mk_apply, Variant.evalsTo_ofMeasure,
    Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure, meet_prop_eq_and,
    ofProp_prop_eq, ite_true] at *
  all_goals first
    | exact siftInvariant_empty _ _ _ hA
    | exact ‹SiftInvariant _ _ _ true _ _ _ _›.toList_eq_pointsOfDen hes hb hb63 hH
    | exact ‹_ ∧ SiftInvariant _ _ _ false _ _ _ _›.2.exit_of_not_lt ‹_›
    | (have := rbaLength_pos; (try split) <;> lia)
    | obtain ⟨rfl, h⟩ := ‹_ ∧ SiftInvariant _ _ _ false _ _ _ _›
      first
        | exact ⟨h.toNat_sub_lt ‹_›, h.append h.w1_eq h.one_le_range (by lia)
            (ite_eq_toNat_mul_sub (by lia)) (of_forall_map_rows hp ‹_›)⟩
        | exact ⟨by lia, h.append (by lia) (by lia) (Int.le_refl _)
            (sub_toNat_emod_eq_toNat_mul_sub H) (of_forall_map_rows hp ‹_›)⟩

/-- The sieve entries of the first two stages are quantified in the postcondition, since the program
does not mention them; the loop over the pieces ends by the measure `H / rbaLength + 1 - w0`, since
every piece has at least one bit array; the test for common factors on the words of the C code needs
`0 < b < 2 ^ 63` and the numerators `|a| ≤ H < 2 ^ 63` (`Ratpoints.Sieve.accepted_spec`), and the
third stage entries of the shape of `Ratpoints.Sieve.SieveEntry.IsPrimeEntry` with the reciprocals
of their moduli. -/
@[spec]
theorem sift_spec (c : List Int) (d H A b : Nat) (rev : Bool) (sp1 : Nat)
    (rows : List (Nat × Array (Thunk (Array UInt64)))) (es3 : List SieveEntry) (mgs3 : List Nat)
    (cw : UInt64) :
    ⦃ 1 ≤ A ∧ 0 < b ∧ b < 2 ^ 63 ∧ H < 2 ^ 63 ∧ (∀ e ∈ es3, e.IsPrimeEntry) ∧
        mgs3 = es3.map fun e ↦ magic e.p ⦄
    sift c d H A b rev sp1 rows es3 mgs3 cw
    ⦃ fun out ↦ ∀ entries : List SieveEntry, (∀ e ∈ entries, 0 < e.p) →
        rows = entries.map (fun e ↦ (e.p, e.rows)) →
        out.toList = (pointsOfDen c d b ((numerators H).filter fun a ↦
          classBit cw a && survives (entries ++ es3) b a)).map (if rev then swapPoint else id) ⦄ :=
  ⟨fun ⟨hA, hb, hb63, hH, hes, hmg⟩ entries hp hrows ↦ by
    subst hrows hmg
    exact (sift_spec_map c d H b rev sp1 es3 cw hA hb hb63 hH hp hes).le_wp trivial⟩

/-- `Ratpoints.Sieve.sift` with the flag `rev` of the reversal, the class word `cw`, the entries
`entries` of the first two stages and the entries `es3` of the third, of the shape of
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, with the reciprocals of their moduli, for a denominator
`0 < b < 2 ^ 63` and `H < 2 ^ 63`, gives the points of the plain sieve with all these entries and
its check, the reference of the words, whose numerators pass `cw`
(`Ratpoints.Sieve.classBit`), mapped by `Ratpoints.Sieve.swapPoint` when `rev` is set: the plain
sieve and its check give what the brute-force reference finds over `b` and the numerators `-H, …, H`
that survive the sieve entries (`Ratpoints.Sieve.sieveDen_spec`, `Ratpoints.Sieve.checkDen_spec`),
and `Ratpoints.Sieve.sift` gives those of these points whose numerators pass `cw`, mapped
(`Ratpoints.Sieve.sift_spec`, `Ratpoints.BruteForce.pointsOfDen_filter`).
-/
theorem toList_run_sift_eq_checkDen (c : List Int) (d H b : Nat) (rev : Bool) (sp1 : Nat)
    (cw : UInt64) {A : Nat} (hA : 1 ≤ A) (hb : 0 < b) (hb63 : b < 2 ^ 63) (hH : H < 2 ^ 63)
    {entries es3 : List SieveEntry} (hp : ∀ e ∈ entries, 0 < e.p)
    (hes : ∀ e ∈ es3, e.IsPrimeEntry) :
    (Id.run (sift c d H A b rev sp1 (entries.map fun e ↦ (e.p, e.rows)) es3
      (es3.map fun e ↦ magic e.p) cw)).toList =
      ((Id.run (checkDen c d H b (Id.run (sieveDen H b (entries ++ es3))))).toList.filter
        fun q ↦ classBit cw q.1).map (if rev then swapPoint else id) :=
  ((sift_spec_map c d H b rev sp1 es3 cw hA hb hb63 hH hp hes).le_wp trivial).trans <| by
    rw [← List.filter_filter, pointsOfDen_filter, ← (checkDen_spec c d H b _).le_wp trivial _
      ((sieveDen_spec H b (entries ++ es3)).le_wp trivial)]
    rfl

end Sieve

end Ratpoints

end
