/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Scan

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers
import Std.Tactic.Do

/-!
# The counters of the scan of a piece

The counts that the components of the model on words from the walk through the set bits of a word
on, through the second stage and the extraction of one bit array, up to the scan of a piece, add to
the counters of the sieving thread (`Ratpoints.Sieve.Counters`), as contracts proved with `vcgen`,
the program logic of Lean core, with loop invariants that are named definitions. When the callback
does not stop the search, each component adds closed forms that depend neither on the callback nor
on the delivery: the counts of the tests of a candidate (`Ratpoints.Sieve.testedCounts`) of the
numerators that the contracts of `Ratpoints.Proof.Scan` deliver the points of, and, for the scan of
a piece, the number of its bit arrays that are not zero; so the counters, from which the search of
ratpoints corrects its moduli between the blocks, do not depend on the callback, the flags of the
output or the store of the tables of rows.

## Main definitions

* `Ratpoints.Sieve.WalkCountsInvariant`, `Ratpoints.Sieve.SiftBitArrayCounts`,
  `Ratpoints.Sieve.ScanPieceCounts`: the counters of the walk through a word, of the loops of the
  extraction of one bit array and of the scan of a piece.

## Main statements

* `Ratpoints.Sieve.walkWord_counters_spec`: the walk through the set bits of a word adds the counts
  of the tests of the numerators of its set bits.
* `Ratpoints.Sieve.siftBitArrayByWords_counters_spec`,
  `Ratpoints.Sieve.siftBitArrayWhole_counters_spec`, `Ratpoints.Sieve.siftBitArray_counters_spec`:
  in either arm of the second stage, one bit array adds the counts of the tests of the numerators
  of the set bits of its words and-ed with the rows of the moduli of the second stage.
* `Ratpoints.Sieve.scanPiece_counters_spec`: if the bits of a piece and-ed with the rows of the
  second stage are a test `keep` of the bits, the scan of the piece adds the number of its bit
  arrays that are not zero and the counts of the tests of the numerators of its bits that pass
  `keep`.
* `Ratpoints.Sieve.isZeroAt_eq_not_any`: a bit array whose bits are a test of the bits is zero
  exactly when none of its bits passes the test.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Scan` does. The contracts of the
counters are apart from those of the delivery, which `vcgen` uses for the calls of the components:
the proofs of the counters name the contracts of the counters of the components they call. Their
loop invariants hold the counters before a return, which comes only at a stop; the counts of the
tests of a candidate are irreducible, so that the verification conditions are closed by the lemmas
of their lists. The contracts of the counters of the pieces, of the bits of one interval and of the
sieve of one denominator are in `Ratpoints.Proof.SiftBits` and `Ratpoints.Proof.Sift`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

variable {σ : Type} (process : Int → Int → Int → σ → Answer σ)

/- The invariants of the delivery are irreducible here: the verification conditions of the
counters are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] WalkWhileInvariant ScanPieceSentinelInvariant

/-! ### The counters of the walk -/

/- The counts of the tests of a candidate are irreducible from here on: the verification conditions
of the counters are closed by the lemmas of their lists, never by computing the counts. -/
attribute [local irreducible] testedCounts

/-- The property of the counters `c` of a walk through the set bits of the word `x0`, lowest first,
bit `t` standing for the numerator `a0 + step t`, from the counters `cnt0`, after the set bits below
`k`: they are `cnt0` plus the counts of the tests of a candidate of the numerators of the set bits
`t < k` of `x0`, over the denominator `b` with the thunk `checks` of the third stage
(`Ratpoints.Sieve.testedCounts`). -/
def WalkCountsInvariant (b : Nat) (checks : Thunk (List CheckSpec)) (x0 : UInt64) (a0 : Int)
    (step : Nat) (cnt0 : Counters) (k : Nat) (c : Counters) : Prop :=
  c = cnt0 + testedCounts b checks
    (((List.range k).filter (x0.toBitVec.getLsbD ·)).map fun t : Nat ↦ a0 + step * t)

/-- The invariant of the `while` loop of `Ratpoints.Sieve.walkWord` for its counters, whose state is
the value of a return, the word, the delivery and the counters: before a return,
`Ratpoints.Sieve.WalkWhileInvariant` for `Ratpoints.Sieve.WalkCountsInvariant`; the return comes at
a stop, with the flag of the delivery returned set. -/
def WalkCountsWhileInvariant {σ : Type} (b : Nat) (checks : Thunk (List CheckSpec)) (x0 : UInt64)
    (a0 : Int) (step : Nat) (cnt0 : Counters) :
    Std.WP.WhileInvariant (Option (Delivery σ × Counters) × UInt64 × Delivery σ × Counters) Prop :=
  .mk fun exit s ↦ s.1 = none ∧
    WalkWhileInvariant x0 (WalkCountsInvariant b checks x0 a0 step cnt0) exit (s.2.2.2, s.2.1) ∨
      exit = true ∧ s.1.map (·.1.quit) = some true

section

variable {b : Nat} {checks : Thunk (List CheckSpec)} {x0 x : UInt64} {a0 : Int} {step : Nat}
  {cnt0 c c' : Counters} {o : Option (Delivery σ × Counters)} {mb : Nat}

theorem walkCountsInvariant_zero (b : Nat) (checks : Thunk (List CheckSpec)) (x0 : UInt64)
    (a0 : Int) (step : Nat) (cnt0 : Counters) :
    WalkWhileInvariant x0 (WalkCountsInvariant b checks x0 a0 step cnt0) false (cnt0, x0) :=
  walkWhileInvariant_self (by simp [WalkCountsInvariant])

/-- A step of the walk, at the lowest set bit of `x`, whose numerator the test of a candidate counts
after the count in `bits`. -/
theorem WalkCountsInvariant.and_sub_one {ok : Bool}
    (h : x.toNat = mb ∧ o = none ∧
      WalkWhileInvariant x0 (WalkCountsInvariant b checks x0 a0 step cnt0) false (c, x))
    (hx : (x != 0) = true)
    (hc : (ok, c') = Id.run (accepted (a0 + step * x.toBitVec.ctz.toNat) b checks
      { c with bits := c.bits + 1 })) :
    (x &&& x - 1).toNat < mb ∧
      WalkWhileInvariant x0 (WalkCountsInvariant b checks x0 a0 step cnt0) false
        (c', x &&& x - 1) :=
  WalkWhileInvariant.and_sub_one ⟨h.1, h.2.2⟩ hx fun _ hk hP ↦ by
    rw [WalkCountsInvariant, eq_add_testedCounts_of_eq_run_accepted hc, hP, Counters.add_assoc,
      hk.filter_range_succ_ctz (bne_iff_ne.mp hx), List.map_append, testedCounts_append]
    rfl

theorem WalkCountsInvariant.exit (hx : ¬(x != 0) = true)
    (h : x.toNat = mb ∧ o = none ∧
      WalkWhileInvariant x0 (WalkCountsInvariant b checks x0 a0 step cnt0) false (c, x)) :
    WalkWhileInvariant x0 (WalkCountsInvariant b checks x0 a0 step cnt0) true (c, x) :=
  WalkWhileInvariant.exit hx ⟨h.1, h.2.2⟩

/-- At the exit of the walk, the counters are those of the tests of the numerators of all the set
bits of `x0`. -/
theorem WalkCountsInvariant.eq_of_exit
    (h : WalkWhileInvariant x0 (WalkCountsInvariant b checks x0 a0 step cnt0) true (c, x)) :
    c = cnt0 + testedCounts b checks
      (((List.range 64).filter (x0.toBitVec.getLsbD ·)).map fun t : Nat ↦ a0 + step * t) := by
  obtain ⟨k, hcl, hk⟩ := h.exists_clearedBelow_zero
  rw [hk, hcl.filter_range_of_eq_zero]

end

/- The invariants of the counters of the walk are irreducible from here on. -/
attribute [local irreducible] WalkCountsInvariant

open Std.WP Lean.Order in
/-- When the callback does not stop the search, the walk through the set bits of a word adds to the
counters the counts of the tests of a candidate of the numerators `a0 + step t` of its set bits `t`
(`Ratpoints.Sieve.testedCounts`); the test of a candidate is read as its value. -/
theorem walkWord_counters_spec (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (checks : Thunk (List CheckSpec)) (x : UInt64) (a0 : Int) (step : Nat) (r : Delivery σ)
    (cnt : Counters) :
    ⦃ True ⦄ walkWord process w d b fl checks x a0 step r cnt
    ⦃ fun r' ↦ r'.1.quit = false → r'.2 = cnt + testedCounts b checks
        (((List.range 64).filter (x.toBitVec.getLsbD ·)).map fun t : Nat ↦ a0 + step * t) ⦄ := by
  vcgen [walkWord, accepted_value] invariants
  · WalkCountsWhileInvariant (σ := σ) b checks x a0 step cnt
  · Variant.ofMeasure fun s : Option (Delivery σ × Counters) × UInt64 × Delivery σ × Counters ↦
      s.2.1.toNat
  all_goals subst_vars
  all_goals simp only [WalkCountsWhileInvariant, WhileInvariant.mk_apply,
    Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure,
    meet_prop_eq_and, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    Option.some.injEq, Option.map_some, Option.map_none] at *
  all_goals first
    | exact walkCountsInvariant_zero _ _ _ _ _ _
    | exact bne_iff_ne.mp ‹_›
    | exact WalkCountsInvariant.exit ‹_› ‹_›
    | exact WalkCountsInvariant.and_sub_one ‹_› ‹_› ‹_›
    | exact WalkCountsInvariant.eq_of_exit ‹_›
    | assumption
    | (simp_all; done)

/-! ### The counters of one bit array -/

/-- The property of the counters `c` of the loops of the two arms of `Ratpoints.Sieve.siftBitArray`
over the words `words κ` of the bit array with the word number `i`, in the packing of the class
`cl`, from the counters `cnt0`, after its first `k` words: they are `cnt0` plus the counts of the
tests of a candidate (`Ratpoints.Sieve.testedCounts`) of the numerators of the bit numbers
`rbaLength i + 64 κ + t` of the set bits `t` of the words `κ < k` (`Ratpoints.Sieve.bitNumbers`),
over the denominator `b` with the thunk `checks` of the third stage. -/
def SiftBitArrayCounts (words : Nat → UInt64) (b : Nat) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (cnt0 : Counters) (k : Nat) (c : Counters) : Prop :=
  c = cnt0 + testedCounts b checks ((bitNumbers words (rbaLength * i) k).map cl.numerator)

/-- The invariant of the loop of `Ratpoints.Sieve.siftBitArrayByWords` over `[0:rbaPack]` for its
counters, whose state is the value of a return, the delivery and the counters:
`Ratpoints.Sieve.SiftBitArrayCounts` after the words done before a return; the return comes at a
stop. -/
def SiftBitArrayCountsLoopInvariant (words : Nat → UInt64) (b : Nat)
    (checks : Thunk (List CheckSpec)) (cl : NumClass) (i : Int) (cnt0 : Counters) :
    Std.WP.Invariant Nat (Option (Delivery σ × Counters) × Delivery σ × Counters) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun done _ s ↦ SiftBitArrayCounts words b checks cl i cnt0 done.length s.2)
    (fun ret _ ↦ ret.1.quit = true)

/-- `Ratpoints.Sieve.flatMap_numerator_bitNumbers_succ` for the numerators themselves: the
numerators of the bit numbers of the set bits of the words `0, …, k` are those of the words
`0, …, k - 1` followed by those of word `k`, as the walk through it computes them. -/
theorem map_numerator_bitNumbers_succ (words : Nat → UInt64) (cl : NumClass) (i : Int) (k : Nat) :
    (bitNumbers words (rbaLength * i) (k + 1)).map cl.numerator =
      (bitNumbers words (rbaLength * i) k).map cl.numerator ++
        ((List.range 64).filter ((words k).toBitVec.getLsbD ·)).map fun t : Nat ↦
          cl.a0 + i * (rbaLength * 2 ^ cl.k) + k * (64 * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t := by
  simpa [← List.map_eq_flatMap] using flatMap_numerator_bitNumbers_succ words (fun a ↦ [a]) cl i k

section

variable {words : Nat → UInt64} {b : Nat} {checks : Thunk (List CheckSpec)} {cl : NumClass}
  {i : Int} {cnt0 c c' : Counters} {o : Option (Delivery σ × Counters)}

theorem siftBitArrayCounts_zero (words : Nat → UInt64) (b : Nat) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (cnt0 : Counters) :
    SiftBitArrayCounts words b checks cl i cnt0 0 cnt0 := by
  simp [SiftBitArrayCounts]

/-- The walk through word `k` from its first numerator adds the counts of its numerators. -/
theorem SiftBitArrayCounts.succ {k : Nat} (h : SiftBitArrayCounts words b checks cl i cnt0 k c)
    (hc : c' = c + testedCounts b checks (((List.range 64).filter
      ((words k).toBitVec.getLsbD ·)).map fun t : Nat ↦
        cl.a0 + i * (rbaLength * 2 ^ cl.k) + k * (64 * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t)) :
    SiftBitArrayCounts words b checks cl i cnt0 (k + 1) c' := by
  rw [SiftBitArrayCounts, map_numerator_bitNumbers_succ, testedCounts_append,
    ← Counters.add_assoc, hc, h]

/-- The walk through word `cur` of the loop over `[0:rbaPack]`, when the callback does not stop the
search in it, in the shape of the verification condition. -/
theorem SiftBitArrayCounts.append {done suff : List Nat} {cur : Nat} {r : Delivery σ}
    (h : o = none ∧ SiftBitArrayCounts words b checks cl i cnt0 done.length c)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff) (hq : ¬r.quit = true)
    (hc : r.quit = false → c' = c + testedCounts b checks (((List.range 64).filter
      ((words cur).toBitVec.getLsbD ·)).map fun t : Nat ↦
        cl.a0 + i * (rbaLength * 2 ^ cl.k) + cur * (64 * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t)) :
    SiftBitArrayCounts words b checks cl i cnt0 (done ++ [cur]).length c' := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton]
  exact h.2.succ (hc (Bool.eq_false_iff.mpr hq))

/-- A word that is zero adds nothing. -/
theorem SiftBitArrayCounts.append_of_eq_zero {done suff : List Nat} {cur : Nat}
    (h : o = none ∧ SiftBitArrayCounts words b checks cl i cnt0 done.length c)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff) (hz : words cur = 0) :
    SiftBitArrayCounts words b checks cl i cnt0 (done ++ [cur]).length c := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton]
  exact h.2.succ (by
    simp [hz, List.filter_eq_nil_iff.mpr fun (_ : Nat) _ ↦ Bool.false_ne_true])

/-- The counters of the numerators of the set bits of words that agree. -/
theorem SiftBitArrayCounts.congr {words' : Nat → UInt64} {k : Nat}
    (hw : ∀ κ < k, words κ = words' κ) (h : SiftBitArrayCounts words b checks cl i cnt0 k c) :
    SiftBitArrayCounts words' b checks cl i cnt0 k c := by
  rw [SiftBitArrayCounts, h, bitNumbers_congr hw]

/-- After all the words of the bit array, the counters are those of their numerators. -/
theorem SiftBitArrayCounts.eq_of_rbaPack {words' : Nat → UInt64}
    (hw : ∀ κ < rbaPack, words κ = words' κ)
    (h : SiftBitArrayCounts words b checks cl i cnt0 rbaPack c) :
    c = cnt0 + testedCounts b checks
      ((bitNumbers words' (rbaLength * i) rbaPack).map cl.numerator) :=
  h.congr hw

/-- At the end of the loop over `[0:rbaPack]`, the counters are those of the numerators of all the
words of the bit array. -/
theorem SiftBitArrayCounts.eq
    (h : SiftBitArrayCounts words b checks cl i cnt0 (ForIn.toList [0:rbaPack]).length c) :
    c = cnt0 + testedCounts b checks
      ((bitNumbers words (rbaLength * i) rbaPack).map cl.numerator) := by
  simp only [Std.Legacy.Range.length_toList, Nat.sub_zero] at h
  exact h

end

/- The counters of the loops over the words of a bit array are irreducible from here on. -/
attribute [local irreducible] SiftBitArrayCounts

open Std.WP Lean.Order in
/-- When the callback does not stop the search, the arm for one word at a time adds to the counters
the counts of the tests of a candidate of the numerators of the set bits of the words of `nums`
and-ed with the rows of the moduli of `specs`. -/
theorem siftBitArrayByWords_counters_spec (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (nums : Vector UInt64 rbaPack) (r : Delivery σ) (cnt : Counters) :
    ⦃ StageFits specs mgs small i (i + 1) ⦄
    siftBitArrayByWords process w d b fl specs mgs small checks cl i nums r cnt
    ⦃ fun r' ↦ r'.1.quit = false → r'.2 = cnt + testedCounts b checks
        ((bitNumbers (fun κ ↦ andWords specs nums[κ]! i κ) (rbaLength * i) rbaPack).map
          cl.numerator) ⦄ := by
  vcgen [siftBitArrayByWords, walkWord_counters_spec] invariants
  | inv1 => SiftBitArrayCountsLoopInvariant (σ := σ) (fun κ ↦ andWords specs nums[κ]! i κ) b
      checks cl i cnt
  all_goals subst_vars
  all_goals simp only [SiftBitArrayCountsLoopInvariant, meet_prop_eq_and, join_prop_eq_or,
    iSup_prop_eq_exists, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, exists_eq_left', exists_false, and_true] at *
  all_goals first
    | exact siftBitArrayCounts_zero _ _ _ _ _ _
    | exact SiftBitArrayCounts.eq ‹_›
    | exact Std.Legacy.Range.lt_of_toList_eq_append_cons ‹_›
    | exact SiftBitArrayCounts.append ‹_› ‹_› ‹_› ‹_›
    | exact SiftBitArrayCounts.append_of_eq_zero ‹_› ‹_› (by simp_all)
    | assumption
    | (simp_all; done)

/-- `Ratpoints.Sieve.SiftBitArrayCounts` after the words `0, …, k`, with the numerator `a0` of bit
`0` of word `k`, `a₀ + i (rbaLength 2 ^ cl.k) + k (64 2 ^ cl.k)` as the program computes it: the
invariant of the counters of the loop over the words after the first in
`Ratpoints.Sieve.siftBitArrayWhole`. -/
def SiftBitArrayWalkCounts (words : Nat → UInt64) (b : Nat) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (cnt0 : Counters) (k : Nat) (s : Counters × Int) : Prop :=
  s.2 = cl.a0 + i * (rbaLength * 2 ^ cl.k) + k * (64 * 2 ^ cl.k) ∧
    SiftBitArrayCounts words b checks cl i cnt0 (k + 1) s.1

/-- The invariant of the loop of `Ratpoints.Sieve.siftBitArrayWhole` over `[1:rbaPack]` for its
counters, whose state is the value of a return, the delivery, the counters and the numerator of bit
`0` of the word: `Ratpoints.Sieve.SiftBitArrayWalkCounts` after the words done before a return; the
return comes at a stop. -/
def SiftBitArrayWalkCountsLoopInvariant (words : Nat → UInt64) (b : Nat)
    (checks : Thunk (List CheckSpec)) (cl : NumClass) (i : Int) (cnt0 : Counters) :
    Std.WP.Invariant Nat (Option (Delivery σ × Counters) × Delivery σ × Counters × Int) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun done _ s ↦ SiftBitArrayWalkCounts words b checks cl i cnt0 done.length s.2)
    (fun ret _ ↦ ret.1.quit = true)

section

variable {words : Nat → UInt64} {b : Nat} {checks : Thunk (List CheckSpec)} {cl : NumClass}
  {i : Int} {cnt0 c c' : Counters} {o : Option (Delivery σ × Counters)}

/-- The walk through the first word, from the first numerator `a₀ + i (rbaLength 2 ^ cl.k)` of the
bit array, when the callback does not stop the search in it, starts the invariant of the counters
of the loop over the other words. -/
theorem siftBitArrayWalkCounts_zero {r : Delivery σ} (hq : ¬r.quit = true)
    (hc : r.quit = false → c = cnt0 + testedCounts b checks (((List.range 64).filter
      ((words 0).toBitVec.getLsbD ·)).map fun t : Nat ↦
        cl.a0 + i * (rbaLength * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t)) :
    SiftBitArrayWalkCounts words b checks cl i cnt0 ([] : List Nat).length
      (c, cl.a0 + i * (rbaLength * 2 ^ cl.k)) :=
  ⟨by simp, (siftBitArrayCounts_zero words b checks cl i cnt0).succ (by
    simpa using hc (Bool.eq_false_iff.mpr hq))⟩

/-- The step `64 2 ^ cl.k` to the first numerator of word `cur` of the loop over `[1:rbaPack]`, and
the walk through it from there, when the callback does not stop the search in it. -/
theorem SiftBitArrayWalkCounts.append {done suff : List Nat} {cur : Nat} {a : Int}
    {r : Delivery σ}
    (h' : o = none ∧ SiftBitArrayWalkCounts words b checks cl i cnt0 done.length (c, a))
    (hl : ForIn.toList [1:rbaPack] = done ++ cur :: suff)
    (hc : r.quit = false → c' = c + testedCounts b checks (((List.range 64).filter
      ((words cur).toBitVec.getLsbD ·)).map fun t : Nat ↦
        a + (64 * 2 ^ cl.k : Nat) + (2 ^ cl.k : Nat) * t))
    (hq : ¬r.quit = true) :
    SiftBitArrayWalkCounts words b checks cl i cnt0 (done ++ [cur]).length
      (c', a + (64 * 2 ^ cl.k : Nat)) := by
  obtain ⟨-, h⟩ := h'
  obtain rfl : cur = done.length + 1 := by
    lia [Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl]
  rw [add_eq_numerator_succ h.1] at hc ⊢
  rw [List.length_append, List.length_singleton]
  exact ⟨rfl, h.2.succ (hc (Bool.eq_false_iff.mpr hq))⟩

/-- At the end of the loop over `[1:rbaPack]`, the counters are those of the numerators of all the
words of the bit array. -/
theorem SiftBitArrayWalkCounts.eq {a : Int} {words' : Nat → UInt64}
    (hw : ∀ κ < rbaPack, words κ = words' κ)
    (h : SiftBitArrayWalkCounts words b checks cl i cnt0 (ForIn.toList [1:rbaPack]).length (c, a)) :
    c = cnt0 + testedCounts b checks
      ((bitNumbers words' (rbaLength * i) rbaPack).map cl.numerator) := by
  have hl : (ForIn.toList [1:rbaPack]).length + 1 = rbaPack := by
    simp only [Std.Legacy.Range.length_toList]
    lia [rbaPack_pos]
  exact (hl ▸ h.2).eq_of_rbaPack hw

/-- When the second stage leaves the bit array zero, the words walked through have no set bits, and
nothing is counted. -/
theorem eq_add_testedCounts_of_isZeroAt {specs : List SieveSpec}
    {nums nums' : Vector UInt64 rbaPack}
    (hw : ∀ κ < rbaPack, nums'[κ]! = andWords specs nums[κ]! i κ)
    (hz : ¬(!isZeroAt nums' 0) = true) (c : Counters) :
    c = c + testedCounts b checks
      ((bitNumbers (fun κ ↦ andWords specs nums[κ]! i κ) (rbaLength * i) rbaPack).map
        cl.numerator) := by
  rw [bitNumbers_eq_nil fun κ hκ ↦ ?_]
  · simp
  have := (isZeroAt_eq_true_iff nums' 0).mp (by simpa using hz) κ hκ
  simp_all

end

/- The counters of the loop over the words after the first are irreducible from here on. -/
attribute [local irreducible] SiftBitArrayWalkCounts

open Std.WP Lean.Order in
/-- When the callback does not stop the search, the arm of the second stage on the whole bit array
adds to the counters the counts of the tests of a candidate of the numerators of the set bits of the
words of `nums` and-ed with the rows of the moduli of `specs`, nothing when the second stage leaves
the bit array zero. -/
theorem siftBitArrayWhole_counters_spec (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (nums : Vector UInt64 rbaPack) (r0 : Delivery σ) (cnt0 : Counters) :
    ⦃ StageFits specs mgs small i (i + 1) ⦄
    siftBitArrayWhole process w d b fl specs mgs small checks cl i nums r0 cnt0
    ⦃ fun r' ↦ r'.1.quit = false → r'.2 = cnt0 + testedCounts b checks
        ((bitNumbers (fun κ ↦ andWords specs nums[κ]! i κ) (rbaLength * i) rbaPack).map
          cl.numerator) ⦄ := by
  vcgen [siftBitArrayWhole, walkWord_counters_spec] invariants
  | inv1 => SiftBitArrayWalkCountsLoopInvariant (σ := σ) (fun κ ↦ nums[κ]!) b checks cl i cnt0
  all_goals subst_vars
  all_goals try simp only [SiftBitArrayWalkCountsLoopInvariant, meet_prop_eq_and, join_prop_eq_or,
    iSup_prop_eq_exists, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, exists_eq_left', exists_false, and_true] at *
  all_goals first
    | exact siftBitArrayWalkCounts_zero ‹_› ‹_›
    | exact SiftBitArrayWalkCounts.eq ‹_› ‹_›
    | exact SiftBitArrayWalkCounts.append ‹_› ‹_› ‹_› ‹_›
    | exact eq_add_testedCounts_of_isZeroAt ‹_› ‹_› cnt0
    | assumption
    | (simp_all; done)

/-- Both arms add to the counters the counts of the tests of a candidate of the numerators of the
set bits of the same words, the words of `nums` and-ed with the rows of the moduli of `specs`
(`Ratpoints.Sieve.siftBitArrayByWords_counters_spec`,
`Ratpoints.Sieve.siftBitArrayWhole_counters_spec`), when the callback does not stop the search. -/
theorem siftBitArray_counters_spec (useLong : Bool) (w : Thunk (List Int)) (d b : Nat)
    (fl : CheckFlags) (specs : List SieveSpec) (mgs : List Nat) (small : Bool)
    (checks : Thunk (List CheckSpec)) (cl : NumClass) (i : Int) (nums : Vector UInt64 rbaPack)
    (r : Delivery σ) (cnt : Counters) :
    ⦃ StageFits specs mgs small i (i + 1) ⦄
    siftBitArray process useLong w d b fl specs mgs small checks cl i nums r cnt
    ⦃ fun r' ↦ r'.1.quit = false → r'.2 = cnt + testedCounts b checks
        ((bitNumbers (fun κ ↦ andWords specs nums[κ]! i κ) (rbaLength * i) rbaPack).map
          cl.numerator) ⦄ := by
  cases useLong
  · exact siftBitArrayWhole_counters_spec process w d b fl specs mgs small checks cl i nums r cnt
  · exact siftBitArrayByWords_counters_spec process w d b fl specs mgs small checks cl i nums r cnt

/-! ### The counters of the scan of a piece -/

/-- The property of the counters `c` of the scan of `Ratpoints.Sieve.scanPiece` at bit array `pos`
of the words `sv`, for a piece of `n` bit arrays from the word number `w0` on and the moduli `specs`
of the second stage with their rows, from the counters `cnt0`: `pos ≤ n`, and `c` is `cnt0` plus the
number of the bit arrays before `pos` that are not zero, in `arrays`, plus the counts of the tests
of a candidate (`Ratpoints.Sieve.testedCounts`), over the denominator `b` with the thunk `checks` of
the third stage, of the numerators in the packing of the class `cl` of the bits
`rbaLength w0 + 64 y + t` of the set bits `t` of the words `y < rbaPack pos` and-ed with the rows of
`specs` (`Ratpoints.Sieve.andWords`). -/
def ScanPieceCounts {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec) (b : Nat)
    (checks : Thunk (List CheckSpec)) (cl : NumClass) (w0 : Int) (n : Nat) (cnt0 : Counters)
    (pos : Nat) (c : Counters) : Prop :=
  pos ≤ n ∧ c = cnt0 + { arrays := ((List.range pos).countP fun p ↦ !isZeroAt sv p).toUInt64 } +
    testedCounts b checks ((bitNumbers (fun y ↦ andWords specs sv[y]! w0 y) (rbaLength * w0)
      (rbaPack * pos)).map cl.numerator)

/-- `Ratpoints.Sieve.ScanPieceCounts` as the invariant of the counters of the scan of
`Ratpoints.Sieve.scanPiece`, whose state is the value of a return, the position, the delivery and
the counters, with all `n` bit arrays done at the exit; the return comes at a stop. -/
def ScanPieceCountsWhileInvariant {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec)
    (b : Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass) (w0 : Int) (n : Nat)
    (cnt0 : Counters) :
    Std.WP.WhileInvariant (Option (Delivery σ × Counters) × Nat × Delivery σ × Counters) Prop :=
  .mk fun exit s ↦ s.1 = none ∧ ScanPieceCounts sv specs b checks cl w0 n cnt0 s.2.1 s.2.2.2 ∧
    (exit = true → s.2.1 = n) ∨ exit = true ∧ s.1.map (·.1.quit) = some true

/-- The invariant of the counters of the loop of `Ratpoints.Sieve.scanPiece` that steps over the bit
arrays that are zero, from bit array `pos0` on, with the counters `c` of the bit arrays before
`pos0`: the position is at least `pos0`, and `Ratpoints.Sieve.ScanPieceCounts` holds there with
`c`. -/
def ScanPieceCountsZeroInvariant {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec)
    (b : Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass) (w0 : Int) (n : Nat)
    (cnt0 : Counters) (pos0 : Nat) (c : Counters) :
    Std.WP.WhileInvariant Nat Prop :=
  .mk fun exit pos ↦ pos0 ≤ pos ∧ ScanPieceCounts sv specs b checks cl w0 n cnt0 pos c ∧
    (exit = true → isZeroAt sv pos = false)

section

variable {m : Nat} {sv : Vector UInt64 m} {specs : List SieveSpec} {b : Nat}
  {checks : Thunk (List CheckSpec)} {cl : NumClass} {w0 : Int} {n pos pos0 mb : Nat}
  {cnt0 c c' : Counters} {o : Option (Delivery σ × Counters)}

theorem scanPieceCounts_zero (sv : Vector UInt64 m) (specs : List SieveSpec) (b : Nat)
    (checks : Thunk (List CheckSpec)) (cl : NumClass) (w0 : Int) (n : Nat) (cnt0 : Counters) :
    ScanPieceCounts sv specs b checks cl w0 n cnt0 0 cnt0 ∧ (False → 0 = n) :=
  ⟨⟨Nat.zero_le _, by simp⟩, nofun⟩

theorem ScanPieceCounts.le (h : ScanPieceCounts sv specs b checks cl w0 n cnt0 pos c) : pos ≤ n :=
  h.1

/-- A bit array that is zero adds nothing; it is not the sentinel, so that the measure `n - pos` of
the loop that steps over the bit arrays that are zero decreases. -/
theorem ScanPieceCounts.add_one_of_isZeroAt {surv : Vector UInt64 m}
    (h : n - pos = mb ∧ pos0 ≤ pos ∧ ScanPieceCounts sv specs b checks cl w0 n cnt0 pos c ∧
      (False → isZeroAt sv pos = false))
    (hs : ScanPieceSentinelInvariant n surv (ForIn.toList [0:rbaPack]).length sv)
    (hz : isZeroAt sv pos = true) :
    n - (pos + 1) < mb ∧ pos0 ≤ pos + 1 ∧
      ScanPieceCounts sv specs b checks cl w0 n cnt0 (pos + 1) c ∧
        (False → isZeroAt sv (pos + 1) = false) := by
  obtain ⟨rfl, h0, ⟨hle, h⟩, -⟩ := h
  have hlt : pos < n := Nat.lt_of_le_of_ne hle (hs.ne_of_isZeroAt hz)
  refine ⟨by lia, by lia, ⟨hlt, ?_⟩, nofun⟩
  rw [h, bitNumbers_rbaPack_mul_succ, bitNumbers_eq_nil (k := rbaPack) fun κ hκ ↦ ?_]
  · simp [List.range_succ, hz]
  simp [Vector.getElem!_ofFn hκ, (isZeroAt_eq_true_iff sv pos).mp hz κ hκ]

/-- Bit array `pos`, which is not zero, copied and passed through
`Ratpoints.Sieve.siftBitArray` with its word number `w0 + pos` after the count `arrays` one up, when
the callback does not stop the search in it. -/
theorem ScanPieceCounts.add_one_of_siftBitArray {r : Delivery σ} {c0 : Counters}
    (hm : n - pos0 = mb ∧ o = none ∧ ScanPieceCounts sv specs b checks cl w0 n cnt0 pos0 c0 ∧
      (False → pos0 = n))
    (h' : pos0 ≤ pos ∧ ScanPieceCounts sv specs b checks cl w0 n cnt0 pos c ∧
      (True → isZeroAt sv pos = false))
    (hlt : ¬n ≤ pos)
    (hc : r.quit = false → c' = { c with arrays := c.arrays + 1 } + testedCounts b checks
      ((bitNumbers (fun κ ↦ andWords specs
        (Vector.ofFn fun κ : Fin rbaPack ↦ sv[rbaPack * pos + κ]!)[κ]! (w0 + pos) κ)
          (rbaLength * (w0 + pos)) rbaPack).map cl.numerator))
    (hq : ¬r.quit = true) :
    n - (pos + 1) < mb ∧ ScanPieceCounts sv specs b checks cl w0 n cnt0 (pos + 1) c' ∧
      (False → pos + 1 = n) := by
  obtain ⟨h0, ⟨-, h⟩, hz⟩ := h'
  refine ⟨by lia [hm.1], ⟨by lia, ?_⟩, nofun⟩
  have hA : ({ arrays := ((List.range (pos + 1)).countP fun p ↦ !isZeroAt sv p).toUInt64 } :
      Counters) = { arrays := ((List.range pos).countP fun p ↦ !isZeroAt sv p).toUInt64 } +
        { arrays := 1 } := by
    simp [List.range_succ (n := pos), List.countP_append, hz trivial, UInt64.ofNat_add,
      Counters.ext_iff]
  rw [hc (Bool.eq_false_iff.mpr hq), Counters.arrays_add_one, h, bitNumbers_rbaPack_mul_succ,
    List.map_append, testedCounts_append, hA]
  ac_rfl

/-- At the end of the scan, the counters are those of the bit arrays of the piece that are not zero
and of the numerators of the set bits of its words and-ed with the rows, which are those of
`surv`, since the sentinel was written past them. -/
theorem ScanPieceCounts.eq {surv : Vector UInt64 m}
    (h : ScanPieceCounts sv specs b checks cl w0 n cnt0 pos c ∧ (True → pos = n))
    (hs : ScanPieceSentinelInvariant n surv (ForIn.toList [0:rbaPack]).length sv) :
    c = cnt0 + { arrays := ((List.range n).countP fun p ↦ !isZeroAt surv p).toUInt64 } +
      testedCounts b checks ((bitNumbers (fun y ↦ andWords specs surv[y]! w0 y) (rbaLength * w0)
        (n * rbaPack)).map cl.numerator) := by
  have hn := h.2 trivial
  have hc := h.1.2
  rw [hn] at hc
  rw [hc, hs.bitNumbers_eq,
    List.countP_congr fun p hp ↦ by rw [hs.isZeroAt_eq (List.mem_range.mp hp)]]

end

/- The counters of the scan are irreducible from here on. -/
attribute [local irreducible] ScanPieceCounts

-- The contract of the counters of `Ratpoints.Sieve.scanPiece` in terms of the set bits of the words
-- of the piece and-ed with the rows of the second stage.
open Std.WP Lean.Order in
private theorem scanPiece_counters_spec_getLsbD (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (w0 : Int) (n : Nat) (surv : Vector UInt64 ((n + 1) * rbaPack))
    (r : Delivery σ) (cnt0 : Counters) :
    ⦃ StageFits specs mgs small w0 (w0 + n) ⦄
    scanPiece process w d b fl specs mgs small checks cl w0 n surv r cnt0
    ⦃ fun r' ↦ r'.1.quit = false → r'.2 = cnt0 +
        { arrays := ((List.range n).countP fun p ↦ !isZeroAt surv p).toUInt64 } +
        testedCounts b checks ((bitNumbers (fun y ↦ andWords specs surv[y]! w0 y) (rbaLength * w0)
          (n * rbaPack)).map cl.numerator) ⦄ := by
  vcgen [scanPiece, siftBitArray_counters_spec] invariants
  | inv1 => fun done _ ↦ ScanPieceSentinelInvariant n surv done.length
  | inv2 sv _ => ScanPieceCountsWhileInvariant (σ := σ) sv specs b checks cl w0 n cnt0
  | inv3 => Variant.ofMeasure fun s ↦ n - s.2.1
  | inv4 sv _ _ pos0 _ c0 _ _ => ScanPieceCountsZeroInvariant sv specs b checks cl w0 n cnt0 pos0 c0
  | inv5 => Variant.ofMeasure fun s : Nat ↦ n - s
  all_goals (subst_vars; try simp only [ScanPieceCountsWhileInvariant,
    ScanPieceCountsZeroInvariant, WhileInvariant.mk_apply, Variant.evalsTo_ofMeasure,
    Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure, meet_prop_eq_and,
    ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and, and_false,
    Option.some.injEq, Option.map] at *)
  all_goals first
    | exact ScanPieceSentinelInvariant.append_set! ‹_› ‹_›
    | exact ScanPieceCounts.eq ‹_› ‹_›
    | exact StageFits.mono ‹StageFits _ _ _ _ _› (by lia) (by lia)
    | exact ScanPieceCounts.add_one_of_siftBitArray ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact ScanPieceCounts.add_one_of_isZeroAt ‹_› ‹_› ‹_›
    | grind [scanPieceSentinelInvariant_zero, scanPieceCounts_zero, → ScanPieceCounts.le]

/-- The loop over the zero bit arrays ends at the sentinel at latest, so that both loops of the scan
end by the measure `n - pos`; the test `keep` is quantified in the postcondition, since the program
does not mention it. When the callback does not stop the search, the scan adds to the counters the
number of the bit arrays of the piece that are not zero, in `arrays`, and the counts of the tests
of a candidate (`Ratpoints.Sieve.testedCounts`) of the numerators of its bits that pass `keep`, the
bits of the piece and-ed with the rows of the second stage. -/
theorem scanPiece_counters_spec (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (w0 : Int) (n : Nat) (surv : Vector UInt64 ((n + 1) * rbaPack))
    (r : Delivery σ) (cnt : Counters) :
    ⦃ StageFits specs mgs small w0 (w0 + n) ⦄
    scanPiece process w d b fl specs mgs small checks cl w0 n surv r cnt
    ⦃ fun r' ↦ ∀ keep : Int → Bool, (∀ y < n * rbaPack, ∀ t : Nat,
        (andWords specs surv[y]! w0 y).toBitVec.getLsbD t =
          (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t))) →
      r'.1.quit = false → r'.2 = cnt +
        { arrays := ((List.range n).countP fun p ↦ !isZeroAt surv p).toUInt64 } +
        testedCounts b checks ((((List.range (n * rbaLength)).map fun k : Nat ↦
          rbaLength * w0 + k).filter keep).map cl.numerator) ⦄ :=
  ⟨fun pre keep hkeep hq ↦ by
    rw [(scanPiece_counters_spec_getLsbD process w d b fl specs mgs small checks cl w0 n surv r
      cnt).le_wp pre hq, bitNumbers_eq_filter hkeep, rbaLength_eq, Nat.mul_left_comm]⟩

/-- A bit array of the words `v`, among the first `n`, whose bits are a test `keep` of the bits
`rbaLength w0 + 64 y + t` of the set bits `t < 64` of the words `y`, for the number `rbaLength` of
bits of a bit array (`Ratpoints.rbaLength`), is zero exactly when none of its bits passes `keep`. -/
theorem isZeroAt_eq_not_any {m n : Nat} {v : Vector UInt64 m} {w0 : Int} {keep : Int → Bool}
    (hv : ∀ y < n * rbaPack, ∀ t : Nat, v[y]!.toBitVec.getLsbD t =
      (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t)))
    {pos : Nat} (hpos : pos < n) :
    isZeroAt v pos = !(List.range rbaLength).any fun t ↦ keep (rbaLength * (w0 + pos) + t) := by
  have hy (κ : Nat) (hκ : κ < rbaPack) : rbaPack * pos + κ < n * rbaPack :=
    Nat.mul_add_lt_mul_of_lt_of_lt' hpos hκ
  have hj (κ t : Nat) : (rbaLength : Int) * w0 + 64 * (rbaPack * pos + κ : Nat) + t =
      rbaLength * (w0 + pos) + (64 * κ + t : Nat) := by
    rw [rbaLength_eq]
    push_cast
    grind
  rw [Bool.eq_iff_iff, isZeroAt_eq_true_iff, Bool.not_eq_true', List.any_eq_false]
  simp only [List.mem_range]
  refine ⟨fun h t ht hk ↦ ?_, fun h κ hκ ↦ UInt64.eq_of_getLsbD_eq fun s ↦ ?_⟩
  · have hv' := hv _ (hy (t / 64) (by rw [rbaLength_eq] at ht; lia)) (t % 64)
    rw [h _ (by rw [rbaLength_eq] at ht; lia), hj, Nat.div_add_mod] at hv'
    simp [Nat.mod_lt t (by decide : 0 < 64), hk] at hv'
  · rw [hv _ (hy κ hκ) s, hj]
    by_cases hs : s < 64
    · simpa [hs] using h (64 * κ + s) (by rw [rbaLength_eq]; lia)
    · simp [hs]

end Sieve

end Ratpoints

end
