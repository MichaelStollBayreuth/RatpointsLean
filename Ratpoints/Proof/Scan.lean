/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Packing
public import Ratpoints.Proof.Stages

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
import Std.Tactic.Do

/-!
# The contracts of the scan of a piece

The contracts of the components of the model on words from the walk through the set bits of a word
on, through the second stage and the extraction of one bit array, up to the scan of a piece, as
`@[spec]` theorems proved with `vcgen`, the program logic of Lean core, with loop invariants that
are named definitions. Each component hands the points it finds to the callback of the caller on a
delivery (`Ratpoints.Delivery`), whose flag of the stop is clear at the start, and returns as soon
as a call sets it; its contract says that the delivery it returns is the reference of the delivery
(`Ratpoints.Delivery.deliver`) of the list of the points it finds, which passes over the points
after the stop. The contracts speak of the bits `j` of the packing of a class `cl`
(`Ratpoints.Sieve.NumClass`), each standing for the numerator `a₀ + 2 ^ k j`
(`Ratpoints.Sieve.NumClass.numerator`), and of the words of the bit arrays and-ed with the rows of
the moduli of the second stage at their offsets (`Ratpoints.Sieve.andWords`); the points of a
numerator are those that the exact check delivers with the flags of the search
(`Ratpoints.Sieve.acceptedPoints`).

## Main definitions

* `Ratpoints.Sieve.WalkDeliveryInvariant`, `Ratpoints.Sieve.SiftBitArrayInvariant`,
  `Ratpoints.Sieve.ScanPieceInvariant`: the deliveries of the walk through a word, of the loops of
  the extraction of one bit array and of the scan of a piece, before a stop.

## Main statements

* `Ratpoints.Sieve.walkWord_spec`: the walk through the set bits of a word delivers the points of
  the numerators `a0 + step t` of its set bits `t`, in increasing order.
* `Ratpoints.Sieve.siftBitArrayByWords_spec`, `Ratpoints.Sieve.siftBitArrayWhole_spec`,
  `Ratpoints.Sieve.siftBitArray_spec`: in either arm of the second stage, one bit array delivers the
  points of the numerators of the set bits of its words and-ed with the rows of the moduli of the
  second stage, in increasing order.
* `Ratpoints.Sieve.scanPiece_spec`: if the bits of a piece and-ed with the rows of the second stage
  are a test `keep` of the bits, the scan of the piece delivers the points of the numerators of its
  bits that pass `keep`, in increasing order.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Stages`, `Ratpoints.Proof.Packing` and
`Ratpoints.Proof.Delivery` do. The walk reads the test of a candidate as its value
(`Ratpoints.Sieve.acceptedPoints`), so that the contracts need nothing of the numerators and the
denominator. The loops return at a stop: their invariants hold the delivery of the points found so
far with the flag clear before a return, and the value returned after it, the delivery of all the
points, since the reference passes over the points after the first call that sets the flag
(`Ratpoints.Delivery.deliver_eq_of_prefix`); their verification conditions are closed by lemmas in
their shape. The contracts of the counters of these components are in `Ratpoints.Proof.ScanCounts`;
those of the pieces and of the bits of one interval are in `Ratpoints.Proof.SiftBits`, and that of
the sieve of one denominator in `Ratpoints.Proof.Sift`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

variable {σ : Type} (process : Int → Int → Int → σ → Answer σ)

/-! ### The walk through the set bits of a word -/

-- A pair whose first component is not `true` has no first component `true`, in the shape of the
-- verification conditions of a component that returns a Boolean with its counters.
private theorem not_fst_eq_true_of_eq {α : Type} {ok : Bool} {c : α} {p : Bool × α}
    (h : (ok, c) = p) (hok : ¬ok = true) : ¬p.1 = true :=
  h ▸ hok

/-- The property of the delivery `r` of a walk through the set bits of the word `x0`, lowest first,
bit `t` standing for the numerator `a0 + step t`, that delivers the list `g a` of the numerator `a`
of each set bit from the delivery `r0`, after the set bits below `k`: the callback has not stopped
the search, and `r` is the delivery of the lists of the numerators of the set bits `t < k` of `x0`,
in increasing order. In `Ratpoints.Sieve.walkWord`, `g a` is the list of the points that
`Ratpoints.Sieve.acceptedPoints` gives for the numerator `a`. -/
def WalkDeliveryInvariant (g : Int → List (Int × Int × Int)) (x0 : UInt64) (a0 : Int) (step : Nat)
    (r0 : Delivery σ) (k : Nat) (r : Delivery σ) :
    Prop :=
  r.quit = false ∧ r = r0.deliver process ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map
    fun t : Nat ↦ a0 + step * t).flatMap g)

/-- The invariant of the `while` loop of `Ratpoints.Sieve.walkWord`, whose state is the value of a
return, the word and the delivery: before a return, `Ratpoints.Sieve.WalkWhileInvariant` for
`Ratpoints.Sieve.WalkDeliveryInvariant`; after the return at a stop, the value returned is the
delivery of the lists of the numerators of all the set bits of `x0`, since those after the stop are
passed over. -/
def WalkDeliveryWhileInvariant (g : Int → List (Int × Int × Int)) (x0 : UInt64) (a0 : Int)
    (step : Nat) (r0 : Delivery σ) :
    Std.WP.WhileInvariant (Option (Delivery σ × Counters) × UInt64 × Delivery σ × Counters) Prop :=
  .mk fun exit s ↦ s.1 = none ∧
    WalkWhileInvariant x0 (WalkDeliveryInvariant process g x0 a0 step r0) exit (s.2.2.1, s.2.1) ∨
      exit = true ∧ s.1.map Prod.fst = some (r0.deliver process ((((List.range 64).filter
        (x0.toBitVec.getLsbD ·)).map fun t : Nat ↦ a0 + step * t).flatMap g))

section

variable {process} {g : Int → List (Int × Int × Int)} {x0 x : UInt64} {a0 : Int} {step : Nat}
  {r0 r r' : Delivery σ} {o : Option (Delivery σ × Counters)} {mb : Nat}

theorem walkDeliveryInvariant_zero (g : Int → List (Int × Int × Int)) (x0 : UInt64) (a0 : Int)
    (step : Nat) (h : r0.quit = false) :
    WalkDeliveryInvariant process g x0 a0 step r0 0 r0 :=
  ⟨h, by simp⟩

/-- The step of the walk at the lowest set bit of `x`, which has the bits of `x0` below `k`
cleared. -/
theorem WalkDeliveryInvariant.eq_deliver_succ {k : Nat}
    (h : WalkDeliveryInvariant process g x0 a0 step r0 k r) (hx : ClearedBelow x0 k x)
    (hx0 : x ≠ 0)
    (hr' : r.quit = false → r' = r.deliver process (g (a0 + step * x.toBitVec.ctz.toNat))) :
    r' = r0.deliver process ((((List.range (x.toBitVec.ctz.toNat + 1)).filter
      (x0.toBitVec.getLsbD ·)).map fun t : Nat ↦ a0 + step * t).flatMap g) := by
  rw [hr' h.1, h.2, hx.filter_range_succ_ctz hx0, List.map_append, List.flatMap_append,
    List.map_singleton, List.flatMap_singleton, Delivery.deliver_append]

/-- A step of the walk at which the callback does not stop the search. -/
theorem WalkDeliveryInvariant.and_sub_one
    (h : x.toNat = mb ∧ o = none ∧
      WalkWhileInvariant x0 (WalkDeliveryInvariant process g x0 a0 step r0) false (r, x))
    (hx : (x != 0) = true)
    (hr' : r.quit = false → r' = r.deliver process (g (a0 + step * x.toBitVec.ctz.toNat)))
    (hq : r.quit = false → r'.quit = false) :
    (x &&& x - 1).toNat < mb ∧
      WalkWhileInvariant x0 (WalkDeliveryInvariant process g x0 a0 step r0) false
        (r', x &&& x - 1) :=
  WalkWhileInvariant.and_sub_one ⟨h.1, h.2.2⟩ hx fun _ hk hP ↦
    ⟨hq hP.1, hP.eq_deliver_succ hk (bne_iff_ne.mp hx) hr'⟩

/-- The step of the walk at which the callback stops the search: the delivery is that of the lists
of the numerators of all the set bits, since the bits after the stop are passed over. -/
theorem WalkDeliveryInvariant.eq_deliver_of_quit
    (h : x.toNat = mb ∧ o = none ∧
      WalkWhileInvariant x0 (WalkDeliveryInvariant process g x0 a0 step r0) false (r, x))
    (hx : (x != 0) = true)
    (hr' : r.quit = false → r' = r.deliver process (g (a0 + step * x.toBitVec.ctz.toNat)))
    (hq : r'.quit = true) :
    r' = r0.deliver process ((((List.range 64).filter (x0.toBitVec.getLsbD ·)).map
      fun t : Nat ↦ a0 + step * t).flatMap g) := by
  obtain ⟨k, hk, hP, -⟩ := h.2.2
  have hx0 := bne_iff_ne.mp hx
  rw [hP.eq_deliver_succ hk hx0 hr'] at hq ⊢
  refine (Delivery.deliver_flatMap_eq_of_prefix process ((List.IsPrefix.filter _ ?_).map _) g
    hq).symm
  exact List.range_prefix_range (UInt64.toNat_ctz_lt hx0)

/-- The exit of the walk, when the word is `0`. -/
theorem WalkDeliveryInvariant.exit
    (h : x.toNat = mb ∧ o = none ∧
      WalkWhileInvariant x0 (WalkDeliveryInvariant process g x0 a0 step r0) false (r, x))
    (hx : ¬(x != 0) = true) :
    WalkWhileInvariant x0 (WalkDeliveryInvariant process g x0 a0 step r0) true (r, x) :=
  WalkWhileInvariant.exit hx ⟨h.1, h.2.2⟩

/-- At the exit of the walk, the delivery is that of the lists of the numerators of all the set bits
of `x0`. -/
theorem WalkDeliveryInvariant.eq_deliver_of_exit
    (h : WalkWhileInvariant x0 (WalkDeliveryInvariant process g x0 a0 step r0) true (r, x)) :
    r = r0.deliver process ((((List.range 64).filter (x0.toBitVec.getLsbD ·)).map
      fun t : Nat ↦ a0 + step * t).flatMap g) := by
  obtain ⟨k, hcl, hk⟩ := h.exists_clearedBelow_zero
  rw [hk.2, hcl.filter_range_of_eq_zero]

variable {w : Thunk (List Int)} {d b : Nat} {fl : CheckFlags} {checks : Thunk (List CheckSpec)}
  {cnt : Counters}

/-- A step of the walk at a numerator that passes the test of a candidate and whose exact check does
not stop the search. -/
theorem WalkDeliveryInvariant.and_sub_one_of_accepted
    (h : x.toNat = mb ∧ o = none ∧ WalkWhileInvariant x0
      (WalkDeliveryInvariant process (acceptedPoints w d b fl checks) x0 a0 step r0) false (r, x))
    (hx : (x != 0) = true)
    (hq : ¬(checkPoint process w d b fl (a0 + step * x.toBitVec.ctz.toNat) r).quit = true)
    (ha : true = (Id.run (accepted (a0 + step * x.toBitVec.ctz.toNat) b checks cnt)).1) :
    (x &&& x - 1).toNat < mb ∧ WalkWhileInvariant x0
      (WalkDeliveryInvariant process (acceptedPoints w d b fl checks) x0 a0 step r0) false
        (checkPoint process w d b fl (a0 + step * x.toBitVec.ctz.toNat) r, x &&& x - 1) :=
  WalkDeliveryInvariant.and_sub_one h hx
    (checkPoint_eq_deliver_acceptedPoints process w d b fl ha.symm)
    fun _ ↦ Bool.eq_false_iff.mpr hq

/-- A step of the walk at a numerator that does not pass the test of a candidate. -/
theorem WalkDeliveryInvariant.and_sub_one_of_not_accepted
    (h : x.toNat = mb ∧ o = none ∧ WalkWhileInvariant x0
      (WalkDeliveryInvariant process (acceptedPoints w d b fl checks) x0 a0 step r0) false (r, x))
    (hx : (x != 0) = true)
    (ha : ¬(Id.run (accepted (a0 + step * x.toBitVec.ctz.toNat) b checks cnt)).1 = true) :
    (x &&& x - 1).toNat < mb ∧ WalkWhileInvariant x0
      (WalkDeliveryInvariant process (acceptedPoints w d b fl checks) x0 a0 step r0) false
        (r, x &&& x - 1) :=
  WalkDeliveryInvariant.and_sub_one h hx
    (fun _ ↦ (deliver_acceptedPoints_of_not_accepted process w d b fl ha r).symm) id

/-- The step of the walk at a numerator that passes the test of a candidate and whose exact check
stops the search. -/
theorem WalkDeliveryInvariant.eq_deliver_of_accepted_of_quit
    (h : x.toNat = mb ∧ o = none ∧ WalkWhileInvariant x0
      (WalkDeliveryInvariant process (acceptedPoints w d b fl checks) x0 a0 step r0) false (r, x))
    (hx : (x != 0) = true)
    (hq : (checkPoint process w d b fl (a0 + step * x.toBitVec.ctz.toNat) r).quit = true)
    (ha : true = (Id.run (accepted (a0 + step * x.toBitVec.ctz.toNat) b checks cnt)).1) :
    checkPoint process w d b fl (a0 + step * x.toBitVec.ctz.toNat) r =
      r0.deliver process ((((List.range 64).filter (x0.toBitVec.getLsbD ·)).map
        fun t : Nat ↦ a0 + step * t).flatMap (acceptedPoints w d b fl checks)) :=
  WalkDeliveryInvariant.eq_deliver_of_quit h hx
    (checkPoint_eq_deliver_acceptedPoints process w d b fl ha.symm) hq

end

/- The invariants of the walk are irreducible from here on: the verification conditions of
`Ratpoints.Sieve.walkWord` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] WalkWhileInvariant WalkDeliveryInvariant

open Std.WP Lean.Order in
/-- The loop ends, since clearing the lowest set bit makes a word other than `0` smaller, or at a
stop; the test of a candidate is read as its value, `Ratpoints.Sieve.acceptedPoints`. -/
@[spec]
theorem walkWord_spec (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (checks : Thunk (List CheckSpec)) (x : UInt64) (a0 : Int) (step : Nat) (r : Delivery σ)
    (cnt : Counters) :
    ⦃ r.quit = false ⦄ walkWord process w d b fl checks x a0 step r cnt
    ⦃ fun r' ↦ r'.1 = r.deliver process ((((List.range 64).filter (x.toBitVec.getLsbD ·)).map
        fun t : Nat ↦ a0 + step * t).flatMap (acceptedPoints w d b fl checks)) ⦄ := by
  vcgen [walkWord, accepted_value] invariants
  · WalkDeliveryWhileInvariant process (acceptedPoints w d b fl checks) x a0 step r
  · Variant.ofMeasure fun s : Option (Delivery σ × Counters) × UInt64 × Delivery σ × Counters ↦
      s.2.1.toNat
  all_goals subst_vars
  all_goals simp only [WalkDeliveryWhileInvariant, WhileInvariant.mk_apply,
    Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure,
    meet_prop_eq_and, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    Option.some.injEq, Option.map_some, Option.map_none] at *
  all_goals first
    | exact walkWhileInvariant_self (walkDeliveryInvariant_zero _ _ _ _ ‹_›)
    | exact bne_iff_ne.mp ‹_›
    | exact WalkDeliveryInvariant.exit ‹_› ‹_›
    | exact WalkDeliveryInvariant.and_sub_one_of_accepted ‹_› ‹_› ‹_› (congrArg Prod.fst ‹_›)
    | exact WalkDeliveryInvariant.eq_deliver_of_accepted_of_quit ‹_› ‹_› ‹_›
        (congrArg Prod.fst ‹_›)
    | exact WalkDeliveryInvariant.and_sub_one_of_not_accepted ‹_› ‹_›
        (not_fst_eq_true_of_eq ‹_› ‹_›)
    | exact WalkDeliveryInvariant.eq_deliver_of_exit ‹_›
    | exact ‹_›

/-! ### The second stage and the extraction of one bit array -/

/-- The invariant of the loops of the two arms of `Ratpoints.Sieve.siftBitArray` over the words of
the bit array with the word number `i`, after its first `k` words, for the words `words κ` that the
walks go through, the class `cl` and the points `g a` of a numerator `a`, from the delivery `r0`:
the callback has not stopped the search, and `r` is the delivery of the points of the numerators of
the bit numbers `rbaLength i + 64 κ + t` of the set bits `t` of the words `κ < k`
(`Ratpoints.Sieve.bitNumbers`) in the packing of `cl` (`Ratpoints.Sieve.NumClass.numerator`), in
increasing order. The invariant of the scan of a piece (`Ratpoints.Sieve.ScanPieceInvariant`) is
this one for the words of the piece from its first word number on. -/
def SiftBitArrayInvariant (words : Nat → UInt64) (g : Int → List (Int × Int × Int)) (cl : NumClass)
    (i : Int) (r0 : Delivery σ) (k : Nat) (r : Delivery σ) :
    Prop :=
  r.quit = false ∧ r = r0.deliver process
    ((bitNumbers words (rbaLength * i) k).flatMap fun j ↦ g (cl.numerator j))

/-- `Ratpoints.Sieve.SiftBitArrayInvariant` after the words `0, …, k`, with the numerator `a0` of
bit `0` of word `k`, `a₀ + i (rbaLength 2 ^ cl.k) + k (64 2 ^ cl.k)` as the program computes it,
for the stride `2 ^ cl.k` of the class: the invariant of the loop over the words after the first in
the arm of the second stage on the whole bit array (`Ratpoints.Sieve.siftBitArrayWhole`), which
steps `a0` from one word to the next before it walks through the word, as the C code does. -/
def SiftBitArrayWalkInvariant (words : Nat → UInt64) (g : Int → List (Int × Int × Int))
    (cl : NumClass) (i : Int) (r0 : Delivery σ) (k : Nat) (s : Delivery σ × Int) :
    Prop :=
  s.2 = cl.a0 + i * (rbaLength * 2 ^ cl.k) + k * (64 * 2 ^ cl.k) ∧
    SiftBitArrayInvariant process words g cl i r0 (k + 1) s.1

/-- The invariant of the loop of `Ratpoints.Sieve.siftBitArrayByWords` over `[0:rbaPack]`, whose
state is the value of a return and the delivery: before a return,
`Ratpoints.Sieve.SiftBitArrayInvariant` after the words done; after the return at a stop, the value
returned is the delivery of the points of the numerators of the set bits of all the words of the
bit array. -/
def SiftBitArrayLoopInvariant (words : Nat → UInt64) (g : Int → List (Int × Int × Int))
    (cl : NumClass) (i : Int) (r0 : Delivery σ) :
    Std.WP.Invariant Nat (Option (Delivery σ × Counters) × Delivery σ × Counters) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun done _ s ↦ SiftBitArrayInvariant process words g cl i r0 done.length s.1)
    (fun ret _ ↦ ret.1 = r0.deliver process
      ((bitNumbers words (rbaLength * i) rbaPack).flatMap fun j ↦ g (cl.numerator j)))

/-- The invariant of the loop of `Ratpoints.Sieve.siftBitArrayWhole` over `[1:rbaPack]`, whose state
is the value of a return, the delivery and the numerator of bit `0` of the word:
`Ratpoints.Sieve.SiftBitArrayWalkInvariant` after the words done before a return, and after the
return at a stop the delivery of the points of the numerators of the set bits of all the words of
the bit array as the value returned. -/
def SiftBitArrayWalkLoopInvariant (words : Nat → UInt64) (g : Int → List (Int × Int × Int))
    (cl : NumClass) (i : Int) (r0 : Delivery σ) :
    Std.WP.Invariant Nat (Option (Delivery σ × Counters) × Delivery σ × Counters × Int) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun done _ s ↦ SiftBitArrayWalkInvariant process words g cl i r0 done.length (s.1, s.2.2))
    (fun ret _ ↦ ret.1 = r0.deliver process
      ((bitNumbers words (rbaLength * i) rbaPack).flatMap fun j ↦ g (cl.numerator j)))

-- The numerator of bit `t` of word `κ` as the walk computes it from that of bit `0` of the word.
private theorem numerator_rbaLength_mul_add (cl : NumClass) (i : Int) (κ t : Nat) :
    cl.a0 + i * (rbaLength * 2 ^ cl.k) + κ * (64 * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t =
      cl.numerator (rbaLength * i + 64 * κ + t) := by
  simp only [NumClass.numerator]
  push_cast
  grind

/-- The points of the numerators of the bit numbers of the set bits of the words `0, …, k` are
those of the words `0, …, k - 1` followed by those of word `k`, whose numerators the walk through
it computes from the numerator `a₀ + i (rbaLength 2 ^ cl.k) + k (64 2 ^ cl.k)` of its bit `0`. -/
theorem flatMap_numerator_bitNumbers_succ (words : Nat → UInt64) {β : Type} (g : Int → List β)
    (cl : NumClass) (i : Int) (k : Nat) :
    (bitNumbers words (rbaLength * i) (k + 1)).flatMap (fun j ↦ g (cl.numerator j)) =
      (bitNumbers words (rbaLength * i) k).flatMap (fun j ↦ g (cl.numerator j)) ++
        (((List.range 64).filter ((words k).toBitVec.getLsbD ·)).map fun t : Nat ↦
          cl.a0 + i * (rbaLength * 2 ^ cl.k) + k * (64 * 2 ^ cl.k) +
            (2 ^ cl.k : Nat) * t).flatMap g := by
  simp only [bitNumbers_succ, List.flatMap_append, List.flatMap_map, numerator_rbaLength_mul_add]

section

variable {process} {words : Nat → UInt64} {g : Int → List (Int × Int × Int)} {cl : NumClass}
  {i : Int} {r0 r : Delivery σ}

theorem SiftBitArrayInvariant.quit_eq_false {k : Nat} {o : Option (Delivery σ × Counters)}
    (h : o = none ∧ SiftBitArrayInvariant process words g cl i r0 k r) :
    r.quit = false :=
  h.2.1

theorem siftBitArrayInvariant_zero (words : Nat → UInt64) (g : Int → List (Int × Int × Int))
    (cl : NumClass) (i : Int) (h : r0.quit = false) :
    SiftBitArrayInvariant process words g cl i r0 0 r0 :=
  ⟨h, by simp⟩

/-- The delivery of the list `D` of the points that follow those of the bit numbers of the words
before `k` among those of the words before `k'`, when the callback does not stop the search in
it. -/
theorem SiftBitArrayInvariant.deliver_of_flatMap_eq {k k' : Nat} {D : List (Int × Int × Int)}
    (h : SiftBitArrayInvariant process words g cl i r0 k r)
    (hD : (bitNumbers words (rbaLength * i) k').flatMap (fun j ↦ g (cl.numerator j)) =
      (bitNumbers words (rbaLength * i) k).flatMap (fun j ↦ g (cl.numerator j)) ++ D)
    (hq : ¬(r.deliver process D).quit = true) :
    SiftBitArrayInvariant process words g cl i r0 k' (r.deliver process D) :=
  ⟨Bool.eq_false_iff.mpr hq, by rw [hD, Delivery.deliver_append, ← h.2]⟩

/-- The delivery of the list `D` of the points that follow those of the bit numbers of the words
before `k` among those of the words before `k'`, when the callback stops the search in it: the
delivery is that of the points of the words before any `m ≥ k'`, since the points after the stop
are passed over. -/
theorem SiftBitArrayInvariant.deliver_eq_of_quit {k k' m : Nat} {D : List (Int × Int × Int)}
    (h : SiftBitArrayInvariant process words g cl i r0 k r)
    (hD : (bitNumbers words (rbaLength * i) k').flatMap (fun j ↦ g (cl.numerator j)) =
      (bitNumbers words (rbaLength * i) k).flatMap (fun j ↦ g (cl.numerator j)) ++ D)
    (hk' : k' ≤ m) (hq : (r.deliver process D).quit = true) :
    r.deliver process D = r0.deliver process
      ((bitNumbers words (rbaLength * i) m).flatMap fun j ↦ g (cl.numerator j)) := by
  rw [h.2, ← Delivery.deliver_append, ← hD] at hq ⊢
  exact (Delivery.deliver_flatMap_eq_of_prefix process (bitNumbers_prefix _ _ hk') _ hq).symm

/-- The walk through word `k` from its first numerator, when the callback does not stop the
search in it. -/
theorem SiftBitArrayInvariant.succ {k : Nat} (h : SiftBitArrayInvariant process words g cl i r0 k r)
    (hq : ¬(r.deliver process ((((List.range 64).filter ((words k).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + k * (64 * 2 ^ cl.k) +
        (2 ^ cl.k : Nat) * t).flatMap g)).quit = true) :
    SiftBitArrayInvariant process words g cl i r0 (k + 1)
      (r.deliver process ((((List.range 64).filter ((words k).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + k * (64 * 2 ^ cl.k) +
          (2 ^ cl.k : Nat) * t).flatMap g)) :=
  h.deliver_of_flatMap_eq (flatMap_numerator_bitNumbers_succ words g cl i k) hq

/-- The walk through word `cur` of the loop over `[0:rbaPack]`, when the callback does not stop the
search in it. -/
theorem SiftBitArrayInvariant.append {done suff : List Nat} {cur : Nat}
    {o : Option (Delivery σ × Counters)}
    (h : o = none ∧ SiftBitArrayInvariant process words g cl i r0 done.length r)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff)
    (hq : ¬(r.deliver process ((((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + cur * (64 * 2 ^ cl.k) +
        (2 ^ cl.k : Nat) * t).flatMap g)).quit = true) :
    SiftBitArrayInvariant process words g cl i r0 (done ++ [cur]).length
      (r.deliver process ((((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + cur * (64 * 2 ^ cl.k) +
          (2 ^ cl.k : Nat) * t).flatMap g)) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton]
  exact h.2.succ hq

/-- A word that is zero adds nothing. -/
theorem SiftBitArrayInvariant.append_of_eq_zero {done suff : List Nat} {cur : Nat}
    {o : Option (Delivery σ × Counters)}
    (h' : o = none ∧ SiftBitArrayInvariant process words g cl i r0 done.length r)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff) (hz : words cur = 0) :
    SiftBitArrayInvariant process words g cl i r0 (done ++ [cur]).length r := by
  obtain ⟨-, h⟩ := h'
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton]
  refine ⟨h.1, ?_⟩
  rw [flatMap_numerator_bitNumbers_succ, hz, Delivery.deliver_append, ← h.2]
  simp only [UInt64.toBitVec_zero, BitVec.getLsbD_zero,
    List.filter_eq_nil_iff.mpr fun _ _ ↦ Bool.false_ne_true, List.map_nil, List.flatMap_nil,
    Delivery.deliver_nil]

/-- The walk through word `cur` of the loop over `[0:rbaPack]`, when the callback stops the search
in it: the delivery is that of all the words of the bit array. -/
theorem SiftBitArrayInvariant.eq_deliver_of_quit_append {done suff : List Nat} {cur : Nat}
    {o : Option (Delivery σ × Counters)}
    (h : o = none ∧ SiftBitArrayInvariant process words g cl i r0 done.length r)
    (hl : ForIn.toList [0:rbaPack] = done ++ cur :: suff)
    (hq : (r.deliver process ((((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + cur * (64 * 2 ^ cl.k) +
        (2 ^ cl.k : Nat) * t).flatMap g)).quit = true) :
    r.deliver process ((((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + cur * (64 * 2 ^ cl.k) +
        (2 ^ cl.k : Nat) * t).flatMap g) = r0.deliver process
      ((bitNumbers words (rbaLength * i) rbaPack).flatMap fun j ↦ g (cl.numerator j)) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  exact h.2.deliver_eq_of_quit (flatMap_numerator_bitNumbers_succ words g cl i _)
    (Std.Legacy.Range.lt_of_toList_eq_append_cons hl) hq

/-- At the end of the loop over `[0:rbaPack]`, the delivery is that of all the words of the bit
array. -/
theorem SiftBitArrayInvariant.eq_deliver
    (h : SiftBitArrayInvariant process words g cl i r0 (ForIn.toList [0:rbaPack]).length r) :
    r = r0.deliver process
      ((bitNumbers words (rbaLength * i) rbaPack).flatMap fun j ↦ g (cl.numerator j)) := by
  simpa using h.2

/-- The walk through the first word, from the first numerator `a₀ + i (rbaLength 2 ^ cl.k)` of the
bit array, when the callback does not stop the search in it, starts the invariant of the loop over
the other words. -/
theorem siftBitArrayWalkInvariant_zero (hr : r0.quit = false)
    (hq : ¬(r0.deliver process ((((List.range 64).filter ((words 0).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t).flatMap g)).quit =
        true) :
    SiftBitArrayWalkInvariant process words g cl i r0 0
      (r0.deliver process ((((List.range 64).filter ((words 0).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t).flatMap g),
        cl.a0 + i * (rbaLength * 2 ^ cl.k)) :=
  ⟨by simp, by simpa using (siftBitArrayInvariant_zero words g cl i hr).succ (by simpa using hq)⟩

/-- The numerator of bit `0` of word `k + 1`, stepped by `64 2 ^ cl.k` from that of word `k`, as the
walk through the words of a bit array computes it. -/
theorem add_eq_numerator_succ {cl : NumClass} {i a : Int} {k : Nat}
    (ha : a = cl.a0 + i * (rbaLength * 2 ^ cl.k) + k * (64 * 2 ^ cl.k)) :
    a + (64 * 2 ^ cl.k : Nat) =
      cl.a0 + i * (rbaLength * 2 ^ cl.k) + (k + 1 : Nat) * (64 * 2 ^ cl.k) := by
  rw [ha]
  push_cast
  grind

theorem SiftBitArrayWalkInvariant.quit_eq_false {k : Nat} {s : Delivery σ × Int}
    {o : Option (Delivery σ × Counters)}
    (h : o = none ∧ SiftBitArrayWalkInvariant process words g cl i r0 k s) :
    s.1.quit = false :=
  h.2.2.1

/-- The step `64 2 ^ cl.k` to the first numerator of word `cur` of the loop over `[1:rbaPack]`, and
the walk through it from there, when the callback does not stop the search in it. -/
theorem SiftBitArrayWalkInvariant.append {done suff : List Nat} {cur : Nat} {s : Delivery σ × Int}
    {o : Option (Delivery σ × Counters)}
    (h' : o = none ∧ SiftBitArrayWalkInvariant process words g cl i r0 done.length s)
    (hl : ForIn.toList [1:rbaPack] = done ++ cur :: suff)
    (hq : ¬(s.1.deliver process ((((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ s.2 + (64 * 2 ^ cl.k : Nat) + (2 ^ cl.k : Nat) * t).flatMap g)).quit = true) :
    SiftBitArrayWalkInvariant process words g cl i r0 (done ++ [cur]).length
      (s.1.deliver process ((((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
        fun t : Nat ↦ s.2 + (64 * 2 ^ cl.k : Nat) + (2 ^ cl.k : Nat) * t).flatMap g),
        s.2 + (64 * 2 ^ cl.k : Nat)) := by
  obtain ⟨-, h⟩ := h'
  obtain rfl : cur = done.length + 1 := by
    lia [Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl]
  rw [add_eq_numerator_succ h.1] at hq ⊢
  rw [List.length_append, List.length_singleton]
  exact ⟨rfl, h.2.succ hq⟩

/-- The walk through word `cur` of the loop over `[1:rbaPack]`, when the callback stops the search
in it: the delivery is that of all the words of the bit array. -/
theorem SiftBitArrayWalkInvariant.eq_deliver_of_quit {done suff : List Nat} {cur : Nat}
    {s : Delivery σ × Int} {o : Option (Delivery σ × Counters)}
    (h' : o = none ∧ SiftBitArrayWalkInvariant process words g cl i r0 done.length s)
    (hl : ForIn.toList [1:rbaPack] = done ++ cur :: suff)
    (hq : (s.1.deliver process ((((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ s.2 + (64 * 2 ^ cl.k : Nat) + (2 ^ cl.k : Nat) * t).flatMap g)).quit = true) :
    s.1.deliver process ((((List.range 64).filter ((words cur).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ s.2 + (64 * 2 ^ cl.k : Nat) + (2 ^ cl.k : Nat) * t).flatMap g) =
      r0.deliver process
        ((bitNumbers words (rbaLength * i) rbaPack).flatMap fun j ↦ g (cl.numerator j)) := by
  obtain ⟨-, h⟩ := h'
  have hlt := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain rfl : cur = done.length + 1 := by
    lia [Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl]
  rw [add_eq_numerator_succ h.1] at hq ⊢
  exact h.2.deliver_eq_of_quit (flatMap_numerator_bitNumbers_succ words g cl i _) hlt hq

/-- At the end of the loop over `[1:rbaPack]`, the delivery is that of all the words of the bit
array. -/
theorem SiftBitArrayWalkInvariant.eq_deliver {s : Delivery σ × Int} {words' : Nat → UInt64}
    (hw : ∀ κ < rbaPack, words κ = words' κ)
    (h : SiftBitArrayWalkInvariant process words g cl i r0 (ForIn.toList [1:rbaPack]).length s) :
    s.1 = r0.deliver process
      ((bitNumbers words' (rbaLength * i) rbaPack).flatMap fun j ↦ g (cl.numerator j)) := by
  have hl : (ForIn.toList [1:rbaPack]).length + 1 = rbaPack := by
    simp only [Std.Legacy.Range.length_toList]
    lia [rbaPack_pos]
  rw [← bitNumbers_congr hw]
  exact (hl ▸ h.2).2

/-- The walk through the first word of words that agree with `words'`, from the first numerator
`a₀ + i (rbaLength 2 ^ cl.k)` of the bit array, when the callback stops the search in it: the
delivery is that of all the words of `words'`. -/
theorem eq_deliver_of_quit_of_forall_eq {words' : Nat → UInt64} (hr : r0.quit = false)
    (hw : ∀ κ < rbaPack, words κ = words' κ)
    (hq : (r0.deliver process ((((List.range 64).filter ((words 0).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t).flatMap g)).quit =
        true) :
    r0.deliver process ((((List.range 64).filter ((words 0).toBitVec.getLsbD ·)).map
      fun t : Nat ↦ cl.a0 + i * (rbaLength * 2 ^ cl.k) + (2 ^ cl.k : Nat) * t).flatMap g) =
      r0.deliver process
        ((bitNumbers words' (rbaLength * i) rbaPack).flatMap fun j ↦ g (cl.numerator j)) := by
  rw [← bitNumbers_congr hw]
  simpa using (siftBitArrayInvariant_zero words g cl i hr).deliver_eq_of_quit
    (flatMap_numerator_bitNumbers_succ words g cl i 0) rbaPack_pos (by simpa using hq)

/-- The words of a bit array that the second stage leaves zero have no set bits: nothing is
delivered. -/
theorem eq_deliver_of_isZeroAt {specs : List SieveSpec} {nums nums' : Vector UInt64 rbaPack}
    (hw : ∀ κ < rbaPack, nums'[κ]! = andWords specs nums[κ]! i κ)
    (hz : ¬(!isZeroAt nums' 0) = true) (r : Delivery σ) :
    r = r.deliver process ((bitNumbers (fun κ ↦ andWords specs nums[κ]! i κ) (rbaLength * i)
      rbaPack).flatMap fun j ↦ g (cl.numerator j)) := by
  rw [bitNumbers_eq_nil fun κ hκ ↦ ?_]
  · simp
  have := (isZeroAt_eq_true_iff nums' 0).mp (by simpa using hz) κ hκ
  simp_all

end


attribute [local irreducible] SiftBitArrayInvariant SiftBitArrayWalkInvariant in
open Std.WP Lean.Order in
/-- The arm for one word at a time walks through the set bits of the words of `nums` and-ed with the
rows of the moduli of `specs` (`Ratpoints.Sieve.secondStageWord_spec`), each bit `j` standing for
the numerator `a₀ + 2 ^ k j` of the class `cl`, and skips a word that is zero, which loses nothing;
it returns at a stop. -/
@[spec]
theorem siftBitArrayByWords_spec (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (nums : Vector UInt64 rbaPack) (r : Delivery σ) (cnt : Counters) :
    ⦃ r.quit = false ∧ StageFits specs mgs small i (i + 1) ⦄
    siftBitArrayByWords process w d b fl specs mgs small checks cl i nums r cnt
    ⦃ fun r' ↦ r'.1 = r.deliver process ((bitNumbers (fun κ ↦ andWords specs nums[κ]! i κ)
        (rbaLength * i) rbaPack).flatMap
          fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ⦄ := by
  vcgen [siftBitArrayByWords] invariants
  | inv1 => SiftBitArrayLoopInvariant process (fun κ ↦ andWords specs nums[κ]! i κ)
      (acceptedPoints w d b fl checks) cl i r
  all_goals subst_vars
  all_goals simp only [SiftBitArrayLoopInvariant, meet_prop_eq_and, join_prop_eq_or,
    iSup_prop_eq_exists, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, exists_eq_left', exists_false, and_true] at *
  all_goals first
    | exact siftBitArrayInvariant_zero _ _ _ _ ‹_ ∧ _›.1
    | exact ‹_ ∧ _›.2
    | exact SiftBitArrayInvariant.quit_eq_false ‹_›
    | exact ‹_›
    | exact SiftBitArrayInvariant.eq_deliver ‹_›
    | exact Std.Legacy.Range.lt_of_toList_eq_append_cons ‹_›
    | exact SiftBitArrayInvariant.eq_deliver_of_quit_append ‹_› ‹_› ‹_›
    | exact SiftBitArrayInvariant.append ‹_› ‹_› ‹_›
    | exact SiftBitArrayInvariant.append_of_eq_zero ‹_› ‹_› (by simp_all)

attribute [local irreducible] SiftBitArrayInvariant SiftBitArrayWalkInvariant in
open Std.WP Lean.Order in
/-- The arm of the second stage on the whole bit array walks through the set bits of the words of
`nums` and-ed with the rows of the moduli of `specs` (`Ratpoints.Sieve.secondStage_spec`), each bit
`j` standing for the numerator `a₀ + 2 ^ k j` of the class `cl`, and skips the walks when the second
stage leaves the bit array zero, which loses nothing; it returns at a stop. -/
@[spec]
theorem siftBitArrayWhole_spec (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (nums : Vector UInt64 rbaPack) (r0 : Delivery σ) (cnt : Counters) :
    ⦃ r0.quit = false ∧ StageFits specs mgs small i (i + 1) ⦄
    siftBitArrayWhole process w d b fl specs mgs small checks cl i nums r0 cnt
    ⦃ fun r' ↦ r'.1 = r0.deliver process ((bitNumbers (fun κ ↦ andWords specs nums[κ]! i κ)
        (rbaLength * i) rbaPack).flatMap
          fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ⦄ := by
  vcgen [siftBitArrayWhole] invariants
  | inv1 => SiftBitArrayWalkLoopInvariant process (fun κ ↦ nums[κ]!)
      (acceptedPoints w d b fl checks) cl i r0
  all_goals subst_vars
  all_goals try simp only [SiftBitArrayWalkLoopInvariant, meet_prop_eq_and, join_prop_eq_or,
    iSup_prop_eq_exists, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, exists_eq_left', exists_false, and_true] at *
  all_goals first
    | exact ‹_ ∧ _›.2
    | exact ‹_ ∧ _›.1
    | exact eq_deliver_of_quit_of_forall_eq ‹_ ∧ _›.1 ‹_› ‹_›
    | exact siftBitArrayWalkInvariant_zero ‹_ ∧ _›.1 ‹_›
    | exact ‹_ = _›.trans (by rw [bitNumbers_congr ‹_›])
    | exact SiftBitArrayWalkInvariant.eq_deliver ‹_› ‹_›
    | exact SiftBitArrayWalkInvariant.quit_eq_false ‹_›
    | exact SiftBitArrayWalkInvariant.eq_deliver_of_quit ‹_› ‹_› ‹_›
    | exact SiftBitArrayWalkInvariant.append ‹_› ‹_› ‹_›
    | exact eq_deliver_of_isZeroAt ‹_› ‹_› r0

/-- Both arms deliver the points of the numerators of the set bits of the same words, the words of
`nums` and-ed with the rows of the moduli of `specs`
(`Ratpoints.Sieve.siftBitArrayByWords_spec`, `Ratpoints.Sieve.siftBitArrayWhole_spec`). -/
@[spec]
theorem siftBitArray_spec (useLong : Bool) (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (i : Int) (nums : Vector UInt64 rbaPack) (r : Delivery σ) (cnt : Counters) :
    ⦃ r.quit = false ∧ StageFits specs mgs small i (i + 1) ⦄
    siftBitArray process useLong w d b fl specs mgs small checks cl i nums r cnt
    ⦃ fun r' ↦ r'.1 = r.deliver process ((bitNumbers (fun κ ↦ andWords specs nums[κ]! i κ)
        (rbaLength * i) rbaPack).flatMap
          fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ⦄ := by
  cases useLong
  · exact siftBitArrayWhole_spec process w d b fl specs mgs small checks cl i nums r cnt
  · exact siftBitArrayByWords_spec process w d b fl specs mgs small checks cl i nums r cnt

/-! ### The scan of a piece -/

/-- The invariant of the loop of `Ratpoints.Sieve.scanPiece` that writes the sentinel into bit
array `n` of `surv`: the words of the piece are those of `surv`, and the first `k` words of bit
array `n` are all ones. -/
def ScanPieceSentinelInvariant {m : Nat} (n : Nat) (surv : Vector UInt64 m) (k : Nat)
    (sv : Vector UInt64 m) : Prop :=
  (∀ y < n * rbaPack, sv[y]! = surv[y]!) ∧ ∀ κ < k, sv[rbaPack * n + κ]! = ~~~0

/-- The invariant of the scan of `Ratpoints.Sieve.scanPiece` at bit array `pos` of the words `sv`,
for a piece of `n` bit arrays from the word number `w0` on, the moduli `specs` of the second stage
with their rows and the points `g a` of the numerator `a` of a bit in the packing of the class `cl`
(in the scan, those of `Ratpoints.Sieve.acceptedPoints`), from the delivery `r0`: `pos ≤ n`, the
callback has not stopped the search, and `r` is the delivery of the points of the bits
`rbaLength w0 + 64 y + t` of the set bits `t` of the words `y < rbaPack pos` and-ed with the rows of
`specs` (`Ratpoints.Sieve.andWords`), in increasing order: the invariant of the extraction of one
bit array (`Ratpoints.Sieve.SiftBitArrayInvariant`) for the words of the piece from `w0` on. -/
def ScanPieceInvariant {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec)
    (g : Int → List (Int × Int × Int)) (cl : NumClass) (w0 : Int) (n : Nat) (r0 : Delivery σ)
    (pos : Nat) (r : Delivery σ) :
    Prop :=
  pos ≤ n ∧
    SiftBitArrayInvariant process (fun y ↦ andWords specs sv[y]! w0 y) g cl w0 r0 (rbaPack * pos) r

/-- `Ratpoints.Sieve.ScanPieceInvariant` as the invariant of the scan of
`Ratpoints.Sieve.scanPiece`, whose state is the value of a return, the position and the delivery,
with all `n` bit arrays done at the exit; after the return at a stop, the value returned is the
delivery of the points of all the bit arrays of the piece. -/
def ScanPieceWhileInvariant {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec)
    (g : Int → List (Int × Int × Int)) (cl : NumClass) (w0 : Int) (n : Nat) (r0 : Delivery σ) :
    Std.WP.WhileInvariant (Option (Delivery σ × Counters) × Nat × Delivery σ × Counters) Prop :=
  .mk fun exit s ↦ s.1 = none ∧ ScanPieceInvariant process sv specs g cl w0 n r0 s.2.1 s.2.2.1 ∧
    (exit = true → s.2.1 = n) ∨ exit = true ∧ s.1.map Prod.fst = some (r0.deliver process
      ((bitNumbers (fun y ↦ andWords specs sv[y]! w0 y) (rbaLength * w0) (rbaPack * n)).flatMap
        fun j ↦ g (cl.numerator j)))

/-- The invariant of the loop of `Ratpoints.Sieve.scanPiece` that steps over the bit arrays that are
zero, from bit array `pos0` on, with the delivery `r` of the bit arrays before `pos0`: the position
is at least `pos0`, and `Ratpoints.Sieve.ScanPieceInvariant` holds there with `r`, since a bit array
that is zero has no set bits. -/
def ScanPieceZeroInvariant {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec)
    (g : Int → List (Int × Int × Int)) (cl : NumClass) (w0 : Int) (n : Nat) (r0 : Delivery σ)
    (pos0 : Nat) (r : Delivery σ) :
    Std.WP.WhileInvariant Nat Prop :=
  .mk fun _ pos ↦ pos0 ≤ pos ∧ ScanPieceInvariant process sv specs g cl w0 n r0 pos r

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
    (h : ScanPieceSentinelInvariant n surv (ForIn.toList [0:rbaPack]).length sv) {pos : Nat}
    (hz : isZeroAt sv pos = true) :
    pos ≠ n := by
  rintro rfl
  rw [Std.Legacy.Range.length_toList] at h
  have h0 := (isZeroAt_eq_true_iff sv pos).mp hz 0 rbaPack_pos
  rw [h.2 0 (by simpa using rbaPack_pos)] at h0
  exact absurd h0 (by decide)

/-- The bit numbers of the set bits of the words of a piece before the sentinel are those of the
words of `surv`, since the sentinel was written past them. -/
theorem ScanPieceSentinelInvariant.bitNumbers_eq {m n : Nat} {surv sv : Vector UInt64 m}
    (hs : ScanPieceSentinelInvariant n surv (ForIn.toList [0:rbaPack]).length sv)
    (specs : List SieveSpec) (w0 : Int) :
    bitNumbers (fun y ↦ andWords specs sv[y]! w0 y) (rbaLength * w0) (rbaPack * n) =
      bitNumbers (fun y ↦ andWords specs surv[y]! w0 y) (rbaLength * w0) (n * rbaPack) := by
  rw [Nat.mul_comm rbaPack n]
  exact bitNumbers_congr (fun y hy ↦ by rw [hs.1 y hy]) _

/-- The bit arrays of a piece before the sentinel are those of `surv`, since the sentinel was
written past them. -/
theorem ScanPieceSentinelInvariant.isZeroAt_eq {m n : Nat} {surv sv : Vector UInt64 m}
    (hs : ScanPieceSentinelInvariant n surv (ForIn.toList [0:rbaPack]).length sv) {p : Nat}
    (hp : p < n) : isZeroAt sv p = isZeroAt surv p := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [isZeroAt_eq_true_iff, isZeroAt_eq_true_iff]
  refine forall₂_congr fun κ hκ ↦ ?_
  rw [hs.1 _ (Nat.mul_add_lt_mul_of_lt_of_lt' hp hκ)]

/-- The bit numbers of the set bits of the first `pos + 1` bit arrays of a piece are those of the
first `pos` followed by those of bit array `pos`, copied and passed through
`Ratpoints.Sieve.siftBitArray` with its word number `w0 + pos`. -/
theorem bitNumbers_rbaPack_mul_succ {m : Nat} (sv : Vector UInt64 m) (specs : List SieveSpec)
    (w0 : Int) (pos : Nat) :
    bitNumbers (fun y ↦ andWords specs sv[y]! w0 y) (rbaLength * w0) (rbaPack * (pos + 1)) =
      bitNumbers (fun y ↦ andWords specs sv[y]! w0 y) (rbaLength * w0) (rbaPack * pos) ++
        bitNumbers (fun κ ↦ andWords specs
          (Vector.ofFn fun κ : Fin rbaPack ↦ sv[rbaPack * pos + κ]!)[κ]! (w0 + pos) κ)
          (rbaLength * (w0 + pos)) rbaPack := by
  have hb : (rbaLength : Int) * w0 + 64 * (rbaPack * pos : Nat) = rbaLength * (w0 + pos) := by
    push_cast [rbaLength_eq]
    grind
  rw [Nat.mul_succ, bitNumbers_add, hb]
  exact congrArg (_ ++ ·) (bitNumbers_congr (fun κ hκ ↦ by
    simp only [Vector.getElem!_ofFn hκ, andWords_rbaPack_mul_add _ _ _ _ hκ]) _)

section

variable {process} {m : Nat} {sv : Vector UInt64 m} {specs : List SieveSpec} {cl : NumClass}
  {g : Int → List (Int × Int × Int)} {w0 : Int} {n pos : Nat} {r0 r : Delivery σ}

theorem ScanPieceInvariant.le (h : ScanPieceInvariant process sv specs g cl w0 n r0 pos r) :
    pos ≤ n :=
  h.1

theorem scanPieceInvariant_zero (sv : Vector UInt64 m) (specs : List SieveSpec)
    (g : Int → List (Int × Int × Int)) (cl : NumClass) (w0 : Int) (n : Nat) (h : r0.quit = false) :
    ScanPieceInvariant process sv specs g cl w0 n r0 0 r0 :=
  ⟨Nat.zero_le _, h, by simp⟩

/-- Bit array `pos`, copied and passed through `Ratpoints.Sieve.siftBitArray` with its word number
`w0 + pos`, when the callback does not stop the search in it. -/
theorem ScanPieceInvariant.add_one_of_siftBitArray {pos0 mb : Nat}
    {o : Option (Delivery σ × Counters)}
    {r' : Delivery σ} (hm : n - pos0 = mb ∧ o = none ∧
      ScanPieceInvariant process sv specs g cl w0 n r0 pos0 r' ∧ (False → pos0 = n))
    (h' : pos0 ≤ pos ∧ ScanPieceInvariant process sv specs g cl w0 n r0 pos r) (hlt : ¬n ≤ pos)
    (hq : ¬(r.deliver process ((bitNumbers (fun κ ↦ andWords specs
      (Vector.ofFn fun κ : Fin rbaPack ↦ sv[rbaPack * pos + κ]!)[κ]! (w0 + pos) κ)
        (rbaLength * (w0 + pos)) rbaPack).flatMap fun j ↦ g (cl.numerator j))).quit = true) :
    n - (pos + 1) < mb ∧ ScanPieceInvariant process sv specs g cl w0 n r0 (pos + 1)
      (r.deliver process ((bitNumbers (fun κ ↦ andWords specs
        (Vector.ofFn fun κ : Fin rbaPack ↦ sv[rbaPack * pos + κ]!)[κ]! (w0 + pos) κ)
          (rbaLength * (w0 + pos)) rbaPack).flatMap fun j ↦ g (cl.numerator j))) ∧
        (False → pos + 1 = n) :=
  ⟨by lia [hm.1], ⟨by lia, h'.2.2.deliver_of_flatMap_eq
    (by rw [bitNumbers_rbaPack_mul_succ, List.flatMap_append]) hq⟩, nofun⟩

/-- Bit array `pos`, copied and passed through `Ratpoints.Sieve.siftBitArray` with its word number
`w0 + pos`, when the callback stops the search in it: the delivery is that of the whole piece. -/
theorem ScanPieceInvariant.eq_deliver_of_quit {pos0 : Nat}
    (h' : pos0 ≤ pos ∧ ScanPieceInvariant process sv specs g cl w0 n r0 pos r) (hlt : ¬n ≤ pos)
    (hq : (r.deliver process ((bitNumbers (fun κ ↦ andWords specs
      (Vector.ofFn fun κ : Fin rbaPack ↦ sv[rbaPack * pos + κ]!)[κ]! (w0 + pos) κ)
        (rbaLength * (w0 + pos)) rbaPack).flatMap fun j ↦ g (cl.numerator j))).quit = true) :
    r.deliver process ((bitNumbers (fun κ ↦ andWords specs
      (Vector.ofFn fun κ : Fin rbaPack ↦ sv[rbaPack * pos + κ]!)[κ]! (w0 + pos) κ)
        (rbaLength * (w0 + pos)) rbaPack).flatMap fun j ↦ g (cl.numerator j)) =
      r0.deliver process ((bitNumbers (fun y ↦ andWords specs sv[y]! w0 y) (rbaLength * w0)
        (rbaPack * n)).flatMap fun j ↦ g (cl.numerator j)) :=
  h'.2.2.deliver_eq_of_quit (by rw [bitNumbers_rbaPack_mul_succ, List.flatMap_append])
    (Nat.mul_le_mul_left rbaPack (by lia)) hq

/-- A bit array that is zero adds nothing; it is not the sentinel, so that the measure `n - pos` of
the loop that steps over the bit arrays that are zero decreases. -/
theorem ScanPieceInvariant.add_one_of_isZeroAt {surv : Vector UInt64 m} {pos0 mb : Nat}
    (h : n - pos = mb ∧ pos0 ≤ pos ∧ ScanPieceInvariant process sv specs g cl w0 n r0 pos r)
    (hs : ScanPieceSentinelInvariant n surv (ForIn.toList [0:rbaPack]).length sv)
    (hz : isZeroAt sv pos = true) :
    n - (pos + 1) < mb ∧ pos0 ≤ pos + 1 ∧
      ScanPieceInvariant process sv specs g cl w0 n r0 (pos + 1) r := by
  obtain ⟨rfl, h0, h⟩ := h
  have hlt : pos < n := Nat.lt_of_le_of_ne h.1 (hs.ne_of_isZeroAt hz)
  refine ⟨by lia, by lia, hlt, h.2.1, ?_⟩
  rw [bitNumbers_rbaPack_mul_succ, bitNumbers_eq_nil (k := rbaPack) (fun κ hκ ↦ ?_),
    List.append_nil, ← h.2.2]
  simp [Vector.getElem!_ofFn hκ, (isZeroAt_eq_true_iff sv pos).mp hz κ hκ]

theorem ScanPieceInvariant.quit_eq_false {pos0 : Nat}
    (h : pos0 ≤ pos ∧ ScanPieceInvariant process sv specs g cl w0 n r0 pos r) : r.quit = false :=
  h.2.2.1

/-- The value returned at a stop in the scan, the delivery of the points of the bits of the words
before the sentinel, is the delivery of those of the words of `surv`. -/
theorem ScanPieceSentinelInvariant.eq_deliver_of_eq {surv : Vector UInt64 m} {r' : Delivery σ}
    (h : r' = r0.deliver process ((bitNumbers (fun y ↦ andWords specs sv[y]! w0 y) (rbaLength * w0)
      (rbaPack * n)).flatMap fun j ↦ g (cl.numerator j)))
    (hs : ScanPieceSentinelInvariant n surv (ForIn.toList [0:rbaPack]).length sv) :
    r' = r0.deliver process ((bitNumbers (fun y ↦ andWords specs surv[y]! w0 y) (rbaLength * w0)
      (n * rbaPack)).flatMap fun j ↦ g (cl.numerator j)) := by
  rw [h, hs.bitNumbers_eq]

/-- At the end of the scan, the delivery is that of the points of the set bits of the words of the
piece and-ed with the rows, which are those of `surv`, since the sentinel was written past them. -/
theorem ScanPieceInvariant.eq_deliver {surv : Vector UInt64 m}
    (h : ScanPieceInvariant process sv specs g cl w0 n r0 pos r ∧ (True → pos = n))
    (hs : ScanPieceSentinelInvariant n surv (ForIn.toList [0:rbaPack]).length sv) :
    r = r0.deliver process ((bitNumbers (fun y ↦ andWords specs surv[y]! w0 y) (rbaLength * w0)
      (n * rbaPack)).flatMap fun j ↦ g (cl.numerator j)) := by
  obtain ⟨h, rfl⟩ := And.intro h.1 (h.2 trivial)
  rw [h.2.2, hs.bitNumbers_eq]

end

/- The invariants are irreducible from here on: the verification conditions of
`Ratpoints.Sieve.scanPiece` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] ScanPieceSentinelInvariant ScanPieceInvariant

-- The contract of `Ratpoints.Sieve.scanPiece` in terms of the set bits of the words of the piece
-- and-ed with the rows of the second stage.
open Std.WP Lean.Order in
private theorem scanPiece_spec_getLsbD (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (w0 : Int) (n : Nat) (surv : Vector UInt64 ((n + 1) * rbaPack))
    (r : Delivery σ) (cnt : Counters) :
    ⦃ r.quit = false ∧ StageFits specs mgs small w0 (w0 + n) ⦄
    scanPiece process w d b fl specs mgs small checks cl w0 n surv r cnt
    ⦃ fun r' ↦ r'.1 = r.deliver process ((bitNumbers (fun y ↦ andWords specs surv[y]! w0 y)
        (rbaLength * w0) (n * rbaPack)).flatMap
          fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ⦄ := by
  vcgen [scanPiece] invariants
  | inv1 => fun done _ ↦ ScanPieceSentinelInvariant n surv done.length
  | inv2 sv _ => ScanPieceWhileInvariant process sv specs (acceptedPoints w d b fl checks) cl w0 n r
  | inv3 => Variant.ofMeasure fun s ↦ n - s.2.1
  | inv4 sv _ _ pos0 r' _ _ _ => ScanPieceZeroInvariant process sv specs
      (acceptedPoints w d b fl checks) cl w0 n r pos0 r'
  | inv5 => Variant.ofMeasure fun s : Nat ↦ n - s
  all_goals (subst_vars; try simp only [ScanPieceWhileInvariant, ScanPieceZeroInvariant,
    WhileInvariant.mk_apply, Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat,
    Assertion.NondetFun.evalsTo_pure, meet_prop_eq_and, ofProp_prop_eq, reduceCtorEq, false_and,
    or_false, false_or, true_and, and_false, Option.some.injEq, Option.map] at *)
  all_goals first
    | exact ScanPieceSentinelInvariant.append_set! ‹_› ‹_›
    | exact ScanPieceSentinelInvariant.eq_deliver_of_eq ‹_› ‹_›
    | exact ScanPieceInvariant.eq_deliver ‹_› ‹_›
    | exact ⟨ScanPieceInvariant.quit_eq_false ‹_›, StageFits.mono ‹_ ∧ _›.2 (by lia) (by lia)⟩
    | exact ScanPieceInvariant.eq_deliver_of_quit ‹_› ‹_› ‹_›
    | exact ScanPieceInvariant.add_one_of_siftBitArray ‹_› ‹_› ‹_› ‹_›
    | exact ScanPieceInvariant.add_one_of_isZeroAt ‹_› ‹_› ‹_›
    | grind [scanPieceSentinelInvariant_zero, scanPieceInvariant_zero, → ScanPieceInvariant.le]

/-- The loop over the zero bit arrays ends at the sentinel at the latest, so that both loops of the
scan end by the measure `n - pos`; the test `keep` is quantified in the postcondition, since the
program does not mention it. -/
@[spec]
theorem scanPiece_spec (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (w0 : Int) (n : Nat) (surv : Vector UInt64 ((n + 1) * rbaPack))
    (r : Delivery σ) (cnt : Counters) :
    ⦃ r.quit = false ∧ StageFits specs mgs small w0 (w0 + n) ⦄
    scanPiece process w d b fl specs mgs small checks cl w0 n surv r cnt
    ⦃ fun r' ↦ ∀ keep : Int → Bool, (∀ y < n * rbaPack, ∀ t : Nat,
        (andWords specs surv[y]! w0 y).toBitVec.getLsbD t =
          (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t))) →
      r'.1 = r.deliver process ((((List.range (n * rbaLength)).map fun k : Nat ↦
        rbaLength * w0 + k).filter keep).flatMap
          fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ⦄ :=
  ⟨fun pre keep hkeep ↦ by
    rw [(scanPiece_spec_getLsbD process w d b fl specs mgs small checks cl w0 n surv r cnt).le_wp
      pre,
      bitNumbers_eq_filter hkeep, rbaLength_eq, Nat.mul_left_comm]⟩

end Sieve

end Ratpoints

end
