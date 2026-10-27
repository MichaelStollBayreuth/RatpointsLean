/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Packing
public import Ratpoints.Proof.Stages

import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
import Ratpoints.Proof.FirstStage
import Ratpoints.Proof.ScanCounts
import Std.Tactic.Do

/-!
# The contracts of the pieces and the bits of one interval

The contracts of the components of the model on words from one piece on up to the bits of one
interval in pieces, as `@[spec]` theorems proved with `vcgen`, the program logic of Lean core, with
loop invariants that are named definitions. Each component hands the points it finds to the
callback of the caller on a delivery (`Ratpoints.Delivery`), whose flag of the stop is clear at the
start, and returns as soon as a call sets it; its contract says that the delivery it returns is the
reference of the delivery (`Ratpoints.Delivery.deliver`) of the list of the points it finds, which
passes over the points after the stop. The contracts speak of the bits `j` of the packing of a class
`cl` (`Ratpoints.Sieve.NumClass`), each standing for the numerator `a₀ + 2 ^ k j`
(`Ratpoints.Sieve.NumClass.numerator`), and of the tests of the bits that the rows of the moduli
read at their offsets (`Ratpoints.Sieve.SieveSpec.Reads`); the points of a numerator are those that
the exact check delivers with the flags of the search (`Ratpoints.Sieve.acceptedPoints`).

## Main definitions

* `Ratpoints.Sieve.IsMasked`: the words of a piece with the masks at its two ends applied.
* `Ratpoints.Sieve.arraysWith`, `Ratpoints.Sieve.bitsCounts`: the number of the bit arrays that hold
  a bit that passes a test, and the counts that the bits of one interval add to the counters.
* `Ratpoints.Sieve.lowMask`, `Ratpoints.Sieve.highMask`, `Ratpoints.Sieve.bitsBefore`,
  `Ratpoints.Sieve.pieceBits`: the masks of `Ratpoints.Sieve.siftBits` at the two ends of a piece,
  the bits of the pieces before a word number, and the bits of a piece that its masks leave.
* `Ratpoints.Sieve.PieceResult`: what a piece returns, as the two contracts of
  `Ratpoints.Sieve.siftPiece` state it.
* `Ratpoints.Sieve.SiftInvariant`, `Ratpoints.Sieve.SiftWhileInvariant`: the invariant of the loop
  of `Ratpoints.Sieve.siftBits` over the pieces, of the delivery and of the counters.

## Main statements

* `Ratpoints.Sieve.siftPiece_spec`: one piece with rows that read tests of the bits delivers, in
  either arm of the first stage, the points of the numerators of the bits that the masks at its two
  ends leave and that pass the pattern of the class (`Ratpoints.Sieve.classBit`) and the tests of
  the rows, in increasing order.
* `Ratpoints.Sieve.siftPiece_counters_spec`: when the callback does not stop the search, one piece
  adds to the counters its words, its bit arrays that hold a bit that passes the pattern of the
  class, the tests of the first stage and the masks, and the counts of the tests of a candidate of
  the numerators whose points it delivers.
* `Ratpoints.Sieve.siftBits_spec`: the bits from `low` to `high` in pieces deliver the points of the
  numerators of those that pass the pattern of the class and the tests of the rows, and, when the
  callback does not stop the search, add the counts of `Ratpoints.Sieve.bitsCounts`, independent of
  the size of the pieces.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Words`, `Ratpoints.Proof.FirstStage`,
`Ratpoints.Proof.Stages`, `Ratpoints.Proof.Packing`, `Ratpoints.Proof.Delivery` and
`Ratpoints.Proof.Scan` do, whose lemmas on bit arrays, rows, classes and the delivery and whose
contracts of both arms of the first stage and of the scan of a piece it builds on. The contracts
read the test of a candidate as its value (`Ratpoints.Sieve.acceptedPoints`), so that they need
nothing of the numerators and the denominator. The loop over the pieces returns at a stop: its
invariant holds the delivery of the points found so far with the flag clear before a return, and
the value returned after it, the delivery of all the points, since the reference passes over the
points after the first call that sets the flag (`Ratpoints.Delivery.deliver_eq_of_prefix`); its
verification conditions are closed by lemmas in their shape. A piece has a contract of the delivery
and one of the counters, as the scan has (`Ratpoints.Proof.ScanCounts`), whose proofs name the
contracts of the counters of the components they call; the loop over the pieces holds the delivery
and the counters in one invariant, and the contract of the bits of one interval states both. The
counts of the tests of a candidate, of the bit arrays and of the bits of one interval are
irreducible in their verification conditions. The contract of the sieve of one denominator, which
calls `Ratpoints.Sieve.siftBits` for each search interval, is in `Ratpoints.Proof.Sift`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

variable {σ : Type} (process : Int → Int → Int → σ → Answer σ)

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

/-- The bits of the words `v` of a piece of `n` bit arrays from the word number `w0` on, the words
of its first stage with the first `sp1` moduli of `specs` from the class word `cw` on (`hand`, as
`Ratpoints.Sieve.andRows_spec` states it) with the masks at its two ends applied, when the rows of
the moduli read the tests `sf.2` of the bits (`Ratpoints.Sieve.SieveSpec.Reads`): bit `t` of word
`y` stands for the bit `rbaLength w0 + 64 y + t`, which is set when it passes the class word, the
tests of the first stage and the masks. -/
theorem IsMasked.getLsbD_eq {n : Nat} {sp1 : Nat} {specs : List SieveSpec} {cw : UInt64}
    {w0 : Int} {maskLow maskHigh : Nat} {surv v : Vector UInt64 ((n + 1) * rbaPack)}
    (hand : ∀ y < n * rbaPack, surv[y]! = andWords (specs.take sp1) cw w0 y)
    (h : IsMasked n maskLow maskHigh surv v)
    {sfs : List (SieveSpec × (Int → Bool))} (hspecs : specs = sfs.map Prod.fst)
    (hsfs : ∀ sf ∈ sfs, sf.1.Reads sf.2) (y : Nat) (hy : y < n * rbaPack) (t : Nat) :
    v[y]!.toBitVec.getLsbD t = (decide (t < 64) && (fun j ↦ (classBit cw j &&
      (sfs.take sp1).all (·.2 j)) && decide (rbaLength * w0 + maskLow ≤ j ∧
        j + maskHigh < rbaLength * w0 + (n * rbaLength : Nat))) (rbaLength * w0 + 64 * y + t)) := by
  dsimp only
  by_cases ht : t < 64
  · rw [h y hy t ht, hand y hy, hspecs, ← List.map_take,
      getLsbD_andWords fun sf hsf ↦ hsfs sf (List.mem_of_mem_take hsf),
      classBit_rbaLength_mul_add cw w0 y ht]
    grind
  · simp [ht, BitVec.getLsbD_of_ge _ t (Nat.le_of_not_lt ht)]

/-- The words of the scan of a piece of `n` bit arrays from the word number `w0` on, the words `v`
of its first stage with the first `sp1` moduli of `specs` from the class word `cw` on (`hand`) with
the masks at its two ends applied, and-ed with the rows of the other moduli, when the rows of the
moduli read the tests `sf.2` of the bits (`Ratpoints.Sieve.SieveSpec.Reads`): bit `t` of word `y`
stands for the bit `rbaLength w0 + 64 y + t`, which is set when it passes the class word, the tests
of all the moduli and the masks. -/
theorem IsMasked.getLsbD_andWords_drop {n : Nat} {sp1 : Nat} {specs : List SieveSpec}
    {cw : UInt64} {w0 : Int} {maskLow maskHigh : Nat} {surv v : Vector UInt64 ((n + 1) * rbaPack)}
    (hand : ∀ y < n * rbaPack, surv[y]! = andWords (specs.take sp1) cw w0 y)
    (h : IsMasked n maskLow maskHigh surv v)
    {sfs : List (SieveSpec × (Int → Bool))} (hspecs : specs = sfs.map Prod.fst)
    (hsfs : ∀ sf ∈ sfs, sf.1.Reads sf.2) (y : Nat) (hy : y < n * rbaPack) (t : Nat) :
    (andWords (specs.drop sp1) v[y]! w0 y).toBitVec.getLsbD t = (decide (t < 64) &&
      (fun j ↦ (classBit cw j && sfs.all (·.2 j)) && decide (rbaLength * w0 + maskLow ≤ j ∧
        j + maskHigh < rbaLength * w0 + (n * rbaLength : Nat))) (rbaLength * w0 + 64 * y + t)) := by
  dsimp only
  rw [hspecs, ← List.map_drop, getLsbD_andWords fun sf hsf ↦ hsfs sf (List.mem_of_mem_drop hsf),
    h.getLsbD_eq hand hspecs hsfs y hy t, ← List.take_append_drop sp1 sfs, List.all_append,
    List.take_append_drop]
  grind

variable {process} in
/-- The points of a piece of `n` bit arrays from the word number `w0` on, given the contracts of its
first stage with the first `sp1` moduli of `specs` from the class word `cw` on the words `surv`
(`hand`, as `Ratpoints.Sieve.andRows_spec` states it) and of its scan with the other moduli on the
words `v` (`hout`, as `Ratpoints.Sieve.scanPiece_spec` states it, with the points `g j` of a bit
`j`), when `v` is `surv` with the masks applied and the rows of the moduli read the tests `sf.2` of
the bits (`Ratpoints.Sieve.SieveSpec.Reads`): the points of the bits from `rbaLength w0 + maskLow`
to `rbaLength (w0 + n) - 1 - maskHigh` that pass the class word (`Ratpoints.Sieve.classBit`) and
all the tests. -/
theorem IsMasked.eq_deliver {n : Nat} {g : Int → List (Int × Int × Int)} {sp1 : Nat}
    {specs : List SieveSpec} {cw : UInt64} {w0 : Int} {maskLow maskHigh : Nat}
    {surv v : Vector UInt64 ((n + 1) * rbaPack)} {r r' : Delivery σ}
    (hand : ∀ y < n * rbaPack, surv[y]! = andWords (specs.take sp1) cw w0 y)
    (h : IsMasked n maskLow maskHigh surv v)
    (hout : ∀ keep : Int → Bool, (∀ y < n * rbaPack, ∀ t : Nat,
        (andWords (specs.drop sp1) v[y]! w0 y).toBitVec.getLsbD t =
          (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t))) →
      r' = r.deliver process ((((List.range (n * rbaLength)).map fun k : Nat ↦
        rbaLength * w0 + k).filter keep).flatMap g))
    {sfs : List (SieveSpec × (Int → Bool))} (hspecs : specs = sfs.map Prod.fst)
    (hsfs : ∀ sf ∈ sfs, sf.1.Reads sf.2) :
    r' = r.deliver process ((((List.range (n * rbaLength - maskLow - maskHigh)).map fun k : Nat ↦
      rbaLength * w0 + maskLow + k).filter fun j ↦ classBit cw j && sfs.all (·.2 j)).flatMap
        g) := by
  rw [hout (fun j ↦ (classBit cw j && sfs.all (·.2 j)) &&
    decide (rbaLength * w0 + maskLow ≤ j ∧ j + maskHigh < rbaLength * w0 + (n * rbaLength : Nat)))
    (h.getLsbD_andWords_drop hand hspecs hsfs), ← List.filter_filter,
    List.filter_map_range_eq_map_range]

/-- The rows of the moduli, read at their offsets, are given by the tests `sf.2` of the bits that
they read (`Ratpoints.Sieve.SieveSpec.Reads`), quantified in the postcondition since the program
does not mention them; the first `sp1` moduli go to the first stage, in the chunked arm
(`Ratpoints.Sieve.andRowsChunked_spec`) for `1 < chunk ≤ 16` and in the other otherwise
(`Ratpoints.Sieve.andRows_spec`), the others to the second, with their reciprocals and the test
`small`, which keeps the values that the reductions by the reciprocals see in range
(`Ratpoints.Sieve.SieveSpec.Fits`); the bound on `maskHigh` is that of the high mask
(`Ratpoints.Sieve.getLsbD_clearHighBits`), and the low mask needs none. -/
@[spec]
theorem siftPiece_spec (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags) (sp1 : Nat)
    (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass)
    (w0 : Int) (n maskLow maskHigh : Nat) (r : Delivery σ) (cnt : Counters) :
    ⦃ r.quit = false ∧ maskHigh < rbaLength ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ⦄
    siftPiece process w d b fl sp1 specs mgs checks cl w0 n maskLow maskHigh r cnt
    ⦃ fun r' ↦ ∀ sfs : List (SieveSpec × (Int → Bool)), specs = sfs.map Prod.fst →
        (∀ sf ∈ sfs, sf.1.Reads sf.2) →
        r'.1 = r.deliver process ((((List.range (n * rbaLength - maskLow - maskHigh)).map
          fun k : Nat ↦ rbaLength * w0 + maskLow + k).filter fun j ↦
            classBit cl.bits j && sfs.all (·.2 j)).flatMap
              fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ⦄ := by
  vcgen [siftPiece]
  all_goals first
    | exact ⟨‹r.quit = false ∧ _›.1,
        stageFits_drop ‹r.quit = false ∧ maskHigh < rbaLength ∧ _›.2.2 (smallFits_decide w0 n) sp1⟩
    | exact ⟨‹1 < chunk ∧ chunk ≤ 16›.2,
        stageFits_take ‹r.quit = false ∧ maskHigh < rbaLength ∧ _›.2.2 (smallFits_decide w0 n) sp1⟩
    | exact stageFits_take ‹r.quit = false ∧ maskHigh < rbaLength ∧ _›.2.2
        (smallFits_decide w0 n) sp1
    | exact IsMasked.eq_deliver ‹_› (isMasked_clearHighBits_clearLowBits _ _
        ‹r.quit = false ∧ maskHigh < rbaLength ∧ _›.2.1) ‹_› ‹_› ‹_›
    | exact IsMasked.eq_deliver ‹_› (isMasked_clearLowBits _ _ (Decidable.of_not_not ‹_›)) ‹_› ‹_›
        ‹_›
    | exact IsMasked.eq_deliver ‹_› (isMasked_clearHighBits _ (Decidable.of_not_not ‹_›)
        ‹r.quit = false ∧ maskHigh < rbaLength ∧ _›.2.1) ‹_› ‹_› ‹_›
    | exact IsMasked.eq_deliver ‹_› (isMasked_self _ _ (Decidable.of_not_not ‹_›)
        (Decidable.of_not_not ‹_›)) ‹_› ‹_› ‹_›

/-! ### The counters of one piece -/

/- The counts of the tests of a candidate are irreducible from here on: the verification conditions
of the counters are closed by the lemmas of their lists, never by computing the counts. -/
attribute [local irreducible] testedCounts

/-- The number of the bit arrays with the word numbers `w0, …, w0 + n - 1`, of
`Ratpoints.rbaLength` bits each, that hold a bit that passes `keep`. -/
def arraysWith (keep : Int → Bool) (w0 : Int) (n : Nat) : Nat :=
  (List.range n).countP fun pos : Nat ↦ (List.range rbaLength).any fun t : Nat ↦
    keep (rbaLength * (w0 + pos) + t)

theorem arraysWith_zero (keep : Int → Bool) (w0 : Int) : arraysWith keep w0 0 = 0 :=
  rfl

theorem arraysWith_add (keep : Int → Bool) (w0 : Int) (m k : Nat) :
    arraysWith keep w0 (m + k) = arraysWith keep w0 m + arraysWith keep (w0 + m) k := by
  rw [arraysWith, arraysWith, arraysWith, List.range_add, List.countP_append, List.countP_map]
  exact congrArg (_ + ·) (List.countP_congr fun pos _ ↦ by
    rw [Function.comp_apply, Int.natCast_add, Int.add_assoc])

theorem arraysWith_add_of_eq (keep : Int → Bool) {w0 w0' : Int} {m : Nat} (h : w0' + m = w0)
    (k : Nat) : arraysWith keep w0' (m + k) = arraysWith keep w0' m + arraysWith keep w0 k := by
  rw [arraysWith_add, h]

theorem arraysWith_congr {keep keep' : Int → Bool} {w0 : Int} {n : Nat}
    (h : ∀ pos < n, ∀ t < rbaLength,
      keep (rbaLength * (w0 + pos) + t) = keep' (rbaLength * (w0 + pos) + t)) :
    arraysWith keep w0 n = arraysWith keep' w0 n :=
  List.countP_congr fun pos hpos ↦ by
    simp only [List.any_eq_true, List.mem_range]
    exact exists_congr fun t ↦ and_congr_right fun ht ↦ by
      rw [h pos (List.mem_range.mp hpos) t ht]

variable {process} in
/-- The counters of a piece of `n` bit arrays from the word number `w0` on, given the contracts of
its first stage with the first `sp1` moduli of `specs` from the class word `cw` on the words `surv`
(`hand`) and of the counters of its scan with the other moduli on the words `v` (`hout`, as
`Ratpoints.Sieve.scanPiece_counters_spec` states it), when `v` is `surv` with the masks applied and
the rows of the moduli read the tests `sf.2` of the bits: the bit arrays that hold a bit that the
masks leave and that passes the class word and the tests of the first stage, and the counts of the
tests of a candidate of the numerators of the bits from `rbaLength w0 + maskLow` to
`rbaLength (w0 + n) - 1 - maskHigh` that pass the class word and all the tests. -/
theorem IsMasked.eq_counters {n : Nat} {sp1 : Nat} {specs : List SieveSpec} {cw : UInt64}
    {w0 : Int} {maskLow maskHigh : Nat} {surv v : Vector UInt64 ((n + 1) * rbaPack)}
    {b : Nat} {checks : Thunk (List CheckSpec)} {cl : NumClass} {c c' : Counters}
    {r : Delivery σ}
    (hand : ∀ y < n * rbaPack, surv[y]! = andWords (specs.take sp1) cw w0 y)
    (h : IsMasked n maskLow maskHigh surv v)
    (hout : ∀ keep : Int → Bool, (∀ y < n * rbaPack, ∀ t : Nat,
        (andWords (specs.drop sp1) v[y]! w0 y).toBitVec.getLsbD t =
          (decide (t < 64) && keep (rbaLength * w0 + 64 * y + t))) →
      r.quit = false → c' = { c with words := c.words + n.toUInt64 * rbaPack.toUInt64 } +
        { arrays := ((List.range n).countP fun p ↦ !isZeroAt v p).toUInt64 } +
        testedCounts b checks ((((List.range (n * rbaLength)).map fun k : Nat ↦
          rbaLength * w0 + k).filter keep).map cl.numerator))
    {sfs : List (SieveSpec × (Int → Bool))} (hspecs : specs = sfs.map Prod.fst)
    (hsfs : ∀ sf ∈ sfs, sf.1.Reads sf.2) (hq : r.quit = false) :
    c' = c + { words := (n * rbaPack).toUInt64 } +
      { arrays := (arraysWith (fun j ↦ (classBit cw j && (sfs.take sp1).all (·.2 j)) &&
        decide (rbaLength * w0 + maskLow ≤ j ∧
          j + maskHigh < rbaLength * w0 + (n * rbaLength : Nat))) w0 n).toUInt64 } +
      testedCounts b checks ((((List.range (n * rbaLength - maskLow - maskHigh)).map fun k : Nat ↦
        rbaLength * w0 + maskLow + k).filter fun j ↦ classBit cw j && sfs.all (·.2 j)).map
          cl.numerator) := by
  rw [hout (fun j ↦ (classBit cw j && sfs.all (·.2 j)) &&
    decide (rbaLength * w0 + maskLow ≤ j ∧ j + maskHigh < rbaLength * w0 + (n * rbaLength : Nat)))
    (h.getLsbD_andWords_drop hand hspecs hsfs) hq, ← List.filter_filter,
    List.filter_map_range_eq_map_range, arraysWith,
    Counters.words_add_eq, List.countP_congr fun pos hpos ↦ by
      rw [isZeroAt_eq_not_any (keep := fun j ↦ (classBit cw j && (sfs.take sp1).all (·.2 j)) &&
          decide (rbaLength * w0 + maskLow ≤ j ∧
            j + maskHigh < rbaLength * w0 + (n * rbaLength : Nat)))
          (h.getLsbD_eq hand hspecs hsfs) (List.mem_range.mp hpos),
        Bool.not_not]]
  simp only [Nat.toUInt64_eq, UInt64.ofNat_mul]

open Std.WP Lean.Order in
/-- When the callback does not stop the search, one piece of `n` bit arrays adds to the counters its
`n Ratpoints.rbaPack` words, in `words`, the number of its bit arrays that hold a bit that the masks
leave and that passes the pattern of the class (`Ratpoints.Sieve.classBit`) and the tests of the
rows of the first stage, the first `sp1` moduli of `specs`, in `arrays`, and the counts of the tests
of a candidate (`Ratpoints.Sieve.testedCounts`) of the numerators of the bits that the masks leave
and that pass the pattern of the class and the tests of the rows of all the moduli; the tests
`sf.2` that the rows read (`Ratpoints.Sieve.SieveSpec.Reads`) are quantified in the postcondition.
-/
theorem siftPiece_counters_spec (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags) (sp1 : Nat)
    (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass)
    (w0 : Int) (n maskLow maskHigh : Nat) (r : Delivery σ) (cnt : Counters) :
    ⦃ maskHigh < rbaLength ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ⦄
    siftPiece process w d b fl sp1 specs mgs checks cl w0 n maskLow maskHigh r cnt
    ⦃ fun r' ↦ ∀ sfs : List (SieveSpec × (Int → Bool)), specs = sfs.map Prod.fst →
        (∀ sf ∈ sfs, sf.1.Reads sf.2) → r'.1.quit = false →
        r'.2 = cnt + { words := (n * rbaPack).toUInt64 } +
          { arrays := (arraysWith (fun j ↦ (classBit cl.bits j && (sfs.take sp1).all (·.2 j)) &&
            decide (rbaLength * w0 + maskLow ≤ j ∧
              j + maskHigh < rbaLength * w0 + (n * rbaLength : Nat))) w0 n).toUInt64 } +
          testedCounts b checks ((((List.range (n * rbaLength - maskLow - maskHigh)).map
            fun k : Nat ↦ rbaLength * w0 + maskLow + k).filter fun j ↦
              classBit cl.bits j && sfs.all (·.2 j)).map cl.numerator) ⦄ := by
  vcgen [siftPiece, scanPiece_counters_spec]
  all_goals first
    | exact stageFits_drop ‹maskHigh < rbaLength ∧ _›.2 (smallFits_decide w0 n) sp1
    | exact ⟨‹1 < chunk ∧ chunk ≤ 16›.2,
        stageFits_take ‹maskHigh < rbaLength ∧ _›.2 (smallFits_decide w0 n) sp1⟩
    | exact stageFits_take ‹maskHigh < rbaLength ∧ _›.2 (smallFits_decide w0 n) sp1
    | exact IsMasked.eq_counters ‹_› (isMasked_clearHighBits_clearLowBits _ _ ‹_ ∧ _›.1) ‹_› ‹_›
        ‹_› ‹_›
    | exact IsMasked.eq_counters ‹_› (isMasked_clearLowBits _ _ (Decidable.of_not_not ‹_›)) ‹_›
        ‹_› ‹_› ‹_›
    | exact IsMasked.eq_counters ‹_› (isMasked_clearHighBits _ (Decidable.of_not_not ‹_›)
        ‹_ ∧ _›.1) ‹_› ‹_› ‹_› ‹_›
    | exact IsMasked.eq_counters ‹_› (isMasked_self _ _ (Decidable.of_not_not ‹_›)
        (Decidable.of_not_not ‹_›)) ‹_› ‹_› ‹_› ‹_›

/-! ### The bits of one interval -/

open BruteForce

/-- The low mask of `Ratpoints.Sieve.siftBits` on the piece from the word number `w0` on: the number
of the bits of the first piece below `low`, `0` on the others. -/
abbrev lowMask (low w0 : Int) : Nat :=
  if w0 = low / rbaLength then (low - rbaLength * (low / rbaLength)).toNat else 0

/-- The low mask on a piece from the word number `w0` on: the number of its bits below `low`. -/
theorem lowMask_eq {low w0 : Int} (hw0 : low / rbaLength ≤ w0) :
    lowMask low w0 = (low - rbaLength * w0).toNat := by
  have hR := natCast_rbaLength_pos
  rw [lowMask]
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
  rw [Int.mul_add, Int.mul_one]
  lia [Int.emod_def high rbaLength, Int.emod_nonneg high (Int.ne_of_gt natCast_rbaLength_pos)]

/-- The high mask of `Ratpoints.Sieve.siftBits` on the piece that ends at the word number `w1`: the
number of the bits of the last piece above `high`, `0` on the others. -/
abbrev highMask (high w1 : Int) : Nat :=
  if w1 = high / rbaLength + 1 then rbaLength - 1 - (high % rbaLength).toNat else 0

/-- The high mask on a piece that ends at the word number `w1`: the number of its bits above
`high`. -/
theorem highMask_eq {high w1 : Int} (hw1 : w1 ≤ high / rbaLength + 1) :
    highMask high w1 = (rbaLength * w1 - 1 - high).toNat := by
  rw [highMask]
  split
  · subst_vars
    exact sub_toNat_emod_eq_toNat_mul_sub high
  · have hR := natCast_rbaLength_pos
    lia [Int.mul_ediv_self_le (x := high) (Int.ne_of_gt hR),
      Int.mul_le_mul_of_nonneg_left (show w1 ≤ high / rbaLength by lia) (Int.le_of_lt hR)]

/-- The bits from that of `low` up to the word number `w0` that lie in `low, …, high`: those of the
pieces of `Ratpoints.Sieve.siftBits` before `w0`. -/
abbrev bitsBefore (low high w0 : Int) : List Int :=
  ((List.range ((w0 - low / rbaLength).toNat * rbaLength)).map
    fun k : Nat ↦ rbaLength * (low / rbaLength) + k).filter fun a ↦ decide (low ≤ a ∧ a ≤ high)

/-- The bits of a piece of `n` bit arrays from the word number `w0` on that the masks `maskLow` and
`maskHigh` at its two ends leave. -/
abbrev pieceBits (w0 : Int) (n maskLow maskHigh : Nat) : List Int :=
  (List.range (n * rbaLength - maskLow - maskHigh)).map fun k : Nat ↦ rbaLength * w0 + maskLow + k

/-- The bits up to the word number `w0` and those of the next piece of `r` bit arrays, with the low
mask of `Ratpoints.Sieve.siftBits` and a high mask `mH`, the number of its bits above `high`, that
pass `keep`, with their points `g`: those up to the word number `w1' = w0 + r`. -/
theorem flatMap_filter_range_append {β : Type} {g : Int → List β} {keep : Int → Bool}
    {low high : Int} {r mH : Nat} {w0 w1' : Int} (hle : low / rbaLength ≤ w0) (hr : w1' = w0 + r)
    (hmH : mH = (rbaLength * w1' - 1 - high).toNat) :
    ((bitsBefore low high w0).filter keep).flatMap g ++
        ((pieceBits w0 r (lowMask low w0) mH).filter keep).flatMap g =
      ((bitsBefore low high w1').filter keep).flatMap g := by
  have hm : (rbaLength : Int) * w1' - 1 - high =
      rbaLength * w0 + ((r * rbaLength : Nat) : Int) - 1 - high := by
    rw [hr, Int.mul_add, Int.natCast_mul, Int.mul_comm (r : Int)]
  rw [lowMask_eq hle, hmH, hm, pieceBits, ← List.filter_map_range_eq_map_range']
  have hl : (w1' - low / rbaLength).toNat = (w0 - low / rbaLength).toNat + r := by lia
  have hmap : (List.range (r * rbaLength)).map ((fun k : Nat ↦ rbaLength * (low / rbaLength) + k) ∘
        fun x ↦ (w0 - low / rbaLength).toNat * rbaLength + x) =
      (List.range (r * rbaLength)).map fun k : Nat ↦ rbaLength * w0 + k :=
    List.map_congr_left fun k _ ↦ by grind
  rw [← List.flatMap_append, bitsBefore, bitsBefore, ← List.filter_append, ← List.filter_append, hl,
    Nat.add_mul, List.range_add, List.map_append, List.map_map, hmap]

/-- The bits up to the word number `w0` come first among those up to `w0' ≥ w0`. -/
theorem flatMap_filter_range_prefix {β : Type} (g : Int → List β) (keep : Int → Bool)
    (low high : Int) {w0 w0' : Int} (h : w0 ≤ w0') :
    ((bitsBefore low high w0).filter keep).flatMap g <+:
      ((bitsBefore low high w0').filter keep).flatMap g := by
  obtain ⟨l, hl⟩ := List.range_prefix_range (Nat.mul_le_mul_right rbaLength
    (show (w0 - low / rbaLength).toNat ≤ (w0' - low / rbaLength).toNat by lia))
  exact ⟨_, by rw [bitsBefore, bitsBefore, ← hl, List.map_append, List.filter_append,
    List.filter_append, List.flatMap_append]⟩

/-- The bits from that of `low` up to the word number one past that of `high` that lie in
`low, …, high` are the bits `low, …, high`. -/
theorem flatMap_filter_range_eq {β : Type} (g : Int → List β) (keep : Int → Bool)
    {low high : Int} (hlh : low / rbaLength ≤ high / rbaLength + 1) :
    ((bitsBefore low high (high / rbaLength + 1)).filter keep).flatMap g =
      (((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter keep).flatMap g := by
  have hR := natCast_rbaLength_pos
  have hL := Int.mul_ediv_self_le (x := low) (Int.ne_of_gt hR)
  have := Int.lt_mul_ediv_self_add (x := high) hR
  have hM : (((high / rbaLength + 1 - low / rbaLength).toNat * rbaLength : Nat) : Int) =
      rbaLength * (high / rbaLength) + rbaLength - rbaLength * (low / rbaLength) := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg (by lia)]
    grind
  rw [bitsBefore, List.filter_map_range_eq_map_range_of_le hL (by lia)]

/-- On the words of a piece from the word number `w0 ≥ ⌊low / rbaLength⌋` on that ends at
`w1' = w0 + rr`, with the low mask of `Ratpoints.Sieve.siftBits` and a high mask `mH`, the number of
its bits above `high`, the masks leave the bits in `low, …, high`. -/
theorem arraysWith_masked_eq {low high w0 w1' : Int} {rr mH : Nat} (hle : low / rbaLength ≤ w0)
    (hr : w1' = w0 + rr) (hmH : mH = (rbaLength * w1' - 1 - high).toNat) (keep : Int → Bool) :
    arraysWith (fun j ↦ keep j && decide (rbaLength * w0 + (lowMask low w0 : Int) ≤ j ∧
        j + mH < rbaLength * w0 + (rr * rbaLength : Nat))) w0 rr =
      arraysWith (fun j ↦ keep j && decide (low ≤ j ∧ j ≤ high)) w0 rr := by
  rw [lowMask_eq hle]
  refine arraysWith_congr fun pos hpos t ht ↦ ?_
  have h1 := Nat.mul_add_lt_mul_of_lt_of_lt' hpos ht
  have h2 : (rbaLength : Int) * (w0 + pos) + t = rbaLength * w0 + (rbaLength * pos + t : Nat) := by
    push_cast
    rw [Int.mul_add, Int.add_assoc]
  have h3 : (rbaLength : Int) * w1' = rbaLength * w0 + (rr * rbaLength : Nat) := by
    rw [hr, Int.mul_add, Int.natCast_mul, Int.mul_comm (rr : Int)]
  rw [h2]
  exact congrArg (keep _ && ·) (decide_eq_decide.mpr (by subst hmH; lia))

/-- The counts that the bits `low, …, high` of the class `cl` of the denominator `b` add to the
counters when they go through the sieve in pieces (`Ratpoints.Sieve.siftBits`), for the tests
`keep1` and `keep` of the bits that the rows of the first stage and of the first two stages read,
with the thunk `checks` of the third stage: none if `high < low`, and otherwise the
`Ratpoints.rbaPack` words of each of the bit arrays from that of `low` to that of `high`, in
`words`, the number of these bit arrays that hold one of the bits that passes the pattern of the
class (`Ratpoints.Sieve.classBit`) and `keep1`, in `arrays`, and the counts of the tests of a
candidate (`Ratpoints.Sieve.testedCounts`) of the numerators of the bits that pass the pattern of
the class and `keep`, each as a `UInt64`, wrapping. -/
def bitsCounts (b : Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass)
    (keep1 keep : Int → Bool) (low high : Int) : Counters :=
  if low ≤ high then
    { words := ((high / rbaLength + 1 - low / rbaLength).toNat * rbaPack).toUInt64 } +
      { arrays := (arraysWith (fun j ↦ (classBit cl.bits j && keep1 j) &&
        decide (low ≤ j ∧ j ≤ high)) (low / rbaLength)
          (high / rbaLength + 1 - low / rbaLength).toNat).toUInt64 } +
      testedCounts b checks ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦
        low + k).filter fun j ↦ classBit cl.bits j && keep j).map cl.numerator)
  else {}

/-- What a piece of `n` bit arrays from the word number `w0` on with the masks `mL` and `mH` at its
two ends returns in the loop of `Ratpoints.Sieve.siftBits` over the pieces of the class `cl`, from
the delivery `r` and the counters `c`, for the tests `keep1` and `keep` of the bits that the rows of
the first stage and of the first two stages read and the points `g` of the bits: the delivery `r'`
of the points of its bits that the masks leave and that pass the pattern of the class and `keep`,
and, when the callback does not stop the search in it, the counters `c'` with its words, the number
of its bit arrays that hold a bit that the masks leave and that passes the pattern of the class and
`keep1`, and the counts of the tests of a candidate, with the thunk `checks` of the third stage over
the denominator `b`, of the numerators whose points it delivers. -/
def PieceResult (g : Int → List (Int × Int × Int)) (b : Nat) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (keep1 keep : Int → Bool) (w0 : Int) (n mL mH : Nat) (r r' : Delivery σ)
    (c c' : Counters) : Prop :=
  r' = r.deliver process (((pieceBits w0 n mL mH).filter fun j ↦
      classBit cl.bits j && keep j).flatMap g) ∧
    (r'.quit = false → c' = c + { words := (n * rbaPack).toUInt64 } +
      { arrays := (arraysWith (fun j ↦ (classBit cl.bits j && keep1 j) &&
        decide (rbaLength * w0 + mL ≤ j ∧ j + mH < rbaLength * w0 + (n * rbaLength : Nat))) w0
          n).toUInt64 } +
      testedCounts b checks (((pieceBits w0 n mL mH).filter fun j ↦
        classBit cl.bits j && keep j).map cl.numerator))

-- Both contracts of `Ratpoints.Sieve.siftPiece` for a reading list `sfs` of its moduli, the form
-- that the loop over the pieces of `Ratpoints.Sieve.siftBits` uses.
private theorem siftPiece_spec_reads (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (sp1 : Nat) (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (w0 : Int) (n maskLow maskHigh : Nat) (r : Delivery σ) (cnt : Counters)
    {sfs : List (SieveSpec × (Int → Bool))} (hspecs : specs = sfs.map Prod.fst)
    (hsfs : ∀ sf ∈ sfs, sf.1.Reads sf.2) :
    ⦃ r.quit = false ∧ maskHigh < rbaLength ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ⦄
    siftPiece process w d b fl sp1 specs mgs checks cl w0 n maskLow maskHigh r cnt
    ⦃ fun r' ↦ PieceResult process (fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) b
        checks cl (fun j ↦ (sfs.take sp1).all (·.2 j)) (fun j ↦ sfs.all (·.2 j)) w0 n maskLow
        maskHigh r r'.1 cnt r'.2 ⦄ :=
  ⟨fun pre ↦ ⟨(siftPiece_spec process w d b fl sp1 specs mgs checks cl w0 n maskLow maskHigh r
    cnt).le_wp pre sfs hspecs hsfs, (siftPiece_counters_spec process w d b fl sp1 specs mgs checks
      cl w0 n maskLow maskHigh r cnt).le_wp pre.2 sfs hspecs hsfs⟩⟩

/-- The invariant of the loop of `Ratpoints.Sieve.siftBits` over the pieces, for the bits from
`low` to `high` of the packing of the class `cl`, the tests `keep1` and `keep` of the bits that the
rows of the first stage and of the first two stages read and the points `g` of the bits, from the
delivery `r0` and the counters `cnt0`, at the exit of the loop or not: the bit arrays from that of
`low` up to the word number `w0` are done, the callback has not stopped the search, the delivery is
that of the points of their bits in `low, …, high` that pass the pattern of the class and `keep`,
and the counters are `cnt0` plus their words, the number of them that hold a bit in
`low, …, high` that passes the pattern of the class and `keep1`, and the counts of the tests of a
candidate, with the thunk `checks` of the third stage over the denominator `b`, of the numerators
whose points are delivered. -/
structure SiftInvariant (g : Int → List (Int × Int × Int)) (b : Nat)
    (checks : Thunk (List CheckSpec)) (cl : NumClass) (keep1 keep : Int → Bool) (low high : Int)
    (r0 : Delivery σ) (cnt0 : Counters) (exit : Bool) (range : Nat) (w0 w1 : Int) (r : Delivery σ)
    (c : Counters) : Prop where
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
  /-- The callback has not stopped the search. -/
  quit_eq_false : r.quit = false
  /-- The delivery is that of the points of the bits up to `w0` that pass the pattern of the class
  and `keep`, in increasing order. -/
  eq_deliver : r = r0.deliver process (((bitsBefore low high w0).filter fun j ↦
    classBit cl.bits j && keep j).flatMap g)
  /-- The counters of the bit arrays from that of `low` up to `w0`. -/
  eq_counts : c = cnt0 + { words := ((w0 - low / rbaLength).toNat * rbaPack).toUInt64 } +
    { arrays := (arraysWith (fun j ↦ (classBit cl.bits j && keep1 j) &&
      decide (low ≤ j ∧ j ≤ high)) (low / rbaLength) (w0 - low / rbaLength).toNat).toUInt64 } +
    testedCounts b checks (((bitsBefore low high w0).filter fun j ↦
      classBit cl.bits j && keep j).map cl.numerator)

/-- `Ratpoints.Sieve.SiftInvariant` as the invariant of the `while` loop of
`Ratpoints.Sieve.siftBits`, with the value of a return at a stop: the delivery of the points of all
the bits `low, …, high` that pass the pattern of the class and `keep`, whose flag of the stop is
set. -/
def SiftWhileInvariant (g : Int → List (Int × Int × Int)) (b : Nat)
    (checks : Thunk (List CheckSpec)) (cl : NumClass) (keep1 keep : Int → Bool) (low high : Int)
    (r0 : Delivery σ) (cnt0 : Counters) :
    Std.WP.WhileInvariant (Option (Delivery σ × Counters) × Delivery σ × Counters × Nat × Int × Int)
      Prop :=
  .mk fun exit s ↦ s.1 = none ∧ SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 exit
      s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2 s.2.1 s.2.2.1 ∨
    exit = true ∧ s.1.map Prod.fst = some (r0.deliver process
      ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter fun j ↦
        classBit cl.bits j && keep j).flatMap g)) ∧ s.1.map (·.1.quit) = some true

section

variable {process} {g : Int → List (Int × Int × Int)} {b : Nat} {checks : Thunk (List CheckSpec)}
  {cl : NumClass} {keep1 keep : Int → Bool} {low high : Int} {r0 r r' : Delivery σ}
  {cnt0 c c' : Counters}

theorem siftInvariant_init (h : low ≤ high) {A : Nat} (hA : 1 ≤ A) (hr : r0.quit = false) :
    SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false A (low / rbaLength)
      (low / rbaLength + A) r0 cnt0 :=
  ⟨Int.le_refl _, by lia [Int.ediv_le_ediv natCast_rbaLength_pos h], nofun, rfl, hA, hr,
    by simp [bitsBefore], by simp [bitsBefore, arraysWith_zero]⟩

/-- A piece of `rr ≥ 1` bit arrays from the word number `w0` on, which ends at
`w1' ≤ high / rbaLength + 1`, with the low mask of `Ratpoints.Sieve.siftBits` and a high mask `mH`,
the number of its bits above `high`, when the callback does not stop the search in it. -/
theorem SiftInvariant.append {range rr mH : Nat} {w0 w1 w1' : Int}
    (h : SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false range w0 w1 r c)
    (hr : w1' = w0 + rr) (hr1 : 1 ≤ rr) (hw1' : w1' ≤ high / rbaLength + 1)
    (hmH : mH = (rbaLength * w1' - 1 - high).toNat)
    (hp : PieceResult process g b checks cl keep1 keep w0 rr (lowMask low w0) mH r r' c c')
    (hq : ¬r'.quit = true) :
    SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false rr w1' (w1' + rr) r'
      c' := by
  have hl := flatMap_filter_range_append (g := fun j ↦ [cl.numerator j])
    (keep := fun j ↦ classBit cl.bits j && keep j) (high := high) h.le_w0 hr hmH
  simp only [← List.map_eq_flatMap] at hl
  refine ⟨by lia [h.le_w0], hw1', nofun, rfl, hr1, Bool.eq_false_iff.mpr hq, ?_, ?_⟩
  · rw [hp.1, h.eq_deliver, ← Delivery.deliver_append, flatMap_filter_range_append h.le_w0 hr hmH]
  rw [hp.2 (Bool.eq_false_iff.mpr hq), h.eq_counts, arraysWith_masked_eq h.le_w0 hr hmH, ← hl,
    testedCounts_append, show (w1' - low / rbaLength).toNat = (w0 - low / rbaLength).toNat + rr by
      lia [h.le_w0], arraysWith_add_of_eq _
        (show low / rbaLength + (w0 - low / rbaLength).toNat = w0 by lia [h.le_w0]), Nat.add_mul]
  simp only [Nat.toUInt64_eq, UInt64.ofNat_add, Counters.words_mk_add, Counters.arrays_mk_add]
  ac_rfl

/-- A piece that ends at `w1' ≤ high / rbaLength + 1`, when the callback stops the search in it: the
delivery is that of all the bits `low, …, high` that pass the pattern of the class and `keep`. -/
theorem SiftInvariant.eq_deliver_of_quit {range rr mH : Nat} {w0 w1 w1' : Int}
    (h : SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false range w0 w1 r c)
    (hr : w1' = w0 + rr) (hw1' : w1' ≤ high / rbaLength + 1)
    (hmH : mH = (rbaLength * w1' - 1 - high).toNat)
    (hp : PieceResult process g b checks cl keep1 keep w0 rr (lowMask low w0) mH r r' c c')
    (hq : r'.quit = true) :
    r' = r0.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      fun j ↦ classBit cl.bits j && keep j).flatMap g) := by
  rw [hp.1, h.eq_deliver, ← Delivery.deliver_append,
    flatMap_filter_range_append h.le_w0 hr hmH] at hq ⊢
  rw [← flatMap_filter_range_eq g _ (by lia [h.le_w0, h.w0_le])]
  exact (Delivery.deliver_eq_of_prefix process (flatMap_filter_range_prefix g _ low high hw1')
    hq).symm

/-- The pieces advance: the measure `high / rbaLength + 1 - w0` of the loop of
`Ratpoints.Sieve.siftBits` decreases from one piece to the next. -/
theorem SiftInvariant.toNat_sub_lt {range : Nat} {w0 w1 : Int}
    (h : SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false range w0 w1 r c)
    (hw0 : w0 < high / rbaLength + 1) :
    (high / rbaLength + 1 - w1).toNat < (high / rbaLength + 1 - w0).toNat := by
  lia [h.w1_eq, h.one_le_range]

/-- The loop of `Ratpoints.Sieve.siftBits` ends at the word number one past that of `high`. -/
theorem SiftInvariant.exit_of_not_lt {range : Nat} {w0 w1 : Int}
    (h : SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false range w0 w1 r c)
    (hw0 : ¬w0 < high / rbaLength + 1) :
    SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 true range w0 w1 r c :=
  { h with eq_of_exit := fun _ ↦ Int.le_antisymm h.w0_le (Int.not_lt.mp hw0) }

/-- A middle piece, which ends at the word number `w1 ≤ high / rbaLength + 1`, when the callback
does not stop the search in it, in the shape of the verification condition. -/
theorem SiftInvariant.append_of_not_lt {range mb : Nat} {w0 w1 : Int}
    {o : Option (Delivery σ × Counters)}
    (hm : (high / rbaLength + 1 - w0).toNat = mb ∧ o = none ∧
      SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false range w0 w1 r c)
    (hlt : w0 < high / rbaLength + 1) (hw : ¬high / rbaLength + 1 < w1)
    (hp : PieceResult process g b checks cl keep1 keep w0 range (lowMask low w0) (highMask high w1)
      r r' c c') (hq : ¬r'.quit = true) :
    (high / rbaLength + 1 - w1).toNat < mb ∧
      SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false range w1 (w1 + range) r'
        c' := by
  obtain ⟨rfl, -, h⟩ := hm
  exact ⟨h.toNat_sub_lt hlt, h.append h.w1_eq h.one_le_range (by lia) (highMask_eq (by lia)) hp hq⟩

/-- The last piece, which ends at the word number `high / rbaLength + 1`, when the callback does not
stop the search in it, in the shape of the verification condition. -/
theorem SiftInvariant.append_of_lt {range mb : Nat} {w0 w1 : Int}
    {o : Option (Delivery σ × Counters)}
    (hm : (high / rbaLength + 1 - w0).toNat = mb ∧ o = none ∧
      SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false range w0 w1 r c)
    (hlt : w0 < high / rbaLength + 1)
    (hp : PieceResult process g b checks cl keep1 keep w0 (high / rbaLength + 1 - w0).toNat
      (lowMask low w0) (rbaLength - 1 - (high % rbaLength).toNat) r r' c c')
    (hq : ¬r'.quit = true) :
    (high / rbaLength + 1 - (high / rbaLength + 1)).toNat < mb ∧
      SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false
        (high / rbaLength + 1 - w0).toNat (high / rbaLength + 1)
        (high / rbaLength + 1 + (high / rbaLength + 1 - w0).toNat) r' c' := by
  obtain ⟨rfl, -, h⟩ := hm
  exact ⟨by lia, h.append (by lia) (by lia) (Int.le_refl _) (sub_toNat_emod_eq_toNat_mul_sub high)
    hp hq⟩

/-- A middle piece, when the callback stops the search in it, in the shape of the verification
condition: the delivery is that of all the bits `low, …, high` that pass the pattern of the class
and `keep`. -/
theorem SiftInvariant.eq_deliver_of_quit_of_not_lt {range mb : Nat} {w0 w1 : Int}
    {o : Option (Delivery σ × Counters)}
    (hm : (high / rbaLength + 1 - w0).toNat = mb ∧ o = none ∧
      SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false range w0 w1 r c)
    (hw : ¬high / rbaLength + 1 < w1)
    (hp : PieceResult process g b checks cl keep1 keep w0 range (lowMask low w0) (highMask high w1)
      r r' c c') (hq : r'.quit = true) :
    r' = r0.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      fun j ↦ classBit cl.bits j && keep j).flatMap g) ∧ r'.quit = true :=
  ⟨hm.2.2.eq_deliver_of_quit hm.2.2.w1_eq (by lia) (highMask_eq (by lia)) hp hq, hq⟩

/-- The last piece, when the callback stops the search in it, in the shape of the verification
condition: the delivery is that of all the bits `low, …, high` that pass the pattern of the class
and `keep`. -/
theorem SiftInvariant.eq_deliver_of_quit_of_lt {range mb : Nat} {w0 w1 : Int}
    {o : Option (Delivery σ × Counters)}
    (hm : (high / rbaLength + 1 - w0).toNat = mb ∧ o = none ∧
      SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false range w0 w1 r c)
    (hlt : w0 < high / rbaLength + 1)
    (hp : PieceResult process g b checks cl keep1 keep w0 (high / rbaLength + 1 - w0).toNat
      (lowMask low w0) (rbaLength - 1 - (high % rbaLength).toNat) r r' c c')
    (hq : r'.quit = true) :
    r' = r0.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      fun j ↦ classBit cl.bits j && keep j).flatMap g) ∧ r'.quit = true :=
  ⟨hm.2.2.eq_deliver_of_quit (by lia) (Int.le_refl _) (sub_toNat_emod_eq_toNat_mul_sub high) hp hq,
    hq⟩

/-- What the piece of the verification condition needs of the invariant: the callback has not
stopped the search. -/
theorem SiftInvariant.quit_eq_false_and {range mb mH : Nat} {w0 w1 : Int}
    {o : Option (Delivery σ × Counters)} {P : Prop}
    (hm : (high / rbaLength + 1 - w0).toNat = mb ∧ o = none ∧
      SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 false range w0 w1 r c)
    (hP : P) (hmH : mH < rbaLength) :
    r.quit = false ∧ mH < rbaLength ∧ P ∧ True :=
  ⟨hm.2.2.quit_eq_false, hmH, hP, trivial⟩

/-- At the exit of the loop of `Ratpoints.Sieve.siftBits`, the delivery is that of the points of the
bits `low, …, high` that pass the pattern of the class and `keep`, and the counters are those of
`Ratpoints.Sieve.bitsCounts`. -/
theorem SiftInvariant.post {range : Nat} {w0 w1 : Int} (hlh : low ≤ high)
    (h : SiftInvariant process g b checks cl keep1 keep low high r0 cnt0 true range w0 w1 r c) :
    r = r0.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      fun j ↦ classBit cl.bits j && keep j).flatMap g) ∧
      (r.quit = false → c = cnt0 + bitsCounts b checks cl keep1 keep low high) := by
  have hle : low / rbaLength ≤ high / rbaLength + 1 := by lia [h.le_w0, h.w0_le]
  have hl := flatMap_filter_range_eq (fun j ↦ [cl.numerator j])
    (fun j ↦ classBit cl.bits j && keep j) hle
  simp only [← List.map_eq_flatMap] at hl
  refine ⟨by rw [h.eq_deliver, h.eq_of_exit rfl, flatMap_filter_range_eq g _ hle], fun _ ↦ ?_⟩
  simp only [bitsCounts, hlh, ↓reduceIte]
  rw [h.eq_counts, h.eq_of_exit rfl, hl]
  ac_rfl

/-- An empty interval of bits delivers nothing and counts nothing. -/
theorem eq_deliver_and_of_not_le (h : ¬low ≤ high) (r : Delivery σ) (c : Counters) :
    r = r.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      fun j ↦ classBit cl.bits j && keep j).flatMap g) ∧
      (r.quit = false → c = c + bitsCounts b checks cl keep1 keep low high) := by
  rw [Int.toNat_of_nonpos (z := high + 1 - low) (by lia)]
  exact ⟨rfl, fun _ ↦ by simp only [bitsCounts, h, ↓reduceIte, Counters.add_empty]⟩

end

/- The counts of the bit arrays and of the bits of one interval are irreducible from here on. -/
attribute [local irreducible] arraysWith bitsCounts

-- The contract of `Ratpoints.Sieve.siftBits` for the reading list `sfs` of its moduli.
open Std.WP Lean.Order in
private theorem siftBits_spec_reads (w : Thunk (List Int)) (d b A : Nat) (fl : CheckFlags)
    (sp1 : Nat) (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (low high : Int) (r : Delivery σ) (cnt : Counters)
    {sfs : List (SieveSpec × (Int → Bool))} (hA : 1 ≤ A) (hfits : ∀ s ∈ specs, s.Fits)
    (hmg : mgs = specs.map (magic ·.p)) (hspecs : specs = sfs.map Prod.fst)
    (hsfs : ∀ sf ∈ sfs, sf.1.Reads sf.2) :
    ⦃ r.quit = false ⦄ siftBits process w d b A fl sp1 specs mgs checks cl low high r cnt
    ⦃ fun r' ↦ r'.1 = r.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦
        low + k).filter fun j ↦ classBit cl.bits j && sfs.all (·.2 j)).flatMap
          fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ∧
        (r'.1.quit = false → r'.2 = cnt + bitsCounts b checks cl
          (fun j ↦ (sfs.take sp1).all (·.2 j)) (fun j ↦ sfs.all (·.2 j)) low high) ⦄ := by
  vcgen [siftBits, siftPiece_spec_reads process (hspecs := hspecs) (hsfs := hsfs)] invariants
  · SiftWhileInvariant process (fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) b checks cl
      (fun j ↦ (sfs.take sp1).all (·.2 j)) (fun j ↦ sfs.all (·.2 j)) low high r cnt
  · .ofMeasure fun s ↦ (high / rbaLength + 1 - s.2.2.2.2.1).toNat
  all_goals (subst_vars; try simp only [SiftWhileInvariant, WhileInvariant.mk_apply,
    Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure,
    meet_prop_eq_and, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, Option.map_some, Option.map_none] at *)
  all_goals first
    | exact SiftInvariant.quit_eq_false_and ‹_› hfits (by (try split) <;> lia [rbaLength_pos])
    | have : ¬high / rbaLength + 1 < _ := ‹_›
      first
        | exact SiftInvariant.append_of_not_lt ‹_› ‹_› ‹_› ‹_› ‹_›
        | exact SiftInvariant.eq_deliver_of_quit_of_not_lt ‹_› ‹_› ‹_› ‹_›
    | have : high / rbaLength + 1 < _ := ‹_›
      first
        | exact SiftInvariant.append_of_lt ‹_› ‹_› ‹_› ‹_›
        | exact SiftInvariant.eq_deliver_of_quit_of_lt ‹_› ‹_› ‹_› ‹_›
    | grind [siftInvariant_init, SiftInvariant.exit_of_not_lt, eq_deliver_and_of_not_le,
        SiftInvariant.post]

/-- The bits from `low` to `high` in pieces of `A ≥ 1` bit arrays, with the moduli `specs` and their
reciprocals, deliver the points of the numerators of the bits that pass the class word of `cl` and
the tests `sf.2` that the rows of the moduli read (`Ratpoints.Sieve.SieveSpec.Reads`), quantified in
the postcondition since the program does not mention them, and, when the callback does not stop the
search, add to the counters the counts of `Ratpoints.Sieve.bitsCounts`, with the tests of the first
`sp1` moduli for the first stage; an empty interval delivers and counts nothing; the loop over the
pieces ends by the measure `high / rbaLength + 1 - w0`, since every piece has at least one bit
array, or at a stop. -/
@[spec]
theorem siftBits_spec (w : Thunk (List Int)) (d b A : Nat) (fl : CheckFlags) (sp1 : Nat)
    (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass)
    (low high : Int) (r : Delivery σ) (cnt : Counters) :
    ⦃ r.quit = false ∧ 1 ≤ A ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ⦄
    siftBits process w d b A fl sp1 specs mgs checks cl low high r cnt
    ⦃ fun r' ↦ ∀ sfs : List (SieveSpec × (Int → Bool)), specs = sfs.map Prod.fst →
        (∀ sf ∈ sfs, sf.1.Reads sf.2) →
        r'.1 = r.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦
          low + k).filter fun j ↦ classBit cl.bits j && sfs.all (·.2 j)).flatMap
            fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ∧
          (r'.1.quit = false → r'.2 = cnt + bitsCounts b checks cl
            (fun j ↦ (sfs.take sp1).all (·.2 j)) (fun j ↦ sfs.all (·.2 j)) low high) ⦄ :=
  ⟨fun ⟨hr, hA, hfits, hmg⟩ _ hspecs hsfs ↦ (siftBits_spec_reads process w d b A fl sp1 specs mgs
    checks cl low high r cnt hA hfits hmg hspecs hsfs).le_wp hr⟩

end Sieve

end Ratpoints

end
