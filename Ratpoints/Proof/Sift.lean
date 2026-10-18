/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.BitRange
public import Ratpoints.Proof.Packing
public import Ratpoints.Proof.RowStore
public import Ratpoints.Proof.Stages

import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
import Ratpoints.Proof.FirstStage
import Ratpoints.Proof.Scan
import Ratpoints.Proof.Sieve
import Std.Tactic.Do

/-!
# The contracts of the sieve of one denominator

The contracts of the components of the model on words from one piece on, through the bits of one
interval in pieces, up to the sieve of one denominator in the packing of its class, as
`@[spec]` theorems proved with `vcgen`, the program logic of Lean core, with loop invariants that
are named definitions. Each component hands the points it finds to the callback of the caller on a
delivery (`Ratpoints.Delivery`), whose flag of the stop is clear at the start, and returns as soon
as a call sets it; its contract says that the delivery it returns is the reference of the delivery
(`Ratpoints.Delivery.deliver`) of the list of the points it finds, which passes over the points
after the stop. Up to the bits of one interval, the contracts speak of the bits `j` of the packing
of a class `cl` (`Ratpoints.Sieve.NumClass`), each standing for the numerator `a₀ + 2 ^ k j`
(`Ratpoints.Sieve.NumClass.numerator`), and of the tests of the bits that the rows of the moduli
read at their offsets (`Ratpoints.Sieve.SieveSpec.Reads`); the numerators come in with the bits of
the numerators `-H, …, H` of one denominator; the points of a numerator are those that the exact
check delivers with the flags of the search (`Ratpoints.Sieve.acceptedPoints`).

## Main definitions

* `Ratpoints.Sieve.packedReads`: the closed forms of the rows of the sieve entries for a denominator
  in the packing of a class, with the tests of the bits that they read.
* `Ratpoints.Sieve.SiftIntervalsInvariant`, `Ratpoints.Sieve.SiftIntervalsLoopInvariant`: the
  invariant of the loop of `Ratpoints.Sieve.sift` over the search intervals, range after range.
* `Ratpoints.Sieve.IsSiftArgs`: what the contract of `Ratpoints.Sieve.sift` on the ranges of the
  numerators needs of its arguments.

## Main statements

* `Ratpoints.Sieve.siftPiece_spec`: one piece with rows that read tests of the bits delivers, in
  either arm of the first stage, the points of the numerators of the bits that the masks at its two
  ends leave and that pass the pattern of the class (`Ratpoints.Sieve.classBit`) and the tests of
  the rows, in increasing order.
* `Ratpoints.Sieve.siftBits_spec`: the bits from `low` to `high` in pieces deliver the points of the
  numerators of those that pass the pattern of the class and the tests of the rows.
* `Ratpoints.Sieve.eq_map_fst_packedReads_of_eq_run_buildRows`,
  `Ratpoints.Sieve.reads_of_mem_packedReads`: the rows that `Ratpoints.Sieve.setRows` and
  `Ratpoints.Sieve.buildRows` give for the residues `b dinv[k] mod p`, the closed forms of the rows
  of the entries, at the offsets of the class read whether the rows of `b` admit the numerators of
  the bits (`Ratpoints.Sieve.SieveEntry.reads_row`).
* `Ratpoints.Sieve.flatMap_filter_bits_eq`: the bits of `numerators_to_bits` of the height in the
  packing of the class of a class word `w` give the numerators `-H, …, H` that pass `w`;
  `Ratpoints.Sieve.flatMap_filter_intervalBits_eq`: the bits of a search interval that
  `Ratpoints.Sieve.intervalBits` gives, neither of the codes `1` and `2`, give the numerators
  `-H, …, H` of its range that pass `w`.
* `Ratpoints.Sieve.sift_spec`: the pieces of a denominator `0 < b < 2 ^ 63` in the packing of a
  class `cl` of the class word `w`, for `H < 2 ^ 63`, entries of the first two stages with their
  tables of inverses and the row offsets of the packing of `cl`, a store of the tables of rows that
  fits them (`Ratpoints.Sieve.RowStore.Fits`), and entries of the third stage of the shape of
  `Ratpoints.Sieve.SieveEntry.IsPrimeEntry` with the reciprocals of their moduli, deliver, for the
  ranges of the numerators that the bounds of the search intervals give
  (`Ratpoints.Sieve.RangesFor`), the points of the check with the flags
  (`Ratpoints.Sieve.checkNumWith`) of the numerators
  `-H, …, H` in one of the ranges that pass `w` and survive the sieve entries of all three stages,
  and the store with the rows built for `b` still fits the entries;
  `Ratpoints.Sieve.run_sift_eq_deliver_checkDen`: without `RATPOINTS_NO_CHECK`, these are the points
  that the plain sieve of `b` with all the entries gives whose numerators lie in the ranges and pass
  `w`, mapped by `Ratpoints.Sieve.swapPoint` after a reversal, without those with `y < 0` under
  `RATPOINTS_NO_Y`.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Words`, `Ratpoints.Proof.FirstStage`,
`Ratpoints.Proof.Stages`, `Ratpoints.Proof.Packing`, `Ratpoints.Proof.BitRange`,
`Ratpoints.Proof.RowStore`, `Ratpoints.Proof.Delivery` and `Ratpoints.Proof.Scan` do, whose lemmas
on bit arrays, rows, classes, the bits of an interval and the delivery and whose contracts of both
arms of the first stage, of the scan of a piece and of the third stage and of the rows built into
the tables of rows of the run it builds on. The contracts of one piece and of one interval read the
test of a candidate as its value (`Ratpoints.Sieve.acceptedPoints`), so that they need nothing of
the numerators and the denominator; the hypotheses of the test on the words of the C code,
`0 < b < 2 ^ 63` and `|a| ≤ H < 2 ^ 63`, come in with the numerators `-H, …, H` of one denominator
(`Ratpoints.Sieve.acceptedPoints_eq_ite`). The loop over the pieces returns at a stop: its invariant
holds the delivery of the points found so far with the flag clear before a return, and the value
returned after it, the delivery of all the points, since the reference passes over the points after
the first call that sets the flag (`Ratpoints.Delivery.deliver_eq_of_prefix`); its verification
conditions are closed by lemmas in their shape. The loop of `Ratpoints.Sieve.sift` over the search
intervals returns at the first interval above `H` and at a stop: its invariant holds the delivery of
the points of the ranges done, range after range, which are those of the numerators in one of the
ranges, the ranges being increasing and strictly apart (`List.flatMap_filter_eq_filter_any`); the
sieve specs, made at the first interval that is neither below `-H` nor above `H`, are those of
`Ratpoints.Sieve.packedReads` from then on, and the store of the tables of rows fits the entries in
both branches, which a contract of its own also states without the class word and the ranges. The
contract of the run over the denominators, which calls `Ratpoints.Sieve.sift` with the class of
each denominator, is in `Ratpoints.Proof.Denominators`.
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
      SmallFits (decide (-rowBias ≤ w0 ∧ w0 + n ≤ rowBias - 2 * maxPrimeEven)) w0 (w0 + n) :=
  ⟨fun s hs ↦ h.2.1 s (List.mem_of_mem_take hs), by rw [h.2.2, List.map_take],
    smallFits_decide w0 n⟩

/-- What the chunked first stage of a piece of `n` bit arrays from the word number `w0` on needs of
the first `sp1` moduli and their reciprocals (`Ratpoints.Sieve.andRowsChunked_spec`), in the arm
that the test `1 < chunk ∧ chunk ≤ 16` of `Ratpoints.Sieve.siftPiece` chooses. -/
theorem chunk_le_and_fits_take {specs : List SieveSpec} {mgs : List Nat} {maskHigh : Nat}
    (hc : 1 < chunk ∧ chunk ≤ 16)
    (h : maskHigh < rbaLength ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p)) (sp1 : Nat)
    (w0 : Int) (n : Nat) :
    chunk ≤ 16 ∧ (∀ s ∈ specs.take sp1, s.Fits) ∧ mgs.take sp1 = (specs.take sp1).map (magic ·.p) ∧
      SmallFits (decide (-rowBias ≤ w0 ∧ w0 + n ≤ rowBias - 2 * maxPrimeEven)) w0 (w0 + n) :=
  ⟨hc.2, fits_take h sp1 w0 n⟩

/-- What the scan of a piece of `n` bit arrays from the word number `w0` on needs of the moduli and
their reciprocals after the first `sp1`, with the test `small` that `Ratpoints.Sieve.siftPiece`
computes. -/
theorem fits_drop {specs : List SieveSpec} {mgs : List Nat} {maskHigh : Nat}
    (h : maskHigh < rbaLength ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p)) (sp1 : Nat)
    (w0 : Int) (n : Nat) :
    (∀ s ∈ specs.drop sp1, s.Fits) ∧ mgs.drop sp1 = (specs.drop sp1).map (magic ·.p) ∧
      SmallFits (decide (-rowBias ≤ w0 ∧ w0 + n ≤ rowBias - 2 * maxPrimeEven)) w0 (w0 + n) :=
  ⟨fun s hs ↦ h.2.1 s (List.mem_of_mem_drop hs), by rw [h.2.2, List.map_drop],
    smallFits_decide w0 n⟩

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
    (w0 : Int) (n maskLow maskHigh : Nat) (r : Delivery σ) :
    ⦃ r.quit = false ∧ maskHigh < rbaLength ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ⦄
    siftPiece process w d b fl sp1 specs mgs checks cl w0 n maskLow maskHigh r
    ⦃ fun r' ↦ ∀ sfs : List (SieveSpec × (Int → Bool)), specs = sfs.map Prod.fst →
        (∀ sf ∈ sfs, sf.1.Reads sf.2) →
        r' = r.deliver process ((((List.range (n * rbaLength - maskLow - maskHigh)).map
          fun k : Nat ↦ rbaLength * w0 + maskLow + k).filter fun j ↦
            classBit cl.bits j && sfs.all (·.2 j)).flatMap
              fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ⦄ := by
  vcgen [siftPiece]
  all_goals first
    | exact ⟨‹r.quit = false ∧ _›.1, fits_drop ‹r.quit = false ∧ _›.2 sp1 w0 n⟩
    | exact chunk_le_and_fits_take ‹_› ‹r.quit = false ∧ _›.2 sp1 w0 n
    | exact fits_take ‹r.quit = false ∧ _›.2 sp1 w0 n
    | exact IsMasked.eq_deliver ‹_› (isMasked_clearHighBits_clearLowBits _ _
        ‹r.quit = false ∧ maskHigh < rbaLength ∧ _›.2.1) ‹_› ‹_› ‹_›
    | exact IsMasked.eq_deliver ‹_› (isMasked_clearLowBits _ _ (Decidable.of_not_not ‹_›)) ‹_› ‹_›
        ‹_›
    | exact IsMasked.eq_deliver ‹_› (isMasked_clearHighBits _ (Decidable.of_not_not ‹_›)
        ‹r.quit = false ∧ maskHigh < rbaLength ∧ _›.2.1) ‹_› ‹_› ‹_›
    | exact IsMasked.eq_deliver ‹_› (isMasked_self _ _ (Decidable.of_not_not ‹_›)
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
  rw [Int.mul_add, Int.mul_one]
  lia [Int.emod_def high rbaLength, Int.emod_nonneg high (Int.ne_of_gt natCast_rbaLength_pos)]

-- The high mask of `Ratpoints.Sieve.siftBits` on the piece that ends at the word number `w1`: the
-- number of its bits above `high`, `0` for every piece but the last.
private theorem ite_eq_toNat_mul_sub {high w1 : Int} (hw1 : w1 ≤ high / rbaLength + 1) :
    (if w1 = high / rbaLength + 1 then rbaLength - 1 - (high % rbaLength).toNat else 0) =
      (rbaLength * w1 - 1 - high).toNat := by
  split
  · subst_vars
    exact sub_toNat_emod_eq_toNat_mul_sub high
  · have hR := natCast_rbaLength_pos
    lia [Int.mul_ediv_self_le (x := high) (Int.ne_of_gt hR),
      Int.mul_le_mul_of_nonneg_left (show w1 ≤ high / rbaLength by lia) (Int.le_of_lt hR)]

/-- The bits from that of `low` up to the word number `w0` that lie in `low, …, high` and pass
`keep`, with their points `g`: what the pieces of `Ratpoints.Sieve.siftBits` before `w0` give. -/
theorem flatMap_filter_range_append {g : Int → List (Int × Int × Int)} {keep : Int → Bool}
    {low high : Int} {r mH : Nat} {w0 w1' : Int} (hle : low / rbaLength ≤ w0) (hr : w1' = w0 + r)
    (hmH : mH = (rbaLength * w1' - 1 - high).toNat) :
    ((((List.range ((w0 - low / rbaLength).toNat * rbaLength)).map
      fun k : Nat ↦ rbaLength * (low / rbaLength) + k).filter
        fun a ↦ decide (low ≤ a ∧ a ≤ high)).filter keep).flatMap g ++
      (((List.range (r * rbaLength - (if w0 = low / rbaLength then
        (low - rbaLength * (low / rbaLength)).toNat else 0) - mH)).map fun k : Nat ↦
          rbaLength * w0 + ((if w0 = low / rbaLength then
            (low - rbaLength * (low / rbaLength)).toNat else 0 : Nat) : Int) + k).filter
              keep).flatMap g =
      ((((List.range ((w1' - low / rbaLength).toNat * rbaLength)).map
        fun k : Nat ↦ rbaLength * (low / rbaLength) + k).filter
          fun a ↦ decide (low ≤ a ∧ a ≤ high)).filter keep).flatMap g := by
  have hm : (rbaLength : Int) * w1' - 1 - high =
      rbaLength * w0 + ((r * rbaLength : Nat) : Int) - 1 - high := by
    rw [hr, Int.mul_add, Int.natCast_mul, Int.mul_comm (r : Int)]
  rw [ite_eq_toNat_sub hle, hmH, hm, ← List.filter_map_range_eq_map_range']
  have hl : (w1' - low / rbaLength).toNat = (w0 - low / rbaLength).toNat + r := by lia
  have hmap : (List.range (r * rbaLength)).map ((fun k : Nat ↦ rbaLength * (low / rbaLength) + k) ∘
        fun x ↦ (w0 - low / rbaLength).toNat * rbaLength + x) =
      (List.range (r * rbaLength)).map fun k : Nat ↦ rbaLength * w0 + k :=
    List.map_congr_left fun k _ ↦ by grind
  rw [← List.flatMap_append, ← List.filter_append, ← List.filter_append, hl, Nat.add_mul,
    List.range_add, List.map_append, List.map_map, hmap]

/-- The bits up to the word number `w0` come first among those up to `w0' ≥ w0`. -/
theorem flatMap_filter_range_prefix (g : Int → List (Int × Int × Int)) (keep : Int → Bool)
    (low high : Int) {w0 w0' : Int} (h : w0 ≤ w0') :
    ((((List.range ((w0 - low / rbaLength).toNat * rbaLength)).map
      fun k : Nat ↦ rbaLength * (low / rbaLength) + k).filter
        fun a ↦ decide (low ≤ a ∧ a ≤ high)).filter keep).flatMap g <+:
      ((((List.range ((w0' - low / rbaLength).toNat * rbaLength)).map
        fun k : Nat ↦ rbaLength * (low / rbaLength) + k).filter
          fun a ↦ decide (low ≤ a ∧ a ≤ high)).filter keep).flatMap g := by
  obtain ⟨l, hl⟩ := List.range_prefix_range (Nat.mul_le_mul_right rbaLength
    (show (w0 - low / rbaLength).toNat ≤ (w0' - low / rbaLength).toNat by lia))
  exact ⟨_, by rw [← hl, List.map_append, List.filter_append, List.filter_append,
    List.flatMap_append]⟩

/-- The bits from that of `low` up to the word number one past that of `high` that lie in
`low, …, high` are the bits `low, …, high`. -/
theorem flatMap_filter_range_eq (g : Int → List (Int × Int × Int)) (keep : Int → Bool)
    {low high : Int} (hlh : low / rbaLength ≤ high / rbaLength + 1) :
    ((((List.range ((high / rbaLength + 1 - low / rbaLength).toNat * rbaLength)).map
      fun k : Nat ↦ rbaLength * (low / rbaLength) + k).filter
        fun a ↦ decide (low ≤ a ∧ a ≤ high)).filter keep).flatMap g =
      (((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter keep).flatMap g := by
  have hR := natCast_rbaLength_pos
  have hL := Int.mul_ediv_self_le (x := low) (Int.ne_of_gt hR)
  have := Int.lt_mul_ediv_self_add (x := high) hR
  have hM : (((high / rbaLength + 1 - low / rbaLength).toNat * rbaLength : Nat) : Int) =
      rbaLength * (high / rbaLength) + rbaLength - rbaLength * (low / rbaLength) := by
    rw [Int.natCast_mul, Int.toNat_of_nonneg (by lia)]
    grind
  rw [List.filter_map_range_eq_map_range_of_le hL (by lia)]

/-- The invariant of the loop of `Ratpoints.Sieve.siftBits` over the pieces, for the bits from
`low` to `high`, a test `keep` of the bits and their points `g`, from the delivery `r0`, at the
exit of the loop or not: the bit arrays from that of `low` up to the word number `w0` are done, the
callback has not stopped the search, and the delivery is that of the points of their bits that lie
in `low, …, high` and pass `keep`. -/
structure SiftInvariant (g : Int → List (Int × Int × Int)) (keep : Int → Bool) (low high : Int)
    (r0 : Delivery σ) (exit : Bool) (range : Nat) (w0 w1 : Int) (r : Delivery σ) :
    Prop where
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
  /-- The delivery is that of the points of the bits of the bit arrays from that of `low` up to `w0`
  that lie in `low, …, high` and pass `keep`, in increasing order. -/
  eq_deliver : r = r0.deliver process (((((List.range ((w0 - low / rbaLength).toNat *
    rbaLength)).map fun k : Nat ↦ rbaLength * (low / rbaLength) + k).filter
      fun a ↦ decide (low ≤ a ∧ a ≤ high)).filter keep).flatMap g)

/-- `Ratpoints.Sieve.SiftInvariant` as the invariant of the `while` loop of
`Ratpoints.Sieve.siftBits`, with the value of a return at a stop, the delivery of the points of all
the bits `low, …, high` that pass `keep`. -/
def SiftWhileInvariant (g : Int → List (Int × Int × Int)) (keep : Int → Bool) (low high : Int)
    (r0 : Delivery σ) :
    Std.WP.WhileInvariant (Option (Delivery σ) × Delivery σ × Nat × Int × Int) Prop :=
  .mk fun exit s ↦ s.1 = none ∧
    SiftInvariant process g keep low high r0 exit s.2.2.1 s.2.2.2.1 s.2.2.2.2 s.2.1 ∨
      exit = true ∧ s.1 = some (r0.deliver process
        ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter keep).flatMap g))

section

variable {process} {g : Int → List (Int × Int × Int)} {keep : Int → Bool} {low high : Int}
  {r0 r : Delivery σ}

theorem siftInvariant_empty (g : Int → List (Int × Int × Int)) (keep : Int → Bool)
    (h : low ≤ high) {A : Nat} (hA : 1 ≤ A) (hr : r0.quit = false) :
    SiftInvariant process g keep low high r0 false A (low / rbaLength) (low / rbaLength + A) r0 :=
  ⟨Int.le_refl _, by lia [Int.ediv_le_ediv natCast_rbaLength_pos h], nofun, rfl, hA, hr, by simp⟩

/-- A piece of `rr ≥ 1` bit arrays from the word number `w0` on, which ends at
`w1' ≤ high / rbaLength + 1`, with the low mask of `Ratpoints.Sieve.siftBits` and a high mask `mH`,
the number of its bits above `high`, when the callback does not stop the search in it. -/
theorem SiftInvariant.append {range rr mH : Nat} {w0 w1 w1' : Int} {r' : Delivery σ}
    (h : SiftInvariant process g keep low high r0 false range w0 w1 r) (hr : w1' = w0 + rr)
    (hr1 : 1 ≤ rr) (hw1' : w1' ≤ high / rbaLength + 1)
    (hmH : mH = (rbaLength * w1' - 1 - high).toNat)
    (hpts : r' = r.deliver process ((((List.range (rr * rbaLength - (if w0 = low / rbaLength then
      (low - rbaLength * (low / rbaLength)).toNat else 0) - mH)).map fun k : Nat ↦
        rbaLength * w0 + ((if w0 = low / rbaLength then
          (low - rbaLength * (low / rbaLength)).toNat else 0 : Nat) : Int) + k).filter keep).flatMap
            g)) (hq : ¬r'.quit = true) :
    SiftInvariant process g keep low high r0 false rr w1' (w1' + rr) r' :=
  ⟨by lia [h.le_w0], hw1', nofun, rfl, hr1, Bool.eq_false_iff.mpr hq, by
    rw [hpts, h.eq_deliver, ← Delivery.deliver_append, flatMap_filter_range_append h.le_w0 hr hmH]⟩

/-- A piece that ends at `w1' ≤ high / rbaLength + 1`, when the callback stops the search in it: the
delivery is that of all the bits `low, …, high` that pass `keep`. -/
theorem SiftInvariant.eq_deliver_of_quit {range rr mH : Nat} {w0 w1 w1' : Int} {r' : Delivery σ}
    (h : SiftInvariant process g keep low high r0 false range w0 w1 r) (hr : w1' = w0 + rr)
    (hw1' : w1' ≤ high / rbaLength + 1)
    (hmH : mH = (rbaLength * w1' - 1 - high).toNat)
    (hpts : r' = r.deliver process ((((List.range (rr * rbaLength - (if w0 = low / rbaLength then
      (low - rbaLength * (low / rbaLength)).toNat else 0) - mH)).map fun k : Nat ↦
        rbaLength * w0 + ((if w0 = low / rbaLength then
          (low - rbaLength * (low / rbaLength)).toNat else 0 : Nat) : Int) + k).filter keep).flatMap
            g)) (hq : r'.quit = true) :
    r' = r0.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      keep).flatMap g) := by
  rw [hpts, h.eq_deliver, ← Delivery.deliver_append,
    flatMap_filter_range_append h.le_w0 hr hmH] at hq ⊢
  rw [← flatMap_filter_range_eq g keep (by lia [h.le_w0, h.w0_le])]
  exact (Delivery.deliver_eq_of_prefix process (flatMap_filter_range_prefix g keep low high hw1')
    hq).symm

/-- The pieces advance: the measure `high / rbaLength + 1 - w0` of the loop of
`Ratpoints.Sieve.siftBits` decreases from one piece to the next. -/
theorem SiftInvariant.toNat_sub_lt {range : Nat} {w0 w1 : Int}
    (h : SiftInvariant process g keep low high r0 false range w0 w1 r)
    (hw0 : w0 < high / rbaLength + 1) :
    (high / rbaLength + 1 - w1).toNat < (high / rbaLength + 1 - w0).toNat := by
  lia [h.w1_eq, h.one_le_range]

/-- The loop of `Ratpoints.Sieve.siftBits` ends at the word number one past that of `high`. -/
theorem SiftInvariant.exit_of_not_lt {range : Nat} {w0 w1 : Int}
    (h : SiftInvariant process g keep low high r0 false range w0 w1 r)
    (hw0 : ¬w0 < high / rbaLength + 1) :
    SiftInvariant process g keep low high r0 true range w0 w1 r :=
  ⟨h.le_w0, h.w0_le, fun _ ↦ Int.le_antisymm h.w0_le (Int.not_lt.mp hw0), h.w1_eq,
    h.one_le_range, h.quit_eq_false, h.eq_deliver⟩

/-- A middle piece, which ends at the word number `w1 ≤ high / rbaLength + 1`, when the callback
does not stop the search in it, in the shape of the verification condition. -/
theorem SiftInvariant.append_of_not_lt {range mb : Nat} {w0 w1 : Int} {o : Option (Delivery σ)}
    {r' : Delivery σ} (hm : (high / rbaLength + 1 - w0).toNat = mb ∧ o = none ∧
      SiftInvariant process g keep low high r0 false range w0 w1 r)
    (hlt : w0 < high / rbaLength + 1) (hw : ¬high / rbaLength + 1 < w1)
    (hpts : r' = r.deliver process ((((List.range (range * rbaLength - (if w0 = low / rbaLength then
      (low - rbaLength * (low / rbaLength)).toNat else 0) - (if w1 = high / rbaLength + 1 then
        rbaLength - 1 - (high % rbaLength).toNat else 0))).map fun k : Nat ↦
          rbaLength * w0 + ((if w0 = low / rbaLength then
            (low - rbaLength * (low / rbaLength)).toNat else 0 : Nat) : Int) + k).filter
              keep).flatMap g)) (hq : ¬r'.quit = true) :
    (high / rbaLength + 1 - w1).toNat < mb ∧
      SiftInvariant process g keep low high r0 false range w1 (w1 + range) r' := by
  obtain ⟨rfl, -, h⟩ := hm
  exact ⟨h.toNat_sub_lt hlt, h.append h.w1_eq h.one_le_range (by lia)
    (ite_eq_toNat_mul_sub (by lia)) hpts hq⟩

/-- The last piece, which ends at the word number `high / rbaLength + 1`, when the callback does not
stop the search in it, in the shape of the verification condition. -/
theorem SiftInvariant.append_of_lt {range mb : Nat} {w0 w1 : Int} {o : Option (Delivery σ)}
    {r' : Delivery σ} (hm : (high / rbaLength + 1 - w0).toNat = mb ∧ o = none ∧
      SiftInvariant process g keep low high r0 false range w0 w1 r)
    (hlt : w0 < high / rbaLength + 1)
    (hpts : r' = r.deliver process ((((List.range ((high / rbaLength + 1 - w0).toNat * rbaLength -
      (if w0 = low / rbaLength then (low - rbaLength * (low / rbaLength)).toNat else 0) -
        (rbaLength - 1 - (high % rbaLength).toNat))).map fun k : Nat ↦
          rbaLength * w0 + ((if w0 = low / rbaLength then
            (low - rbaLength * (low / rbaLength)).toNat else 0 : Nat) : Int) + k).filter
              keep).flatMap g)) (hq : ¬r'.quit = true) :
    (high / rbaLength + 1 - (high / rbaLength + 1)).toNat < mb ∧
      SiftInvariant process g keep low high r0 false (high / rbaLength + 1 - w0).toNat
        (high / rbaLength + 1) (high / rbaLength + 1 + (high / rbaLength + 1 - w0).toNat) r' := by
  obtain ⟨rfl, -, h⟩ := hm
  exact ⟨by lia, h.append (by lia) (by lia) (Int.le_refl _) (sub_toNat_emod_eq_toNat_mul_sub high)
    hpts hq⟩

/-- A middle piece, when the callback stops the search in it, in the shape of the verification
condition: the delivery is that of all the bits `low, …, high` that pass `keep`. -/
theorem SiftInvariant.eq_deliver_of_quit_of_not_lt {range mb : Nat} {w0 w1 : Int}
    {o : Option (Delivery σ)} {r' : Delivery σ} (hm : (high / rbaLength + 1 - w0).toNat = mb ∧
      o = none ∧ SiftInvariant process g keep low high r0 false range w0 w1 r)
    (hw : ¬high / rbaLength + 1 < w1)
    (hpts : r' = r.deliver process ((((List.range (range * rbaLength - (if w0 = low / rbaLength then
      (low - rbaLength * (low / rbaLength)).toNat else 0) - (if w1 = high / rbaLength + 1 then
        rbaLength - 1 - (high % rbaLength).toNat else 0))).map fun k : Nat ↦
          rbaLength * w0 + ((if w0 = low / rbaLength then
            (low - rbaLength * (low / rbaLength)).toNat else 0 : Nat) : Int) + k).filter
              keep).flatMap g)) (hq : r'.quit = true) :
    r' = r0.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      keep).flatMap g) :=
  hm.2.2.eq_deliver_of_quit hm.2.2.w1_eq (by lia) (ite_eq_toNat_mul_sub (by lia)) hpts hq

/-- The last piece, when the callback stops the search in it, in the shape of the verification
condition: the delivery is that of all the bits `low, …, high` that pass `keep`. -/
theorem SiftInvariant.eq_deliver_of_quit_of_lt {range mb : Nat} {w0 w1 : Int}
    {o : Option (Delivery σ)} {r' : Delivery σ} (hm : (high / rbaLength + 1 - w0).toNat = mb ∧
      o = none ∧ SiftInvariant process g keep low high r0 false range w0 w1 r)
    (hlt : w0 < high / rbaLength + 1)
    (hpts : r' = r.deliver process ((((List.range ((high / rbaLength + 1 - w0).toNat * rbaLength -
      (if w0 = low / rbaLength then (low - rbaLength * (low / rbaLength)).toNat else 0) -
        (rbaLength - 1 - (high % rbaLength).toNat))).map fun k : Nat ↦
          rbaLength * w0 + ((if w0 = low / rbaLength then
            (low - rbaLength * (low / rbaLength)).toNat else 0 : Nat) : Int) + k).filter
              keep).flatMap g)) (hq : r'.quit = true) :
    r' = r0.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      keep).flatMap g) :=
  hm.2.2.eq_deliver_of_quit (by lia) (Int.le_refl _) (sub_toNat_emod_eq_toNat_mul_sub high) hpts hq

/-- What the piece of the verification condition needs of the invariant: the callback has not
stopped the search. -/
theorem SiftInvariant.quit_eq_false_and {range mb mH : Nat} {w0 w1 : Int} {o : Option (Delivery σ)}
    {P : Prop} (hm : (high / rbaLength + 1 - w0).toNat = mb ∧ o = none ∧
      SiftInvariant process g keep low high r0 false range w0 w1 r) (hP : P)
    (hmH : mH < rbaLength) :
    r.quit = false ∧ mH < rbaLength ∧ P ∧ True :=
  ⟨hm.2.2.quit_eq_false, hmH, hP, trivial⟩

/-- An empty interval of bits delivers nothing. -/
theorem eq_deliver_of_not_le (h : ¬low ≤ high) (r : Delivery σ) :
    r = r.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      keep).flatMap g) := by
  rw [Int.toNat_of_nonpos (z := high + 1 - low) (by lia)]
  rfl

/-- At the exit of the loop of `Ratpoints.Sieve.siftBits`, the delivery is that of the points of the
bits `low, …, high` that pass `keep`. -/
theorem SiftInvariant.eq_deliver_flatMap_filter {range : Nat} {w0 w1 : Int}
    (h : SiftInvariant process g keep low high r0 true range w0 w1 r) :
    r = r0.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦ low + k).filter
      keep).flatMap g) := by
  rw [h.eq_deliver, h.eq_of_exit rfl, flatMap_filter_range_eq g keep (by lia [h.le_w0, h.w0_le])]

end

-- The contract of `Ratpoints.Sieve.siftBits` for the reading list `sfs` of its moduli.
open Std.WP Lean.Order in
private theorem siftBits_spec_reads (w : Thunk (List Int)) (d b A : Nat) (fl : CheckFlags)
    (sp1 : Nat) (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec))
    (cl : NumClass) (low high : Int) (r : Delivery σ) {sfs : List (SieveSpec × (Int → Bool))}
    (hA : 1 ≤ A) (hfits : ∀ s ∈ specs, s.Fits) (hmg : mgs = specs.map (magic ·.p))
    (hspecs : specs = sfs.map Prod.fst) (hsfs : ∀ sf ∈ sfs, sf.1.Reads sf.2) :
    ⦃ r.quit = false ⦄ siftBits process w d b A fl sp1 specs mgs checks cl low high r
    ⦃ fun r' ↦ r' = r.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦
        low + k).filter fun j ↦ classBit cl.bits j && sfs.all (·.2 j)).flatMap
          fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ⦄ := by
  vcgen [siftBits] invariants
  · SiftWhileInvariant process (fun j ↦ acceptedPoints w d b fl checks (cl.numerator j))
      (fun j ↦ classBit cl.bits j && sfs.all (·.2 j)) low high r
  · .ofMeasure fun s ↦ (high / rbaLength + 1 - s.2.2.2.1).toNat
  all_goals (subst_vars; try simp only [SiftWhileInvariant, WhileInvariant.mk_apply,
    Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure,
    meet_prop_eq_and, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq] at *)
  all_goals first
    | exact SiftInvariant.quit_eq_false_and ‹_› hfits (by (try split) <;> lia [rbaLength_pos])
    | have hall := ‹∀ _ : List (SieveSpec × (Int → Bool)), _ → _ → _›
      first
        | have : ¬high / rbaLength + 1 < _ := ‹_›
          first
            | exact SiftInvariant.append_of_not_lt ‹_› ‹_› ‹_› (hall sfs rfl hsfs) ‹_›
            | exact SiftInvariant.eq_deliver_of_quit_of_not_lt ‹_› ‹_› (hall sfs rfl hsfs) ‹_›
        | exact SiftInvariant.append_of_lt ‹_› ‹_› (hall sfs rfl hsfs) ‹_›
        | exact SiftInvariant.eq_deliver_of_quit_of_lt ‹_› ‹_› (hall sfs rfl hsfs) ‹_›
    | grind [siftInvariant_empty, SiftInvariant.exit_of_not_lt, eq_deliver_of_not_le,
        SiftInvariant.eq_deliver_flatMap_filter]

/-- The bits from `low` to `high` in pieces of `A ≥ 1` bit arrays, with the moduli `specs` and their
reciprocals, deliver the points of the numerators of the bits that pass the class word of `cl` and
the tests `sf.2` that the rows of the moduli read (`Ratpoints.Sieve.SieveSpec.Reads`), quantified in
the postcondition since the program does not mention them; an empty interval delivers none; the loop
over the pieces ends by the measure `high / rbaLength + 1 - w0`, since every piece has at least one
bit array, or at a stop. -/
@[spec]
theorem siftBits_spec (w : Thunk (List Int)) (d b A : Nat) (fl : CheckFlags) (sp1 : Nat)
    (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass)
    (low high : Int) (r : Delivery σ) :
    ⦃ r.quit = false ∧ 1 ≤ A ∧ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ⦄
    siftBits process w d b A fl sp1 specs mgs checks cl low high r
    ⦃ fun r' ↦ ∀ sfs : List (SieveSpec × (Int → Bool)), specs = sfs.map Prod.fst →
        (∀ sf ∈ sfs, sf.1.Reads sf.2) →
        r' = r.deliver process ((((List.range (high + 1 - low).toNat).map fun k : Nat ↦
          low + k).filter fun j ↦ classBit cl.bits j && sfs.all (·.2 j)).flatMap
            fun j ↦ acceptedPoints w d b fl checks (cl.numerator j)) ⦄ :=
  ⟨fun ⟨hr, hA, hfits, hmg⟩ _ hspecs hsfs ↦ (siftBits_spec_reads process w d b A fl sp1 specs mgs
    checks cl low high r hA hfits hmg hspecs hsfs).le_wp hr⟩

/-! ### One denominator -/

/-- The rows of the sieve entries `es` for the denominator `b` in the packing of the class `cl`,
with the row offsets from position `pos` of `offsets` on, as `Ratpoints.Sieve.setRows` and
`Ratpoints.Sieve.buildRows` make them: the closed forms of the rows of the residues
`b dinv[k] mod p` (`Ratpoints.Sieve.closedRow`), with the start `0` and the end `p`, each with the
test of the bits that it reads (`Ratpoints.Sieve.SieveSpec.Reads`): whether the row of `b` admits
the numerator of the bit (`Ratpoints.Sieve.SieveEntry.reads_row`). -/
def packedReads (es : List SieveEntry) (b : Nat) (cl : NumClass) (offsets : Array Nat) (pos : Nat) :
    List (SieveSpec × (Int → Bool)) :=
  es.mapIdx fun n e ↦ (⟨e.p, offsets[pos + n]!, closedRow e.admits e.p (b * e.dinv[cl.k]! % e.p),
    0, e.p⟩, fun j ↦ e.admits b (cl.numerator j))

/-- The sieve specs that `Ratpoints.Sieve.buildRows` completes for the residues `b dinv[k] mod p`
of the entries (`Ratpoints.Sieve.buildRows_setRows_map_spec`), the residues that
`Ratpoints.Sieve.fillBpList` gives (`Ratpoints.Sieve.fillBpList_eq_map`), at the offsets of the
class from its position `pos` on, are those of `Ratpoints.Sieve.packedReads`. -/
theorem mapIdx_eq_map_fst_packedReads (es : List SieveEntry) (b : Nat) {cl : NumClass} {pos : Nat}
    (hpos : cl.offset = some pos) (offsets : Array Nat) :
    es.mapIdx (fun n e ↦ (⟨e.p, offsets[cl.offset.getD 0 + n]!,
      closedRow e.admits e.p (b * e.dinv[cl.k]! % e.p), 0, e.p⟩ : SieveSpec)) =
      (packedReads es b cl offsets pos).map Prod.fst :=
  List.ext_getElem (by simp [packedReads]) fun n _ _ ↦ by simp [packedReads, hpos]

-- The specs of `Ratpoints.Sieve.packedReads` fit, for entries packed for the class at their
-- offsets.
private theorem fits_of_mem_packedReads {es : List SieveEntry} {b : Nat} {cl : NumClass}
    {offsets : Array Nat} {pos : Nat}
    (hoff : ∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!) :
    ∀ s ∈ (packedReads es b cl offsets pos).map Prod.fst, s.Fits := by
  intro s hs
  obtain ⟨sf, hsf, rfl⟩ := List.mem_map.mp hs
  obtain ⟨n, hn, rfl⟩ := List.mem_mapIdx.mp hsf
  exact (hoff n hn).fits _ _

-- The reciprocals of the moduli of the entries are those of the specs of
-- `Ratpoints.Sieve.packedReads`.
private theorem map_magic_packedReads (es : List SieveEntry) (b : Nat) (cl : NumClass)
    (offsets : Array Nat) (pos : Nat) :
    es.map (magic ·.p) = ((packedReads es b cl offsets pos).map Prod.fst).map (magic ·.p) :=
  List.ext_getElem (by simp [packedReads]) fun n _ _ ↦ by simp [packedReads]

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
    (Nat.mul_mul_mod_mod_of_mul_mod_eq_one _ h.dinv_mul_mod)

-- The tests of `Ratpoints.Sieve.packedReads` pass the bit `j` exactly when its numerator survives
-- the entries.
private theorem all_packedReads (es : List SieveEntry) (b : Nat) (cl : NumClass)
    (offsets : Array Nat) (pos : Nat) (j : Int) :
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

/-- The numerators `-H, …, H` are increasing. -/
theorem _root_.Ratpoints.BruteForce.pairwise_lt_numerators (H : Nat) :
    (numerators H).Pairwise (· < ·) :=
  List.pairwise_map.mpr (List.pairwise_lt_range.imp fun h ↦ by lia)

/-- For the points of `Ratpoints.Sieve.acceptedPoints` with the thunks of the products and of what
the third stage needs of the entries `es3` of the shape of
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, with the reciprocals of their moduli, for a denominator
`0 < b < 2 ^ 63`, `H < 2 ^ 63` and the flags `fl`, the numerators `-H, …, H` that pass a test `p`
and survive the entries of the first two stages give the points of the check with the flags
(`Ratpoints.Sieve.checkNumWith`) of the numerators that pass `p` and survive the entries of all
three stages (`Ratpoints.Sieve.acceptedPoints_eq_ite`). -/
theorem flatMap_acceptedPoints_eq_flatMap_checkNumWith {c : List Int} {d b : Nat} {fl : CheckFlags}
    {p : Int → Bool} {entries es3 : List SieveEntry} (hes : ∀ e ∈ es3, e.IsPrimeEntry) {H : Nat}
    (hb : 0 < b) (hb63 : b < 2 ^ 63) (hH : H < 2 ^ 63) :
    ((numerators H).filter fun a ↦ p a && survives entries b a).flatMap
        (acceptedPoints (.mk fun _ ↦ scaledCoeffs c d b) d b fl
          (.mk fun _ ↦ fillChecks b H es3 (es3.map fun e ↦ magic e.p))) =
      ((numerators H).filter fun a ↦ p a && survives (entries ++ es3) b a).flatMap
        (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl) := by
  rw [List.flatMap, List.map_congr_left fun a ha ↦ acceptedPoints_eq_ite hes rfl _ _ fl hb hb63
      (natAbs_le_of_mem_numerators (List.mem_filter.mp ha).1) hH, ← List.flatMap,
    ← List.flatMap_filter, List.filter_filter]
  simp only [survives_append, Bool.and_comm (survives es3 b _), Bool.and_assoc]
  rfl

/-- The bits from `⌈(-H - a₀) / 2 ^ k⌉` to `⌊(H - a₀) / 2 ^ k⌋` of the packing of a class `cl` of
the class word `w` (`Ratpoints.Sieve.NumClass.Packs`) that pass a test of the numerators of the
bits give the points of the numerators `-H, …, H` that pass `w` and the test: the numerators of the
bits are those of the class among `-H, …, H`
(`Ratpoints.Sieve.NumClass.WF.map_range_numerator_eq_filter_numerators`), the pattern of the class
lets the numerator of a bit through exactly when `w` does
(`Ratpoints.Sieve.NumClass.Packs.classBit_bits`), and `w` lets nothing off the class through. -/
theorem flatMap_filter_bits_eq {cl : NumClass} {w : UInt64} (hcl : cl.Packs w) {H : Nat}
    {lo hi : Int} (hlo : lo = -((cl.a0 + H : Int) / 2 ^ cl.k))
    (hhi : hi = ((H : Int) - cl.a0) / 2 ^ cl.k) {test t : Int → Bool}
    (htest : ∀ j, test j = t (cl.numerator j)) (g : Int → List (Int × Int × Int)) :
    (((List.range (hi + 1 - lo).toNat).map fun k : Nat ↦ lo + k).filter
        fun j ↦ classBit cl.bits j && test j).flatMap (fun j ↦ g (cl.numerator j)) =
      ((numerators H).filter fun a ↦ classBit w a && t a).flatMap g := by
  rw [← List.flatMap_map, ← hcl.filter_filter_emod,
    ← hcl.toWF.map_range_numerator_eq_filter_numerators hlo hhi]
  simp only [List.filter_map, List.map_map]
  congr 2
  exact List.filter_congr fun j _ ↦ by simp [hcl.classBit_bits, htest]

-- The rows of the sieve specs of the denominator that `Ratpoints.Sieve.setRows` and
-- `Ratpoints.Sieve.buildRows` make, as a value for the contract of `Ratpoints.Sieve.sift`.
private theorem buildRows_value (missing : Bool) (es : List SieveEntry) (bp : List Nat)
    (specs : List SieveSpec) (store : RowStore) :
    ⦃ True ⦄ buildRows missing es bp specs store
    ⦃ fun r ↦ r = Id.run (buildRows missing es bp specs store) ⦄ :=
  ⟨fun _ ↦ rfl⟩

/-- The sieve specs of the denominator `b` that `Ratpoints.Sieve.setRows` makes and
`Ratpoints.Sieve.buildRows` completes, for the residues `b dinv[k] mod p` of the entries, the class
`cl` with its row offsets from position `pos` on and a store that fits the entries
(`Ratpoints.Sieve.RowStore.Fits`), are those of `Ratpoints.Sieve.packedReads`. -/
theorem eq_map_fst_packedReads_of_eq_run_buildRows {store store' : RowStore}
    {es : List SieveEntry} (hs : store.Fits es) {b : Nat} {cl : NumClass} {pos : Nat}
    (hpos : cl.offset = some pos) {offsets : Array Nat} {specs : List SieveSpec}
    (hr : (specs, store') = Id.run (buildRows
      (setRows store es (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets).2 es
      (es.map fun e ↦ b * e.dinv[cl.k]! % e.p)
      (setRows store es (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets).1 store)) :
    specs = (packedReads es b cl offsets pos).map Prod.fst :=
  ((hs.buildRows_setRows (fun e he ↦ Nat.mod_lt _ (hs.pos e he)) hr).1).trans
    (mapIdx_eq_map_fst_packedReads es b hpos offsets)

-- For a numerator `|a| ≤ H`, the range `lo, …, hi` within `-H, …, H` holds `a` exactly when the
-- range does.
private theorem decide_max_le_and_le_min {H : Nat} {a : Int} (ha : a.natAbs ≤ H) (lo hi : Int) :
    decide (max lo (-H) ≤ a ∧ a ≤ min hi H) = decide (lo ≤ a ∧ a ≤ hi) :=
  decide_eq_decide.mpr (by lia)

/-- The bits of a search interval with the bounds `bd`, which give the range `lo, …, hi` of the
numerators (`Ratpoints.Sieve.IntervalBounds.Represents`), when `Ratpoints.Sieve.intervalBits` gives
neither the code `1` nor the code `2`, in the packing of a class `cl` of the class word `w`, with
the tests that the rows of `Ratpoints.Sieve.packedReads` read and the points of the check of
`Ratpoints.Sieve.acceptedPoints`, give the points of the check with the flags
(`Ratpoints.Sieve.checkNumWith`) of the numerators `-H, …, H` in `lo, …, hi` that pass `w` and
survive the entries of all three stages. -/
theorem flatMap_filter_intervalBits_eq {c : List Int} {d b H : Nat} {fl : CheckFlags}
    {es es3 : List SieveEntry} (hes : ∀ e ∈ es3, e.IsPrimeEntry) {w : UInt64} {cl : NumClass}
    (hcl : cl.Packs w) {offsets : Array Nat} {pos : Nat} {bd : IntervalBounds} {lo hi : Int}
    (hrep : bd.Represents b H lo hi) (h1 : (intervalBits b.toInt64 bd H.toInt64 cl).1 ≠ 1)
    (h2 : (intervalBits b.toInt64 bd H.toInt64 cl).1 ≠ 2) (hb : 0 < b) (hb63 : b < 2 ^ 63)
    (hH : H < 2 ^ 63) :
    (((List.range ((intervalBits b.toInt64 bd H.toInt64 cl).2.2.toInt + 1 -
      (intervalBits b.toInt64 bd H.toInt64 cl).2.1.toInt).toNat).map fun k : Nat ↦
        (intervalBits b.toInt64 bd H.toInt64 cl).2.1.toInt + k).filter fun j ↦
          classBit cl.bits j && (packedReads es b cl offsets pos).all (·.2 j)).flatMap
      (fun j ↦ acceptedPoints (.mk fun _ ↦ scaledCoeffs c d b) d b fl
        (.mk fun _ ↦ fillChecks b H es3 (es3.map fun e ↦ magic e.p)) (cl.numerator j)) =
      ((numerators H).filter fun a ↦ decide (lo ≤ a ∧ a ≤ hi) &&
        (classBit w a && survives (es ++ es3) b a)).flatMap
          (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl) := by
  obtain ⟨hl, hh⟩ := hrep.bits cl hcl.toWF h1 h2
  rw [hl, hh, cl.map_range_eq_filter_map_range (H := H) (by lia) (by lia), List.filter_filter,
    List.filter_congr fun j _ ↦ by
      rw [all_packedReads, Bool.and_assoc, Bool.and_comm (survives _ _ _)],
    flatMap_filter_bits_eq hcl (H := H) rfl rfl
      (t := fun a ↦ decide (max lo (-H) ≤ a ∧ a ≤ min hi H) && survives es b a) fun _ ↦ rfl,
    List.filter_congr fun a ha ↦ by
      rw [decide_max_le_and_le_min (natAbs_le_of_mem_numerators ha), ← Bool.and_assoc],
    flatMap_acceptedPoints_eq_flatMap_checkNumWith hes hb hb63 hH]
  exact congrArg (List.flatMap _) (List.filter_congr fun a _ ↦ by
    rw [Bool.and_comm (classBit w a), Bool.and_assoc])

/-- The invariant of the loop of `Ratpoints.Sieve.sift` over the bounds of the search intervals,
from the delivery `r0`, after the first `k` intervals, for the ranges `rs` of the numerators that
they give, the increasing list `l` of the numerators, their test `q` and their points `g`: the
callback has not stopped the search, the store of the tables of rows fits the sieve entries `es`,
the sieve specs are `specs0` once they are made (`doSetup` false), and the delivery is that of the
points of the numerators of `l` that pass `q`, range after range, for the first `k` ranges. -/
structure SiftIntervalsInvariant (l : List Int) (q : Int → Bool) (g : Int → List (Int × Int × Int))
    (es : List SieveEntry) (specs0 : List SieveSpec) (rs : List (Int × Int)) (r0 : Delivery σ)
    (k : Nat) (r : Delivery σ) (store : RowStore) (doSetup : Bool) (specs : List SieveSpec) :
    Prop where
  /-- The callback has not stopped the search. -/
  quit_eq_false : r.quit = false
  /-- The store fits the sieve entries of the first two stages. -/
  fits : store.Fits es
  /-- The sieve specs, once made. -/
  specs_eq : doSetup = false → specs = specs0
  /-- The delivery is that of the points of the first `k` ranges. -/
  eq_deliver : r = r0.deliver process ((rs.take k).flatMap fun rg ↦
    (l.filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g)

/-- The invariant of the loop of `Ratpoints.Sieve.sift` over the bounds of the search intervals of
the denominator `b`, with the class word `w`, the sieve entries `es` and `es3`, the specs of
`Ratpoints.Sieve.packedReads` with the row offsets from position `pos` of `offsets` on, and the
ranges `rs` of the numerators, whose state is the value of a return, the delivery, the store of the
tables of rows, the flag of the set-up and the sieve specs: before a return,
`Ratpoints.Sieve.SiftIntervalsInvariant` after the intervals done, for the numerators `-H, …, H`,
their test by `w` and the entries, and the points of the check with the flags `fl`; after the
return at a stop or at an interval above the height bound, the store returned fits the entries and
the delivery returned is that of the points of all the ranges. -/
def SiftIntervalsLoopInvariant (c : List Int) (d H b : Nat) (fl : CheckFlags)
    (es es3 : List SieveEntry) (w : UInt64) (cl : NumClass) (offsets : Array Nat) (pos : Nat)
    (rs : List (Int × Int)) (r0 : Delivery σ) :
    Std.WP.Invariant IntervalBounds
      (Option (Delivery σ × RowStore) × Delivery σ × RowStore × Bool × List SieveSpec) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun pref _ s ↦ SiftIntervalsInvariant process (numerators H)
      (fun a ↦ classBit w a && survives (es ++ es3) b a)
      (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl) es
      ((packedReads es b cl offsets pos).map Prod.fst) rs r0 pref.length s.1 s.2.1 s.2.2.1 s.2.2.2)
    (fun ret _ ↦ RowStore.Fits ret.2 es ∧ ret.1 = r0.deliver process (rs.flatMap fun rg ↦
      ((numerators H).filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) &&
        (classBit w a && survives (es ++ es3) b a)).flatMap
          (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)))

section

variable {process} {l : List Int} {q : Int → Bool} {g : Int → List (Int × Int × Int)}
  {es : List SieveEntry} {specs0 : List SieveSpec} {rs : List (Int × Int)} {r0 r r' : Delivery σ}
  {store st : RowStore} {doSetup : Bool} {specs specs' : List SieveSpec}
  {pref suff : List IntervalBounds} {cur : IntervalBounds} {o : Option (Delivery σ × RowStore)}

theorem siftIntervalsInvariant_zero (hr : r0.quit = false) (hs : store.Fits es)
    (specs : List SieveSpec) :
    SiftIntervalsInvariant process l q g es specs0 rs r0 0 r0 store true specs :=
  ⟨hr, hs, nofun, by simp⟩

/-- After the last range, the delivery is that of the points of all the ranges. -/
theorem SiftIntervalsInvariant.post_of_length_le {k : Nat}
    (h : SiftIntervalsInvariant process l q g es specs0 rs r0 k r store doSetup specs)
    (hk : rs.length ≤ k) :
    store.Fits es ∧ r = r0.deliver process (rs.flatMap fun rg ↦
      (l.filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g) :=
  ⟨h.fits, by rw [h.eq_deliver, List.take_of_length_le hk]⟩

/-- When the ranges from the `k`-th on hold no element of `l` that passes `q`, the delivery after
the first `k` ranges is that of the points of all of them. -/
theorem SiftIntervalsInvariant.post_of_forall_mem_drop {k : Nat}
    (h : SiftIntervalsInvariant process l q g es specs0 rs r0 k r store doSetup specs)
    (hnil : ∀ rg ∈ rs.drop k, l.filter (fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a) = []) :
    store.Fits es ∧ r = r0.deliver process (rs.flatMap fun rg ↦
      (l.filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g) := by
  refine ⟨h.fits, ?_⟩
  rw [h.eq_deliver]
  conv => rhs; rw [← List.take_append_drop k rs]
  rw [List.flatMap_append, List.flatMap_eq_nil_iff.mpr fun rg (hrg : rg ∈ rs.drop k) ↦ by
    rw [hnil rg hrg]; rfl, List.append_nil]

/-- A range that holds no element of `l` that passes `q`, or none at all, delivers nothing. -/
theorem SiftIntervalsInvariant.append_of_forall_mem
    (h : o = none ∧ SiftIntervalsInvariant process l q g es specs0 rs r0 pref.length r store
      doSetup specs)
    (hnil : ∀ rg ∈ rs[pref.length]?,
      l.filter (fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a) = []) :
    SiftIntervalsInvariant process l q g es specs0 rs r0 (pref ++ [cur]).length r store doSetup
      specs := by
  refine ⟨h.2.quit_eq_false, h.2.fits, h.2.specs_eq, ?_⟩
  rw [h.2.eq_deliver, List.length_append, List.length_singleton, List.take_add_one,
    List.flatMap_append]
  rcases hk : rs[pref.length]? with _ | rg
  · simp
  · simp only [Option.toList_some, List.flatMap_singleton]
    rw [hnil rg (by simp [hk]), List.flatMap_nil, List.append_nil]

-- The delivery of the points of the next range after those of the first `pref.length` ranges.
private theorem SiftIntervalsInvariant.eq_deliver_take_succ {k : Nat}
    (h : SiftIntervalsInvariant process l q g es specs0 rs r0 k r store doSetup specs)
    (hr : r' = r.deliver process (rs[k]?.toList.flatMap fun rg ↦
      (l.filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g)) :
    r' = r0.deliver process ((rs.take (k + 1)).flatMap fun rg ↦
      (l.filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g) := by
  rw [hr, h.eq_deliver, ← Delivery.deliver_append, ← List.flatMap_append, ← List.take_add_one]

/-- A range whose points the delivery `r'` adds, after which the callback has not stopped the
search, with the store `st` that fits the entries and the sieve specs made, keeps the invariant. -/
theorem SiftIntervalsInvariant.append_of_eq_deliver
    (h : o = none ∧ SiftIntervalsInvariant process l q g es specs0 rs r0 pref.length r store
      doSetup specs)
    (hr : r' = r.deliver process (rs[pref.length]?.toList.flatMap fun rg ↦
      (l.filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g))
    (hq : ¬r'.quit = true) (hs : st.Fits es) (hsp : specs' = specs0) (ds : Bool) :
    SiftIntervalsInvariant process l q g es specs0 rs r0 (pref ++ [cur]).length r' st ds specs' :=
  ⟨Bool.eq_false_iff.mpr hq, hs, fun _ ↦ hsp, by
    rw [List.length_append, List.length_singleton]; exact h.2.eq_deliver_take_succ hr⟩

/-- A range whose points the delivery `r'` adds, after which the callback has stopped the search:
the delivery is that of the points of all the ranges
(`Ratpoints.Delivery.deliver_flatMap_eq_of_prefix`). -/
theorem SiftIntervalsInvariant.post_of_quit
    (h : o = none ∧ SiftIntervalsInvariant process l q g es specs0 rs r0 pref.length r store
      doSetup specs)
    (hr : r' = r.deliver process (rs[pref.length]?.toList.flatMap fun rg ↦
      (l.filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g))
    (hq : r'.quit = true) (hs : st.Fits es) :
    st.Fits es ∧ r' = r0.deliver process (rs.flatMap fun rg ↦
      (l.filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g) := by
  have he := h.2.eq_deliver_take_succ hr
  rw [he] at hq ⊢
  exact ⟨hs, (Delivery.deliver_flatMap_eq_of_prefix process (List.take_prefix _ rs) _ hq).symm⟩

/-- Once the sieve specs are made, they are `specs0`, and the store fits the entries. -/
theorem SiftIntervalsInvariant.specs_eq_and_fits_of_not {k : Nat}
    (h : o = none ∧ SiftIntervalsInvariant process l q g es specs0 rs r0 k r store doSetup specs)
    (hd : ¬doSetup = true) :
    specs = specs0 ∧ store.Fits es :=
  ⟨h.2.specs_eq (Bool.eq_false_iff.mpr hd), h.2.fits⟩

end

theorem filter_numerators_eq_nil_of_lt_neg {H : Nat} {lo hi : Int} (h : hi < -H)
    (q : Int → Bool) : (numerators H).filter (fun a ↦ decide (lo ≤ a ∧ a ≤ hi) && q a) = [] :=
  List.filter_eq_nil_iff.mpr fun a ha ↦ by
    have := natAbs_le_of_mem_numerators ha
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    lia

theorem filter_numerators_eq_nil_of_lt {H : Nat} {lo hi : Int} (h : (H : Int) < lo)
    (q : Int → Bool) : (numerators H).filter (fun a ↦ decide (lo ≤ a ∧ a ≤ hi) && q a) = [] :=
  List.filter_eq_nil_iff.mpr fun a ha ↦ by
    have := natAbs_le_of_mem_numerators ha
    simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
    lia

/-- What the contract of `Ratpoints.Sieve.sift` on the ranges `rs` of the numerators that the bounds
`iv` of the search intervals give (`Ratpoints.Sieve.RangesFor`) needs of its arguments: a
denominator `0 < b < 2 ^ 63` and `H < 2 ^ 63`, the sieve entries `es3` of the third stage of the
shape that it needs, the class `cl` that packs the class word `w` with its row offsets from position
`pos` of `offsets` on, and the sieve entries `es` of the first two stages with their tables of
inverses and the offsets of the packing of `cl`. -/
structure IsSiftArgs (es es3 : List SieveEntry) (w : UInt64) (cl : NumClass) (offsets : Array Nat)
    (pos : Nat) (iv : Array IntervalBounds) (b H : Nat) (rs : List (Int × Int)) : Prop where
  /-- The denominator is positive. -/
  pos_b : 0 < b
  /-- The denominator is below `2 ^ 63`. -/
  b_lt : b < 2 ^ 63
  /-- The height bound is below `2 ^ 63`. -/
  H_lt : H < 2 ^ 63
  /-- The entries of the third stage have the shape that it needs. -/
  isPrimeEntry : ∀ e ∈ es3, e.IsPrimeEntry
  /-- The class packs the class word. -/
  packs : cl.Packs w
  /-- The row offsets of the class start at `pos`. -/
  offset_eq : cl.offset = some pos
  /-- The entries of the first two stages have their tables of inverses. -/
  hasInverses : ∀ e ∈ es, ∀ f ∈ e.factors, f.HasInverses e.p
  /-- The entries of the first two stages have the offsets of the packing of the class. -/
  packedFor : ∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!
  /-- The bounds of the search intervals give the ranges. -/
  rangesFor : RangesFor iv b H rs

namespace IsSiftArgs

variable {process} {c : List Int} {d b H : Nat} {fl : CheckFlags} {es es3 : List SieveEntry}
  {w : UInt64} {cl : NumClass} {offsets : Array Nat} {pos : Nat} {iv : Array IntervalBounds}
  {rs : List (Int × Int)} {q : Int → Bool} {g : Int → List (Int × Int × Int)}
  {specs0 : List SieveSpec} {r0 r r' : Delivery σ} {store st : RowStore} {doSetup : Bool}
  {specs specs' : List SieveSpec} {pref suff : List IntervalBounds} {cur : IntervalBounds}
  {o : Option (Delivery σ × RowStore)}

/-- After the last interval, the delivery is that of the points of all the ranges. -/
theorem post_of_length (ha : IsSiftArgs es es3 w cl offsets pos iv b H rs)
    (h : SiftIntervalsInvariant process (numerators H) q g es specs0 rs r0 (ForIn.toList iv).length
      r store doSetup specs) :
    store.Fits es ∧ r = r0.deliver process (rs.flatMap fun rg ↦
      ((numerators H).filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g) :=
  h.post_of_length_le (by simp [Std.Internal.ForIn.toList_array, ha.rangesFor.length_eq])

/-- At an interval with the code `2`, above the height bound, the delivery is that of the points of
all the ranges: the ranges from that interval on lie above `H`. -/
theorem post_of_two (ha : IsSiftArgs es es3 w cl offsets pos iv b H rs)
    (hl : ForIn.toList iv = pref ++ cur :: suff)
    (h : o = none ∧ SiftIntervalsInvariant process (numerators H) q g es specs0 rs r0 pref.length r
      store doSetup specs)
    (h2 : (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 2) :
    store.Fits es ∧ r = r0.deliver process (rs.flatMap fun rg ↦
      ((numerators H).filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) && q a).flatMap g) :=
  have ⟨hk, hrep⟩ := ha.rangesFor.represents_of_eq_append_cons hl
  h.2.post_of_forall_mem_drop fun rg hrg ↦ filter_numerators_eq_nil_of_lt
    (ha.rangesFor.lt_fst_of_mem_drop hk (hrep.two cl ha.packs.toWF h2) rg hrg) q

/-- An interval with the code `1`, below `-H`, keeps the invariant. -/
theorem append_of_one (ha : IsSiftArgs es es3 w cl offsets pos iv b H rs)
    (hl : ForIn.toList iv = pref ++ cur :: suff)
    (h : o = none ∧ SiftIntervalsInvariant process (numerators H) q g es specs0 rs r0 pref.length r
      store doSetup specs)
    (h1 : (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 1) :
    SiftIntervalsInvariant process (numerators H) q g es specs0 rs r0 (pref ++ [cur]).length r store
      doSetup specs :=
  have ⟨hk, hrep⟩ := ha.rangesFor.represents_of_eq_append_cons hl
  SiftIntervalsInvariant.append_of_forall_mem h fun rg hrg ↦ by
    obtain rfl : rs[pref.length] = rg := by simpa [List.getElem?_eq_getElem hk] using hrg
    exact filter_numerators_eq_nil_of_lt_neg (hrep.one cl ha.packs.toWF h1) q

/-- The sieve specs that `Ratpoints.Sieve.setRows` and `Ratpoints.Sieve.buildRows` make at the first
interval that asks for them are those of `Ratpoints.Sieve.packedReads`, and the store after them
fits the entries (`Ratpoints.Sieve.eq_map_fst_packedReads_of_eq_run_buildRows`). -/
theorem specs_eq_and_fits_of_eq_run_buildRows (ha : IsSiftArgs es es3 w cl offsets pos iv b H rs)
    {k : Nat} (h : o = none ∧ SiftIntervalsInvariant process (numerators H) q g es specs0 rs r0 k r
      store doSetup specs)
    (hr : (specs', st) = Id.run (buildRows
      (setRows store es (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets).2 es
      (es.map fun e ↦ b * e.dinv[cl.k]! % e.p)
      (setRows store es (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets).1 store)) :
    specs' = (packedReads es b cl offsets pos).map Prod.fst ∧ st.Fits es :=
  ⟨eq_map_fst_packedReads_of_eq_run_buildRows h.2.fits ha.offset_eq hr,
    (h.2.fits.buildRows_setRows (fun e he ↦ Nat.mod_lt _ (h.2.fits.pos e he)) hr).2⟩

/-- What `Ratpoints.Sieve.siftBits` needs of the sieve specs of `Ratpoints.Sieve.packedReads`. -/
theorem pre_siftBits (ha : IsSiftArgs es es3 w cl offsets pos iv b H rs) {A : Nat} (hA : 1 ≤ A)
    {k : Nat} (h : o = none ∧ SiftIntervalsInvariant process (numerators H) q g es specs0 rs r0 k r
      store doSetup specs)
    (hsp : specs' = (packedReads es b cl offsets pos).map Prod.fst ∧ st.Fits es) :
    r.quit = false ∧ 1 ≤ A ∧ (∀ s ∈ specs', s.Fits) ∧
      es.map (fun x ↦ magic x.p) = specs'.map (fun x ↦ magic x.p) :=
  hsp.1 ▸ ⟨h.2.quit_eq_false, hA, fits_of_mem_packedReads ha.packedFor, map_magic_packedReads ..⟩

/-- The delivery after `Ratpoints.Sieve.siftBits` on the bits that `Ratpoints.Sieve.intervalBits`
gives for the interval at the position `pref.length`, neither of the codes `1` and `2`, with the
sieve specs of `Ratpoints.Sieve.packedReads`, adds the points of the range of the numerators of
that interval (`Ratpoints.Sieve.flatMap_filter_intervalBits_eq`). -/
theorem eq_deliver_getElem? (ha : IsSiftArgs es es3 w cl offsets pos iv b H rs)
    (hl : ForIn.toList iv = pref ++ cur :: suff)
    (h2 : ¬(intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 2)
    (h1 : ¬(intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 1)
    (hsp : specs = (packedReads es b cl offsets pos).map Prod.fst)
    (hsb : ∀ sfs : List (SieveSpec × (Int → Bool)), specs = sfs.map Prod.fst →
      (∀ sf ∈ sfs, sf.1.Reads sf.2) →
      r' = r.deliver process ((((List.range
        ((intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.2.toInt + 1 -
          (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.1.toInt).toNat).map fun k : Nat ↦
        (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.1.toInt + k).filter
          fun j ↦ classBit cl.bits j && sfs.all (·.2 j)).flatMap
        fun j ↦ acceptedPoints (.mk fun _ ↦ scaledCoeffs c d b) d b fl
          (.mk fun _ ↦ fillChecks b H es3 (es3.map fun e ↦ magic e.p)) (cl.numerator j))) :
    r' = r.deliver process (rs[pref.length]?.toList.flatMap fun rg ↦
      ((numerators H).filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) &&
        (classBit w a && survives (es ++ es3) b a)).flatMap
          (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)) := by
  obtain ⟨hk, hrep⟩ := ha.rangesFor.represents_of_eq_append_cons hl
  rw [hsb _ hsp (reads_of_mem_packedReads ha.hasInverses ha.packedFor),
    flatMap_filter_intervalBits_eq ha.isPrimeEntry ha.packs hrep h1 h2 ha.pos_b ha.b_lt ha.H_lt,
    List.getElem?_eq_getElem hk]
  simp only [Option.toList_some, List.flatMap_singleton]

/-- An interval whose bits `Ratpoints.Sieve.siftBits` delivers with the sieve specs
of `Ratpoints.Sieve.packedReads`, after which the callback has stopped the search: the delivery is
that of the points of all the ranges (`Ratpoints.Sieve.IsSiftArgs.eq_deliver_getElem?`). -/
theorem post_of_siftBits (ha : IsSiftArgs es es3 w cl offsets pos iv b H rs)
    (h : o = none ∧ SiftIntervalsInvariant process (numerators H)
      (fun a ↦ classBit w a && survives (es ++ es3) b a)
      (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl) es
      ((packedReads es b cl offsets pos).map Prod.fst) rs r0 pref.length r store doSetup specs)
    (hl : ForIn.toList iv = pref ++ cur :: suff)
    (h2 : ¬(intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 2)
    (h1 : ¬(intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 1)
    (hsf : specs' = (packedReads es b cl offsets pos).map Prod.fst ∧ st.Fits es)
    (hsb : ∀ sfs : List (SieveSpec × (Int → Bool)), specs' = sfs.map Prod.fst →
      (∀ sf ∈ sfs, sf.1.Reads sf.2) →
      r' = r.deliver process ((((List.range
        ((intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.2.toInt + 1 -
          (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.1.toInt).toNat).map fun k : Nat ↦
        (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.1.toInt + k).filter
          fun j ↦ classBit cl.bits j && sfs.all (·.2 j)).flatMap
        fun j ↦ acceptedPoints (.mk fun _ ↦ scaledCoeffs c d b) d b fl
          (.mk fun _ ↦ fillChecks b H es3 (es3.map fun e ↦ magic e.p)) (cl.numerator j)))
    (hq : r'.quit = true) :
    st.Fits es ∧ r' = r0.deliver process (rs.flatMap fun rg ↦
      ((numerators H).filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) &&
        (classBit w a && survives (es ++ es3) b a)).flatMap
          (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)) :=
  SiftIntervalsInvariant.post_of_quit h (ha.eq_deliver_getElem? hl h2 h1 hsf.1 hsb) hq hsf.2

/-- An interval whose bits `Ratpoints.Sieve.siftBits` delivers with the sieve specs
of `Ratpoints.Sieve.packedReads`, after which the callback has not stopped the search, keeps the
invariant (`Ratpoints.Sieve.IsSiftArgs.eq_deliver_getElem?`). -/
theorem append_of_siftBits (ha : IsSiftArgs es es3 w cl offsets pos iv b H rs)
    (h : o = none ∧ SiftIntervalsInvariant process (numerators H)
      (fun a ↦ classBit w a && survives (es ++ es3) b a)
      (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl) es
      ((packedReads es b cl offsets pos).map Prod.fst) rs r0 pref.length r store doSetup specs)
    (hl : ForIn.toList iv = pref ++ cur :: suff)
    (h2 : ¬(intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 2)
    (h1 : ¬(intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 1)
    (hsf : specs' = (packedReads es b cl offsets pos).map Prod.fst ∧ st.Fits es)
    (hsb : ∀ sfs : List (SieveSpec × (Int → Bool)), specs' = sfs.map Prod.fst →
      (∀ sf ∈ sfs, sf.1.Reads sf.2) →
      r' = r.deliver process ((((List.range
        ((intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.2.toInt + 1 -
          (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.1.toInt).toNat).map fun k : Nat ↦
        (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.1.toInt + k).filter
          fun j ↦ classBit cl.bits j && sfs.all (·.2 j)).flatMap
        fun j ↦ acceptedPoints (.mk fun _ ↦ scaledCoeffs c d b) d b fl
          (.mk fun _ ↦ fillChecks b H es3 (es3.map fun e ↦ magic e.p)) (cl.numerator j)))
    (hq : ¬r'.quit = true) (ds : Bool) :
    SiftIntervalsInvariant process (numerators H) (fun a ↦ classBit w a && survives (es ++ es3) b a)
      (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl) es
      ((packedReads es b cl offsets pos).map Prod.fst) rs r0 (pref ++ [cur]).length r' st ds
      specs' :=
  SiftIntervalsInvariant.append_of_eq_deliver h (ha.eq_deliver_getElem? hl h2 h1 hsf.1 hsb) hq hsf.2
    hsf.1 ds

end IsSiftArgs

open Std.WP Lean.Order in
-- The contract of `Ratpoints.Sieve.sift` for the class word `w`, the position `pos` of the row
-- offsets of the class and the ranges `rs` of the numerators of the search intervals, range by
-- range.
private theorem sift_spec_ranges (c : List Int) (d H A b : Nat) (fl : CheckFlags) (sp1 : Nat)
    {es es3 : List SieveEntry} {w : UInt64} {cl : NumClass} {pos : Nat} (offsets : Array Nat)
    {iv : Array IntervalBounds} {rs : List (Int × Int)} (store : RowStore) (r : Delivery σ)
    (hA : 1 ≤ A) (ha : IsSiftArgs es es3 w cl offsets pos iv b H rs) (hs : store.Fits es) :
    ⦃ r.quit = false ⦄
    sift process c d H A b fl sp1 es (es.map (magic ·.p)) (es.map fun e ↦ b * e.dinv[cl.k]! % e.p)
      cl offsets es3 (es3.map fun e ↦ magic e.p) iv store r
    ⦃ fun r' ↦ r'.2.Fits es ∧ r'.1 = r.deliver process (rs.flatMap fun rg ↦
        ((numerators H).filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) &&
          (classBit w a && survives (es ++ es3) b a)).flatMap
            (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)) ⦄ := by
  vcgen [sift, buildRows_value] invariants
  · SiftIntervalsLoopInvariant process c d H b fl es es3 w cl offsets pos rs r
  all_goals subst_vars
  all_goals simp only [SiftIntervalsLoopInvariant, meet_prop_eq_and, join_prop_eq_or,
    iSup_prop_eq_exists, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, exists_eq_left', exists_false, and_true] at *
  all_goals first
    | exact ‹_›
    | exact siftIntervalsInvariant_zero ‹_› hs _
    | exact ha.post_of_length ‹_›
    | exact ha.post_of_two ‹_› ‹_› ‹_›
    | exact ha.append_of_one ‹_› ‹_› ‹_›
    | (first
        | have hsf := ha.specs_eq_and_fits_of_eq_run_buildRows ‹_› ‹_›
        | have hsf := SiftIntervalsInvariant.specs_eq_and_fits_of_not ‹_› ‹_›)
      first
        | exact ha.pre_siftBits hA ‹_› hsf
        | exact ha.post_of_siftBits ‹_› ‹_› ‹_› ‹_› hsf ‹_› ‹_›
        | exact ha.append_of_siftBits ‹_› ‹_› ‹_› ‹_› hsf ‹_› ‹_› _

-- The delivery of `Ratpoints.Sieve.siftBits`, as a value for the contract of the store of
-- `Ratpoints.Sieve.sift`.
private theorem siftBits_value (w : Thunk (List Int)) (d b A : Nat) (fl : CheckFlags) (sp1 : Nat)
    (specs : List SieveSpec) (mgs : List Nat) (checks : Thunk (List CheckSpec)) (cl : NumClass)
    (low high : Int) (r : Delivery σ) :
    ⦃ True ⦄ siftBits process w d b A fl sp1 specs mgs checks cl low high r
    ⦃ fun r' ↦ r' = Id.run (siftBits process w d b A fl sp1 specs mgs checks cl low high r) ⦄ :=
  ⟨fun _ ↦ rfl⟩

open Std.WP Lean.Order in
-- The store of the tables of rows that `Ratpoints.Sieve.sift` returns fits the sieve entries `es`
-- of the first two stages when the one it is given does: the rows built for the residues
-- `b dinv[k] mod p` (`Ratpoints.Sieve.RowStore.Fits.buildRows_setRows`).
private theorem sift_fits (c : List Int) (d H A b : Nat) (fl : CheckFlags) (sp1 : Nat)
    (es : List SieveEntry) (mgs : List Nat) (cl : NumClass) (offsets : Array Nat)
    (es3 : List SieveEntry) (mgs3 : List Nat) (iv : Array IntervalBounds) (store : RowStore)
    (r : Delivery σ) :
    ⦃ store.Fits es ⦄
    sift process c d H A b fl sp1 es mgs (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets es3
      mgs3 iv store r
    ⦃ fun r' ↦ r'.2.Fits es ⦄ := by
  vcgen [sift, buildRows_value, siftBits_value] invariants
  · Std.WP.Invariant.withEarlyReturnNewDo Prop (fun _ _ s ↦ RowStore.Fits s.2.1 es)
      (fun ret _ ↦ RowStore.Fits ret.2 es)
  all_goals subst_vars
  all_goals simp only [meet_prop_eq_and, join_prop_eq_or, iSup_prop_eq_exists, ofProp_prop_eq,
    reduceCtorEq, false_and, or_false, false_or, true_and, and_false, Option.some.injEq,
    exists_eq_left', exists_false, and_true] at *
  all_goals first
    | exact ‹_›
    | exact ‹_ ∧ _›.2
    | have h := ‹_ ∧ RowStore.Fits _ es›.2
      exact (h.buildRows_setRows (fun e he ↦ Nat.mod_lt _ (h.pos e he)) ‹_›).2

/-- The store of the tables of rows fits the sieve entries `es` of the first two stages
(`Ratpoints.Sieve.RowStore.Fits`) before the denominator and after it, with the rows built for it
when an interval asks for them (the lazy set-up), and the denominator delivers, for the ranges `rs`
of the numerators that the bounds `iv` of the search intervals give for it
(`Ratpoints.Sieve.RangesFor`), the points of the check with the flags `fl`
(`Ratpoints.Sieve.checkNumWith`) of the numerators `-H, …, H` in one of the ranges that pass the
class word `w` and survive the sieve entries of all three stages. The class word `w` that the class
`cl` packs, the position `pos` of the row offsets of `cl` and the ranges are quantified in the
postcondition, since the program does not mention them; the reciprocals and the residues
`b dinv[k] mod p` (`Ratpoints.Sieve.fillBpList_eq_map`) are those of the entries, which have their
tables of inverses and the offsets of the packing of `cl` (`Ratpoints.Sieve.SieveEntry.PackedFor`);
the test for common factors on the words of the C code needs `0 < b < 2 ^ 63` and the numerators
`|a| ≤ H < 2 ^ 63` (`Ratpoints.Sieve.accepted_spec`), and the third stage entries of the shape of
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry` with the reciprocals of their moduli. -/
@[spec]
theorem sift_spec (c : List Int) (d H A b : Nat) (fl : CheckFlags) (sp1 : Nat)
    (es : List SieveEntry) (mgs bp : List Nat) (cl : NumClass) (offsets : Array Nat)
    (es3 : List SieveEntry) (mgs3 : List Nat) (iv : Array IntervalBounds) (store : RowStore)
    (r : Delivery σ) :
    ⦃ r.quit = false ∧ 1 ≤ A ∧ 0 < b ∧ b < 2 ^ 63 ∧ H < 2 ^ 63 ∧ (∀ e ∈ es3, e.IsPrimeEntry) ∧
        mgs3 = es3.map (fun e ↦ magic e.p) ∧ mgs = es.map (magic ·.p) ∧
        bp = es.map (fun e ↦ b * e.dinv[cl.k]! % e.p) ∧
        (∀ e ∈ es, ∀ f ∈ e.factors, f.HasInverses e.p) ∧ store.Fits es ⦄
    sift process c d H A b fl sp1 es mgs bp cl offsets es3 mgs3 iv store r
    ⦃ fun r' ↦ r'.2.Fits es ∧ ∀ (w : UInt64) (pos : Nat) (rs : List (Int × Int)), cl.Packs w →
        cl.offset = some pos → (∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!) →
        RangesFor iv b H rs →
        r'.1 = r.deliver process (((numerators H).filter fun a ↦
          inRanges rs a && classBit w a && survives (es ++ es3) b a).flatMap
            (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)) ⦄ :=
  ⟨fun ⟨hr, hA, hb, hb63, hH, hes, hmg3, hmg, hbp, hinv, hs⟩ ↦ by
    subst hmg3 hmg hbp
    refine ⟨(sift_fits process c d H A b fl sp1 es _ cl offsets es3 _ iv store r).le_wp hs,
      fun w pos rs hcl hpos hoff hiv ↦ ?_⟩
    rw [((sift_spec_ranges process c d H A b fl sp1 offsets store r hA
      ⟨hb, hb63, hH, hes, hcl, hpos, hinv, hoff, hiv⟩ hs).le_wp hr).2,
      flatMap_flatMap_filter_eq_flatMap_filter_inRanges
        (pairwise_lt_numerators H) hiv.pairwise]
    simp only [Bool.and_assoc]⟩

/-- Without `RATPOINTS_NO_CHECK`, `Ratpoints.Sieve.sift` with the flags `fl`, the class `cl` that
packs the class word `w` with its row offsets from position `pos` of `offsets` on, the entries `es`
of the first two stages with their reciprocals and residues `b dinv[k] mod p`, their tables of
inverses and the offsets of the packing of `cl`, a store of the tables of rows that fits them
(`Ratpoints.Sieve.RowStore.Fits`), the entries `es3` of the third, of the shape of
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, with the reciprocals of their moduli, and bounds of the
search intervals that give the ranges `rs` of the numerators (`Ratpoints.Sieve.RangesFor`), for a
denominator `0 < b < 2 ^ 63` and `H < 2 ^ 63`, delivers the points of the plain sieve with all these
entries and its check, the reference of the words, whose numerators lie in one of the ranges and
pass `w` (`Ratpoints.Sieve.classBit`), mapped by `Ratpoints.Sieve.swapPoint` when `fl.reversed` is
set, those with `y < 0` left out under `RATPOINTS_NO_Y`: the plain sieve and its check give what the
brute-force reference finds over `b` and the numerators `-H, …, H` that survive the sieve entries
(`Ratpoints.Sieve.sieveDen_spec`, `Ratpoints.Sieve.checkDen_spec`), and `Ratpoints.Sieve.sift`
delivers those of these points whose numerators lie in the ranges and pass `w`
(`Ratpoints.Sieve.sift_spec`, `Ratpoints.BruteForce.pointsOfDen_filter`). -/
theorem run_sift_eq_deliver_checkDen (c : List Int) (d H b : Nat) {fl : CheckFlags}
    (hc : fl.noCheck = false) (sp1 : Nat) {A : Nat} (hA : 1 ≤ A) (hb : 0 < b) (hb63 : b < 2 ^ 63)
    (hH : H < 2 ^ 63) {es es3 : List SieveEntry} {w : UInt64} {cl : NumClass} {pos : Nat}
    (offsets : Array Nat) {iv : Array IntervalBounds} {rs : List (Int × Int)} {store : RowStore}
    (hes : ∀ e ∈ es3, e.IsPrimeEntry) (hcl : cl.Packs w) (hpos : cl.offset = some pos)
    (hinv : ∀ e ∈ es, ∀ f ∈ e.factors, f.HasInverses e.p)
    (hoff : ∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!)
    (hiv : RangesFor iv b H rs) (hs : store.Fits es) {r : Delivery σ} (hr : r.quit = false) :
    (Id.run (sift process c d H A b fl sp1 es (es.map (magic ·.p))
      (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets es3 (es3.map fun e ↦ magic e.p) iv
        store r)).1 =
      r.deliver process ((((Id.run (checkDen c d H b
        (Id.run (sieveDen H b (es ++ es3))))).toList.filter fun q ↦
          inRanges rs q.1 && classBit w q.1).map
            (if fl.reversed then swapPoint else id)).filter fun p ↦ !fl.noY || 0 ≤ p.2.1) :=
  (((sift_spec process c d H A b fl sp1 es _ _ cl offsets es3 _ iv store r).le_wp
    ⟨hr, hA, hb, hb63, hH, hes, rfl, rfl, rfl, hinv, hs⟩).2 w pos rs hcl hpos hoff hiv).trans <| by
    rw [flatMap_checkNumWith_of_noCheck_eq_false hc, ← List.filter_filter, pointsOfDen_filter,
      ← (checkDen_spec c d H b _).le_wp trivial _ ((sieveDen_spec H b (es ++ es3)).le_wp trivial)]
    rfl

end Sieve

end Ratpoints

end
