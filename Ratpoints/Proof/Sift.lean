/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.BitRange
public import Ratpoints.Proof.RowStore
public import Ratpoints.Proof.SiftBits

import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
import Ratpoints.Proof.Sieve
import Std.Tactic.Do

/-!
# The contract of the sieve of one denominator

The contract of the sieve of one denominator in the packing of its class
(`Ratpoints.Sieve.sift`), over the search intervals in pieces, as an `@[spec]` theorem proved with
`vcgen`, the program logic of Lean core, with loop invariants that are named definitions, on the
contracts of the pieces and of the bits of one interval (`Ratpoints.Proof.SiftBits`). The sieve
hands the points it finds to the callback of the caller on a delivery (`Ratpoints.Delivery`), whose
flag of the stop is clear at the start, and returns as soon as a call sets it; its contract says
that the delivery it returns is the reference of the delivery (`Ratpoints.Delivery.deliver`) of the
list of the points it finds, which passes over the points after the stop, and that, when the
callback does not stop the search, the counters it returns are those it is given plus a closed form
that depends neither on the callback, the delivery and the flags of the output nor on the store of
the tables of rows (`Ratpoints.Sieve.siftCounts`). The numerators come in with the bits of the
numerators `-H, …, H` of one denominator; the points of a numerator are those that the exact check
delivers with the flags of the search.

## Main definitions

* `Ratpoints.Sieve.packedReads`: the closed forms of the rows of the sieve entries for a denominator
  in the packing of a class, with the tests of the bits that they read.
* `Ratpoints.Sieve.SiftIntervalsInvariant`, `Ratpoints.Sieve.SiftIntervalsLoopInvariant`: the
  invariant of the loop of `Ratpoints.Sieve.sift` over the search intervals, range after range.
* `Ratpoints.Sieve.IsSiftArgs`: what the contract of `Ratpoints.Sieve.sift` on the ranges of the
  numerators needs of its arguments.
* `Ratpoints.Sieve.intervalCounts`, `Ratpoints.Sieve.siftCounts`: the counts of one search interval
  and of the sieve of one denominator; `Ratpoints.Sieve.SiftIntervalsCounts`: the invariant of the
  counters of the loop over the search intervals.

## Main statements

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
  (`Ratpoints.Sieve.checkNumWith`) of the numerators `-H, …, H` in one of the ranges that pass `w`
  and survive the sieve entries of all three stages, the store with the rows built for `b` still
  fits the entries, and, when the callback does not stop the search, they add the counts of
  `Ratpoints.Sieve.siftCounts` to the counters; `Ratpoints.Sieve.run_sift_eq_deliver_checkDen`:
  without `RATPOINTS_NO_CHECK`, these are the points that the plain sieve of `b` with all the
  entries gives whose numerators lie in the ranges and pass `w`, mapped by
  `Ratpoints.Sieve.swapPoint` after a reversal, without those with `y < 0` under `RATPOINTS_NO_Y`.
* `Ratpoints.Sieve.sift_storeHolds`, `Ratpoints.Sieve.RowStore.Fits.fits_run_sift`: the sieve of
  one denominator with the first entries of a run as those of its first two stages keeps a store
  that fits all the entries of the run, since it only adds rows.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.SiftBits`, `Ratpoints.Proof.Stages`,
`Ratpoints.Proof.Packing`, `Ratpoints.Proof.BitRange`, `Ratpoints.Proof.RowStore` and
`Ratpoints.Proof.Delivery` do, whose contracts of the bits of one interval and of the rows built
into the tables of rows of the run and whose lemmas on classes, the bits of an interval and the
delivery it builds on. The hypotheses of the test on the words of the C code, `0 < b < 2 ^ 63` and
`|a| ≤ H < 2 ^ 63`, come in with the numerators `-H, …, H` of one denominator
(`Ratpoints.Sieve.acceptedPoints_eq_ite`). The loop of `Ratpoints.Sieve.sift` over the search
intervals returns at the first interval above `H` and at a stop: its invariant holds the delivery of
the points of the ranges done, range after range, which are those of the numerators in one of the
ranges, the ranges being increasing and strictly apart (`List.flatMap_filter_eq_filter_any`); the
sieve specs, made at the first interval that is neither below `-H` nor above `H`, are those of
`Ratpoints.Sieve.packedReads` from then on, and the store of the tables of rows fits the entries in
both branches, which a contract of its own also states without the class word and the ranges. The
counters have a contract of their own too (the contracts of the counters of the components it calls
are in `Ratpoints.Proof.ScanCounts` and `Ratpoints.Proof.SiftBits`), which needs neither the class
word nor the ranges, and `Ratpoints.Sieve.sift_spec` states the three. The contracts of one block
and of the run over the blocks, which call `Ratpoints.Sieve.sift` with the class of each
denominator, are in `Ratpoints.Proof.Blocks` and `Ratpoints.Proof.Correction`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

variable {σ : Type} (process : Int → Int → Int → σ → Answer σ)

open BruteForce

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
    {offsets : Array Nat} {pos : Nat} (hinv : ∀ e ∈ es, e.HasInverses)
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
      (Option (Delivery σ × RowStore × Counters) × Delivery σ × RowStore × Counters × Bool ×
        List SieveSpec) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun pref _ s ↦ SiftIntervalsInvariant process (numerators H)
      (fun a ↦ classBit w a && survives (es ++ es3) b a)
      (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl) es
      ((packedReads es b cl offsets pos).map Prod.fst) rs r0 pref.length s.1 s.2.1 s.2.2.2.1
      s.2.2.2.2)
    (fun ret _ ↦ RowStore.Fits ret.2.1 es ∧ ret.1 = r0.deliver process (rs.flatMap fun rg ↦
      ((numerators H).filter fun a ↦ decide (rg.1 ≤ a ∧ a ≤ rg.2) &&
        (classBit w a && survives (es ++ es3) b a)).flatMap
          (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)))

section

variable {process} {l : List Int} {q : Int → Bool} {g : Int → List (Int × Int × Int)}
  {es : List SieveEntry} {specs0 : List SieveSpec} {rs : List (Int × Int)} {r0 r r' : Delivery σ}
  {store st : RowStore} {doSetup : Bool} {specs specs' : List SieveSpec}
  {pref suff : List IntervalBounds} {cur : IntervalBounds}
    {o : Option (Delivery σ × RowStore × Counters)}

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
  hasInverses : ∀ e ∈ es, e.HasInverses
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
  {o : Option (Delivery σ × RowStore × Counters)}

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
    (cnt : Counters) (hA : 1 ≤ A) (ha : IsSiftArgs es es3 w cl offsets pos iv b H rs)
    (hs : store.Fits es) :
    ⦃ r.quit = false ⦄
    sift process c d H A b fl sp1 es (es.map (magic ·.p)) (es.map fun e ↦ b * e.dinv[cl.k]! % e.p)
      cl offsets es3 (es3.map fun e ↦ magic e.p) iv store r cnt
    ⦃ fun r' ↦ r'.2.1.Fits es ∧ r'.1 = r.deliver process (rs.flatMap fun rg ↦
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
    (low high : Int) (r : Delivery σ) (cnt : Counters) :
    ⦃ True ⦄ siftBits process w d b A fl sp1 specs mgs checks cl low high r cnt
    ⦃ fun r' ↦ r' = Id.run (siftBits process w d b A fl sp1 specs mgs checks cl low high r cnt) ⦄ :=
  ⟨fun _ ↦ rfl⟩

open Std.WP Lean.Order in
-- The store of the tables of rows that `Ratpoints.Sieve.sift` returns fits the sieve entries `es`
-- of the first two stages when the one it is given does: the rows built for the residues
-- `b dinv[k] mod p` (`Ratpoints.Sieve.RowStore.Fits.buildRows_setRows`).
private theorem sift_fits (c : List Int) (d H A b : Nat) (fl : CheckFlags) (sp1 : Nat)
    (es : List SieveEntry) (mgs : List Nat) (cl : NumClass) (offsets : Array Nat)
    (es3 : List SieveEntry) (mgs3 : List Nat) (iv : Array IntervalBounds) (store : RowStore)
    (r : Delivery σ) (cnt : Counters) :
    ⦃ store.Fits es ⦄
    sift process c d H A b fl sp1 es mgs (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets es3
      mgs3 iv store r cnt
    ⦃ fun r' ↦ r'.2.1.Fits es ⦄ := by
  vcgen [sift, buildRows_value, siftBits_value] invariants
  · Std.WP.Invariant.withEarlyReturnNewDo Prop (fun _ _ s ↦ RowStore.Fits s.2.1 es)
      (fun ret _ ↦ RowStore.Fits ret.2.1 es)
  all_goals subst_vars
  all_goals simp only [meet_prop_eq_and, join_prop_eq_or, iSup_prop_eq_exists, ofProp_prop_eq,
    reduceCtorEq, false_and, or_false, false_or, true_and, and_false, Option.some.injEq,
    exists_eq_left', exists_false, and_true] at *
  all_goals first
    | exact ‹_›
    | exact ‹_ ∧ _›.2
    | have h := ‹_ ∧ RowStore.Fits _ es›.2
      exact (h.buildRows_setRows (fun e he ↦ Nat.mod_lt _ (h.pos e he)) ‹_›).2

-- The moduli of entries that fit the rows `R` are positive.
private theorem pos_of_rowsFit {R : EntryRef → Nat → Array UInt64} {L : List SieveEntry}
    (hfit : ∀ n (h : n < L.length), L[n].RowsFit R n) (e : SieveEntry) (he : e ∈ L) : 0 < e.p :=
  have ⟨n, hn, he⟩ := List.getElem_of_mem he
  he ▸ (hfit n hn).pos

open Std.WP Lean.Order in
/-- The sieve of one denominator with the first `k` entries of `L` as those of its first two stages
keeps a store that holds the rows `R` for all of `L` (`Ratpoints.Sieve.StoreHolds`), since building
rows keeps the rows of the store (`Ratpoints.Sieve.StoreHolds.buildRows_setRows_take`). -/
theorem sift_storeHolds (c : List Int) (d H A b : Nat) (fl : CheckFlags) (sp1 : Nat)
    {R : EntryRef → Nat → Array UInt64} {L : List SieveEntry} (k : Nat) (mgs : List Nat)
    (cl : NumClass) (offsets : Array Nat) (es3 : List SieveEntry) (mgs3 : List Nat)
    (iv : Array IntervalBounds) (store : RowStore) (r : Delivery σ) (cnt : Counters)
    (hfit : ∀ n (h : n < L.length), L[n].RowsFit R n) :
    ⦃ StoreHolds R L store ⦄
    sift process c d H A b fl sp1 (L.take k) mgs ((L.take k).map fun e ↦ b * e.dinv[cl.k]! % e.p) cl
      offsets es3 mgs3 iv store r cnt
    ⦃ fun r' ↦ StoreHolds R L r'.2.1 ⦄ := by
  vcgen [sift, buildRows_value, siftBits_value] invariants
  · Std.WP.Invariant.withEarlyReturnNewDo Prop (fun _ _ s ↦ StoreHolds R L s.2.1)
      (fun ret _ ↦ StoreHolds R L ret.2.1)
  all_goals subst_vars
  all_goals simp only [meet_prop_eq_and, join_prop_eq_or, iSup_prop_eq_exists, ofProp_prop_eq,
    reduceCtorEq, false_and, or_false, false_or, true_and, and_false, Option.some.injEq,
    exists_eq_left', exists_false, and_true] at *
  all_goals first
    | exact ‹_›
    | exact ‹_ ∧ _›.2
    | exact StoreHolds.buildRows_setRows_take ‹_ ∧ _›.2 hfit
        (fun e he ↦ Nat.mod_lt _ (pos_of_rowsFit hfit e (List.mem_of_mem_take he))) ‹_›

/-- The sieve of one denominator with the first `k` entries of the run `L` as those of its first two
stages only adds rows to the store of the tables of rows, rows of the references of these entries:
a store that fits `L` still fits `L` after it. -/
theorem RowStore.Fits.fits_run_sift (c : List Int) (d H A b : Nat) (fl : CheckFlags) (sp1 : Nat)
    {L : List SieveEntry} {k : Nat} (mgs bp : List Nat) (cl : NumClass) (offsets : Array Nat)
    (es3 : List SieveEntry) (mgs3 : List Nat) (iv : Array IntervalBounds) {store : RowStore}
    (r : Delivery σ) (cnt : Counters) (hs : store.Fits L)
    (hbp : bp = (L.take k).map fun e ↦ b * e.dinv[cl.k]! % e.p) :
    (Id.run (sift process c d H A b fl sp1 (L.take k) mgs bp cl offsets es3 mgs3 iv store r
      cnt)).2.1.Fits L := by
  obtain ⟨R, hR, hfit⟩ := hs
  subst hbp
  exact ⟨R, (sift_storeHolds process c d H A b fl sp1 k mgs cl offsets es3 mgs3 iv store r cnt
    hfit).le_wp hR, hfit⟩

/-! ### The counters of one denominator -/

/-- The counts that the search interval with the bounds `bd` adds to the counters in the sieve of
the denominator `b` (`Ratpoints.Sieve.sift`), for the height `H`, the class `cl` of `b`, the sieve
entries `es` of the first two stages, the first stage ending after `sp1` of them, and the entries
`es3` of the third stage with the reciprocals `mgs3` of their moduli: none for an interval with
the code `1` of `Ratpoints.Sieve.intervalBits`, and otherwise those of its bits
(`Ratpoints.Sieve.bitsCounts`), with the tests of the rows the survivor tests of the entries. -/
def intervalCounts (b H sp1 : Nat) (es es3 : List SieveEntry) (mgs3 : List Nat) (cl : NumClass)
    (bd : IntervalBounds) : Counters :=
  if (intervalBits (Int64.ofNat b) bd (Int64.ofNat H) cl).1 = 1 then {} else
    bitsCounts b (.mk fun _ ↦ fillChecks b H es3 mgs3) cl
      (fun j ↦ survives (es.take sp1) b (cl.numerator j)) (fun j ↦ survives es b (cl.numerator j))
      (intervalBits (Int64.ofNat b) bd (Int64.ofNat H) cl).2.1.toInt
      (intervalBits (Int64.ofNat b) bd (Int64.ofNat H) cl).2.2.toInt

/-- The counts that the sieve of the denominator `b` adds to the counters
(`Ratpoints.Sieve.sift`), for the height `H`, the class `cl` of `b`, the sieve entries `es` of the
first two stages, the first stage ending after `sp1` of them, the entries `es3` of the third stage
with the reciprocals `mgs3` of their moduli and the bounds `iv` of the search intervals: one
denominator, in `sifts`, and the counts of the search intervals (`Ratpoints.Sieve.intervalCounts`)
before the first with the code `2` of `Ratpoints.Sieve.intervalBits`, at which the sieve returns. -/
def siftCounts (b H sp1 : Nat) (es es3 : List SieveEntry) (mgs3 : List Nat) (cl : NumClass)
    (iv : Array IntervalBounds) : Counters :=
  ((iv.toList.takeWhile fun bd ↦ (intervalBits (Int64.ofNat b) bd (Int64.ofNat H) cl).1 != 2).map
    (intervalCounts b H sp1 es es3 mgs3 cl)).foldl (· + ·) { sifts := 1 }

/-- The invariant of the counters of the loop of `Ratpoints.Sieve.sift` over the bounds of the
search intervals of the denominator `b`, after the intervals `pref`, for the sieve entries `es` with
the row offsets of the class `cl` from position `pos` of `offsets` on: the store of the tables of
rows fits `es`, the sieve specs are those of `Ratpoints.Sieve.packedReads` once they are made
(`doSetup` false), none of the intervals of `pref` has the code `2`, and the counters are `cnt0`
plus one denominator and the counts of the intervals of `pref`
(`Ratpoints.Sieve.intervalCounts`). -/
structure SiftIntervalsCounts (b H sp1 : Nat) (es es3 : List SieveEntry) (mgs3 : List Nat)
    (cl : NumClass) (offsets : Array Nat) (pos : Nat) (cnt0 : Counters)
    (pref : List IntervalBounds) (store : RowStore) (doSetup : Bool) (specs : List SieveSpec)
    (c : Counters) : Prop where
  /-- The store fits the sieve entries of the first two stages. -/
  fits : store.Fits es
  /-- The sieve specs, once made. -/
  specs_eq : doSetup = false → specs = (packedReads es b cl offsets pos).map Prod.fst
  /-- No interval done has the code `2`. -/
  ne_two : ∀ bd ∈ pref, (intervalBits (Int64.ofNat b) bd (Int64.ofNat H) cl).1 ≠ 2
  /-- The counters of the intervals done. -/
  eq_counts : c = cnt0 + (pref.map (intervalCounts b H sp1 es es3 mgs3 cl)).foldl (· + ·)
    { sifts := 1 }

/-- `Ratpoints.Sieve.SiftIntervalsCounts` as the invariant of the counters of the loop of
`Ratpoints.Sieve.sift` over the bounds of the search intervals, whose state is the value of a
return, the delivery, the store of the tables of rows, the counters, the flag of the set-up and the
sieve specs; after a return without a stop, at an interval with the code `2`, the counters returned
are those of `Ratpoints.Sieve.siftCounts`. -/
def SiftIntervalsCountsLoopInvariant (b H sp1 : Nat) (es es3 : List SieveEntry) (mgs3 : List Nat)
    (cl : NumClass) (offsets : Array Nat) (pos : Nat) (iv : Array IntervalBounds)
    (cnt0 : Counters) :
    Std.WP.Invariant IntervalBounds
      (Option (Delivery σ × RowStore × Counters) × Delivery σ × RowStore × Counters × Bool ×
        List SieveSpec) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun pref _ s ↦ SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 pref s.2.1
      s.2.2.2.1 s.2.2.2.2 s.2.2.1)
    (fun ret _ ↦ ret.1.quit = false → ret.2.2 = cnt0 + siftCounts b H sp1 es es3 mgs3 cl iv)

/-- The rows of `Ratpoints.Sieve.packedReads` of the first `k` sieve entries are its first `k`. -/
theorem take_packedReads (es : List SieveEntry) (b : Nat) (cl : NumClass) (offsets : Array Nat)
    (pos k : Nat) :
    (packedReads es b cl offsets pos).take k = packedReads (es.take k) b cl offsets pos :=
  List.ext_getElem (by simp [packedReads]) fun n _ _ ↦ by simp [packedReads]

/-- The counts of the bits of a search interval with the tests that the rows of
`Ratpoints.Sieve.packedReads` read are those of `Ratpoints.Sieve.intervalCounts`, for an interval
without the code `1`. -/
theorem bitsCounts_packedReads_eq_intervalCounts {H sp1 : Nat} {es es3 : List SieveEntry}
    {mgs3 : List Nat} {b : Nat} {cl : NumClass} {offsets : Array Nat} {pos : Nat}
    {bd : IntervalBounds} (h1 : ¬(intervalBits (Int64.ofNat b) bd (Int64.ofNat H) cl).1 = 1) :
    bitsCounts b (.mk fun _ ↦ fillChecks b H es3 mgs3) cl
      (fun j ↦ ((packedReads es b cl offsets pos).take sp1).all (·.2 j))
      (fun j ↦ (packedReads es b cl offsets pos).all (·.2 j))
      (intervalBits (Int64.ofNat b) bd (Int64.ofNat H) cl).2.1.toInt
      (intervalBits (Int64.ofNat b) bd (Int64.ofNat H) cl).2.2.toInt =
      intervalCounts b H sp1 es es3 mgs3 cl bd := by
  simp only [intervalCounts, h1, ↓reduceIte, take_packedReads, all_packedReads]

section

variable {b H sp1 : Nat} {es es3 : List SieveEntry} {mgs3 : List Nat} {cl : NumClass}
  {offsets : Array Nat} {pos : Nat} {iv : Array IntervalBounds} {cnt0 c c' : Counters}
  {pref suff : List IntervalBounds} {cur : IntervalBounds} {store st : RowStore}
  {doSetup : Bool} {specs specs' : List SieveSpec}
  {o : Option (Delivery σ × RowStore × Counters)}

theorem siftIntervalsCounts_zero (hs : store.Fits es) (specs : List SieveSpec) :
    SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 [] store true specs
      { cnt0 with sifts := cnt0.sifts + 1 } :=
  ⟨hs, nofun, nofun, Counters.ext (UInt64.add_zero _).symm (UInt64.add_zero _).symm
    (UInt64.add_zero _).symm (UInt64.add_zero _).symm (UInt64.add_zero _).symm rfl⟩

/-- After all the search intervals, none with the code `2`, the counters are those of
`Ratpoints.Sieve.siftCounts`. -/
theorem SiftIntervalsCounts.eq_siftCounts
    (h : SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 (ForIn.toList iv) store
      doSetup specs c) :
    c = cnt0 + siftCounts b H sp1 es es3 mgs3 cl iv := by
  have hne := h.ne_two
  rw [Std.Internal.ForIn.toList_array] at hne
  rw [h.eq_counts, siftCounts, Std.Internal.ForIn.toList_array,
    List.takeWhile_eq_self_of_forall fun bd hbd ↦ bne_iff_ne.mpr (hne bd hbd)]

/-- At an interval with the code `2`, the counters are those of `Ratpoints.Sieve.siftCounts`: the
intervals before it are those that `Ratpoints.Sieve.siftCounts` counts. -/
theorem SiftIntervalsCounts.post_of_two (hl : ForIn.toList iv = pref ++ cur :: suff)
    (h2 : (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 2)
    (h : o = none ∧ SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 pref store doSetup
      specs c) {r : Delivery σ} :
    r.quit = false → c = cnt0 + siftCounts b H sp1 es es3 mgs3 cl iv := by
  rw [Std.Internal.ForIn.toList_array] at hl
  intro
  rw [h.2.eq_counts, siftCounts, hl, List.takeWhile_append_of_pos
    fun bd hbd ↦ bne_iff_ne.mpr (h.2.ne_two bd hbd), List.takeWhile_cons_of_neg (by simp [h2]),
    List.append_nil]

/-- The counters after one more interval with the counts `k`, not with the code `2`. -/
theorem SiftIntervalsCounts.eq_counts_append
    (h : SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 pref store doSetup specs c)
    (hc : c' = c + intervalCounts b H sp1 es es3 mgs3 cl cur) :
    c' = cnt0 + ((pref ++ [cur]).map (intervalCounts b H sp1 es es3 mgs3 cl)).foldl (· + ·)
      { sifts := 1 } := by
  rw [hc, h.eq_counts, List.map_append, List.foldl_append, List.map_singleton, List.foldl_cons,
    List.foldl_nil, Counters.add_assoc]

/-- An interval with the code `1`, below `-H`, counts nothing. -/
theorem SiftIntervalsCounts.append_of_one
    (h2 : ¬(intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 2)
    (h1 : (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 1)
    (h : o = none ∧ SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 pref store doSetup
      specs c) :
    SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 (pref ++ [cur]) store doSetup
      specs c :=
  ⟨h.2.fits, h.2.specs_eq, fun bd hbd ↦ by
    rcases List.mem_append.mp hbd with hbd | hbd
    · exact h.2.ne_two bd hbd
    · rw [List.mem_singleton.mp hbd]; exact h2,
    h.2.eq_counts_append (by simp [intervalCounts, h1])⟩

/-- The sieve specs that `Ratpoints.Sieve.setRows` and `Ratpoints.Sieve.buildRows` make at the first
interval that asks for them are those of `Ratpoints.Sieve.packedReads`, and the store after them
fits the entries (`Ratpoints.Sieve.eq_map_fst_packedReads_of_eq_run_buildRows`). -/
theorem SiftIntervalsCounts.specs_eq_and_fits_of_eq_run_buildRows (hpos : cl.offset = some pos)
    (h : o = none ∧ SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 pref store doSetup
      specs c)
    (hr : (specs', st) = Id.run (buildRows
      (setRows store es (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets).2 es
      (es.map fun e ↦ b * e.dinv[cl.k]! % e.p)
      (setRows store es (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets).1 store)) :
    specs' = (packedReads es b cl offsets pos).map Prod.fst ∧ st.Fits es :=
  ⟨eq_map_fst_packedReads_of_eq_run_buildRows h.2.fits hpos hr,
    (h.2.fits.buildRows_setRows (fun e he ↦ Nat.mod_lt _ (h.2.fits.pos e he)) hr).2⟩

/-- Once the sieve specs are made, they are those of `Ratpoints.Sieve.packedReads`, and the store
fits the entries. -/
theorem SiftIntervalsCounts.specs_eq_and_fits_of_not_doSetup
    (h : o = none ∧ SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 pref store doSetup
      specs c)
    (hd : ¬doSetup = true) :
    specs = (packedReads es b cl offsets pos).map Prod.fst ∧ store.Fits es :=
  ⟨h.2.specs_eq (Bool.eq_false_iff.mpr hd), h.2.fits⟩

-- What the contract of the counters of `Ratpoints.Sieve.siftBits` needs of the sieve specs of
-- `Ratpoints.Sieve.packedReads`, in the shape of the verification condition.
private theorem pre_siftBits_counters {A : Nat} (hA : 1 ≤ A)
    (hoff : ∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!)
    (hsp : specs' = (packedReads es b cl offsets pos).map Prod.fst ∧ st.Fits es) :
    1 ≤ A ∧ (∀ s ∈ specs', s.Fits) ∧
      es.map (fun x ↦ magic x.p) = specs'.map (fun x ↦ magic x.p) :=
  hsp.1 ▸ ⟨hA, fits_of_mem_packedReads hoff, map_magic_packedReads ..⟩

/-- An interval whose bits `Ratpoints.Sieve.siftBits` sifts with the sieve specs of
`Ratpoints.Sieve.packedReads`, after which the callback has not stopped the search, adds its counts
(`Ratpoints.Sieve.bitsCounts_packedReads_eq_intervalCounts`). -/
theorem SiftIntervalsCounts.append_of_siftBits {r : Delivery σ}
    (h : o = none ∧ SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 pref store doSetup
      specs c)
    (h2 : ¬(intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 2)
    (h1 : ¬(intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).1 = 1)
    (hsf : specs' = (packedReads es b cl offsets pos).map Prod.fst ∧ st.Fits es)
    (hinv : ∀ e ∈ es, e.HasInverses)
    (hoff : ∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!)
    (hc : ∀ sfs : List (SieveSpec × (Int → Bool)), specs' = sfs.map Prod.fst →
      (∀ sf ∈ sfs, sf.1.Reads sf.2) → r.quit = false →
        c' = c + bitsCounts b (.mk fun _ ↦ fillChecks b H es3 mgs3) cl
          (fun j ↦ (sfs.take sp1).all (·.2 j)) (fun j ↦ sfs.all (·.2 j))
          (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.1.toInt
          (intervalBits (Int64.ofNat b) cur (Int64.ofNat H) cl).2.2.toInt)
    (hq : ¬r.quit = true) (ds : Bool) :
    SiftIntervalsCounts b H sp1 es es3 mgs3 cl offsets pos cnt0 (pref ++ [cur]) st ds specs' c' :=
  ⟨hsf.2, fun _ ↦ hsf.1, fun bd hbd ↦ by
    rcases List.mem_append.mp hbd with hbd | hbd
    · exact h.2.ne_two bd hbd
    · rw [List.mem_singleton.mp hbd]; exact h2,
    h.2.eq_counts_append (by
      rw [hc _ hsf.1 (reads_of_mem_packedReads hinv hoff) (Bool.eq_false_iff.mpr hq),
        bitsCounts_packedReads_eq_intervalCounts h1])⟩

end

-- A flag that is set is not clear, in the shape of the verification condition.
private theorem eq_false_imp_of_eq_true {x : Bool} {P : Prop} (h : x = true) : x = false → P :=
  fun h' ↦ absurd (h'.symm.trans h) Bool.false_ne_true

open Std.WP Lean.Order in
-- The contract of the counters of `Ratpoints.Sieve.sift` for the position `pos` of the row offsets
-- of the class.
private theorem sift_counters_spec_pos (c : List Int) (d H A b : Nat) (fl : CheckFlags)
    (sp1 : Nat) {es es3 : List SieveEntry} {mgs3 : List Nat} {cl : NumClass} {pos : Nat}
    (offsets : Array Nat) (iv : Array IntervalBounds) (store : RowStore) (r : Delivery σ)
    (cnt0 : Counters) (hA : 1 ≤ A) (hpos : cl.offset = some pos) (hinv : ∀ e ∈ es, e.HasInverses)
    (hoff : ∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!)
    (hs : store.Fits es) :
    ⦃ True ⦄
    sift process c d H A b fl sp1 es (es.map (magic ·.p)) (es.map fun e ↦ b * e.dinv[cl.k]! % e.p)
      cl offsets es3 mgs3 iv store r cnt0
    ⦃ fun r' ↦ r'.1.quit = false → r'.2.2 = cnt0 + siftCounts b H sp1 es es3 mgs3 cl iv ⦄ := by
  vcgen [sift, buildRows_value, siftBits_counters_spec] invariants
  · SiftIntervalsCountsLoopInvariant (σ := σ) b H sp1 es es3 mgs3 cl offsets pos iv cnt0
  all_goals subst_vars
  all_goals simp only [SiftIntervalsCountsLoopInvariant, meet_prop_eq_and, join_prop_eq_or,
    iSup_prop_eq_exists, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, exists_eq_left', exists_false, and_true] at *
  all_goals first
    | exact siftIntervalsCounts_zero hs _
    | exact SiftIntervalsCounts.eq_siftCounts ‹_›
    | exact SiftIntervalsCounts.post_of_two ‹_› ‹_› ‹_›
    | exact SiftIntervalsCounts.append_of_one ‹_› ‹_› ‹_›
    | exact eq_false_imp_of_eq_true ‹_›
    | (first
        | have hsf := SiftIntervalsCounts.specs_eq_and_fits_of_eq_run_buildRows hpos ‹_› ‹_›
        | have hsf := SiftIntervalsCounts.specs_eq_and_fits_of_not_doSetup ‹_› ‹_›)
      first
        | exact pre_siftBits_counters hA hoff hsf
        | exact SiftIntervalsCounts.append_of_siftBits ‹_› ‹_› ‹_› hsf hinv hoff ‹_› ‹_› _
    | (simp_all; done)

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
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry` with the reciprocals of their moduli. When the callback
does not stop the search, the denominator adds the counts of `Ratpoints.Sieve.siftCounts` to the
counters, for the position `pos` of the row offsets of `cl`, quantified in the postcondition. -/
@[spec]
theorem sift_spec (c : List Int) (d H A b : Nat) (fl : CheckFlags) (sp1 : Nat)
    (es : List SieveEntry) (mgs bp : List Nat) (cl : NumClass) (offsets : Array Nat)
    (es3 : List SieveEntry) (mgs3 : List Nat) (iv : Array IntervalBounds) (store : RowStore)
    (r : Delivery σ) (cnt : Counters) :
    ⦃ r.quit = false ∧ 1 ≤ A ∧ 0 < b ∧ b < 2 ^ 63 ∧ H < 2 ^ 63 ∧ (∀ e ∈ es3, e.IsPrimeEntry) ∧
        mgs3 = es3.map (fun e ↦ magic e.p) ∧ mgs = es.map (magic ·.p) ∧
        bp = es.map (fun e ↦ b * e.dinv[cl.k]! % e.p) ∧ (∀ e ∈ es, e.HasInverses) ∧ store.Fits es ⦄
    sift process c d H A b fl sp1 es mgs bp cl offsets es3 mgs3 iv store r cnt
    ⦃ fun r' ↦ r'.2.1.Fits es ∧ (∀ (w : UInt64) (pos : Nat) (rs : List (Int × Int)), cl.Packs w →
        cl.offset = some pos → (∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!) →
        RangesFor iv b H rs →
        r'.1 = r.deliver process (((numerators H).filter fun a ↦
          inRanges rs a && classBit w a && survives (es ++ es3) b a).flatMap
            (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl))) ∧
        ∀ pos : Nat, cl.offset = some pos →
          (∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!) → r'.1.quit = false →
          r'.2.2 = cnt + siftCounts b H sp1 es es3 mgs3 cl iv ⦄ :=
  ⟨fun ⟨hr, hA, hb, hb63, hH, hes, hmg3, hmg, hbp, hinv, hs⟩ ↦ by
    subst hmg hbp
    refine ⟨(sift_fits process c d H A b fl sp1 es _ cl offsets es3 _ iv store r cnt).le_wp hs,
      fun w pos rs hcl hpos hoff hiv ↦ ?_, fun pos hpos hoff ↦
        (sift_counters_spec_pos process c d H A b fl sp1 offsets iv store r cnt hA hpos hinv hoff
          hs).le_wp trivial⟩
    subst hmg3
    rw [((sift_spec_ranges process c d H A b fl sp1 offsets store r cnt hA
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
    (hinv : ∀ e ∈ es, e.HasInverses)
    (hoff : ∀ n (h : n < es.length), es[n].PackedFor cl offsets[pos + n]!)
    (hiv : RangesFor iv b H rs) (hs : store.Fits es) {r : Delivery σ} (hr : r.quit = false)
    (cnt : Counters) :
    (Id.run (sift process c d H A b fl sp1 es (es.map (magic ·.p))
      (es.map fun e ↦ b * e.dinv[cl.k]! % e.p) cl offsets es3 (es3.map fun e ↦ magic e.p) iv
        store r cnt)).1 =
      r.deliver process ((((Id.run (checkDen c d H b
        (Id.run (sieveDen H b (es ++ es3))))).toList.filter fun q ↦
          inRanges rs q.1 && classBit w q.1).map
            (if fl.reversed then swapPoint else id)).filter fun p ↦ !fl.noY || 0 ≤ p.2.1) :=
  (((sift_spec process c d H A b fl sp1 es _ _ cl offsets es3 _ iv store r cnt).le_wp
    ⟨hr, hA, hb, hb63, hH, hes, rfl, rfl, rfl, hinv, hs⟩).2.1 w pos rs hcl hpos hoff hiv).trans <|
    by
    rw [flatMap_checkNumWith_of_noCheck_eq_false hc, ← List.filter_filter, pointsOfDen_filter,
      ← (checkDen_spec c d H b _).le_wp trivial _ ((sieveDen_spec H b (es ++ es3)).le_wp trivial)]
    rfl

end Sieve

end Ratpoints

end
