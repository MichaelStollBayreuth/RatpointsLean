/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Denominators
public import Ratpoints.Proof.BitRange
public import Ratpoints.Proof.Packing
public import Ratpoints.Proof.RowStore
public import Ratpoints.Proof.Stages

import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
import Ratpoints.Proof.Shapes
import Ratpoints.Proof.Sift
import Std.Tactic.Do

/-!
# The contract of the run over the denominators

The run of the sieve over the denominators of a shape (`Ratpoints.Sieve.sieveRun`) delivers to the
callback, for each denominator of the shape's list that passes the tests of the shape, the points of
the check with the flags of the search (`Ratpoints.Sieve.checkNumWith`) of its numerators in the
search intervals, those in the ranges that the bounds of the run give for it
(`Ratpoints.Sieve.RangesFor`), that pass the word of its class modulo 64 and survive the sieve
entries, and returns when the callback stops the search; when the shape's list is a list `l`
filtered by a test, this is the delivery over `l`, in its order, of the points of the numerators
that pass that test, the tests of the shape, the class word and the sieve entries.

## Main statements

* `Ratpoints.Sieve.sieveRun_spec`: for a delivery whose flag of the stop is clear, any cut points,
  sieve entries of the first two stages, the first `sp2`, with their tables of inverses
  (`Ratpoints.Sieve.Factor.HasInverses`) and the row offsets of the packings of the classes with a
  pattern (`Ratpoints.Sieve.OffsetsFor`), whose bits are those of the word `db`, a store of the
  tables of rows that fits them (`Ratpoints.Sieve.RowStore.Fits`), sieve entries from the cut point
  `sp2` on of the shape that the third stage needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), the
  reciprocals of the moduli, the denominators from `bLow ≥ 1` to `bHigh < 2 ^ 63` and a height below
  `2 ^ 63`, the run gives the delivery (`Ratpoints.Delivery.deliver`), for each denominator `b` of
  the list of the shape that passes its tests (`Ratpoints.Sieve.Shape.dens`,
  `Ratpoints.Sieve.Shape.keep`), of the points of the check with the flags of the numerators
  `-H, …, H` in one of the ranges `rs b` that the bounds of the search intervals give for `b`
  (`Ratpoints.Sieve.RangesFor`), that pass the class word `nb[b mod 64]`
  (`Ratpoints.Sieve.classBit`), for any words `nb` that the classes pack
  (`Ratpoints.Sieve.NumClass.Packs`) and any such ranges, and survive the sieve entries of all three
  stages; `Ratpoints.Sieve.run_sieveRun` states this as an equation.
* `Ratpoints.Sieve.fst_run_runSetup`, `Ratpoints.Sieve.snd_run_runSetup`: the shape that
  `Ratpoints.Sieve.runSetup` chooses from the flags of the search, and the bounds of the search
  intervals that it makes.
* `Ratpoints.Sieve.run_sieveRun_of_eq_filter`: when the list of the shape is a list `l` filtered by
  a test `p`, the run delivers, over the denominators `b` of `l`, the points of the numerators that
  pass `p b`, the tests of the shape on `b`, the class word and the sieve entries.

## Implementation notes

The contract is proved with `vcgen`, with loop invariants that are named definitions, in a file with
Mathlib, like the other contracts of the side of the denominators. The run returns when the callback
stops the search: the invariant of the loop has the disjunct of the early return
(`Ratpoints.Sieve.SieveRunLoopInvariant`), and the delivery of the points of a prefix of the
denominators after which the flag is set is that of all of them
(`Ratpoints.Delivery.deliver_flatMap_eq_of_prefix`). The tests of the shape and the list of its
denominators are read as values, `Id.run` of their computations, so that the contract of the run
does not depend on their contracts, which are stated in the files of their components; their own
loops are not unfolded by `vcgen` here. The denominators of the shapes lie between `bLow` and
`bHigh` (`Ratpoints.Sieve.Shape.le_and_le_of_mem_dens`), and the class of each that passes the tests
of the shape has a pattern (`Ratpoints.Sieve.Shape.bits_ne_zero_of_mem_dens`), so its row offsets,
so that the contract of the sieve of one denominator in the packing of its class
(`Ratpoints.Sieve.sift_spec`) applies to each of them, with the first `sp2` sieve entries in the
first two stages, the residues of `fill_bp_list` (`Ratpoints.Sieve.fillBpList_eq_map`,
`Ratpoints.Sieve.SieveRunInvariant.eq_deliver_append`) and the store of the tables of rows, which
fits these entries before each denominator and after it (`Ratpoints.Sieve.RowStore.Fits`, a field of
`Ratpoints.Sieve.SieveRunInvariant`). The words of the classes are not arguments of the run, which
reads the classes: they are quantified in the postcondition, as in
`Ratpoints.Sieve.SieveRunInvariant`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

open BruteForce

-- The list of the denominators of a shape, as a value for the contract of the run.
private theorem dens_value (s : Shape) (db : UInt64) (bLow bHigh : ℕ) :
    ⦃ True ⦄ s.dens db bLow bHigh ⦃ fun r ↦ r = Id.run (s.dens db bLow bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

-- The tests of a shape on a denominator, as a value for the contract of the run.
private theorem keep_value (s : Shape) (cls : Vector NumClass 64) (b : ℕ) :
    ⦃ True ⦄ s.keep cls b ⦃ fun r ↦ r = Id.run (s.keep cls b) ⦄ :=
  ⟨fun _ ↦ rfl⟩

variable {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ)

/-- The invariant of the loop of `Ratpoints.Sieve.sieveRun` over the denominators of a shape, from
the delivery `r0`, after the denominators `pref`: the callback has not stopped the search, the store
of the tables of rows fits the sieve entries of the first two stages, the first `sp2` of `entries`
(`Ratpoints.Sieve.RowStore.Fits`), and for words `nb` of the classes modulo 64 that the classes
`cls` pack and ranges `rs b` of the numerators that the bounds `iv` of the search intervals give for
the denominators `b` from `bLow` to `bHigh` (`Ratpoints.Sieve.RangesFor`), the delivery `r` is that
of the points of the check with the flags `fl` (`Ratpoints.Sieve.checkNumWith`) over the
denominators `b` of `pref` that pass the test `keep` and the numerators `-H, …, H` in one of the
ranges `rs b` that pass the class word `nb[b mod 64]` (`Ratpoints.Sieve.classBit`) and survive the
sieve entries `entries`. -/
structure SieveRunInvariant (c : List ℤ) (d H : ℕ) (fl : CheckFlags) (entries : List SieveEntry)
    (sp2 : ℕ) (cls : Vector NumClass 64) (iv : Array IntervalBounds) (bLow bHigh : ℕ)
    (keep : ℕ → Bool) (r0 : Delivery σ) (pref : List ℕ) (r : Delivery σ) (store : RowStore) :
    Prop where
  /-- The callback has not stopped the search. -/
  quit_eq_false : r.quit = false
  /-- The store fits the sieve entries of the first two stages. -/
  fits : store.Fits (entries.take sp2)
  /-- The delivery is that of the points of the denominators of `pref` that pass `keep` and the
  numerators in their ranges that pass their class words and survive the entries. -/
  eq_deliver : ∀ (nb : Vector UInt64 64) (rs : ℕ → List (ℤ × ℤ)), (∀ b < 64, cls[b]!.Packs nb[b]!) →
    (∀ b, bLow ≤ b → b ≤ bHigh → RangesFor iv b H (rs b)) →
    r = r0.deliver process ((pref.filter keep).flatMap fun b : ℕ ↦ ((numerators H).filter
      fun a ↦ inRanges (rs b) a && classBit nb[b % 64]! a && survives entries b a).flatMap
        (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl))

/-- The invariant of the loop of `Ratpoints.Sieve.sieveRun` over the list `dens` of the denominators
of a shape, whose state is the value of a return, the delivery and the store of the tables of rows:
before a return, `Ratpoints.Sieve.SieveRunInvariant` after the denominators done; after the return
at a stop, the value returned is the delivery of the points of all the denominators of `dens` that
pass `keep`. -/
def SieveRunLoopInvariant (c : List ℤ) (d H : ℕ) (fl : CheckFlags) (entries : List SieveEntry)
    (sp2 : ℕ) (cls : Vector NumClass 64) (iv : Array IntervalBounds) (bLow bHigh : ℕ)
    (keep : ℕ → Bool) (r0 : Delivery σ) (dens : List ℕ) :
    Std.WP.Invariant ℕ (Option (Delivery σ) × Delivery σ × RowStore) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun pref _ s ↦ SieveRunInvariant process c d H fl entries sp2 cls iv bLow bHigh keep r0 pref
      s.1 s.2)
    (fun ret _ ↦ ∀ (nb : Vector UInt64 64) (rs : ℕ → List (ℤ × ℤ)),
      (∀ b < 64, cls[b]!.Packs nb[b]!) → (∀ b, bLow ≤ b → b ≤ bHigh → RangesFor iv b H (rs b)) →
      ret = r0.deliver process ((dens.filter keep).flatMap fun b : ℕ ↦ ((numerators H).filter
        fun a ↦ inRanges (rs b) a && classBit nb[b % 64]! a && survives entries b a).flatMap
          (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)))

-- A denominator of the loop over the list of a shape is positive and below `2 ^ 63`.
private theorem pos_and_lt_of_eq_append_cons {s : Shape} {db : UInt64} {bLow bHigh : ℕ}
    (hbLow : 1 ≤ bLow) (hbHigh : bHigh < 2 ^ 63) {pref suff : List ℕ} {cur : ℕ}
    (hl : Id.run (s.dens db bLow bHigh) = pref ++ cur :: suff) :
    0 < cur ∧ cur < 2 ^ 63 := by
  lia [s.le_and_le_of_mem_dens db hbLow (hl ▸ List.mem_append_right pref List.mem_cons_self)]

-- The entries with the offsets of the packing of a class have what `fill_bp_list` needs.
private theorem forall_mem_of_packedFor {es : List SieveEntry} {cl : NumClass} {offsets : Array ℕ}
    {pos : ℕ} (h : ∀ n (hn : n < es.length), es[n].PackedFor cl offsets[pos + n]!) :
    ∀ e ∈ es, 0 < e.p ∧ e.p ≤ maxPrimeEven ∧ e.dinv[cl.k]! < e.p := fun _ he ↦
  have ⟨n, hn, he⟩ := List.getElem_of_mem he
  he ▸ ⟨(h n hn).pos, (h n hn).le_maxPrimeEven, (h n hn).dinv_lt⟩

-- The class of a denominator of the loop over the list of a shape that its tests let through has a
-- pattern (`Ratpoints.Sieve.Shape.bits_ne_zero_of_mem_dens`), and so the row offsets of the packing
-- of the class for the first `sp2` sieve entries.
private theorem exists_packedFor_of_eq_append_cons {entries : List SieveEntry}
    {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64} {shape : Shape} {bLow bHigh : ℕ}
    {pref suff : List ℕ} {cur sp2 : ℕ} (hoff : OffsetsFor cls (entries.take sp2) offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0))
    (hl : Id.run (shape.dens db bLow bHigh) = pref ++ cur :: suff)
    (hk : Id.run (shape.keep cls cur) = true) :
    ∃ pos, cls[cur % 64]!.offset = some pos ∧ ∀ n (h : n < (entries.take sp2).length),
      (entries.take sp2)[n].PackedFor cls[cur % 64]! offsets[pos + n]! :=
  hoff (cur % 64) (Nat.mod_lt _ (by decide)) (shape.bits_ne_zero_of_mem_dens hdb
    (hl ▸ List.mem_append_right pref List.mem_cons_self) hk)

-- The residues of `fill_bp_list` for a denominator of the loop over the list of a shape that its
-- tests let through are those of the entries of the first two stages
-- (`Ratpoints.Sieve.fillBpList_eq_map`).
private theorem fillBpList_eq_map_of_eq_append_cons {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    {shape : Shape} {bLow bHigh : ℕ} {pref suff : List ℕ} {cur sp2 : ℕ}
    (hmg : magics.toList = entries.map fun e ↦ magic e.p)
    (hoff : OffsetsFor cls (entries.take sp2) offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0))
    (hl : Id.run (shape.dens db bLow bHigh) = pref ++ cur :: suff)
    (hk : Id.run (shape.keep cls cur) = true) :
    fillBpList cur cls[cur % 64]!.k (entries.take sp2) (magics.toList.take sp2) =
      (entries.take sp2).map fun e ↦ cur * e.dinv[cls[cur % 64]!.k]! % e.p := by
  obtain ⟨pos, -, hpf⟩ := exists_packedFor_of_eq_append_cons hoff hdb hl hk
  rw [hmg, ← List.map_take]
  exact fillBpList_eq_map (forall_mem_of_packedFor hpf)

section

variable {process} {c : List ℤ} {d H : ℕ} {fl : CheckFlags} {entries : List SieveEntry}
  {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64} {shape : Shape}
  {iv : Array IntervalBounds} {bLow bHigh : ℕ} {pref suff : List ℕ} {r0 r r' : Delivery σ}
  {store st : RowStore} {cur sp2 : ℕ} {o : Option (Delivery σ)} {P : Prop}

/-- The delivery after the denominator `cur` of the list of the shape that its tests let through,
for words `nb` that the classes pack and ranges `rs b` of the numerators of the search intervals:
by the contract of `Ratpoints.Sieve.sift` (`Ratpoints.Sieve.sift_spec`) with the class
`cls[cur mod 64]`, which has a pattern (`Ratpoints.Sieve.Shape.bits_ne_zero_of_mem_dens`) and so
the row of its offsets, the first `sp2` sieve entries in the first two stages and the others in the
third, and the ranges of `cur`, which lies between `bLow ≥ 1` and `bHigh`
(`Ratpoints.Sieve.Shape.le_and_le_of_mem_dens`), that of the points of the denominators of
`pref ++ [cur]` that pass the tests. -/
theorem SieveRunInvariant.eq_deliver_append (hoff : OffsetsFor cls (entries.take sp2) offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0)) (hbLow : 1 ≤ bLow)
    (hl : Id.run (shape.dens db bLow bHigh) = pref ++ cur :: suff)
    (h : SieveRunInvariant process c d H fl entries sp2 cls iv bLow bHigh
      (fun b ↦ Id.run (shape.keep cls b)) r0 pref r store)
    (hk : Id.run (shape.keep cls cur) = true)
    (hpts : ∀ (w : UInt64) (pos : ℕ) (rs : List (ℤ × ℤ)), cls[cur % 64]!.Packs w →
      cls[cur % 64]!.offset = some pos → (∀ n (h : n < (entries.take sp2).length),
        (entries.take sp2)[n].PackedFor cls[cur % 64]! offsets[pos + n]!) →
      RangesFor iv cur H rs →
      r' = r.deliver process (((numerators H).filter fun a ↦ inRanges rs a && classBit w a &&
        survives (entries.take sp2 ++ entries.drop sp2) cur a).flatMap
          (checkNumWith (scaledCoeffs c d cur) (if d % 2 = 1 then cur else 1) cur fl)))
    (nb : Vector UInt64 64) (rs : ℕ → List (ℤ × ℤ)) (hnb : ∀ b < 64, cls[b]!.Packs nb[b]!)
    (hrs : ∀ b, bLow ≤ b → b ≤ bHigh → RangesFor iv b H (rs b)) :
    r' = r0.deliver process (((pref ++ [cur]).filter fun b ↦ Id.run (shape.keep cls b)).flatMap
      fun b : ℕ ↦ ((numerators H).filter fun a ↦ inRanges (rs b) a && classBit nb[b % 64]! a &&
        survives entries b a).flatMap
          (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)) := by
  obtain ⟨pos, hpos, hpf⟩ := exists_packedFor_of_eq_append_cons hoff hdb hl hk
  have hb :=
    shape.le_and_le_of_mem_dens db hbLow (hl ▸ List.mem_append_right pref List.mem_cons_self)
  have := hpts nb[cur % 64]! pos (rs cur) (hnb _ (Nat.mod_lt _ (by decide))) hpos hpf
    (hrs cur hb.1 hb.2)
  rw [List.take_append_drop] at this
  rw [this, h.eq_deliver nb rs hnb hrs, ← Delivery.deliver_append]
  simp [List.filter_append, hk]

/-- The denominator `cur` of the list of the shape that its tests let through, after which the
callback has not stopped the search, keeps the invariant; the store after it fits the sieve entries
of the first two stages. The contract of one denominator enters in the shape of the verification
condition, with what it says of the counters, `P`, which the run discards. -/
theorem SieveRunInvariant.append_of_keep (hoff : OffsetsFor cls (entries.take sp2) offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0)) (hbLow : 1 ≤ bLow)
    (hl : Id.run (shape.dens db bLow bHigh) = pref ++ cur :: suff)
    (h : o = none ∧ SieveRunInvariant process c d H fl entries sp2 cls iv bLow bHigh
      (fun b ↦ Id.run (shape.keep cls b)) r0 pref r store)
    (hk : Id.run (shape.keep cls cur) = true)
    (hpts : st.Fits (entries.take sp2) ∧ (∀ (w : UInt64) (pos : ℕ) (rs : List (ℤ × ℤ)),
      cls[cur % 64]!.Packs w → cls[cur % 64]!.offset = some pos →
      (∀ n (h : n < (entries.take sp2).length),
        (entries.take sp2)[n].PackedFor cls[cur % 64]! offsets[pos + n]!) →
      RangesFor iv cur H rs →
      r' = r.deliver process (((numerators H).filter fun a ↦ inRanges rs a && classBit w a &&
        survives (entries.take sp2 ++ entries.drop sp2) cur a).flatMap
          (checkNumWith (scaledCoeffs c d cur) (if d % 2 = 1 then cur else 1) cur fl))) ∧ P)
    (hq : ¬r'.quit = true) :
    SieveRunInvariant process c d H fl entries sp2 cls iv bLow bHigh
      (fun b ↦ Id.run (shape.keep cls b)) r0 (pref ++ [cur]) r' st :=
  ⟨Bool.eq_false_iff.mpr hq, hpts.1, h.2.eq_deliver_append hoff hdb hbLow hl hk hpts.2.1⟩

/-- The denominator `cur` of the list of the shape that its tests let through, after which the
callback has stopped the search: the delivery is that of the points of all the denominators of the
list that pass the tests (`Ratpoints.Delivery.deliver_flatMap_eq_of_prefix`). The contract of one
denominator enters in the shape of the verification condition, with what it says of the counters,
`P`, which the run discards. -/
theorem SieveRunInvariant.eq_deliver_of_quit (hoff : OffsetsFor cls (entries.take sp2) offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0)) (hbLow : 1 ≤ bLow)
    (hl : Id.run (shape.dens db bLow bHigh) = pref ++ cur :: suff)
    (h : o = none ∧ SieveRunInvariant process c d H fl entries sp2 cls iv bLow bHigh
      (fun b ↦ Id.run (shape.keep cls b)) r0 pref r store)
    (hk : Id.run (shape.keep cls cur) = true)
    (hpts : st.Fits (entries.take sp2) ∧ (∀ (w : UInt64) (pos : ℕ) (rs : List (ℤ × ℤ)),
      cls[cur % 64]!.Packs w → cls[cur % 64]!.offset = some pos →
      (∀ n (h : n < (entries.take sp2).length),
        (entries.take sp2)[n].PackedFor cls[cur % 64]! offsets[pos + n]!) →
      RangesFor iv cur H rs →
      r' = r.deliver process (((numerators H).filter fun a ↦ inRanges rs a && classBit w a &&
        survives (entries.take sp2 ++ entries.drop sp2) cur a).flatMap
          (checkNumWith (scaledCoeffs c d cur) (if d % 2 = 1 then cur else 1) cur fl))) ∧ P)
    (hq : r'.quit = true) (nb : Vector UInt64 64) (rs : ℕ → List (ℤ × ℤ))
    (hnb : ∀ b < 64, cls[b]!.Packs nb[b]!)
    (hrs : ∀ b, bLow ≤ b → b ≤ bHigh → RangesFor iv b H (rs b)) :
    r' = r0.deliver process (((Id.run (shape.dens db bLow bHigh)).filter
      fun b ↦ Id.run (shape.keep cls b)).flatMap fun b : ℕ ↦ ((numerators H).filter
        fun a ↦ inRanges (rs b) a && classBit nb[b % 64]! a && survives entries b a).flatMap
          (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)) := by
  have he := h.2.eq_deliver_append hoff hdb hbLow hl hk hpts.2.1 nb rs hnb hrs
  rw [he] at hq ⊢
  refine (Delivery.deliver_flatMap_eq_of_prefix process ?_ _ hq).symm
  rw [hl, List.append_cons pref cur suff]
  exact (List.prefix_append (pref ++ [cur]) suff).filter _

theorem SieveRunInvariant.quit_eq_false_and_fits
    (h : o = none ∧ SieveRunInvariant process c d H fl entries sp2 cls iv bLow bHigh
      (fun b ↦ Id.run (shape.keep cls b)) r0 pref r store) :
    r.quit = false ∧ store.Fits (entries.take sp2) :=
  ⟨h.2.quit_eq_false, h.2.fits⟩

theorem sieveRunInvariant_nil (c : List ℤ) (d H : ℕ) (fl : CheckFlags) (cls : Vector NumClass 64)
    (keep : ℕ → Bool) (hr : r0.quit = false) (hs : store.Fits (entries.take sp2)) :
    SieveRunInvariant process c d H fl entries sp2 cls iv bLow bHigh keep r0 [] r0 store :=
  ⟨hr, hs, fun _ _ _ _ ↦ by simp⟩

/-- A denominator that the tests of the shape reject delivers nothing. -/
theorem SieveRunInvariant.append_of_not_keep {keep : ℕ → Bool}
    (h : o = none ∧ SieveRunInvariant process c d H fl entries sp2 cls iv bLow bHigh keep r0 pref r
      store)
    (hk : ¬keep cur = true) :
    SieveRunInvariant process c d H fl entries sp2 cls iv bLow bHigh keep r0 (pref ++ [cur]) r
      store :=
  ⟨h.2.quit_eq_false, h.2.fits, fun nb rs hnb hrs ↦ by
    rw [h.2.eq_deliver nb rs hnb hrs]
    simp [List.filter_append, hk]⟩

end

open Std.WP Lean.Order in
/-- The callback has not stopped the search; the array size `A ≥ 1` makes the loops over the pieces
end; the sieve entries of the first two stages, the first `sp2`, have their tables of inverses and
the row offsets of the packings of the classes `cls` with a pattern (`Ratpoints.Sieve.OffsetsFor`),
whose bits are those of the word `db` of the word shape, the store of the tables of rows fits them
(`Ratpoints.Sieve.RowStore.Fits`), and the sieve entries from position `sp2` on, those of the third
stage, have the shape that it needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`); `magics` holds the
reciprocals of the moduli in the order of the entries, as the stages read them; the test for common
factors on the words of the C code needs the denominators, which lie between `bLow ≥ 1` and `bHigh`
(`Ratpoints.Sieve.Shape.le_and_le_of_mem_dens`), and the height below `2 ^ 63`. Each denominator
delivers the points of the numerators in the ranges that the bounds `iv` of the search intervals
give for it (`Ratpoints.Sieve.RangesFor`, `Ratpoints.Sieve.sift_spec`). The run returns when the
callback stops the search, which the delivery of the whole list of points accounts for
(`Ratpoints.Delivery.deliver_flatMap_eq_of_prefix`). The words `nb` of the classes modulo 64 that
the classes pack and the ranges `rs b` of the numerators of each denominator are quantified in the
postcondition, since the program does not mention them. -/
@[spec]
theorem sieveRun_spec (c : List ℤ) (d H A : ℕ) (fl : CheckFlags) (sp1 sp2 : ℕ)
    (entries : List SieveEntry) (magics : Array ℕ) (cls : Vector NumClass 64) (offsets : Array ℕ)
    (db : UInt64) (shape : Shape) (iv : Array IntervalBounds) (bLow bHigh : ℕ) (store : RowStore)
    (r : Delivery σ) :
    ⦃ r.quit = false ∧ 1 ≤ A ∧ (∀ e ∈ entries.drop sp2, e.IsPrimeEntry) ∧
        magics.toList = entries.map (fun e ↦ magic e.p) ∧ 1 ≤ bLow ∧ bHigh < 2 ^ 63 ∧ H < 2 ^ 63 ∧
        (∀ e ∈ entries.take sp2, ∀ f ∈ e.factors, f.HasInverses e.p) ∧
        OffsetsFor cls (entries.take sp2) offsets ∧
        (∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0)) ∧ store.Fits (entries.take sp2) ⦄
    sieveRun process c d H A fl sp1 sp2 entries magics cls offsets db shape iv bLow bHigh store r
    ⦃ fun r' ↦ ∀ (nb : Vector UInt64 64) (rs : ℕ → List (ℤ × ℤ)), (∀ b < 64, cls[b]!.Packs nb[b]!) →
        (∀ b, bLow ≤ b → b ≤ bHigh → RangesFor iv b H (rs b)) →
        r' = r.deliver process (((Id.run (shape.dens db bLow bHigh)).filter
          fun b ↦ Id.run (shape.keep cls b)).flatMap fun b : ℕ ↦ ((numerators H).filter
            fun a ↦ inRanges (rs b) a && classBit nb[b % 64]! a && survives entries b a).flatMap
              (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)) ⦄ := by
  vcgen [sieveRun, dens_value, keep_value] invariants
  | inv1 => SieveRunLoopInvariant process c d H fl entries sp2 cls iv bLow bHigh
      (fun b ↦ Id.run (shape.keep cls b)) r (Id.run (shape.dens db bLow bHigh))
  all_goals obtain ⟨hr, hA, hes, hmg, hb, hb63, hH, hinv, hoff, hdb, hs⟩ := ‹r.quit = false ∧ _›
  all_goals subst_vars
  all_goals simp only [SieveRunLoopInvariant, meet_prop_eq_and, join_prop_eq_or,
    iSup_prop_eq_exists, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, exists_eq_left', exists_false, and_true] at *
  all_goals first
    | exact sieveRunInvariant_nil c d H fl cls _ hr hs
    | (rename_i h; exact h _ _ ‹_› ‹_›)
    | exact SieveRunInvariant.eq_deliver ‹_› _ _ ‹_› ‹_›
    | exact SieveRunInvariant.append_of_not_keep ‹_› ‹_›
    | exact SieveRunInvariant.append_of_keep hoff hdb hb ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact SieveRunInvariant.eq_deliver_of_quit hoff hdb hb ‹_› ‹_› ‹_› ‹_› ‹_›
    | have := pos_and_lt_of_eq_append_cons hb hb63 ‹_›
      have := SieveRunInvariant.quit_eq_false_and_fits ‹_›
      exact ⟨this.1, hA, ‹0 < _ ∧ _›.1, ‹0 < _ ∧ _›.2, hH, hes, by rw [hmg, List.map_drop],
        by rw [hmg, List.map_take], fillBpList_eq_map_of_eq_append_cons hmg hoff hdb ‹_› ‹_›, hinv,
        this.2⟩

/-- `Ratpoints.Sieve.sieveRun_spec` as an equation, which the proofs use without the program
logic. -/
theorem run_sieveRun (c : List ℤ) (d H : ℕ) (fl : CheckFlags) (sp1 sp2 : ℕ) {A : ℕ} (hA : 1 ≤ A)
    {entries : List SieveEntry} (hes : ∀ e ∈ entries.drop sp2, e.IsPrimeEntry) {magics : Array ℕ}
    (hmg : magics.toList = entries.map fun e ↦ magic e.p)
    (hinv : ∀ e ∈ entries.take sp2, ∀ f ∈ e.factors, f.HasInverses e.p) {cls : Vector NumClass 64}
    {offsets : Array ℕ} (hoff : OffsetsFor cls (entries.take sp2) offsets) {db : UInt64}
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0)) {nb : Vector UInt64 64}
    (hnb : ∀ b < 64, cls[b]!.Packs nb[b]!) (shape : Shape) {iv : Array IntervalBounds}
    {bLow bHigh : ℕ} {rs : ℕ → List (ℤ × ℤ)}
    (hiv : ∀ b, bLow ≤ b → b ≤ bHigh → RangesFor iv b H (rs b))
    (hbLow : 1 ≤ bLow) (hbHigh : bHigh < 2 ^ 63) (hH : H < 2 ^ 63) {store : RowStore}
    (hs : store.Fits (entries.take sp2)) {r : Delivery σ} (hr : r.quit = false) :
    Id.run (sieveRun process c d H A fl sp1 sp2 entries magics cls offsets db shape iv bLow bHigh
      store r) = r.deliver process (((Id.run (shape.dens db bLow bHigh)).filter
        fun b ↦ Id.run (shape.keep cls b)).flatMap fun b : ℕ ↦ ((numerators H).filter
          fun a ↦ inRanges (rs b) a && classBit nb[b % 64]! a && survives entries b a).flatMap
            (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((sieveRun_spec process c d H A fl sp1 sp2 entries magics cls offsets
    db shape iv bLow bHigh store r).le_wp
      ⟨hr, hA, hes, hmg, hbLow, hbHigh, hH, hinv, hoff, hdb, hs⟩) nb rs hnb hiv

/-- When the list of the denominators of the shape is a list `l` filtered by a test `p`, the run
delivers, over the denominators `b` of `l`, the points of the check with the flags `fl`
(`Ratpoints.Sieve.checkNumWith`) of the numerators `a` of `-H, …, H` that pass the test of the
sieve: `b` passes `p` and the tests of the shape, and `a` lies in one of the ranges `rs b` that the
bounds of the search intervals give for `b` (`Ratpoints.Sieve.RangesFor`), passes the word of its
class among the words `nb` that the classes `cls` pack and survives the sieve entries
(`Ratpoints.Sieve.run_sieveRun`). -/
theorem run_sieveRun_of_eq_filter {c : List ℤ} {d H A : ℕ} {fl : CheckFlags} {sp1 sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} {nb : Vector UInt64 64} {shape : Shape} {iv : Array IntervalBounds}
    {bLow bHigh : ℕ} {rs : ℕ → List (ℤ × ℤ)} {store : RowStore} {l : List ℕ} {p : ℕ → Bool}
    (hA : 1 ≤ A) (hes : ∀ e ∈ entries.drop sp2, e.IsPrimeEntry)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p)
    (hinv : ∀ e ∈ entries.take sp2, ∀ f ∈ e.factors, f.HasInverses e.p)
    (hoff : OffsetsFor cls (entries.take sp2) offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0))
    (hnb : ∀ b < 64, cls[b]!.Packs nb[b]!)
    (hiv : ∀ b, bLow ≤ b → b ≤ bHigh → RangesFor iv b H (rs b)) (hbLow : 1 ≤ bLow)
    (hbHigh : bHigh < 2 ^ 63) (hH : H < 2 ^ 63) (hs : store.Fits (entries.take sp2))
    (hdens : Id.run (shape.dens db bLow bHigh) = l.filter p) {r : Delivery σ}
    (hr : r.quit = false) :
    Id.run (sieveRun process c d H A fl sp1 sp2 entries magics cls offsets db shape iv bLow bHigh
      store r) = r.deliver process (l.flatMap fun b : ℕ ↦ ((numerators H).filter fun a ↦
        p b && Id.run (shape.keep cls b) && inRanges (rs b) a && classBit nb[b % 64]! a &&
          survives entries b a).flatMap
            (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)) := by
  rw [run_sieveRun process c d H fl sp1 sp2 hA hes hmg hinv hoff hdb hnb shape hiv hbLow hbHigh hH
    hs hr, hdens, List.filter_filter, List.flatMap_filter_flatMap_filter]
  simp only [Bool.and_comm (Id.run (shape.keep cls _)) (p _), Bool.and_assoc]

/-- The shape that `Ratpoints.Sieve.runSetup` chooses from the flags of the search. -/
theorem fst_run_runSetup (useSquares : Bool) (us1 : Option (List Setup.DenInfo × List ℕ))
    (checkDenom useJacobi : Bool) (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal)
    (lcf : ℤ) (H bHigh : ℕ) (domain : List (Double × Double)) :
    (Id.run (runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf H bHigh domain)).1 =
      if useSquares then .squares else match us1 with
        | some (info, divisors) => .squares1 info divisors
        | none => if checkDenom then .words forb forbVal useJacobi
            (if useJacobi then Id.run (jacobiSetup lcf bHigh) else none) lcf else .all := by
  cases useSquares <;> rcases us1 with _ | ⟨info, divisors⟩ <;> cases checkDenom <;>
    cases useJacobi <;> rfl

/-- The bounds of the search intervals of the run that `Ratpoints.Sieve.runSetup` makes. -/
theorem snd_run_runSetup (useSquares : Bool) (us1 : Option (List Setup.DenInfo × List ℕ))
    (checkDenom useJacobi : Bool) (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal)
    (lcf : ℤ) (H bHigh : ℕ) (domain : List (Double × Double)) :
    (Id.run (runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf H bHigh domain)).2 =
      Id.run (exactBounds domain H.toInt64 bHigh.toInt64) := by
  cases useSquares <;> rcases us1 with _ | ⟨info, divisors⟩ <;> cases checkDenom <;>
    cases useJacobi <;> rfl

end Sieve

end Ratpoints

end
