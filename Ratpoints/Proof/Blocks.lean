/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.BlockLoops
public import Ratpoints.Proof.BlockPlan
public import Ratpoints.Proof.Shapes
public import Ratpoints.Proof.Sift

import Ratpoints.Proof.Denominators
import Ratpoints.Proof.Params

/-!
# The blocks of the run

The run sifts the denominators of its shape in blocks
(`Ratpoints.Sieve.Shape.blockPlan`, `Ratpoints.Sieve.BlockPlan.steps`), each with the cut points of
the decision in force for it (`Ratpoints.Sieve.findDecision`, `Ratpoints.Sieve.runBlock`), the loop
of the shape over the steps of the block (`Ratpoints.Sieve.Shape.blockLoop`) handing each
denominator that passes the tests of the shape to the sieve of one denominator
(`Ratpoints.Sieve.siftDen`). The blocks of the run, in order, visit the denominators of the listing
of the shape (`Ratpoints.Sieve.Shape.dens`) in its order
(`Ratpoints.Sieve.Shape.flatMap_blockDens`), and a block delivers the points of its denominators
(`Ratpoints.Sieve.blockDens`) that pass the tests of the shape, each with the entries of the first
three stages of its decision (`Ratpoints.Sieve.denPoints`), keeps a store of the tables of rows that
fits all the entries, and counts closed forms of its denominators (`Ratpoints.Sieve.denCounts`),
which depend neither on the callback nor on the flags of the output
(`Ratpoints.Sieve.runBlock_spec`).

## Main definitions

* `Ratpoints.Sieve.RunWords`, `Ratpoints.Sieve.denPoints`, `Ratpoints.Sieve.denCounts`: the words of
  the classes and the ranges of the numerators that the deliveries are stated for, the points of a
  denominator, and the counts of its sieve.
* `Ratpoints.Sieve.blockDens`: the denominators of a block, before the tests of the shape.

## Main statements

* `Ratpoints.Sieve.siftDen_spec`: the contract of the step of the blocks, the sieve of one
  denominator with the entries cut by a decision.
* `Ratpoints.Sieve.Shape.flatMap_blockDens`: the blocks of the run visit the denominators of the
  listing of the shape in its order; `Ratpoints.Sieve.Shape.flatMap_filter_blockDens`: so lists of
  the denominators made block by block are lists over the listing;
  `Ratpoints.Sieve.Shape.eq_of_mem_blockDens`: when the listing has no denominator twice, a
  denominator lies in one block at most.
* `Ratpoints.Sieve.forbFits_of_forall_isForbiddenEntry`,
  `Ratpoints.Sieve.forbFits_fst_run_runSetup`: the forbidden divisors of the loop of the tables have
  what the loop of the word shape needs, and so has the shape that `Ratpoints.Sieve.runSetup`
  chooses with them.
* `Ratpoints.Sieve.decisionWF_getElem!_findDecision`: the decision in force for a block, among
  well-formed decisions, is well-formed.
* `Ratpoints.Sieve.runBlock_spec`: the contract of one block.

## Implementation notes

The store frame of the sieve of one denominator (`Ratpoints.Sieve.RowStore.Fits.fits_run_sift`) is
in `Ratpoints.Proof.Sift`, the loops of the shapes in `Ratpoints.Proof.BlockLoops`, the plan of the
blocks and the well-formed decisions (`Ratpoints.Sieve.DecisionWF`) in
`Ratpoints.Proof.BlockPlan`, and the listing of the shape, a definition of the proofs, in
`Ratpoints.Proof.Shapes`; the contract of the run over the blocks with the correction of the moduli
is in `Ratpoints.Proof.Correction`.
-/

@[expose] public section

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### One denominator of a block -/

open BruteForce

/-- The words `x.1` of the classes modulo 64 that the classes `cls` pack, and the ranges `x.2 b` of
the numerators that the bounds `iv` of the search intervals give for the denominators `b` from
`bLow` to `bHigh` (`Ratpoints.Sieve.RangesFor`), for the height `H`: what the deliveries of the
run are stated for, since the program does not mention them. -/
def RunWords (cls : Vector NumClass 64) (iv : Array IntervalBounds) (H bLow bHigh : Nat)
    (x : Vector UInt64 64 × (Nat → List (Int × Int))) : Prop :=
  (∀ b < 64, cls[b]!.Packs x.1[b]!) ∧ ∀ b, bLow ≤ b → b ≤ bHigh → RangesFor iv b H (x.2 b)

/-- The points that the run delivers for the denominator `b`, for the polynomial of degree `d` with
the coefficient list `c`, the height `H`, the flags `fl` and the sieve entries `es` of the first
three stages, with the words `x.1` of the classes and the ranges `x.2 b` of the numerators of
`Ratpoints.Sieve.RunWords`: the points of the check with the flags
(`Ratpoints.Sieve.checkNumWith`) of the numerators `-H, …, H` in one of the ranges that pass the
word of the class of `b` (`Ratpoints.Sieve.classBit`) and survive the entries. -/
def denPoints (c : List Int) (d H : Nat) (fl : CheckFlags) (es : List SieveEntry)
    (x : Vector UInt64 64 × (Nat → List (Int × Int))) (b : Nat) : List (Int × Int × Int) :=
  ((numerators H).filter fun a ↦ inRanges (x.2 b) a && classBit x.1[b % 64]! a &&
    survives es b a).flatMap (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)

-- The entries with the offsets of the packing of a class have what `fill_bp_list` needs.
private theorem forall_mem_of_packedFor {es : List SieveEntry} {cl : NumClass} {offsets : Array Nat}
    {pos : Nat} (h : ∀ n (hn : n < es.length), es[n].PackedFor cl offsets[pos + n]!) :
    ∀ e ∈ es, 0 < e.p ∧ e.p ≤ maxPrimeEven ∧ e.dinv[cl.k]! < e.p := fun _ he ↦
  have ⟨n, hn, he⟩ := List.getElem_of_mem he
  he ▸ ⟨(h n hn).pos, (h n hn).le_maxPrimeEven, (h n hn).dinv_lt⟩

/-- The entries of the first two stages of a decision `sp2 ≤ sp3`, followed by those of the third,
are the first `sp3` entries. -/
theorem take_append_take_drop {α : Type} (l : List α) {m n : Nat} (h : m ≤ n) :
    l.take m ++ (l.drop m).take (n - m) = l.take n := by
  rw [← List.take_add, Nat.add_sub_cancel' h]

/-- The counts that the sieve of the denominator `b` adds to the counters of its block
(`Ratpoints.Sieve.siftCounts`), for the height `H`, the end `sp1` of the first stage, the first
`sp2` sieve entries of `entries` in the first two stages and those up to `sp3` in the third, with
the reciprocals `magics` of their moduli, the classes `cls` and the bounds `iv` of the search
intervals. -/
def denCounts (H sp1 : Nat) (entries : List SieveEntry) (magics : Array Nat)
    (cls : Vector NumClass 64) (iv : Array IntervalBounds) (sp2 sp3 b : Nat) : Counters :=
  siftCounts b H sp1 (entries.take sp2) ((entries.drop sp2).take (sp3 - sp2))
    ((magics.toList.drop sp2).take (sp3 - sp2)) cls[b % 64]! iv

open Std.WP Lean.Order in
/-- One denominator `b` of a block, with the first `sp2` sieve entries in the first two stages and
those up to `sp3` in the third, delivers the points of `Ratpoints.Sieve.denPoints` with the first
`sp3` entries, for every choice of the words of the classes and the ranges of the numerators of
`Ratpoints.Sieve.RunWords`, keeps a store of the tables of rows that fits all the entries, and adds
the counts of `Ratpoints.Sieve.siftCounts` to the counters, for a denominator between `bLow ≥ 1` and
`bHigh < 2 ^ 63` whose class has a pattern, entries with the tables of inverses of their factors,
prime entries from `sp2` on, the reciprocals of the moduli and the offsets of the packings of the
classes with a pattern. -/
theorem siftDen_spec {σ : Type} (process : Int → Int → Int → σ → Answer σ) (c : List Int)
    (d H A : Nat) (fl : CheckFlags) (sp1 : Nat) (entries : List SieveEntry) (magics : Array Nat)
    (sp2 sp3 : Nat) (cls : Vector NumClass 64) (offsets : Array Nat) (iv : Array IntervalBounds)
    (bLow bHigh : Nat) (hA : 1 ≤ A)
    (hent : ∀ e ∈ entries, (e.nf = 0 → e.IsPrimeEntry) ∧ ∀ f ∈ e.factors, f.HasInverses e.p)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p) (hoff : OffsetsFor cls entries offsets)
    (h23 : sp2 ≤ sp3) (hnf : ∀ e ∈ entries.drop sp2, e.nf = 0) (hbLow : 1 ≤ bLow)
    (hbHigh : bHigh < 2 ^ 63) (hH : H < 2 ^ 63) (b : Nat) (st : BlockState σ) :
    ⦃ (bLow ≤ b ∧ b ≤ bHigh ∧ cls[b % 64]!.bits ≠ 0) ∧ st.1.quit = false ∧ st.2.1.Fits entries ⦄
    siftDen process c d H A fl sp1 (entries.take sp2) (magics.toList.take sp2)
      ((entries.drop sp2).take (sp3 - sp2)) ((magics.toList.drop sp2).take (sp3 - sp2)) cls offsets
      iv b st
    ⦃ fun st' ↦ BlockPost process (RunWords cls iv H bLow bHigh)
        (denPoints c d H fl (entries.take sp3))
        (denCounts H sp1 entries magics cls iv sp2 sp3) (·.Fits entries) [b] st st' ⦄ := by
  refine ⟨fun ⟨⟨hb1, hb2, hbits⟩, hq, hQ⟩ ↦ ?_⟩
  obtain ⟨pos, hpos, hpf⟩ := hoff.take sp2 (b % 64) (Nat.mod_lt _ (by decide)) hbits
  have hmgs : magics.toList.take sp2 = (entries.take sp2).map (magic ·.p) := by
    rw [hmg, List.map_take]
  have hbp := hmgs ▸ fillBpList_eq_map (b := b) (forall_mem_of_packedFor hpf)
  have hs := (sift_spec process c d H A b fl sp1 (entries.take sp2) (magics.toList.take sp2)
    (fillBpList b cls[b % 64]!.k (entries.take sp2) (magics.toList.take sp2)) cls[b % 64]! offsets
    ((entries.drop sp2).take (sp3 - sp2)) ((magics.toList.drop sp2).take (sp3 - sp2)) iv st.2.1
    st.1 st.2.2).le_wp
      ⟨hq, hA, by lia, by lia, hH, fun e he ↦ (hent e (List.mem_of_mem_drop
        (List.mem_of_mem_take he))).1 (hnf e (List.mem_of_mem_take he)), by
        simp [hmg], hmgs, hbp, fun e he ↦
        (hent e (List.mem_of_mem_take he)).2, hQ.take sp2⟩
  refine ⟨fun x hx ↦ ?_, hQ.fits_run_sift process c d H A b fl sp1 _ _ _ offsets _ _ iv _ _ hbp,
    fun hq' ↦ ?_⟩
  · rw [List.flatMap_singleton, denPoints, ← take_append_take_drop entries h23]
    exact hs.2.1 x.1[b % 64]! pos (x.2 b) (hx.1 _ (Nat.mod_lt _ (by decide))) hpos hpf
      (hx.2 b hb1 hb2)
  · exact hs.2.2 pos hpos hpf hq'

/-! ### The denominators of a block -/

/-- The denominators of block `i` of the blocks `plan` of the shape `shape` for the denominators
`bLow, …, bHigh`, before the tests of the shape on a single denominator: those of its steps in
order (`Ratpoints.Sieve.Shape.stepDens`, `Ratpoints.Sieve.BlockPlan.blockSteps`). -/
def blockDens (shape : Shape) (db : UInt64) (plan : BlockPlan) (bLow bHigh i : Nat) : List Nat :=
  (plan.blockSteps i).flatMap (shape.stepDens db bLow bHigh (plan.blockSeg i))

-- A list over the positions of a list, read with `[i]!`, is that over its entries.
private theorem flatMap_range_length_getElem! {α β : Type} [Inhabited α] (l : List α)
    (g : α → List β) : (List.range l.length).flatMap (fun i ↦ g l[i]!) = l.flatMap g := by
  induction l with
  | nil => rfl
  | cons x l ih =>
    rw [List.length_cons, List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
    simp only [Nat.succ_eq_add_one, List.getElem!_cons_succ, List.getElem!_cons_zero, ih,
      List.flatMap_cons]

-- The segments of the blocks of a shape, as the plan of its blocks holds them.
private theorem flatMap_range_size_segs {β : Type} {segs : Array (Nat × Nat)} {n : Nat}
    {f : Nat → Nat × Nat} (hs : segs.toList = (List.range n).map f) (F : Nat → Nat × Nat → List β) :
    (List.range segs.size).flatMap (fun seg ↦ F seg segs[seg]!) =
      (List.range n).flatMap fun seg ↦ F seg (f seg) := by
  have hn : segs.size = n := by simpa using congrArg List.length hs
  rw [hn]
  refine congrArg List.flatten (List.map_congr_left fun seg hseg ↦ ?_)
  have hlt := List.mem_range.mp hseg
  rw [getElem!_pos segs seg (by lia), ← Array.getElem_toList, List.getElem_of_eq hs]
  simp

/-- The steps of the segments of a shape, in order, with the denominators of each step, are the
denominators of the listing of the shape (`Ratpoints.Sieve.Shape.dens`): the squares, the divisors
one after the other, the words with their denominators, and every denominator. -/
theorem Shape.flatMap_range_numSegs (shape : Shape) (db : UInt64) (bLow bHigh : Nat) :
    (List.range shape.numSegs).flatMap (fun seg ↦ (List.range' (shape.segment bLow bHigh seg).1
      ((shape.segment bLow bHigh seg).2 + 1 - (shape.segment bLow bHigh seg).1)).flatMap
        (shape.stepDens db bLow bHigh seg)) = Id.run (shape.dens db bLow bHigh) := by
  rcases shape with _ | ⟨info, divisors⟩ | ⟨forb, forbVal, useJacobi, fast, lcf⟩ | _
  · simp only [Shape.numSegs, Shape.segment, Shape.dens, squaresDens, List.map_eq_flatMap,
      List.range_one, List.flatMap_singleton]
    rfl
  · simp only [Shape.numSegs, Shape.segment, Shape.dens, squares1Dens]
    rw [← flatMap_range_length_getElem! divisors]
    simp only [List.map_eq_flatMap]
    rfl
  · change _ = (Id.run (wordsDens db forb bLow bHigh)).toList
    rw [Std.WP.Id.of_run_eq_wp rfl _ ((wordsDens_spec db forb bLow bHigh).le_wp trivial)]
    simp only [Shape.numSegs, Shape.segment, List.range_one, List.flatMap_singleton]
    rfl
  · simp only [Shape.numSegs, Shape.segment, Shape.dens, List.range_one, List.flatMap_singleton]
    exact List.flatMap_singleton' _

/-- The blocks of the run of a shape, in order, visit the denominators of the listing of the shape
(`Ratpoints.Sieve.Shape.dens`) in its order: the blocks of each segment cover its steps in order
(`Ratpoints.Sieve.BlockPlan.WF.flatMap_blockSteps`), and the steps of the segments are those of the
listing (`Ratpoints.Sieve.Shape.flatMap_range_numSegs`). -/
theorem Shape.flatMap_blockDens (shape : Shape) (db : UInt64) (bLow bHigh : Nat) :
    (List.range (Id.run (shape.blockPlan bLow bHigh)).nblocks).flatMap
        (blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh) =
      Id.run (shape.dens db bLow bHigh) := by
  have hp := Std.WP.Id.of_run_eq_wp rfl _ ((shape.blockPlan_spec bLow bHigh).le_wp trivial)
  have hs : (Id.run (shape.blockPlan bLow bHigh)).segs.toList =
      (List.range shape.numSegs).map (shape.segment bLow bHigh) := by
    rw [hp.2, Shape.toList_fst_run_segments]
  refine (hp.1.flatMap_blockSteps (shape.stepDens db bLow bHigh)).trans ?_
  rw [flatMap_range_size_segs hs fun seg sg ↦ (List.range' sg.1 (sg.2 + 1 - sg.1)).flatMap
      (shape.stepDens db bLow bHigh seg)]
  exact shape.flatMap_range_numSegs db bLow bHigh

/-- A denominator of a block of the run of a shape is one of the listing of the shape. -/
theorem Shape.mem_dens_of_mem_blockDens {shape : Shape} {db : UInt64} {bLow bHigh i b : Nat}
    (hi : i < (Id.run (shape.blockPlan bLow bHigh)).nblocks)
    (hb : b ∈ blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh i) :
    b ∈ Id.run (shape.dens db bLow bHigh) := by
  rw [← shape.flatMap_blockDens db bLow bHigh]
  exact List.mem_flatMap.mpr ⟨i, List.mem_range.mpr hi, hb⟩

/-- The blocks of the run of a shape, each delivering for its denominators that pass the tests of
the shape the lists `F i b`, which agree with the lists `G b` of the denominators, deliver the lists
`G b` of the denominators of the listing of the shape that pass its tests, in order. -/
theorem Shape.flatMap_filter_blockDens {β : Type} (shape : Shape) (db : UInt64)
    (cls : Vector NumClass 64) (bLow bHigh : Nat) {F : Nat → Nat → List β} {G : Nat → List β}
    (hF : ∀ i < (Id.run (shape.blockPlan bLow bHigh)).nblocks,
      ∀ b ∈ blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh i, F i b = G b) :
    (List.range (Id.run (shape.blockPlan bLow bHigh)).nblocks).flatMap (fun i ↦
        ((blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh i).filter
          fun b ↦ Id.run (shape.keep cls b)).flatMap (F i)) =
      ((Id.run (shape.dens db bLow bHigh)).filter fun b ↦ Id.run (shape.keep cls b)).flatMap G := by
  rw [← shape.flatMap_blockDens db bLow bHigh, List.filter_flatMap, List.flatMap_assoc]
  refine List.flatMap_congr fun i hi ↦ List.flatMap_congr fun b hb ↦ ?_
  exact hF i (List.mem_range.mp hi) b (List.mem_filter.mp hb).1

/-- When the listing of the shape has no denominator twice, a denominator lies in one block of the
run at most. -/
theorem Shape.eq_of_mem_blockDens {shape : Shape} {db : UInt64} {bLow bHigh i j b : Nat}
    (hnd : (Id.run (shape.dens db bLow bHigh)).Nodup)
    (hi : i < (Id.run (shape.blockPlan bLow bHigh)).nblocks)
    (hj : j < (Id.run (shape.blockPlan bLow bHigh)).nblocks)
    (hbi : b ∈ blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh i)
    (hbj : b ∈ blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh j) : i = j := by
  rw [← shape.flatMap_blockDens db bLow bHigh, List.nodup_flatMap] at hnd
  have hp := List.pairwise_iff_getElem.mp hnd.2
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with h | h
  · have := hp i j (by simpa using hi) (by simpa using hj) h
    simp only [List.getElem_range, Function.onFun] at this
    exact List.disjoint_left.mp this hbi hbj
  · have := hp j i (by simpa using hj) (by simpa using hi) h
    simp only [List.getElem_range, Function.onFun] at this
    exact List.disjoint_left.mp this hbj hbi

/-- The decision in force for a block, among well-formed decisions of which the first is for block
`0`, is well-formed. -/
theorem decisionWF_getElem!_findDecision {es : List SieveEntry} {sp1 : Nat} {decs : Array Decision}
    (h0 : 0 < decs.size) (hb : decs[0]!.block = 0) (h : ∀ d ∈ decs, DecisionWF es sp1 d) (i : Nat) :
    DecisionWF es sp1 decs[Id.run (findDecision decs i)]! := by
  have hf := (findDecision_spec decs i).le_wp ⟨h0, hb⟩
  rw [getElem!_pos decs _ hf.1]
  exact h _ (Array.getElem_mem hf.1)

/-- A forbidden divisor tested with words that the loop of the tables may record is a prime of the
table, with the words of `Ratpoints.Sieve.forbiddenRow`. -/
theorem IsForbiddenEntry.mem_primeTable {c : List ℤ} {d bHigh : ℕ} {e : ForbiddenEntry}
    (h : IsForbiddenEntry c d bHigh e) : e.p ∈ primeTable := by
  rcases h with ⟨p, hp, h⟩ | ⟨h, -⟩
  · obtain ⟨rfl, -⟩ := eq_of_run_forbiddenOfPrime_eq_inl h
    exact hp
  · exact h

/-- Forbidden divisors tested with words that the loop of the tables may record have what the loop
of a block of the word shape needs: positive primes of the table, below `2 ^ 32`, with their
reciprocals (`Ratpoints.Sieve.IsForbiddenEntry.magic_eq`). -/
theorem forbFits_of_forall_isForbiddenEntry {c : List ℤ} {d bHigh : ℕ} {forb : List ForbiddenEntry}
    (h : ∀ e ∈ forb, IsForbiddenEntry c d bHigh e) : ForbFits forb := fun e he ↦
  have hp := (h e he).mem_primeTable
  ⟨(prime_of_mem_primeTable hp).pos, by lia [lt_of_mem_primeTable hp], (h e he).magic_eq⟩

/-- The shape that `Ratpoints.Sieve.runSetup` chooses with forbidden divisors tested with words that
the loop of the tables may record has what its loops need. -/
theorem forbFits_fst_run_runSetup {c : List ℤ} {d bHigh' : ℕ} (useSquares : Bool)
    (us1 : Option (List Setup.DenInfo × List ℕ)) (checkDenom useJacobi : Bool)
    {forb : List ForbiddenEntry} (forbVal : List ForbiddenVal) (lcf : ℤ) (H bHigh : ℕ)
    (domain : List (Double × Double)) (h : ∀ e ∈ forb, IsForbiddenEntry c d bHigh' e) :
    (Id.run (runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf H bHigh
      domain)).1.ForbFits := by
  rw [fst_run_runSetup]
  split
  · trivial
  · split
    · trivial
    · split
      · exact forbFits_of_forall_isForbiddenEntry h
      · trivial

/-! ### One block -/

/-- The blocks of the run of a shape have what its loops need, for the word shape with forbidden
divisors that have what the loop needs: the first segment from the word of `bLow` to that of
`bHigh`. -/
theorem Shape.loopFits_run_blockPlan {shape : Shape} (hf : shape.ForbFits) (bLow bHigh : Nat) :
    shape.LoopFits (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh := by
  rcases shape with _ | _ | ⟨forb, forbVal, useJacobi, fast, lcf⟩ | _
  · trivial
  · trivial
  · refine ⟨hf, ?_⟩
    have hp := Std.WP.Id.of_run_eq_wp rfl _ ((Shape.blockPlan_spec (.words forb forbVal useJacobi
      fast lcf) bLow bHigh).le_wp trivial)
    have hs := Shape.toList_fst_run_segments (.words forb forbVal useJacobi fast lcf) bLow bHigh
    have h1 : (Id.run ((Shape.words forb forbVal useJacobi fast lcf).segments bLow bHigh)).1.size =
        1 := by simpa [Shape.numSegs] using congrArg List.length hs
    rw [hp.2, getElem!_pos _ 0 (by lia),
      ← Array.getElem_toList, List.getElem_of_eq hs]
    rfl
  · trivial

-- The denominators that a block hands to its step: those of the listing of the shape, between
-- `bLow` and `bHigh`, with a class that has a pattern.
private theorem le_and_le_and_bits_ne_zero_of_mem {shape : Shape} {db : UInt64}
    {cls : Vector NumClass 64} {bLow bHigh i b : Nat}
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0)) (hbLow : 1 ≤ bLow)
    (hi : i < (Id.run (shape.blockPlan bLow bHigh)).nblocks)
    (hb : b ∈ (blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh i).filter
      fun b ↦ Id.run (shape.keep cls b)) :
    bLow ≤ b ∧ b ≤ bHigh ∧ cls[b % 64]!.bits ≠ 0 := by
  obtain ⟨hb, hk⟩ := List.mem_filter.mp hb
  have hd := Shape.mem_dens_of_mem_blockDens hi hb
  exact ⟨(shape.le_and_le_of_mem_dens db hbLow hd).1, (shape.le_and_le_of_mem_dens db hbLow hd).2,
    shape.bits_ne_zero_of_mem_dens hdb hd hk⟩

open Std.WP Lean.Order in
/-- Block `i` of the run of a shape, with the decision in force for it, delivers the points of the
denominators of the block (`Ratpoints.Sieve.blockDens`) that pass the tests of the shape, in order,
each with the first `sp3` entries of the decision (`Ratpoints.Sieve.denPoints`), for every choice of
the words of the classes and the ranges of the numerators of `Ratpoints.Sieve.RunWords`; it keeps a
store of the tables of rows that fits all the entries, counts the counts of these denominators from
zero when the callback does not stop the search (`Ratpoints.Sieve.denCounts`), and reports the
decision. The block needs a well-formed decision (`Ratpoints.Sieve.DecisionWF`), entries with the
tables of inverses of their factors, prime entries where no factor is counted, the reciprocals of
the moduli, the offsets of the packings of the classes with a pattern, whose bits the word `db` has,
the blocks of the shape (`Ratpoints.Sieve.Shape.blockPlan`) with `i` one of them, forbidden divisors
of the word shape that have what its loop needs (`Ratpoints.Sieve.Shape.ForbFits`), the denominators
from `bLow ≥ 1` to `bHigh < 2 ^ 63` and the height below `2 ^ 63`. -/
@[spec]
theorem runBlock_spec {σ : Type} (process : Int → Int → Int → σ → Answer σ) (c : List Int)
    (d H A : Nat) (fl : CheckFlags) (sp1 : Nat) (entries : List SieveEntry) (magics : Array Nat)
    (cls : Vector NumClass 64) (offsets : Array Nat) (db : UInt64) (shape : Shape)
    (iv : Array IntervalBounds) (bLow bHigh : Nat) (plan : BlockPlan) (decs : Array Decision)
    (i : Nat) (store : RowStore) (r : Delivery σ) :
    ⦃ r.quit = false ∧ 1 ≤ A ∧
        (∀ e ∈ entries, (e.nf = 0 → e.IsPrimeEntry) ∧ ∀ f ∈ e.factors, f.HasInverses e.p) ∧
        magics.toList = entries.map (fun e ↦ magic e.p) ∧ OffsetsFor cls entries offsets ∧
        (∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0)) ∧
        DecisionWF entries sp1 decs[Id.run (findDecision decs i)]! ∧
        plan = Id.run (shape.blockPlan bLow bHigh) ∧ shape.ForbFits ∧ i < plan.nblocks ∧
        1 ≤ bLow ∧ bHigh < 2 ^ 63 ∧ H < 2 ^ 63 ∧ store.Fits entries ⦄
    runBlock process c d H A fl sp1 entries magics cls offsets db shape iv bLow bHigh plan decs i
      store r
    ⦃ fun res ↦ res.2.1.Fits entries ∧ res.2.2.dec = Id.run (findDecision decs i) ∧
        res.2.2.sp2 = decs[Id.run (findDecision decs i)]!.sp2 ∧
        res.2.2.sp3 = decs[Id.run (findDecision decs i)]!.sp3 ∧
        (∀ x, RunWords cls iv H bLow bHigh x → res.1 = r.deliver process
          (((blockDens shape db plan bLow bHigh i).filter fun b ↦ Id.run (shape.keep cls b)).flatMap
            (denPoints c d H fl (entries.take decs[Id.run (findDecision decs i)]!.sp3) x))) ∧
        (res.1.quit = false → res.2.2.cnt =
          ((((blockDens shape db plan bLow bHigh i).filter fun b ↦ Id.run (shape.keep cls b)).map
            (denCounts H sp1 entries magics cls iv decs[Id.run (findDecision decs i)]!.sp2
              decs[Id.run (findDecision decs i)]!.sp3)).foldl (· + ·) {})) ⦄ :=
  ⟨fun ⟨hr, hA, hent, hmg, hoff, hdb, hdec, hplan, hforb, hi, hbLow, hbHigh, hH, hs⟩ ↦ by
    subst hplan
    have hwf := (Std.WP.Id.of_run_eq_wp rfl _ ((shape.blockPlan_spec bLow bHigh).le_wp trivial)).1
    have h := (Shape.blockLoop_spec process shape _ _ (RunWords cls iv H bLow bHigh)
      (denPoints c d H fl (entries.take decs[Id.run (findDecision decs i)]!.sp3))
      (denCounts H sp1 entries magics cls iv decs[Id.run (findDecision decs i)]!.sp2
        decs[Id.run (findDecision decs i)]!.sp3) (·.Fits entries)
      (siftDen_spec process c d H A fl sp1 entries magics _ _ cls offsets iv bLow bHigh hA hent hmg
        hoff hdec.2.1 hdec.2.2.2 hbLow hbHigh hH) cls db _ _ _ _ bLow bHigh (r, store, {})).le_wp
      ⟨hr, hs, hwf.run_steps_le hi, Shape.loopFits_run_blockPlan hforb bLow bHigh,
        fun b hb ↦ le_and_le_and_bits_ne_zero_of_mem hdb hbLow hi hb⟩
    exact ⟨h.2.1, rfl, rfl, rfl, h.1, h.2.2⟩⟩

end Sieve

end Ratpoints

end
