/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Blocks
public import Std.WP

import Ratpoints.Proof.VCSimp
import Std.Tactic.Do

/-!
# The plan of the blocks of the run

The run cuts the steps of its shape into segments (`Ratpoints.Sieve.Shape.segments`), one for each
divisor of the divisor shape and one otherwise, and each segment into blocks of one length
(`Ratpoints.Sieve.Shape.blockPlan`), the first block of each segment recorded with the number of
the blocks at the end; the steps of block `i` are found from the segment that holds it
(`Ratpoints.Sieve.BlockPlan.steps`). The plan that the run makes is well-formed
(`Ratpoints.Sieve.BlockPlan.WF`): blocks of at least one step, the first blocks of the segments the
running sums of the numbers of their blocks (`Ratpoints.Sieve.numBlocks`); for a well-formed plan
the search for the segment of a block ends, the steps of the block are those of
`Ratpoints.Sieve.blockRange`, its first step at most its last, and the blocks in order cover the
steps of the segments in order. A decision of the correction of the moduli is well-formed for the
entries of the run (`Ratpoints.Sieve.DecisionWF`) when its cut points are in order within the
entries and the entries from its second cut point on count no factor.

## Main definitions

* `Ratpoints.Sieve.numBlocks`, `Ratpoints.Sieve.blockRange`: the number of the blocks of a segment
  and the first and last steps of each.
* `Ratpoints.Sieve.Shape.numSegs`, `Ratpoints.Sieve.Shape.segment`: the segments of a shape.
* `Ratpoints.Sieve.BlockPlan.WF`: a well-formed plan of the blocks.
* `Ratpoints.Sieve.BlockPlan.blockSteps`, `Ratpoints.Sieve.BlockPlan.blockSeg`: the steps and the
  segment of a block.
* `Ratpoints.Sieve.DecisionWF`: a decision whose cut points the blocks can use.

## Main statements

* `Ratpoints.Sieve.flatMap_blockRange`: the blocks of a segment cover its steps in order.
* `Ratpoints.Sieve.Shape.segments_spec`, `Ratpoints.Sieve.Shape.blockPlan_spec`: the segments of a
  shape, and the plan of its blocks well-formed over them.
* `Ratpoints.Sieve.one_le_blockLength`: a block has at least one step.
* `Ratpoints.Sieve.BlockPlan.WF.steps_spec`, `Ratpoints.Sieve.BlockPlan.WF.run_steps_eq`: the steps
  of a block of a well-formed plan, from its segment.
* `Ratpoints.Sieve.BlockPlan.WF.flatMap_blockSteps`: the blocks of a well-formed plan, in order,
  cover the steps of its segments in order.
* `Ratpoints.Sieve.BlockPlan.WF.run_steps_le`: the first step of a block is at most its last, which
  the loops of the blocks need to end.
* `Ratpoints.Sieve.DecisionWF.mk_sp2`, `Ratpoints.Sieve.DecisionWF.map_dinv`: a well-formed decision
  stays well-formed with no third stage, and for the entries with the inverses of the strides that
  `Ratpoints.Sieve.classOffsets` sets.

## Implementation notes

The file uses Lean core and `Std` only, as the contracts of the sieve do.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The blocks of a segment -/

/-- The number of the blocks of `len` steps of the segment of the steps `lo, …, hi`, the last
possibly shorter: `⌊(hi - lo) / len⌋ + 1`, and none for an empty segment, `hi < lo`. -/
def numBlocks (lo hi len : Nat) : Nat := if lo ≤ hi then (hi - lo) / len + 1 else 0

/-- The first and last steps of block `j` of `len` steps of the segment of the steps `lo, …, hi`:
from `lo + j len`, `len` steps or up to `hi`. -/
def blockRange (lo hi len j : Nat) : Nat × Nat :=
  let a := lo + j * len
  (a, if hi - a < len then hi else a + len - 1)

theorem blockRange_succ (lo hi len j : Nat) :
    blockRange lo hi len (j + 1) = blockRange (lo + len) hi len j := by
  simp only [blockRange, Nat.succ_mul, ← Nat.add_assoc, Nat.add_right_comm lo len]

theorem numBlocks_of_le {lo hi len : Nat} (hlen : 1 ≤ len) (h : lo + len ≤ hi) :
    numBlocks lo hi len = numBlocks (lo + len) hi len + 1 := by
  simp only [numBlocks, show lo ≤ hi by lia, h, ↓reduceIte]
  rw [show hi - lo = hi - (lo + len) + len * 1 by lia, Nat.add_mul_div_left _ _ (by lia)]

/-- A block of a segment has its first step at most its last, both within the segment. -/
theorem blockRange_le {lo hi len j : Nat} (hlen : 1 ≤ len) (hj : j < numBlocks lo hi len) :
    lo ≤ (blockRange lo hi len j).1 ∧ (blockRange lo hi len j).1 ≤ (blockRange lo hi len j).2 ∧
      (blockRange lo hi len j).2 ≤ hi := by
  simp only [numBlocks] at hj
  split at hj
  · have : j * len ≤ hi - lo := (Nat.le_div_iff_mul_le hlen).mp (Nat.lt_succ_iff.mp hj)
    simp only [blockRange]
    split <;> lia
  · lia

-- One block of a segment, or none, with its steps.
private theorem flatMap_blockRange_of_lt {lo hi len : Nat} (hlen : 1 ≤ len) (hlt : hi < lo + len)
    {β : Type} (g : Nat → List β) :
    (List.range (numBlocks lo hi len)).flatMap (fun j ↦
      (List.range' (blockRange lo hi len j).1
        ((blockRange lo hi len j).2 + 1 - (blockRange lo hi len j).1)).flatMap g) =
      (List.range' lo (hi + 1 - lo)).flatMap g := by
  by_cases hle : lo ≤ hi
  · have : numBlocks lo hi len = 1 := by
      simp only [numBlocks, hle, ↓reduceIte, Nat.add_eq_right]
      exact Nat.div_eq_of_lt (by lia)
    simp [this, blockRange, show hi - lo < len by lia]
  · simp [numBlocks, hle, show hi + 1 - lo = 0 by lia]

/-- The blocks of a segment, in order, cover its steps in order. -/
theorem flatMap_blockRange {len : Nat} (hlen : 1 ≤ len) {β : Type} (g : Nat → List β)
    (lo hi : Nat) :
    (List.range (numBlocks lo hi len)).flatMap (fun j ↦
      (List.range' (blockRange lo hi len j).1
        ((blockRange lo hi len j).2 + 1 - (blockRange lo hi len j).1)).flatMap g) =
      (List.range' lo (hi + 1 - lo)).flatMap g := by
  by_cases hlt : hi < lo + len
  · exact flatMap_blockRange_of_lt hlen hlt g
  rw [numBlocks_of_le hlen (by lia), List.range_succ_eq_map, List.flatMap_cons, List.flatMap_map]
  simp only [Nat.succ_eq_add_one, blockRange_succ]
  rw [flatMap_blockRange hlen g (lo + len) hi]
  simp only [blockRange, Nat.zero_mul, Nat.add_zero, show ¬hi - lo < len by lia, ↓reduceIte]
  rw [← List.flatMap_append, show lo + len - 1 + 1 - lo = len by lia, List.range'_append_1]
  congr 2
  lia
termination_by hi + 1 - lo
decreasing_by lia

/-! ### The plan of the blocks -/

/-- The number of the segments of steps of the shape `s`: one for each divisor of the divisor
shape, and one otherwise. -/
def Shape.numSegs : Shape → Nat
  | .squares1 _ divisors => divisors.length
  | _ => 1

/-- The first and last steps of segment `n` of the shape `s` for the denominators `bLow, …, bHigh`
(`Ratpoints.Sieve.Shape.segments`). -/
def Shape.segment (s : Shape) (bLow bHigh n : Nat) : Nat × Nat :=
  match s with
  | .squares => (ceilSqrt bLow, floorSqrt bHigh)
  | .squares1 _ divisors =>
    (ceilSqrt ((bLow - 1) / divisors[n]! + 1), floorSqrt (bHigh / divisors[n]!))
  | .words .. => (bLow / 64, bHigh / 64)
  | .all => (bLow, bHigh)

-- The step of the loop of `Ratpoints.Sieve.Shape.segments`: the segment of the cursor pushed.
private theorem toList_push_of_eq_map {β : Type} {segs : Array (Nat × Nat)} {f : β → Nat × Nat}
    {pref : List β} (h : segs.toList = pref.map f) (cur : β) {p : Nat × Nat} (hp : p = f cur) :
    (segs.push (p.1, p.2)).toList = (pref ++ [cur]).map f := by
  simp [h, hp]

-- The invariant of the loop of `Ratpoints.Sieve.Shape.segments` over the segments done, `pref`:
-- their segments pushed.
private def SegmentsInvariant (s : Shape) (bLow bHigh : Nat) (pref : List Nat)
    (st : Array (Nat × Nat) × Nat) : Prop :=
  st.1.toList = pref.map (s.segment bLow bHigh)

open Std.WP Lean.Order in
/-- The segments of steps of the shape `s`, one for each of its segments in order. -/
theorem Shape.segments_spec (s : Shape) (bLow bHigh : Nat) :
    ⦃ True ⦄ s.segments bLow bHigh
    ⦃ fun r ↦ r.1.toList = (List.range s.numSegs).map (s.segment bLow bHigh) ⦄ := by
  vcgen [Shape.segments] invariants
  | inv1 => fun pref _ st ↦ SegmentsInvariant s bLow bHigh pref st
  all_goals simp only [SegmentsInvariant] at *
  all_goals first
    | exact toList_push_of_eq_map ‹_› _ rfl
    | rfl
    | (rename_i h; cases s <;> simpa [List.range_eq_range', Shape.numSegs] using h)

theorem Shape.toList_fst_run_segments (s : Shape) (bLow bHigh : Nat) :
    (Id.run (s.segments bLow bHigh)).1.toList = (List.range s.numSegs).map (s.segment bLow bHigh) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((s.segments_spec bLow bHigh).le_wp trivial)

/-- The blocks `plan` are well-formed: blocks of at least one step, and the first block of each
segment the number of the blocks of the segments before it
(`Ratpoints.Sieve.numBlocks`), the number of all the blocks at the end. -/
structure BlockPlan.WF (plan : BlockPlan) : Prop where
  /-- The blocks have at least one step. -/
  one_le_len : 1 ≤ plan.len
  /-- The first block of each segment, and the number of all the blocks at the end. -/
  segBlock_eq : plan.segBlock.toList = (List.range (plan.segs.size + 1)).map fun j ↦
    ((plan.segs.toList.take j).map fun sg ↦ numBlocks sg.1 sg.2 plan.len).sum

/-- A block has at least one step: the length that a build sets is positive
(`Ratpoints.blockLen_pos`), and otherwise the length is at least `1`. -/
theorem one_le_blockLength (steps : Nat) : 1 ≤ blockLength steps := by
  rw [blockLength]
  rcases h : blockLen with _ | n
  · simp only [Option.getD_none]
    split <;> lia
  · exact blockLen_pos n (by simp [h])

-- The invariant of the loop of `Ratpoints.Sieve.Shape.blockPlan` over the segments done, `pref`:
-- the first blocks of the segments done, and the number of their blocks.
private def BlockPlanInvariant (len : Nat) (pref : List (Nat × Nat)) (st : Nat × Array Nat) :
    Prop :=
  st.1 = (pref.map fun sg ↦ numBlocks sg.1 sg.2 len).sum ∧
    st.2.toList = (List.range pref.length).map fun j ↦
      ((pref.take j).map fun sg ↦ numBlocks sg.1 sg.2 len).sum

private theorem BlockPlanInvariant.push {len : Nat} {pref : List (Nat × Nat)} {cur : Nat × Nat}
    {n : Nat} {segBlock : Array Nat} (h : BlockPlanInvariant len pref (n, segBlock))
    (n' : Nat) (hn : n' = n + numBlocks cur.1 cur.2 len) :
    BlockPlanInvariant len (pref ++ [cur]) (n', segBlock.push n) := by
  obtain ⟨h1, h2⟩ := h
  simp only at h1 h2
  refine ⟨by simp [hn, h1], ?_⟩
  rw [Array.toList_push, h2, List.length_append, List.length_singleton, List.range_succ,
    List.map_append, List.map_singleton, List.take_append_of_le_length (Nat.le_refl _),
    List.take_length, h1]
  congr 1
  refine List.map_congr_left fun j hj ↦ ?_
  rw [List.take_append_of_le_length (Nat.le_of_lt (List.mem_range.mp hj))]

private theorem BlockPlanInvariant.push_of_le {len lo hi n : Nat} {pref : List (Nat × Nat)}
    {segBlock : Array Nat} (h : BlockPlanInvariant len pref (n, segBlock)) (hle : lo ≤ hi) :
    BlockPlanInvariant len (pref ++ [(lo, hi)]) (n + (hi - lo) / len + 1, segBlock.push n) :=
  h.push _ (by simp [numBlocks, hle]; lia)

private theorem BlockPlanInvariant.push_of_not_le {len lo hi n : Nat} {pref : List (Nat × Nat)}
    {segBlock : Array Nat} (h : BlockPlanInvariant len pref (n, segBlock)) (hle : ¬lo ≤ hi) :
    BlockPlanInvariant len (pref ++ [(lo, hi)]) (n, segBlock.push n) :=
  h.push _ (by simp [numBlocks, hle])

private theorem BlockPlanInvariant.wf {len : Nat} {segs : Array (Nat × Nat)} {n : Nat}
    {segBlock : Array Nat} (h : BlockPlanInvariant len (ForIn.toList segs) (n, segBlock))
    (hlen : 1 ≤ len) : ({ segs, len, segBlock := segBlock.push n } : BlockPlan).WF := by
  obtain ⟨h1, h2⟩ := h
  simp only [Std.Internal.ForIn.toList_array] at h1 h2
  refine ⟨hlen, ?_⟩
  simp only [Array.toList_push, h2, h1, List.range_succ, List.map_append,
    List.map_singleton, ← Array.length_toList, List.take_length]

-- The segments, as a value for the contract of the blocks.
private theorem segments_value (s : Shape) (bLow bHigh : Nat) :
    ⦃ True ⦄ s.segments bLow bHigh ⦃ fun r ↦ r = Id.run (s.segments bLow bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

open Std.WP Lean.Order in
/-- The blocks that `Ratpoints.Sieve.Shape.blockPlan` makes are well-formed, over the segments
of `Ratpoints.Sieve.Shape.segments`. -/
theorem Shape.blockPlan_spec (s : Shape) (bLow bHigh : Nat) :
    ⦃ True ⦄ s.blockPlan bLow bHigh
    ⦃ fun plan ↦ plan.WF ∧ plan.segs = (Id.run (s.segments bLow bHigh)).1 ⦄ := by
  vcgen [Shape.blockPlan, segments_value] invariants
  | inv1 => fun pref _ st ↦ BlockPlanInvariant (blockLength (Id.run (s.segments bLow bHigh)).2)
      pref st
  all_goals
    have hst := congrArg Prod.snd ‹(_, _) = Id.run (s.segments bLow bHigh)›
    have hsg := congrArg Prod.fst ‹(_, _) = Id.run (s.segments bLow bHigh)›
    simp only at hst hsg
    subst hst hsg
  all_goals first
    | exact ⟨rfl, rfl⟩
    | exact ⟨BlockPlanInvariant.wf ‹_› (one_le_blockLength _), rfl⟩
    | exact BlockPlanInvariant.push_of_le ‹_› ‹_›
    | exact BlockPlanInvariant.push_of_not_le ‹_› ‹_›

section

variable {plan : BlockPlan}

theorem BlockPlan.WF.size_segBlock (h : plan.WF) : plan.segBlock.size = plan.segs.size + 1 := by
  simpa using congrArg List.length h.segBlock_eq

theorem BlockPlan.WF.getElem!_segBlock (h : plan.WF) {j : Nat} (hj : j ≤ plan.segs.size) :
    plan.segBlock[j]! =
      ((plan.segs.toList.take j).map fun sg ↦ numBlocks sg.1 sg.2 plan.len).sum := by
  rw [getElem!_pos plan.segBlock j (by rw [h.size_segBlock]; lia), ← Array.getElem_toList]
  simp [h.segBlock_eq]

theorem BlockPlan.WF.segBlock_succ (h : plan.WF) {j : Nat} (hj : j < plan.segs.size) :
    plan.segBlock[j + 1]! =
      plan.segBlock[j]! + numBlocks plan.segs[j]!.1 plan.segs[j]!.2 plan.len := by
  rw [h.getElem!_segBlock hj, h.getElem!_segBlock (Nat.le_of_lt hj),
    List.take_succ_eq_append_getElem (by simpa using hj)]
  simp [getElem!_pos plan.segs j hj]

theorem BlockPlan.WF.nblocks_eq (h : plan.WF) : plan.nblocks = plan.segBlock[plan.segs.size]! := by
  rw [BlockPlan.nblocks, Array.back!, h.size_segBlock, Nat.add_sub_cancel]

theorem BlockPlan.WF.segBlock_mono (h : plan.WF) {j k : Nat} (hjk : j ≤ k)
    (hk : k ≤ plan.segs.size) : plan.segBlock[j]! ≤ plan.segBlock[k]! := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_add_of_le hjk
  induction n with
  | zero => exact Nat.le_refl _
  | succ n ih =>
    rw [← Nat.add_assoc, h.segBlock_succ (by lia)]
    exact Nat.le_add_right_of_le (ih (by lia) (by lia))

theorem BlockPlan.WF.segBlock_zero (h : plan.WF) : plan.segBlock[0]! = 0 := by
  simp [h.getElem!_segBlock (Nat.zero_le _)]

-- Block `i < plan.nblocks` lies in a segment from the first on: there is one.
private theorem BlockPlan.WF.segment_pre (h : plan.WF) {i : Nat} (hi : i < plan.nblocks) :
    0 < plan.segs.size ∧ plan.segBlock[0]! ≤ i ∧ (false = true → i < plan.segBlock[0 + 1]!) := by
  refine ⟨Nat.pos_of_ne_zero fun h0 ↦ ?_, by rw [h.segBlock_zero]; lia, nofun⟩
  rw [h.nblocks_eq, h0, h.segBlock_zero] at hi
  lia

-- The search for the segment of block `i < plan.nblocks` goes on to the next segment while the
-- first block of the next is at most `i`, which is then not the end.
private theorem BlockPlan.WF.segment_succ (h : plan.WF) {i seg mb : Nat} (hi : i < plan.nblocks)
    (hs : plan.segBlock[seg + 1]! ≤ i)
    (hinv : plan.segs.size - seg = mb ∧ seg < plan.segs.size ∧ plan.segBlock[seg]! ≤ i ∧
      (false = true → i < plan.segBlock[seg + 1]!)) :
    plan.segs.size - (seg + 1) < mb ∧ seg + 1 < plan.segs.size ∧ plan.segBlock[seg + 1]! ≤ i ∧
      (false = true → i < plan.segBlock[seg + 1 + 1]!) := by
  refine ⟨by lia, Nat.lt_of_le_of_ne hinv.2.1 fun he ↦ ?_, hs, nofun⟩
  rw [h.nblocks_eq, ← he] at hi
  lia

end

/-- The invariant of the search of `Ratpoints.Sieve.BlockPlan.steps` for the segment of block `i`,
whose state is the segment `seg`: a segment of the blocks whose first block is at most `i`, and at
the exit the segment whose blocks hold `i`. -/
def SegmentSearchInvariant (plan : BlockPlan) (i : Nat) : Std.WP.WhileInvariant Nat Prop :=
  .mk fun exit seg ↦ seg < plan.segs.size ∧ plan.segBlock[seg]! ≤ i ∧
    (exit = true → i < plan.segBlock[seg + 1]!)

/-- The steps of block `i < plan.nblocks` of well-formed blocks: its segment, the one whose blocks
hold it, and its first and last steps (`Ratpoints.Sieve.blockRange`). The search for the segment
ends, since the first block after the last segment is the number of the blocks. -/
theorem BlockPlan.WF.steps_spec {plan : BlockPlan} (h : plan.WF) (i : Nat) :
    ⦃ i < plan.nblocks ⦄ plan.steps i
    ⦃ fun r ↦ r.1 < plan.segs.size ∧ plan.segBlock[r.1]! ≤ i ∧ i < plan.segBlock[r.1 + 1]! ∧
        r.2 = blockRange plan.segs[r.1]!.1 plan.segs[r.1]!.2 plan.len
          (i - plan.segBlock[r.1]!) ⦄ := by
  vcgen [BlockPlan.steps] invariants
  | inv1 => SegmentSearchInvariant plan i
  | inv2 => .ofMeasure fun seg ↦ plan.segs.size - seg
  all_goals try vc_simp [SegmentSearchInvariant]
  all_goals first
    | exact h.segment_pre ‹_›
    | exact h.segment_succ ‹_› ‹_› ‹_›
    | (rename_i hinv; exact ⟨hinv.1, hinv.2.1, hinv.2.2 trivial, rfl⟩)
    | (rename_i hs hinv; exact ⟨hinv.2.1, hinv.2.2.1, fun _ ↦ Nat.lt_of_not_le hs⟩)

/-- The steps of block `i < plan.nblocks` of well-formed blocks, from the segment whose blocks hold
it (`Ratpoints.Sieve.BlockPlan.WF.steps_spec`). -/
theorem BlockPlan.WF.run_steps {plan : BlockPlan} (h : plan.WF) {i : Nat}
    (hi : i < plan.nblocks) :
    ∃ seg < plan.segs.size, plan.segBlock[seg]! ≤ i ∧ i < plan.segBlock[seg + 1]! ∧
      Id.run (plan.steps i) =
        (seg, blockRange plan.segs[seg]!.1 plan.segs[seg]!.2 plan.len (i - plan.segBlock[seg]!)) :=
  have h' := (h.steps_spec i).le_wp hi
  ⟨_, h'.1, h'.2.1, h'.2.2.1, Prod.ext rfl h'.2.2.2⟩

/-- The steps of a block of well-formed blocks that lies in the segment `seg`: the block
`i - segBlock[seg]` of the segment (`Ratpoints.Sieve.blockRange`). -/
theorem BlockPlan.WF.run_steps_eq {plan : BlockPlan} (h : plan.WF) {i seg : Nat}
    (hs : seg < plan.segs.size) (h1 : plan.segBlock[seg]! ≤ i) (h2 : i < plan.segBlock[seg + 1]!) :
    Id.run (plan.steps i) =
      (seg, blockRange plan.segs[seg]!.1 plan.segs[seg]!.2 plan.len (i - plan.segBlock[seg]!)) := by
  have hi : i < plan.nblocks := by
    rw [h.nblocks_eq]
    exact Nat.lt_of_lt_of_le h2 (h.segBlock_mono hs (Nat.le_refl _))
  obtain ⟨seg', hs', h1', h2', he⟩ := h.run_steps hi
  obtain rfl : seg' = seg := by
    rcases Nat.lt_trichotomy seg' seg with hlt | heq | hgt
    · lia [h.segBlock_mono (Nat.succ_le_of_lt hlt) (Nat.le_of_lt hs)]
    · exact heq
    · lia [h.segBlock_mono (Nat.succ_le_of_lt hgt) (Nat.le_of_lt hs')]
  exact he

-- `List.flatMap_congr` of Mathlib, for this file without Mathlib.
private theorem flatMap_congr_mem {α β : Type} {l : List α} {f g : α → List β}
    (h : ∀ x ∈ l, f x = g x) : l.flatMap f = l.flatMap g :=
  congrArg List.flatten (List.map_congr_left h)

/-- The steps of block `i` of the blocks `plan`, in order. -/
def BlockPlan.blockSteps (plan : BlockPlan) (i : Nat) : List Nat :=
  List.range' (Id.run (plan.steps i)).2.1
    ((Id.run (plan.steps i)).2.2 + 1 - (Id.run (plan.steps i)).2.1)

/-- The segment of block `i` of the blocks `plan`. -/
def BlockPlan.blockSeg (plan : BlockPlan) (i : Nat) : Nat :=
  (Id.run (plan.steps i)).1

-- The blocks before the first block of segment `k` are those of the segments before it.
private theorem BlockPlan.WF.range_segBlock {plan : BlockPlan} (h : plan.WF) {k : Nat}
    (hk : k ≤ plan.segs.size) :
    List.range plan.segBlock[k]! = (List.range k).flatMap fun seg ↦
      List.range' plan.segBlock[seg]! (numBlocks plan.segs[seg]!.1 plan.segs[seg]!.2 plan.len) := by
  induction k with
  | zero => simp [h.segBlock_zero]
  | succ k ih =>
    rw [h.segBlock_succ (by lia), List.range_add, ih (by lia), List.range_succ, List.flatMap_append,
      List.flatMap_singleton, List.range'_eq_map_range]

-- The blocks of segment `seg`, as the blocks `j` of the segment, with their steps.
private theorem BlockPlan.WF.flatMap_range'_segBlock {plan : BlockPlan} (h : plan.WF) {seg : Nat}
    (hs : seg < plan.segs.size) {β : Type} (g : Nat → Nat → List β) :
    (List.range' plan.segBlock[seg]!
        (numBlocks plan.segs[seg]!.1 plan.segs[seg]!.2 plan.len)).flatMap
          (fun i ↦ (plan.blockSteps i).flatMap (g (plan.blockSeg i))) =
      (List.range' plan.segs[seg]!.1 (plan.segs[seg]!.2 + 1 - plan.segs[seg]!.1)).flatMap
        (g seg) := by
  rw [← flatMap_blockRange h.one_le_len (g seg), List.range'_eq_map_range, List.flatMap_map]
  refine flatMap_congr_mem fun j hj ↦ ?_
  have := h.run_steps_eq hs (Nat.le_add_right _ j)
    (by rw [h.segBlock_succ hs]; exact Nat.add_lt_add_left (List.mem_range.mp hj) _)
  simp only [BlockPlan.blockSteps, BlockPlan.blockSeg, this, Nat.add_sub_cancel_left]

/-- The blocks of well-formed blocks, in order, cover the steps of their segments in order, and so
the lists `g seg k` of the steps `k` of each segment `seg`, in order. -/
theorem BlockPlan.WF.flatMap_blockSteps {plan : BlockPlan} (h : plan.WF) {β : Type}
    (g : Nat → Nat → List β) :
    (List.range plan.nblocks).flatMap (fun i ↦ (plan.blockSteps i).flatMap (g (plan.blockSeg i))) =
      (List.range plan.segs.size).flatMap fun seg ↦
        (List.range' plan.segs[seg]!.1 (plan.segs[seg]!.2 + 1 - plan.segs[seg]!.1)).flatMap
          (g seg) := by
  rw [h.nblocks_eq, h.range_segBlock (Nat.le_refl _), List.flatMap_assoc]
  exact flatMap_congr_mem fun seg hs ↦ h.flatMap_range'_segBlock (List.mem_range.mp hs) g

/-- The steps of a block of well-formed blocks run from its first to its last, which is not before
it. -/
theorem BlockPlan.WF.run_steps_le {plan : BlockPlan} (h : plan.WF) {i : Nat}
    (hi : i < plan.nblocks) : (Id.run (plan.steps i)).2.1 ≤ (Id.run (plan.steps i)).2.2 := by
  obtain ⟨seg, hs, h1, h2, he⟩ := h.run_steps hi
  rw [he]
  refine (blockRange_le h.one_le_len ?_).2.1
  rw [h.segBlock_succ hs] at h2
  lia

/-! ### Well-formed decisions -/

/-- A decision `d` of the correction of the moduli is well-formed for the sieve entries `es` of the
run and the end `sp1` of the first stage: `sp1 ≤ d.sp2 ≤ d.sp3 ≤ |es|`, and every entry from the
position `d.sp2` on, those of the third stage and the reserve, counts no factor
(`Ratpoints.Sieve.SieveEntry.nf` zero), so that, for the entries of the choice of the moduli, it is
a prime of the table, as the third stage needs. -/
structure DecisionWF (es : List SieveEntry) (sp1 : Nat) (d : Decision) : Prop where
  /-- The end of the second stage is at least that of the first. -/
  sp1_le_sp2 : sp1 ≤ d.sp2
  /-- The end of the third stage is at least that of the second. -/
  sp2_le_sp3 : d.sp2 ≤ d.sp3
  /-- The end of the third stage is at most the number of the entries. -/
  sp3_le_length : d.sp3 ≤ es.length
  /-- Every entry from the end of the second stage on counts no factor. -/
  nf_eq_zero : ∀ e ∈ es.drop d.sp2, e.nf = 0

/-- A well-formed decision gives a well-formed decision with its end of the second stage and no
third stage, for any first block. -/
theorem DecisionWF.mk_sp2 {l : List SieveEntry} {sp1 : Nat} {d : Decision}
    (h : DecisionWF l sp1 d) (b : Nat) : DecisionWF l sp1 ⟨b, d.sp2, d.sp2⟩ :=
  ⟨h.sp1_le_sp2, Nat.le_refl _, by lia [h.sp2_le_sp3, h.sp3_le_length], h.nf_eq_zero⟩

/-- A well-formed decision stays well-formed for the sieve entries with the inverses of the strides
that `Ratpoints.Sieve.classOffsets` sets. -/
theorem DecisionWF.map_dinv {es : List SieveEntry} {sp1 : Nat} {d : Decision}
    (h : DecisionWF es sp1 d) (dinv : SieveEntry → Array Nat) :
    DecisionWF (es.map fun e ↦ { e with dinv := dinv e }) sp1 d := by
  refine ⟨h.sp1_le_sp2, h.sp2_le_sp3, by simpa using h.sp3_le_length, fun e he ↦ ?_⟩
  rw [← List.map_drop] at he
  obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
  exact h.nf_eq_zero e' he'

end Sieve

end Ratpoints

end
