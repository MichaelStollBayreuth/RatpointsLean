/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Blocks

import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
import Std.Tactic.Do

/-!
# The correction of the moduli and the run

The run sifts its blocks in order (`Ratpoints.Sieve.sieveRun`), each with the cut points of the
decision for it (`Ratpoints.Sieve.findDecision`), and folds the counters of each block into the
state of the correction (`Ratpoints.Sieve.runFold`), which may push a decision for the blocks from
`Ratpoints.adaptLag + 1` blocks later on (`Ratpoints.Sieve.adaptPrimes`). The counters are counted
before the exact check, so that the decisions depend neither on the callback nor on the flags of the
output: while the callback does not stop the search, the state of the correction is a fold of the
reports of the blocks in closed form (`Ratpoints.Sieve.correctionAfter`), and a stop of the callback
in a block ends the run before any decision that the fold of that block pushes is read. So the run
delivers the points of its blocks in order, each with the decision of the block
(`Ratpoints.Sieve.blockDecision`), and, over the denominators of its shape in the order of its
loops, the points of the numerators that pass the class word and survive the entries of the first
three stages of the decision of the block of the denominator, a decision that is a function of the
denominator alone. The correction keeps the decisions well-formed (`Ratpoints.Sieve.DecisionWF`) for
any values of the doubles of its cost model, and the decision of a block reads only the folds of the
blocks at least `Ratpoints.adaptLag + 1` blocks before it.

## Main definitions

* `Ratpoints.Sieve.Correction.WF`: a well-formed state of the correction.
* `Ratpoints.Sieve.correctionAfter`, `Ratpoints.Sieve.blockDecision`: the state of the correction
  after the folds of the first blocks with their reports in closed form
  (`Ratpoints.Sieve.blockReport`), and the decision of a block, both free of the callback and the
  flags.
* `Ratpoints.Sieve.blockPoints`: the points that a block delivers.
* `Ratpoints.Sieve.deliverSlots`: the calling thread of a run with threads, which delivers the
  slots of the blocks in their order.

## Main statements

* `Ratpoints.Sieve.adaptPrimes_spec`, `Ratpoints.Sieve.runFold_spec`,
  `Ratpoints.Sieve.wf_correctionAfter`: the correction keeps the decisions well-formed.
* `Ratpoints.Sieve.getElem!_findDecision_correctionAfter`: the lag of the correction, the decision
  in force for block `i` is the same after the folds of any `k ≥ i - adaptLag` blocks.
* `Ratpoints.Sieve.sieveRun_spec`, `Ratpoints.Sieve.fst_run_sieveRun`: the block lemma, the run
  delivers the points of its blocks in order, each with its decision.
* `Ratpoints.Sieve.exists_run_sieveRun_eq_deliver`: the contract of the run per denominator.
* `Ratpoints.Sieve.run_deliverSlots_eq_fst_run_sieveRun`: the property that the threads, which the
  model leaves out, preserve: the blocks sifted apart into slots with the decisions after enough
  folds, each with a store of its own, and delivered in their order give the output of the run.

## Implementation notes

The contracts of the loops of the correction state only what the natural numbers of the C code do:
no proof reads a value of the doubles, so every statement holds for whatever values the cost model
computes. The run's invariant (`Ratpoints.Sieve.SieveRunLoopInvariant`) states the delivery for
every choice of the words of the classes and the ranges of the numerators
(`Ratpoints.Sieve.RunWords`), as the contract of one block does (`Ratpoints.Sieve.runBlock_spec`).
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

open BruteForce

/-! ### The correction keeps the decisions well-formed -/

/-- The invariant of the loop of `Ratpoints.Sieve.adaptUp` over the entries from `start` on, on
the new end of the second stage: at least `start`, and at most `start` plus the entries passed. -/
def AdaptUpInvariant (start : Nat) : Std.WP.Invariant Nat (Nat × Float × Float) Prop :=
  fun pref _ st ↦ start ≤ st.1 ∧ st.1 ≤ start + pref.length

theorem AdaptUpInvariant.push {start want cur : Nat} {pref : List Nat}
    (h : start ≤ want ∧ want ≤ start + pref.length) :
    start ≤ want + 1 ∧ want + 1 ≤ start + (pref ++ [cur]).length := by
  simp only [List.length_append, List.length_singleton]
  lia

theorem AdaptUpInvariant.done {start want m cur : Nat} {pref suff : List Nat}
    (hl : ForIn.toList [start:m] = pref ++ cur :: suff)
    (h : start ≤ want ∧ want ≤ start + pref.length) :
    start ≤ want ∧ want ≤ start + (ForIn.toList [start:m]).length := by
  rw [hl, List.length_append]
  lia

open Std.WP Lean.Order in
/-- The walk of the correction up from the end `start` of the second stage takes some of the
entries from `start` on: for any values of the doubles, the new end is at least `start` and at most
the number of the entries, if `start` is. -/
theorem adaptUp_spec (es : Array SieveEntry) (start : Nat)
    (level chance rate s costSurv ct U D : Float) :
    ⦃ True ⦄ adaptUp es start level chance rate s costSurv ct U D
    ⦃ fun r ↦ start ≤ r.1 ∧ r.1 ≤ start + (es.size - start) ⦄ := by
  vcgen [adaptUp] invariants
  | inv1 => AdaptUpInvariant start
  all_goals simp only [AdaptUpInvariant, Std.Legacy.Range.length_toList] at *
  all_goals first
    | exact ⟨Nat.le_refl _, Nat.le_add_right _ _⟩
    | exact ‹_›
    | exact AdaptUpInvariant.push ‹_›
    | exact (Std.Legacy.Range.length_toList start es.size) ▸ AdaptUpInvariant.done ‹_› ‹_›

/-- The invariant of the loop of `Ratpoints.Sieve.adaptDown` on the new end `want` of the second
stage and the position `n` of the next entry, from the end `sp2`: `want` at most `sp2` and at least
`sp1` if `sp2` is, the entries from `want` to `sp2` primes of the table, and `n` the position just
below `want` while it is not `0`. -/
def AdaptDownInvariant (es : Array SieveEntry) (sp1 sp2 : Nat) :
    Std.WP.WhileInvariant (Nat × Float × Float × Nat) Prop :=
  .mk fun _ st ↦ st.1 ≤ sp2 ∧ (sp1 ≤ sp2 → sp1 ≤ st.1) ∧
    (∀ k, st.1 ≤ k → k < sp2 → es[k]!.nf = 0) ∧ (st.2.2.2 = 0 ∨ st.1 = st.2.2.2 + 1)

theorem adaptDownInvariant_init (es : Array SieveEntry) (sp1 sp2 : Nat) :
    sp2 ≤ sp2 ∧ (sp1 ≤ sp2 → sp1 ≤ sp2) ∧ (∀ k, sp2 ≤ k → k < sp2 → es[k]!.nf = 0) ∧
      (sp2 - 1 = 0 ∨ sp2 = sp2 - 1 + 1) :=
  ⟨Nat.le_refl _, id, fun _ h h' ↦ absurd h' (by lia), by lia⟩

theorem AdaptDownInvariant.sub_one {es : Array SieveEntry} {sp1 sp2 want n : Nat}
    (h : want ≤ sp2 ∧ (sp1 ≤ sp2 → sp1 ≤ want) ∧ (∀ k, want ≤ k → k < sp2 → es[k]!.nf = 0) ∧
      (n = 0 ∨ want = n + 1)) (hc : (decide (sp1 < n) && es[n]!.nf == 0) = true) :
    n - 1 < n ∧ want - 1 ≤ sp2 ∧ (sp1 ≤ sp2 → sp1 ≤ want - 1) ∧
      (∀ k, want - 1 ≤ k → k < sp2 → es[k]!.nf = 0) ∧ (n - 1 = 0 ∨ want - 1 = n - 1 + 1) := by
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨by lia, by lia, fun _ ↦ by lia, fun k hk hk' ↦ ?_, by lia⟩
  rcases Nat.lt_or_ge k want with hlt | hge
  · obtain rfl : k = n := by lia
    exact hc.2
  · exact h3 k hge hk'

open Std.WP Lean.Order in
/-- The walk of the correction down from the end `sp2` of the second stage drops some of the
entries below `sp2`, only primes of the table and never below `sp1`: for any values of the doubles,
the new end is at most `sp2`, at least `sp1` if `sp2` is, and the entries from it to `sp2` count no
factors. -/
theorem adaptDown_spec (es : Array SieveEntry) (sp1 sp2 : Nat)
    (level chance rate s costSurv ct U D : Float) :
    ⦃ True ⦄ adaptDown es sp1 sp2 level chance rate s costSurv ct U D
    ⦃ fun r ↦ r.1 ≤ sp2 ∧ (sp1 ≤ sp2 → sp1 ≤ r.1) ∧ ∀ k, r.1 ≤ k → k < sp2 → es[k]!.nf = 0 ⦄ := by
  vcgen [adaptDown] invariants
  | inv1 => AdaptDownInvariant es sp1 sp2
  | inv2 => .ofMeasure fun st ↦ st.2.2.2
  all_goals simp only [AdaptDownInvariant, WhileInvariant.mk_apply, Variant.evalsTo_ofMeasure,
    Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure, meet_prop_eq_and,
    ofProp_prop_eq] at *
  all_goals first
    | exact adaptDownInvariant_init es sp1 sp2
    | (rename_i hc _ h
       obtain ⟨rfl, h⟩ := h
       exact AdaptDownInvariant.sub_one h hc)
    | (rename_i h
       first
         | exact h.2
         | exact ⟨h.1, h.2.1, h.2.2.1⟩)

/-- The invariant of the loop of `Ratpoints.Sieve.adaptThird` on the end `sp3` of the third stage,
from the end `sp2` of the second: at least `sp2` and at most `sp2` and the number of the entries. -/
def AdaptThirdInvariant (es : Array SieveEntry) (sp2 : Nat) :
    Std.WP.WhileInvariant (Float × Nat) Prop :=
  .mk fun _ st ↦ sp2 ≤ st.2 ∧ st.2 ≤ sp2 + (es.size - sp2)

open Std.WP Lean.Order in
/-- The correction of the third stage takes some of the entries from the end `sp2` of the second
stage on: for any values of the doubles, the end of the third stage is at least `sp2` and at most
the number of the entries, if `sp2` is. -/
theorem adaptThird_spec (es : Array SieveEntry) (c : RunCounts) (sp2 : Nat)
    (q checkRel level chance r2 s : Float) :
    ⦃ True ⦄ adaptThird es c sp2 q checkRel level chance r2 s
    ⦃ fun r ↦ sp2 ≤ r ∧ r ≤ sp2 + (es.size - sp2) ⦄ := by
  vcgen [adaptThird] invariants
  | inv1 => AdaptThirdInvariant es sp2
  | inv2 => .ofMeasure fun st ↦ es.size - st.2
  | inv3 => AdaptThirdInvariant es sp2
  | inv4 => .ofMeasure fun st ↦ es.size - st.2
  all_goals simp only [AdaptThirdInvariant, WhileInvariant.mk_apply, Variant.evalsTo_ofMeasure,
    Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure, meet_prop_eq_and,
    ofProp_prop_eq] at *
  all_goals lia

-- The end of the second stage after the walk up is well-formed.
private theorem DecisionWF.of_up {es : Array SieveEntry} {sp1 b b' x y : Nat}
    (h : DecisionWF es.toList sp1 ⟨b, x, x⟩) (hy : x ≤ y ∧ y ≤ x + (es.size - x)) :
    DecisionWF es.toList sp1 ⟨b', y, y⟩ := by
  obtain ⟨h1, -, h3, h4⟩ := h
  simp only [Array.length_toList] at h3
  exact ⟨by lia, Nat.le_refl _, by simp only [Array.length_toList]; lia,
    fun e he ↦ h4 e ((List.drop_sublist_drop_left _ hy.1).subset he)⟩

-- The end of the second stage after the walk down is well-formed.
private theorem DecisionWF.of_down {es : Array SieveEntry} {sp1 b b' x y : Nat}
    (h : DecisionWF es.toList sp1 ⟨b, x, x⟩)
    (hy : y ≤ x ∧ (sp1 ≤ x → sp1 ≤ y) ∧ ∀ k, y ≤ k → k < x → es[k]!.nf = 0) :
    DecisionWF es.toList sp1 ⟨b', y, y⟩ := by
  obtain ⟨h1, -, h3, h4⟩ := h
  refine ⟨hy.2.1 h1, Nat.le_refl _, by lia, List.forall_mem_drop_of_forall_getElem! h4 ?_⟩
  intro k hk hk'
  rw [getElem!_pos es.toList k (by lia), Array.getElem_toList,
    ← getElem!_pos es k (by simp at h3; lia)]
  exact hy.2.2 k hk hk'

-- The end of the third stage after its correction is well-formed.
private theorem DecisionWF.of_third {es : Array SieveEntry} {sp1 b b' x z : Nat}
    (h : DecisionWF es.toList sp1 ⟨b, x, x⟩) (hz : x ≤ z ∧ z ≤ x + (es.size - x)) :
    DecisionWF es.toList sp1 ⟨b', x, z⟩ := by
  obtain ⟨h1, -, h3, h4⟩ := h
  simp only [Array.length_toList] at h3
  exact ⟨h1, hz.1, by simp only [Array.length_toList]; lia, h4⟩

-- The end of the third stage, at least that of the second, is well-formed.
private theorem DecisionWF.ite_lt {l : List SieveEntry} {sp1 b b' b'' x y z : Nat}
    (h : DecisionWF l sp1 ⟨b, x, x⟩) (h' : DecisionWF l sp1 ⟨b'', y, z⟩) :
    DecisionWF l sp1 ⟨b', x, if z < x then x else z⟩ := by
  refine ⟨h.sp1_le_sp2, ?_, ?_, h.nf_eq_zero⟩ <;> split <;>
    lia [h.sp3_le_length, h'.sp3_le_length]

open Std.WP Lean.Order in
/-- The correction of the end of the second stage keeps it well-formed. -/
theorem adaptSecond_spec (es : Array SieveEntry) (c : RunCounts) (sp1 : Nat)
    (level chance r2 checkRel ct U D : Float) :
    ⦃ DecisionWF es.toList sp1 ⟨0, c.sp2, c.sp2⟩ ⦄
    adaptSecond es c sp1 level chance r2 checkRel ct U D
    ⦃ fun r ↦ DecisionWF es.toList sp1 ⟨0, r.1, r.1⟩ ⦄ := by
  vcgen [adaptSecond, adaptUp_spec, adaptDown_spec]
  all_goals dsimp only at *
  all_goals first
    | exact DecisionWF.of_down ‹_› ‹_›
    | exact DecisionWF.of_up ‹_› ‹_›

-- The rates of the run, of no matter here.
private theorem adaptRates_true (es : Array SieveEntry) (c : RunCounts) (sp1 : Nat) :
    ⦃ True ⦄ adaptRates es c sp1 ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

open Std.WP Lean.Order in
/-- The correction of the choice of the moduli keeps the decision well-formed. -/
theorem adaptPrimes_spec (s : SieveOptions) (P : Params) (es : Array SieveEntry) (c : RunCounts)
    (sp2 sp3 : Nat) :
    ⦃ DecisionWF es.toList P.sp1 ⟨0, sp2, sp3⟩ ∧ DecisionWF es.toList P.sp1 ⟨0, c.sp2, c.sp2⟩ ⦄
    adaptPrimes s P es c sp2 sp3
    ⦃ fun r ↦ DecisionWF es.toList P.sp1 ⟨0, r.1, r.2.1⟩ ⦄ := by
  vcgen [adaptPrimes, adaptRates_true, adaptSecond_spec, adaptThird_spec]
  all_goals try dsimp only at *
  all_goals obtain ⟨hwf, hc⟩ := ‹DecisionWF _ _ _ ∧ DecisionWF _ _ _›
  all_goals first
    | exact hc
    | exact hwf
    | exact DecisionWF.of_third ‹_› ‹_›
    | exact DecisionWF.ite_lt ‹_› hwf
    | exact DecisionWF.ite_lt (hwf.mk_sp2 0) hwf
    | exact DecisionWF.of_third (hwf.mk_sp2 0) ‹_›

/-! ### The fold of a block -/

/-- The counters of the second stage on, after a fold, are counted under the end of the second stage
of the block folded. -/
@[simp]
theorem RunCounts.sp2_fold (c : RunCounts) (sp2 : Nat) (k : Counters) :
    (c.fold sp2 k).sp2 = sp2 := by
  simp only [RunCounts.fold]
  split <;> simp_all

/-- The state of the correction of the moduli is well-formed for the sieve entries `es` and the end
`sp1` of the first stage: its decisions, the first for block `0`, well-formed
(`Ratpoints.Sieve.DecisionWF`), as are the latest decision and the end of the second stage that the
counters of the run were counted under. -/
structure Correction.WF (es : List SieveEntry) (sp1 : Nat) (corr : Correction) : Prop where
  /-- There is a decision. -/
  size_pos : 0 < corr.decisions.size
  /-- The first decision is for block `0`. -/
  block_zero : corr.decisions[0]!.block = 0
  /-- Every decision is well-formed. -/
  decisionWF : ∀ d ∈ corr.decisions, DecisionWF es sp1 d
  /-- The latest decision is well-formed. -/
  latest : DecisionWF es sp1 ⟨0, corr.sp2, corr.sp3⟩
  /-- The end of the second stage of the counters is one of a well-formed decision. -/
  counted : DecisionWF es sp1 ⟨0, corr.cnt.sp2, corr.cnt.sp2⟩

theorem Correction.wf_start {es : List SieveEntry} {sp1 sp2 sp3 : Nat} (adaptAt : UInt64)
    (h : DecisionWF es sp1 ⟨0, sp2, sp3⟩) : (Correction.start sp2 sp3 adaptAt).WF es sp1 :=
  ⟨by simp [Correction.start], rfl, by simpa [Correction.start] using h, h, h.mk_sp2 0⟩

-- The end of the second stage that the counters of the run are counted under after the fold of a
-- block reported with one of the decisions is one of a well-formed decision.
private theorem Correction.WF.fold {es : List SieveEntry} {sp1 : Nat} {st : Correction}
    {b : BlockStat} (h : st.WF es sp1) (hb : b.dec < st.decisions.size) :
    DecisionWF es sp1 ⟨0, (st.cnt.fold st.decisions[b.dec]!.sp2 b.cnt).sp2,
      (st.cnt.fold st.decisions[b.dec]!.sp2 b.cnt).sp2⟩ := by
  rw [RunCounts.sp2_fold]
  exact (h.decisionWF _ (getElem!_pos st.decisions b.dec hb ▸ Array.getElem_mem hb)).mk_sp2 0

-- The fold of a block before the words of the next correction.
private theorem Correction.WF.fold_of_lt {es : List SieveEntry} {sp1 : Nat} {st : Correction}
    {b : BlockStat} (h : st.WF es sp1) (hb : b.dec < st.decisions.size) :
    Correction.WF es sp1
      { st with
        cnt := st.cnt.fold st.decisions[b.dec]!.sp2 b.cnt
        folded := st.folded + 1
        lastSp2 := b.sp2
        lastSp3 := b.sp3 } ∧
      ∃ L, st.decisions.toList = st.decisions.toList ++ L ∧
        ∀ d ∈ L, d.block = st.folded + adaptLag + 1 :=
  ⟨⟨h.size_pos, h.block_zero, h.decisionWF, h.latest, h.fold hb⟩, [], by simp, by simp⟩

-- The fold of a block with a correction, whose decision is well-formed.
private theorem Correction.WF.fold_adapt {es : List SieveEntry} {sp1 : Nat} {st : Correction}
    {b : BlockStat} (h : st.WF es sp1) (hb : b.dec < st.decisions.size) {sp2 sp3 : Nat}
    (adaptAt : UInt64) (ha : DecisionWF es sp1 ⟨0, sp2, sp3⟩) :
    Correction.WF es sp1
      { st with
        cnt := st.cnt.fold st.decisions[b.dec]!.sp2 b.cnt
        folded := st.folded + 1
        lastSp2 := b.sp2
        lastSp3 := b.sp3
        sp2 := sp2
        sp3 := sp3
        adaptAt := adaptAt
        decisions := if (sp2 != st.sp2 || sp3 != st.sp3) = true then
          st.decisions.push ⟨st.folded + adaptLag + 1, sp2, sp3⟩ else st.decisions } ∧
      ∃ L, (if (sp2 != st.sp2 || sp3 != st.sp3) = true then
          st.decisions.push ⟨st.folded + adaptLag + 1, sp2, sp3⟩ else st.decisions).toList =
        st.decisions.toList ++ L ∧ ∀ d ∈ L, d.block = st.folded + adaptLag + 1 := by
  split
  · refine ⟨⟨by simp, ?_, fun d hd ↦ ?_, ha, h.fold hb⟩, [⟨st.folded + adaptLag + 1, sp2, sp3⟩],
      by simp, by simp⟩
    · rw [getElem!_pos _ 0 (by simp), Array.getElem_push_lt h.size_pos,
        ← getElem!_pos _ 0 h.size_pos, h.block_zero]
    · rcases Array.mem_push.mp hd with hd | rfl
      · exact h.decisionWF d hd
      · exact ⟨ha.sp1_le_sp2, ha.sp2_le_sp3, ha.sp3_le_length, ha.nf_eq_zero⟩
  · exact ⟨⟨h.size_pos, h.block_zero, h.decisionWF, ha, h.fold hb⟩, [], by simp, by simp⟩

open Std.WP Lean.Order in
/-- The fold of a block reported with one of the decisions keeps the correction well-formed: the
counters are then counted under the end of the second stage of that decision, and the decision that
the correction may push is well-formed (`Ratpoints.Sieve.adaptPrimes_spec`). -/
theorem runFold_spec (s : SieveOptions) (P : Params) (es : List SieveEntry) (st : Correction)
    (b : BlockStat) :
    ⦃ st.WF es P.sp1 ∧ b.dec < st.decisions.size ⦄ runFold s P es.toArray st b
    ⦃ fun st' ↦ st'.WF es P.sp1 ⦄ := by
  vcgen [runFold, adaptPrimes_spec]
  all_goals dsimp only at *
  all_goals obtain ⟨h, hb⟩ := ‹Correction.WF _ _ _ ∧ _›
  all_goals first
    | exact (h.fold_of_lt hb).1
    | exact ⟨h.latest, h.fold hb⟩
    | exact (h.fold_adapt hb _ ‹_›).1

-- The decisions after the fold of a block, with or without a new one.
private theorem exists_toList_ite_push (c : Bool) (decs : Array Decision) (j sp2 sp3 : Nat) :
    ∃ L, (if c = true then decs.push ⟨j, sp2, sp3⟩ else decs).toList = decs.toList ++ L ∧
      ∀ d ∈ L, d.block = j := by
  split
  · exact ⟨[⟨j, sp2, sp3⟩], by simp, by simp⟩
  · exact ⟨[], by simp, by simp⟩

-- The correction of the moduli, of no matter for the decisions pushed.
private theorem adaptPrimes_true (s : SieveOptions) (P : Params) (es : Array SieveEntry)
    (c : RunCounts) (sp2 sp3 : Nat) : ⦃ True ⦄ adaptPrimes s P es c sp2 sp3 ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

open Std.WP Lean.Order in
/-- The fold of a block counts one more block folded and pushes at most a decision, for the blocks
from `Ratpoints.adaptLag + 1` blocks later on. -/
theorem runFold_decisions_spec (s : SieveOptions) (P : Params) (es : Array SieveEntry)
    (st : Correction) (b : BlockStat) :
    ⦃ True ⦄ runFold s P es st b
    ⦃ fun st' ↦ st'.folded = st.folded + 1 ∧ ∃ L, st'.decisions.toList =
        st.decisions.toList ++ L ∧ ∀ d ∈ L, d.block = st.folded + adaptLag + 1 ⦄ := by
  vcgen [runFold, adaptPrimes_true]
  all_goals dsimp only at *
  all_goals first
    | exact exists_toList_ite_push _ _ _ _ _
    | exact ⟨[], (List.append_nil _).symm, fun _ h ↦ absurd h List.not_mem_nil⟩

/-! ### The correction of the run in closed form -/

/-- The state of the correction of the moduli after the folds of the first `k` blocks of the run
(`Ratpoints.Sieve.runFold`), each with its report in closed form (`Ratpoints.Sieve.blockReport`),
from the choice (`Ratpoints.Sieve.Correction.start`, with the ends `P.sp2` and `P.sp3` and the words
`P.adaptAt`): what the run keeps while the callback does not stop the search, a function of the
arguments of the run that depends neither on the callback nor on the flags of the output, for the
height `H`, the options `s`, the result `P` of the choice, the sieve entries `entries` with the
reciprocals `magics` of their moduli, the classes `cls`, the word `db` of the classes that admit a
numerator, the shape `shape`, the bounds `iv` of the search intervals and the denominators from
`bLow` to `bHigh`. -/
def correctionAfter (H : Nat) (s : SieveOptions) (P : Params) (entries : List SieveEntry)
    (magics : Array Nat) (cls : Vector NumClass 64) (db : UInt64) (shape : Shape)
    (iv : Array IntervalBounds) (bLow bHigh : Nat) : Nat → Correction
  | 0 => Correction.start P.sp2 P.sp3 P.adaptAt
  | k + 1 =>
    let corr := correctionAfter H s P entries magics cls db shape iv bLow bHigh k
    Id.run (runFold s P entries.toArray corr
      (blockReport H P.sp1 entries magics cls db shape iv bLow bHigh corr.decisions k))

/-- The decision of the correction of the moduli in force for block `i` of the run
(`Ratpoints.Sieve.findDecision`), among the decisions after the folds of the blocks before it
(`Ratpoints.Sieve.correctionAfter`), which depends neither on the callback nor on the flags of the
output. -/
def blockDecision (H : Nat) (s : SieveOptions) (P : Params) (entries : List SieveEntry)
    (magics : Array Nat) (cls : Vector NumClass 64) (db : UInt64) (shape : Shape)
    (iv : Array IntervalBounds) (bLow bHigh i : Nat) : Decision :=
  let decs := (correctionAfter H s P entries magics cls db shape iv bLow bHigh i).decisions
  decs[Id.run (findDecision decs i)]!

section

variable {H : Nat} {s : SieveOptions} {P : Params} {entries : List SieveEntry} {magics : Array Nat}
  {cls : Vector NumClass 64} {db : UInt64} {shape : Shape} {iv : Array IntervalBounds}
  {bLow bHigh : Nat}

/-- The blocks folded so far. -/
theorem folded_correctionAfter (k : Nat) :
    (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).folded = k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    exact ((runFold_decisions_spec s P _ _ _).le_wp trivial).1.trans (congrArg (· + 1) ih)

/-- The decisions after the folds of the first `k` blocks are those after the first `m ≤ k`
followed by decisions for the blocks from `m + Ratpoints.adaptLag + 1` on. -/
theorem exists_toList_decisions_correctionAfter {m k : Nat} (hmk : m ≤ k) :
    ∃ L, (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).decisions.toList =
      (correctionAfter H s P entries magics cls db shape iv bLow bHigh m).decisions.toList ++ L ∧
        ∀ d ∈ L, m + adaptLag + 1 ≤ d.block := by
  induction k, hmk using Nat.le_induction with
  | base => exact ⟨[], by simp, by simp⟩
  | succ k hmk ih =>
    obtain ⟨L, hL, hb⟩ := ih
    obtain ⟨-, L', hL', hb'⟩ := (runFold_decisions_spec s P entries.toArray
      (correctionAfter H s P entries magics cls db shape iv bLow bHigh k) _).le_wp trivial
    refine ⟨L ++ L', ?_, fun d hd ↦ ?_⟩
    · rw [← List.append_assoc, ← hL, ← hL']
      rfl
    · rcases List.mem_append.mp hd with hd | hd
      · exact hb d hd
      · rw [hb' d hd, folded_correctionAfter]
        lia

/-- There is a decision, and the first is for block `0`. -/
theorem size_pos_and_block_zero_correctionAfter (k : Nat) :
    0 < (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).decisions.size ∧
      (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).decisions[0]!.block =
        0 := by
  obtain ⟨L, hL, -⟩ := exists_toList_decisions_correctionAfter (H := H) (s := s) (P := P)
    (entries := entries) (magics := magics) (cls := cls) (db := db) (shape := shape) (iv := iv)
    (bLow := bLow) (bHigh := bHigh) (Nat.zero_le k)
  replace hL : _ = [⟨0, P.sp2, P.sp3⟩] ++ L := hL
  have hs :
      0 < (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).decisions.size := by
    rw [← Array.length_toList, hL]
    simp
  refine ⟨hs, ?_⟩
  rw [getElem!_pos _ 0 hs, ← Array.getElem_toList, List.getElem_of_eq hL]
  rfl

/-- The state of the correction of the moduli after the folds of the first `k` blocks of the run is
well-formed, for a well-formed decision of the choice. -/
theorem wf_correctionAfter (hdec : DecisionWF entries P.sp1 ⟨0, P.sp2, P.sp3⟩) (k : Nat) :
    (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).WF entries P.sp1 := by
  induction k with
  | zero => exact Correction.wf_start _ hdec
  | succ k ih =>
    exact (runFold_spec s P entries _ _).le_wp ⟨ih, ((findDecision_spec _ k).le_wp ⟨ih.size_pos,
      ih.block_zero⟩).1⟩

end

/-! ### The decision in force for a block: the lag -/

-- The entries of the decisions extended by `L` at the positions of the decisions.
private theorem getElem!_eq_of_toList_eq_append {decs decs' : Array Decision} {L : List Decision}
    (h : decs'.toList = decs.toList ++ L) {j : Nat} (hj : j < decs.size) :
    decs'[j]! = decs[j]! := by
  have hs : decs'.size = decs.size + L.length := by simpa using congrArg List.length h
  rw [getElem!_pos decs' j (by lia), getElem!_pos decs j hj, ← Array.getElem_toList,
    List.getElem_of_eq h, List.getElem_append_left (by simpa using hj), Array.getElem_toList]

-- The entries of the decisions extended by `L` beyond the positions of the decisions.
private theorem getElem!_mem_of_toList_eq_append {decs decs' : Array Decision} {L : List Decision}
    (h : decs'.toList = decs.toList ++ L) {j : Nat} (hj : decs.size ≤ j) (hj' : j < decs'.size) :
    decs'[j]! ∈ L := by
  rw [getElem!_pos decs' j hj', ← Array.getElem_toList, List.getElem_of_eq h,
    List.getElem_append_right (by simpa using hj)]
  exact List.getElem_mem _

/-- The decision in force for block `i` is unique: the last whose first block is at most `i`. -/
theorem Decision.InForce.unique {decs : Array Decision} {i dd dd' : Nat}
    (h : InForce decs i dd) (h' : InForce decs i dd') : dd = dd' := by
  by_contra hne
  rcases Nat.lt_or_gt_of_ne hne with hlt | hlt
  · exact absurd (h.2.2 dd' hlt h'.1) (Nat.not_lt.mpr h'.2.1)
  · exact absurd (h'.2.2 dd hlt h.1) (Nat.not_lt.mpr h.2.1)

/-- The index of the decision in force for block `i` among decisions of which the first is for
block `0` is also that among these decisions followed by decisions for blocks after block `i`: the
decision in force is unique (`Ratpoints.Sieve.Decision.InForce.unique`). -/
theorem findDecision_eq_of_toList_eq_append {decs decs' : Array Decision} {L : List Decision}
    {i : Nat} (h0 : 0 < decs.size) (hb : decs[0]!.block = 0) (h : decs'.toList = decs.toList ++ L)
    (hL : ∀ d ∈ L, i < d.block) :
    Id.run (findDecision decs' i) = Id.run (findDecision decs i) := by
  have hs : decs'.size = decs.size + L.length := by simpa using congrArg List.length h
  obtain ⟨h1, h2, h3⟩ := (findDecision_spec decs i).le_wp ⟨h0, hb⟩
  refine Decision.InForce.unique ((findDecision_spec decs' i).le_wp ⟨by lia,
    (congrArg Decision.block (getElem!_eq_of_toList_eq_append h h0)).trans hb⟩)
    ⟨by rw [hs]; exact Nat.lt_add_right _ h1, ?_, fun j hj hj' ↦ ?_⟩
  · exact (congrArg Decision.block (getElem!_eq_of_toList_eq_append h h1)).trans_le h2
  · rcases Nat.lt_or_ge j decs.size with hjs | hjs
    · rw [getElem!_eq_of_toList_eq_append h hjs]
      exact h3 j hj hjs
    · exact hL _ (getElem!_mem_of_toList_eq_append h hjs hj')

/-- The decision in force for block `i` among decisions of which the first is for block `0` is
also that among these decisions followed by decisions for blocks after block `i`. -/
theorem getElem!_findDecision_eq_of_toList_eq_append {decs decs' : Array Decision}
    {L : List Decision} {i : Nat} (h0 : 0 < decs.size) (hb : decs[0]!.block = 0)
    (h : decs'.toList = decs.toList ++ L) (hL : ∀ d ∈ L, i < d.block) :
    decs'[Id.run (findDecision decs' i)]! = decs[Id.run (findDecision decs i)]! := by
  rw [findDecision_eq_of_toList_eq_append h0 hb h hL]
  exact getElem!_eq_of_toList_eq_append h ((findDecision_spec decs i).le_wp ⟨h0, hb⟩).1

section

variable {H : Nat} {s : SieveOptions} {P : Params} {entries : List SieveEntry} {magics : Array Nat}
  {cls : Vector NumClass 64} {db : UInt64} {shape : Shape} {iv : Array IntervalBounds}
  {bLow bHigh : Nat}

-- The decisions after `k ≥ i - adaptLag` folds, for block `i`, are those after `i - adaptLag`.
private theorem getElem!_findDecision_correctionAfter_eq {i k : Nat} (hk : i - adaptLag ≤ k) :
    (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).decisions[Id.run
        (findDecision (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).decisions
          i)]! =
      (correctionAfter H s P entries magics cls db shape iv bLow bHigh (i - adaptLag)).decisions[
        Id.run (findDecision (correctionAfter H s P entries magics cls db shape iv bLow bHigh
          (i - adaptLag)).decisions i)]! := by
  obtain ⟨L, hL, hb⟩ := exists_toList_decisions_correctionAfter (H := H) (s := s) (P := P)
    (entries := entries) (magics := magics) (cls := cls) (db := db) (shape := shape) (iv := iv)
    (bLow := bLow) (bHigh := bHigh) hk
  exact getElem!_findDecision_eq_of_toList_eq_append (size_pos_and_block_zero_correctionAfter _).1
    (size_pos_and_block_zero_correctionAfter _).2 hL fun d hd ↦ by lia [hb d hd]

/-- The lag of the correction of the moduli: the decision in force for block `i` among the decisions
after the folds of the first `k` blocks is the decision of block `i`
(`Ratpoints.Sieve.blockDecision`) for every `k ≥ i - Ratpoints.adaptLag`, since a decision made at
the fold of block `j` is for the blocks from `j + Ratpoints.adaptLag + 1` on: block `i` reads only
the decisions made at the folds of the blocks before block `i - Ratpoints.adaptLag`. -/
theorem getElem!_findDecision_correctionAfter {i k : Nat} (hk : i - adaptLag ≤ k) :
    (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).decisions[Id.run
        (findDecision (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).decisions
          i)]! = blockDecision H s P entries magics cls db shape iv bLow bHigh i :=
  (getElem!_findDecision_correctionAfter_eq hk).trans
    (getElem!_findDecision_correctionAfter_eq (Nat.sub_le i adaptLag)).symm

end

/-! ### The run -/

-- The plan of the blocks and the fold of a block, as values for the contract of the run.
private theorem blockPlan_value (shape : Shape) (bLow bHigh : Nat) :
    ⦃ True ⦄ shape.blockPlan bLow bHigh ⦃ fun p ↦ p = Id.run (shape.blockPlan bLow bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem runFold_value (s : SieveOptions) (P : Params) (es : Array SieveEntry)
    (st : Correction) (b : BlockStat) :
    ⦃ True ⦄ runFold s P es st b ⦃ fun st' ↦ st' = Id.run (runFold s P es st b) ⦄ :=
  ⟨fun _ ↦ rfl⟩

variable {σ : Type} (process : Int → Int → Int → σ → Answer σ)

/-- The points that block `i` of the run delivers, for the polynomial of degree `d` with the
coefficient list `c`, the height `H`, the flags `fl` and the words `x.1` of the classes and the
ranges `x.2` of the numerators of `Ratpoints.Sieve.RunWords`: those of its denominators
(`Ratpoints.Sieve.blockDens`) that pass the tests of the shape, in order, each with the first `sp3`
sieve entries of the decision of the block (`Ratpoints.Sieve.blockDecision`,
`Ratpoints.Sieve.denPoints`). -/
def blockPoints (c : List Int) (d H : Nat) (fl : CheckFlags) (s : SieveOptions) (P : Params)
    (entries : List SieveEntry) (magics : Array Nat) (cls : Vector NumClass 64) (db : UInt64)
    (shape : Shape) (iv : Array IntervalBounds) (bLow bHigh : Nat)
    (x : Vector UInt64 64 × (Nat → List (Int × Int))) (i : Nat) : List (Int × Int × Int) :=
  ((blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh i).filter
    fun b ↦ Id.run (shape.keep cls b)).flatMap (denPoints c d H fl
      (entries.take (blockDecision H s P entries magics cls db shape iv bLow bHigh i).sp3) x)

/-- The invariant of the loop of `Ratpoints.Sieve.sieveRun` over the blocks, whose state is the
correction, the delivery and the store of the tables of rows, from the delivery `r0`: the delivery
is that of the points of the blocks done (`Ratpoints.Sieve.blockPoints`), for every choice of the
words of the classes and the ranges of the numerators of `Ratpoints.Sieve.RunWords`; while the
callback has not stopped the search, the correction is that after the folds of the blocks done in
closed form (`Ratpoints.Sieve.correctionAfter`) and the store fits all the entries; and the callback
has not stopped the search before the loop is done. -/
def SieveRunLoopInvariant (c : List Int) (d H : Nat) (fl : CheckFlags) (s : SieveOptions)
    (P : Params) (entries : List SieveEntry) (magics : Array Nat) (cls : Vector NumClass 64)
    (db : UInt64) (shape : Shape) (iv : Array IntervalBounds) (bLow bHigh : Nat)
    (r0 : Delivery σ) : Std.WP.Invariant Nat (Correction × Delivery σ × RowStore) Prop :=
  fun pref suff st ↦ (∀ x, RunWords cls iv H bLow bHigh x → st.2.1 = r0.deliver process
      (pref.flatMap (blockPoints c d H fl s P entries magics cls db shape iv bLow bHigh x))) ∧
    (st.2.1.quit = false →
      st.1 = correctionAfter H s P entries magics cls db shape iv bLow bHigh pref.length ∧
        st.2.2.Fits entries) ∧
    (suff = [] ∨ st.2.1.quit = false)

section

variable {process} {c : List Int} {d H : Nat} {fl : CheckFlags} {s : SieveOptions} {P : Params}
  {entries : List SieveEntry} {magics : Array Nat} {cls : Vector NumClass 64} {db : UInt64}
  {shape : Shape} {iv : Array IntervalBounds} {bLow bHigh : Nat} {r0 r1 r' : Delivery σ}
  {corr corr' : Correction} {st st' : RowStore} {pref suff : List Nat} {cur n : Nat}
  {b : BlockStat}

theorem sieveRunLoopInvariant_nil (hr : r0.quit = false) (hs : st.Fits entries) (l : List Nat) :
    SieveRunLoopInvariant process c d H fl s P entries magics cls db shape iv bLow bHigh r0 [] l
      (Correction.start P.sp2 P.sp3 P.adaptAt, r0, st) :=
  ⟨fun _ _ ↦ by simp, fun _ ↦ ⟨rfl, hs⟩, .inr hr⟩

/-- What the block at the cursor `cur` needs. -/
theorem SieveRunLoopInvariant.pre (hdec : DecisionWF entries P.sp1 ⟨0, P.sp2, P.sp3⟩)
    (h : SieveRunLoopInvariant process c d H fl s P entries magics cls db shape iv bLow bHigh r0
      pref (cur :: suff) (corr, r1, st)) :
    r1.quit = false ∧ DecisionWF entries P.sp1 corr.decisions[Id.run (findDecision corr.decisions
      cur)]! ∧ st.Fits entries := by
  have hq := h.2.2.resolve_left nofun
  obtain ⟨rfl, hs⟩ := h.2.1 hq
  have hwf := wf_correctionAfter (H := H) (s := s) (magics := magics) (cls := cls) (db := db)
    (shape := shape) (iv := iv) (bLow := bLow) (bHigh := bHigh) hdec pref.length
  exact ⟨hq, decisionWF_getElem!_findDecision hwf.size_pos hwf.block_zero hwf.decisionWF cur, hs⟩

-- The delivery after the block at the cursor `cur`, with the decision of the block.
private theorem deliver_append_blockPoints (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : SieveRunLoopInvariant process c d H fl s P entries magics cls db shape iv bLow bHigh r0
      pref (cur :: suff) (corr, r1, st))
    (hb : ∀ x, RunWords cls iv H bLow bHigh x → r' = r1.deliver process
      (((blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh cur).filter
        fun b ↦ Id.run (shape.keep cls b)).flatMap (denPoints c d H fl
          (entries.take corr.decisions[Id.run (findDecision corr.decisions cur)]!.sp3) x)))
    (x : Vector UInt64 64 × (Nat → List (Int × Int))) (hx : RunWords cls iv H bLow bHigh x) :
    r' = r0.deliver process ((pref ++ [cur]).flatMap
      (blockPoints c d H fl s P entries magics cls db shape iv bLow bHigh x)) := by
  obtain ⟨hd, hc, hq⟩ := h
  dsimp only at hd hc hq
  obtain ⟨rfl, -⟩ := hc (hq.resolve_left nofun)
  rw [hb x hx, hd x hx, List.flatMap_append, Delivery.deliver_append, List.flatMap_singleton,
    ← Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  rfl

/-- The block at the cursor `cur` after which the callback stops the search. -/
theorem SieveRunLoopInvariant.quit (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : SieveRunLoopInvariant process c d H fl s P entries magics cls db shape iv bLow bHigh r0
      pref (cur :: suff) (corr, r1, st))
    (hb : ∀ x, RunWords cls iv H bLow bHigh x → r' = r1.deliver process
      (((blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh cur).filter
        fun b ↦ Id.run (shape.keep cls b)).flatMap (denPoints c d H fl
          (entries.take corr.decisions[Id.run (findDecision corr.decisions cur)]!.sp3) x)))
    (hq : r'.quit = true) :
    SieveRunLoopInvariant process c d H fl s P entries magics cls db shape iv bLow bHigh r0
      (ForIn.toList [:n]) [] (corr', r', st') := by
  refine ⟨fun x hx ↦ ?_, fun h' ↦ absurd (hq.symm.trans h') Bool.true_eq_false.mp, .inl rfl⟩
  have hd := deliver_append_blockPoints hl h hb x hx
  rw [hd]
  exact (Delivery.deliver_flatMap_eq_of_prefix process (l₂ := ForIn.toList [:n])
    ⟨suff, by rw [hl]; simp⟩ _ (hd ▸ hq)).symm

/-- The block at the cursor `cur` after which the callback has not stopped the search. -/
theorem SieveRunLoopInvariant.append (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : SieveRunLoopInvariant process c d H fl s P entries magics cls db shape iv bLow bHigh r0
      pref (cur :: suff) (corr, r1, st))
    (hs : st'.Fits entries)
    (hb : ∀ x, RunWords cls iv H bLow bHigh x → r' = r1.deliver process
      (((blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh cur).filter
        fun b ↦ Id.run (shape.keep cls b)).flatMap (denPoints c d H fl
          (entries.take corr.decisions[Id.run (findDecision corr.decisions cur)]!.sp3) x)))
    (hc : r'.quit = false →
      b = blockReport H P.sp1 entries magics cls db shape iv bLow bHigh corr.decisions cur)
    (hcorr : corr' = Id.run (runFold s P entries.toArray corr b)) (hq : ¬r'.quit = true) :
    SieveRunLoopInvariant process c d H fl s P entries magics cls db shape iv bLow bHigh r0
      (pref ++ [cur]) suff (corr', r', st') := by
  have hq' := Bool.eq_false_iff.mpr hq
  refine ⟨deliver_append_blockPoints hl h hb, fun _ ↦ ⟨?_, hs⟩, .inr hq'⟩
  obtain ⟨rfl, -⟩ := h.2.1 (h.2.2.resolve_left nofun)
  rw [hcorr, hc hq', List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  rfl

/-- At the end of the loop, the points of all the blocks. -/
theorem SieveRunLoopInvariant.post {stt : Correction × Delivery σ × RowStore}
    (h : SieveRunLoopInvariant process c d H fl s P entries magics cls db shape iv bLow bHigh r0
      (ForIn.toList [:n]) [] stt) (x : Vector UInt64 64 × (Nat → List (Int × Int)))
    (hx : RunWords cls iv H bLow bHigh x) :
    stt.2.1 = r0.deliver process ((List.range n).flatMap
      (blockPoints c d H fl s P entries magics cls db shape iv bLow bHigh x)) := by
  rw [List.range_eq_range']
  simpa using h.1 x hx

end

attribute [local irreducible] SieveRunLoopInvariant in
open Std.WP Lean.Order in
/-- The contract of the run over the blocks with the correction of the moduli, the block lemma: for
sieve entries with the tables of inverses of their factors, prime entries wherever no factor is
counted, the reciprocals of their moduli, the row offsets of the packings of the classes `cls` with
a pattern, whose bits are those of the word `db`, a well-formed decision of the choice
(`Ratpoints.Sieve.DecisionWF`), forbidden divisors of the word shape that have what its loop needs,
pieces of at least one bit array, the denominators from `bLow ≥ 1` to `bHigh < 2 ^ 63` and the
height below `2 ^ 63`, the run, with a delivery whose flag of the stop is clear and a store of the
tables of rows that fits all the entries, delivers the points of its blocks in order
(`Ratpoints.Sieve.blockPoints`), each a function of the block and of its decision
(`Ratpoints.Sieve.blockDecision`), which depends neither on the callback nor on the flags of the
output, for every choice of the words of the classes and the ranges of the numerators of
`Ratpoints.Sieve.RunWords`. -/
theorem sieveRun_spec (c : List Int) (d H A : Nat) (fl : CheckFlags) (s : SieveOptions)
    (P : Params) (entries : List SieveEntry) (magics : Array Nat) (cls : Vector NumClass 64)
    (offsets : Array Nat) (db : UInt64) (shape : Shape) (iv : Array IntervalBounds)
    (bLow bHigh : Nat) (store : RowStore) (r : Delivery σ) (hA : 1 ≤ A)
    (hent : ∀ e ∈ entries, (e.nf = 0 → e.IsPrimeEntry) ∧ ∀ f ∈ e.factors, f.HasInverses e.p)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p) (hoff : OffsetsFor cls entries offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0))
    (hdec : DecisionWF entries P.sp1 ⟨0, P.sp2, P.sp3⟩) (hforb : shape.ForbFits) (hbLow : 1 ≤ bLow)
    (hbHigh : bHigh < 2 ^ 63) (hH : H < 2 ^ 63) :
    ⦃ r.quit = false ∧ store.Fits entries ⦄
    sieveRun process c d H A fl s P entries magics cls offsets db shape iv bLow bHigh store r
    ⦃ fun res ↦ ∀ x, RunWords cls iv H bLow bHigh x → res.1 = r.deliver process
        ((List.range (Id.run (shape.blockPlan bLow bHigh)).nblocks).flatMap
          (blockPoints c d H fl s P entries magics cls db shape iv bLow bHigh x)) ⦄ := by
  vcgen [sieveRun, blockPlan_value, runFold_value] invariants
  | inv1 => SieveRunLoopInvariant process c d H fl s P entries magics cls db shape iv bLow bHigh r
  all_goals subst plan
  all_goals try dsimp only at *
  all_goals first
    | exact sieveRunLoopInvariant_nil ‹_ ∧ _›.1 ‹_ ∧ _›.2 _
    | exact SieveRunLoopInvariant.post ‹_› _ ‹_›
    | (obtain ⟨hq, hd, hs⟩ := SieveRunLoopInvariant.pre hdec ‹_›
       exact ⟨hq, hA, hent, hmg, hoff, hdb, hd, rfl, hforb,
         Std.Legacy.Range.lt_of_toList_eq_append_cons ‹_›, hbLow, hbHigh, hH, hs⟩)
    | (obtain ⟨hs, hb, hc⟩ := ‹RowStore.Fits _ _ ∧ _›
       first
         | exact SieveRunLoopInvariant.quit ‹_› ‹_› hb ‹_›
         | exact SieveRunLoopInvariant.append ‹_› ‹_› hs hb hc ‹_› ‹_›)

/-- `Ratpoints.Sieve.sieveRun_spec` as a plain statement. -/
theorem fst_run_sieveRun (c : List Int) (d H A : Nat) (fl : CheckFlags) (s : SieveOptions)
    (P : Params) (entries : List SieveEntry) (magics : Array Nat) (cls : Vector NumClass 64)
    (offsets : Array Nat) (db : UInt64) (shape : Shape) (iv : Array IntervalBounds)
    (bLow bHigh : Nat) (store : RowStore) {r : Delivery σ} (hA : 1 ≤ A)
    (hent : ∀ e ∈ entries, (e.nf = 0 → e.IsPrimeEntry) ∧ ∀ f ∈ e.factors, f.HasInverses e.p)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p) (hoff : OffsetsFor cls entries offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0))
    (hdec : DecisionWF entries P.sp1 ⟨0, P.sp2, P.sp3⟩) (hforb : shape.ForbFits) (hbLow : 1 ≤ bLow)
    (hbHigh : bHigh < 2 ^ 63) (hH : H < 2 ^ 63) (hr : r.quit = false) (hs : store.Fits entries)
    {x : Vector UInt64 64 × (Nat → List (Int × Int))} (hx : RunWords cls iv H bLow bHigh x) :
    (Id.run (sieveRun process c d H A fl s P entries magics cls offsets db shape iv bLow bHigh
      store r)).1 = r.deliver process
        ((List.range (Id.run (shape.blockPlan bLow bHigh)).nblocks).flatMap
          (blockPoints c d H fl s P entries magics cls db shape iv bLow bHigh x)) :=
  (sieveRun_spec process c d H A fl s P entries magics cls offsets db shape iv bLow bHigh store r hA
    hent hmg hoff hdb hdec hforb hbLow hbHigh hH).le_wp ⟨hr, hs⟩ x hx

/-- The contract of the run over the blocks with the correction of the moduli, per denominator: for
sieve entries with the tables of inverses of their factors, prime entries wherever no factor is
counted, the row offsets of the packings of the classes `cls` with a pattern
(`Ratpoints.Sieve.OffsetsFor`), whose bits are those of the word `db`, the reciprocals of the moduli
in their order, a store of the tables of rows that fits all the entries, a first decision of the
parameters that is well-formed (`Ratpoints.Sieve.DecisionWF`), forbidden divisors of the word shape
that have what its loop needs (`Ratpoints.Sieve.Shape.ForbFits`), a listing of the shape with no
denominator twice, so that each lies in one block (`Ratpoints.Sieve.Shape.eq_of_mem_blockDens`),
pieces of at least one bit array, the denominators from `bLow ≥ 1` to `bHigh < 2 ^ 63` and the
height below `2 ^ 63`, there is a number `sp3At b` of the entries of the first three stages for each
denominator `b`, the end of the third stage of the decision of its block
(`Ratpoints.Sieve.blockDecision`), which depends neither on the callback nor on the flags of the
output, such that the run, with any callback, flags and delivery whose flag of the stop is clear,
delivers for each denominator `b` of the listing of the shape that passes its tests
(`Ratpoints.Sieve.Shape.dens`, `Ratpoints.Sieve.Shape.keep`), in order, the points of the check with
the flags of the numerators `-H, …, H` in one of the ranges `rs b` that the bounds of the search
intervals give for `b` (`Ratpoints.Sieve.RangesFor`), that pass the class word `nb[b mod 64]` for
words `nb` that the classes pack, and survive the first `sp3At b` entries: the blocks in order
(`Ratpoints.Sieve.sieveRun_spec`) visit the denominators of the listing in its order
(`Ratpoints.Sieve.Shape.flatMap_filter_blockDens`). -/
theorem exists_run_sieveRun_eq_deliver (c : List ℤ) (d H A : ℕ) (s : SieveOptions) (P : Params)
    (entries : List SieveEntry) (magics : Array ℕ) (cls : Vector NumClass 64) (offsets : Array ℕ)
    (db : UInt64) (shape : Shape) (iv : Array IntervalBounds) (bLow bHigh : ℕ) (store : RowStore)
    (hA : 1 ≤ A)
    (hent : ∀ e ∈ entries, (e.nf = 0 → e.IsPrimeEntry) ∧ ∀ f ∈ e.factors, f.HasInverses e.p)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p) (hoff : OffsetsFor cls entries offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0))
    (hdec : DecisionWF entries P.sp1 ⟨0, P.sp2, P.sp3⟩) (hforb : shape.ForbFits)
    (hnd : (Id.run (shape.dens db bLow bHigh)).Nodup) (hbLow : 1 ≤ bLow)
    (hbHigh : bHigh < 2 ^ 63) (hH : H < 2 ^ 63) (hs : store.Fits entries) :
    ∃ sp3At : ℕ → ℕ, ∀ {σ : Type} (process : ℤ → ℤ → ℤ → σ → Answer σ) (fl : CheckFlags)
      (r : Delivery σ), r.quit = false → ∀ (nb : Vector UInt64 64) (rs : ℕ → List (ℤ × ℤ)),
      (∀ b < 64, cls[b]!.Packs nb[b]!) → (∀ b, bLow ≤ b → b ≤ bHigh → RangesFor iv b H (rs b)) →
      (Id.run (sieveRun process c d H A fl s P entries magics cls offsets db shape iv bLow bHigh
        store r)).1 = r.deliver process (((Id.run (shape.dens db bLow bHigh)).filter
          fun b ↦ Id.run (shape.keep cls b)).flatMap fun b : ℕ ↦ ((numerators H).filter
            fun a ↦ inRanges (rs b) a && classBit nb[b % 64]! a &&
              survives (entries.take (sp3At b)) b a).flatMap
                (checkNumWith (scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl)) := by
  classical
  refine ⟨fun b ↦ if h : ∃ i < (Id.run (shape.blockPlan bLow bHigh)).nblocks,
      b ∈ blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh i then
      (blockDecision H s P entries magics cls db shape iv bLow bHigh h.choose).sp3 else 0,
    fun process fl r hr nb rs hnb hrs ↦ ?_⟩
  rw [fst_run_sieveRun process c d H A fl s P entries magics cls offsets db shape iv bLow bHigh
    store hA hent hmg hoff hdb hdec hforb hbLow hbHigh hH hr hs (x := (nb, rs)) ⟨hnb, hrs⟩]
  refine congrArg (r.deliver process) (shape.flatMap_filter_blockDens db cls bLow bHigh
    fun i hi b hb ↦ ?_)
  have h : ∃ i < (Id.run (shape.blockPlan bLow bHigh)).nblocks,
      b ∈ blockDens shape db (Id.run (shape.blockPlan bLow bHigh)) bLow bHigh i := ⟨i, hi, hb⟩
  dsimp only
  rw [dite_eq_left h, Shape.eq_of_mem_blockDens hnd h.choose_spec.1 hi
    h.choose_spec.2 hb]
  rfl

/-! ### The threads -/

/-- The calling thread of a run whose blocks are sifted by threads, which the model leaves out with
the threads: the slots `slot i` of the blocks `i < n`, the points that each block delivered to the
appending callback (`Ratpoints.appendPoint`), delivered to the callback `process` on the delivery
`r` in the order of the blocks, the loop ending when the callback has stopped the search. -/
def deliverSlots (slot : Nat → Array (Int × Int × Int)) (n : Nat) (r : Delivery σ) :
    Id (Delivery σ) := do
  let mut r := r
  for i in [0:n] do
    r := r.deliver process (slot i).toList
    if r.quit then break
  return r

/-- The invariant of the loop of `Ratpoints.Sieve.deliverSlots`, whose state is the delivery, from
the delivery `r0`: that of the points of the slots done, and the callback has not stopped the search
before the loop is done. -/
def DeliverSlotsInvariant (slot : Nat → Array (Int × Int × Int)) (r0 : Delivery σ) :
    Std.WP.Invariant Nat (Delivery σ) Prop :=
  fun pref suff r ↦ r = r0.deliver process (pref.flatMap fun i ↦ (slot i).toList) ∧
    (suff = [] ∨ r.quit = false)

section

variable {process} {slot : Nat → Array (Int × Int × Int)} {r0 r : Delivery σ} {n cur : Nat}
  {pref suff : List Nat}

/-- The slot at the cursor `cur` after which the callback stops the search. -/
theorem DeliverSlotsInvariant.quit (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : r = r0.deliver process (pref.flatMap fun i ↦ (slot i).toList) ∧
      (cur :: suff = [] ∨ r.quit = false))
    (hq : (r.deliver process (slot cur).toList).quit = true) :
    r.deliver process (slot cur).toList =
        r0.deliver process ((ForIn.toList [:n]).flatMap fun i ↦ (slot i).toList) ∧
      (True ∨ (r.deliver process (slot cur).toList).quit = false) := by
  obtain ⟨rfl, -⟩ := h
  refine ⟨?_, .inl trivial⟩
  rw [← Delivery.deliver_append, ← List.flatMap_singleton (fun i ↦ (slot i).toList) cur,
    ← List.flatMap_append] at hq ⊢
  exact (Delivery.deliver_flatMap_eq_of_prefix process (l₂ := ForIn.toList [:n])
    ⟨suff, by rw [hl]; simp⟩ _ hq).symm

/-- The slot at the cursor `cur` after which the callback has not stopped the search. -/
theorem DeliverSlotsInvariant.append
    (h : r = r0.deliver process (pref.flatMap fun i ↦ (slot i).toList) ∧
      (cur :: suff = [] ∨ r.quit = false))
    (hq : ¬(r.deliver process (slot cur).toList).quit = true) :
    r.deliver process (slot cur).toList =
        r0.deliver process ((pref ++ [cur]).flatMap fun i ↦ (slot i).toList) ∧
      (suff = [] ∨ (r.deliver process (slot cur).toList).quit = false) := by
  obtain ⟨rfl, -⟩ := h
  refine ⟨?_, .inr (Bool.eq_false_iff.mpr hq)⟩
  rw [List.flatMap_append, Delivery.deliver_append, List.flatMap_singleton]

end

open Std.WP Lean.Order in
/-- The calling thread delivers the points of the slots in the order of the blocks. -/
theorem deliverSlots_spec (slot : Nat → Array (Int × Int × Int)) (n : Nat) (r : Delivery σ) :
    ⦃ r.quit = false ⦄ deliverSlots process slot n r
    ⦃ fun r' ↦ r' = r.deliver process ((List.range n).flatMap fun i ↦ (slot i).toList) ⦄ := by
  vcgen [deliverSlots] invariants
  | inv1 => DeliverSlotsInvariant process slot r
  all_goals simp only [DeliverSlotsInvariant] at *
  all_goals first
    | exact ⟨(Delivery.deliver_nil process r).symm, .inr ‹_›⟩
    | exact DeliverSlotsInvariant.quit ‹_› ‹_› ‹_›
    | exact DeliverSlotsInvariant.append ‹_› ‹_›
    | (rename_i h
       rw [List.range_eq_range']
       simpa using h.1)

/-- Block `i` of the run, sifted with the decisions after the folds of the first `k` blocks, for
`k ≥ i - Ratpoints.adaptLag`, with a store of its own that fits all the entries, delivers to the
appending callback (`Ratpoints.appendPoint`) from an empty array the points of the block with its
decision (`Ratpoints.Sieve.blockPoints`): the contract of one block
(`Ratpoints.Sieve.runBlock_spec`) and the lag of the correction
(`Ratpoints.Sieve.getElem!_findDecision_correctionAfter`). The pool of threads of the C code meets
these hypotheses: it starts block `i` only once the blocks before block `i - RP_ADAPT_LAG` are
folded (`find_points.c:4292-4296`), and the tables of rows that its threads share only gain complete
rows (`init.c:180`, `init.c:241`, `init.c:391`, `init.c:443`). -/
theorem toList_info_run_runBlock_appendPoint (c : List Int) (d H A : Nat) (fl : CheckFlags)
    (s : SieveOptions) (P : Params) (entries : List SieveEntry) (magics : Array Nat)
    (cls : Vector NumClass 64) (offsets : Array Nat) (db : UInt64) (shape : Shape)
    (iv : Array IntervalBounds) (bLow bHigh : Nat) {i k : Nat} {store : RowStore} (hA : 1 ≤ A)
    (hent : ∀ e ∈ entries, (e.nf = 0 → e.IsPrimeEntry) ∧ ∀ f ∈ e.factors, f.HasInverses e.p)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p) (hoff : OffsetsFor cls entries offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0))
    (hdec : DecisionWF entries P.sp1 ⟨0, P.sp2, P.sp3⟩) (hforb : shape.ForbFits) (hbLow : 1 ≤ bLow)
    (hbHigh : bHigh < 2 ^ 63) (hH : H < 2 ^ 63) (hk : i - adaptLag ≤ k)
    (hi : i < (Id.run (shape.blockPlan bLow bHigh)).nblocks) (hs : store.Fits entries)
    {x : Vector UInt64 64 × (Nat → List (Int × Int))} (hx : RunWords cls iv H bLow bHigh x) :
    (Id.run (runBlock appendPoint c d H A fl P.sp1 entries magics cls offsets db shape iv bLow
      bHigh (Id.run (shape.blockPlan bLow bHigh))
      (correctionAfter H s P entries magics cls db shape iv bLow bHigh k).decisions i store
      ⟨#[], 0, false⟩)).1.info.toList =
      blockPoints c d H fl s P entries magics cls db shape iv bLow bHigh x i := by
  have hwf := wf_correctionAfter (H := H) (s := s) (magics := magics) (cls := cls) (db := db)
    (shape := shape) (iv := iv) (bLow := bLow) (bHigh := bHigh) hdec k
  have h := Std.WP.Id.of_run_eq_wp rfl _ ((runBlock_spec appendPoint c d H A fl P.sp1 entries
    magics cls offsets db shape iv bLow bHigh _ _ i store ⟨#[], 0, false⟩).le_wp ⟨rfl, hA, hent,
      hmg, hoff, hdb, decisionWF_getElem!_findDecision hwf.size_pos hwf.block_zero hwf.decisionWF i,
      rfl, hforb, hi, hbLow, hbHigh, hH, hs⟩)
  rw [h.2.1 x hx, Delivery.deliver_appendPoint, getElem!_findDecision_correctionAfter hk]
  simp [blockPoints]

/-- The threads preserve the output of the run: the blocks of the run, each sifted with the
decisions after the folds of the first `k i ≥ i - Ratpoints.adaptLag` blocks and a store of its own
that fits all the entries, into a slot by the appending callback, their slots delivered in the order
of the blocks by the calling thread (`Ratpoints.Sieve.deliverSlots`), give what the run on the
calling thread gives (`Ratpoints.Sieve.sieveRun`), for the hypotheses of
`Ratpoints.Sieve.sieveRun_spec` and words of the classes and ranges of the numerators of
`Ratpoints.Sieve.RunWords`. The pool of threads of the C code meets these hypotheses: a thread
starts block `i` only once the blocks before block `i - RP_ADAPT_LAG` are folded
(`find_points.c:4292-4296`), and the tables of rows that the threads share only gain complete rows,
published once built (`init.c:180`, `init.c:241`, `init.c:391`, `init.c:443`), so that they fit all
the entries whenever a thread reads them (`find_points.c:3160`, `find_points.c:3533-3535`). -/
theorem run_deliverSlots_eq_fst_run_sieveRun (c : List Int) (d H A : Nat) (fl : CheckFlags)
    (s : SieveOptions) (P : Params) (entries : List SieveEntry) (magics : Array Nat)
    (cls : Vector NumClass 64) (offsets : Array Nat) (db : UInt64) (shape : Shape)
    (iv : Array IntervalBounds) (bLow bHigh : Nat) {store : RowStore} {r : Delivery σ}
    {k : Nat → Nat} {stores : Nat → RowStore} (hA : 1 ≤ A)
    (hent : ∀ e ∈ entries, (e.nf = 0 → e.IsPrimeEntry) ∧ ∀ f ∈ e.factors, f.HasInverses e.p)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p) (hoff : OffsetsFor cls entries offsets)
    (hdb : ∀ j < 64, db.toBitVec.getLsbD j = (cls[j]!.bits != 0))
    (hdec : DecisionWF entries P.sp1 ⟨0, P.sp2, P.sp3⟩) (hforb : shape.ForbFits) (hbLow : 1 ≤ bLow)
    (hbHigh : bHigh < 2 ^ 63) (hH : H < 2 ^ 63) (hk : ∀ i, i - adaptLag ≤ k i)
    (hst : ∀ i, (stores i).Fits entries) (hr : r.quit = false) (hs : store.Fits entries)
    {x : Vector UInt64 64 × (Nat → List (Int × Int))} (hx : RunWords cls iv H bLow bHigh x) :
    Id.run (deliverSlots process (fun i ↦ (Id.run (runBlock appendPoint c d H A fl P.sp1 entries
      magics cls offsets db shape iv bLow bHigh (Id.run (shape.blockPlan bLow bHigh))
      (correctionAfter H s P entries magics cls db shape iv bLow bHigh (k i)).decisions i
      (stores i) ⟨#[], 0, false⟩)).1.info) (Id.run (shape.blockPlan bLow bHigh)).nblocks r) =
      (Id.run (sieveRun process c d H A fl s P entries magics cls offsets db shape iv bLow bHigh
        store r)).1 := by
  rw [fst_run_sieveRun process c d H A fl s P entries magics cls offsets db shape iv bLow bHigh
    store hA hent hmg hoff hdb hdec hforb hbLow hbHigh hH hr hs hx,
    (deliverSlots_spec process _ _ r).le_wp hr]
  exact congrArg (r.deliver process) (List.flatMap_congr fun i hi ↦
    toList_info_run_runBlock_appendPoint c d H A fl s P entries magics cls offsets db shape iv bLow
      bHigh hA hent hmg hoff hdb hdec hforb hbLow hbHigh hH (hk i) (List.mem_range.mp hi) (hst i)
      hx)

end Sieve

end Ratpoints

end
