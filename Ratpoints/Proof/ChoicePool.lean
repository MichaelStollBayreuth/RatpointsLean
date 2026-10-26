/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Choice
public import Std.WP

import Ratpoints.Proof.Containers
import Std.Tactic.Do

/-!
# The pool of the candidate moduli

The contracts of the stages of the choice of the moduli on the pool of the candidates
(`Ratpoints.ModulusCandidate`), for every property of the candidates that the stages keep
(`Ratpoints.AllQ`): the stages drop candidates (`Ratpoints.dropUsed`, `Ratpoints.takeEntries`,
`Ratpoints.dropComposites`), sort them (`Ratpoints.sortFrom`) and key them again
(`Ratpoints.rankSecond`), and leave the cut points within the pool, with only primes that say more
than coprimality from the end of the second stage on (`Ratpoints.TailNf`); for any values of the
doubles of the cost model, which no contract reads.

## Main definitions

* `Ratpoints.AllQ`: every candidate of the pool has a property.
* `Ratpoints.TailNf`: the candidates from a position on count no factors.

## Main statements

* `Ratpoints.takeEntries_spec`, `Ratpoints.dropComposites_spec`, `Ratpoints.bestByR_spec`: the
  contracts of the loops on the pool.
* `Ratpoints.firstStages_spec`, `Ratpoints.firstStages_run`: the first two stages.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

open Sieve

/-! ### Options -/

theorem _root_.Option.eq_none_of_forall_prod4 {α β γ δ : Type _} {x : Option (α × β × γ × δ)}
    (h : ∀ a b c d, x = some (a, b, c, d) → False) : x = none :=
  Option.eq_none_iff_forall_ne_some.mpr fun ⟨a, b, c, d⟩ h' ↦ h a b c d h'

/-! ### The pool -/

/-- Every candidate of the pool `pool` has the property `Q`. -/
def AllQ (Q : ModulusCandidate → Prop) (pool : Array ModulusCandidate) : Prop :=
  ∀ e ∈ pool, Q e

theorem AllQ.eraseIdxIfInBounds {Q : ModulusCandidate → Prop} {pool : Array ModulusCandidate}
    (h : AllQ Q pool) (n : Nat) : AllQ Q (pool.eraseIdxIfInBounds n) := fun e he ↦
  h e (by
    rw [Array.eraseIdxIfInBounds_eq] at he
    split at he
    · exact Array.mem_of_mem_eraseIdx he
    · exact he)

theorem AllQ.push {Q : ModulusCandidate → Prop} {pool : Array ModulusCandidate} (h : AllQ Q pool)
    {e : ModulusCandidate} (he : Q e) : AllQ Q (pool.push e) :=
  Array.forall_mem_push.mpr ⟨he, h⟩

-- The rule of the first stage, as a value: no contract reads it.
private theorem phase1Wants_true (pool : Array ModulusCandidate) (n pnp taken : Nat)
    (bpw rate target : Float) (extra : Nat) :
    ⦃ True ⦄ phase1Wants pool n pnp taken bpw rate target extra ⦃ fun _ ↦ True ⦄ :=
  ⟨fun _ ↦ trivial⟩

/-- The invariant of the loop of `Ratpoints.dropUsed`. -/
def DropUsedInvariant (Q : ModulusCandidate → Prop) (start : Nat) :
    Std.WP.WhileInvariant (Array ModulusCandidate × Nat) Prop :=
  .mk fun _ st ↦ AllQ Q st.1 ∧ start ≤ st.2 ∧ st.2 ≤ st.1.size

open Std.WP Std.WP.Assertion Lean.Order in
/-- The contract of `Ratpoints.dropUsed`: it keeps a property `Q` of the candidates and the position
`start` within the pool, since it only drops candidates from `start` on. -/
theorem dropUsed_spec (Q : ModulusCandidate → Prop) (pool : Array ModulusCandidate) (start : Nat)
    (used : UInt64) :
    ⦃ AllQ Q pool ∧ start ≤ pool.size ⦄ dropUsed pool start used
    ⦃ fun r ↦ AllQ Q r ∧ start ≤ r.size ⦄ := by
  vcgen [dropUsed] invariants
  | inv1 => DropUsedInvariant Q start
  | inv2 => .ofMeasure fun st : Array ModulusCandidate × Nat ↦ st.1.size + (st.1.size - st.2)
  all_goals simp only [Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat,
    NondetFun.evalsTo_pure, meet_prop_eq_and, ofProp_prop_eq, DropUsedInvariant,
    WhileInvariant.mk] at *
  all_goals grind [AllQ.eraseIdxIfInBounds, Array.size_eraseIdxIfInBounds_of_lt]

/-- The invariant of the loop of `Ratpoints.takeEntries`. -/
def TakeEntriesInvariant (Q : ModulusCandidate → Prop) (start : Nat) :
    Std.WP.WhileInvariant (Array ModulusCandidate × UInt64 × Float × Nat × Nat) Prop :=
  .mk fun _ st ↦ AllQ Q st.1 ∧ st.2.2.2.1 = start + st.2.2.2.2 ∧ st.2.2.2.1 ≤ st.1.size

open Std.WP Std.WP.Assertion Lean.Order in
/-- The contract of `Ratpoints.takeEntries`, for any values of the doubles and any rule of the first
stage: it keeps a property `Q` of the candidates, since it only drops candidates, and the candidates
taken from `start` on lie within the pool. -/
theorem takeEntries_spec (Q : ModulusCandidate → Prop) (pool : Array ModulusCandidate)
    (start : Nat) (used : UInt64) (want : Int) (rate bpw target : Float) (extra : Nat) :
    ⦃ AllQ Q pool ∧ start ≤ pool.size ⦄ takeEntries pool start used want rate bpw target extra
    ⦃ fun r ↦ AllQ Q r.1 ∧ start + r.2.2.2 ≤ r.1.size ⦄ := by
  vcgen [takeEntries, dropUsed_spec Q, phase1Wants_true] invariants
  | inv1 => TakeEntriesInvariant Q start
  | inv2 => .ofMeasure fun st : Array ModulusCandidate × UInt64 × Float × Nat × Nat ↦
      st.1.size + (st.1.size - st.2.2.2.1)
  all_goals simp only [Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat,
    NondetFun.evalsTo_pure, meet_prop_eq_and, ofProp_prop_eq, TakeEntriesInvariant,
    WhileInvariant.mk] at *
  all_goals grind [AllQ.eraseIdxIfInBounds, Array.size_eraseIdxIfInBounds_of_lt]

/-- The candidates of the pool `pool` from the position `s` on have no factors counted: primes that
say more than coprimality. -/
def TailNf (pool : Array ModulusCandidate) (s : Nat) : Prop :=
  ∀ i (h : i < pool.size), s ≤ i → pool[i].nf = 0

/-- The invariant of the loop of `Ratpoints.dropComposites`. -/
def DropCompositesInvariant (Q : ModulusCandidate → Prop) (start : Nat) :
    Std.WP.WhileInvariant (Array ModulusCandidate × Nat) Prop :=
  .mk fun exit st ↦ AllQ Q st.1 ∧ start ≤ st.2 ∧ st.2 ≤ st.1.size ∧
    (∀ i (h : i < st.1.size), start ≤ i → i < st.2 → st.1[i].nf = 0) ∧
    (exit = true → st.1.size ≤ st.2)

open Std.WP Std.WP.Assertion Lean.Order in
/-- The contract of `Ratpoints.dropComposites`: it keeps a property `Q` of the candidates and the
position `start` within the pool, and the candidates from `start` on count no factors
(`Ratpoints.TailNf`). -/
theorem dropComposites_spec (Q : ModulusCandidate → Prop) (pool : Array ModulusCandidate)
    (start : Nat) :
    ⦃ AllQ Q pool ∧ start ≤ pool.size ⦄ dropComposites pool start
    ⦃ fun r ↦ AllQ Q r ∧ start ≤ r.size ∧ TailNf r start ⦄ := by
  vcgen [dropComposites] invariants
  | inv1 => DropCompositesInvariant Q start
  | inv2 => .ofMeasure fun st : Array ModulusCandidate × Nat ↦ st.1.size + (st.1.size - st.2)
  all_goals simp only [Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat,
    NondetFun.evalsTo_pure, meet_prop_eq_and, ofProp_prop_eq, DropCompositesInvariant,
    WhileInvariant.mk, TailNf] at *
  all_goals grind [AllQ.eraseIdxIfInBounds, Array.size_eraseIdxIfInBounds_of_lt,
    Array.getElem_eraseIdxIfInBounds_of_lt]

/-- The contract of `Ratpoints.bestByR`: the position it returns is that of a candidate from `sp3`
on. -/
theorem bestByR_spec (pool : Array ModulusCandidate) (sp3 : Nat) :
    ⦃ True ⦄ bestByR pool sp3
    ⦃ fun r ↦ ∀ b, r = some b → sp3 ≤ b ∧ b < pool.size ⦄ := by
  vcgen [bestByR] invariants
  | inv1 => fun _ _ best ↦ sp3 ≤ best ∧ best < pool.size
  all_goals grind

theorem AllQ.sortFrom {Q : ModulusCandidate → Prop} {pool : Array ModulusCandidate}
    (h : AllQ Q pool) (s : Nat) (le : ModulusCandidate → ModulusCandidate → Bool) :
    AllQ Q (sortFrom pool s le) := fun e he ↦ by
  simp only [Ratpoints.sortFrom, Array.mem_append, List.mem_toArray, List.mem_mergeSort,
    Array.mem_toList_iff] at he
  rcases he with he | he <;>
    exact h e (by
      obtain ⟨i, hi, rfl⟩ := Array.mem_extract_iff_getElem.mp he
      exact Array.getElem_mem ..)

theorem size_sortFrom {pool : Array ModulusCandidate} {s : Nat} (hs : s ≤ pool.size)
    (le : ModulusCandidate → ModulusCandidate → Bool) : (sortFrom pool s le).size = pool.size := by
  simp only [Ratpoints.sortFrom, Array.size_append, Array.size_extract, List.size_toArray,
    List.length_mergeSort, Array.length_toList]
  lia

theorem AllQ.mapIdx_key {Q : ModulusCandidate → Prop} (hQ : ∀ e, Q e → ∀ k, Q { e with key := k })
    {pool : Array ModulusCandidate} (h : AllQ Q pool) (key : Nat → ModulusCandidate → Float)
    (s : Nat) :
    AllQ Q (pool.mapIdx fun n e ↦ if s ≤ n then { e with key := key n e } else e) := fun e he ↦ by
  obtain ⟨i, hi, rfl⟩ := Array.mem_mapIdx.mp he
  split
  · exact hQ _ (h _ (Array.getElem_mem hi)) _
  · exact h _ (Array.getElem_mem hi)

theorem AllQ.rankSecond {Q : ModulusCandidate → Prop}
    (hQ : ∀ e, Q e → ∀ k, Q { e with key := k }) {pool : Array ModulusCandidate}
    (h : AllQ Q pool) (sp1 : Nat) (rate bpws ct U D : Float) :
    AllQ Q (Ratpoints.rankSecond pool sp1 rate bpws ct U D).1 := by
  simp only [Ratpoints.rankSecond]
  split
  · exact (h.mapIdx_key hQ _ sp1).sortFrom _ _
  · exact h

theorem size_rankSecond (pool : Array ModulusCandidate) (sp1 : Nat) (rate bpws ct U D : Float) :
    (rankSecond pool sp1 rate bpws ct U D).1.size = pool.size := by
  simp only [rankSecond]
  split
  · rw [size_sortFrom (by simp; lia), Array.size_mapIdx]
  · rfl

/-- The first two stages keep the property `Q` of the candidates, which reads no key, and leave the
cut points `sp1 ≤ sp2` within the pool, with only primes that say more than coprimality from `sp2`
on. -/
theorem firstStages_spec (Q : ModulusCandidate → Prop) (hQ : ∀ e, Q e → ∀ k, Q { e with key := k })
    (pool : Array ModulusCandidate) (s : SieveOptions) (target ct : Float) (est : RunEstimate)
    (bpws : Float) (sp2e : Nat) :
    ⦃ AllQ Q pool ⦄ firstStages pool s target ct est bpws sp2e
    ⦃ fun r ↦ AllQ Q r.1 ∧ TailNf r.1 r.2.2 ∧ r.2.1 ≤ r.2.2 ∧ r.2.2 ≤ r.1.size ⦄ := by
  vcgen [firstStages, takeEntries_spec Q, dropComposites_spec Q]
  · exact ⟨‹_›, Nat.zero_le _⟩
  · obtain ⟨h, hs⟩ := ‹AllQ Q _ ∧ 0 + _ ≤ _›
    exact ⟨h.rankSecond hQ _ _ _ _ _ _, by rw [size_rankSecond]; lia⟩
  · exact ‹_›
  · obtain ⟨h, hs, ht⟩ := ‹AllQ Q _ ∧ _ ∧ TailNf _ _›
    exact ⟨h, ht, Nat.le_add_right _ _, hs⟩

theorem getElem_sortFrom_of_lt {pool : Array ModulusCandidate} {s : Nat} (hs : s ≤ pool.size)
    (le : ModulusCandidate → ModulusCandidate → Bool) {n : Nat} (hn : n < s) :
    (sortFrom pool s le)[n]'(by rw [size_sortFrom hs]; lia) = pool[n] := by
  simp only [sortFrom]
  rw [Array.getElem_append_left (by simp; lia), Array.getElem_extract]
  simp

theorem exists_getElem_sortFrom_eq {pool : Array ModulusCandidate} {s : Nat}
    (le : ModulusCandidate → ModulusCandidate → Bool) {n : Nat} (hsn : s ≤ n)
    (hn : n < (sortFrom pool s le).size) :
    ∃ k, ∃ (hk : k < pool.size), s ≤ k ∧ (sortFrom pool s le)[n] = pool[k] := by
  have hm : (sortFrom pool s le)[n] ∈ (pool.extract s pool.size).toList.mergeSort le := by
    simp only [sortFrom] at hn ⊢
    rw [Array.getElem_append_right (by simp; lia)]
    exact List.getElem_mem ..
  obtain ⟨i, hi, he⟩ := Array.mem_extract_iff_getElem.mp
    (Array.mem_toList_iff.mp (List.mem_mergeSort.mp hm))
  exact ⟨s + i, by simp at hi; lia, Nat.le_add_right _ _, he.symm⟩

/-- `Ratpoints.firstStages_spec` for the result of the first two stages. -/
theorem firstStages_run {Q : ModulusCandidate → Prop}
    (hQ : ∀ e, Q e → ∀ k, Q { e with key := k }) {pool : Array ModulusCandidate}
    (h : AllQ Q pool) (s : SieveOptions) (target ct : Float) (est : RunEstimate) (bpws : Float)
    (sp2e : Nat) :
    AllQ Q (Id.run (firstStages pool s target ct est bpws sp2e)).1 ∧
      TailNf (Id.run (firstStages pool s target ct est bpws sp2e)).1
        (Id.run (firstStages pool s target ct est bpws sp2e)).2.2 ∧
      (Id.run (firstStages pool s target ct est bpws sp2e)).2.1 ≤
        (Id.run (firstStages pool s target ct est bpws sp2e)).2.2 ∧
      (Id.run (firstStages pool s target ct est bpws sp2e)).2.2 ≤
        (Id.run (firstStages pool s target ct est bpws sp2e)).1.size :=
  Std.WP.Id.of_run_eq_wp rfl _ ((firstStages_spec Q hQ pool s target ct est bpws sp2e).le_wp h)

/-- The sieve entries of an array of candidates each with its sieve entry (`(·.ssp)`) with a
property at its position: one for each candidate, each with the property at its position. -/
theorem length_filterMap_ssp_and_forall {pool : Array ModulusCandidate}
    {P : Nat → SieveEntry → Prop}
    (h : ∀ n (hn : n < pool.size), ∃ se, pool[n].ssp = some se ∧ P n se) :
    (pool.toList.filterMap (·.ssp)).length = pool.size ∧
      ∀ n (hn : n < (pool.toList.filterMap (·.ssp)).length),
        P n (pool.toList.filterMap (·.ssp))[n] := by
  have hsome (e : ModulusCandidate) (he : e ∈ pool.toList) : e.ssp.isSome := by
    obtain ⟨n, hn, rfl⟩ := List.getElem_of_mem he
    obtain ⟨se, hs, -⟩ := h n (by simpa using hn)
    simp [hs]
  have hm := List.map_some_filterMap_of_forall_isSome hsome
  have hl : (pool.toList.filterMap (·.ssp)).length = pool.size :=
    (List.filterMap_length_eq_length.mpr hsome).trans Array.length_toList
  refine ⟨hl, fun n hn ↦ ?_⟩
  obtain ⟨se, hs, hp⟩ := h n (hl ▸ hn)
  have := congrArg (·[n]?) hm
  simp only [List.getElem?_map, List.getElem?_eq_getElem hn, Option.map_some,
    List.getElem?_eq_getElem (by simpa using hl ▸ hn : n < pool.toList.length),
    Array.getElem_toList, hs, Option.some.injEq] at this
  exact this ▸ hp

end Ratpoints

end
