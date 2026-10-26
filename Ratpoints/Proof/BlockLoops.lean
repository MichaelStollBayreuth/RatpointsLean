/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Blocks
public import Ratpoints.Proof.Shapes
public import Ratpoints.Proof.Stages

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
import Std.Tactic.Do

/-!
# The loops of the shapes over a block

The loops of the four shapes over the steps of a block (`Ratpoints.Sieve.squaresBlock`,
`Ratpoints.Sieve.squares1Block`, `Ratpoints.Sieve.wordsBlock`, `Ratpoints.Sieve.allBlock`, with the
walk through the set bits of a word `Ratpoints.Sieve.walkDens`, the positions of the forbidden
divisors at the first word `Ratpoints.Sieve.forbStarts` and the word of the denominators
`Ratpoints.Sieve.denWord`), and the dispatch over the shapes (`Ratpoints.Sieve.Shape.blockLoop`),
each for any step that sifts a denominator: when the step delivers the lists `L x b` of the
denominator `b`, for every `x` with `P x`, keeps a property `Q` of the store of the tables of rows
and adds the counts `κ b` to the counters when the callback does not stop the search, the loop
delivers the lists of the denominators of its steps that pass the tests of the shape, in order,
keeps `Q`, and adds their counts (`Ratpoints.Sieve.BlockPost`). The search for the decision in
force for a block ends at the last decision whose first block is at most the block
(`Ratpoints.Sieve.findDecision_spec`).

## Main definitions

* `Ratpoints.Sieve.BlockPost`, `Ratpoints.Sieve.BlockInv`: what a loop of a block does to its state,
  and the invariant of the loops.
* `Ratpoints.Sieve.ForbFits`, `Ratpoints.Sieve.PosAt`: forbidden divisors tested with words whose
  positions at the first word of a block `Ratpoints.Sieve.forbStarts` finds, and their positions
  at a word.
* `Ratpoints.Sieve.wordDens`: the denominators of a word of the word shape.
* `Ratpoints.Sieve.Shape.stepDens`, `Ratpoints.Sieve.Shape.ForbFits`,
  `Ratpoints.Sieve.Shape.LoopFits`: the denominators of a step of a shape, and what the loops of the
  shapes need.

## Main statements

* `Ratpoints.Sieve.squaresBlock_spec`, `Ratpoints.Sieve.squares1Block_spec`,
  `Ratpoints.Sieve.allBlock_spec`, `Ratpoints.Sieve.walkDens_spec`,
  `Ratpoints.Sieve.wordsBlock_spec`: the contracts of the loops of the shapes over a block, for the
  contract of the step as a hypothesis.
* `Ratpoints.Sieve.posAt_forbStarts`, `Ratpoints.Sieve.denWord_spec`: the positions of the
  forbidden divisors at the first word of a block, and the word of the denominators of a word, that
  of `Ratpoints.Sieve.wordBits`, with the positions at the next word.
* `Ratpoints.Sieve.Shape.blockLoop_spec`: the loop of a shape over a block delivers the lists of the
  denominators of its steps (`Ratpoints.Sieve.Shape.stepDens`) that pass the tests of the shape.
* `Ratpoints.Sieve.findDecision_spec`: the decision in force for a block.

## Implementation notes

The loops with a cursor (`repeat`, `while`) end by measures: the steps left for the loops of a block
over `a ≤ e`, the word for the walk, the index for the search of the decision. The deliveries are
stated for a family `L x` of lists with a property `P x`, since the run states its delivery for
every choice of the words of the classes and the ranges of the numerators, which the program does
not mention.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

variable {σ : Type} (process : Int → Int → Int → σ → Answer σ)

/-- What a loop over the denominators `M` of a block does to its state, from `st` to `st'`, for a
step that delivers the points `L b` of each denominator `b`, keeps the property `Q` of the store of
the tables of rows and adds the counts `κ b` to the counters: the delivery is that of the points of
the denominators of `M` in order, the store has the property `Q`, and when the callback has not
stopped the search, the counters are those of `st` plus the counts of the denominators of `M`. -/
def BlockPost {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int))
    (κ : Nat → Counters) (Q : RowStore → Prop) (M : List Nat) (st st' : BlockState σ) : Prop :=
  (∀ x, P x → st'.1 = st.1.deliver process (M.flatMap (L x))) ∧ Q st'.2.1 ∧
    (st'.1.quit = false → st'.2.2 = (M.map κ).foldl (· + ·) st.2.2)

/-- `Ratpoints.Sieve.BlockPost` with the callback not stopping the search: the invariant of the
loops of the blocks after the denominators `M`. -/
def BlockInv {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int))
    (κ : Nat → Counters) (Q : RowStore → Prop) (st0 : BlockState σ) (M : List Nat)
    (st : BlockState σ) : Prop :=
  st.1.quit = false ∧ BlockPost process P L κ Q M st0 st

section

variable {process} {ι : Type} {P : ι → Prop} {L : ι → Nat → List (Int × Int × Int)}
  {κ : Nat → Counters} {Q : RowStore → Prop}
  {st0 st st' : BlockState σ} {M M' : List Nat} {b : Nat}

theorem blockInv_nil (hq : st0.1.quit = false) (hQ : Q st0.2.1) :
    BlockInv process P L κ Q st0 [] st0 :=
  ⟨hq, fun _ _ ↦ by simp, hQ, fun _ ↦ rfl⟩

/-- The step at the denominator `b` after the denominators `M`. -/
theorem BlockInv.append (h : BlockInv process P L κ Q st0 M st)
    (hs : BlockPost process P L κ Q [b] st st') : BlockPost process P L κ Q (M ++ [b]) st0 st' := by
  obtain ⟨h0, h1, -, h3⟩ := h
  obtain ⟨hs1, hs2, hs3⟩ := hs
  refine ⟨fun x hx ↦ by rw [hs1 x hx, h1 x hx, List.flatMap_append, Delivery.deliver_append], hs2,
    fun hq ↦ ?_⟩
  rw [hs3 hq, h3 h0, List.map_append, List.foldl_append]

/-- The denominators `N` after the denominators `M`. -/
theorem BlockInv.append_list {N : List Nat} (h : BlockInv process P L κ Q st0 M st)
    (hs : BlockPost process P L κ Q N st st') : BlockPost process P L κ Q (M ++ N) st0 st' := by
  obtain ⟨h0, h1, -, h3⟩ := h
  obtain ⟨hs1, hs2, hs3⟩ := hs
  refine ⟨fun x hx ↦ by rw [hs1 x hx, h1 x hx, List.flatMap_append, Delivery.deliver_append], hs2,
    fun hq ↦ ?_⟩
  rw [hs3 hq, h3 h0, List.map_append, List.foldl_append]

/-- No denominator: the state is kept. -/
theorem BlockInv.blockPost_nil (h : BlockInv process P L κ Q st0 M st) :
    BlockPost process P L κ Q [] st st :=
  ⟨fun _ _ ↦ by simp, h.2.2.1, fun _ ↦ rfl⟩

theorem BlockPost.blockInv (h : BlockPost process P L κ Q M st0 st) (hq : ¬st.1.quit = true) :
    BlockInv process P L κ Q st0 M st :=
  ⟨Bool.eq_false_iff.mpr hq, h⟩

/-- At a stop, the delivery is that of the points of all the denominators of the block. -/
theorem BlockPost.of_prefix (h : BlockPost process P L κ Q M st0 st) (hM : M <+: M')
    (hq : st.1.quit = true) : BlockPost process P L κ Q M' st0 st := by
  obtain ⟨h1, h2, -⟩ := h
  refine ⟨fun x hx ↦ ?_, h2, fun h ↦ by simp [hq] at h⟩
  rw [h1 x hx] at hq ⊢
  exact (Delivery.deliver_flatMap_eq_of_prefix process hM (L x) hq).symm

end

/-! ### The loops over the steps of a block with a cursor -/

section RepeatLoop

variable {process} {ι : Type} {P : ι → Prop} {L : ι → Nat → List (Int × Int × Int)}
  {κ : Nat → Counters} {Q : RowStore → Prop}
  {D : Nat → Prop} {st0 st st' s : BlockState σ} {g : Nat → List Nat} {keep : Nat → Bool}
  {a e b mb : Nat} {o : Option (BlockState σ)}

theorem blockInv_range'_init (hae : a ≤ e) (hq : st0.1.quit = false) (hQ : Q st0.2.1) :
    a ≤ a ∧ a ≤ e ∧
      BlockInv process P L κ Q st0 (((List.range' a (a - a)).flatMap g).filter keep) st0 :=
  ⟨Nat.le_refl a, hae, by simpa using blockInv_nil hq hQ⟩

/-- At the exit of a loop of a block with a cursor, after its last step `e`. -/
theorem BlockPost.of_eq_none_range' (ho : o = none)
    (h : o = none ∧ a ≤ b ∧ b ≤ e ∧ b = e ∧
        BlockInv process P L κ Q st0 (((List.range' a (b - a + 1)).flatMap g).filter keep) s ∨
      ∃ r, o = some r ∧
        BlockPost process P L κ Q (((List.range' a (e + 1 - a)).flatMap g).filter keep) st0 r) :
    BlockPost process P L κ Q (((List.range' a (e + 1 - a)).flatMap g).filter keep) st0 s := by
  rcases h with ⟨-, hab, -, rfl, h⟩ | ⟨r, hr, -⟩
  · rw [show b + 1 - a = b - a + 1 by lia]
    exact h.2
  · simp [ho] at hr

-- `List.IsPrefix.flatMap`, which core does not have.
private theorem isPrefix_flatMap {l₁ l₂ : List Nat} (h : l₁ <+: l₂) (g : Nat → List Nat) :
    l₁.flatMap g <+: l₂.flatMap g := by
  obtain ⟨t, rfl⟩ := h
  exact ⟨t.flatMap g, by rw [List.flatMap_append]⟩

theorem filter_flatMap_range'_succ (hab : a ≤ b) :
    ((List.range' a (b - a + 1)).flatMap g).filter keep =
      ((List.range' a (b - a)).flatMap g).filter keep ++ (g b).filter keep := by
  rw [← List.range'_append_1, List.flatMap_append, List.filter_append]
  simp [show a + (b - a) = b by lia]

/-- The step `b` of a loop of a block with a cursor after which the callback stops the search. -/
theorem BlockInv.post_of_quit_range' (h : e - b = mb ∧ o = none ∧ a ≤ b ∧ b ≤ e ∧
      BlockInv process P L κ Q st0 (((List.range' a (b - a)).flatMap g).filter keep) st)
    (hs : BlockPost process P L κ Q ((g b).filter keep) st st') (hq : st'.1.quit = true) :
    BlockPost process P L κ Q (((List.range' a (e + 1 - a)).flatMap g).filter keep) st0 st' := by
  obtain ⟨-, -, hab, hbe, h⟩ := h
  have h' :
      BlockPost process P L κ Q (((List.range' a (b - a + 1)).flatMap g).filter keep) st0 st' := by
    rw [filter_flatMap_range'_succ hab]
    exact h.append_list hs
  refine h'.of_prefix ((isPrefix_flatMap ?_ g).filter keep) hq
  rw [show e + 1 - a = (b - a + 1) + (e - b) by lia]
  exact ⟨_, List.range'_append_1⟩

/-- The step `b = e` of a loop of a block with a cursor, after which the loop ends. -/
theorem BlockInv.append_range'_of_eq (h : e - b = mb ∧ o = none ∧ a ≤ b ∧ b ≤ e ∧
      BlockInv process P L κ Q st0 (((List.range' a (b - a)).flatMap g).filter keep) st)
    (hs : BlockPost process P L κ Q ((g b).filter keep) st st') (hq : ¬st'.1.quit = true)
    (hbe : b = e) :
    a ≤ b ∧ b ≤ e ∧ b = e ∧
      BlockInv process P L κ Q st0 (((List.range' a (b - a + 1)).flatMap g).filter keep) st' := by
  obtain ⟨-, -, hab, hbe', h⟩ := h
  refine ⟨hab, hbe', hbe, ?_⟩
  rw [filter_flatMap_range'_succ hab]
  exact (h.append_list hs).blockInv hq

/-- A step `b < e` of a loop of a block with a cursor after which the callback has not stopped the
search. -/
theorem BlockInv.append_range'_of_ne (h : e - b = mb ∧ o = none ∧ a ≤ b ∧ b ≤ e ∧
      BlockInv process P L κ Q st0 (((List.range' a (b - a)).flatMap g).filter keep) st)
    (hs : BlockPost process P L κ Q ((g b).filter keep) st st') (hq : ¬st'.1.quit = true)
    (hbe : ¬b = e) :
    e - (b + 1) < mb ∧ a ≤ b + 1 ∧ b + 1 ≤ e ∧
      BlockInv process P L κ Q st0 (((List.range' a (b + 1 - a)).flatMap g).filter keep) st' := by
  obtain ⟨rfl, -, hab, hbe', h⟩ := h
  refine ⟨by lia, by lia, by lia, ?_⟩
  rw [show b + 1 - a = b - a + 1 by lia, filter_flatMap_range'_succ hab]
  exact (h.append_list hs).blockInv hq

/-- A step `b` with one denominator, sifted when it passes the test. -/
theorem BlockPost.filter_singleton (hk : keep b = true) (h : BlockPost process P L κ Q [b] st st') :
    BlockPost process P L κ Q ([b].filter keep) st st' := by
  simpa [hk] using h

/-- The step `b = e` with one denominator that the test rejects. -/
theorem BlockInv.append_range'_of_eq_of_not_keep (h : e - b = mb ∧ o = none ∧ a ≤ b ∧ b ≤ e ∧
      BlockInv process P L κ Q st0 (((List.range' a (b - a)).flatMap fun b ↦ [b]).filter keep) st)
    (hk : ¬keep b = true) (hbe : b = e) :
    a ≤ b ∧ b ≤ e ∧ b = e ∧ BlockInv process P L κ Q st0
      (((List.range' a (b - a + 1)).flatMap fun b ↦ [b]).filter keep) st :=
  BlockInv.append_range'_of_eq h (by simpa [hk] using h.2.2.2.2.blockPost_nil)
    (by simp [h.2.2.2.2.1]) hbe

/-- A step `b < e` with one denominator that the test rejects. -/
theorem BlockInv.append_range'_of_ne_of_not_keep (h : e - b = mb ∧ o = none ∧ a ≤ b ∧ b ≤ e ∧
      BlockInv process P L κ Q st0 (((List.range' a (b - a)).flatMap fun b ↦ [b]).filter keep) st)
    (hk : ¬keep b = true) (hbe : ¬b = e) :
    e - (b + 1) < mb ∧ a ≤ b + 1 ∧ b + 1 ≤ e ∧ BlockInv process P L κ Q st0
      (((List.range' a (b + 1 - a)).flatMap fun b ↦ [b]).filter keep) st :=
  BlockInv.append_range'_of_ne h (by simpa [hk] using h.2.2.2.2.blockPost_nil)
    (by simp [h.2.2.2.2.1]) hbe

theorem mem_filter_range'_of_le (hab : a ≤ b) (hbe : b ≤ e) (hk : keep b = true) :
    b ∈ (List.range' a (e + 1 - a)).filter keep := by
  simp only [List.mem_filter, List.mem_range'_1, hk, and_true]
  lia

/-- What the step at the denominator `b` of a loop with a cursor needs. -/
theorem BlockInv.pre_range' {N : List Nat}
    (hD : ∀ b ∈ (List.range' a (e + 1 - a)).filter keep, D b) (hk : keep b = true)
    (h : e - b = mb ∧ o = none ∧ a ≤ b ∧ b ≤ e ∧ BlockInv process P L κ Q st0 N st) :
    D b ∧ st.1.quit = false ∧ Q st.2.1 :=
  ⟨hD b (mem_filter_range'_of_le h.2.2.1 h.2.2.2.1 hk), h.2.2.2.2.1, h.2.2.2.2.2.2.1⟩

end RepeatLoop

/-! ### The loops over a range of steps -/

section ForLoop

variable {process} {ι : Type} {P : ι → Prop} {L : ι → Nat → List (Int × Int × Int)}
  {κ : Nat → Counters} {Q : RowStore → Prop}
  {D : Nat → Prop} {st0 st st' s : BlockState σ} {f : Nat → Nat} {keep : Nat → Bool} {a e : Nat}
  {pref suff : List Nat} {cur : Nat} {o : Option (BlockState σ)} {M N : List Nat}

theorem blockInv_map_nil (hq : st0.1.quit = false) (hQ : Q st0.2.1) :
    BlockInv process P L κ Q st0 ((([] : List Nat).map f).filter keep) st0 :=
  blockInv_nil hq hQ

/-- After the return of a loop of a block at a stop, the state returned. -/
theorem BlockPost.of_eq_some {R : Prop} (ho : o = some s)
    (h : o = none ∧ R ∨ ∃ r, o = some r ∧ BlockPost process P L κ Q M st0 r) :
    BlockPost process P L κ Q M st0 s := by
  rcases h with ⟨h, -⟩ | ⟨r, hr, h⟩
  · simp [h] at ho
  · rw [ho, Option.some.injEq] at hr
    exact hr ▸ h

/-- At the end of a loop of a block over the steps `a, …, e`, the state after all of them. -/
theorem BlockPost.of_eq_none (ho : o = none)
    (h : o = none ∧ BlockInv process P L κ Q st0 (((ForIn.toList [a:e + 1]).map f).filter keep) s ∨
      ∃ r, o = some r ∧ BlockPost process P L κ Q M st0 r) :
    BlockPost process P L κ Q (((List.range' a (e + 1 - a)).map f).filter keep) st0 s := by
  rcases h with ⟨-, h⟩ | ⟨r, hr, -⟩
  · simpa using h.2
  · simp [ho] at hr

theorem mem_filter_map_of_toList_eq_append_cons (hl : ForIn.toList [a:e + 1] = pref ++ cur :: suff)
    (hk : keep (f cur) = true) : f cur ∈ ((List.range' a (e + 1 - a)).map f).filter keep := by
  have : cur ∈ ForIn.toList [a:e + 1] := by simp [hl]
  simp only [Std.Internal.ForIn.toList_range, Std.Legacy.Range.size] at this
  simp only [List.mem_filter, List.mem_map, hk, and_true]
  exact ⟨cur, by simpa using this, rfl⟩

/-- What the step at the step `cur` needs. -/
theorem BlockInv.pre_map (hl : ForIn.toList [a:e + 1] = pref ++ cur :: suff)
    (hk : keep (f cur) = true) (hD : ∀ b ∈ ((List.range' a (e + 1 - a)).map f).filter keep, D b)
    (h : o = none ∧ BlockInv process P L κ Q st0 N st) :
    D (f cur) ∧ st.1.quit = false ∧ Q st.2.1 :=
  ⟨hD _ (mem_filter_map_of_toList_eq_append_cons hl hk), h.2.1, h.2.2.2.1⟩

theorem filter_map_append_of_keep (hk : keep (f cur) = true) :
    ((pref ++ [cur]).map f).filter keep = (pref.map f).filter keep ++ [f cur] := by
  simp [List.filter_append, hk]

/-- The step at the step `cur` at which the callback stops the search. -/
theorem BlockInv.post_of_quit_map (hl : ForIn.toList [a:e + 1] = pref ++ cur :: suff)
    (hk : keep (f cur) = true)
    (h : o = none ∧ BlockInv process P L κ Q st0 ((pref.map f).filter keep) st)
    (hs : BlockPost process P L κ Q [f cur] st st') (hq : st'.1.quit = true) :
    BlockPost process P L κ Q (((List.range' a (e + 1 - a)).map f).filter keep) st0 st' := by
  refine (h.2.append hs).of_prefix ?_ hq
  rw [← filter_map_append_of_keep hk]
  refine (List.IsPrefix.map f ?_).filter keep
  rw [show List.range' a (e + 1 - a) = ForIn.toList [a:e + 1] by simp, hl]
  exact ⟨suff, by simp⟩

/-- The step at the step `cur` after which the callback has not stopped the search. -/
theorem BlockInv.append_map (hk : keep (f cur) = true)
    (h : o = none ∧ BlockInv process P L κ Q st0 ((pref.map f).filter keep) st)
    (hs : BlockPost process P L κ Q [f cur] st st') (hq : ¬st'.1.quit = true) :
    BlockInv process P L κ Q st0 (((pref ++ [cur]).map f).filter keep) st' := by
  rw [filter_map_append_of_keep hk]
  exact (h.2.append hs).blockInv hq

/-- A step whose denominator the test rejects. -/
theorem BlockInv.append_map_of_not_keep (hk : ¬keep (f cur) = true)
    (h : o = none ∧ BlockInv process P L κ Q st0 ((pref.map f).filter keep) st) :
    BlockInv process P L κ Q st0 (((pref ++ [cur]).map f).filter keep) st := by
  simpa [List.filter_append, hk] using h.2

end ForLoop

/-- The invariant of the loops of `Ratpoints.Sieve.squaresBlock` and
`Ratpoints.Sieve.squares1Block` over the steps `a, …, e` of a block, whose state is the value of a
return and the state of the block, for the denominator `f k` of the step `k` and the test `keep` of
the shape, from the state `st0`: before a return, `Ratpoints.Sieve.BlockInv` after the denominators
of the steps done that pass the test; after the return at a stop, the state returned is that after
all the denominators of the block that pass the test. -/
def MapBlockInvariant {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int))
    (κ : Nat → Counters) (Q : RowStore → Prop) (f : Nat → Nat) (keep : Nat → Bool)
    (st0 : BlockState σ) (a e : Nat) :
    Std.WP.Invariant Nat (Option (BlockState σ) × BlockState σ) Prop :=
  Std.WP.Invariant.withEarlyReturnNewDo Prop
    (fun pref _ st ↦ BlockInv process P L κ Q st0 ((pref.map f).filter keep) st)
    (fun ret _ ↦ BlockPost process P L κ Q (((List.range' a (e + 1 - a)).map f).filter keep) st0
      ret)

attribute [local irreducible] BlockInv BlockPost WalkWhileInvariant in
open Std.WP Lean.Order in
/-- The loop of the square shape over the steps `a, …, e` of a block, for a step that delivers the
lists of `L`, keeps `Q` and counts `κ b` for each denominator `b` with `D b`: the squares `k ^ 2` of
the steps whose class has a pattern, in order (`Ratpoints.Sieve.BlockPost`). -/
theorem squaresBlock_spec (step : Nat → BlockState σ → Id (BlockState σ)) (D : Nat → Prop)
    {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int)) (κ : Nat → Counters)
    (Q : RowStore → Prop)
    (hstep : ∀ b st, ⦃ D b ∧ st.1.quit = false ∧ Q st.2.1 ⦄ step b st
      ⦃ fun st' ↦ BlockPost process P L κ Q [b] st st' ⦄)
    (cls : Vector NumClass 64) (a e : Nat) (st : BlockState σ) :
    ⦃ st.1.quit = false ∧ Q st.2.1 ∧ ∀ b ∈ ((List.range' a (e + 1 - a)).map fun k ↦ k * k).filter
        fun b ↦ cls[b % 64]!.bits != 0, D b ⦄
    squaresBlock step cls a e st
    ⦃ fun st' ↦ BlockPost process P L κ Q (((List.range' a (e + 1 - a)).map fun k ↦ k * k).filter
        fun b ↦ cls[b % 64]!.bits != 0) st st' ⦄ := by
  vcgen [squaresBlock, hstep] invariants
  | inv1 => MapBlockInvariant process P L κ Q (fun k ↦ k * k) (fun b ↦ cls[b % 64]!.bits != 0) st a
      e
  all_goals simp only [MapBlockInvariant, meet_prop_eq_and, join_prop_eq_or, iSup_prop_eq_exists,
    ofProp_prop_eq,
    reduceCtorEq, false_and, or_false, false_or, true_and, and_false, Option.some.injEq,
    exists_eq_left', exists_false, and_true] at *
  all_goals obtain ⟨hq0, hQ0, hD⟩ := ‹st.1.quit = false ∧ _›
  all_goals first
    | exact blockInv_map_nil hq0 hQ0
    | exact BlockPost.of_eq_some ‹_› ‹_›
    | exact BlockPost.of_eq_none ‹_› ‹_›
    | exact BlockInv.pre_map ‹_› ‹_› hD ‹_›
    | exact BlockInv.post_of_quit_map ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact BlockInv.append_map ‹_› ‹_› ‹_› ‹_›
    | exact BlockInv.append_map_of_not_keep ‹_› ‹_›

-- The two tests of the loop of the divisor shape, in the form of its verification conditions.
private theorem and_eq_true_of_eq {x y t : Bool} (h1 : x = true) (ht : t = y) (h : t = true) :
    (x && y) = true := by
  simp_all

private theorem and_ne_true_of_left {x y : Bool} (h1 : ¬x = true) : ¬(x && y) = true := by
  simp_all

private theorem and_ne_true_of_eq {x y t : Bool} (ht : t = y) (h : ¬t = true) :
    ¬(x && y) = true := by
  simp_all

-- The valuation test of the divisor shape, as a value for the contract of its loop.
private theorem denInfoTest_value (info : List Setup.DenInfo) (b : Nat) :
    ⦃ True ⦄ denInfoTest info b ⦃ fun r ↦ r = Id.run (denInfoTest info b) ⦄ :=
  ⟨fun _ ↦ rfl⟩

attribute [local irreducible] BlockInv BlockPost WalkWhileInvariant in
open Std.WP Lean.Order in
/-- The loop of a segment of the divisor shape, of the divisor `dv`, over the steps `a, …, e` of a
block, for a step that delivers the lists of `L`, keeps `Q` and counts `κ b` for each denominator
`b` with `D b`: the products `dv k ^ 2` of the steps whose class has a pattern and that pass the
valuation test (`Ratpoints.Sieve.denInfoTest`), in order. -/
theorem squares1Block_spec (step : Nat → BlockState σ → Id (BlockState σ)) (D : Nat → Prop)
    {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int)) (κ : Nat → Counters)
    (Q : RowStore → Prop)
    (hstep : ∀ b st, ⦃ D b ∧ st.1.quit = false ∧ Q st.2.1 ⦄ step b st
      ⦃ fun st' ↦ BlockPost process P L κ Q [b] st st' ⦄)
    (cls : Vector NumClass 64) (info : List Setup.DenInfo) (dv a e : Nat) (st : BlockState σ) :
    ⦃ st.1.quit = false ∧ Q st.2.1 ∧
        ∀ b ∈ ((List.range' a (e + 1 - a)).map fun k ↦ dv * k * k).filter
        (fun b ↦ cls[b % 64]!.bits != 0 && Id.run (denInfoTest info b)), D b ⦄
    squares1Block step cls info dv a e st
    ⦃ fun st' ↦ BlockPost process P L κ Q
        (((List.range' a (e + 1 - a)).map fun k ↦ dv * k * k).filter
        fun b ↦ cls[b % 64]!.bits != 0 && Id.run (denInfoTest info b)) st st' ⦄ := by
  vcgen [squares1Block, hstep, denInfoTest_value] invariants
  | inv1 => MapBlockInvariant process P L κ Q (fun k ↦ dv * k * k)
      (fun b ↦ cls[b % 64]!.bits != 0 && Id.run (denInfoTest info b)) st a e
  all_goals simp only [MapBlockInvariant, meet_prop_eq_and, join_prop_eq_or, iSup_prop_eq_exists,
    ofProp_prop_eq,
    reduceCtorEq, false_and, or_false, false_or, true_and, and_false, Option.some.injEq,
    exists_eq_left', exists_false, and_true] at *
  all_goals obtain ⟨hq0, hQ0, hD⟩ := ‹st.1.quit = false ∧ _›
  all_goals first
    | exact blockInv_map_nil hq0 hQ0
    | exact BlockPost.of_eq_some ‹_› ‹_›
    | exact BlockPost.of_eq_none ‹_› ‹_›
    | exact BlockInv.pre_map ‹_› (and_eq_true_of_eq ‹_› ‹_› ‹_›) hD ‹_›
    | exact BlockInv.post_of_quit_map ‹_› (and_eq_true_of_eq ‹_› ‹_› ‹_›) ‹_› ‹_› ‹_›
    | exact BlockInv.append_map (and_eq_true_of_eq ‹_› ‹_› ‹_›) ‹_› ‹_› ‹_›
    | exact BlockInv.append_map_of_not_keep (and_ne_true_of_eq ‹_› ‹_›) ‹_›
    | exact BlockInv.append_map_of_not_keep (and_ne_true_of_left ‹_›) ‹_›

/-- The invariant of the loop of `Ratpoints.Sieve.allBlock` over the denominators `a, …, e` of a
block, whose state is the value of a return, the state of the block and the cursor `b`, for the test
`keep` of the shape, from the state `st0`: before a return, `a ≤ b ≤ e` and
`Ratpoints.Sieve.BlockInv` after the denominators before `b`, and after `b` too at the exit; after
the return at a stop, the state returned is that after all the denominators of the block. -/
def AllBlockInvariant {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int))
    (κ : Nat → Counters)
    (Q : RowStore → Prop) (keep : Nat → Bool) (st0 : BlockState σ) (a e : Nat) :
    Std.WP.WhileInvariant (Option (BlockState σ) × BlockState σ × Nat) Prop :=
  .mk fun exit s ↦ (s.1 = none ∧ a ≤ s.2.2 ∧ s.2.2 ≤ e ∧ (exit = true → s.2.2 = e) ∧
      BlockInv process P L κ Q st0 (((List.range' a (s.2.2 - a + if exit then 1 else 0)).flatMap
        fun b ↦ [b]).filter keep) s.2.1) ∨
    (exit = true ∧ ∃ r, s.1 = some r ∧ BlockPost process P L κ Q
      (((List.range' a (e + 1 - a)).flatMap fun b ↦ [b]).filter keep) st0 r)

attribute [local irreducible] BlockInv BlockPost WalkWhileInvariant in
open Std.WP Lean.Order in
/-- The loop of the shape of every denominator over the steps `a ≤ e` of a block, for a step that
delivers the lists of `L`, keeps `Q` and counts `κ b` for each denominator `b` with `D b`: the
denominators `a, …, e` whose class has a pattern, in order; the loop ends, since the steps left
decrease. -/
theorem allBlock_spec (step : Nat → BlockState σ → Id (BlockState σ)) (D : Nat → Prop)
    {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int)) (κ : Nat → Counters)
    (Q : RowStore → Prop)
    (hstep : ∀ b st, ⦃ D b ∧ st.1.quit = false ∧ Q st.2.1 ⦄ step b st
      ⦃ fun st' ↦ BlockPost process P L κ Q [b] st st' ⦄)
    (cls : Vector NumClass 64) (a e : Nat) (st : BlockState σ) :
    ⦃ st.1.quit = false ∧ Q st.2.1 ∧ a ≤ e ∧ ∀ b ∈ (List.range' a (e + 1 - a)).filter
        (fun b ↦ cls[b % 64]!.bits != 0), D b ⦄
    allBlock step cls a e st
    ⦃ fun st' ↦ BlockPost process P L κ Q (((List.range' a (e + 1 - a)).flatMap fun b ↦ [b]).filter
        fun b ↦ cls[b % 64]!.bits != 0) st st' ⦄ := by
  vcgen [allBlock, hstep] invariants
  | inv1 => AllBlockInvariant process P L κ Q (fun b ↦ cls[b % 64]!.bits != 0) st a e
  | inv2 => .ofMeasure fun s ↦ e - s.2.2
  all_goals simp only [AllBlockInvariant, WhileInvariant.mk_apply,
    Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure,
    meet_prop_eq_and, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, exists_eq_left', exists_false, ↓reduceIte, Nat.add_zero,
    forall_const, false_implies] at *
  all_goals obtain ⟨hq0, hQ0, hae, hD⟩ := ‹st.1.quit = false ∧ _›
  all_goals first
    | exact blockInv_range'_init hae hq0 hQ0
    | exact BlockPost.of_eq_some ‹_› ‹_›
    | exact BlockPost.of_eq_none_range' ‹_› ‹_›
    | exact BlockInv.pre_range' hD ‹_› ‹_›
    | exact BlockInv.post_of_quit_range' ‹_› (BlockPost.filter_singleton ‹_› ‹_›) ‹_›
    | exact BlockInv.append_range'_of_eq ‹_› (BlockPost.filter_singleton ‹_› ‹_›) ‹_› ‹_›
    | exact BlockInv.append_range'_of_ne ‹_› (BlockPost.filter_singleton ‹_› ‹_›) ‹_› ‹_›
    | exact BlockInv.append_range'_of_eq_of_not_keep ‹_› ‹_› ‹_›
    | exact BlockInv.append_range'_of_ne_of_not_keep ‹_› ‹_› ‹_›

/-! ### The walk through the set bits of a word of the word shape -/

/-- The invariant of the loop of `Ratpoints.Sieve.walkDens` through the set bits of the word `x0`
of the denominators `base + t`, whose state is the value of a return, the word and the state of the
block, for the test `keep` of the word shape, from the state `st0`: before a return,
`Ratpoints.Sieve.WalkWhileInvariant` for `Ratpoints.Sieve.BlockInv` after the denominators of the
set bits below `k` that pass the test; after the return at a stop, the state returned is that after
all of them. -/
def WalkDensWhileInvariant {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int))
    (κ : Nat → Counters)
    (Q : RowStore → Prop) (keep : Nat → Bool) (x0 : UInt64) (base : Nat) (st0 : BlockState σ) :
    Std.WP.WhileInvariant (Option (BlockState σ) × UInt64 × BlockState σ) Prop :=
  .mk fun exit s ↦ s.1 = none ∧ WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
      ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) exit
        (s.2.2, s.2.1) ∨
    exit = true ∧ ∃ r, s.1 = some r ∧ BlockPost process P L κ Q
      ((((List.range 64).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st0 r

section Walk

variable {process} {ι : Type} {P : ι → Prop} {L : ι → Nat → List (Int × Int × Int)}
  {κ : Nat → Counters} {Q : RowStore → Prop}
  {D : Nat → Prop} {keep : Nat → Bool} {x0 x : UInt64} {base t k mb : Nat} {y : Bool}
  {st0 st st' s : BlockState σ} {o : Option (BlockState σ)}

/-- The denominators `base + t` of the set bits `t` of `x0` up to the lowest set bit of `x`, which
has the bits of `x0` below `k` cleared, that pass the test `keep`. -/
theorem ClearedBelow.filter_map_filter_range_succ_ctz (hx : ClearedBelow x0 k x) (hx0 : x ≠ 0) :
    (((List.range (x.toBitVec.ctz.toNat + 1)).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter
        keep = (((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep ++
      [base + x.toBitVec.ctz.toNat].filter keep := by
  rw [hx.filter_range_succ_ctz hx0, List.map_append, List.filter_append]
  rfl

theorem walkWhileInvariant_init (hq : st0.1.quit = false) (hQ : Q st0.2.1) :
    WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
      ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) false
        (st0, x0) :=
  walkWhileInvariant_self (by simpa using blockInv_nil hq hQ)

/-- At the exit of the walk, after all the set bits of `x0`. -/
theorem BlockPost.of_eq_none_walk (ho : o = none)
    (h : o = none ∧ WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
        ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) true
          (s, x) ∨
      ∃ r, o = some r ∧ BlockPost process P L κ Q
        ((((List.range 64).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st0 r) :
    BlockPost process P L κ Q
      ((((List.range 64).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st0 s := by
  rcases h with ⟨-, h⟩ | ⟨r, hr, -⟩
  · obtain ⟨k, hcl, hk⟩ := h.exists_clearedBelow_zero
    rw [← hcl.filter_range_of_eq_zero]
    exact hk.2
  · simp [ho] at hr

/-- What the step at the lowest set bit of `x` needs: its denominator is one of the walk. -/
theorem walkWhileInvariant_pre
    (hD : ∀ b ∈ (((List.range 64).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep, D b)
    (h : x.toNat = mb ∧ o = none ∧ WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
      ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) false
        (st, x))
    (hx : (x != 0) = true) (ht : t = x.toBitVec.ctz.toNat) (hy : y = keep (base + t))
    (hy' : y = true) : D (base + t) ∧ st.1.quit = false ∧ Q st.2.1 := by
  obtain ⟨-, -, k, hcl, hk, -⟩ := h
  have hx0 := bne_iff_ne.mp hx
  refine ⟨hD _ ?_, hk.1, hk.2.2.1⟩
  subst ht
  obtain ⟨hc, -⟩ := hcl.getLsbD_ctz_and_le_ctz hx0
  simp only [List.mem_filter, List.mem_map, List.mem_range, ← hy, hy', and_true]
  exact ⟨_, ⟨UInt64.toNat_ctz_lt hx0, hc⟩, rfl⟩

/-- The step at the lowest set bit of `x` after which the callback stops the search. -/
theorem walkWhileInvariant_post_of_quit
    (h : x.toNat = mb ∧ o = none ∧ WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
      ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) false
        (st, x))
    (hx : (x != 0) = true) (ht : t = x.toBitVec.ctz.toNat) (hy : y = keep (base + t))
    (hy' : y = true) (hs : BlockPost process P L κ Q [base + t] st st') (hq : st'.1.quit = true) :
    BlockPost process P L κ Q
      ((((List.range 64).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st0 st' := by
  obtain ⟨-, -, k, hcl, hk, -⟩ := h
  have hx0 := bne_iff_ne.mp hx
  subst ht
  have h' := hk.append_list (BlockPost.filter_singleton (hy' ▸ hy).symm hs)
  rw [← hcl.filter_map_filter_range_succ_ctz hx0] at h'
  exact h'.of_prefix (((List.range_prefix_range (UInt64.toNat_ctz_lt hx0)).filter _).map _
    |>.filter _) hq

/-- A step of the walk at whose set bit the callback does not stop the search, or whose denominator
the test rejects (`st' = st`). -/
theorem walkWhileInvariant_and_sub_one
    (h : x.toNat = mb ∧ o = none ∧ WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
      ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) false
        (st, x))
    (hx : (x != 0) = true) (ht : t = x.toBitVec.ctz.toNat)
    (hs : BlockPost process P L κ Q ([base + t].filter keep) st st') (hq : ¬st'.1.quit = true) :
    (x &&& x - 1).toNat < mb ∧ WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
      ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) false
        (st', x &&& x - 1) := by
  subst ht
  exact WalkWhileInvariant.and_sub_one ⟨h.1, h.2.2⟩ hx fun _ hcl hk ↦ by
    rw [hcl.filter_map_filter_range_succ_ctz (bne_iff_ne.mp hx)]
    exact (hk.append_list hs).blockInv hq

/-- A step whose denominator the test passes. -/
theorem walkWhileInvariant_and_sub_one_of_keep
    (h : x.toNat = mb ∧ o = none ∧ WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
      ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) false
        (st, x))
    (hx : (x != 0) = true) (ht : t = x.toBitVec.ctz.toNat) (hy : y = keep (base + t))
    (hy' : y = true) (hs : BlockPost process P L κ Q [base + t] st st') (hq : ¬st'.1.quit = true) :
    (x &&& x - 1).toNat < mb ∧ WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
      ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) false
        (st', x &&& x - 1) :=
  walkWhileInvariant_and_sub_one h hx ht (BlockPost.filter_singleton (hy' ▸ hy).symm hs) hq

/-- A step whose denominator the test rejects. -/
theorem walkWhileInvariant_and_sub_one_of_not_keep
    (h : x.toNat = mb ∧ o = none ∧ WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
      ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) false
        (st, x))
    (hx : (x != 0) = true) (ht : t = x.toBitVec.ctz.toNat) (hy : y = keep (base + t))
    (hy' : ¬y = true) :
    (x &&& x - 1).toNat < mb ∧ WalkWhileInvariant x0 (fun k st ↦ BlockInv process P L κ Q st0
      ((((List.range k).filter (x0.toBitVec.getLsbD ·)).map (base + ·)).filter keep) st) false
        (st, x &&& x - 1) := by
  obtain ⟨k, -, hk, -⟩ := h.2.2
  have hq : st.1.quit = false := hk.1
  refine walkWhileInvariant_and_sub_one h hx ht ?_ (by simp [hq])
  simpa [← hy, hy'] using hk.blockPost_nil

theorem walkWhileInvariant_exit {W : Nat → BlockState σ → Prop}
    (h : x.toNat = mb ∧ o = none ∧ WalkWhileInvariant x0 W false (st, x)) (hx : ¬(x != 0) = true) :
    WalkWhileInvariant x0 W true (st, x) :=
  WalkWhileInvariant.exit hx ⟨h.1, h.2.2⟩

end Walk

-- The test of the word shape, as a value for the contract of the walk.
private theorem test_value (test : Nat → Id Bool) (b : Nat) :
    ⦃ True ⦄ test b ⦃ fun r ↦ r = Id.run (test b) ⦄ :=
  ⟨fun _ ↦ rfl⟩

attribute [local irreducible] BlockInv BlockPost WalkWhileInvariant in
open Std.WP Lean.Order in
/-- The walk through the set bits `t` of the word `x`, lowest first, for a step that delivers
the lists of `L`, keeps `Q` and counts `κ b` for each denominator `b` with `D b`: the denominators
`base + t` that pass the test `test`, in order; the walk ends, since clearing the lowest set bit
makes a word other than `0` smaller. -/
theorem walkDens_spec (step : Nat → BlockState σ → Id (BlockState σ)) (D : Nat → Prop)
    {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int)) (κ : Nat → Counters)
    (Q : RowStore → Prop)
    (hstep : ∀ b st, ⦃ D b ∧ st.1.quit = false ∧ Q st.2.1 ⦄ step b st
      ⦃ fun st' ↦ BlockPost process P L κ Q [b] st st' ⦄)
    (test : Nat → Id Bool) (x : UInt64) (base : Nat) (st : BlockState σ) :
    ⦃ st.1.quit = false ∧ Q st.2.1 ∧ ∀ b ∈ (((List.range 64).filter (x.toBitVec.getLsbD ·)).map
        (base + ·)).filter (fun b ↦ Id.run (test b)), D b ⦄
    walkDens step test x base st
    ⦃ fun st' ↦ BlockPost process P L κ Q ((((List.range 64).filter (x.toBitVec.getLsbD ·)).map
        (base + ·)).filter fun b ↦ Id.run (test b)) st st' ⦄ := by
  vcgen [walkDens, hstep, test_value test] invariants
  | inv1 => WalkDensWhileInvariant process P L κ Q (fun b ↦ Id.run (test b)) x base st
  | inv2 => .ofMeasure fun s ↦ s.2.1.toNat
  all_goals simp only [WalkDensWhileInvariant, WhileInvariant.mk_apply,
    Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure,
    meet_prop_eq_and, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, exists_eq_left', exists_false] at *
  all_goals obtain ⟨hq0, hQ0, hD⟩ := ‹st.1.quit = false ∧ _›
  all_goals first
    | exact walkWhileInvariant_init hq0 hQ0
    | exact BlockPost.of_eq_some ‹_› ‹_›
    | exact BlockPost.of_eq_none_walk ‹_› ‹_›
    | exact bne_iff_ne.mp ‹_›
    | exact walkWhileInvariant_pre hD ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact walkWhileInvariant_post_of_quit ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact walkWhileInvariant_and_sub_one_of_keep ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact walkWhileInvariant_and_sub_one_of_not_keep ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact walkWhileInvariant_exit ‹_› ‹_›

/-! ### The words of the word shape -/

/-- The forbidden divisors `forb` tested with words have positive primes `p ≤ 2 ^ 32` with their
reciprocals (`Ratpoints.Sieve.magic`), so that `Ratpoints.Sieve.forbStarts` finds the position of
each at the first word of a block. -/
def ForbFits (forb : List ForbiddenEntry) : Prop :=
  ∀ f ∈ forb, 0 < f.p ∧ f.p ≤ 2 ^ 32 ∧ f.magic = magic f.p

/-- The positions `cur` of the forbidden divisors `forb` tested with words are those at the word
`w`: one for each, `w mod p` for the prime `p`. -/
def PosAt (forb : Array ForbiddenEntry) (cur : Array Nat) (w : Nat) : Prop :=
  cur.size = forb.size ∧ ∀ n < forb.size, cur[n]! = w % forb[n]!.p

/-- The positions of the forbidden divisors tested with words at the first word `a` of a block are
those at `a`: `a mod p`, by the reciprocal of `p` when `a ≤ Ratpoints.mulModLimit`
(`Ratpoints.Sieve.mulMod_magic`) and by `Ratpoints.Sieve.modLong` otherwise. -/
theorem posAt_forbStarts {forb : Array ForbiddenEntry} (h : ForbFits forb.toList) (a : Nat) :
    PosAt forb (forbStarts forb a) a := by
  refine ⟨by simp [forbStarts], fun n hn ↦ ?_⟩
  obtain ⟨hp, hp32, hm⟩ := h _ (Array.getElem_mem_toList hn)
  rw [forbStarts, getElem!_pos _ n (by simpa using hn), Array.getElem_map,
    getElem!_pos forb n hn]
  split
  · rename_i hle
    rw [hm, mulMod_magic hp (mul_lt_two_pow_64_of_le_mulModLimit (of_decide_eq_true hle) hp32)]
  · rw [modLong_eq_emod _ (Int.natCast_nonneg _), ← Int.natCast_emod, Int.toNat_natCast]

-- The invariant of the loop of `Ratpoints.Sieve.denWord` over the forbidden divisors done, `pref`:
-- the word and-ed with their words at `w`, and their positions stepped on to `w + 1`.
private def DenWordInvariant (db : UInt64) (forb : Array ForbiddenEntry) (w : Nat) (k : Nat)
    (s : UInt64 × Array Nat) : Prop :=
  s.1 = (forb.toList.take k).foldl (fun x e ↦ x &&& e.words[w % e.p]!) db ∧
    s.2.size = forb.size ∧ ∀ n < forb.size, s.2[n]! = (if n < k then w + 1 else w) % forb[n]!.p

private theorem DenWordInvariant.succ {db : UInt64} {forb : Array ForbiddenEntry} {w cur : Nat}
    {x : UInt64} {pos : Array Nat} (hpos : ∀ f ∈ forb.toList, 0 < f.p) (hc : cur < forb.size)
    (h : DenWordInvariant db forb w cur (x, pos)) :
    DenWordInvariant db forb w (cur + 1) (x &&& forb[cur]!.words[pos[cur]!]!,
      pos.set! cur (if pos[cur]! + 1 = forb[cur]!.p then 0 else pos[cur]! + 1)) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only at h1 h2 h3
  have hp := hpos _ (Array.getElem_mem_toList hc)
  have hcur := h3 cur hc
  simp only [Nat.lt_irrefl, ↓reduceIte] at hcur
  refine ⟨?_, by simp [h2], fun n hn ↦ ?_⟩
  · rw [List.take_succ_eq_append_getElem (by simpa using hc), List.foldl_append, ← h1, hcur]
    simp [getElem!_pos forb cur hc]
  · rw [Array.getElem!_set! (by rw [h2]; exact hn)]
    split
    · subst n
      rw [getElem!_pos forb cur hc] at hcur ⊢
      rw [hcur, Nat.ite_mod_add_one_eq_add_one_mod hp]
      simp
    · rw [h3 n hn]
      congr 2
      grind

private theorem DenWordInvariant.init {db : UInt64} {forb : Array ForbiddenEntry} {w : Nat}
    {cur : Array Nat} (h : PosAt forb cur w) : DenWordInvariant db forb w 0 (db, cur) :=
  ⟨rfl, h.1, fun n hn ↦ by simpa using h.2 n hn⟩

-- The word after the loop over the forbidden divisors is the word and-ed with all their words at
-- `w`, and the positions are those at the next word.
private theorem DenWordInvariant.post {db : UInt64} {forb : Array ForbiddenEntry} {w : Nat}
    {x : UInt64} {c : Array Nat}
    (h : DenWordInvariant db forb w (ForIn.toList [0:forb.size]).length (x, c)) :
    x = forb.toList.foldl (fun x e ↦ x &&& e.words[w % e.p]!) db ∧ PosAt forb c (w + 1) := by
  obtain ⟨h1, h2, h3⟩ := h
  simp only [Std.Legacy.Range.length_toList, Nat.sub_zero] at h1 h2 h3
  rw [h1, show forb.size = forb.toList.length by simp, List.take_length]
  exact ⟨rfl, h2, fun n hn ↦ by simpa [hn] using h3 n hn⟩

private theorem DenWordInvariant.append {db : UInt64} {forb : Array ForbiddenEntry} {w cur : Nat}
    {x : UInt64} {c : Array Nat} {pref suff : List Nat} (hpos : ∀ f ∈ forb.toList, 0 < f.p)
    (hl : ForIn.toList [0:forb.size] = pref ++ cur :: suff)
    (h : DenWordInvariant db forb w pref.length (x, c)) :
    DenWordInvariant db forb w (pref ++ [cur]).length (x &&& forb[cur]!.words[c[cur]!]!,
      c.set! cur (if c[cur]! + 1 = forb[cur]!.p then 0 else c[cur]! + 1)) := by
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  rw [Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl] at h
  exact h.succ hpos (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)

theorem wordBits_eq_foldl (db : UInt64) (forb : List ForbiddenEntry) (bLow bHigh w : Nat)
    {x : UInt64}
    (hx : x = forb.foldl (fun x e ↦ x &&& e.words[w % e.p]!) db) :
    wordBits db forb bLow bHigh w =
      if w = bHigh / 64 then
        (if w = bLow / 64 then x &&& ~~~0 <<< UInt64.ofNat (bLow % 64) else x) &&&
          ~~~0 >>> UInt64.ofNat (63 - bHigh % 64)
      else if w = bLow / 64 then x &&& ~~~0 <<< UInt64.ofNat (bLow % 64) else x := by
  rw [hx]
  rfl

attribute [local irreducible] DenWordInvariant in
open Std.WP Lean.Order in
/-- The word of the denominators of the word `w` that the class test and the forbidden divisors
`forb` tested with words leave, from their positions `cur` at `w`, with the masks of the first and
the last word of the run: the word of `Ratpoints.Sieve.wordBits`; the positions are then those at
`w + 1`. -/
theorem denWord_spec (db : UInt64) (forb : Array ForbiddenEntry) (cur : Array Nat)
    (lo0 hi0 bLow bHigh w : Nat) :
    ⦃ (∀ f ∈ forb.toList, 0 < f.p) ∧ PosAt forb cur w ∧ lo0 = bLow / 64 ∧ hi0 = bHigh / 64 ⦄
    denWord db forb cur lo0 hi0 bLow bHigh w
    ⦃ fun r ↦ r.1 = wordBits db forb.toList bLow bHigh w ∧ PosAt forb r.2 (w + 1) ⦄ := by
  vcgen [denWord] invariants
  | inv1 => fun pref _ s ↦ DenWordInvariant db forb w pref.length s
  all_goals obtain ⟨hpos, hcur, rfl, rfl⟩ := ‹(∀ f ∈ forb.toList, 0 < f.p) ∧ _›
  all_goals first
    | exact DenWordInvariant.init hcur
    | exact DenWordInvariant.append hpos ‹_› ‹_›
    | (obtain ⟨hx, hp⟩ := DenWordInvariant.post ‹_›
       refine ⟨?_, hp⟩
       rw [wordBits_eq_foldl db forb.toList bLow bHigh w hx]
       split_ifs
       rfl)

/-- The denominators `64 w + t` of the word `w` of the word shape, of the set bits `t` of its word
(`Ratpoints.Sieve.wordBits`), lowest first. -/
def wordDens (db : UInt64) (forb : List ForbiddenEntry) (bLow bHigh w : Nat) : List Nat :=
  ((List.range 64).filter (wordBits db forb bLow bHigh w).toBitVec.getLsbD).map (64 * w + ·)

/-- The invariant of the loop of `Ratpoints.Sieve.wordsBlock` over the words `a, …, e` of a block,
whose state is the value of a return, the positions of the forbidden divisors `forb` tested with
words, the state of the block and the word `w`, for the test `keep` of the word shape, from the
state `st0`: before a return, `a ≤ w ≤ e`, `Ratpoints.Sieve.BlockInv` after the denominators of the
words before `w` (`Ratpoints.Sieve.wordDens`), and of `w` too at the exit, and the positions those
at `w` before it; after the return at a stop, the state returned is that after all the denominators
of the block. -/
def WordsBlockInvariant {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int))
    (κ : Nat → Counters)
    (Q : RowStore → Prop) (keep : Nat → Bool) (db : UInt64) (forb : Array ForbiddenEntry)
    (bLow bHigh : Nat) (st0 : BlockState σ) (a e : Nat) :
    Std.WP.WhileInvariant (Option (BlockState σ) × Array Nat × BlockState σ × Nat) Prop :=
  .mk fun exit s ↦ (s.1 = none ∧ a ≤ s.2.2.2 ∧ s.2.2.2 ≤ e ∧ (exit = true → s.2.2.2 = e) ∧
      BlockInv process P L κ Q st0 (((List.range' a (s.2.2.2 - a + if exit then 1 else 0)).flatMap
        (wordDens db forb.toList bLow bHigh)).filter keep) s.2.2.1 ∧
      (exit = false → PosAt forb s.2.1 s.2.2.2)) ∨
    (exit = true ∧ ∃ r, s.1 = some r ∧ BlockPost process P L κ Q
      (((List.range' a (e + 1 - a)).flatMap (wordDens db forb.toList bLow bHigh)).filter keep) st0
        r)

section Words

variable {process} {ι : Type} {P : ι → Prop} {L : ι → Nat → List (Int × Int × Int)}
  {κ : Nat → Counters} {Q : RowStore → Prop}
  {D : Nat → Prop} {keep : Nat → Bool} {db x : UInt64} {forb : Array ForbiddenEntry}
  {bLow bHigh a e w mb : Nat} {st0 st st' s : BlockState σ} {o : Option (BlockState σ)}
  {cur cur' : Array Nat}

theorem wordsBlockInvariant_init (hae : a ≤ e) (hq : st0.1.quit = false) (hQ : Q st0.2.1)
    (hforb : ForbFits forb.toList) :
    a ≤ a ∧ a ≤ e ∧ BlockInv process P L κ Q st0 (((List.range' a (a - a)).flatMap
      (wordDens db forb.toList bLow bHigh)).filter keep) st0 ∧ PosAt forb (forbStarts forb a) a :=
  have h := blockInv_range'_init (g := wordDens db forb.toList bLow bHigh) (keep := keep) hae hq hQ
  ⟨h.1, h.2.1, h.2.2, posAt_forbStarts hforb a⟩

/-- What the word of the denominators of `w` needs. -/
theorem wordsBlockInvariant_pre_denWord (hforb : ForbFits forb.toList)
    (h : e - w = mb ∧ o = none ∧ a ≤ w ∧ w ≤ e ∧ BlockInv process P L κ Q st0
      (((List.range' a (w - a)).flatMap (wordDens db forb.toList bLow bHigh)).filter keep) st ∧
        PosAt forb cur w) :
    (∀ f ∈ forb.toList, 0 < f.p) ∧ PosAt forb cur w ∧ bLow / 64 = bLow / 64 ∧
      bHigh / 64 = bHigh / 64 :=
  ⟨fun f hf ↦ (hforb f hf).1, h.2.2.2.2.2, rfl, rfl⟩

theorem BlockPost.of_eq_none_words (ho : o = none)
    (h : o = none ∧ a ≤ w ∧ w ≤ e ∧ w = e ∧ BlockInv process P L κ Q st0 (((List.range'
        a (w - a + 1)).flatMap (wordDens db forb.toList bLow bHigh)).filter keep) s ∧ True ∨
      ∃ r, o = some r ∧ BlockPost process P L κ Q (((List.range' a (e + 1 - a)).flatMap
        (wordDens db forb.toList bLow bHigh)).filter keep) st0 r) :
    BlockPost process P L κ Q (((List.range' a (e + 1 - a)).flatMap
      (wordDens db forb.toList bLow bHigh)).filter keep) st0 s :=
  BlockPost.of_eq_none_range' ho (h.imp (fun h ↦ ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩) id)

/-- The walk through the word of `w` is through its denominators (`Ratpoints.Sieve.wordDens`). -/
theorem BlockPost.wordDens_of_eq
    (hx : x = wordBits db forb.toList bLow bHigh w ∧ PosAt forb cur' (w + 1))
    (hs : BlockPost process P L κ Q ((((List.range 64).filter x.toBitVec.getLsbD).map
      (HAdd.hAdd (64 * w))).filter keep) st st') :
    BlockPost process P L κ Q ((wordDens db forb.toList bLow bHigh w).filter keep) st st' := by
  rw [hx.1] at hs
  exact hs

/-- What the walk through the word of `w` needs: its denominators are those of the block. -/
theorem wordsBlockInvariant_pre_walk
    (hD : ∀ b ∈ ((List.range' a (e + 1 - a)).flatMap (wordDens db forb.toList bLow bHigh)).filter
      keep, D b)
    (hx : x = wordBits db forb.toList bLow bHigh w ∧ PosAt forb cur' (w + 1))
    (h : e - w = mb ∧ o = none ∧ a ≤ w ∧ w ≤ e ∧ BlockInv process P L κ Q st0
      (((List.range' a (w - a)).flatMap (wordDens db forb.toList bLow bHigh)).filter keep) st ∧
        PosAt forb cur w) :
    st.1.quit = false ∧ Q st.2.1 ∧ ∀ b ∈ (((List.range 64).filter x.toBitVec.getLsbD).map
      (HAdd.hAdd (64 * w))).filter keep, D b := by
  refine ⟨h.2.2.2.2.1.1, h.2.2.2.2.1.2.2.1, fun b hb ↦ hD b ?_⟩
  rw [hx.1] at hb
  obtain ⟨hb, hk⟩ := List.mem_filter.mp hb
  exact List.mem_filter.mpr
    ⟨List.mem_flatMap.mpr ⟨w, by simp only [List.mem_range'_1]; lia, hb⟩, hk⟩

theorem wordsBlockInvariant_post_of_quit
    (hx : x = wordBits db forb.toList bLow bHigh w ∧ PosAt forb cur' (w + 1))
    (hs : BlockPost process P L κ Q ((((List.range 64).filter x.toBitVec.getLsbD).map
      (HAdd.hAdd (64 * w))).filter keep) st st') (hq : st'.1.quit = true)
    (h : e - w = mb ∧ o = none ∧ a ≤ w ∧ w ≤ e ∧ BlockInv process P L κ Q st0
      (((List.range' a (w - a)).flatMap (wordDens db forb.toList bLow bHigh)).filter keep) st ∧
        PosAt forb cur w) :
    BlockPost process P L κ Q (((List.range' a (e + 1 - a)).flatMap
      (wordDens db forb.toList bLow bHigh)).filter keep) st0 st' :=
  BlockInv.post_of_quit_range' ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
    (BlockPost.wordDens_of_eq hx hs) hq

theorem wordsBlockInvariant_append_of_eq
    (hx : x = wordBits db forb.toList bLow bHigh w ∧ PosAt forb cur' (w + 1))
    (hs : BlockPost process P L κ Q ((((List.range 64).filter x.toBitVec.getLsbD).map
      (HAdd.hAdd (64 * w))).filter keep) st st') (hq : ¬st'.1.quit = true) (hwe : w = e)
    (h : e - w = mb ∧ o = none ∧ a ≤ w ∧ w ≤ e ∧ BlockInv process P L κ Q st0
      (((List.range' a (w - a)).flatMap (wordDens db forb.toList bLow bHigh)).filter keep) st ∧
        PosAt forb cur w) :
    a ≤ w ∧ w ≤ e ∧ w = e ∧ BlockInv process P L κ Q st0 (((List.range' a (w - a + 1)).flatMap
      (wordDens db forb.toList bLow bHigh)).filter keep) st' ∧ True :=
  have h' := BlockInv.append_range'_of_eq ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
    (BlockPost.wordDens_of_eq hx hs) hq hwe
  ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2, trivial⟩

theorem wordsBlockInvariant_append_of_ne
    (hx : x = wordBits db forb.toList bLow bHigh w ∧ PosAt forb cur' (w + 1))
    (hs : BlockPost process P L κ Q ((((List.range 64).filter x.toBitVec.getLsbD).map
      (HAdd.hAdd (64 * w))).filter keep) st st') (hq : ¬st'.1.quit = true) (hwe : ¬w = e)
    (h : e - w = mb ∧ o = none ∧ a ≤ w ∧ w ≤ e ∧ BlockInv process P L κ Q st0
      (((List.range' a (w - a)).flatMap (wordDens db forb.toList bLow bHigh)).filter keep) st ∧
        PosAt forb cur w) :
    e - (w + 1) < mb ∧ a ≤ w + 1 ∧ w + 1 ≤ e ∧ BlockInv process P L κ Q st0
      (((List.range' a (w + 1 - a)).flatMap (wordDens db forb.toList bLow bHigh)).filter keep) st' ∧
        PosAt forb cur' (w + 1) :=
  have h' := BlockInv.append_range'_of_ne ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1⟩
    (BlockPost.wordDens_of_eq hx hs) hq hwe
  ⟨h'.1, h'.2.1, h'.2.2.1, h'.2.2.2, hx.2⟩

end Words

attribute [local irreducible] BlockInv BlockPost WalkWhileInvariant in
open Std.WP Lean.Order in
/-- The loop of the word shape over the words `a ≤ e` of a block, with the first and last words of
the run `bLow / 64` and `bHigh / 64` and forbidden divisors that have what the loop needs
(`Ratpoints.Sieve.ForbFits`), for a step that delivers the lists of `L`, keeps `Q` and counts `κ b`
for each denominator `b` with `D b`: the denominators of the words (`Ratpoints.Sieve.wordDens`) that
pass the tests `test`, in order; the positions of the divisors step on with the words
(`Ratpoints.Sieve.posAt_forbStarts`, `Ratpoints.Sieve.denWord_spec`), and the loop ends, since the
words left decrease. -/
theorem wordsBlock_spec (step : Nat → BlockState σ → Id (BlockState σ)) (D : Nat → Prop)
    {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int)) (κ : Nat → Counters)
    (Q : RowStore → Prop)
    (hstep : ∀ b st, ⦃ D b ∧ st.1.quit = false ∧ Q st.2.1 ⦄ step b st
      ⦃ fun st' ↦ BlockPost process P L κ Q [b] st st' ⦄)
    (forb : Array ForbiddenEntry) (test : Nat → Id Bool) (db : UInt64)
    (lo0 hi0 bLow bHigh a e : Nat) (st : BlockState σ) :
    ⦃ st.1.quit = false ∧ Q st.2.1 ∧ a ≤ e ∧ lo0 = bLow / 64 ∧ hi0 = bHigh / 64 ∧
        ForbFits forb.toList ∧ ∀ b ∈ ((List.range' a (e + 1 - a)).flatMap
          (wordDens db forb.toList bLow bHigh)).filter (fun b ↦ Id.run (test b)), D b ⦄
    wordsBlock step forb test db lo0 hi0 bLow bHigh a e st
    ⦃ fun st' ↦ BlockPost process P L κ Q (((List.range' a (e + 1 - a)).flatMap
        (wordDens db forb.toList bLow bHigh)).filter fun b ↦ Id.run (test b)) st st' ⦄ := by
  vcgen [wordsBlock, denWord_spec, walkDens_spec process step D P L κ Q hstep test] invariants
  | inv1 => WordsBlockInvariant process P L κ Q (fun b ↦ Id.run (test b)) db forb bLow bHigh st a e
  | inv2 => .ofMeasure fun s ↦ e - s.2.2.2
  all_goals simp only [WordsBlockInvariant, WhileInvariant.mk_apply,
    Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure,
    meet_prop_eq_and, ofProp_prop_eq, reduceCtorEq, false_and, or_false, false_or, true_and,
    and_false, Option.some.injEq, exists_eq_left', exists_false, ↓reduceIte, Nat.add_zero,
    forall_const, false_implies] at *
  all_goals obtain ⟨hq0, hQ0, hae, rfl, rfl, hforb, hD⟩ := ‹st.1.quit = false ∧ _›
  all_goals first
    | exact wordsBlockInvariant_init hae hq0 hQ0 hforb
    | exact BlockPost.of_eq_some ‹_› ‹_›
    | exact BlockPost.of_eq_none_words ‹_› ‹_›
    | exact wordsBlockInvariant_pre_denWord hforb ‹_›
    | exact wordsBlockInvariant_pre_walk hD ‹_› ‹_›
    | exact wordsBlockInvariant_post_of_quit ‹_› ‹_› ‹_› ‹_›
    | exact wordsBlockInvariant_append_of_eq ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact wordsBlockInvariant_append_of_ne ‹_› ‹_› ‹_› ‹_› ‹_›

/-! ### The loop of a shape over a block -/

/-- The denominators of the step `k` of the segment `seg` of the shape `shape` for the
denominators `bLow, …, bHigh`, before the tests of the shape on a single denominator: the square
`k ^ 2`, the product `s k ^ 2` with the divisor `s` of the segment, the denominators of the word `k`
that the class test and the forbidden divisors tested with words leave
(`Ratpoints.Sieve.wordDens`, with the word `db` of the classes that admit a numerator), and `k`
itself. -/
def Shape.stepDens (shape : Shape) (db : UInt64) (bLow bHigh seg k : Nat) : List Nat :=
  match shape with
  | .squares => [k * k]
  | .squares1 _ divisors => [divisors[seg]! * k * k]
  | .words forb .. => wordDens db forb bLow bHigh k
  | .all => [k]

/-- The forbidden divisors tested with words of the word shape have what the loop of a block over
the words needs (`Ratpoints.Sieve.ForbFits`); the other shapes have none. -/
def Shape.ForbFits : Shape → Prop
  | .words forb .. => Sieve.ForbFits forb
  | _ => True

/-- What the loop of the shape over a block of the blocks `plan` for the denominators
`bLow, …, bHigh` needs: for the word shape, forbidden divisors that have what the loop needs
(`Ratpoints.Sieve.ForbFits`) and the first segment of the blocks from the word of `bLow` to that of
`bHigh`, the first and last words of the run, which the masks compare with; nothing for the other
shapes. -/
def Shape.LoopFits (plan : BlockPlan) (bLow bHigh : Nat) : Shape → Prop
  | .words forb .. => Sieve.ForbFits forb ∧ plan.segs[0]! = (bLow / 64, bHigh / 64)
  | _ => True

theorem run_keep_squares1 (info : List Setup.DenInfo) (divisors : List Nat)
    (cls : Vector NumClass 64) (b : Nat) :
    Id.run ((Shape.squares1 info divisors).keep cls b) =
      (cls[b % 64]!.bits != 0 && Id.run (denInfoTest info b)) := by
  simp only [Shape.keep]
  split <;> simp_all

theorem filter_flatMap_stepDens_squares (db : UInt64) (cls : Vector NumClass 64)
    (bLow bHigh seg : Nat) (l : List Nat) :
    (l.flatMap (Shape.squares.stepDens db bLow bHigh seg)).filter
        (fun b ↦ Id.run (Shape.squares.keep cls b)) =
      (l.map fun k ↦ k * k).filter fun b ↦ cls[b % 64]!.bits != 0 := by
  rw [List.map_eq_flatMap]
  rfl

theorem filter_flatMap_stepDens_squares1 (info : List Setup.DenInfo) (divisors : List Nat)
    (db : UInt64) (cls : Vector NumClass 64) (bLow bHigh seg : Nat) (l : List Nat) :
    (l.flatMap ((Shape.squares1 info divisors).stepDens db bLow bHigh seg)).filter
        (fun b ↦ Id.run ((Shape.squares1 info divisors).keep cls b)) =
      (l.map fun k ↦ divisors[seg]! * k * k).filter
        fun b ↦ cls[b % 64]!.bits != 0 && Id.run (denInfoTest info b) := by
  rw [List.map_eq_flatMap]
  exact List.filter_congr fun b _ ↦ run_keep_squares1 info divisors cls b

open Std.WP Lean.Order in
/-- The loop of the shape over the steps `a ≤ e` of a block of the segment `seg`, each denominator
that passes the tests of the shape handed to a step that delivers `L b`, keeps `Q` and counts `κ b`,
for the denominators of the steps (`Ratpoints.Sieve.Shape.stepDens`) that pass the tests of the
shape (`Ratpoints.Sieve.Shape.keep`), in order; for the word shape, with the first and last words of
the run as the first segment of the blocks and forbidden divisors that have what the loop needs. -/
theorem Shape.blockLoop_spec (shape : Shape) (step : Nat → BlockState σ → Id (BlockState σ))
    (D : Nat → Prop) {ι : Type} (P : ι → Prop) (L : ι → Nat → List (Int × Int × Int))
    (κ : Nat → Counters)
    (Q : RowStore → Prop)
    (hstep : ∀ b st, ⦃ D b ∧ st.1.quit = false ∧ Q st.2.1 ⦄ step b st
      ⦃ fun st' ↦ BlockPost process P L κ Q [b] st st' ⦄)
    (cls : Vector NumClass 64) (db : UInt64) (plan : BlockPlan) (seg a e bLow bHigh : Nat)
    (st : BlockState σ) :
    ⦃ st.1.quit = false ∧ Q st.2.1 ∧ a ≤ e ∧ shape.LoopFits plan bLow bHigh ∧
        ∀ b ∈ ((List.range' a (e + 1 - a)).flatMap (shape.stepDens db bLow bHigh seg)).filter
          (fun b ↦ Id.run (shape.keep cls b)), D b ⦄
    shape.blockLoop step cls db plan seg a e bLow bHigh st
    ⦃ fun st' ↦ BlockPost process P L κ Q (((List.range' a (e + 1 - a)).flatMap
        (shape.stepDens db bLow bHigh seg)).filter fun b ↦ Id.run (shape.keep cls b)) st st' ⦄ := by
  rcases shape with _ | ⟨info, divisors⟩ | ⟨forb, forbVal, useJacobi, fast, lcf⟩ | _ <;>
    refine ⟨fun ⟨hq, hQ, hae, hf, hD⟩ ↦ ?_⟩ <;> simp only [Shape.blockLoop]
  · rw [filter_flatMap_stepDens_squares] at hD ⊢
    exact (squaresBlock_spec process step D P L κ Q hstep cls a e st).le_wp ⟨hq, hQ, hD⟩
  · rw [filter_flatMap_stepDens_squares1] at hD ⊢
    exact (squares1Block_spec process step D P L κ Q hstep cls info divisors[seg]! a e st).le_wp
      ⟨hq, hQ, hD⟩
  · rw [hf.2]
    exact (wordsBlock_spec process step D P L κ Q hstep forb.toArray _ db _ _ bLow bHigh a e
      st).le_wp
      ⟨hq, hQ, hae, rfl, rfl, hf.1, hD⟩
  · exact (allBlock_spec process step D P L κ Q hstep cls a e st).le_wp ⟨hq, hQ, hae,
      fun b hb ↦ hD b (by simpa [Shape.stepDens, Shape.keep] using hb)⟩

/-! ### The decision in force for a block -/

-- The search for the decision in force for block `i` goes back while the first block of the
-- decision is above `i`, which is then not the first decision.
private theorem findDecision_back {decs : Array Decision} {i dd : Nat} (h0 : decs[0]!.block = 0)
    (hi : i < decs[dd]!.block)
    (h : dd < decs.size ∧ ∀ j, dd < j → j < decs.size → i < decs[j]!.block) :
    dd - 1 < dd ∧ dd - 1 < decs.size ∧ ∀ j, dd - 1 < j → j < decs.size → i < decs[j]!.block := by
  have hd : dd ≠ 0 := by rintro rfl; rw [h0] at hi; lia
  refine ⟨by lia, by lia, fun j h1 h2 ↦ ?_⟩
  rcases Nat.lt_or_ge dd j with h3 | h3
  · exact h.2 j h3 h2
  · rwa [show j = dd by lia]

/-- The invariant of the search of `Ratpoints.Sieve.findDecision` for the decision in force for
block `i`, whose state is the index `dd` of a decision: every later decision is for a block after
`i`, and at the exit the decision `dd` is for a block at most `i`. -/
def DecisionSearchInvariant (decs : Array Decision) (i : Nat) : Std.WP.WhileInvariant Nat Prop :=
  .mk fun exit dd ↦ dd < decs.size ∧ (∀ j, dd < j → j < decs.size → i < decs[j]!.block) ∧
    (exit = true → decs[dd]!.block ≤ i)

open Std.WP Lean.Order in
/-- For decisions of which the first is for block `0`, the decision in force for block `i` is the
last whose first block is at most `i`: the search from the last decision back ends there, at the
first decision at the latest. -/
theorem findDecision_spec (decs : Array Decision) (i : Nat) :
    ⦃ 0 < decs.size ∧ decs[0]!.block = 0 ⦄ findDecision decs i
    ⦃ fun dd ↦ dd < decs.size ∧ decs[dd]!.block ≤ i ∧
        ∀ j, dd < j → j < decs.size → i < decs[j]!.block ⦄ := by
  vcgen [findDecision] invariants
  | inv1 => DecisionSearchInvariant decs i
  | inv2 => .ofMeasure fun dd ↦ dd
  all_goals simp only [DecisionSearchInvariant, WhileInvariant.mk_apply, Variant.evalsTo_ofMeasure,
    Variant.evalsBelow_ofMeasure_nat, Assertion.NondetFun.evalsTo_pure, meet_prop_eq_and,
    ofProp_prop_eq, true_implies, false_implies, Bool.false_eq_true, and_true] at *
  all_goals first
    | exact ⟨by lia, fun j h1 h2 ↦ absurd h2 (by lia)⟩
    | exact ⟨‹_ ∧ _ ∧ _›.1, ‹_ ∧ _ ∧ _›.2.2, ‹_ ∧ _ ∧ _›.2.1⟩
    | (rename_i hi h
       obtain ⟨rfl, h⟩ := h
       exact findDecision_back ‹_ ∧ _›.2 hi h)
    | (rename_i hi h
       exact ⟨h.2.1, h.2.2, Nat.le_of_not_lt hi⟩)

end Sieve

end Ratpoints

end
