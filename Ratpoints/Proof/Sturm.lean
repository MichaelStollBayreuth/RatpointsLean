/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Sturm
public import Std.WP

import Ratpoints.Proof.Bits
import Std.Tactic.Do

/-!
# The contract of the remainder chain

The steps of the remainder chain `Ratpoints.Sturm.chain` as plain functions, by well-founded
recursion where the model has a loop, the predicate of a remainder chain, and the contract of the
chain as a `@[spec]` theorem proved with `vcgen`, the program logic of Lean core, with loop
invariants that are named definitions.

## Main definitions

* `Ratpoints.Sturm.dropZeros`, `Ratpoints.Sturm.reduceOnce`, `Ratpoints.Sturm.fullReduce`: the zero
  leading coefficients of a remainder dropped, one reduction step followed by that drop, and the
  reduction of a remainder until its degree is below that of the divisor, `#[]` when it becomes
  zero.
* `Ratpoints.Sturm.content`, `Ratpoints.Sturm.normalize`: the gcd of the coefficients of a
  remainder, and the remainder negated and divided by it.
* `Ratpoints.Sturm.IsChain`: a remainder chain of a polynomial and its derivative.
* `Ratpoints.Sturm.IsChainResult`: the result of the chain as its contract states it, a chain whose
  last row is constant, or `none` when a chain reduces to zero.

## Main statements

* `Ratpoints.Sturm.chain_spec`: the loops of `Ratpoints.Sturm.chain` end, and its result satisfies
  `Ratpoints.Sturm.IsChainResult`; `Ratpoints.Sturm.isChainResult_run_chain` states this without
  the program logic.
* `Ratpoints.Sturm.IsChain.size_le`: a chain of a polynomial of degree `d` has at most `d + 1` rows.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Words` does; the lemmas on arrays,
lists, ranges and integers that are not about the model are in `Ratpoints.Proof.Bits`. The plain
statement `Ratpoints.Sturm.isChainResult_run_chain` lets the files with Mathlib use the contract
without the program logic.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sturm

/-! ### The steps of the chain -/

/-- The array `t` with its zero entries on top dropped, the zero leading coefficients of a
remainder: the loop of `Ratpoints.Sturm.chain` after a reduction step. -/
def dropZeros (t : Array Int) : Array Int :=
  if (t.back? == some 0) = true then dropZeros t.pop else t
termination_by t.size
decreasing_by exact Array.size_pop_lt_of_back?_eq_some (beq_iff_eq.mp ‹_›)

theorem dropZeros_of_beq {t : Array Int} (h : (t.back? == some 0) = true) :
    dropZeros t = dropZeros t.pop := by
  rw [dropZeros, ite_eq_left h]

theorem dropZeros_of_not_beq {t : Array Int} (h : ¬(t.back? == some 0) = true) :
    dropZeros t = t := by
  rw [dropZeros, ite_eq_right h]

theorem size_dropZeros_le (t : Array Int) : (dropZeros t).size ≤ t.size := by
  fun_induction dropZeros t with
  | case1 t h ih =>
    have := Array.size_pop_lt_of_back?_eq_some (beq_iff_eq.mp h)
    lia
  | case2 => exact Nat.le_refl _

theorem back!_dropZeros_ne_zero {t : Array Int} (h : (dropZeros t).size ≠ 0) :
    (dropZeros t).back! ≠ 0 := by
  fun_induction dropZeros t with
  | case1 t _ ih => exact ih h
  | case2 t h' => exact Array.back!_ne_of_back?_ne h (by simpa using h')

theorem getElem!_dropZeros (t : Array Int) (i : Nat) : (dropZeros t)[i]! = t[i]! := by
  fun_induction dropZeros t with
  | case1 t h ih =>
    rw [ih, Array.getElem!_pop_of_back!_eq (by rw [Array.back!_eq_back?, beq_iff_eq.mp h]; rfl)]
  | case2 => rfl

theorem size_reduce (s t : Array Int) : (reduce s t).size = t.size - 1 + 1 := by
  simp [reduce]

/-- The entries of the reduction of `t` by `s`, `deg t ≥ deg s`: `u t - v X^(deg t - deg s) s` with
`u > 0` and `u lc t = v lc s`, so that the leading entry cancels. -/
theorem exists_getElem!_reduce {s t : Array Int} (hle : s.size ≤ t.size) (hs : s.back! ≠ 0) :
    ∃ u v : Int, 0 < u ∧ u * t.back! = v * s.back! ∧ ∀ n, (reduce s t)[n]! =
      u * t[n]! - v * if t.size - s.size ≤ n then s[n - (t.size - s.size)]! else 0 := by
  -- `hs1` halves the time of the `grind` at the end
  have hs1 := Array.size_ne_zero_of_back!_ne hs
  simp only [reduce]
  generalize hg : ((Int.gcd s.back! t.back! : Nat) : Int) = g
  have hds : g ∣ s.back! := hg ▸ Int.gcd_dvd_left ..
  have key := Int.ediv_mul_eq_ediv_mul_of_dvd hds (hg ▸ Int.gcd_dvd_right ..)
  have hu := Int.ediv_ne_zero_of_dvd hds hs
  refine ⟨if s.back! / g < 0 then -(s.back! / g) else s.back! / g,
    if s.back! / g < 0 then -(t.back! / g) else t.back! / g, by split <;> lia,
    by split <;> first | exact key | rw [Int.neg_mul, Int.neg_mul, key], fun n ↦ ?_⟩
  by_cases hn : n < t.size <;> grind [Array.getElem!_map_range, Int.default_eq_zero]

theorem back!_reduce {s t : Array Int} (hle : s.size ≤ t.size) (hs : s.back! ≠ 0) :
    (reduce s t).back! = 0 := by
  obtain ⟨u, v, -, huv, h⟩ := exists_getElem!_reduce hle hs
  have hs1 := Array.size_ne_zero_of_back!_ne hs
  grind [Array.back!_eq_getElem!, size_reduce]

/-- One reduction of `t` by `s` with the leading entry, which cancels, dropped, and then the zeros
on top: one pass of the reduction loop of `Ratpoints.Sturm.chain`. -/
def reduceOnce (s t : Array Int) : Array Int :=
  dropZeros (reduce s t).pop

theorem exists_getElem!_reduceOnce {s t : Array Int} (hle : s.size ≤ t.size) (hs : s.back! ≠ 0) :
    ∃ u v : Int, 0 < u ∧ ∀ n, (reduceOnce s t)[n]! =
      u * t[n]! - v * if t.size - s.size ≤ n then s[n - (t.size - s.size)]! else 0 := by
  obtain ⟨u, v, hu, -, h⟩ := exists_getElem!_reduce hle hs
  refine ⟨u, v, hu, fun n ↦ ?_⟩
  rw [reduceOnce, getElem!_dropZeros, Array.getElem!_pop_of_back!_eq (back!_reduce hle hs), h]

theorem size_reduceOnce_lt {s t : Array Int} (h : (reduceOnce s t).size ≠ 0) :
    (reduceOnce s t).size < t.size := by
  have := size_dropZeros_le (reduce s t).pop
  rw [Array.size_pop, size_reduce] at this
  rw [reduceOnce] at h ⊢
  lia

/-- The reduction loop of `Ratpoints.Sturm.chain`: `t` reduced by `s` until its size is below that
of `s`, and `#[]` when a reduction leaves nothing, where the chain returns `none`. -/
def fullReduce (s t : Array Int) : Array Int :=
  if s.size ≤ t.size then
    if (reduceOnce s t).size = 0 then #[] else fullReduce s (reduceOnce s t)
  else t
termination_by t.size
decreasing_by exact size_reduceOnce_lt ‹_›

theorem fullReduce_of_lt {s t : Array Int} (h : t.size < s.size) : fullReduce s t = t := by
  rw [fullReduce, ite_eq_right (by lia)]

theorem fullReduce_of_size_eq_zero {s t : Array Int} (hle : s.size ≤ t.size)
    (h : (reduceOnce s t).size = 0) : fullReduce s t = #[] := by
  rw [fullReduce, ite_eq_left hle, ite_eq_left h]

theorem fullReduce_of_size_ne_zero {s t : Array Int} (hle : s.size ≤ t.size)
    (h : (reduceOnce s t).size ≠ 0) : fullReduce s t = fullReduce s (reduceOnce s t) := by
  rw [fullReduce, ite_eq_left hle, ite_eq_right h]

/-- The gcd of the entries of `t`, the loop of `Ratpoints.Sturm.chain` over the coefficients of a
remainder, there with a `break` once the gcd is `1`. -/
def content (t : Array Int) : Nat :=
  t.foldl (fun g a ↦ g.gcd a.natAbs) 0

/-- The array `t` negated and divided by the gcd of its entries: the change of sign and the
division of a remainder by the gcd of its coefficients in `Ratpoints.Sturm.chain`. -/
def normalize (t : Array Int) : Array Int :=
  (t.map Neg.neg).map fun x ↦ x / (content (t.map Neg.neg) : Int)

theorem natCast_content_dvd_getElem! (t : Array Int) (i : Nat) : (content t : Int) ∣ t[i]! := by
  by_cases hi : i < t.size
  · rw [content, ← Array.foldl_toList, getElem!_pos t i hi]
    exact Int.ofNat_dvd_left.mpr
      (List.foldl_gcd_natAbs_dvd_natAbs 0 (Array.mem_def.mp (Array.getElem_mem hi)))
  · rw [getElem!_neg t i hi]
    exact Int.dvd_zero _

theorem size_normalize (t : Array Int) : (normalize t).size = t.size := by
  simp [normalize]

theorem mul_getElem!_normalize (t : Array Int) (i : Nat) :
    (content (t.map Neg.neg) : Int) * (normalize t)[i]! = -t[i]! := by
  rw [normalize, Array.getElem!_map (f := (· / _)) (Int.zero_ediv _),
    Int.mul_ediv_cancel' (natCast_content_dvd_getElem! _ i), Array.getElem!_map Int.neg_zero]

theorem content_map_neg_ne_zero {t : Array Int} (h : (normalize t).back! ≠ 0) :
    content (t.map Neg.neg) ≠ 0 := fun h0 ↦
  h (by rw [normalize, h0, Array.back!_map (f := (· / _)) (Int.zero_ediv _)]; simp)

theorem back!_normalize_ne_zero {t : Array Int} (h : t.back! ≠ 0) : (normalize t).back! ≠ 0 := by
  have hd := natCast_content_dvd_getElem! (t.map Neg.neg) (t.size - 1)
  grind [normalize, Array.back!_eq_getElem!, Int.ediv_ne_zero_of_dvd]

/-! ### Remainder chains -/

/-- The rows `ch` are a remainder chain of the polynomial `f` of degree `d` with the coefficients
`c₀, …, c_d`, the entries of `c`, as `Ratpoints.Sturm.chain` computes it. -/
structure IsChain (c : List Int) (d : Nat) (ch : Array (Array Int)) : Prop where
  /-- The chain has `f` and `f'` at least. -/
  two_le_size : 2 ≤ ch.size
  /-- The first row is `f`, the coefficients `c₀, …, c_d`. -/
  getElem!_zero : ch[0]! = (Array.range (d + 1)).map fun x ↦ c.getD x 0
  /-- The second row is `f'`, the coefficients `(n + 1) c_(n+1)` for `n < d`. -/
  getElem!_one : ch[1]! = (Array.range d).map fun n ↦ ((n + 1 : Nat) : Int) * c.getD (n + 1) 0
  /-- Each further row is the full reduction of the row two before by the row before, negated and
  divided by the gcd of its entries. -/
  getElem!_add_two (k : Nat) (hk : k + 2 < ch.size) :
    ch[k + 2]! = normalize (fullReduce ch[k + 1]! ch[k]!)
  /-- Every row has a nonzero last entry, its leading coefficient. -/
  back!_ne_zero (k : Nat) (hk : k < ch.size) : ch[k]!.back! ≠ 0
  /-- The sizes decrease strictly from `f'` on. -/
  size_lt (k : Nat) (hk : k + 2 < ch.size) : ch[k + 2]!.size < ch[k + 1]!.size

/-- The result of `Ratpoints.Sturm.chain` as its contract states it: `some ch` for a chain `ch`
whose last row is constant; `none` when there is a chain whose last row is not constant and reduces
the row before it to zero, which `Ratpoints.Sturm.fullReduce` gives as `#[]`. -/
def IsChainResult (c : List Int) (d : Nat) : Option (Array (Array Int)) → Prop
  | none => ∃ ch, IsChain c d ch ∧ 2 ≤ ch.back!.size ∧ fullReduce ch.back! ch[ch.size - 2]! = #[]
  | some ch => IsChain c d ch ∧ ch.back!.size = 1

theorem isChain_init {c : List Int} {d : Nat} (hd : 1 ≤ d) (hc : c.getD d 0 ≠ 0) :
    IsChain c d #[(Array.range (d + 1)).map fun x ↦ c.getD x 0,
      (Array.range d).map fun n ↦ ((n + 1 : Nat) : Int) * c.getD (n + 1) 0] := by
  refine ⟨by simp, by simp, by simp, fun k hk ↦ absurd hk (by simp), fun k hk ↦ ?_,
    fun k hk ↦ absurd hk (by simp)⟩
  obtain rfl | rfl : k = 0 ∨ k = 1 := by simp at hk; lia
  · simpa [Array.back!_map_range _ (Nat.succ_ne_zero d)] using hc
  · simpa [Array.back!_map_range _ (by lia : d ≠ 0), Nat.sub_add_cancel hd] using
      Int.mul_ne_zero (by lia) hc

theorem IsChain.push {c : List Int} {d : Nat} {ch : Array (Array Int)} {t : Array Int}
    (h : IsChain c d ch) (ht : fullReduce ch.back! ch[ch.size - 2]! = t) (ht0 : t.back! ≠ 0)
    (hlt : t.size < ch.back!.size) : IsChain c d (ch.push (normalize t)) := by
  obtain ⟨m, hm⟩ : ∃ m, ch.size = m + 2 := ⟨ch.size - 2, by have := h.two_le_size; lia⟩
  have hp {i : Nat} (hi : i < m + 2) : (ch.push (normalize t))[i]! = ch[i]! :=
    Array.getElem!_push_lt (hm ▸ hi)
  have hn : (ch.push (normalize t))[m + 2]! = normalize t := hm ▸ Array.getElem!_push_eq
  simp only [Array.back!_eq_getElem!, hm, show m + 2 - 1 = m + 1 by lia,
    show m + 2 - 2 = m by lia] at ht hlt
  refine ⟨by simp [hm], by rw [hp (by lia), h.getElem!_zero], by rw [hp (by lia), h.getElem!_one],
    fun k hk ↦ ?_, fun k hk ↦ ?_, fun k hk ↦ ?_⟩ <;> rw [Array.size_push, hm] at hk
  · rcases Nat.lt_succ_iff_lt_or_eq.mp (by lia : k < m + 1) with hk' | rfl
    · rw [hp (by lia), hp (by lia), hp (by lia), h.getElem!_add_two k (by lia)]
    · rw [hn, hp (by lia), hp (by lia), ht]
  · rcases Nat.lt_succ_iff_lt_or_eq.mp hk with hk' | rfl
    · exact hp hk' ▸ h.back!_ne_zero k (hm ▸ hk')
    · exact (congrArg Array.back! hn).symm ▸ back!_normalize_ne_zero ht0
  · rcases Nat.lt_succ_iff_lt_or_eq.mp (by lia : k < m + 1) with hk' | rfl
    · rw [hp (by lia), hp (by lia)]
      exact h.size_lt k (by lia)
    · rw [hn, hp (by lia), size_normalize]
      exact hlt

/-- The row `k + 1` of a chain has at most `d - k` entries: the sizes drop by one at least from
`f'` on. -/
theorem IsChain.size_getElem!_add_one_add_le {c : List Int} {d : Nat} {ch : Array (Array Int)}
    (h : IsChain c d ch) {k : Nat} (hk : k + 1 < ch.size) : ch[k + 1]!.size + k ≤ d := by
  induction k with
  | zero => simp [h.getElem!_one]
  | succ k ih => grind [h.size_lt k hk]

/-- A chain has at most `d + 1` rows, the rows of the table of the C code. -/
theorem IsChain.size_le {c : List Int} {d : Nat} {ch : Array (Array Int)} (h : IsChain c d ch) :
    ch.size ≤ d + 1 := by
  have := h.two_le_size
  have := h.size_getElem!_add_one_add_le (k := ch.size - 2) (by lia)
  have := Array.size_ne_zero_of_back!_ne (h.back!_ne_zero (ch.size - 2 + 1) (by lia))
  lia

/-! ### The invariants -/

/-- The rows while the loop of `Ratpoints.Sturm.chain` over `k` runs, after the indices `pref`, with
the indices `suff` still to come: a chain (`Ratpoints.Sturm.IsChain`), whose last row is constant
once no index is left; while indices are left, one row for each index done after `f` and `f'`, the
last one not constant, its size and the number of rows adding up to at most `d + 2`. -/
def ChainLoopInvariant (c : List Int) (d : Nat) (pref suff : List Nat)
    (ch : Array (Array Int)) : Prop :=
  IsChain c d ch ∧ (suff = [] → ch.back!.size = 1) ∧
    (suff ≠ [] → ch.size = pref.length + 2 ∧ 2 ≤ ch.back!.size ∧ ch.back!.size + ch.size ≤ d + 2)

/-- The invariant of the loop of `Ratpoints.Sturm.chain` over `k`, on the pair of the value of an
early `return` and the rows: no `return` yet and `Ratpoints.Sturm.ChainLoopInvariant`, or the
`return` of `none`, which ends the loop, with the result `none` of the contract. -/
def ChainInvariant (c : List Int) (d : Nat) (pref suff : List Nat)
    (x : Option (Option (Array (Array Int))) × Array (Array Int)) : Prop :=
  x.1 = none ∧ ChainLoopInvariant c d pref suff x.2 ∨
    suff = [] ∧ x.1 = some none ∧ IsChainResult c d none

/-- The invariant of the reduction loop of `Ratpoints.Sturm.chain` of `t₀` by `s`, on the pair of
the value of an early `return` and the remainder: no `return`, the same full reduction as `t₀`, a
nonzero last entry, and at the exit a size below that of `s`; or, at the exit, the `return` of
`none`, when the full reduction of `t₀` leaves nothing. -/
def ReduceInvariant (s t₀ : Array Int) (exit : Bool)
    (x : Option (Option (Array (Array Int))) × Array Int) : Prop :=
  x.1 = none ∧ fullReduce s x.2 = fullReduce s t₀ ∧ x.2.back! ≠ 0 ∧
      (exit = true → x.2.size < s.size) ∨
    exit = true ∧ x.1 = some none ∧ fullReduce s t₀ = #[]

/-- The invariant of the loop of `Ratpoints.Sturm.chain` that drops the zeros on top of `t₀`: the
same result of `Ratpoints.Sturm.dropZeros`, and no zero on top at the exit. -/
def DropZerosInvariant (t₀ : Array Int) (exit : Bool) (t : Array Int) : Prop :=
  dropZeros t = dropZeros t₀ ∧ (exit = true → ¬(t.back? == some 0) = true)

/-- The invariant of the loop of `Ratpoints.Sturm.chain` over the entries of a remainder: the gcd of
the entries `pref` done, the `break` at `1` included. -/
def ContentInvariant (pref : List Int) (g : Nat) : Prop :=
  g = pref.foldl (fun g a ↦ g.gcd a.natAbs) 0

/-! ### The verification conditions, one lemma each in the shape `vcgen` states it -/

theorem chainInvariant_init {c : List Int} {d : Nat} (h : 1 ≤ d ∧ c.getD d 0 ≠ 0) :
    ChainInvariant c d [] (ForIn.toList [2:d + 1])
      (none, #[(Array.range (d + 1)).map fun x ↦ c.getD x 0,
        (Array.range d).map fun n ↦ ((n + 1 : Nat) : Int) * c.getD (n + 1) 0]) := by
  have hl : ForIn.toList [2:d + 1] = List.range' 2 (d - 1) := by simp [Std.Legacy.Range.size]
  refine .inl ⟨rfl, isChain_init h.1 h.2, fun h0 ↦ ?_, fun h0 ↦ ?_⟩
  · rw [hl, List.range'_eq_nil_iff] at h0
    simp [Array.back!_eq_getElem!]
    lia
  · have : d - 1 ≠ 0 := fun h1 ↦ h0 (by rw [hl, h1]; rfl)
    simp [Array.back!_eq_getElem!]
    lia

theorem ChainInvariant.isChainResult {c : List Int} {d : Nat} {pref suff : List Nat}
    {y : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    {a : Option (Array (Array Int))} (h : ChainInvariant c d pref suff (y, ch)) (hy : y = some a) :
    IsChainResult c d a := by
  rcases h with ⟨hy', -⟩ | ⟨-, hy', h⟩
  · cases hy.symm.trans hy'
  · obtain rfl := Option.some.inj (hy.symm.trans hy')
    exact h

theorem ChainInvariant.isChainResult_some {c : List Int} {d : Nat} {pref : List Nat}
    {y : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    (h : ChainInvariant c d pref [] (y, ch)) (hy : y = none) : IsChainResult c d (some ch) := by
  rcases h with ⟨-, h⟩ | ⟨-, hy', -⟩
  · exact ⟨h.1, h.2.1 rfl⟩
  · cases hy.symm.trans hy'

theorem ChainInvariant.chainLoopInvariant {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {y : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    (h : ChainInvariant c d pref (cur :: suff) (y, ch)) :
    y = none ∧ ChainLoopInvariant c d pref (cur :: suff) ch :=
  h.resolve_right fun h ↦ List.cons_ne_nil _ _ h.1

/-- At the index `cur`, the chain has `cur` rows: the reduction is of the row `cur - 2` by the row
`cur - 1`, the last one. -/
theorem ChainLoopInvariant.size_eq {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {ch : Array (Array Int)} (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainLoopInvariant c d pref (cur :: suff) ch) : ch.size = cur := by
  have := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have := (h.2.2 (List.cons_ne_nil _ _)).1
  lia

theorem ChainInvariant.reduceInvariant {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {y : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainInvariant c d pref (cur :: suff) (y, ch)) :
    ReduceInvariant ch[cur - 1]! ch[cur - 2]! false (none, ch[cur - 2]!) := by
  obtain ⟨-, h⟩ := h.chainLoopInvariant
  have := h.size_eq hl
  exact .inl ⟨rfl, rfl, h.1.back!_ne_zero _ (by have := h.1.two_le_size; lia), nofun⟩

theorem ChainInvariant.of_reduceInvariant_some {c : List Int} {d : Nat} {pref : List Nat}
    {cur : Nat} {suff : List Nat} {y z : Option (Option (Array (Array Int)))}
    {ch : Array (Array Int)} {t : Array Int} {a : Option (Array (Array Int))}
    (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainInvariant c d pref (cur :: suff) (y, ch))
    (ht : ReduceInvariant ch[cur - 1]! ch[cur - 2]! true (z, t)) (hz : z = some a) :
    ChainInvariant c d (ForIn.toList [2:d + 1]) [] (some a, ch) := by
  obtain ⟨-, h⟩ := h.chainLoopInvariant
  have hs := h.size_eq hl
  rcases ht with ⟨hz', -⟩ | ⟨-, hz', ht⟩
  · cases hz.symm.trans hz'
  · obtain rfl := Option.some.inj (hz.symm.trans hz')
    refine .inr ⟨rfl, rfl, ch, h.1, (h.2.2 (List.cons_ne_nil _ _)).2.1, ?_⟩
    rwa [Array.back!_eq_getElem!, hs]

/-- The step of the loop over `k`: the normalized full reduction `t` pushed onto the chain. -/
theorem ChainLoopInvariant.push {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {ch : Array (Array Int)} {t : Array Int}
    (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainLoopInvariant c d pref (cur :: suff) ch)
    (ht : fullReduce ch[cur - 1]! ch[cur - 2]! = t) (ht0 : t.back! ≠ 0)
    (hlt : t.size < ch[cur - 1]!.size) :
    IsChain c d (ch.push (normalize t)) ∧ (¬(normalize t).size = 1 →
      ChainLoopInvariant c d (pref ++ [cur]) suff (ch.push (normalize t))) := by
  have hs := h.size_eq hl
  have hlen := Std.Legacy.Range.length_add_length_add_one_of_toList_eq_append_cons hl
  have hcur := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  obtain ⟨-, hb2, hle⟩ := h.2.2 (List.cons_ne_nil _ _)
  rw [← hs, ← Array.back!_eq_getElem!] at ht hlt
  have hc := h.1.push ht ht0 hlt
  have ht1 := Array.size_ne_zero_of_back!_ne ht0
  refine ⟨hc, fun h1 ↦ ⟨hc, fun hsuff ↦ ?_, fun _ ↦ ?_⟩⟩ <;>
    simp only [Array.back!_push, Array.size_push, size_normalize, List.length_append,
      List.length_singleton] at h1 ⊢
  · simp only [hsuff, List.length_nil] at hlen
    lia
  · lia

theorem ChainInvariant.push_normalize {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {y : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    {t : Array Int} (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainInvariant c d pref (cur :: suff) (y, ch))
    (ht : ReduceInvariant ch[cur - 1]! ch[cur - 2]! true (none, t)) :
    ((normalize t).size = 1 →
        ChainInvariant c d (ForIn.toList [2:d + 1]) [] (none, ch.push (normalize t))) ∧
      (¬(normalize t).size = 1 →
        ChainInvariant c d (pref ++ [cur]) suff (none, ch.push (normalize t))) := by
  obtain ⟨-, h⟩ := h.chainLoopInvariant
  obtain ⟨-, hfr, ht0, hlt⟩ := ht.resolve_right (by simp)
  rw [fullReduce_of_lt (hlt rfl)] at hfr
  obtain ⟨hc, h'⟩ := h.push hl hfr.symm ht0 (hlt rfl)
  refine ⟨fun h1 ↦ .inl ⟨rfl, hc, fun _ ↦ ?_, fun h ↦ absurd rfl h⟩, fun h1 ↦ .inl ⟨rfl, h' h1⟩⟩
  rwa [Array.back!_push]

theorem contentInvariant_nil : ContentInvariant [] 0 :=
  rfl

theorem ContentInvariant.append {pref : List Int} {g : Nat} (h : ContentInvariant pref g)
    (cur : Int) : ContentInvariant (pref ++ [cur]) (g.gcd cur.natAbs) := by
  rw [ContentInvariant, List.foldl_append, ← h]
  rfl

theorem ContentInvariant.of_gcd_eq_one {xs pref suff : List Int} {cur : Int} {g : Nat}
    (hl : xs = pref ++ cur :: suff) (h : ContentInvariant pref g) (hg : g.gcd cur.natAbs = 1) :
    ContentInvariant xs (g.gcd cur.natAbs) := by
  rw [ContentInvariant, hl, List.foldl_append, List.foldl_cons, ← h, hg,
    List.foldl_gcd_natAbs_one]

theorem ContentInvariant.normalize_eq {t : Array Int} {g : Nat}
    (h : ContentInvariant (ForIn.toList (t.map Neg.neg)) g) :
    normalize t = (t.map Neg.neg).map fun x ↦ x / (g : Int) := by
  rw [ContentInvariant, Std.Internal.ForIn.toList_array, Array.foldl_toList] at h
  rw [normalize, content, h]

theorem ContentInvariant.normalize_eq_map_neg {t : Array Int} {g : Nat}
    (h : ContentInvariant (ForIn.toList (t.map Neg.neg)) g) (h1 : ¬¬g = 1) :
    normalize t = t.map Neg.neg := by
  rw [h.normalize_eq, Decidable.of_not_not h1]
  simp

theorem ChainInvariant.push_of_size_eq_one {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {y z : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    {t r : Array Int} (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainInvariant c d pref (cur :: suff) (y, ch))
    (ht : ReduceInvariant ch[cur - 1]! ch[cur - 2]! true (z, t)) (hz : z = none)
    (hr : normalize t = r) (h1 : r.size = 1) :
    ChainInvariant c d (ForIn.toList [2:d + 1]) [] (none, ch.push r) := by
  subst hz hr
  exact (h.push_normalize hl ht).1 h1

theorem ChainInvariant.push_of_size_ne_one {c : List Int} {d : Nat} {pref : List Nat} {cur : Nat}
    {suff : List Nat} {y z : Option (Option (Array (Array Int)))} {ch : Array (Array Int)}
    {t r : Array Int} (hl : ForIn.toList [2:d + 1] = pref ++ cur :: suff)
    (h : ChainInvariant c d pref (cur :: suff) (y, ch))
    (ht : ReduceInvariant ch[cur - 1]! ch[cur - 2]! true (z, t)) (hz : z = none)
    (hr : normalize t = r) (h1 : ¬r.size = 1) :
    ChainInvariant c d (pref ++ [cur]) suff (none, ch.push r) := by
  subst hz hr
  exact (h.push_normalize hl ht).2 h1

theorem dropZerosInvariant_self (t : Array Int) : DropZerosInvariant t false t :=
  ⟨rfl, nofun⟩

theorem DropZerosInvariant.pop {t₀ t : Array Int} {mb : Nat}
    (h : t.size = mb ∧ DropZerosInvariant t₀ false t) (hb : (t.back? == some 0) = true) :
    t.pop.size < mb ∧ DropZerosInvariant t₀ false t.pop := by
  obtain ⟨rfl, h⟩ := h
  exact ⟨Array.size_pop_lt_of_back?_eq_some (beq_iff_eq.mp hb),
    (dropZeros_of_beq hb).symm.trans h.1, nofun⟩

theorem DropZerosInvariant.exit {t₀ t : Array Int} {mb : Nat}
    (h : t.size = mb ∧ DropZerosInvariant t₀ false t) (hb : ¬(t.back? == some 0) = true) :
    DropZerosInvariant t₀ true t :=
  ⟨h.2.1, fun _ ↦ hb⟩

theorem DropZerosInvariant.eq_reduceOnce {s t t' : Array Int}
    (h : DropZerosInvariant (reduce s t).pop true t') : t' = reduceOnce s t :=
  (dropZeros_of_not_beq (h.2 rfl)).symm.trans h.1

theorem ReduceInvariant.of_size_eq_zero {s t₀ t t' : Array Int}
    {y : Option (Option (Array (Array Int)))} {mb : Nat}
    (h : t.size = mb ∧ ReduceInvariant s t₀ false (y, t)) (hle : s.size ≤ t.size)
    (hd : DropZerosInvariant (reduce s t).pop true t') (h0 : t'.size = 0) :
    ReduceInvariant s t₀ true (some none, t') := by
  obtain ⟨-, hfr, -, -⟩ := h.2.resolve_right (by simp)
  rw [hd.eq_reduceOnce] at h0
  exact .inr ⟨rfl, rfl, hfr ▸ fullReduce_of_size_eq_zero hle h0⟩

theorem ReduceInvariant.of_size_ne_zero {s t₀ t t' : Array Int}
    {y : Option (Option (Array (Array Int)))} {mb : Nat}
    (h : t.size = mb ∧ ReduceInvariant s t₀ false (y, t)) (hle : s.size ≤ t.size)
    (hd : DropZerosInvariant (reduce s t).pop true t') (h0 : ¬t'.size = 0) :
    t'.size < mb ∧ ReduceInvariant s t₀ false (none, t') := by
  obtain ⟨rfl, h⟩ := h
  obtain ⟨-, hfr, -, -⟩ := h.resolve_right (by simp)
  rw [hd.eq_reduceOnce] at h0 ⊢
  exact ⟨size_reduceOnce_lt h0, .inl ⟨rfl, (fullReduce_of_size_ne_zero hle h0).symm.trans hfr,
    back!_dropZeros_ne_zero h0, nofun⟩⟩

theorem ReduceInvariant.exit {s t₀ t : Array Int} {y : Option (Option (Array (Array Int)))}
    {mb : Nat} (h : t.size = mb ∧ ReduceInvariant s t₀ false (y, t)) (hlt : ¬s.size ≤ t.size) :
    ReduceInvariant s t₀ true (none, t) := by
  obtain ⟨-, hfr, ht0, -⟩ := h.2.resolve_right (by simp)
  exact .inl ⟨rfl, hfr, ht0, fun _ ↦ by lia⟩

/- The invariants are irreducible from here on: the verification conditions of
`Ratpoints.Sturm.chain` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] ChainLoopInvariant ChainInvariant ReduceInvariant DropZerosInvariant
  ContentInvariant

/-- The loop over `k` ends by its range, the reduction loop by the size of the remainder, which
drops with every pass, and the loop that drops the zeros on top by the size as well. -/
@[spec]
theorem chain_spec (c : List Int) (d : Nat) :
    ⦃ 1 ≤ d ∧ c.getD d 0 ≠ 0 ⦄ chain c d ⦃ IsChainResult c d ⦄ := by
  vcgen [chain] invariants
  | inv1 => fun pref suff x ↦ ChainInvariant c d pref suff x
  | inv2 _ cur _ _ _ ch _ => .mk (ReduceInvariant ch[cur - 1]! ch[cur - 2]!)
  | inv3 => .ofMeasure fun x : Option (Option (Array (Array Int))) × Array Int ↦ x.2.size
  | inv4 => fun pref _ g ↦ ContentInvariant pref g
  | inv5 _ cur _ _ _ ch _ _ t _ _ _ => .mk (DropZerosInvariant (reduce ch[cur - 1]! t).pop)
  | inv6 => .ofMeasure fun t : Array Int ↦ t.size
  all_goals try simp only [Std.WP.WhileInvariant.mk_apply, Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals solve_by_elim (maxDepth := 10) [chainInvariant_init, ChainInvariant.isChainResult,
    ChainInvariant.isChainResult_some, ChainInvariant.reduceInvariant,
    ChainInvariant.of_reduceInvariant_some, ChainInvariant.push_of_size_eq_one,
    ChainInvariant.push_of_size_ne_one, ContentInvariant.normalize_eq,
    ContentInvariant.normalize_eq_map_neg, contentInvariant_nil, ContentInvariant.of_gcd_eq_one,
    ContentInvariant.append, dropZerosInvariant_self, DropZerosInvariant.pop,
    DropZerosInvariant.exit, ReduceInvariant.of_size_eq_zero, ReduceInvariant.of_size_ne_zero,
    ReduceInvariant.exit]

/-- `Ratpoints.Sturm.chain_spec` as a plain statement, which the files with Mathlib use without the
program logic. -/
theorem isChainResult_run_chain {c : List Int} {d : Nat} (hd : 1 ≤ d) (hc : c.getD d 0 ≠ 0) :
    IsChainResult c d (Id.run (chain c d)) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((chain_spec c d).le_wp ⟨hd, hc⟩)

end Sturm

end Ratpoints

end
