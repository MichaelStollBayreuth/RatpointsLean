/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Bounds
public import Ratpoints.Spec.Basic
public import Ratpoints.Spec.Sturm

import Ratpoints.Mathlib.Algebra.Order.Field.Basic
import Ratpoints.Proof.SturmCoverage

/-!
# The search region after the Sturm step

The Sturm step of the search (`Ratpoints.sturmRegion`) refuses exactly when the remainder chain
does, leaves the search intervals as they are when it is off, and otherwise, at a depth of at most
`55`, leaves well-formed intervals inside the given ones (`Ratpoints.run_sturmRegion_subset`, from
`Ratpoints.Sturm.computeSturm_wf`); assuming Sturm's theorem
(`Ratpoints.SturmTheorem`), for a polynomial of degree `d < 2 ^ 57` every `a / b` with
`|a| ≤ 2 ^ 63` of the given intervals with `F(a, b) ≥ 0`, in particular the `x / z` of every point,
lies in one of the intervals that it leaves (`Ratpoints.run_sturmRegion_covers`, from
`Ratpoints.Sturm.covers_computeSturm`). The search region of the search that
`Ratpoints.findPointsWith` runs (`Ratpoints.searchRegion`), over the values of the ends of its
intervals, lies inside the caller's search intervals, and assuming Sturm's theorem when the step is
on, it holds the `x / z` of every point in them.

## Main definitions

* `Ratpoints.searchRegion`: the search intervals of the search after the Sturm step, over the values
  of their ends, or none when the step returns before the search.

## Main statements

* `Ratpoints.run_sturmRegion_eq_error_iff`, `Ratpoints.run_sturmRegion_of_neg`,
  `Ratpoints.run_sturmRegion_eq_ok_none`: the refusal of the Sturm step, the step off, and the
  return before the search, only for even degree and a leading coefficient that is not a square.
* `Ratpoints.run_sturmRegion_subset`: the intervals that the step leaves at a depth of at most `55`,
  where the search clamps it, are well formed and lie inside the given ones.
* `Ratpoints.run_sturmRegion_covers`: assuming Sturm's theorem, they hold every `a / b` of the given
  intervals with `F(a, b) ≥ 0` and `|a| ≤ 2 ^ 63`.
* `Ratpoints.searchRegion_subset`, `Ratpoints.searchRegion_covers`,
  `Ratpoints.searchRegion_eq_none`: the search region inside the caller's intervals, holding the
  `x / z` of every point in them, and none only for even degree and a leading coefficient that is
  not a square.
-/

@[expose] public section

namespace Ratpoints

/-! ### The Sturm step -/

theorem run_sturmRegion_of_neg (c : List ℤ) (d : ℕ) {s : ℤ} (hs : s < 0)
    (dom : List (Double × Double)) :
    Id.run (sturmRegion c d s dom) = .ok (some (dom, false)) := by
  simp [sturmRegion, hs]

/-- The Sturm step on, by the result of `Ratpoints.Sturm.computeSturm`. -/
theorem run_sturmRegion_of_nonneg (c : List ℤ) (d : ℕ) {s : ℤ} (hs : 0 ≤ s)
    (dom : List (Double × Double)) :
    Id.run (sturmRegion c d s dom) =
      match Id.run (Sturm.computeSturm c d s.toNat dom.toArray) with
      | none => .error .notSquarefree
      | some iv => if iv = #[] then
          if d % 2 = 1 ∨ Setup.isSquare (c.getD d 0) then .ok (some ([], true)) else .ok none
        else .ok (some (iv.toList, false)) := by
  simp only [sturmRegion, Int.not_lt.mpr hs, ↓reduceIte, Id.run_bind]
  rcases Id.run (Sturm.computeSturm c d s.toNat dom.toArray) with _ | iv
  · rfl
  · by_cases hiv : iv = #[] <;> simp [hiv]
    split_ifs <;> rfl

/-- The Sturm step refuses exactly when it is on and the remainder chain fails
(`Ratpoints.Sturm.run_computeSturm_eq_none_iff`). -/
theorem run_sturmRegion_eq_error_iff (c : List ℤ) (d : ℕ) (s : ℤ) (dom : List (Double × Double))
    (e : Refusal) :
    Id.run (sturmRegion c d s dom) = .error e ↔
      0 ≤ s ∧ Id.run (Sturm.chain c d) = none ∧ e = .notSquarefree := by
  rcases Int.lt_or_le s 0 with hs | hs
  · simp [run_sturmRegion_of_neg c d hs, hs.not_ge]
  rw [run_sturmRegion_of_nonneg c d hs,
    ← Sturm.run_computeSturm_eq_none_iff c d s.toNat dom.toArray]
  rcases Id.run (Sturm.computeSturm c d s.toNat dom.toArray) with _ | iv
  · simp [hs, eq_comm]
  · grind

/-- The Sturm step returns before the search only for even degree and a leading coefficient that is
not a square, when there is no point at infinity. -/
theorem run_sturmRegion_eq_ok_none {c : List ℤ} {d : ℕ} {s : ℤ} {dom : List (Double × Double)}
    (h : Id.run (sturmRegion c d s dom) = .ok none) :
    d % 2 = 0 ∧ Setup.isSquare (c.getD d 0) = false := by
  rcases Int.lt_or_le s 0 with hs | hs
  · simp [run_sturmRegion_of_neg c d hs] at h
  rw [run_sturmRegion_of_nonneg c d hs] at h
  revert h
  rcases Id.run (Sturm.computeSturm c d s.toNat dom.toArray) with _ | iv
  · simp
  · grind

/-- The intervals that the Sturm step at a depth of at most `55` leaves for well-formed intervals
are well formed (`Ratpoints.Sturm.computeSturm_wf`), none when it sets `sturm_empty`, and lie inside
the given ones. -/
theorem run_sturmRegion_subset {c : List ℤ} {d : ℕ} {s : ℤ} {dom dom' : List (Double × Double)}
    {empty : Bool} (hs : s ≤ 55) (hdom : IntervalsWF (domainBits dom))
    (h : Id.run (sturmRegion c d s dom) = .ok (some (dom', empty))) :
    IntervalsWF (domainBits dom') ∧ (empty = true → dom' = []) ∧
      ∀ x, InIntervals (domainValues dom') x → InIntervals (domainValues dom) x := by
  rcases Int.lt_or_le s 0 with hs0 | hs0
  · rw [run_sturmRegion_of_neg c d hs0] at h
    obtain ⟨rfl, rfl⟩ : dom = dom' ∧ false = empty := by simpa using h
    exact ⟨hdom, nofun, fun _ h ↦ h⟩
  rw [run_sturmRegion_of_nonneg c d hs0] at h
  rcases hc : Id.run (Sturm.computeSturm c d s.toNat dom.toArray) with _ | iv
  · simp [hc] at h
  obtain ⟨hwf, hsub⟩ := Sturm.computeSturm_wf (by lia) (by simpa using hdom) hc
  simp only [hc] at h
  by_cases hiv : iv = #[]
  · obtain ⟨rfl, -⟩ : [] = dom' ∧ true = empty := by
      revert h; simp only [hiv, ↓reduceIte]; split_ifs <;> simp
    exact ⟨by simp [IntervalsWF, AreSearchIntervals], fun _ ↦ rfl, fun x hx ↦ by
      simp [InIntervals] at hx⟩
  · obtain ⟨rfl, rfl⟩ : iv.toList = dom' ∧ false = empty := by simpa [hiv] using h
    exact ⟨hwf, nofun, fun x hx ↦ by simpa using hsub x hx⟩

/-- Assuming Sturm's theorem when the step is on, the intervals that the Sturm step at a depth of at
most `55` leaves for well-formed intervals and the polynomial `c` of degree `0 < d < 2 ^ 57` hold
every `a / b`, `b ≥ 1`, `|a| ≤ 2 ^ 63`, of the given intervals with `F(a, b) ≥ 0`
(`Ratpoints.Sturm.covers_computeSturm`): the step does not return before the search then, and does
not set `sturm_empty`. -/
theorem run_sturmRegion_covers {c : List ℤ} {d : ℕ} {s : ℤ} {dom : List (Double × Double)}
    {r : Option (List (Double × Double) × Bool)} (hS : 0 ≤ s → SturmTheorem) (hs : s ≤ 55)
    (hdom : IntervalsWF (domainBits dom)) (hd : d = degree c) (hd0 : 0 < d) (hd57 : d < 2 ^ 57)
    (h : Id.run (sturmRegion c d s dom) = .ok r) {a : ℤ} {b : ℕ} (hb : 0 < b)
    (ha : a.natAbs ≤ 2 ^ 63) (hF : 0 ≤ binaryForm c a b)
    (hx : InIntervals (domainValues dom) (a / b)) :
    ∃ dom', r = some (dom', false) ∧ InIntervals (domainValues dom') (a / b) := by
  rcases Int.lt_or_le s 0 with hs0 | hs0
  · rw [run_sturmRegion_of_neg c d hs0] at h
    exact ⟨dom, (Except.ok.inj h).symm, hx⟩
  rw [run_sturmRegion_of_nonneg c d hs0] at h
  rcases hc : Id.run (Sturm.computeSturm c d s.toNat dom.toArray) with _ | iv
  · simp [hc] at h
  subst hd
  have ha' : |(a : ℚ)| ≤ 2 ^ 63 := by rw [← Int.cast_abs, Int.abs_eq_natAbs]; exact_mod_cast ha
  have hin := Sturm.covers_computeSturm (hS hs0) hd0 (getD_degree_ne_zero_of_pos hd0) hd57
    (by lia) (by simpa using hdom) hc (Sturm.eval_chainPoly_nonneg hb hF)
    (by simpa using (abs_intCast_div_intCast_le_abs (α := ℚ) a b).trans ha')
    (by simpa using hx)
  have hiv : iv ≠ #[] := by rintro rfl; simp [InIntervals] at hin
  simp only [hc, hiv, ↓reduceIte] at h
  exact ⟨iv.toList, (Except.ok.inj h).symm, hin⟩

/-! ### The search region of the search -/

/-- The search intervals, over the values of their ends, of the search that
`Ratpoints.findPointsWith` runs for the options `o` and the height bound `H` on the polynomial `c`
of degree `d` that the reversal check hands on, after the Sturm step: none when the step returns
before the search (`find_points.c:4889`), no intervals when it leaves none (`sturm_empty`, the
search delivering the points at infinity only), and otherwise the values of the intervals that it
leaves, inside those of the caller or the default interval (`Ratpoints.searchIntervals`). Junk
(none) for the search intervals and the polynomials that `Ratpoints.findPointsWith` refuses. -/
def searchRegion (c : List ℤ) (d H : ℕ) (o : Options) :
    Option (List (WithBotTop ℚ × WithBotTop ℚ)) :=
  match Id.run (searchIntervals H o.domain) with
  | none => none
  | some dom =>
    match Id.run (sturmRegion c d (o.normalize H).sturm dom) with
    | .ok (some (dom', empty)) => some (if empty then [] else domainValues dom')
    | _ => none

/-- The search region of the search lies inside the caller's search intervals, when there are
some. -/
theorem searchRegion_subset {c : List ℤ} {d H : ℕ} {o : Options}
    {D : List (WithBotTop ℚ × WithBotTop ℚ)} (hdom : IntervalsWF (domainBits o.domain))
    (h : searchRegion c d H o = some D) (x : ℚ) (hx : InIntervals D x) :
    o.domain = [] ∨ InIntervals (domainValues o.domain) x := by
  rcases eq_or_ne o.domain [] with hn | hn
  · exact .inl hn
  refine .inr ?_
  simp only [searchRegion, run_searchIntervals_of_ne_nil H hn hdom] at h
  revert h
  rcases hst : Id.run (sturmRegion c d (o.normalize H).sturm o.domain) with _ | _ | ⟨dom', empty⟩
    <;> simp only [reduceCtorEq, Option.some.injEq, false_implies]
  rintro rfl
  obtain ⟨-, hempty, hsub⟩ := run_sturmRegion_subset (o.sturm_normalize_le H) hdom hst
  cases empty
  · exact hsub x hx
  · simp [InIntervals] at hx

/-- Assuming Sturm's theorem when the step is on, the search region of the search for the
polynomial `c` of degree `0 < d < 2 ^ 57`, `1 ≤ H < 2 ^ 63` and well-formed search intervals of the
caller holds every `a / b` with `b ≥ 1`, `|a| ≤ H` and `F(a, b) ≥ 0` in the caller's intervals
(anywhere when there are none), when the Sturm step does not refuse. -/
theorem searchRegion_covers {c : List ℤ} {d H : ℕ} {o : Options} (hS : 0 ≤ o.sturm → SturmTheorem)
    (hdom : IntervalsWF (domainBits o.domain)) (hd : d = degree c) (hd0 : 0 < d) (hd57 : d < 2 ^ 57)
    (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) (hc : 0 ≤ o.sturm → Id.run (Sturm.chain c d) ≠ none)
    {a : ℤ} {b : ℕ} (hb : 0 < b) (ha : a.natAbs ≤ H) (hF : 0 ≤ binaryForm c a b)
    (hx : o.domain = [] ∨ InIntervals (domainValues o.domain) (a / b)) :
    ∃ D, searchRegion c d H o = some D ∧ InIntervals D (a / b) := by
  obtain ⟨dom, hsi, hwf, hx'⟩ : ∃ dom, Id.run (searchIntervals H o.domain) = some dom ∧
      IntervalsWF (domainBits dom) ∧ InIntervals (domainValues dom) (a / b) := by
    rcases eq_or_ne o.domain [] with hn | hn
    · obtain ⟨dom, hsi, hwf, hall⟩ := exists_run_searchIntervals_nil hH hH63
      exact ⟨dom, hn ▸ hsi, hwf, hall a b hb ha⟩
    · exact ⟨_, run_searchIntervals_of_ne_nil H hn hdom, hdom, hx.resolve_left hn⟩
  rcases hst : Id.run (sturmRegion c d (o.normalize H).sturm dom) with e | r
  · obtain ⟨h1, h2, -⟩ := (run_sturmRegion_eq_error_iff ..).mp hst
    exact (hc ((o.sturm_normalize_nonneg_iff H).mp h1) h2).elim
  obtain ⟨dom', rfl, hin⟩ := run_sturmRegion_covers
    (fun h ↦ hS ((o.sturm_normalize_nonneg_iff H).mp h)) (o.sturm_normalize_le H) hwf hd hd0 hd57
    hst hb (by lia) hF hx'
  exact ⟨_, by simp [searchRegion, hsi, hst], hin⟩

/-- The search region of the search is none only for even degree and a leading coefficient that is
not a square, when the search intervals are well formed and the Sturm step does not refuse. -/
theorem searchRegion_eq_none {c : List ℤ} {d H : ℕ} {o : Options}
    (hdom : IntervalsWF (domainBits o.domain))
    (hc : 0 ≤ o.sturm → Id.run (Sturm.chain c d) ≠ none) (h : searchRegion c d H o = none) :
    d % 2 = 0 ∧ Setup.isSquare (c.getD d 0) = false := by
  rcases hsi : Id.run (searchIntervals H o.domain) with _ | dom
  · exact absurd hdom ((run_searchIntervals_eq_none_iff H o.domain).mp hsi)
  rcases hst : Id.run (sturmRegion c d (o.normalize H).sturm dom) with e | _ | ⟨dom', empty⟩
  · obtain ⟨h1, h2, -⟩ := (run_sturmRegion_eq_error_iff ..).mp hst
    exact (hc ((o.sturm_normalize_nonneg_iff H).mp h1) h2).elim
  · exact run_sturmRegion_eq_ok_none hst
  · simp [searchRegion, hsi, hst] at h

/-- The search region of the search, from the result of the Sturm step on the search intervals of
`Ratpoints.searchIntervals`. -/
theorem searchRegion_eq_of_run_sturmRegion_eq {c : List ℤ} {d H : ℕ} {o : Options}
    {dom : List (Double × Double)} (hsi : Id.run (searchIntervals H o.domain) = some dom)
    {r : Option (List (Double × Double) × Bool)}
    (hst : Id.run (sturmRegion c d (o.normalize H).sturm dom) = .ok r) :
    searchRegion c d H o = r.map fun x ↦ if x.2 then [] else domainValues x.1 := by
  rcases r with _ | ⟨dom', empty⟩ <;> simp [searchRegion, hsi, hst]

/-- When the Sturm step of the normalized options is on and does not refuse, the remainder chain
succeeds (`Ratpoints.run_sturmRegion_eq_error_iff`). -/
theorem chain_ne_none_of_run_sturmRegion_eq_ok {c : List ℤ} {d H : ℕ} {o : Options}
    {dom : List (Double × Double)} {r : Option (List (Double × Double) × Bool)}
    (h : Id.run (sturmRegion c d (o.normalize H).sturm dom) = .ok r) (hs : 0 ≤ o.sturm) :
    Id.run (Sturm.chain c d) ≠ none := fun hc ↦ by
  simp [(run_sturmRegion_eq_error_iff ..).mpr ⟨(o.sturm_normalize_nonneg_iff H).mpr hs, hc, rfl⟩]
    at h

end Ratpoints

end
