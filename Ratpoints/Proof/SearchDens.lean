/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Shapes

import Ratpoints.Mathlib.Data.List.Basic
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Order
import Ratpoints.Proof.Setup

/-!
# The denominators of the search

The search of the polynomial with the coefficient list `c` of degree `d` visits the denominators
from `bLow` to the largest denominator `bHigh` in the order of the loop of its shape
(`Ratpoints.searchDens`): the divisors of the leading coefficient times squares when `d` is odd,
`|c_d| ≠ 1` and the divisor set-up up to `bHigh` succeeds, and `bLow, …, bHigh` otherwise. These are
the denominators of the specification of the order up to `bHigh` (`Ratpoints.searchDenominators`)
from `bLow` on, each once, and their points, with the points at infinity, are a permutation of the
brute-force reference restricted to these denominators.

## Main definitions

* `Ratpoints.searchDens`: the denominators of the search, in the order of its loop.

## Main statements

* `Ratpoints.perm_filter_bruteForce_append_flatMap_searchDens`: the points at infinity and those of
  the denominators of the search from `bLow` to `bHigh` are a permutation of the brute-force
  reference restricted to these denominators.
* `Ratpoints.searchDens_eq_range'`: the denominators of the search are `bLow, …, bHigh` when it does
  not use the divisor shape.
* `Ratpoints.searchDens_one_eq_searchDenominators`: the denominators of the search from `1` on are
  those of the specification of the order up to `bHigh`; `Ratpoints.searchDens_eq_filter`: from
  `bLow` on, they are those from `1` on that are at least `bLow`.

## Proof

The divisor shape visits each denominator of a point once
(`Ratpoints.exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd`,
`Ratpoints.Setup.mem_iff_of_setupUs1_eq_some`, `Ratpoints.Sieve.mem_squares1Dens_iff`,
`Ratpoints.Sieve.nodup_squares1Dens`), so that its list gives a permutation of the reference
(`List.perm_flatMap_of_nodup`); the divisor set-up succeeds exactly when the specification of the
order takes the divisor shape, with the divisors of `Ratpoints.binaryDivisors`
(`Ratpoints.Setup.map_snd_run_setupUs1`).
-/

@[expose] public section

namespace Ratpoints

open BruteForce Sieve

/-- The denominators of the search of the polynomial with the coefficient list `c` of degree `d`,
from `bLow` to the largest denominator `bHigh`, in the order of its loop: the divisors of the
leading coefficient times squares (`Ratpoints.Sieve.squares1Dens`) when `d` is odd, `|c_d| ≠ 1`
and the divisor set-up up to `bHigh` succeeds (`Ratpoints.Setup.setupUs1`), and `bLow, …, bHigh`
otherwise, of which the other shapes visit, in this order, those that their tests let through
(`Ratpoints.Sieve.Shape`). -/
def searchDens (c : List ℤ) (d bLow bHigh : ℕ) : List ℕ :=
  match if d % 2 == 1 && (c.getD d 0).natAbs != 1 then Id.run (Setup.setupUs1 c d bHigh) else none
  with
  | some (_, divisors) => squares1Dens divisors bLow bHigh
  | none => List.range' bLow (bHigh + 1 - bLow)

/-- The denominators of the search are `bLow, …, bHigh` when it does not use the divisor shape: for
even degree, for `|c_d| = 1`, and when the divisor set-up fails. -/
theorem searchDens_eq_range' {c : List ℤ} {d bLow bHigh : ℕ}
    (h : d % 2 = 0 ∨ (c.getD d 0).natAbs = 1 ∨ Id.run (Setup.setupUs1 c d bHigh) = none) :
    searchDens c d bLow bHigh = List.range' bLow (bHigh + 1 - bLow) := by
  rcases h with h | h | h
  · simp [searchDens, h]
  · simp only [searchDens, h, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  · simp [searchDens, h]

-- The denominators of the search are `bLow, …, bHigh` or, for odd degree, those of the divisor
-- shape.
private theorem searchDens_eq_range'_or (c : List ℤ) (d bLow bHigh : ℕ) :
    searchDens c d bLow bHigh = List.range' bLow (bHigh + 1 - bLow) ∨ ∃ info divisors,
      d % 2 = 1 ∧ Id.run (Setup.setupUs1 c d bHigh) = some (info, divisors) ∧
        searchDens c d bLow bHigh = squares1Dens divisors bLow bHigh := by
  rw [searchDens]
  split
  · rename_i h
    obtain ⟨hcond, hs⟩ := Option.ite_none_right_eq_some.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact .inr ⟨_, _, hcond.1, hs, rfl⟩
  · exact .inl rfl

-- The divisors of the set-up for odd degree are positive.
private theorem pos_of_mem_of_setupUs1_eq_some {c : List ℤ} {bHigh : ℕ} (hb : 1 ≤ bHigh)
    (hd : degree c % 2 = 1) {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) bHigh) = some (info, divisors)) {s : ℕ}
    (hs' : s ∈ divisors) : 0 < s :=
  Nat.pos_of_ne_zero ((Setup.mem_iff_of_setupUs1_eq_some hs
    (getD_degree_ne_zero_of_pos (by lia)) hb).mp hs').1.ne_zero

-- The divisor shape of a successful set-up for odd degree lists each denominator once.
private theorem nodup_squares1Dens_of_setupUs1_eq_some {c : List ℤ} {bHigh : ℕ} (hb : 1 ≤ bHigh)
    (hd : degree c % 2 = 1) {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) bHigh) = some (info, divisors)) (bLow : ℕ) :
    (squares1Dens divisors bLow bHigh).Nodup :=
  have hc : c.getD (degree c) 0 ≠ 0 := getD_degree_ne_zero_of_pos (by lia)
  nodup_squares1Dens (Setup.nodup_of_setupUs1_eq_some hs hc hb)
    (fun _ hs' ↦ ((Setup.mem_iff_of_setupUs1_eq_some hs hc hb).mp hs').1) bLow bHigh

-- The divisor shape over `bLow, …, bHigh` lists denominators of `bLow, …, bHigh`.
private theorem mem_range'_of_mem_squares1Dens {divisors : List ℕ} {bLow bHigh b : ℕ}
    (hbLow : 1 ≤ bLow) (hb : b ∈ squares1Dens divisors bLow bHigh) :
    b ∈ List.range' bLow (bHigh + 1 - bLow) :=
  have := le_and_le_of_mem_squares1Dens hbLow hb
  List.mem_range'_1.mpr ⟨this.1, by lia⟩

/-- The denominators of the search lie in `bLow, …, bHigh`. -/
theorem le_and_le_of_mem_searchDens {c : List ℤ} {bLow bHigh b : ℕ} (hbLow : 1 ≤ bLow)
    (hb : b ∈ searchDens c (degree c) bLow bHigh) : bLow ≤ b ∧ b ≤ bHigh := by
  obtain h | ⟨_, _, -, -, h⟩ := searchDens_eq_range'_or c (degree c) bLow bHigh
  · rw [h] at hb
    lia [List.mem_range'_1.mp hb]
  · exact le_and_le_of_mem_squares1Dens hbLow (h ▸ hb)

/-- The denominators of the search from `bLow ≥ 1` are distinct: `bLow, …, bHigh`, or for odd degree
the products of the distinct squarefree divisors of the set-up with squares
(`Ratpoints.Sieve.nodup_squares1Dens`), and none for `bHigh = 0`. -/
theorem nodup_searchDens (c : List ℤ) {bLow bHigh : ℕ} (hbLow : 1 ≤ bLow) :
    (searchDens c (degree c) bLow bHigh).Nodup := by
  rcases Nat.eq_zero_or_pos bHigh with rfl | hb
  · have h : searchDens c (degree c) bLow 0 = [] := List.eq_nil_iff_forall_not_mem.mpr fun b hb ↦
      absurd (le_and_le_of_mem_searchDens hbLow hb) (by lia)
    exact h ▸ List.nodup_nil
  obtain h | ⟨info, divisors, hd, hs, h⟩ := searchDens_eq_range'_or c (degree c) bLow bHigh
  · exact h ▸ List.nodup_range'
  · exact h ▸ nodup_squares1Dens_of_setupUs1_eq_some hb hd hs bLow

/-- The divisor shape visits each denominator of a point once, so that it gives a permutation of
the points of the denominators `bLow, …, bHigh`: the denominator of every point is `s k ^ 2` with
`s` squarefree and dividing `c_d`, so one of the divisors of the set-up, and the shape lists each
such product once (`List.perm_flatMap_of_nodup`). -/
theorem perm_flatMap_squares1Dens {c : List ℤ} {H bLow bHigh : ℕ} (hbLow : 1 ≤ bLow)
    (hb : 1 ≤ bHigh) (hd : degree c % 2 = 1) {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) bHigh) = some (info, divisors)) :
    ((squares1Dens divisors bLow bHigh).flatMap fun b : ℕ ↦
      pointsOfDen c (degree c) b (numerators H)).Perm
      ((List.range' bLow (bHigh + 1 - bLow)).flatMap fun b : ℕ ↦
        pointsOfDen c (degree c) b (numerators H)) := by
  have hc : c.getD (degree c) 0 ≠ 0 := getD_degree_ne_zero_of_pos (by lia)
  have hmem (s : ℕ) := Setup.mem_iff_of_setupUs1_eq_some hs hc hb (s := s)
  refine List.perm_flatMap_of_nodup List.nodup_range'
    (nodup_squares1Dens_of_setupUs1_eq_some hb hd hs bLow)
    (fun _ ↦ mem_range'_of_mem_squares1Dens hbLow) fun b hb' hne ↦ ?_
  have hb'' := List.mem_range'_1.mp hb'
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil hne
  obtain ⟨s, k, hsq, hdvd, hbsk⟩ := exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd hd hg hy
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hbsk; lia
  exact (mem_squares1Dens_iff (fun _ ↦ pos_of_mem_of_setupUs1_eq_some hb hd hs) hbLow).mpr
    ⟨hb''.1, by lia, s, (hmem s).mpr ⟨hsq, hdvd,
      by lia [Nat.le_mul_of_pos_right s (Nat.mul_pos hk hk)]⟩, k, hbsk⟩

/-- The points at infinity and those of the denominators of the search from `bLow ≥ 1` to
`bHigh ≤ H` are a permutation of the brute-force reference restricted to the points at infinity and
the denominators from `bLow` to `bHigh` (`Ratpoints.perm_flatMap_squares1Dens`). -/
theorem perm_filter_bruteForce_append_flatMap_searchDens (c : List ℤ) {H bLow bHigh : ℕ}
    (hbLow : 1 ≤ bLow) (hb : 1 ≤ bHigh) (hbH : bHigh ≤ H) :
    (pointsOfDen c (degree c) 0 [1] ++ (searchDens c (degree c) bLow bHigh).flatMap fun b : ℕ ↦
      pointsOfDen c (degree c) b (numerators H)).Perm ((bruteForce c H).filter fun p ↦
        p.2.2 = 0 ∨ bLow ≤ p.2.2 ∧ p.2.2 ≤ bHigh) := by
  rw [filter_bruteForce_eq_append c (hb.trans hbH) hbLow hbH]
  refine .append_left _ ?_
  obtain h | ⟨info, divisors, hd, hs, h⟩ := searchDens_eq_range'_or c (degree c) bLow bHigh
  · rw [h]
  · rw [h]
    exact perm_flatMap_squares1Dens hbLow hb hd hs

/-- The denominators of the search from `bLow ≥ 1` on are those from `1` on that are at least
`bLow`, for each shape by its listing (`Ratpoints.Sieve.squares1Dens_eq_filter`). -/
theorem searchDens_eq_filter (c : List ℤ) (d : ℕ) {bLow : ℕ} (hbLow : 1 ≤ bLow) (bHigh : ℕ) :
    searchDens c d bLow bHigh = (searchDens c d 1 bHigh).filter (bLow ≤ ·) := by
  rw [searchDens, searchDens]
  split
  · exact squares1Dens_eq_filter hbLow bHigh
  · exact List.range'_eq_filter_range' hbLow bHigh

/-- The denominators of the search of the polynomial with the coefficient list `c` of its degree
from `1` to `bHigh ≥ 1` are those of the specification of the order
(`Ratpoints.searchDenominators`): the divisor set-up succeeds exactly when the specification takes
the divisor shape, with the divisors of `Ratpoints.binaryDivisors`
(`Ratpoints.Setup.map_snd_run_setupUs1`). -/
theorem searchDens_one_eq_searchDenominators (c : List ℤ) {bHigh : ℕ} (hb : 1 ≤ bHigh) :
    searchDens c (degree c) 1 bHigh = searchDenominators maxDivisors c bHigh := by
  rw [searchDens, searchDenominators]
  by_cases hd : degree c % 2 = 1 ∧ (c.getD (degree c) 0).natAbs ≠ 1
  · have hs := Setup.map_snd_run_setupUs1 (getD_degree_ne_zero_of_pos (c := c) (by lia)) hb
    rw [ite_eq_left (show (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1) = true by
      simpa using hd)]
    simp only [hd.1, hd.2, true_and, ne_eq, not_false_eq_true]
    rcases h : Id.run (Setup.setupUs1 c (degree c) bHigh) with _ | ⟨info, divs⟩ <;> rw [h] at hs <;>
      split_ifs at hs ⊢
    · simp at hs
    · simp
    · simp only [Option.map_some, Option.some.injEq] at hs
      subst hs
      exact squares1Dens_one_eq_filter (fun _ ↦ pos_of_mem_binaryDivisors) bHigh
    · simp at hs
  · rw [ite_eq_right (by simpa using hd), ite_eq_right (by tauto)]
    simp

end Ratpoints

end
