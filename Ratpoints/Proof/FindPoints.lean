/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Ratpoints.Model.FindPoints
public import Ratpoints.Proof.Words
public import Ratpoints.Spec.Basic

import Ratpoints.Mathlib.Data.List.Basic
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Denominators
import Ratpoints.Proof.Params
import Ratpoints.Proof.Setup
import Ratpoints.Proof.Shapes
import Ratpoints.Proof.Sieve
import Ratpoints.Proof.Tables
import Ratpoints.Proof.TwoAdic
import Std.Tactic.Do

/-!
# The sieve finds exactly the points, and the refusals

The search of the polynomial that the set-up hands on gives, for well-formed parameters, the points
at infinity followed by the points of the brute-force reference over the denominators that the
loop of its shape visits, in its order (`Ratpoints.searchDens`), each mapped by
`Ratpoints.Sieve.swapPoint` when the flag of the reversal is set, also when it takes one of its
exits (`Ratpoints.run_searchPoints`). These are the points of the reference in another order,
except where the shape visits the denominators in increasing order: every shape but that of the
divisors of the leading coefficient times squares. So the list that `Ratpoints.findPoints c H P o`
returns is that of the search of the polynomial that the reversal check hands on, mapped back after
a reversal (`Ratpoints.exists_eq_of_findPoints_eq_ok`): in every case a permutation of the
reference of `c`, so that it holds exactly the points of the specification, each once, for every
option. `Ratpoints.findPoints` refuses exactly the inputs that the program refuses: with the Sturm
step on, those with fewer than two or more than `Ratpoints.maxDegree + 1` coefficients, the height
bound `0` and the binary forms `Φ_c` that are not squarefree; without it, instead of the last, those
that the test of the leading zeros and the reversal check refuse. Comparator certifies the
membership, the absence of duplicates and both refusal theorems (`comparator/Challenge.lean`).

## Main definitions

* `Ratpoints.searchDens`: the denominators of the search, in the order of its loop.

## Main statements

* `Ratpoints.perm_bruteForce_append_flatMap_searchDens`: the points at infinity and those of the
  denominators of the search are a permutation of the brute-force reference;
  `Ratpoints.append_flatMap_searchDens_eq_bruteForce`: they are the reference when the denominators
  of the search are `1, …, H` (`Ratpoints.searchDens_eq_range'`).
* `Ratpoints.run_searchPoints`: for well-formed parameters, `H ≥ 1` and the degree of the
  polynomial, the search gives these points, mapped by `Ratpoints.Sieve.swapPoint` when the flag of
  the reversal is set, also when it takes an exit.
* `Ratpoints.exists_eq_of_findPoints_eq_ok`: for well-formed parameters, every list that
  `Ratpoints.findPoints` returns is the list of the search of the polynomial that the reversal
  check hands on, mapped back after a reversal;
  `Ratpoints.eq_bruteForce_of_findPoints_eq_ok_of_reverse_eq_false`: the reference when the options
  forbid the reversal and the denominators of the search are `1, …, H`.
* `Ratpoints.perm_bruteForce_of_findPoints_eq_ok`: the list is a permutation of the reference.
* `Ratpoints.mem_iff_isPoint_of_findPoints_eq_ok`: a triple lies in the list that
  `Ratpoints.findPoints` returns exactly when it is a normalized point of height at most `H`.
* `Ratpoints.nodup_of_findPoints_eq_ok`: the list has no duplicates.
* `Ratpoints.toFinset_eq_points_of_findPoints_eq_ok`: its set of elements is `Ratpoints.points`.
* `Ratpoints.exists_findPoints_eq_error_iff_of_sturm_nonneg`: with the Sturm step on,
  `Ratpoints.findPoints` refuses exactly the inputs with fewer than two or more than
  `Ratpoints.maxDegree + 1` coefficients, the height bound `0` and the forms that are not
  squarefree.
* `Ratpoints.exists_findPoints_eq_error_iff_of_sturm_neg`: without it, those with fewer than two or
  more than `Ratpoints.maxDegree + 1` coefficients, the height bound `0`, a degree `d` with
  `d + 2 ≤ 2 ⌈n / 2⌉`, and, when the reversal is allowed, an even degree with `c₀ = c₁ = 0`.

## Proof

By the reduction of the run to the reference (`Ratpoints.Sieve.toList_run_sieveRun_eq_flatMap`), for
pieces of at least one bit array and moduli that are primes, hence positive, the run gives the
reference over the list of its shape when its filters are sound: every numerator of a point passes
the word of the class of its denominator and survives the tables
(`Ratpoints.Sieve.classBit_and_survives_of_ne_nil`), and every denominator of a point passes the
tests of the shape that `Ratpoints.Sieve.runSetup` chooses: the squares for odd degree and
`|c_d| = 1` (`Ratpoints.isSquare_of_sq_eq_binaryForm_of_odd`,
`Ratpoints.Sieve.squaresDens_eq_filter`), the divisors with their valuation test
(`Ratpoints.Sieve.run_denInfoTest_of_sq_eq`), the words with the forbidden divisors and the Jacobi
test (`Ratpoints.Sieve.toList_run_wordsDens`, `Ratpoints.Sieve.getLsbD_denBits_and_all_of_sq_eq`,
`Ratpoints.Sieve.run_wordsTest_of_sq_eq`), and every denominator, by the class test
(`Ratpoints.Sieve.getElem!_twoAdic_ne_zero`). The divisor shape visits each denominator of a point
once (`Ratpoints.exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd`,
`Ratpoints.Setup.mem_iff_of_setupUs1_eq_some`, `Ratpoints.Sieve.mem_squares1Dens_iff`,
`Ratpoints.Sieve.nodup_squares1Dens`), so that its list gives a permutation of the reference
(`List.perm_flatMap_of_nodup`). The points at infinity are those of the candidate `(1, 0)` of the
reference (`Ratpoints.Sieve.pointsAtInfinity_eq_pointsOfDen`), mapped when the flag is set
(`Ratpoints.Sieve.pointsAtInfinity_eq_map`). In the search, the pieces have at least one bit array
(`Ratpoints.Params.one_le_arraySizeAt`) and the moduli of well-formed parameters are primes
(`Ratpoints.Params.WF.prime_of_mem`); a table that the search makes is that of the reference
(`Ratpoints.Sieve.eq_examinePrime_of_examinePrime?_eq_some`); when the search takes the exit of a
table, the curve has no points (`Ratpoints.Sieve.not_isPoint_of_examinePrime?_eq_none`), and when it
takes the 2-adic exit, no class of the denominators admits a numerator, so that the curve has no
points either (`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`): the reference is empty, and so
are the points at infinity and those of the denominators of the search, which lie in `1, …, H`.
`Ratpoints.findPoints` runs the search on the polynomial that the reversal check hands on, with its
degree (`Ratpoints.Setup.degree_eq_of_reversal_eq_ok`) and its flag of the reversal; the binary form
of a reversed polynomial is that of `c` with `x` and `z` exchanged
(`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`), so that its reference, mapped back, is a
permutation of that of `c` (`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`). Of the refusals, the
test of the leading zeros and that of the reversal check stand for `Z ^ 2 ∣ Φ_c` and `X ^ 2 ∣ Φ_c`
(`Ratpoints.not_squarefree_binaryFormPoly_of_lt`,
`Ratpoints.Setup.not_squarefree_binaryFormPoly_of_reversal_eq_error`), and after them the remainder
chain of the polynomial searched is none exactly when `Φ_c` is not squarefree
(`Ratpoints.Sturm.run_chain_eq_none_iff_of_reversal_eq_ok`).

## Implementation notes

The search is proved with `vcgen`, which reads its components (the divisor set-up, the 2-adic
information, the forbidden divisors, the choice of the shape and the run) through private
specifications `⦃True⦄ x ⦃fun r ↦ r = Id.run x⦄`, so that its verification conditions speak of the
values of the components; the run of the shape that `Ratpoints.Sieve.runSetup` chooses is handled
by cases in one lemma. The exits use only that the denominators of the search lie in `1, …, H`, so
that the contract of the search does not rest on the permutation of the reference
(`Ratpoints.perm_bruteForce_append_flatMap_searchDens`), which the theorems on
`Ratpoints.findPoints` use.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

open BruteForce Sieve

/-! ### The points at infinity and the points of a denominator -/

namespace BruteForce

theorem horner_scaledCoeffs_one_zero (c : List ℤ) (d : ℕ) :
    horner (scaledCoeffs c d 0) 1 = c.getD d 0 := by
  rw [horner_scaledCoeffs, Finset.sum_range_succ, Finset.sum_eq_zero fun k hk ↦ by
    rw [zero_pow (by have := Finset.mem_range.mp hk; lia)]; simp]
  simp

end BruteForce

namespace Sieve

theorem survives_of_mem_pointsOfDen {c : List ℤ} {ms : List ℕ} (hms : ∀ p ∈ ms, p.Prime) {b : ℕ}
    {xs : List ℤ} {q : ℤ × ℤ × ℤ} (hq : q ∈ pointsOfDen c (BruteForce.degree c) b xs) :
    survives (ms.map (examinePrime c (BruteForce.degree c))) b q.1 = true := by
  obtain ⟨x, y, z⟩ := q
  obtain ⟨-, rfl, hg, hy⟩ := mem_pointsOfDen_iff.mp hq
  rw [horner_scaledCoeffs_mul] at hy
  simp only [survives, List.all_map, List.all_eq_true, Function.comp_apply]
  exact fun p hp ↦ admits_examinePrime_of_sq_eq (hms p hp) hg hy

theorem pointsAtInfinity_eq_pointsOfDen (c : List ℤ) (d : ℕ) :
    pointsAtInfinity c d false = pointsOfDen c d 0 [1] := by
  simp only [pointsAtInfinity, pointsOfDen_singleton, Int.gcd_one_left, reduceCtorEq, ↓reduceIte,
    horner_scaledCoeffs_one_zero]
  split_ifs <;> simp [pointsAbove]

theorem pointsAtInfinity_eq_map (c : List ℤ) (d : ℕ) (rev : Bool) :
    pointsAtInfinity c d rev =
      (pointsAtInfinity c d false).map (if rev then swapPoint else id) := by
  cases rev <;> simp [pointsAtInfinity, pointsAbove, apply_ite (List.map swapPoint), swapPoint]

/-- The class word of the denominator `b` and the tables of primes let the numerator of every point
over `b` through (`Ratpoints.Sieve.classBit_twoAdic_of_sq_eq`,
`Ratpoints.Sieve.survives_of_mem_pointsOfDen`). -/
theorem classBit_and_survives_of_ne_nil {c : List ℤ} {ms : List ℕ} (hms : ∀ p ∈ ms, p.Prime)
    {b : ℕ} {a : ℤ} (h : pointsOfDen c (degree c) b [a] ≠ []) :
    classBit (Id.run (twoAdic c (degree c)))[b % 64]! a = true ∧
      survives (ms.map (examinePrime c (degree c))) b a = true := by
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hx, -, hg, hy⟩ := mem_pointsOfDen_iff.mp hq
  obtain rfl := List.mem_singleton.mp hx
  exact ⟨classBit_twoAdic_of_sq_eq hg (hy.trans (horner_scaledCoeffs_mul c _ _)),
    survives_of_mem_pointsOfDen hms hq⟩

end Sieve

/-! ### The denominators of the search -/

/-- The denominators of the search of the polynomial with the coefficient list `c` of degree `d`,
for the height `H`, in the order of its loop: the divisors of the leading coefficient times squares
(`Ratpoints.Sieve.squares1Dens`) when `d` is odd, `|c_d| ≠ 1` and the divisor set-up succeeds
(`Ratpoints.Setup.setupUs1`), and `1, …, H` otherwise, of which the other shapes visit, in this
order, those that their tests let through (`Ratpoints.Sieve.Shape`). -/
def searchDens (c : List ℤ) (d H : ℕ) : List ℕ :=
  match if d % 2 == 1 && (c.getD d 0).natAbs != 1 then Id.run (Setup.setupUs1 c d H) else none with
  | some (_, divisors) => squares1Dens divisors 1 H
  | none => List.range' 1 H

/-- The denominators of the search are `1, …, H` when it does not use the divisor shape: for even
degree, for `|c_d| = 1`, and when the divisor set-up fails. -/
theorem searchDens_eq_range' {c : List ℤ} {d H : ℕ}
    (h : d % 2 = 0 ∨ (c.getD d 0).natAbs = 1 ∨ Id.run (Setup.setupUs1 c d H) = none) :
    searchDens c d H = List.range' 1 H := by
  rcases h with h | h | h
  · simp [searchDens, h]
  · simp only [searchDens, h, bne_self_eq_false, Bool.and_false, Bool.false_eq_true, ↓reduceIte]
  · simp [searchDens, h]

-- The denominators of the search are `1, …, H` or, for odd degree, those of the divisor shape.
private theorem searchDens_eq_range'_or (c : List ℤ) (d H : ℕ) :
    searchDens c d H = List.range' 1 H ∨ ∃ info divisors, d % 2 = 1 ∧
      Id.run (Setup.setupUs1 c d H) = some (info, divisors) ∧
        searchDens c d H = squares1Dens divisors 1 H := by
  rw [searchDens]
  split
  · rename_i h
    obtain ⟨hcond, hs⟩ := Option.ite_none_right_eq_some.mp h
    simp only [Bool.and_eq_true, beq_iff_eq] at hcond
    exact .inr ⟨_, _, hcond.1, hs, rfl⟩
  · exact .inl rfl

-- The reference with its points at infinity apart.
private theorem bruteForce_eq_append (c : List ℤ) {H : ℕ} (hH : 1 ≤ H) :
    bruteForce c H = pointsAtInfinity c (degree c) false ++
      (List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H) := by
  simp [bruteForce, hH, pointsAtInfinity_eq_pointsOfDen, List.range'_eq_map_range, Nat.add_comm,
    List.flatMap_map, BruteForce.degree_eq]

-- The divisors of the set-up for odd degree are positive.
private theorem pos_of_mem_of_setupUs1_eq_some {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (hd : degree c % 2 = 1) {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) H) = some (info, divisors)) {s : ℕ}
    (hs' : s ∈ divisors) : 0 < s :=
  Nat.pos_of_ne_zero ((Setup.mem_iff_of_setupUs1_eq_some hs
    (getD_degree_ne_zero_of_pos (by lia)) hH).mp hs').1.ne_zero

-- The divisor shape over `1, …, H` lists denominators of `1, …, H`.
private theorem mem_range'_of_mem_squares1Dens {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (hd : degree c % 2 = 1) {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) H) = some (info, divisors)) {b : ℕ}
    (hb : b ∈ squares1Dens divisors 1 H) : b ∈ List.range' 1 H := by
  obtain ⟨h1, h2, -⟩ :=
    (mem_squares1Dens_iff (fun _ ↦ pos_of_mem_of_setupUs1_eq_some hH hd hs) le_rfl).mp hb
  exact List.mem_range'_1.mpr ⟨h1, by lia⟩

-- The denominators of the search lie in `1, …, H`.
private theorem mem_range'_of_mem_searchDens {c : List ℤ} {H b : ℕ} (hH : 1 ≤ H)
    (hb : b ∈ searchDens c (degree c) H) : b ∈ List.range' 1 H := by
  obtain h | ⟨info, divisors, hd, hs, h⟩ := searchDens_eq_range'_or c (degree c) H
  · rwa [h] at hb
  · exact mem_range'_of_mem_squares1Dens hH hd hs (h ▸ hb)

/-- The divisor shape visits each denominator of a point once, so that it gives a permutation of
the points of the denominators `1, …, H`: the denominator of every point is `s k ^ 2` with `s`
squarefree and dividing `c_d`, so one of the divisors of the set-up, and the shape lists each such
product once (`List.perm_flatMap_of_nodup`). -/
theorem perm_flatMap_squares1Dens {c : List ℤ} {H : ℕ} (hH : 1 ≤ H) (hd : degree c % 2 = 1)
    {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) H) = some (info, divisors)) :
    ((squares1Dens divisors 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).Perm
      ((List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)) := by
  have hc : c.getD (degree c) 0 ≠ 0 := getD_degree_ne_zero_of_pos (by lia)
  have hmem (s : ℕ) := Setup.mem_iff_of_setupUs1_eq_some hs hc hH (s := s)
  refine List.perm_flatMap_of_nodup List.nodup_range' (nodup_squares1Dens
    (Setup.nodup_of_setupUs1_eq_some hs hc) (fun s hs' ↦ ((hmem s).mp hs').1) 1 H)
    (fun _ ↦ mem_range'_of_mem_squares1Dens hH hd hs) fun b hb hne ↦ ?_
  have hb' := List.mem_range'_1.mp hb
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil hne
  obtain ⟨s, k, hsq, hdvd, hbsk⟩ := exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd hd hg hy
  have hk : 0 < k := Nat.pos_of_ne_zero fun h0 ↦ by simp [h0] at hbsk; lia
  have hsb : s ≤ s * k * k := by
    rw [Nat.mul_assoc]
    exact Nat.le_mul_of_pos_right s (Nat.mul_pos hk hk)
  exact (mem_squares1Dens_iff (fun _ ↦ pos_of_mem_of_setupUs1_eq_some hH hd hs) le_rfl).mpr
    ⟨hb'.1, by lia, s, (hmem s).mpr ⟨hsq, hdvd, by lia⟩, k, hbsk⟩

/-- The points at infinity and those of the denominators of the search are a permutation of the
brute-force reference (`Ratpoints.perm_flatMap_squares1Dens`). -/
theorem perm_bruteForce_append_flatMap_searchDens (c : List ℤ) {H : ℕ} (hH : 1 ≤ H) :
    (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap fun b : ℕ ↦
      pointsOfDen c (degree c) b (numerators H)).Perm (bruteForce c H) := by
  rw [bruteForce_eq_append c hH]
  refine .append_left _ ?_
  obtain h | ⟨info, divisors, hd, hs, h⟩ := searchDens_eq_range'_or c (degree c) H
  · rw [h]
  · rw [h]
    exact perm_flatMap_squares1Dens hH hd hs

theorem append_flatMap_searchDens_eq_bruteForce {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (hs : searchDens c (degree c) H = List.range' 1 H) :
    pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
      (fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)) = bruteForce c H := by
  rw [hs, bruteForce_eq_append c hH]

/-! ### The run in each shape -/

namespace Sieve

-- The run with the tables of the primes `ms` and the words of the 2-adic information, for a shape
-- whose list is `l` filtered by `p` and whose tests let the denominator of every point through.
private theorem toList_run_sieveRun_of_sound {c : List ℤ} {H A : ℕ} {ms : List ℕ}
    (hms : ∀ p ∈ ms, p.Prime) (hA : 1 ≤ A) (rev : Bool) {shape : Shape} {l : List ℕ}
    {p : ℕ → Bool}
    (hdens : Id.run (shape.dens (denBits (Id.run (twoAdic c (degree c)))) 1 H) = l.filter p)
    (hkeep : ∀ b ∈ l, pointsOfDen c (degree c) b (numerators H) ≠ [] →
      p b = true ∧ Id.run (shape.keep (Id.run (twoAdic c (degree c))) b) = true) :
    (Id.run (sieveRun c (degree c) H A rev (ms.map (examinePrime c (degree c)))
      (Id.run (twoAdic c (degree c))) (denBits (Id.run (twoAdic c (degree c)))) shape 1 H)).toList =
      (l.flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) :=
  toList_run_sieveRun_eq_flatMap hA (List.forall_mem_map.mpr fun _ hq ↦ (hms _ hq).pos) hdens
    hkeep fun _ _ _ h ↦ classBit_and_survives_of_ne_nil hms h

-- The shape of every denominator.
private theorem toList_run_sieveRun_all {c : List ℤ} {H A : ℕ} {ms : List ℕ}
    (hms : ∀ p ∈ ms, p.Prime) (hA : 1 ≤ A) (rev : Bool) :
    (Id.run (sieveRun c (degree c) H A rev (ms.map (examinePrime c (degree c)))
      (Id.run (twoAdic c (degree c))) (denBits (Id.run (twoAdic c (degree c)))) .all 1 H)).toList =
      ((List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) :=
  toList_run_sieveRun_of_sound hms hA rev (p := fun _ ↦ true) (by simp [Shape.dens])
    fun _ _ h ↦ ⟨rfl, by simpa [Shape.keep] using getElem!_twoAdic_ne_zero h⟩

-- The square shape, for odd degree and `|c_d| = 1`.
private theorem toList_run_sieveRun_squares {c : List ℤ} {H A : ℕ} {ms : List ℕ}
    (hms : ∀ p ∈ ms, p.Prime) (hA : 1 ≤ A) (rev : Bool) (hd : degree c % 2 = 1)
    (hc : (c.getD (degree c) 0).natAbs = 1) :
    (Id.run (sieveRun c (degree c) H A rev (ms.map (examinePrime c (degree c)))
      (Id.run (twoAdic c (degree c))) (denBits (Id.run (twoAdic c (degree c)))) .squares 1
        H)).toList =
      ((List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) := by
  refine toList_run_sieveRun_of_sound hms hA rev (p := fun b ↦ Nat.sqrt b * Nat.sqrt b == b)
    (by simp [Shape.dens, squaresDens_eq_filter (le_refl 1)]) fun b _ h ↦
      ⟨?_, by simpa [Shape.keep] using getElem!_twoAdic_ne_zero h⟩
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil h
  obtain ⟨r, rfl⟩ := isSquare_of_sq_eq_binaryForm_of_odd hd (Int.isUnit_iff_natAbs_eq.mpr hc) hg hy
  simp [Nat.sqrt_eq]

-- The divisor shape, for odd degree when the divisor set-up succeeds.
private theorem toList_run_sieveRun_squares1 {c : List ℤ} {H A : ℕ} {ms : List ℕ}
    (hms : ∀ p ∈ ms, p.Prime) (hA : 1 ≤ A) (rev : Bool) (hH : 1 ≤ H) (hd : degree c % 2 = 1)
    {info : List Setup.DenInfo} {divisors : List ℕ}
    (hs : Id.run (Setup.setupUs1 c (degree c) H) = some (info, divisors)) :
    (Id.run (sieveRun c (degree c) H A rev (ms.map (examinePrime c (degree c)))
      (Id.run (twoAdic c (degree c))) (denBits (Id.run (twoAdic c (degree c))))
        (.squares1 info divisors) 1 H)).toList =
      ((squares1Dens divisors 1 H).flatMap fun b : ℕ ↦
        pointsOfDen c (degree c) b (numerators H)).map (if rev then swapPoint else id) := by
  refine toList_run_sieveRun_of_sound hms hA rev (p := fun _ ↦ true) (by simp [Shape.dens])
    fun b hb h ↦ ⟨rfl, ?_⟩
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil h
  have hb0 : b ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (List.mem_range'_1.mp (mem_range'_of_mem_squares1Dens hH hd hs hb)).1
  simp [Shape.keep, getElem!_twoAdic_ne_zero h, run_denInfoTest_of_sq_eq hd hs hb0 hg hy]

-- The word shape, for even degree.
private theorem toList_run_sieveRun_words {c : List ℤ} {H A : ℕ} {ms : List ℕ}
    (hms : ∀ p ∈ ms, p.Prime) (hA : 1 ≤ A) (rev : Bool) (hd : degree c % 2 = 0) {maxF : ℕ}
    {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hf : Id.run (forbidden c (degree c) ms maxF H) = (forb, forbVal)) (useJacobi : Bool) :
    (Id.run (sieveRun c (degree c) H A rev (ms.map (examinePrime c (degree c)))
      (Id.run (twoAdic c (degree c))) (denBits (Id.run (twoAdic c (degree c))))
        (.words forb forbVal useJacobi
          (if useJacobi then Id.run (jacobiSetup (c.getD (degree c) 0) H) else none)
          (c.getD (degree c) 0)) 1 H)).toList =
      ((List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) := by
  have hforb (e : ForbiddenEntry) (he : e ∈ forb) :
      e ∈ (Id.run (forbidden c (degree c) ms maxF H)).1 := by rw [hf]; exact he
  refine toList_run_sieveRun_of_sound hms hA rev ?_ fun b hb h ↦
    have hb' := List.mem_range'_1.mp hb
    (exists_sq_eq_of_pointsOfDen_ne_nil h).elim fun _ ⟨_, _, hg, hy⟩ ↦
      ⟨getLsbD_denBits_and_all_of_sq_eq hms hd hf (by lia) (by lia) hg hy,
        run_wordsTest_of_sq_eq hms hd hf _ (by lia) (by lia) hg hy⟩
  simpa [Shape.dens] using toList_run_wordsDens
    (fun e he ↦ (prime_of_mem_forbidden_fst hms (hforb e he)).pos)
    (fun e he ↦ words_eq_of_mem_forbidden_fst (hforb e he)) 1 H

end Sieve

/-! ### The search -/

-- The shape that `Ratpoints.Sieve.runSetup` chooses from the flags of the search.
private theorem toList_run_sieveRun_runSetup {c : List ℤ} {H A : ℕ} {P : Params} (hP : P.WF)
    (hH : 1 ≤ H) (hA : 1 ≤ A) (rev : Bool) {us1 : Option (List Setup.DenInfo × List ℕ)}
    (hus1 : (if degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1 then
      Id.run (Setup.setupUs1 c (degree c) H) else none) = us1)
    {checkDenom useJacobi : Bool} {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hcd : checkDenom = true → degree c % 2 = 0 ∧
      Id.run (forbidden c (degree c) P.moduli P.maxForbidden H) = (forb, forbVal)) :
    (Id.run (sieveRun c (degree c) H A rev (P.moduli.map (examinePrime c (degree c)))
      (Id.run (twoAdic c (degree c))) (denBits (Id.run (twoAdic c (degree c))))
      (Id.run (runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) us1 checkDenom
        useJacobi forb forbVal (c.getD (degree c) 0) H)) 1 H)).toList =
      ((searchDens c (degree c) H).flatMap fun b : ℕ ↦
        pointsOfDen c (degree c) b (numerators H)).map (if rev then swapPoint else id) := by
  have hms (p : ℕ) (hp : p ∈ P.moduli) : p.Prime := hP.prime_of_mem hp
  rw [searchDens, hus1]
  rcases Nat.mod_two_eq_zero_or_one (degree c) with hd | hd
  · obtain rfl : us1 = none := by rw [← hus1, hd]; rfl
    rw [hd]
    cases checkDenom
    · exact toList_run_sieveRun_all hms hA rev
    · cases useJacobi <;> exact toList_run_sieveRun_words hms hA rev hd (hcd rfl).2 _
  by_cases hc : (c.getD (degree c) 0).natAbs = 1
  · obtain rfl : us1 = none := by rw [← hus1, hd, hc]; rfl
    rw [hd, hc]
    exact toList_run_sieveRun_squares hms hA rev hd hc
  have hflag : (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) = false := by
    rw [hd, beq_eq_false_iff_ne.mpr hc, Bool.and_false]
  rw [hflag]
  rcases us1 with _ | ⟨info, divisors⟩
  · obtain rfl : checkDenom = false := by cases checkDenom <;> simp_all
    exact toList_run_sieveRun_all hms hA rev
  · exact toList_run_sieveRun_squares1 hms hA rev hH hd (Option.ite_none_right_eq_some.mp hus1).2

-- A curve without points modulo a prime has an empty reference.
private theorem bruteForce_eq_nil_of_examinePrime?_eq_none {c : List ℤ} {p : ℕ} {u : Bool}
    (h : examinePrime? c (degree c) p u = none) (hp : p.Prime) (H : ℕ) : bruteForce c H = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun q hq ↦
    not_isPoint_of_examinePrime?_eq_none h hp H q (mem_bruteForce_iff.mp hq)

-- A curve whose classes of the denominators modulo 64 admit no numerator has an empty reference.
private theorem bruteForce_eq_nil_of_denBits_eq_zero {c : List ℤ}
    (h : denBits (Id.run (twoAdic c (degree c))) = 0) (H : ℕ) : bruteForce c H = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun q hq ↦
    not_isPoint_of_denBits_eq_zero h H q (mem_bruteForce_iff.mp hq)

-- A curve whose reference is empty has no points at infinity and none over the denominators of
-- its search, which lie in `1, …, H`.
private theorem nil_eq_of_bruteForce_eq_nil {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (h : bruteForce c H = []) (rev : Bool) :
    [] = (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
      fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) := by
  rw [bruteForce_eq_append c hH, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  rw [h.1, List.nil_append, List.flatMap_eq_nil_iff.mpr fun b hb ↦
    h.2 b (mem_range'_of_mem_searchDens hH hb), List.map_nil]

-- The 2-adic exit of the search: no class of the denominators admits a numerator, so that the
-- curve has no points.
private theorem nil_eq_of_denBits_eq_zero {c : List ℤ} {H : ℕ} (hH : 1 ≤ H) (rev : Bool)
    {nb : Vector UInt64 64} (hnb : nb = Id.run (twoAdic c (degree c)))
    (h : (denBits nb == 0 && !(degree c % 2 == 1 || Setup.isSquare (c.getD (degree c) 0))) = true) :
    [] = (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
      fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) := by
  subst hnb
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  exact nil_eq_of_bruteForce_eq_nil hH (bruteForce_eq_nil_of_denBits_eq_zero h.1 H) rev

-- The exit of the tables of the moduli: the curve has no points.
private theorem nil_eq_of_mapM_eq_none {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF) (hH : 1 ≤ H)
    (rev : Bool)
    (h : P.moduli.mapM (fun x ↦ examinePrime? c (degree c) x (Setup.useCLong c (degree c))) =
      none) :
    [] = (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
      fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) := by
  obtain ⟨_, hp, he⟩ := List.exists_mem_of_mapM_eq_none h
  exact nil_eq_of_bruteForce_eq_nil hH
    (bruteForce_eq_nil_of_examinePrime?_eq_none he (hP.prime_of_mem hp) H) rev

-- The run of the search after its exits, with the shape that `Ratpoints.Sieve.runSetup` chooses.
private theorem append_eq_of_mapM_eq_some {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF)
    (hH : 1 ≤ H) (rev : Bool) {entries : List Entry} {nb : Vector UInt64 64} {shape : Shape}
    {pts : Array (ℤ × ℤ × ℤ)}
    (hpts : pts = Id.run (sieveRun c (degree c) H (P.arraySizeAt H) rev entries nb (denBits nb)
      shape 1 H))
    {us1 : Option (List Setup.DenInfo × List ℕ)} {checkDenom useJacobi : Bool}
    {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hshape : shape = Id.run (runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) us1
      checkDenom useJacobi forb forbVal (c.getD (degree c) 0) H))
    (hm : P.moduli.mapM (fun x ↦ examinePrime? c (degree c) x (Setup.useCLong c (degree c))) =
      some entries) (hnb : nb = Id.run (twoAdic c (degree c)))
    (hus1 : (if degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1 then
      Id.run (Setup.setupUs1 c (degree c) H) else none) = us1)
    (hcd : checkDenom = true → degree c % 2 = 0 ∧
      Id.run (forbidden c (degree c) P.moduli P.maxForbidden H) = (forb, forbVal)) :
    pointsAtInfinity c (degree c) rev ++ pts.toList =
      (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
        fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
          (if rev then swapPoint else id) := by
  rw [List.eq_map_of_mapM_eq_some (fun _ _ _ ↦ eq_examinePrime_of_examinePrime?_eq_some) hm] at hpts
  subst hnb hshape hpts
  rw [toList_run_sieveRun_runSetup hP hH (P.one_le_arraySizeAt hH) rev hus1 hcd,
    pointsAtInfinity_eq_map, List.map_append]

-- The components of the search, as values for its contract.
private theorem setupUs1_value (c : List ℤ) (d bHigh : ℕ) :
    ⦃ True ⦄ Setup.setupUs1 c d bHigh ⦃ fun r ↦ r = Id.run (Setup.setupUs1 c d bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem twoAdic_value (c : List ℤ) (d : ℕ) :
    ⦃ True ⦄ twoAdic c d ⦃ fun r ↦ r = Id.run (twoAdic c d) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem forbidden_value (c : List ℤ) (d : ℕ) (moduli : List ℕ) (maxForbidden bHigh : ℕ) :
    ⦃ True ⦄ forbidden c d moduli maxForbidden bHigh
    ⦃ fun r ↦ r = Id.run (forbidden c d moduli maxForbidden bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem runSetup_value (useSquares : Bool) (us1 : Option (List Setup.DenInfo × List ℕ))
    (checkDenom useJacobi : Bool) (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal)
    (lcf : ℤ) (bHigh : ℕ) :
    ⦃ True ⦄ runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf bHigh
    ⦃ fun r ↦ r = Id.run (runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem sieveRun_value (c : List ℤ) (d H A : ℕ) (rev : Bool) (entries : List Entry)
    (nb : Vector UInt64 64) (db : UInt64) (shape : Shape) (bLow bHigh : ℕ) :
    ⦃ True ⦄ sieveRun c d H A rev entries nb db shape bLow bHigh
    ⦃ fun r ↦ r = Id.run (sieveRun c d H A rev entries nb db shape bLow bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

-- The contract of the search, for the degree of the polynomial.
private theorem searchPoints_spec (c : List ℤ) (H : ℕ) (P : Params) (rev : Bool) :
    ⦃ P.WF ∧ 1 ≤ H ⦄ searchPoints c (degree c) H P rev
    ⦃ fun r ↦ r = (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
        fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
          (if rev then swapPoint else id) ⦄ := by
  vcgen [searchPoints, setupUs1_value, twoAdic_value, forbidden_value, runSetup_value,
    sieveRun_value]
  all_goals first
    | exact nil_eq_of_denBits_eq_zero ‹P.WF ∧ 1 ≤ H›.2 rev ‹_› ‹_›
    | exact nil_eq_of_mapM_eq_none ‹P.WF ∧ 1 ≤ H›.1 ‹P.WF ∧ 1 ≤ H›.2 rev ‹_›
    | exact append_eq_of_mapM_eq_some ‹P.WF ∧ 1 ≤ H›.1 ‹P.WF ∧ 1 ≤ H›.2 rev ‹_› ‹_› ‹_› ‹_›
        (by split <;> simp_all) (by intro; simp_all)

/-- The run of the shape that `Ratpoints.Sieve.runSetup` chooses gives the reference over the
denominators of the search, its tests and the class words being sound
(`Ratpoints.Sieve.toList_run_sieveRun_eq_flatMap`); when the search takes the exit of a table or the
2-adic exit, the curve has no points (`Ratpoints.Sieve.not_isPoint_of_examinePrime?_eq_none`,
`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`), so that both sides are empty. -/
theorem run_searchPoints {c : List ℤ} {d H : ℕ} {P : Params} (hP : P.WF) (hH : 1 ≤ H)
    (hd : d = degree c) (rev : Bool) :
    Id.run (searchPoints c d H P rev) =
      (pointsAtInfinity c d false ++ (searchDens c d H).flatMap fun b : ℕ ↦
        pointsOfDen c d b (numerators H)).map (if rev then swapPoint else id) := by
  subst hd
  exact (searchPoints_spec c H P rev).le_wp ⟨hP, hH⟩

/-! ### The output of `Ratpoints.findPoints` -/

/-- For well-formed parameters, the list that `Ratpoints.findPoints` returns is that of the search
of the polynomial `c'` of degree `d'` that the reversal check hands on
(`Ratpoints.run_searchPoints`): its points at infinity and those of the denominators of its search,
mapped back by `Ratpoints.Sieve.swapPoint` after a reversal; also when the search takes an exit,
since the curve has no points then. -/
theorem exists_eq_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) :
    ∃ c' d' rev, Setup.reversal o.reverse c (degree c) = .ok (c', d', rev) ∧ d' = degree c' ∧
      1 ≤ H ∧ L = (pointsAtInfinity c' d' false ++ (searchDens c' d' H).flatMap fun b : ℕ ↦
        pointsOfDen c' d' b (numerators H)).map (if rev then swapPoint else id) := by
  simp only [findPoints] at h
  split_ifs at h
  split at h
  · cases h
  rename_i c' d' rev hr
  split_ifs at h
  cases h
  have hd := (Setup.degree_eq_of_reversal_eq_ok rfl hr).symm
  exact ⟨c', d', rev, hr, hd, by lia, run_searchPoints hP (by lia) hd rev⟩

/-- When the options forbid the reversal and the denominators of the search are `1, …, H`
(`Ratpoints.searchDens_eq_range'`: even degree, `|c_d| = 1`, or the divisor set-up fails), the list
that `Ratpoints.findPoints` returns is the brute-force reference itself. -/
theorem eq_bruteForce_of_findPoints_eq_ok_of_reverse_eq_false {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (ho : o.reverse = false) (hs : searchDens c (degree c) H = List.range' 1 H) :
    L = bruteForce c H := by
  obtain ⟨c', d', rev, hr, rfl, hH, rfl⟩ := exists_eq_of_findPoints_eq_ok hP h
  rw [ho, Setup.reversal_false] at hr
  cases hr
  simpa using append_flatMap_searchDens_eq_bruteForce hH hs

/-- For well-formed parameters, the list that `Ratpoints.findPoints` returns is a permutation of
the brute-force reference: the search gives the reference of the polynomial searched in the order
of its denominators (`Ratpoints.perm_bruteForce_append_flatMap_searchDens`), and after a reversal
the binary form of the polynomial searched is that of `c` with `x` and `z` exchanged
(`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`), so that its reference, mapped back, is a
permutation of that of `c` (`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`). -/
theorem perm_bruteForce_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) :
    L.Perm (bruteForce c H) := by
  obtain ⟨c', d', rev, hr, rfl, hH, rfl⟩ := exists_eq_of_findPoints_eq_ok hP h
  have hp := (perm_bruteForce_append_flatMap_searchDens c' hH).map (if rev then swapPoint else id)
  cases rev
  · simpa [(Setup.eq_of_reversal_eq_ok_false hr).1] using hp
  · exact hp.trans (perm_map_swapPoint_bruteForce (Setup.binaryForm_eq_of_reversal_eq_ok rfl hr) H)

/-! ### The main theorems -/

/-- For well-formed parameters and every option, a triple lies in the list that
`Ratpoints.findPoints` returns exactly when it is a normalized point of height at most `H`;
comparator certifies this (`comparator/Challenge.lean`). -/
theorem mem_iff_isPoint_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) {p : ℤ × ℤ × ℤ} :
    p ∈ L ↔ IsPoint c H p :=
  (perm_bruteForce_of_findPoints_eq_ok hP h).mem_iff.trans mem_bruteForce_iff

/-- For well-formed parameters and every option, the list that `Ratpoints.findPoints` returns has
no duplicates; comparator certifies this (`comparator/Challenge.lean`). -/
theorem nodup_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) : L.Nodup :=
  (perm_bruteForce_of_findPoints_eq_ok hP h).nodup_iff.mpr (nodup_bruteForce c H)

theorem toFinset_eq_points_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) :
    L.toFinset = points c H :=
  (List.toFinset_eq_of_perm _ _ (perm_bruteForce_of_findPoints_eq_ok hP h)).trans
    (toFinset_bruteForce c H)

/-! ### The refusals -/

/-- With the Sturm step on (`0 ≤ o.sturm`, as in a run of the program without options),
`Ratpoints.findPoints` refuses exactly the inputs with fewer than two or more than
`Ratpoints.maxDegree + 1` coefficients, the height bound `0` and the binary forms
`Ratpoints.binaryFormPoly c` that are not squarefree, for all parameters, whether the reversal is
allowed or not; comparator certifies this (`comparator/Challenge.lean`). -/
theorem exists_findPoints_eq_error_iff_of_sturm_nonneg {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} (hs : 0 ≤ o.sturm) :
    (∃ e, findPoints c H P o = .error e) ↔
      c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 ∨ ¬ Squarefree (binaryFormPoly c) := by
  rw [findPoints]
  dsimp only
  rw [BruteForce.degree_eq]
  split_ifs with h1 h2 h3 h4
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · simp [not_squarefree_binaryFormPoly_of_lt h4]
  simp only [h1, h2, h3, false_or]
  split <;> rename_i hr
  · exact iff_of_true ⟨_, rfl⟩ (Setup.not_squarefree_binaryFormPoly_of_reversal_eq_error hr)
  · rw [← Sturm.run_chain_eq_none_iff_of_reversal_eq_ok (by lia) (by lia) hr]
    split_ifs <;> simp_all

/-- Without the Sturm step (`o.sturm < 0`, the option `-s` of the program), `Ratpoints.findPoints`
refuses, besides the coefficient lists of fewer than two or more than `Ratpoints.maxDegree + 1`
entries and the height bound `0`, exactly the forms whose leading zeros lower `⌈n / 2⌉`, for `n + 1`
coefficients, that is `d + 2 ≤ 2 ⌈n / 2⌉` for the degree `d`, and, when the reversal is allowed,
those of even degree with `c₀ = c₁ = 0`: forms that are not squarefree, but not all of them;
comparator certifies this (`comparator/Challenge.lean`), so that a `Ratpoints.findPoints` that
refused every input under `-s` would not pass. -/
theorem exists_findPoints_eq_error_iff_of_sturm_neg {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} (hs : o.sturm < 0) :
    (∃ e, findPoints c H P o = .error e) ↔
      c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 ∨ degree c + 2 ≤ 2 * (c.length / 2) ∨
        o.reverse = true ∧ degree c % 2 = 0 ∧ c.getD 0 0 = 0 ∧ c.getD 1 0 = 0 := by
  rw [findPoints]
  dsimp only
  rw [BruteForce.degree_eq]
  split_ifs with h1 h2 h3 h4
  · simp [h1]
  · simp [h2]
  · simp [h3]
  · simp only [Except.error.injEq, exists_eq', true_iff]
    lia
  simp only [h1, h2, h3, false_or, show ¬ degree c + 2 ≤ 2 * (c.length / 2) by lia,
    ← Setup.exists_reversal_eq_error_iff]
  split <;> rename_i hr <;> simp [hr, hs.not_ge]

/-! ### The axioms of the main theorems -/

/--
info: 'Ratpoints.perm_bruteForce_of_findPoints_eq_ok' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms perm_bruteForce_of_findPoints_eq_ok

/--
info: 'Ratpoints.mem_iff_isPoint_of_findPoints_eq_ok' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms mem_iff_isPoint_of_findPoints_eq_ok

/--
info: 'Ratpoints.nodup_of_findPoints_eq_ok' depends on axioms: [propext, Classical.choice,
Quot.sound]
-/
#guard_msgs in
#print axioms nodup_of_findPoints_eq_ok

/--
info: 'Ratpoints.toFinset_eq_points_of_findPoints_eq_ok' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms toFinset_eq_points_of_findPoints_eq_ok

/--
info: 'Ratpoints.exists_findPoints_eq_error_iff_of_sturm_nonneg' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_findPoints_eq_error_iff_of_sturm_nonneg

/--
info: 'Ratpoints.exists_findPoints_eq_error_iff_of_sturm_neg' depends on axioms: [propext,
Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms exists_findPoints_eq_error_iff_of_sturm_neg

end Ratpoints

end
