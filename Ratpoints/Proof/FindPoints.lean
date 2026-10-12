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
import Ratpoints.Proof.Sieve
import Ratpoints.Proof.Tables
import Ratpoints.Proof.TwoAdic

/-!
# The sieve finds exactly the points, and the refusals

The search of the polynomial that the set-up hands on gives, for well-formed parameters, the list of
the brute-force reference of the polynomial with its degree, mapped by `Ratpoints.Sieve.swapPoint`
when the flag of the reversal is set, also when it takes one of its exits
(`Ratpoints.run_searchPoints`): the points at infinity, followed by the run over the denominators
`1, …, H` in the shape of every denominator, whose filters, the class test, the class words and the
tables, let every point through. So the list that `Ratpoints.findPoints c H P o` returns is the
reference of the polynomial that the reversal check hands on, mapped back after a reversal, and the
reference of `c` itself when the check does not reverse (`Ratpoints.exists_eq_of_findPoints_eq_ok`):
in every case a permutation of the reference of `c`, so that it holds exactly the points of the
specification, each once, for every option. `Ratpoints.findPoints` refuses exactly the inputs that
the program refuses: with the Sturm step on, those with fewer than two or more than
`Ratpoints.maxDegree + 1` coefficients, the height bound `0` and the binary forms `Φ_c` that are not
squarefree; without it, instead of the last, those that the test of the leading zeros and the
reversal check refuse. Comparator certifies the membership, the absence of duplicates and both
refusal theorems (`comparator/Challenge.lean`).

## Main statements

* `Ratpoints.run_searchPoints`: for well-formed parameters, `H ≥ 1` and the degree of the
  polynomial, the search gives the list of `Ratpoints.bruteForce`, with the flag of the reversal
  clear, and that list mapped by `Ratpoints.Sieve.swapPoint` when it is set, also when it takes an
  exit.
* `Ratpoints.exists_eq_of_findPoints_eq_ok`: for well-formed parameters, every list that
  `Ratpoints.findPoints` returns is the list of the reference of the polynomial that the reversal
  check hands on, mapped back after a reversal, and that of `c` without a reversal;
  `Ratpoints.eq_bruteForce_of_findPoints_eq_ok_of_reverse_eq_false`: in particular when the options
  forbid the reversal.
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
pieces of at least one bit array and moduli that are primes, hence positive, the run in the shape of
every denominator gives the reference over `1, …, H`, mapped when the flag of the reversal is set,
since its filters let every point through: the word of the class of the denominator of a point in
the 2-adic information is not `0` (`Ratpoints.Sieve.getElem!_twoAdic_ne_zero`), and every numerator
over which the exact check finds a point passes the word of its class and survives the tables
(`Ratpoints.Sieve.classBit_and_survives_of_ne_nil`); and the points at infinity are those of the
candidate `(1, 0)` of the reference (`Ratpoints.Sieve.pointsAtInfinity_eq_pointsOfDen`), mapped when
the flag is set (`Ratpoints.Sieve.pointsAtInfinity_eq_map`). In the search, the pieces have at least
one bit array (`Ratpoints.Params.one_le_arraySizeAt`) and the moduli of well-formed parameters are
primes (`Ratpoints.Params.WF.prime_of_mem`); a table that the search makes is that of the reference
(`Ratpoints.Sieve.eq_examinePrime_of_examinePrime?_eq_some`); when the search takes the exit of a
table, the curve has no points (`Ratpoints.Sieve.not_isPoint_of_examinePrime?_eq_none`), and when it
takes the 2-adic exit, no class of the denominators admits a numerator, so that the curve has no
points either (`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`): the reference is empty.
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
-/

@[expose] public section

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

/-! ### The search -/

-- The reference with its points at infinity apart.
private theorem bruteForce_eq_append (c : List ℤ) {H : ℕ} (hH : 1 ≤ H) :
    bruteForce c H = pointsAtInfinity c (degree c) false ++
      (List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H) := by
  simp [bruteForce, hH, pointsAtInfinity_eq_pointsOfDen, List.range'_eq_map_range, Nat.add_comm,
    List.flatMap_map, BruteForce.degree_eq]

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

-- The run in the shape of every denominator, with the tables of the primes `ms` and the words of
-- the 2-adic information: its filters let every point through.
private theorem toList_run_sieveRun_all {c : List ℤ} {H A : ℕ} {ms : List ℕ}
    (hms : ∀ p ∈ ms, p.Prime) (hA : 1 ≤ A) (rev : Bool) :
    (Id.run (sieveRun c (degree c) H A rev (ms.map (examinePrime c (degree c)))
      (Id.run (twoAdic c (degree c))) (denBits (Id.run (twoAdic c (degree c)))) .all 1 H)).toList =
      ((List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) :=
  toList_run_sieveRun_eq_flatMap hA (List.forall_mem_map.mpr fun _ hq ↦ (hms _ hq).pos)
    (p := fun _ ↦ true) (by simp [Shape.dens])
    (fun _ _ h ↦ ⟨rfl, by simpa [Shape.keep] using getElem!_twoAdic_ne_zero h⟩)
    fun _ _ _ h ↦ classBit_and_survives_of_ne_nil hms h

/-- The search takes the 2-adic exit only when no class of the denominators admits a numerator, and
the exit of a table only when the curve has no points modulo that prime, and the curve has no points
then (`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`,
`Ratpoints.Sieve.not_isPoint_of_examinePrime?_eq_none`); otherwise the tables that it makes are
those of the reference (`Ratpoints.Sieve.eq_examinePrime_of_examinePrime?_eq_some`), on which the
run in the shape of every denominator gives the reference over `1, …, H`
(`Ratpoints.Sieve.toList_run_sieveRun_eq_flatMap`), after the points at infinity of the candidate
`(1, 0)` (`Ratpoints.Sieve.pointsAtInfinity_eq_pointsOfDen`). -/
theorem run_searchPoints {c : List ℤ} {d H : ℕ} {P : Params} (hP : P.WF) (hH : 1 ≤ H)
    (hd : d = degree c) (rev : Bool) :
    Id.run (searchPoints c d H P rev) = (bruteForce c H).map (if rev then swapPoint else id) := by
  subst hd
  simp only [searchPoints, Id.run_bind]
  split <;> rename_i h2
  · simp only [Bool.and_eq_true, beq_iff_eq] at h2
    simp [bruteForce_eq_nil_of_denBits_eq_zero h2.1 H]
  split <;> rename_i hm
  · obtain ⟨_, hp, he⟩ := List.exists_mem_of_mapM_eq_none hm
    simp [bruteForce_eq_nil_of_examinePrime?_eq_none he (hP.prime_of_mem hp) H]
  · rw [List.eq_map_of_mapM_eq_some (fun _ _ _ ↦ eq_examinePrime_of_examinePrime?_eq_some) hm]
    simp only [Id.run_bind, Id.run_pure]
    rw [toList_run_sieveRun_all (fun _ ↦ hP.prime_of_mem) (P.one_le_arraySizeAt hH) rev,
      bruteForce_eq_append c hH, pointsAtInfinity_eq_map, List.map_append]

/-! ### The output of `Ratpoints.findPoints` -/

/-- For well-formed parameters, the list that `Ratpoints.findPoints` returns is the list of the
brute-force reference of the polynomial `c'` that the reversal check hands on, mapped back by
`Ratpoints.Sieve.swapPoint` after a reversal, and the reference of `c` itself when the check does
not reverse (`Ratpoints.run_searchPoints`); also when the search takes the exit, since the reference
is empty then. -/
theorem exists_eq_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) :
    ∃ c' d' rev, Setup.reversal o.reverse c (degree c) = .ok (c', d', rev) ∧
      L = if rev then (bruteForce c' H).map swapPoint else bruteForce c H := by
  simp only [findPoints] at h
  split_ifs at h
  split at h
  · cases h
  rename_i c' d' rev hr
  split_ifs at h
  cases h
  refine ⟨c', d', rev, hr, ?_⟩
  rw [run_searchPoints hP (by lia) (Setup.degree_eq_of_reversal_eq_ok rfl hr).symm]
  cases rev
  · simp [(Setup.eq_of_reversal_eq_ok_false hr).1]
  · rfl

theorem eq_bruteForce_of_findPoints_eq_ok_of_reverse_eq_false {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L)
    (ho : o.reverse = false) : L = bruteForce c H := by
  obtain ⟨c', d', rev, hr, rfl⟩ := exists_eq_of_findPoints_eq_ok hP h
  rw [ho, Setup.reversal_false] at hr
  cases hr
  rfl

/-- For well-formed parameters, the list that `Ratpoints.findPoints` returns is a permutation of
the brute-force reference: after a reversal, the binary form of the polynomial searched is that of
`c` with `x` and `z` exchanged (`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`), so that its
reference, mapped back, is a permutation of that of `c`
(`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`). -/
theorem perm_bruteForce_of_findPoints_eq_ok {c : List ℤ} {H : ℕ} {P : Params} {o : Options}
    {L : List (ℤ × ℤ × ℤ)} (hP : P.WF) (h : findPoints c H P o = .ok L) :
    L.Perm (bruteForce c H) := by
  obtain ⟨c', d', rev, hr, rfl⟩ := exists_eq_of_findPoints_eq_ok hP h
  cases rev
  · exact .refl _
  · exact perm_map_swapPoint_bruteForce (Setup.binaryForm_eq_of_reversal_eq_ok rfl hr) H

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
