/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Forbidden
public import Ratpoints.Proof.Moduli
public import Ratpoints.Proof.Stages

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
bound `0` or one of `2 ^ 63` or more, which is not a `long`, and the binary forms `Φ_c` that are not
squarefree; without it, instead of the last, those that the test of the leading zeros and the
reversal check refuse. Comparator certifies the membership, the absence of duplicates and both
refusal theorems (`comparator/Challenge.lean`).

## Main definitions

* `Ratpoints.Sieve.SieveEntry.IsSound`: a sieve entry with a positive modulus that admits the
  numerator of every point.
* `Ratpoints.Sieve.IsSoundRun`: what the run of the search needs of its arguments.
* `Ratpoints.SievingInfoEntries`, `Ratpoints.SievingInfoInvariant`: what the loop over the moduli of
  `Ratpoints.sievingInfo` has made before a return, and its invariant.
* `Ratpoints.IsSievingInfo`: what the search needs of the result of `Ratpoints.sievingInfo`.
* `Ratpoints.searchDens`: the denominators of the search, in the order of its loop.

## Main statements

* `Ratpoints.perm_bruteForce_append_flatMap_searchDens`: the points at infinity and those of the
  denominators of the search are a permutation of the brute-force reference;
  `Ratpoints.append_flatMap_searchDens_eq_bruteForce`: they are the reference when the denominators
  of the search are `1, …, H` (`Ratpoints.searchDens_eq_range'`).
* `Ratpoints.sievingInfo_spec`: for well-formed parameters, the sieve entries that
  `Ratpoints.sievingInfo` makes are those of the moduli, in their order, are sound, have the fields
  that the packing reads and the tables of inverses of their factors, and hold the reciprocals of
  their moduli, which it returns in the order of the entries, those of the third stage having the
  shape that it needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), its forbidden divisors are among
  those that the loops of the tables and of the further primes may record, and the store of the
  tables of rows that it returns fits the entries (`Ratpoints.Sieve.RowStore.Fits`); when it returns
  none, the curve has no points.
* `Ratpoints.run_searchPoints`: for well-formed parameters, `1 ≤ H < 2 ^ 63` and the degree of the
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
  `Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or more, and the
  forms that are not squarefree.
* `Ratpoints.exists_findPoints_eq_error_iff_of_sturm_neg`: without it, those with fewer than two or
  more than `Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or
  more, a degree `d` with `d + 2 ≤ 2 ⌈n / 2⌉`, and, when the reversal is allowed, an even degree
  with `c₀ = c₁ = 0`.

## Proof

By the reduction of the run to the reference (`Ratpoints.Sieve.toList_run_sieveRun_eq_flatMap`), for
pieces of at least one bit array, sieve entries and their reciprocals, of which those of the first
two stages have their tables of inverses and the row offsets of the packings of the classes, which
pack the words of the 2-adic information, and those of the third stage the shape that it needs
(`Ratpoints.Sieve.IsSoundRun`), and denominators and a height below `2 ^ 63`, the run gives the
reference over the list of its shape when its filters are sound: every numerator of a point passes
the word of the class of its denominator and survives the sieve entries, when they are sound
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
(`Ratpoints.Params.one_le_arraySizeAt`), and the height, the largest denominator, is below `2 ^ 63`
by the refusals of `Ratpoints.findPoints`; the tables of the loop of the tables are those of the
reference (`Ratpoints.Sieve.getElem_eq_examinePrime_of_run_examinePrimes_eq_some`), so that the
sieve entries that the loop over the moduli of well-formed parameters makes are sound, have the
tables of inverses of their factors and the fields that the packing reads, and hold the reciprocals
of their moduli, which it returns in their order, and those of the moduli of the third stage, primes
among the first `Ratpoints.numPrimes` of the table, have the prime with the table of the reference
as their only factor (`Ratpoints.makeModulus?_spec`, `Ratpoints.SievingInfoInvariant.push`,
`Ratpoints.Sieve.isPrimeEntry_examinePrime`); each entry has the reference to its table of rows and
the kind of its builder of its position, so that the store that the loop of the tables starts
(`Ratpoints.Sieve.primeStore_of_run_examinePrimes_eq_some`) and the tables of rows of the entries
complete holds the rows of the references of the run (`Ratpoints.Sieve.runRows`,
`Ratpoints.Sieve.RowStore.MadeFor`), which every entry fits (`Ratpoints.SievingInfoEntries.fits`);
and the forbidden divisors are those that the loops of the tables and of the further primes may
record (`Ratpoints.Sieve.isForbiddenEntry_of_run_examinePrimes_eq_some`,
`Ratpoints.Sieve.forbidden_spec` and their counterparts for the valuations), with the switch of the
forbidden divisors on or off; the classes that `Ratpoints.Sieve.numClasses` makes pack the words of
the 2-adic information, with `den_bits` the word of `Ratpoints.Sieve.denBits`
(`Ratpoints.Sieve.snd_run_numClasses`), and `Ratpoints.Sieve.classOffsets`, in the array of
`Ratpoints.Sieve.numPackings` rows, gives each class with a pattern its row offsets and the entries
the inverses of the strides (`Ratpoints.Sieve.numClasses_spec`,
`Ratpoints.Sieve.classOffsets_spec`); when the search takes the exit of the loop of the tables or of
a modulus, the curve has no points (`Ratpoints.Sieve.not_isPoint_of_run_examinePrimes_eq_none`,
`Ratpoints.makeModulus?_spec`), and when it takes the 2-adic exit, no class of the denominators
admits a numerator, the word `den_bits` of the classes being that of `Ratpoints.Sieve.denBits`
(`Ratpoints.Sieve.snd_run_numClasses`), so that the curve has no points either
(`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`): the reference is empty, and so are the points at
infinity and those of the denominators of the search, which lie in `1, …, H`. `Ratpoints.findPoints`
runs the search on the polynomial that the reversal check hands on, with its degree
(`Ratpoints.Setup.degree_eq_of_reversal_eq_ok`) and its flag of the reversal; the binary form of a
reversed polynomial is that of `c` with `x` and `z` exchanged
(`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`), so that its reference, mapped back, is a
permutation of that of `c` (`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`). Of the refusals, the
heights that are not `long`s are those of `2 ^ 63` or more (`Ratpoints.fitsLong_natCast`), and the
test of the leading zeros and that of the reversal check stand for `Z ^ 2 ∣ Φ_c` and `X ^ 2 ∣ Φ_c`
(`Ratpoints.not_squarefree_binaryFormPoly_of_lt`,
`Ratpoints.Setup.not_squarefree_binaryFormPoly_of_reversal_eq_error`), and after them the remainder
chain of the polynomial searched is none exactly when `Φ_c` is not squarefree
(`Ratpoints.Sturm.run_chain_eq_none_iff_of_reversal_eq_ok`).

## Implementation notes

The search is proved with `vcgen`, which reads its components (the divisor set-up, the 2-adic
information, what `Ratpoints.sievingInfo` computes, the choice of the shape and the run) through
private specifications `⦃True⦄ x ⦃fun r ↦ r = Id.run x⦄`, so that its verification conditions speak
of the values of the components; the run of the shape that `Ratpoints.Sieve.runSetup` chooses is
handled by cases in one lemma. The exits use only that the denominators of the search lie in
`1, …, H`, so that the contract of the search does not rest on the permutation of the reference
(`Ratpoints.perm_bruteForce_append_flatMap_searchDens`), which the theorems on
`Ratpoints.findPoints` use. The contract of `Ratpoints.sievingInfo` is proved with `vcgen` as well,
with the loop invariant `Ratpoints.SievingInfoInvariant`, reading the loop of the tables through
such a private specification and the further primes and the sieve entries of the moduli through
their contracts.
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

/-- A sieve entry that lets the numerator of every point of the curve `y ^ 2 = F(x, z)` with the
coefficient list `c` through: its modulus is positive, and its row of the denominator `b` admits the
numerator `a` of every triple `(a, y, b)` with `gcd(a, b) = 1` and `y ^ 2 = F(a, b)`. For
well-formed parameters, the search makes only such entries (`Ratpoints.sievingInfo_spec`). -/
structure SieveEntry.IsSound (c : List ℤ) (e : SieveEntry) : Prop where
  /-- The modulus is positive. -/
  pos : 0 < e.p
  /-- The row of the denominator of every point admits its numerator. -/
  admits_of_sq_eq {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    e.admits b a = true

theorem survives_of_mem_pointsOfDen {c : List ℤ} {entries : List SieveEntry}
    (hent : ∀ e ∈ entries, e.IsSound c) {b : ℕ} {xs : List ℤ} {q : ℤ × ℤ × ℤ}
    (hq : q ∈ pointsOfDen c (BruteForce.degree c) b xs) : survives entries b q.1 = true := by
  obtain ⟨x, y, z⟩ := q
  obtain ⟨-, rfl, hg, hy⟩ := mem_pointsOfDen_iff.mp hq
  rw [horner_scaledCoeffs_mul] at hy
  exact List.all_eq_true.mpr fun e he ↦ (hent e he).admits_of_sq_eq hg hy

theorem pointsAtInfinity_eq_pointsOfDen (c : List ℤ) (d : ℕ) :
    pointsAtInfinity c d false = pointsOfDen c d 0 [1] := by
  simp only [pointsAtInfinity, pointsOfDen_singleton, Int.gcd_one_left, reduceCtorEq, ↓reduceIte,
    horner_scaledCoeffs_one_zero]
  split_ifs <;> simp [pointsAbove]

theorem pointsAtInfinity_eq_map (c : List ℤ) (d : ℕ) (rev : Bool) :
    pointsAtInfinity c d rev =
      (pointsAtInfinity c d false).map (if rev then swapPoint else id) := by
  cases rev <;> simp [pointsAtInfinity, pointsAbove, apply_ite (List.map swapPoint), swapPoint]

/-- The class word of the denominator `b` and sound sieve entries let the numerator of every point
over `b` through (`Ratpoints.Sieve.classBit_twoAdic_of_sq_eq`,
`Ratpoints.Sieve.survives_of_mem_pointsOfDen`). -/
theorem classBit_and_survives_of_ne_nil {c : List ℤ} {entries : List SieveEntry}
    (hent : ∀ e ∈ entries, e.IsSound c) {b : ℕ} {a : ℤ} (h : pointsOfDen c (degree c) b [a] ≠ []) :
    classBit (Id.run (twoAdic c (degree c)))[b % 64]! a = true ∧
      survives entries b a = true := by
  obtain ⟨q, hq⟩ := List.exists_mem_of_ne_nil _ h
  obtain ⟨hx, -, hg, hy⟩ := mem_pointsOfDen_iff.mp hq
  obtain rfl := List.mem_singleton.mp hx
  exact ⟨classBit_twoAdic_of_sq_eq hg (hy.trans (horner_scaledCoeffs_mul c _ _)),
    survives_of_mem_pointsOfDen hent hq⟩

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
private theorem mem_range'_of_mem_squares1Dens {divisors : List ℕ} {H b : ℕ}
    (hb : b ∈ squares1Dens divisors 1 H) : b ∈ List.range' 1 H :=
  have := le_and_le_of_mem_squares1Dens le_rfl hb
  List.mem_range'_1.mpr ⟨this.1, by lia⟩

-- The denominators of the search lie in `1, …, H`.
private theorem mem_range'_of_mem_searchDens {c : List ℤ} {H b : ℕ}
    (hb : b ∈ searchDens c (degree c) H) : b ∈ List.range' 1 H := by
  obtain h | ⟨_, _, -, -, h⟩ := searchDens_eq_range'_or c (degree c) H
  · rwa [h] at hb
  · exact mem_range'_of_mem_squares1Dens (h ▸ hb)

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
    (fun _ ↦ mem_range'_of_mem_squares1Dens) fun b hb hne ↦ ?_
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

/-- What the run of the search needs of its arguments for the curve `y ^ 2 = F(x, z)` with the
coefficient list `c`: sound sieve entries (`Ratpoints.Sieve.SieveEntry.IsSound`), those of the
first two stages, the first `sp2`, with their tables of inverses and the row offsets of the
packings of the classes `cls` (`Ratpoints.Sieve.OffsetsFor`), those of the third stage of the shape
that it needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), the reciprocals of the moduli in the
order of the entries, classes that pack the words of the 2-adic information
(`Ratpoints.Sieve.twoAdic`), and the word `db` of the classes that admit a numerator
(`Ratpoints.Sieve.denBits`). -/
structure IsSoundRun (c : List ℤ) (sp2 : ℕ) (entries : List SieveEntry) (magics : Array ℕ)
    (cls : Vector NumClass 64) (offsets : Array ℕ) (db : UInt64) : Prop where
  /-- The sieve entries are sound. -/
  isSound : ∀ e ∈ entries, e.IsSound c
  /-- The sieve entries of the third stage have the shape that it needs. -/
  isPrimeEntry : ∀ e ∈ entries.drop sp2, e.IsPrimeEntry
  /-- The reciprocals of the moduli, in the order of the entries. -/
  magics_eq : magics.toList = entries.map fun e ↦ magic e.p
  /-- The sieve entries of the first two stages have their tables of inverses. -/
  hasInverses : ∀ e ∈ entries.take sp2, ∀ f ∈ e.factors, f.HasInverses e.p
  /-- The classes with a pattern have their row offsets for the first two stages. -/
  offsetsFor : OffsetsFor cls (entries.take sp2) offsets
  /-- The classes pack the words of the 2-adic information. -/
  packs : ∀ b < 64, cls[b]!.Packs (Id.run (twoAdic c (degree c)))[b]!
  /-- The word of the classes that admit a numerator. -/
  db_eq : db = denBits (Id.run (twoAdic c (degree c)))

/-- The class test of a sound run on the denominator `b` is the test of the word of its class in
the 2-adic information. -/
theorem IsSoundRun.bits_bne_zero {c : List ℤ} {sp2 : ℕ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    (h : IsSoundRun c sp2 entries magics cls offsets db) (b : ℕ) :
    (cls[b % 64]!.bits != 0) = ((Id.run (twoAdic c (degree c)))[b % 64]! != 0) :=
  (h.packs _ (Nat.mod_lt _ (by decide))).bits_bne_zero

/-- The bits of the word `db` of a sound run are those of its classes with a pattern. -/
theorem IsSoundRun.getLsbD_db {c : List ℤ} {sp2 : ℕ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    (h : IsSoundRun c sp2 entries magics cls offsets db) {j : ℕ} (hj : j < 64) :
    db.toBitVec.getLsbD j = (cls[j]!.bits != 0) := by
  rw [h.db_eq, getLsbD_denBits, decide_eq_true hj, Bool.true_and, (h.packs j hj).bits_bne_zero]

-- The run with sound arguments, for a shape whose list is `l` filtered by `p` and whose tests let
-- the denominator of every point through.
private theorem toList_run_sieveRun_of_sound {c : List ℤ} {H A sp1 sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} (hrun : IsSoundRun c sp2 entries magics cls offsets db) (hH63 : H < 2 ^ 63)
    (hA : 1 ≤ A) (rev : Bool) {shape : Shape} {l : List ℕ} {p : ℕ → Bool}
    (hdens : Id.run (shape.dens db 1 H) = l.filter p)
    (hkeep : ∀ b ∈ l, pointsOfDen c (degree c) b (numerators H) ≠ [] →
      p b = true ∧ Id.run (shape.keep cls b) = true) :
    (Id.run (sieveRun c (degree c) H A rev sp1 sp2 entries magics cls offsets db shape 1
      H)).toList = (l.flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) :=
  toList_run_sieveRun_eq_flatMap hA hrun.isPrimeEntry hrun.magics_eq hrun.hasInverses
    hrun.offsetsFor (fun _ ↦ hrun.getLsbD_db) hrun.packs le_rfl hH63 hH63 hdens hkeep
    fun _ _ _ h ↦ classBit_and_survives_of_ne_nil hrun.isSound h

-- The shape of every denominator.
private theorem toList_run_sieveRun_all {c : List ℤ} {H A sp1 sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} (hrun : IsSoundRun c sp2 entries magics cls offsets db) (hH63 : H < 2 ^ 63)
    (hA : 1 ≤ A) (rev : Bool) :
    (Id.run (sieveRun c (degree c) H A rev sp1 sp2 entries magics cls offsets db .all 1 H)).toList =
      ((List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) :=
  toList_run_sieveRun_of_sound hrun hH63 hA rev (p := fun _ ↦ true) (by simp [Shape.dens])
    fun b _ h ↦ ⟨rfl, by simpa [Shape.keep, hrun.bits_bne_zero b] using getElem!_twoAdic_ne_zero h⟩

-- The square shape, for odd degree and `|c_d| = 1`.
private theorem toList_run_sieveRun_squares {c : List ℤ} {H A sp1 sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} (hrun : IsSoundRun c sp2 entries magics cls offsets db) (hH63 : H < 2 ^ 63)
    (hA : 1 ≤ A) (rev : Bool) (hd : degree c % 2 = 1) (hc : (c.getD (degree c) 0).natAbs = 1) :
    (Id.run (sieveRun c (degree c) H A rev sp1 sp2 entries magics cls offsets db .squares 1
      H)).toList =
      ((List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) := by
  refine toList_run_sieveRun_of_sound hrun hH63 hA rev
    (p := fun b ↦ Nat.sqrt b * Nat.sqrt b == b)
    (by simp [Shape.dens, squaresDens_eq_filter (le_refl 1)]) fun b _ h ↦
      ⟨?_, by simpa [Shape.keep, hrun.bits_bne_zero b] using getElem!_twoAdic_ne_zero h⟩
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil h
  obtain ⟨r, rfl⟩ := isSquare_of_sq_eq_binaryForm_of_odd hd (Int.isUnit_iff_natAbs_eq.mpr hc) hg hy
  simp [Nat.sqrt_eq]

-- The divisor shape, for odd degree when the divisor set-up succeeds.
private theorem toList_run_sieveRun_squares1 {c : List ℤ} {H A sp1 sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} (hrun : IsSoundRun c sp2 entries magics cls offsets db) (hH63 : H < 2 ^ 63)
    (hA : 1 ≤ A) (rev : Bool) (hd : degree c % 2 = 1) {info : List Setup.DenInfo}
    {divisors : List ℕ} (hs : Id.run (Setup.setupUs1 c (degree c) H) = some (info, divisors)) :
    (Id.run (sieveRun c (degree c) H A rev sp1 sp2 entries magics cls offsets db
      (.squares1 info divisors) 1 H)).toList =
      ((squares1Dens divisors 1 H).flatMap fun b : ℕ ↦
        pointsOfDen c (degree c) b (numerators H)).map (if rev then swapPoint else id) := by
  refine toList_run_sieveRun_of_sound hrun hH63 hA rev (p := fun _ ↦ true)
    (by simp [Shape.dens]) fun b hb h ↦ ⟨rfl, ?_⟩
  obtain ⟨a, -, y, hg, hy⟩ := exists_sq_eq_of_pointsOfDen_ne_nil h
  have hb0 : b ≠ 0 :=
    Nat.one_le_iff_ne_zero.mp (List.mem_range'_1.mp (mem_range'_of_mem_squares1Dens hb)).1
  simp [Shape.keep, hrun.bits_bne_zero b, getElem!_twoAdic_ne_zero h,
    run_denInfoTest_of_sq_eq hd hs hb0 hg hy]

-- The word shape, for even degree.
private theorem toList_run_sieveRun_words {c : List ℤ} {H A sp1 sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} (hrun : IsSoundRun c sp2 entries magics cls offsets db) (hH63 : H < 2 ^ 63)
    (hA : 1 ≤ A) (rev : Bool) (hd : degree c % 2 = 0) {forb : List ForbiddenEntry}
    {forbVal : List ForbiddenVal} (hforb : ∀ e ∈ forb, IsForbiddenEntry c (degree c) H e)
    (hval : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e) (useJacobi : Bool) :
    (Id.run (sieveRun c (degree c) H A rev sp1 sp2 entries magics cls offsets db
      (.words forb forbVal useJacobi
        (if useJacobi then Id.run (jacobiSetup (c.getD (degree c) 0) H) else none)
        (c.getD (degree c) 0)) 1 H)).toList =
      ((List.range' 1 H).flatMap fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) := by
  obtain rfl := hrun.db_eq
  refine toList_run_sieveRun_of_sound hrun hH63 hA rev ?_ fun _ hb h ↦
    have hb' := List.mem_range'_1.mp hb
    (exists_sq_eq_of_pointsOfDen_ne_nil h).elim fun _ ⟨_, _, hg, hy⟩ ↦
      ⟨getLsbD_denBits_and_all_of_sq_eq hd hforb (by lia) (by lia) hg hy,
        run_wordsTest_of_sq_eq hd hval _ (by lia) (by lia) hg hy⟩
  simpa [Shape.dens] using toList_run_wordsDens (fun e he ↦ (hforb e he).prime.pos)
    (fun e he ↦ (hforb e he).words_eq) 1 H

end Sieve

/-! ### What `Ratpoints.sievingInfo` computes -/

/-- What the loop of `Ratpoints.sievingInfo` over the moduli has made after the moduli `pref`,
before a return: the sieve entries `entries` of the moduli `pref`, in their order, each made by
`Ratpoints.makeModulus?` (`Ratpoints.IsModulusEntry`) with the reference to its table of rows and
the kind of its builder of its position (`Ratpoints.Sieve.SieveEntry.refInit`), that of one of the
first `Ratpoints.numPrimes` primes of the table having the shape that the third stage of the sieve
needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), and the store `store` of the tables of rows as
the loop of the tables and the tables of these entries make it
(`Ratpoints.Sieve.RowStore.MadeFor`). -/
structure SievingInfoEntries (c : List ℤ) (pref : List ℕ) (entries : Array SieveEntry)
    (store : RowStore) : Prop where
  /-- The entries are those of the moduli `pref`, in their order. -/
  map_p : entries.toList.map (·.p) = pref
  /-- Each entry is made by `Ratpoints.makeModulus?`. -/
  isModulusEntry : ∀ e ∈ entries, IsModulusEntry c e.p e
  /-- Each entry has the reference and the kind of builder of its position. -/
  refInit : ∀ n (h : n < entries.size),
    (entries[n].ref, entries[n].init) = SieveEntry.refInit n entries[n].factors
  /-- The entry of one of the first `Ratpoints.numPrimes` primes has the shape that the third stage
  needs. -/
  isPrimeEntry : ∀ e ∈ entries, ∀ pn < numPrimes, primeTable[pn]! = e.p → e.IsPrimeEntry
  /-- The store is made for the entries. -/
  madeFor : store.MadeFor c (degree c) entries.toList

/-- The invariant of the loop of `Ratpoints.sievingInfo` over the moduli, after the moduli `pref`
and with the moduli `suff` still to come, on the result of an early return, the sieve entries made
and the store of the tables of rows: before a return, what the loop has made
(`Ratpoints.SievingInfoEntries`); a result, which is `none` and comes when the curve has no points
of height at most `H`, only at the end. -/
def SievingInfoInvariant (c : List ℤ) (H : ℕ) (pref suff : List ℕ)
    (st : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore)) × Array SieveEntry × RowStore) : Prop :=
  st.1.elim (SievingInfoEntries c pref st.2.1 st.2.2) fun r ↦ suff = [] ∧ r = none ∧
    ∀ q, ¬IsPoint c H q

/-- The loop of `Ratpoints.sievingInfo` starts with the store of the loop of the tables, which holds
the rows of `0` of the primes and no others (`Ratpoints.Sieve.PrimeStore`). -/
theorem sievingInfoInvariant_empty (c : List ℤ) (H : ℕ) (suff : List ℕ) {store : RowStore}
    (h : PrimeStore store) : SievingInfoInvariant c H [] suff (none, #[], store) :=
  ⟨rfl, nofun, nofun, nofun, RowStore.madeFor_nil c (degree c) h.1 h.2⟩

-- The sieve entry of one of the first `numPrimes` primes of the table with the prime as its only
-- factor, with the table of the reference, and the reciprocal of the prime has the shape that the
-- third stage needs.
private theorem isPrimeEntry_of_factors_eq {c : List ℤ} {e : SieveEntry} {pn : ℕ}
    (hpn : pn < numPrimes) (hm : primeTable[pn]! = e.p)
    (h : e.factors = [.prime (examinePrime c (degree c) e.p)]) (hmg : e.magic = magic e.p) :
    e.IsPrimeEntry :=
  isPrimeEntry_examinePrime c (degree c)
    (hm ▸ prime_getElem!_primeTable (hpn.trans_le numPrimes_le_size_primeTable))
    (hm ▸ (getElem!_primeTable_lt_maxPrimeEven hpn).le.trans maxPrimeEven_le_two_pow_32) h rfl hmg

/-- A sieve entry made by `Ratpoints.makeModulus?` is sound. -/
theorem IsModulusEntry.isSound {c : List ℤ} {m : ℕ} {s : SieveEntry} (h : IsModulusEntry c m s) :
    s.IsSound c :=
  ⟨Nat.zero_lt_of_lt h.packable.one_lt, fun hab hy ↦ h.admits_of_sq_eq hab hy⟩

-- The prime factors of a sieve entry made by `Ratpoints.makeModulus?` are positive.
private theorem IsModulusEntry.pos_of_prime_mem {c : List ℤ} {m : ℕ} {s : SieveEntry}
    (h : IsModulusEntry c m s) (t : Entry) (ht : .prime t ∈ s.factors) : 0 < t.p :=
  (h.buildable _ ht).1

/-- The references and the kinds of builder of the entries made after the next entry `e`, of the
position `entries.size`. -/
theorem refInit_push {entries : Array SieveEntry}
    (h : ∀ n (h : n < entries.size),
      (entries[n].ref, entries[n].init) = SieveEntry.refInit n entries[n].factors)
    {e : SieveEntry} (he : (e.ref, e.init) = SieveEntry.refInit entries.size e.factors) :
    ∀ n (h : n < (entries.push e).size),
      ((entries.push e)[n].ref, (entries.push e)[n].init) =
        SieveEntry.refInit n (entries.push e)[n].factors := by
  intro n hn
  rw [Array.getElem_push]
  split
  · exact h n ‹_›
  · obtain rfl : n = entries.size := by simp at hn; lia
    exact he

/-- The step of the loop of `Ratpoints.sievingInfo` at a modulus `m`, whose sieve entry
`Ratpoints.makeModulus?` makes at the position `entries.size` (`Ratpoints.makeModulus?_spec`), with
its tables of rows and those of its factors added to the store
(`Ratpoints.Sieve.SieveEntry.addTables`): the entry of one of the first `Ratpoints.numPrimes` primes
of the table has the shape that the third stage needs, and the store is made for the entries with
`e` (`Ratpoints.Sieve.RowStore.MadeFor.addTables`). -/
theorem SievingInfoInvariant.push {c : List ℤ} {H m : ℕ} {pref suff : List ℕ}
    {o : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore))}
    {entries : Array SieveEntry} {store : RowStore} {r : Option SieveEntry} {e : SieveEntry}
    (h : SievingInfoInvariant c H pref (m :: suff) (o, entries, store))
    (hr : (∀ s, r = some s → IsModulusEntry c m s ∧
          (s.ref, s.init) = SieveEntry.refInit entries.size s.factors ∧
          ∀ pn < numPrimes, primeTable[pn]! = m →
            s.factors = [.prime (examinePrime c (degree c) m)]) ∧
      (r = none → ∀ H q, ¬IsPoint c H q))
    (he : r = some e) :
    SievingInfoInvariant c H (pref ++ [m]) suff (none, entries.push e, e.addTables store) := by
  cases o with
  | some _ => exact absurd h.1 (List.cons_ne_nil _ _)
  | none =>
    obtain ⟨hme, href, hf⟩ := hr.1 e he
    obtain rfl := hme.p_eq
    have hmd := h.madeFor.addTables
      (SieveEntry.refFits_of_refInit_eq href fun _ ↦ hme.p_eq_modulus) hme.pos_of_prime_mem
    refine ⟨by simp [h.map_p], Array.forall_mem_push.mpr ⟨hme, h.isModulusEntry⟩,
      refInit_push h.refInit href, Array.forall_mem_push.mpr ⟨fun pn hpn hm ↦
        isPrimeEntry_of_factors_eq hpn hm (hf pn hpn hm) hme.packable.magic_eq, h.isPrimeEntry⟩, ?_⟩
    rwa [Array.toList_push]

/-- What the search needs of the result of `Ratpoints.sievingInfo` for the parameters `P`: the sieve
entries `entries` are those of the moduli, in their order, sound
(`Ratpoints.Sieve.SieveEntry.IsSound`), with the fields that the packing reads
(`Ratpoints.Sieve.SieveEntry.Packable`) and the tables of inverses of their factors
(`Ratpoints.Sieve.Factor.HasInverses`), those of the third stage of the shape that it needs
(`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`); `magics` holds the reciprocals of their moduli, in
their order; the forbidden divisors are among those that the loops of the tables and of the further
primes may record (`Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`); and the
store of the tables of rows fits the entries (`Ratpoints.Sieve.RowStore.Fits`). -/
structure IsSievingInfo (c : List ℤ) (H : ℕ) (P : Params) (entries : List SieveEntry)
    (magics : Array ℕ) (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal)
    (store : RowStore) : Prop where
  /-- The sieve entries are sound, with the fields that the packing reads and the tables of inverses
  of their factors. -/
  isSound : ∀ e ∈ entries, e.IsSound c ∧ e.Packable ∧ ∀ f ∈ e.factors, f.HasInverses e.p
  /-- The reciprocals of the moduli, in the order of the entries. -/
  magics_eq : magics.toList = entries.map fun e ↦ magic e.p
  /-- The entries are those of the moduli, in their order. -/
  map_p : entries.map (·.p) = P.moduli
  /-- The entries of the third stage have the shape that it needs. -/
  isPrimeEntry : ∀ e ∈ entries.drop P.sp2, e.IsPrimeEntry
  /-- The forbidden divisors tested with words are sound. -/
  isForbiddenEntry : ∀ e ∈ forb, IsForbiddenEntry c (degree c) H e
  /-- The forbidden divisors tested by their valuations are sound. -/
  isForbiddenVal : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e
  /-- The store of the tables of rows fits the entries. -/
  fits : store.Fits entries

/-- The early return of the loop of `Ratpoints.sievingInfo` at a modulus whose sieve entry is none:
the curve has no points. -/
theorem sievingInfoInvariant_some_none {c : List ℤ} {H m : ℕ} {pref : List ℕ}
    {entries : Array SieveEntry} {store : RowStore} {r x : Option SieveEntry} {n : ℕ}
    (hr : (∀ s, r = some s → IsModulusEntry c m s ∧
          (s.ref, s.init) = SieveEntry.refInit n s.factors ∧ ∀ pn < numPrimes, primeTable[pn]! = m →
            s.factors = [.prime (examinePrime c (degree c) m)]) ∧
      (r = none → ∀ H q, ¬IsPoint c H q))
    (hx : ∀ e, x = some e → False) (he : r = x) :
    SievingInfoInvariant c H pref [] (some none, entries, store) :=
  ⟨rfl, rfl, hr.2 (he.trans (Option.eq_none_iff_forall_ne_some.mpr hx)) H⟩

/-- The end of the loop of `Ratpoints.sievingInfo` after an early return. -/
theorem SievingInfoInvariant.post_some {c : List ℤ} {H : ℕ} {P : Params} {pref : List ℕ}
    {o : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore))}
    {entries : Array SieveEntry} {store : RowStore}
    {r : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal × RowStore)}
    (h : SievingInfoInvariant c H pref [] (o, entries, store)) (ho : o = some r) :
    (∀ entries magics forb forbVal store, r = some (entries, magics, forb, forbVal, store) →
        IsSievingInfo c H P entries magics forb forbVal store) ∧
      (r = none → ∀ q, ¬IsPoint c H q) := by
  subst ho
  obtain ⟨-, rfl, h⟩ := h
  exact ⟨nofun, fun _ ↦ h⟩

-- The sieve entries of the moduli of well-formed parameters, in their order, of which those of the
-- first `numPrimes` primes of the table have the shape that the third stage needs: those of the
-- third stage have it.
private theorem forall_mem_drop_isPrimeEntry {P : Params} (hP : P.WF) {entries : List SieveEntry}
    (hmap : entries.map (·.p) = P.moduli)
    (h : ∀ e ∈ entries, ∀ pn < numPrimes, primeTable[pn]! = e.p → e.IsPrimeEntry) :
    ∀ e ∈ entries.drop P.sp2, e.IsPrimeEntry := fun e he ↦
  have ⟨pn, hpn, hm⟩ := hP.exists_getElem!_primeTable_eq_of_mem_drop
    (hmap ▸ List.map_drop ▸ List.mem_map_of_mem he)
  h e (List.mem_of_mem_drop he) pn hpn hm

/-- The store made for the sieve entries of a run by `Ratpoints.makeModulus?`, each with the
reference and the kind of builder of its position, fits them, for the rows of the references of the
run (`Ratpoints.Sieve.runRows`, `Ratpoints.IsModulusEntry.rowsFit_runRows`). -/
theorem SievingInfoEntries.fits {c : List ℤ} {pref : List ℕ} {entries : Array SieveEntry}
    {store : RowStore} (h : SievingInfoEntries c pref entries store) : store.Fits entries.toList :=
  ⟨_, h.madeFor.storeHolds, fun n hn ↦ by
    have hn' : n < entries.size := by simpa using hn
    simp only [Array.getElem_toList]
    exact (h.isModulusEntry _ (Array.getElem_mem hn')).rowsFit_runRows (h.refInit n hn')
      (by simp [hn'])⟩

/-- The end of the loop of `Ratpoints.sievingInfo` over all the moduli of well-formed parameters,
with forbidden divisors that the loops of the tables and of the further primes may record: the
reciprocals of the sieve entries are those of their moduli, the entries of the moduli of the third
stage are among those of the first `Ratpoints.numPrimes` primes of the table
(`Ratpoints.Params.WF.exists_getElem!_primeTable_eq_of_mem_drop`), and the store fits the entries
(`Ratpoints.SievingInfoEntries.fits`). -/
theorem SievingInfoInvariant.post_none {c : List ℤ} {H : ℕ} {P : Params}
    {o : Option (Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
      RowStore))}
    {entries : Array SieveEntry} {store : RowStore} {forb : List ForbiddenEntry}
    {forbVal : List ForbiddenVal} (hP : P.WF)
    (h : SievingInfoInvariant c H P.moduli [] (o, entries, store)) (ho : o = none)
    (hforb : (∀ e ∈ forb, IsForbiddenEntry c (degree c) H e) ∧
      ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e) :
    (∀ entries' magics forb' forbVal' store',
        some (entries.toList, entries.map (·.magic), forb, forbVal, store) =
          some (entries', magics, forb', forbVal', store') →
        IsSievingInfo c H P entries' magics forb' forbVal' store') ∧
      (some (entries.toList, entries.map (·.magic), forb, forbVal, store) = none →
        ∀ q, ¬IsPoint c H q) := by
  subst ho
  refine ⟨fun _ _ _ _ _ h' ↦ ?_, nofun⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := h'
  have hent (e : SieveEntry) (he : e ∈ entries.toList) :=
    h.isModulusEntry e (Array.mem_toList_iff.mp he)
  refine ⟨fun e he ↦ ⟨(hent e he).isSound, (hent e he).packable, (hent e he).hasInverses⟩, ?_,
    h.map_p, forall_mem_drop_isPrimeEntry hP h.map_p fun e he ↦
      h.isPrimeEntry e (Array.mem_toList_iff.mp he), hforb.1, hforb.2, h.fits⟩
  rw [Array.toList_map]
  exact List.map_congr_left fun e he ↦ (hent e he).packable.magic_eq

-- The exit of the loop of the tables in `Ratpoints.sievingInfo`: the curve has no points.
private theorem post_of_run_examinePrimes_eq {c : List ℤ} {u checkDenom : Bool} {P : Params}
    {H : ℕ} {x : Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal × RowStore)}
    (hn : P.examined ≤ numPrimes)
    (hx : ∀ tables ba val store, x = some (tables, ba, val, store) → False)
    (he : Id.run (examinePrimes c (degree c) u checkDenom P.examined P.maxForbidden H) = x) :
    (∀ entries magics forb forbVal store,
        (none : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
          RowStore)) = some (entries, magics, forb, forbVal, store) →
        IsSievingInfo c H P entries magics forb forbVal store) ∧
      ((none : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal ×
        RowStore)) = none → ∀ q, ¬IsPoint c H q) :=
  ⟨nofun, fun _ ↦ not_isPoint_of_run_examinePrimes_eq_none
    (he.trans (Option.eq_none_iff_forall_ne_some.mpr fun ⟨t, b, v, s⟩ h ↦ hx t b v s h)) hn H⟩

-- The forbidden divisors that the loop of the tables records, as lists.
private theorem forall_mem_toList_isForbiddenEntry_and_isForbiddenVal {c : List ℤ} {d : ℕ}
    {u checkDenom : Bool} {n maxForbidden H : ℕ} {tables : Array Entry}
    {ba : Array ForbiddenEntry} {val : Array ForbiddenVal} {store : RowStore}
    (h : Id.run (examinePrimes c d u checkDenom n maxForbidden H) = some (tables, ba, val, store))
    (hn : n ≤ numPrimes) :
    (∀ e ∈ ba.toList, IsForbiddenEntry c d H e) ∧ ∀ e ∈ val.toList, IsForbiddenVal c d H e :=
  ⟨fun _ he ↦ isForbiddenEntry_of_run_examinePrimes_eq_some h hn (Array.mem_toList_iff.mp he),
    fun _ he ↦ isForbiddenVal_of_run_examinePrimes_eq_some h hn (Array.mem_toList_iff.mp he)⟩

-- The loop of the tables, as a value for the contract of `Ratpoints.sievingInfo`.
private theorem examinePrimes_value (c : List ℤ) (d : ℕ) (u checkDenom : Bool)
    (n maxForbidden bHigh : ℕ) :
    ⦃ True ⦄ examinePrimes c d u checkDenom n maxForbidden bHigh
    ⦃ fun r ↦ r = Id.run (examinePrimes c d u checkDenom n maxForbidden bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

attribute [local irreducible] SievingInfoInvariant in
/-- For well-formed parameters, what `Ratpoints.sievingInfo` computes serves the search
(`Ratpoints.IsSievingInfo`): the sieve entries are those of the moduli, in their order, and are
sound (`Ratpoints.SievingInfoInvariant.push`, the tables of the loop of the tables being those of
the reference, `Ratpoints.makeModulus?_spec`), have the fields that the packing reads
(`Ratpoints.Sieve.SieveEntry.Packable`) and the tables of inverses of their factors
(`Ratpoints.Sieve.Factor.HasInverses`), and hold the reciprocals of their moduli, which are the
reciprocals returned, in the order of the entries, those of the third stage having the shape that it
needs (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`); the forbidden divisors are among those that the
loop of the tables and the loop of the further primes may record
(`Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`), with the switch of the
forbidden divisors on or off; and the store of the tables of rows that the loop of the tables and
the loop over the moduli make fits the entries (`Ratpoints.Sieve.RowStore.Fits`). When it returns
none, the curve has no points, none modulo a prime of the loop of the tables
(`Ratpoints.Sieve.not_isPoint_of_run_examinePrimes_eq_none`) or modulo a prime examined for a
modulus. -/
@[spec]
theorem sievingInfo_spec (c : List ℤ) (u checkDenom : Bool) (P : Params) (H : ℕ) :
    ⦃ P.WF ⦄ sievingInfo c (degree c) u checkDenom P H
    ⦃ fun r ↦ (∀ entries magics forb forbVal store,
        r = some (entries, magics, forb, forbVal, store) →
          IsSievingInfo c H P entries magics forb forbVal store) ∧
      (r = none → ∀ q, ¬IsPoint c H q) ⦄ := by
  vcgen [sievingInfo, examinePrimes_value] invariants
  · fun pref suff st ↦ SievingInfoInvariant c H pref suff st
  · fun pref suff st ↦ SievingInfoInvariant c H pref suff st
  all_goals try dsimp only at *
  all_goals try obtain rfl := ‹_ = Id.run (examinePrimes _ _ _ _ _ _ _)›
  all_goals have hP := ‹P.WF›
  all_goals first
    | exact sievingInfoInvariant_empty c H _
        (primeStore_of_run_examinePrimes_eq_some ‹_› hP.examined_le)
    | exact SievingInfoInvariant.post_some ‹_› ‹_›
    | exact SievingInfoInvariant.post_none hP ‹_› ‹_› ‹_›
    | exact SievingInfoInvariant.post_none hP ‹_› ‹_›
        (forall_mem_toList_isForbiddenEntry_and_isForbiddenVal ‹_› hP.examined_le)
    | exact SievingInfoInvariant.push ‹_› ‹_› ‹_›
    | exact sievingInfoInvariant_some_none ‹_› ‹_› ‹_›
    | exact ⟨getElem_eq_examinePrime_of_run_examinePrimes_eq_some ‹_› hP.examined_le,
        hP.modulus _ (by simp [‹P.moduli = _›])⟩
    | exact ⟨fun _ ↦ isForbiddenEntry_of_run_examinePrimes_eq_some ‹_› hP.examined_le,
        fun _ ↦ isForbiddenVal_of_run_examinePrimes_eq_some ‹_› hP.examined_le⟩
    | exact post_of_run_examinePrimes_eq hP.examined_le ‹_› ‹_›

-- `Ratpoints.sievingInfo_spec` as a plain statement.
private theorem run_sievingInfo_spec {c : List ℤ} {u checkDenom : Bool} {P : Params} {H : ℕ}
    (hP : P.WF) :
    (∀ entries magics forb forbVal store, Id.run (sievingInfo c (degree c) u checkDenom P H) =
        some (entries, magics, forb, forbVal, store) →
          IsSievingInfo c H P entries magics forb forbVal store) ∧
      (Id.run (sievingInfo c (degree c) u checkDenom P H) = none → ∀ q, ¬IsPoint c H q) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((sievingInfo_spec c u checkDenom P H).le_wp hP)

/-! ### The search -/

-- The shape that `Ratpoints.Sieve.runSetup` chooses from the flags of the search.
private theorem toList_run_sieveRun_runSetup {c : List ℤ} {H A sp1 sp2 : ℕ}
    {entries : List SieveEntry} {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ}
    {db : UInt64} (hrun : IsSoundRun c sp2 entries magics cls offsets db) (hH63 : H < 2 ^ 63)
    (hA : 1 ≤ A) (rev : Bool) {us1 : Option (List Setup.DenInfo × List ℕ)}
    (hus1 : (if degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1 then
      Id.run (Setup.setupUs1 c (degree c) H) else none) = us1)
    {checkDenom useJacobi : Bool} {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hforb : ∀ e ∈ forb, IsForbiddenEntry c (degree c) H e)
    (hval : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e)
    (hcd : checkDenom = true → degree c % 2 = 0) :
    (Id.run (sieveRun c (degree c) H A rev sp1 sp2 entries magics cls offsets db
      (Id.run (runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) us1 checkDenom
        useJacobi forb forbVal (c.getD (degree c) 0) H)) 1 H)).toList =
      ((searchDens c (degree c) H).flatMap fun b : ℕ ↦
        pointsOfDen c (degree c) b (numerators H)).map (if rev then swapPoint else id) := by
  rw [searchDens, hus1]
  rcases Nat.mod_two_eq_zero_or_one (degree c) with hd | hd
  · obtain rfl : us1 = none := by rw [← hus1, hd]; rfl
    rw [hd]
    cases checkDenom
    · exact toList_run_sieveRun_all hrun hH63 hA rev
    · cases useJacobi <;> exact toList_run_sieveRun_words hrun hH63 hA rev hd hforb hval _
  by_cases hc : (c.getD (degree c) 0).natAbs = 1
  · obtain rfl : us1 = none := by rw [← hus1, hd, hc]; rfl
    rw [hd, hc]
    exact toList_run_sieveRun_squares hrun hH63 hA rev hd hc
  have hflag : (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) = false := by
    rw [hd, beq_eq_false_iff_ne.mpr hc, Bool.and_false]
  rw [hflag]
  rcases us1 with _ | ⟨info, divisors⟩
  · obtain rfl : checkDenom = false := by cases checkDenom <;> simp_all
    exact toList_run_sieveRun_all hrun hH63 hA rev
  · exact toList_run_sieveRun_squares1 hrun hH63 hA rev hd
      (Option.ite_none_right_eq_some.mp hus1).2

-- A curve without points of height at most `H` has an empty reference.
private theorem bruteForce_eq_nil_of_forall_not_isPoint {c : List ℤ} {H : ℕ}
    (h : ∀ q, ¬IsPoint c H q) : bruteForce c H = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun q hq ↦ h q (mem_bruteForce_iff.mp hq)

-- A curve whose reference is empty has no points at infinity and none over the denominators of
-- its search, which lie in `1, …, H`.
private theorem nil_eq_of_bruteForce_eq_nil {c : List ℤ} {H : ℕ} (hH : 1 ≤ H)
    (h : bruteForce c H = []) (rev : Bool) :
    [] = (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
      fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) := by
  rw [bruteForce_eq_append c hH, List.append_eq_nil_iff, List.flatMap_eq_nil_iff] at h
  rw [h.1, List.nil_append, List.flatMap_eq_nil_iff.mpr fun b hb ↦
    h.2 b (mem_range'_of_mem_searchDens hb), List.map_nil]

-- The 2-adic exit of the search: no class of the denominators admits a numerator, so that the
-- curve has no points.
private theorem nil_eq_of_denBits_eq_zero {c : List ℤ} {H : ℕ} (hH : 1 ≤ H) (rev : Bool)
    {nb : Vector UInt64 64} (hnb : nb = Id.run (twoAdic c (degree c))) {cls : Vector NumClass 64}
    {db : UInt64} (hnc : (cls, db) = Id.run (numClasses nb))
    (h : (db == 0 && !(degree c % 2 == 1 || Setup.isSquare (c.getD (degree c) 0))) = true) :
    [] = (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
      fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) := by
  subst hnb
  have hdb : db = denBits (Id.run (twoAdic c (degree c))) := by rw [← snd_run_numClasses, ← hnc]
  simp only [Bool.and_eq_true, beq_iff_eq, hdb] at h
  exact nil_eq_of_bruteForce_eq_nil hH
    (bruteForce_eq_nil_of_forall_not_isPoint (not_isPoint_of_denBits_eq_zero h.1 H)) rev

-- The exit of `Ratpoints.sievingInfo`: the curve has no points.
private theorem nil_eq_of_run_sievingInfo_eq_none {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF)
    (hH : 1 ≤ H) (rev : Bool) {u checkDenom : Bool}
    {r r' : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal × RowStore)}
    (hr : r = Id.run (sievingInfo c (degree c) u checkDenom P H))
    (hnone : ∀ entries magics forb forbVal store,
      r' = some (entries, magics, forb, forbVal, store) → False)
    (h : r = r') :
    [] = (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
      fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
        (if rev then swapPoint else id) := by
  obtain rfl : r' = none := Option.eq_none_iff_forall_ne_some.mpr fun _ h' ↦ hnone _ _ _ _ _ h'
  exact nil_eq_of_bruteForce_eq_nil hH
    (bruteForce_eq_nil_of_forall_not_isPoint ((run_sievingInfo_spec hP).2 (hr.symm.trans h)))
    rev

-- The classes after `class_offsets`, with the entries whose inverses of the strides it sets, the
-- other fields unchanged, and its row offsets, make a sound run with the word of the classes that
-- admit a numerator.
private theorem isSoundRun_of_map {c : List ℤ} {sp2 : ℕ} {entries : List SieveEntry}
    {magics : Array ℕ} {cls cls' : Vector NumClass 64} {offsets : Array ℕ}
    {dinv : SieveEntry → Array ℕ}
    (hent : ∀ e ∈ entries, e.IsSound c ∧ e.Packable ∧ ∀ f ∈ e.factors, f.HasInverses e.p)
    (hes : ∀ e ∈ entries.drop sp2, e.IsPrimeEntry)
    (hmg : magics.toList = entries.map fun e ↦ magic e.p)
    (hcls : ∀ b < 64, cls[b]!.Packs (Id.run (twoAdic c (degree c)))[b]!)
    (hbits : ∀ b < 64, cls'[b]!.bits = cls[b]!.bits ∧ cls'[b]!.k = cls[b]!.k ∧
      cls'[b]!.a0 = cls[b]!.a0)
    (hoff : OffsetsFor cls' (entries.map fun e ↦ { e with dinv := dinv e }) offsets) :
    IsSoundRun c sp2 (entries.map fun e ↦ { e with dinv := dinv e }) magics cls' offsets
      (denBits (Id.run (twoAdic c (degree c)))) := by
  refine ⟨fun e he ↦ ?_, fun e he ↦ ?_, by simp [hmg], fun e he ↦ ?_, hoff.take sp2,
    fun b hb ↦ (hcls b hb).congr (hbits b hb).1 (hbits b hb).2.1 (hbits b hb).2.2, rfl⟩
  · obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact ⟨(hent e' he').1.pos, (hent e' he').1.admits_of_sq_eq⟩
  · rw [← List.map_drop] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact hes e' he'
  · rw [← List.map_take] at he
    obtain ⟨e', he', rfl⟩ := List.mem_map.mp he
    exact (hent e' (List.mem_of_mem_take he')).2.2

-- The classes, the entries and the row offsets of the search after `class_offsets`, in the array
-- of `num_packings` rows, make a sound run (`Ratpoints.sievingInfo_spec`,
-- `Ratpoints.Sieve.numClasses_spec`, `Ratpoints.Sieve.numPackings_spec`,
-- `Ratpoints.Sieve.classOffsets_spec`).
private theorem isSoundRun_of_run_classOffsets {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF)
    {u cd : Bool}
    {r : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal × RowStore)}
    {entries : List SieveEntry} {magics : Array ℕ} {forb : List ForbiddenEntry}
    {forbVal : List ForbiddenVal} {store : RowStore}
    (hr : r = Id.run (sievingInfo c (degree c) u cd P H))
    (hs : r = some (entries, magics, forb, forbVal, store)) {nb : Vector UInt64 64}
    (hnb : nb = Id.run (twoAdic c (degree c))) {cls : Vector NumClass 64} {db : UInt64}
    (hnc : (cls, db) = Id.run (numClasses nb)) {n : ℕ} (hn : n = Id.run (numPackings cls))
    {cls' : Vector NumClass 64} {entries' : List SieveEntry} {offsets : Array ℕ}
    (hco : (cls', entries', offsets) =
      Id.run (classOffsets cls entries (Array.replicate (n * max entries.length 1) 0))) :
    IsSoundRun c P.sp2 entries' magics cls' offsets db := by
  have hi := (run_sievingInfo_spec hP).1 _ _ _ _ _ (hr.symm.trans hs)
  subst hnb
  obtain ⟨rfl, rfl⟩ : cls = (Id.run (numClasses _)).1 ∧ db = (Id.run (numClasses _)).2 := by
    rw [← hnc]; exact ⟨rfl, rfl⟩
  have hcls (b : ℕ) (hb : b < 64) :=
    packs_getElem!_fst_run_numClasses (Id.run (twoAdic c (degree c))) hb
  have hn' : n = max 1 (firstKeys _ 64) :=
    hn.trans (Std.WP.Id.of_run_eq_wp rfl _ ((numPackings_spec _).le_wp fun b hb ↦ (hcls b hb).1))
  have hsize : firstKeys (Id.run (numClasses (Id.run (twoAdic c (degree c))))).1 64 *
      entries.length ≤ (Array.replicate (n * max entries.length 1) (0 : ℕ)).size := by
    rw [Array.size_replicate, hn']
    exact Nat.mul_le_mul (Nat.le_max_right _ _) (Nat.le_max_left _ _)
  obtain ⟨hbits, ⟨f, hf⟩, hoff⟩ := Std.WP.Id.of_run_eq_wp rfl _
    ((classOffsets_spec _ entries _).le_wp ⟨fun e he ↦ (hi.isSound e he).2.1,
      fun b hb ↦ (hcls b hb).1, hsize⟩)
  rw [← hco] at hbits hf hoff
  simp only at hbits hf hoff
  subst hf
  rw [snd_run_numClasses]
  exact isSoundRun_of_map hi.isSound hi.isPrimeEntry hi.magics_eq hcls hbits hoff

-- The run of the search after its exits, with the shape that `Ratpoints.Sieve.runSetup` chooses.
private theorem append_eq_of_run_sievingInfo_eq_some {c : List ℤ} {H : ℕ} {P : Params} (hP : P.WF)
    (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) (rev : Bool) {entries entries' : List SieveEntry}
    {magics : Array ℕ} {cls : Vector NumClass 64} {offsets : Array ℕ} {db : UInt64}
    (hrun : IsSoundRun c P.sp2 entries' magics cls offsets db) {shape : Shape}
    {pts : Array (ℤ × ℤ × ℤ)}
    (hpts : pts = Id.run (sieveRun c (degree c) H (P.arraySizeAt H) rev P.sp1 P.sp2 entries' magics
      cls offsets db shape 1 H))
    {us1 : Option (List Setup.DenInfo × List ℕ)} {checkDenom useJacobi : Bool}
    {forb : List ForbiddenEntry} {forbVal : List ForbiddenVal}
    (hshape : shape = Id.run (runSetup (degree c % 2 == 1 && (c.getD (degree c) 0).natAbs == 1) us1
      checkDenom useJacobi forb forbVal (c.getD (degree c) 0) H))
    {u cd : Bool}
    {r : Option (List SieveEntry × Array ℕ × List ForbiddenEntry × List ForbiddenVal × RowStore)}
    (hr : r = Id.run (sievingInfo c (degree c) u cd P H)) {store : RowStore}
    (hs : r = some (entries, magics, forb, forbVal, store))
    (hus1 : (if degree c % 2 == 1 && (c.getD (degree c) 0).natAbs != 1 then
      Id.run (Setup.setupUs1 c (degree c) H) else none) = us1)
    (hcd : checkDenom = true → degree c % 2 = 0) :
    pointsAtInfinity c (degree c) rev ++ pts.toList =
      (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
        fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
          (if rev then swapPoint else id) := by
  have hi := (run_sievingInfo_spec hP).1 _ _ _ _ _ (hr.symm.trans hs)
  subst hshape hpts
  rw [toList_run_sieveRun_runSetup hrun hH63 (P.one_le_arraySizeAt hH) rev hus1
    hi.isForbiddenEntry hi.isForbiddenVal hcd,
    pointsAtInfinity_eq_map, List.map_append]

-- The components of the search, as values for its contract.
private theorem setupUs1_value (c : List ℤ) (d bHigh : ℕ) :
    ⦃ True ⦄ Setup.setupUs1 c d bHigh ⦃ fun r ↦ r = Id.run (Setup.setupUs1 c d bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem twoAdic_value (c : List ℤ) (d : ℕ) :
    ⦃ True ⦄ twoAdic c d ⦃ fun r ↦ r = Id.run (twoAdic c d) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem sievingInfo_value (c : List ℤ) (d : ℕ) (u checkDenom : Bool) (P : Params)
    (bHigh : ℕ) :
    ⦃ True ⦄ sievingInfo c d u checkDenom P bHigh
    ⦃ fun r ↦ r = Id.run (sievingInfo c d u checkDenom P bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem runSetup_value (useSquares : Bool) (us1 : Option (List Setup.DenInfo × List ℕ))
    (checkDenom useJacobi : Bool) (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal)
    (lcf : ℤ) (bHigh : ℕ) :
    ⦃ True ⦄ runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf bHigh
    ⦃ fun r ↦ r = Id.run (runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem numClasses_value (nb : Vector UInt64 64) :
    ⦃ True ⦄ numClasses nb ⦃ fun r ↦ r = Id.run (numClasses nb) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem numPackings_value (cls : Vector NumClass 64) :
    ⦃ True ⦄ numPackings cls ⦃ fun r ↦ r = Id.run (numPackings cls) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem classOffsets_value (cls : Vector NumClass 64) (es : List SieveEntry)
    (offsets : Array ℕ) :
    ⦃ True ⦄ classOffsets cls es offsets ⦃ fun r ↦ r = Id.run (classOffsets cls es offsets) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem sieveRun_value (c : List ℤ) (d H A : ℕ) (rev : Bool) (sp1 sp2 : ℕ)
    (entries : List SieveEntry) (magics : Array ℕ) (cls : Vector NumClass 64) (offsets : Array ℕ)
    (db : UInt64) (shape : Shape) (bLow bHigh : ℕ) :
    ⦃ True ⦄ sieveRun c d H A rev sp1 sp2 entries magics cls offsets db shape bLow bHigh
    ⦃ fun r ↦ r = Id.run (sieveRun c d H A rev sp1 sp2 entries magics cls offsets db shape bLow
        bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

-- The contract of the search, for the degree of the polynomial.
private theorem searchPoints_spec (c : List ℤ) (H : ℕ) (P : Params) (rev : Bool) :
    ⦃ P.WF ∧ 1 ≤ H ∧ H < 2 ^ 63 ⦄ searchPoints c (degree c) H P rev
    ⦃ fun r ↦ r = (pointsAtInfinity c (degree c) false ++ (searchDens c (degree c) H).flatMap
        fun b : ℕ ↦ pointsOfDen c (degree c) b (numerators H)).map
          (if rev then swapPoint else id) ⦄ := by
  vcgen [searchPoints, setupUs1_value, twoAdic_value, numClasses_value, sievingInfo_value,
    numPackings_value, classOffsets_value, runSetup_value, sieveRun_value]
  all_goals obtain ⟨hP, hH, hH63⟩ := ‹P.WF ∧ 1 ≤ H ∧ H < 2 ^ 63›
  all_goals first
    | exact nil_eq_of_denBits_eq_zero hH rev ‹_› ‹_› ‹_›
    | exact nil_eq_of_run_sievingInfo_eq_none hP hH rev ‹_› ‹_› ‹_›
    | exact append_eq_of_run_sievingInfo_eq_some hP hH hH63 rev
        (isSoundRun_of_run_classOffsets hP ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›) ‹_› ‹_› ‹_› ‹_›
        (by split <;> simp_all) (by simp)

/-- The run of the shape that `Ratpoints.Sieve.runSetup` chooses gives the reference over the
denominators of the search, its tests, the class words and the sieve entries of the moduli being
sound (`Ratpoints.Sieve.toList_run_sieveRun_eq_flatMap`, `Ratpoints.sievingInfo_spec`), with the
reciprocals that `Ratpoints.sievingInfo` returns; the height below `2 ^ 63`, which
`Ratpoints.findPoints` gives by its refusals, is what the test for common factors on the words of
the C code needs. When the search takes the exit of `Ratpoints.sievingInfo` or the 2-adic exit, the
curve has no points (`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`), so that both sides are
empty. -/
theorem run_searchPoints {c : List ℤ} {d H : ℕ} {P : Params} (hP : P.WF) (hH : 1 ≤ H)
    (hH63 : H < 2 ^ 63) (hd : d = degree c) (rev : Bool) :
    Id.run (searchPoints c d H P rev) =
      (pointsAtInfinity c d false ++ (searchDens c d H).flatMap fun b : ℕ ↦
        pointsOfDen c d b (numerators H)).map (if rev then swapPoint else id) := by
  subst hd
  exact (searchPoints_spec c H P rev).le_wp ⟨hP, hH, hH63⟩

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
  exact ⟨c', d', rev, hr, hd, by lia, run_searchPoints hP (by lia) (by simp_all [fitsLong_natCast])
    hd rev⟩

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
`Ratpoints.maxDegree + 1` coefficients, the height bound `0` or one of `2 ^ 63` or more, which is
not a `long` (`Ratpoints.fitsLong_natCast`), and the binary forms `Ratpoints.binaryFormPoly c` that
are not squarefree, for all parameters, whether the reversal is allowed or not; comparator certifies
this (`comparator/Challenge.lean`). -/
theorem exists_findPoints_eq_error_iff_of_sturm_nonneg {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} (hs : 0 ≤ o.sturm) :
    (∃ e, findPoints c H P o = .error e) ↔
      c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        ¬ Squarefree (binaryFormPoly c) := by
  rw [findPoints]
  dsimp only
  rw [BruteForce.degree_eq]
  simp only [fitsLong_natCast, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  split_ifs with h1 h2 h3 h4
  · simp [h1]
  · simp [h2]
  · grind
  · simp [not_squarefree_binaryFormPoly_of_lt h4]
  simp only [h1, h2, not_or.mp h3, false_or]
  split <;> rename_i hr
  · exact iff_of_true ⟨_, rfl⟩ (Setup.not_squarefree_binaryFormPoly_of_reversal_eq_error hr)
  · rw [← Sturm.run_chain_eq_none_iff_of_reversal_eq_ok (by lia) (by lia) hr]
    split_ifs <;> simp_all

/-- Without the Sturm step (`o.sturm < 0`, the option `-s` of the program), `Ratpoints.findPoints`
refuses, besides the coefficient lists of fewer than two or more than `Ratpoints.maxDegree + 1`
entries and the height bound `0` or one of `2 ^ 63` or more, which is not a `long`
(`Ratpoints.fitsLong_natCast`), exactly the forms whose leading zeros lower `⌈n / 2⌉`, for `n + 1`
coefficients, that is `d + 2 ≤ 2 ⌈n / 2⌉` for the degree `d`, and, when the reversal is allowed,
those of even degree with `c₀ = c₁ = 0`: forms that are not squarefree, but not all of them;
comparator certifies this (`comparator/Challenge.lean`), so that a `Ratpoints.findPoints` that
refused every input under `-s` would not pass. -/
theorem exists_findPoints_eq_error_iff_of_sturm_neg {c : List ℤ} {H : ℕ} {P : Params}
    {o : Options} (hs : o.sturm < 0) :
    (∃ e, findPoints c H P o = .error e) ↔
      c.length < 2 ∨ maxDegree + 1 < c.length ∨ H = 0 ∨ 2 ^ 63 ≤ H ∨
        degree c + 2 ≤ 2 * (c.length / 2) ∨
        o.reverse = true ∧ degree c % 2 = 0 ∧ c.getD 0 0 = 0 ∧ c.getD 1 0 = 0 := by
  rw [findPoints]
  dsimp only
  rw [BruteForce.degree_eq]
  simp only [fitsLong_natCast, Bool.not_eq_true', decide_eq_false_iff_not, not_lt]
  split_ifs with h1 h2 h3 h4
  · simp [h1]
  · simp [h2]
  · grind
  · simp only [Except.error.injEq, exists_eq', true_iff]
    lia
  simp only [h1, h2, not_or.mp h3, false_or, show ¬ degree c + 2 ≤ 2 * (c.length / 2) by lia,
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
