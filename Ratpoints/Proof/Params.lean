/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Ratpoints.Model.Params

import Mathlib.Tactic.NormNum.Prime
import Ratpoints.Mathlib.Data.List.Pairwise
import Ratpoints.Mathlib.Data.List.Sort
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Reductions
import Std.WP

/-!
# The sieving parameters: the table and the array size

Every entry of `Ratpoints.primeTable` is a prime, which `norm_num` checks one entry at a time, the
table lists every odd prime below 1022 in increasing order, which `decide` checks, so that its first
`Ratpoints.numPrimes` entries are below `Ratpoints.maxPrimeEven`, a bound that keeps the accumulator
of Horner's rule in `examine_prime` and the values of `examine_power` in the range of their C types;
and the pieces of the numerators have at least one bit array.

## Main statements

* `Ratpoints.prime_of_mem_primeTable`, `Ratpoints.prime_getElem!_primeTable`: every entry of
  `Ratpoints.primeTable` is a prime.
* `Ratpoints.pairwise_lt_toList_primeTable`, `Ratpoints.lt_of_mem_primeTable`,
  `Ratpoints.mem_primeTable_of_prime`: the table lists every odd prime below 1022, and nothing
  larger, in increasing order, which `decide` checks; `Ratpoints.mem_of_toList_primeTable_eq`: so it
  lists every odd prime below an entry before it;
  `Ratpoints.le_of_toList_primeTable_eq_append_cons_cons`: no prime lies between two neighbours;
  `Ratpoints.forIn_toList_primeTable`, `Ratpoints.eq_of_toList_primeTable_eq_append_singleton`: it
  begins with `3` and ends with `1021`.
* `Ratpoints.getElem!_primeTable_lt_maxPrimeEven`: the first `Ratpoints.numPrimes` primes of the
  table are below `Ratpoints.maxPrimeEven`; `Ratpoints.getElem!_primeTable_le_of_le`: the table
  increases.
* `Ratpoints.mul_add_lt_two_pow_64_of_lt_maxPrimeEven`,
  `Ratpoints.mul_self_lt_two_pow_63_of_lt_maxPrimeEven`: the values of `examine_power` stay in the
  range of their C types, the moduli being below `2 ^ 10` (`Ratpoints.maxPrimeEven_le_two_pow_10`);
  `Ratpoints.pow_hornerSteps_add_one_lt`: so does the accumulator of Horner's rule in
  `examine_prime` between two reductions, since `hornerSteps + 1 = 64 / maxBitsInPrime`
  (`Ratpoints.hornerSteps_add_one`).
* `Ratpoints.one_le_arraySizeAt`, `Ratpoints.Params.one_le_arraySizeAt`: for a height bound
  `H ≥ 1` a piece of the numerators has at least one bit array.
-/

@[expose] public section

namespace Ratpoints

theorem prime_of_mem_primeTable {p : ℕ} (h : p ∈ primeTable) : p.Prime := by
  rw [primeTable, List.mem_toArray] at h
  repeat' obtain rfl | h := List.mem_cons.mp h
  all_goals first | exact absurd h List.not_mem_nil | norm_num

theorem pairwise_lt_toList_primeTable : primeTable.toList.Pairwise (· < ·) := by
  decide +kernel

-- Every odd number below 1022 that the table does not hold has a divisor `1 < d < 32`.
private theorem all_toList_primeTable_or : ((List.range 1022).all fun q ↦ q < 3 || q % 2 == 0 ||
    (List.range' 2 30).any (fun d ↦ d < q && q % d == 0) || primeTable.toList.contains q) =
      true := by
  decide +kernel

private theorem all_toList_primeTable_lt : (primeTable.toList.all fun p ↦ p < 1022) = true := by
  decide +kernel

theorem lt_of_mem_primeTable {p : ℕ} (hp : p ∈ primeTable) : p < 1022 := by
  simpa using List.all_eq_true.mp all_toList_primeTable_lt p (Array.mem_toList_iff.mpr hp)

/-- The table holds every odd prime below 1022, which `decide` checks: every odd number below 1022
that it does not hold has a divisor `1 < d < 32`. -/
theorem mem_primeTable_of_prime {q : ℕ} (hq : q.Prime) (h2 : q ≠ 2) (h : q < 1022) :
    q ∈ primeTable := by
  have := List.all_eq_true.mp all_toList_primeTable_or q (List.mem_range.mpr h)
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range'_1, Bool.and_eq_true,
    List.elem_eq_mem, decide_eq_true_eq] at this
  rcases this with ((h3 | h4) | ⟨d, hdm, hdq, hd⟩) | hmem
  · exact absurd hq.two_le (by lia)
  · exact absurd (hq.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero h4)) (by lia)
  · lia [hq.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hd)]
  · exact Array.mem_toList_iff.mp hmem

/-- The table lists every odd prime below its entry `cur` before it, since it holds every odd prime
below 1022 in increasing order: the cofactor that `Ratpoints.Setup.factorLcf` has left when it
reaches `cur` has no prime factor below `cur`. -/
theorem mem_of_toList_primeTable_eq {pref suff : List ℕ} {cur q : ℕ}
    (hl : primeTable.toList = pref ++ cur :: suff) (hq : q.Prime) (h2 : q ≠ 2) (hlt : q < cur) :
    q ∈ pref := by
  have hcur : cur ∈ primeTable := Array.mem_toList_iff.mp (by simp [hl])
  exact List.mem_of_mem_append_cons_of_rel (hl ▸ pairwise_lt_toList_primeTable)
    (hl ▸ Array.mem_toList_iff.mpr
      (mem_primeTable_of_prime hq h2 ((lt_of_mem_primeTable hcur).trans' hlt))) hlt

/-- The table begins with `3`, the first prime of the loop of `Ratpoints.Setup.factorLcf`. -/
theorem forIn_toList_primeTable : ForIn.toList primeTable = 3 :: primeTable.toList.tail := by
  rw [Std.Internal.ForIn.toList_array]
  rfl

theorem two_lt_of_mem_toList_primeTable {q : ℕ} (hq : q ∈ primeTable.toList) : 2 < q := by
  have h : (primeTable.toList.all fun p ↦ 2 < p) = true := by decide
  simpa using List.all_eq_true.mp h q hq

/-- The last prime of the table is `1021`. -/
theorem eq_of_toList_primeTable_eq_append_singleton {pref : List ℕ} {cur : ℕ}
    (hl : primeTable.toList = pref ++ [cur]) :
    cur = 1021 := by
  have h : primeTable.toList.getLast? = some 1021 := by decide
  simpa [hl] using h

/-- No prime lies strictly between two neighbours of the table, which lists every odd prime below
1022 in increasing order. -/
theorem le_of_toList_primeTable_eq_append_cons_cons {pref suff : List ℕ} {cur next p : ℕ}
    (hl : primeTable.toList = pref ++ cur :: next :: suff) (hp : p.Prime) (hcp : cur < p) :
    next ≤ p := by
  refine Nat.le_of_not_lt fun hlt ↦ ?_
  have hpw := pairwise_lt_toList_primeTable
  rw [hl] at hpw
  have h3 : 2 < cur := two_lt_of_mem_toList_primeTable (by simp [hl])
  have hm := mem_of_toList_primeTable_eq (pref := pref ++ [cur]) (suff := suff) (by simp [hl]) hp
    (by lia) hlt
  rcases List.mem_append.mp hm with hm | hm
  · exact absurd ((List.pairwise_append.mp hpw).2.2 p hm cur (by simp)) (by lia)
  · lia [List.mem_singleton.mp hm]

theorem numPrimes_le_size_primeTable : numPrimes ≤ primeTable.size :=
  (List.length_filter_le _ _).trans_eq primeTable.length_toList

/-! ### The primes of the table by their positions -/

theorem prime_getElem!_primeTable {pn : ℕ} (h : pn < primeTable.size) : primeTable[pn]!.Prime :=
  prime_of_mem_primeTable (Array.getElem!_mem h)

theorem one_lt_getElem!_primeTable {pn : ℕ} (h : pn < numPrimes) : 1 < primeTable[pn]! :=
  (prime_getElem!_primeTable (h.trans_le numPrimes_le_size_primeTable)).one_lt

/-- The first `Ratpoints.numPrimes` primes of the table are below `Ratpoints.maxPrimeEven`, since
the table increases. -/
theorem getElem!_primeTable_lt_maxPrimeEven {pn : ℕ} (h : pn < numPrimes) :
    primeTable[pn]! < maxPrimeEven := by
  rw [getElem!_pos primeTable pn (h.trans_le numPrimes_le_size_primeTable), ← Array.getElem_toList]
  exact pairwise_lt_toList_primeTable.sortedLT.sortedLE.getElem_lt_of_lt_length_filter h

/-- The table increases: an entry is at most each entry after it. -/
theorem getElem!_primeTable_le_of_le {i j : ℕ} (hij : i ≤ j) (hj : j < primeTable.size) :
    primeTable[i]! ≤ primeTable[j]! := by
  rw [getElem!_pos primeTable i (hij.trans_lt hj), getElem!_pos primeTable j hj,
    ← Array.getElem_toList, ← Array.getElem_toList]
  exact pairwise_lt_toList_primeTable.sortedLT.sortedLE.getElem_le_getElem_of_le hij

/-! ### The moduli in the range of the C types -/

/-- The range obligation of the steps of Horner's rule in `examine_power`: for a modulus
`m < maxPrimeEven`, the steps `v x + c` (`find_points.c:2291`, `find_points.c:2298`), with `v`, `x`
and `c` below `m`, are below `m ^ 2 ≤ 2 ^ 64` (`Ratpoints.maxPrimeEven_le_two_pow_32`): the
`unsigned long`s do not wrap. The square of a residue, a product of `long`s, is
`Ratpoints.mul_self_lt_two_pow_63_of_lt_maxPrimeEven`. -/
theorem mul_add_lt_two_pow_64_of_lt_maxPrimeEven {m v x c : ℕ} (hm : m < maxPrimeEven)
    (hv : v < m) (hx : x < m) (hc : c < m) : v * x + c < 2 ^ 64 :=
  calc v * x + c < m * m := Nat.mul_add_lt_mul_of_lt hv hx hc
    _ ≤ 2 ^ 32 * 2 ^ 32 := Nat.mul_le_mul (hm.trans_le maxPrimeEven_le_two_pow_32).le
      (hm.trans_le maxPrimeEven_le_two_pow_32).le
    _ = 2 ^ 64 := by norm_num

/-- The range obligation of the square `x x` of a residue in `examine_power`
(`find_points.c:2284`), a product of `long`s: for `x` below a modulus, so below
`maxPrimeEven ≤ 2 ^ 10` (`Ratpoints.maxPrimeEven_le_two_pow_10`), it is below `2 ^ 20`, so below
`2 ^ 63`: the signed product does not overflow. -/
theorem mul_self_lt_two_pow_63_of_lt_maxPrimeEven {x : ℕ} (hx : x < maxPrimeEven) :
    x * x < 2 ^ 63 :=
  (Nat.mul_self_lt_mul_self (hx.trans_le maxPrimeEven_le_two_pow_10)).trans (by norm_num)

/-- The defining formula `hornerSteps = 64 / maxBitsInPrime - 1` without the truncated
subtraction, since `1 ≤ hornerSteps` (`Ratpoints.one_le_hornerSteps`). -/
theorem hornerSteps_add_one : hornerSteps + 1 = 64 / maxBitsInPrime := by
  have := one_le_hornerSteps
  rw [hornerSteps] at this ⊢
  lia

/-- The bound of the schedule of Horner's rule in `examine_prime`: `p ^ (hornerSteps + 1) < 2 ^ 64`
for `p < maxPrimeEven`, since `hornerSteps + 1 = 64 / maxBitsInPrime`
(`Ratpoints.hornerSteps_add_one`) and `maxBitsInPrime (64 / maxBitsInPrime) ≤ 64`. -/
theorem pow_hornerSteps_add_one_lt {p : ℕ} (hp : p < maxPrimeEven) :
    p ^ (hornerSteps + 1) < 2 ^ 64 :=
  hornerSteps_add_one ▸ Nat.pow_lt_two_pow_of_lt hp (Nat.mul_div_le 64 _)
    (hornerSteps_add_one ▸ Nat.succ_ne_zero _)

/-- The pieces of the numerators are not empty, so that the loop over the pieces of a denominator
advances; this reads off only that `Ratpoints.defaultArraySize`, `Ratpoints.maxArraySize` and the
chunk `Ratpoints.chunk` are positive, the rounding up to a multiple of the chunk keeping the size at
least `1`. -/
theorem one_le_arraySizeAt (a : ℕ) {H : ℕ} (hH : 1 ≤ H) : 1 ≤ arraySizeAt a H := by
  rw [arraySizeAt, Nat.mul_comm]
  refine Nat.le_trans ?_ (Nat.le_mul_add_sub_one_div _ chunk_pos)
  split <;> lia [defaultArraySize_pos, maxArraySize_pos]

theorem Params.one_le_arraySizeAt (P : Params) {H : ℕ} (hH : 1 ≤ H) : 1 ≤ P.arraySizeAt H :=
  Ratpoints.one_le_arraySizeAt P.arraySize hH

end Ratpoints

end
