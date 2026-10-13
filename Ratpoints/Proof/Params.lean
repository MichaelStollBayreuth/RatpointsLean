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
import Ratpoints.Proof.Bits

/-!
# The sieving parameters: the primes of the table, well-formedness and the array size

Every entry of `Ratpoints.primeTable` is a prime, which `norm_num` checks one entry at a time, the
table lists every odd prime below 1022 in increasing order, which `decide` checks, so that its first
`Ratpoints.numPrimes` entries are below `Ratpoints.maxPrimeEven`, a bound that keeps the accumulator
of Horner's rule in `examine_prime` in the range of its C type; every parameter set that the options
of the program give is well-formed; and the pieces of the numerators have at least one bit array.

## Main statements

* `Ratpoints.prime_of_mem_primeTable`, `Ratpoints.prime_getElem!_primeTable`: every entry of
  `Ratpoints.primeTable` is a prime, so that the moduli of well-formed parameters are primes
  (`Ratpoints.Params.WF.prime_of_mem`).
* `Ratpoints.pairwise_lt_toList_primeTable`, `Ratpoints.lt_of_mem_primeTable`,
  `Ratpoints.mem_primeTable_of_prime`: the table lists every odd prime below 1022, and nothing
  larger, in increasing order, which `decide` checks; `Ratpoints.mem_of_toList_primeTable_eq`: so it
  lists every odd prime below an entry before it.
* `Ratpoints.getElem!_primeTable_lt_maxPrimeEven`: the first `Ratpoints.numPrimes` primes of the
  table are below `Ratpoints.maxPrimeEven`.
* `Ratpoints.maxPrimeEven_le_two_pow_10`, `Ratpoints.maxPrimeEven_le_two_pow_32`: the moduli below
  `Ratpoints.maxPrimeEven` are below `2 ^ 10`, so below `2 ^ 32`;
  `Ratpoints.pow_hornerSteps_add_one_lt`: the accumulator of Horner's rule in `examine_prime` stays
  in the range of its C type between two reductions.
* `Ratpoints.wf_sieveParams`: every parameter set that the options of the program give is
  well-formed; comparator certifies this (`comparator/Challenge.lean`), which also rules out a
  well-formedness that nothing satisfies.
* `Ratpoints.wf_defaultParams`: the parameters of a run without options are well-formed.
* `Ratpoints.Params.one_le_arraySizeAt`: for a height bound `H ≥ 1` a piece of the numerators has
  at least one bit array.
-/

@[expose] public section

namespace Ratpoints

theorem prime_of_mem_primeTable {p : ℕ} (h : p ∈ primeTable) : p.Prime := by
  rw [primeTable, List.mem_toArray] at h
  repeat' obtain rfl | h := List.mem_cons.mp h
  all_goals first | exact absurd h List.not_mem_nil | norm_num

theorem Params.WF.prime_of_mem {P : Params} (hP : P.WF) {p : ℕ} (hp : p ∈ P.moduli) : p.Prime :=
  prime_of_mem_primeTable (hP.mem_primeTable p hp)

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
  · have := hq.eq_one_or_self_of_dvd d (Nat.dvd_of_mod_eq_zero hd)
    lia
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

theorem numPrimes_le_size_primeTable : numPrimes ≤ primeTable.size :=
  (List.length_filter_le _ _).trans_eq primeTable.length_toList

/-! ### The primes of the table by their positions -/

theorem prime_getElem!_primeTable {pn : ℕ} (h : pn < primeTable.size) : primeTable[pn]!.Prime :=
  (getElem!_pos primeTable pn h).symm ▸ prime_of_mem_primeTable (Array.getElem_mem h)

theorem one_lt_getElem!_primeTable {pn : ℕ} (h : pn < numPrimes) : 1 < primeTable[pn]! :=
  (prime_getElem!_primeTable (h.trans_le numPrimes_le_size_primeTable)).one_lt

/-- The first `Ratpoints.numPrimes` primes of the table are below `Ratpoints.maxPrimeEven`, since
the table increases. -/
theorem getElem!_primeTable_lt_maxPrimeEven {pn : ℕ} (h : pn < numPrimes) :
    primeTable[pn]! < maxPrimeEven := by
  rw [getElem!_pos primeTable pn (h.trans_le numPrimes_le_size_primeTable), ← Array.getElem_toList]
  exact List.getElem_lt_of_lt_length_filter (pairwise_lt_toList_primeTable.imp le_of_lt) h

/-! ### The moduli in the range of the C types -/

/-- The moduli below `maxPrimeEven` are below `2 ^ 10`, since `maxBitsInPrime ≤ 10`
(`Ratpoints.maxBitsInPrime_le_ten`), as the comment on Horner's rule in `examine_power` assumes
(`find_points.c:2286-2287`). -/
theorem maxPrimeEven_le_two_pow_10 : maxPrimeEven ≤ 2 ^ 10 :=
  Nat.pow_le_pow_right (by decide) maxBitsInPrime_le_ten

/-- The moduli below `maxPrimeEven` are below `2 ^ 32` (`Ratpoints.maxPrimeEven_le_two_pow_10`):
so the helper `mod` of the C code keeps its values in the range of a `long` for them
(`Ratpoints.fitsLong_sixteen_mul`, `Ratpoints.fitsLong_add_sixteen_mul`, for `b < 2 ^ 59`), where
`examine_power` calls it (`find_points.c:2278`). -/
theorem maxPrimeEven_le_two_pow_32 : maxPrimeEven ≤ 2 ^ 32 :=
  maxPrimeEven_le_two_pow_10.trans (by norm_num)

/-- The bound of the schedule of Horner's rule in the table of a prime `p < maxPrimeEven` in
`examine_prime`: `p ^ (hornerSteps + 1) < 2 ^ 64`, since `hornerSteps + 1 = 64 / maxBitsInPrime`,
which `Ratpoints.one_le_hornerSteps` gives, and `maxBitsInPrime (64 / maxBitsInPrime) ≤ 64`. -/
theorem pow_hornerSteps_add_one_lt {p : ℕ} (hp : p < maxPrimeEven) :
    p ^ (hornerSteps + 1) < 2 ^ 64 := by
  have := one_le_hornerSteps
  rw [hornerSteps] at this ⊢
  rw [Nat.sub_add_cancel (by lia : 1 ≤ 64 / maxBitsInPrime)]
  exact Nat.pow_lt_two_pow_of_lt hp (Nat.mul_div_le 64 _) (by lia)

/-- Every parameter set that the options of the program give is well-formed; comparator certifies
this (`comparator/Challenge.lean`). -/
theorem wf_sieveParams (o : SieveOptions) : (sieveParams o).WF where
  mem_primeTable _ hm := Array.mem_toList_iff.mp (List.mem_of_mem_take hm)
  sp1_le_sp2 := by
    simp only [sieveParams]
    split_ifs <;> lia
  sp2_le_length := by
    have := numPrimes_le_size_primeTable
    simp only [sieveParams, List.length_take, Array.length_toList]
    split_ifs <;> lia

theorem wf_defaultParams : defaultParams.WF := wf_sieveParams {}

/-- The pieces of the numerators are not empty, so that the loop over the pieces of a denominator
advances; this reads off only that `Ratpoints.defaultArraySize` and `Ratpoints.maxArraySize` are
positive. -/
theorem Params.one_le_arraySizeAt (P : Params) {H : ℕ} (hH : 1 ≤ H) : 1 ≤ P.arraySizeAt H := by
  have := defaultArraySize_pos
  have := maxArraySize_pos
  rw [arraySizeAt]
  split <;> lia

/-! ### The axioms of the certified theorem -/

/--
info: 'Ratpoints.wf_sieveParams' depends on axioms: [propext, Classical.choice, Quot.sound]
-/
#guard_msgs in
#print axioms wf_sieveParams

end Ratpoints

end
