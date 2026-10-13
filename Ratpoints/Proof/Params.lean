/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.Prime.Defs
public import Ratpoints.Model.Params
public import Std.WP

import Mathlib.Algebra.BigOperators.Group.List.Lemmas
import Mathlib.Tactic.NormNum.Prime
import Ratpoints.Mathlib.Data.List.Pairwise
import Ratpoints.Mathlib.Data.List.Sort
import Ratpoints.Proof.Bits
import Std.Tactic.Do

/-!
# The sieving parameters: the table, the factors of a modulus, well-formedness, the array size

Every entry of `Ratpoints.primeTable` is a prime, which `norm_num` checks one entry at a time, the
table lists every odd prime below 1022 in increasing order, which `decide` checks, so that its first
`Ratpoints.numPrimes` entries are below `Ratpoints.maxPrimeEven`, a bound that keeps the accumulator
of Horner's rule in `examine_prime` and the values of `examine_power` in the range of their C types;
the factors of a modulus over the table multiply to it with the cofactor, and the factorization of
a modulus each of whose divisors above `1` is divisible by one of the first `Ratpoints.numPrimes`
primes of the table, which the moduli of well-formed parameters are, is complete; every parameter
set that the options of the program give is well-formed; and the pieces of the numerators have at
least one bit array.

## Main definitions

* `Ratpoints.ModulusFactorsInvariant`, `Ratpoints.ModulusFactorsPowInvariant`: the invariants of
  the loops of `Ratpoints.modulusFactors`.

## Main statements

* `Ratpoints.prime_of_mem_primeTable`, `Ratpoints.prime_getElem!_primeTable`: every entry of
  `Ratpoints.primeTable` is a prime, so that the moduli of the third stage of well-formed parameters
  are primes (`Ratpoints.Params.WF.prime_of_mem_drop`).
* `Ratpoints.pairwise_lt_toList_primeTable`, `Ratpoints.lt_of_mem_primeTable`,
  `Ratpoints.mem_primeTable_of_prime`: the table lists every odd prime below 1022, and nothing
  larger, in increasing order, which `decide` checks; `Ratpoints.mem_of_toList_primeTable_eq`: so it
  lists every odd prime below an entry before it.
* `Ratpoints.getElem!_primeTable_lt_maxPrimeEven`: the first `Ratpoints.numPrimes` primes of the
  table are below `Ratpoints.maxPrimeEven`; `Ratpoints.getElem!_primeTable_le_of_le`: the table
  increases.
* `Ratpoints.maxPrimeEven_le_two_pow_10`, `Ratpoints.maxPrimeEven_le_two_pow_32`: the moduli below
  `Ratpoints.maxPrimeEven` are below `2 ^ 10`, so below `2 ^ 32`;
  `Ratpoints.mul_add_lt_two_pow_64_of_lt_maxPrimeEven`,
  `Ratpoints.mul_self_lt_two_pow_63_of_lt_maxPrimeEven`: the values of `examine_power` stay in the
  range of their C types; `Ratpoints.pow_hornerSteps_add_one_lt`: so does the accumulator of
  Horner's rule in `examine_prime` between two reductions, since
  `hornerSteps + 1 = 64 / maxBitsInPrime` (`Ratpoints.hornerSteps_add_one`).
* `Ratpoints.modulusFactors_spec`: the contract of the factors of a modulus over the table, with its
  plain forms `Ratpoints.eq_mul_prod_run_modulusFactors`,
  `Ratpoints.lt_numPrimes_of_mem_run_modulusFactors`, `Ratpoints.one_le_of_mem_run_modulusFactors`,
  `Ratpoints.pow_dvd_of_mem_run_modulusFactors`, each factor dividing the modulus,
  `Ratpoints.getElem!_primeTable_ne_snd_run_modulusFactors`, the cofactor being none of the first
  `Ratpoints.numPrimes` primes of the table, and
  `Ratpoints.snd_run_modulusFactors_lt_mul_self_of_dvd`, a prime of the table that divides the
  cofactor being above its square root.
* `Ratpoints.snd_run_modulusFactors_eq_one`: a modulus each of whose divisors above `1` is
  divisible by one of the first `Ratpoints.numPrimes` primes of the table, as the moduli of
  well-formed parameters are, factors completely over the table.
* `Ratpoints.Params.WF.one_lt_of_mem`, `Ratpoints.Params.WF.prime_of_mem_drop`: what the search
  reads off well-formed parameters, beyond their fields.
* `Ratpoints.wf_sieveParams`: every parameter set that the options of the program give is
  well-formed; comparator certifies this (`comparator/Challenge.lean`), which also rules out a
  well-formedness that nothing satisfies.
* `Ratpoints.wf_defaultParams`: the parameters of a run without options are well-formed.
* `Ratpoints.Params.one_le_arraySizeAt`: for a height bound `H ≥ 1` a piece of the numerators has
  at least one bit array.

## Implementation notes

The contract of `Ratpoints.modulusFactors` is proved with `vcgen`, the program logic of Lean core,
with loop invariants that are named definitions.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

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

/-- The prime at the cursor of a loop over the positions of the first `Ratpoints.numPrimes` primes
of the table is above `1`. -/
theorem one_lt_getElem!_primeTable_of_toList {pref suff : List ℕ} {cur : ℕ}
    (hl : ForIn.toList [:numPrimes] = pref ++ cur :: suff) : 1 < primeTable[cur]! :=
  one_lt_getElem!_primeTable (Std.Legacy.Range.lt_of_toList_eq_append_cons hl)

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

/-- The moduli below `Ratpoints.maxPrimeEven` are below `2 ^ 10`, since `maxBitsInPrime ≤ 10`
(`Ratpoints.maxBitsInPrime_le_ten`), as the comment on Horner's rule in `examine_power` assumes
(`find_points.c:2286-2287`). -/
theorem maxPrimeEven_le_two_pow_10 : maxPrimeEven ≤ 2 ^ 10 :=
  Nat.pow_le_pow_right (by decide) maxBitsInPrime_le_ten

/-- The moduli below `Ratpoints.maxPrimeEven` are below `2 ^ 32`
(`Ratpoints.maxPrimeEven_le_two_pow_10`): so the helper `mod` of the C code keeps its values in the
range of a `long` for them (`Ratpoints.fitsLong_sixteen_mul`, `Ratpoints.fitsLong_add_sixteen_mul`,
for `b < 2 ^ 59`), where `examine_power` calls it (`find_points.c:2278`). -/
theorem maxPrimeEven_le_two_pow_32 : maxPrimeEven ≤ 2 ^ 32 :=
  maxPrimeEven_le_two_pow_10.trans (by norm_num)

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
    p ^ (hornerSteps + 1) < 2 ^ 64 := by
  rw [hornerSteps_add_one]
  exact Nat.pow_lt_two_pow_of_lt hp (Nat.mul_div_le 64 _) (hornerSteps_add_one ▸ Nat.succ_ne_zero _)

/-! ### The factors of a modulus over the table -/

/-- The invariant of the loop of `Ratpoints.modulusFactors` over the positions below `k` of
`Ratpoints.primeTable`, on the cofactor `s.1` and the factors `s.2` found: `m` is the cofactor times
the product of the factors `primeTable[pn] ^ e`, whose positions `pn` increase and are below `k` and
whose exponents `e` are at least `1`; the cofactor is none of the primes at the positions below `k`,
while the loop goes on none of them divides it, and one of them that divides it is above its square
root. -/
def ModulusFactorsInvariant (m k : ℕ) (s : ℕ × Array (ℕ × ℕ)) : Prop :=
  m = s.1 * (s.2.toList.map fun f ↦ primeTable[f.1]! ^ f.2).prod ∧
    (s.2.toList.map Prod.fst).Pairwise (· < ·) ∧ (∀ f ∈ s.2.toList, f.1 < k ∧ 1 ≤ f.2) ∧
    ∀ j < k, primeTable[j]! ≠ s.1 ∧ (k < numPrimes → ¬primeTable[j]! ∣ s.1) ∧
      (primeTable[j]! ∣ s.1 → s.1 < primeTable[j]! * primeTable[j]!)

/-- The invariant of the loop of `Ratpoints.modulusFactors` that divides `p` off the cofactor `r`,
on the cofactor `s.1` and the exponent `s.2`: `s.1 p ^ s.2 = r` with `s.1 ≥ 1`, `p ∣ s.1` before the
first division, and `p ∤ s.1` at the exit. -/
def ModulusFactorsPowInvariant (r p : ℕ) : Std.WP.WhileInvariant (ℕ × ℕ) Prop :=
  .mk fun exit s ↦ s.1 * p ^ s.2 = r ∧ 0 < s.1 ∧ (s.2 = 0 → s.1 % p = 0) ∧
    (exit = true → s.1 % p ≠ 0)

-- The positions of the factors after a push of a factor at a position above all of them.
private theorem pairwise_map_fst_toList_push {fac : Array (ℕ × ℕ)} {g : ℕ × ℕ}
    (h : (fac.toList.map Prod.fst).Pairwise (· < ·)) (hg : ∀ f ∈ fac.toList, f.1 < g.1) :
    ((fac.push g).toList.map Prod.fst).Pairwise (· < ·) := by
  rw [Array.toList_push, List.map_append, List.pairwise_append]
  refine ⟨h, List.pairwise_singleton _ _, fun a ha b hb ↦ ?_⟩
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp ha
  rw [List.map_cons, List.map_nil, List.mem_singleton] at hb
  exact hb ▸ hg f hf

theorem modulusFactorsInvariant_zero (m : ℕ) : ModulusFactorsInvariant m 0 (m, #[]) := by
  simp [ModulusFactorsInvariant]

-- The invariant at the end of the loop, from the first three parts at a position up to
-- `numPrimes`, a cofactor that is none of the first `numPrimes` primes of the table and below the
-- square of each of them that divides it.
private theorem ModulusFactorsInvariant.toList_of_ne {m k rest : ℕ} {fac : Array (ℕ × ℕ)}
    (h : ModulusFactorsInvariant m k (rest, fac)) (hk : k ≤ numPrimes)
    (hne : ∀ j < numPrimes, primeTable[j]! ≠ rest)
    (hsq : ∀ j < numPrimes, primeTable[j]! ∣ rest → rest < primeTable[j]! * primeTable[j]!) :
    ModulusFactorsInvariant m (ForIn.toList [:numPrimes]).length (rest, fac) := by
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero]
  exact ⟨h.1, h.2.1, fun f hf ↦ ⟨(h.2.2.1 f hf).1.trans_le hk, (h.2.2.1 f hf).2⟩,
    fun j hj ↦ ⟨hne j hj, by lia, hsq j hj⟩⟩

-- A cofactor at most `1` is below the square of every prime of the table among the first
-- `numPrimes`.
private theorem lt_mul_self_getElem!_primeTable_of_le_one {r j : ℕ} (hr : r ≤ 1)
    (hj : j < numPrimes) : r < primeTable[j]! * primeTable[j]! :=
  hr.trans_lt ((one_lt_getElem!_primeTable hj).trans_le (Nat.le_mul_self _))

/-- The exit of the loop of `Ratpoints.modulusFactors` when the cofactor is at most `1`. -/
theorem ModulusFactorsInvariant.of_le_one {m rest : ℕ} {fac : Array (ℕ × ℕ)} {pref suff : List ℕ}
    {cur : ℕ} (h : ModulusFactorsInvariant m pref.length (rest, fac))
    (hl : ForIn.toList [:numPrimes] = pref ++ cur :: suff) (hr : rest ≤ 1) :
    ModulusFactorsInvariant m (ForIn.toList [:numPrimes]).length (rest, fac) :=
  h.toList_of_ne (Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl ▸
    (Std.Legacy.Range.lt_of_toList_eq_append_cons hl).le)
    (fun j hj ↦ by have := one_lt_getElem!_primeTable hj; lia)
    fun j hj _ ↦ lt_mul_self_getElem!_primeTable_of_le_one hr hj

/-- The exit of the loop of `Ratpoints.modulusFactors` when the cofactor, below the square of the
prime at the cursor, is a prime of the table from the cursor on: it becomes a factor with the
exponent `1`. -/
theorem ModulusFactorsInvariant.push_find {m rest pn : ℕ} {fac : Array (ℕ × ℕ)}
    {pref suff : List ℕ} {cur : ℕ} (h : ModulusFactorsInvariant m pref.length (rest, fac))
    (hl : ForIn.toList [:numPrimes] = pref ++ cur :: suff)
    (hf : (List.range' cur (numPrimes - cur)).find? (primeTable[·]! == rest) = some pn) :
    ModulusFactorsInvariant m (ForIn.toList [:numPrimes]).length (1, fac.push (pn, 1)) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hpn := List.mem_range'_1.mp (List.mem_of_find?_eq_some hf)
  have hr : primeTable[pn]! = rest := by simpa using List.find?_some hf
  obtain ⟨hm, hpw, hfac, -⟩ := h
  refine ModulusFactorsInvariant.toList_of_ne (k := numPrimes) ⟨?_, ?_, ?_, ?_⟩ le_rfl
    (fun j hj ↦ by have := one_lt_getElem!_primeTable hj; lia)
    fun j hj _ ↦ lt_mul_self_getElem!_primeTable_of_le_one le_rfl hj
  · simp [hm, hr, Nat.mul_comm]
  · exact pairwise_map_fst_toList_push hpw fun f hf' ↦ (hfac f hf').1.trans_le hpn.1
  · exact Array.forall_mem_toList_push (fun f hf' ↦ ⟨(hfac f hf').1.trans (by lia), (hfac f hf').2⟩)
      ⟨by lia, le_rfl⟩
  · exact fun j hj ↦ ⟨by have := one_lt_getElem!_primeTable hj; lia, by lia,
      fun _ ↦ lt_mul_self_getElem!_primeTable_of_le_one le_rfl hj⟩

/-- The exit of the loop of `Ratpoints.modulusFactors` when the cofactor, below the square of the
prime at the cursor, is no prime of the table from the cursor on; the primes of the table from the
cursor on are at least the prime at the cursor. -/
theorem ModulusFactorsInvariant.of_find?_eq {m rest : ℕ} {fac : Array (ℕ × ℕ)}
    {pref suff : List ℕ} {cur : ℕ} {o : Option ℕ}
    (h : ModulusFactorsInvariant m pref.length (rest, fac))
    (hl : ForIn.toList [:numPrimes] = pref ++ cur :: suff)
    (hlt : rest < primeTable[cur]! * primeTable[cur]!) (ho : ∀ pn, o = some pn → False)
    (hf : (List.range' cur (numPrimes - cur)).find? (primeTable[·]! == rest) = o) :
    ModulusFactorsInvariant m (ForIn.toList [:numPrimes]).length (rest, fac) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hnone := List.find?_eq_none.mp (hf.trans (Option.eq_none_iff_forall_ne_some.mpr
    fun pn hpn ↦ ho pn hpn))
  refine h.toList_of_ne hcur.le (fun j hj ↦ ?_) fun j hj hd ↦ ?_
  all_goals rcases Nat.lt_or_ge j pref.length with hj' | hj'
  · exact (h.2.2.2 j hj').1
  · simpa using hnone j (List.mem_range'_1.mpr ⟨hj', by lia⟩)
  · exact absurd hd ((h.2.2.2 j hj').2.1 hcur)
  · have := getElem!_primeTable_le_of_le hj' (hj.trans_le numPrimes_le_size_primeTable)
    exact hlt.trans_le (Nat.mul_le_mul this this)

-- The last part of the invariant after the cursor `k`, for a divisor `x` of the cofactor that the
-- prime at the cursor does not divide.
private theorem forall_ne_and_not_dvd_of_dvd {k r x : ℕ}
    (h : ∀ j < k, primeTable[j]! ≠ r ∧ (k < numPrimes → ¬primeTable[j]! ∣ r) ∧
      (primeTable[j]! ∣ r → r < primeTable[j]! * primeTable[j]!))
    (hk : k < numPrimes) (hx : x ∣ r) (hkx : ¬primeTable[k]! ∣ x) :
    ∀ j < k + 1, primeTable[j]! ≠ x ∧ (k + 1 < numPrimes → ¬primeTable[j]! ∣ x) ∧
      (primeTable[j]! ∣ x → x < primeTable[j]! * primeTable[j]!) := by
  have hnd (j : ℕ) (hj : j < k + 1) : ¬primeTable[j]! ∣ x := by
    rcases Nat.lt_or_ge j k with hj' | hj'
    · exact fun hd ↦ (h j hj').2.1 hk (hd.trans hx)
    · exact (by lia : j = k) ▸ hkx
  exact fun j hj ↦ ⟨fun he ↦ hnd j hj (he ▸ dvd_rfl), fun _ ↦ hnd j hj, (absurd · (hnd j hj))⟩

/-- The step of the loop of `Ratpoints.modulusFactors` at a prime of the table that does not
divide the cofactor. -/
theorem ModulusFactorsInvariant.push_of_mod_ne_zero {m rest : ℕ} {fac : Array (ℕ × ℕ)}
    {pref suff : List ℕ} {cur : ℕ} (h : ModulusFactorsInvariant m pref.length (rest, fac))
    (hl : ForIn.toList [:numPrimes] = pref ++ cur :: suff) (hr : ¬rest % primeTable[cur]! = 0) :
    ModulusFactorsInvariant m (pref ++ [cur]).length (rest, fac) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton]
  exact ⟨h.1, h.2.1, fun f hf ↦ ⟨(h.2.2.1 f hf).1.trans (by lia), (h.2.2.1 f hf).2⟩,
    forall_ne_and_not_dvd_of_dvd h.2.2.2 hcur dvd_rfl fun hd ↦ hr (Nat.mod_eq_zero_of_dvd hd)⟩

/-- The step of the loop of `Ratpoints.modulusFactors` at a prime of the table that divides the
cofactor: after the loop that divides it off, it is a factor with its exponent. -/
theorem ModulusFactorsInvariant.push_pow {m rest x e : ℕ} {fac : Array (ℕ × ℕ)}
    {pref suff : List ℕ} {cur : ℕ} (h : ModulusFactorsInvariant m pref.length (rest, fac))
    (hl : ForIn.toList [:numPrimes] = pref ++ cur :: suff)
    (hv : ModulusFactorsPowInvariant rest primeTable[cur]! true (x, e)) :
    ModulusFactorsInvariant m (pref ++ [cur]).length (x, fac.push (cur, e)) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨hxe, -, he, hx⟩ := hv
  have hx := hx rfl
  obtain ⟨hm, hpw, hfac, hne⟩ := h
  rw [List.length_append, List.length_singleton]
  refine ⟨?_, ?_, ?_, forall_ne_and_not_dvd_of_dvd hne hcur (Dvd.intro _ hxe)
    fun hd ↦ hx (Nat.mod_eq_zero_of_dvd hd)⟩
  · simp only [Array.toList_push, List.map_append, List.prod_append, hm, ← hxe]
    simp only [List.map_cons, List.map_nil, List.prod_singleton]
    ac_rfl
  · exact pairwise_map_fst_toList_push hpw fun f hf' ↦ (hfac f hf').1
  · exact Array.forall_mem_toList_push (fun f hf' ↦ ⟨(hfac f hf').1.trans (by lia), (hfac f hf').2⟩)
      ⟨by lia, Nat.one_le_iff_ne_zero.mpr fun h0 ↦ hx (he h0)⟩

/-- The invariant of the loop of `Ratpoints.modulusFactors` at its end gives its contract. -/
theorem ModulusFactorsInvariant.post {m rest : ℕ} {fac : Array (ℕ × ℕ)}
    (h : ModulusFactorsInvariant m (ForIn.toList [:numPrimes]).length (rest, fac)) :
    m = rest * (fac.toList.map fun f ↦ primeTable[f.1]! ^ f.2).prod ∧
      (fac.toList.map Prod.fst).Pairwise (· < ·) ∧ (∀ f ∈ fac.toList, f.1 < numPrimes ∧ 1 ≤ f.2) ∧
      ∀ j < numPrimes, primeTable[j]! ≠ rest ∧
        (primeTable[j]! ∣ rest → rest < primeTable[j]! * primeTable[j]!) := by
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at h
  exact ⟨h.1, h.2.1, h.2.2.1, fun j hj ↦ ⟨(h.2.2.2 j hj).1, (h.2.2.2 j hj).2.2⟩⟩

theorem modulusFactorsPowInvariant_zero {r p : ℕ} (hr : ¬r ≤ 1) (hp : r % p = 0) :
    ModulusFactorsPowInvariant r p false (r, 0) :=
  ⟨by simp, by lia, fun _ ↦ hp, nofun⟩

/-- The step of the loop of `Ratpoints.modulusFactors` that divides `p > 1` off the cofactor, with
the measure. -/
theorem ModulusFactorsPowInvariant.div {r p x e : ℕ}
    (h : ModulusFactorsPowInvariant r p false (x, e)) (hp : 1 < p) (hx : x % p = 0) :
    x / p < x ∧ ModulusFactorsPowInvariant r p false (x / p, e + 1) := by
  obtain ⟨hxe, hx0, -, -⟩ := h
  dsimp only at hxe hx0
  have hpx : p ∣ x := Nat.dvd_of_mod_eq_zero hx
  refine ⟨Nat.div_lt_self hx0 hp, ?_, Nat.div_pos (Nat.le_of_dvd hx0 hpx) (by lia), nofun, nofun⟩
  rw [← hxe, Nat.pow_succ, Nat.mul_comm (p ^ e) p, ← Nat.mul_assoc, Nat.div_mul_cancel hpx]

theorem ModulusFactorsPowInvariant.exit {r p x e : ℕ}
    (h : ModulusFactorsPowInvariant r p false (x, e)) (hx : ¬x % p = 0) :
    ModulusFactorsPowInvariant r p true (x, e) :=
  ⟨h.1, h.2.1, h.2.2.1, fun _ ↦ hx⟩

-- `primeTable` irreducible: a failed alternative of the dispatch would compare `1` with
-- `primeTable[cur]! * primeTable[cur]!` and evaluate the table until the recursion limit.
attribute [local irreducible] ModulusFactorsInvariant ModulusFactorsPowInvariant primeTable in
/-- The contract of `Ratpoints.modulusFactors`: `m` is the cofactor times the product of the
factors `primeTable[pn] ^ e`, whose positions `pn` increase and are below `Ratpoints.numPrimes` and
whose exponents `e` are at least `1`, and the cofactor is none of the first `Ratpoints.numPrimes`
primes of the table and below the square of each of them that divides it. The loop that divides a
prime off ends, since the cofactor drops. -/
@[spec]
theorem modulusFactors_spec (m : ℕ) :
    ⦃ True ⦄ modulusFactors m
    ⦃ fun r ↦ m = r.2 * (r.1.map fun f ↦ primeTable[f.1]! ^ f.2).prod ∧
        (r.1.map Prod.fst).Pairwise (· < ·) ∧ (∀ f ∈ r.1, f.1 < numPrimes ∧ 1 ≤ f.2) ∧
        ∀ j < numPrimes, primeTable[j]! ≠ r.2 ∧
          (primeTable[j]! ∣ r.2 → r.2 < primeTable[j]! * primeTable[j]!) ⦄ := by
  vcgen [modulusFactors] invariants
  | inv1 => fun pref _ s ↦ ModulusFactorsInvariant m pref.length s
  | inv2 _ cur _ _ rest _ _ _ _ _ => ModulusFactorsPowInvariant rest primeTable[cur]!
  | inv3 => .ofMeasure fun s : ℕ × ℕ ↦ s.1
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals try obtain ⟨rfl, _⟩ := ‹_ = _ ∧ ModulusFactorsPowInvariant _ _ false _›
  all_goals first
    | exact modulusFactorsInvariant_zero m
    | exact ModulusFactorsInvariant.post ‹_›
    | exact ModulusFactorsInvariant.of_le_one ‹_› ‹_› ‹_›
    | exact ModulusFactorsInvariant.push_find ‹_› ‹_› ‹_›
    | exact ModulusFactorsInvariant.of_find?_eq ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact modulusFactorsPowInvariant_zero ‹_› ‹_›
    | exact ModulusFactorsInvariant.push_pow ‹_› ‹_› ‹_›
    | exact ModulusFactorsPowInvariant.div ‹_› (one_lt_getElem!_primeTable_of_toList ‹_›) ‹_›
    | exact ModulusFactorsPowInvariant.exit ‹_› ‹_›
    | exact ModulusFactorsInvariant.push_of_mod_ne_zero ‹_› ‹_› ‹_›

/-- `Ratpoints.modulusFactors_spec` as a plain statement: `m` is the cofactor times the product of
the factors. -/
theorem eq_mul_prod_run_modulusFactors (m : ℕ) :
    m = (Id.run (modulusFactors m)).2 *
      ((Id.run (modulusFactors m)).1.map fun f ↦ primeTable[f.1]! ^ f.2).prod :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((modulusFactors_spec m).le_wp trivial)).1

theorem lt_numPrimes_of_mem_run_modulusFactors {m : ℕ} {f : ℕ × ℕ}
    (hf : f ∈ (Id.run (modulusFactors m)).1) : f.1 < numPrimes :=
  ((Std.WP.Id.of_run_eq_wp rfl _ ((modulusFactors_spec m).le_wp trivial)).2.2.1 f hf).1

theorem one_le_of_mem_run_modulusFactors {m : ℕ} {f : ℕ × ℕ}
    (hf : f ∈ (Id.run (modulusFactors m)).1) : 1 ≤ f.2 :=
  ((Std.WP.Id.of_run_eq_wp rfl _ ((modulusFactors_spec m).le_wp trivial)).2.2.1 f hf).2

theorem getElem!_primeTable_ne_snd_run_modulusFactors (m : ℕ) {j : ℕ} (hj : j < numPrimes) :
    primeTable[j]! ≠ (Id.run (modulusFactors m)).2 :=
  ((Std.WP.Id.of_run_eq_wp rfl _ ((modulusFactors_spec m).le_wp trivial)).2.2.2 j hj).1

/-- A prime among the first `Ratpoints.numPrimes` of the table that divides the cofactor of `m` is
above the square root of the cofactor. -/
theorem snd_run_modulusFactors_lt_mul_self_of_dvd (m : ℕ) {j : ℕ} (hj : j < numPrimes)
    (h : primeTable[j]! ∣ (Id.run (modulusFactors m)).2) :
    (Id.run (modulusFactors m)).2 < primeTable[j]! * primeTable[j]! :=
  ((Std.WP.Id.of_run_eq_wp rfl _ ((modulusFactors_spec m).le_wp trivial)).2.2.2 j hj).2 h

/-- Each factor `primeTable[pn] ^ e` of `m` over the table divides `m`. -/
theorem pow_dvd_of_mem_run_modulusFactors {m : ℕ} {f : ℕ × ℕ}
    (hf : f ∈ (Id.run (modulusFactors m)).1) : primeTable[f.1]! ^ f.2 ∣ m := by
  rw [eq_mul_prod_run_modulusFactors m]
  exact (List.dvd_prod (List.mem_map_of_mem hf)).mul_left _

/-- A modulus `m > 0` each of whose divisors above `1` is divisible by one of the first
`Ratpoints.numPrimes` primes of the table factors completely over the table, as the moduli of
well-formed parameters do (`Ratpoints.Params.WF`): a cofactor `r > 1` would have its least prime
factor among these primes, other than `r`, so that `r` would not be a prime and its least prime
factor would be at most its square root, which no prime of the table that divides the cofactor is
(`Ratpoints.snd_run_modulusFactors_lt_mul_self_of_dvd`). -/
theorem snd_run_modulusFactors_eq_one {m : ℕ} (hm : 0 < m)
    (h : ∀ q > 1, q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q) :
    (Id.run (modulusFactors m)).2 = 1 := by
  have hr : (Id.run (modulusFactors m)).2 ∣ m := Dvd.intro _ (eq_mul_prod_run_modulusFactors m).symm
  by_contra h1
  have hq := Nat.minFac_prime h1
  obtain ⟨pn, hpn, hd⟩ := h _ hq.one_lt ((Nat.minFac_dvd _).trans hr)
  have hp := prime_getElem!_primeTable (hpn.trans_le numPrimes_le_size_primeTable)
  have heq := (Nat.prime_dvd_prime_iff_eq hp hq).mp hd
  have hlt := snd_run_modulusFactors_lt_mul_self_of_dvd m hpn (heq ▸ Nat.minFac_dvd _)
  have hsq := Nat.minFac_sq_le_self (Nat.pos_of_dvd_of_pos hr hm) fun hrp ↦
    getElem!_primeTable_ne_snd_run_modulusFactors m hpn (heq.trans hrp.minFac_eq)
  rw [← heq, sq] at hsq
  lia

/-! ### Well-formed parameters -/

/-- A modulus of well-formed parameters is above `1`. -/
theorem Params.WF.one_lt_of_mem {P : Params} (hP : P.WF) {m : ℕ} (hm : m ∈ P.moduli) : 1 < m :=
  (hP.modulus m hm).1

/-- The moduli of the third stage of well-formed parameters, from the position
`Ratpoints.Params.sp2` on, are primes. -/
theorem Params.WF.prime_of_mem_drop {P : Params} (hP : P.WF) {m : ℕ}
    (hm : m ∈ P.moduli.drop P.sp2) : m.Prime :=
  prime_of_mem_primeTable (hP.mem_primeTable_of_mem_drop m hm)

-- The moduli of the parameters that the options give are among the first `numPrimes` primes of
-- the table.
private theorem exists_lt_numPrimes_of_mem_moduli_sieveParams {o : SieveOptions} {m : ℕ}
    (hm : m ∈ (sieveParams o).moduli) : ∃ pn < numPrimes, primeTable[pn]! = m := by
  simp only [sieveParams] at hm
  obtain ⟨i, hi, rfl⟩ := List.mem_take_iff_getElem.mp hm
  refine ⟨i, ?_, by rw [Array.getElem_toList, getElem!_pos]⟩
  rw [lt_min_iff] at hi
  split_ifs at hi <;> lia

/-- Every parameter set that the options of the program give is well-formed; comparator certifies
this (`comparator/Challenge.lean`): its moduli are the first primes of the table, which are below
`Ratpoints.maxPrimeEven` (`Ratpoints.getElem!_primeTable_lt_maxPrimeEven`), and the only divisor
above `1` of such a prime is the prime itself. -/
theorem wf_sieveParams (o : SieveOptions) : (sieveParams o).WF where
  modulus m hm := by
    obtain ⟨pn, hpn, rfl⟩ := exists_lt_numPrimes_of_mem_moduli_sieveParams hm
    refine ⟨one_lt_getElem!_primeTable hpn, getElem!_primeTable_lt_maxPrimeEven hpn,
      fun q hq hd ↦ ⟨pn, hpn, ?_⟩⟩
    have hp := prime_getElem!_primeTable (hpn.trans_le numPrimes_le_size_primeTable)
    rw [(hp.eq_one_or_self_of_dvd q hd).resolve_left hq.ne']
  mem_primeTable_of_mem_drop _ hm :=
    Array.mem_toList_iff.mp (List.mem_of_mem_take (List.mem_of_mem_drop hm))
  examined_le := Nat.min_le_right _ _
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
