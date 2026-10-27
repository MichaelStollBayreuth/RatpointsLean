/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Ratpoints.Mathlib.NumberTheory.SmoothNumbers
public import Ratpoints.Model.Setup
public import Ratpoints.Spec.Basic
public import Ratpoints.Spec.Order
public import Std.WP

import Mathlib.Data.Nat.Squarefree
import Ratpoints.Mathlib.Data.Int.GCD
import Ratpoints.Mathlib.Data.List.Prime
import Ratpoints.Mathlib.Data.Nat.PadicValNat
import Ratpoints.Mathlib.Data.Nat.Prime.Defs
import Ratpoints.Mathlib.NumberTheory.Padics.PadicVal.Basic
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Params
import Ratpoints.Proof.Setup
import Ratpoints.Proof.Valuation
import Std.Tactic.Do

/-!
# The denominators of a polynomial of odd degree

For a polynomial of odd degree the denominator of every point is a squarefree divisor of the
leading coefficient `c_d` times a square, and a square when `|c_d| = 1`: a prime `p ∤ c_d` divides
it an even number of times, since the term `c_d a ^ d b` of `F(a, b)` alone has the least valuation.
The divisor set-up (`Ratpoints.Setup.setupUs1`) factors `|c_d|` over `2` and the primes of the
table, the cofactor below the square of the next prime of the table being a prime since the table
holds every odd prime below 1022 in increasing order (`Ratpoints.Setup.factorLcf`), lists the
squarefree divisors of `c_d` up to the largest denominator by the doubling loop
(`Ratpoints.Setup.squarefreeDivisors`), and computes the slopes of the valuation test
(`Ratpoints.Setup.slope`), whose entries exclude no denominator of a point. The products `x p` that
the C code computes as `long`s stay at most the largest denominator, and the square `p * p` of a
prime of the table, an `int`, below `2 ^ 31`. The factorization finds the primes in increasing
order, so that the divisors come in the order of binary counting over the primes, and while a prime
of the table is still to come its cofactor is the part of `|c_d|` at the primes from it on
(`Nat.IsRoughPart`), so that it is complete exactly when the specification of the order says so
(`Ratpoints.FactorsByTrialDivision`): the divisor set-up succeeds exactly when the factorization is
complete and the doubling loop, which lists a prefix of all the products when it stops, finds fewer
than `Ratpoints.maxDivisors` divisors.

## Main definitions

* `Ratpoints.Setup.IsFactorization`: a list of primes in increasing order with their valuations
  that holds every prime factor of a number.
* `Ratpoints.Setup.extendDivisors`: one pass of the doubling loop of the squarefree divisors.
* `Ratpoints.Setup.DenInfo.excludes`: whether an entry of the valuation test of the divisor shape
  excludes a denominator.

## Main statements

* `Ratpoints.isSquare_of_sq_eq_binaryForm_of_odd`: for odd degree and `|c_d| = 1`, the denominator
  of every point is a square.
* `Ratpoints.exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd`: for odd degree, the denominator of every
  point is `s k ^ 2` with `s` squarefree and `s ∣ c_d`.
* `Ratpoints.even_add_of_sq_eq_binaryForm_of_odd`: the valuation test of the slopes.
* `Ratpoints.factorsByTrialDivision_of_isRoughPart_one`,
  `Ratpoints.factorsByTrialDivision_of_isRoughPart_of_lt`,
  `Ratpoints.eq_one_iff_factorsByTrialDivision_of_isRoughPart`: whether ratpoints factors a number
  completely, read off its parts at the primes from a bound on.
* `Ratpoints.Setup.factorLcf_spec`, `Ratpoints.Setup.squarefreeDivisors_spec`,
  `Ratpoints.Setup.slope_spec`, `Ratpoints.Setup.setupUs1_spec`: the contracts of the divisor
  set-up; the factorization leaves the cofactor `1` exactly when ratpoints factors the number
  completely, and then it lists the primes in increasing order, each with its valuation; the set-up
  succeeds exactly when the cofactor is `1` and the doubling loop gives fewer than
  `Ratpoints.maxDivisors` divisors.
* `Ratpoints.Setup.foldl_extendDivisors_eq_filter`: the doubling loop lists the products of the
  sublists of the primes in the order of binary counting, up to the bound.
* `Ratpoints.Setup.map_snd_run_setupUs1`: the divisor set-up succeeds exactly when ratpoints factors
  `|c_d|` completely and finds fewer than `Ratpoints.maxDivisors` divisors, and its divisors are
  then those of `Ratpoints.binaryDivisors`.
* `Ratpoints.mem_binaryDivisors_iff`, `Ratpoints.nodup_binaryDivisors`: the divisors of
  `Ratpoints.binaryDivisors` are the squarefree divisors up to the bound, each once.
* `Ratpoints.Setup.mem_iff_of_setupUs1_eq_some`, `Ratpoints.Setup.nodup_of_setupUs1_eq_some`: so
  the divisors of the divisor set-up are the squarefree divisors of `|c_d|` up to the largest
  denominator, each once.
* `Ratpoints.Setup.DenInfo.excludes_eq_false_of_sq_eq`: no entry of the valuation test, a prime of
  `c_d` with its valuation and its slope, excludes the denominator of a point.
* `Ratpoints.Setup.fitsLong_mul_of_le_div`: the products `x p` of the C code are `long`s;
  `Ratpoints.Setup.mul_self_lt_of_mem_primeTable`, `Ratpoints.Setup.fitsLong_of_lt_mul_self`: the
  square `p * p` of a prime of the table is an `int`, and a cofactor below it a `long`.

## Implementation notes

The contracts are proved with `vcgen`, the program logic of Lean core, with loop invariants that are
named definitions, in a file with Mathlib, since they speak of primes and their valuations. That
the macro `CEIL` of the C code rounds up is a private lemma of this file, which only the slopes use:
its `if` is that of the macro, and Mathlib has no ceiling division of integers to state it with.
`Ratpoints.Setup.fitsLong_mul_of_le_div` discharges a range obligation that a Deviation paragraph of
the model states, and no proof consumes it.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

-- The macro `CEIL` of the C code rounds up: `q ⌈t / q⌉ ≥ t` for `q > 0`, with `⌈t / q⌉` as
-- `-⌊-t / q⌋` for `t ≤ 0` and `1 + ⌊(t - 1) / q⌋` for `t > 0`.
private theorem Int.le_mul_ite_neg_ediv (t : ℤ) {q : ℤ} (hq : 0 < q) :
    t ≤ q * if t ≤ 0 then -((-t) / q) else 1 + (t - 1) / q := by
  split <;> lia [Int.emod_add_mul_ediv (-t) q, Int.emod_add_mul_ediv (t - 1) q,
    Int.emod_lt_of_pos (t - 1) hq, Int.emod_nonneg (-t) (by lia : q ≠ 0)]

namespace Ratpoints

/-! ### The denominators of the points -/

/-- For odd degree, a point `(a, y, b)` whose term `c_d a ^ d b` of `F(a, b)` is `p ^ V u` with
`p ∤ u`, while `p ^ (V + 1)` divides every other term, has an even `V`
(`Int.even_and_exists_isSquare_add_of_sq_eq_sum`). -/
theorem even_of_sq_eq_binaryForm_of_odd_of_dvd {c : List ℤ} {a y : ℤ} {b : ℕ} {p V : ℕ}
    [Fact p.Prime] (hd : degree c % 2 = 1) (hy : y ^ 2 = binaryForm c a b) {u : ℤ}
    (hu : c.getD (degree c) 0 * a ^ degree c * b = (p : ℤ) ^ V * u) (hpu : ¬(p : ℤ) ∣ u)
    (h : ∀ i < degree c, (p : ℤ) ^ (V + 1) ∣ c.getD i 0 * a ^ i * (b : ℤ) ^ (degree c + 1 - i)) :
    Even V := by
  rw [binaryForm, hd] at hy
  exact (Int.even_and_exists_isSquare_add_of_sq_eq_sum hy (Finset.self_mem_range_succ _)
    (by rw [Nat.add_sub_cancel_left, pow_one, hu]) hpu
    fun i hi hne ↦ h i (by lia [Finset.mem_range.mp hi])).1

-- The terms of `F(a, b)` other than `c_d a ^ d b`, for `b = p ^ m b'` and `k < d`, when
-- `(d - k) m ≥ 1 + val - v_p(c_k)` for `c_k ≠ 0`, are divisible by `p ^ (val + m + 1)`.
private theorem pow_dvd_of_add_one_le {c : List ℤ} {a b' : ℤ} {p m val k : ℕ} (hk : k < degree c)
    (hmin : c.getD k 0 ≠ 0 → val + 1 ≤ padicValNat p (c.getD k 0).natAbs + (degree c - k) * m) :
    (p : ℤ) ^ (val + m + 1) ∣ c.getD k 0 * a ^ k * ((p : ℤ) ^ m * b') ^ (degree c + 1 - k) := by
  rcases eq_or_ne (c.getD k 0) 0 with h0 | h0
  · rw [h0, zero_mul, zero_mul]
    exact dvd_zero _
  have hc : (p : ℤ) ^ padicValNat p (c.getD k 0).natAbs ∣ c.getD k 0 :=
    Int.natCast_dvd.mpr (by simpa using pow_padicValNat_dvd)
  have hle : val + m + 1 ≤ padicValNat p (c.getD k 0).natAbs + m * (degree c + 1 - k) := by
    have : m * (degree c + 1 - k) = (degree c - k) * m + m := by
      rw [Nat.sub_add_comm hk.le]
      ring
    lia
  refine (pow_dvd_pow _ hle).trans ?_
  rw [pow_add, mul_pow, ← pow_mul]
  exact mul_dvd_mul (hc.mul_right _) (dvd_mul_right _ _)

/-- **The valuation test of the slopes** (odd degree): for a prime `p` with `v_p(c_d) = val` and a
denominator `b` of a point with `m = v_p(b) ≥ 1` and `(d - k) m ≥ 1 + val - v_p(c_k)` for every
`k < d` with `c_k ≠ 0`, the term `c_d a ^ d b` of `F(a, b)` alone has the least valuation
`val + m`, which is then even. -/
theorem even_add_of_sq_eq_binaryForm_of_odd {c : List ℤ} {a y : ℤ} {b p val : ℕ}
    [hp : Fact p.Prime] (hd : degree c % 2 = 1)
    (hval : padicValNat p (c.getD (degree c) 0).natAbs = val)
    (hmin : ∀ k < degree c, c.getD k 0 ≠ 0 →
      val + 1 ≤ padicValNat p (c.getD k 0).natAbs + (degree c - k) * padicValNat p b)
    (hab : Int.gcd a b = 1) (hm : padicValNat p b ≠ 0) (hy : y ^ 2 = binaryForm c a b) :
    Even (val + padicValNat p b) := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpa := Int.not_natCast_dvd_of_gcd_eq_one hp.out.ne_one hab
    (dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr hm))
  obtain ⟨b', hb', hpb'⟩ := Int.exists_eq_pow_padicValInt_mul hp.out.ne_one (n := b)
    fun h ↦ by simp_all
  rw [padicValInt.of_nat] at hb'
  obtain ⟨r, hr, hpr⟩ := Int.exists_eq_pow_padicValInt_mul hp.out.ne_one
    (getD_degree_ne_zero_of_pos (c := c) (by lia))
  rw [padicValInt, hval] at hr
  refine even_of_sq_eq_binaryForm_of_odd_of_dvd hd hy (u := r * a ^ degree c * b')
    (by rw [hr, hb', pow_add]; ring)
    (hpp.not_dvd_mul (hpp.not_dvd_mul hpr (mt hpp.dvd_of_dvd_pow hpa)) hpb') fun i hi ↦ ?_
  rw [hb']
  exact pow_dvd_of_add_one_le hi (hmin i hi)

/-- For odd degree, a prime `p ∤ c_d` divides the denominator `b` of every point an even number of
times: for `v_p(b) ≥ 1` the term `c_d a ^ d b` of `F(a, b)` alone has the least valuation `v_p(b)`
(`Ratpoints.even_add_of_sq_eq_binaryForm_of_odd` with `v_p(c_d) = 0`). -/
theorem even_of_sq_eq_binaryForm_of_odd {c : List ℤ} {a y : ℤ} {b p : ℕ} [Fact p.Prime]
    (hd : degree c % 2 = 1) (hc : ¬(p : ℤ) ∣ c.getD (degree c) 0) (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) : Even (padicValNat p b) := by
  rcases eq_or_ne (padicValNat p b) 0 with h0 | hm
  · simp [h0]
  simpa using even_add_of_sq_eq_binaryForm_of_odd hd
    (padicValNat.eq_zero_of_not_dvd (mt Int.natCast_dvd.mpr hc))
    (fun k hk _ ↦ le_add_left (Nat.mul_pos (Nat.sub_pos_of_lt hk) (Nat.pos_of_ne_zero hm)))
    hab hm hy

/-- For odd degree and a leading coefficient `±1`, the denominator `b` of every point is a square:
its valuation `v_p(b)` at every prime `p` is even (`Ratpoints.even_of_sq_eq_binaryForm_of_odd`),
since for `v_p(b) ≥ 1` the term `c_d a ^ d b` of `F(a, b)` alone has the least valuation. -/
theorem isSquare_of_sq_eq_binaryForm_of_odd {c : List ℤ} (hd : degree c % 2 = 1)
    (hc : IsUnit (c.getD (degree c) 0)) {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) : IsSquare b := by
  refine Nat.isSquare_iff_even_factorization.mpr fun p hp ↦ ?_
  have : Fact p.Prime := ⟨hp⟩
  rw [Nat.factorization_def _ hp]
  exact even_of_sq_eq_binaryForm_of_odd hd
    (fun h ↦ (Nat.prime_iff_prime_int.mp hp).not_isUnit (isUnit_of_dvd_unit h hc)) hab hy

/-- For odd degree, the denominator of every point is `s k ^ 2` with `s` squarefree and dividing the
leading coefficient: a prime that divides `b` an odd number of times divides `c_d`
(`Ratpoints.even_of_sq_eq_binaryForm_of_odd`). -/
theorem exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd {c : List ℤ} (hd : degree c % 2 = 1)
    {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    ∃ s k : ℕ, Squarefree s ∧ s ∣ (c.getD (degree c) 0).natAbs ∧ b = s * k * k := by
  rcases eq_or_ne b 0 with rfl | hb
  · exact ⟨1, 0, squarefree_one, one_dvd _, by simp⟩
  obtain ⟨k, s, hks, hs⟩ := exists_sq_mul_squarefree b
  refine ⟨s, k, hs, ?_, by rw [← hks]; ring⟩
  rcases eq_or_ne (c.getD (degree c) 0) 0 with h0 | h0
  · rw [h0, Int.natAbs_zero]
    exact dvd_zero s
  rw [← Nat.prod_primeFactors_of_squarefree hs, Nat.prod_primeFactors_dvd_iff (by simpa using h0)]
  intro p hp
  obtain ⟨hpp, hps, -⟩ := Nat.mem_primeFactors.mp hp
  refine Nat.mem_primeFactors.mpr ⟨hpp, Int.natCast_dvd.mp (by_contra fun hc ↦ ?_),
    by simpa using h0⟩
  have : Fact p.Prime := ⟨hpp⟩
  have hev := even_of_sq_eq_binaryForm_of_odd hd hc hab hy
  rw [← Nat.factorization_def _ hpp, ← hks, Nat.factorization_mul (left_ne_zero_of_mul (hks ▸ hb))
    hs.ne_zero, Finsupp.add_apply, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul,
    Nat.factorization_eq_one_of_squarefree hs hpp hps] at hev
  exact Nat.not_even_iff_odd.mpr ⟨_, rfl⟩ hev

/-! ### Factoring by trial division -/

/-- A number whose part at the primes from `q ≤ 1022` on is `1` has no prime factor above `1021`,
so that ratpoints factors it completely. -/
theorem factorsByTrialDivision_of_isRoughPart_one {q n : ℕ} (h : Nat.IsRoughPart q n 1)
    (hq : q ≤ 1022) :
    FactorsByTrialDivision n := by
  obtain ⟨k, hk, rfl, -⟩ := h
  refine .inr fun p hp ↦ ?_
  have := Nat.mem_smoothNumbers'.mp hk p (Nat.prime_of_mem_primeFactorsList hp)
    (by simpa using Nat.dvd_of_mem_primeFactorsList hp)
  lia

/-- A number whose part at the primes from `q ≤ 1021` on is below `q ^ 2` has its part at the
primes from `1021` on below `1021 ^ 2`, so that ratpoints factors it completely. -/
theorem factorsByTrialDivision_of_isRoughPart_of_lt {q n w : ℕ} (h : Nat.IsRoughPart q n w)
    (hn : n ≠ 0) (hq : q ≤ 1021) (hw : w < q * q) :
    FactorsByTrialDivision n := by
  refine .inl ((Nat.le_of_dvd (Nat.pos_of_ne_zero (h.ne_zero hn)) ?_).trans_lt
    (hw.trans_le (by lia [Nat.mul_le_mul hq hq])))
  rw [h.eq_prod_filter hn]
  exact (List.monotone_filter_right _ fun p hp ↦ by simp at hp ⊢; lia).prod_dvd_prod

/-- When the part `w` of `n ≠ 0` at the primes from `1021` on is at least `1021 ^ 2`, ratpoints
factors `n` completely exactly when its part `m` at the primes from `1022` on is `1`. -/
theorem eq_one_iff_factorsByTrialDivision_of_isRoughPart {n w m : ℕ} (h : Nat.IsRoughPart 1021 n w)
    (hn : n ≠ 0) (hw : 1021 * 1021 ≤ w) (hm : Nat.IsRoughPart 1022 n m) :
    m = 1 ↔ FactorsByTrialDivision n := by
  refine ⟨fun h1 ↦ factorsByTrialDivision_of_isRoughPart_one (h1 ▸ hm) le_rfl, fun hf ↦ ?_⟩
  rcases hf with hf | hf
  · rw [← h.eq_prod_filter hn] at hf
    lia
  · by_contra h1
    obtain ⟨k, -, rfl, hk⟩ := hm
    have hp := Nat.minFac_prime h1
    have := hf _ ((Nat.mem_primeFactorsList hn).mpr ⟨hp, (Nat.minFac_dvd m).mul_left k⟩)
    lia [hk _ hp (Nat.minFac_dvd m)]

/-! ### The squarefree divisors in the order of binary counting -/

-- A sublist of the distinct prime factors of `n` is the list of the prime factors of its product.
private theorem eq_primeFactorsList_prod_of_sublist {n : ℕ} {t : List ℕ}
    (ht : t.Sublist n.primeFactorsList.dedup) : t = t.prod.primeFactorsList :=
  (Nat.primeFactorsList_unique rfl fun _ hp ↦ Nat.prime_of_mem_primeFactorsList
    (List.mem_dedup.mp (ht.subset hp))).eq_of_sortedLE
    ((Nat.primeFactorsList_sorted n).pairwise.sublist (ht.trans (List.dedup_sublist _))).sortedLE
    (Nat.primeFactorsList_sorted _)

/-- The products of the sublists of the distinct prime factors of `n ≠ 0` are its squarefree
divisors; for `n = 0` there is only the empty product `1`. -/
theorem mem_binaryDivisors_iff {n H s : ℕ} (hn : n ≠ 0) :
    s ∈ binaryDivisors n H ↔ Squarefree s ∧ s ∣ n ∧ s ≤ H := by
  simp only [binaryDivisors, List.mem_filter, List.mem_map, List.mem_sublists, decide_eq_true_eq]
  refine ⟨fun ⟨⟨t, ht, hts⟩, hsH⟩ ↦ ?_, fun ⟨hs, hsn, hsH⟩ ↦ ⟨⟨s.primeFactorsList, ?_,
    Nat.prod_primeFactorsList hs.ne_zero⟩, hsH⟩⟩
  · subst hts
    have hdvd := (ht.trans (List.dedup_sublist _)).prod_dvd_prod.trans
      (Nat.prod_primeFactorsList hn).dvd
    refine ⟨(Nat.squarefree_iff_nodup_primeFactorsList (ne_zero_of_dvd_ne_zero hn hdvd)).mpr ?_,
      hdvd, hsH⟩
    exact eq_primeFactorsList_prod_of_sublist ht ▸ (List.nodup_dedup _).sublist ht
  · refine List.sublist_of_subperm_of_sortedLE (((Nat.squarefree_iff_nodup_primeFactorsList
      hs.ne_zero).mp hs).subperm fun p hp ↦ List.mem_dedup.mpr
        (Nat.primeFactorsList_subset_of_dvd hsn hn hp)) (Nat.primeFactorsList_sorted s)
      ((Nat.primeFactorsList_sorted n).pairwise.sublist (List.dedup_sublist _)).sortedLE

/-- Distinct sublists of the distinct prime factors of `n` have distinct products. -/
theorem nodup_binaryDivisors (n H : ℕ) : (binaryDivisors n H).Nodup :=
  ((List.nodup_sublists.mpr (List.nodup_dedup _)).map_on (f := List.prod) fun _ ht _ hu h ↦
    (eq_primeFactorsList_prod_of_sublist (List.mem_sublists.mp ht)).trans
      (congr(Nat.primeFactorsList $h).trans
        (eq_primeFactorsList_prod_of_sublist (List.mem_sublists.mp hu)).symm)).filter _

namespace Setup

/-! ### The factorization of the leading coefficient -/

/-- The list `fac` of pairs `(p, v)` is the factorization of `w`: its primes `p` ascend, each with
its valuation `v = v_p(w) ≥ 1`, and every prime factor of `w` is among them. -/
def IsFactorization (w : ℕ) (fac : List (ℕ × ℕ)) : Prop :=
  (fac.map Prod.fst).Pairwise (· < ·) ∧
    (∀ x ∈ fac, x.1.Prime ∧ 0 < x.2 ∧ x.2 = padicValNat x.1 w) ∧
    ∀ q, q.Prime → q ∣ w → q ∈ fac.map Prod.fst

/-- The square `p * p` of a prime of the table, which `setup_us1` computes as an `int`
(`find_points.c:800`), is below `2 ^ 31`. -/
theorem mul_self_lt_of_mem_primeTable {p : ℕ} (hp : p ∈ primeTable) : p * p < 2 ^ 31 := by
  lia [Nat.mul_self_le_mul_self (Nat.le_of_lt_succ (lt_of_mem_primeTable hp))]

/-- A cofactor below the square of a prime of the table is a `long`, so that the test of
`Ratpoints.Setup.factorLcf` before it takes the cofactor as a prime always passes
(`find_points.c:808`). -/
theorem fitsLong_of_lt_mul_self {w p : ℕ} (hp : p ∈ primeTable) (hw : w < p * p) :
    fitsLong (w : ℤ) = true := by
  simp [fitsLong]
  lia [mul_self_lt_of_mem_primeTable hp]

/-- The part of the invariant of `Ratpoints.Setup.factorLcf` for its cofactor `w`, with the factors
`fac` found and the primes `suff` of the table still to come: while a prime `cur` is still to come,
the primes found lie below it and every prime factor of `w` is at least `cur`; at the end, `w = 1`
exactly when ratpoints factors `w0` completely. -/
def CofactorInvariant (w0 : ℕ) (fac : List (ℕ × ℕ)) : List ℕ → ℕ → Prop
  | [], w => w = 1 ↔ FactorsByTrialDivision w0
  | cur :: _, w => (∀ x ∈ fac, x.1 < cur) ∧ ∀ p, p.Prime → p ∣ w → cur ≤ p

/-- The invariant of the loop of `Ratpoints.Setup.factorLcf` over the primes of the table, for the
number `w0 ≥ 1` to factor, with the primes `suff` still to come: `w0` is the cofactor `w` times the
powers of the factors found, ascending primes `p` with their valuations `v_p(w0) ≥ 1` that do not
divide `w`, and the cofactor satisfies `Ratpoints.Setup.CofactorInvariant`: while a prime `cur` of
the table is still to come, `w` is the part of `w0` at the primes from `cur` on
(`Ratpoints.Setup.FactorLcfInvariant.isRoughPart`). -/
structure FactorLcfInvariant (w0 : ℕ) (suff : List ℕ) (w : ℕ) (fac : Array (ℕ × ℕ)) : Prop where
  /-- `w0` is the cofactor times the powers of the factors found. -/
  eq_mul_prod : w0 = w * (fac.toList.map fun x ↦ x.1 ^ x.2).prod
  /-- The primes found ascend. -/
  pairwise_lt : (fac.toList.map Prod.fst).Pairwise (· < ·)
  /-- Each factor found is a prime with its valuation in `w0`, at least `1`, that does not divide
  the cofactor. -/
  prime_valuation : ∀ x ∈ fac.toList, x.1.Prime ∧ x.2 = padicValNat x.1 w0 ∧ 0 < x.2 ∧ ¬x.1 ∣ w
  /-- The cofactor satisfies `Ratpoints.Setup.CofactorInvariant`. -/
  cofactor : CofactorInvariant w0 fac.toList suff w

theorem FactorLcfInvariant.ne_zero {w0 w : ℕ} {suff : List ℕ} {fac : Array (ℕ × ℕ)}
    (h : FactorLcfInvariant w0 suff w fac) (hw0 : 0 < w0) :
    w ≠ 0 := by
  rintro rfl
  simp [h.eq_mul_prod] at hw0

/-- While the prime `cur` of the table is still to come, the cofactor is the part of `w0` at the
primes from `cur` on: the product of the powers of the primes found, all below `cur`, is
`cur`-smooth. -/
theorem FactorLcfInvariant.isRoughPart {w0 w cur : ℕ} {suff : List ℕ} {fac : Array (ℕ × ℕ)}
    (h : FactorLcfInvariant w0 (cur :: suff) w fac) :
    Nat.IsRoughPart cur w0 w := by
  refine ⟨_, Nat.mem_smoothNumbers'.mpr fun p hp hpd ↦ ?_, h.eq_mul_prod.trans (Nat.mul_comm _ _),
    h.cofactor.2⟩
  obtain ⟨a, ha, hpa⟩ := hp.prime.dvd_prod_iff.mp hpd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  exact (Nat.le_of_dvd (h.prime_valuation x hx).1.pos (hp.dvd_of_dvd_pow hpa)).trans_lt
    (h.cofactor.1 x hx)

/-- A new prime factor `p` of the cofactor `w = p ^ v m`, `p ∤ m`, above the primes found, taken
with its exponent `v ≥ 1`, leaves the cofactor `m`. -/
theorem FactorLcfInvariant.push {w0 w m p v : ℕ} {suff suff' : List ℕ} {fac : Array (ℕ × ℕ)}
    (h : FactorLcfInvariant w0 suff w fac) (hp : p.Prime) (hv : 0 < v) (hm : w = p ^ v * m)
    (hpm : ¬p ∣ m) (hlt : ∀ x ∈ fac.toList, x.1 < p)
    (h4 : CofactorInvariant w0 (fac.push (p, v)).toList suff' m) :
    FactorLcfInvariant w0 suff' m (fac.push (p, v)) := by
  obtain ⟨h1, h2, h3, -⟩ := h
  have hP : ¬p ∣ (fac.toList.map fun x ↦ x.1 ^ x.2).prod :=
    hp.prime.not_dvd_prod_map_pow fun x hx ↦ ⟨(h3 x hx).1.prime, (hlt x hx).ne⟩
  refine ⟨by rw [h1, hm, Array.toList_push, List.map_append, List.prod_append]; simp; ring,
    Array.pairwise_map_toList_push.mpr ⟨h2, hlt⟩, Array.forall_mem_toList_push (fun x hx ↦ ?_) ?_,
    h4⟩
  · exact ⟨(h3 x hx).1, (h3 x hx).2.1, (h3 x hx).2.2.1,
      fun hd ↦ (h3 x hx).2.2.2 (hd.trans (hm ▸ dvd_mul_left m _))⟩
  · exact ⟨hp, (padicValNat_eq_of_eq_pow_mul_of_not_dvd hp.ne_zero (by rw [h1, hm]; ring)
      (hp.prime.not_dvd_mul hpm hP)).symm, hv, hpm⟩

/-- After the power `2 ^ v2 ≠ 1` of `w0`, found: the odd part of `w0`, every prime factor of which
is at least `3`, the first prime of the table. -/
theorem factorLcfInvariant_nil_push {w0 v2 r : ℕ} (hw0 : 0 < w0)
    (hv : (v2, r) = Id.run (valuation (w0 : ℤ) 2)) (h : 0 < v2) :
    FactorLcfInvariant w0 (ForIn.toList primeTable) (w0 / 2 ^ v2) (#[].push (2, v2)) := by
  obtain ⟨m, hm, hm2⟩ := exists_eq_of_eq_run_valuation hw0.ne' Nat.one_lt_two hv
  have hw : FactorLcfInvariant w0 [2] w0 #[] :=
    ⟨by simp, by simp, by simp, by simp, fun p hp _ ↦ hp.two_le⟩
  rw [Nat.div_eq_of_eq_mul_right (Nat.two_pow_pos v2) hm, forIn_toList_primeTable]
  exact hw.push Nat.prime_two h hm hm2 (by simp)
    ⟨by simp, fun p hp hpm ↦ hp.two_le.lt_of_ne fun h2 ↦ hm2 (h2 ▸ hpm)⟩

/-- For odd `w0`: the cofactor `w0`, every prime factor of which is at least `3`, the first prime of
the table, and no prime found. -/
theorem factorLcfInvariant_nil {w0 v2 r : ℕ} (hw0 : 0 < w0)
    (hv : (v2, r) = Id.run (valuation (w0 : ℤ) 2)) (h : ¬0 < v2) :
    FactorLcfInvariant w0 (ForIn.toList primeTable) w0 #[] := by
  obtain ⟨m, hm, hm2⟩ := exists_eq_of_eq_run_valuation hw0.ne' Nat.one_lt_two hv
  obtain rfl : v2 = 0 := by lia
  rw [Nat.pow_zero, Nat.one_mul] at hm
  subst hm
  rw [forIn_toList_primeTable]
  exact ⟨by simp, by simp, by simp, by simp,
    fun p hp hpm ↦ hp.two_le.lt_of_ne fun h2 ↦ hm2 (h2 ▸ hpm)⟩

/-- The cofactor `m` after the prime `cur` of the table, whose part `w ≥ cur ^ 2` of `w0` at the
primes from `cur` on it has divided by the power of `cur`, with the primes found at most `cur`:
while a prime is still to come, the primes found lie below it and `m` is the part of `w0` at the
primes from it on; after the last prime, `1021`, `m = 1` exactly when ratpoints factors `w0`
completely. -/
theorem cofactorInvariant_of_isRoughPart {w0 w m cur : ℕ} {pref suff : List ℕ} {fac : List (ℕ × ℕ)}
    (hl : ForIn.toList primeTable = pref ++ cur :: suff) (hw0 : w0 ≠ 0)
    (hw : Nat.IsRoughPart cur w0 w) (hlt : ¬w < cur * cur) (hm : Nat.IsRoughPart (cur + 1) w0 m)
    (hfac : ∀ x ∈ fac, x.1 ≤ cur) :
    CofactorInvariant w0 fac suff m := by
  rw [Std.Internal.ForIn.toList_array] at hl
  cases suff with
  | nil =>
    obtain rfl := eq_of_toList_primeTable_eq_append_singleton hl
    exact eq_one_iff_factorsByTrialDivision_of_isRoughPart hw hw0 (Nat.not_lt.mp hlt) hm
  | cons next suff =>
    have hpw := pairwise_lt_toList_primeTable
    rw [hl, List.pairwise_append, List.pairwise_cons] at hpw
    have hnext := hpw.2.1.1 next List.mem_cons_self
    obtain ⟨-, -, -, hm⟩ := hm.of_le_of_forall hnext
      fun p hp h ↦ le_of_toList_primeTable_eq_append_cons_cons hl hp h
    exact ⟨fun x hx ↦ (hfac x hx).trans_lt hnext, hm⟩

/-- The prime `cur` of the table divided off `w` with its valuation `v ≥ 1`. -/
theorem FactorLcfInvariant.push_cur {w0 w cur v r : ℕ} {pref suff : List ℕ}
    {fac : Array (ℕ × ℕ)} (hl : ForIn.toList primeTable = pref ++ cur :: suff)
    (h : FactorLcfInvariant w0 (cur :: suff) w fac) (hw0 : 0 < w0) (hlt : ¬w < cur * cur)
    (hv : (v, r) = Id.run (valuation (w : ℤ) cur)) (hpos : 0 < v) :
    FactorLcfInvariant w0 suff (w / cur ^ v) (fac.push (cur, v)) := by
  have hcur : cur.Prime := prime_of_mem_primeTable (Array.mem_of_forIn_toList_eq_append_cons hl)
  have hw := h.isRoughPart
  obtain ⟨m, hm, hpm⟩ := exists_eq_of_eq_run_valuation (h.ne_zero hw0) hcur.one_lt hv
  rw [Nat.div_eq_of_eq_mul_right (Nat.pow_pos hcur.pos) hm]
  refine h.push hcur hpos hm hpm h.cofactor.1 (cofactorInvariant_of_isRoughPart hl hw0.ne' hw
    hlt ((hm ▸ hw).succ hcur hpm) ?_)
  exact Array.forall_mem_toList_push (fun x hx ↦ (h.cofactor.1 x hx).le) le_rfl

/-- The prime `cur` of the table, which does not divide `w`, passed. -/
theorem FactorLcfInvariant.skip {w0 w cur v r : ℕ} {pref suff : List ℕ}
    {fac : Array (ℕ × ℕ)} (hl : ForIn.toList primeTable = pref ++ cur :: suff)
    (h : FactorLcfInvariant w0 (cur :: suff) w fac) (hw0 : 0 < w0) (hlt : ¬w < cur * cur)
    (hv : (v, r) = Id.run (valuation (w : ℤ) cur)) (h0 : ¬0 < v) :
    FactorLcfInvariant w0 suff w fac := by
  have hcur : cur.Prime := prime_of_mem_primeTable (Array.mem_of_forIn_toList_eq_append_cons hl)
  have hw := h.isRoughPart
  obtain ⟨m, hm, hpm⟩ := exists_eq_of_eq_run_valuation (h.ne_zero hw0) hcur.one_lt hv
  obtain rfl : v = 0 := by lia
  have hm' := (hm ▸ hw).succ hcur hpm
  rw [Nat.pow_zero, Nat.one_mul] at hm
  exact ⟨h.eq_mul_prod, h.pairwise_lt, h.prime_valuation,
    cofactorInvariant_of_isRoughPart hl hw0.ne' hw hlt (hm ▸ hm') fun x hx ↦ (h.cofactor.1 x hx).le⟩

/-- A cofactor `w ≠ 1` below `cur ^ 2`, with no prime factor below `cur`, is a prime
(`Nat.prime_of_lt_mul_self`), taken with the valuation `1`, which leaves the cofactor `1`. -/
theorem FactorLcfInvariant.push_self {w0 w cur : ℕ} {pref suff : List ℕ} {fac : Array (ℕ × ℕ)}
    (hl : ForIn.toList primeTable = pref ++ cur :: suff)
    (h : FactorLcfInvariant w0 (cur :: suff) w fac) (hw0 : 0 < w0) (h1 : ¬(w == 1) = true)
    (hlt : w < cur * cur) :
    FactorLcfInvariant w0 [] 1 (fac.push (w, 1)) := by
  have hcur := lt_of_mem_primeTable (Array.mem_of_forIn_toList_eq_append_cons hl)
  have h4 : CofactorInvariant w0 fac.toList (cur :: suff) w := h.cofactor
  have hw : w.Prime := Nat.prime_of_lt_mul_self (h.ne_zero hw0) (by simpa using h1) hlt h4.2
  exact h.push hw Nat.one_pos (by simp) hw.not_dvd_one
    (fun x hx ↦ (h4.1 x hx).trans_le (h4.2 w hw dvd_rfl))
    (iff_of_true rfl
      (factorsByTrialDivision_of_isRoughPart_of_lt h.isRoughPart hw0.ne' (by lia) hlt))

/-- The cofactor `1`: the loop ends, every prime factor of `w0` found. -/
theorem FactorLcfInvariant.of_eq_one {w0 w cur : ℕ} {pref suff : List ℕ} {fac : Array (ℕ × ℕ)}
    (hl : ForIn.toList primeTable = pref ++ cur :: suff)
    (h : FactorLcfInvariant w0 (cur :: suff) w fac) (h1 : (w == 1) = true) :
    FactorLcfInvariant w0 [] w fac := by
  have hcur := lt_of_mem_primeTable (Array.mem_of_forIn_toList_eq_append_cons hl)
  obtain rfl : w = 1 := by simpa using h1
  exact ⟨h.eq_mul_prod, h.pairwise_lt, h.prime_valuation,
    iff_of_true rfl (factorsByTrialDivision_of_isRoughPart_one h.isRoughPart (by lia))⟩

/-- A cofactor below `cur ^ 2` is a `long`, so the loop never ends with it unfactored. -/
theorem FactorLcfInvariant.of_not_fitsLong {w0 w cur : ℕ} {pref suff : List ℕ}
    {fac : Array (ℕ × ℕ)} (hl : ForIn.toList primeTable = pref ++ cur :: suff)
    (hlt : w < cur * cur) (hf : ¬fitsLong (w : ℤ) = true) :
    FactorLcfInvariant w0 [] w fac :=
  absurd (fitsLong_of_lt_mul_self (Array.mem_of_forIn_toList_eq_append_cons hl) hlt) hf

/-- At the end of the loop, the cofactor is `1` exactly when ratpoints factors `w0` completely, and
then the factors found are the factorization of `w0`. -/
theorem FactorLcfInvariant.iff_and_isFactorization {w0 w : ℕ} {fac : Array (ℕ × ℕ)}
    (h : FactorLcfInvariant w0 [] w fac) :
    (w = 1 ↔ FactorsByTrialDivision w0) ∧ (w = 1 → IsFactorization w0 fac.toList) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨h4, fun hw ↦ ⟨h2, fun x hx ↦ ⟨(h3 x hx).1, (h3 x hx).2.2.1, (h3 x hx).2.1⟩,
    fun q hq hqw ↦ by_contra fun hn ↦ ?_⟩⟩
  rw [h1, hw, Nat.one_mul] at hqw
  exact hq.prime.not_dvd_prod_map_pow
    (fun x hx ↦ ⟨(h3 x hx).1.prime, fun he ↦ hn (List.mem_map.mpr ⟨x, hx, he⟩)⟩) hqw

-- The table of primes, the test of the `long`s and the valuation are irreducible here: their
-- unfolding in a failed unification of the dispatch does not end.
attribute [local irreducible] fitsLong valuation primeTable in
/-- The factorization of `w ≥ 1` over `2` and the primes of the table leaves the cofactor `1`
exactly when ratpoints factors `w` completely, and then it is the factorization of `w`, the primes
in increasing order, each with its valuation. -/
@[spec]
theorem factorLcf_spec (w : ℕ) :
    ⦃ 0 < w ⦄ factorLcf w
    ⦃ fun r ↦ (r.2 = 1 ↔ FactorsByTrialDivision w) ∧ (r.2 = 1 → IsFactorization w r.1) ⦄ := by
  vcgen [factorLcf, valuation_value] invariants
  · fun _ suff s ↦ FactorLcfInvariant w suff s.1 s.2
  · fun _ suff s ↦ FactorLcfInvariant w suff s.1 s.2
  all_goals dsimp only at *
  all_goals first
    | exact factorLcfInvariant_nil_push ‹_› ‹_› ‹_›
    | exact factorLcfInvariant_nil ‹_› ‹_› ‹_›
    | exact ‹FactorLcfInvariant _ _ _ _›.iff_and_isFactorization
    | exact ‹FactorLcfInvariant _ _ _ _›.of_eq_one ‹_› ‹_›
    | exact ‹FactorLcfInvariant _ _ _ _›.push_self ‹_› ‹_› ‹_› ‹_›
    | exact FactorLcfInvariant.of_not_fitsLong ‹_› ‹_› ‹_›
    | exact ‹FactorLcfInvariant _ _ _ _›.push_cur ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact ‹FactorLcfInvariant _ _ _ _›.skip ‹_› ‹_› ‹_› ‹_› ‹_›

/-- `Ratpoints.Setup.factorLcf_spec` as a plain statement, for the cofactor. -/
theorem snd_run_factorLcf_eq_one_iff {w : ℕ} (hw : 0 < w) :
    (Id.run (factorLcf w)).2 = 1 ↔ FactorsByTrialDivision w :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((factorLcf_spec w).le_wp hw)).1

/-- `Ratpoints.Setup.factorLcf_spec` as a plain statement, for a factorization with the cofactor
`1`. -/
theorem isFactorization_of_run_factorLcf_eq {w : ℕ} (hw : 0 < w) {fac : List (ℕ × ℕ)}
    (h : Id.run (factorLcf w) = (fac, 1)) : IsFactorization w fac := by
  have := (Std.WP.Id.of_run_eq_wp rfl _ ((factorLcf_spec w).le_wp hw)).2
  rw [h] at this
  exact this rfl

/-! ### The squarefree divisors -/

/-- One pass of the doubling loop of `Ratpoints.Setup.squarefreeDivisors` with the prime `p`: the
divisors `ds` found so far, then `x p` for each `x` of them with `x ≤ ⌊bHigh / p⌋`, in their
order. -/
def extendDivisors (bHigh : ℕ) (ds : List ℕ) (p : ℕ) : List ℕ :=
  ds ++ (ds.filter (· ≤ bHigh / p)).map (· * p)

/-- The invariant of the loop of `Ratpoints.Setup.squarefreeDivisors` over the primes, after the
primes `pref` with the primes `suff` still to come: the list is that of the passes over `pref`
(`Ratpoints.Setup.extendDivisors`), or the loop has stopped at the end with
`Ratpoints.maxDivisors` entries or more, a prefix of that list. -/
def DivisorsInvariant (bHigh : ℕ) (pref suff : List ℕ) (divs : Array ℕ) : Prop :=
  divs.toList = pref.foldl (extendDivisors bHigh) [1] ∨
    maxDivisors ≤ divs.size ∧ suff = [] ∧ divs.toList <+: pref.foldl (extendDivisors bHigh) [1]

/-- The invariant of the pass of `Ratpoints.Setup.squarefreeDivisors` with the prime `p` over the
divisors `divs0`, after the positions `pref` with the positions `suff` still to come: the list is
`divs0` followed by the products `x p` of the entries `x ≤ ⌊bHigh / p⌋` among the first `|pref|`
ones, or the pass has stopped at the end with `Ratpoints.maxDivisors` entries or more, a prefix of
that list. -/
def ExtendDivisorsInvariant (bHigh p : ℕ) (divs0 : Array ℕ) (pref suff : List ℕ) (divs : Array ℕ) :
    Prop :=
  divs.toList = divs0.toList ++
      ((divs0.toList.take pref.length).filter (· ≤ bHigh / p)).map (· * p) ∨
    maxDivisors ≤ divs.size ∧ suff = [] ∧ divs.toList <+: divs0.toList ++
      ((divs0.toList.take pref.length).filter (· ≤ bHigh / p)).map (· * p)

theorem divisorsInvariant_nil (bHigh : ℕ) (ps : List ℕ) : DivisorsInvariant bHigh [] ps #[1] :=
  .inl rfl

theorem DivisorsInvariant.eq_of_cons {bHigh cur : ℕ} {pref suff : List ℕ} {divs : Array ℕ}
    (h : DivisorsInvariant bHigh pref (cur :: suff) divs) :
    divs.toList = pref.foldl (extendDivisors bHigh) [1] :=
  h.resolve_right (by simp)

theorem DivisorsInvariant.eq_or {bHigh : ℕ} {ps : List ℕ} {divs : Array ℕ}
    (h : DivisorsInvariant bHigh ps [] divs) :
    divs.toList = ps.foldl (extendDivisors bHigh) [1] ∨
      maxDivisors ≤ divs.toList.length ∧ divs.toList <+: ps.foldl (extendDivisors bHigh) [1] :=
  h.imp_right fun h ↦ ⟨by simpa using h.1, h.2.2⟩

theorem extendDivisorsInvariant_nil (bHigh p : ℕ) (divs0 : Array ℕ) (suff : List ℕ) :
    ExtendDivisorsInvariant bHigh p divs0 [] suff divs0 :=
  .inl (by simp)

/-- The pass over all positions of `divs0` ends with `Ratpoints.Setup.extendDivisors` of `divs0`,
or with a prefix of it with `Ratpoints.maxDivisors` entries or more. -/
theorem ExtendDivisorsInvariant.eq_or {bHigh p : ℕ} {divs0 divs : Array ℕ}
    (h : ExtendDivisorsInvariant bHigh p divs0 (ForIn.toList [:divs0.size]) [] divs) :
    divs.toList = extendDivisors bHigh divs0.toList p ∨
      maxDivisors ≤ divs.size ∧ divs.toList <+: extendDivisors bHigh divs0.toList p := by
  have hlen : (ForIn.toList [:divs0.size]).length = divs0.toList.length := by
    simp [Std.Internal.ForIn.toList_range]
  rw [ExtendDivisorsInvariant, hlen, List.take_length] at h
  exact h.imp_right fun h ↦ ⟨h.1, h.2.2⟩

-- The list of the passes before the prime `p`, which the loop extends with `p` and the primes
-- `suff`, is a prefix of the list of all passes.
private theorem prefix_foldl_extendDivisors {bHigh : ℕ} (ds : List ℕ) (ps : List ℕ) :
    ds <+: ps.foldl (extendDivisors bHigh) ds := by
  induction ps generalizing ds with
  | nil => exact List.prefix_refl ds
  | cons p ps ih => exact (List.prefix_append _ _).trans (ih _)

theorem ExtendDivisorsInvariant.divisorsInvariant_of_le {bHigh cur : ℕ} {ps pref suff : List ℕ}
    {divs0 divs : Array ℕ} (hps : ps = pref ++ cur :: suff)
    (h0 : DivisorsInvariant bHigh pref (cur :: suff) divs0)
    (h : ExtendDivisorsInvariant bHigh cur divs0 (ForIn.toList [:divs0.size]) [] divs)
    (hle : maxDivisors ≤ divs.size) :
    DivisorsInvariant bHigh ps [] divs := by
  have hd0 := h0.eq_of_cons
  refine .inr ⟨hle, rfl, ?_⟩
  have hd : divs.toList <+: (pref ++ [cur]).foldl (extendDivisors bHigh) [1] := by
    rw [List.foldl_concat, ← hd0]
    exact h.eq_or.elim (fun h ↦ h ▸ List.prefix_refl _) fun h ↦ h.2
  exact hd.trans (hps ▸ (by simpa using prefix_foldl_extendDivisors _ suff))

theorem ExtendDivisorsInvariant.divisorsInvariant {bHigh cur : ℕ} {pref suff : List ℕ}
    {divs0 divs : Array ℕ} (h0 : DivisorsInvariant bHigh pref (cur :: suff) divs0)
    (h : ExtendDivisorsInvariant bHigh cur divs0 (ForIn.toList [:divs0.size]) [] divs)
    (hlt : ¬maxDivisors ≤ divs.size) :
    DivisorsInvariant bHigh (pref ++ [cur]) suff divs := by
  refine .inl ?_
  rw [h.eq_or.resolve_right fun h ↦ hlt h.1, h0.eq_of_cons, List.foldl_concat]

theorem ExtendDivisorsInvariant.eq_of_cons {bHigh p cur : ℕ} {divs0 divs : Array ℕ}
    {pref suff : List ℕ} (h : ExtendDivisorsInvariant bHigh p divs0 pref (cur :: suff) divs) :
    divs.toList = divs0.toList ++
      ((divs0.toList.take pref.length).filter (· ≤ bHigh / p)).map (· * p) :=
  h.resolve_right (by simp)

-- The pass at the position `cur` with the entries before it done: `divs[cur]!` is the entry of
-- `divs0` there, and the next prefix of `divs0` adds it.
private theorem take_add_one_eq {bHigh p cur : ℕ} {divs0 divs : Array ℕ} {pref suff : List ℕ}
    (hl : ForIn.toList [:divs0.size] = pref ++ cur :: suff)
    (hd : divs.toList = divs0.toList ++
      ((divs0.toList.take pref.length).filter (· ≤ bHigh / p)).map (· * p)) :
    divs0.toList.take (pref.length + 1) = divs0.toList.take pref.length ++ [divs[cur]!] := by
  have hcs := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcs' : pref.length < divs0.toList.length := by rwa [Array.length_toList]
  rw [getElem!_pos divs _ (by rw [← Array.length_toList, hd]; simp; lia), ← Array.getElem_toList,
    List.take_add_one, List.getElem?_eq_getElem hcs']
  simp only [hd, List.getElem_append_left hcs', Option.toList_some]

-- The prefixes of the pass: the first `k ≤ n` positions give a prefix of the first `n`.
private theorem prefix_append_map_filter_take {bHigh p k n : ℕ} (l : List ℕ) (h : k ≤ n) :
    l ++ ((l.take k).filter (· ≤ bHigh / p)).map (· * p) <+:
      l ++ ((l.take n).filter (· ≤ bHigh / p)).map (· * p) :=
  (List.prefix_append_right_inj l).mpr (((List.take_prefix_take_left h).filter _).map _)

-- The pass at the position `cur`: `divs[cur]! p` appended when `divs[cur]! ≤ ⌊bHigh / p⌋`.
private theorem toList_eq_of_cons {bHigh p cur : ℕ} {divs0 divs : Array ℕ} {pref suff : List ℕ}
    (hl : ForIn.toList [:divs0.size] = pref ++ cur :: suff)
    (h : ExtendDivisorsInvariant bHigh p divs0 pref (cur :: suff) divs) :
    (if divs[cur]! ≤ bHigh / p then divs.push (divs[cur]! * p) else divs).toList =
      divs0.toList ++ ((divs0.toList.take (pref ++ [cur]).length).filter (· ≤ bHigh / p)).map
        (· * p) := by
  rw [List.length_append, List.length_singleton, take_add_one_eq hl h.eq_of_cons]
  split_ifs with hle <;> simp [h.eq_of_cons, hle]

theorem ExtendDivisorsInvariant.push {bHigh p cur : ℕ} {divs0 divs : Array ℕ}
    {pref suff : List ℕ} (hl : ForIn.toList [:divs0.size] = pref ++ cur :: suff)
    (h : ExtendDivisorsInvariant bHigh p divs0 pref (cur :: suff) divs)
    (hle : divs[cur]! ≤ bHigh / p) :
    ExtendDivisorsInvariant bHigh p divs0 (pref ++ [cur]) suff (divs.push (divs[cur]! * p)) :=
  .inl (by simpa [hle] using toList_eq_of_cons hl h)

theorem ExtendDivisorsInvariant.skip {bHigh p cur : ℕ} {divs0 divs : Array ℕ}
    {pref suff : List ℕ} (hl : ForIn.toList [:divs0.size] = pref ++ cur :: suff)
    (h : ExtendDivisorsInvariant bHigh p divs0 pref (cur :: suff) divs)
    (hgt : ¬divs[cur]! ≤ bHigh / p) :
    ExtendDivisorsInvariant bHigh p divs0 (pref ++ [cur]) suff divs :=
  .inl (by simpa [hgt] using toList_eq_of_cons hl h)

theorem ExtendDivisorsInvariant.push_of_le {bHigh p cur : ℕ} {divs0 divs : Array ℕ}
    {pref suff : List ℕ} (hl : ForIn.toList [:divs0.size] = pref ++ cur :: suff)
    (h : ExtendDivisorsInvariant bHigh p divs0 pref (cur :: suff) divs)
    (hle : divs[cur]! ≤ bHigh / p) (hmax : maxDivisors ≤ (divs.push (divs[cur]! * p)).size) :
    ExtendDivisorsInvariant bHigh p divs0 (ForIn.toList [:divs0.size]) []
      (divs.push (divs[cur]! * p)) :=
  .inr ⟨hmax, rfl, by
    have h' := toList_eq_of_cons hl h
    simp only [hle, ↓reduceIte] at h'
    rw [h']
    exact prefix_append_map_filter_take _ (by simp [hl])⟩

theorem ExtendDivisorsInvariant.skip_of_le {bHigh p cur : ℕ} {divs0 divs : Array ℕ}
    {pref suff : List ℕ} (hl : ForIn.toList [:divs0.size] = pref ++ cur :: suff)
    (h : ExtendDivisorsInvariant bHigh p divs0 pref (cur :: suff) divs)
    (hgt : ¬divs[cur]! ≤ bHigh / p) (hmax : maxDivisors ≤ divs.size) :
    ExtendDivisorsInvariant bHigh p divs0 (ForIn.toList [:divs0.size]) [] divs :=
  .inr ⟨hmax, rfl, by
    have h' := toList_eq_of_cons hl h
    simp only [hgt, ↓reduceIte] at h'
    rw [h']
    exact prefix_append_map_filter_take _ (by simp [hl])⟩

-- The invariants are irreducible here: the verification conditions of
-- `Ratpoints.Setup.squarefreeDivisors` are closed by their lemmas, never by unfolding them.
attribute [local irreducible] DivisorsInvariant ExtendDivisorsInvariant in
/-- The doubling loop gives the list of all passes (`Ratpoints.Setup.extendDivisors`), or, when it
stops at `Ratpoints.maxDivisors` entries, a prefix of it with that many entries or more. -/
@[spec]
theorem squarefreeDivisors_spec (ps : List ℕ) (bHigh : ℕ) :
    ⦃ True ⦄ squarefreeDivisors ps bHigh
    ⦃ fun r ↦ r = ps.foldl (extendDivisors bHigh) [1] ∨
        maxDivisors ≤ r.length ∧ r <+: ps.foldl (extendDivisors bHigh) [1] ⦄ := by
  vcgen [squarefreeDivisors] invariants
  | inv1 => fun pref suff divs ↦ DivisorsInvariant bHigh pref suff divs
  | inv2 _ p _ _ divs0 _ =>
    fun pref suff divs ↦ ExtendDivisorsInvariant bHigh p divs0 pref suff divs
  all_goals first
    | exact divisorsInvariant_nil _ _
    | exact extendDivisorsInvariant_nil _ _ _ _
    | exact ‹DivisorsInvariant _ _ _ _›.eq_or
    | exact ‹ExtendDivisorsInvariant _ _ _ _ _ _›.divisorsInvariant_of_le ‹_› ‹_› ‹_›
    | exact ‹ExtendDivisorsInvariant _ _ _ _ _ _›.divisorsInvariant ‹_› ‹_›
    | exact ‹ExtendDivisorsInvariant _ _ _ _ _ _›.push_of_le ‹_› ‹_› ‹_›
    | exact ‹ExtendDivisorsInvariant _ _ _ _ _ _›.push ‹_› ‹_›
    | exact ‹ExtendDivisorsInvariant _ _ _ _ _ _›.skip_of_le ‹_› ‹_› ‹_›
    | exact ‹ExtendDivisorsInvariant _ _ _ _ _ _›.skip ‹_› ‹_›

/-- `Ratpoints.Setup.squarefreeDivisors_spec` as a plain statement. -/
theorem run_squarefreeDivisors_eq_or (ps : List ℕ) (bHigh : ℕ) :
    Id.run (squarefreeDivisors ps bHigh) = ps.foldl (extendDivisors bHigh) [1] ∨
      maxDivisors ≤ (Id.run (squarefreeDivisors ps bHigh)).length ∧
        Id.run (squarefreeDivisors ps bHigh) <+: ps.foldl (extendDivisors bHigh) [1] :=
  Std.WP.Id.of_run_eq_wp rfl _ ((squarefreeDivisors_spec ps bHigh).le_wp trivial)

/-! ### The divisors in the order of binary counting -/

-- One pass of the doubling loop with `p > 0` over the divisors at most `bHigh` of a list `L`:
-- the products `x p ≤ bHigh`, in the order of `L`.
private theorem map_filter_filter_le_div {bHigh p : ℕ} (hp : 0 < p) (L : List ℕ) :
    (((L.filter (· ≤ bHigh)).filter (· ≤ bHigh / p)).map (· * p)) =
      (L.map (· * p)).filter (· ≤ bHigh) := by
  rw [List.filter_filter, List.filter_map]
  congr 1
  refine List.filter_congr fun x _ ↦ ?_
  simp only [Function.comp_apply, Nat.le_div_iff_mul_le hp]
  grind [Nat.le_mul_of_pos_right x hp]

/-- The doubling loop over positive numbers `ps` lists the products of the sublists of `ps` that
are at most `bHigh ≥ 1`, in the order of `List.sublists`: binary counting, the first entry of `ps`
the lowest bit. -/
theorem foldl_extendDivisors_eq_filter {bHigh : ℕ} (hb : 1 ≤ bHigh) {ps : List ℕ}
    (hps : ∀ p ∈ ps, 0 < p) :
    ps.foldl (extendDivisors bHigh) [1] = (ps.sublists.map List.prod).filter (· ≤ bHigh) := by
  induction ps using List.reverseRecOn with
  | nil => simp [hb]
  | append_singleton ps p ih =>
    rw [List.foldl_concat, ih fun q hq ↦ hps q (List.mem_append_left _ hq), extendDivisors,
      List.sublists_concat, List.map_append, List.filter_append, List.map_map,
      map_filter_filter_le_div (hps p (by simp))]
    congr 2
    rw [List.map_map]
    exact List.map_congr_left fun l _ ↦ by simp

/-- The distinct primes of a factorization of `n ≠ 0`, in increasing order, are those of
`Nat.primeFactorsList n`. -/
theorem IsFactorization.map_fst_eq_dedup {n : ℕ} {fac : List (ℕ × ℕ)} (h : IsFactorization n fac)
    (hn : n ≠ 0) :
    fac.map Prod.fst = n.primeFactorsList.dedup := by
  refine h.1.eq_of_mem_iff (((Nat.primeFactorsList_sorted n).pairwise.sublist
    (List.dedup_sublist _)).and (List.nodup_dedup _) |>.imp fun h ↦ lt_of_le_of_ne h.1 h.2)
    fun p ↦ ?_
  rw [List.mem_dedup, Nat.mem_primeFactorsList hn]
  refine ⟨fun hp ↦ ?_, fun ⟨hp, hpn⟩ ↦ h.2.2 p hp hpn⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp
  have : Fact x.1.Prime := ⟨(h.2.1 x hx).1⟩
  exact ⟨(h.2.1 x hx).1, dvd_of_one_le_padicValNat ((h.2.1 x hx).2.2 ▸ (h.2.1 x hx).2.1)⟩

/-! ### The slopes -/

/-- The invariant of the loop of `Ratpoints.Setup.slope` after the positions `pref`: the slope `n`
so far is at least `1`, and for the coefficient `c_k`, `k = d - 1 - j`, of each position `j` done,
`(d - k) n ≥ 1 + val - v_p(c_k)`, with the valuation of `Ratpoints.Setup.valuation`. -/
def SlopeInvariant (c : List ℤ) (d p val : ℕ) (pref : List ℕ) (n : ℤ) : Prop :=
  1 ≤ n ∧ ∀ j ∈ pref, 1 + (val : ℤ) - (Id.run (valuation (c.getD (d - 1 - j) 0) p)).1 ≤
    ((d - (d - 1 - j) : ℕ) : ℤ) * n

theorem slopeInvariant_nil (c : List ℤ) (d p val : ℕ) : SlopeInvariant c d p val [] 1 :=
  ⟨Int.le_refl 1, nofun⟩

theorem SlopeInvariant.append_of_lt {c : List ℤ} {d p val cur vk r : ℕ} {pref suff : List ℕ}
    {n t : ℤ} (hl : ForIn.toList [:d] = pref ++ cur :: suff) (h : SlopeInvariant c d p val pref n)
    (hv : (vk, r) = Id.run (valuation (c.getD (d - 1 - cur) 0) p)) (ht : 1 + (val : ℤ) - vk = t)
    (hlt : n < if t ≤ 0 then -((-t) / ((d - (d - 1 - cur) : ℕ) : ℤ))
      else 1 + (t - 1) / ((d - (d - 1 - cur) : ℕ) : ℤ)) :
    SlopeInvariant c d p val (pref ++ [cur]) (if t ≤ 0 then -((-t) / ((d - (d - 1 - cur) : ℕ) : ℤ))
      else 1 + (t - 1) / ((d - (d - 1 - cur) : ℕ) : ℤ)) := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hm := Int.le_mul_ite_neg_ediv t (q := ((d - (d - 1 - cur) : ℕ) : ℤ)) (by lia)
  refine ⟨by lia [h.1], fun j hj ↦ ?_⟩
  rcases List.mem_append.mp hj with hj | hj
  · exact (h.2 j hj).trans (Int.mul_le_mul_of_nonneg_left hlt.le (by lia))
  · obtain rfl := List.mem_singleton.mp hj
    rwa [← hv, ht]

theorem SlopeInvariant.append_of_not_lt {c : List ℤ} {d p val cur vk r : ℕ}
    {pref suff : List ℕ} {n t : ℤ} (hl : ForIn.toList [:d] = pref ++ cur :: suff)
    (h : SlopeInvariant c d p val pref n)
    (hv : (vk, r) = Id.run (valuation (c.getD (d - 1 - cur) 0) p)) (ht : 1 + (val : ℤ) - vk = t)
    (hlt : ¬n < if t ≤ 0 then -((-t) / ((d - (d - 1 - cur) : ℕ) : ℤ))
      else 1 + (t - 1) / ((d - (d - 1 - cur) : ℕ) : ℤ)) :
    SlopeInvariant c d p val (pref ++ [cur]) n := by
  have hcur := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hm := Int.le_mul_ite_neg_ediv t (q := ((d - (d - 1 - cur) : ℕ) : ℤ)) (by lia)
  refine ⟨h.1, fun j hj ↦ ?_⟩
  rcases List.mem_append.mp hj with hj | hj
  · exact h.2 j hj
  · obtain rfl := List.mem_singleton.mp hj
    rw [← hv, ht]
    exact hm.trans (Int.mul_le_mul_of_nonneg_left (by lia) (by lia))

theorem SlopeInvariant.one_le_toNat_and_le_mul {c : List ℤ} {d p val : ℕ} {n : ℤ}
    (h : SlopeInvariant c d p val (ForIn.toList [:d]) n) :
    1 ≤ n.toNat ∧ ∀ k < d, 1 + (val : ℤ) - (Id.run (valuation (c.getD k 0) p)).1 ≤
      ((d - k : ℕ) : ℤ) * n.toNat := by
  refine ⟨by lia [h.1], fun k hk ↦ ?_⟩
  have := h.2 (d - 1 - k) (by simp; lia)
  rw [Nat.sub_sub_self (by lia : k ≤ d - 1)] at this
  rwa [Int.toNat_of_nonneg (by lia [h.1])]

section

/- The invariant is irreducible here, and so is the valuation. -/
attribute [local irreducible] SlopeInvariant valuation

/-- The slope of the valuation test of the divisor shape is at least `1` and satisfies
`(d - k) n ≥ 1 + val - v_p(c_k)` for every `k < d`, the valuation by `Ratpoints.Setup.valuation`
(`Ratpoints.veryBig` for `c_k = 0`), since the macro `CEIL` rounds up. -/
@[spec]
theorem slope_spec (c : List ℤ) (d p val : ℕ) :
    ⦃ True ⦄ slope c d p val
    ⦃ fun n : ℕ ↦ 1 ≤ n ∧ ∀ k < d, 1 + (val : ℤ) - (Id.run (valuation (c.getD k 0) p)).1 ≤
        ((d - k : ℕ) : ℤ) * n ⦄ := by
  vcgen [slope, valuation_value] invariants
  · fun pref _ n ↦ SlopeInvariant c d p val pref n
  all_goals first
    | exact slopeInvariant_nil _ _ _ _
    | exact ‹SlopeInvariant _ _ _ _ _ _›.append_of_lt ‹_› ‹_› rfl ‹_›
    | exact ‹SlopeInvariant _ _ _ _ _ _›.append_of_not_lt ‹_› ‹_› rfl ‹_›
    | exact ‹SlopeInvariant _ _ _ _ _ _›.one_le_toNat_and_le_mul

end

/-! ### The divisor set-up -/

-- The factorization, the divisors and the slopes, as values for the contract of the set-up.
private theorem factorLcf_value (w : ℕ) :
    ⦃ True ⦄ factorLcf w ⦃ fun r ↦ r = Id.run (factorLcf w) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem squarefreeDivisors_value (ps : List ℕ) (bHigh : ℕ) :
    ⦃ True ⦄ squarefreeDivisors ps bHigh ⦃ fun r ↦ r = Id.run (squarefreeDivisors ps bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem slope_value (c : List ℤ) (d p val : ℕ) :
    ⦃ True ⦄ slope c d p val ⦃ fun r ↦ r = Id.run (slope c d p val) ⦄ :=
  ⟨fun _ ↦ rfl⟩

/-- The divisor set-up succeeds exactly when the factorization of `|c_d|` leaves the cofactor `1`
(`Ratpoints.Setup.factorLcf`) and the doubling loop over its primes
(`Ratpoints.Setup.squarefreeDivisors`) gives fewer than `Ratpoints.maxDivisors` entries; it then
gives the primes with their valuations and slopes (`Ratpoints.Setup.slope`) and that list. -/
@[spec]
theorem setupUs1_spec (c : List ℤ) (d bHigh : ℕ) :
    ⦃ True ⦄ setupUs1 c d bHigh
    ⦃ fun r ↦ ∀ fac w divs, Id.run (factorLcf (c.getD d 0).natAbs) = (fac, w) →
        Id.run (squarefreeDivisors (fac.map Prod.fst) bHigh) = divs →
        r = if w = 1 ∧ divs.length < maxDivisors then
          some (fac.map fun x ↦ ⟨x.1, x.2, Id.run (slope c d x.1 x.2)⟩, divs) else none ⦄ := by
  vcgen [setupUs1, factorLcf_value, squarefreeDivisors_value, slope_value] invariants
  · fun pref _ info ↦ info.toList = pref.map fun x ↦ ⟨x.1, x.2, Id.run (slope c d x.1 x.2)⟩
  all_goals grind

/-- `Ratpoints.Setup.setupUs1_spec` as a plain statement, which the proofs use without the program
logic. -/
theorem run_setupUs1_eq {c : List ℤ} {d bHigh : ℕ} {fac : List (ℕ × ℕ)} {w : ℕ} {divs : List ℕ}
    (hf : Id.run (factorLcf (c.getD d 0).natAbs) = (fac, w))
    (hd : Id.run (squarefreeDivisors (fac.map Prod.fst) bHigh) = divs) :
    Id.run (setupUs1 c d bHigh) = if w = 1 ∧ divs.length < maxDivisors then
      some (fac.map fun x ↦ ⟨x.1, x.2, Id.run (slope c d x.1 x.2)⟩, divs) else none :=
  Std.WP.Id.of_run_eq_wp rfl _ ((setupUs1_spec c d bHigh).le_wp trivial) fac w divs hf hd

/-- The divisor set-up, when it succeeds for `c_d ≠ 0`, is made of the factorization of `|c_d|`
(`Ratpoints.Setup.factorLcf`, with the cofactor `1`) and its primes with their valuations and
slopes (`Ratpoints.Setup.slope`). -/
theorem exists_isFactorization_of_setupUs1_eq_some {c : List ℤ} {d bHigh : ℕ}
    {info : List DenInfo} {divisors : List ℕ}
    (h : Id.run (setupUs1 c d bHigh) = some (info, divisors)) (hc : c.getD d 0 ≠ 0) :
    ∃ fac : List (ℕ × ℕ), IsFactorization (c.getD d 0).natAbs fac ∧
      info = fac.map fun x ↦ ⟨x.1, x.2, Id.run (slope c d x.1 x.2)⟩ := by
  rcases hf : Id.run (factorLcf (c.getD d 0).natAbs) with ⟨fac, w⟩
  rw [run_setupUs1_eq hf rfl] at h
  split_ifs at h with hw
  obtain ⟨rfl, -⟩ := Prod.mk.inj (Option.some.inj h)
  exact ⟨fac, isFactorization_of_run_factorLcf_eq (Int.natAbs_pos.mpr hc) (hw.1 ▸ hf), rfl⟩

/-- For a factorization of `n ≥ 1` with the cofactor `1`, the doubling loop over its primes lists
the squarefree divisors of `n` up to `bHigh ≥ 1` in the order of `Ratpoints.binaryDivisors`. -/
theorem foldl_extendDivisors_eq_binaryDivisors {n bHigh : ℕ} {fac : List (ℕ × ℕ)} (hn : 0 < n)
    (h : Id.run (factorLcf n) = (fac, 1)) (hb : 1 ≤ bHigh) :
    (fac.map Prod.fst).foldl (extendDivisors bHigh) [1] = binaryDivisors n bHigh := by
  rw [(isFactorization_of_run_factorLcf_eq hn h).map_fst_eq_dedup hn.ne',
    foldl_extendDivisors_eq_filter hb fun p hp ↦
      (Nat.prime_of_mem_primeFactorsList (List.mem_dedup.mp hp)).pos]
  rfl

/-- The divisor set-up of `c_d ≠ 0` succeeds exactly when ratpoints factors `|c_d|` completely
and `|c_d|` has fewer than `Ratpoints.maxDivisors` squarefree divisors up to `bHigh ≥ 1`; its
divisors are then those of `Ratpoints.binaryDivisors`, in that order. -/
theorem map_snd_run_setupUs1 {c : List ℤ} {d bHigh : ℕ} (hc : c.getD d 0 ≠ 0) (hb : 1 ≤ bHigh) :
    (Id.run (setupUs1 c d bHigh)).map Prod.snd =
      if FactorsByTrialDivision (c.getD d 0).natAbs ∧
          (binaryDivisors (c.getD d 0).natAbs bHigh).length < maxDivisors then
        some (binaryDivisors (c.getD d 0).natAbs bHigh)
      else none := by
  have hn : 0 < (c.getD d 0).natAbs := Int.natAbs_pos.mpr hc
  have hcof := snd_run_factorLcf_eq_one_iff hn
  rcases hf : Id.run (factorLcf (c.getD d 0).natAbs) with ⟨fac, w⟩
  rw [hf] at hcof
  rw [run_setupUs1_eq hf rfl]
  by_cases hw : w = 1
  · subst hw
    have hfd := foldl_extendDivisors_eq_binaryDivisors hn hf hb
    rcases run_squarefreeDivisors_eq_or (fac.map Prod.fst) bHigh with h' | h'
    · rw [h', hfd]
      simp only [hcof.mp rfl, true_and]
      split_ifs <;> rfl
    · rw [hfd] at h'
      rw [ite_eq_right fun h ↦ by lia [h.2], ite_eq_right fun h ↦ by lia [h.2, h'.2.length_le]]
      rfl
  · rw [ite_eq_right fun h ↦ hw h.1, ite_eq_right fun h ↦ hw (hcof.mpr h.1)]
    rfl

/-- When the divisor set-up of `c_d ≠ 0` succeeds, its divisors are those of
`Ratpoints.binaryDivisors` up to `bHigh ≥ 1`. -/
theorem eq_binaryDivisors_of_setupUs1_eq_some {c : List ℤ} {d bHigh : ℕ} {info : List DenInfo}
    {divisors : List ℕ} (h : Id.run (setupUs1 c d bHigh) = some (info, divisors))
    (hc : c.getD d 0 ≠ 0) (hb : 1 ≤ bHigh) :
    divisors = binaryDivisors (c.getD d 0).natAbs bHigh := by
  have := map_snd_run_setupUs1 hc hb
  rw [h, Option.map_some] at this
  split_ifs at this
  exact Option.some.inj this

/-- When the divisor set-up succeeds, its divisors are exactly the squarefree divisors of `|c_d|` up
to the largest denominator `bHigh ≥ 1`. -/
theorem mem_iff_of_setupUs1_eq_some {c : List ℤ} {d bHigh : ℕ} {info : List DenInfo}
    {divisors : List ℕ} (h : Id.run (setupUs1 c d bHigh) = some (info, divisors))
    (hc : c.getD d 0 ≠ 0) (hbHigh : 1 ≤ bHigh) {s : ℕ} :
    s ∈ divisors ↔ Squarefree s ∧ s ∣ (c.getD d 0).natAbs ∧ s ≤ bHigh :=
  eq_binaryDivisors_of_setupUs1_eq_some h hc hbHigh ▸ mem_binaryDivisors_iff
    (Int.natAbs_ne_zero.mpr hc)

theorem nodup_of_setupUs1_eq_some {c : List ℤ} {d bHigh : ℕ} {info : List DenInfo}
    {divisors : List ℕ} (h : Id.run (setupUs1 c d bHigh) = some (info, divisors))
    (hc : c.getD d 0 ≠ 0) (hb : 1 ≤ bHigh) : divisors.Nodup :=
  eq_binaryDivisors_of_setupUs1_eq_some h hc hb ▸ nodup_binaryDivisors _ _

/-- The products `x p` that the doubling loop of the C code computes, only for `x ≤ ⌊bHigh / p⌋`
(`find_points.c:876`), are at most `bHigh`, and so `long`s for a `long` `bHigh`. -/
theorem fitsLong_mul_of_le_div {x p bHigh : ℕ} (h : x ≤ bHigh / p) (hH : bHigh < 2 ^ 63) :
    fitsLong ((x * p : ℕ) : ℤ) = true := by
  simp [fitsLong]
  lia [(Nat.mul_le_mul_right p h).trans (Nat.div_mul_le_self bHigh p)]

/-- Whether the entry `e` of the valuation test of the divisor shape (`Ratpoints.Sieve.denInfoTest`)
excludes the denominator `b`: `v_p(b) ≥ e.slope` with `v_p(b) + e.val` odd, for the valuation
`v_p(b)` of `Ratpoints.Setup.valuation`. -/
def DenInfo.excludes (e : DenInfo) (b : ℕ) : Bool :=
  decide (e.slope ≤ (Id.run (valuation b e.p)).1) && ((Id.run (valuation b e.p)).1 + e.val) % 2 == 1

theorem DenInfo.excludes_eq_false_iff {e : DenInfo} {b : ℕ} :
    e.excludes b = false ↔ ¬(decide (e.slope ≤ (Id.run (valuation b e.p)).1) &&
      ((Id.run (valuation b e.p)).1 + e.val) % 2 == 1) = true :=
  Bool.eq_false_iff

/-- An entry of the valuation test, a prime `p` with the valuation `val = v_p(c_d)` and its slope
(`Ratpoints.Setup.slope_spec`), does not exclude the denominator `b ≥ 1` of a point: for
`v_p(b) ≥ slope`, `v_p(b) + val` is even (`Ratpoints.even_add_of_sq_eq_binaryForm_of_odd`). -/
theorem DenInfo.excludes_eq_false_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 1) {p val : ℕ}
    (hp : p.Prime) (hval : val = padicValNat p (c.getD (degree c) 0).natAbs) {a y : ℤ} {b : ℕ}
    (hb : b ≠ 0) (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    (⟨p, val, Id.run (Setup.slope c (degree c) p val)⟩ : DenInfo).excludes b = false := by
  have : Fact p.Prime := ⟨hp⟩
  have hsl := Std.WP.Id.of_run_eq_wp rfl _ ((slope_spec c (degree c) p val).le_wp trivial)
  have hv : (Id.run (valuation b p)).1 = padicValNat p b := by
    rw [fst_run_valuation (Int.natCast_ne_zero.mpr hb) hp.one_lt, Int.natAbs_natCast]
  simp only [DenInfo.excludes_eq_false_iff, hv, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine fun ⟨hle, hodd⟩ ↦ Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr (by lia))
    (even_add_of_sq_eq_binaryForm_of_odd hd hval.symm (fun k hk hck ↦ ?_) hab (by lia) hy)
  have := hsl.2 k hk
  rw [fst_run_valuation hck hp.one_lt] at this
  lia [Nat.mul_le_mul_left (degree c - k) hle]

end Setup

end Ratpoints

end
