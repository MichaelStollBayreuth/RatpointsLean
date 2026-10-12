/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Nat.PrimeFin
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Ratpoints.Model.Setup
public import Ratpoints.Spec.Basic
public import Std.WP

import Mathlib.Data.Nat.Squarefree
import Ratpoints.Mathlib.Data.Int.GCD
import Ratpoints.Mathlib.Data.Nat.Prime.Defs
import Ratpoints.Mathlib.NumberTheory.Padics.PadicVal.Basic
import Ratpoints.Proof.Bits
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
prime of the table, an `int`, below `2 ^ 31`.

## Main definitions

* `Ratpoints.Setup.IsFactorization`: a list of distinct primes with their valuations that holds
  every prime factor of a number.
* `Ratpoints.Setup.extendDivisors`: one pass of the doubling loop of the squarefree divisors.
* `Ratpoints.Setup.DenInfo.excludes`: whether an entry of the valuation test of the divisor shape
  excludes a denominator.

## Main statements

* `Ratpoints.isSquare_of_sq_eq_binaryForm_of_odd`: for odd degree and `|c_d| = 1`, the denominator
  of every point is a square.
* `Ratpoints.exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd`: for odd degree, the denominator of every
  point is `s k ^ 2` with `s` squarefree and `s ∣ c_d`.
* `Ratpoints.even_add_of_sq_eq_binaryForm_of_odd`: the valuation test of the slopes.
* `Ratpoints.Setup.factorLcf_spec`, `Ratpoints.Setup.squarefreeDivisors_spec`,
  `Ratpoints.Setup.slope_spec`, `Ratpoints.Setup.setupUs1_spec`: the contracts of the divisor
  set-up.
* `Ratpoints.Setup.mem_foldl_extendDivisors_one_iff`,
  `Ratpoints.Setup.nodup_foldl_extendDivisors`: the doubling loop over distinct primes lists the
  squarefree products of the primes up to the bound, each once.
* `Ratpoints.Setup.mem_iff_of_setupUs1_eq_some`, `Ratpoints.Setup.nodup_of_setupUs1_eq_some`: the
  divisors of the divisor set-up are the squarefree divisors of `|c_d|` up to the largest
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
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

-- The macro `CEIL` of the C code rounds up: `q ⌈t / q⌉ ≥ t` for `q > 0`, with `⌈t / q⌉` as
-- `-⌊-t / q⌋` for `t ≤ 0` and `1 + ⌊(t - 1) / q⌋` for `t > 0`.
private theorem Int.le_mul_ite_neg_ediv (t : ℤ) {q : ℤ} (hq : 0 < q) :
    t ≤ q * if t ≤ 0 then -((-t) / q) else 1 + (t - 1) / q := by
  have h1 := Int.emod_add_mul_ediv (-t) q
  have h2 := Int.emod_add_mul_ediv (t - 1) q
  have h3 := Int.emod_lt_of_pos (t - 1) hq
  have h4 := Int.emod_nonneg (-t) (by lia : q ≠ 0)
  split <;> lia

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
    fun i hi hne ↦ h i (by have := Finset.mem_range.mp hi; lia)).1

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
    have := hmin h0
    have : m * (degree c + 1 - k) = (degree c - k) * m + m := by
      rw [show degree c + 1 - k = degree c - k + 1 by lia]
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

/-- For odd degree and a leading coefficient `±1`, the denominator of every point is a square: for
`b = p ^ m b'` with `p ∤ b'`, the term `c_d a ^ d b` of `F(a, b)` alone has the least valuation
`m`, which is then even (`Ratpoints.even_of_sq_eq_binaryForm_of_odd`). -/
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

namespace Setup

/-! ### The factorization of the leading coefficient -/

/-- A prime that is none of the primes of the list `l` of primes with exponents does not divide the
product of the powers. -/
theorem not_dvd_prod_pow {p : ℕ} (hp : p.Prime) {l : List (ℕ × ℕ)}
    (hl : ∀ x ∈ l, x.1.Prime ∧ x.1 ≠ p) : ¬p ∣ (l.map fun x ↦ x.1 ^ x.2).prod := by
  rw [(Nat.prime_iff.mp hp).dvd_prod_iff]
  intro ⟨a, ha, hpa⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  exact (hl x hx).2 ((Nat.prime_dvd_prime_iff_eq hp (hl x hx).1).mp (hp.dvd_of_dvd_pow hpa)).symm

/-- The list `fac` of pairs `(p, v)` is the factorization of `w`: its primes `p` are distinct, each
with its valuation `v = v_p(w) ≥ 1`, and every prime factor of `w` is among them. -/
def IsFactorization (w : ℕ) (fac : List (ℕ × ℕ)) : Prop :=
  (fac.map Prod.fst).Nodup ∧ (∀ x ∈ fac, x.1.Prime ∧ 0 < x.2 ∧ x.2 = padicValNat x.1 w) ∧
    ∀ q, q.Prime → q ∣ w → q ∈ fac.map Prod.fst

/-- The invariant of the loop of `Ratpoints.Setup.factorLcf` over the primes of the table, for the
number `w0 ≥ 1` to factor, after the primes `pref` with the primes `suff` still to come: `w0` is the
cofactor `w` times the powers of the factors found, distinct primes `p` with their valuations
`v_p(w0) ≥ 1` that do not divide `w`; while primes are left, `w` has no prime factor `2` and none
among the primes done. -/
def FactorLcfInvariant (w0 : ℕ) (pref suff : List ℕ) (w : ℕ) (fac : Array (ℕ × ℕ)) : Prop :=
  w0 = w * (fac.toList.map fun x ↦ x.1 ^ x.2).prod ∧ (fac.toList.map Prod.fst).Nodup ∧
    (∀ x ∈ fac.toList, x.1.Prime ∧ x.2 = padicValNat x.1 w0 ∧ 0 < x.2 ∧ ¬x.1 ∣ w) ∧
    (suff ≠ [] → ∀ q, q.Prime → q ∣ w → q ≠ 2 ∧ q ∉ pref)

theorem FactorLcfInvariant.ne_zero {w0 w : ℕ} {pref suff : List ℕ} {fac : Array (ℕ × ℕ)}
    (h : FactorLcfInvariant w0 pref suff w fac) (hw0 : 0 < w0) : w ≠ 0 := by
  rintro rfl
  simp [h.1] at hw0

/-- A new prime factor `p` of the cofactor `w = p ^ v m`, `p ∤ m`, taken with its exponent `v ≥ 1`,
leaves the cofactor `m`. -/
theorem FactorLcfInvariant.push {w0 w m p v : ℕ} {pref suff pref' suff' : List ℕ}
    {fac : Array (ℕ × ℕ)} (h : FactorLcfInvariant w0 pref suff w fac) (hw0 : 0 < w0)
    (hp : p.Prime) (hv : 0 < v) (hm : w = p ^ v * m) (hpm : ¬p ∣ m)
    (h4 : suff' ≠ [] → ∀ q, q.Prime → q ∣ m → q ≠ 2 ∧ q ∉ pref') :
    FactorLcfInvariant w0 pref' suff' m (fac.push (p, v)) := by
  obtain ⟨h1, h2, h3, -⟩ := h
  have hpw : p ∣ w := hm ▸ Dvd.dvd.mul_right (dvd_pow_self p hv.ne') m
  have hP := not_dvd_prod_pow hp (l := fac.toList) fun x hx ↦
    ⟨(h3 x hx).1, fun he ↦ (h3 x hx).2.2.2 (he ▸ hpw)⟩
  have : Fact p.Prime := ⟨hp⟩
  have hm0 : m ≠ 0 := by rintro rfl; exact hpm (dvd_zero p)
  refine ⟨by rw [h1, hm, Array.toList_push, List.map_append, List.prod_append]; simp; ring,
    ?_, fun x hx ↦ ?_, h4⟩
  · simpa using List.nodup_append.mpr ⟨h2, List.nodup_singleton _, by grind⟩
  rw [Array.toList_push, List.mem_append, List.mem_singleton] at hx
  rcases hx with hx | rfl
  · exact ⟨(h3 x hx).1, (h3 x hx).2.1, (h3 x hx).2.2.1,
      fun hd ↦ (h3 x hx).2.2.2 (hd.trans (hm ▸ dvd_mul_left m _))⟩
  · have hw0' : w * (fac.toList.map fun x ↦ x.1 ^ x.2).prod ≠ 0 := h1 ▸ hw0.ne'
    refine ⟨hp, ?_, hv, hpm⟩
    rw [h1, padicValNat.mul (left_ne_zero_of_mul hw0') (right_ne_zero_of_mul hw0'), hm,
      padicValNat.mul (pow_ne_zero _ hp.ne_zero) hm0, padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hpm, padicValNat.eq_zero_of_not_dvd hP]
    rfl

theorem factorLcfInvariant_nil_push {w0 v2 r : ℕ} (hw0 : 0 < w0)
    (hv : (v2, r) = Id.run (valuation (w0 : ℤ) 2)) (h : 0 < v2) :
    FactorLcfInvariant w0 [] (ForIn.toList primeTable) (w0 / 2 ^ v2) (#[].push (2, v2)) := by
  obtain ⟨m, hm, hm2⟩ := exists_eq_of_eq_run_valuation hw0.ne' Nat.one_lt_two hv
  have hw : FactorLcfInvariant w0 [] [] w0 #[] := ⟨by simp, by simp, by simp, nofun⟩
  rw [Nat.div_eq_of_eq_mul_right (Nat.two_pow_pos v2) hm]
  exact hw.push hw0 Nat.prime_two h hm hm2 fun _ q _ hq ↦ ⟨fun h2 ↦ hm2 (h2 ▸ hq), by simp⟩

theorem factorLcfInvariant_nil {w0 v2 r : ℕ} (hw0 : 0 < w0)
    (hv : (v2, r) = Id.run (valuation (w0 : ℤ) 2)) (h : ¬0 < v2) :
    FactorLcfInvariant w0 [] (ForIn.toList primeTable) w0 #[] := by
  obtain ⟨m, hm, hm2⟩ := exists_eq_of_eq_run_valuation hw0.ne' Nat.one_lt_two hv
  obtain rfl : v2 = 0 := by lia
  rw [Nat.pow_zero, Nat.one_mul] at hm
  exact ⟨by simp, by simp, by simp, fun _ q _ hq ↦ ⟨fun h2 ↦ hm2 (hm ▸ h2 ▸ hq), by simp⟩⟩

theorem FactorLcfInvariant.done {w0 w : ℕ} {pref suff : List ℕ} {fac : Array (ℕ × ℕ)}
    (h : FactorLcfInvariant w0 pref suff w fac) (xs : List ℕ) :
    FactorLcfInvariant w0 xs [] w fac :=
  ⟨h.1, h.2.1, h.2.2.1, fun h ↦ absurd rfl h⟩

/-- A cofactor `w ≠ 1` below `p ^ 2` for the entry `p` of the table, with no prime factor among the
earlier ones and `2`, is a prime (`Ratpoints.mem_of_toList_primeTable_eq`), taken with the valuation
`1`. -/
theorem FactorLcfInvariant.push_self {w0 w cur : ℕ} {pref suff : List ℕ} {fac : Array (ℕ × ℕ)}
    (hl : ForIn.toList primeTable = pref ++ cur :: suff)
    (h : FactorLcfInvariant w0 pref (cur :: suff) w fac) (hw0 : 0 < w0) (h1 : ¬(w == 1) = true)
    (hlt : w < cur * cur) :
    FactorLcfInvariant w0 (ForIn.toList primeTable) [] 1 (fac.push (w, 1)) := by
  rw [Std.Internal.ForIn.toList_array] at hl
  have hw : w.Prime := Nat.prime_of_lt_mul_self (h.ne_zero hw0) (by simpa using h1) hlt
    fun q hq hqw ↦ Nat.le_of_not_lt fun hlt ↦ (h.2.2.2 (List.cons_ne_nil _ _) q hq hqw).2
      (mem_of_toList_primeTable_eq hl hq (h.2.2.2 (List.cons_ne_nil _ _) q hq hqw).1 hlt)
  exact h.push hw0 hw Nat.one_pos (by simp) hw.not_dvd_one nofun

theorem FactorLcfInvariant.push_cur {w0 w cur v r : ℕ} {pref suff : List ℕ}
    {fac : Array (ℕ × ℕ)} (hl : ForIn.toList primeTable = pref ++ cur :: suff)
    (h : FactorLcfInvariant w0 pref (cur :: suff) w fac) (hw0 : 0 < w0)
    (hv : (v, r) = Id.run (valuation (w : ℤ) cur)) (hpos : 0 < v) :
    FactorLcfInvariant w0 (pref ++ [cur]) suff (w / cur ^ v) (fac.push (cur, v)) := by
  have hcur : cur.Prime := prime_of_mem_primeTable (Array.mem_of_forIn_toList_eq_append_cons hl)
  obtain ⟨m, hm, hpm⟩ := exists_eq_of_eq_run_valuation (h.ne_zero hw0) hcur.one_lt hv
  rw [Nat.div_eq_of_eq_mul_right (Nat.pow_pos hcur.pos) hm]
  refine h.push hw0 hcur hpos hm hpm fun _ q hq hqm ↦ ?_
  have := h.2.2.2 (List.cons_ne_nil _ _) q hq (hm ▸ Dvd.dvd.mul_left hqm _)
  exact ⟨this.1, fun hmem ↦ (List.mem_append.mp hmem).elim this.2 fun he ↦
    hpm (List.mem_singleton.mp he ▸ hqm)⟩

theorem FactorLcfInvariant.skip {w0 w cur v r : ℕ} {pref suff : List ℕ}
    {fac : Array (ℕ × ℕ)} (hl : ForIn.toList primeTable = pref ++ cur :: suff)
    (h : FactorLcfInvariant w0 pref (cur :: suff) w fac) (hw0 : 0 < w0)
    (hv : (v, r) = Id.run (valuation (w : ℤ) cur)) (h0 : ¬0 < v) :
    FactorLcfInvariant w0 (pref ++ [cur]) suff w fac := by
  have hcur : cur.Prime := prime_of_mem_primeTable (Array.mem_of_forIn_toList_eq_append_cons hl)
  obtain ⟨m, hm, hpm⟩ := exists_eq_of_eq_run_valuation (h.ne_zero hw0) hcur.one_lt hv
  obtain rfl : v = 0 := by lia
  rw [Nat.pow_zero, Nat.one_mul] at hm
  refine ⟨h.1, h.2.1, h.2.2.1, fun _ q hq hqw ↦ ?_⟩
  have := h.2.2.2 (List.cons_ne_nil _ _) q hq hqw
  exact ⟨this.1, fun hmem ↦ (List.mem_append.mp hmem).elim this.2 fun he ↦
    hpm (hm ▸ List.mem_singleton.mp he ▸ hqw)⟩

theorem FactorLcfInvariant.post {w0 w : ℕ} {xs : List ℕ} {fac : Array (ℕ × ℕ)}
    (h : FactorLcfInvariant w0 xs [] w fac) (hw : w = 1) : IsFactorization w0 fac.toList := by
  obtain ⟨h1, h2, h3, -⟩ := h
  refine ⟨h2, fun x hx ↦ ⟨(h3 x hx).1, (h3 x hx).2.2.1, (h3 x hx).2.1⟩,
    fun q hq hqw ↦ by_contra fun hn ↦ ?_⟩
  rw [h1, hw, Nat.one_mul] at hqw
  refine not_dvd_prod_pow hq (fun x hx ↦ ⟨(h3 x hx).1, fun he ↦ hn ?_⟩) hqw
  exact List.mem_map.mpr ⟨x, hx, he⟩

-- The valuation, as a value for the contracts of the factorization and of the slopes.
private theorem valuation_value (n : ℤ) (p : ℕ) :
    ⦃ True ⦄ valuation n p ⦃ fun r ↦ r = Id.run (valuation n p) ⦄ :=
  ⟨fun _ ↦ rfl⟩

section

/- The invariant is irreducible here, and so are the table of primes, the test of the `long`s and
the valuation, whose unfolding in a failed unification of the dispatch does not end. -/
attribute [local irreducible] FactorLcfInvariant fitsLong valuation primeTable

/-- The factorization of `w ≥ 1` over `2` and the primes of the table, when it leaves the cofactor
`1`: the distinct primes of `w`, each with its valuation. -/
@[spec]
theorem factorLcf_spec (w : ℕ) :
    ⦃ 0 < w ⦄ factorLcf w ⦃ fun r ↦ r.2 = 1 → IsFactorization w r.1 ⦄ := by
  vcgen [factorLcf, valuation_value] invariants
  · fun pref suff s ↦ FactorLcfInvariant w pref suff s.1 s.2
  · fun pref suff s ↦ FactorLcfInvariant w pref suff s.1 s.2
  all_goals dsimp only at *
  all_goals first
    | exact factorLcfInvariant_nil_push ‹_› ‹_› ‹_›
    | exact factorLcfInvariant_nil ‹_› ‹_› ‹_›
    | exact FactorLcfInvariant.push_self ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact FactorLcfInvariant.push_cur ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact FactorLcfInvariant.skip ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact ‹FactorLcfInvariant _ _ _ _ _›.done _
    | exact ‹FactorLcfInvariant _ _ _ _ _›.post ‹_›

end

/-- `Ratpoints.Setup.factorLcf_spec` as a plain statement, for a factorization with the cofactor
`1`. -/
theorem isFactorization_of_run_factorLcf_eq {w : ℕ} (hw : 0 < w) {fac : List (ℕ × ℕ)}
    (h : Id.run (factorLcf w) = (fac, 1)) : IsFactorization w fac := by
  have := Std.WP.Id.of_run_eq_wp rfl _ ((factorLcf_spec w).le_wp hw)
  rw [h] at this
  exact this rfl

/-- The square `p * p` of a prime of the table, which `setup_us1` computes as an `int`
(`find_points.c:800`), is below `2 ^ 31`. -/
theorem mul_self_lt_of_mem_primeTable {p : ℕ} (hp : p ∈ primeTable) : p * p < 2 ^ 31 := by
  have := lt_of_mem_primeTable hp
  have := Nat.mul_self_le_mul_self (Nat.le_of_lt_succ this)
  lia

/-- A cofactor below the square of a prime of the table is a `long`, so that the test of
`Ratpoints.Setup.factorLcf` before it takes the cofactor as a prime always passes
(`find_points.c:808`). -/
theorem fitsLong_of_lt_mul_self {w p : ℕ} (hp : p ∈ primeTable) (hw : w < p * p) :
    fitsLong (w : ℤ) = true := by
  have := mul_self_lt_of_mem_primeTable hp
  simp [fitsLong]
  lia

/-! ### The squarefree divisors -/

/-- One pass of the doubling loop of `Ratpoints.Setup.squarefreeDivisors` with the prime `p`: the
divisors `ds` found so far, then `x p` for each `x` of them with `x ≤ ⌊bHigh / p⌋`, in their
order. -/
def extendDivisors (bHigh : ℕ) (ds : List ℕ) (p : ℕ) : List ℕ :=
  ds ++ (ds.filter (· ≤ bHigh / p)).map (· * p)

/-- The invariant of the loop of `Ratpoints.Setup.squarefreeDivisors` over the primes, after the
primes `pref`: the list has stopped, with `Ratpoints.maxDivisors` entries or more, or it is that of
the passes over `pref` (`Ratpoints.Setup.extendDivisors`). -/
def DivisorsInvariant (bHigh : ℕ) (pref : List ℕ) (divs : Array ℕ) : Prop :=
  maxDivisors ≤ divs.size ∨ divs.toList = pref.foldl (extendDivisors bHigh) [1]

/-- The invariant of the pass of `Ratpoints.Setup.squarefreeDivisors` with the prime `p` over the
divisors `divs0`, after the positions `pref`: the list has stopped, or it is `divs0` followed by
the products `x p` of the entries `x ≤ ⌊bHigh / p⌋` among the first `|pref|` ones. -/
def ExtendDivisorsInvariant (bHigh p : ℕ) (divs0 : Array ℕ) (pref : List ℕ) (divs : Array ℕ) :
    Prop :=
  maxDivisors ≤ divs.size ∨ divs.toList =
    divs0.toList ++ ((divs0.toList.take pref.length).filter (· ≤ bHigh / p)).map (· * p)

theorem divisorsInvariant_nil (bHigh : ℕ) : DivisorsInvariant bHigh [] #[1] :=
  .inr rfl

theorem extendDivisorsInvariant_nil (bHigh p : ℕ) (divs0 : Array ℕ) :
    ExtendDivisorsInvariant bHigh p divs0 [] divs0 :=
  .inr (by simp)

theorem divisorsInvariant_of_le {bHigh : ℕ} {pref : List ℕ} {divs : Array ℕ}
    (h : maxDivisors ≤ divs.size) : DivisorsInvariant bHigh pref divs :=
  .inl h

theorem extendDivisorsInvariant_of_le {bHigh p : ℕ} {divs0 : Array ℕ} {pref : List ℕ}
    {divs : Array ℕ} (h : maxDivisors ≤ divs.size) :
    ExtendDivisorsInvariant bHigh p divs0 pref divs :=
  .inl h

theorem ExtendDivisorsInvariant.divisorsInvariant {bHigh p : ℕ} {divs0 divs : Array ℕ}
    {pref : List ℕ} (h0 : DivisorsInvariant bHigh pref divs0)
    (h : ExtendDivisorsInvariant bHigh p divs0 (ForIn.toList [:divs0.size]) divs)
    (hlt : ¬maxDivisors ≤ divs.size) : DivisorsInvariant bHigh (pref ++ [p]) divs := by
  have hd := h.resolve_left hlt
  have hle : divs0.size ≤ divs.size := by
    rw [← Array.length_toList, ← Array.length_toList, hd, List.length_append]
    lia
  refine .inr ?_
  rw [hd, List.foldl_append, List.foldl_cons, List.foldl_nil, ← h0.resolve_left (by lia),
    List.take_of_length_le (by simp [Std.Legacy.Range.size])]
  rfl

-- The entry at the position `cur` of a pass is that of `divs0`, which the pass has not changed.
private theorem ExtendDivisorsInvariant.getElem?_eq {bHigh p cur : ℕ} {divs0 divs : Array ℕ}
    {pref suff : List ℕ} (hl : ForIn.toList [:divs0.size] = pref ++ cur :: suff)
    (h : ExtendDivisorsInvariant bHigh p divs0 pref divs) (hlt : ¬maxDivisors ≤ divs.size) :
    pref.length = cur ∧ divs0.toList[cur]? = some divs[cur]! := by
  have hcs := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hd := h.resolve_left hlt
  have hcs' : cur < divs0.toList.length := by rw [Array.length_toList]; exact hcs
  refine ⟨Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl, ?_⟩
  rw [getElem!_pos divs cur (by rw [← Array.length_toList, hd]; simp; lia), ← Array.getElem_toList,
    List.getElem?_eq_getElem hcs']
  simp only [hd, List.getElem_append_left hcs']

theorem ExtendDivisorsInvariant.push {bHigh p cur : ℕ} {divs0 divs : Array ℕ}
    {pref suff : List ℕ} (hl : ForIn.toList [:divs0.size] = pref ++ cur :: suff)
    (h : ExtendDivisorsInvariant bHigh p divs0 pref divs) (hle : divs[cur]! ≤ bHigh / p)
    (hlt : ¬maxDivisors ≤ (divs.push (divs[cur]! * p)).size) :
    ExtendDivisorsInvariant bHigh p divs0 (pref ++ [cur]) (divs.push (divs[cur]! * p)) := by
  have hlt' : ¬maxDivisors ≤ divs.size := by simp at hlt; lia
  obtain ⟨hc, hx⟩ := h.getElem?_eq hl hlt'
  refine .inr ?_
  rw [Array.toList_push, h.resolve_left hlt', List.length_append, List.length_singleton, hc,
    List.take_add_one, hx]
  simp [hle]

theorem ExtendDivisorsInvariant.skip {bHigh p cur : ℕ} {divs0 divs : Array ℕ}
    {pref suff : List ℕ} (hl : ForIn.toList [:divs0.size] = pref ++ cur :: suff)
    (h : ExtendDivisorsInvariant bHigh p divs0 pref divs) (hgt : ¬divs[cur]! ≤ bHigh / p)
    (hlt : ¬maxDivisors ≤ divs.size) :
    ExtendDivisorsInvariant bHigh p divs0 (pref ++ [cur]) divs := by
  obtain ⟨hc, hx⟩ := h.getElem?_eq hl hlt
  refine .inr ?_
  rw [h.resolve_left hlt, List.length_append, List.length_singleton, hc, List.take_add_one, hx]
  simp [hgt]

theorem DivisorsInvariant.eq_foldl {bHigh : ℕ} {ps : List ℕ} {divs : Array ℕ}
    (h : DivisorsInvariant bHigh ps divs) (hlt : divs.toList.length < maxDivisors) :
    divs.toList = ps.foldl (extendDivisors bHigh) [1] :=
  h.resolve_left (by simpa using hlt)

section

/- The invariants are irreducible here: the verification conditions of
`Ratpoints.Setup.squarefreeDivisors` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] DivisorsInvariant ExtendDivisorsInvariant

/-- When the doubling loop stops at `Ratpoints.maxDivisors` entries, its list has that many; so a
shorter list is that of all passes (`Ratpoints.Setup.extendDivisors`). -/
@[spec]
theorem squarefreeDivisors_spec (ps : List ℕ) (bHigh : ℕ) :
    ⦃ True ⦄ squarefreeDivisors ps bHigh
    ⦃ fun r ↦ r.length < maxDivisors → r = ps.foldl (extendDivisors bHigh) [1] ⦄ := by
  vcgen [squarefreeDivisors] invariants
  | inv1 => fun pref _ divs ↦ DivisorsInvariant bHigh pref divs
  | inv2 _ p _ _ divs0 _ => fun pref _ divs ↦ ExtendDivisorsInvariant bHigh p divs0 pref divs
  all_goals first
    | exact divisorsInvariant_nil _
    | exact extendDivisorsInvariant_nil _ _ _
    | exact divisorsInvariant_of_le ‹_›
    | exact extendDivisorsInvariant_of_le ‹_›
    | exact ‹ExtendDivisorsInvariant _ _ _ _ _›.divisorsInvariant ‹_› ‹_›
    | exact ‹ExtendDivisorsInvariant _ _ _ _ _›.push ‹_› ‹_› ‹_›
    | exact ‹ExtendDivisorsInvariant _ _ _ _ _›.skip ‹_› ‹_› ‹_›
    | exact ‹DivisorsInvariant _ _ _›.eq_foldl ‹_›

end

-- `t p` for a squarefree `t` whose primes lie in `qs ∌ p` is squarefree with the primes `qs ∪ {p}`.
private theorem squarefree_mul_and_primeFactors_subset {p t : ℕ} (hp : p.Prime) {qs : Finset ℕ}
    (hpq : p ∉ qs) (ht : Squarefree t) (htq : t.primeFactors ⊆ qs) :
    Squarefree (t * p) ∧ (t * p).primeFactors ⊆ insert p qs := by
  have hpt : ¬p ∣ t := fun h ↦ hpq (htq (Nat.mem_primeFactors.mpr ⟨hp, h, ht.ne_zero⟩))
  refine ⟨Nat.squarefree_mul_iff.mpr ⟨Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr
    hpt), ht, hp.squarefree⟩, ?_⟩
  rw [Nat.primeFactors_mul ht.ne_zero hp.ne_zero, hp.primeFactors, Finset.union_comm]
  exact Finset.union_subset_union (fun _ h ↦ h) htq

-- A squarefree `s ≤ bHigh` whose primes lie in `insert p qs` arises in the pass with `p`.
private theorem mem_extendDivisors_of_squarefree {bHigh p : ℕ} (hp : p.Prime) {qs : Finset ℕ}
    {ds : List ℕ} (hds : ∀ s, s ∈ ds ↔ Squarefree s ∧ s.primeFactors ⊆ qs ∧ s ≤ bHigh) {s : ℕ}
    (hs : Squarefree s) (hsub : s.primeFactors ⊆ insert p qs) (hb : s ≤ bHigh) :
    s ∈ extendDivisors bHigh ds p := by
  simp only [extendDivisors, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq, hds]
  by_cases hps : p ∣ s
  · obtain ⟨t, rfl⟩ := hps
    have ht : Squarefree t := hs.of_mul_right
    have hpt : ¬p ∣ t := fun h ↦ hp.one_lt.ne' (Nat.isUnit_iff.mp (hs p (mul_dvd_mul_left p h)))
    refine .inr ⟨t, ⟨⟨ht, fun x hx ↦ ?_, ?_⟩, ?_⟩, Nat.mul_comm t p⟩
    · rcases Finset.mem_insert.mp (hsub (Nat.primeFactors_mono (dvd_mul_left t p)
        (mul_ne_zero hp.ne_zero ht.ne_zero) hx)) with rfl | h
      · exact absurd (Nat.dvd_of_mem_primeFactors hx) hpt
      · exact h
    · exact (Nat.le_mul_of_pos_left t hp.pos).trans hb
    · exact (Nat.le_div_iff_mul_le hp.pos).mpr (by rw [Nat.mul_comm]; exact hb)
  · refine .inl ⟨hs, fun x hx ↦ ?_, hb⟩
    rcases Finset.mem_insert.mp (hsub hx) with rfl | h
    · exact absurd (Nat.dvd_of_mem_primeFactors hx) hps
    · exact h

theorem mem_extendDivisors_iff {bHigh p : ℕ} (hp : p.Prime) {qs : Finset ℕ} (hpq : p ∉ qs)
    {ds : List ℕ} (hds : ∀ s, s ∈ ds ↔ Squarefree s ∧ s.primeFactors ⊆ qs ∧ s ≤ bHigh) (s : ℕ) :
    s ∈ extendDivisors bHigh ds p ↔ Squarefree s ∧ s.primeFactors ⊆ insert p qs ∧ s ≤ bHigh := by
  refine ⟨fun h ↦ ?_, fun ⟨hs, hsub, hb⟩ ↦ mem_extendDivisors_of_squarefree hp hds hs hsub hb⟩
  simp only [extendDivisors, List.mem_append, List.mem_map, List.mem_filter, decide_eq_true_eq,
    hds] at h
  rcases h with ⟨hs, hsub, hb⟩ | ⟨t, ⟨⟨ht, htsub, -⟩, htp⟩, rfl⟩
  · exact ⟨hs, hsub.trans (Finset.subset_insert _ _), hb⟩
  · exact ⟨(squarefree_mul_and_primeFactors_subset hp hpq ht htsub).1,
      (squarefree_mul_and_primeFactors_subset hp hpq ht htsub).2,
      (Nat.le_div_iff_mul_le hp.pos).mp htp⟩

theorem mem_foldl_extendDivisors_iff {bHigh : ℕ} {ps : List ℕ} (hps : ∀ p ∈ ps, p.Prime)
    (hnd : ps.Nodup) {qs : Finset ℕ} (hdisj : ∀ p ∈ ps, p ∉ qs) {ds : List ℕ}
    (hds : ∀ s, s ∈ ds ↔ Squarefree s ∧ s.primeFactors ⊆ qs ∧ s ≤ bHigh) (s : ℕ) :
    s ∈ ps.foldl (extendDivisors bHigh) ds ↔
      Squarefree s ∧ s.primeFactors ⊆ qs ∪ ps.toFinset ∧ s ≤ bHigh := by
  induction ps generalizing qs ds with
  | nil => simpa using hds s
  | cons p ps ih =>
    rw [List.foldl_cons, ih (fun q hq ↦ hps q (.tail _ hq)) hnd.of_cons (qs := insert p qs)
      (fun q hq ↦ ?_) (mem_extendDivisors_iff (hps p (.head _)) (hdisj p (.head _)) hds)]
    · simp [Finset.insert_union, Finset.union_insert]
    · rw [Finset.mem_insert, not_or]
      exact ⟨fun h ↦ (List.nodup_cons.mp hnd).1 (h ▸ hq), hdisj q (.tail _ hq)⟩

/-- The doubling loop over distinct primes lists exactly the squarefree numbers up to `bHigh ≥ 1`
made of these primes. -/
theorem mem_foldl_extendDivisors_one_iff {bHigh : ℕ} (hbHigh : 1 ≤ bHigh) {ps : List ℕ}
    (hps : ∀ p ∈ ps, p.Prime) (hnd : ps.Nodup) (s : ℕ) :
    s ∈ ps.foldl (extendDivisors bHigh) [1] ↔
      Squarefree s ∧ s.primeFactors ⊆ ps.toFinset ∧ s ≤ bHigh := by
  rw [mem_foldl_extendDivisors_iff hps hnd (qs := ∅) (by simp) fun s ↦ ?_, Finset.empty_union]
  simp only [List.mem_singleton, Finset.subset_empty, Nat.primeFactors_eq_empty]
  exact ⟨by rintro rfl; exact ⟨squarefree_one, .inr rfl, hbHigh⟩,
    fun ⟨hs, h, _⟩ ↦ h.resolve_left hs.ne_zero⟩

-- One pass with a new prime keeps the list without duplicates, and its entries made of the primes.
private theorem nodup_extendDivisors {bHigh p : ℕ} (hp : p.Prime) {qs : Finset ℕ} (hpq : p ∉ qs)
    {ds : List ℕ} (hd : ds.Nodup) (hds : ∀ s ∈ ds, s ≠ 0 ∧ s.primeFactors ⊆ qs) :
    (extendDivisors bHigh ds p).Nodup ∧
      ∀ s ∈ extendDivisors bHigh ds p, s ≠ 0 ∧ s.primeFactors ⊆ insert p qs := by
  have hpd (s : ℕ) (hs : s ∈ ds) : ¬p ∣ s := fun h ↦
    hpq ((hds s hs).2 (Nat.mem_primeFactors.mpr ⟨hp, h, (hds s hs).1⟩))
  refine ⟨List.nodup_append.mpr ⟨hd, (hd.filter _).map fun a b h ↦
    Nat.eq_of_mul_eq_mul_right hp.pos h, fun a ha b hb hab ↦ ?_⟩, fun s hs ↦ ?_⟩
  · obtain ⟨c, -, rfl⟩ := List.mem_map.mp hb
    exact hpd a ha (hab ▸ dvd_mul_left p c)
  rcases List.mem_append.mp hs with hs | hs
  · exact ⟨(hds s hs).1, (hds s hs).2.trans (Finset.subset_insert _ _)⟩
  · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hs
    have hc := hds c (List.mem_filter.mp hc).1
    refine ⟨mul_ne_zero hc.1 hp.ne_zero, ?_⟩
    rw [Nat.primeFactors_mul hc.1 hp.ne_zero, hp.primeFactors, Finset.union_comm]
    exact Finset.union_subset_union (fun _ h ↦ h) hc.2

theorem nodup_foldl_extendDivisors {bHigh : ℕ} {ps : List ℕ} (hps : ∀ p ∈ ps, p.Prime)
    (hnd : ps.Nodup) {qs : Finset ℕ} (hdisj : ∀ p ∈ ps, p ∉ qs) {ds : List ℕ} (hd : ds.Nodup)
    (hds : ∀ s ∈ ds, s ≠ 0 ∧ s.primeFactors ⊆ qs) :
    (ps.foldl (extendDivisors bHigh) ds).Nodup := by
  induction ps generalizing qs ds with
  | nil => exact hd
  | cons p ps ih =>
    have h := nodup_extendDivisors (bHigh := bHigh) (hps p (.head _)) (hdisj p (.head _)) hd hds
    refine ih (fun q hq ↦ hps q (.tail _ hq)) hnd.of_cons (qs := insert p qs) (fun q hq ↦ ?_)
      h.1 h.2
    rw [Finset.mem_insert, not_or]
    exact ⟨fun h ↦ (List.nodup_cons.mp hnd).1 (h ▸ hq), hdisj q (.tail _ hq)⟩

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
  have := h.1
  refine ⟨by lia, fun j hj ↦ ?_⟩
  rcases List.mem_append.mp hj with hj | hj
  · exact Int.le_trans (h.2 j hj) (Int.mul_le_mul_of_nonneg_left (Int.le_of_lt hlt) (by lia))
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
    exact Int.le_trans hm (Int.mul_le_mul_of_nonneg_left (by lia) (by lia))

theorem SlopeInvariant.post {c : List ℤ} {d p val : ℕ} {n : ℤ}
    (h : SlopeInvariant c d p val (ForIn.toList [:d]) n) :
    1 ≤ n.toNat ∧ ∀ k < d, 1 + (val : ℤ) - (Id.run (valuation (c.getD k 0) p)).1 ≤
      ((d - k : ℕ) : ℤ) * n.toNat := by
  refine ⟨by have := h.1; lia, fun k hk ↦ ?_⟩
  have := h.2 (d - 1 - k) (by simp [Std.Legacy.Range.size]; lia)
  rw [Nat.sub_sub_self (by lia : k ≤ d - 1)] at this
  rwa [Int.toNat_of_nonneg (by have := h.1; lia)]

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
    | exact ‹SlopeInvariant _ _ _ _ _ _›.post

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

/-- The divisor set-up, when it succeeds, is made of the factorization of `|c_d|` with the cofactor
`1` (`Ratpoints.Setup.factorLcf`), the list of the doubling loop over its primes
(`Ratpoints.Setup.squarefreeDivisors`) with fewer than `Ratpoints.maxDivisors` entries, and the
primes with their valuations and slopes (`Ratpoints.Setup.slope`). -/
@[spec]
theorem setupUs1_spec (c : List ℤ) (d bHigh : ℕ) :
    ⦃ True ⦄ setupUs1 c d bHigh
    ⦃ fun r ↦ ∀ info divisors, r = some (info, divisors) →
        ∃ fac, Id.run (factorLcf (c.getD d 0).natAbs) = (fac, 1) ∧
          divisors = Id.run (squarefreeDivisors (fac.map Prod.fst) bHigh) ∧
          divisors.length < maxDivisors ∧
          info = fac.map fun x ↦ ⟨x.1, x.2, Id.run (slope c d x.1 x.2)⟩ ⦄ := by
  vcgen [setupUs1, factorLcf_value, squarefreeDivisors_value, slope_value] invariants
  · fun pref _ info ↦ info.toList = pref.map fun x ↦ ⟨x.1, x.2, Id.run (slope c d x.1 x.2)⟩
  all_goals first
    | exact nomatch ‹none = some _›
    | rfl
    | grind

/-- `Ratpoints.Setup.setupUs1_spec` as a plain statement, which the proofs use without the program
logic. -/
theorem exists_of_setupUs1_eq_some {c : List ℤ} {d bHigh : ℕ} {info : List DenInfo}
    {divisors : List ℕ} (h : Id.run (setupUs1 c d bHigh) = some (info, divisors)) :
    ∃ fac, Id.run (factorLcf (c.getD d 0).natAbs) = (fac, 1) ∧
      divisors = Id.run (squarefreeDivisors (fac.map Prod.fst) bHigh) ∧
      divisors.length < maxDivisors ∧
      info = fac.map fun x ↦ ⟨x.1, x.2, Id.run (slope c d x.1 x.2)⟩ := by
  have := Std.WP.Id.of_run_eq_wp rfl _ ((setupUs1_spec c d bHigh).le_wp trivial)
  exact this info divisors h

/-- When the divisor set-up succeeds, its divisors are those of the doubling loop over the distinct
primes of `|c_d|`, each with its valuation. -/
theorem eq_foldl_of_setupUs1_eq_some {c : List ℤ} {d bHigh : ℕ} {info : List DenInfo}
    {divisors : List ℕ} (h : Id.run (setupUs1 c d bHigh) = some (info, divisors))
    (hc : c.getD d 0 ≠ 0) :
    ∃ fac : List (ℕ × ℕ), IsFactorization (c.getD d 0).natAbs fac ∧
      divisors = (fac.map Prod.fst).foldl (extendDivisors bHigh) [1] ∧
      info = fac.map fun x ↦ ⟨x.1, x.2, Id.run (slope c d x.1 x.2)⟩ := by
  obtain ⟨fac, hfac, hdiv, hlen, rfl⟩ := exists_of_setupUs1_eq_some h
  refine ⟨fac, isFactorization_of_run_factorLcf_eq (Int.natAbs_pos.mpr hc) hfac, ?_, rfl⟩
  subst hdiv
  exact Std.WP.Id.of_run_eq_wp rfl _ ((squarefreeDivisors_spec _ bHigh).le_wp trivial) hlen

/-- When the divisor set-up succeeds, its divisors are exactly the squarefree divisors of `|c_d|` up
to the largest denominator `bHigh ≥ 1`: the factorization is complete and the list of the doubling
loop has fewer than `Ratpoints.maxDivisors` entries, so that it did not stop early. -/
theorem mem_iff_of_setupUs1_eq_some {c : List ℤ} {d bHigh : ℕ} {info : List DenInfo}
    {divisors : List ℕ} (h : Id.run (setupUs1 c d bHigh) = some (info, divisors))
    (hc : c.getD d 0 ≠ 0) (hbHigh : 1 ≤ bHigh) {s : ℕ} :
    s ∈ divisors ↔ Squarefree s ∧ s ∣ (c.getD d 0).natAbs ∧ s ≤ bHigh := by
  obtain ⟨fac, ⟨hnd, hp, hall⟩, rfl, -⟩ := eq_foldl_of_setupUs1_eq_some h hc
  rw [mem_foldl_extendDivisors_one_iff hbHigh (fun p hp' ↦ ?_) hnd]
  · refine and_congr_right fun hs ↦ and_congr_left fun _ ↦ ?_
    have hdvd : s ∣ (c.getD d 0).natAbs ↔ s.primeFactors ⊆ (c.getD d 0).natAbs.primeFactors := by
      nth_rw 1 [← Nat.prod_primeFactors_of_squarefree hs]
      exact Nat.prod_primeFactors_dvd_iff (Int.natAbs_ne_zero.mpr hc)
    rw [hdvd]
    refine ⟨fun hsub q hq ↦ ?_, fun hsub q hq ↦ ?_⟩
    · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp (List.mem_toFinset.mp (hsub hq))
      refine Nat.mem_primeFactors.mpr ⟨(hp x hx).1, ?_, Int.natAbs_ne_zero.mpr hc⟩
      have : Fact x.1.Prime := ⟨(hp x hx).1⟩
      exact dvd_of_one_le_padicValNat ((hp x hx).2.2 ▸ (hp x hx).2.1)
    · obtain ⟨hqp, hqd, -⟩ := Nat.mem_primeFactors.mp (hsub hq)
      exact List.mem_toFinset.mpr (hall q hqp hqd)
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hp'
    exact (hp x hx).1

theorem nodup_of_setupUs1_eq_some {c : List ℤ} {d bHigh : ℕ} {info : List DenInfo}
    {divisors : List ℕ} (h : Id.run (setupUs1 c d bHigh) = some (info, divisors))
    (hc : c.getD d 0 ≠ 0) : divisors.Nodup := by
  obtain ⟨fac, ⟨hnd, hp, -⟩, rfl, -⟩ := eq_foldl_of_setupUs1_eq_some h hc
  exact nodup_foldl_extendDivisors (fun q hq ↦ by
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hq
    exact (hp x hx).1) hnd (qs := ∅) (by simp) (List.nodup_singleton 1) (by simp)

/-- The products `x p` that the doubling loop of the C code computes, only for `x ≤ ⌊bHigh / p⌋`
(`find_points.c:876`), are at most `bHigh`, and so `long`s for a `long` `bHigh`. -/
theorem fitsLong_mul_of_le_div {x p bHigh : ℕ} (h : x ≤ bHigh / p) (hH : bHigh < 2 ^ 63) :
    fitsLong ((x * p : ℕ) : ℤ) = true := by
  have : x * p ≤ bHigh := by
    rcases Nat.eq_zero_or_pos p with rfl | hp
    · simp
    · exact (Nat.le_div_iff_mul_le hp).mp h
  simp [fitsLong]
  lia

/-- Whether the entry `e` of the valuation test of the divisor shape (`Ratpoints.Sieve.denInfoTest`)
excludes the denominator `b`: `v_p(b) ≥ e.slope` with `v_p(b) + e.val` odd, for the valuation
`v_p(b)` of `Ratpoints.Setup.valuation`. -/
def DenInfo.excludes (e : DenInfo) (b : ℕ) : Bool :=
  decide (e.slope ≤ (Id.run (valuation b e.p)).1) && ((Id.run (valuation b e.p)).1 + e.val) % 2 == 1

theorem DenInfo.excludes_eq_false_iff {e : DenInfo} {b : ℕ} :
    e.excludes b = false ↔ ¬(decide (e.slope ≤ (Id.run (valuation b e.p)).1) &&
      ((Id.run (valuation b e.p)).1 + e.val) % 2 == 1) = true :=
  Bool.eq_false_iff

/-- An entry of the valuation test, a prime `p` of `|c_d|` with its valuation `val` and its slope
(`Ratpoints.Setup.slope_spec`), does not exclude the denominator `b = p ^ m b'` of a point:
for `m ≥ slope`, `m + val` is even (`Ratpoints.even_add_of_sq_eq_binaryForm_of_odd`). -/
theorem DenInfo.excludes_eq_false_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 1) {p val : ℕ}
    (hp : p.Prime) (hval : val = padicValNat p (c.getD (degree c) 0).natAbs) {a y : ℤ} {b : ℕ}
    (hb : b ≠ 0) (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    (⟨p, val, Id.run (Setup.slope c (degree c) p val)⟩ : DenInfo).excludes b = false := by
  have : Fact p.Prime := ⟨hp⟩
  have hsl := Std.WP.Id.of_run_eq_wp rfl _ ((slope_spec c (degree c) p val).le_wp trivial)
  have hv : (Id.run (valuation b p)).1 = padicValNat p b := by
    rw [fst_run_valuation (Int.natCast_ne_zero.mpr hb) hp, Int.natAbs_natCast]
  simp only [DenInfo.excludes_eq_false_iff, hv, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
  refine fun ⟨hle, hodd⟩ ↦ Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr (by lia))
    (even_add_of_sq_eq_binaryForm_of_odd hd hval.symm (fun k hk hck ↦ ?_) hab (by lia) hy)
  have := hsl.2 k hk
  rw [fst_run_valuation hck hp] at this
  have := Nat.mul_le_mul_left (degree c - k) hle
  lia

end Setup

end Ratpoints

end
