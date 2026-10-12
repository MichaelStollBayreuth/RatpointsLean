/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Ratpoints.Model.Denominators
public import Ratpoints.Spec.Basic
public import Std.WP

import Ratpoints.Mathlib.Data.Nat.Factors
import Ratpoints.Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Ratpoints.Proof.Bits
import Ratpoints.Proof.Tables
import Std.Tactic.Do

/-!
# The Jacobi test by the binary algorithm

The binary algorithm of the C code (`Ratpoints.Sieve.jacobi`) computes the Jacobi symbol
`(lcf / b*)` for `b ≥ 1`, where `b*` is the largest divisor of `b` prime to `2 lcf`, the product of
the prime factors of `b` prime to `2 lcf`
(`(b.primeFactorsList.filter (·.Coprime (2 * lcf.natAbs))).prod`, which
`Nat.prod_filter_primeFactorsList_dvd`, `Nat.coprime_prod_filter_primeFactorsList` and
`Nat.dvd_prod_filter_primeFactorsList_of_dvd` characterize as that divisor): each round
(`Ratpoints.Sieve.jacobiRound`) keeps the symbol with its sign, taking out the factors `2` with the
sign of `(2 / m)` (`Ratpoints.Sieve.twoSign`) and exchanging the two numbers with the sign of the
reciprocity, and gives the symbol of `f` and `b` or their gcd, which the algorithm divides out of
`b`. For a polynomial of even degree the symbol is `1` on the denominator `b` of every point, since
`c_d` is a square modulo every prime factor of `b` prime to `c_d`
(`Ratpoints.Sieve.isSquare_getD_degree_of_sq_eq_binaryForm`); so the binary algorithm lets the
denominator of every point through, and so does the test by tables, which computes the same symbol
(`Ratpoints.Sieve.run_jacobiTest`).

## Main statements

* `Ratpoints.Sieve.twoSign_eq`: the sign of `(2 / m)`.
* `Ratpoints.Sieve.jacobiReduce_spec`, `Ratpoints.Sieve.jacobiRound_spec`: the contracts of the
  subtraction loop and of a round.
* `Ratpoints.Sieve.jacobi_spec`, `Ratpoints.Sieve.run_jacobi`: the binary algorithm computes
  `(lcf / b*)`.
* `Ratpoints.Sieve.jacobiSym_eq_one_of_sq_eq_binaryForm`: the symbol of `c_d` over a divisor of the
  denominator of a point prime to `c_d` is `1`, and so is `(c_d / b*)`
  (`Ratpoints.Sieve.jacobiSym_prod_filter_primeFactorsList_eq_one_of_sq_eq`).
* `Ratpoints.Sieve.run_jacobi_eq_one_of_sq_eq`: the binary algorithm gives `1` on the denominator of
  every point.

## Implementation notes

The contracts are proved with `vcgen`, with loop invariants that are named definitions, in a file
with Mathlib, since they speak of the Jacobi symbol; the early return of the main loop of
`Ratpoints.Sieve.jacobi` is part of the invariant of that loop.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP NumberTheorySymbols

namespace Ratpoints

namespace Sieve

/-! ### The binary algorithm -/

theorem twoSign_eq {m : ℕ} (hm : m % 2 = 1) (s : ℤ) :
    twoSign m s = if m % 8 = 3 ∨ m % 8 = 5 then -s else s := by
  rw [twoSign, Nat.and_eq_mod_two_pow_and (n := 3) (by decide : 2 < 2 ^ 3),
    Nat.and_eq_mod_two_pow_and (n := 3) (by decide : 4 < 2 ^ 3)]
  obtain h | h | h | h : m % 8 = 1 ∨ m % 8 = 3 ∨ m % 8 = 5 ∨ m % 8 = 7 := by lia
  all_goals simp [h]

/-- Halving an even `x` against an odd `y` multiplies the symbol by `(2 / y)`, the factor that
`Ratpoints.Sieve.twoSign` takes. -/
theorem twoSign_mul_jacobiSym_div_two {x y : ℕ} (hx : x % 2 = 0) (hy : y % 2 = 1) (s : ℤ) :
    twoSign y s * J((x / 2 : ℕ) | y) = s * J(x | y) := by
  rw [twoSign_eq hy, ← jacobiSym.even_odd (a := x) (by lia) hy, Int.natCast_div, Nat.cast_ofNat]
  split_ifs <;> ring

/-- The exchange of two odd numbers in the binary algorithm, with the sign of the reciprocity,
`-1` exactly when both are `3 (mod 4)`, as `Ratpoints.Sieve.jacobiRound` tests it on their bits. -/
theorem ite_neg_mul_jacobiSym {n m : ℕ} (hn : n % 2 = 1) (hm : m % 2 = 1) (s : ℤ) :
    (if (n &&& m &&& 2 != 0) = true then -s else s) * J(m | n) = s * J(n | m) := by
  rw [← jacobiSym.quadratic_reciprocity_if hn hm]
  simp only [Nat.and_and_two_ne_zero_iff hn hm]
  split_ifs <;> ring

theorem mul_jacobiSym_eq_of_eq_ite_neg {n m m' : ℕ} {s s' t c : ℤ} (hn : n % 2 = 1)
    (hm : m % 2 = 1) (hc : s * J(n | m) = c) (hr : s' * J(m' | n) = t * J(m | n))
    (ht : t = if (n &&& m &&& 2 != 0) = true then -s else s) : s' * J(m' | n) = c := by
  rw [hr, ht, ite_neg_mul_jacobiSym hn hm, hc]

/-- The invariant of the outer loop of `Ratpoints.Sieve.jacobiReduce` on the odd `x` and `y` with
the sign `s`: the current `x'` is odd, at most `x`, has the gcd of `x` with `y`, and
`s' J(x' | y) = s J(x | y)`; at the exit `x' ≤ y`. -/
def JacobiReduceInvariant (x y : ℕ) (s : ℤ) : Std.WP.WhileInvariant (ℕ × ℤ) Prop :=
  .mk fun exit st ↦ st.1 % 2 = 1 ∧ st.1 ≤ x ∧ st.2 * J(st.1 | y) = s * J(x | y) ∧
    Nat.gcd st.1 y = Nat.gcd x y ∧ (exit = true → st.1 ≤ y)

/-- The invariant of the inner loop of `Ratpoints.Sieve.jacobiReduce`, which halves `x₀ - y`, for
the value `x₀` of the outer loop: the current `x'` is positive and below `x₀`, keeps the symbol and
the gcd of `x` and `y`, and is even while the loop goes on and odd at its exit. -/
def JacobiReduceHalveInvariant (x y x₀ : ℕ) (s : ℤ) : Std.WP.WhileInvariant (ℕ × ℤ) Prop :=
  .mk fun exit st ↦ 0 < st.1 ∧ st.1 < x₀ ∧ st.2 * J(st.1 | y) = s * J(x | y) ∧
    Nat.gcd st.1 y = Nat.gcd x y ∧ st.1 % 2 = if exit then 1 else 0

theorem jacobiReduceInvariant_self {x y : ℕ} (s : ℤ) (h : x % 2 = 1 ∧ y % 2 = 1) :
    JacobiReduceInvariant x y s false (x, s) :=
  ⟨h.1, le_rfl, rfl, rfl, nofun⟩

theorem JacobiReduceInvariant.post {x y x' : ℕ} {s s' : ℤ}
    (h : JacobiReduceInvariant x y s true (x', s')) :
    x' % 2 = 1 ∧ x' ≤ x ∧ x' ≤ y ∧ s' * J(x' | y) = s * J(x | y) ∧ Nat.gcd x' y = Nat.gcd x y :=
  ⟨h.1, h.2.1, h.2.2.2.2 rfl, h.2.2.1, h.2.2.2.1⟩

theorem JacobiReduceInvariant.exit {x y x' mb : ℕ} {s s' : ℤ} (hle : ¬y < x')
    (h : x' = mb ∧ JacobiReduceInvariant x y s false (x', s')) :
    JacobiReduceInvariant x y s true (x', s') :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, fun _ ↦ Nat.le_of_not_lt hle⟩

theorem JacobiReduceInvariant.jacobiReduceHalveInvariant {x y x₀ mb : ℕ} {s s₀ : ℤ}
    (hy : x % 2 = 1 ∧ y % 2 = 1) (hlt : y < x₀)
    (h : x₀ = mb ∧ JacobiReduceInvariant x y s false (x₀, s₀)) :
    JacobiReduceHalveInvariant x y x₀ s false (x₀ - y, s₀) := by
  obtain ⟨-, h1, -, h3, h4, -⟩ := h
  refine ⟨by lia, by lia, ?_, ?_, by simp; lia⟩
  · rwa [jacobiSym.natCast_sub_self hlt.le]
  · rwa [Nat.gcd_sub_self_left hlt.le]

theorem JacobiReduceHalveInvariant.div_two {x y x₀ x' mb : ℕ} {s s' : ℤ} {e : Bool}
    (hy : x % 2 = 1 ∧ y % 2 = 1) (h : x' = mb ∧ JacobiReduceHalveInvariant x y x₀ s false (x', s'))
    (he : x' / 2 % 2 = if e then 1 else 0) :
    JacobiReduceHalveInvariant x y x₀ s e (x' / 2, twoSign y s') := by
  obtain ⟨-, h1, h2, h3, h4, h5⟩ := h
  simp only [Bool.false_eq_true, ↓reduceIte] at h5
  exact ⟨by lia, by lia, by rwa [twoSign_mul_jacobiSym_div_two h5 hy.2],
    by rwa [Nat.gcd_div_two_of_mod_two h5 hy.2], he⟩

theorem JacobiReduceHalveInvariant.done {x y x₀ x' mb : ℕ} {s s' : ℤ}
    (hy : x % 2 = 1 ∧ y % 2 = 1) (h : x' = mb ∧ JacobiReduceHalveInvariant x y x₀ s false (x', s'))
    (hb : (x' / 2 % 2 == 1) = true) :
    JacobiReduceHalveInvariant x y x₀ s true (x' / 2, twoSign y s') :=
  JacobiReduceHalveInvariant.div_two hy h (by simpa using hb)

theorem JacobiReduceHalveInvariant.next {x y x₀ x' mb : ℕ} {s s' : ℤ}
    (hy : x % 2 = 1 ∧ y % 2 = 1) (h : x' = mb ∧ JacobiReduceHalveInvariant x y x₀ s false (x', s'))
    (hb : ¬(x' / 2 % 2 == 1) = true) :
    x' / 2 < mb ∧ JacobiReduceHalveInvariant x y x₀ s false (x' / 2, twoSign y s') :=
  ⟨by have := h.2.1; lia,
    JacobiReduceHalveInvariant.div_two hy h (by simp at hb; simpa using hb)⟩

theorem JacobiReduceHalveInvariant.exit {x y x₀ x' mb : ℕ} {s s' s₀ : ℤ}
    (h : JacobiReduceHalveInvariant x y x₀ s true (x', s'))
    (h₀ : x₀ = mb ∧ JacobiReduceInvariant x y s false (x₀, s₀)) :
    x' < mb ∧ JacobiReduceInvariant x y s false (x', s') := by
  obtain ⟨-, h1, h2, h3, h4⟩ := h
  obtain ⟨rfl, -, h₀1, -⟩ := h₀
  exact ⟨h1, by simpa using h4, by lia, h2, h3, nofun⟩

section

/- The invariants are irreducible here: the verification conditions of
`Ratpoints.Sieve.jacobiReduce` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] JacobiReduceInvariant JacobiReduceHalveInvariant

/-- The subtraction loop of the binary algorithm keeps the symbol with its sign and the gcd, and
ends with an odd `x' ≤ y`; its loops end, since `x'` drops with every pass. -/
@[spec]
theorem jacobiReduce_spec (x y : ℕ) (s : ℤ) :
    ⦃ x % 2 = 1 ∧ y % 2 = 1 ⦄ jacobiReduce x y s
    ⦃ fun r ↦ r.1 % 2 = 1 ∧ r.1 ≤ x ∧ r.1 ≤ y ∧ r.2 * J(r.1 | y) = s * J(x | y) ∧
      Nat.gcd r.1 y = Nat.gcd x y ⦄ := by
  vcgen [jacobiReduce] invariants
  | inv1 => JacobiReduceInvariant x y s
  | inv2 => .ofMeasure fun st : ℕ × ℤ ↦ st.1
  | inv3 x₀ _ _ _ _ => JacobiReduceHalveInvariant x y x₀ s
  | inv4 => .ofMeasure fun st : ℕ × ℤ ↦ st.1
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals first
    | exact jacobiReduceInvariant_self s ‹_›
    | exact JacobiReduceInvariant.post ‹_›
    | exact JacobiReduceInvariant.jacobiReduceHalveInvariant ‹_› ‹_› ‹_›
    | exact JacobiReduceHalveInvariant.exit ‹_› ‹_›
    | exact JacobiReduceHalveInvariant.done ‹_› ‹_› ‹_›
    | exact JacobiReduceHalveInvariant.next ‹_› ‹_› ‹_›
    | exact JacobiReduceInvariant.exit ‹_› ‹_›

end

/-- The invariant of the loop of `Ratpoints.Sieve.jacobiRound` on `f > 0` and the odd `b` that
takes the factors `2` out of `n = f`: `n` is positive, `s J(n | b) = J(f | b)`, the gcd with `b` is
that of `f`, and `n` is odd at the exit. -/
def JacobiRoundHalveInvariant (f b : ℕ) : Std.WP.WhileInvariant (ℤ × ℕ) Prop :=
  .mk fun exit st ↦ 0 < st.2 ∧ st.1 * J(st.2 | b) = J(f | b) ∧ Nat.gcd st.2 b = Nat.gcd f b ∧
    (exit = true → st.2 % 2 = 1)

/-- The invariant of the main loop of `Ratpoints.Sieve.jacobiRound` on `f` and `b`, on the sign `s`
and the odd `n` and `m`: `s J(n | m) = J(f | b)`, the gcd of `n` and `m` is that of `f` and `b`, and
`n = m` at the exit. -/
def JacobiRoundInvariant (f b : ℕ) : Std.WP.WhileInvariant (ℤ × ℕ × ℕ) Prop :=
  .mk fun exit st ↦ st.2.1 % 2 = 1 ∧ st.2.2 % 2 = 1 ∧ st.1 * J(st.2.1 | st.2.2) = J(f | b) ∧
    Nat.gcd st.2.1 st.2.2 = Nat.gcd f b ∧ (exit = true → st.2.1 = st.2.2)

theorem jacobiRoundHalveInvariant_one {f b : ℕ} (h : 0 < f ∧ b % 2 = 1) :
    JacobiRoundHalveInvariant f b false (1, f) :=
  ⟨h.1, one_mul _, rfl, nofun⟩

theorem JacobiRoundHalveInvariant.div_two {f b n mb : ℕ} {s : ℤ} (h : 0 < f ∧ b % 2 = 1)
    (hn : (n % 2 == 0) = true) (hi : n = mb ∧ JacobiRoundHalveInvariant f b false (s, n)) :
    n / 2 < mb ∧ JacobiRoundHalveInvariant f b false (twoSign b s, n / 2) := by
  obtain ⟨rfl, h1, h2, h3, -⟩ := hi
  have hn : n % 2 = 0 := by simpa using hn
  exact ⟨by lia, by lia, by rwa [twoSign_mul_jacobiSym_div_two hn h.2],
    by rwa [Nat.gcd_div_two_of_mod_two hn h.2], nofun⟩

theorem JacobiRoundHalveInvariant.exit {f b n mb : ℕ} {s : ℤ} (hn : ¬(n % 2 == 0) = true)
    (hi : n = mb ∧ JacobiRoundHalveInvariant f b false (s, n)) :
    JacobiRoundHalveInvariant f b true (s, n) :=
  ⟨hi.2.1, hi.2.2.1, hi.2.2.2.1, fun _ ↦ by simpa using hn⟩

theorem JacobiRoundHalveInvariant.jacobiRoundInvariant {f b n : ℕ} {s : ℤ}
    (h : 0 < f ∧ b % 2 = 1) (hi : JacobiRoundHalveInvariant f b true (s, n)) :
    JacobiRoundInvariant f b false (s, n, b) :=
  ⟨hi.2.2.2 rfl, h.2, hi.2.1, hi.2.2.1, nofun⟩

theorem JacobiRoundInvariant.post {f b n m : ℕ} {s : ℤ}
    (h : JacobiRoundInvariant f b true (s, n, m)) : m = Nat.gcd f b ∧ (m = 1 → s = J(f | b)) := by
  obtain ⟨-, -, h3, h4, h5⟩ := h
  obtain rfl : n = m := h5 rfl
  refine ⟨by rwa [Nat.gcd_self] at h4, fun hn ↦ ?_⟩
  rwa [hn, Nat.cast_one, jacobiSym.one_left, mul_one] at h3

theorem JacobiRoundInvariant.odd {f b n m mb : ℕ} {s : ℤ}
    (h : n + m = mb ∧ JacobiRoundInvariant f b false (s, n, m)) : m % 2 = 1 ∧ n % 2 = 1 :=
  ⟨h.2.2.1, h.2.1⟩

theorem JacobiRoundInvariant.odd_of_mod_two_eq_one {f b n m m' mb : ℕ} {s : ℤ}
    (h : n + m = mb ∧ JacobiRoundInvariant f b false (s, n, m)) (hm' : m' % 2 = 1) :
    n % 2 = 1 ∧ m' % 2 = 1 :=
  ⟨h.2.1, hm'⟩

/-- The first half of a pass of `Ratpoints.Sieve.jacobiRound`: after the exchange and the reduction
of `m` by `n`, the symbol of the reduced `m'` over `n` with the new sign is that of `f` and `b`. -/
theorem JacobiRoundInvariant.first_half {f b n m m' mb : ℕ} {s s' t : ℤ}
    (h : n + m = mb ∧ JacobiRoundInvariant f b false (s, n, m))
    (hr : m' % 2 = 1 ∧ m' ≤ m ∧ m' ≤ n ∧ s' * J(m' | n) = t * J(m | n) ∧
      Nat.gcd m' n = Nat.gcd m n)
    (ht : t = if (n &&& m &&& 2 != 0) = true then -s else s) :
    s' * J(m' | n) = J(f | b) ∧ Nat.gcd n m' = Nat.gcd f b := by
  obtain ⟨-, h1, h2, h3, h4, -⟩ := h
  exact ⟨mul_jacobiSym_eq_of_eq_ite_neg h1 h2 h3 hr.2.2.2.1 ht,
    by rw [Nat.gcd_comm, hr.2.2.2.2, Nat.gcd_comm, h4]⟩

/-- The second half of a pass of `Ratpoints.Sieve.jacobiRound`: after the second exchange and the
reduction of `n` by `m'`, the symbol of the reduced `n'` over `m'` with the new sign is that of `f`
and `b`. -/
theorem JacobiRoundInvariant.second_half {f b n m m' n' mb : ℕ} {s s' s'' t t' : ℤ}
    (h : n + m = mb ∧ JacobiRoundInvariant f b false (s, n, m))
    (hr : m' % 2 = 1 ∧ m' ≤ m ∧ m' ≤ n ∧ s' * J(m' | n) = t * J(m | n) ∧
      Nat.gcd m' n = Nat.gcd m n)
    (hr' : n' % 2 = 1 ∧ n' ≤ n ∧ n' ≤ m' ∧ s'' * J(n' | m') = t' * J(n | m') ∧
      Nat.gcd n' m' = Nat.gcd n m')
    (ht : t = if (n &&& m &&& 2 != 0) = true then -s else s)
    (ht' : t' = if (m' &&& n &&& 2 != 0) = true then -s' else s') :
    s'' * J(n' | m') = J(f | b) ∧ Nat.gcd n' m' = Nat.gcd f b := by
  obtain ⟨h1, h2⟩ := JacobiRoundInvariant.first_half h hr ht
  refine ⟨mul_jacobiSym_eq_of_eq_ite_neg hr.1 h.2.1 h1 hr'.2.2.2.1 ?_, by rw [hr'.2.2.2.2, h2]⟩
  rw [ht', Nat.and_comm m' n]

theorem JacobiRoundInvariant.first_break {f b n m m' mb : ℕ} {s s' t : ℤ}
    (h : n + m = mb ∧ JacobiRoundInvariant f b false (s, n, m))
    (hr : m' % 2 = 1 ∧ m' ≤ m ∧ m' ≤ n ∧ s' * J(m' | n) = t * J(m | n) ∧
      Nat.gcd m' n = Nat.gcd m n)
    (heq : (m' == n) = true) (ht : t = if (n &&& m &&& 2 != 0) = true then -s else s) :
    JacobiRoundInvariant f b true (s', n, m') := by
  obtain ⟨h1, h2⟩ := JacobiRoundInvariant.first_half h hr ht
  obtain rfl : m' = n := by simpa using heq
  exact ⟨hr.1, hr.1, h1, h2, fun _ ↦ rfl⟩

theorem JacobiRoundInvariant.second_break {f b n m m' n' mb : ℕ} {s s' s'' t t' : ℤ}
    (h : n + m = mb ∧ JacobiRoundInvariant f b false (s, n, m))
    (hr : m' % 2 = 1 ∧ m' ≤ m ∧ m' ≤ n ∧ s' * J(m' | n) = t * J(m | n) ∧
      Nat.gcd m' n = Nat.gcd m n)
    (hr' : n' % 2 = 1 ∧ n' ≤ n ∧ n' ≤ m' ∧ s'' * J(n' | m') = t' * J(n | m') ∧
      Nat.gcd n' m' = Nat.gcd n m')
    (heq : (m' == n') = true) (ht : t = if (n &&& m &&& 2 != 0) = true then -s else s)
    (ht' : t' = if (n &&& m' &&& 2 != 0) = true then -s' else s') :
    JacobiRoundInvariant f b true (s'', n', m') := by
  obtain ⟨h1, h2⟩ := JacobiRoundInvariant.second_half h hr hr' ht (by rwa [Nat.and_comm m' n])
  exact ⟨hr'.1, hr.1, h1, h2, fun _ ↦ (by simpa using heq : m' = n').symm⟩

theorem JacobiRoundInvariant.next {f b n m m' n' mb : ℕ} {s s' s'' t t' : ℤ}
    (h : n + m = mb ∧ JacobiRoundInvariant f b false (s, n, m))
    (hr : m' % 2 = 1 ∧ m' ≤ m ∧ m' ≤ n ∧ s' * J(m' | n) = t * J(m | n) ∧
      Nat.gcd m' n = Nat.gcd m n)
    (hne : ¬(m' == n) = true)
    (hr' : n' % 2 = 1 ∧ n' ≤ n ∧ n' ≤ m' ∧ s'' * J(n' | m') = t' * J(n | m') ∧
      Nat.gcd n' m' = Nat.gcd n m')
    (ht : t = if (n &&& m &&& 2 != 0) = true then -s else s)
    (ht' : t' = if (n &&& m' &&& 2 != 0) = true then -s' else s') :
    n' + m' < mb ∧ JacobiRoundInvariant f b false (s'', n', m') := by
  obtain ⟨h1, h2⟩ := JacobiRoundInvariant.second_half h hr hr' ht (by rwa [Nat.and_comm m' n])
  have : m' ≠ n := by simpa using hne
  exact ⟨by have := h.1; lia, hr'.1, hr.1, h1, h2, nofun⟩

section

/- The invariants are irreducible here: the verification conditions of
`Ratpoints.Sieve.jacobiRound` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] JacobiRoundHalveInvariant JacobiRoundInvariant

/-- A round of the binary algorithm on `f > 0` and the odd `b` gives their gcd, with the symbol
`J(f | b)` when it is `1`; its main loop ends, since `n + m` drops with every pass. -/
@[spec]
theorem jacobiRound_spec (f b : ℕ) :
    ⦃ 0 < f ∧ b % 2 = 1 ⦄ jacobiRound f b
    ⦃ fun r ↦ r.1 = Nat.gcd f b ∧ (r.1 = 1 → r.2 = J(f | b)) ⦄ := by
  vcgen [jacobiRound] invariants
  | inv1 => JacobiRoundHalveInvariant f b
  | inv2 => .ofMeasure fun st : ℤ × ℕ ↦ st.2
  | inv3 => JacobiRoundInvariant f b
  | inv4 => .ofMeasure fun st : ℤ × ℕ × ℕ ↦ st.2.1 + st.2.2
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals first
    | exact jacobiRoundHalveInvariant_one ‹_›
    | exact JacobiRoundHalveInvariant.div_two ‹_› ‹_› ‹_›
    | exact JacobiRoundHalveInvariant.exit ‹_› ‹_›
    | exact JacobiRoundHalveInvariant.jacobiRoundInvariant ‹_› ‹_›
    | exact JacobiRoundInvariant.post ‹_›
    | exact JacobiRoundInvariant.odd ‹_›
    | exact JacobiRoundInvariant.odd_of_mod_two_eq_one ‹_› (And.left ‹_›)
    | exact JacobiRoundInvariant.first_break ‹_› ‹_› ‹_› (by simp [*])
    | exact JacobiRoundInvariant.second_break ‹_› ‹_› ‹_› ‹_› (by simp [*]) (by simp [*])
    | exact JacobiRoundInvariant.next ‹_› ‹_› ‹_› ‹_› (by simp [*]) (by simp [*])

end

-- A prime factor of `m` is not prime to `m`.
private theorem decide_coprime_eq_false {q m : ℕ} (hq : q.Prime) (h : q ∣ m) :
    decide (q.Coprime m) = false :=
  decide_eq_false fun hc ↦ (Nat.Prime.coprime_iff_not_dvd hq).mp hc h

/-- The invariant of the loop of `Ratpoints.Sieve.jacobi` that takes the factors `2` out of `b`:
the current `b'` is positive with the part of `b` prime to `2 lcf`, and odd at the exit. -/
def JacobiOddInvariant (b : ℕ) (lcf : ℤ) : Std.WP.WhileInvariant ℕ Prop :=
  .mk fun exit b' ↦ 0 < b' ∧
    (b'.primeFactorsList.filter (·.Coprime (2 * lcf.natAbs))).prod =
      (b.primeFactorsList.filter (·.Coprime (2 * lcf.natAbs))).prod ∧ (exit = true → b' % 2 = 1)

/-- The invariant of the main loop of `Ratpoints.Sieve.jacobi` on `b` and `lcf`, on the result of an
early return, the current `b'` and `f`: without a result, `b'` is odd and positive, `f < b'`,
`f ≡ lcf (mod b')`, the part of `b'` prime to `2 lcf` is that of `b`, and `f = 0` at the exit; a
result comes only at the exit and is the symbol `(lcf / b*)` of the part `b*` of `b` prime to
`2 lcf`. -/
def JacobiInvariant (b : ℕ) (lcf : ℤ) : Std.WP.WhileInvariant (Option ℤ × ℕ × ℕ) Prop :=
  .mk fun exit st ↦ st.1.elim (0 < st.2.1 ∧ st.2.1 % 2 = 1 ∧ st.2.2 < st.2.1 ∧
      (st.2.2 : ℤ) % st.2.1 = lcf % st.2.1 ∧
      (st.2.1.primeFactorsList.filter (·.Coprime (2 * lcf.natAbs))).prod =
        (b.primeFactorsList.filter (·.Coprime (2 * lcf.natAbs))).prod ∧
      (exit = true → st.2.2 = 0))
    fun r ↦ exit = true ∧ r = J(lcf | (b.primeFactorsList.filter (·.Coprime (2 * lcf.natAbs))).prod)

theorem jacobiOddInvariant_self {b : ℕ} (lcf : ℤ) (hb : 0 < b) :
    JacobiOddInvariant b lcf false b :=
  ⟨hb, rfl, nofun⟩

theorem JacobiOddInvariant.div_two {b b' mb : ℕ} {lcf : ℤ} (h : (b' % 2 == 0) = true)
    (hi : b' = mb ∧ JacobiOddInvariant b lcf false b') :
    b' / 2 < mb ∧ JacobiOddInvariant b lcf false (b' / 2) := by
  obtain ⟨rfl, h1, h2, -⟩ := hi
  have h : b' % 2 = 0 := by simpa using h
  refine ⟨by lia, by lia, ?_, nofun⟩
  rw [← h2, ← Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h), Nat.mul_div_cancel_left _ two_pos,
    Nat.prod_filter_primeFactorsList_mul_of_forall two_ne_zero (by lia)]
  simp [Nat.primeFactorsList_two]

theorem JacobiOddInvariant.exit {b b' mb : ℕ} {lcf : ℤ} (h : ¬(b' % 2 == 0) = true)
    (hi : b' = mb ∧ JacobiOddInvariant b lcf false b') : JacobiOddInvariant b lcf true b' :=
  ⟨hi.2.1, hi.2.2.1, fun _ ↦ by simpa using h⟩

theorem JacobiOddInvariant.jacobiInvariant {b b' : ℕ} {lcf : ℤ}
    (hi : JacobiOddInvariant b lcf true b') :
    JacobiInvariant b lcf false (none, b', (lcf % b').toNat) := by
  obtain ⟨h1, h2, h3⟩ := hi
  have h0 := Int.emod_nonneg lcf (b := b') (by lia)
  have hlt := Int.emod_lt_of_pos lcf (b := b') (by lia)
  refine ⟨h1, h3 rfl, by lia, ?_, h2, nofun⟩
  rw [Int.toNat_of_nonneg h0, Int.emod_emod]

theorem JacobiInvariant.post_some {b b' f : ℕ} {lcf r : ℤ} {o : Option ℤ}
    (hi : JacobiInvariant b lcf true (o, b', f)) (h : o = some r) :
    r = J(lcf | (b.primeFactorsList.filter (·.Coprime (2 * lcf.natAbs))).prod) := by
  subst h
  exact hi.2

/-- At the exit of `Ratpoints.Sieve.jacobi` without a result, `b' ∣ lcf`, so that the part of `b`
prime to `2 lcf`, that of `b'`, is `1`. -/
theorem JacobiInvariant.post_none {b b' f : ℕ} {lcf : ℤ} {o : Option ℤ}
    (hi : JacobiInvariant b lcf true (o, b', f)) (h : o = none) :
    1 = J(lcf | (b.primeFactorsList.filter (·.Coprime (2 * lcf.natAbs))).prod) := by
  subst h
  obtain ⟨h1, -, -, h4, h5, h6⟩ := hi
  have hd : (b' : ℤ) ∣ lcf := by
    rw [h6 rfl] at h4
    exact Int.dvd_of_emod_eq_zero (by simpa using h4.symm)
  rw [← h5, Nat.prod_filter_primeFactorsList_eq_one fun q hq ↦ decide_coprime_eq_false
    (Nat.prime_of_mem_primeFactorsList hq) (Dvd.dvd.mul_left (Int.natCast_dvd.mp
      ((Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mem_primeFactorsList hq)).trans hd)) 2),
    jacobiSym.one_right]

theorem JacobiInvariant.eq_none {b b' f : ℕ} {lcf : ℤ} {o : Option ℤ}
    (hi : JacobiInvariant b lcf false (o, b', f)) : o = none := by
  cases o
  · rfl
  · exact absurd hi.1 Bool.false_ne_true

theorem JacobiInvariant.pre {b b' f mb : ℕ} {lcf : ℤ} {o : Option ℤ} (hf : (f != 0) = true)
    (hi : b' = mb ∧ JacobiInvariant b lcf false (o, b', f)) : 0 < f ∧ b' % 2 = 1 := by
  obtain rfl := hi.2.eq_none
  exact ⟨by simpa [Nat.pos_iff_ne_zero] using hf, hi.2.2.1⟩

theorem JacobiInvariant.exit {b b' f mb : ℕ} {lcf : ℤ} {o : Option ℤ} (hf : ¬(f != 0) = true)
    (hi : b' = mb ∧ JacobiInvariant b lcf false (o, b', f)) :
    JacobiInvariant b lcf true (none, b', f) := by
  obtain rfl := hi.2.eq_none
  obtain ⟨h1, h2, h3, h4, h5, -⟩ := hi.2
  exact ⟨h1, h2, h3, h4, h5, fun _ ↦ by simpa using hf⟩

/-- When `gcd(f, b') = 1`, the symbol of the round is `J(lcf | b')`, and `b'` is the part of `b`
prime to `2 lcf`, being odd and prime to `lcf`. -/
theorem JacobiInvariant.exit_some {b b' f g mb : ℕ} {lcf s : ℤ} {o : Option ℤ}
    (hr : g = Nat.gcd f b' ∧ (g = 1 → s = J(f | b'))) (hg : (g == 1) = true)
    (hi : b' = mb ∧ JacobiInvariant b lcf false (o, b', f)) :
    JacobiInvariant b lcf true (some s, b', f) := by
  obtain rfl := hi.2.eq_none
  obtain ⟨h1, h2, -, h4, h5, -⟩ := hi.2
  have hg : g = 1 := by simpa using hg
  have hl := Int.gcd_emod f b'
  rw [h4, Int.gcd_emod, Int.gcd_natCast_natCast, ← hr.1, hg] at hl
  have hc : Nat.Coprime b' (2 * lcf.natAbs) := Nat.Coprime.mul_right
    (Nat.coprime_two_right.mpr (Nat.odd_iff.mpr h2)) (Nat.Coprime.symm hl)
  refine ⟨rfl, ?_⟩
  rw [hr.2 hg, ← h5, Nat.prod_filter_primeFactorsList_eq_self (by lia) fun q hq ↦
    decide_eq_true (hc.coprime_dvd_left (Nat.dvd_of_mem_primeFactorsList hq))]
  exact jacobiSym.mod_left' h4

/-- Dividing `b'` by `g = gcd(f, b') > 1` keeps the part of `b'` prime to `2 lcf`, since the primes
of `g` divide `lcf`, and `f ≡ lcf` modulo the quotient, which stays odd. -/
theorem JacobiInvariant.div_gcd {b b' f g f' mb : ℕ} {lcf s : ℤ} {o : Option ℤ}
    (hf : (f != 0) = true) (hr : g = Nat.gcd f b' ∧ (g = 1 → s = J(f | b')))
    (hg : ¬(g == 1) = true) (hi : b' = mb ∧ JacobiInvariant b lcf false (o, b', f))
    (hf' : f' = if b' / g ≤ f then f % (b' / g) else f) :
    b' / g < mb ∧ JacobiInvariant b lcf false (none, b' / g, f') := by
  obtain rfl := hi.2.eq_none
  obtain ⟨rfl, h1, h2, -, h4, h5, -⟩ := hi
  have hgb : g ∣ b' := hr.1 ▸ Nat.gcd_dvd_right f b'
  have hg2 : 1 < g := by
    have := hr.1 ▸ Nat.gcd_pos_of_pos_left b' (Nat.pos_of_ne_zero (by simpa using hf))
    have : g ≠ 1 := by simpa using hg
    lia
  have hq : 0 < b' / g := Nat.div_pos (Nat.le_of_dvd h1 hgb) (by lia)
  have hd : ((b' / g : ℕ) : ℤ) ∣ b' := Int.natCast_dvd_natCast.mpr (Nat.div_dvd_of_dvd hgb)
  refine ⟨Nat.div_lt_self h1 hg2, hq,
    Nat.odd_iff.mp ((Nat.odd_iff.mpr h2).of_dvd_nat (Nat.div_dvd_of_dvd hgb)), ?_, ?_, ?_, nofun⟩
  · split_ifs at hf' <;> subst hf' <;> [exact Nat.mod_lt _ hq; lia]
  · rw [← Int.emod_emod_of_dvd lcf hd, ← h4, Int.emod_emod_of_dvd _ hd]
    split_ifs at hf' <;> subst hf' <;> simp
  · rw [← h5, ← Nat.mul_div_cancel' hgb, Nat.mul_div_cancel_left _ (by lia),
      Nat.prod_filter_primeFactorsList_mul_of_forall (by lia) (by lia) fun q hq' ↦
        decide_coprime_eq_false (Nat.prime_of_mem_primeFactorsList hq')
          (Dvd.dvd.mul_left (Int.dvd_natAbs_of_dvd_gcd h4
            (hr.1 ▸ Nat.dvd_of_mem_primeFactorsList hq')) 2)]

section

/- The invariants are irreducible here: the verification conditions of `Ratpoints.Sieve.jacobi`
are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] JacobiOddInvariant JacobiInvariant

/-- **The binary algorithm.** `jacobi b lcf` is the Jacobi symbol `(lcf / b*)` for `b ≥ 1`, `b*` the
largest divisor of `b` prime to `2 lcf`; its main loop ends, since every round that does not return
divides `b` by a gcd above `1`. -/
@[spec]
theorem jacobi_spec (b : ℕ) (lcf : ℤ) :
    ⦃ 0 < b ⦄ jacobi b lcf
    ⦃ fun r ↦ r = J(lcf | (b.primeFactorsList.filter (·.Coprime (2 * lcf.natAbs))).prod) ⦄ := by
  vcgen [jacobi] invariants
  | inv1 => JacobiOddInvariant b lcf
  | inv2 => .ofMeasure fun st : ℕ ↦ st
  | inv3 => JacobiInvariant b lcf
  | inv4 => .ofMeasure fun st ↦ st.2.1
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals first
    | exact jacobiOddInvariant_self lcf ‹_›
    | exact JacobiOddInvariant.div_two ‹_› ‹_›
    | exact JacobiOddInvariant.exit ‹_› ‹_›
    | exact JacobiOddInvariant.jacobiInvariant ‹_›
    | exact JacobiInvariant.post_some ‹_› ‹_›
    | exact JacobiInvariant.post_none ‹_› ‹_›
    | exact JacobiInvariant.pre ‹_› ‹_›
    | exact JacobiInvariant.exit_some ‹_› ‹_› ‹_›
    | exact JacobiInvariant.exit ‹_› ‹_›
    | exact JacobiInvariant.div_gcd ‹_› ‹_› ‹_› ‹_›
        (by first | exact (ite_eq_left ‹_›).symm | exact (ite_eq_right ‹_›).symm)

end

theorem run_jacobi {b : ℕ} (hb : b ≠ 0) (lcf : ℤ) :
    Id.run (jacobi b lcf) =
      J(lcf | (b.primeFactorsList.filter (·.Coprime (2 * lcf.natAbs))).prod) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((jacobi_spec b lcf).le_wp (Nat.pos_of_ne_zero hb))

/-! ### The denominators of the points -/

/-- **Soundness of every form of the Jacobi test.** For a point `(a, y, b)` of a curve of even
degree, every divisor `b'` of `b` prime to the leading coefficient `c_d` has `J(c_d | b') = 1`: a
prime `q ∣ b'` divides `b`, so `c_d` is a square modulo `q`
(`Ratpoints.Sieve.isSquare_getD_degree_of_sq_eq_binaryForm`), and a Jacobi symbol `-1` would have a
prime factor `q` with `J(c_d | q) = -1` (`jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one`). -/
theorem jacobiSym_eq_one_of_sq_eq_binaryForm {c : List ℤ} {a y : ℤ} {b b' : ℕ}
    (hab : Int.gcd a b = 1) (hd : degree c % 2 = 0) (hy : y ^ 2 = binaryForm c a b)
    (hb' : b' ∣ b) (hc : Int.gcd (c.getD (degree c) 0) b' = 1) :
    J(c.getD (degree c) 0 | b') = 1 := by
  refine (jacobiSym.eq_one_or_neg_one hc).resolve_right fun h ↦ ?_
  obtain ⟨q, hq, hqb', hJ⟩ := jacobiSym.eq_neg_one_at_prime_divisor_of_eq_neg_one h
  have : Fact q.Prime := ⟨hq⟩
  exact ZMod.nonsquare_iff_jacobiSym_eq_neg_one.mp hJ <|
    isSquare_getD_degree_of_sq_eq_binaryForm hab (Nat.mod_eq_zero_of_dvd (hqb'.trans hb')) hd hy

/-- The symbol `(c_d / b*)` of the largest divisor `b*` of the denominator `b` of a point prime to
`2 c_d` is `1`, for even degree. -/
theorem jacobiSym_prod_filter_primeFactorsList_eq_one_of_sq_eq {c : List ℤ}
    (hd : degree c % 2 = 0) {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) :
    J(c.getD (degree c) 0 | (b.primeFactorsList.filter
      (·.Coprime (2 * (c.getD (degree c) 0).natAbs))).prod) = 1 :=
  jacobiSym_eq_one_of_sq_eq_binaryForm hab hd hy (Nat.prod_filter_primeFactorsList_dvd _ _)
    ((Nat.coprime_prod_filter_primeFactorsList b _).coprime_dvd_right (dvd_mul_left _ 2)).symm

/-- The binary algorithm gives the symbol `1` on the denominator `b` of every point of a curve of
even degree: it computes the Jacobi symbol `(c_d / b*)`, and modulo a prime `q ∣ b` with `q ∤ c_d`,
`c_d` is the square of `y / a ^ (d / 2)`. -/
theorem run_jacobi_eq_one_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 0) {a y : ℤ} {b : ℕ}
    (hb : b ≠ 0) (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    Id.run (jacobi b (c.getD (degree c) 0)) = 1 :=
  (run_jacobi hb _).trans (jacobiSym_prod_filter_primeFactorsList_eq_one_of_sq_eq hd hab hy)

end Sieve

end Ratpoints

end
