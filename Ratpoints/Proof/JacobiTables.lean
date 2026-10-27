/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
public import Ratpoints.Mathlib.Data.Nat.Factors
public import Ratpoints.Model.Denominators
public import Ratpoints.Spec.Basic
public import Std.WP

import Ratpoints.Mathlib.Algebra.BigOperators.Group.List.Basic
import Ratpoints.Mathlib.Data.List.Prime
import Ratpoints.Mathlib.Data.Nat.PadicValNat
import Ratpoints.Mathlib.Data.ZMod.Basic
import Ratpoints.Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Jacobi
import Ratpoints.Proof.Params
import Ratpoints.Proof.Stages
import Ratpoints.Proof.Valuation
import Std.Tactic.Do

/-!
# The Jacobi test by tables

The test by tables (`Ratpoints.Sieve.jacobiSetup`, `Ratpoints.Sieve.jacobiTest`) computes the symbol
of the binary algorithm, `(lcf / b*)` for `1 ≤ b ≤ bHigh`, where `b*` is the largest divisor of `b`
prime to `2 lcf`: it takes `2` and the odd primes of `lcf` out of `b` and reads the symbol off the
sign of `b* mod 8` and the tables of the non-squares modulo the primes of `lcf` with an odd
exponent, by quadratic reciprocity. The proof has two layers: the contracts describe the loops, the
tables of the non-squares giving the Legendre symbol, the set-up the tables of `lcf`
(`Ratpoints.Sieve.IsJacobiInfo`) and the test the exclusive or of the sign and the entries over the
part of `b` free of `2` and of the primes of the tables; and
`Ratpoints.Sieve.jacobiSym_eq_ite_foldl` reads the Jacobi symbol off the tables. So the test lets
the denominator of every point of a curve of even degree through. The set-up gives tables only for
`bHigh ≤ Ratpoints.mulModLimit`, so that the denominators of the test stay below `2 ^ 32`, where
`RP_MULDIV` with the reciprocals that the tables hold, those of their primes, is exact
(`Ratpoints.Sieve.run_jacobiTest`).

## Main definitions

* `Ratpoints.Sieve.IsJacobiInfo`: what the tables of the test by tables say of the leading
  coefficient.

## Main statements

* `Ratpoints.Sieve.nonSquares_spec`, `Ratpoints.Sieve.legendreSym_eq_ite_getElem!_nonSquares`: the
  tables of the non-squares give the Legendre symbol; `Ratpoints.Sieve.ite_getElem!_jacobiSigns`:
  the signs.
* `Ratpoints.Sieve.jacobiSetup_spec`, `Ratpoints.Sieve.jacobiTest_spec`: the contracts of the
  set-up, whose tables hold primes of `Ratpoints.primeTable` with their reciprocals, and of the test
  by tables.
* `Ratpoints.Sieve.jacobiSym_eq_ite_foldl`: the Jacobi symbol read off the tables.
* `Ratpoints.Sieve.run_jacobiTest`: the test by tables decides whether `(lcf / b*) = 1`.
* `Ratpoints.Sieve.run_jacobiTest_of_sq_eq`: the test by tables passes the denominator of every
  point of a curve of even degree.

## Implementation notes

The contracts are proved with `vcgen`, with loop invariants that are named definitions, in a file
with Mathlib, since they speak of primes, their valuations and the Legendre symbol. A contract that
needs the exact value of a component that its loop calls takes a specification
`⦃True⦄ x ⦃fun r ↦ r = Id.run x⦄` of it (`Ratpoints.Setup.valuation_value` for the valuation, a
private one for the table of the non-squares), since the registered contract would give only what it
says of the value. The test reduces by the reciprocals that the tables hold, which the set-up makes
those of their primes, and the reductions are exact (`Ratpoints.Sieve.mulDiv_magic`), since these
are primes of `Ratpoints.primeTable`, below `1022`, and the denominators are at most
`Ratpoints.mulModLimit < 2 ^ 32` (`Ratpoints.mul_lt_two_pow_64_of_le_mulModLimit`). The proofs use
only that `Ratpoints.mulModLimit` is below `2 ^ 64` and `2 ^ 32` (`Ratpoints.mulModLimit_lt_size`,
`Ratpoints.mulModLimit_lt_two_pow_32`, which `decide` checks next to the constant), never the values
of `Ratpoints.mulModLimit`, `Ratpoints.jacobiPrimes` and `Ratpoints.jacobiTable`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP NumberTheorySymbols

namespace Ratpoints

namespace Sieve

/-! ### The tables of the non-squares and the signs -/

/-- The invariant of the loop of `Ratpoints.Sieve.nonSquares` on `q` after the steps `x ≤ k`, `k`
the length of `pref`: the table has `q` entries, `s = (k + 1) ^ 2 mod q`, and an entry `r < q` is
false exactly when `r = x ^ 2 mod q` for some `1 ≤ x ≤ k`. -/
def NonSquaresInvariant (q : ℕ) (pref : List ℕ) (st : Array Bool × ℕ) : Prop :=
  st.1.size = q ∧ st.2 = (pref.length + 1) * (pref.length + 1) % q ∧
    ∀ r < q, (st.1[r]! = false ↔ ∃ x, 1 ≤ x ∧ x ≤ pref.length ∧ x * x % q = r)

theorem nonSquaresInvariant_nil {q : ℕ} (hq : q % 2 = 1 ∧ 1 < q) :
    NonSquaresInvariant q [] (Array.replicate q true, 1) := by
  refine ⟨by simp, by simp [Nat.mod_eq_of_lt hq.2], fun r hr ↦ ?_⟩
  simp only [List.length_nil, Nat.le_zero,
    getElem!_pos (Array.replicate q true) r (by simpa using hr), Array.getElem_replicate,
    Bool.true_eq_false, false_iff, not_exists, not_and]
  intro x hx h0
  lia

theorem NonSquaresInvariant.size_eq_and_getElem!_eq_false_iff {q s : ℕ} {ns : Array Bool}
    (h : NonSquaresInvariant q (ForIn.toList [1:q / 2 + 1]) (ns, s)) :
    ns.size = q ∧ ∀ r < q, (ns[r]! = false ↔ ∃ x, 1 ≤ x ∧ x ≤ q / 2 ∧ x * x % q = r) :=
  ⟨h.1, by simpa only [Std.Legacy.Range.length_toList, Nat.add_sub_cancel] using h.2.2⟩

/-- The step `x` of `Ratpoints.Sieve.nonSquares` clears the entry of `s = x ^ 2 mod q` and moves on
to `(x + 1) ^ 2 mod q = s + 2 x + 1`, less `q` at most once, since `2 x + 1 ≤ q` for odd `q`. -/
theorem NonSquaresInvariant.set! {q cur s s' : ℕ} {pref suff : List ℕ} {ns : Array Bool}
    (hq : q % 2 = 1 ∧ 1 < q) (hl : ForIn.toList [1:q / 2 + 1] = pref ++ cur :: suff)
    (h : NonSquaresInvariant q pref (ns, s))
    (hs : s' = if q ≤ s + 2 * cur + 1 then s + 2 * cur + 1 - q else s + 2 * cur + 1) :
    NonSquaresInvariant q (pref ++ [cur]) (ns.set! s false, s') := by
  simp only [NonSquaresInvariant, List.length_append, List.length_singleton] at h ⊢
  obtain ⟨h1, h2, h3⟩ := h
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hlen := Std.Legacy.Range.length_add_length_add_one_of_toList_eq_append_cons hl
  have hsq : s < q := h2 ▸ Nat.mod_lt _ (by lia)
  refine ⟨by simp [h1], ?_, fun r hr ↦ ?_⟩
  · rw [hs, ← Nat.mod_eq_ite_of_lt_two_mul (by lia), h2, Nat.add_assoc, Nat.mod_add_mod]
    exact congr($(by rw [← hc]; ring) % q)
  have := h3 r hr
  rw [getElem!_pos _ r (by lia)] at this
  rw [Array.set!_eq_setIfInBounds, getElem!_pos _ r (by simpa [h1] using hr),
    Array.getElem_setIfInBounds (by lia)]
  split_ifs with hsr
  · simpa only [true_iff] using ⟨pref.length + 1, by lia, le_rfl, by rw [← h2, hsr]⟩
  rw [this]
  refine ⟨fun ⟨x, h1, h2, h3⟩ ↦ ⟨x, h1, by lia, h3⟩, fun ⟨x, hx1, hx2, hx3⟩ ↦ ⟨x, hx1, ?_, hx3⟩⟩
  by_contra hx
  obtain rfl : x = pref.length + 1 := by lia
  exact hsr (h2.trans hx3)

/-- The table of the non-squares modulo an odd `q > 1` has `q` entries, an entry `r < q` being false
exactly when `r` is the square modulo `q` of one of `1, …, q / 2`. -/
@[spec]
theorem nonSquares_spec (q : ℕ) :
    ⦃ q % 2 = 1 ∧ 1 < q ⦄ nonSquares q
    ⦃ fun ns ↦ ns.size = q ∧
        ∀ r < q, (ns[r]! = false ↔ ∃ x, 1 ≤ x ∧ x ≤ q / 2 ∧ x * x % q = r) ⦄ := by
  vcgen [nonSquares] invariants
  | inv1 => fun pref _ st ↦ NonSquaresInvariant q pref st
  all_goals first
    | exact nonSquaresInvariant_nil ‹_›
    | exact NonSquaresInvariant.size_eq_and_getElem!_eq_false_iff ‹_›
    | exact NonSquaresInvariant.set! ‹_› ‹_› ‹_›
        (by first | exact (ite_eq_left ‹_›).symm | exact (ite_eq_right ‹_›).symm)

/-- The table of `Ratpoints.Sieve.nonSquares` gives the Legendre symbol of a residue `r ≠ 0` modulo
an odd prime `q`: its entry is true exactly where the symbol is `-1`. -/
theorem legendreSym_eq_ite_getElem!_nonSquares {q r : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hr0 : r ≠ 0) (hr : r < q) :
    legendreSym q r = if (Id.run (nonSquares q))[r]! then -1 else 1 := by
  have hodd := hq.out.eq_two_or_odd.resolve_left hq2
  have hns := (Std.WP.Id.of_run_eq_wp rfl _ ((nonSquares_spec q).le_wp
    ⟨hodd, hq.out.one_lt⟩)).2 r hr
  rw [← ZMod.isSquare_natCast_iff_exists_mul_self_mod_eq hodd hr0 hr] at hns
  cases h : (Id.run (nonSquares q))[r]!
  · have hr' : (r : ZMod q) ≠ 0 := by
      rw [Ne, ZMod.natCast_eq_zero_iff]
      exact fun hd ↦ hr0 (Nat.eq_zero_of_dvd_of_lt hd hr)
    exact (legendreSym.eq_one_iff' q hr').mpr (hns.mp h)
  · exact (legendreSym.eq_neg_one_iff' q).mpr fun hs ↦ by simp [hns.mpr hs] at h

-- The sign of an exclusive or, read as `-1` for true.
private theorem ite_xor_eq_mul (a b : Bool) :
    (if (a ^^ b) = true then (-1 : ℤ) else 1) =
      (if a = true then -1 else 1) * (if b = true then -1 else 1) := by
  cases a <;> cases b <;> simp

-- The sign of `c ∧ k odd`, read as `-1` for true.
private theorem ite_and_mod_two_eq (c : Bool) (k : ℕ) :
    (if (c && k % 2 == 1) = true then (-1 : ℤ) else 1) = if c = true then (-1) ^ k else 1 := by
  cases c
  · simp
  · rw [neg_one_pow_eq_pow_mod_two]
    rcases Nat.mod_two_eq_zero_or_one k with h | h <;> simp [h]

/-- The signs of `Ratpoints.Sieve.jacobiSigns` for odd `b`: the entry of `b mod 8`, read as `-1` for
true, is `χ₄(b) ^ (n₃ + neg) χ₈(b) ^ v`, the product of the signs of `(-1 / b) ^ neg`, of the
reciprocity of the `n₃` primes `≡ 3 (mod 4)` and of `(2 / b) ^ v`. -/
theorem ite_getElem!_jacobiSigns {b : ℕ} (hb : b % 2 = 1) (n3 : ℕ) (neg : Bool) (v : ℕ) :
    (if (jacobiSigns n3 neg v)[b % 8]! then (-1 : ℤ) else 1) =
      ZMod.χ₄ b ^ (n3 + if neg then 1 else 0) * ZMod.χ₈ b ^ v := by
  rw [jacobiSigns, Array.getElem!_map_range _ (Nat.mod_lt _ (by decide)), ite_xor_eq_mul,
    ite_and_mod_two_eq, ite_and_mod_two_eq, ZMod.χ₄_nat_eq_if_mod_four, ZMod.χ₈_nat_eq_if_mod_eight]
  obtain h | h | h | h : b % 8 = 1 ∨ b % 8 = 3 ∨ b % 8 = 5 ∨ b % 8 = 7 := by lia
  all_goals simp [h, show b % 4 = b % 8 % 4 by lia, hb]

/-! ### The set-up of the tables -/

/-- What the tables `ji` of the Jacobi test say of the leading coefficient `lcf`
(`Ratpoints.Sieve.jacobiSetup`): its primes are odd primes of `lcf`, each with the table of the
non-squares modulo it (`Ratpoints.Sieve.nonSquares`) exactly when its exponent in `lcf` is odd;
`|lcf|` is `2 ^ v₂(lcf)` times the powers of these primes with their exponents in `lcf`; and the
signs are those of `Ratpoints.Sieve.jacobiSigns` for the number of these primes with an odd
exponent that are `3 (mod 4)`, the sign of `lcf` and `v₂(lcf)`. -/
def IsJacobiInfo (lcf : ℤ) (ji : JacobiInfo) : Prop :=
  (∀ x ∈ ji.primes, x.1.Prime ∧ x.1 ≠ 2 ∧ x.1 ∣ lcf.natAbs ∧
    x.2 = if padicValNat x.1 lcf.natAbs % 2 = 1 then some (Id.run (nonSquares x.1)) else none) ∧
  lcf.natAbs = 2 ^ padicValNat 2 lcf.natAbs *
    (ji.primes.map fun x ↦ x.1 ^ padicValNat x.1 lcf.natAbs).prod ∧
  ji.sign = jacobiSigns (ji.primes.filter fun x ↦ x.2.isSome && x.1 &&& 2 != 0).length
    (decide (lcf < 0)) (padicValNat 2 lcf.natAbs)

/-- The invariant of the loop of `Ratpoints.Sieve.jacobiSetup` on `lcf` with the exponent `v` of `2`
in it, on the cofactor `w` and the entries `qs`: for `lcf = 0`, `w = 0`; otherwise `|lcf|` is
`2 ^ v w` times the powers of the primes of `qs` with their exponents in `lcf`, `w` is odd, and the
entries are odd primes of `lcf` from `Ratpoints.primeTable` that do not divide `w`, each with the
table of the non-squares exactly when its exponent in `lcf` is odd. -/
def JacobiSetupInvariant (lcf : ℤ) (v w : ℕ) (qs : Array (ℕ × Option (Array Bool))) : Prop :=
  (lcf = 0 → w = 0) ∧ (lcf ≠ 0 →
    lcf.natAbs = 2 ^ v * w * (qs.toList.map fun x ↦ x.1 ^ padicValNat x.1 lcf.natAbs).prod ∧
    w % 2 = 1 ∧ ∀ x ∈ qs.toList, x.1 ∈ primeTable ∧ x.1 ≠ 2 ∧ x.1 ∣ lcf.natAbs ∧ ¬x.1 ∣ w ∧
      x.2 = if padicValNat x.1 lcf.natAbs % 2 = 1 then some (Id.run (nonSquares x.1)) else none)

theorem jacobiSetupInvariant_empty {lcf : ℤ} {v r : ℕ}
    (hv : (v, r) = Id.run (Setup.valuation lcf 2)) :
    JacobiSetupInvariant lcf v (lcf.natAbs / 2 ^ v) #[] := by
  refine ⟨fun h ↦ by simp [h], fun h ↦ ?_⟩
  obtain rfl : v = padicValNat 2 lcf.natAbs := by
    rw [← Setup.fst_run_valuation h Nat.one_lt_two, ← hv]
  have hd : 2 ^ padicValNat 2 lcf.natAbs ∣ lcf.natAbs := pow_padicValNat_dvd
  refine ⟨by simp [Nat.mul_div_cancel' hd], ?_, by simp⟩
  rw [← Nat.factorization_def _ Nat.prime_two]
  exact Nat.two_dvd_ne_zero.mp (Nat.not_dvd_ordCompl Nat.prime_two (by simpa using h))

/-- The invariant of the loop of `Ratpoints.Sieve.jacobiSetup` over the primes of the table, with
the primes `suff` still to come, on the result of an early return, the cofactor, the entries, the
reciprocals, the number `n3` and the space taken by the tables: without a result,
`Ratpoints.Sieve.JacobiSetupInvariant` of the cofactor and the entries, with the reciprocals those
of the primes of the entries in their order (`Ratpoints.Sieve.magic`) and `n3` the number of the
entries with a table whose prime is `3 (mod 4)`; and a result, which is `none`, only at the end. -/
def JacobiSetupLoopInvariant (lcf : ℤ) (v : ℕ) (suff : List ℕ)
    (st : Option (Option JacobiInfo) × ℕ × Array (ℕ × Option (Array Bool)) × Array ℕ × ℕ × ℕ) :
    Prop :=
  st.1.elim (JacobiSetupInvariant lcf v st.2.1 st.2.2.1 ∧
      st.2.2.2.1.toList = st.2.2.1.toList.map (fun x ↦ magic x.1) ∧
      st.2.2.2.2.1 = (st.2.2.1.toList.filter fun x ↦ x.2.isSome && x.1 &&& 2 != 0).length)
    fun r ↦ suff = [] ∧ r = none

theorem jacobiSetupLoopInvariant_empty {lcf : ℤ} {v r : ℕ}
    (hv : (v, r) = Id.run (Setup.valuation lcf 2)) (suff : List ℕ) (u : ℕ) :
    JacobiSetupLoopInvariant lcf v suff (none, lcf.natAbs / 2 ^ v, #[], #[], 0, u) :=
  ⟨jacobiSetupInvariant_empty hv, rfl, rfl⟩

theorem jacobiSetupLoopInvariant_some_none (lcf : ℤ) (v w n3 u : ℕ)
    (qs : Array (ℕ × Option (Array Bool))) (ms : Array ℕ) :
    JacobiSetupLoopInvariant lcf v [] (some none, w, qs, ms, n3, u) :=
  ⟨rfl, rfl⟩

/-- Before the last prime, the loop of `Ratpoints.Sieve.jacobiSetup` has not returned, and its state
passes on unchanged to any primes to come. -/
theorem JacobiSetupLoopInvariant.of_cons {lcf : ℤ} {v w n3 u cur : ℕ}
    {qs : Array (ℕ × Option (Array Bool))} {ms : Array ℕ} {suff suff' : List ℕ}
    {o : Option (Option JacobiInfo)}
    (h : JacobiSetupLoopInvariant lcf v (cur :: suff) (o, w, qs, ms, n3, u)) :
    JacobiSetupLoopInvariant lcf v suff' (none, w, qs, ms, n3, u) := by
  cases o with
  | none => exact h
  | some r => exact absurd h.1 (List.cons_ne_nil _ _)

theorem JacobiSetupInvariant.dvd_natAbs {lcf : ℤ} {v w : ℕ}
    {qs : Array (ℕ × Option (Array Bool))} (h : JacobiSetupInvariant lcf v w qs) (h0 : lcf ≠ 0) :
    w ∣ lcf.natAbs := by
  obtain ⟨h1, -, -⟩ := h.2 h0
  refine ⟨2 ^ v * (qs.toList.map fun x ↦ x.1 ^ padicValNat x.1 lcf.natAbs).prod, ?_⟩
  nth_rw 1 [h1]
  ring

/-- The exponent `e` of a prime `q` of the cofactor `w = q ^ e m`, `q ∤ m`, is `v_q(lcf)`, since `q`
is neither `2` nor one of the primes taken out before. -/
theorem JacobiSetupInvariant.padicValNat_eq {lcf : ℤ} {v w q e m : ℕ}
    {qs : Array (ℕ × Option (Array Bool))} (h0 : lcf ≠ 0) (h : JacobiSetupInvariant lcf v w qs)
    (hq : q.Prime) (hm : w = q ^ e * m) (hqm : ¬q ∣ m) (hqw : q ∣ w) :
    padicValNat q lcf.natAbs = e := by
  obtain ⟨h1, h2, h3⟩ := h.2 h0
  have h2q : ¬q ∣ 2 := fun hd ↦ by
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_two).mp hd
    lia
  have hP : ¬q ∣ (qs.toList.map fun x ↦ x.1 ^ padicValNat x.1 lcf.natAbs).prod :=
    hq.prime.not_dvd_prod_map_pow fun x hx ↦
      ⟨(prime_of_mem_primeTable (h3 x hx).1).prime, fun he ↦ (h3 x hx).2.2.2.1 (he ▸ hqw)⟩
  refine padicValNat_eq_of_eq_pow_mul_of_not_dvd hq.ne_zero ?_ (hq.prime.not_dvd_mul
    (hq.prime.not_dvd_mul hqm (mt (hq.prime.dvd_of_dvd_pow (n := v)) h2q)) hP)
  nth_rw 1 [h1, hm]
  ring

/-- An entry `(q, ns)` for a prime `q` of the cofactor `w = q ^ e m`, `q ∤ m`, with its exponent
`e = v_q(lcf)` and the table of the non-squares exactly for odd `e`, leaves the cofactor `m`. -/
theorem JacobiSetupInvariant.push {lcf : ℤ} {v w cur e r : ℕ} {pref suff : List ℕ}
    {qs : Array (ℕ × Option (Array Bool))} {ns : Option (Array Bool)}
    (hl : ForIn.toList primeTable = pref ++ cur :: suff) (h : JacobiSetupInvariant lcf v w qs)
    (hw : ¬(w % cur != 0) = true) (he : (e, r) = Id.run (Setup.valuation (w : ℤ) cur))
    (hns : ns = if e % 2 = 1 then some (Id.run (nonSquares cur)) else none) :
    JacobiSetupInvariant lcf v (w / cur ^ e) (qs.push (cur, ns)) := by
  refine ⟨fun h0 ↦ by simp [h.1 h0], fun h0 ↦ ?_⟩
  obtain ⟨h1, h2, h3⟩ := h.2 h0
  have hmem := Array.mem_of_forIn_toList_eq_append_cons hl
  have hcur : cur.Prime := prime_of_mem_primeTable hmem
  have hw0 : w ≠ 0 := by rintro rfl; simp at h1; lia
  obtain ⟨m, hm, hcm⟩ := Setup.exists_eq_of_eq_run_valuation hw0 hcur.one_lt he
  have hcw : cur ∣ w := Nat.dvd_of_mod_eq_zero (by simpa using hw)
  have hv := h.padicValNat_eq h0 hcur hm hcm hcw
  have hmw : m ∣ w := hm ▸ dvd_mul_left m _
  rw [Nat.div_eq_of_eq_mul_right (Nat.pow_pos hcur.pos) hm]
  refine ⟨?_, Nat.odd_iff.mp ((Nat.odd_iff.mpr h2).of_dvd_nat hmw), fun x hx ↦ ?_⟩
  · simp only [Array.toList_push, List.map_append, List.map_cons, List.map_nil, List.prod_append,
      List.prod_cons, List.prod_nil, Nat.mul_one, hv]
    nth_rw 1 [h1, hm]
    ring
  rcases List.mem_append.mp (Array.toList_push ▸ hx) with hx | hx
  · exact ⟨(h3 x hx).1, (h3 x hx).2.1, (h3 x hx).2.2.1, fun hd ↦ (h3 x hx).2.2.2.1 (hd.trans hmw),
      (h3 x hx).2.2.2.2⟩
  obtain rfl := List.mem_singleton.mp hx
  exact ⟨hmem, fun h2' ↦ by subst h2'; lia, hcw.trans (h.dvd_natAbs h0), hcm, by rwa [hv]⟩

/-- An entry for the prime `cur` of the table that divides the cofactor `w`, with the table of the
non-squares exactly for an odd exponent `e`, and the count `n3` of the entries with a table whose
prime is `3 (mod 4)`; the space `u'` taken by the tables is free. -/
theorem JacobiSetupLoopInvariant.push {lcf : ℤ} {v w n3 n3' u u' cur e r : ℕ} {pref suff : List ℕ}
    {qs : Array (ℕ × Option (Array Bool))} {ms : Array ℕ} {o : Option (Option JacobiInfo)}
    {ns : Option (Array Bool)} (hl : ForIn.toList primeTable = pref ++ cur :: suff)
    (h : JacobiSetupLoopInvariant lcf v (cur :: suff) (o, w, qs, ms, n3, u))
    (hw : ¬(w % cur != 0) = true) (he : (e, r) = Id.run (Setup.valuation (w : ℤ) cur))
    (hns : ns = if e % 2 = 1 then some (Id.run (nonSquares cur)) else none)
    (hn3 : n3' = n3 + if (ns.isSome && cur &&& 2 != 0) = true then 1 else 0) :
    JacobiSetupLoopInvariant lcf v suff
      (none, w / cur ^ e, qs.push (cur, ns), ms.push (magic cur), n3', u') := by
  have h' := h.of_cons (suff' := suff)
  exact ⟨h'.1.push hl hw he hns, by simpa using h'.2.1, by
    have h3 : n3 = _ := h'.2.2
    simp [hn3, h3, List.filter_singleton, apply_ite List.length]⟩

theorem JacobiSetupLoopInvariant.false_of_some {lcf : ℤ} {v w n3 u : ℕ}
    {qs : Array (ℕ × Option (Array Bool))} {ms : Array ℕ} {o : Option (Option JacobiInfo)}
    {a : Option JacobiInfo} {ji : JacobiInfo}
    (h : JacobiSetupLoopInvariant lcf v [] (o, w, qs, ms, n3, u)) (ho : o = some a)
    (ha : a = some ji) : False := by
  subst ho ha
  exact Option.some_ne_none ji h.2

/-- At the end of the loop of `Ratpoints.Sieve.jacobiSetup` with the cofactor `1`, `lcf ≠ 0`, the
tables are those of `lcf`, their primes are from `Ratpoints.primeTable`, and they hold the
reciprocals of their primes. -/
theorem JacobiSetupLoopInvariant.isJacobiInfo {lcf : ℤ} {bHigh v r w n3 u : ℕ}
    {qs : Array (ℕ × Option (Array Bool))} {ms : Array ℕ} {o : Option (Option JacobiInfo)}
    {ji : JacobiInfo} (hb : ¬mulModLimit < bHigh) (hv : (v, r) = Id.run (Setup.valuation lcf 2))
    (h : JacobiSetupLoopInvariant lcf v [] (o, w, qs, ms, n3, u)) (ho : o = none)
    (hw : ¬(w != 1) = true)
    (hji : some ⟨qs.toList, ms, jacobiSigns n3 (decide (lcf < 0)) v⟩ = some ji) :
    bHigh ≤ mulModLimit ∧ lcf ≠ 0 ∧ IsJacobiInfo lcf ji ∧ (∀ x ∈ ji.primes, x.1 ∈ primeTable) ∧
      ji.magic.toList = ji.primes.map fun x ↦ magic x.1 := by
  subst ho
  obtain ⟨h, hms, hn3⟩ := h
  obtain rfl : w = 1 := by simpa using hw
  have h0 : lcf ≠ 0 := fun h0 ↦ one_ne_zero (h.1 h0)
  obtain ⟨h1, -, h3⟩ := h.2 h0
  obtain rfl : v = padicValNat 2 lcf.natAbs := by
    rw [← Setup.fst_run_valuation h0 Nat.one_lt_two, ← hv]
  obtain rfl := Option.some.inj hji
  refine ⟨Nat.le_of_not_lt hb, h0, ⟨fun x hx ↦ ?_, by simpa using h1, congr(jacobiSigns $hn3 _ _)⟩,
    fun x hx ↦ (h3 x hx).1, hms⟩
  exact ⟨prime_of_mem_primeTable (h3 x hx).1, (h3 x hx).2.1, (h3 x hx).2.2.1, (h3 x hx).2.2.2.2⟩

-- The table of the non-squares, as a value for the contract of the set-up.
private theorem nonSquares_value (q : ℕ) :
    ⦃ True ⦄ nonSquares q ⦃ fun r ↦ r = Id.run (nonSquares q) ⦄ :=
  ⟨fun _ ↦ rfl⟩

section

/- The invariant is irreducible here, and so are the table of primes, the valuation and the table
of the non-squares, whose unfolding in a failed unification of the dispatch does not end. -/
attribute [local irreducible] JacobiSetupInvariant JacobiSetupLoopInvariant primeTable
  Setup.valuation nonSquares

/-- The set-up of the test by tables gives tables only for `bHigh ≤ Ratpoints.mulModLimit` and
`lcf ≠ 0`, and then the tables of `lcf` (`Ratpoints.Sieve.IsJacobiInfo`), whose primes are from
`Ratpoints.primeTable` and which hold their reciprocals, so that the reductions of the test by them
are exact. -/
@[spec]
theorem jacobiSetup_spec (lcf : ℤ) (bHigh : ℕ) :
    ⦃ True ⦄ jacobiSetup lcf bHigh
    ⦃ fun r ↦ ∀ ji, r = some ji → bHigh ≤ mulModLimit ∧ lcf ≠ 0 ∧ IsJacobiInfo lcf ji ∧
        (∀ x ∈ ji.primes, x.1 ∈ primeTable) ∧
        ji.magic.toList = ji.primes.map fun x ↦ magic x.1 ⦄ := by
  vcgen [jacobiSetup, Setup.valuation_value, nonSquares_value] invariants
  | inv1 => fun _ suff st ↦ JacobiSetupLoopInvariant lcf v suff st
  all_goals try dsimp only at *
  all_goals first
    | exact jacobiSetupLoopInvariant_empty ‹_› _ _
    | exact JacobiSetupLoopInvariant.of_cons ‹_›
    | exact jacobiSetupLoopInvariant_some_none _ _ _ _ _ _ _
    | exact (nomatch ‹none = some _›)
    | exact (JacobiSetupLoopInvariant.false_of_some ‹_› ‹_› ‹_›).elim
    | exact JacobiSetupLoopInvariant.isJacobiInfo ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact JacobiSetupLoopInvariant.push ‹_› ‹_› ‹_› ‹_› (by simp_all) (by simp_all)

end

/-! ### The test by tables -/

/-- The precondition of `Ratpoints.Sieve.jacobiTest` on the tables `ji` and the denominator `b`,
under which the reductions by the reciprocals that the tables hold are exact. -/
structure JacobiTestPre (ji : JacobiInfo) (b : ℕ) : Prop where
  /-- The denominator is positive. -/
  pos : 0 < b
  /-- The denominator is below `2 ^ 64`. -/
  lt_size : b < UInt64.size
  /-- The entries are primes `q` with `b q < 2 ^ 64`. -/
  prime_mul_lt : ∀ x ∈ ji.primes, x.1.Prime ∧ b * x.1 < 2 ^ 64
  /-- The tables hold the reciprocals of their primes. -/
  magic_eq : ji.magic.toList = ji.primes.map fun x ↦ magic x.1

/-- The invariant of the first loop of `Ratpoints.Sieve.jacobiTest` on the tables `ji` and the
denominator `b`, after the entries `pref`: the current `b'` is odd and positive, has the part of `b`
free of `2` and of the primes of `ji`, is prime to the primes of `pref`, and is at most `b`, so that
the reductions by the reciprocals of the primes stay exact (`Ratpoints.Sieve.mulDiv_magic`). -/
def JacobiTestInvariant (ji : JacobiInfo) (b : ℕ) (pref : List (ℕ × Option (Array Bool)))
    (b' : ℕ) : Prop :=
  0 < b' ∧ b' % 2 = 1 ∧
    (b'.primeFactorsList.filter fun p ↦ decide (p ≠ 2 ∧ p ∉ ji.primes.map Prod.fst)).prod =
      (b.primeFactorsList.filter fun p ↦ decide (p ≠ 2 ∧ p ∉ ji.primes.map Prod.fst)).prod ∧
    (∀ x ∈ pref, ¬x.1 ∣ b') ∧ b' ≤ b

/-- The invariant of the loop of `Ratpoints.Sieve.jacobiTest` that divides `b'` by the prime `q` as
often as it divides: that of the first loop, and `q ∤ b'` at the exit. -/
def JacobiDivideInvariant (ji : JacobiInfo) (b : ℕ) (pref : List (ℕ × Option (Array Bool)))
    (q : ℕ) : Std.WP.WhileInvariant ℕ Prop :=
  .mk fun exit b' ↦ JacobiTestInvariant ji b pref b' ∧ (exit = true → ¬q ∣ b')

theorem jacobiTestInvariant_nil {ji : JacobiInfo} {b t : ℕ}
    (h : JacobiTestPre ji b) (ht : t = (UInt64.ofNat b).toBitVec.ctz.toNat) :
    JacobiTestInvariant ji b [] (b >>> t) := by
  have h1 := UInt64.two_pow_ctz_mul_shiftRight_ofNat h.pos h.lt_size
  have h2 := UInt64.shiftRight_ctz_ofNat_mod_two h.pos h.lt_size
  rw [← ht] at h1 h2
  refine ⟨by lia, h2, ?_, by simp, Nat.shiftRight_le b t⟩
  conv_rhs => rw [← h1]
  rw [Nat.prod_filter_primeFactorsList_mul_of_forall (by simp) fun q hq ↦ ?_]
  rw [Nat.prime_two.primeFactorsList_pow] at hq
  simp [List.eq_of_mem_replicate hq]

/-- The quotient by the prime `q` of the entry at the position `i` of the tables `ji`, by the
reciprocal that the tables hold there, is exact for the current `b' ≤ b`, since `b q < 2 ^ 64`. -/
theorem JacobiTestInvariant.mulDiv_getElem!_magic {ji : JacobiInfo} {b b' q i : ℕ}
    {o : Option (Array Bool)} {pref : List (ℕ × Option (Array Bool))}
    {pref' suff' : List ((ℕ × Option (Array Bool)) × ℕ)} (hpre : JacobiTestPre ji b)
    (hl : ji.primes.zipIdx = pref' ++ ((q, o), i) :: suff') (h : JacobiTestInvariant ji b pref b') :
    mulDiv b' ji.magic[i]! = b' / q := by
  have hmem : ((q, o), i) ∈ ji.primes.zipIdx := by simp [hl]
  have hq := hpre.prime_mul_lt _ (List.fst_mem_of_mem_zipIdx hmem)
  have hm : ji.magic[i]! = magic q := by rw [← Array.getElem!_toList, hpre.magic_eq]; grind
  exact hm ▸ mulDiv_magic hq.1.one_lt (Nat.lt_of_le_of_lt (Nat.mul_le_mul_right q h.2.2.2.2) hq.2)

/-- The remainder by the prime `q` of the entry at the position `i` of the tables `ji`, by the
reciprocal that the tables hold there, is exact for the current `b' ≤ b`, since `b q < 2 ^ 64`. -/
theorem JacobiTestInvariant.sub_mulDiv_getElem!_magic_mul {ji : JacobiInfo} {b b' q i : ℕ}
    {o : Option (Array Bool)} {pref : List (ℕ × Option (Array Bool))}
    {pref' suff' : List ((ℕ × Option (Array Bool)) × ℕ)} (hpre : JacobiTestPre ji b)
    (hl : ji.primes.zipIdx = pref' ++ ((q, o), i) :: suff') (h : JacobiTestInvariant ji b pref b') :
    b' - mulDiv b' ji.magic[i]! * q = b' % q := by
  rw [h.mulDiv_getElem!_magic hpre hl, Nat.mod_eq_sub_div_mul]

/-- At the end of the first loop of `Ratpoints.Sieve.jacobiTest`, `b'` is the part of `b` free of
`2` and of the primes of the tables. -/
theorem JacobiTestInvariant.eq_prod_filter {ji : JacobiInfo} {b b' : ℕ}
    (h : JacobiTestInvariant ji b ji.primes b') :
    b' = (b.primeFactorsList.filter fun p ↦ decide (p ≠ 2 ∧ p ∉ ji.primes.map Prod.fst)).prod := by
  obtain ⟨h1, h2, h3, h4, -⟩ := h
  rw [← h3, Nat.prod_filter_primeFactorsList_eq_self (by lia) fun q hq ↦ ?_]
  have hqb := Nat.dvd_of_mem_primeFactorsList hq
  refine decide_eq_true ⟨fun hq2 ↦ by subst hq2; lia, fun hm ↦ ?_⟩
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
  exact h4 x hx hqb

/-- The invariant of the second loop of `Ratpoints.Sieve.jacobiTest` on the tables `ji` and the
odd part `b'` free of their primes, after the entries `pref`: the sign `s` is the exclusive or of
the sign of `b' mod 8` and the entries of `b' mod q` in the tables of the primes `q` of `pref`. -/
def JacobiTestSignInvariant (ji : JacobiInfo) (b' : ℕ) (pref : List (ℕ × Option (Array Bool)))
    (s : Bool) : Prop :=
  s = pref.foldl (fun s x ↦ x.2.elim s fun ns ↦ s ^^ ns[b' % x.1]!) ji.sign[b' % 8]!

theorem jacobiTestSignInvariant_nil (ji : JacobiInfo) (b' : ℕ) :
    JacobiTestSignInvariant ji b' [] ji.sign[b' % 8]! :=
  rfl

theorem JacobiTestSignInvariant.not_eq_not_foldl {ji : JacobiInfo} {b b' : ℕ} {s : Bool}
    (h : JacobiTestInvariant ji b ji.primes b') (hs : JacobiTestSignInvariant ji b' ji.primes s) :
    (!s) = !(ji.primes.foldl (fun s x ↦ x.2.elim s fun ns ↦ s ^^ ns[(b.primeFactorsList.filter
      fun p ↦ decide (p ≠ 2 ∧ p ∉ ji.primes.map Prod.fst)).prod % x.1]!)
      ji.sign[(b.primeFactorsList.filter
        fun p ↦ decide (p ≠ 2 ∧ p ∉ ji.primes.map Prod.fst)).prod % 8]!) := by
  rw [hs, ← h.eq_prod_filter]

theorem JacobiTestSignInvariant.append_some {ji : JacobiInfo} {b b' q i : ℕ} {s : Bool}
    {pref : List (ℕ × Option (Array Bool))} {pref' suff' : List ((ℕ × Option (Array Bool)) × ℕ)}
    {o : Option (Array Bool)} {ns : Array Bool} (hpre : JacobiTestPre ji b)
    (hb : JacobiTestInvariant ji b ji.primes b')
    (hl : ji.primes.zipIdx = pref' ++ ((q, o), i) :: suff')
    (hs : JacobiTestSignInvariant ji b' pref s) (ho : o = some ns) :
    JacobiTestSignInvariant ji b' (pref ++ [(q, o)])
      (s ^^ ns[b' - mulDiv b' ji.magic[i]! * q]!) := by
  simp only [JacobiTestSignInvariant, hb.sub_mulDiv_getElem!_magic_mul hpre hl] at hs ⊢
  subst hs ho
  simp

theorem JacobiTestSignInvariant.append_none {ji : JacobiInfo} {b' q : ℕ} {s : Bool}
    {pref : List (ℕ × Option (Array Bool))} {o o' : Option (Array Bool)}
    (hs : JacobiTestSignInvariant ji b' pref s) (hn : ∀ ns, o' = some ns → False) (ho : o = o') :
    JacobiTestSignInvariant ji b' (pref ++ [(q, o)]) s := by
  simp only [JacobiTestSignInvariant] at hs ⊢
  subst hs ho
  cases o with
  | none => simp
  | some ns => exact (hn ns rfl).elim

theorem JacobiTestInvariant.jacobiDivideInvariant {ji : JacobiInfo} {b b' q : ℕ}
    {pref : List (ℕ × Option (Array Bool))} (h : JacobiTestInvariant ji b pref b') :
    JacobiDivideInvariant ji b pref q false b' :=
  ⟨h, nofun⟩

theorem JacobiDivideInvariant.exit {ji : JacobiInfo} {b b' q i mb : ℕ}
    {pref : List (ℕ × Option (Array Bool))} {pref' suff' : List ((ℕ × Option (Array Bool)) × ℕ)}
    {o : Option (Array Bool)} (hpre : JacobiTestPre ji b)
    (hl : ji.primes.zipIdx = pref' ++ ((q, o), i) :: suff')
    (hq : (b' - mulDiv b' ji.magic[i]! * q != 0) = true)
    (h : b' = mb ∧ JacobiDivideInvariant ji b pref q false b') :
    JacobiDivideInvariant ji b pref q true b' := by
  rw [h.2.1.sub_mulDiv_getElem!_magic_mul hpre hl] at hq
  exact ⟨h.2.1, fun _ hd ↦ by simp [Nat.mod_eq_zero_of_dvd hd] at hq⟩

theorem JacobiDivideInvariant.jacobiTestInvariant {ji : JacobiInfo} {b b' q : ℕ}
    {pref : List (ℕ × Option (Array Bool))} {o : Option (Array Bool)}
    (h : JacobiDivideInvariant ji b pref q true b') :
    JacobiTestInvariant ji b (pref ++ [(q, o)]) b' := by
  obtain ⟨⟨h1, h2, h3, h4, hb⟩, h5⟩ := h
  refine ⟨h1, h2, h3, fun x hx ↦ ?_, hb⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h4 x hx
  · obtain rfl := List.mem_singleton.mp hx
    exact h5 rfl

/-- Dividing `b'` by a prime `q` of the tables keeps the part of `b'` free of `2` and of the primes
of the tables. -/
theorem JacobiDivideInvariant.div {ji : JacobiInfo} {b b' q i mb : ℕ} {o : Option (Array Bool)}
    {pref : List (ℕ × Option (Array Bool))} {pref' suff' : List ((ℕ × Option (Array Bool)) × ℕ)}
    (hpre : JacobiTestPre ji b) (hl : ji.primes.zipIdx = pref' ++ ((q, o), i) :: suff')
    (hq : ¬(b' - mulDiv b' ji.magic[i]! * q != 0) = true)
    (h : b' = mb ∧ JacobiDivideInvariant ji b pref q false b') :
    mulDiv b' ji.magic[i]! < mb ∧
      JacobiDivideInvariant ji b pref q false (mulDiv b' ji.magic[i]!) := by
  rw [h.2.1.sub_mulDiv_getElem!_magic_mul hpre hl] at hq
  rw [h.2.1.mulDiv_getElem!_magic hpre hl]
  obtain ⟨rfl, ⟨h1, h2, h3, h4, hb⟩, -⟩ := h
  have hmem : ((q, o), i) ∈ ji.primes.zipIdx := by simp [hl]
  have hqp : q.Prime := (hpre.prime_mul_lt _ (List.fst_mem_of_mem_zipIdx hmem)).1
  have hqb : q ∣ b' := Nat.dvd_of_mod_eq_zero (by simpa using hq)
  have hpos : 0 < b' / q := Nat.div_pos (Nat.le_of_dvd h1 hqb) hqp.pos
  refine ⟨Nat.div_lt_self h1 hqp.one_lt, ⟨hpos,
    Nat.odd_iff.mp ((Nat.odd_iff.mpr h2).of_dvd_nat (Nat.div_dvd_of_dvd hqb)), ?_,
    fun x hx hd ↦ h4 x hx (hd.trans (Nat.div_dvd_of_dvd hqb)), (Nat.div_le_self b' q).trans hb⟩,
    nofun⟩
  rw [← h3, ← Nat.mul_div_cancel' hqb, Nat.mul_div_cancel_left _ hqp.pos,
    Nat.prod_filter_primeFactorsList_mul_of_forall hqp.ne_zero fun r hr ↦ ?_]
  rw [Nat.primeFactorsList_prime hqp, List.mem_singleton] at hr
  subst hr
  exact decide_eq_false fun hc ↦ hc.2 (List.mem_map.mpr ⟨_, List.fst_mem_of_mem_zipIdx hmem, rfl⟩)

section

/- The invariants are irreducible here: the verification conditions of
`Ratpoints.Sieve.jacobiTest` are closed by their lemmas, never by unfolding them. -/
attribute [local irreducible] JacobiTestInvariant JacobiDivideInvariant JacobiTestSignInvariant

/-- The test by tables on `0 < b < 2 ^ 64`, for tables whose entries are primes `q` with
`b q < 2 ^ 64` and which hold the reciprocals of their primes, so that the reductions by them are
exact: the exclusive or of the sign of `b* mod 8` and the entries of `b* mod q` in the tables of the
primes `q`, negated, for `b*` the part of `b` free of `2` and of the primes of the tables. -/
@[spec]
theorem jacobiTest_spec (ji : JacobiInfo) (b : ℕ) :
    ⦃ JacobiTestPre ji b ⦄ jacobiTest ji b
    ⦃ fun r ↦ r = !(ji.primes.foldl (fun s x ↦ x.2.elim s fun ns ↦
        s ^^ ns[(b.primeFactorsList.filter
          fun p ↦ decide (p ≠ 2 ∧ p ∉ ji.primes.map Prod.fst)).prod % x.1]!)
        ji.sign[(b.primeFactorsList.filter
          fun p ↦ decide (p ≠ 2 ∧ p ∉ ji.primes.map Prod.fst)).prod % 8]!) ⦄ := by
  vcgen [jacobiTest] invariants
  | inv1 => fun pref _ b' ↦ JacobiTestInvariant ji b (pref.map Prod.fst) b'
  | inv2 b' _ => fun pref _ s ↦ JacobiTestSignInvariant ji b' (pref.map Prod.fst) s
  | inv3 pref q _ _ _ _ _ _ => JacobiDivideInvariant ji b (pref.map Prod.fst) q
  | inv4 => .ofMeasure fun b' : ℕ ↦ b'
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq, List.map_append, List.map_cons,
    List.map_nil, List.zipIdx_map_fst] at *
  all_goals first
    | exact UInt64.ofNat_ne_zero_of_lt ‹JacobiTestPre _ _›.pos ‹JacobiTestPre _ _›.lt_size
    | exact jacobiTestInvariant_nil ‹_› ‹_›
    | exact jacobiTestSignInvariant_nil _ _
    | exact JacobiTestSignInvariant.not_eq_not_foldl ‹_› ‹_›
    | exact JacobiTestSignInvariant.append_some ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact JacobiTestSignInvariant.append_none ‹_› ‹_› ‹_›
    | exact JacobiTestInvariant.jacobiDivideInvariant ‹_›
    | exact JacobiDivideInvariant.jacobiTestInvariant ‹_›
    | exact JacobiDivideInvariant.exit ‹_› ‹_› ‹_› ‹_›
    | exact JacobiDivideInvariant.div ‹_› ‹_› ‹_› ‹_›

end

/-! ### The Jacobi symbol by the tables -/

theorem ite_foldl_xor_eq_mul_prod {b : ℕ} (L : List (ℕ × Option (Array Bool))) (s : Bool) :
    (if L.foldl (fun s x ↦ x.2.elim s fun ns ↦ s ^^ ns[b % x.1]!) s then (-1 : ℤ) else 1) =
      (if s then -1 else 1) *
        (L.map fun x ↦ x.2.elim 1 fun ns ↦ if ns[b % x.1]! then -1 else 1).prod := by
  induction L generalizing s with
  | nil => exact (mul_one _).symm
  | cons x L ih =>
    rw [List.foldl_cons, ih, List.map_cons, List.prod_cons, ← mul_assoc]
    congr 1
    rcases x with ⟨q, _ | ns⟩
    · exact (mul_one _).symm
    · exact ite_xor_eq_mul _ _

/-- The factor `J(q | b) ^ e` of an odd prime `q ∤ b` of the leading coefficient with its exponent
`e`, for odd `b`: `1` for even `e`, and for odd `e`, with the table `ns` of the non-squares modulo
`q`, the entry of `b mod q` read as a sign, times `χ₄(b)` when `q ≡ 3 (mod 4)`. -/
theorem jacobiSym_pow_eq_mul {q b e : ℕ} {o : Option (Array Bool)} [hq : Fact q.Prime]
    (hq2 : q ≠ 2) (hb : b % 2 = 1) (hqb : ¬q ∣ b)
    (ho : o = if e % 2 = 1 then some (Id.run (nonSquares q)) else none) :
    J(q | b) ^ e = (if (o.isSome && q &&& 2 != 0) = true then ZMod.χ₄ b else 1) *
      o.elim 1 fun ns ↦ if ns[b % q]! = true then -1 else 1 := by
  have hqo : q % 2 = 1 := hq.out.eq_two_or_odd.resolve_left hq2
  have hJ := jacobiSym.eq_one_or_neg_one (a := q) (b := b)
    (by simpa using hq.out.coprime_iff_not_dvd.mpr hqb)
  rcases Nat.mod_two_eq_zero_or_one e with he | he
  · simp only [he, zero_ne_one, ↓reduceIte] at ho
    subst ho
    rcases hJ with h | h <;> simp [h, (Nat.even_iff.mpr he).neg_one_pow]
  simp only [he, ↓reduceIte] at ho
  subst ho
  have hr : b % q ≠ 0 := fun h ↦ hqb (Nat.dvd_of_mod_eq_zero h)
  have hJe : J(q | b) ^ e = J(q | b) := by
    rcases hJ with h | h <;> simp [h, (Nat.odd_iff.mpr he).neg_one_pow]
  rw [hJe, jacobiSym.natCast_eq_ite_mul_legendreSym hq2 hb, legendreSym.mod, ← Int.natCast_mod,
    legendreSym_eq_ite_getElem!_nonSquares hq2 hr (Nat.mod_lt _ hq.out.pos),
    ZMod.χ₄_nat_eq_if_mod_four]
  simp only [Option.isSome_some, Bool.true_and, Nat.and_two_ne_zero_iff hqo, Option.elim_some]
  split_ifs <;> first | rfl | lia

-- For odd `b`, the sign of `a` comes out of `J(a | b)` as a power of `χ₄(b)`.
private theorem jacobiSym_eq_χ₄_pow_mul_natAbs (a : ℤ) {b : ℕ} (hb : b % 2 = 1) :
    J(a | b) = ZMod.χ₄ b ^ (if a < 0 then 1 else 0) * J(a.natAbs | b) := by
  rcases lt_or_ge a 0 with h | h
  · nth_rw 1 [Int.eq_neg_natAbs_of_nonpos h.le]
    simp [jacobiSym.neg _ (Nat.odd_iff.mpr hb), h]
  · simp [h.not_gt, Int.natAbs_of_nonneg h]

theorem jacobiSym_natAbs_eq_mul_prod {lcf : ℤ} {v b : ℕ} {L : List (ℕ × Option (Array Bool))}
    (h : lcf.natAbs = 2 ^ v * (L.map fun x ↦ x.1 ^ padicValNat x.1 lcf.natAbs).prod)
    (hb : b % 2 = 1) :
    J(lcf.natAbs | b) =
      ZMod.χ₈ b ^ v * (L.map fun x ↦ J(x.1 | b) ^ padicValNat x.1 lcf.natAbs).prod := by
  nth_rw 1 [h]
  push_cast
  rw [jacobiSym.mul_left, jacobiSym.pow_left, jacobiSym.at_two (Nat.odd_iff.mpr hb),
    jacobiSym.list_prod_left]
  simp [List.map_map, Function.comp_def, jacobiSym.pow_left]

theorem prod_map_jacobiSym_pow_eq {lcf : ℤ} {L : List (ℕ × Option (Array Bool))}
    (h : ∀ x ∈ L, x.1.Prime ∧ x.1 ≠ 2 ∧ x.1 ∣ lcf.natAbs ∧
      x.2 = if padicValNat x.1 lcf.natAbs % 2 = 1 then some (Id.run (nonSquares x.1)) else none)
    {b : ℕ} (hb : b % 2 = 1) (hq : ∀ x ∈ L, ¬x.1 ∣ b) :
    (L.map fun x ↦ J(x.1 | b) ^ padicValNat x.1 lcf.natAbs).prod =
      ZMod.χ₄ b ^ (L.filter fun x ↦ x.2.isSome && x.1 &&& 2 != 0).length *
        (L.map fun x ↦ x.2.elim 1 fun ns ↦ if ns[b % x.1]! = true then -1 else 1).prod := by
  rw [← List.prod_map_ite_eq_pow, ← List.prod_map_mul]
  refine congr(List.prod $(List.map_congr_left fun x hx ↦ ?_))
  have : Fact x.1.Prime := ⟨(h x hx).1⟩
  exact jacobiSym_pow_eq_mul (h x hx).2.1 hb (hq x hx) (h x hx).2.2.2

/-- **The Jacobi symbol by the tables.** The symbol `(lcf / b)` of an odd `b` prime to the primes of
the tables `ji` of `lcf` is read off the tables, by quadratic reciprocity: the exclusive or of the
sign of `b mod 8` and the entries of `b mod q` in the tables of the primes `q` with an odd exponent,
read as `-1` for true. -/
theorem jacobiSym_eq_ite_foldl {lcf : ℤ} {ji : JacobiInfo} (hji : IsJacobiInfo lcf ji) {b : ℕ}
    (hb : b % 2 = 1) (hq : ∀ x ∈ ji.primes, ¬x.1 ∣ b) :
    J(lcf | b) = if ji.primes.foldl (fun s x ↦ x.2.elim s fun ns ↦ s ^^ ns[b % x.1]!)
      ji.sign[b % 8]! = true then -1 else 1 := by
  obtain ⟨h1, h2, h3⟩ := hji
  rw [ite_foldl_xor_eq_mul_prod, h3, ite_getElem!_jacobiSigns hb,
    jacobiSym_eq_χ₄_pow_mul_natAbs lcf hb, jacobiSym_natAbs_eq_mul_prod h2 hb,
    prod_map_jacobiSym_pow_eq h1 hb hq]
  simp only [decide_eq_true_eq]
  ring

/-- For the tables of `lcf`, the primes prime to `2 lcf` are those other than `2` and the primes of
the tables, which are all the odd primes of `lcf`. -/
theorem IsJacobiInfo.coprime_two_mul_natAbs_iff {lcf : ℤ} {ji : JacobiInfo}
    (hji : IsJacobiInfo lcf ji) {p : ℕ} (hp : p.Prime) :
    p.Coprime (2 * lcf.natAbs) ↔ p ≠ 2 ∧ p ∉ ji.primes.map Prod.fst := by
  rw [hp.coprime_iff_not_dvd]
  refine ⟨fun h ↦ ⟨fun h2 ↦ h (by subst h2; exact dvd_mul_right 2 _), fun hm ↦ ?_⟩,
    fun ⟨h2, hm⟩ hd ↦ ?_⟩
  · obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hm
    exact h ((hji.1 x hx).2.2.1.mul_left 2)
  have h2' : ¬p ∣ 2 := fun h ↦ h2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h)
  rw [hji.2.1, ← mul_assoc, ← pow_succ'] at hd
  rcases hp.dvd_mul.mp hd with hd | hd
  · exact h2' (hp.dvd_of_dvd_pow hd)
  obtain ⟨a, ha, hpa⟩ := hp.prime.dvd_prod_iff.mp hd
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp ha
  exact hm (List.mem_map.mpr ⟨x, hx,
    ((Nat.prime_dvd_prime_iff_eq hp (hji.1 x hx).1).mp (hp.dvd_of_dvd_pow hpa)).symm⟩)

theorem IsJacobiInfo.prod_filter_primeFactorsList_eq {lcf : ℤ} {ji : JacobiInfo}
    (hji : IsJacobiInfo lcf ji) (b : ℕ) :
    (b.primeFactorsList.filter fun p ↦ decide (p ≠ 2 ∧ p ∉ ji.primes.map Prod.fst)).prod =
      b.coprimePart (2 * lcf.natAbs) :=
  congr(List.prod $(List.filter_congr fun _ hp ↦ decide_eq_decide.mpr
    (hji.coprime_two_mul_natAbs_iff (Nat.prime_of_mem_primeFactorsList hp)).symm))

/-- **The test by tables.** It decides whether `(lcf / b*) = 1`, `b*` the largest divisor of `b`
prime to `2 lcf`, for `1 ≤ b ≤ bHigh` when the set-up gives tables. The C code refuses the tables
for a `b_high` above `Ratpoints.mulModLimit`, `RP_MULMOD_LIMIT` (`find_points.c:688`), so that
`jacobi_test` divides only numbers below `2 ^ 32`, where its multiplication by the reciprocal
`RP_MULDIV` is exact (`rp-private.h:389-393`). -/
theorem run_jacobiTest {lcf : ℤ} {bHigh : ℕ} {ji : JacobiInfo}
    (hji : Id.run (jacobiSetup lcf bHigh) = some ji) {b : ℕ} (hb : b ≠ 0) (hbH : b ≤ bHigh) :
    Id.run (jacobiTest ji b) = decide (J(lcf | b.coprimePart (2 * lcf.natAbs)) = 1) := by
  obtain ⟨hH, -, hI, hT, hM⟩ :=
    (Std.WP.Id.of_run_eq_wp rfl _ ((jacobiSetup_spec lcf bHigh).le_wp trivial)) ji hji
  have hbs : b < UInt64.size := by lia [mulModLimit_lt_size]
  rw [Std.WP.Id.of_run_eq_wp rfl _ ((jacobiTest_spec ji b).le_wp
    ⟨Nat.pos_of_ne_zero hb, hbs, fun x hx ↦ ⟨(hI.1 x hx).1, mul_lt_two_pow_64_of_le_mulModLimit
      (hbH.trans hH) ((lt_of_mem_primeTable (hT x hx)).le.trans (by norm_num))⟩, hM⟩),
    hI.prod_filter_primeFactorsList_eq]
  have hc := Nat.coprime_coprimePart b (2 * lcf.natAbs)
  rw [jacobiSym_eq_ite_foldl hI (Nat.odd_iff.mp (Nat.coprime_two_right.mp
    (hc.coprime_dvd_right (dvd_mul_right 2 _)))) fun x hx hd ↦ (hI.1 x hx).1.one_lt.ne'
      ((hc.coprime_dvd_left hd).eq_one_of_dvd ((hI.1 x hx).2.2.1.mul_left 2))]
  cases List.foldl _ _ _ <;> simp

/-- The Jacobi test by the tables of the leading coefficient, when they apply, passes the
denominator `b ≤ bHigh` of every point of a curve of even degree: it computes whether the Jacobi
symbol `(c_d / b*)` is `1`. -/
theorem run_jacobiTest_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 0) {bHigh : ℕ} {ji : JacobiInfo}
    (hji : Id.run (jacobiSetup (c.getD (degree c) 0) bHigh) = some ji) {a y : ℤ} {b : ℕ}
    (hb : b ≠ 0) (hbH : b ≤ bHigh) (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    Id.run (jacobiTest ji b) = true :=
  (run_jacobiTest hji hb hbH).trans
    (decide_eq_true (jacobiSym_coprimePart_eq_one_of_sq_eq hd hab hy))

end Sieve

end Ratpoints

end
