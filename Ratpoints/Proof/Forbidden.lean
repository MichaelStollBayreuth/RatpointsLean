/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Defs
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Ratpoints.Model.Denominators
public import Ratpoints.Spec.Basic
public import Std.WP

import Ratpoints.Mathlib.Data.Int.GCD
import Ratpoints.Mathlib.Data.ZMod.Basic
import Ratpoints.Mathlib.NumberTheory.Padics.PadicVal.Basic
import Ratpoints.Proof.Bits
import Ratpoints.Proof.Params
import Ratpoints.Proof.Tables
import Ratpoints.Proof.Valuation
import Std.Tactic.Do

/-!
# The forbidden divisors

For a polynomial of even degree `d`, a point `(a, y, b)` with `m = v_p(b) ≥ 1` has the terms
`c_{d-j} a ^ (d - j) b ^ j` of `F(a, b)` of the valuations `w_j + j m` at `p`, where
`w_j = v_p(c_{d-j})`; when one of them alone has the least valuation, that valuation is even, and
for even `j` the unit part of `c_{d-j}` is a square modulo `p`
(`Ratpoints.even_and_isSquare_of_sq_eq_binaryForm_of_even`), the Newton polygon of the comment of
`forbidden_valuations`. So the valuations that `Ratpoints.Sieve.forbiddenAt` excludes, with the unit
parts of the coefficients (`Ratpoints.Sieve.unitParts`), are those of no denominator of a point, and
so are the bits of the mask of `Ratpoints.Sieve.forbiddenValuations`, the unit parts read from the
coefficients reduced modulo `p` that the table of `p` hands back. The forbidden divisors are
therefore sound, those that the loop of the tables records prime by prime from what each table hands
back (`Ratpoints.Sieve.examinePrimes`), the coefficients modulo `p` and the entry at infinity, and
those of the further primes (`Ratpoints.Sieve.forbidden`): a prime tested with words divides no
denominator `b ≤ bHigh` of a point, since the mask holds every valuation that such a denominator can
have (`Ratpoints.Sieve.allValuations`) or there are no points at infinity modulo `p`, that is `c_d`
is not a square modulo `p`, and its words are those of `Ratpoints.Sieve.forbiddenRow`, bit `j` of
word `r` clear exactly when `p ∣ 64 r + j`; a prime tested by its valuation excludes no denominator
of a point. The loop of the tables also keeps the table of every prime it examines, that of the
reference (`Ratpoints.Sieve.examinePrime`), and when it takes its exit, the curve has no points. The
masks, which the C code keeps in an `unsigned long`, stay below `2 ^ 40` for an odd prime and a
`long` `b_high`, so that its cap on the valuations never binds; the products `pm p` of its loops of
the valuations and the square `p p` of a prime of the table that its loop over the further primes
compares with `b_high` are `long`s (`Ratpoints.Setup.fitsLong_mul_of_le_div`,
`Ratpoints.Setup.mul_self_lt_of_mem_primeTable`).

## Main definitions

* `Ratpoints.Sieve.IsUnitPart`: what an entry of `Ratpoints.Sieve.unitParts` says of a coefficient.
* `Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`: the forbidden divisors of
  the primes of `Ratpoints.primeTable` that `Ratpoints.Sieve.examinePrimes` may record, tested with
  words or by their valuations, and those tested with words that `Ratpoints.Sieve.forbidden` may
  add.
* `Ratpoints.Sieve.ForbiddenVal.excludes`: whether a forbidden divisor tested by its valuation
  excludes a denominator.

## Main statements

* `Ratpoints.even_and_isSquare_of_sq_eq_binaryForm_of_even`: the Newton polygon at a prime.
* `Ratpoints.Sieve.unitParts_spec`, `Ratpoints.Sieve.forbiddenAt_spec`,
  `Ratpoints.Sieve.forbiddenValuations_spec`, `Ratpoints.Sieve.allValuations_spec`,
  `Ratpoints.Sieve.examinePrimes_spec`, `Ratpoints.Sieve.forbidden_spec`: the contracts of the
  forbidden divisors and of the loop of the tables.
* `Ratpoints.Sieve.run_forbiddenAt_eq_false_of_sq_eq`,
  `Ratpoints.Sieve.testBit_run_forbiddenValuations_eq_false_of_sq_eq`: no denominator of a point has
  a forbidden valuation.
* `Ratpoints.Sieve.getElem_eq_examinePrime_of_run_examinePrimes_eq_some`,
  `Ratpoints.Sieve.not_isPoint_of_run_examinePrimes_eq_none`: the tables that the loop of the tables
  keeps are those of the reference, and when it takes its exit, the curve has no points.
* `Ratpoints.Sieve.IsForbiddenEntry.prime`, `Ratpoints.Sieve.IsForbiddenEntry.words_eq`: the
  forbidden divisors tested with words are primes with the words of `Ratpoints.Sieve.forbiddenRow`.
* `Ratpoints.Sieve.IsForbiddenEntry.not_dvd`, `Ratpoints.Sieve.IsForbiddenVal.excludes_eq_false`:
  the forbidden divisors let the denominator of every point through.
* `Ratpoints.Sieve.getLsbD_getElem!_forbiddenRow`: the bits of the words of a forbidden divisor.
* `Ratpoints.Sieve.lt_forty_of_pow_le`, `Ratpoints.Sieve.run_forbiddenValuations_lt`,
  `Ratpoints.Sieve.run_allValuations_lt`: the cap of the loops of the valuations never binds, and
  the masks fit an `unsigned long`.

## Implementation notes

The contracts are proved with `vcgen`, the program logic of Lean core, with loop invariants that are
named definitions, in a file with Mathlib, since they speak of primes, their valuations and the
squares modulo a prime. A contract that needs the exact value of a component that its loop calls
takes a private specification `⦃True⦄ x ⦃fun r ↦ r = Id.run x⦄` of it, since the registered
contract would give only what it says of the value.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

/-! ### The Newton polygon at a prime -/

/-- The binary form of a polynomial of even degree `d` as the sum over the exponent `j` of `b`:
`F(a, b) = ∑ c_{d-j} a ^ (d - j) b ^ j`. -/
theorem binaryForm_eq_sum_of_even {c : List ℤ} (hd : degree c % 2 = 0) (a b : ℤ) :
    binaryForm c a b = ∑ j ∈ Finset.range (degree c + 1),
      c.getD (degree c - j) 0 * a ^ (degree c - j) * b ^ j := by
  rw [binaryForm, hd, Nat.add_zero, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun j hj ↦ ?_
  rw [Nat.add_sub_cancel, Nat.add_zero, Nat.sub_sub_self (Finset.mem_range_succ_iff.mp hj)]

-- An integer `u` such that `u x ^ 2 + p t` is a square, for an `x` prime to the prime `p`, is a
-- square modulo `p`, since `x` is a unit there.
private theorem isSquare_intCast_of_isSquare_mul_sq_add {p : ℕ} [Fact p.Prime] {u x t : ℤ}
    (hx : ¬(p : ℤ) ∣ x) (h : IsSquare (u * x ^ 2 + p * t)) : IsSquare (u : ZMod p) := by
  obtain ⟨z, hz⟩ := h
  have hz' := congr(($hz : ZMod p))
  push_cast at hz'
  rw [ZMod.natCast_self, zero_mul, add_zero] at hz'
  have hx0 : (x : ZMod p) ^ 2 ≠ 0 :=
    pow_ne_zero _ (by rwa [Ne, ZMod.intCast_zmod_eq_zero_iff_dvd])
  rw [eq_div_of_mul_eq hx0 hz']
  exact (IsSquare.mul_self _).div (IsSquare.sq _)

/-- **The Newton polygon at a prime `p`** (even degree): for a point `(a, y, b)` with
`m = v_p(b) ≥ 1`, whose term `c_{d-j} a ^ (d - j) b ^ j` of `F(a, b)` alone has the least
valuation `w + j m`, where `c_{d-j} = p ^ w u` with `p ∤ u` and `p ^ (w + j m + 1)` divides
`c_{d-i} p ^ (i m)` for every other `i ≤ d`, the valuation `w + j m` is even, and for even `j` the
unit part `u` is a square modulo `p`, since `a ^ (d - j)` and `(b / p ^ m) ^ j` then are. -/
theorem even_and_isSquare_of_sq_eq_binaryForm_of_even {c : List ℤ} {p : ℕ} [hp : Fact p.Prime]
    (hd : degree c % 2 = 0) {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) (hm : padicValNat p b ≠ 0) {j w : ℕ} {u : ℤ}
    (hj : j ≤ degree c) (hu : c.getD (degree c - j) 0 = (p : ℤ) ^ w * u) (hpu : ¬(p : ℤ) ∣ u)
    (hmin : ∀ i ≤ degree c, i ≠ j → (p : ℤ) ^ (w + j * padicValNat p b + 1) ∣
      c.getD (degree c - i) 0 * (p : ℤ) ^ (i * padicValNat p b)) :
    Even (w + j * padicValNat p b) ∧ (Even j → IsSquare (u : ZMod p)) := by
  have hpp : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp.out
  have hpa := Int.not_natCast_dvd_of_gcd_eq_one hp.out.ne_one hab
    (dvd_of_one_le_padicValNat (Nat.one_le_iff_ne_zero.mpr hm))
  obtain ⟨b', hb', hpb'⟩ := Int.exists_eq_pow_padicValInt_mul hp.out.ne_one (n := b)
    fun h ↦ by simp_all
  rw [padicValInt.of_nat] at hb'
  have hterm (i : ℕ) : c.getD (degree c - i) 0 * a ^ (degree c - i) * (b : ℤ) ^ i =
      c.getD (degree c - i) 0 * (p : ℤ) ^ (i * padicValNat p b) *
        (a ^ (degree c - i) * b' ^ i) := by rw [hb']; ring
  rw [binaryForm_eq_sum_of_even hd] at hy
  obtain ⟨hev, t, ht⟩ := Int.even_and_exists_isSquare_add_of_sq_eq_sum
    (v := w + j * padicValNat p b) (u := u * a ^ (degree c - j) * b' ^ j) hy
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) (by rw [hterm, hu, pow_add]; ring)
    (hpp.not_dvd_mul (hpp.not_dvd_mul hpu (mt hpp.dvd_of_dvd_pow hpa)) (mt hpp.dvd_of_dvd_pow hpb'))
    fun i hi hij ↦ hterm i ▸ (hmin i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hij).mul_right _
  refine ⟨hev, fun ⟨k, hk⟩ ↦ ?_⟩
  obtain ⟨l, hl⟩ : Even (degree c - j) := (Nat.even_sub hj).mpr (by simp [Nat.even_iff, hd, hk])
  exact isSquare_intCast_of_isSquare_mul_sq_add (x := a ^ l * b' ^ k) (t := t)
    (hpp.not_dvd_mul (mt hpp.dvd_of_dvd_pow hpa) (mt hpp.dvd_of_dvd_pow hpb'))
    (by convert ht using 2; rw [hl, hk]; ring)

namespace Sieve

/-! ### The unit parts of the coefficients -/

/-- What an entry `o` of `Ratpoints.Sieve.unitParts` says of the coefficient `x` at the prime `p`:
none for `x = 0`, and otherwise the pair `(w, r)` with `x = p ^ w u`, `p ∤ u`, and `r < p` the
residue of the unit part `u` modulo `p`. -/
def IsUnitPart (p : ℕ) (x : ℤ) : Option (ℕ × ℕ) → Prop
  | none => x = 0
  | some (w, r) => r < p ∧ ∃ u : ℤ, x = (p : ℤ) ^ w * u ∧ ¬(p : ℤ) ∣ u ∧ (r : ZMod p) = u

theorem isUnitPart_of_emod_ne_zero {p : ℕ} (hp : 0 < p) {x : ℤ} (hx : x % (p : ℤ) ≠ 0) :
    IsUnitPart p x (some (0, (x % (p : ℤ)).toNat)) := by
  have : NeZero p := ⟨hp.ne'⟩
  refine ⟨Int.toNat_emod_lt x hp, x, by simp,
    fun h ↦ hx (Int.emod_eq_zero_of_dvd h), ZMod.natCast_toNat_emod x⟩

/-- The residue `r ≠ 0` of the coefficient `x` modulo `p`, as the table of `p` hands it back
(`Ratpoints.Sieve.examinePrime?`), describes `x` at `p` with the valuation `0`. -/
theorem isUnitPart_of_eq_toNat_emod {p : ℕ} (hp : 0 < p) {x : ℤ} {r : ℕ}
    (hr : r = (x % (p : ℤ)).toNat) (h : r ≠ 0) : IsUnitPart p x (some (0, r)) :=
  hr ▸ isUnitPart_of_emod_ne_zero hp fun h' ↦ h (by simp [hr, h'])

/-- The valuation of a nonzero coefficient `x` with the residue `r` of `|x| / p ^ w` modulo `p`
(`Ratpoints.Setup.valuation`), and `p - r` for `x < 0`, describes `x` at `p`: the unit part of `x`
carries its sign. -/
theorem isUnitPart_of_eq_run_valuation {p : ℕ} (hp : 1 < p) {x : ℤ} (hx : x ≠ 0) {w r : ℕ}
    (h : (w, r) = Id.run (Setup.valuation x p)) :
    IsUnitPart p x (some (w, if x < 0 then p - r else r)) := by
  obtain ⟨m, hm, hmr, hr⟩ := Setup.exists_eq_run_valuation hx hp
  rw [← h] at hm hmr hr
  dsimp only at hm hmr hr
  have hrp : r < p := hmr ▸ Nat.mod_lt _ (by lia)
  have hpm : ¬(p : ℤ) ∣ m := fun h ↦
    hr (hmr ▸ Nat.mod_eq_zero_of_dvd (Int.natCast_dvd_natCast.mp h))
  have hmr' : (m : ZMod p) = r := by rw [← hmr, ZMod.natCast_mod]
  split_ifs with hneg
  · refine ⟨by lia, -m, ?_, by rwa [Int.dvd_neg], ?_⟩
    · rw [Int.eq_neg_natAbs_of_nonpos hneg.le, hm]
      push_cast
      ring
    · rw [Nat.cast_sub hrp.le, ZMod.natCast_self, zero_sub, Int.cast_neg, Int.cast_natCast, hmr']
  · refine ⟨hrp, m, ?_, hpm, by rw [Int.cast_natCast, hmr']⟩
    rw [← Int.natAbs_of_nonneg (Int.not_lt.mp hneg), hm]
    push_cast
    ring

-- The valuation of a coefficient, as a value for the contract of the unit parts.
private theorem valuation_value (n : ℤ) (p : ℕ) :
    ⦃ True ⦄ Setup.valuation n p ⦃ fun r ↦ r = Id.run (Setup.valuation n p) ⦄ :=
  ⟨fun _ ↦ rfl⟩

/-- The invariant of the loop of `Ratpoints.Sieve.unitParts` after `k` coefficients: the entries
describe the coefficients `c_d, …, c_{d-k+1}`. -/
def UnitPartsInvariant (c : List ℤ) (d p k : ℕ) (us : Array (Option (ℕ × ℕ))) : Prop :=
  us.size = k ∧ ∀ j < k, IsUnitPart p (c.getD (d - j) 0) us[j]!

theorem unitPartsInvariant_zero (c : List ℤ) (d p : ℕ) : UnitPartsInvariant c d p 0 #[] :=
  ⟨rfl, nofun⟩

theorem UnitPartsInvariant.push {c : List ℤ} {d p : ℕ} {pref suff : List ℕ} {cur : ℕ}
    {us : Array (Option (ℕ × ℕ))} {o : Option (ℕ × ℕ)}
    (h : UnitPartsInvariant c d p pref.length us)
    (hl : ForIn.toList [:d + 1] = pref ++ cur :: suff) (ho : IsUnitPart p (c.getD (d - cur) 0) o) :
    UnitPartsInvariant c d p (pref ++ [cur]).length (us.push o) := by
  have hcur := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  refine ⟨by simp [h.1], fun j hj ↦ ?_⟩
  rw [List.length_append, List.length_singleton] at hj
  rcases Nat.lt_or_ge j pref.length with hj' | hj'
  · rw [Array.getElem!_push_lt (h.1 ▸ hj')]
    exact h.2 j hj'
  · obtain rfl : j = us.size := by rw [h.1]; lia
    rwa [Array.getElem!_push_eq, h.1, hcur]

theorem UnitPartsInvariant.size_eq_and_isUnitPart {c : List ℤ} {d p : ℕ}
    {us : Array (Option (ℕ × ℕ))}
    (h : UnitPartsInvariant c d p (ForIn.toList [:d + 1]).length us) :
    us.size = d + 1 ∧ ∀ j ≤ d, IsUnitPart p (c.getD (d - j) 0) us[j]! := by
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at h
  exact ⟨h.1, fun j hj ↦ h.2 j (by lia)⟩

-- The residue of the coefficient at the cursor of the loop of `Ratpoints.Sieve.unitParts`.
private theorem getElem!_sub_eq {c : List ℤ} {d p : ℕ} {cm : Array ℕ}
    (h : 1 < p ∧ ∀ j ≤ d, cm[j]! = (c.getD j 0 % (p : ℤ)).toNat) (k : ℕ) :
    cm[d - k]! = (c.getD (d - k) 0 % (p : ℤ)).toNat :=
  h.2 _ (Nat.sub_le d k)

attribute [local irreducible] UnitPartsInvariant in
/-- The contract of `Ratpoints.Sieve.unitParts`: for `p > 1` and the coefficients `cm` reduced
modulo `p`, as the table of `p` hands them back (`Ratpoints.Sieve.examinePrime?`), its entries
describe the coefficients `c_d, …, c_0` at `p` (`Ratpoints.Sieve.IsUnitPart`). -/
@[spec]
theorem unitParts_spec (c : List ℤ) (d p : ℕ) (cm : Array ℕ) :
    ⦃ 1 < p ∧ ∀ j ≤ d, cm[j]! = (c.getD j 0 % (p : ℤ)).toNat ⦄ unitParts c d p cm
    ⦃ fun us ↦ us.size = d + 1 ∧ ∀ j ≤ d, IsUnitPart p (c.getD (d - j) 0) us[j]! ⦄ := by
  vcgen [unitParts, valuation_value] invariants
  · fun pref _ us ↦ UnitPartsInvariant c d p pref.length us
  all_goals first
    | exact unitPartsInvariant_zero c d p
    | exact UnitPartsInvariant.size_eq_and_isUnitPart ‹_›
    | exact UnitPartsInvariant.push ‹_› ‹_› ‹_›
    | exact UnitPartsInvariant.push ‹_› ‹_›
        (isUnitPart_of_eq_run_valuation ‹1 < p ∧ _›.1 ‹_› ‹_›)
    | exact UnitPartsInvariant.push ‹_› ‹_›
        (isUnitPart_of_eq_toNat_emod (by have := ‹1 < p ∧ _›.1; lia) (getElem!_sub_eq ‹_› _) ‹_›)

/-- `Ratpoints.Sieve.unitParts_spec` as a plain statement. -/
theorem isUnitPart_run_unitParts (c : List ℤ) (d : ℕ) {p : ℕ} (hp : 1 < p) {cm : Array ℕ}
    (hcm : ∀ j ≤ d, cm[j]! = (c.getD j 0 % (p : ℤ)).toNat) {j : ℕ} (hj : j ≤ d) :
    IsUnitPart p (c.getD (d - j) 0) (Id.run (unitParts c d p cm))[j]! :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((unitParts_spec c d p cm).le_wp ⟨hp, hcm⟩)).2 j hj

theorem le_of_getElem!_run_unitParts_eq_some {c : List ℤ} {d p j : ℕ} (hp : 1 < p) {cm : Array ℕ}
    (hcm : ∀ j ≤ d, cm[j]! = (c.getD j 0 % (p : ℤ)).toNat) {x : ℕ × ℕ}
    (h : (Id.run (unitParts c d p cm))[j]! = some x) : j ≤ d := by
  by_contra hlt
  rw [getElem!_neg _ j (by
    rw [(Std.WP.Id.of_run_eq_wp rfl _ ((unitParts_spec c d p cm).le_wp ⟨hp, hcm⟩)).1]; lia)] at h
  exact Option.some_ne_none _ h.symm

/-! ### The valuations that the terms exclude -/

/-- The invariant of the loop of `Ratpoints.Sieve.forbiddenAt` over the coefficients `j ≤ k`, on
the index `jmin`, the least valuation `vmin` and the flag `tie`: `jmin` is `0` or a coefficient
present, `vmin` is the valuation `w_jmin + jmin m` of its term, at most that of every term `j ≤ k`
(the term of `j = 0` counted as present), and less than those of the others unless `tie`. -/
def ForbiddenAtInvariant (us : Array (Option (ℕ × ℕ))) (m k jmin vmin : ℕ) (tie : Bool) :
    Prop :=
  jmin ≤ k ∧ (jmin = 0 ∨ us[jmin]!.isSome) ∧ vmin = (us[jmin]!.getD (0, 0)).1 + jmin * m ∧
    (∀ j ≤ k, (j = 0 ∨ us[j]!.isSome) → vmin ≤ (us[j]!.getD (0, 0)).1 + j * m) ∧
    (tie = false → ∀ j ≤ k, (j = 0 ∨ us[j]!.isSome) → j ≠ jmin →
      vmin < (us[j]!.getD (0, 0)).1 + j * m)

theorem forbiddenAtInvariant_zero (us : Array (Option (ℕ × ℕ))) (m : ℕ) :
    ForbiddenAtInvariant us m 0 0 (us[0]!.getD (0, 0)).1 false := by
  refine ⟨le_rfl, .inl rfl, by simp, fun j hj _ ↦ ?_, fun _ j hj _ hne ↦ absurd (by lia) hne⟩
  obtain rfl : j = 0 := by lia
  simp

-- The cursor of the loop of `Ratpoints.Sieve.forbiddenAt` and the number of coefficients done.
private theorem eq_length_of_toList_eq {n cur : ℕ} {pref suff : List ℕ}
    (hl : ForIn.toList [1:n] = pref ++ cur :: suff) : cur = pref.length + 1 := by
  have := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  lia

/-- The step of `Ratpoints.Sieve.forbiddenAt` at a coefficient whose term has a valuation less than
`vmin`: it becomes the least one, with no tie. -/
theorem ForbiddenAtInvariant.update {us : Array (Option (ℕ × ℕ))} {m jmin vmin : ℕ} {tie : Bool}
    {pref suff : List ℕ} {cur w r : ℕ} (h : ForbiddenAtInvariant us m pref.length jmin vmin tie)
    (hl : ForIn.toList [1:us.size] = pref ++ cur :: suff) (hw : us[cur]! = some (w, r))
    (hlt : w + cur * m < vmin) :
    ForbiddenAtInvariant us m (pref ++ [cur]).length cur (w + cur * m) false := by
  have hcur := eq_length_of_toList_eq hl
  obtain ⟨-, -, -, hle, -⟩ := h
  rw [List.length_append, List.length_singleton, ← hcur]
  refine ⟨le_rfl, .inr (by simp [hw]), by simp [hw], fun j hj hc ↦ ?_, fun _ j hj hc hne ↦ ?_⟩
  · rcases Nat.lt_or_ge j cur with hj' | hj'
    · exact (hle j (by lia) hc).trans' hlt.le
    · obtain rfl : j = cur := by lia
      simp [hw]
  · exact (hle j (by lia) hc).trans_lt' hlt

/-- The step of `Ratpoints.Sieve.forbiddenAt` at a coefficient whose term has the valuation `vmin`:
a tie. -/
theorem ForbiddenAtInvariant.tie {us : Array (Option (ℕ × ℕ))} {m jmin vmin : ℕ} {tie : Bool}
    {pref suff : List ℕ} {cur w r : ℕ} (h : ForbiddenAtInvariant us m pref.length jmin vmin tie)
    (hl : ForIn.toList [1:us.size] = pref ++ cur :: suff) (hw : us[cur]! = some (w, r))
    (heq : w + cur * m = vmin) :
    ForbiddenAtInvariant us m (pref ++ [cur]).length jmin vmin true := by
  have hcur := eq_length_of_toList_eq hl
  obtain ⟨hj, hc, hv, hle, -⟩ := h
  rw [List.length_append, List.length_singleton]
  refine ⟨by lia, hc, hv, fun j hj' hcj ↦ ?_, nofun⟩
  rcases Nat.lt_or_ge j cur with hj'' | hj''
  · exact hle j (by lia) hcj
  · obtain rfl : j = cur := by lia
    simp [hw, heq]

/-- The step of `Ratpoints.Sieve.forbiddenAt` at a coefficient absent or whose term has a valuation
greater than `vmin`: nothing changes. -/
theorem ForbiddenAtInvariant.keep {us : Array (Option (ℕ × ℕ))} {m jmin vmin : ℕ} {tie : Bool}
    {pref suff : List ℕ} {cur : ℕ} (h : ForbiddenAtInvariant us m pref.length jmin vmin tie)
    (hl : ForIn.toList [1:us.size] = pref ++ cur :: suff)
    (hw : ∀ w r, us[cur]! = some (w, r) → vmin < w + cur * m) :
    ForbiddenAtInvariant us m (pref ++ [cur]).length jmin vmin tie := by
  have hcur := eq_length_of_toList_eq hl
  obtain ⟨hj, hc, hv, hle, hlt⟩ := h
  rw [List.length_append, List.length_singleton]
  have key (j : ℕ) (hj' : j ≤ pref.length + 1) (hcj : j = 0 ∨ us[j]!.isSome) :
      j ≤ pref.length ∨ vmin < (us[j]!.getD (0, 0)).1 + j * m := by
    rcases Nat.lt_or_ge j cur with hj'' | hj''
    · exact .inl (by lia)
    · obtain rfl : j = cur := by lia
      obtain ⟨⟨w, r⟩, hwr⟩ := Option.isSome_iff_exists.mp (hcj.resolve_left (by lia))
      exact .inr (by simpa [hwr] using hw w r hwr)
  refine ⟨by lia, hc, hv, fun j hj' hcj ↦ ?_, fun ht j hj' hcj hne ↦ ?_⟩
  · exact (key j hj' hcj).elim (hle j · hcj) Nat.le_of_lt
  · exact (key j hj' hcj).elim (hlt ht j · hcj hne) id

theorem ForbiddenAtInvariant.exists_of_eq_true {us : Array (Option (ℕ × ℕ))} {sq : Array Bool}
    {m jmin vmin : ℕ} {tie : Bool}
    (h : ForbiddenAtInvariant us m (ForIn.toList [1:us.size]).length jmin vmin tie)
    (hr : (!tie && (vmin % 2 == 1 || jmin % 2 == 0 && !sq[(us[jmin]!.getD (0, 0)).2]!)) = true) :
    ∃ j₀, (j₀ = 0 ∨ us[j₀]!.isSome) ∧
      (∀ j, (j = 0 ∨ us[j]!.isSome) → j ≠ j₀ →
        (us[j₀]!.getD (0, 0)).1 + j₀ * m < (us[j]!.getD (0, 0)).1 + j * m) ∧
      (((us[j₀]!.getD (0, 0)).1 + j₀ * m) % 2 = 1 ∨
        (j₀ % 2 = 0 ∧ sq[(us[j₀]!.getD (0, 0)).2]! = false)) := by
  obtain ⟨-, hc, rfl, -, hlt⟩ := h
  simp only [Bool.and_eq_true, Bool.not_eq_true', Bool.or_eq_true, beq_iff_eq] at hr
  refine ⟨jmin, hc, fun j hcj hne ↦ hlt hr.1 j ?_ hcj hne, by simpa using hr.2⟩
  have : j < us.size ∨ j = 0 := hcj.symm.imp_left fun h ↦ by
    by_contra hlt'
    rw [getElem!_neg us j (by lia)] at h
    exact Bool.false_ne_true h
  rw [Std.Legacy.Range.length_toList]
  lia

attribute [local irreducible] ForbiddenAtInvariant in
/-- The contract of `Ratpoints.Sieve.forbiddenAt`: when it excludes the valuation `m`, the term of
some `j₀`, `0` or a coefficient present, has a valuation `w_{j₀} + j₀ m` less than those of the
other terms (the term of `j = 0` counted as present), which is odd, or `j₀` is even and the residue
of its unit part is not marked in `sq`. -/
@[spec]
theorem forbiddenAt_spec (us : Array (Option (ℕ × ℕ))) (sq : Array Bool) (m : ℕ) :
    ⦃ True ⦄ forbiddenAt us sq m
    ⦃ fun r ↦ r = true → ∃ j₀, (j₀ = 0 ∨ us[j₀]!.isSome) ∧
        (∀ j, (j = 0 ∨ us[j]!.isSome) → j ≠ j₀ →
          (us[j₀]!.getD (0, 0)).1 + j₀ * m < (us[j]!.getD (0, 0)).1 + j * m) ∧
        (((us[j₀]!.getD (0, 0)).1 + j₀ * m) % 2 = 1 ∨
          (j₀ % 2 = 0 ∧ sq[(us[j₀]!.getD (0, 0)).2]! = false)) ⦄ := by
  vcgen [forbiddenAt] invariants
  · fun pref _ s ↦ ForbiddenAtInvariant us m pref.length s.1 s.2.1 s.2.2
  all_goals dsimp only at *
  all_goals first
    | exact forbiddenAtInvariant_zero us m
    | exact ForbiddenAtInvariant.exists_of_eq_true ‹_› ‹_›
    | exact ForbiddenAtInvariant.update ‹_› ‹_› ‹_› ‹_›
    | exact ForbiddenAtInvariant.tie ‹_› ‹_› ‹_› ‹_›
    | exact ForbiddenAtInvariant.keep ‹_› ‹_› fun _ _ h ↦ by grind

/-- `Ratpoints.Sieve.forbiddenAt_spec` as a plain statement. -/
theorem exists_of_run_forbiddenAt_eq_true {us : Array (Option (ℕ × ℕ))} {sq : Array Bool} {m : ℕ}
    (h : Id.run (forbiddenAt us sq m) = true) :
    ∃ j₀, (j₀ = 0 ∨ us[j₀]!.isSome) ∧
      (∀ j, (j = 0 ∨ us[j]!.isSome) → j ≠ j₀ →
        (us[j₀]!.getD (0, 0)).1 + j₀ * m < (us[j]!.getD (0, 0)).1 + j * m) ∧
      (((us[j₀]!.getD (0, 0)).1 + j₀ * m) % 2 = 1 ∨
        (j₀ % 2 = 0 ∧ sq[(us[j₀]!.getD (0, 0)).2]! = false)) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((forbiddenAt_spec us sq m).le_wp trivial) h

/-- A coefficient `x` with the entry `o` at `p` makes `x p ^ (i m)` divisible by `p ^ (V + 1)` when
`V < w + i m` for the valuation `w` of `o`; for `o = none`, `x = 0`. -/
theorem pow_dvd_mul_pow_of_isUnitPart {p : ℕ} {x : ℤ} {o : Option (ℕ × ℕ)} (h : IsUnitPart p x o)
    {V i m : ℕ} (hV : ∀ w r, o = some (w, r) → V < w + i * m) :
    (p : ℤ) ^ (V + 1) ∣ x * (p : ℤ) ^ (i * m) := by
  rcases o with _ | ⟨w, r⟩
  · obtain rfl : x = 0 := h
    simp
  · obtain ⟨-, u, rfl, -⟩ := h
    exact (pow_dvd_pow _ (hV w r rfl)).trans ⟨u, by rw [pow_add]; ring⟩

/-- For a point `(a, y, b)` of a curve of even degree with `v_p(b) = m ≥ 1`, a coefficient
`c_{d-j₀}`, with the entry `(w, r)` at `p`, whose term has a valuation `w + j₀ m` less than those of
the other terms present has an even `w + j₀ m`, and for even `j₀` a unit part whose residue `r` is
marked as a square modulo `p` (`Ratpoints.even_and_isSquare_of_sq_eq_binaryForm_of_even`); `cm` are
the coefficients reduced modulo `p`. -/
theorem even_and_getElem!_squaresMod_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 0) {p : ℕ}
    (hp : p.Prime) {cm : Array ℕ} (hcm : ∀ j ≤ degree c, cm[j]! = (c.getD j 0 % (p : ℤ)).toNat)
    {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b)
    (hm : padicValNat p b ≠ 0) {j₀ w r : ℕ}
    (hus : (Id.run (unitParts c (degree c) p cm))[j₀]! = some (w, r))
    (hmin : ∀ j, (Id.run (unitParts c (degree c) p cm))[j]!.isSome → j ≠ j₀ →
      w + j₀ * padicValNat p b <
        ((Id.run (unitParts c (degree c) p cm))[j]!.getD (0, 0)).1 + j * padicValNat p b) :
    Even (w + j₀ * padicValNat p b) ∧ (Even j₀ → (squaresMod p)[r]! = true) := by
  have : Fact p.Prime := ⟨hp⟩
  have hj₀ := le_of_getElem!_run_unitParts_eq_some hp.one_lt hcm hus
  obtain ⟨hr, u, hu, hpu, hru⟩ := hus ▸ isUnitPart_run_unitParts c (degree c) hp.one_lt hcm hj₀
  obtain ⟨hev, hsq⟩ := even_and_isSquare_of_sq_eq_binaryForm_of_even hd hab hy hm hj₀ hu hpu
    fun i hi hne ↦
      pow_dvd_mul_pow_of_isUnitPart (isUnitPart_run_unitParts c (degree c) hp.one_lt hcm hi)
        fun w' r' h' ↦ by simpa [h'] using hmin i (by simp [h']) hne
  exact ⟨hev, fun hj ↦ getElem!_squaresMod_of_isSquare hp hr (hru ▸ hsq hj)⟩

/-- **The forbidden valuations are sound.** No denominator `b` of a point of a curve of even degree
has a valuation `v_p(b) ≥ 1` at a prime `p` that `Ratpoints.Sieve.forbiddenAt` excludes, with the
unit parts of the coefficients at `p` (`Ratpoints.Sieve.unitParts`) and the squares modulo `p`: the
term of the least valuation would make `F(a, b)` a non-square
(`Ratpoints.Sieve.even_and_getElem!_squaresMod_of_sq_eq`), and for `c_d = 0` the term of `j = 0`,
of the valuation `0` and the unit part `0`, a square, is the least one; `cm` are the coefficients
reduced modulo `p`. -/
theorem run_forbiddenAt_eq_false_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 0) {p : ℕ}
    (hp : p.Prime) {cm : Array ℕ} (hcm : ∀ j ≤ degree c, cm[j]! = (c.getD j 0 % (p : ℤ)).toNat)
    {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b)
    (hm : padicValNat p b ≠ 0) :
    Id.run (forbiddenAt (Id.run (unitParts c (degree c) p cm)) (squaresMod p)
      (padicValNat p b)) = false := by
  refine Bool.eq_false_iff.mpr fun h ↦ ?_
  obtain ⟨j₀, hc, hmin, hcrit⟩ := exists_of_run_forbiddenAt_eq_true h
  rcases hus : (Id.run (unitParts c (degree c) p cm))[j₀]! with _ | ⟨w, r⟩
  · obtain rfl : j₀ = 0 := hc.resolve_right (by simp [hus])
    simp [hus, getElem!_squaresMod_zero hp] at hcrit
  simp only [hus, Option.getD_some] at hmin hcrit
  obtain ⟨hev, hsq⟩ := even_and_getElem!_squaresMod_of_sq_eq hd hp hcm hab hy hm hus
    fun j hj hne ↦ hmin j (.inr hj) hne
  rcases hcrit with hodd | ⟨hj, hs⟩
  · exact Nat.not_even_iff_odd.mpr (Nat.odd_iff.mpr hodd) hev
  · exact Bool.false_ne_true (hs.symm.trans (hsq (Nat.even_iff.mpr hj)))

/-! ### The masks of the valuations -/

/-- The invariant of the loops of `Ratpoints.Sieve.forbiddenValuations` and
`Ratpoints.Sieve.allValuations` on the mask, the valuation `m` and `pm`, for the test `f` of the
valuations: before the exit, `pm = p ^ m` with `m ≥ 1`, `p ^ t ≤ bHigh` for `1 ≤ t < m`, and the
mask holds the `t` with `1 ≤ t < m` that pass `f`; at the exit, the mask holds the `t ≥ 1` with
`p ^ t ≤ bHigh` that pass `f`. -/
def ValuationsInvariant (f : ℕ → Bool) (p bHigh : ℕ) : Std.WP.WhileInvariant (ℕ × ℕ × ℕ) Prop :=
  .mk fun exit s ↦
    (exit = false → s.2.2 = p ^ s.2.1 ∧ 1 ≤ s.2.1 ∧ (∀ t ≥ 1, t < s.2.1 → p ^ t ≤ bHigh) ∧
      ∀ t, s.1.testBit t = (decide (1 ≤ t) && decide (t < s.2.1) && f t)) ∧
    (exit = true → ∀ t, s.1.testBit t = (decide (1 ≤ t) && decide (p ^ t ≤ bHigh) && f t))

theorem valuationsInvariant_zero_one (f : ℕ → Bool) (p bHigh : ℕ) :
    ValuationsInvariant f p bHigh false (0, 1, p) :=
  ⟨fun _ ↦ ⟨(pow_one p).symm, le_rfl, fun _ h h' ↦ absurd h' (by lia), fun t ↦ by
    simp only [Nat.zero_testBit]; grind⟩, nofun⟩

-- The bits of the mask after the step of the valuation `m`, from the mask before it.
private theorem testBit_eq_of_testBit_or {f : ℕ → Bool} {m : ℕ} {mask mask' : ℕ}
    (hmask : ∀ t, mask.testBit t = (decide (1 ≤ t) && decide (t < m) && f t))
    (h' : ∀ t, mask'.testBit t = (mask.testBit t || (decide (t = m) && f m))) (hm : 1 ≤ m)
    (t : ℕ) : mask'.testBit t = (decide (1 ≤ t) && decide (t < m + 1) && f t) := by
  grind

/-- The step of the valuation `m` of the loops of `Ratpoints.Sieve.forbiddenValuations` and
`Ratpoints.Sieve.allValuations` that ends them, `p ^ (m + 1) > bHigh`, with the bit of `m` set when
`m` passes `f`. -/
theorem ValuationsInvariant.exit_of_div_lt {f : ℕ → Bool} {p bHigh mask m pm mask' : ℕ} (hp : 0 < p)
    (h : ValuationsInvariant f p bHigh false (mask, m, pm)) (hpm : pm ≤ bHigh)
    (hb : bHigh / p < pm)
    (h' : ∀ t, mask'.testBit t = (mask.testBit t || (decide (t = m) && f m))) :
    ValuationsInvariant f p bHigh true (mask', m, pm) := by
  obtain ⟨hpm', hm, hlt, hmask⟩ := h.1 rfl
  dsimp only at hpm' hm hlt hmask
  subst hpm'
  refine ⟨nofun, fun _ t ↦ ?_⟩
  rw [testBit_eq_of_testBit_or hmask h' hm]
  have : p ^ t ≤ bHigh ↔ t < m + 1 := by
    refine ⟨fun ht ↦ Nat.lt_of_not_le fun ht' ↦ ?_, fun ht ↦ ?_⟩
    · have := (Nat.div_lt_iff_lt_mul hp).mp hb
      have := Nat.pow_le_pow_right hp ht'
      rw [pow_succ] at this
      lia
    · exact (Nat.pow_le_pow_right hp (Nat.le_of_lt_succ ht)).trans hpm
  grind

/-- The step of the valuation `m` of the loops of `Ratpoints.Sieve.forbiddenValuations` and
`Ratpoints.Sieve.allValuations` that goes on, with the bit of `m` set when `m` passes `f`. -/
theorem ValuationsInvariant.add_one {f : ℕ → Bool} {p bHigh mask m pm mask' : ℕ}
    (h : ValuationsInvariant f p bHigh false (mask, m, pm)) (hpm : pm ≤ bHigh)
    (hb : ¬bHigh / p < pm)
    (h' : ∀ t, mask'.testBit t = (mask.testBit t || (decide (t = m) && f m))) :
    ValuationsInvariant f p bHigh false (mask', m + 1, pm * p) := by
  obtain ⟨hpm', hm, hlt, hmask⟩ := h.1 rfl
  dsimp only at hpm' hm hlt hmask
  subst hpm'
  refine ⟨fun _ ↦ ⟨(pow_succ p m).symm, by lia, fun t ht ht' ↦ ?_,
    testBit_eq_of_testBit_or hmask h' hm⟩, nofun⟩
  rcases Nat.lt_or_ge t m with htm | htm
  exacts [hlt t ht htm, (by lia : t = m) ▸ hpm]

/-- The exit of the loops of `Ratpoints.Sieve.forbiddenValuations` and
`Ratpoints.Sieve.allValuations` at `p ^ m > bHigh`. -/
theorem ValuationsInvariant.exit {f : ℕ → Bool} {p bHigh mask m pm : ℕ} (hp : 0 < p)
    (h : ValuationsInvariant f p bHigh false (mask, m, pm)) (hpm : ¬pm ≤ bHigh) :
    ValuationsInvariant f p bHigh true (mask, m, pm) := by
  obtain ⟨hpm', hm, hlt, hmask⟩ := h.1 rfl
  dsimp only at hpm' hm hlt hmask
  subst hpm'
  refine ⟨nofun, fun _ t ↦ ?_⟩
  rw [hmask]
  have (ht1 : 1 ≤ t) : p ^ t ≤ bHigh ↔ t < m :=
    ⟨fun ht ↦ Nat.lt_of_not_le fun ht' ↦ hpm ((Nat.pow_le_pow_right hp ht').trans ht),
      hlt t ht1⟩
  grind

theorem ValuationsInvariant.testBit {f : ℕ → Bool} {p bHigh mask m pm : ℕ}
    (h : ValuationsInvariant f p bHigh true (mask, m, pm)) (t : ℕ) :
    mask.testBit t = (decide (1 ≤ t) && decide (p ^ t ≤ bHigh) && f t) :=
  h.2 rfl t

/-- The measure of the loops of `Ratpoints.Sieve.forbiddenValuations` and
`Ratpoints.Sieve.allValuations` drops with each step that goes on: `pm p ≤ bHigh`, and `pm p > pm`
since `pm = p ^ m ≥ 1` and `p > 1`. -/
theorem ValuationsInvariant.sub_mul_lt {f : ℕ → Bool} {p bHigh mask m pm : ℕ} (hp : 1 < p)
    (h : ValuationsInvariant f p bHigh false (mask, m, pm)) (hb : ¬bHigh / p < pm) :
    bHigh + 1 - pm * p < bHigh + 1 - pm := by
  obtain ⟨hpm, -⟩ := h.1 rfl
  dsimp only at hpm
  have h1 : 1 ≤ pm := hpm ▸ Nat.one_le_pow _ _ (by lia)
  have h2 : pm * p ≤ bHigh := (Nat.le_div_iff_mul_le (by lia)).mp (Nat.le_of_not_lt hb)
  have h3 : pm < pm * p := (Nat.lt_mul_iff_one_lt_right (by lia)).mpr hp
  lia

/-- The step of the loops of `Ratpoints.Sieve.forbiddenValuations` and
`Ratpoints.Sieve.allValuations` that goes on, with the measure. -/
theorem ValuationsInvariant.sub_lt_and_add_one {f : ℕ → Bool} {p bHigh mask m pm mask' : ℕ}
    (hp : 1 < p) (h : ValuationsInvariant f p bHigh false (mask, m, pm)) (hpm : pm ≤ bHigh)
    (hb : ¬bHigh / p < pm)
    (h' : ∀ t, mask'.testBit t = (mask.testBit t || (decide (t = m) && f m))) :
    bHigh + 1 - pm * p < bHigh + 1 - pm ∧
      ValuationsInvariant f p bHigh false (mask', m + 1, pm * p) :=
  ⟨h.sub_mul_lt hp hb, h.add_one hpm hb h'⟩

-- The mask with the bit of `m` set when the test `x` of `m` holds.
private theorem testBit_or_one_shiftLeft {x y : Bool} (hx : x = y) (hy : x = true)
    (mask m t : ℕ) : (mask ||| 1 <<< m).testBit t = (mask.testBit t || (decide (t = m) && y)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, ← hx, hy]
  grind

private theorem testBit_eq_or {x y : Bool} (hx : x = y) (hy : ¬x = true) (mask m t : ℕ) :
    mask.testBit t = (mask.testBit t || (decide (t = m) && y)) := by
  simp [← hx, Bool.eq_false_iff.mpr hy]

-- The unit parts and the test of a valuation, as values for the contract of the mask.
private theorem unitParts_value (c : List ℤ) (d p : ℕ) (cm : Array ℕ) :
    ⦃ True ⦄ unitParts c d p cm ⦃ fun r ↦ r = Id.run (unitParts c d p cm) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem forbiddenAt_value (us : Array (Option (ℕ × ℕ))) (sq : Array Bool) (m : ℕ) :
    ⦃ True ⦄ forbiddenAt us sq m ⦃ fun r ↦ r = Id.run (forbiddenAt us sq m) ⦄ :=
  ⟨fun _ ↦ rfl⟩

attribute [local irreducible] ValuationsInvariant in
/-- The contract of `Ratpoints.Sieve.forbiddenValuations`: bit `m` of the mask is set exactly for
the `m ≥ 1` with `p ^ m ≤ bHigh` that `Ratpoints.Sieve.forbiddenAt` excludes. The loop ends for
`p > 1`, since `pm = p ^ m` grows and stays at most `bHigh` while it goes on. -/
@[spec]
theorem forbiddenValuations_spec (c : List ℤ) (d p bHigh : ℕ) (cm : Array ℕ) :
    ⦃ 1 < p ⦄ forbiddenValuations c d p bHigh cm
    ⦃ fun mask ↦ ∀ m, mask.testBit m = (decide (1 ≤ m) && decide (p ^ m ≤ bHigh) &&
        Id.run (forbiddenAt (Id.run (unitParts c d p cm)) (squaresMod p) m)) ⦄ := by
  vcgen [forbiddenValuations, unitParts_value, forbiddenAt_value] invariants
  · ValuationsInvariant
      (fun m ↦ Id.run (forbiddenAt (Id.run (unitParts c d p cm)) (squaresMod p) m)) p bHigh
  · .ofMeasure fun s : ℕ × ℕ × ℕ ↦ bHigh + 1 - s.2.2
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals try obtain ⟨rfl, _⟩ := ‹_ = _ ∧ ValuationsInvariant _ _ _ false _›
  all_goals subst ‹_ = Id.run (unitParts _ _ _ _)›
  all_goals first
    | exact valuationsInvariant_zero_one _ _ _
    | exact ‹ValuationsInvariant _ _ _ true _›.testBit _
    | exact ValuationsInvariant.exit_of_div_lt (by lia) ‹_› ‹_› ‹_›
        (testBit_or_one_shiftLeft ‹_› ‹_› _ _)
    | exact ValuationsInvariant.exit_of_div_lt (by lia) ‹_› ‹_› ‹_› (testBit_eq_or ‹_› ‹_› _ _)
    | exact ValuationsInvariant.sub_lt_and_add_one ‹_› ‹_› ‹_› ‹_›
        (testBit_or_one_shiftLeft ‹_› ‹_› _ _)
    | exact ValuationsInvariant.sub_lt_and_add_one ‹_› ‹_› ‹_› ‹_› (testBit_eq_or ‹_› ‹_› _ _)
    | exact ValuationsInvariant.exit (by lia) ‹_› ‹_›

attribute [local irreducible] ValuationsInvariant in
/-- The contract of `Ratpoints.Sieve.allValuations`: bit `m` of the mask is set exactly for the
`m ≥ 1` with `p ^ m ≤ bHigh`. -/
@[spec]
theorem allValuations_spec (p bHigh : ℕ) :
    ⦃ 1 < p ⦄ allValuations p bHigh
    ⦃ fun all ↦ ∀ m, all.testBit m = (decide (1 ≤ m) && decide (p ^ m ≤ bHigh)) ⦄ := by
  vcgen [allValuations] invariants
  · ValuationsInvariant (fun _ ↦ true) p bHigh
  · .ofMeasure fun s : ℕ × ℕ × ℕ ↦ bHigh + 1 - s.2.2
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals try obtain ⟨rfl, _⟩ := ‹_ = _ ∧ ValuationsInvariant _ _ _ false _›
  all_goals first
    | exact valuationsInvariant_zero_one _ _ _
    | exact (ValuationsInvariant.testBit ‹_› _).trans (Bool.and_true _)
    | exact ValuationsInvariant.exit_of_div_lt (by lia) ‹_› ‹_› ‹_›
        (testBit_or_one_shiftLeft rfl rfl _ _)
    | exact ValuationsInvariant.sub_lt_and_add_one ‹_› ‹_› ‹_› ‹_›
        (testBit_or_one_shiftLeft rfl rfl _ _)
    | exact ValuationsInvariant.exit (by lia) ‹_› ‹_›

/-- `Ratpoints.Sieve.forbiddenValuations_spec` as a plain statement. -/
theorem testBit_run_forbiddenValuations (c : List ℤ) (d : ℕ) {p : ℕ} (hp : 1 < p) (bHigh : ℕ)
    (cm : Array ℕ) (m : ℕ) :
    (Id.run (forbiddenValuations c d p bHigh cm)).testBit m = (decide (1 ≤ m) &&
      decide (p ^ m ≤ bHigh) &&
        Id.run (forbiddenAt (Id.run (unitParts c d p cm)) (squaresMod p) m)) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((forbiddenValuations_spec c d p bHigh cm).le_wp hp) m

/-- `Ratpoints.Sieve.allValuations_spec` as a plain statement. -/
theorem testBit_run_allValuations {p : ℕ} (hp : 1 < p) (bHigh m : ℕ) :
    (Id.run (allValuations p bHigh)).testBit m = (decide (1 ≤ m) && decide (p ^ m ≤ bHigh)) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((allValuations_spec p bHigh).le_wp hp) m

/-- The mask of the forbidden valuations at a prime `p`, with the coefficients `cm` reduced modulo
`p`, has no bit `v_p(b)` for the denominator `b` of a point of a curve of even degree
(`Ratpoints.Sieve.run_forbiddenAt_eq_false_of_sq_eq`); its bit `0` is never set. -/
theorem testBit_run_forbiddenValuations_eq_false_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 0)
    {p : ℕ} (hp : p.Prime) (bHigh : ℕ) {cm : Array ℕ}
    (hcm : ∀ j ≤ degree c, cm[j]! = (c.getD j 0 % (p : ℤ)).toNat) {a y : ℤ} {b : ℕ}
    (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    (Id.run (forbiddenValuations c (degree c) p bHigh cm)).testBit (padicValNat p b) = false := by
  rw [testBit_run_forbiddenValuations c _ hp.one_lt]
  rcases eq_or_ne (padicValNat p b) 0 with h0 | h0
  · simp [h0]
  · simp [run_forbiddenAt_eq_false_of_sq_eq hd hp hcm hab hy h0]

/-! ### The forbidden divisors -/

/-- A forbidden divisor tested with words that `Ratpoints.Sieve.forbiddenOfPrime` gives for `p`
from the coefficients `cm` and the entry `atInf` at infinity is `p` with its words, for `cm[d] = 0`
and a mask of the forbidden valuations that holds every valuation a denominator can have, or for
`atInf = false`: for the coefficients reduced modulo `p` and the entry at infinity of the table of
`p`, when `p ∣ c_d`, or when there are no points at infinity modulo `p`. -/
theorem eq_of_run_forbiddenOfPrime_eq_inl {c : List ℤ} {d p bHigh : ℕ} {cm : Array ℕ}
    {atInf : Bool} {e : ForbiddenEntry}
    (h : Id.run (forbiddenOfPrime c d p bHigh cm atInf) = some (.inl e)) :
    e = ⟨p, forbiddenRow p⟩ ∧ ((cm[d]! = 0 ∧
      Id.run (forbiddenValuations c d p bHigh cm) &&& Id.run (allValuations p bHigh) =
        Id.run (allValuations p bHigh)) ∨ atInf = false) := by
  simp only [forbiddenOfPrime, apply_ite Id.run, Id.run_bind] at h
  split_ifs at h <;> simp_all

/-- A forbidden divisor tested by its valuation that `Ratpoints.Sieve.forbiddenOfPrime` gives for
`p` from the coefficients `cm` is `p` with the mask of the forbidden valuations of `cm`
(`Ratpoints.Sieve.forbiddenValuations`). -/
theorem eq_of_run_forbiddenOfPrime_eq_inr {c : List ℤ} {d p bHigh : ℕ} {cm : Array ℕ}
    {atInf : Bool} {e : ForbiddenVal}
    (h : Id.run (forbiddenOfPrime c d p bHigh cm atInf) = some (.inr e)) :
    e = ⟨p, Id.run (forbiddenValuations c d p bHigh cm)⟩ := by
  simp only [forbiddenOfPrime, apply_ite Id.run, Id.run_bind] at h
  split_ifs at h <;> simp_all

/-- **A forbidden divisor tested with words that an examined prime gives is sound**, from the
coefficients `cm` reduced modulo `p` and the entry `atInf` at infinity of the table of `p`, as the
table hands them back: for a point `(a, y, b)` of a curve of even degree with `b ≤ bHigh`, the prime
would divide `b` with a valuation that the mask holds, if it holds every valuation a denominator can
have, or `c_d` would be a square modulo `p`, so that there are points at infinity modulo `p`. -/
theorem not_dvd_of_run_forbiddenOfPrime_eq_inl {c : List ℤ} (hd : degree c % 2 = 0) {p bHigh : ℕ}
    (hp : p.Prime) {cm : Array ℕ} (hcm : ∀ j ≤ degree c, cm[j]! = (c.getD j 0 % (p : ℤ)).toNat)
    {atInf : Bool} (hinf : atInf = (examinePrime c (degree c) p).isFSquare[p]!)
    {e : ForbiddenEntry}
    (he : Id.run (forbiddenOfPrime c (degree c) p bHigh cm atInf) = some (.inl e)) {a y : ℤ}
    {b : ℕ} (hb : b ≠ 0) (hbH : b ≤ bHigh) (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) : ¬p ∣ b := by
  intro hpb
  rcases (eq_of_run_forbiddenOfPrime_eq_inl he).2 with ⟨-, hall⟩ | rfl
  · have : Fact p.Prime := ⟨hp⟩
    have hv : padicValNat p b ≠ 0 := Nat.pos_iff_ne_zero.mp (one_le_padicValNat_of_dvd hb hpb)
    have hle : p ^ padicValNat p b ≤ bHigh := (Nat.le_of_dvd (by lia) pow_padicValNat_dvd).trans hbH
    have := congr(Nat.testBit $hall (padicValNat p b))
    simp only [Nat.testBit_and, testBit_run_allValuations hp.one_lt,
      testBit_run_forbiddenValuations_eq_false_of_sq_eq hd hp bHigh hcm hab hy] at this
    simp [hv, hle] at this
  · rw [getElem!_isFSquare_examinePrime_self, getElem!_squaresMod_of_sq_eq hd hp hab hy hpb,
      Bool.or_true] at hinf
    cases hinf

/-- Whether the forbidden divisor `e` tested by its valuation excludes the denominator `b`: bit
`v_p(b)` of its mask, for the valuation `v_p(b)` of `Ratpoints.Setup.valuation`, the test that the
tests of the word shape make with `e` (`Ratpoints.Sieve.wordsTest`). -/
def ForbiddenVal.excludes (e : ForbiddenVal) (b : ℕ) : Bool :=
  e.mask.testBit (Id.run (Setup.valuation b e.p)).1

theorem ForbiddenVal.excludes_eq_false_iff {e : ForbiddenVal} {b : ℕ} :
    e.excludes b = false ↔ ¬e.mask.testBit (Id.run (Setup.valuation b e.p)).1 = true :=
  Bool.eq_false_iff

/-- A forbidden divisor tested by its valuation that an examined prime `p` gives, from the
coefficients `cm` reduced modulo `p`, excludes no denominator of a point of a curve of even degree:
the valuations of its mask are excluded by the terms of `F(a, b)`
(`Ratpoints.Sieve.forbiddenValuations`). -/
theorem ForbiddenVal.excludes_eq_false_of_run_forbiddenOfPrime_eq_inr {c : List ℤ}
    (hd : degree c % 2 = 0) {p bHigh : ℕ} (hp : p.Prime) {cm : Array ℕ}
    (hcm : ∀ j ≤ degree c, cm[j]! = (c.getD j 0 % (p : ℤ)).toNat) {atInf : Bool}
    {e : ForbiddenVal}
    (he : Id.run (forbiddenOfPrime c (degree c) p bHigh cm atInf) = some (.inr e))
    {a y : ℤ} {b : ℕ} (hb : b ≠ 0) (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    e.excludes b = false := by
  obtain rfl := eq_of_run_forbiddenOfPrime_eq_inr he
  rw [excludes_eq_false_iff, Setup.fst_run_valuation (Int.natCast_ne_zero.mpr hb) hp.one_lt,
    Int.natAbs_natCast, Bool.not_eq_true]
  exact testBit_run_forbiddenValuations_eq_false_of_sq_eq hd hp bHigh hcm hab hy

/-- A forbidden divisor tested with words that `Ratpoints.Sieve.examinePrimes` and
`Ratpoints.Sieve.forbidden` may record: the one that `Ratpoints.Sieve.forbiddenOfPrime` gives for a
prime `p` of `Ratpoints.primeTable` from the coefficients reduced modulo `p` and the entry at
infinity of the table of the reference (`Ratpoints.Sieve.examinePrime`), what
`Ratpoints.Sieve.examinePrime?` hands back for the primes the loop of the tables examines, or a
prime of the table with its words (`Ratpoints.Sieve.forbiddenRow`) at which `c_d` is not a square
modulo it. -/
def IsForbiddenEntry (c : List ℤ) (d bHigh : ℕ) (e : ForbiddenEntry) : Prop :=
  (∃ p ∈ primeTable, Id.run (forbiddenOfPrime c d p bHigh
      ((Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)
      (examinePrime c d p).isFSquare[p]!) = some (.inl e)) ∨
    (e.p ∈ primeTable ∧ e.words = forbiddenRow e.p ∧
      (squaresMod e.p)[(c.getD d 0 % (e.p : ℤ)).toNat]! = false)

/-- A forbidden divisor tested by its valuation that `Ratpoints.Sieve.examinePrimes` may record:
the one that `Ratpoints.Sieve.forbiddenOfPrime` gives for a prime `p` of `Ratpoints.primeTable` from
the coefficients reduced modulo `p` and the entry at infinity of the table of the reference
(`Ratpoints.Sieve.examinePrime`). -/
def IsForbiddenVal (c : List ℤ) (d bHigh : ℕ) (e : ForbiddenVal) : Prop :=
  ∃ p ∈ primeTable, Id.run (forbiddenOfPrime c d p bHigh
    ((Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)
    (examinePrime c d p).isFSquare[p]!) = some (.inr e)

theorem getElem!_map_range_toNat_emod (c : List ℤ) (d p : ℕ) {j : ℕ} (hj : j ≤ d) :
    ((Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)[j]! =
      (c.getD j 0 % (p : ℤ)).toNat :=
  Array.getElem!_map_range _ (Nat.lt_succ_of_le hj)

theorem IsForbiddenEntry.prime {c : List ℤ} {d bHigh : ℕ} {e : ForbiddenEntry}
    (h : IsForbiddenEntry c d bHigh e) : e.p.Prime := by
  rcases h with ⟨p, hp, h⟩ | ⟨h, -⟩
  · obtain ⟨rfl, -⟩ := eq_of_run_forbiddenOfPrime_eq_inl h
    exact prime_of_mem_primeTable hp
  · exact prime_of_mem_primeTable h

theorem IsForbiddenEntry.words_eq {c : List ℤ} {d bHigh : ℕ} {e : ForbiddenEntry}
    (h : IsForbiddenEntry c d bHigh e) : e.words = forbiddenRow e.p := by
  rcases h with ⟨p, -, h⟩ | ⟨-, h, -⟩
  · obtain ⟨rfl, -⟩ := eq_of_run_forbiddenOfPrime_eq_inl h
    dsimp only
  · exact h

/-- A forbidden divisor tested with words divides no denominator `b ≤ bHigh` of a point of a curve
of even degree: either every valuation that such a denominator can have at `p` is excluded by the
terms of `F(a, b)` (`Ratpoints.Sieve.forbiddenValuations`), or `c_d` is not a square modulo `p`
while `F(a, b) ≡ c_d a ^ d (mod p)` for `p ∣ b`. -/
theorem IsForbiddenEntry.not_dvd {c : List ℤ} {bHigh : ℕ} {e : ForbiddenEntry}
    (h : IsForbiddenEntry c (degree c) bHigh e) (hd : degree c % 2 = 0) {a y : ℤ} {b : ℕ}
    (hb : b ≠ 0) (hbH : b ≤ bHigh) (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    ¬e.p ∣ b := by
  rcases h with ⟨p, hp, h⟩ | ⟨h, -, hsq⟩
  · obtain ⟨rfl, -⟩ := eq_of_run_forbiddenOfPrime_eq_inl h
    exact not_dvd_of_run_forbiddenOfPrime_eq_inl hd (prime_of_mem_primeTable hp)
      (fun _ hj ↦ getElem!_map_range_toNat_emod c _ p hj) rfl h hb hbH hab hy
  · exact fun hpb ↦ Bool.false_ne_true (hsq.symm.trans
      (getElem!_squaresMod_of_sq_eq hd (prime_of_mem_primeTable h) hab hy hpb))

/-- A forbidden divisor tested by its valuation excludes no denominator of a point of a curve of
even degree (`Ratpoints.Sieve.ForbiddenVal.excludes_eq_false_of_run_forbiddenOfPrime_eq_inr`). -/
theorem IsForbiddenVal.excludes_eq_false {c : List ℤ} {bHigh : ℕ} {e : ForbiddenVal}
    (h : IsForbiddenVal c (degree c) bHigh e) (hd : degree c % 2 = 0) {a y : ℤ} {b : ℕ}
    (hb : b ≠ 0) (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    e.excludes b = false :=
  let ⟨p, hp, h⟩ := h
  ForbiddenVal.excludes_eq_false_of_run_forbiddenOfPrime_eq_inr hd (prime_of_mem_primeTable hp)
    (fun _ hj ↦ getElem!_map_range_toNat_emod c _ p hj) h hb hab hy

/-! ### The loop of the tables -/

/-- The forbidden divisor that the prime at the position `k < Ratpoints.numPrimes` of the table
gives from what its table hands back (`Ratpoints.Sieve.examinePrime?`) is that of the coefficients
reduced modulo the prime and the entry at infinity of the table of the reference. -/
theorem run_forbiddenOfPrime_eq_of_run_examinePrime?_eq_some {c : List ℤ} {d k : ℕ} {u : Bool}
    {e : Entry} {cm : Array ℕ} (hk : k < numPrimes)
    (he : Id.run (examinePrime? c d primeTable[k]! u) = some (e, cm)) (bHigh : ℕ) :
    Id.run (forbiddenOfPrime c d primeTable[k]! bHigh cm e.isFSquare[primeTable[k]!]!) =
      Id.run (forbiddenOfPrime c d primeTable[k]! bHigh
        ((Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (primeTable[k]! : ℤ)).toNat)
        (examinePrime c d primeTable[k]!).isFSquare[primeTable[k]!]!) := by
  rw [eq_map_range_of_run_examinePrime?_eq_some he,
    eq_examinePrime_of_lt_numPrimes_of_run_examinePrime?_eq_some hk he]

/-- The invariant of the loop of `Ratpoints.Sieve.examinePrimes` over the positions of the first
primes of the table, after `k` of them, on the tables and the forbidden divisors found: the tables
are those of the reference of the primes `Ratpoints.primeTable[i]`, `i < k`, and the forbidden
divisors are at most `maxForbidden` of those that the loop may record
(`Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`). -/
def ExaminePrimesInvariant (c : List ℤ) (d maxForbidden bHigh k : ℕ) (tables : Array Entry)
    (ba : Array ForbiddenEntry) (val : Array ForbiddenVal) : Prop :=
  tables.size = k ∧
    (∀ (i : ℕ) (hi : i < tables.size), tables[i] = examinePrime c d primeTable[i]!) ∧
    (∀ e ∈ ba, IsForbiddenEntry c d bHigh e) ∧ (∀ e ∈ val, IsForbiddenVal c d bHigh e) ∧
    ba.size + val.size ≤ maxForbidden

/-- The invariant of the loop of `Ratpoints.Sieve.examinePrimes` with the positions `suff` still to
come, on the result of an early return, the tables and the forbidden divisors:
`Ratpoints.Sieve.ExaminePrimesInvariant` after the positions `pref` without a result, and a result,
which is `none` and comes from a position `pn < n` whose prime has no table
(`Ratpoints.Sieve.examinePrime?`), only at the end. -/
def ExaminePrimesLoopInvariant (c : List ℤ) (d : ℕ) (u : Bool) (n maxForbidden bHigh : ℕ)
    (pref suff : List ℕ)
    (st : Option (Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal)) ×
      Array Entry × Array ForbiddenEntry × Array ForbiddenVal) : Prop :=
  st.1.elim (ExaminePrimesInvariant c d maxForbidden bHigh pref.length st.2.1 st.2.2.1 st.2.2.2)
    fun r ↦ suff = [] ∧ r = none ∧ ∃ pn < n, Id.run (examinePrime? c d primeTable[pn]! u) = none

theorem examinePrimesLoopInvariant_empty (c : List ℤ) (d : ℕ) (u : Bool)
    (n maxForbidden bHigh : ℕ) (suff : List ℕ) :
    ExaminePrimesLoopInvariant c d u n maxForbidden bHigh [] suff (none, #[], #[], #[]) :=
  ⟨rfl, fun _ hi ↦ absurd hi (Nat.not_lt_zero _), nofun, nofun, Nat.zero_le _⟩

/-- Before the last position, the loop of `Ratpoints.Sieve.examinePrimes` has not returned. -/
theorem ExaminePrimesLoopInvariant.examinePrimesInvariant {c : List ℤ} {d : ℕ} {u : Bool}
    {n maxForbidden bHigh cur : ℕ} {pref suff : List ℕ} {o : Option (Option
      (Array Entry × Array ForbiddenEntry × Array ForbiddenVal))} {tables : Array Entry}
    {ba : Array ForbiddenEntry} {val : Array ForbiddenVal}
    (h : ExaminePrimesLoopInvariant c d u n maxForbidden bHigh pref (cur :: suff)
      (o, tables, ba, val)) :
    ExaminePrimesInvariant c d maxForbidden bHigh pref.length tables ba val := by
  cases o with
  | none => exact h
  | some r => exact absurd h.1 (List.cons_ne_nil _ _)

/-- After a step of the loop of `Ratpoints.Sieve.examinePrimes` without a return. -/
theorem ExaminePrimesInvariant.examinePrimesLoopInvariant {c : List ℤ} {d : ℕ} {u : Bool}
    {n maxForbidden bHigh : ℕ} {pref : List ℕ} {tables : Array Entry} {ba : Array ForbiddenEntry}
    {val : Array ForbiddenVal}
    (h : ExaminePrimesInvariant c d maxForbidden bHigh (pref.length + 1) tables ba val)
    (cur : ℕ) (suff : List ℕ) :
    ExaminePrimesLoopInvariant c d u n maxForbidden bHigh (pref ++ [cur]) suff
      (none, tables, ba, val) := by
  change ExaminePrimesInvariant c d maxForbidden bHigh (pref ++ [cur]).length tables ba val
  rwa [List.length_append, List.length_singleton]

/-- The step of the loop of `Ratpoints.Sieve.examinePrimes` at the position
`k < Ratpoints.numPrimes`, whose prime has a table (`Ratpoints.Sieve.examinePrime?`), the table of
the reference: the table is kept, and the forbidden divisors become `ba'` and `val'`. -/
theorem ExaminePrimesInvariant.push {c : List ℤ} {d maxForbidden bHigh k : ℕ} {u : Bool}
    {tables : Array Entry} {ba ba' : Array ForbiddenEntry} {val val' : Array ForbiddenVal}
    {e : Entry} {cm : Array ℕ} (h : ExaminePrimesInvariant c d maxForbidden bHigh k tables ba val)
    (hk : k < numPrimes) (he : Id.run (examinePrime? c d primeTable[k]! u) = some (e, cm))
    (hba : ∀ f ∈ ba', IsForbiddenEntry c d bHigh f) (hval : ∀ f ∈ val', IsForbiddenVal c d bHigh f)
    (hsize : ba'.size + val'.size ≤ maxForbidden) :
    ExaminePrimesInvariant c d maxForbidden bHigh (k + 1) (tables.push e) ba' val' := by
  obtain ⟨hs, ht, -⟩ := h
  refine ⟨by simp [hs], fun i hi ↦ ?_, hba, hval, hsize⟩
  rw [Array.getElem_push]
  split
  · exact ht i _
  · obtain rfl : i = k := by simp at hi; lia
    exact eq_examinePrime_of_lt_numPrimes_of_run_examinePrime?_eq_some hk he

-- The position at the cursor of the loop of `Ratpoints.Sieve.examinePrimes` is that of a prime of
-- the table, the number of positions done.
private theorem eq_length_and_lt_of_toList_eq {n cur : ℕ} {pref suff : List ℕ}
    (hl : ForIn.toList [:n] = pref ++ cur :: suff) (hn : n ≤ numPrimes) :
    pref.length = cur ∧ cur < numPrimes :=
  ⟨Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl,
    (Std.Legacy.Range.lt_of_toList_eq_append_cons hl).trans_le hn⟩

/-- A forbidden divisor tested with words that the prime at the position `k < Ratpoints.numPrimes`
gives from what its table hands back is one that the loop of the tables may record. -/
theorem isForbiddenEntry_of_run_examinePrime?_eq_some {c : List ℤ} {d bHigh k : ℕ} {u : Bool}
    {e : Entry} {cm : Array ℕ} {f : ForbiddenEntry} (hk : k < numPrimes)
    (he : Id.run (examinePrime? c d primeTable[k]! u) = some (e, cm))
    (hf : Id.run (forbiddenOfPrime c d primeTable[k]! bHigh cm e.isFSquare[primeTable[k]!]!) =
      some (.inl f)) :
    IsForbiddenEntry c d bHigh f :=
  .inl ⟨_, Array.getElem!_mem (hk.trans_le numPrimes_le_size_primeTable),
    (run_forbiddenOfPrime_eq_of_run_examinePrime?_eq_some hk he bHigh) ▸ hf⟩

/-- A forbidden divisor tested by its valuation that the prime at the position
`k < Ratpoints.numPrimes` gives from what its table hands back is one that the loop of the tables
may record. -/
theorem isForbiddenVal_of_run_examinePrime?_eq_some {c : List ℤ} {d bHigh k : ℕ} {u : Bool}
    {e : Entry} {cm : Array ℕ} {f : ForbiddenVal} (hk : k < numPrimes)
    (he : Id.run (examinePrime? c d primeTable[k]! u) = some (e, cm))
    (hf : Id.run (forbiddenOfPrime c d primeTable[k]! bHigh cm e.isFSquare[primeTable[k]!]!) =
      some (.inr f)) :
    IsForbiddenVal c d bHigh f :=
  ⟨_, Array.getElem!_mem (hk.trans_le numPrimes_le_size_primeTable),
    (run_forbiddenOfPrime_eq_of_run_examinePrime?_eq_some hk he bHigh) ▸ hf⟩

/-- The step of the loop of `Ratpoints.Sieve.examinePrimes` that records a forbidden divisor tested
with words. -/
theorem ExaminePrimesLoopInvariant.push_inl {c : List ℤ} {d : ℕ} {u checkDenom : Bool}
    {n maxForbidden bHigh cur : ℕ} {pref suff : List ℕ}
    {o : Option (Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal))}
    {tables : Array Entry} {ba : Array ForbiddenEntry} {val : Array ForbiddenVal} {e : Entry}
    {cm : Array ℕ} {r : Option (ForbiddenEntry ⊕ ForbiddenVal)} {f : ForbiddenEntry}
    (hn : n ≤ numPrimes) (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : ExaminePrimesLoopInvariant c d u n maxForbidden bHigh pref (cur :: suff)
      (o, tables, ba, val))
    (he : Id.run (examinePrime? c d primeTable[cur]! u) = some (e, cm))
    (hlt : (checkDenom && decide (ba.size + val.size < maxForbidden)) = true)
    (hr : r = Id.run
      (forbiddenOfPrime c d primeTable[cur]! bHigh cm e.isFSquare[primeTable[cur]!]!))
    (hf : r = some (.inl f)) :
    ExaminePrimesLoopInvariant c d u n maxForbidden bHigh (pref ++ [cur]) suff
      (none, tables.push e, ba.push f, val) := by
  obtain ⟨rfl, hk⟩ := eq_length_and_lt_of_toList_eq hl hn
  have h' := h.examinePrimesInvariant
  refine (h'.push hk he (Array.forall_mem_push.mpr ⟨isForbiddenEntry_of_run_examinePrime?_eq_some
    hk he (hr ▸ hf), h'.2.2.1⟩) h'.2.2.2.1 ?_).examinePrimesLoopInvariant _ _
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
  simp only [Array.size_push]
  lia

/-- The step of the loop of `Ratpoints.Sieve.examinePrimes` that records a forbidden divisor tested
by its valuation. -/
theorem ExaminePrimesLoopInvariant.push_inr {c : List ℤ} {d : ℕ} {u checkDenom : Bool}
    {n maxForbidden bHigh cur : ℕ} {pref suff : List ℕ}
    {o : Option (Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal))}
    {tables : Array Entry} {ba : Array ForbiddenEntry} {val : Array ForbiddenVal} {e : Entry}
    {cm : Array ℕ} {r : Option (ForbiddenEntry ⊕ ForbiddenVal)} {f : ForbiddenVal}
    (hn : n ≤ numPrimes) (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : ExaminePrimesLoopInvariant c d u n maxForbidden bHigh pref (cur :: suff)
      (o, tables, ba, val))
    (he : Id.run (examinePrime? c d primeTable[cur]! u) = some (e, cm))
    (hlt : (checkDenom && decide (ba.size + val.size < maxForbidden)) = true)
    (hr : r = Id.run
      (forbiddenOfPrime c d primeTable[cur]! bHigh cm e.isFSquare[primeTable[cur]!]!))
    (hf : r = some (.inr f)) :
    ExaminePrimesLoopInvariant c d u n maxForbidden bHigh (pref ++ [cur]) suff
      (none, tables.push e, ba, val.push f) := by
  obtain ⟨rfl, hk⟩ := eq_length_and_lt_of_toList_eq hl hn
  have h' := h.examinePrimesInvariant
  refine (h'.push hk he h'.2.2.1 (Array.forall_mem_push.mpr
    ⟨isForbiddenVal_of_run_examinePrime?_eq_some hk he (hr ▸ hf), h'.2.2.2.1⟩)
    ?_).examinePrimesLoopInvariant _ _
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hlt
  simp only [Array.size_push]
  lia

/-- The step of the loop of `Ratpoints.Sieve.examinePrimes` that keeps the table and records no
forbidden divisor. -/
theorem ExaminePrimesLoopInvariant.push {c : List ℤ} {d : ℕ} {u : Bool}
    {n maxForbidden bHigh cur : ℕ} {pref suff : List ℕ}
    {o : Option (Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal))}
    {tables : Array Entry} {ba : Array ForbiddenEntry} {val : Array ForbiddenVal} {e : Entry}
    {cm : Array ℕ} (hn : n ≤ numPrimes) (hl : ForIn.toList [:n] = pref ++ cur :: suff)
    (h : ExaminePrimesLoopInvariant c d u n maxForbidden bHigh pref (cur :: suff)
      (o, tables, ba, val))
    (he : Id.run (examinePrime? c d primeTable[cur]! u) = some (e, cm)) :
    ExaminePrimesLoopInvariant c d u n maxForbidden bHigh (pref ++ [cur]) suff
      (none, tables.push e, ba, val) := by
  obtain ⟨rfl, hk⟩ := eq_length_and_lt_of_toList_eq hl hn
  have h' := h.examinePrimesInvariant
  exact (h'.push hk he h'.2.2.1 h'.2.2.2.1 h'.2.2.2.2).examinePrimesLoopInvariant _ _

/-- The early return of the loop of `Ratpoints.Sieve.examinePrimes` at a position whose prime has no
table (`Ratpoints.Sieve.examinePrime?`). -/
theorem examinePrimesLoopInvariant_some_none {c : List ℤ} {d : ℕ} {u : Bool}
    {n maxForbidden bHigh cur : ℕ} {pref suff pref' : List ℕ} {tables : Array Entry}
    {ba : Array ForbiddenEntry} {val : Array ForbiddenVal} {x : Option (Entry × Array ℕ)}
    (hl : ForIn.toList [:n] = pref ++ cur :: suff) (hx : ∀ e cm, x = some (e, cm) → False)
    (he : Id.run (examinePrime? c d primeTable[cur]! u) = x) :
    ExaminePrimesLoopInvariant c d u n maxForbidden bHigh pref' [] (some none, tables, ba, val) :=
  ⟨rfl, rfl, cur, Std.Legacy.Range.lt_of_toList_eq_append_cons hl,
    he.trans (Option.eq_none_iff_forall_ne_some.mpr fun ⟨e, cm⟩ h ↦ hx e cm h)⟩

/-- The end of the loop of `Ratpoints.Sieve.examinePrimes` after an early return. -/
theorem ExaminePrimesLoopInvariant.post_some {c : List ℤ} {d : ℕ} {u : Bool}
    {n maxForbidden bHigh : ℕ} {pref : List ℕ}
    {o : Option (Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal))}
    {tables : Array Entry} {ba : Array ForbiddenEntry} {val : Array ForbiddenVal}
    {r : Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal)}
    (h : ExaminePrimesLoopInvariant c d u n maxForbidden bHigh pref [] (o, tables, ba, val))
    (ho : o = some r) :
    (∀ tables ba val, r = some (tables, ba, val) → tables.size = n ∧
        (∀ (i : ℕ) (hi : i < tables.size), tables[i] = examinePrime c d primeTable[i]!) ∧
        (∀ e ∈ ba, IsForbiddenEntry c d bHigh e) ∧ (∀ e ∈ val, IsForbiddenVal c d bHigh e) ∧
        ba.size + val.size ≤ maxForbidden) ∧
      (r = none → ∃ pn < n, Id.run (examinePrime? c d primeTable[pn]! u) = none) := by
  subst ho
  obtain ⟨-, rfl, h⟩ := h
  exact ⟨fun _ _ _ h' ↦ (nomatch h'), fun _ ↦ h⟩

/-- The end of the loop of `Ratpoints.Sieve.examinePrimes` over all the positions `pn < n`. -/
theorem ExaminePrimesLoopInvariant.post_none {c : List ℤ} {d : ℕ} {u : Bool}
    {n maxForbidden bHigh : ℕ}
    {o : Option (Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal))}
    {tables : Array Entry} {ba : Array ForbiddenEntry} {val : Array ForbiddenVal}
    (h : ExaminePrimesLoopInvariant c d u n maxForbidden bHigh (ForIn.toList [:n]) []
      (o, tables, ba, val)) (ho : o = none) :
    (∀ tables' ba' val', some (tables, ba, val) = some (tables', ba', val') → tables'.size = n ∧
        (∀ (i : ℕ) (hi : i < tables'.size), tables'[i] = examinePrime c d primeTable[i]!) ∧
        (∀ e ∈ ba', IsForbiddenEntry c d bHigh e) ∧ (∀ e ∈ val', IsForbiddenVal c d bHigh e) ∧
        ba'.size + val'.size ≤ maxForbidden) ∧
      (some (tables, ba, val) = none →
        ∃ pn < n, Id.run (examinePrime? c d primeTable[pn]! u) = none) := by
  subst ho
  refine ⟨fun _ _ _ h' ↦ ?_, nofun⟩
  simp only [Option.some.injEq, Prod.mk.injEq] at h'
  obtain ⟨rfl, rfl, rfl⟩ := h'
  obtain ⟨hs, h⟩ := h
  exact ⟨by rw [hs, Std.Legacy.Range.length_toList, Nat.sub_zero], h⟩

-- The table of a prime and the entry that an examined prime gives, as values for the contract of
-- the loop of the tables.
private theorem examinePrime?_value (c : List ℤ) (d p : ℕ) (u : Bool) :
    ⦃ True ⦄ examinePrime? c d p u ⦃ fun r ↦ r = Id.run (examinePrime? c d p u) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem forbiddenOfPrime_value (c : List ℤ) (d p bHigh : ℕ) (cm : Array ℕ) (atInf : Bool) :
    ⦃ True ⦄ forbiddenOfPrime c d p bHigh cm atInf
    ⦃ fun r ↦ r = Id.run (forbiddenOfPrime c d p bHigh cm atInf) ⦄ :=
  ⟨fun _ ↦ rfl⟩

attribute [local irreducible] ExaminePrimesInvariant ExaminePrimesLoopInvariant primeTable in
/-- The contract of `Ratpoints.Sieve.examinePrimes` for `n ≤ Ratpoints.numPrimes`: on tables and
forbidden divisors, a table for each of the first `n` primes of the table, that of the reference
(`Ratpoints.Sieve.examinePrime`), and at most `maxForbidden` forbidden divisors, each one that the
loop may record (`Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`); on none, one
of these primes has no table (`Ratpoints.Sieve.examinePrime?`), the curve having no points modulo
it. -/
@[spec]
theorem examinePrimes_spec (c : List ℤ) (d : ℕ) (u checkDenom : Bool) (n maxForbidden bHigh : ℕ) :
    ⦃ n ≤ numPrimes ⦄ examinePrimes c d u checkDenom n maxForbidden bHigh
    ⦃ fun r ↦ (∀ tables ba val, r = some (tables, ba, val) → tables.size = n ∧
        (∀ (i : ℕ) (hi : i < tables.size), tables[i] = examinePrime c d primeTable[i]!) ∧
        (∀ e ∈ ba, IsForbiddenEntry c d bHigh e) ∧ (∀ e ∈ val, IsForbiddenVal c d bHigh e) ∧
        ba.size + val.size ≤ maxForbidden) ∧
      (r = none → ∃ pn < n, Id.run (examinePrime? c d primeTable[pn]! u) = none) ⦄ := by
  vcgen [examinePrimes, examinePrime?_value, forbiddenOfPrime_value] invariants
  | inv1 => fun pref suff st ↦ ExaminePrimesLoopInvariant c d u n maxForbidden bHigh pref suff st
  all_goals try dsimp only at *
  all_goals try obtain rfl := ‹_ = Id.run (examinePrime? _ _ _ _)›
  all_goals first
    | exact examinePrimesLoopInvariant_empty c d u n maxForbidden bHigh _
    | exact ExaminePrimesLoopInvariant.post_some ‹_› ‹_›
    | exact ExaminePrimesLoopInvariant.post_none ‹_› ‹_›
    | exact ExaminePrimesLoopInvariant.push_inl ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact ExaminePrimesLoopInvariant.push_inr ‹_› ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact ExaminePrimesLoopInvariant.push ‹_› ‹_› ‹_› ‹_›
    | exact examinePrimesLoopInvariant_some_none ‹_› ‹_› ‹_›

-- `Ratpoints.Sieve.examinePrimes_spec` as a plain statement.
private theorem run_examinePrimes_spec {c : List ℤ} {d : ℕ} {u checkDenom : Bool}
    {n maxForbidden bHigh : ℕ} (hn : n ≤ numPrimes) :
    (∀ tables ba val, Id.run (examinePrimes c d u checkDenom n maxForbidden bHigh) =
        some (tables, ba, val) → tables.size = n ∧
        (∀ (i : ℕ) (hi : i < tables.size), tables[i] = examinePrime c d primeTable[i]!) ∧
        (∀ e ∈ ba, IsForbiddenEntry c d bHigh e) ∧ (∀ e ∈ val, IsForbiddenVal c d bHigh e) ∧
        ba.size + val.size ≤ maxForbidden) ∧
      (Id.run (examinePrimes c d u checkDenom n maxForbidden bHigh) = none →
        ∃ pn < n, Id.run (examinePrime? c d primeTable[pn]! u) = none) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((examinePrimes_spec c d u checkDenom n maxForbidden bHigh).le_wp hn)

theorem size_eq_of_run_examinePrimes_eq_some {c : List ℤ} {d : ℕ} {u checkDenom : Bool}
    {n maxForbidden bHigh : ℕ} {tables : Array Entry} {ba : Array ForbiddenEntry}
    {val : Array ForbiddenVal}
    (h : Id.run (examinePrimes c d u checkDenom n maxForbidden bHigh) = some (tables, ba, val))
    (hn : n ≤ numPrimes) : tables.size = n :=
  ((run_examinePrimes_spec hn).1 _ _ _ h).1

/-- The tables that the loop of the tables keeps are those of the reference. -/
theorem getElem_eq_examinePrime_of_run_examinePrimes_eq_some {c : List ℤ} {d : ℕ}
    {u checkDenom : Bool} {n maxForbidden bHigh : ℕ} {tables : Array Entry}
    {ba : Array ForbiddenEntry} {val : Array ForbiddenVal}
    (h : Id.run (examinePrimes c d u checkDenom n maxForbidden bHigh) = some (tables, ba, val))
    (hn : n ≤ numPrimes) (i : ℕ) (hi : i < tables.size) :
    tables[i] = examinePrime c d primeTable[i]! :=
  ((run_examinePrimes_spec hn).1 _ _ _ h).2.1 i hi

theorem isForbiddenEntry_of_run_examinePrimes_eq_some {c : List ℤ} {d : ℕ} {u checkDenom : Bool}
    {n maxForbidden bHigh : ℕ} {tables : Array Entry} {ba : Array ForbiddenEntry}
    {val : Array ForbiddenVal}
    (h : Id.run (examinePrimes c d u checkDenom n maxForbidden bHigh) = some (tables, ba, val))
    (hn : n ≤ numPrimes) {e : ForbiddenEntry} (he : e ∈ ba) : IsForbiddenEntry c d bHigh e :=
  ((run_examinePrimes_spec hn).1 _ _ _ h).2.2.1 e he

theorem isForbiddenVal_of_run_examinePrimes_eq_some {c : List ℤ} {d : ℕ} {u checkDenom : Bool}
    {n maxForbidden bHigh : ℕ} {tables : Array Entry} {ba : Array ForbiddenEntry}
    {val : Array ForbiddenVal}
    (h : Id.run (examinePrimes c d u checkDenom n maxForbidden bHigh) = some (tables, ba, val))
    (hn : n ≤ numPrimes) {e : ForbiddenVal} (he : e ∈ val) : IsForbiddenVal c d bHigh e :=
  ((run_examinePrimes_spec hn).1 _ _ _ h).2.2.2.1 e he

/-- When the loop of the tables over the first `n ≤ Ratpoints.numPrimes` primes takes its exit, the
curve has no points of any height (`Ratpoints.Sieve.not_isPoint_of_run_examinePrime?_eq_none`). -/
theorem not_isPoint_of_run_examinePrimes_eq_none {c : List ℤ} {u checkDenom : Bool}
    {n maxForbidden bHigh : ℕ}
    (h : Id.run (examinePrimes c (degree c) u checkDenom n maxForbidden bHigh) = none)
    (hn : n ≤ numPrimes) (H : ℕ) (q : ℤ × ℤ × ℤ) : ¬IsPoint c H q := by
  obtain ⟨pn, hpn, he⟩ := (run_examinePrimes_spec hn).2 h
  exact not_isPoint_of_lt_numPrimes_of_run_examinePrime?_eq_none (hpn.trans_le hn) he H q

/-! ### The further primes -/

/-- The step of the loop of `Ratpoints.Sieve.forbidden` over the further primes that records a
prime of the table at which `c_d` is not a square modulo it, with its words: the forbidden divisors
stay of the kind that `Ratpoints.Sieve.IsForbiddenEntry` describes. -/
theorem forall_isForbiddenEntry_push {c : List ℤ} {d examined bHigh : ℕ} {pref suff : List ℕ}
    {cur : ℕ} {ba : Array ForbiddenEntry} (h : ∀ e ∈ ba, IsForbiddenEntry c d bHigh e)
    (hl : ForIn.toList [examined:primeTable.size] = pref ++ cur :: suff)
    (hs : (!(squaresMod primeTable[cur]!)[(c.getD d 0 % (primeTable[cur]! : ℤ)).toNat]!) = true) :
    ∀ e ∈ ba.push ⟨primeTable[cur]!, forbiddenRow primeTable[cur]!⟩,
      IsForbiddenEntry c d bHigh e := by
  have hcur : cur < primeTable.size := by
    have := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
    have := Std.Legacy.Range.length_add_length_add_one_of_toList_eq_append_cons hl
    lia
  -- `rfl` for the words would unfold `Ratpoints.Sieve.forbiddenRow` until the recursion limit
  exact Array.forall_mem_push.mpr ⟨.inr ⟨Array.getElem!_mem hcur, by dsimp only,
    Bool.not_eq_true' _ ▸ hs⟩, h⟩

theorem forall_isForbiddenEntry_and_forall_isForbiddenVal {c : List ℤ} {d bHigh : ℕ}
    {ba : Array ForbiddenEntry} {val : Array ForbiddenVal}
    (h : ∀ e ∈ val, IsForbiddenVal c d bHigh e) (h' : ∀ e ∈ ba, IsForbiddenEntry c d bHigh e) :
    (∀ e ∈ ba.toList, IsForbiddenEntry c d bHigh e) ∧
      ∀ e ∈ val.toList, IsForbiddenVal c d bHigh e :=
  ⟨fun e he ↦ h' e (Array.mem_toList_iff.mp he), fun e he ↦ h e (Array.mem_toList_iff.mp he)⟩

attribute [local irreducible] IsForbiddenEntry IsForbiddenVal in
/-- The contract of `Ratpoints.Sieve.forbidden`: from forbidden divisors `ba` and `val` of the
kinds that `Ratpoints.Sieve.IsForbiddenEntry` and `Ratpoints.Sieve.IsForbiddenVal` describe, such
as the loop of the tables records, it returns forbidden divisors of the same kinds, since the
further primes add only primes of the table with their words at which `c_d` is not a square modulo
the prime, and `val` passes through. -/
@[spec]
theorem forbidden_spec (c : List ℤ) (d examined maxForbidden bHigh : ℕ) (ba : Array ForbiddenEntry)
    (val : Array ForbiddenVal) :
    ⦃ (∀ e ∈ ba, IsForbiddenEntry c d bHigh e) ∧ ∀ e ∈ val, IsForbiddenVal c d bHigh e ⦄
    forbidden c d examined maxForbidden bHigh ba val
    ⦃ fun r ↦ (∀ e ∈ r.1, IsForbiddenEntry c d bHigh e) ∧
        ∀ e ∈ r.2, IsForbiddenVal c d bHigh e ⦄ := by
  vcgen [forbidden] invariants
  · fun _ _ ba ↦ ∀ e ∈ ba, IsForbiddenEntry c d bHigh e
  all_goals try dsimp only at *
  all_goals have h :=
    ‹(∀ e ∈ ba, IsForbiddenEntry c d bHigh e) ∧ ∀ e ∈ val, IsForbiddenVal c d bHigh e›
  all_goals first
    | exact h.1 _ ‹_›
    | exact forall_isForbiddenEntry_and_forall_isForbiddenVal h.2
        ‹∀ e ∈ _, IsForbiddenEntry _ _ _ e›
    | exact forall_isForbiddenEntry_and_forall_isForbiddenVal h.2 h.1
    | exact forall_isForbiddenEntry_push ‹_› ‹_› ‹_›
    | assumption

/-! ### The words of a forbidden divisor -/

-- The words of `Ratpoints.Sieve.forbiddenRow` after the bits of the first `k` multiples of `p` are
-- cleared.
private theorem size_fold_modify (p k : ℕ) :
    (Nat.fold k (fun i _ row ↦ row.modify (p * i / 64) (· &&& ~~~(1 <<< (p * i % 64).toUInt64)))
      (Array.replicate p (~~~0 : UInt64))).size = p := by
  induction k with
  | zero => simp
  | succ k ih => rw [Nat.fold_succ, Array.size_modify, ih]

private theorem exists_lt_succ_mul_eq_iff {p k r t : ℕ} (ht : t < 64) :
    (∃ i < k + 1, p * i = 64 * r + t) ↔
      (∃ i < k, p * i = 64 * r + t) ∨ (p * k / 64 = r ∧ t = p * k % 64) := by
  rw [Nat.exists_lt_succ_right]
  exact or_congr_right ⟨fun h ↦ ⟨by lia, by lia⟩, fun h ↦ by lia⟩

private theorem getLsbD_fold_modify {p r : ℕ} (hr : r < p) (k t : ℕ) :
    (Nat.fold k (fun i _ row ↦ row.modify (p * i / 64) (· &&& ~~~(1 <<< (p * i % 64).toUInt64)))
      (Array.replicate p (~~~0 : UInt64)))[r]!.toBitVec.getLsbD t =
      (decide (t < 64) && !decide (∃ i < k, p * i = 64 * r + t)) := by
  induction k with
  | zero =>
    rw [Nat.fold_zero, getElem!_pos _ r (by rwa [Array.size_replicate]),
      Array.getElem_replicate, UInt64.getLsbD_allOnes]
    simp
  | succ k ih =>
    rw [Nat.fold_succ, getElem!_pos _ r (by rwa [Array.size_modify, size_fold_modify]),
      Array.getElem_modify, ← getElem!_pos _ r (by rwa [size_fold_modify])]
    rcases Nat.lt_or_ge t 64 with ht | ht
    · simp only [decide_eq_true ht, Bool.true_and, exists_lt_succ_mul_eq_iff ht]
      split
      · rw [UInt64.toBitVec_and, BitVec.getLsbD_and, ih, UInt64.toBitVec_not, BitVec.getLsbD_not,
          UInt64.getLsbD_one_shiftLeft (Nat.mod_lt _ (by decide))]
        simp [*]
      · rw [ih]
        simp [*]
    · simp [BitVec.getLsbD_of_ge _ _ ht, decide_eq_false (Nat.not_lt.mpr ht)]

-- The multiples `p i`, `i < 64`, of `p` are those among the positions `64 r + t` with `r < p` and
-- `t < 64`.
private theorem exists_lt_mul_eq_iff {p r t : ℕ} (hr : r < p) (ht : t < 64) :
    (∃ i < 64, p * i = 64 * r + t) ↔ (64 * r + t) % p = 0 := by
  refine ⟨fun ⟨i, _, h⟩ ↦ h ▸ Nat.mul_mod_right p i, fun h ↦ ⟨(64 * r + t) / p, ?_,
    Nat.mul_div_cancel' (Nat.dvd_of_mod_eq_zero h)⟩⟩
  rw [Nat.div_lt_iff_lt_mul (by lia)]
  lia

/-- Bit `t` of word `r < p` of the words of the forbidden divisor `p` is clear exactly when
`p ∣ 64 r + t`, the multiples `p i` of `p` with `i < 64` being cleared. -/
theorem getLsbD_getElem!_forbiddenRow {p r : ℕ} (hr : r < p) (t : ℕ) :
    (forbiddenRow p)[r]!.toBitVec.getLsbD t = (decide (t < 64) && (64 * r + t) % p != 0) := by
  rw [forbiddenRow, getLsbD_fold_modify hr]
  rcases Nat.lt_or_ge t 64 with ht | ht
  · by_cases h : (64 * r + t) % p = 0 <;> simp [ht, exists_lt_mul_eq_iff hr ht, h]
  · simp [decide_eq_false (Nat.not_lt.mpr ht)]

/-! ### The `long`s of the C code -/

/-- The valuations `m` with `p ^ m ≤ bHigh` for `p ≥ 3`, as for an odd prime, and a `long` `bHigh`
are below `40`, since `3 ^ 40 > 2 ^ 63`: the cap `m < LONG_LENGTH - 1` of the loops of
`forbidden_valuations` and of the valuations that a denominator can have (`find_points.c:2217`,
`find_points.c:2636-2637`), which the model drops, never binds, and the bits `1UL << m` that they
set are defined. The values `pm * p` of these loops, computed only for `pm ≤ ⌊b_high / p⌋`, are
`long`s too (`Ratpoints.Setup.fitsLong_mul_of_le_div`). -/
theorem lt_forty_of_pow_le {p m bHigh : ℕ} (hp : 3 ≤ p) (hH : bHigh < 2 ^ 63) (h : p ^ m ≤ bHigh) :
    m < 40 := by
  by_contra hm
  have h1 := Nat.pow_le_pow_left hp m
  have h2 := Nat.pow_le_pow_right three_pos (Nat.le_of_not_lt hm)
  have h3 : 2 ^ 63 < 3 ^ 40 := by decide
  lia

/-- For `p ≥ 3`, as for an odd prime, and a `long` `bHigh`, the mask of the forbidden valuations is
below `2 ^ 40`, so that the `unsigned long` `mask` of `forbidden_valuations` holds it
(`find_points.c:2229`). -/
theorem run_forbiddenValuations_lt (c : List ℤ) (d : ℕ) {p bHigh : ℕ} (cm : Array ℕ) (hp : 3 ≤ p)
    (hH : bHigh < 2 ^ 63) : Id.run (forbiddenValuations c d p bHigh cm) < 2 ^ 40 :=
  Nat.lt_pow_two_of_testBit _ fun m hm ↦ by
    have : ¬p ^ m ≤ bHigh := mt (lt_forty_of_pow_le hp hH) (by lia)
    simp [testBit_run_forbiddenValuations c d (by lia : 1 < p), this]

/-- For `p ≥ 3`, as for an odd prime, and a `long` `bHigh`, the mask of the valuations that a
denominator can have is below `2 ^ 40`, so that the `unsigned long` `all` of `sieving_info` holds it
(`find_points.c:2638`). -/
theorem run_allValuations_lt {p bHigh : ℕ} (hp : 3 ≤ p) (hH : bHigh < 2 ^ 63) :
    Id.run (allValuations p bHigh) < 2 ^ 40 :=
  Nat.lt_pow_two_of_testBit _ fun m hm ↦ by
    have : ¬p ^ m ≤ bHigh := mt (lt_forty_of_pow_le hp hH) (by lia)
    simp [testBit_run_allValuations (by lia : 1 < p), this]

end Sieve

end Ratpoints

end
