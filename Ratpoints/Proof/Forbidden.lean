/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Ratpoints.Model.Denominators
public import Ratpoints.Spec.Basic
public import Std.WP

import Ratpoints.Mathlib.Algebra.Field.ZMod
import Ratpoints.Mathlib.Algebra.Prime.Defs
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
so are the bits of the mask of `Ratpoints.Sieve.forbiddenValuations`. The forbidden divisors
(`Ratpoints.Sieve.forbidden`) are therefore sound: a prime tested with words divides no denominator
`b ≤ bHigh` of a point, since the mask holds every valuation that such a denominator can have
(`Ratpoints.Sieve.allValuations`) or `c_d` is not a square modulo `p`, and its words are those of
`Ratpoints.Sieve.forbiddenRow`, bit `j` of word `r` clear exactly when `p ∣ 64 r + j`; a prime
tested by its valuation excludes no denominator of a point. The masks, which the C code keeps in an
`unsigned long`, stay below `2 ^ 40` for an odd prime and a `long` `b_high`, so that its cap on the
valuations never binds; the products `pm p` of its loops of the valuations and the square `p p` of a
prime of the table that its loop over the further primes compares with `b_high` are `long`s
(`Ratpoints.Setup.fitsLong_mul_of_le_div`, `Ratpoints.Setup.mul_self_lt_of_mem_primeTable`).

## Main definitions

* `Ratpoints.Sieve.IsUnitPart`: what an entry of `Ratpoints.Sieve.unitParts` says of a coefficient.
* `Ratpoints.Sieve.IsForbiddenEntry`, `Ratpoints.Sieve.IsForbiddenVal`: the forbidden divisors that
  `Ratpoints.Sieve.forbidden` may record.
* `Ratpoints.Sieve.ForbiddenVal.excludes`: whether a forbidden divisor tested by its valuation
  excludes a denominator.

## Main statements

* `Ratpoints.even_and_isSquare_of_sq_eq_binaryForm_of_even`: the Newton polygon at a prime.
* `Ratpoints.Sieve.unitParts_spec`, `Ratpoints.Sieve.forbiddenAt_spec`,
  `Ratpoints.Sieve.forbiddenValuations_spec`, `Ratpoints.Sieve.allValuations_spec`,
  `Ratpoints.Sieve.forbidden_spec`: the contracts of the forbidden divisors.
* `Ratpoints.Sieve.run_forbiddenAt_eq_false_of_sq_eq`,
  `Ratpoints.Sieve.testBit_run_forbiddenValuations_eq_false_of_sq_eq`: no denominator of a point has
  a forbidden valuation.
* `Ratpoints.Sieve.prime_of_mem_forbidden_fst`, `Ratpoints.Sieve.words_eq_of_mem_forbidden_fst`:
  the forbidden divisors tested with words are primes with the words of
  `Ratpoints.Sieve.forbiddenRow`.
* `Ratpoints.Sieve.not_dvd_of_mem_forbidden_fst`,
  `Ratpoints.Sieve.excludes_eq_false_of_mem_forbidden_snd`: the forbidden divisors let the
  denominator of every point through.
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
  obtain ⟨b', hb', hpb'⟩ := Int.exists_eq_pow_padicValNat_mul (p := p) (n := b) fun h ↦ by simp_all
  rw [Int.natAbs_natCast] at hb'
  have hterm (i : ℕ) : c.getD (degree c - i) 0 * a ^ (degree c - i) * (b : ℤ) ^ i =
      c.getD (degree c - i) 0 * (p : ℤ) ^ (i * padicValNat p b) *
        (a ^ (degree c - i) * b' ^ i) := by rw [hb']; ring
  rw [binaryForm_eq_sum_of_even hd] at hy
  obtain ⟨hev, t, ht⟩ := Int.even_and_exists_isSquare_add_of_sq_eq_sum
    (v := w + j * padicValNat p b) (u := u * a ^ (degree c - j) * b' ^ j) hy
    (Finset.mem_range.mpr (Nat.lt_succ_of_le hj)) (by rw [hterm, hu, pow_add]; ring)
    (hpp.not_dvd_mul_pow_mul hpu hpa (mt hpp.dvd_of_dvd_pow hpb') _)
    fun i hi hij ↦ hterm i ▸ (hmin i (Nat.le_of_lt_succ (Finset.mem_range.mp hi)) hij).mul_right _
  refine ⟨hev, fun ⟨k, hk⟩ ↦ ?_⟩
  obtain ⟨l, hl⟩ : Even (degree c - j) := (Nat.even_sub hj).mpr (by simp [Nat.even_iff, hd, hk])
  exact ZMod.isSquare_intCast_of_isSquare_mul_sq_add (x := a ^ l * b' ^ k) (t := t)
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
  refine ⟨(Int.toNat_lt' hp).mpr (Int.emod_lt_of_pos _ (mod_cast hp)), x, by simp,
    fun h ↦ hx (Int.emod_eq_zero_of_dvd h), ZMod.natCast_toNat_emod x⟩

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
  have hmr' : ((m : ℕ) : ZMod p) = r := by rw [← hmr, ZMod.natCast_mod]
  split_ifs with hneg
  · refine ⟨by lia, -m, ?_, by rwa [Int.dvd_neg], ?_⟩
    · rw [Int.eq_neg_natAbs_of_nonpos (Int.le_of_lt hneg), hm]
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

theorem UnitPartsInvariant.post {c : List ℤ} {d p : ℕ} {us : Array (Option (ℕ × ℕ))}
    (h : UnitPartsInvariant c d p (ForIn.toList [:d + 1]).length us) :
    us.size = d + 1 ∧ ∀ j ≤ d, IsUnitPart p (c.getD (d - j) 0) us[j]! := by
  simp only [Std.Internal.ForIn.toList_range, List.length_range', Std.Legacy.Range.size,
    Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one] at h
  exact ⟨h.1, fun j hj ↦ h.2 j (by lia)⟩

attribute [local irreducible] UnitPartsInvariant in
/-- The contract of `Ratpoints.Sieve.unitParts`: for `p > 1`, its entries describe the coefficients
`c_d, …, c_0` at `p` (`Ratpoints.Sieve.IsUnitPart`). -/
@[spec]
theorem unitParts_spec (c : List ℤ) (d p : ℕ) :
    ⦃ 1 < p ⦄ unitParts c d p
    ⦃ fun us ↦ us.size = d + 1 ∧ ∀ j ≤ d, IsUnitPart p (c.getD (d - j) 0) us[j]! ⦄ := by
  vcgen [unitParts, valuation_value] invariants
  · fun pref _ us ↦ UnitPartsInvariant c d p pref.length us
  all_goals first
    | exact unitPartsInvariant_zero c d p
    | exact UnitPartsInvariant.post ‹_›
    | exact UnitPartsInvariant.push ‹_› ‹_› ‹_›
    | exact UnitPartsInvariant.push ‹_› ‹_› (isUnitPart_of_eq_run_valuation ‹_› ‹_› ‹_›)
    | exact UnitPartsInvariant.push ‹_› ‹_› (isUnitPart_of_emod_ne_zero (by lia) ‹_›)

/-- `Ratpoints.Sieve.unitParts_spec` as a plain statement. -/
theorem isUnitPart_run_unitParts (c : List ℤ) (d : ℕ) {p : ℕ} (hp : 1 < p) {j : ℕ} (hj : j ≤ d) :
    IsUnitPart p (c.getD (d - j) 0) (Id.run (unitParts c d p))[j]! :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((unitParts_spec c d p).le_wp hp)).2 j hj

theorem le_of_getElem!_run_unitParts_eq_some {c : List ℤ} {d p j : ℕ} (hp : 1 < p)
    {x : ℕ × ℕ} (h : (Id.run (unitParts c d p))[j]! = some x) : j ≤ d := by
  by_contra hlt
  rw [getElem!_neg _ j (by
    rw [(Std.WP.Id.of_run_eq_wp rfl _ ((unitParts_spec c d p).le_wp hp)).1]; lia)] at h
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

theorem ForbiddenAtInvariant.post {us : Array (Option (ℕ × ℕ))} {sq : Array Bool}
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
  simp only [Std.Internal.ForIn.toList_range, List.length_range', Std.Legacy.Range.size]
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
    | exact ForbiddenAtInvariant.post ‹_› ‹_›
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

theorem getElem!_squaresMod_zero {p : ℕ} (hp : p.Prime) : (squaresMod p)[0]! = true := by
  simpa using getElem!_squaresMod_mul_self_mod hp hp.pos

/-- For a point `(a, y, b)` of a curve of even degree with `v_p(b) = m ≥ 1`, a coefficient
`c_{d-j₀}`, with the entry `(w, r)` at `p`, whose term has a valuation `w + j₀ m` less than those of
the other terms present has an even `w + j₀ m`, and for even `j₀` a unit part whose residue `r` is
marked as a square modulo `p` (`Ratpoints.even_and_isSquare_of_sq_eq_binaryForm_of_even`). -/
theorem even_and_getElem!_squaresMod_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 0) {p : ℕ}
    (hp : p.Prime) {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b)
    (hm : padicValNat p b ≠ 0) {j₀ w r : ℕ}
    (hus : (Id.run (unitParts c (degree c) p))[j₀]! = some (w, r))
    (hmin : ∀ j, (Id.run (unitParts c (degree c) p))[j]!.isSome → j ≠ j₀ →
      w + j₀ * padicValNat p b <
        ((Id.run (unitParts c (degree c) p))[j]!.getD (0, 0)).1 + j * padicValNat p b) :
    Even (w + j₀ * padicValNat p b) ∧ (Even j₀ → (squaresMod p)[r]! = true) := by
  have : Fact p.Prime := ⟨hp⟩
  have hj₀ := le_of_getElem!_run_unitParts_eq_some hp.one_lt hus
  obtain ⟨hr, u, hu, hpu, hru⟩ := hus ▸ isUnitPart_run_unitParts c (degree c) hp.one_lt hj₀
  obtain ⟨hev, hsq⟩ := even_and_isSquare_of_sq_eq_binaryForm_of_even hd hab hy hm hj₀ hu hpu
    fun i hi hne ↦
      pow_dvd_mul_pow_of_isUnitPart (isUnitPart_run_unitParts c (degree c) hp.one_lt hi)
        fun w' r' h' ↦ by simpa [h'] using hmin i (by simp [h']) hne
  exact ⟨hev, fun hj ↦ getElem!_squaresMod_of_isSquare hp hr (hru ▸ hsq hj)⟩

/-- **The forbidden valuations are sound.** No denominator `b` of a point of a curve of even degree
has a valuation `v_p(b) ≥ 1` at a prime `p` that `Ratpoints.Sieve.forbiddenAt` excludes, with the
unit parts of the coefficients at `p` (`Ratpoints.Sieve.unitParts`) and the squares modulo `p`: the
term of the least valuation would make `F(a, b)` a non-square
(`Ratpoints.Sieve.even_and_getElem!_squaresMod_of_sq_eq`), and for `c_d = 0` the term of `j = 0`,
of the valuation `0` and the unit part `0`, a square, is the least one. -/
theorem run_forbiddenAt_eq_false_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 0) {p : ℕ}
    (hp : p.Prime) {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b)
    (hm : padicValNat p b ≠ 0) :
    Id.run (forbiddenAt (Id.run (unitParts c (degree c) p)) (squaresMod p) (padicValNat p b)) =
      false := by
  refine Bool.eq_false_iff.mpr fun h ↦ ?_
  obtain ⟨j₀, hc, hmin, hcrit⟩ := exists_of_run_forbiddenAt_eq_true h
  rcases hus : (Id.run (unitParts c (degree c) p))[j₀]! with _ | ⟨w, r⟩
  · obtain rfl : j₀ = 0 := hc.resolve_right (by simp [hus])
    simp [hus, getElem!_squaresMod_zero hp] at hcrit
  simp only [hus, Option.getD_some] at hmin hcrit
  obtain ⟨hev, hsq⟩ := even_and_getElem!_squaresMod_of_sq_eq hd hp hab hy hm hus
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
theorem ValuationsInvariant.break {f : ℕ → Bool} {p bHigh mask m pm mask' : ℕ} (hp : 0 < p)
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
theorem ValuationsInvariant.next {f : ℕ → Bool} {p bHigh mask m pm mask' : ℕ}
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
theorem ValuationsInvariant.next_measure {f : ℕ → Bool} {p bHigh mask m pm mask' : ℕ}
    (hp : 1 < p) (h : ValuationsInvariant f p bHigh false (mask, m, pm)) (hpm : pm ≤ bHigh)
    (hb : ¬bHigh / p < pm)
    (h' : ∀ t, mask'.testBit t = (mask.testBit t || (decide (t = m) && f m))) :
    bHigh + 1 - pm * p < bHigh + 1 - pm ∧
      ValuationsInvariant f p bHigh false (mask', m + 1, pm * p) :=
  ⟨h.sub_mul_lt hp hb, h.next hpm hb h'⟩

-- The mask with the bit of `m` set when the test `x` of `m` holds.
private theorem testBit_or_one_shiftLeft {x y : Bool} (hx : x = y) (hy : x = true)
    (mask m t : ℕ) : (mask ||| 1 <<< m).testBit t = (mask.testBit t || (decide (t = m) && y)) := by
  rw [Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, ← hx, hy]
  grind

private theorem testBit_eq_or {x y : Bool} (hx : x = y) (hy : ¬x = true) (mask m t : ℕ) :
    mask.testBit t = (mask.testBit t || (decide (t = m) && y)) := by
  simp [← hx, Bool.eq_false_iff.mpr hy]

-- The unit parts and the test of a valuation, as values for the contract of the mask.
private theorem unitParts_value (c : List ℤ) (d p : ℕ) :
    ⦃ True ⦄ unitParts c d p ⦃ fun r ↦ r = Id.run (unitParts c d p) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem forbiddenAt_value (us : Array (Option (ℕ × ℕ))) (sq : Array Bool) (m : ℕ) :
    ⦃ True ⦄ forbiddenAt us sq m ⦃ fun r ↦ r = Id.run (forbiddenAt us sq m) ⦄ :=
  ⟨fun _ ↦ rfl⟩

attribute [local irreducible] ValuationsInvariant in
/-- The contract of `Ratpoints.Sieve.forbiddenValuations`: bit `m` of the mask is set exactly for
the `m ≥ 1` with `p ^ m ≤ bHigh` that `Ratpoints.Sieve.forbiddenAt` excludes. The loop ends for
`p > 1`, since `pm = p ^ m` grows and stays at most `bHigh` while it goes on. -/
@[spec]
theorem forbiddenValuations_spec (c : List ℤ) (d p bHigh : ℕ) :
    ⦃ 1 < p ⦄ forbiddenValuations c d p bHigh
    ⦃ fun mask ↦ ∀ m, mask.testBit m = (decide (1 ≤ m) && decide (p ^ m ≤ bHigh) &&
        Id.run (forbiddenAt (Id.run (unitParts c d p)) (squaresMod p) m)) ⦄ := by
  vcgen [forbiddenValuations, unitParts_value, forbiddenAt_value] invariants
  · ValuationsInvariant (fun m ↦ Id.run (forbiddenAt (Id.run (unitParts c d p)) (squaresMod p) m))
      p bHigh
  · .ofMeasure fun s : ℕ × ℕ × ℕ ↦ bHigh + 1 - s.2.2
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals try obtain ⟨rfl, _⟩ := ‹_ = _ ∧ ValuationsInvariant _ _ _ false _›
  all_goals subst ‹_ = Id.run (unitParts _ _ _)›
  all_goals first
    | exact valuationsInvariant_zero_one _ _ _
    | exact ‹ValuationsInvariant _ _ _ true _›.testBit _
    | exact ValuationsInvariant.break (by lia) ‹_› ‹_› ‹_› (testBit_or_one_shiftLeft ‹_› ‹_› _ _)
    | exact ValuationsInvariant.break (by lia) ‹_› ‹_› ‹_› (testBit_eq_or ‹_› ‹_› _ _)
    | exact ValuationsInvariant.next_measure ‹_› ‹_› ‹_› ‹_›
        (testBit_or_one_shiftLeft ‹_› ‹_› _ _)
    | exact ValuationsInvariant.next_measure ‹_› ‹_› ‹_› ‹_› (testBit_eq_or ‹_› ‹_› _ _)
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
    | exact ValuationsInvariant.break (by lia) ‹_› ‹_› ‹_› (testBit_or_one_shiftLeft rfl rfl _ _)
    | exact ValuationsInvariant.next_measure ‹_› ‹_› ‹_› ‹_›
        (testBit_or_one_shiftLeft rfl rfl _ _)
    | exact ValuationsInvariant.exit (by lia) ‹_› ‹_›

/-- `Ratpoints.Sieve.forbiddenValuations_spec` as a plain statement. -/
theorem testBit_run_forbiddenValuations (c : List ℤ) (d : ℕ) {p : ℕ} (hp : 1 < p) (bHigh m : ℕ) :
    (Id.run (forbiddenValuations c d p bHigh)).testBit m = (decide (1 ≤ m) &&
      decide (p ^ m ≤ bHigh) && Id.run (forbiddenAt (Id.run (unitParts c d p)) (squaresMod p) m)) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((forbiddenValuations_spec c d p bHigh).le_wp hp) m

/-- `Ratpoints.Sieve.allValuations_spec` as a plain statement. -/
theorem testBit_run_allValuations {p : ℕ} (hp : 1 < p) (bHigh m : ℕ) :
    (Id.run (allValuations p bHigh)).testBit m = (decide (1 ≤ m) && decide (p ^ m ≤ bHigh)) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((allValuations_spec p bHigh).le_wp hp) m

/-- The mask of the forbidden valuations at a prime `p` has no bit `v_p(b)` for the denominator `b`
of a point of a curve of even degree (`Ratpoints.Sieve.run_forbiddenAt_eq_false_of_sq_eq`); its bit
`0` is never set. -/
theorem testBit_run_forbiddenValuations_eq_false_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 0)
    {p : ℕ} (hp : p.Prime) (bHigh : ℕ) {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) :
    (Id.run (forbiddenValuations c (degree c) p bHigh)).testBit (padicValNat p b) = false := by
  rw [testBit_run_forbiddenValuations c _ hp.one_lt]
  rcases eq_or_ne (padicValNat p b) 0 with h0 | h0
  · simp [h0]
  · simp [run_forbiddenAt_eq_false_of_sq_eq hd hp hab hy h0]

/-! ### The forbidden divisors -/

/-- For a point `(a, y, b)` of a curve of even degree and a prime `p ∣ b`, the residue of `c_d`
modulo `p` is marked as a square (`Ratpoints.Sieve.isSquare_getD_degree_of_sq_eq_binaryForm`). -/
theorem getElem!_squaresMod_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 0) {p : ℕ} (hp : p.Prime)
    {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) (hpb : p ∣ b) :
    (squaresMod p)[(c.getD (degree c) 0 % (p : ℤ)).toNat]! = true := by
  have : Fact p.Prime := ⟨hp⟩
  refine getElem!_squaresMod_of_isSquare hp
    ((Int.toNat_lt' hp.pos).mpr (Int.emod_lt_of_pos _ (mod_cast hp.pos))) ?_
  rw [ZMod.natCast_toNat_emod]
  exact isSquare_getD_degree_of_sq_eq_binaryForm hab (Nat.mod_eq_zero_of_dvd hpb) hd hy

/-- A forbidden divisor tested with words that the examined prime `p` gives is `p` with its words,
for a mask of the forbidden valuations at `p ∣ c_d` that holds every valuation a denominator can
have, or for `c_d` not a square modulo `p`. -/
theorem eq_of_run_forbiddenOfPrime_eq_inl {c : List ℤ} {d p bHigh : ℕ} {e : ForbiddenEntry}
    (h : Id.run (forbiddenOfPrime c d p bHigh) = some (.inl e)) :
    e = ⟨p, forbiddenRow p⟩ ∧ ((c.getD d 0 % (p : ℤ) = 0 ∧
      Id.run (forbiddenValuations c d p bHigh) &&& Id.run (allValuations p bHigh) =
        Id.run (allValuations p bHigh)) ∨
      (squaresMod p)[(c.getD d 0 % (p : ℤ)).toNat]! = false) := by
  simp only [forbiddenOfPrime, apply_ite Id.run, Id.run_bind] at h
  split_ifs at h <;> simp_all

/-- A forbidden divisor tested by its valuation that the examined prime `p` gives is `p` with the
mask of the forbidden valuations. -/
theorem eq_of_run_forbiddenOfPrime_eq_inr {c : List ℤ} {d p bHigh : ℕ} {e : ForbiddenVal}
    (h : Id.run (forbiddenOfPrime c d p bHigh) = some (.inr e)) :
    e = ⟨p, Id.run (forbiddenValuations c d p bHigh)⟩ := by
  simp only [forbiddenOfPrime, apply_ite Id.run, Id.run_bind] at h
  split_ifs at h <;> simp_all

/-- **A forbidden divisor tested with words that an examined prime gives is sound**: for a point
`(a, y, b)` of a curve of even degree with `b ≤ bHigh`, the prime would divide `b` with a valuation
that the mask holds, if it holds every valuation a denominator can have, or `c_d` would be a square
modulo `p`. -/
theorem not_dvd_of_run_forbiddenOfPrime_eq_inl {c : List ℤ} (hd : degree c % 2 = 0) {p bHigh : ℕ}
    (hp : p.Prime) {e : ForbiddenEntry}
    (he : Id.run (forbiddenOfPrime c (degree c) p bHigh) = some (.inl e)) {a y : ℤ} {b : ℕ}
    (hb : b ≠ 0) (hbH : b ≤ bHigh) (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    ¬p ∣ b := by
  intro hpb
  rcases (eq_of_run_forbiddenOfPrime_eq_inl he).2 with ⟨-, hall⟩ | hsq
  · have : Fact p.Prime := ⟨hp⟩
    have hv : padicValNat p b ≠ 0 := Nat.pos_iff_ne_zero.mp (one_le_padicValNat_of_dvd hb hpb)
    have hle : p ^ padicValNat p b ≤ bHigh := (Nat.le_of_dvd (by lia) pow_padicValNat_dvd).trans hbH
    have := congr(Nat.testBit $hall (padicValNat p b))
    simp only [Nat.testBit_and, testBit_run_allValuations hp.one_lt,
      testBit_run_forbiddenValuations_eq_false_of_sq_eq hd hp bHigh hab hy] at this
    simp [hv, hle] at this
  · exact Bool.false_ne_true (hsq.symm.trans (getElem!_squaresMod_of_sq_eq hd hp hab hy hpb))

/-- A forbidden divisor tested with words that `Ratpoints.Sieve.forbidden` may record for the
examined primes `moduli`: the one of an examined prime (`Ratpoints.Sieve.forbiddenOfPrime`), or a
prime of `Ratpoints.primeTable` with its words (`Ratpoints.Sieve.forbiddenRow`) at which `c_d` is
not a square. -/
def IsForbiddenEntry (c : List ℤ) (d : ℕ) (moduli : List ℕ) (bHigh : ℕ) (e : ForbiddenEntry) :
    Prop :=
  (∃ p ∈ moduli, Id.run (forbiddenOfPrime c d p bHigh) = some (.inl e)) ∨
    (e.p ∈ primeTable ∧ e.words = forbiddenRow e.p ∧
      (squaresMod e.p)[(c.getD d 0 % (e.p : ℤ)).toNat]! = false)

/-- A forbidden divisor tested by its valuation that `Ratpoints.Sieve.forbidden` may record for the
examined primes `moduli`: the one of an examined prime (`Ratpoints.Sieve.forbiddenOfPrime`). -/
def IsForbiddenVal (c : List ℤ) (d : ℕ) (moduli : List ℕ) (bHigh : ℕ) (e : ForbiddenVal) : Prop :=
  ∃ p ∈ moduli, Id.run (forbiddenOfPrime c d p bHigh) = some (.inr e)

/-- The invariant of the loop of `Ratpoints.Sieve.forbidden` over the examined primes, on the
forbidden divisors found so far. -/
def ForbiddenInvariant (c : List ℤ) (d : ℕ) (moduli : List ℕ) (bHigh : ℕ)
    (s : Array ForbiddenEntry × Array ForbiddenVal) : Prop :=
  (∀ e ∈ s.1, IsForbiddenEntry c d moduli bHigh e) ∧ ∀ e ∈ s.2, IsForbiddenVal c d moduli bHigh e

theorem forbiddenInvariant_empty (c : List ℤ) (d : ℕ) (moduli : List ℕ) (bHigh : ℕ) :
    ForbiddenInvariant c d moduli bHigh (#[], #[]) :=
  ⟨nofun, nofun⟩

theorem ForbiddenInvariant.fst {c : List ℤ} {d : ℕ} {moduli : List ℕ} {bHigh : ℕ}
    {ba : Array ForbiddenEntry} {val : Array ForbiddenVal}
    (h : ForbiddenInvariant c d moduli bHigh (ba, val)) :
    ∀ e ∈ ba, IsForbiddenEntry c d moduli bHigh e :=
  h.1

theorem ForbiddenInvariant.push_inl {c : List ℤ} {d : ℕ} {moduli pref suff : List ℕ} {cur : ℕ}
    {bHigh : ℕ} {ba : Array ForbiddenEntry} {val : Array ForbiddenVal}
    {o : Option (ForbiddenEntry ⊕ ForbiddenVal)} {e : ForbiddenEntry}
    (h : ForbiddenInvariant c d moduli bHigh (ba, val)) (hl : moduli = pref ++ cur :: suff)
    (ho : o = Id.run (forbiddenOfPrime c d cur bHigh)) (he : o = some (.inl e)) :
    ForbiddenInvariant c d moduli bHigh (ba.push e, val) :=
  ⟨Array.forall_mem_push.mpr ⟨.inl ⟨cur, by simp [hl], ho ▸ he⟩, h.1⟩, h.2⟩

theorem ForbiddenInvariant.push_inr {c : List ℤ} {d : ℕ} {moduli pref suff : List ℕ} {cur : ℕ}
    {bHigh : ℕ} {ba : Array ForbiddenEntry} {val : Array ForbiddenVal}
    {o : Option (ForbiddenEntry ⊕ ForbiddenVal)} {e : ForbiddenVal}
    (h : ForbiddenInvariant c d moduli bHigh (ba, val)) (hl : moduli = pref ++ cur :: suff)
    (ho : o = Id.run (forbiddenOfPrime c d cur bHigh)) (he : o = some (.inr e)) :
    ForbiddenInvariant c d moduli bHigh (ba, val.push e) :=
  ⟨h.1, Array.forall_mem_push.mpr ⟨⟨cur, by simp [hl], ho ▸ he⟩, h.2⟩⟩

/-- A prime of the table at which `c_d` is not a square, recorded with its words by the loop of
`Ratpoints.Sieve.forbidden` over the further primes. -/
theorem forall_isForbiddenEntry_push {c : List ℤ} {d : ℕ} {moduli pref suff : List ℕ} {cur : ℕ}
    {bHigh : ℕ} {ba : Array ForbiddenEntry} (h : ∀ e ∈ ba, IsForbiddenEntry c d moduli bHigh e)
    (hl : ForIn.toList [moduli.length:primeTable.size] = pref ++ cur :: suff)
    (hs : (!(squaresMod primeTable[cur]!)[(c.getD d 0 % (primeTable[cur]! : ℤ)).toNat]!) = true) :
    ∀ e ∈ ba.push ⟨primeTable[cur]!, forbiddenRow primeTable[cur]!⟩,
      IsForbiddenEntry c d moduli bHigh e := by
  have hcur : cur < primeTable.size := by
    have := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
    have := Std.Legacy.Range.length_add_length_add_one_of_toList_eq_append_cons hl
    lia
  -- `rfl` for the words would unfold `Ratpoints.Sieve.forbiddenRow` until the recursion limit
  refine Array.forall_mem_push.mpr ⟨.inr ⟨?_, by dsimp only, Bool.not_eq_true' _ ▸ hs⟩, h⟩
  rw [getElem!_pos primeTable cur hcur]
  exact Array.getElem_mem hcur

theorem ForbiddenInvariant.post {c : List ℤ} {d : ℕ} {moduli : List ℕ} {bHigh : ℕ}
    {ba ba' : Array ForbiddenEntry} {val : Array ForbiddenVal}
    (h : ForbiddenInvariant c d moduli bHigh (ba, val))
    (h' : ∀ e ∈ ba', IsForbiddenEntry c d moduli bHigh e) :
    (∀ e ∈ ba'.toList, IsForbiddenEntry c d moduli bHigh e) ∧
      ∀ e ∈ val.toList, IsForbiddenVal c d moduli bHigh e :=
  ⟨fun e he ↦ h' e (Array.mem_toList_iff.mp he), fun e he ↦ h.2 e (Array.mem_toList_iff.mp he)⟩

-- The entry that an examined prime gives, as a value for the contract of the forbidden divisors.
private theorem forbiddenOfPrime_value (c : List ℤ) (d p bHigh : ℕ) :
    ⦃ True ⦄ forbiddenOfPrime c d p bHigh ⦃ fun r ↦ r = Id.run (forbiddenOfPrime c d p bHigh) ⦄ :=
  ⟨fun _ ↦ rfl⟩

attribute [local irreducible] IsForbiddenEntry IsForbiddenVal ForbiddenInvariant in
/-- The contract of `Ratpoints.Sieve.forbidden`: each forbidden divisor tested with words is that of
an examined prime or a prime of the table with its words at which `c_d` is not a square
(`Ratpoints.Sieve.IsForbiddenEntry`), and each one tested by its valuation is that of an examined
prime (`Ratpoints.Sieve.IsForbiddenVal`). -/
@[spec]
theorem forbidden_spec (c : List ℤ) (d : ℕ) (moduli : List ℕ) (maxForbidden bHigh : ℕ) :
    ⦃ True ⦄ forbidden c d moduli maxForbidden bHigh
    ⦃ fun r ↦ (∀ e ∈ r.1, IsForbiddenEntry c d moduli bHigh e) ∧
        ∀ e ∈ r.2, IsForbiddenVal c d moduli bHigh e ⦄ := by
  vcgen [forbidden, forbiddenOfPrime_value] invariants
  · fun _ _ s ↦ ForbiddenInvariant c d moduli bHigh s
  · fun _ _ ba ↦ ∀ e ∈ ba, IsForbiddenEntry c d moduli bHigh e
  all_goals try dsimp only at *
  all_goals first
    | exact forbiddenInvariant_empty c d moduli bHigh
    | exact ForbiddenInvariant.fst ‹_› _ ‹_›
    | exact ForbiddenInvariant.post ‹_› ‹∀ e ∈ _, IsForbiddenEntry _ _ _ _ e›
    | exact ForbiddenInvariant.post ‹_› (ForbiddenInvariant.fst ‹_›)
    | exact ForbiddenInvariant.push_inl ‹_› ‹_› ‹_› ‹_›
    | exact ForbiddenInvariant.push_inr ‹_› ‹_› ‹_› ‹_›
    | exact forall_isForbiddenEntry_push ‹_› ‹_› ‹_›
    | assumption

/-- `Ratpoints.Sieve.forbidden_spec` as a plain statement for the forbidden divisors tested with
words. -/
theorem isForbiddenEntry_of_mem_forbidden_fst {c : List ℤ} {d : ℕ} {moduli : List ℕ}
    {maxForbidden bHigh : ℕ} {e : ForbiddenEntry}
    (he : e ∈ (Id.run (forbidden c d moduli maxForbidden bHigh)).1) :
    IsForbiddenEntry c d moduli bHigh e :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((forbidden_spec c d moduli maxForbidden bHigh).le_wp trivial)).1
    e he

/-- `Ratpoints.Sieve.forbidden_spec` as a plain statement for the forbidden divisors tested by
their valuations. -/
theorem isForbiddenVal_of_mem_forbidden_snd {c : List ℤ} {d : ℕ} {moduli : List ℕ}
    {maxForbidden bHigh : ℕ} {e : ForbiddenVal}
    (he : e ∈ (Id.run (forbidden c d moduli maxForbidden bHigh)).2) :
    IsForbiddenVal c d moduli bHigh e :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((forbidden_spec c d moduli maxForbidden bHigh).le_wp trivial)).2
    e he

theorem prime_of_mem_forbidden_fst {c : List ℤ} {d : ℕ} {moduli : List ℕ}
    (hm : ∀ p ∈ moduli, p.Prime) {maxForbidden bHigh : ℕ} {e : ForbiddenEntry}
    (he : e ∈ (Id.run (forbidden c d moduli maxForbidden bHigh)).1) : e.p.Prime := by
  rcases isForbiddenEntry_of_mem_forbidden_fst he with ⟨p, hp, h⟩ | ⟨h, -⟩
  · obtain ⟨rfl, -⟩ := eq_of_run_forbiddenOfPrime_eq_inl h
    exact hm p hp
  · exact prime_of_mem_primeTable h

theorem words_eq_of_mem_forbidden_fst {c : List ℤ} {d : ℕ} {moduli : List ℕ}
    {maxForbidden bHigh : ℕ} {e : ForbiddenEntry}
    (he : e ∈ (Id.run (forbidden c d moduli maxForbidden bHigh)).1) :
    e.words = forbiddenRow e.p := by
  rcases isForbiddenEntry_of_mem_forbidden_fst he with ⟨p, -, h⟩ | ⟨-, h, -⟩
  · obtain ⟨rfl, -⟩ := eq_of_run_forbiddenOfPrime_eq_inl h
    dsimp only
  · exact h

/-- A forbidden divisor tested with words divides no denominator `b ≤ bHigh` of a point of a curve
of even degree: either every valuation that such a denominator can have at `p` is excluded by the
terms of `F(a, b)` (`Ratpoints.Sieve.forbiddenValuations`), or `c_d` is not a square modulo `p`
while `F(a, b) ≡ c_d a ^ d (mod p)` for `p ∣ b`. -/
theorem not_dvd_of_mem_forbidden_fst {c : List ℤ} {moduli : List ℕ} (hm : ∀ p ∈ moduli, p.Prime)
    {maxForbidden bHigh : ℕ} {e : ForbiddenEntry}
    (he : e ∈ (Id.run (forbidden c (degree c) moduli maxForbidden bHigh)).1)
    (hd : degree c % 2 = 0) {a y : ℤ} {b : ℕ} (hb : b ≠ 0) (hbH : b ≤ bHigh)
    (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) : ¬e.p ∣ b := by
  rcases isForbiddenEntry_of_mem_forbidden_fst he with ⟨p, hp, h⟩ | ⟨h, -, hsq⟩
  · obtain ⟨rfl, -⟩ := eq_of_run_forbiddenOfPrime_eq_inl h
    exact not_dvd_of_run_forbiddenOfPrime_eq_inl hd (hm p hp) h hb hbH hab hy
  · exact fun hpb ↦ Bool.false_ne_true (hsq.symm.trans
      (getElem!_squaresMod_of_sq_eq hd (prime_of_mem_primeTable h) hab hy hpb))

/-- Whether the forbidden divisor `e` tested by its valuation excludes the denominator `b`: bit
`v_p(b)` of its mask, for the valuation `v_p(b)` of `Ratpoints.Setup.valuation`, the test that the
tests of the word shape make with `e` (`Ratpoints.Sieve.wordsTest`). -/
def ForbiddenVal.excludes (e : ForbiddenVal) (b : ℕ) : Bool :=
  e.mask.testBit (Id.run (Setup.valuation b e.p)).1

theorem ForbiddenVal.excludes_eq_false_iff {e : ForbiddenVal} {b : ℕ} :
    e.excludes b = false ↔ ¬e.mask.testBit (Id.run (Setup.valuation b e.p)).1 = true :=
  Bool.eq_false_iff

/-- A forbidden divisor tested by its valuation excludes no denominator of a point of a curve of
even degree: the valuations of its mask are excluded by the terms of `F(a, b)`
(`Ratpoints.Sieve.forbiddenValuations`). -/
theorem excludes_eq_false_of_mem_forbidden_snd {c : List ℤ} {moduli : List ℕ}
    (hm : ∀ p ∈ moduli, p.Prime) {maxForbidden bHigh : ℕ} {e : ForbiddenVal}
    (he : e ∈ (Id.run (forbidden c (degree c) moduli maxForbidden bHigh)).2)
    (hd : degree c % 2 = 0) {a y : ℤ} {b : ℕ} (hb : b ≠ 0) (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) : e.excludes b = false := by
  obtain ⟨p, hp, h⟩ := isForbiddenVal_of_mem_forbidden_snd he
  obtain rfl := eq_of_run_forbiddenOfPrime_eq_inr h
  rw [ForbiddenVal.excludes_eq_false_iff, Setup.fst_run_valuation (Int.natCast_ne_zero.mpr hb)
    (hm p hp), Int.natAbs_natCast, Bool.not_eq_true]
  exact testBit_run_forbiddenValuations_eq_false_of_sq_eq hd (hm p hp) bHigh hab hy

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

/-- The valuations `m` with `p ^ m ≤ bHigh` of an odd prime `p` and a `long` `bHigh` are below
`40`, since `3 ^ 40 > 2 ^ 63`: the cap `m < LONG_LENGTH - 1` of the loops of `forbidden_valuations`
and of the valuations that a denominator can have (`find_points.c:2217`,
`find_points.c:2636-2637`), which the model drops, never binds, and the bits `1UL << m` that they
set are defined. The values `pm * p` of these loops, computed only for `pm ≤ ⌊b_high / p⌋`, are
`long`s too (`Ratpoints.Setup.fitsLong_mul_of_le_div`). -/
theorem lt_forty_of_pow_le {p m bHigh : ℕ} (hp : 3 ≤ p) (hH : bHigh < 2 ^ 63) (h : p ^ m ≤ bHigh) :
    m < 40 := by
  by_contra hm
  have h1 := Nat.pow_le_pow_left hp m
  have h2 := Nat.pow_le_pow_right (by decide : 0 < 3) (Nat.le_of_not_lt hm)
  have h3 : 2 ^ 63 < 3 ^ 40 := by decide
  lia

/-- For an odd prime `p` and a `long` `bHigh`, the mask of the forbidden valuations is below
`2 ^ 40`, so that the `unsigned long` `mask` of `forbidden_valuations` holds it
(`find_points.c:2229`). -/
theorem run_forbiddenValuations_lt (c : List ℤ) (d : ℕ) {p bHigh : ℕ} (hp : 3 ≤ p)
    (hH : bHigh < 2 ^ 63) : Id.run (forbiddenValuations c d p bHigh) < 2 ^ 40 :=
  Nat.lt_pow_two_of_testBit _ fun m hm ↦ by
    have : ¬p ^ m ≤ bHigh := mt (lt_forty_of_pow_le hp hH) (by lia)
    simp [testBit_run_forbiddenValuations c d (by lia : 1 < p), this]

/-- For an odd prime `p` and a `long` `bHigh`, the mask of the valuations that a denominator can
have is below `2 ^ 40`, so that the `unsigned long` `all` of `sieving_info` holds it
(`find_points.c:2638`). -/
theorem run_allValuations_lt {p bHigh : ℕ} (hp : 3 ≤ p) (hH : bHigh < 2 ^ 63) :
    Id.run (allValuations p bHigh) < 2 ^ 40 :=
  Nat.lt_pow_two_of_testBit _ fun m hm ↦ by
    have : ¬p ^ m ≤ bHigh := mt (lt_forty_of_pow_le hp hH) (by lia)
    simp [testBit_run_allValuations (by lia : 1 < p), this]

end Sieve

end Ratpoints

end
