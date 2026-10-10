/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Ratpoints.Model.Sieve
public import Ratpoints.Spec.Basic

import Mathlib.Tactic.Field
import Mathlib.Tactic.Ring
import Ratpoints.Mathlib.Data.ZMod.Basic
import Ratpoints.Proof.BruteForce

/-!
# The tables of a prime and the soundness of the rows

The tables of the sieve compute what they claim: the squares, the inverses and Horner's rule
modulo `p`. With them, the row of a denominator `b` in the table of a prime `p` lets the numerator
`a` of every point `(a, y, b)` through (`Ratpoints.Sieve.admits_examinePrime_of_sq_eq`): for
`p ∤ b`, since `F(a, b) ≡ b ^ D f(a / b) (mod p)` with `D` even, so that `f(a / b)` is a square
modulo `p`; for `p ∣ b`, since `gcd(a, b) = 1`, so that `p ∤ a`. The model computes modulo `p`
in `ℕ`; the proofs go through `ZMod p`.

## Main statements

* `Ratpoints.isSquare_sum_mul_div_pow_of_sq_eq`: a square value of the form gives a square value
  of `f`.
* `Ratpoints.Sieve.getElem!_squaresMod_mul_self_mod`,
  `Ratpoints.Sieve.getElem!_inversesMod_mul_mod`, `Ratpoints.Sieve.natCast_evalMod`: the tables
  compute their definitions.
* `Ratpoints.Sieve.getElem!_isFSquare_examinePrime_of_isSquare`: the table of a prime marks every
  residue at which `f` takes a square value.
* `Ratpoints.Sieve.admits_examinePrime_of_sq_eq`: the rows let every point through.
-/

@[expose] public section

namespace Ratpoints

/-- The binary form `∑ fᵢ aⁱ b^(D - i)` of degree `D ≥ d` is the value of `f = ∑ fᵢ Xⁱ` at `a / b`
times `b ^ D`, as `Polynomial.eval_homogenize` says for polynomials. -/
theorem sum_mul_pow_mul_pow_sub_eq_sum_mul_pow {K : Type*} [Semifield K] {d D : ℕ} (hd : d ≤ D)
    (f : ℕ → K) (a : K) {b : K} (hb : b ≠ 0) :
    ∑ i ∈ Finset.range (d + 1), f i * a ^ i * b ^ (D - i) =
      (∑ i ∈ Finset.range (d + 1), f i * (a / b) ^ i) * b ^ D := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [div_pow, ← pow_sub_mul_pow b ((Finset.mem_range_succ_iff.mp hi).trans hd)]
  field

/-- If `y ^ 2` is the value at `(a, b)` of the binary form of even degree `D ≥ d` made from
`f = ∑ fᵢ Xⁱ`, then `f(a / b)` is the square of `y / b ^ (D / 2)`. -/
theorem isSquare_sum_mul_div_pow_of_sq_eq {K : Type*} [Semifield K] {d D : ℕ} (hd : d ≤ D)
    (hD : Even D) {f : ℕ → K} {a b y : K} (hb : b ≠ 0)
    (h : y ^ 2 = ∑ i ∈ Finset.range (d + 1), f i * a ^ i * b ^ (D - i)) :
    IsSquare (∑ i ∈ Finset.range (d + 1), f i * (a / b) ^ i) := by
  rw [sum_mul_pow_mul_pow_sub_eq_sum_mul_pow hd f a hb] at h
  exact eq_div_of_mul_eq (pow_ne_zero D hb) h.symm ▸ (IsSquare.sq y).div (hD.isSquare_pow b)

namespace Sieve

/-! ### The squares, the inverses and Horner's rule modulo `p` -/

-- The entries that a fold of `setIfInBounds · true` marks.
private theorem getElem!_foldl_setIfInBounds {α : Type*} (l : List α) (f : α → ℕ) (w : Array Bool)
    {t : ℕ} (ht : t < w.size) :
    (l.foldl (fun w i ↦ w.setIfInBounds (f i) true) w)[t]! = (w[t]! || l.any (f · == t)) := by
  induction l generalizing w with
  | nil => simp
  | cons j l ih =>
    rw [List.foldl_cons, ih _ (by simpa using ht), List.any_cons, getElem!_pos w t ht,
      getElem!_pos (w.setIfInBounds (f j) true) t (by simpa using ht),
      Array.getElem_setIfInBounds ht]
    grind

/-- Modulo a prime `p`, the square of a residue `s ≠ 0` below `p` is the square of an odd residue,
of `s` or of `p - s`: the squares that the generator of the tables of ratpoints marks. -/
theorem exists_odd_mul_self_mod_eq {p s : ℕ} (hp : p.Prime) (hs : s < p) (hs0 : s ≠ 0) :
    ∃ i < p, Odd i ∧ i * i % p = s * s % p := by
  rcases Nat.even_or_odd' s with ⟨k, rfl | rfl⟩
  · have hodd := hp.eq_two_or_odd.resolve_left (by lia)
    refine ⟨p - 2 * k, by lia, Nat.odd_iff.mpr (by lia), ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff', Nat.cast_mul, Nat.cast_mul, Nat.cast_sub hs.le,
      ZMod.natCast_self, zero_sub, neg_mul_neg]
  · exact ⟨2 * k + 1, hs, odd_two_mul_add_one k, rfl⟩

theorem getElem!_squaresMod_mul_self_mod {p s : ℕ} (hp : p.Prime) (hs : s < p) :
    (squaresMod p)[s * s % p]! = true := by
  have ht : s * s % p < ((Array.replicate p false).setIfInBounds 0 true).size := by
    simpa using Nat.mod_lt _ hp.pos
  simp only [squaresMod, Array.set!_eq_setIfInBounds, getElem!_foldl_setIfInBounds _ _ _ ht,
    Bool.or_eq_true, List.any_eq_true, beq_iff_eq, List.mem_range']
  obtain rfl | hs0 := eq_or_ne s 0
  · left
    rw [getElem!_pos ((Array.replicate p false).setIfInBounds 0 true) _ ht]
    simp
  · obtain ⟨_, hi, ⟨m, rfl⟩, heq⟩ := exists_odd_mul_self_mod_eq hp hs hs0
    exact .inr ⟨_, ⟨m, by lia, by lia⟩, heq⟩

/-- Modulo a prime `p`, a residue `0 < r < p` has an inverse among `1, …, p - 1`, so that the trial
of `Ratpoints.Sieve.inversesMod` finds one. -/
theorem exists_mem_range'_mul_mod_eq_one {p r : ℕ} (hp : p.Prime) (hr : r < p) (hr0 : r ≠ 0) :
    ∃ i ∈ List.range' 1 (p - 1), i * r % p = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hr' : (r : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h ↦ hr0 (Nat.eq_zero_of_dvd_of_lt h hr)
  have h0 := (ZMod.val_ne_zero _).mpr (inv_ne_zero hr')
  refine ⟨((r : ZMod p)⁻¹).val, List.mem_range'_1.mpr ⟨by lia, ?_⟩, ?_⟩
  · have := ((r : ZMod p)⁻¹).val_lt
    lia
  · rw [← ZMod.val_natCast, Nat.cast_mul, ZMod.natCast_zmod_val, inv_mul_cancel₀ hr', ZMod.val_one]

theorem getElem!_inversesMod_mul_mod {p r : ℕ} (hp : p.Prime) (hr : r < p) (hr0 : r ≠ 0) :
    (inversesMod p)[r]! * r % p = 1 := by
  obtain ⟨s, hs⟩ : ∃ s, (List.range' 1 (p - 1)).find? (· * r % p == 1) = some s := by
    rw [← Option.isSome_iff_exists, List.find?_isSome]
    simpa using exists_mem_range'_mul_mod_eq_one hp hr hr0
  rw [getElem!_pos (inversesMod p) r (by simpa [inversesMod] using hr)]
  simpa [inversesMod, hs] using List.find?_some hs

theorem natCast_mul_getElem!_inversesMod_mod {p : ℕ} [hp : Fact p.Prime] (x : ℕ) {r : ℕ}
    (hr : r < p) (hr0 : r ≠ 0) :
    ((x * (inversesMod p)[r]! % p : ℕ) : ZMod p) = x / r := by
  have h : ((inversesMod p)[r]! : ZMod p) * r = 1 := by
    rw [← Nat.cast_mul, ← ZMod.natCast_mod, getElem!_inversesMod_mul_mod hp.out hr hr0,
      Nat.cast_one]
  rw [ZMod.natCast_mod, Nat.cast_mul, div_eq_mul_inv, eq_inv_of_mul_eq_one_left h]

@[simp]
theorem evalMod_nil (p x : ℕ) : evalMod [] p x = 0 := rfl

@[simp]
theorem evalMod_cons (a : ℕ) (cs : List ℕ) (p x : ℕ) :
    evalMod (a :: cs) p x = (a + x * evalMod cs p x) % p := rfl

theorem evalMod_lt (cs : List ℕ) {p : ℕ} (hp : 0 < p) (x : ℕ) : evalMod cs p x < p := by
  cases cs with
  | nil => exact hp
  | cons a cs => exact Nat.mod_lt _ hp

theorem natCast_evalMod (cs : List ℕ) (p x : ℕ) :
    (evalMod cs p x : ZMod p) = ∑ k ∈ Finset.range cs.length, (cs.getD k 0 : ZMod p) * x ^ k := by
  induction cs with
  | nil => simp
  | cons a cs ih =>
    rw [evalMod_cons, ZMod.natCast_mod, List.length_cons, Finset.sum_range_succ']
    simp only [Nat.cast_add, Nat.cast_mul, ih, Finset.mul_sum, List.getD_cons_succ,
      List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]
    exact congr($(Finset.sum_congr rfl fun k _ ↦ by ring) + _)

theorem natCast_evalMod_map_range (c : List ℤ) (d : ℕ) {p : ℕ} [NeZero p] (t : ℕ) :
    (evalMod ((List.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat) p t : ZMod p) =
      ∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod p) * t ^ k := by
  rw [natCast_evalMod, List.length_map, List.length_range]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (Finset.mem_range.mp hk),
    Option.map_some, Option.getD_some, ZMod.natCast_toNat_emod]

/-! ### The table of a prime -/

@[simp]
theorem p_examinePrime (c : List ℤ) (d p : ℕ) : (examinePrime c d p).p = p := rfl

@[simp]
theorem inverses_examinePrime (c : List ℤ) (d p : ℕ) :
    (examinePrime c d p).inverses = inversesMod p := rfl

theorem getElem!_isFSquare_examinePrime (c : List ℤ) (d : ℕ) {p t : ℕ} (ht : t < p) :
    (examinePrime c d p).isFSquare[t]! = (squaresMod p)[evalMod
      ((List.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat) p t]! := by
  simp only [examinePrime]
  rw [getElem!_pos _ t (by simpa using ht)]
  simp

/-! ### The rows let every point through -/

theorem toNat_emod_ne_zero_of_gcd_eq_one {p : ℕ} (hp : 1 < p) {a : ℤ} {b : ℕ}
    (hab : Int.gcd a b = 1) (hb : b % p = 0) : (a % (p : ℤ)).toNat ≠ 0 := by
  intro ha
  have hp0 : (p : ℤ) ≠ 0 := by lia
  have hpa : (p : ℤ) ∣ a := Int.dvd_of_emod_eq_zero (by have := Int.emod_nonneg a hp0; lia)
  have hpb : (p : ℤ) ∣ b := mod_cast Nat.dvd_of_mod_eq_zero hb
  have := Int.dvd_gcd hpa hpb
  rw [hab, Nat.dvd_one] at this
  lia

/-- The table of the prime `p` marks every residue `t` at which `f = ∑ cₖ Xᵏ` takes a square value
modulo `p`. -/
theorem getElem!_isFSquare_examinePrime_of_isSquare {c : List ℤ} {d p t : ℕ} (hp : p.Prime)
    (ht : t < p) (h : IsSquare (∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod p) * t ^ k)) :
    (examinePrime c d p).isFSquare[t]! = true := by
  have : NeZero p := ⟨hp.ne_zero⟩
  rw [← natCast_evalMod_map_range c d t] at h
  obtain ⟨s, hs, h⟩ := ZMod.exists_eq_mul_self_mod_of_isSquare (evalMod_lt _ hp.pos _) h
  rw [getElem!_isFSquare_examinePrime _ _ ht, h]
  exact getElem!_squaresMod_mul_self_mod hp hs

theorem isSquare_sum_mul_div_pow_of_sq_eq_binaryForm {c : List ℤ} {p : ℕ} [Fact p.Prime]
    {a y : ℤ} {b : ℕ} (hb : b % p ≠ 0) (hy : y ^ 2 = binaryForm c a b) :
    IsSquare (∑ k ∈ Finset.range (degree c + 1), (c.getD k 0 : ZMod p) * (a / b : ZMod p) ^ k) := by
  have hb' : (b : ZMod p) ≠ 0 :=
    fun h ↦ hb (Nat.mod_eq_zero_of_dvd ((ZMod.natCast_eq_zero_iff _ _).mp h))
  have h2 := congr(($hy : ZMod p))
  push_cast [binaryForm] at h2
  exact isSquare_sum_mul_div_pow_of_sq_eq (by lia) (Nat.even_iff.mpr (by lia)) hb' h2

/-- The row of the denominator `b` in the table of the prime `p` admits the numerator `a` of every
point `(a, y, b)` with `gcd(a, b) = 1`; neither `b ≥ 1` nor an odd `p` is needed. -/
theorem admits_examinePrime_of_sq_eq {c : List ℤ} {p : ℕ} (hp : p.Prime) {a y : ℤ} {b : ℕ}
    (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    (examinePrime c (BruteForce.degree c) p).admits b a = true := by
  have : Fact p.Prime := ⟨hp⟩
  simp only [Entry.admits, p_examinePrime, inverses_examinePrime]
  by_cases hb : b % p = 0 <;> simp only [hb, ↓reduceIte]
  · simpa using toNat_emod_ne_zero_of_gcd_eq_one hp.one_lt hab hb
  · refine getElem!_isFSquare_examinePrime_of_isSquare hp (Nat.mod_lt _ hp.pos) ?_
    rw [BruteForce.degree_eq, natCast_mul_getElem!_inversesMod_mod _ (Nat.mod_lt _ hp.pos) hb,
      ZMod.natCast_toNat_emod, ZMod.natCast_mod]
    exact isSquare_sum_mul_div_pow_of_sq_eq_binaryForm hb hy

end Sieve

end Ratpoints

end
