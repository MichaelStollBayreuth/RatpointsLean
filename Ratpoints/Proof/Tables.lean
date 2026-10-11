/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Ratpoints.Model.Setup
public import Ratpoints.Model.Sieve
public import Ratpoints.Spec.Basic

import Mathlib.Tactic.Field
import Mathlib.Tactic.Ring
import Ratpoints.Mathlib.Data.ZMod.Basic
import Ratpoints.Proof.BruteForce

/-!
# The tables of a prime, the soundness of the rows and the exit

The tables of the sieve compute what they claim: the squares, the inverses and Horner's rule modulo
`p`. With them, the row of a denominator `b` in the table of a prime `p` lets the numerator `a` of
every point `(a, y, b)` through (`Ratpoints.Sieve.admits_examinePrime_of_sq_eq`): for `p ∤ b`, since
`F(a, b) ≡ b ^ D f(a / b) (mod p)` with `D` even, so that `f(a / b)` is a square modulo `p`
(`Ratpoints.Sieve.isSquare_sum_mul_div_pow_of_sq_eq_binaryForm`), which the table of the prime marks
(`Ratpoints.Sieve.getElem!_isFSquare_examinePrime_of_isSquare`); for `p ∣ b`, since `gcd(a, b) = 1`,
so that `p ∤ a` (`Ratpoints.Sieve.toNat_emod_ne_zero_of_gcd_eq_one`). The model computes modulo `p`
in `ℕ`; the proofs go through `ZMod p`.

The table of a prime with the exit (`Ratpoints.Sieve.examinePrime?`) reduces the coefficients on two
paths with the same result, since the helper `mod` of the C code is the Euclidean `%`
(`Ratpoints.Sieve.modLong_eq_emod`); a table that it gives is that of the reference
`Ratpoints.Sieve.examinePrime`, and when it gives none, the curve has no points
(`Ratpoints.Sieve.not_isPoint_of_examinePrime?_eq_none`): a point `(a, y, b)` gives a residue that
the table marks for `p ∤ b`, and for `p ∣ b` a point at infinity modulo `p`, since `c_d` is then a
square modulo `p` for even `d` (`Ratpoints.Sieve.isSquare_getD_degree_of_sq_eq_binaryForm`). The
values of the C code that could leave the range of a `long` stay in it: those of `mod` for moduli
below `2 ^ 59`, whose inputs are `long`s by the flag of the `long`s, and the negations of the map of
a reversed search.

## Main statements

* `Ratpoints.isSquare_sum_mul_div_pow_of_sq_eq`: a square value of the form gives a square value
  of `f`.
* `Ratpoints.Sieve.getElem!_squaresMod_mul_self_mod`,
  `Ratpoints.Sieve.getElem!_squaresMod_of_isSquare`, `Ratpoints.Sieve.getElem!_inversesMod_mul_mod`,
  `Ratpoints.Sieve.natCast_evalMod`: the tables compute their definitions.
* `Ratpoints.Sieve.getElem!_isFSquare_examinePrime_of_isSquare`: the table of a prime marks every
  residue at which `f` takes a square value.
* `Ratpoints.Sieve.admits_examinePrime_of_sq_eq`: the rows let every point through.
* `Ratpoints.Sieve.modLong_eq_emod`: the helper `mod` of the C code is the Euclidean `%`.
* `Ratpoints.Sieve.examinePrime?_eq_examinePrime?_false`,
  `Ratpoints.Sieve.eq_examinePrime_of_examinePrime?_eq_some`,
  `Ratpoints.Sieve.examinePrime?_eq_none_iff`: the two paths of the table with the exit give the
  same result, its table is that of the reference, and when it gives none.
* `Ratpoints.Sieve.not_isPoint_of_examinePrime?_eq_none`: a curve without points modulo a prime
  has no points.
* `Ratpoints.fitsLong_sixteen_mul`, `Ratpoints.fitsLong_add_sixteen_mul`, `Ratpoints.fitsLong_neg`:
  the values of the C code that could leave the range of a `long` stay in it.
* `Ratpoints.Setup.fitsLong_getD_of_useCLong`: the inputs of `mod` are `long`s.
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

theorem getElem!_squaresMod_of_isSquare {p t : ℕ} (hp : p.Prime) (ht : t < p)
    (h : IsSquare (t : ZMod p)) : (squaresMod p)[t]! = true := by
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨s, hs, rfl⟩ := ZMod.exists_eq_mul_self_mod_of_isSquare ht h
  exact getElem!_squaresMod_mul_self_mod hp hs

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
  rw [getElem!_isFSquare_examinePrime _ _ ht]
  exact getElem!_squaresMod_of_isSquare hp (evalMod_lt _ hp.pos _) h

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

/-! ### The helper `mod` -/

-- A conditional subtraction of `m` reduces `0 ≤ a < 2 m` modulo `m`: a rung of the ladder of `mod`.
private theorem ite_le_sub_eq_emod {a m : ℤ} (h0 : 0 ≤ a) (h1 : a < 2 * m) :
    (if m ≤ a then a - m else a) = a % m := by
  split
  · rw [← Int.sub_emod_right a m, Int.emod_eq_of_lt (by lia) (by lia)]
  · rw [Int.emod_eq_of_lt h0 (by lia)]

-- The rung on a residue modulo `n = 2 m`.
private theorem ite_le_emod_sub_eq_emod (a : ℤ) {m n : ℤ} (hm : 0 < m) (hn : n = 2 * m) :
    (if m ≤ a % n then a % n - m else a % n) = a % m := by
  rw [ite_le_sub_eq_emod (Int.emod_nonneg _ (by lia)) (hn ▸ Int.emod_lt_of_pos _ (by lia)),
    Int.emod_emod_of_dvd _ (hn ▸ dvd_mul_left m 2)]

-- `mod` for `-16 b ≤ a < 16 b`: `16 b` added to a negative `a`, then the ladder of conditional
-- subtractions.
private theorem modLong_eq_emod_of_le_of_lt {a b : ℤ} (hb : 0 < b) (h0 : -(16 * b) ≤ a)
    (h1 : a < 16 * b) : modLong a b = a % b := by
  simp only [modLong, h0.not_gt, h1.not_ge, and_false, ↓reduceIte]
  have hy : (if a < 0 then a + 16 * b else a) % b = a % b := by split <;> simp
  have h2 : 0 ≤ (if a < 0 then a + 16 * b else a) := by split <;> lia
  have h3 : (if a < 0 then a + 16 * b else a) < 2 * (8 * b) := by split <;> lia
  generalize (if a < 0 then a + 16 * b else a) = y at hy h2 h3 ⊢
  rw [← hy, ite_le_sub_eq_emod h2 h3, ite_le_emod_sub_eq_emod y (m := 4 * b) (by lia) (by lia),
    ite_le_emod_sub_eq_emod y (m := 2 * b) (by lia) (by lia), ite_le_emod_sub_eq_emod y hb rfl]

/-- The helper `mod` of the C code is the Euclidean `%`, for every integer `a` and every `b ≥ 0`:
the model computes with integers, and the obligations that the values of the C code stay in the
range of a `long` are `Ratpoints.fitsLong_sixteen_mul`, `Ratpoints.fitsLong_neg` and
`Ratpoints.fitsLong_add_sixteen_mul`. -/
theorem modLong_eq_emod (a : ℤ) {b : ℤ} (hb : 0 ≤ b) : modLong a b = a % b := by
  obtain rfl | hb := hb.eq_or_lt
  · simp [modLong]
  rcases lt_or_ge a (-(16 * b)) with h | h
  · grind [modLong, Int.tmod_eq_emod, Int.emod_nonneg a hb.ne', Int.emod_lt_of_pos a hb]
  rcases lt_or_ge a (16 * b) with h' | h'
  · exact modLong_eq_emod_of_le_of_lt hb h h'
  · grind [modLong, Int.tmod_eq_emod_of_nonneg]

/-! ### The table of a prime with the exit -/

/-- The path through `long`s, with the helper `mod` of the C code, and the path through GMP
integers give the same table, whatever the coefficients: the flag of the `long`s changes nothing. -/
theorem examinePrime?_eq_examinePrime?_false (c : List ℤ) (d p : ℕ) (u : Bool) :
    examinePrime? c d p u = examinePrime? c d p false := by
  simp [examinePrime?, modLong_eq_emod]

theorem eq_examinePrime_of_examinePrime?_eq_some {c : List ℤ} {d p : ℕ} {u : Bool} {e : Entry}
    (h : examinePrime? c d p u = some e) : e = examinePrime c d p := by
  grind [examinePrime?_eq_examinePrime?_false, examinePrime?, examinePrime]

/-- The exit of `examine_prime`, in the terms of the table of the reference: no residue at which
`f` takes a square value modulo `p`, even degree, and `c_d` not a square modulo `p`. -/
theorem examinePrime?_eq_none_iff {c : List ℤ} {d p : ℕ} {u : Bool} :
    examinePrime? c d p u = none ↔ (examinePrime c d p).isFSquare.any id = false ∧
      d % 2 = 0 ∧ (squaresMod p)[(c.getD d 0 % (p : ℤ)).toNat]! = false := by
  rw [examinePrime?_eq_examinePrime?_false]
  simp [examinePrime?, examinePrime, List.getD_eq_getElem?_getD]

/-! ### The exit -/

/-- A point `(a, y, b)` with `p ∣ b`, among them the points at infinity, makes the leading
coefficient `c_d` a square modulo `p` for even `d`: since `gcd(a, b) = 1`, `p ∤ a`, and
`y ^ 2 ≡ c_d a ^ d (mod p)`. -/
theorem isSquare_getD_degree_of_sq_eq_binaryForm {c : List ℤ} {p : ℕ} [Fact p.Prime]
    {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hb : b % p = 0) (hd : degree c % 2 = 0)
    (hy : y ^ 2 = binaryForm c a b) : IsSquare (c.getD (degree c) 0 : ZMod p) := by
  have hb' : (b : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hb)
  have ha : (a : ZMod p) ≠ 0 := fun h ↦ (Fact.out : p.Prime).one_lt.ne' <| by
    simpa [hab] using Int.dvd_gcd ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)
      (Int.natCast_dvd_natCast.mpr (Nat.dvd_of_mod_eq_zero hb))
  have h2 := congr(($hy : ZMod p))
  push_cast [binaryForm, hb', hd, Nat.add_zero] at h2
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi ↦ by
    rw [zero_pow (by have := Finset.mem_range.mp hi; lia), mul_zero], zero_add, Nat.sub_self,
    pow_zero, mul_one] at h2
  rw [eq_div_of_mul_eq (pow_ne_zero _ ha) h2.symm]
  exact (IsSquare.sq (y : ZMod p)).div ((Nat.even_iff.mpr hd).isSquare_pow _)

-- A point gives a residue `t < p` that the table of `p` marks, or a point at infinity modulo `p`:
-- odd degree, or `c_d` marked as a square.
private theorem exists_isFSquare_or_of_sq_eq_binaryForm {c : List ℤ} {p : ℕ} (hp : p.Prime)
    {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    (∃ t < p, (examinePrime c (degree c) p).isFSquare[t]! = true) ∨
      degree c % 2 = 1 ∨ (squaresMod p)[(c.getD (degree c) 0 % (p : ℤ)).toNat]! = true := by
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  by_cases hb : b % p = 0
  · rcases Nat.mod_two_eq_zero_or_one (degree c) with hd | hd
    · refine .inr (.inr (getElem!_squaresMod_of_isSquare hp ?_ ?_))
      · exact (Int.toNat_lt' hp.pos).mpr (Int.emod_lt_of_pos _ (mod_cast hp.pos))
      · rw [ZMod.natCast_toNat_emod]
        exact isSquare_getD_degree_of_sq_eq_binaryForm hab hb hd hy
    · exact .inr (.inl hd)
  · have h := admits_examinePrime_of_sq_eq hp hab hy
    simp only [Entry.admits, p_examinePrime, inverses_examinePrime, hb, ↓reduceIte] at h
    exact .inl ⟨_, Nat.mod_lt _ hp.pos, h⟩

/-- When the table of the prime `p` is none, where `examine_prime` returns `-1` and the search ends,
the curve has no points of any height. -/
theorem not_isPoint_of_examinePrime?_eq_none {c : List ℤ} {d p : ℕ} {u : Bool}
    (h : examinePrime? c d p u = none) (hp : p.Prime) (hd : d = degree c) (H : ℕ)
    (q : ℤ × ℤ × ℤ) : ¬ IsPoint c H q := by
  obtain ⟨hany, h2, hsq⟩ := examinePrime?_eq_none_iff.mp h
  subst hd
  intro ⟨hy, hg, hn, _, _⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, q.2.2 = b := ⟨q.2.2.toNat, by lia⟩
  rw [hb] at hy hg
  rcases exists_isFSquare_or_of_sq_eq_binaryForm hp hg hy with ⟨t, ht, hf⟩ | hd | hc
  · rw [getElem!_pos _ t (by simpa [examinePrime] using ht)] at hf
    exact Array.any_eq_false.mp hany t _ hf
  · lia
  · exact Bool.false_ne_true (hsq.symm.trans hc)

end Sieve

/-! ### The coefficients as `long`s -/

/-- The value `b1 = 16 b` that the helper `mod` of the C code (`Ratpoints.Sieve.modLong`) computes
first is a `long` for `0 ≤ b < 2 ^ 59`, and so is its negation (`Ratpoints.fitsLong_neg`), which
`mod` compares with `a`. -/
theorem fitsLong_sixteen_mul {b : ℤ} (hb0 : 0 ≤ b) (hb : b < 2 ^ 59) :
    fitsLong (16 * b) = true := by
  grind [fitsLong]

/-- The value `a + 16 b` that the helper `mod` of the C code (`Ratpoints.Sieve.modLong`) computes
for `-16 b ≤ a < 0` is a `long` for `b < 2 ^ 59`. The other values that `mod` computes, but for
`16 b` and its negation (`Ratpoints.fitsLong_sixteen_mul`, `Ratpoints.fitsLong_neg`), lie between
`-b` and `16 b`. -/
theorem fitsLong_add_sixteen_mul {a b : ℤ} (hb : b < 2 ^ 59) (ha0 : -(16 * b) ≤ a) (ha : a < 0) :
    fitsLong (a + 16 * b) = true := by
  grind [fitsLong]

/-- The negation of an integer of absolute value below `2 ^ 63` is a `long`: so is the negation
`-16 b` that the helper `mod` of the C code (`Ratpoints.Sieve.modLong`) computes for
`0 ≤ b < 2 ^ 59`, and so are the negations `-b` and `-a` of the map of a reversed search
(`Ratpoints.Sieve.swapPoint`) for a point `(a, y, b)` with `|a| ≤ H` and `1 ≤ b ≤ H`, since the
height bound `H` is a `long`. -/
theorem fitsLong_neg {a : ℤ} (ha : |a| < 2 ^ 63) : fitsLong (-a) = true := by
  grind [fitsLong, abs_lt.mp ha]

/-- The inputs of the helper `mod` of the C code on the path through `long`s of the table of a
prime, the coefficients `c₀, …, c_d`, are `long`s: `use_c_long` holds only when each of them is. -/
theorem Setup.fitsLong_getD_of_useCLong {c : List ℤ} {d n : ℕ} (h : useCLong c d = true)
    (hn : n ≤ d) : fitsLong (c.getD n 0) = true :=
  List.all_eq_true.mp h n (List.mem_range.mpr (Nat.lt_succ_of_le hn))

end Ratpoints

end
