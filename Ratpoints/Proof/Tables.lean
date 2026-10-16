/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Field.ZMod
public import Ratpoints.Model.Setup
public import Ratpoints.Proof.Stages
public import Ratpoints.Spec.Basic

import Mathlib.Data.List.GetD
import Ratpoints.Mathlib.Algebra.Group.Even
import Ratpoints.Mathlib.Data.ZMod.Basic
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Params
import Std.Tactic.Do

/-!
# The tables of a prime, the soundness of the rows and the exit

The tables of the sieve compute what they claim: the squares, the inverses and Horner's rule modulo
`p`. With them, the row of a denominator `b` in the table of a prime `p` lets the numerator `a` of
every point `(a, y, b)` through (`Ratpoints.Sieve.admits_examinePrime_of_sq_eq`): for `p ∤ b`, since
`F(a, b) ≡ b ^ D f(a / b) (mod p)` with `D` even, so that `f(a / b)` is a square modulo `p`
(`Ratpoints.Sieve.isSquare_sum_mul_div_pow_of_sq_eq_binaryForm`), which the table of the prime marks
(`Ratpoints.Sieve.getElem!_isFSquare_examinePrime_of_isSquare`); for `p ∣ b`, since `gcd(a, b) = 1`,
so that `p ∤ a` (`Int.toNat_emod_ne_zero_of_gcd_eq_one`). The model computes modulo `p` in `ℕ`; the
proofs go through `ZMod p`.

The table of a prime with the exit (`Ratpoints.Sieve.examinePrime?`) reduces the coefficients on two
paths with the same result, since the helper `mod` of the C code is the Euclidean `%`
(`Ratpoints.Sieve.modLong_eq_emod`), and computes the values of `f` by Horner's rule with Barrett's
reduction on a fixed schedule (`Ratpoints.Sieve.hornerBarrett`): Barrett's reduction gives the
remainder of every `u < 2 ^ 64` (`Ratpoints.Sieve.barrett_eq`), and for `p < maxPrimeEven` the
accumulator stays below `p ^ (hornerSteps + 1) < 2 ^ 64` between two reductions
(`Ratpoints.Sieve.HornerInvariant.lt_two_pow_64`). So for `0 < p < maxPrimeEven` the table that its
loop over the residues gives is that of the reference `Ratpoints.Sieve.examinePrime`, handed back
with the coefficients reduced modulo `p`, and when it gives none for a prime `p`, the curve has no
points (`Ratpoints.Sieve.not_isPoint_of_run_examinePrime?_eq_none`): a point `(a, y, b)` gives a
residue that the table marks for `p ∤ b`, and for `p ∣ b` a point at infinity modulo `p`, the last
entry of the table, since `c_d` is then a square modulo `p` for even `d`
(`Ratpoints.Sieve.isSquare_getD_degree_of_sq_eq_binaryForm`). The values of the C code that could
leave the range of a `long` stay in it: those of `mod` for moduli below `2 ^ 59`, whose inputs are
`long`s by the flag of the `long`s, the negations of the map of a reversed search, and the negation
of a negative leading coefficient in `jacobi1`, with `LONG_MIN` replaced by its quarter.

## Main definitions

* `Ratpoints.Sieve.HornerInvariant`, `Ratpoints.Sieve.ExaminePrimeInvariant`: the invariants of the
  loop of Horner's rule in `Ratpoints.Sieve.hornerBarrett` and of the loop over the residues in
  `Ratpoints.Sieve.examinePrime?`.

## Main statements

* `Ratpoints.sum_mul_pow_mul_pow_sub_of_eq_mul`: the binary form of degree `D` at `a = k b` is
  `f(k) b ^ D`, in any commutative semiring.
* `Ratpoints.isSquare_sum_mul_pow_of_sq_eq_binaryForm`,
  `Ratpoints.isSquare_sum_mul_pow_sub_of_sq_eq_binaryForm`: a point whose denominator, or numerator,
  is a unit of a commutative ring makes `f`, or the reversed polynomial, take a square value there;
  `Ratpoints.isSquare_sum_mul_div_pow_of_sq_eq`: in a semifield, a square value of the form gives a
  square value of `f`.
* `Ratpoints.Sieve.getElem!_squaresMod_mul_self_mod`,
  `Ratpoints.Sieve.getElem!_squaresMod_of_isSquare`, `Ratpoints.Sieve.getElem!_inversesMod_mul_mod`,
  `Ratpoints.Sieve.natCast_evalMod`, `Ratpoints.Sieve.natCast_evalMod_reverse`: the tables compute
  their definitions.
* `Ratpoints.Sieve.getElem!_isFSquare_examinePrime_of_isSquare`: the table of a prime marks every
  residue at which `f` takes a square value.
* `Ratpoints.Sieve.getElem!_isFSquare_examinePrime_self`: the entry of the table of a prime at `p`
  says whether there are points at infinity modulo `p`.
* `Ratpoints.Sieve.admits_examinePrime_of_sq_eq`: the rows let every point through.
* `Ratpoints.Sieve.isPrimeEntry_examinePrime`: a sieve entry of a prime `p ≤ 2 ^ 32` whose single
  factor is its table, with its reciprocal, has the shape that the third stage needs.
* `Ratpoints.Sieve.barrett_eq`: Barrett's reduction computes the remainder of every `u < 2 ^ 64`.
* `Ratpoints.Sieve.HornerInvariant.lt_two_pow_64`: the accumulator of Horner's rule in the table of
  `p < maxPrimeEven` stays below `2 ^ 64` (`Ratpoints.pow_hornerSteps_add_one_lt`).
* `Ratpoints.Sieve.hornerBarrett_spec`: Horner's rule with Barrett's reduction on its schedule
  computes the value modulo `p` (`Ratpoints.Sieve.evalMod`).
* `Ratpoints.Sieve.examinePrime?_eq_examinePrime?_false`, `Ratpoints.Sieve.examinePrime?_spec`,
  with its plain forms `Ratpoints.Sieve.run_examinePrime?`,
  `Ratpoints.Sieve.eq_examinePrime_of_run_examinePrime?_eq_some`,
  `Ratpoints.Sieve.eq_map_range_of_run_examinePrime?_eq_some` and
  `Ratpoints.Sieve.run_examinePrime?_eq_none_iff`: the two paths of the table with the exit give
  the same result, which is the table of the reference with the coefficients reduced modulo `p` for
  `0 < p < maxPrimeEven`, and when it gives none;
  `Ratpoints.Sieve.eq_examinePrime_of_lt_numPrimes_of_run_examinePrime?_eq_some`: so for the prime
  at a position below `Ratpoints.numPrimes` of the table.
* `Ratpoints.Sieve.any_isFSquare_examinePrime_of_sq_eq`,
  `Ratpoints.Sieve.not_isPoint_of_run_examinePrime?_eq_none`,
  `Ratpoints.Sieve.not_isPoint_of_lt_numPrimes_of_run_examinePrime?_eq_none`: a point makes an
  entry of the table of a prime true, so a curve without points modulo a prime has no points.
* `Ratpoints.fitsLong_natCast`: a natural number is a `long` exactly when it is below `2 ^ 63`.
* `Ratpoints.fitsLong_sixteen_mul`, `Ratpoints.fitsLong_add_sixteen_mul`, `Ratpoints.fitsLong_neg`,
  `Ratpoints.fitsLong_neg_ite_div_four`: the values of the C code that could leave the range of a
  `long` stay in it.
* `Ratpoints.Setup.fitsLong_getD_of_useCLong`: the inputs of `mod` are `long`s.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

/-- The binary form `∑ fᵢ aⁱ b^(D - i)` of degree `D ≥ d` at `a = k b` is `f(k) b ^ D`, in any
commutative semiring; over a field, `k = a / b` for `b ≠ 0`, as `Polynomial.eval_homogenize` says
for polynomials. -/
theorem sum_mul_pow_mul_pow_sub_of_eq_mul {R : Type*} [CommSemiring R] {d D : ℕ} (hd : d ≤ D)
    (f : ℕ → R) {a b k : R} (h : a = k * b) :
    ∑ i ∈ Finset.range (d + 1), f i * a ^ i * b ^ (D - i) =
      (∑ i ∈ Finset.range (d + 1), f i * k ^ i) * b ^ D := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [h, mul_pow, ← pow_mul_pow_sub b ((Finset.mem_range_succ_iff.mp hi).trans hd)]
  ring

/-- The binary form `∑ fᵢ aⁱ b^(D - i)` of degree `D ≥ d` at `b = t a` is the value
`∑ fᵢ t^(D - i)` of the reversed polynomial times `a ^ D`, in any commutative semiring. -/
theorem sum_mul_pow_mul_pow_sub_of_eq_mul' {R : Type*} [CommSemiring R] {d D : ℕ} (hd : d ≤ D)
    (f : ℕ → R) {a b t : R} (h : b = t * a) :
    ∑ i ∈ Finset.range (d + 1), f i * a ^ i * b ^ (D - i) =
      (∑ i ∈ Finset.range (d + 1), f i * t ^ (D - i)) * a ^ D := by
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  rw [h, mul_pow, ← pow_mul_pow_sub a ((Finset.mem_range_succ_iff.mp hi).trans hd)]
  ring

/-- If `y ^ 2` is the value at `(a, b)` of the binary form of even degree `D ≥ d` made from
`f = ∑ fᵢ Xⁱ`, then `f(a / b)` is the square of `y / b ^ (D / 2)`. -/
theorem isSquare_sum_mul_div_pow_of_sq_eq {K : Type*} [Semifield K] {d D : ℕ} (hd : d ≤ D)
    (hD : Even D) {f : ℕ → K} {a b y : K} (hb : b ≠ 0)
    (h : y ^ 2 = ∑ i ∈ Finset.range (d + 1), f i * a ^ i * b ^ (D - i)) :
    IsSquare (∑ i ∈ Finset.range (d + 1), f i * (a / b) ^ i) := by
  rw [sum_mul_pow_mul_pow_sub_of_eq_mul hd f (div_mul_cancel₀ a hb).symm] at h
  exact hb.isUnit.isSquare_of_sq_eq_mul_pow hD h

/-- A point `(a, y, b)` whose denominator `b` is a unit of the commutative ring `R` makes `f` take a
square value at the `k` with `a = k b` in `R`: `F(a, b) = f(k) b ^ D` with `D` even. -/
theorem isSquare_sum_mul_pow_of_sq_eq_binaryForm {R : Type*} [CommRing R] {c : List ℤ}
    {a y : ℤ} {b : ℕ} {k : R} (hb : IsUnit (b : R)) (hk : (a : R) = k * b)
    (hy : y ^ 2 = binaryForm c a b) :
    IsSquare (∑ i ∈ Finset.range (degree c + 1), (c.getD i 0 : R) * k ^ i) := by
  have h2 := congr(($hy : R))
  push_cast [binaryForm] at h2
  rw [sum_mul_pow_mul_pow_sub_of_eq_mul (by lia) _ hk] at h2
  exact hb.isSquare_of_sq_eq_mul_pow (Nat.even_iff.mpr (by lia)) h2

/-- A point `(a, y, b)` whose numerator `a` is a unit of the commutative ring `R` makes the reversed
polynomial take a square value `∑ cᵢ t^(D - i)` at the `t` with `b = t a` in `R`:
`F(a, b) = a ^ D ∑ cᵢ t^(D - i)` with `D` even. -/
theorem isSquare_sum_mul_pow_sub_of_sq_eq_binaryForm {R : Type*} [CommRing R] {c : List ℤ}
    {a y : ℤ} {b : ℕ} {t : R} (ha : IsUnit (a : R)) (ht : (b : R) = t * a)
    (hy : y ^ 2 = binaryForm c a b) :
    IsSquare (∑ i ∈ Finset.range (degree c + 1),
      (c.getD i 0 : R) * t ^ (degree c + degree c % 2 - i)) := by
  have h2 := congr(($hy : R))
  push_cast [binaryForm] at h2
  rw [sum_mul_pow_mul_pow_sub_of_eq_mul' (by lia) _ ht] at h2
  exact ha.isSquare_of_sq_eq_mul_pow (Nat.even_iff.mpr (by lia)) h2

namespace Sieve

/-! ### The squares, the inverses and Horner's rule modulo `p` -/

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
  simp only [squaresMod, Array.set!_eq_setIfInBounds, Array.getElem!_foldl_setIfInBounds _ _ _ ht,
    Bool.or_eq_true, List.any_eq_true, beq_iff_eq, List.mem_range']
  obtain rfl | hs0 := eq_or_ne s 0
  · left
    rw [getElem!_pos ((Array.replicate p false).setIfInBounds 0 true) _ ht]
    simp
  · obtain ⟨_, hi, ⟨m, rfl⟩, heq⟩ := exists_odd_mul_self_mod_eq hp hs hs0
    exact .inr ⟨_, ⟨m, by lia, by lia⟩, heq⟩

theorem getElem!_squaresMod_zero {p : ℕ} (hp : p.Prime) : (squaresMod p)[0]! = true := by
  simpa using getElem!_squaresMod_mul_self_mod hp hp.pos

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

/-- The entries of the table of the inverses modulo `p` are residues modulo `p`. -/
theorem getElem!_inversesMod_lt {p r : ℕ} (hr : r < p) : (inversesMod p)[r]! < p := by
  rw [getElem!_pos (inversesMod p) r (by simpa [inversesMod] using hr)]
  simp only [inversesMod, Array.getElem_map, Array.getElem_range]
  cases h : (List.range' 1 (p - 1)).find? (· * r % p == 1) with
  | none => simpa using Nat.zero_lt_of_lt hr
  | some s => have := List.mem_range'_1.mp (List.mem_of_find?_eq_some h); simp; lia

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

/-- Entry `k ≤ d` of the coefficients `c₀, …, c_d` reduced modulo `m` is `c_k` in `ZMod m`. -/
theorem natCast_getD_map_range_toNat_emod (c : List ℤ) (d : ℕ) {m : ℕ} [NeZero m] {k : ℕ}
    (hk : k < d + 1) :
    ((((List.range (d + 1)).map fun n ↦ (c.getD n 0 % (m : ℤ)).toNat).getD k 0 : ℕ) : ZMod m) =
      c.getD k 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
    Option.getD_some, ZMod.natCast_toNat_emod]

theorem natCast_evalMod_map_range (c : List ℤ) (d : ℕ) {p : ℕ} [NeZero p] (t : ℕ) :
    (evalMod ((List.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat) p t : ZMod p) =
      ∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod p) * t ^ k := by
  rw [natCast_evalMod, List.length_map, List.length_range]
  exact Finset.sum_congr rfl fun _ hk ↦
    congr($(natCast_getD_map_range_toNat_emod c d (Finset.mem_range.mp hk)) * _)

/-- Horner's rule modulo `m` on the reversed list of coefficients: the value at `x` of the
polynomial whose coefficient of `x ^ (n - 1 - k)` is entry `k` of the list of length `n`. -/
theorem natCast_evalMod_reverse (cs : List ℕ) (m x : ℕ) :
    (evalMod cs.reverse m x : ZMod m) =
      ∑ k ∈ Finset.range cs.length, (cs.getD k 0 : ZMod m) * x ^ (cs.length - 1 - k) := by
  rw [natCast_evalMod, List.length_reverse, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun _ hk ↦ ?_
  have hk := Finset.mem_range.mp hk
  rw [List.getD_reverse _ (by lia), Nat.sub_sub_self (by lia)]

theorem evalMod_cons_zero (a : ℕ) (cs : List ℕ) (p : ℕ) : evalMod (a :: cs) p 0 = a % p := by
  simp

-- One step of Horner's rule modulo `p` on the coefficients of `l` from position `i` on.
private theorem evalMod_drop {l : List ℕ} {i : ℕ} (hi : i < l.length) (p x : ℕ) :
    evalMod (l.drop i) p x = (l[i] + x * evalMod (l.drop (i + 1)) p x) % p := by
  rw [List.drop_eq_getElem_cons hi, evalMod_cons]

/-! ### Barrett's reduction and the schedule of Horner's rule -/

/-- Barrett's reduction with the reciprocal `⌊(2 ^ 64 - 1) / p⌋` computes `u mod p` for every
`u < 2 ^ 64`: the estimate of the quotient is `⌊u / p⌋` or one less
(`Nat.mul_sub_one_div_div_mul_le`, `Nat.lt_mul_sub_one_div_div_add_two_mul`), so that one
conditional subtraction finishes. -/
theorem barrett_eq {u p : ℕ} (hp : 0 < p) (hu : u < 2 ^ 64) :
    barrett u p ((2 ^ 64 - 1) / p) = u % p := by
  have h1 := Nat.mul_sub_one_div_div_mul_le u (2 ^ 64) p
  have h2 := Nat.lt_mul_sub_one_div_div_add_two_mul hp hu
  simp only [barrett]
  generalize u * ((2 ^ 64 - 1) / p) / 2 ^ 64 = q at h1 h2
  rw [← Nat.sub_mul_mod (Nat.mul_comm q p ▸ h1),
    Nat.mod_eq_ite_of_lt_two_mul (by rw [Nat.add_mul] at h2; lia), Nat.mul_comm p q]

/-- The invariant of the loops of Horner's rule of `Ratpoints.Sieve.hornerBarrett` after `i`
steps, the last reduction `k` steps back: the accumulator `s` is congruent modulo `p` to the value
at `a` of the polynomial with the coefficients `cm[d - i], …, cm[d]`, and below `p ^ (k + 1)`. -/
def HornerInvariant (cm : Array ℕ) (d p a i k s : ℕ) : Prop :=
  s % p = evalMod (cm.toList.drop (d - i)) p a ∧ s < p ^ (k + 1)

theorem hornerInvariant_zero {cm : Array ℕ} {d p : ℕ} (hsize : cm.size = d + 1) (a : ℕ)
    (hd : cm[d]! < p) : HornerInvariant cm d p a 0 0 cm[d]! := by
  refine ⟨?_, by simpa using hd⟩
  rw [Nat.sub_zero, List.drop_eq_getElem_cons (by simp [hsize]), List.drop_eq_nil_of_le
    (by simp [hsize]), evalMod_cons, evalMod_nil, Nat.mul_zero, Nat.add_zero, Array.getElem_toList,
    getElem!_pos cm d (by lia)]

theorem HornerInvariant.pos {cm : Array ℕ} {d p a i k s : ℕ} (h : HornerInvariant cm d p a i k s) :
    0 < p :=
  Nat.pos_of_ne_zero fun hp ↦ by simpa [hp] using h.2

/-- The range obligation of the accumulator of Horner's rule in `examine_prime`: for
`p < maxPrimeEven`, the values `s a + c` of the steps (`find_points.c:1729`, `find_points.c:1741`)
and the values that Barrett's reduction takes (`find_points.c:1731`, `find_points.c:1742`,
`find_points.c:1744`) are below `p ^ (k + 1)` with `k ≤ hornerSteps`, so below `2 ^ 64`: the
`unsigned long` does not wrap. -/
theorem HornerInvariant.lt_two_pow_64 {cm : Array ℕ} {d p a i k s : ℕ}
    (h : HornerInvariant cm d p a i k s) (hp : p < maxPrimeEven) (hk : k ≤ hornerSteps) :
    s < 2 ^ 64 :=
  calc s < p ^ (k + 1) := h.2
    _ ≤ p ^ (hornerSteps + 1) := Nat.pow_le_pow_right h.pos (by lia)
    _ < 2 ^ 64 := pow_hornerSteps_add_one_lt hp

theorem HornerInvariant.add_one {cm : Array ℕ} {d p a i k s : ℕ}
    (h : HornerInvariant cm d p a i k s) (hsize : cm.size = d + 1) (hi : i < d) (ha : a < p)
    (hc : cm[d - 1 - i]! < p) :
    HornerInvariant cm d p a (i + 1) (k + 1) (s * a + cm[d - 1 - i]!) := by
  refine ⟨?_, Nat.pow_succ p (k + 1) ▸ Nat.mul_add_lt_mul_of_lt h.2 ha hc⟩
  rw [Nat.sub_right_comm d 1 i, Nat.sub_add_eq d i 1, evalMod_drop (by simp; lia),
    Nat.sub_one_add_one_eq_of_pos (Nat.sub_pos_of_lt hi), ← h.1, Array.getElem_toList,
    getElem!_pos cm (d - i - 1) (by lia)]
  simp [Nat.add_mod, Nat.mul_mod, Nat.mul_comm, Nat.add_comm]

/-- The reduction by Barrett's method in the loop of Horner's rule keeps the invariant and restarts
the bound. -/
theorem HornerInvariant.barrett_zero {cm : Array ℕ} {d p a i k s : ℕ}
    (h : HornerInvariant cm d p a i k s) (hp : p < maxPrimeEven) (hk : k ≤ hornerSteps) :
    HornerInvariant cm d p a i 0 (barrett s p ((2 ^ 64 - 1) / p)) :=
  barrett_eq h.pos (h.lt_two_pow_64 hp hk) ▸
    ⟨by rw [Nat.mod_mod, h.1], by simpa using Nat.mod_lt s h.pos⟩

theorem HornerInvariant.barrett_eq_evalMod {cm : Array ℕ} {d p a k s : ℕ}
    (h : HornerInvariant cm d p a d k s) (hp : p < maxPrimeEven) (hk : k ≤ hornerSteps) :
    barrett s p ((2 ^ 64 - 1) / p) = evalMod cm.toList p a := by
  rw [barrett_eq h.pos (h.lt_two_pow_64 hp hk), h.1, Nat.sub_self, List.drop_zero]

theorem HornerInvariant.push {cm : Array ℕ} {d p a k s : ℕ} {pref suff : List ℕ} {cur : ℕ}
    (h : HornerInvariant cm d p a pref.length k s) (hl : ForIn.toList [:d] = pref ++ cur :: suff)
    (hsize : cm.size = d + 1) (ha : a < p) (hcm : ∀ i : ℕ, cm[i]! < p) :
    HornerInvariant cm d p a (pref ++ [cur]).length (k + 1) (s * a + cm[d - 1 - cur]!) := by
  obtain rfl := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton]
  exact h.add_one hsize (Std.Legacy.Range.lt_of_toList_eq_append_cons hl) ha (hcm _)

/-- The step of the loop of Horner's rule of `Ratpoints.Sieve.hornerBarrett` without reductions,
for `d ≤ hornerSteps`. -/
theorem HornerInvariant.push_self {cm : Array ℕ} {d p a s : ℕ} {pref suff : List ℕ} {cur : ℕ}
    (h : HornerInvariant cm d p a pref.length pref.length s)
    (hl : ForIn.toList [:d] = pref ++ cur :: suff) (hsize : cm.size = d + 1) (ha : a < p)
    (hcm : ∀ i : ℕ, cm[i]! < p) :
    HornerInvariant cm d p a (pref ++ [cur]).length (pref ++ [cur]).length
      (s * a + cm[d - 1 - cur]!) := by
  simpa only [List.length_append, List.length_singleton] using h.push hl hsize ha hcm

/-- The step of the loop of Horner's rule of `Ratpoints.Sieve.hornerBarrett` with reductions, for
`d > hornerSteps`, that reduces. -/
theorem HornerInvariant.push_barrett {cm : Array ℕ} {d p a k s : ℕ} {pref suff : List ℕ}
    {cur : ℕ} (h : HornerInvariant cm d p a pref.length k s ∧ k < hornerSteps)
    (hl : ForIn.toList [:d] = pref ++ cur :: suff) (hk : k + 1 = hornerSteps)
    (hsize : cm.size = d + 1) (hp : p < maxPrimeEven) (ha : a < p) (hcm : ∀ i : ℕ, cm[i]! < p) :
    HornerInvariant cm d p a (pref ++ [cur]).length 0
        (barrett (s * a + cm[d - 1 - cur]!) p ((2 ^ 64 - 1) / p)) ∧ 0 < hornerSteps :=
  ⟨(h.1.push hl hsize ha hcm).barrett_zero hp hk.le, one_le_hornerSteps⟩

/-- The step of the loop of Horner's rule of `Ratpoints.Sieve.hornerBarrett` with reductions, for
`d > hornerSteps`, that does not reduce. -/
theorem HornerInvariant.push_lt {cm : Array ℕ} {d p a k s : ℕ} {pref suff : List ℕ} {cur : ℕ}
    (h : HornerInvariant cm d p a pref.length k s ∧ k < hornerSteps)
    (hl : ForIn.toList [:d] = pref ++ cur :: suff) (hk : ¬k + 1 = hornerSteps)
    (hsize : cm.size = d + 1) (ha : a < p) (hcm : ∀ i : ℕ, cm[i]! < p) :
    HornerInvariant cm d p a (pref ++ [cur]).length (k + 1) (s * a + cm[d - 1 - cur]!) ∧
      k + 1 < hornerSteps :=
  ⟨h.1.push hl hsize ha hcm, by lia⟩

/-- The exit of the loop of Horner's rule of `Ratpoints.Sieve.hornerBarrett` without reductions,
for `d ≤ hornerSteps`, with the reduction at the end. -/
theorem HornerInvariant.barrett_eq_evalMod_of_le {cm : Array ℕ} {d p a s : ℕ}
    (h : HornerInvariant cm d p a (ForIn.toList [:d]).length (ForIn.toList [:d]).length s)
    (hp : p < maxPrimeEven) (hd : d ≤ hornerSteps) :
    barrett s p ((2 ^ 64 - 1) / p) = evalMod cm.toList p a := by
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at h
  exact h.barrett_eq_evalMod hp hd

/-- The exit of the loop of Horner's rule of `Ratpoints.Sieve.hornerBarrett` with reductions, for
`d > hornerSteps`, with the reduction at the end. -/
theorem HornerInvariant.barrett_eq_evalMod_of_lt {cm : Array ℕ} {d p a k s : ℕ}
    (h : HornerInvariant cm d p a (ForIn.toList [:d]).length k s ∧ k < hornerSteps)
    (hp : p < maxPrimeEven) : barrett s p ((2 ^ 64 - 1) / p) = evalMod cm.toList p a := by
  rw [Std.Legacy.Range.length_toList, Nat.sub_zero] at h
  exact h.1.barrett_eq_evalMod hp h.2.le

attribute [local irreducible] HornerInvariant in
/-- The contract of `Ratpoints.Sieve.hornerBarrett`: for a modulus `p < maxPrimeEven`, a residue
`a < p` and `d + 1` coefficients below `p`, Horner's rule with Barrett's reduction on its schedule
computes the value modulo `p` at `a` (`Ratpoints.Sieve.evalMod`); the accumulator stays below
`2 ^ 64` (`Ratpoints.Sieve.HornerInvariant.lt_two_pow_64`). -/
@[spec]
theorem hornerBarrett_spec (cm : Array ℕ) (d p a : ℕ) :
    ⦃ cm.size = d + 1 ∧ p < maxPrimeEven ∧ a < p ∧ ∀ i : ℕ, cm[i]! < p ⦄
    hornerBarrett cm d p ((2 ^ 64 - 1) / p) a
    ⦃ fun r ↦ r = evalMod cm.toList p a ⦄ := by
  vcgen [hornerBarrett] invariants
  · fun pref _ s ↦ HornerInvariant cm d p a pref.length pref.length s
  · fun pref _ s ↦ HornerInvariant cm d p a pref.length s.2 s.1 ∧ s.2 < hornerSteps
  all_goals obtain ⟨hsize, hp, ha, hcm⟩ := ‹cm.size = d + 1 ∧ _›
  all_goals first
    | exact hornerInvariant_zero hsize a (hcm d)
    | exact ⟨hornerInvariant_zero hsize a (hcm d), one_le_hornerSteps⟩
    | exact ‹HornerInvariant _ _ _ _ _ _ _›.barrett_eq_evalMod_of_le hp ‹_›
    | exact HornerInvariant.barrett_eq_evalMod_of_lt ‹_› hp
    | exact ‹HornerInvariant _ _ _ _ _ _ _›.push_self ‹_› hsize ha hcm
    | exact HornerInvariant.push_barrett ‹_› ‹_› ‹_› hsize hp ha hcm
    | exact HornerInvariant.push_lt ‹_› ‹_› ‹_› hsize ha hcm

/-! ### The table of a prime -/

@[simp]
theorem p_examinePrime (c : List ℤ) (d p : ℕ) : (examinePrime c d p).p = p := rfl

@[simp]
theorem inverses_examinePrime (c : List ℤ) (d p : ℕ) :
    (examinePrime c d p).inverses = inversesMod p := rfl

/-- The sieve entry of a prime `p ≤ 2 ^ 32` whose single factor is the table of the reference, with
the reciprocal of `p`, has the shape that the third stage needs
(`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`), whatever its fields of the packing: the inverses of
the nonzero residues are residues, and nonzero, since they are inverses. -/
theorem isPrimeEntry_examinePrime (c : List ℤ) (d : ℕ) {p : ℕ} (hp : p.Prime) (hp32 : p ≤ 2 ^ 32)
    {e : SieveEntry} (hf : e.factors = [.prime (examinePrime c d p)]) (hep : e.p = p)
    (hm : e.magic = magic p) : e.IsPrimeEntry :=
  ⟨examinePrime c d p, hf, hep, hm, hp.one_lt, hp32, fun r hr hr0 ↦
    ⟨fun h ↦ absurd (getElem!_inversesMod_mul_mod hp hr hr0) (by simp_all),
      getElem!_inversesMod_lt hr⟩⟩

theorem getElem!_isFSquare_examinePrime (c : List ℤ) (d : ℕ) {p t : ℕ} (ht : t < p) :
    (examinePrime c d p).isFSquare[t]! = (squaresMod p)[evalMod
      ((List.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat) p t]! := by
  simp only [examinePrime]
  rw [getElem!_pos _ t (by simp; lia), Array.getElem_push_lt (by simpa using ht)]
  simp

@[simp]
theorem getElem!_isFSquare_examinePrime_self (c : List ℤ) (d p : ℕ) :
    (examinePrime c d p).isFSquare[p]! =
      (d % 2 == 1 || (squaresMod p)[(c.getD d 0 % (p : ℤ)).toNat]!) := by
  simpa [examinePrime, List.getD_eq_getElem?_getD] using Array.getElem!_push_eq
    (xs := (Array.range p).map fun x ↦ (squaresMod p)[evalMod
      ((List.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat) p x]!)
    (x := d % 2 == 1 || (squaresMod p)[(c.getD d 0 % (p : ℤ)).toNat]!)

/-! ### The rows let every point through -/

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
  exact isSquare_sum_mul_pow_of_sq_eq_binaryForm hb'.isUnit (div_mul_cancel₀ _ hb').symm hy

/-- The row of the denominator `b` in the table of the prime `p` admits the numerator `a` of every
point `(a, y, b)` with `gcd(a, b) = 1`; neither `b ≥ 1` nor an odd `p` is needed. -/
theorem admits_examinePrime_of_sq_eq {c : List ℤ} {p : ℕ} (hp : p.Prime) {a y : ℤ} {b : ℕ}
    (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    (examinePrime c (BruteForce.degree c) p).admits b a = true := by
  have : Fact p.Prime := ⟨hp⟩
  simp only [Entry.admits, p_examinePrime, inverses_examinePrime]
  by_cases hb : b % p = 0 <;> simp only [hb, ↓reduceIte]
  · simpa using Int.toNat_emod_ne_zero_of_gcd_eq_one hp.one_lt hab hb
  · refine getElem!_isFSquare_examinePrime_of_isSquare hp (Nat.mod_lt _ hp.pos) ?_
    rw [BruteForce.degree_eq, natCast_mul_getElem!_inversesMod_mod _ (Nat.mod_lt _ hp.pos) hb,
      ZMod.natCast_toNat_emod, ZMod.natCast_mod]
    exact isSquare_sum_mul_div_pow_of_sq_eq_binaryForm hb hy

/-! ### The table of a prime with the exit -/

/-- The path through `long`s, with the helper `mod` of the C code, and the path through GMP
integers give the same table, whatever the coefficients: the flag of the `long`s changes nothing. -/
theorem examinePrime?_eq_examinePrime?_false (c : List ℤ) (d p : ℕ) (u : Bool) :
    examinePrime? c d p u = examinePrime? c d p false := by
  simp [examinePrime?, modLong_eq_emod]

-- The coefficients of the table, reduced on the path that the flag of the `long`s chooses, are
-- those reduced by the Euclidean `%`.
private theorem map_range_toNat_ite_modLong (c : List ℤ) (d p : ℕ) (u : Bool) :
    ((Array.range (d + 1)).map fun n ↦
      (if u = true then modLong (c.getD n 0) p else c.getD n 0 % (p : ℤ)).toNat) =
      (Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat := by
  simp [modLong_eq_emod]

-- The coefficients of the table, reduced modulo `p > 0`, are below `p`.
private theorem getElem!_map_range_emod_lt (c : List ℤ) (d : ℕ) {p : ℕ} (hp : 0 < p) (i : ℕ) :
    ((Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)[i]! < p := by
  by_cases hi : i < d + 1
  · rw [Array.getElem!_map_range _ hi]
    exact Int.toNat_emod_lt _ hp
  · rwa [getElem!_neg _ i (by simpa using hi)]

/-- The invariant of the loop of `Ratpoints.Sieve.examinePrime?` over the residues `1, …, k`, on the
table `t`: entry `0` and the entries of these residues, each whether the value modulo `p` of
Horner's rule (`Ratpoints.Sieve.evalMod`) on the coefficients reduced modulo `p` is a square modulo
`p`. -/
def ExaminePrimeInvariant (c : List ℤ) (d p k : ℕ) (t : Array Bool) : Prop :=
  t = (Array.range (k + 1)).map fun x ↦ (squaresMod p)[evalMod
    ((List.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat) p x]!

theorem examinePrimeInvariant_zero (c : List ℤ) (d : ℕ) {p : ℕ} (hp : 0 < p) :
    ExaminePrimeInvariant c d p 0
      #[(squaresMod p)[((Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)[0]!]!] := by
  have h0 := getElem!_map_range_emod_lt c d hp 0
  rw [Array.getElem!_map_range _ (Nat.succ_pos d)] at h0 ⊢
  rw [ExaminePrimeInvariant, ← Array.toList_inj, Array.toList_map, Array.toList_range,
    Nat.zero_add, List.range_one, List.map_singleton, List.range_succ_eq_map, List.map_cons,
    evalMod_cons_zero, Nat.mod_eq_of_lt h0]

/-- The step of the loop of `Ratpoints.Sieve.examinePrime?` at the residue `cur`, the value `s` of
Horner's rule with Barrett's reduction being that of Horner's rule reduced at every step. -/
theorem ExaminePrimeInvariant.push {c : List ℤ} {d p cur s : ℕ} {pref suff : List ℕ}
    {t : Array Bool} (hl : ForIn.toList [1:p] = pref ++ cur :: suff)
    (h : ExaminePrimeInvariant c d p pref.length t)
    (hs : s = evalMod ((Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat).toList p
      cur) :
    ExaminePrimeInvariant c d p (pref ++ [cur]).length (t.push (squaresMod p)[s]!) := by
  rw [ExaminePrimeInvariant] at h ⊢
  rw [h, hs, Array.toList_map, Array.toList_range,
    ← Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl]
  simp [Array.range_succ, Nat.add_comm 1]

/-- At the end of the loop of `Ratpoints.Sieve.examinePrime?` over the residues, for `p > 0`, the
table with the entry at infinity is that of the reference. -/
theorem ExaminePrimeInvariant.push_eq {c : List ℤ} {d p : ℕ} {t : Array Bool}
    (h : ExaminePrimeInvariant c d p (ForIn.toList [1:p]).length t) (hp : 0 < p) :
    t.push (d % 2 == 1 ||
      (squaresMod p)[((Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)[d]!]!) =
      (examinePrime c d p).isFSquare := by
  rw [ExaminePrimeInvariant, Std.Legacy.Range.length_toList, Nat.sub_add_cancel hp] at h
  rw [h, examinePrime, Array.getElem!_map_range _ (Nat.lt_succ_self d)]
  simp [List.getD_eq_getElem?_getD]

/-- The exit of `Ratpoints.Sieve.examinePrime?`: no entry of the table is true. -/
theorem ExaminePrimeInvariant.none_eq {c : List ℤ} {d p : ℕ} {t : Array Bool}
    (h : ExaminePrimeInvariant c d p (ForIn.toList [1:p]).length t) (hp : 0 < p)
    (hn : (!(t.push (d % 2 == 1 || (squaresMod p)[((Array.range (d + 1)).map fun n ↦
      (c.getD n 0 % (p : ℤ)).toNat)[d]!]!)).any id) = true) :
    none = if (examinePrime c d p).isFSquare.any id then
      some (examinePrime c d p, (Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)
    else none := by
  rw [h.push_eq hp] at hn
  exact (ite_eq_right (by simpa using hn)).symm

/-- The entry that `Ratpoints.Sieve.examinePrime?` returns when an entry of the table is true. -/
theorem ExaminePrimeInvariant.some_eq {c : List ℤ} {d p : ℕ} {t : Array Bool}
    (h : ExaminePrimeInvariant c d p (ForIn.toList [1:p]).length t) (hp : 0 < p)
    (hn : ¬(!(t.push (d % 2 == 1 || (squaresMod p)[((Array.range (d + 1)).map fun n ↦
      (c.getD n 0 % (p : ℤ)).toNat)[d]!]!)).any id) = true) :
    some ({ p, isFSquare := t.push (d % 2 == 1 || (squaresMod p)[((Array.range (d + 1)).map
      fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)[d]!]!), inverses := inversesMod p },
      (Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat) =
      if (examinePrime c d p).isFSquare.any id then
        some (examinePrime c d p, (Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)
      else none := by
  rw [h.push_eq hp] at hn ⊢
  exact (ite_eq_left (by simpa using hn)).symm

attribute [local irreducible] ExaminePrimeInvariant in
/-- The contract of `Ratpoints.Sieve.examinePrime?`: for `0 < p < maxPrimeEven`, on both paths of
the reduction of the coefficients, the table with the exit is that of the reference
`Ratpoints.Sieve.examinePrime`, handed back with the `d + 1` coefficients reduced modulo `p`, when
one of its entries is true, and none otherwise. Horner's rule with Barrett's reduction on its
schedule gives the values of Horner's rule reduced at every step
(`Ratpoints.Sieve.hornerBarrett_spec`). -/
@[spec]
theorem examinePrime?_spec (c : List ℤ) (d p : ℕ) (u : Bool) :
    ⦃ 0 < p ∧ p < maxPrimeEven ⦄ examinePrime? c d p u
    ⦃ fun r ↦ r = if (examinePrime c d p).isFSquare.any id then
        some (examinePrime c d p, (Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)
      else none ⦄ := by
  vcgen [examinePrime?] invariants
  · fun pref _ t ↦ ExaminePrimeInvariant c d p pref.length t
  all_goals try rw [map_range_toNat_ite_modLong] at *
  all_goals obtain ⟨hp0, hp⟩ := ‹0 < p ∧ p < maxPrimeEven›
  all_goals first
    | exact examinePrimeInvariant_zero c d hp0
    | exact ‹ExaminePrimeInvariant _ _ _ _ _›.push ‹_› ‹_›
    | exact ⟨by simp, hp, Std.Legacy.Range.lt_of_toList_eq_append_cons ‹_›,
        getElem!_map_range_emod_lt c d hp0⟩
    | exact ‹ExaminePrimeInvariant _ _ _ _ _›.none_eq hp0 ‹_›
    | exact ‹ExaminePrimeInvariant _ _ _ _ _›.some_eq hp0 ‹_›

theorem run_examinePrime? {c : List ℤ} {d p : ℕ} (u : Bool) (hp0 : 0 < p)
    (hp : p < maxPrimeEven) :
    Id.run (examinePrime? c d p u) = if (examinePrime c d p).isFSquare.any id then
      some (examinePrime c d p, (Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat)
    else none :=
  Std.WP.Id.of_run_eq_wp rfl _ ((examinePrime?_spec c d p u).le_wp ⟨hp0, hp⟩)

theorem eq_examinePrime_of_run_examinePrime?_eq_some {c : List ℤ} {d p : ℕ} {u : Bool}
    {e : Entry} {cm : Array ℕ} (h : Id.run (examinePrime? c d p u) = some (e, cm)) (hp0 : 0 < p)
    (hp : p < maxPrimeEven) : e = examinePrime c d p := by
  rw [run_examinePrime? u hp0 hp] at h
  split at h <;> grind

theorem eq_examinePrime_of_lt_numPrimes_of_run_examinePrime?_eq_some {c : List ℤ} {d k : ℕ}
    {u : Bool} {e : Entry} {cm : Array ℕ} (hk : k < numPrimes)
    (h : Id.run (examinePrime? c d primeTable[k]! u) = some (e, cm)) :
    e = examinePrime c d primeTable[k]! :=
  eq_examinePrime_of_run_examinePrime?_eq_some h (Nat.zero_lt_of_lt (one_lt_getElem!_primeTable hk))
    (getElem!_primeTable_lt_maxPrimeEven hk)

/-- The coefficients that the table hands back are those of `f` reduced modulo `p`. -/
theorem eq_map_range_of_run_examinePrime?_eq_some {c : List ℤ} {d p : ℕ} {u : Bool} {e : Entry}
    {cm : Array ℕ} (h : Id.run (examinePrime? c d p u) = some (e, cm)) :
    cm = (Array.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : ℤ)).toNat := by
  rw [examinePrime?_eq_examinePrime?_false] at h
  simp only [examinePrime?, Bool.false_eq_true, ↓reduceIte, Id.run_bind] at h
  split at h
  · simp at h
  · simp only [Id.run_pure, Option.some.injEq, Prod.mk.injEq] at h
    exact h.2.symm

/-- The exit of `examine_prime`, for `0 < p < maxPrimeEven`: no entry of the table of the reference
is true. -/
theorem run_examinePrime?_eq_none_iff {c : List ℤ} {d p : ℕ} {u : Bool} (hp0 : 0 < p)
    (hp : p < maxPrimeEven) :
    Id.run (examinePrime? c d p u) = none ↔ (examinePrime c d p).isFSquare.any id = false := by
  rw [run_examinePrime? u hp0 hp]
  split <;> simp_all

/-! ### The exit -/

/-- A point `(a, y, b)` with `p ∣ b`, among them the points at infinity, makes the leading
coefficient `c_d` a square modulo `p` for even `d`: since `gcd(a, b) = 1`, `p ∤ a`, and
`y ^ 2 ≡ c_d a ^ d (mod p)`. -/
theorem isSquare_getD_degree_of_sq_eq_binaryForm {c : List ℤ} {p : ℕ} [Fact p.Prime]
    {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hb : b % p = 0) (hd : degree c % 2 = 0)
    (hy : y ^ 2 = binaryForm c a b) : IsSquare (c.getD (degree c) 0 : ZMod p) := by
  have hb' : (b : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).mpr (Nat.dvd_of_mod_eq_zero hb)
  have ha : (a : ZMod p) ≠ 0 := fun h ↦
    Int.toNat_emod_ne_zero_of_gcd_eq_one (Fact.out : p.Prime).one_lt hab hb
      (by simp [Int.emod_eq_zero_of_dvd ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).mp h)])
  have h2 := congr(($hy : ZMod p))
  push_cast [binaryForm, hb', hd, Nat.add_zero] at h2
  rw [Finset.sum_range_succ, Finset.sum_eq_zero fun i hi ↦ by
    rw [zero_pow (by have := Finset.mem_range.mp hi; lia), mul_zero], zero_add, Nat.sub_self,
    pow_zero, mul_one] at h2
  rw [eq_div_of_mul_eq (pow_ne_zero _ ha) h2.symm]
  exact (IsSquare.sq (y : ZMod p)).div ((Nat.even_iff.mpr hd).isSquare_pow _)

/-- For a point `(a, y, b)` of a curve of even degree and a prime `p ∣ b`, the residue of `c_d`
modulo `p` is marked as a square (`Ratpoints.Sieve.isSquare_getD_degree_of_sq_eq_binaryForm`). -/
theorem getElem!_squaresMod_of_sq_eq {c : List ℤ} (hd : degree c % 2 = 0) {p : ℕ} (hp : p.Prime)
    {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) (hpb : p ∣ b) :
    (squaresMod p)[(c.getD (degree c) 0 % (p : ℤ)).toNat]! = true := by
  have : Fact p.Prime := ⟨hp⟩
  refine getElem!_squaresMod_of_isSquare hp (Int.toNat_emod_lt _ hp.pos) ?_
  rw [ZMod.natCast_toNat_emod]
  exact isSquare_getD_degree_of_sq_eq_binaryForm hab (Nat.mod_eq_zero_of_dvd hpb) hd hy

/-- A point `(a, y, b)` makes an entry of the table of the prime `p` true: the residue `a / b` for
`p ∤ b`, and the entry `p` at infinity for `p ∣ b`, since the degree is odd or `c_d` is a square
modulo `p` (`Ratpoints.Sieve.getElem!_squaresMod_of_sq_eq`). -/
theorem any_isFSquare_examinePrime_of_sq_eq {c : List ℤ} {p : ℕ} (hp : p.Prime) {a y : ℤ} {b : ℕ}
    (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    (examinePrime c (degree c) p).isFSquare.any id = true := by
  by_cases hb : b % p = 0
  · refine Array.any_id_eq_true_of_getElem!_eq_true (i := p) ?_
    rcases Nat.mod_two_eq_zero_or_one (degree c) with hd | hd
    · rw [getElem!_isFSquare_examinePrime_self,
        getElem!_squaresMod_of_sq_eq hd hp hab hy (Nat.dvd_of_mod_eq_zero hb), Bool.or_true]
    · simp [hd]
  · have h := admits_examinePrime_of_sq_eq hp hab hy
    simp only [Entry.admits, p_examinePrime, inverses_examinePrime, hb, ↓reduceIte] at h
    exact Array.any_id_eq_true_of_getElem!_eq_true h

/-- When the table of the prime `p < maxPrimeEven` is none, where `examine_prime` returns `-1` and
the search ends, the curve has no points of any height. -/
theorem not_isPoint_of_run_examinePrime?_eq_none {c : List ℤ} {p : ℕ} {u : Bool}
    (h : Id.run (examinePrime? c (degree c) p u) = none) (hp : p.Prime) (hpp : p < maxPrimeEven)
    (H : ℕ) (q : ℤ × ℤ × ℤ) : ¬ IsPoint c H q := by
  intro ⟨hy, hg, _, _, _⟩
  obtain ⟨b, hb⟩ : ∃ b : ℕ, q.2.2 = b := ⟨q.2.2.toNat, by lia⟩
  rw [hb] at hy hg
  rw [run_examinePrime?_eq_none_iff hp.pos hpp, any_isFSquare_examinePrime_of_sq_eq hp hg hy] at h
  cases h

theorem not_isPoint_of_lt_numPrimes_of_run_examinePrime?_eq_none {c : List ℤ} {k : ℕ} {u : Bool}
    (hk : k < numPrimes) (h : Id.run (examinePrime? c (degree c) primeTable[k]! u) = none)
    (H : ℕ) (q : ℤ × ℤ × ℤ) : ¬IsPoint c H q :=
  not_isPoint_of_run_examinePrime?_eq_none h
    (prime_getElem!_primeTable (hk.trans_le numPrimes_le_size_primeTable))
    (getElem!_primeTable_lt_maxPrimeEven hk) H q

end Sieve

/-! ### The coefficients as `long`s -/

/-- A natural number is a `long` exactly when it is below `2 ^ 63`: the height bounds that
`Ratpoints.findPoints` does not refuse are those from `1` to `2 ^ 63 - 1`. -/
theorem fitsLong_natCast (n : ℕ) : fitsLong n = decide (n < 2 ^ 63) := by
  simp [fitsLong]

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

/-- The value `-f` that `jacobi1` forms from a negative `long` leading coefficient `f`, after it
replaces `LONG_MIN` by `LONG_MIN / 4` (`find_points.c:579-584`), is a `long`. The helper `mod` that
`jacobi1` then calls for `b < 2 ^ 59` (`find_points.c:585`) keeps its values in the range of a
`long` (`Ratpoints.fitsLong_sixteen_mul`, `Ratpoints.fitsLong_neg`,
`Ratpoints.fitsLong_add_sixteen_mul`), and the other values of `jacobi1` and `jacobi` lie between
`0` and the larger of `b` and `|f|`. -/
theorem fitsLong_neg_ite_div_four {f : ℤ} (hf : fitsLong f = true) :
    fitsLong (-(if f = -2 ^ 63 then f / 4 else f)) = true := by
  grind [fitsLong]

/-- The inputs of the helper `mod` of the C code on the path through `long`s of the table of a
prime, the coefficients `c₀, …, c_d`, are `long`s: `use_c_long` holds only when each of them is. -/
theorem Setup.fitsLong_getD_of_useCLong {c : List ℤ} {d n : ℕ} (h : useCLong c d = true)
    (hn : n ≤ d) : fitsLong (c.getD n 0) = true :=
  List.all_eq_true.mp h n (List.mem_range.mpr (Nat.lt_succ_of_le hn))

end Ratpoints

end
