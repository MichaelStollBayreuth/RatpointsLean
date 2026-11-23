/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.List.Forall2
public import Mathlib.Data.ZMod.Basic
public import Ratpoints.Proof.Stages

import Ratpoints.Mathlib.Data.ZMod.Basic
import Ratpoints.Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Jacobi

/-!
# The modular test before the exact check loses no point

A search whose exact check is costly tests each numerator that reaches the check modulo sixteen
large primes first (`Ratpoints.Sieve.passesTest`), and checks exactly, by Horner's rule with a
running power of the denominator (`Ratpoints.Sieve.homHorner`), only a numerator that passes the
test. A numerator whose value is a square passes the test, whatever the moduli are, as long as none
is `0`, and both of Horner's rules give the same value, so that the exact check of such a search
delivers the points of the check without the test.

## Main statements

* `Ratpoints.Sieve.homHorner_eq_horner`: Horner's rule with a running power of the denominator
  gives the value of Horner's rule on the products of the coefficients with its powers.
* `Ratpoints.Sieve.natCast_formMod`: the value that the test computes modulo `q` from residues is
  the residue of the value that the exact check tests for a square.
* `Ratpoints.Sieve.run_passesTest_of_sq_eq`: a numerator whose value is a square passes the test.
* `Ratpoints.CheckFlags.TestFor`, `Ratpoints.CheckFlags.testFor_modTest`: the flags of a run hold
  what the test reads for the polynomial searched.
* `Ratpoints.CheckFlags.TestFor.hasSoundTest`: with such flags, the points that the exact check
  delivers are those of the check without the test (`Ratpoints.CheckFlags.HasSoundTest`), which is
  what the contracts of the sieve ask of the flags.

## Proof

The steps of Horner's rule modulo `q` on residues simulate the steps on the integers
(`Ratpoints.Sieve.natCast_fst_foldl_modStep`), so that the value of the test is the cast to
`ZMod q` of the value of the check; the binary algorithm gives the Jacobi symbol of that residue
over a divisor of `q` (`Ratpoints.Sieve.run_jacobi`), and the symbol of a residue of a square is not
`-1` (`jacobiSym.sq_left_nonneg`).
-/

@[expose] public section

open Ratpoints.BruteForce (scaledCoeffs)

namespace Ratpoints

namespace Sieve

/-! ### Horner's rule with a running power of the denominator -/

theorem foldl_homStep (a b : ℤ) (cs : List ℤ) (v p : ℤ) :
    cs.foldl (homStep a b) (v, p) =
      (v * a ^ cs.length + ∑ i ∈ Finset.range cs.length,
        cs.getD i 0 * (p * b ^ (i + 1)) * a ^ (cs.length - 1 - i), p * b ^ cs.length) := by
  induction cs generalizing v p with
  | nil => simp
  | cons x cs ih =>
    rw [List.foldl_cons, homStep, ih, List.length_cons, Finset.sum_range_succ']
    refine Prod.ext ?_ (by ring)
    simp only [List.getD_cons_succ, List.getD_cons_zero, Nat.add_sub_cancel, Nat.sub_zero]
    rw [Finset.sum_congr rfl fun i hi ↦ show cs.getD i 0 * (p * b * b ^ (i + 1)) *
      a ^ (cs.length - 1 - i) = cs.getD i 0 * (p * b ^ (i + 1 + 1)) * a ^ (cs.length - (i + 1))
      by rw [Nat.sub_sub, Nat.add_comm 1 i]; ring]
    ring

theorem homHorner_eq_sum (c : List ℤ) (d : ℕ) (a b : ℤ) :
    homHorner c d a b = ∑ k ∈ Finset.range (d + 1), c.getD k 0 * b ^ (d - k) * a ^ k := by
  rw [homHorner, foldl_homStep, List.length_map, List.length_reverse, List.length_range,
    Finset.sum_range_succ, Nat.sub_self, pow_zero, mul_one, add_comm, ← Finset.sum_range_reflect]
  refine congr($(Finset.sum_congr rfl fun k hk ↦ ?_) + _)
  have hk := Finset.mem_range.mp hk
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_reverse (by simpa using by lia),
    List.length_range, List.getElem?_range (by lia)]
  simp only [Option.map_some, Option.getD_some, one_mul]
  congr 2 <;> congr 1 <;> lia

/-- Horner's rule with a running power of the denominator gives the value of Horner's rule on the
products of the coefficients with the powers of the denominator: both are
`∑ cₖ a ^ k b ^ (d - k)`. -/
theorem homHorner_eq_horner (c : List ℤ) (d : ℕ) (a b : ℤ) :
    homHorner c d a b = BruteForce.horner (scaledCoeffs c d b) a :=
  (homHorner_eq_sum c d a b).trans (BruteForce.horner_scaledCoeffs c d a b).symm

/-! ### The value of the binary form modulo a modulus of the test -/

theorem natCast_fst_modStep (q a b : ℕ) (s : ℕ × ℕ) (ck : ℕ) :
    ((modStep q a b s ck).1 : ZMod q) = s.1 * a + ck * (s.2 * b) := by
  simp [modStep, ZMod.natCast_mod]

theorem natCast_snd_modStep (q a b : ℕ) (s : ℕ × ℕ) (ck : ℕ) :
    ((modStep q a b s ck).2 : ZMod q) = s.2 * b := by
  simp [modStep, ZMod.natCast_mod]

/-- The residues simulate the integers: the steps of Horner's rule modulo `q` on residues of the
coefficients, of `a` and of `b` give a residue of what the steps on the integers give. -/
theorem natCast_fst_foldl_modStep {q : ℕ} {a b : ℤ} {a' b' : ℕ} (ha : (a' : ZMod q) = a)
    (hb : (b' : ZMod q) = b) {cs : List ℤ} {cs' : List ℕ}
    (hcs : List.Forall₂ (fun (x' : ℕ) (x : ℤ) ↦ (x' : ZMod q) = x) cs' cs) {s : ℤ × ℤ}
    {s' : ℕ × ℕ} (h1 : (s'.1 : ZMod q) = s.1) (h2 : (s'.2 : ZMod q) = s.2) :
    ((cs'.foldl (modStep q a' b') s').1 : ZMod q) = (cs.foldl (homStep a b) s).1 := by
  induction hcs generalizing s s' with
  | nil => exact h1
  | cons hx _ ih =>
    refine ih ?_ ?_
    · simp [natCast_fst_modStep, homStep, h1, h2, ha, hb, hx]
    · simp [natCast_snd_modStep, homStep, h2, hb]

/-- The residue modulo `q` of the coefficient `c_k`, for `k ≤ d`, in the list of the residues of
`c₀, …, c_d` that the modular test reads (`Ratpoints.Sieve.testResidues`). -/
theorem natCast_getD_map_range (c : List ℤ) (q : ℕ) [NeZero q] {d k : ℕ} (hk : k ≤ d) :
    ((((List.range (d + 1)).map fun k ↦ (c.getD k 0 % q).toNat).getD k 0 : ℕ) : ZMod q) =
      c.getD k 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_range (Nat.lt_succ_of_le hk),
    ZMod.natCast_toNat_emod]

/-- The value of `Ratpoints.Sieve.formMod` on the residues of the coefficients `c₀, …, c_d`, of `a`
and of `b` modulo `q` is the residue of the value that the exact check tests for a square: that of
Horner's rule with a running power of `b`, times `b` for odd `d`. -/
theorem natCast_formMod {q : ℕ} [NeZero q] (c : List ℤ) (d : ℕ) {a b : ℤ} {a' b' : ℕ}
    (ha : (a' : ZMod q) = a) (hb : (b' : ZMod q) = b) :
    (formMod ((List.range (d + 1)).map fun k ↦ (c.getD k 0 % q).toNat) d q a' b' : ZMod q) =
      (homHorner c d a b * if d % 2 = 1 then b else 1 : ℤ) := by
  have h := natCast_fst_foldl_modStep ha hb (cs := (List.range d).reverse.map (c.getD · 0))
    (cs' := (List.range d).reverse.map
      (((List.range (d + 1)).map fun k ↦ (c.getD k 0 % q).toNat).getD · 0))
    (s := (c.getD d 0, 1))
    (s' := (((List.range (d + 1)).map fun k ↦ (c.getD k 0 % q).toNat).getD d 0, 1))
    (List.forall₂_map_left_iff.mpr <| List.forall₂_map_right_iff.mpr <| List.forall₂_same.mpr
      fun k hk ↦ natCast_getD_map_range c q (List.mem_range.mp (List.mem_reverse.mp hk)).le)
    (natCast_getD_map_range c q le_rfl) (by simp)
  simp only [homHorner, formMod]
  split_ifs
  · rw [ZMod.natCast_mod, Nat.cast_mul, h, hb, Int.cast_mul]
  · rw [h, mul_one]

/-! ### The test loses no point -/

/-- For a numerator `a` over `b` whose value, that of Horner's rule with a running power of `b`
times `b` for odd `d`, is a square, the modular test admits it at every modulus `q ≠ 0` with the
residues of the coefficients: the binary algorithm gives a Jacobi symbol of a residue of a square,
which is not `-1`. -/
theorem testAdmits_of_sq_eq {q : ℕ} (hq : q ≠ 0) {c : List ℤ} {d : ℕ} {a b y : ℤ}
    (hy : y ^ 2 = homHorner c d a b * if d % 2 = 1 then b else 1) :
    testAdmits d a b (q, (List.range (d + 1)).map fun k ↦ (c.getD k 0 % q).toNat) = true := by
  have : NeZero q := ⟨hq⟩
  rw [testAdmits, decide_eq_true_eq, run_jacobi hq, jacobiSym.mod_left' (a₂ := y ^ 2)]
  · exact jacobiSym.sq_left_nonneg y _
  · refine Int.ModEq.of_dvd (Int.natCast_dvd_natCast.mpr (Nat.coprimePart_dvd ..)) ?_
    rw [← ZMod.intCast_eq_intCast_iff, hy, Int.cast_natCast,
      natCast_formMod c d (ZMod.natCast_toNat_emod a) (ZMod.natCast_toNat_emod b)]

/-- **Soundness of the modular test.** A numerator whose value is a square passes the test with the
residues of the coefficients of the polynomial, so that the test rejects no numerator of a point. -/
theorem run_passesTest_of_sq_eq {c : List ℤ} {d : ℕ} {a b y : ℤ}
    (hy : y ^ 2 = homHorner c d a b * if d % 2 = 1 then b else 1) :
    Id.run (passesTest ⟨c, testResidues c d⟩ d a b) = true := by
  rw [run_passesTest, List.all_eq_true, testResidues, ← List.map_prod_left_eq_zip]
  intro qc hqc
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hqc
  exact testAdmits_of_sq_eq (testModuli_pos q hq).ne' hy

/-! ### The points of the check with the test -/

/-- The flags `fl` hold, when they hold something for the modular test before the exact check, what
the test reads for the polynomial of degree `d` with the coefficient list `c`: the coefficients with
their residues modulo the moduli of the test (`Ratpoints.Sieve.testResidues`), as the sieving of a
search puts it there (`Ratpoints.Sieve.modTest`). -/
def _root_.Ratpoints.CheckFlags.TestFor (fl : CheckFlags) (c : List ℤ) (d : ℕ) : Prop :=
  ∀ t ∈ fl.test, t = ⟨c, testResidues c d⟩

theorem _root_.Ratpoints.CheckFlags.testFor_modTest (fl : CheckFlags) (modular : Bool)
    (c : List ℤ) (d : ℕ) : CheckFlags.TestFor { fl with test := modTest modular c d } c d := by
  cases modular <;> simp [CheckFlags.TestFor, modTest]

/-- When the flags hold what the modular test reads for the coefficients `c` and the degree `d`, the
points that the exact check delivers on the products of these coefficients with the powers of a
denominator `b` are those of the check without the test: a numerator that the test rejects has no
points, and Horner's rule with a running power of `b` gives the value of Horner's rule on the
products. -/
theorem _root_.Ratpoints.CheckFlags.TestFor.hasSoundTest {c : List ℤ} {d : ℕ} {fl : CheckFlags}
    (ht : fl.TestFor c d) : fl.HasSoundTest c d := by
  intro b a
  cases h : fl.test with
  | none => simp [checkedList, h]
  | some t =>
    obtain rfl := ht t h
    by_cases hp : (!fl.noCheck && !Id.run (passesTest ⟨c, testResidues c d⟩ d a b)) = true
    · simp only [checkedList, h, hp, ↓reduceIte]
      simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hp
      simp only [checkPointList, hp.1, Bool.false_eq_true, ↓reduceIte]
      rw [BruteForce.pointsAbove_eq_nil fun y hy ↦ ?_, List.filter_nil, List.map_nil]
      rw [← homHorner_eq_horner] at hy
      exact Bool.false_ne_true (hp.2.symm.trans (run_passesTest_of_sq_eq hy))
    · simp [checkedList, h, hp, checkPointList, BruteForce.horner_singleton, homHorner_eq_horner]

end Sieve

end Ratpoints

end
