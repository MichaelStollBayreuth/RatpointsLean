/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Int.ModEq
public import Ratpoints.Fast.Sieve
public import Ratpoints.Spec.Basic
public import Ratpoints.Spec.Region

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Divisors

/-!
# The fast search finds exactly the points

`Ratpoints.Fast.fastPoints c H bLow bHigh tu` lists the normalized points of height at most `H`
on `y ^ 2 = F(x, z)` whose denominator is `0` or lies in the range of `bLow` and `bHigh`, each
once, for every setting `tu` of its parameters (`Ratpoints.Fast.mem_fastPoints_iff`,
`Ratpoints.Fast.nodup_fastPoints`).

The sieve is a sound filter: a point `(a, y, b)` makes `(a, b)` a candidate
(`Ratpoints.Fast.IsCandidate`), and the residues of a candidate modulo every `m` pass the table
`Ratpoints.Fast.admitTable` (`Ratpoints.Fast.admitTable_spec`), so the bit of `a` survives in the
row of every family (`Ratpoints.Fast.Family.IsSound`, `Ratpoints.Fast.mkFamily_isSound`), in that
row shifted to the start of each chunk (`Ratpoints.Fast.Family.IsSound.testBit_shiftRight`) and in
the sieve (`Ratpoints.Fast.testBit_sieve`); `Ratpoints.Fast.setBits` lists the bits that survive
(`Ratpoints.Fast.mem_setBits`), and the exact check of `Ratpoints.BruteForce.pointsOfDen` keeps the
points among them. The slots, the chunks of the classes modulo `G`, cover each numerator once
(`Ratpoints.Fast.exists_mem_slots`, `Ratpoints.Fast.pairwise_slots`), so the search lists the
points of its denominators, each once (`Ratpoints.Fast.mem_search`, `Ratpoints.Fast.nodup_search`),
and for odd degree the denominators that the search leaves out carry no point
(`Ratpoints.Fast.mem_denominators_of_isCandidate`, from
`Ratpoints.exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd`).

## Main statements

* `Ratpoints.Fast.mem_fastPoints_iff`: the list holds exactly the points of the region.
* `Ratpoints.Fast.nodup_fastPoints`: each of them once.
-/

@[expose] public section

namespace Ratpoints.Fast

open BruteForce

/-! ### The positions of the bits -/

/-- The bits of a positive number are its highest bit, at `Nat.log2 n`, and the bits of the
rest. -/
theorem testBit_iff_eq_log2_or {n t : ℕ} (h : n ≠ 0) :
    n.testBit t ↔ t = n.log2 ∨ (n - 2 ^ n.log2).testBit t := by
  have h1 : 2 ^ n.log2 ≤ n := Nat.log2_self_le h
  have h2 : n < 2 ^ (n.log2 + 1) := Nat.lt_log2_self
  generalize n.log2 = j at h1 h2
  obtain ⟨r, rfl⟩ : ∃ r, n = 2 ^ j + r := ⟨n - 2 ^ j, by lia⟩
  have hr : r < 2 ^ j := by rw [pow_succ] at h2; lia
  rw [Nat.add_sub_cancel_left]
  rcases lt_trichotomy t j with htj | rfl | htj
  · simp [Nat.testBit_two_pow_add_gt htj, htj.ne]
  · simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hr]
  · have : 2 ^ j + r < 2 ^ t := by
      calc 2 ^ j + r < 2 ^ (j + 1) := by rw [pow_succ]; lia
        _ ≤ 2 ^ t := Nat.pow_le_pow_right two_pos htj
    simp [Nat.testBit_lt_two_pow this, htj.ne',
      Nat.testBit_lt_two_pow (hr.trans (Nat.pow_lt_pow_right one_lt_two htj))]

theorem mem_setBitsSmall {n t : ℕ} : t ∈ setBitsSmall n ↔ n.testBit t := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [setBitsSmall]
    split_ifs with h
    · simp [h]
    · rw [List.mem_cons, ih _ (Nat.sub_lt (Nat.pos_of_ne_zero h) (Nat.two_pow_pos _)),
        testBit_iff_eq_log2_or h]

theorem nodup_setBitsSmall (n : ℕ) : (setBitsSmall n).Nodup := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rw [setBitsSmall]
    split_ifs with h
    · exact List.nodup_nil
    · refine List.nodup_cons.mpr ⟨fun hm ↦ ?_, ih _ (Nat.sub_lt (Nat.pos_of_ne_zero h)
        (Nat.two_pow_pos _))⟩
      rw [mem_setBitsSmall, Nat.testBit_lt_two_pow] at hm
      · exact Bool.false_ne_true hm
      · have := Nat.lt_log2_self (n := n)
        rw [pow_succ] at this
        lia

theorem or_testBit_iff {o h n t : ℕ} :
    (o + h ≤ t ∧ n.testBit (h + (t - (o + h))) = true) ∨
      (o ≤ t ∧ t - o < h ∧ n.testBit (t - o) = true) ↔ o ≤ t ∧ n.testBit (t - o) = true := by
  constructor
  · rintro (⟨ho, hb⟩ | ⟨ho, -, hb⟩)
    · exact ⟨by lia, by rwa [show h + (t - (o + h)) = t - o by lia] at hb⟩
    · exact ⟨ho, hb⟩
  · intro ⟨ho, hb⟩
    by_cases ht : t - o < h
    · exact .inr ⟨ho, ht, hb⟩
    · exact .inl ⟨by lia, by rwa [show h + (t - (o + h)) = t - o by lia]⟩

theorem mem_setBitsAux {o n k t : ℕ} : t ∈ setBitsAux o n k ↔ o ≤ t ∧ n.testBit (t - o) := by
  induction k generalizing o n with
  | zero =>
    simp only [setBitsAux, List.mem_map, mem_setBitsSmall]
    constructor
    · rintro ⟨s, hs, rfl⟩
      simpa using hs
    · intro ⟨ho, hb⟩
      exact ⟨t - o, hb, by lia⟩
  | succ k ih =>
    rw [setBitsAux]
    split_ifs with h
    · simp [h]
    · rw [List.mem_append, ih, ih, Nat.testBit_shiftRight, Nat.testBit_mod_two_pow]
      simp only [Bool.and_eq_true, decide_eq_true_eq]
      exact or_testBit_iff

theorem nodup_setBitsAux (o n k : ℕ) : (setBitsAux o n k).Nodup := by
  induction k generalizing o n with
  | zero => exact (nodup_setBitsSmall n).map fun _ _ h ↦ Nat.add_left_cancel h
  | succ k ih =>
    rw [setBitsAux]
    split_ifs
    · exact List.nodup_nil
    · refine List.nodup_append.mpr ⟨ih .., ih .., fun a ha b hb ↦ ?_⟩
      rw [mem_setBitsAux] at ha hb
      rw [Nat.testBit_mod_two_pow] at hb
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hb
      lia

theorem mem_setBits {n t : ℕ} : t ∈ setBits n ↔ n.testBit t := by
  simp [setBits, mem_setBitsAux]

theorem nodup_setBits (n : ℕ) : (setBits n).Nodup := nodup_setBitsAux ..

/-! ### The residues that allow a point -/

/-- `(a, b)` can carry a point: `gcd(a, b) = 1` and `F(a, b)` is a square. -/
def IsCandidate (c : List ℤ) (a : ℤ) (b : ℕ) : Prop :=
  Int.gcd a b = 1 ∧ ∃ y : ℤ, y ^ 2 = binaryForm c a b

theorem hornerMod_modEq {m : ℕ} {w w' : List ℤ} (hw : List.Forall₂ (Int.ModEq m) w w') {x x' : ℤ}
    (hx : x ≡ x' [ZMOD m]) : hornerMod w x m ≡ horner w' x' [ZMOD m] := by
  induction hw with
  | nil => rfl
  | cons ha _ ih =>
    simp only [hornerMod, horner, List.foldr_cons] at ih ⊢
    exact (Int.mod_modEq _ _).trans (ha.add (hx.mul ih))

theorem powMod_eq (r m e : ℕ) : powMod r m e = r ^ e % m := by
  induction e with
  | zero => rfl
  | succ e ih => rw [powMod, ih, pow_succ, Nat.mod_mul_mod]

theorem forall₂_scaledCoeffsMod (c : List ℤ) (d m r : ℕ) :
    List.Forall₂ (Int.ModEq m) (scaledCoeffsMod c d m r) (scaledCoeffs c d r) := by
  rw [scaledCoeffsMod, scaledCoeffs, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun k _ ↦ (Int.mod_modEq _ _).mul ?_
  rw [powMod_eq]
  push_cast [Int.natCast_mod]
  exact Int.mod_modEq _ _

theorem hornerMod_scaledCoeffsMod_modEq (c : List ℤ) (m r x : ℕ) :
    hornerMod (scaledCoeffsMod c (BruteForce.degree c) m r) x m *
      (if BruteForce.degree c % 2 = 1 then (r : ℤ) else 1) ≡ binaryForm c x r [ZMOD m] := by
  rw [← horner_scaledCoeffs_mul]
  exact (hornerMod_modEq (forall₂_scaledCoeffsMod c _ m r) (Int.ModEq.refl _)).mul_right _

theorem binaryForm_modEq (c : List ℤ) {m : ℕ} {a a' b b' : ℤ} (ha : a ≡ a' [ZMOD m])
    (hb : b ≡ b' [ZMOD m]) : binaryForm c a b ≡ binaryForm c a' b' [ZMOD m] := by
  rw [← ZMod.intCast_eq_intCast_iff] at ha hb ⊢
  simp only [binaryForm]
  push_cast
  rw [ha, hb]

/-- The binary form is homogeneous of degree `D = d + d % 2`. -/
theorem binaryForm_mul_self (c : List ℤ) (u b : ℤ) :
    binaryForm c (u * b) b = b ^ (degree c + degree c % 2) * binaryForm c u 1 := by
  simp only [binaryForm, one_pow, mul_one, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i hi ↦ ?_
  have : i ≤ degree c + degree c % 2 := by have := Finset.mem_range.mp hi; lia
  calc c.getD i 0 * (u * b) ^ i * b ^ (degree c + degree c % 2 - i)
      = c.getD i 0 * u ^ i * (b ^ i * b ^ (degree c + degree c % 2 - i)) := by ring
    _ = b ^ (degree c + degree c % 2) * (c.getD i 0 * u ^ i) := by
      rw [← pow_add, Nat.add_sub_cancel' this]
      ring

theorem sqTable_sq {m : ℕ} (hm : 0 < m) (y : ℤ) : (sqTable m)[(y ^ 2 % m).toNat]! = true := by
  have hm' : (0 : ℤ) < m := Int.natCast_pos.mpr hm
  have hy : (y % m).toNat < m := by have := Int.emod_lt_of_pos y hm'; lia
  have heq : (y % m).toNat * (y % m).toNat % m = (y ^ 2 % m).toNat := by
    rw [← Int.natCast_inj]
    push_cast [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne'), Int.natCast_mod]
    rw [← Int.mul_emod, sq]
  refine Array.getElem!_foldl_set!_eq_true _ _ (by simpa [← heq] using Nat.mod_lt _ hm)
    (.inr ⟨_, List.mem_range.mpr hy, heq⟩)

theorem coprimeWith_of_gcd_eq_one {a : ℤ} {b m : ℕ} (hm : 0 < m) (hab : Int.gcd a b = 1) :
    coprimeWith (Nat.gcd (b % m) m) (a % (m : ℤ)).toNat = true := by
  simp only [coprimeWith, Bool.or_eq_true, beq_iff_eq]
  right
  set g := Nat.gcd (a % (m : ℤ)).toNat (Nat.gcd (b % m) m)
  have h1 : g ∣ (a % (m : ℤ)).toNat := Nat.gcd_dvd_left _ _
  have h2 : g ∣ b % m := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_left _ _)
  have h3 : g ∣ m := (Nat.gcd_dvd_right _ _).trans (Nat.gcd_dvd_right _ _)
  have ha : (g : ℤ) ∣ a := by
    rw [← Int.emod_add_mul_ediv a m]
    refine dvd_add ?_ (dvd_mul_of_dvd_left (Int.natCast_dvd_natCast.mpr h3) _)
    rw [← Int.toNat_of_nonneg (Int.emod_nonneg a (by lia))]
    exact Int.natCast_dvd_natCast.mpr h1
  have hb : g ∣ b := by
    rw [← Nat.mod_add_div b m]
    exact dvd_add h2 (dvd_mul_of_dvd_left h3 _)
  have := Int.dvd_gcd ha (Int.natCast_dvd_natCast.mpr hb)
  rw [hab] at this
  exact Nat.dvd_one.mp this

theorem getElem!_map_range {α : Type*} [Inhabited α] (f : ℕ → α) {n i : ℕ} (hi : i < n) :
    ((List.range n).toArray.map f)[i]! = f i := by
  simp [getElem!_pos, hi]

theorem sqTable_of_modEq {m : ℕ} (hm : 0 < m) {v y : ℤ} (h : v ≡ y ^ 2 [ZMOD m]) :
    (sqTable m)[(v % m).toNat]! = true := by
  rw [show v % m = y ^ 2 % m from h]
  exact sqTable_sq hm y

theorem getElem!_admitRow {c : List ℤ} {m r x : ℕ} (hm : 0 < m) (hx : x < m)
    (hg : coprimeWith (Nat.gcd r m) x = true) {y : ℤ} (hy : binaryForm c x r ≡ y ^ 2 [ZMOD m]) :
    (admitRow c (BruteForce.degree c) m (sqTable m) r)[x]! = true := by
  rw [admitRow, getElem!_map_range _ hx, hg, Bool.true_and]
  exact sqTable_of_modEq hm ((hornerMod_scaledCoeffsMod_modEq c m r x).trans hy)

theorem intCast_mul_modEq_one {b u m : ℕ} (h : b % m * u % m = 1 % m) :
    (b : ℤ) * u ≡ 1 [ZMOD m] := by
  have := congr(((($h : ℕ)) : ℤ))
  push_cast [Int.natCast_mod] at this
  exact ((Int.mod_modEq _ _).mul_right _).symm.trans this

/-- For `b u ≡ 1` modulo `m`, `F(x u, 1)` is a square modulo `m` for every `x ≡ a` with
`F(a, b)` a square, `F` being homogeneous of even degree (`Ratpoints.Fast.binaryForm_mul_self`). -/
theorem binaryForm_mul_modEq_sq {c : List ℤ} {m : ℕ} {a y : ℤ} {b u x : ℕ}
    (hy : y ^ 2 = binaryForm c a b) (hxa : (x : ℤ) ≡ a [ZMOD m]) (hru : b % m * u % m = 1 % m) :
    binaryForm c ((x * u % m : ℕ) : ℤ) ((1 : ℕ) : ℤ) ≡
      (y * u ^ ((degree c + degree c % 2) / 2)) ^ 2 [ZMOD m] := by
  have hD : degree c + degree c % 2 = 2 * ((degree c + degree c % 2) / 2) := by lia
  have hbu := intCast_mul_modEq_one hru
  have hv : ((x * u % m : ℕ) : ℤ) * b ≡ a [ZMOD m] := by
    push_cast [Int.natCast_mod]
    calc (x * u % m : ℤ) * b ≡ x * u * b [ZMOD m] := (Int.mod_modEq _ _).mul_right _
      _ = x * (b * u) := by ring
      _ ≡ x * 1 [ZMOD m] := hbu.mul_left _
      _ = x := mul_one _
      _ ≡ a [ZMOD m] := hxa
  calc binaryForm c ((x * u % m : ℕ) : ℤ) ((1 : ℕ) : ℤ)
      ≡ binaryForm c ((x * u % m : ℕ) : ℤ) 1 * (b * u) ^ (degree c + degree c % 2) [ZMOD m] := by
        simpa using ((hbu.pow (degree c + degree c % 2)).mul_left _).symm
    _ = binaryForm c (((x * u % m : ℕ) : ℤ) * b) b * u ^ (degree c + degree c % 2) := by
        rw [binaryForm_mul_self]
        ring
    _ ≡ binaryForm c a b * u ^ (degree c + degree c % 2) [ZMOD m] :=
        (binaryForm_modEq c hv (Int.ModEq.refl _)).mul_right _
    _ = (y * u ^ ((degree c + degree c % 2) / 2)) ^ 2 := by
        rw [← hy, mul_pow, ← pow_mul, mul_comm _ 2, ← hD]

theorem admitTable_spec {c : List ℤ} {m : ℕ} (hm : 0 < m) {a : ℤ} {b : ℕ}
    (h : IsCandidate c a b) :
    ((admitTable c (BruteForce.degree c) m)[b % m]!)[(a % (m : ℤ)).toNat]! = true := by
  obtain ⟨hab, y, hy⟩ := h
  have hm' : (0 : ℤ) < m := Int.natCast_pos.mpr hm
  have hx : (a % (m : ℤ)).toNat < m := by have := Int.emod_lt_of_pos a hm'; lia
  have hxa : ((a % (m : ℤ)).toNat : ℤ) ≡ a [ZMOD m] := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hm'.ne')]
    exact Int.mod_modEq a m
  rw [admitTable, Array.getElem!_ofFn _ (Nat.mod_lt _ hm)]
  dsimp only
  split_ifs with hu
  · rw [Array.getElem!_ofFn _ hx]
    exact getElem!_admitRow hm (Nat.mod_lt _ hm) (by simp [coprimeWith])
      (binaryForm_mul_modEq_sq hy hxa (by simpa using hu))
  · refine getElem!_admitRow (y := y) hm hx (coprimeWith_of_gcd_eq_one hm hab) ?_
    refine (binaryForm_modEq c hxa ?_).trans (by rw [hy])
    push_cast [Int.natCast_mod]
    exact Int.mod_modEq _ _

/-! ### Bit masks -/

theorem testBit_foldl_pattern (f : ℕ → Bool) (l : List ℕ) (P j : ℕ) :
    (l.foldl (fun P j' ↦ if f j' then P ||| 1 <<< j' else P) P).testBit j =
      (P.testBit j || decide (j ∈ l) && f j) := by
  induction l generalizing P with
  | nil => simp
  | cons j' l ih =>
    rw [List.foldl_cons, ih]
    by_cases hf : f j' <;> by_cases hj : j = j' <;>
      simp [hf, hj, Nat.testBit_or, Nat.one_shiftLeft, eq_comm]

theorem testBit_pattern (m : ℕ) (f : ℕ → Bool) (j : ℕ) :
    (pattern m f).testBit j = (decide (j < m) && f j) := by
  simp [pattern, testBit_foldl_pattern]

theorem testBit_repeatPattern {P m j : ℕ} (k : ℕ) (hj : j < m * 2 ^ k)
    (h : P.testBit (j % m) = true) : (repeatPattern P m k).testBit j = true := by
  induction k generalizing j with
  | zero =>
    rw [pow_zero, mul_one] at hj
    rwa [Nat.mod_eq_of_lt hj] at h
  | succ k ih =>
    rw [repeatPattern, Nat.testBit_or, Bool.or_eq_true]
    by_cases hjk : j < m * 2 ^ k
    · exact .inl (ih hjk h)
    · refine .inr ?_
      obtain ⟨j', rfl⟩ : ∃ j', j = j' + m * 2 ^ k := ⟨j - m * 2 ^ k, by lia⟩
      rw [Nat.testBit_shiftLeft, Nat.add_sub_cancel]
      simp only [ge_iff_le, Nat.le_add_left, decide_true, Bool.true_and]
      refine ih (by rw [pow_succ] at hj; lia) ?_
      rwa [Nat.add_mul_mod_self_left] at h

theorem le_mul_two_pow_doublings {m : ℕ} (hm : 0 < m) (N : ℕ) : N < m * 2 ^ doublings m N := by
  calc N < m * (N / m + 1) := Nat.lt_mul_div_succ N hm
    _ ≤ m * 2 ^ doublings m N := Nat.mul_le_mul_left m Nat.lt_log2_self

theorem testBit_baseRow {T : Array (Array Bool)} {m G N r j : ℕ} (hm : 0 < m) (hj : j < N)
    (h : (T[r]!)[G * j % m]! = true) : (baseRow T m G N r).testBit j = true := by
  refine testBit_repeatPattern _ ((le_mul_two_pow_doublings hm N).trans' hj) ?_
  rwa [testBit_pattern, Nat.mul_mod, Nat.mod_mod, ← Nat.mul_mod, Bool.and_eq_true,
    decide_eq_true_eq, and_iff_right (Nat.mod_lt _ hm)]

/-! ### Families -/

/-- The family `F` is sound for the step `G` and chunks of at most `L` numerators: it has a row for
every residue modulo `F.M > 0`, `F.ginv` inverts `G` modulo `F.M`, and the row of `b` has the bit
`j < L + 8 F.M` set for every candidate `(a, b)` with `a ≡ G j` modulo `F.M`. -/
structure Family.IsSound (c : List ℤ) (G L : ℕ) (F : Family) : Prop where
  /-- A row for every residue. -/
  size_eq : F.rows.size = F.M
  /-- The modulus is positive. -/
  pos : 0 < F.M
  /-- `F.ginv` inverts `G`. -/
  mul_ginv : G * F.ginv % F.M = 1 % F.M
  /-- The row of `b` keeps the bit `j` of every candidate `(a, b)` with `a ≡ G j`. -/
  testBit : ∀ (a : ℤ) (b j : ℕ), j < L + 8 * F.M → IsCandidate c a b → (F.M : ℤ) ∣ a - G * j →
    (F.rows[b % F.M]!).testBit j = true

theorem foldl_mul_fst {α : Type*} (ts : List (ℕ × α)) (k : ℕ) :
    ts.foldl (· * ·.1) k = k * (ts.map (·.1)).prod := by
  induction ts generalizing k with
  | nil => simp
  | cons t ts ih => simp [ih, mul_assoc]

theorem testBit_foldl_and {α : Type*} (g : α → ℕ) (l : List α) {init j : ℕ}
    (hi : init.testBit j = true) (hl : ∀ x ∈ l, (g x).testBit j = true) :
    (l.foldl (fun acc x ↦ acc &&& g x) init).testBit j = true := by
  induction l generalizing init with
  | nil => exact hi
  | cons x l ih =>
    exact ih (by simp [Nat.testBit_and, hi, hl x (by simp)]) fun y hy ↦ hl y (by simp [hy])

theorem natMod_eq_toNat_of_dvd {m : ℕ} {a : ℤ} {k : ℕ} (h : (m : ℤ) ∣ a - k) :
    k % m = (a % (m : ℤ)).toNat := by
  have := Int.modEq_iff_dvd.mpr h
  rw [Int.ModEq] at this
  rw [← this, ← Int.natCast_mod, Int.toNat_natCast]

theorem foldl_mul_fst_pos {α : Type*} {ts : List (ℕ × α)} (h : ∀ t ∈ ts, 0 < t.1) :
    0 < ts.foldl (· * ·.1) 1 := by
  rw [foldl_mul_fst, one_mul]
  exact List.prod_pos fun x hx ↦ by
    obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hx
    exact h t ht

theorem dvd_foldl_mul_fst {α : Type*} {ts : List (ℕ × α)} {t : ℕ × α} (ht : t ∈ ts) :
    t.1 ∣ ts.foldl (· * ·.1) 1 := by
  rw [foldl_mul_fst, one_mul]
  exact List.dvd_prod (List.mem_map.mpr ⟨_, ht, rfl⟩)

/-- The rows of one modulus `m ∣ M` keep the bit `j` of every candidate `(a, b)` with
`a ≡ G j` modulo `M`. -/
theorem testBit_baseRows {c : List ℤ} {m M G N j : ℕ} (hm : 0 < m) (hmM : m ∣ M) (hj : j < N)
    {a : ℤ} {b : ℕ} (hc : IsCandidate c a b) (hdvd : (M : ℤ) ∣ a - G * j) :
    (((List.range m).toArray.map
      (baseRow (admitTable c (BruteForce.degree c) m) m G N))[b % M % m]!).testBit j = true := by
  rw [Nat.mod_mod_of_dvd _ hmM, getElem!_map_range _ (Nat.mod_lt _ hm)]
  refine testBit_baseRow hm hj ?_
  rw [natMod_eq_toNat_of_dvd (k := G * j)
    ((Int.natCast_dvd_natCast.mpr hmM).trans (by simpa using hdvd))]
  exact admitTable_spec hm hc

theorem mkFamily_isSound {c : List ℤ} {G L : ℕ} {ts : List (ℕ × Array (Array Bool))}
    (hts : ∀ t ∈ ts, t.2 = admitTable c (BruteForce.degree c) t.1) {F : Family}
    (h : mkFamily G L ts = some F) :
    F.IsSound c G L := by
  rw [mkFamily] at h
  split_ifs at h with hpos
  dsimp only at h
  split at h
  · simp at h
  rename_i ginv hginv
  obtain rfl := (Option.some.inj h).symm
  have hpos' : ∀ t ∈ ts, 0 < t.1 := by simpa using hpos
  have hM := foldl_mul_fst_pos hpos'
  refine ⟨by simp, hM, by simpa using List.find?_some hginv, fun a b j hj hc hdvd ↦ ?_⟩
  rw [getElem!_map_range _ (Nat.mod_lt _ hM)]
  refine testBit_foldl_and _ _ (by simp [Nat.testBit_two_pow_sub_one, hj]) fun x hx ↦ ?_
  obtain ⟨⟨m, T⟩, ht, rfl⟩ := List.mem_map.mp hx
  obtain rfl : T = admitTable c (BruteForce.degree c) m := hts _ ht
  exact testBit_baseRows (hpos' _ ht) (dvd_foldl_mul_fst ht) hj hc hdvd

/-! ### The shift -/

theorem Family.shift_lt (F : Family) (hF : 0 < F.M) (a₀ : ℤ) : F.shift a₀ < 8 * F.M := by
  have hs : (a₀ * F.ginv % (F.M : ℤ)).toNat < F.M := by
    lia [Int.emod_lt_of_pos (a₀ * F.ginv) (Int.natCast_pos.mpr hF)]
  simp only [Family.shift]
  generalize (a₀ * F.ginv % (F.M : ℤ)).toNat = s at hs ⊢
  have h7 : (8 - s % 8) * F.M % 8 ≤ 7 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  lia [Nat.mul_le_mul_left F.M h7]

theorem Family.IsSound.dvd_sub_shift {c : List ℤ} {G L : ℕ} {F : Family}
    (hF : F.IsSound c G L) (a₀ : ℤ) :
    (F.M : ℤ) ∣ a₀ - G * F.shift a₀ := by
  have hg : (G : ℤ) * F.ginv ≡ 1 [ZMOD F.M] := by
    have := congr((($hF.mul_ginv : ℕ) : ℤ))
    push_cast [Int.natCast_mod] at this
    exact this
  have hs : (G : ℤ) * (a₀ * F.ginv % F.M) ≡ a₀ [ZMOD F.M] :=
    calc (G : ℤ) * (a₀ * F.ginv % F.M) ≡ G * (a₀ * F.ginv) [ZMOD F.M] :=
          (Int.mod_modEq _ _).mul_left _
      _ = a₀ * (G * F.ginv) := by ring
      _ ≡ a₀ * 1 [ZMOD F.M] := hg.mul_left _
      _ = a₀ := mul_one a₀
  obtain ⟨k, hk⟩ : ∃ k, F.shift a₀ = (a₀ * F.ginv % (F.M : ℤ)).toNat + F.M * k := ⟨_, rfl⟩
  have h0 : 0 ≤ a₀ * F.ginv % (F.M : ℤ) := Int.emod_nonneg _ (by lia [hF.pos])
  rw [hk]
  push_cast [Int.toNat_of_nonneg h0]
  refine Int.modEq_iff_dvd.mp ?_
  rw [mul_add, mul_left_comm]
  exact Int.modEq_add_fac_self.trans hs

/-- The row of `b`, shifted to the chunk that starts at `a₀`, keeps the bit `t < L` of every
candidate `(a₀ + G t, b)`. -/
theorem Family.IsSound.testBit_shiftRight {c : List ℤ} {G L : ℕ} {F : Family}
    (hF : F.IsSound c G L) {a₀ : ℤ} {b t : ℕ} (ht : t < L) (hc : IsCandidate c (a₀ + G * t) b) :
    (F.rows[b % F.M]! >>> F.shift a₀).testBit t = true := by
  rw [Nat.testBit_shiftRight]
  refine hF.testBit _ b _ (by lia [F.shift_lt hF.pos a₀]) hc ?_
  have := hF.dvd_sub_shift a₀
  rwa [show a₀ + G * t - G * (F.shift a₀ + t : ℕ) = a₀ - G * F.shift a₀ by push_cast; ring]

theorem Family.IsSound.rows_ne_zero {c : List ℤ} {G L : ℕ} {F : Family} (hF : F.IsSound c G L)
    {a : ℤ} {b : ℕ} (hc : IsCandidate c a b) :
    F.rows[b % F.M]! ≠ 0 := by
  intro h0
  have := hF.testBit a b (F.shift a) (by lia [F.shift_lt hF.pos a]) hc (hF.dvd_sub_shift a)
  simp [h0] at this

/-! ### The sieve -/

theorem testBit_foldl_sieve {α : Type*} (g : α → ℕ) (l : List α) {mask t : ℕ}
    (hmask : mask.testBit t = true) (hl : ∀ x ∈ l, (g x).testBit t = true) :
    (l.foldl (fun acc x ↦ if acc == 0 then 0 else acc &&& g x) mask).testBit t = true := by
  induction l generalizing mask with
  | nil => exact hmask
  | cons x l ih =>
    refine ih ?_ fun y hy ↦ hl y (by simp [hy])
    have h0 : mask ≠ 0 := fun h ↦ by simp [h] at hmask
    simp [h0, Nat.testBit_and, hmask, hl x (by simp)]

theorem testBit_of_testBit_foldl_sieve {α : Type*} {g : α → ℕ} {l : List α} {mask t : ℕ}
    (h : (l.foldl (fun acc x ↦ if acc == 0 then 0 else acc &&& g x) mask).testBit t = true) :
    mask.testBit t = true := by
  induction l generalizing mask with
  | nil => exact h
  | cons x l ih =>
    have := ih h
    dsimp only at this
    split_ifs at this with h0
    · simp at this
    · rw [Nat.testBit_and, Bool.and_eq_true] at this
      exact this.1

theorem testBit_sieve {rs sh : Array ℕ} {mask t : ℕ} (hmask : mask.testBit t = true)
    (h : ∀ i < rs.size, (rs[i]! >>> sh[i]!).testBit t = true) :
    (sieve rs sh mask).testBit t = true :=
  testBit_foldl_sieve (fun i ↦ rs[i]! >>> sh[i]!) _ hmask fun i hi ↦ h i (List.mem_range.mp hi)

theorem testBit_of_testBit_sieve {rs sh : Array ℕ} {mask t : ℕ}
    (h : (sieve rs sh mask).testBit t = true) :
    mask.testBit t = true :=
  testBit_of_testBit_foldl_sieve h

/-! ### The points of a chunk -/

theorem of_mem_chunkPoints {c : List ℤ} {G : ℕ} {rs sh : Array ℕ} {a₀ : ℤ} {len b : ℕ}
    {p : ℤ × ℤ × ℤ} (h : p ∈ chunkPoints c (BruteForce.degree c) G rs sh a₀ len b) :
    p.2.2 = b ∧ (∃ t < len, p.1 = a₀ + G * t) ∧ Int.gcd p.1 p.2.2 = 1 ∧
      p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  simp only [chunkPoints] at h
  split_ifs at h
  · simp at h
  rw [mem_pointsOfDen_iff, horner_scaledCoeffs_mul] at h
  obtain ⟨hx, hz, hg, hy⟩ := h
  obtain ⟨t, ht, hx⟩ := List.mem_map.mp hx
  have := testBit_of_testBit_sieve (mem_setBits.mp ht)
  rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at this
  exact ⟨hz, ⟨t, this, hx.symm⟩, hz ▸ hg, hz ▸ hy⟩

theorem mem_chunkPoints {c : List ℤ} {G : ℕ} {rs sh : Array ℕ} {a₀ : ℤ} {len b : ℕ}
    (hrs : ∀ t < len, IsCandidate c (a₀ + G * t) b →
      ∀ i < rs.size, (rs[i]! >>> sh[i]!).testBit t = true) {p : ℤ × ℤ × ℤ} :
    p ∈ chunkPoints c (BruteForce.degree c) G rs sh a₀ len b ↔
      p.2.2 = b ∧ (∃ t < len, p.1 = a₀ + G * t) ∧ Int.gcd p.1 p.2.2 = 1 ∧
        p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  refine ⟨of_mem_chunkPoints, fun ⟨hz, ⟨t, ht, hx⟩, hg, hy⟩ ↦ ?_⟩
  have hbit := testBit_sieve (rs := rs) (sh := sh) (mask := 2 ^ len - 1)
    (by simp [Nat.testBit_two_pow_sub_one, ht]) (hrs t ht ⟨hx ▸ hz ▸ hg, p.2.1, hx ▸ hz ▸ hy⟩)
  have h0 : sieve rs sh (2 ^ len - 1) ≠ 0 := fun h ↦ by simp [h] at hbit
  simp only [chunkPoints, beq_iff_eq, h0, ↓reduceIte]
  rw [mem_pointsOfDen_iff, horner_scaledCoeffs_mul]
  exact ⟨List.mem_map.mpr ⟨t, mem_setBits.mpr hbit, hx.symm⟩, hz, hz ▸ hg, hz ▸ hy⟩

theorem nodup_chunkPoints (c : List ℤ) {G : ℕ} (hG : 0 < G) (rs sh : Array ℕ) (a₀ : ℤ)
    (len b : ℕ) :
    (chunkPoints c (BruteForce.degree c) G rs sh a₀ len b).Nodup := by
  simp only [chunkPoints]
  split_ifs
  · exact List.nodup_nil
  · refine nodup_pointsOfDen _ _ _ ((nodup_setBits _).map fun t t' h ↦ ?_)
    have : (G : ℤ) * t = G * t' := by simpa using h
    exact_mod_cast mul_left_cancel₀ (by lia : (G : ℤ) ≠ 0) this

/-! ### Chunks and classes -/

theorem mem_chunks_iff {cnt L t₀ len : ℕ} :
    (t₀, len) ∈ chunks cnt L ↔ ∃ k < (cnt + L - 1) / L, t₀ = k * L ∧ len = min L (cnt - k * L) := by
  simp only [chunks, List.mem_map, List.mem_range, Prod.mk.injEq]
  grind

theorem exists_mem_chunks {cnt L u : ℕ} (hL : 0 < L) (hu : u < cnt) :
    ∃ t₀ len, (t₀, len) ∈ chunks cnt L ∧ t₀ = u / L * L ∧ u % L < len := by
  refine ⟨u / L * L, min L (cnt - u / L * L), mem_chunks_iff.mpr ⟨u / L, ?_, rfl, rfl⟩, rfl, ?_⟩
  · have := Nat.div_mul_le_self u L
    exact (Nat.le_div_iff_mul_le hL).mpr (by rw [Nat.succ_mul]; lia)
  · have := Nat.mod_lt u hL
    have := Nat.div_add_mod u L
    lia

theorem le_of_mem_chunks {cnt L t₀ len : ℕ} (h : (t₀, len) ∈ chunks cnt L) :
    t₀ + len ≤ cnt ∧ len ≤ L ∧ t₀ % L = 0 := by
  obtain ⟨k, hk, rfl, rfl⟩ := mem_chunks_iff.mp h
  rcases Nat.eq_zero_or_pos L with rfl | hL
  · simp at hk
  have := (Nat.le_div_iff_mul_le hL).mp hk
  rw [Nat.succ_mul] at this
  exact ⟨by lia, by lia, Nat.mul_mod_left k L⟩

theorem add_mul_lt_of_lt_classCount {n G ρ u : ℕ} (hG : 0 < G) (h : u < classCount n G ρ) :
    ρ + G * u < n := by
  have := (Nat.le_div_iff_mul_le hG).mp h
  rw [Nat.succ_mul, mul_comm] at this
  lia

theorem lt_classCount {n G ρ u : ℕ} (hG : 0 < G) (h : ρ + G * u < n) : u < classCount n G ρ :=
  (Nat.le_div_iff_mul_le hG).mpr (by rw [Nat.succ_mul, mul_comm]; lia)

/-- The numerator `x` with `x + H = i` in the chunk of the class `i % G` that holds it. -/
theorem eq_sub_add_mul_of_natCast_eq {i G L H : ℕ} {x : ℤ} (hi : (i : ℤ) = x + H) :
    x = ((i % G + G * (i / G / L * L) : ℕ) : ℤ) - H + G * ((i / G % L : ℕ) : ℤ) := by
  have h1 : ((i % G : ℕ) : ℤ) + G * ((i / G : ℕ) : ℤ) = i := mod_cast Nat.mod_add_div i G
  have h2 : (L : ℤ) * ((i / G / L : ℕ) : ℤ) + ((i / G % L : ℕ) : ℤ) = ((i / G : ℕ) : ℤ) :=
    mod_cast Nat.div_add_mod (i / G) L
  simp only [Nat.cast_add, Nat.cast_mul]
  linear_combination (-1 : ℤ) * hi - h1 - (G : ℤ) * h2

theorem eq_of_add_mul_eq {G ρ ρ' u u' : ℕ} (hρ : ρ < G) (hρ' : ρ' < G)
    (h : ρ + G * u = ρ' + G * u') : ρ = ρ' ∧ u = u' := by
  have h1 := congrArg (· % G) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ, Nat.mod_eq_of_lt hρ'] at h1
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (n := G) (by lia) (by lia)⟩

theorem eq_of_add_mul_add_eq {G L ρ k k' t t' : ℕ} (hG : 0 < G) (hL : 0 < L) (ht : t < L)
    (ht' : t' < L) (h : ρ + G * (k * L + t) = ρ + G * (k' * L + t')) : k = k' := by
  have := congrArg (· / L) (Nat.eq_of_mul_eq_mul_left hG (Nat.add_left_cancel h))
  simpa [Nat.mul_comm k L, Nat.mul_comm k' L, Nat.mul_add_div hL, Nat.div_eq_of_lt ht,
    Nat.div_eq_of_lt ht'] using this

/-! ### The slots -/

theorem le_of_mem_slots {H G L r len : ℕ} {a₀ : ℤ} (h : (r, a₀, len) ∈ slots H G L) : len ≤ L := by
  simp only [slots, List.mem_flatMap, List.mem_range, List.mem_map, Prod.exists,
    Prod.mk.injEq] at h
  obtain ⟨_, -, _, _, hch, -, -, rfl⟩ := h
  exact (le_of_mem_chunks hch).2.1

theorem abs_add_mul_le_of_mem_slots {H G L r len : ℕ} {a₀ : ℤ} (hG : 0 < G)
    (h : (r, a₀, len) ∈ slots H G L) {t : ℕ} (ht : t < len) :
    |a₀ + G * t| ≤ H := by
  simp only [slots, List.mem_flatMap, List.mem_range, List.mem_map, Prod.exists,
    Prod.mk.injEq] at h
  obtain ⟨ρ, -, t₀, _, hch, -, rfl, rfl⟩ := h
  have := add_mul_lt_of_lt_classCount (n := 2 * H + 1) (ρ := ρ) (u := t₀ + t) hG
    (by lia [(le_of_mem_chunks hch).1])
  rw [abs_le]
  push_cast
  constructor <;> lia

/-- Every numerator `x` with `|x| ≤ H` lies in a slot, with the residue of `x` modulo `G`. -/
theorem exists_mem_slots {H G L : ℕ} (hG : 0 < G) (hL : 0 < L) {x : ℤ} (hx : |x| ≤ H) :
    ∃ a₀ len, ((x % G).toNat, a₀, len) ∈ slots H G L ∧ ∃ t < len, x = a₀ + G * t := by
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = x + H := ⟨(x + H).toNat, by rw [abs_le] at hx; lia⟩
  have hu : i / G < classCount (2 * H + 1) G (i % G) :=
    lt_classCount hG (by rw [abs_le] at hx; lia [Nat.mod_add_div i G])
  obtain ⟨t₀, len, hch, rfl, hlen⟩ := exists_mem_chunks hL hu
  refine ⟨_, len, ?_, i / G % L, hlen, eq_sub_add_mul_of_natCast_eq hi⟩
  simp only [slots, List.mem_flatMap, List.mem_range, List.mem_map, Prod.exists, Prod.mk.injEq]
  refine ⟨i % G, Nat.mod_lt _ hG, _, len, hch, ?_, rfl, rfl⟩
  have := (Int.mod_modEq (i : ℤ) G).sub_right (H : ℤ)
  rw [show (i : ℤ) - H = x by lia] at this
  push_cast [Int.natCast_mod]
  rw [this]

/-- Two slots have no numerator in common. -/
theorem pairwise_slots (H : ℕ) {G L : ℕ} (hG : 0 < G) (hL : 0 < L) :
    (slots H G L).Pairwise fun (s s' : ℕ × ℤ × ℕ) ↦
      ∀ t < s.2.2, ∀ t' < s'.2.2, s.2.1 + G * t ≠ s'.2.1 + G * t' := by
  rw [slots, List.pairwise_flatMap]
  refine ⟨fun ρ _ ↦ ?_, List.nodup_range.pairwise_of_forall_ne
    fun ρ hρ ρ' hρ' hne s hs s' hs' t _ t' _ h ↦ hne ?_⟩
  · rw [chunks, List.map_map, List.pairwise_map]
    refine List.nodup_range.pairwise_of_forall_ne fun k _ k' _ hne t ht t' ht' h ↦ hne ?_
    dsimp only [Function.comp_apply] at ht ht' h
    exact eq_of_add_mul_add_eq (ρ := ρ) hG hL (ht.trans_le (min_le_left _ _))
      (ht'.trans_le (min_le_left _ _)) (by lia)
  · simp only [List.mem_map, Prod.exists] at hs hs'
    obtain ⟨t₀, len, -, rfl⟩ := hs
    obtain ⟨t₀', len', -, rfl⟩ := hs'
    exact (eq_of_add_mul_eq (u := t₀ + t) (u' := t₀' + t') (List.mem_range.mp hρ)
      (List.mem_range.mp hρ') (by lia)).1

/-! ### The search -/

theorem of_mem_search {c : List ℤ} {H G L : ℕ} {fams : Array Family} {dens : List ℕ}
    (hG : 0 < G) {p : ℤ × ℤ × ℤ} (h : p ∈ search c (BruteForce.degree c) H G L fams dens) :
    (∃ b ∈ dens, p.2.2 = b) ∧ |p.1| ≤ H ∧ Int.gcd p.1 p.2.2 = 1 ∧
      p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  simp only [search, List.mem_flatMap, getElem!_map_range _ (Nat.mod_lt _ hG), List.mem_filter,
    List.mem_map, Prod.exists, Prod.mk.injEq] at h
  obtain ⟨b, ⟨hb, -⟩, _, _, _, _, ⟨⟨r, a₀, len, hs, rfl, rfl, rfl, rfl⟩, -⟩, hp⟩ := h
  obtain ⟨hz, ⟨t, ht, hx⟩, hg, hy⟩ := of_mem_chunkPoints hp
  exact ⟨⟨b, hb, hz⟩, hx ▸ abs_add_mul_le_of_mem_slots hG hs ht, hg, hy⟩

theorem mem_search_of {c : List ℤ} {H G L : ℕ} {fams : Array Family} {dens : List ℕ}
    (hG : 0 < G) (hL : 0 < L) (hfams : ∀ F ∈ fams, F.IsSound c G L) {p : ℤ × ℤ × ℤ} {b : ℕ}
    (hb : b ∈ dens) (hz : p.2.2 = b) (ha : |p.1| ≤ H) (hg : Int.gcd p.1 p.2.2 = 1)
    (hy : p.2.1 ^ 2 = binaryForm c p.1 p.2.2) :
    p ∈ search c (BruteForce.degree c) H G L fams dens := by
  have hc : IsCandidate c p.1 b := ⟨hz ▸ hg, p.2.1, hz ▸ hy⟩
  have hF (F) (h : F ∈ fams.filter fun F ↦ F.rows.size == F.M && 0 < F.M) : F.IsSound c G L :=
    hfams F (Array.mem_filter.mp h).1
  obtain ⟨a₀, len, hs, t, ht, hx⟩ := exists_mem_slots hG hL ha
  simp only [search, List.mem_flatMap, getElem!_map_range _ (Nat.mod_lt _ hG), List.mem_filter,
    List.mem_map, Prod.exists, Array.all_eq_true_iff_forall_mem, bne_iff_ne]
  refine ⟨b, ⟨hb, fun F hF' ↦ (hF F hF').rows_ne_zero hc⟩, _, a₀, len, _,
    ⟨⟨_, a₀, len, hs, rfl⟩, by simpa using admitTable_spec hG hc⟩,
    (mem_chunkPoints fun t' ht' hc' i hi ↦ ?_).mpr ⟨hz, ⟨t, ht, hx⟩, hg, hy⟩⟩
  simp only [Array.size_map] at hi
  simp only [getElem!_pos, Array.size_map, hi, Array.getElem_map]
  exact (hF _ (Array.getElem_mem hi)).testBit_shiftRight
    (ht'.trans_le (le_of_mem_slots hs)) hc'

theorem mem_search {c : List ℤ} {H G L : ℕ} {fams : Array Family} {dens : List ℕ}
    (hG : 0 < G) (hL : 0 < L) (hfams : ∀ F ∈ fams, F.IsSound c G L) {p : ℤ × ℤ × ℤ} :
    p ∈ search c (BruteForce.degree c) H G L fams dens ↔
      (∃ b ∈ dens, p.2.2 = b) ∧ |p.1| ≤ H ∧ Int.gcd p.1 p.2.2 = 1 ∧
        p.2.1 ^ 2 = binaryForm c p.1 p.2.2 :=
  ⟨of_mem_search hG, fun ⟨⟨_, hb, hz⟩, ha, hg, hy⟩ ↦ mem_search_of hG hL hfams hb hz ha hg hy⟩

theorem nodup_search (c : List ℤ) (H : ℕ) {G L : ℕ} (fams : Array Family) {dens : List ℕ}
    (hG : 0 < G) (hL : 0 < L) (hdens : dens.Nodup) :
    (search c (BruteForce.degree c) H G L fams dens).Nodup := by
  rw [search]
  refine List.nodup_flatMap.mpr ⟨fun b _ ↦ ?_, (hdens.filter _).pairwise_of_forall_ne
    fun b _ b' _ hne p hp hp' ↦ hne ?_⟩
  · rw [getElem!_map_range _ (Nat.mod_lt _ hG)]
    refine List.nodup_flatMap.mpr ⟨fun _ _ ↦ nodup_chunkPoints c hG .., ?_⟩
    refine (List.pairwise_map.mpr ((pairwise_slots H hG hL).imp fun h p hp hp' ↦ ?_)).filter _
    obtain ⟨t, ht, hx⟩ := (of_mem_chunkPoints hp).2.1
    obtain ⟨t', ht', hx'⟩ := (of_mem_chunkPoints hp').2.1
    exact h t ht t' ht' (hx.symm.trans hx')
  · obtain ⟨_, -, hp⟩ := List.mem_flatMap.mp hp
    obtain ⟨_, -, hp'⟩ := List.mem_flatMap.mp hp'
    exact_mod_cast (of_mem_chunkPoints hp).1.symm.trans (of_mem_chunkPoints hp').1

/-! ### The denominators -/

theorem isSquare_mul_self (k : ℕ) : isSquare (k * k) = true := by
  simp [isSquare, Nat.sqrt_eq]

theorem mem_denominators_iff {c : List ℤ} {d H : ℕ} {bLow bHigh : ℤ} {b : ℕ} :
    b ∈ denominators c d H bLow bHigh ↔
      b ∈ List.range' (max 1 bLow.toNat)
        ((if bHigh < 1 then H else min H bHigh.toNat) + 1 - max 1 bLow.toNat) ∧
      (d % 2 = 1 → ((List.range' 1 (if bHigh < 1 then H else min H bHigh.toNat)).filter
        fun s ↦ (c.getD d 0).natAbs % s == 0).any fun s ↦ b % s == 0 && isSquare (b / s)) := by
  by_cases hd : d % 2 = 1 <;> simp only [denominators, hd, ↓reduceIte, List.mem_filter,
    forall_const, IsEmpty.forall_iff, and_true]

theorem mem_denominators {c : List ℤ} {d H : ℕ} {bLow bHigh : ℤ} {b : ℕ}
    (h : b ∈ denominators c d H bLow bHigh) :
    1 ≤ b ∧ b ≤ H ∧ bLow ≤ b ∧ (bHigh < 1 ∨ (b : ℤ) ≤ bHigh) := by
  have h' := (mem_denominators_iff.mp h).1
  rw [List.mem_range'_1] at h'
  split_ifs at h' <;> lia

theorem mem_denominators_of_isCandidate {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ} {a : ℤ} {b : ℕ}
    (h1 : 1 ≤ b) (h2 : b ≤ H) (h3 : bLow ≤ b) (h4 : bHigh < 1 ∨ (b : ℤ) ≤ bHigh)
    (hc : IsCandidate c a b) : b ∈ denominators c (BruteForce.degree c) H bLow bHigh := by
  refine mem_denominators_iff.mpr ⟨by rw [List.mem_range'_1]; split_ifs <;> lia, fun hd ↦ ?_⟩
  obtain ⟨hab, y, hy⟩ := hc
  obtain ⟨s, k, -, hs, rfl⟩ := exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd hd hab hy
  have hs0 : 0 < s := Nat.pos_of_ne_zero fun h ↦ by simp [h] at h1
  have hk0 : 0 < k := Nat.pos_of_ne_zero fun h ↦ by simp [h] at h1
  have hsb : s ≤ s * k * k :=
    (Nat.le_mul_of_pos_right s hk0).trans (Nat.le_mul_of_pos_right _ hk0)
  simp only [List.any_eq_true, List.mem_filter, List.mem_range'_1, Bool.and_eq_true, beq_iff_eq]
  refine ⟨s, ⟨⟨hs0, ?_⟩, Nat.mod_eq_zero_of_dvd hs⟩, ?_, ?_⟩
  · split_ifs <;> lia
  · rw [mul_assoc]
    exact Nat.mul_mod_right s (k * k)
  · rw [mul_assoc, Nat.mul_div_cancel_left _ hs0]
    exact isSquare_mul_self k

theorem nodup_denominators (c : List ℤ) (d H : ℕ) (bLow bHigh : ℤ) :
    (denominators c d H bLow bHigh).Nodup := by
  by_cases hd : d % 2 = 1 <;> simp only [denominators, hd, ↓reduceIte]
  · exact (List.nodup_range' ..).filter _
  · exact List.nodup_range' ..

/-! ### The parameters -/

theorem mem_of_mem_groupModuli {Mmax : ℕ} {l : List (ℕ × Array (Array Bool))}
    {g : List (ℕ × Array (Array Bool))} (hg : g ∈ groupModuli Mmax l) {t : ℕ × Array (Array Bool)}
    (ht : t ∈ g) : t ∈ l := by
  induction l generalizing g with
  | nil => simp [groupModuli] at hg
  | cons t' ts ih =>
    rw [groupModuli] at hg
    split at hg
    · rename_i g' gs heq
      split_ifs at hg
      · rcases List.mem_cons.mp hg with rfl | hg
        · rcases List.mem_cons.mp ht with rfl | ht
          · exact List.mem_cons_self
          · exact List.mem_cons_of_mem _ (ih (heq ▸ List.mem_cons_self) ht)
        · exact List.mem_cons_of_mem _ (ih (heq ▸ List.mem_cons_of_mem _ hg) ht)
      · rcases List.mem_cons.mp hg with rfl | hg
        · rw [List.mem_singleton.mp ht]
          exact List.mem_cons_self
        · exact List.mem_cons_of_mem _ (ih (heq ▸ hg) ht)
    · rw [List.mem_singleton.mp hg, List.mem_singleton] at ht
      rw [ht]
      exact List.mem_cons_self

theorem choose_G_pos (tu : Tuning) (c : List ℤ) (d H B : ℕ) : 0 < (choose tu c d H B).G := by
  simp only [choose, orDefault]
  split_ifs <;> lia

theorem choose_L_pos (tu : Tuning) (c : List ℤ) (d H B : ℕ) : 0 < (choose tu c d H B).L := by
  simp only [choose]
  lia

theorem eq_admitTable_of_mem_moduliTables {tu : Tuning} {c : List ℤ} {d H B : ℕ}
    {t : ℕ × Array (Array Bool)} (ht : t ∈ moduliTables tu c d H B) : t.2 = admitTable c d t.1 := by
  simp only [moduliTables, List.mem_append, List.mem_map] at ht
  rcases ht with ⟨m, -, rfl⟩ | ⟨m, -, rfl⟩ <;> rfl

theorem eq_admitTable_of_mem_sortedGroups {tu : Tuning} {c : List ℤ} {d H B : ℕ}
    {g : List (ℕ × Array (Array Bool))} (hg : g ∈ sortedGroups tu c d H B)
    {t : ℕ × Array (Array Bool)} (ht : t ∈ g) : t.2 = admitTable c d t.1 := by
  simp only [sortedGroups, List.mem_map, List.mem_mergeSort] at hg
  obtain ⟨⟨g, s⟩, ⟨g', hg', hgs⟩, rfl⟩ := hg
  obtain rfl : g' = g := congr(Prod.fst $hgs)
  exact eq_admitTable_of_mem_moduliTables (mem_of_mem_groupModuli hg' ht)

theorem isSound_of_mem_choose {tu : Tuning} {c : List ℤ} {H B : ℕ} {F : Family}
    (hF : F ∈ (choose tu c (BruteForce.degree c) H B).fams) :
    F.IsSound c (choose tu c (BruteForce.degree c) H B).G
      (choose tu c (BruteForce.degree c) H B).L := by
  simp only [choose, List.mem_toArray, List.mem_filterMap] at hF ⊢
  obtain ⟨g, hg, hF⟩ := hF
  exact mkFamily_isSound (fun t ht ↦ eq_admitTable_of_mem_sortedGroups hg ht) hF

/-! ### The points -/

/-- **The fast search lists exactly the points** of height at most `H` with their denominator in
the range of `bLow` and `bHigh`, for every coefficient list, every height bound, every range and
every setting of the parameters. -/
theorem mem_fastPoints_iff {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ} {tu : Tuning}
    {p : ℤ × ℤ × ℤ} :
    p ∈ fastPoints c H bLow bHigh tu ↔ IsPoint c H p ∧ InRegion [] bLow bHigh p := by
  obtain ⟨x, y, z⟩ := p
  simp only [fastPoints, List.mem_append, List.mem_ite_nil_right, mem_pointsOfDen_iff,
    horner_scaledCoeffs_mul, List.mem_singleton]
  rw [mem_search (choose_G_pos ..) (choose_L_pos ..) fun F hF ↦ isSound_of_mem_choose hF]
  simp only [IsPoint, IsNormalizedPair, InRegion]
  constructor
  · rintro (⟨hH, rfl, rfl, hg, hy⟩ | ⟨⟨b, hb, rfl⟩, hx, hg, hy⟩)
    · exact ⟨⟨hy, hg, .inr ⟨rfl, rfl⟩, by simpa using hH, by simp⟩, .inl rfl⟩
    · obtain ⟨h1, h2, h3, h4⟩ := mem_denominators hb
      exact ⟨⟨hy, hg, .inl (by lia), hx, by lia⟩, .inr ⟨h3, h4, .inl trivial⟩⟩
  · rintro ⟨⟨hy, hg, hz | ⟨rfl, rfl⟩, hx, hzH⟩, hr⟩
    · obtain ⟨b, rfl⟩ : ∃ b : ℕ, z = b := ⟨z.toNat, by lia⟩
      have hr' : bLow ≤ b ∧ (bHigh < 1 ∨ (b : ℤ) ≤ bHigh) := by
        rcases hr with h | ⟨h3, h4, -⟩
        · simp at h
          lia
        · exact ⟨h3, h4⟩
      exact .inr ⟨⟨b, mem_denominators_of_isCandidate (by lia) (by lia) hr'.1 hr'.2
        ⟨hg, y, hy⟩, rfl⟩, hx, hg, hy⟩
    · exact .inl ⟨by simpa using hx, rfl, rfl, hg, hy⟩

/-- **The fast search lists each point once.** -/
theorem nodup_fastPoints (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ) (tu : Tuning) :
    (fastPoints c H bLow bHigh tu).Nodup := by
  rw [fastPoints]
  refine List.Nodup.append ?_ (nodup_search _ _ _ (choose_G_pos ..) (choose_L_pos ..)
    (nodup_denominators ..)) fun p hp hp' ↦ ?_
  · split_ifs
    · exact nodup_pointsOfDen _ _ _ (List.nodup_singleton 1)
    · exact List.nodup_nil
  · have h0 : p.2.2 = 0 := by
      split_ifs at hp
      · exact (mem_pointsOfDen_iff.mp hp).2.1
      · simp at hp
    obtain ⟨⟨b, hb, hz⟩, -⟩ := (mem_search (choose_G_pos ..) (choose_L_pos ..)
      fun F hF ↦ isSound_of_mem_choose hF).mp hp'
    have := (mem_denominators hb).1
    lia

end Ratpoints.Fast

end
