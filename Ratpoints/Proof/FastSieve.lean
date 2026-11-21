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
public import Ratpoints.Spec.Sturm

import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.LinearCombination
import Ratpoints.Mathlib.Algebra.Order.Field.Basic
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Divisors
import Ratpoints.Proof.FastDenominators
import Ratpoints.Proof.Jacobi
import Ratpoints.Proof.Rounding
import Ratpoints.Proof.SturmCoverage

/-!
# The fast search: tables, classes, region, denominators, parameters

Facts about the parts of the fast search `Ratpoints.FastMask.fastPoints` that do not depend on its
bit masks. The sieve is a sound filter: a point `(a, y, b)` makes `(a, b)` a candidate
(`Ratpoints.Fast.IsCandidate`), the filters let every candidate pass, and only the exact check of
the brute force decides what is listed; so only this direction is proved about the tables.

* The residues of a candidate modulo every `m > 0` pass the rows of `Ratpoints.Fast.admitRow`
  (`Ratpoints.Fast.getElem!_admitRow_of_isCandidate`), which also give the classes modulo the step
  that a denominator allows, and the table of `m` (`Ratpoints.Fast.admits_mkTable_of_isCandidate`):
  an entry of `Ratpoints.Fast.Table.admits` is that of row `1` at `x u` when `u` inverts `r`, else
  that of row `r` (`Ratpoints.Fast.admits_mkTable`), and row `1` at `x u` allows a point when row
  `r` at `x` does, the binary form being homogeneous of even degree
  (`Ratpoints.Fast.binaryForm_mul_modEq_sq`).
* The chunks of `[0, cnt)` cover it (`Ratpoints.Fast.mem_chunks_iff`,
  `Ratpoints.Fast.exists_mem_chunks`, `Ratpoints.Fast.le_of_mem_chunks`), and the classes modulo
  `G` split the indices (`Ratpoints.Fast.lt_classCount`,
  `Ratpoints.Fast.add_mul_lt_of_lt_classCount`, `Ratpoints.Fast.eq_of_add_mul_eq`,
  `Ratpoints.Fast.eq_of_add_mul_add_eq`).
* Assuming Sturm's theorem, one of the intervals that the Sturm step keeps holds `a / b` for every
  `a` with `|a| ≤ H` and `F(a, b) ≥ 0` (`Ratpoints.Fast.exists_mem_sturmIntervals`, from
  `Ratpoints.Sturm.covers_computeSturm`), and the bounds that `Ratpoints.Fast.endFrac` makes of
  the ends of the interval bound `a / b` (`Ratpoints.Fast.div_le_of_endFrac_eq_some`,
  `Ratpoints.Fast.le_div_of_endFrac_eq_some`).
* The denominators that the search leaves out carry no point
  (`Ratpoints.Fast.mem_denominators_of_isCandidate`): for odd degree it takes those of the form
  `s k ^ 2` with `s` dividing the leading coefficient, which `Ratpoints.Fast.squareDens` marks
  (`Ratpoints.Fast.getElem!_squareDens_of_isCandidate`, from
  `Ratpoints.exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd`), and for even degree it leaves out
  those that `Ratpoints.Fast.forbiddenDens` marks, multiples of an odd `q` with `J(c_d | q) = -1`
  (`Ratpoints.Fast.exists_dvd_of_getElem!_forbiddenDens_ne_zero`), while the symbol is `1` on every
  divisor of the denominator of a point prime to `c_d`
  (`Ratpoints.Sieve.jacobiSym_eq_one_of_sq_eq_binaryForm`,
  `Ratpoints.Fast.getElem!_forbiddenDens_eq_zero`).
* The tables of the search are those of moduli of the list it is given
  (`Ratpoints.Fast.exists_mem_eq_mkTable_of_mem_takeTables`), all positive
  (`Ratpoints.Fast.pos_of_mem_candidateModuli_append_furtherModuli`), and the families take each of
  them once, in their order (`Ratpoints.Fast.flatten_groupTables`).
* `Ratpoints.Fast.reversed` reverses only for the whole box, and then the binary form of the
  reversed list is that of `c` with `x` and `z` exchanged
  (`Ratpoints.Fast.isFullBox_and_binaryForm_eq_of_reversed_eq`).

## Main statements

* `Ratpoints.Fast.admits_mkTable_of_isCandidate`: the tables admit the residues of a candidate.
* `Ratpoints.Fast.exists_mem_sturmIntervals`: assuming Sturm's theorem, the region holds every
  point.
* `Ratpoints.Fast.mem_denominators_of_isCandidate`: the denominators of the search include that of
  every point.
-/

@[expose] public section

/-! ### Booleans as bytes -/

theorem Bool.toUInt8_bne_zero (b : Bool) : (b.toUInt8 != 0) = b := by
  cases b <;> rfl

namespace Ratpoints.Fast

open BruteForce

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
  have : i ≤ degree c + degree c % 2 := by lia [Finset.mem_range.mp hi]
  calc c.getD i 0 * (u * b) ^ i * b ^ (degree c + degree c % 2 - i)
      = c.getD i 0 * u ^ i * (b ^ i * b ^ (degree c + degree c % 2 - i)) := by ring
    _ = b ^ (degree c + degree c % 2) * (c.getD i 0 * u ^ i) := by
      rw [← pow_add, Nat.add_sub_cancel' this]
      ring

theorem sqTable_sq {m : ℕ} (hm : 0 < m) (y : ℤ) : (sqTable m)[(y ^ 2 % m).toNat]! = true := by
  have hm' : (0 : ℤ) < m := Int.natCast_pos.mpr hm
  have hy : (y % m).toNat < m := by lia [Int.emod_lt_of_pos y hm']
  have heq : (y % m).toNat * (y % m).toNat % m = (y ^ 2 % m).toNat := by
    rw [← Int.natCast_inj]
    push_cast [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne'), Int.natCast_mod]
    rw [← Int.mul_emod, sq]
  refine Array.getElem!_foldl_set!_eq_true _ _ (by simpa [← heq] using Nat.mod_lt _ hm)
    (.inr ⟨_, List.mem_range.mpr hy, heq⟩)

theorem natGcd_eq (a b : ℕ) : natGcd a b = Nat.gcd a b := by
  fun_induction natGcd a b with
  | case1 => simp
  | case2 _ _ _ ih => rw [ih, Nat.gcd_comm, ← Nat.gcd_rec, Nat.gcd_comm]

theorem coprimeWith_of_gcd_eq_one {a : ℤ} {b m : ℕ} (hm : 0 < m) (hab : Int.gcd a b = 1) :
    coprimeWith (Nat.gcd (b % m) m) (a % (m : ℤ)).toNat = true := by
  simp only [coprimeWith, natGcd_eq, Bool.or_eq_true, beq_iff_eq]
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

theorem sqTable_of_modEq {m : ℕ} (hm : 0 < m) {v y : ℤ} (h : v ≡ y ^ 2 [ZMOD m]) :
    (sqTable m)[(v % m).toNat]! = true := by
  rw [h.eq]
  exact sqTable_sq hm y

theorem getElem!_admitRow {c : List ℤ} {m r x : ℕ} (hm : 0 < m) (hx : x < m)
    (hg : coprimeWith (Nat.gcd r m) x = true) {y : ℤ} (hy : binaryForm c x r ≡ y ^ 2 [ZMOD m]) :
    (admitRow c (BruteForce.degree c) m (sqTable m) r)[x]! = true := by
  rw [admitRow, Array.getElem!_map_toArray_range _ hx, natGcd_eq, hg, Bool.true_and]
  exact sqTable_of_modEq hm ((hornerMod_scaledCoeffsMod_modEq c m r x).trans hy)

theorem intCast_mul_modEq_one {b u m : ℕ} (h : b % m * u % m = 1 % m) :
    (b : ℤ) * u ≡ 1 [ZMOD m] := by
  have := congr((($h : ℕ) : ℤ))
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

/-! ### The tables -/

@[simp]
theorem size_admitRow (c : List ℤ) (d m : ℕ) (sq : Array Bool) (r : ℕ) :
    (admitRow c d m sq r).size = m := by
  simp [admitRow]

@[simp]
theorem size_boolBytes (row : Array Bool) : (boolBytes row).size = row.size :=
  Array.size_map ..

theorem getElem!_boolBytes (row : Array Bool) (i : ℕ) :
    (boolBytes row)[i]! = row[i]!.toUInt8 := by
  rw [boolBytes, ByteArray.getElem!_mk, Array.getElem!_map (f := fun x : Bool ↦ x.toUInt8) rfl]

theorem toNat_getElem!_boolBytes_le_one (row : Array Bool) (i : ℕ) :
    (boolBytes row)[i]!.toNat ≤ 1 := by
  rw [getElem!_boolBytes]
  cases row[i]! <;> decide

@[simp]
theorem m_mkTable (c : List ℤ) (d m : ℕ) : (mkTable c d m).m = m := rfl

@[simp]
theorem one_mkTable (c : List ℤ) (d m : ℕ) :
    (mkTable c d m).one = boolBytes (admitRow c d m (sqTable m) 1) := rfl

@[simp]
theorem inv_mkTable (c : List ℤ) (d m : ℕ) : (mkTable c d m).inv = invTable m := rfl

theorem getElem!_sing_mkTable (c : List ℤ) (d : ℕ) {m r : ℕ} (hr : r < m) :
    (mkTable c d m).sing[r]! =
      if r * (invTable m)[r]! % m == 1 % m && (invTable m)[r]! < m then .empty
      else boolBytes (admitRow c d m (sqTable m) r) := by
  simp only [mkTable, Array.getElem!_map_toArray_range _ hr]

theorem toNat_getElem!_sing_mkTable_le_one {c : List ℤ} {d m r : ℕ} (hr : r < m) (i : ℕ) :
    ((mkTable c d m).sing[r]!)[i]!.toNat ≤ 1 := by
  rw [getElem!_sing_mkTable c d hr]
  split_ifs
  · rw [getElem!_neg _ _ (by simp)]
    decide
  · exact toNat_getElem!_boolBytes_le_one _ _

theorem m_pos_of_exists_eq_mkTable {c : List ℤ} {d : ℕ} {T : Table}
    (h : ∃ m > 0, T = mkTable c d m) : 0 < T.m := by
  obtain ⟨m, hm, rfl⟩ := h
  exact hm

/-- An entry of the table of `m` is the entry of row `1` at `x u` when `u = inv[r]` inverts `r`,
else that of row `r`. -/
theorem admits_mkTable (c : List ℤ) (d : ℕ) {m r : ℕ} (hr : r < m) (x : ℕ) :
    (mkTable c d m).admits x r =
      if r * (invTable m)[r]! % m == 1 % m && (invTable m)[r]! < m then
        (admitRow c d m (sqTable m) 1)[x * (invTable m)[r]! % m]!
      else (admitRow c d m (sqTable m) r)[x]! := by
  rw [Table.admits, getElem!_sing_mkTable c d hr]
  by_cases h : (r * (invTable m)[r]! % m == 1 % m && (invTable m)[r]! < m) = true
  · simp [h, getElem!_boolBytes, Bool.toUInt8_bne_zero]
  · simp [h, getElem!_boolBytes, Bool.toUInt8_bne_zero, show m ≠ 0 by lia]

theorem getElem!_admitRow_of_isCandidate {c : List ℤ} {m : ℕ} (hm : 0 < m) {a : ℤ} {b : ℕ}
    (h : IsCandidate c a b) :
    (admitRow c (degree c) m (sqTable m) (b % m))[(a % (m : ℤ)).toNat]! = true := by
  obtain ⟨hab, y, hy⟩ := h
  have hm' : (0 : ℤ) < m := Int.natCast_pos.mpr hm
  refine getElem!_admitRow (y := y) hm (by lia [Int.emod_lt_of_pos a hm'])
    (coprimeWith_of_gcd_eq_one hm hab) ?_
  refine (binaryForm_modEq c ?_ ?_).trans (by rw [hy])
  · rw [Int.toNat_of_nonneg (Int.emod_nonneg a hm'.ne')]
    exact Int.mod_modEq a m
  · push_cast [Int.natCast_mod]
    exact Int.mod_modEq _ _

theorem natMod_eq_toNat_of_dvd {m : ℕ} {a : ℤ} {k : ℕ} (h : (m : ℤ) ∣ a - k) :
    k % m = (a % (m : ℤ)).toNat := by
  rw [← (Int.modEq_iff_dvd.mpr h).eq, ← Int.natCast_mod, Int.toNat_natCast]

theorem admits_mkTable_of_isCandidate {c : List ℤ} {m : ℕ} (hm : 0 < m) {a : ℤ} {b : ℕ}
    (h : IsCandidate c a b) :
    (mkTable c (degree c) m).admits (a % (m : ℤ)).toNat (b % m) = true := by
  rw [admits_mkTable _ _ (Nat.mod_lt b hm)]
  split_ifs with hu
  · obtain ⟨-, y, hy⟩ := h
    have hm' : (0 : ℤ) < m := Int.natCast_pos.mpr hm
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hu
    refine getElem!_admitRow hm (Nat.mod_lt _ hm) (by simp [coprimeWith])
      (binaryForm_mul_modEq_sq hy ?_ (by simpa using hu.1))
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hm'.ne')]
    exact Int.mod_modEq a m
  · exact getElem!_admitRow_of_isCandidate hm h

/-! ### Chunks and classes -/

theorem mem_chunks_iff {cnt L t₀ len : ℕ} :
    (t₀, len) ∈ chunks cnt L ↔ ∃ k < (cnt + L - 1) / L, t₀ = k * L ∧ len = min L (cnt - k * L) := by
  simp only [chunks, List.mem_map, List.mem_range, Prod.mk.injEq]
  grind

theorem exists_mem_chunks {cnt L u : ℕ} (hL : 0 < L) (hu : u < cnt) :
    ∃ t₀ len, (t₀, len) ∈ chunks cnt L ∧ t₀ = u / L * L ∧ u % L < len := by
  refine ⟨u / L * L, min L (cnt - u / L * L), mem_chunks_iff.mpr ⟨u / L, ?_, rfl, rfl⟩, rfl, ?_⟩
  · exact (Nat.le_div_iff_mul_le hL).mpr (by rw [Nat.succ_mul]; lia [Nat.div_mul_le_self u L])
  · lia [Nat.mod_lt u hL, Nat.div_add_mod u L]

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

theorem eq_of_add_mul_eq {G ρ ρ' u u' : ℕ} (hρ : ρ < G) (hρ' : ρ' < G)
    (h : ρ + G * u = ρ' + G * u') : ρ = ρ' := by
  have h1 := congr($h % G)
  rwa [Nat.add_mul_mod_self_left, Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ,
    Nat.mod_eq_of_lt hρ'] at h1

theorem eq_of_add_mul_add_eq {G L ρ k k' t t' : ℕ} (hG : 0 < G) (hL : 0 < L) (ht : t < L)
    (ht' : t' < L) (h : ρ + G * (k * L + t) = ρ + G * (k' * L + t')) : k = k' := by
  have := congr($(Nat.eq_of_mul_eq_mul_left hG (Nat.add_left_cancel h)) / L)
  simpa [Nat.mul_comm k L, Nat.mul_comm k' L, Nat.mul_add_div hL, Nat.div_eq_of_lt ht,
    Nat.div_eq_of_lt ht'] using this

/-! ### The region -/

/-- The bound `n / q` that `Ratpoints.Fast.endFrac` makes of a lower end `x` lies below every `v`
with `|v| ≤ H` above the value of `x`: it is that value when it lies in `[-H, H]`, `-(H + 1)` when
it lies below, and `H + 1` only when it lies above `H`, where no such `v` is. -/
theorem div_le_of_endFrac_eq_some {H : ℕ} {x : Double} {n : ℤ} {q : ℕ}
    (h : endFrac H x = some (n, q)) {v : ℚ} (hv : |v| ≤ H)
    (hx : doubleValue x.bits ≤ (v : WithBotTop ℚ)) : (n : ℚ) / q ≤ v := by
  rw [abs_le] at hv
  rcases hd : x.toDyadic with ⟨m, e⟩
  simp only [endFrac, hd] at h
  split_ifs at h with hf _ _ _ hs <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  · rwa [Double.doubleValue_eq_of_toDyadic_eq hf hd, WithBotTop.coe_le_coe,
      ← intCast_ediv_gcd_div_natCast_div_gcd] at hx
  · push_cast
    linarith
  · rw [Double.doubleValue_eq_of_toDyadic_eq hf hd, WithBotTop.coe_le_coe,
      div_le_iff₀ (by positivity)] at hx
    have : (m * 2 ^ e.toNat : ℤ) ≤ (H : ℤ) * ((2 ^ (-e).toNat : ℕ) : ℤ) :=
      mod_cast hx.trans (mul_le_mul_of_nonneg_right hv.2 (by positivity))
    lia
  · push_cast
    linarith
  · rw [Double.doubleValue_bits, ite_eq_left (by simpa [Double.isFinite] using hf),
      ite_eq_right hs] at hx
    simp at hx

/-- The bound `n / q` that `Ratpoints.Fast.endFrac` makes of an upper end `x` lies above every `v`
with `|v| ≤ H` below the value of `x`: it is that value when it lies in `[-H, H]`, `H + 1` when it
lies above, and `-(H + 1)` only when it lies below `-H`, where no such `v` is. -/
theorem le_div_of_endFrac_eq_some {H : ℕ} {x : Double} {n : ℤ} {q : ℕ}
    (h : endFrac H x = some (n, q)) {v : ℚ} (hv : |v| ≤ H)
    (hx : (v : WithBotTop ℚ) ≤ doubleValue x.bits) : v ≤ (n : ℚ) / q := by
  rw [abs_le] at hv
  rcases hd : x.toDyadic with ⟨m, e⟩
  simp only [endFrac, hd] at h
  split_ifs at h with hf _ _ _ hs <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  · rwa [Double.doubleValue_eq_of_toDyadic_eq hf hd, WithBotTop.coe_le_coe,
      ← intCast_ediv_gcd_div_natCast_div_gcd] at hx
  · rw [Double.doubleValue_eq_of_toDyadic_eq hf hd, WithBotTop.coe_le_coe,
      le_div_iff₀ (by positivity)] at hx
    have : -(H : ℤ) * ((2 ^ (-e).toNat : ℕ) : ℤ) ≤ (m * 2 ^ e.toNat : ℤ) :=
      mod_cast (mul_le_mul_of_nonneg_right hv.1 (by positivity)).trans hx
    lia
  · push_cast
    linarith
  · rw [Double.doubleValue_bits, ite_eq_left (by simpa [Double.isFinite] using hf),
      ite_eq_left hs] at hx
    simp at hx
  · push_cast
    linarith

/-- The denominator of the bound that `Ratpoints.Fast.endFrac` makes of an end is positive: a power
of `2` divided by a divisor of it, or `1`. -/
theorem pos_of_endFrac_eq_some {H : ℕ} {x : Double} {n : ℤ} {q : ℕ}
    (h : endFrac H x = some (n, q)) : 0 < q := by
  rcases hd : x.toDyadic with ⟨m, e⟩
  simp only [endFrac, hd] at h
  split_ifs at h <;> obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
  · exact Nat.div_pos (Nat.le_of_dvd (Nat.two_pow_pos _) (Nat.gcd_dvd_right _ _))
      (Nat.gcd_pos_of_pos_right _ (Nat.two_pow_pos _))
  all_goals exact Nat.one_pos

/-- Assuming Sturm's theorem, the intervals of the Sturm step on the whole line hold every `a / b`
with `|a| ≤ H`, `b > 0` and `F(a, b) ≥ 0` (`Ratpoints.Sturm.covers_computeSturm`). -/
theorem exists_mem_sturmIntervals (hS : SturmTheorem) {c : List ℤ} {H depth : ℕ}
    {ivs : Array (Double × Double)} (h : sturmIntervals c (degree c) H depth = some ivs) {a : ℤ}
    {b : ℕ} (hb : 0 < b) (ha : |a| ≤ H) (hF : 0 ≤ binaryForm c a b) :
    ∃ iv ∈ ivs, doubleValue iv.1.bits ≤ (((a : ℚ) / b : ℚ) : WithBotTop ℚ) ∧
      (((a : ℚ) / b : ℚ) : WithBotTop ℚ) ≤ doubleValue iv.2.bits := by
  simp only [sturmIntervals] at h
  split_ifs at h with hc
  obtain ⟨hd, hd57, hH, hdep⟩ := hc
  have hab : |(a : ℚ) / b| ≤ 2 ^ 63 := (abs_intCast_div_natCast_le ha b).trans (mod_cast hH.le)
  obtain ⟨_, hi, hl, hu⟩ := Sturm.covers_computeSturm hS hd (getD_degree_ne_zero_of_pos hd) hd57
    hdep (by decide) h (Sturm.eval_chainPoly_nonneg hb hF) (by simpa using hab)
    ⟨_, List.mem_singleton_self _, by simp [Double.doubleValue_huge, Double.doubleValue_huge_neg]⟩
  obtain ⟨iv, hiv, rfl⟩ := List.mem_map.mp hi
  exact ⟨iv, Array.mem_toList_iff.mp hiv, hl, hu⟩

/-! ### The denominators -/

theorem getElem!_forbiddenDens_eq_zero {c : List ℤ} (hd : degree c % 2 = 0) {a : ℤ} {b : ℕ}
    (hc : IsCandidate c a b) (hi : ℕ) : (forbiddenDens (c.getD (degree c) 0) hi)[b]! = 0 := by
  by_contra h
  obtain ⟨q, hq, hqb, hJ⟩ := exists_dvd_of_getElem!_forbiddenDens_ne_zero h
  obtain ⟨hab, y, hy⟩ := hc
  have hg : Int.gcd (c.getD (degree c) 0) q = 1 := by
    by_contra hg
    rw [jacobiSym.eq_zero_iff.mpr ⟨by lia, hg⟩] at hJ
    exact absurd hJ (by decide)
  rw [Sieve.jacobiSym_eq_one_of_sq_eq_binaryForm hab hd hy hqb hg] at hJ
  exact absurd hJ (by decide)

/-- For odd degree, the denominator `b` of a candidate is `s k ^ 2` with `s` dividing the leading
coefficient (`Ratpoints.exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd`), which
`Ratpoints.Fast.squareDens` marks. -/
theorem getElem!_squareDens_of_isCandidate {c : List ℤ} (hd : degree c % 2 = 1) {a : ℤ}
    {b hi : ℕ} (hb : 1 ≤ b) (hbhi : b ≤ hi) (hc : IsCandidate c a b) :
    (squareDens (c.getD (degree c) 0).natAbs hi)[b]! = 1 := by
  obtain ⟨hab, y, hy⟩ := hc
  obtain ⟨s, k, -, hs, rfl⟩ := exists_eq_mul_mul_of_sq_eq_binaryForm_of_odd hd hab hy
  have hk : 0 < k := Nat.pos_of_ne_zero fun h ↦ by simp [h] at hb
  exact getElem!_squareDens (Int.natAbs_ne_zero.mpr (getD_degree_ne_zero_of_pos (by lia))) hs hk
    hbhi

/-- The denominators of the search lie in the range of `bLow`, `bHigh` and `H`, in ascending
order. -/
theorem denominators_sublist (c : List ℤ) (d H : ℕ) (bLow bHigh : ℤ) :
    (denominators c d H bLow bHigh).Sublist (List.range' (max 1 bLow.toNat)
      ((if bHigh < 1 then H else min H bHigh.toNat) + 1 - max 1 bLow.toNat)) := by
  simp only [denominators]
  generalize (if bHigh < 1 then H else min H bHigh.toNat) = hi
  split_ifs <;> first | exact collectMarked_sublist _ _ (le_max_left _ _) _ | exact .refl _

theorem mem_denominators {c : List ℤ} {d H : ℕ} {bLow bHigh : ℤ} {b : ℕ}
    (h : b ∈ denominators c d H bLow bHigh) :
    1 ≤ b ∧ b ≤ H ∧ bLow ≤ b ∧ (bHigh < 1 ∨ (b : ℤ) ≤ bHigh) := by
  have h' := (denominators_sublist ..).subset h
  rw [List.mem_range'_1] at h'
  split_ifs at h' <;> lia

theorem mem_denominators_of_isCandidate {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ} {a : ℤ} {b : ℕ}
    (h1 : 1 ≤ b) (h2 : b ≤ H) (h3 : bLow ≤ b) (h4 : bHigh < 1 ∨ (b : ℤ) ≤ bHigh)
    (hc : IsCandidate c a b) : b ∈ denominators c (BruteForce.degree c) H bLow bHigh := by
  have hr : b ∈ List.range' (max 1 bLow.toNat)
      ((if bHigh < 1 then H else min H bHigh.toNat) + 1 - max 1 bLow.toNat) := by
    rw [List.mem_range'_1]
    split_ifs <;> lia
  simp only [denominators]
  generalize (if bHigh < 1 then H else min H bHigh.toNat) = hi at hr ⊢
  have hbhi : b ≤ hi := by lia [List.mem_range'_1.mp hr]
  split_ifs with hd
  · exact (mem_collectMarked_iff (le_max_left _ _)).mpr
      ⟨hr, getElem!_squareDens_of_isCandidate hd h1 hbhi hc⟩
  · exact hr
  · exact (mem_collectMarked_iff (le_max_left _ _)).mpr
      ⟨hr, getElem!_forbiddenDens_eq_zero (Nat.mod_two_ne_one.mp hd) hc hi⟩

theorem nodup_denominators (c : List ℤ) (d H : ℕ) (bLow bHigh : ℤ) :
    (denominators c d H bLow bHigh).Nodup :=
  (List.nodup_range' ..).sublist (denominators_sublist ..)

/-! ### The parameters -/

theorem exists_mem_eq_mkTable_of_mem_takeTables {c : List ℤ} {d κ : ℕ} {ms : List ℕ} {E : ℕ}
    {T : Table} (hT : T ∈ takeTables c d κ ms E) : ∃ m ∈ ms, T = mkTable c d m := by
  induction ms generalizing E with
  | nil => simp [takeTables] at hT
  | cons m ms ih =>
    rw [takeTables] at hT
    split_ifs at hT
    · rcases List.mem_cons.mp hT with rfl | hT
      · exact ⟨m, List.mem_cons_self, rfl⟩
      · obtain ⟨m', hm', rfl⟩ := ih hT
        exact ⟨m', List.mem_cons_of_mem _ hm', rfl⟩
    · simp at hT

/-- The families of `Ratpoints.Fast.groupTables` take every table once, in their order. -/
theorem flatten_groupTables (Mmax : ℕ) (ts : List Table) : (groupTables Mmax ts).flatten = ts := by
  induction ts with
  | nil => rfl
  | cons t ts ih =>
    rw [groupTables]
    split <;> rename_i heq <;> rw [heq] at ih <;> subst ih
    · split_ifs <;> simp
    · rfl

theorem mem_of_mem_groupTables {Mmax : ℕ} {ts g : List Table} (hg : g ∈ groupTables Mmax ts)
    {T : Table} (hT : T ∈ g) : T ∈ ts :=
  flatten_groupTables Mmax ts ▸ List.mem_flatten.mpr ⟨g, hg, hT⟩

theorem pos_of_mem_candidateModuli_append_furtherModuli {m : ℕ}
    (hm : m ∈ candidateModuli ++ furtherModuli) : 0 < m := by
  revert m
  decide

/-! ### The reversal -/

/-- `Ratpoints.Fast.reversed` reverses only for the whole box, and then the binary form of the
reversed list is that of `c` with `x` and `z` exchanged
(`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`). -/
theorem isFullBox_and_binaryForm_eq_of_reversed_eq {c c' : List ℤ} {H : ℕ} {bLow bHigh : ℤ}
    (h : reversed c H bLow bHigh = (c', true)) :
    IsFullBox ([] : List (WithBotTop ℚ × WithBotTop ℚ)) bLow bHigh H ∧
      ∀ x z, binaryForm c' x z = binaryForm c z x := by
  simp only [reversed] at h
  split_ifs at h with hb
  · split at h
    · obtain rfl := congr(Prod.fst $h)
      exact ⟨⟨rfl, hb⟩, Setup.binaryForm_eq_of_reversal_eq_ok ‹_›⟩
    · simp at h
  · simp at h

end Ratpoints.Fast

end
