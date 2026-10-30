/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.Int.ModEq
public import Ratpoints.Model.FastSieve
public import Ratpoints.Spec.Basic
public import Ratpoints.Spec.Region

import Mathlib.Algebra.Order.BigOperators.GroupWithZero.List
import Mathlib.Tactic.LinearCombination
import Ratpoints.Proof.BruteForce
import Ratpoints.Proof.Divisors

/-!
# The fast search finds exactly the points

`Ratpoints.Fast.fastPoints c H bLow bHigh tu` lists the normalized points of height at most `H`
on `y ^ 2 = F(x, z)` whose denominator is `0` or lies in the range of `bLow` and `bHigh`, each
once, for every setting `tu` of its parameters (`Ratpoints.Fast.mem_fastPoints_iff`,
`Ratpoints.Fast.nodup_fastPoints`).

The sieve is a sound filter: a point `(a, y, b)` makes `(a, b)` a candidate
(`Ratpoints.Fast.IsCandidate`), and the residues of a candidate modulo every `m` pass the table
`Ratpoints.Fast.admitTable` (`Ratpoints.Fast.admitTable_spec`), so the bit of `a` survives in
the row of every family (`Ratpoints.Fast.Family.IsSound`, `Ratpoints.Fast.mkFamily_isSound`), in
the entries of each chunk (`Ratpoints.Fast.testBit_entry_row_of_mem_entries`) and in the sieve
(`Ratpoints.Fast.testBit_sieve`); `Ratpoints.Fast.setBits` lists the bits that survive
(`Ratpoints.Fast.mem_setBits`), and the exact check of `Ratpoints.BruteForce.pointsOfDen` keeps the
points among them. The classes modulo `G` and the chunks cover each numerator once
(`Ratpoints.Fast.mem_search`, `Ratpoints.Fast.nodup_search`), and for odd degree the denominators
that the search leaves out carry no point (`Ratpoints.Fast.mem_denominators_of_isCandidate`, from
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

theorem forall₂_scaledCoeffsMod (c : List ℤ) (d m b : ℕ) :
    List.Forall₂ (Int.ModEq m) (scaledCoeffsMod c d m (b % m)) (scaledCoeffs c d b) := by
  rw [scaledCoeffsMod, scaledCoeffs, List.forall₂_map_left_iff, List.forall₂_map_right_iff]
  refine List.forall₂_same.mpr fun k _ ↦ (Int.mod_modEq _ _).mul ?_
  rw [powMod_eq]
  push_cast [Int.natCast_mod]
  exact (Int.mod_modEq _ _).trans ((Int.mod_modEq _ _).pow _)

theorem sqTable_sq {m : ℕ} (hm : 0 < m) (y : ℤ) : (sqTable m)[(y ^ 2 % m).toNat]! = true := by
  have hm' : (0 : ℤ) < m := Int.natCast_pos.mpr hm
  have hlt : (y ^ 2 % m).toNat < m := by
    have := Int.emod_lt_of_pos (y ^ 2) hm'
    lia
  rw [getElem!_pos (sqTable m) _ (by simpa [sqTable] using hlt)]
  simp only [sqTable, Array.getElem_ofFn, List.any_eq_true, List.mem_range, beq_iff_eq]
  refine ⟨(y % m).toNat, by have := Int.emod_lt_of_pos y hm'; lia, ?_⟩
  rw [← Int.natCast_inj]
  push_cast [Int.toNat_of_nonneg (Int.emod_nonneg _ hm'.ne'), Int.natCast_mod]
  rw [← Int.mul_emod, sq]

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

theorem getElem!_admitTable {c : List ℤ} {d m r x : ℕ} (hr : r < m) (hx : x < m) :
    ((admitTable c d m)[r]!)[x]! = (coprimeWith (Nat.gcd r m) x &&
      (sqTable m)[(hornerMod (scaledCoeffsMod c d m r) x m *
        (if d % 2 = 1 then (r : ℤ) else 1) % m).toNat]!) := by
  simp [admitTable, getElem!_pos, hr, hx]

theorem admitTable_spec {c : List ℤ} {m : ℕ} (hm : 0 < m) {a : ℤ} {b : ℕ}
    (h : IsCandidate c a b) :
    ((admitTable c (BruteForce.degree c) m)[b % m]!)[(a % (m : ℤ)).toNat]! = true := by
  obtain ⟨hab, y, hy⟩ := h
  have hm' : (0 : ℤ) < m := Int.natCast_pos.mpr hm
  have hx : (a % (m : ℤ)).toNat < m := by have := Int.emod_lt_of_pos a hm'; lia
  rw [getElem!_admitTable (Nat.mod_lt _ hm) hx, coprimeWith_of_gcd_eq_one hm hab, Bool.true_and]
  have hx' : ((a % (m : ℤ)).toNat : ℤ) ≡ a [ZMOD m] := by
    rw [Int.toNat_of_nonneg (Int.emod_nonneg a hm'.ne')]
    exact Int.mod_modEq a m
  have hf : (if BruteForce.degree c % 2 = 1 then ((b % m : ℕ) : ℤ) else 1) ≡
      (if BruteForce.degree c % 2 = 1 then (b : ℤ) else 1) [ZMOD m] := by
    split_ifs
    · push_cast [Int.natCast_mod]
      exact Int.mod_modEq _ _
    · rfl
  have key := (hornerMod_modEq (forall₂_scaledCoeffsMod c (BruteForce.degree c) m b) hx').mul hf
  rw [horner_scaledCoeffs_mul, ← hy] at key
  rw [key]
  exact sqTable_sq hm y

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

/-- The family `F` is sound for the step `G` and rows of `N` bits: it has a row for every residue
modulo `F.M > 0`, `F.ginv` inverts `G` modulo `F.M`, and the row of `b` has the bit `j < N` set
for every candidate `(a, b)` with `a ≡ G j` modulo `F.M`. -/
structure Family.IsSound (c : List ℤ) (G N : ℕ) (F : Family) : Prop where
  /-- A row for every residue. -/
  size_eq : F.rows.size = F.M
  /-- The modulus is positive. -/
  pos : 0 < F.M
  /-- `F.ginv` inverts `G`. -/
  mul_ginv : G * F.ginv % F.M = 1 % F.M
  /-- The row of `b` keeps the bit `j` of every candidate `(a, b)` with `a ≡ G j`. -/
  testBit : ∀ (a : ℤ) (b j : ℕ), j < N → IsCandidate c a b → (F.M : ℤ) ∣ a - G * j →
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

theorem getElem!_map_range {α : Type*} [Inhabited α] (f : ℕ → α) {n i : ℕ} (hi : i < n) :
    ((List.range n).toArray.map f)[i]! = f i := by
  simp [getElem!_pos, hi]

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

theorem mkFamily_isSound {c : List ℤ} {G N : ℕ} {ts : List (ℕ × Array (Array Bool))}
    (hts : ∀ t ∈ ts, t.2 = admitTable c (BruteForce.degree c) t.1) {F : Family}
    (h : mkFamily G N ts = some F) : F.IsSound c G N := by
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

/-! ### The shift and the entries -/

theorem Family.shift_lt (F : Family) (hF : 0 < F.M) (a₀ : ℤ) : F.shift a₀ < F.M := by
  have := Int.emod_lt_of_pos (a₀ * F.ginv) (Int.natCast_pos.mpr hF)
  rw [Family.shift]
  lia

theorem Family.dvd_sub_shift {c : List ℤ} {G N : ℕ} {F : Family} (hF : F.IsSound c G N) (a₀ : ℤ) :
    (F.M : ℤ) ∣ a₀ - G * F.shift a₀ := by
  have hg : (G : ℤ) * F.ginv ≡ 1 [ZMOD F.M] := by
    have := congr((($hF.mul_ginv : ℕ) : ℤ))
    push_cast [Int.natCast_mod] at this
    exact this
  rw [Family.shift, Int.toNat_of_nonneg (Int.emod_nonneg _ (by have := hF.pos; lia))]
  refine (Int.modEq_iff_dvd.mp ?_)
  calc (G : ℤ) * (a₀ * F.ginv % F.M) ≡ G * (a₀ * F.ginv) [ZMOD F.M] :=
        (Int.mod_modEq _ _).mul_left _
    _ = a₀ * (G * F.ginv) := by ring
    _ ≡ a₀ * 1 [ZMOD F.M] := hg.mul_left _
    _ = a₀ := mul_one a₀

/-- The row of the entry `e` for the denominator `b`, shifted as the sieve shifts it. -/
def Entry.row (e : Entry) (b : ℕ) : ℕ :=
  if e.shift == 0 then e.rows[b % e.M]! else e.rows[b % e.M]! >>> e.shift

theorem testBit_entry_row_of_mem_entries {c : List ℤ} {G N L : ℕ} {fams : Array Family}
    (hfams : ∀ F ∈ fams, F.IsSound c G N ∧ L + F.M ≤ N) {nb len : ℕ} (hlen : len ≤ L) {a₀ : ℤ}
    {e : Entry} (he : e ∈ entries fams nb a₀ len) {b t : ℕ} (ht : t < len)
    (hc : IsCandidate c (a₀ + G * t) b) : (e.row b).testBit t = true := by
  obtain ⟨⟨F, i⟩, hFi, rfl⟩ := Array.mem_map.mp he
  obtain ⟨hF, hN⟩ := hfams F (Array.fst_mem_of_mem_zipIdx hFi)
  have hbit : (F.rows[b % F.M]!).testBit (t + F.shift a₀) = true := by
    refine hF.testBit _ b _ (by have := F.shift_lt hF.pos a₀; lia) hc ?_
    have := Family.dvd_sub_shift hF a₀
    rwa [show a₀ + G * t - G * (t + F.shift a₀ : ℕ) = a₀ - G * F.shift a₀ by push_cast; ring]
  have hlt : b % F.M < F.rows.size := by rw [hF.size_eq]; exact Nat.mod_lt _ hF.pos
  dsimp only
  split_ifs
  · simp only [Entry.row, beq_self_eq_true, ↓reduceIte]
    rw [getElem!_pos _ _ (by simpa using hlt), Array.getElem_map, ← getElem!_pos]
    simp [Nat.testBit_shiftRight, ht, add_comm, hbit]
  · simp only [Entry.row]
    split_ifs with h0
    · simpa [beq_iff_eq.mp h0] using hbit
    · simpa [Nat.testBit_shiftRight, add_comm] using hbit

/-! ### The sieve -/

/-- The step of the sieve. -/
theorem sieve_eq_foldl (es : Array Entry) (mask b : ℕ) :
    sieve es mask b =
      es.toList.foldl (fun acc e ↦ if acc == 0 then 0 else acc &&& e.row b) mask := by
  rw [sieve, ← Array.foldl_toList]
  rfl

theorem testBit_foldl_sieve {b t : ℕ} (l : List Entry) {mask : ℕ} (hmask : mask.testBit t = true)
    (hl : ∀ e ∈ l, (e.row b).testBit t = true) :
    (l.foldl (fun acc e ↦ if acc == 0 then 0 else acc &&& e.row b) mask).testBit t = true := by
  induction l generalizing mask with
  | nil => exact hmask
  | cons e l ih =>
    refine ih ?_ fun e' he' ↦ hl e' (by simp [he'])
    have h0 : (mask == 0) = false := by
      rcases Nat.eq_zero_or_pos mask with rfl | h
      · simp at hmask
      · simpa using h.ne'
    simp [h0, Nat.testBit_and, hmask, hl e (by simp)]

theorem testBit_of_testBit_foldl_sieve {b t : ℕ} (l : List Entry) {mask : ℕ}
    (h : (l.foldl (fun acc e ↦ if acc == 0 then 0 else acc &&& e.row b) mask).testBit t = true) :
    mask.testBit t = true := by
  induction l generalizing mask with
  | nil => exact h
  | cons e l ih =>
    have := ih h
    dsimp only at this
    split_ifs at this with h0
    · simp at this
    · rw [Nat.testBit_and, Bool.and_eq_true] at this
      exact this.1

theorem testBit_sieve {es : Array Entry} {mask b t : ℕ} (hmask : mask.testBit t = true)
    (hes : ∀ e ∈ es, (e.row b).testBit t = true) : (sieve es mask b).testBit t = true := by
  rw [sieve_eq_foldl]
  exact testBit_foldl_sieve _ hmask fun e he ↦ hes e (by simpa using he)

theorem testBit_of_testBit_sieve {es : Array Entry} {mask b t : ℕ}
    (h : (sieve es mask b).testBit t = true) : mask.testBit t = true := by
  rw [sieve_eq_foldl] at h
  exact testBit_of_testBit_foldl_sieve _ h

/-! ### The points of a chunk -/

theorem of_mem_chunkPoints {c : List ℤ} {G : ℕ} {es : Array Entry} {a₀ : ℤ} {len : ℕ}
    {bs : List ℕ} {p : ℤ × ℤ × ℤ} (h : p ∈ chunkPoints c (BruteForce.degree c) G es a₀ len bs) :
    (∃ b ∈ bs, p.2.2 = b) ∧ (∃ t < len, p.1 = a₀ + G * t) ∧ Int.gcd p.1 p.2.2 = 1 ∧
      p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  simp only [chunkPoints, List.mem_flatMap] at h
  obtain ⟨b, hb, hp⟩ := h
  split_ifs at hp with h0
  · simp at hp
  rw [mem_pointsOfDen_iff, horner_scaledCoeffs_mul] at hp
  obtain ⟨hx, hz, hg, hy⟩ := hp
  obtain ⟨t, ht, hx⟩ := List.mem_map.mp hx
  have := testBit_of_testBit_sieve (mem_setBits.mp ht)
  rw [Nat.testBit_two_pow_sub_one, decide_eq_true_eq] at this
  exact ⟨⟨b, hb, hz⟩, ⟨t, this, hx.symm⟩, hz ▸ hg, hz ▸ hy⟩

theorem mem_chunkPoints {c : List ℤ} {G : ℕ} {es : Array Entry} {a₀ : ℤ} {len : ℕ}
    {bs : List ℕ}
    (hes : ∀ b t, t < len → IsCandidate c (a₀ + G * t) b → ∀ e ∈ es, (e.row b).testBit t = true)
    {p : ℤ × ℤ × ℤ} :
    p ∈ chunkPoints c (BruteForce.degree c) G es a₀ len bs ↔
      (∃ b ∈ bs, p.2.2 = b) ∧ (∃ t < len, p.1 = a₀ + G * t) ∧ Int.gcd p.1 p.2.2 = 1 ∧
        p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  refine ⟨of_mem_chunkPoints, fun ⟨⟨b, hb, hz⟩, ⟨t, ht, hx⟩, hg, hy⟩ ↦ ?_⟩
  simp only [chunkPoints, List.mem_flatMap]
  refine ⟨b, hb, ?_⟩
  have hbit := testBit_sieve (mask := 2 ^ len - 1) (es := es)
    (by simp [Nat.testBit_two_pow_sub_one, ht]) (hes b t ht ⟨hx ▸ hz ▸ hg, p.2.1, hx ▸ hz ▸ hy⟩)
  have h0 : (sieve es (2 ^ len - 1) b == 0) = false := by
    rcases Nat.eq_zero_or_pos (sieve es (2 ^ len - 1) b) with h | h
    · simp [h] at hbit
    · simpa using h.ne'
  simp only [h0, Bool.false_eq_true, ↓reduceIte]
  rw [mem_pointsOfDen_iff, horner_scaledCoeffs_mul]
  exact ⟨List.mem_map.mpr ⟨t, mem_setBits.mpr hbit, hx.symm⟩, hz, hz ▸ hg, hz ▸ hy⟩

theorem nodup_chunkPoints (c : List ℤ) {G : ℕ} (hG : 0 < G) (es : Array Entry) (a₀ : ℤ)
    (len : ℕ) {bs : List ℕ} (hbs : bs.Nodup) :
    (chunkPoints c (BruteForce.degree c) G es a₀ len bs).Nodup := by
  have key {b : ℕ} {p : ℤ × ℤ × ℤ} {xs : List ℤ} {acc : ℕ}
      (h : p ∈ if acc == 0 then [] else pointsOfDen c (BruteForce.degree c) b xs) :
      p.2.2 = b := by
    split_ifs at h
    · simp at h
    · exact (mem_pointsOfDen_iff.mp h).2.1
  rw [chunkPoints, List.nodup_flatMap]
  refine ⟨fun b _ ↦ ?_, hbs.pairwise_of_forall_ne fun b _ b' _ hne p hp hp' ↦
    hne (by have := (key hp).symm.trans (key hp'); lia)⟩
  dsimp only
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

/-! ### The search -/

/-- The families that the search keeps are sound and short enough. -/
theorem isSound_of_mem_filter {c : List ℤ} {G L N : ℕ} {fams : Array Family}
    (hfams : ∀ F ∈ fams, F.IsSound c G N) {F : Family}
    (hF : F ∈ fams.filter fun F ↦ L + F.M ≤ N && F.rows.size == F.M && 0 < F.M) :
    F.IsSound c G N ∧ L + F.M ≤ N := by
  obtain ⟨hF, h⟩ := Array.mem_filter.mp hF
  exact ⟨hfams F hF, by simp only [Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1⟩

theorem rows_ne_zero {c : List ℤ} {G N : ℕ} {F : Family} (hF : F.IsSound c G N)
    (hN : F.M ≤ N) {a : ℤ} {b : ℕ} (hc : IsCandidate c a b) : F.rows[b % F.M]! ≠ 0 := by
  intro h0
  have := hF.testBit a b (F.shift a) ((F.shift_lt hF.pos a).trans_le hN) hc (F.dvd_sub_shift hF a)
  simp [h0] at this

theorem of_mem_search {c : List ℤ} {H G L N pre : ℕ} {fams : Array Family} {dens : List ℕ}
    (hG : 0 < G) {p : ℤ × ℤ × ℤ} (h : p ∈ search c (BruteForce.degree c) H G L N pre fams dens) :
    (∃ b ∈ dens, p.2.2 = b) ∧ |p.1| ≤ H ∧ Int.gcd p.1 p.2.2 = 1 ∧
      p.2.1 ^ 2 = binaryForm c p.1 p.2.2 := by
  simp only [search, List.mem_flatMap, List.mem_range, Prod.exists] at h
  obtain ⟨ρ, hρ, t₀, len, hch, hp⟩ := h
  obtain ⟨hcnt, hlen, -⟩ := le_of_mem_chunks hch
  obtain ⟨⟨b, hb, hz⟩, ⟨t, ht, hx⟩, hg, hy⟩ := of_mem_chunkPoints hp
  refine ⟨⟨b, (List.mem_filter.mp (List.mem_filter.mp hb).1).1, hz⟩, ?_, hg, hy⟩
  have := add_mul_lt_of_lt_classCount (n := 2 * H + 1) (ρ := ρ) (u := t₀ + t) hG (by lia)
  rw [hx, abs_le]
  push_cast
  constructor <;> lia

/-- The numerator `x` with `x + H = i` in the chunk of the class `i % G` that holds it. -/
theorem eq_sub_add_mul_of_natCast_eq {i G L H : ℕ} {x : ℤ} (hi : (i : ℤ) = x + H) :
    x = ((i % G + G * (i / G / L * L) : ℕ) : ℤ) - H + G * ((i / G % L : ℕ) : ℤ) := by
  have h1 : ((i % G : ℕ) : ℤ) + G * ((i / G : ℕ) : ℤ) = i := mod_cast Nat.mod_add_div i G
  have h2 : (L : ℤ) * ((i / G / L : ℕ) : ℤ) + ((i / G % L : ℕ) : ℤ) = ((i / G : ℕ) : ℤ) :=
    mod_cast Nat.div_add_mod (i / G) L
  simp only [Nat.cast_add, Nat.cast_mul]
  linear_combination (-1 : ℤ) * hi - h1 - (G : ℤ) * h2

theorem mem_search_of {c : List ℤ} {H G L N pre : ℕ} {fams : Array Family} {dens : List ℕ}
    (hG : 0 < G) (hL : 0 < L) (hfams : ∀ F ∈ fams, F.IsSound c G N) {p : ℤ × ℤ × ℤ} {b : ℕ}
    (hb : b ∈ dens) (hz : p.2.2 = b) (ha : |p.1| ≤ H) (hg : Int.gcd p.1 p.2.2 = 1)
    (hy : p.2.1 ^ 2 = binaryForm c p.1 p.2.2) :
    p ∈ search c (BruteForce.degree c) H G L N pre fams dens := by
  have hc : IsCandidate c p.1 b := ⟨hz ▸ hg, p.2.1, hz ▸ hy⟩
  obtain ⟨i, hi⟩ : ∃ i : ℕ, (i : ℤ) = p.1 + H := ⟨(p.1 + H).toNat, by rw [abs_le] at ha; lia⟩
  have hu : i / G < classCount (2 * H + 1) G (i % G) :=
    lt_classCount hG (by rw [abs_le] at ha; lia [Nat.mod_add_div i G])
  obtain ⟨t₀, len, hch, rfl, hlen⟩ := exists_mem_chunks hL hu
  simp only [search, List.mem_flatMap, List.mem_range, Prod.exists]
  refine ⟨i % G, Nat.mod_lt _ hG, _, len, hch, (mem_chunkPoints fun b t ht hc e he ↦
    testBit_entry_row_of_mem_entries (fun F hF ↦ isSound_of_mem_filter hfams hF)
      (le_of_mem_chunks hch).2.1 he ht hc).mpr ⟨⟨b, ?_, hz⟩, ⟨i / G % L, hlen,
        eq_sub_add_mul_of_natCast_eq hi⟩, hg, hy⟩⟩
  simp only [List.mem_filter, Array.all_eq_true_iff_forall_mem]
  refine ⟨⟨hb, fun F hF ↦ ?_⟩, ?_⟩
  · simpa using rows_ne_zero (isSound_of_mem_filter hfams hF).1 (by
      have := (isSound_of_mem_filter hfams hF).2; lia) hc
  · have := admitTable_spec hG hc
    rwa [eq_sub_add_mul_of_natCast_eq (L := 1) hi, Nat.cast_add, Nat.cast_mul, add_sub_right_comm,
      add_assoc, ← mul_add, Int.add_mul_emod_self_left] at this

theorem mem_search {c : List ℤ} {H G L N pre : ℕ} {fams : Array Family} {dens : List ℕ}
    (hG : 0 < G) (hL : 0 < L) (hfams : ∀ F ∈ fams, F.IsSound c G N) {p : ℤ × ℤ × ℤ} :
    p ∈ search c (BruteForce.degree c) H G L N pre fams dens ↔
      (∃ b ∈ dens, p.2.2 = b) ∧ |p.1| ≤ H ∧ Int.gcd p.1 p.2.2 = 1 ∧
        p.2.1 ^ 2 = binaryForm c p.1 p.2.2 :=
  ⟨of_mem_search hG, fun ⟨⟨_, hb, hz⟩, ha, hg, hy⟩ ↦ mem_search_of hG hL hfams hb hz ha hg hy⟩

theorem eq_of_add_mul_eq {G ρ ρ' u u' : ℕ} (hρ : ρ < G) (hρ' : ρ' < G)
    (h : ρ + G * u = ρ' + G * u') : ρ = ρ' ∧ u = u' := by
  have h1 := congrArg (· % G) h
  simp only [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hρ, Nat.mod_eq_of_lt hρ'] at h1
  subst h1
  exact ⟨rfl, Nat.eq_of_mul_eq_mul_left (n := G) (by lia) (by lia)⟩

theorem exists_index_of_mem_chunkPoints {c : List ℤ} {G H ρ t₀ len : ℕ} {es : Array Entry}
    {bs : List ℕ} {p : ℤ × ℤ × ℤ}
    (hp : p ∈ chunkPoints c (BruteForce.degree c) G es (((ρ + G * t₀ : ℕ) : ℤ) - H) len bs) :
    ∃ t < len, ∃ i : ℕ, (i : ℤ) = p.1 + H ∧ i = ρ + G * (t₀ + t) := by
  obtain ⟨t, ht, hx⟩ := (of_mem_chunkPoints hp).2.1
  exact ⟨t, ht, ρ + G * (t₀ + t), by rw [hx]; push_cast; ring, rfl⟩

theorem eq_of_add_mul_add_eq {G L ρ k k' t t' : ℕ} (hG : 0 < G) (hL : 0 < L) (ht : t < L)
    (ht' : t' < L) (h : ρ + G * (k * L + t) = ρ + G * (k' * L + t')) : k = k' := by
  have := congrArg (· / L) (Nat.eq_of_mul_eq_mul_left hG (Nat.add_left_cancel h))
  simpa [Nat.mul_comm k L, Nat.mul_comm k' L, Nat.mul_add_div hL, Nat.div_eq_of_lt ht,
    Nat.div_eq_of_lt ht'] using this

theorem nodup_search (c : List ℤ) (H G L N pre : ℕ) (fams : Array Family) {dens : List ℕ}
    (hG : 0 < G) (hL : 0 < L) (hdens : dens.Nodup) :
    (search c (BruteForce.degree c) H G L N pre fams dens).Nodup := by
  rw [search]
  refine List.nodup_flatMap.mpr ⟨fun ρ hρ ↦ ?_, List.nodup_range.pairwise_of_forall_ne
    fun ρ hρ ρ' hρ' hne p hp hp' ↦ hne ?_⟩
  · rw [chunks, List.flatMap_map]
    refine List.nodup_flatMap.mpr ⟨fun k _ ↦ nodup_chunkPoints c hG _ _ _
      ((hdens.filter _).filter _), List.nodup_range.pairwise_of_forall_ne
        fun k _ k' _ hne p hp hp' ↦ hne ?_⟩
    obtain ⟨t, ht, i, hi, rfl⟩ := exists_index_of_mem_chunkPoints hp
    obtain ⟨t', ht', i', hi', hii⟩ := exists_index_of_mem_chunkPoints hp'
    exact eq_of_add_mul_add_eq (ρ := ρ) hG hL (ht.trans_le (min_le_left _ _))
      (ht'.trans_le (min_le_left _ _)) (by lia)
  · simp only [List.mem_flatMap, Prod.exists] at hp hp'
    obtain ⟨t₀, len, -, hp⟩ := hp
    obtain ⟨t₀', len', -, hp'⟩ := hp'
    obtain ⟨t, -, i, hi, rfl⟩ := exists_index_of_mem_chunkPoints hp
    obtain ⟨t', -, i', hi', hii⟩ := exists_index_of_mem_chunkPoints hp'
    exact (eq_of_add_mul_eq (u := t₀ + t) (u' := t₀' + t') (List.mem_range.mp hρ)
      (List.mem_range.mp hρ') (by lia)).1

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

theorem isSound_of_mem_choose {tu : Tuning} {c : List ℤ} {H B : ℕ} {F : Family}
    (hF : F ∈ (choose tu c (BruteForce.degree c) H B).fams) :
    F.IsSound c (choose tu c (BruteForce.degree c) H B).G
      (choose tu c (BruteForce.degree c) H B).N := by
  simp only [choose, List.mem_toArray, List.mem_filterMap, List.mem_map, List.mem_mergeSort] at hF ⊢
  obtain ⟨g, ⟨x, hx, rfl⟩, hg⟩ := hF
  obtain ⟨g, hg', rfl⟩ := hx
  refine mkFamily_isSound (fun t ht ↦ ?_) hg
  obtain ⟨m, -, rfl⟩ := List.mem_map.mp (mem_of_mem_groupModuli hg' ht)
  rfl

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
  refine List.Nodup.append ?_ (nodup_search _ _ _ _ _ _ _ (choose_G_pos ..) (choose_L_pos ..)
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
