/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Fast.Search
public import Ratpoints.Proof.FastSieve
public import Ratpoints.Spec.Basic
public import Ratpoints.Spec.Region

import Mathlib.Data.List.Perm.Basic
import Mathlib.Tactic.IntervalCases
import Ratpoints.Proof.Containers

/-!
# The fast search on byte-array masks finds exactly the points

`Ratpoints.FastMask.fastPoints` lists the same points as `Ratpoints.Fast.fastPoints`, in another
order (`Ratpoints.FastMask.fastPoints_perm`), so it lists exactly the points of the region, each
once (`Ratpoints.FastMask.mem_fastPoints_iff`, `Ratpoints.FastMask.nodup_fastPoints`).

A mask is read as the natural number `Ratpoints.Mask.toNat`, whose bit `j` is bit `j` of the mask
(`Ratpoints.Mask.testBit_toNat`). The reference definitions of the two primitives then do what
the search on natural numbers does: `Ratpoints.Mask.andShr` is the AND with a row shifted to the
right (`Ratpoints.Mask.toNat_andShr`), and `Ratpoints.Mask.setBits`, on
`Ratpoints.Mask.nextSet`, lists the set bits in ascending order where `Ratpoints.Fast.setBits` lists
them in descending order (`Ratpoints.Mask.setBits_perm`). The periodic rows of
`Ratpoints.FastMask.baseRow` and `Ratpoints.Fast.baseRow` agree on the bits that a family keeps
(`Ratpoints.FastMask.testBit_toNat_baseRow`, `Ratpoints.Fast.testBit_baseRow_of_lt`), so the
families of the two searches agree once their rows are read as numbers
(`Ratpoints.FastMask.map_toFast_mkFamily`), and so do the parameters, the entries of a chunk and
the candidates that the sieve leaves (`Ratpoints.FastMask.toNat_sieveFrom_ones`).

## Main statements

* `Ratpoints.FastMask.fastPoints_perm`: the two searches list the same points.
* `Ratpoints.FastMask.mem_fastPoints_iff`: the list holds exactly the points of the region.
* `Ratpoints.FastMask.nodup_fastPoints`: each of them once.
-/

@[expose] public section

/-! ### Bytes and bits -/

@[simp]
theorem ByteArray.size_mk (d : Array UInt8) : (⟨d⟩ : ByteArray).size = d.size := rfl

@[simp]
theorem ByteArray.size_emptyWithCapacity (c : ℕ) : (ByteArray.emptyWithCapacity c).size = 0 :=
  rfl

theorem Nat.testBit_of_le_one {x : ℕ} (hx : x ≤ 1) (n : ℕ) :
    x.testBit n = (decide (n = 0) && decide (x = 1)) := by
  interval_cases x
  · simp
  · rw [Bool.eq_iff_iff, Nat.testBit_one_eq_true_iff_self_eq_zero]
    simp

namespace Ratpoints

/-! ### Masks as numbers -/

namespace Mask

/-- The mask `a` as a natural number, byte `i` of `a` standing for its value times `256 ^ i`: bit
`j` of it is `Ratpoints.Mask.bit a j` (`Ratpoints.Mask.testBit_toNat`). -/
def toNat (a : ByteArray) : ℕ := a.data.toList.foldr (fun (x : UInt8) n ↦ x.toNat + 256 * n) 0

theorem testBit_foldr (l : List UInt8) (j : ℕ) :
    (l.foldr (fun (x : UInt8) n ↦ x.toNat + 256 * n) 0).testBit j =
      (l.getD (j / 8) 0).toNat.testBit (j % 8) := by
  induction l generalizing j with
  | nil => simp
  | cons x l ih =>
    rw [List.foldr_cons, add_comm]
    refine (Nat.testBit_two_pow_mul_add _ x.toNat_lt j).trans ?_
    split_ifs with hj
    · simp [Nat.div_eq_of_lt hj, Nat.mod_eq_of_lt hj]
    · rw [ih, show j / 8 = (j - 8) / 8 + 1 by lia, show j % 8 = (j - 8) % 8 by lia]
      rfl

theorem byte_eq_toNat_getD (a : ByteArray) (i : ℕ) :
    byte a i = (a.data.toList.getD i 0).toNat := by
  rw [byte, List.getD_eq_getElem?_getD, Array.getElem?_toList]
  split_ifs with h
  · rw [Array.getElem?_eq_getElem h]
    rfl
  · rw [Array.getElem?_eq_none (Nat.not_lt.mp h)]
    rfl

theorem testBit_toNat (a : ByteArray) (j : ℕ) : (toNat a).testBit j = bit a j := by
  rw [toNat, testBit_foldr, bit, byte_eq_toNat_getD]

theorem byte_of_lt {a : ByteArray} {i : ℕ} (h : i < a.size) : byte a i = a[i].toNat := by
  simp [byte, h]

theorem byte_of_le {a : ByteArray} {i : ℕ} (h : a.size ≤ i) : byte a i = 0 := by
  simp [byte, Nat.not_lt.mpr h]

theorem byte_lt (a : ByteArray) (i : ℕ) : byte a i < 2 ^ 8 := by
  rw [byte]
  split_ifs
  · exact UInt8.toNat_lt _
  · exact Nat.two_pow_pos 8

theorem bit_of_le {a : ByteArray} {j : ℕ} (h : 8 * a.size ≤ j) : bit a j = false := by
  rw [bit, byte_of_le (by lia), Nat.zero_testBit]

theorem toNat_of_size_eq_zero {a : ByteArray} (h : a.size = 0) : toNat a = 0 :=
  Nat.eq_of_testBit_eq fun j ↦ by rw [testBit_toNat, bit_of_le (by lia), Nat.zero_testBit]

@[simp]
theorem toNat_empty : toNat .empty = 0 := toNat_of_size_eq_zero rfl

theorem toNat_eq_zero_iff (a : ByteArray) : toNat a = 0 ↔ ∀ j < 8 * a.size, bit a j = false := by
  refine ⟨fun h j _ ↦ by rw [← testBit_toNat, h, Nat.zero_testBit],
    fun h ↦ Nat.eq_of_testBit_eq fun j ↦ ?_⟩
  rw [testBit_toNat, Nat.zero_testBit]
  by_cases hj : j < 8 * a.size
  · exact h j hj
  · exact bit_of_le (by lia)

/-! ### The AND with a shifted row -/

theorem testBit_shrByte (row : ByteArray) (s i : ℕ) {t : ℕ} (ht : t < 8) :
    (shrByte row s i).toNat.testBit t = bit row (8 * i + t + s) := by
  rw [shrByte, UInt8.toNat_ofNat', Nat.testBit_mod_two_pow, decide_eq_true ht, Bool.true_and,
    Nat.testBit_shiftRight, add_comm (byte row _), Nat.testBit_two_pow_mul_add _ (byte_lt ..), bit]
  split_ifs with h
  · rw [show (8 * i + t + s) / 8 = s / 8 + i by lia, show (8 * i + t + s) % 8 = s % 8 + t by lia]
  · rw [show (8 * i + t + s) / 8 = s / 8 + i + 1 by lia,
      show (8 * i + t + s) % 8 = s % 8 + t - 8 by lia]

theorem bit_mapIdx_and_shrByte (acc row : ByteArray) (s j : ℕ) :
    bit ⟨acc.data.mapIdx fun i x ↦ x &&& shrByte row s i⟩ j = (bit acc j && bit row (j + s)) := by
  change (byte _ (j / 8)).testBit (j % 8) = ((byte acc (j / 8)).testBit (j % 8) && _)
  have hs : (⟨acc.data.mapIdx fun i x ↦ x &&& shrByte row s i⟩ : ByteArray).size = acc.size :=
    Array.size_mapIdx ..
  by_cases h : j / 8 < acc.size
  · rw [byte_of_lt (hs ▸ h), byte_of_lt h, ByteArray.getElem_eq_getElem_data, Array.getElem_mapIdx,
      UInt8.toNat_and, Nat.testBit_and, testBit_shrByte _ _ _ (Nat.mod_lt _ (by lia)),
      Nat.div_add_mod]
    rfl
  · rw [byte_of_le (by lia), byte_of_le (by lia), Nat.zero_testBit, Bool.false_and]

theorem bit_of_all {a : ByteArray} (h : a.data.all (· == 0) = true) (j : ℕ) : bit a j = false := by
  rw [bit, byte]
  split_ifs with hj
  · rw [ByteArray.getElem_eq_getElem_data, beq_iff_eq.mp (Array.all_eq_true.mp h (j / 8) hj),
      UInt8.toNat_zero, Nat.zero_testBit]
  · exact Nat.zero_testBit _

theorem bit_andShrSpec (acc row : ByteArray) (s j : ℕ) :
    bit (andShrSpec acc row s) j = (bit acc j && bit row (j + s)) := by
  rw [andShrSpec, ← bit_mapIdx_and_shrByte]
  split_ifs with h
  · rw [bit_of_all h, bit_of_le (by simp)]
  · rfl

/-- The primitive `Ratpoints.Mask.andShr` (by its reference definition) is the AND with the row
shifted to the right; no mask is needed, the bits of `acc` past its end being `0`. -/
theorem toNat_andShr (acc row : ByteArray) (s : ℕ) :
    toNat (andShr acc row s) = toNat acc &&& toNat row >>> s :=
  Nat.eq_of_testBit_eq fun j ↦ by
    rw [andShr, testBit_toNat, bit_andShrSpec, Nat.testBit_and, Nat.testBit_shiftRight,
      testBit_toNat, testBit_toNat, add_comm]

theorem bit_ones (len j : ℕ) : bit (ones len) j = decide (j < len) := by
  have hs : (ones len).size = 8 * ((len + 63) / 64) := Array.size_ofFn
  rw [bit]
  by_cases h : j / 8 < (ones len).size
  · rw [byte_of_lt h, ByteArray.getElem_eq_getElem_data]
    simp only [ones, Array.getElem_ofFn]
    split_ifs with h1 h2
    · rw [UInt8.toNat_ofNat_of_lt (by decide)]
      change (2 ^ 8 - 1).testBit (j % 8) = _
      rw [Nat.testBit_two_pow_sub_one, decide_eq_decide]
      lia
    · rw [UInt8.toNat_ofNat', Nat.testBit_mod_two_pow, Nat.testBit_two_pow_sub_one,
        decide_eq_true (Nat.mod_lt _ (by lia)), Bool.true_and, decide_eq_decide]
      lia
    · rw [UInt8.toNat_ofNat_of_lt (by decide), Nat.zero_testBit, eq_comm, decide_eq_false_iff_not]
      lia
  · rw [byte_of_le (by lia), Nat.zero_testBit, eq_comm, decide_eq_false_iff_not]
    lia

theorem toNat_ones (len : ℕ) : toNat (ones len) = 2 ^ len - 1 :=
  Nat.eq_of_testBit_eq fun j ↦ by rw [testBit_toNat, bit_ones, Nat.testBit_two_pow_sub_one]

/-! ### The set bits -/

theorem nextSetSpec_zero_eq_iff (a : ByteArray) :
    nextSetSpec a 0 = 8 * a.size ↔ ∀ j < 8 * a.size, bit a j = false := by
  rw [nextSetSpec, Nat.sub_zero]
  cases h : (List.range' 0 (8 * a.size)).find? (bit a) with
  | none =>
    simp only [List.find?_range'_eq_none] at h
    simpa using fun j hj ↦ h j (Nat.zero_le j) (by lia)
  | some k =>
    obtain ⟨hk, hmem, -⟩ := List.find?_range'_eq_some.mp h
    rw [List.mem_range'_1] at hmem
    simp only [Option.getD_some]
    exact iff_of_false (by lia) fun h' ↦ by simp [h' k (by lia)] at hk

theorem isZero_eq_beq (a : ByteArray) : isZero a = (toNat a == 0) := by
  refine Bool.eq_iff_iff.mpr ?_
  rw [isZero, nextSet, beq_iff_eq, toNat_eq_zero_iff, Bool.or_eq_true, beq_iff_eq, beq_iff_eq,
    nextSetSpec_zero_eq_iff]
  exact or_iff_right_of_imp fun h j hj ↦ by lia

theorem le_nextSetSpec (a : ByteArray) {j : ℕ} (h : nextSetSpec a j < 8 * a.size) :
    j ≤ nextSetSpec a j := by
  rw [nextSetSpec] at h ⊢
  cases hf : (List.range' j (8 * a.size - j)).find? (bit a) with
  | none => simp [hf] at h
  | some k => exact (List.mem_range'_1.mp (List.find?_range'_eq_some.mp hf).2.1).1

theorem bit_nextSetSpec (a : ByteArray) {j : ℕ} (h : nextSetSpec a j < 8 * a.size) :
    bit a (nextSetSpec a j) = true := by
  rw [nextSetSpec] at h ⊢
  cases hf : (List.range' j (8 * a.size - j)).find? (bit a) with
  | none => simp [hf] at h
  | some k => exact (List.find?_range'_eq_some.mp hf).1

theorem bit_of_lt_nextSetSpec (a : ByteArray) {i j : ℕ} (hj : j ≤ i) (hi : i < nextSetSpec a j) :
    bit a i = false := by
  rw [nextSetSpec] at hi
  cases hf : (List.range' j (8 * a.size - j)).find? (bit a) with
  | none =>
    rw [hf, Option.getD_none] at hi
    simpa using List.find?_range'_eq_none.mp hf i hj (by lia)
  | some k =>
    rw [hf, Option.getD_some] at hi
    simpa using (List.find?_range'_eq_some.mp hf).2.2 i hj hi

/-- With enough fuel, `Ratpoints.Mask.setBitsFrom a fuel j` lists the set bits of `a` from `j`
on. -/
theorem mem_setBitsFrom (a : ByteArray) {fuel j : ℕ} (h : 8 * a.size ≤ j + fuel) {t : ℕ} :
    t ∈ setBitsFrom a fuel j ↔ j ≤ t ∧ bit a t = true := by
  induction fuel generalizing j with
  | zero =>
    simp only [setBitsFrom, List.not_mem_nil, false_iff, not_and]
    exact fun _ ↦ by rw [bit_of_le (by lia)]; exact Bool.false_ne_true
  | succ fuel ih =>
    rw [setBitsFrom, nextSet]
    split_ifs with hk
    · rw [List.mem_cons, ih (by lia [le_nextSetSpec a hk])]
      refine ⟨fun h' ↦ h'.elim (fun ht ↦ ht ▸ ⟨le_nextSetSpec a hk, bit_nextSetSpec a hk⟩)
        fun h' ↦ ⟨by lia [le_nextSetSpec a hk], h'.2⟩, fun ⟨hjt, hbt⟩ ↦ ?_⟩
      rcases lt_trichotomy t (nextSetSpec a j) with htk | htk | htk
      · simp [bit_of_lt_nextSetSpec a hjt htk] at hbt
      · exact .inl htk
      · exact .inr ⟨htk, hbt⟩
    · simp only [List.not_mem_nil, false_iff, not_and]
      intro hjt hbt
      have : t < 8 * a.size := by
        by_contra! h'
        simp [bit_of_le h'] at hbt
      simp [bit_of_lt_nextSetSpec a hjt (by lia)] at hbt

theorem mem_setBits (a : ByteArray) {t : ℕ} : t ∈ setBits a ↔ (toNat a).testBit t := by
  rw [setBits, mem_setBitsFrom a (by lia), testBit_toNat]
  simp

theorem le_of_mem_setBitsFrom (a : ByteArray) {fuel j t : ℕ} (h : t ∈ setBitsFrom a fuel j) :
    j ≤ t := by
  induction fuel generalizing j with
  | zero => simp [setBitsFrom] at h
  | succ fuel ih =>
    rw [setBitsFrom, nextSet] at h
    split_ifs at h with hk
    · rcases List.mem_cons.mp h with rfl | h
      · exact le_nextSetSpec a hk
      · lia [le_nextSetSpec a hk, ih h]
    · simp at h

theorem nodup_setBitsFrom (a : ByteArray) (fuel j : ℕ) : (setBitsFrom a fuel j).Nodup := by
  induction fuel generalizing j with
  | zero => exact List.nodup_nil
  | succ fuel ih =>
    rw [setBitsFrom]
    split_ifs
    · exact List.nodup_cons.mpr ⟨fun h ↦ by lia [le_of_mem_setBitsFrom a h], ih _⟩
    · exact List.nodup_nil

theorem nodup_setBits (a : ByteArray) : (setBits a).Nodup := nodup_setBitsFrom ..

/-- `Ratpoints.Mask.setBits` lists the set bits in ascending order, `Ratpoints.Fast.setBits` in
descending order. -/
theorem setBits_perm (a : ByteArray) : (setBits a).Perm (Fast.setBits (toNat a)) :=
  (List.perm_ext_iff_of_nodup (nodup_setBits a) (Fast.nodup_setBits _)).mpr fun t ↦ by
    rw [mem_setBits, Fast.mem_setBits]

/-! ### Appending and extracting -/

theorem byte_append (a b : ByteArray) (i : ℕ) :
    byte (a ++ b) i = if i < a.size then byte a i else byte b (i - a.size) := by
  have hs := ByteArray.size_append (a := a) (b := b)
  split_ifs with h
  · rw [byte_of_lt (by lia), byte_of_lt h, ByteArray.getElem_append_left h]
  · by_cases h' : i < a.size + b.size
    · rw [byte_of_lt (by lia), byte_of_lt (by lia), ByteArray.getElem_append_right (by lia)]
    · rw [byte_of_le (by lia), byte_of_le (by lia)]

theorem byte_extract_zero (a : ByteArray) (n i : ℕ) :
    byte (a.extract 0 n) i = if i < n then byte a i else 0 := by
  have hs := ByteArray.size_extract (a := a) (b := 0) (e := n)
  by_cases h : i < min n a.size
  · rw [byte_of_lt (by lia), byte_of_lt (by lia), ByteArray.getElem_extract, ite_eq_left (by lia)]
    simp only [Nat.zero_add]
  · rw [byte_of_le (by lia)]
    split_ifs
    · rw [byte_of_le (by lia)]
    · rfl

end Mask

/-! ### The rows of the search on natural numbers -/

namespace Fast

theorem pattern_lt_two_pow (m : ℕ) (f : ℕ → Bool) : pattern m f < 2 ^ m :=
  Nat.lt_pow_two_of_testBit _ fun i hi ↦ by simp [testBit_pattern, Nat.not_lt.mpr hi]

theorem testBit_repeatPattern_of_lt_two_pow {P m : ℕ} (hP : P < 2 ^ m) (k j : ℕ) :
    (repeatPattern P m k).testBit j = (decide (j < m * 2 ^ k) && P.testBit (j % m)) := by
  induction k generalizing j with
  | zero =>
    rw [repeatPattern, pow_zero, mul_one]
    by_cases hj : j < m
    · simp [hj, Nat.mod_eq_of_lt hj]
    · have := Nat.pow_le_pow_right two_pos (Nat.not_lt.mp hj)
      simp [hj, Nat.testBit_lt_two_pow (hP.trans_le this)]
  | succ k ih =>
    rw [repeatPattern, Nat.testBit_or, Nat.testBit_shiftLeft, ih, ih, pow_succ]
    by_cases hj : j < m * 2 ^ k
    · simp [hj, show j < m * (2 ^ k * 2) by lia]
    · simp only [hj, decide_false, Bool.false_and, Bool.false_or, ge_iff_le,
        Nat.sub_mul_mod (Nat.not_lt.mp hj), decide_eq_true (Nat.not_lt.mp hj), Bool.true_and]
      congr 2
      exact propext (by lia)

/-- The bits below `N` of the row of a modulus, both ways (`Ratpoints.Fast.testBit_baseRow` has
one direction). -/
theorem testBit_baseRow_of_lt {T : Array (Array Bool)} {m G N r j : ℕ} (hm : 0 < m)
    (hj : j < N) : (baseRow T m G N r).testBit j = (T[r]!)[G * j % m]! := by
  rw [baseRow, testBit_repeatPattern_of_lt_two_pow (pattern_lt_two_pow ..), testBit_pattern,
    decide_eq_true ((le_mul_two_pow_doublings hm N).trans' hj), decide_eq_true (Nat.mod_lt _ hm),
    Bool.true_and, Bool.true_and, Nat.mul_mod_mod]

theorem testBit_foldl_and_eq {α : Type*} (g : α → ℕ) (l : List α) (init j : ℕ) :
    (l.foldl (fun acc x ↦ acc &&& g x) init).testBit j =
      (init.testBit j && l.all fun x ↦ (g x).testBit j) := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih => rw [List.foldl_cons, ih, Nat.testBit_and, List.all_cons, Bool.and_assoc]

theorem foldl_and_zero {α : Type*} (g : α → ℕ) (l : List α) :
    l.foldl (fun n x ↦ n &&& g x) 0 = 0 := by
  induction l with
  | nil => rfl
  | cons x l ih => rw [List.foldl_cons, Nat.zero_and, ih]

theorem setBits_zero : setBits 0 = [] :=
  List.eq_nil_iff_forall_not_mem.mpr fun t ht ↦ by simpa using mem_setBits.mp ht

end Fast

/-! ### The rows -/

namespace FastMask

open Mask

theorem size_repeatBytes (a : ByteArray) (k : ℕ) : (repeatBytes a k).size = a.size * 2 ^ k := by
  induction k with
  | zero => simp [repeatBytes]
  | succ k ih => rw [repeatBytes, ByteArray.size_append, ih, pow_succ, Nat.mul_two, Nat.mul_add]

theorem byte_repeatBytes (a : ByteArray) (k i : ℕ) :
    byte (repeatBytes a k) i = if i < a.size * 2 ^ k then byte a (i % a.size) else 0 := by
  induction k generalizing i with
  | zero =>
    simp only [repeatBytes, pow_zero, mul_one]
    split_ifs with h
    · rw [Nat.mod_eq_of_lt h]
    · exact byte_of_le (by lia)
  | succ k ih =>
    rw [repeatBytes, byte_append, size_repeatBytes, ih, ih, pow_succ]
    split_ifs <;> first | rfl | lia | rw [Nat.sub_mul_mod (by lia)]

theorem byte_extract_repeatBytes {a : ByteArray} {k n i : ℕ} (hn : n ≤ a.size * 2 ^ k)
    (hi : i < n) : byte ((repeatBytes a k).extract 0 n) i = byte a (i % a.size) := by
  rw [byte_extract_zero, ite_eq_left hi, byte_repeatBytes, ite_eq_left (by lia)]

/-- Bit `t` of `Ratpoints.FastMask.windowByte q o` is the byte `q[o + t]`, when each byte of `q` is
`0` or `1`. -/
theorem testBit_windowByte {q : ByteArray} (hq : ∀ i : ℕ, q[i]!.toNat ≤ 1) (o : ℕ) {t : ℕ}
    (ht : t < 8) : (windowByte q o).toNat.testBit t = decide (q[o + t]!.toNat = 1) := by
  simp only [windowByte, UInt8.toNat_or, UInt8.toNat_shiftLeft, Nat.testBit_or,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftLeft, Nat.testBit_of_le_one (hq _)]
  interval_cases t <;> simp

theorem size_patternBits (T' : Array Bool) (m G k : ℕ) (acc : ByteArray) :
    (patternBits T' m G k acc).size = acc.size + (m + 8 - k) := by
  fun_induction patternBits T' m G k acc with
  | case1 k acc hk ih => simp only [dite_eq_ite, ByteArray.size_push] at ih; lia
  | case2 k acc hk => lia

theorem getElem!_patternBits_of_lt (T' : Array Bool) (m G k : ℕ) (acc : ByteArray) {i : ℕ}
    (hi : i < acc.size) : (patternBits T' m G k acc)[i]! = acc[i]! := by
  fun_induction patternBits T' m G k acc with
  | case1 k acc hk ih =>
    simp only [dite_eq_ite, ByteArray.size_push] at ih
    rw [ih (by lia), ByteArray.getElem!_push_lt _ _ _ hi]
  | case2 k acc hk => rfl

theorem getElem!_patternBits (T' : Array Bool) (m G k : ℕ) (acc : ByteArray) {j : ℕ}
    (hk : k ≤ j) (hj : j < m + 8) :
    (patternBits T' m G k acc)[acc.size + (j - k)]! = if T'[G * (j % m) % m]! then 1 else 0 := by
  fun_induction patternBits T' m G k acc with
  | case1 k acc hk' ih =>
    simp only [dite_eq_ite, ByteArray.size_push] at ih
    rcases Nat.lt_or_ge k j with h | h
    · rw [← ih (by lia)]; congr 1; lia
    · obtain rfl : k = j := by lia
      simp only [Nat.sub_self, Nat.add_zero]
      rw [getElem!_patternBits_of_lt _ _ _ _ _ (by simp [ByteArray.size_push]),
        ByteArray.getElem!_push_eq]
  | case2 k acc hk' => lia


theorem size_periodBytes (q : ByteArray) (m i o : ℕ) (acc : ByteArray) :
    (periodBytes q m i o acc).size = acc.size + (m - i) := by
  fun_induction periodBytes q m i o acc with
  | case1 i o acc hi ih => simp only [ByteArray.size_push] at ih; lia
  | case2 i o acc hi => lia

theorem getElem!_periodBytes_of_lt (q : ByteArray) (m i o : ℕ) (acc : ByteArray) {i' : ℕ}
    (hi' : i' < acc.size) : (periodBytes q m i o acc)[i']! = acc[i']! := by
  fun_induction periodBytes q m i o acc with
  | case1 i o acc hi ih =>
    simp only [dite_eq_ite, ByteArray.size_push] at ih
    rw [ih (by lia), ByteArray.getElem!_push_lt _ _ _ hi']
  | case2 i o acc hi => rfl

theorem ite_add_eight_eq_mul_mod {m i o : ℕ} (ho : o = 8 * i % m) :
    (if o + 8 < m then o + 8 else (o + 8) % m) = 8 * (i + 1) % m := by
  have h : 8 * (i + 1) % m = (o + 8) % m := by rw [ho, Nat.mod_add_mod]; ring_nf
  split_ifs with h8
  · rw [h, Nat.mod_eq_of_lt h8]
  · exact h.symm

theorem getElem!_periodBytes (q : ByteArray) (m i o : ℕ) (acc : ByteArray) (ho : o = 8 * i % m)
    {j : ℕ} (hi : i ≤ j) (hj : j < m) :
    (periodBytes q m i o acc)[acc.size + (j - i)]! = windowByte q (8 * j % m) := by
  fun_induction periodBytes q m i o acc with
  | case1 i o acc hi' ih =>
    simp only [dite_eq_ite, ByteArray.size_push] at ih
    rcases Nat.lt_or_ge i j with h | h
    · rw [← ih (ite_add_eight_eq_mul_mod ho) (by lia)]; congr 1; lia
    · obtain rfl : i = j := by lia
      simp only [Nat.sub_self, Nat.add_zero]
      rw [getElem!_periodBytes_of_lt _ _ _ _ _ (by simp [ByteArray.size_push]),
        ByteArray.getElem!_push_eq, ho]
  | case2 i o acc hi' => lia


theorem getElem!_patternBits_zero (T' : Array Bool) (m G c j : ℕ) :
    (patternBits T' m G 0 (.emptyWithCapacity c))[j]! =
      if j < m + 8 then (if T'[G * (j % m) % m]! then 1 else 0) else 0 := by
  by_cases hj : j < m + 8
  · simp only [hj, ↓reduceIte]
    have := getElem!_patternBits T' m G 0 (.emptyWithCapacity c) (Nat.zero_le j) hj
    rwa [ByteArray.size_emptyWithCapacity, Nat.zero_add, Nat.sub_zero] at this
  · simp only [hj, ↓reduceIte]
    exact getElem!_neg _ _ (by simp [size_patternBits]; lia)

theorem toNat_getElem!_patternBits_le_one (T' : Array Bool) (m G c j : ℕ) :
    (patternBits T' m G 0 (.emptyWithCapacity c))[j]!.toNat ≤ 1 := by
  rw [getElem!_patternBits_zero]
  split_ifs <;> decide

private theorem mul_div_mod_mod_add_mod_mod (m j : ℕ) :
    (8 * (j / 8 % m) % m + j % 8) % m = j % m := by
  rw [Nat.mul_mod_mod, Nat.mod_add_mod, Nat.div_add_mod]

/-- The bits of the row of a modulus: the bits below `8 nb` of the periodic byte pattern. -/
theorem testBit_toNat_baseRow {T : Array (Array Bool)} {m G nb r j : ℕ} (hm : 0 < m)
    (hj : j < 8 * nb) : (toNat (baseRow T m G nb r)).testBit j = (T[r]!)[G * j % m]! := by
  have hn : nb ≤ m * 2 ^ (Nat.log2 (nb / m) + 1) := (Fast.le_mul_two_pow_doublings hm nb).le
  have hi : j / 8 % m < m := Nat.mod_lt _ hm
  rw [testBit_toNat, bit, baseRow]
  have hp : (periodBytes (patternBits T[r]! m G 0 (.emptyWithCapacity (m + 8))) m 0 0
      (.emptyWithCapacity m)).size = m := by simp [size_periodBytes]
  rw [byte_extract_repeatBytes (by rw [hp]; exact hn) (by lia), hp,
    byte_of_lt (by rw [hp]; exact hi), ← getElem!_pos,
    show j / 8 % m = (ByteArray.emptyWithCapacity m).size + (j / 8 % m - 0) by simp,
    getElem!_periodBytes _ m 0 0 _ rfl (Nat.zero_le _) hi,
    testBit_windowByte (toNat_getElem!_patternBits_le_one _ _ _ _) _ (Nat.mod_lt _ (by lia)),
    getElem!_patternBits_zero, ite_eq_left (by have := Nat.mod_lt (8 * (j / 8 % m)) hm; lia),
    mul_div_mod_mod_add_mod_mod, Nat.mul_mod_mod]
  split_ifs <;> simp_all

/-! ### The families -/

theorem testBit_toNat_foldl_andShr {α : Type*} (g : α → ByteArray) (l : List α)
    (init : ByteArray) (j : ℕ) :
    (toNat (l.foldl (fun acc x ↦ andShr acc (g x) 0) init)).testBit j =
      ((toNat init).testBit j && l.all fun x ↦ (toNat (g x)).testBit j) := by
  induction l generalizing init with
  | nil => simp
  | cons x l ih =>
    rw [List.foldl_cons, ih, toNat_andShr, Nat.shiftRight_zero, Nat.testBit_and, List.all_cons,
      Bool.and_assoc]

/-- The row of a family for the residue `r` is the same in both searches: the AND of the rows
of the moduli agrees on the bits below `N`, and the full mask clears the others. -/
theorem toNat_foldl_baseRow {G N : ℕ} {ts : List (ℕ × Array (Array Bool))}
    (hts : ∀ t ∈ ts, 0 < t.1) (r : ℕ) :
    toNat ((ts.map fun t ↦ (t.1, (List.range t.1).toArray.map
        (baseRow t.2 t.1 G (8 * ((N + 63) / 64))))).foldl
      (fun acc x ↦ andShr acc x.2[r % x.1]! 0) (ones N)) =
    (ts.map fun t ↦ (t.1, (List.range t.1).toArray.map (Fast.baseRow t.2 t.1 G N))).foldl
      (fun acc x ↦ acc &&& x.2[r % x.1]!) (2 ^ N - 1) := by
  refine Nat.eq_of_testBit_eq fun j ↦ ?_
  rw [testBit_toNat_foldl_andShr, Fast.testBit_foldl_and_eq, toNat_ones,
    Nat.testBit_two_pow_sub_one, List.all_map, List.all_map]
  by_cases hj : j < N
  · simp only [hj, decide_true, Bool.true_and, List.all_eq, decide_eq_decide,
      Function.comp_apply]
    refine forall₂_congr fun t ht ↦ ?_
    rw [Fast.getElem!_map_range _ (Nat.mod_lt _ (hts t ht)),
      Fast.getElem!_map_range _ (Nat.mod_lt _ (hts t ht)),
      testBit_toNat_baseRow (hts t ht) (by lia), Fast.testBit_baseRow_of_lt (hts t ht) hj]
  · simp [hj]

/-- The family `F` with its rows as natural numbers (`Ratpoints.Mask.toNat`): the family of
`Ratpoints.Fast` that `Ratpoints.Fast.mkFamily` makes where `Ratpoints.FastMask.mkFamily` makes
`F` (`Ratpoints.FastMask.map_toFast_mkFamily`). -/
def Family.toFast (F : Family) : Fast.Family := ⟨F.M, F.ginv, F.rows.map toNat⟩

@[simp]
theorem Family.toFast_M (F : Family) : F.toFast.M = F.M := rfl

@[simp]
theorem Family.toFast_rows (F : Family) : F.toFast.rows = F.rows.map toNat := rfl

@[simp]
theorem Family.shift_toFast (F : Family) (a₀ : ℤ) : F.toFast.shift a₀ = F.shift a₀ := rfl

theorem map_toFast_mkFamily (G N : ℕ) (ts : List (ℕ × Array (Array Bool))) :
    (mkFamily G N ts).map Family.toFast = Fast.mkFamily G N ts := by
  rw [mkFamily, Fast.mkFamily]
  split_ifs with h
  · dsimp only
    split <;> rename_i hf <;> simp only [hf]
    · rfl
    · simp only [Option.map_some, Family.toFast, Array.map_map, Option.some.injEq,
        Fast.Family.mk.injEq, true_and]
      refine Array.map_congr_left fun r _ ↦ ?_
      exact toNat_foldl_baseRow (by simpa using h) r
  · rfl

theorem map_toFast_fams_choose (tu : Fast.Tuning) (c : List ℤ) (d H B : ℕ) :
    (choose tu c d H B).fams.map Family.toFast = (Fast.choose tu c d H B).fams := by
  simp only [choose, Fast.choose, List.map_toArray, List.map_filterMap, map_toFast_mkFamily]

/-! ### The entries and the sieve -/

/-- The entry `e` with its rows as natural numbers (`Ratpoints.Mask.toNat`): the entry of
`Ratpoints.Fast` that `Ratpoints.Fast.entries` makes where `Ratpoints.FastMask.entries` makes `e`
(`Ratpoints.FastMask.map_toFast_entries`). -/
def Entry.toFast (e : Entry) : Fast.Entry := ⟨e.M, e.rows.map toNat, e.shift⟩

theorem map_toFast_entries (fams : Array Family) (nb : ℕ) (a₀ : ℤ) (len : ℕ) :
    (entries fams nb a₀ len).map Entry.toFast =
      Fast.entries (fams.map Family.toFast) nb a₀ len := by
  rw [entries, Fast.entries, Array.zipIdx_map, Array.map_map, Array.map_map]
  refine Array.map_congr_left fun ⟨F, i⟩ _ ↦ ?_
  simp only [Function.comp_apply, Prod.map_apply, id_eq, Family.toFast_M, Family.toFast_rows,
    Family.shift_toFast]
  by_cases h : (i + 1) * F.M ≤ nb
  · simp only [h, ↓reduceIte, Entry.toFast, Array.map_map, Fast.Entry.mk.injEq, true_and,
      and_true]
    exact Array.map_congr_left fun R _ ↦ by simp [toNat_andShr, toNat_ones, Nat.and_comm]
  · simp only [h, ↓reduceIte]
    rfl

theorem row_toFast (e : Entry) (b : ℕ) : e.toFast.row b = toNat e.rows[b % e.M]! >>> e.shift := by
  have hr : e.toFast.rows[b % e.toFast.M]! = toNat e.rows[b % e.M]! :=
    Array.getElem!_map toNat_empty ..
  rw [Fast.Entry.row, hr]
  split_ifs with h
  · rw [show e.shift = 0 from beq_iff_eq.mp h, Nat.shiftRight_zero]
  · rfl

/-- The sieve on masks, from position `i` on, with the zero tests of the search on natural numbers
dropped: an AND with `0` stays `0`. -/
theorem toNat_sieveFrom (es : Array Entry) (b : ℕ) (acc : ByteArray) (i : ℕ) :
    toNat (sieveFrom es b acc i) =
      (es.toList.drop i).foldl (fun n e ↦ n &&& toNat e.rows[b % e.M]! >>> e.shift)
        (toNat acc) := by
  fun_induction sieveFrom es b acc i with
  | case1 acc i h e acc' h0 =>
    rw [List.drop_eq_getElem_cons (by simpa using h), List.foldl_cons, Array.getElem_toList,
      ← toNat_andShr]
    change toNat acc' = List.foldl _ (toNat acc') _
    rw [toNat_of_size_eq_zero (beq_iff_eq.mp h0), Fast.foldl_and_zero]
  | case2 acc i h e acc' h0 ih =>
    rw [ih, List.drop_eq_getElem_cons (i := i) (by simpa using h), List.foldl_cons,
      Array.getElem_toList, ← toNat_andShr]
  | case3 acc i h => rw [List.drop_eq_nil_of_le (by simpa using h), List.foldl_nil]

theorem sieve_map_toFast (es : Array Entry) (mask b : ℕ) :
    Fast.sieve (es.map Entry.toFast) mask b =
      es.toList.foldl (fun n e ↦ n &&& toNat e.rows[b % e.M]! >>> e.shift) mask := by
  rw [Fast.sieve_eq_foldl, Array.toList_map, List.foldl_map]
  congr 1
  funext n e
  rw [row_toFast]
  split_ifs with h
  · rw [beq_iff_eq.mp h, Nat.zero_and]
  · rfl

theorem toNat_sieveFrom_ones (es : Array Entry) (b len : ℕ) :
    toNat (sieveFrom es b (ones len) 0) = Fast.sieve (es.map Entry.toFast) (2 ^ len - 1) b := by
  rw [toNat_sieveFrom, List.drop_zero, toNat_ones, sieve_map_toFast]

/-! ### The points -/

theorem hornerRec_eq_horner (w : List ℤ) (x : ℤ) : hornerRec w x = BruteForce.horner w x := by
  induction w with
  | nil => rfl
  | cons a w ih => rw [hornerRec, ih, BruteForce.horner, BruteForce.horner, List.foldr_cons]

theorem pointsOfDen_eq_pointsOfDen : FastMask.pointsOfDen = BruteForce.pointsOfDen := by
  funext c d z xs
  simp only [pointsOfDen, BruteForce.pointsOfDen, hornerRec_eq_horner]

theorem chunkPoints_perm (c : List ℤ) (d G : ℕ) (es : Array Entry) (a₀ : ℤ) (len : ℕ)
    (bs : List ℕ) :
    (chunkPoints c d G es a₀ len bs).Perm
      (Fast.chunkPoints c d G (es.map Entry.toFast) a₀ len bs) := by
  rw [chunkPoints, Fast.chunkPoints, pointsOfDen_eq_pointsOfDen]
  refine List.Perm.flatMap_left _ fun b _ ↦ ?_
  dsimp only
  rw [← toNat_sieveFrom_ones]
  generalize sieveFrom es b (ones len) 0 = acc
  rw [ite_eq_right_iff.mpr fun h ↦ ?_, ite_eq_right_iff.mpr fun h ↦ ?_]
  · exact ((setBits_perm acc).map _).flatMap_right _
  · rw [beq_iff_eq.mp h, Fast.setBits_zero]
    rfl
  · rw [setBits, beq_iff_eq.mp h]
    rfl

theorem all_map_toFast (fams : Array Family) (b : ℕ) :
    (fams.map Family.toFast).all (fun F ↦ F.rows[b % F.M]! != 0) =
      fams.all fun F ↦ !isZero F.rows[b % F.M]! := by
  rw [Array.all_map]
  congr 1
  funext F
  rw [Function.comp_apply, Family.toFast_rows, Family.toFast_M, Array.getElem!_map toNat_empty,
    isZero_eq_beq]
  rfl

theorem search_perm (c : List ℤ) (d H G L N pre : ℕ) (fams : Array Family) (dens : List ℕ) :
    (search c d H G L N pre fams dens).Perm
      (Fast.search c d H G L N pre (fams.map Family.toFast) dens) := by
  have hp : ((fun F : Fast.Family ↦ decide (L + F.M ≤ N) && F.rows.size == F.M &&
      decide (0 < F.M)) ∘ Family.toFast) =
      fun F ↦ decide (L + F.M ≤ N) && F.rows.size == F.M && decide (0 < F.M) := by
    funext F
    simp only [Function.comp_apply, Family.toFast_M, Family.toFast_rows, Array.size_map]
    rfl
  rw [search, Fast.search]
  dsimp only
  simp only [Array.filter_map, hp, all_map_toFast, ← map_toFast_entries]
  exact List.Perm.flatMap_left _ fun ρ _ ↦ List.Perm.flatMap_left _ fun x _ ↦ chunkPoints_perm ..

/-- **The search on byte-array masks lists the same points as the search on natural numbers**,
`Ratpoints.Fast.fastPoints`, in another order, for every coefficient list, every height bound,
every range and every setting of the parameters. -/
theorem fastPoints_perm (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ) (tu : Fast.Tuning) :
    (fastPoints c H bLow bHigh tu).Perm (Fast.fastPoints c H bLow bHigh tu) := by
  rw [fastPoints, Fast.fastPoints, pointsOfDen_eq_pointsOfDen, ← map_toFast_fams_choose]
  exact (search_perm ..).append_left _

/-- **The fast search lists exactly the points** of height at most `H` with their denominator in
the range of `bLow` and `bHigh`, for every coefficient list, every height bound, every range and
every setting of the parameters. -/
theorem mem_fastPoints_iff {c : List ℤ} {H : ℕ} {bLow bHigh : ℤ} {tu : Fast.Tuning}
    {p : ℤ × ℤ × ℤ} :
    p ∈ fastPoints c H bLow bHigh tu ↔ IsPoint c H p ∧ InRegion [] bLow bHigh p :=
  (fastPoints_perm ..).mem_iff.trans Fast.mem_fastPoints_iff

/-- **The fast search lists each point once.** -/
theorem nodup_fastPoints (c : List ℤ) (H : ℕ) (bLow bHigh : ℤ) (tu : Fast.Tuning) :
    (fastPoints c H bLow bHigh tu).Nodup :=
  (fastPoints_perm ..).nodup_iff.mpr (Fast.nodup_fastPoints ..)

end FastMask

end Ratpoints

end
