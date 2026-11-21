/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Fast.Search
public import Ratpoints.Proof.FastSieve

import Mathlib.Tactic.IntervalCases
import Ratpoints.Proof.Containers

/-!
# The masks, rows and families of the fast search

Facts about the masks and the rows of the fast search `Ratpoints.FastMask.fastPoints`. The search
lets every candidate (`Ratpoints.Fast.IsCandidate`) pass its filters, so only this direction is
proved about the rows.

A mask is a `ByteArray` whose bit `j` is `Ratpoints.Mask.bit`. The reference definitions of the
primitives do what their docstrings say: `Ratpoints.Mask.andRows` is the AND with all the shifted
rows (`Ratpoints.Mask.bit_andRows_eq_true`, from `Ratpoints.Mask.bit_andShr` for one row), its
result empty or of the size of the mask
(`Ratpoints.Mask.size_andRows_eq_zero_or_eq_size`), and `Ratpoints.Mask.setBits`, on
`Ratpoints.Mask.nextSet`, lists the set bits (`Ratpoints.Mask.mem_setBits`), each once
(`Ratpoints.Mask.nodup_setBits`).

Bit `j` of the row `Ratpoints.FastMask.baseRow` of a table is the entry of the table for the
residues of `G j` and of the denominator (`Ratpoints.FastMask.bit_baseRow`): the first bits are the
entries of the table read with the step `G` (`Ratpoints.FastMask.bit_stepBytes`), a period of `m`
bytes is made of windows of them (`Ratpoints.FastMask.bit_windowBytes`), and the row repeats the
period (`Ratpoints.FastMask.bit_extract_repeatBytes`). So the rows of a family of the tables of `c`
keep the bits of every candidate (`Ratpoints.FastMask.Family.IsSound`,
`Ratpoints.FastMask.mkFamily_isSound`, `Ratpoints.FastMask.trivialFamily_isSound`): the AND of the
rows of the tables keeps them, and a row with a set bit is not replaced by the empty array. The
shift `s` of a family to the start `a₀` of a chunk is below `8 M`, a multiple of `8`, and `G s ≡ a₀`
modulo `M` (`Ratpoints.FastMask.Family.shift_lt`, `Ratpoints.FastMask.Family.eight_dvd_shift`,
`Ratpoints.FastMask.Family.mul_shift_modEq`), so from it on the row has the bits of the candidates
of the chunk (`Ratpoints.FastMask.Family.IsSound.bit_shift_add`).

## Main definitions

* `Ratpoints.FastMask.Family.IsSound`: the rows of a family keep the bits of the candidates.

## Main statements

* `Ratpoints.FastMask.bit_baseRow`: the bits of the row of a table.
* `Ratpoints.FastMask.mkFamily_isSound`: the families of the tables of `c` are sound.
* `Ratpoints.FastMask.Family.IsSound.bit_shift_add`: a sound family keeps the bits of the
  candidates of a chunk.
-/

@[expose] public section

/-! ### Bytes, bits and lists -/

theorem Nat.testBit_of_le_one {x : ℕ} (hx : x ≤ 1) (n : ℕ) :
    x.testBit n = (decide (n = 0) && decide (x = 1)) := by
  interval_cases x
  · simp
  · rw [Bool.eq_iff_iff, Nat.testBit_one_eq_true_iff_self_eq_zero]
    simp

theorem Nat.lt_mul_two_pow_log2_div_add_one {m : ℕ} (hm : 0 < m) (N : ℕ) :
    N < m * 2 ^ (Nat.log2 (N / m) + 1) :=
  calc N < m * (N / m + 1) := Nat.lt_mul_div_succ N hm
    _ ≤ m * 2 ^ (Nat.log2 (N / m) + 1) := Nat.mul_le_mul_left m Nat.lt_log2_self

theorem UInt8.testBit_toNat_or_shiftLeft {f : ℕ → UInt8} (hf : ∀ k, (f k).toNat ≤ 1) {t : ℕ}
    (ht : t < 8) :
    (f 0 ||| f 1 <<< 1 ||| f 2 <<< 2 ||| f 3 <<< 3 ||| f 4 <<< 4 ||| f 5 <<< 5 ||| f 6 <<< 6 |||
      f 7 <<< 7).toNat.testBit t = (f t != 0) := by
  have h (k : ℕ) (u : ℕ) : (f k).toNat.testBit u = (decide (u = 0) && f k != 0) := by
    rw [Nat.testBit_of_le_one (hf k)]
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp (hf k) with h | h <;>
      simp [h, ← UInt8.toNat_inj]
  simp only [UInt8.toNat_or, UInt8.toNat_shiftLeft, Nat.testBit_or, Nat.testBit_mod_two_pow,
    Nat.testBit_shiftLeft, h]
  interval_cases t <;> simp

theorem List.dvd_foldl_mul {α M : Type*} [CommMonoid M] {f : α → M} {l : List α} {x : α}
    (hx : x ∈ l) : f x ∣ l.foldl (fun n y ↦ n * f y) 1 := by
  rw [← List.foldl_map (g := (· * ·)), ← List.prod_eq_foldl]
  exact List.dvd_prod (List.mem_map_of_mem hx)

theorem ByteArray.copySlice_eq_extract (src : ByteArray) {dest : ByteArray} (h : dest.size = 0)
    (off n : ℕ) (exact : Bool) : src.copySlice off dest 0 n exact = src.extract off (off + n) := by
  obtain ⟨d⟩ := dest
  obtain rfl : d = #[] := Array.eq_empty_of_size_eq_zero h
  simp [ByteArray.copySlice, ByteArray.extract]

namespace Ratpoints

namespace Mask

/-! ### The bits of a mask -/

theorem byte_of_lt {a : ByteArray} {i : ℕ} (h : i < a.size) : byte a i = a[i].toNat := by
  simp [byte, h]

theorem byte_of_le {a : ByteArray} {i : ℕ} (h : a.size ≤ i) : byte a i = 0 := by
  simp [byte, Nat.not_lt.mpr h]

theorem byte_lt (a : ByteArray) (i : ℕ) : byte a i < 2 ^ 8 := by
  rw [byte]
  split_ifs
  · exact UInt8.toNat_lt _
  · exact Nat.two_pow_pos 8

theorem byte_eq_toNat_getElem! (a : ByteArray) (i : ℕ) : byte a i = a[i]!.toNat := by
  by_cases h : i < a.size
  · rw [byte_of_lt h, getElem!_pos a i h]
  · rw [byte_of_le (by lia), getElem!_neg a i h]
    rfl

theorem bit_of_le {a : ByteArray} {j : ℕ} (h : 8 * a.size ≤ j) : bit a j = false := by
  rw [bit, byte_of_le (by lia), Nat.zero_testBit]

theorem bit_of_size_eq_zero {a : ByteArray} (h : a.size = 0) (j : ℕ) : bit a j = false :=
  bit_of_le (by lia)

theorem lt_of_bit {a : ByteArray} {j : ℕ} (h : bit a j = true) : j < 8 * a.size := by
  by_contra! h'
  simp [bit_of_le h'] at h

theorem size_pos_of_bit {a : ByteArray} {j : ℕ} (h : bit a j = true) : 0 < a.size :=
  Nat.pos_of_ne_zero fun h0 ↦ by simp [bit_of_size_eq_zero h0] at h

theorem byte_push (a : ByteArray) (x : UInt8) (i : ℕ) :
    byte (a.push x) i = if i = a.size then x.toNat else byte a i := by
  rw [byte_eq_toNat_getElem!, byte_eq_toNat_getElem!, ByteArray.getElem!_push]
  split_ifs <;> rfl

theorem bit_push_of_lt (a : ByteArray) (x : UInt8) {j : ℕ} (hj : j < 8 * a.size) :
    bit (a.push x) j = bit a j := by
  rw [bit, byte_push, ite_eq_right (by lia), bit]

theorem bit_push_size (a : ByteArray) (x : UInt8) {t : ℕ} (ht : t < 8) :
    bit (a.push x) (8 * a.size + t) = x.toNat.testBit t := by
  rw [bit, byte_push, ite_eq_left (by lia), show (8 * a.size + t) % 8 = t by lia]

theorem byte_append (a b : ByteArray) (i : ℕ) :
    byte (a ++ b) i = if i < a.size then byte a i else byte b (i - a.size) := by
  have hs := ByteArray.size_append (a := a) (b := b)
  split_ifs with h
  · rw [byte_of_lt (by lia), byte_of_lt h, ByteArray.getElem_append_left h]
  · by_cases h' : i < a.size + b.size
    · rw [byte_of_lt (by lia), byte_of_lt (by lia), ByteArray.getElem_append_right (by lia)]
    · rw [byte_of_le (by lia), byte_of_le (by lia)]

theorem byte_extract (a : ByteArray) (s e i : ℕ) :
    byte (a.extract s e) i = if s + i < e then byte a (s + i) else 0 := by
  have hs := ByteArray.size_extract (a := a) (b := s) (e := e)
  by_cases h : i < min e a.size - s
  · rw [byte_of_lt (by lia), byte_of_lt (by lia), ByteArray.getElem_extract, ite_eq_left (by lia)]
  · rw [byte_of_le (by lia)]
    split_ifs
    · rw [byte_of_le (by lia)]
    · rfl

theorem bit_extract (a : ByteArray) (s e j : ℕ) :
    bit (a.extract s e) j = (decide (s + j / 8 < e) && bit a (8 * s + j)) := by
  rw [bit, byte_extract, bit, show (8 * s + j) / 8 = s + j / 8 by lia,
    show (8 * s + j) % 8 = j % 8 by lia]
  split_ifs with h <;> simp [h]

theorem bit_mk_replicate (n : ℕ) {j : ℕ} (hj : j < 8 * n) :
    bit ⟨Array.replicate n 255⟩ j = true := by
  have key : ∀ t < 8, (255 : UInt8).toNat.testBit t = true := by decide
  rw [bit, byte_of_lt (by simp; lia), ByteArray.getElem_eq_getElem_data]
  simpa using key _ (Nat.mod_lt j (by decide))

/-! ### The AND with shifted rows -/

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

theorem bit_andShr (acc row : ByteArray) (s j : ℕ) :
    bit (andShr acc row s) j = (bit acc j && bit row (j + s)) := by
  rw [andShr, ← bit_mapIdx_and_shrByte]
  split_ifs with h
  · rw [bit_of_all h, bit_of_le (by simp)]
  · rfl

theorem size_andShr_eq_zero_or_eq_size (acc row : ByteArray) (s : ℕ) :
    (andShr acc row s).size = 0 ∨ (andShr acc row s).size = acc.size := by
  rw [andShr]
  split_ifs
  · exact .inl rfl
  · exact .inr (Array.size_mapIdx ..)

theorem bit_andRowsFrom (rs : Array ByteArray) (sh : Array ℕ) (o : ℕ) (acc : ByteArray)
    (i j : ℕ) :
    bit (andRowsFrom rs sh o acc i) j =
      (bit acc j && ((List.range rs.size).drop i).all fun k ↦ bit rs[k]! (j + sh[k]! + o)) := by
  fun_induction andRowsFrom rs sh o acc i with
  | case1 acc i h acc' h0 =>
    rw [List.drop_eq_getElem_cons (by simpa using h), List.all_cons, List.getElem_range,
      getElem!_pos rs i h, ← Bool.and_assoc, add_assoc, ← bit_andShr]
    change bit acc' j = (bit acc' j && _)
    rw [bit_of_size_eq_zero (beq_iff_eq.mp h0), Bool.false_and]
  | case2 acc i h acc' h0 ih =>
    rw [ih, List.drop_eq_getElem_cons (i := i) (by simpa using h), List.all_cons,
      List.getElem_range, getElem!_pos rs i h, ← Bool.and_assoc, add_assoc, ← bit_andShr]
  | case3 acc i h => rw [List.drop_eq_nil_of_le (by simpa using h), List.all_nil, Bool.and_true]

theorem size_andRowsFrom_eq_zero_or_eq_size (rs : Array ByteArray) (sh : Array ℕ) (o : ℕ)
    (acc : ByteArray) (i : ℕ) :
    (andRowsFrom rs sh o acc i).size = 0 ∨ (andRowsFrom rs sh o acc i).size = acc.size := by
  fun_induction andRowsFrom rs sh o acc i with
  | case1 acc i h acc' h0 => exact .inl (beq_iff_eq.mp h0)
  | case2 acc i h acc' h0 ih =>
    rcases size_andShr_eq_zero_or_eq_size acc rs[i] (sh[i]! + o) with h' | h'
    · exact absurd h' (by simpa using h0)
    · exact h' ▸ ih
  | case3 acc i h => exact .inr rfl

/-- A bit of the primitive `Ratpoints.Mask.andRows` (by its reference definition) is set exactly
when it is set in `acc` and in every shifted row. -/
theorem bit_andRows_eq_true {acc : ByteArray} {rs : Array ByteArray} {sh : Array ℕ} {o j : ℕ} :
    bit (andRows acc rs sh o) j = true ↔
      bit acc j = true ∧ ∀ k < rs.size, bit rs[k]! (j + sh[k]! + o) = true := by
  rw [andRows, bit_andRowsFrom, List.drop_zero, Bool.and_eq_true, List.all_eq_true]
  simp

theorem size_andRows_eq_zero_or_eq_size (acc : ByteArray) (rs : Array ByteArray) (sh : Array ℕ)
    (o : ℕ) :
    (andRows acc rs sh o).size = 0 ∨ (andRows acc rs sh o).size = acc.size :=
  size_andRowsFrom_eq_zero_or_eq_size ..

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

theorem isZero_eq_true {a : ByteArray} : isZero a = true ↔ ∀ j, bit a j = false := by
  rw [isZero, nextSet, Bool.or_eq_true, beq_iff_eq, beq_iff_eq, nextSetSpec_zero_eq_iff]
  refine ⟨fun h j ↦ ?_, fun h ↦ .inr fun j _ ↦ h j⟩
  by_cases hj : j < 8 * a.size
  · exact h.elim (fun h0 ↦ bit_of_size_eq_zero h0 j) fun h ↦ h j hj
  · exact bit_of_le (by lia)

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
      simp [bit_of_lt_nextSetSpec a hjt (by lia [lt_of_bit hbt])] at hbt

theorem mem_setBits {a : ByteArray} {t : ℕ} : t ∈ setBits a ↔ bit a t = true := by
  rw [setBits, mem_setBitsFrom a (by lia)]
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

theorem bit_ite_isZero (x : ByteArray) (j : ℕ) :
    bit (if isZero x then .empty else x) j = bit x j := by
  split_ifs with h
  · rw [bit_of_size_eq_zero rfl, isZero_eq_true.mp h]
  · rfl

theorem size_ite_isZero_andRows_eq_zero_or_eq_size (acc : ByteArray) (rs : Array ByteArray)
    (sh : Array ℕ) (o : ℕ) :
    (if isZero (andRows acc rs sh o) then .empty else andRows acc rs sh o).size = 0 ∨
      (if isZero (andRows acc rs sh o) then .empty else andRows acc rs sh o).size = acc.size := by
  split_ifs
  · exact .inl rfl
  · exact size_andRows_eq_zero_or_eq_size ..

theorem setBits_of_size_eq_zero {a : ByteArray} (h : a.size = 0) : setBits a = [] := by
  rw [setBits, h, Nat.mul_zero, setBitsFrom]

end Mask

namespace FastMask

open Fast Mask

/-! ### The rows of a table -/

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
  rw [byte_extract, ite_eq_left (by lia), Nat.zero_add, byte_repeatBytes, ite_eq_left (by lia)]

theorem bit_extract_repeatBytes {a : ByteArray} {k n j : ℕ} (hn : n ≤ a.size * 2 ^ k)
    (hj : j < 8 * n) :
    bit ((repeatBytes a k).extract 0 n) j = bit a (8 * (j / 8 % a.size) + j % 8) := by
  rw [bit, byte_extract_repeatBytes hn (by lia), bit, show (8 * (j / 8 % a.size) + j % 8) / 8 =
    j / 8 % a.size by lia, show (8 * (j / 8 % a.size) + j % 8) % 8 = j % 8 by lia]

/-- One step of `Ratpoints.FastMask.stepBytes`: a byte with the entries of `tab` at
`i, i + g, …, i + 7 g` modulo `m` as its bits (for entries `0` and `1`), and the index moved on by
`8 g`. -/
theorem exists_stepBytes_succ_eq {tab : ByteArray} (htab : ∀ i : ℕ, tab[i]!.toNat ≤ 1)
    {m g i : ℕ} (hg : g < m) (hi : i < m) (n : ℕ) (acc : ByteArray) :
    ∃ x : UInt8, (∀ t < 8, x.toNat.testBit t = (tab[(i + t * g) % m]! != 0)) ∧
      stepBytes tab m g (n + 1) i acc = stepBytes tab m g n ((i + 8 * g) % m) (acc.push x) := by
  have h1 : (if i + g < m then i + g else i + g - m) = (i + 1 * g) % m := by
    rw [Nat.ite_add_lt_eq_add_mod hi hg, one_mul]
  have hs (k : ℕ) : (if (i + k * g) % m + g < m then (i + k * g) % m + g
      else (i + k * g) % m + g - m) = (i + (k + 1) * g) % m := by
    rw [Nat.ite_add_lt_eq_add_mod (Nat.mod_lt _ (by lia)) hg, Nat.mod_add_mod, add_one_mul,
      add_assoc]
  simp only [stepBytes, h1, hs, ByteArray.get!_eq_getElem!]
  refine ⟨_, fun t ht ↦ ?_, rfl⟩
  have := UInt8.testBit_toNat_or_shiftLeft (f := fun k ↦ tab[(i + k * g) % m]!)
    (fun k ↦ htab _) ht
  simp only [zero_mul, add_zero, Nat.mod_eq_of_lt hi] at this
  exact this

theorem bit_stepBytes_of_lt (tab : ByteArray) (m g n i : ℕ) (acc : ByteArray) {j : ℕ}
    (hj : j < 8 * acc.size) : bit (stepBytes tab m g n i acc) j = bit acc j := by
  induction n generalizing i acc with
  | zero => rfl
  | succ n ih =>
    simp only [stepBytes]
    rw [ih _ _ (by simp; lia), bit_push_of_lt _ _ hj]

/-- Bit `j` of the bytes that `Ratpoints.FastMask.stepBytes` pushes is the entry of `tab` at
`i + j g` modulo `m`, for entries `0` and `1`. -/
theorem bit_stepBytes {tab : ByteArray} (htab : ∀ i : ℕ, tab[i]!.toNat ≤ 1) {m g : ℕ} (hg : g < m)
    (n : ℕ) {i : ℕ} (hi : i < m) (acc : ByteArray) {j : ℕ} (hj : j < 8 * n) :
    bit (stepBytes tab m g n i acc) (8 * acc.size + j) = (tab[(i + j * g) % m]! != 0) := by
  induction n generalizing i acc j with
  | zero => lia
  | succ n ih =>
    obtain ⟨x, hx, heq⟩ := exists_stepBytes_succ_eq htab hg hi n acc
    rw [heq]
    by_cases hj8 : j < 8
    · rw [bit_stepBytes_of_lt _ _ _ _ _ _ (by simp; lia), bit_push_size _ _ hj8, hx j hj8]
    · rw [show 8 * acc.size + j = 8 * (acc.push x).size + (j - 8) by simp; lia,
        ih (Nat.mod_lt _ (by lia)) _ (by lia), Nat.mod_add_mod, add_assoc, ← add_mul,
        show 8 + (j - 8) = j by lia]

theorem bit_stepBytes_zero {tab : ByteArray} (htab : ∀ i : ℕ, tab[i]!.toNat ≤ 1) {m g : ℕ}
    (hg : g < m) (n c : ℕ) {j : ℕ} (hj : j < 8 * n) :
    bit (stepBytes tab m g n 0 (.emptyWithCapacity c)) j = (tab[j * g % m]! != 0) := by
  have := bit_stepBytes htab hg n (Nat.zero_lt_of_lt hg) (.emptyWithCapacity c) hj
  rwa [ByteArray.size_emptyWithCapacity, mul_zero, zero_add, zero_add] at this

/-- One step of `Ratpoints.FastMask.windowBytes`: a byte with the bits `o, …, o + 7` of `p`, and
the position moved on by `8` modulo `m`. -/
theorem exists_windowBytes_succ_eq (p : ByteArray) (m n o : ℕ) (acc : ByteArray) :
    ∃ x : UInt8, (∀ t < 8, x.toNat.testBit t = bit p (o + t)) ∧
      windowBytes p m (n + 1) o acc = windowBytes p m n ((o + 8) % m) (acc.push x) := by
  refine ⟨_, fun t ht ↦ ?_, rfl⟩
  have hq : (o % 8).toUInt16.toNat % 16 = o % 8 := by simp; lia
  simp only [ByteArray.get!_eq_getElem!, ← byte_eq_toNat_getElem!, UInt16.toNat_toUInt8,
    UInt16.toNat_shiftRight, UInt16.toNat_or, UInt16.toNat_shiftLeft, UInt8.toNat_toUInt16,
    Nat.testBit_mod_two_pow, Nat.testBit_shiftRight, Nat.testBit_or, Nat.testBit_shiftLeft, hq,
    decide_eq_true ht, Bool.true_and]
  rw [bit]
  by_cases h : o % 8 + t < 8
  · rw [show (o + t) / 8 = o / 8 by lia, show (o + t) % 8 = o % 8 + t by lia]
    simp [show ¬ 8 ≤ o % 8 + t by lia]
  · rw [show (o + t) / 8 = o / 8 + 1 by lia, show (o + t) % 8 = o % 8 + t - 8 by lia,
      Nat.testBit_lt_two_pow ((byte_lt p _).trans_le (Nat.pow_le_pow_right two_pos (by lia)))]
    simp [show o % 8 + t < 16 by lia, show 8 ≤ o % 8 + t by lia]

theorem size_windowBytes (p : ByteArray) (m n o : ℕ) (acc : ByteArray) :
    (windowBytes p m n o acc).size = acc.size + n := by
  induction n generalizing o acc with
  | zero => rfl
  | succ n ih =>
    rw [windowBytes, ih, ByteArray.size_push]
    lia

theorem bit_windowBytes_of_lt (p : ByteArray) (m n o : ℕ) (acc : ByteArray) {j : ℕ}
    (hj : j < 8 * acc.size) : bit (windowBytes p m n o acc) j = bit acc j := by
  induction n generalizing o acc with
  | zero => rfl
  | succ n ih => rw [windowBytes, ih _ _ (by simp; lia), bit_push_of_lt _ _ hj]

/-- Byte `i` of the bytes that `Ratpoints.FastMask.windowBytes` pushes holds the bits of `p` from
`o + 8 i` modulo `m` on. -/
theorem bit_windowBytes (p : ByteArray) {m o : ℕ} (ho : o < m) (n : ℕ) (acc : ByteArray)
    {i t : ℕ} (hi : i < n) (ht : t < 8) :
    bit (windowBytes p m n o acc) (8 * acc.size + 8 * i + t) = bit p ((o + 8 * i) % m + t) := by
  induction n generalizing o acc i with
  | zero => lia
  | succ n ih =>
    obtain ⟨x, hx, heq⟩ := exists_windowBytes_succ_eq p m n o acc
    rw [heq]
    rcases i with _ | i
    · rw [mul_zero, add_zero, add_zero, bit_windowBytes_of_lt _ _ _ _ _ (by simp; lia),
        bit_push_size _ _ ht, hx t ht, Nat.mod_eq_of_lt ho]
    · rw [show 8 * acc.size + 8 * (i + 1) + t = 8 * (acc.push x).size + 8 * i + t by simp; lia,
        ih (Nat.mod_lt _ (by lia)) _ (by lia), Nat.mod_add_mod,
        show o + 8 + 8 * i = o + 8 * (i + 1) by ring]

theorem bit_windowBytes_zero (p : ByteArray) {m : ℕ} (hm : 0 < m) (c : ℕ) {j : ℕ}
    (hj : j < 8 * m) :
    bit (windowBytes p m m 0 (.emptyWithCapacity c)) j = bit p (8 * (j / 8) % m + j % 8) := by
  have := bit_windowBytes p hm m (.emptyWithCapacity c) (i := j / 8) (by lia)
    (Nat.mod_lt j (by lia))
  rwa [ByteArray.size_emptyWithCapacity, mul_zero, zero_add, Nat.div_add_mod] at this

theorem size_baseRow {T : Table} (hm : 0 < T.m) (G nb r : ℕ) : (baseRow T G nb r).size = nb := by
  simp only [baseRow, ByteArray.size_extract, size_repeatBytes, size_windowBytes,
    ByteArray.size_emptyWithCapacity, zero_add]
  lia [Nat.lt_mul_two_pow_log2_div_add_one hm nb]

private theorem mul_mod_add_mod_eight_mod (G m j : ℕ) :
    G * (8 * (j / 8 % m) % m + j % 8) % m = G * j % m := by
  refine Nat.ModEq.mul_left G ?_
  calc 8 * (j / 8 % m) % m + j % 8 ≡ 8 * (j / 8 % m) + j % 8 [MOD m] :=
        (Nat.mod_modEq _ m).add_right _
    _ ≡ 8 * (j / 8) + j % 8 [MOD m] := ((Nat.mod_modEq _ m).mul_left 8).add_right _
    _ = j := Nat.div_add_mod j 8

/-- The bits of the row of a table `T`: bit `j` is the entry of `T` for the residues of `G j` and
`r`, for a table whose rows have the entries `0` and `1`. -/
theorem bit_baseRow {T : Table} (hm : 0 < T.m) {r : ℕ} (hone : ∀ i : ℕ, T.one[i]!.toNat ≤ 1)
    (hsing : ∀ i : ℕ, (T.sing[r]!)[i]!.toNat ≤ 1) (G nb : ℕ) {j : ℕ} (hj : j < 8 * nb) :
    bit (baseRow T G nb r) j = T.admits (G * j % T.m) r := by
  have hj₂ : 8 * (j / 8 % T.m) % T.m + j % 8 < 8 * (T.m / 8 + 2) := by
    lia [Nat.mod_lt (8 * (j / 8 % T.m)) hm, Nat.mod_lt j (show 0 < 8 by decide)]
  have hmod := mul_mod_add_mod_eight_mod G T.m j
  have hn (p : ByteArray) : nb ≤ (windowBytes p T.m T.m 0 (.emptyWithCapacity T.m)).size *
      2 ^ (Nat.log2 (nb / T.m) + 1) := by
    rw [size_windowBytes, ByteArray.size_emptyWithCapacity, zero_add]
    exact (Nat.lt_mul_two_pow_log2_div_add_one hm nb).le
  simp only [baseRow]
  rw [bit_extract_repeatBytes (hn _) hj, size_windowBytes, ByteArray.size_emptyWithCapacity,
    zero_add, bit_windowBytes_zero _ hm _ (by lia [Nat.mod_lt (j / 8) hm]),
    show (8 * (j / 8 % T.m) + j % 8) / 8 = j / 8 % T.m by lia,
    show (8 * (j / 8 % T.m) + j % 8) % 8 = j % 8 by lia, Table.admits]
  generalize 8 * (j / 8 % T.m) % T.m + j % 8 = j₂ at hj₂ hmod ⊢
  split_ifs
  · rw [bit_stepBytes_zero hone (Nat.mod_lt _ hm) _ _ hj₂, ByteArray.get!_eq_getElem!,
      Nat.mul_mod_mod, show j₂ * (G * T.inv[r]!) = G * j₂ * T.inv[r]! by ring, ← Nat.mod_mul_mod,
      hmod]
  · rw [bit_stepBytes_zero hsing (Nat.mod_lt _ hm) _ _ hj₂, ByteArray.get!_eq_getElem!,
      Nat.mul_mod_mod, mul_comm, hmod]

theorem bit_baseRow_mkTable {c : List ℤ} {d m r : ℕ} (hm : 0 < m) (hr : r < m) (G nb : ℕ)
    {j : ℕ} (hj : j < 8 * nb) :
    bit (baseRow (mkTable c d m) G nb r) j = (mkTable c d m).admits (G * j % m) r :=
  bit_baseRow hm (toNat_getElem!_boolBytes_le_one _) (toNat_getElem!_sing_mkTable_le_one hr) G nb
    hj

/-- The row of a table of `c` with its modulus dividing `M`, for the residue of the denominator `b`
of a candidate `(a, b)`, has the bit `j` set when `G j ≡ a` modulo `M`. -/
theorem bit_baseRow_of_isCandidate {c : List ℤ} {T : Table}
    (hT : ∃ m > 0, T = mkTable c (BruteForce.degree c) m) {M G N : ℕ} (hTM : T.m ∣ M) {a : ℤ}
    {b j : ℕ} (hc : IsCandidate c a b) (hj : j < 8 * N) (hja : (G * j : ℤ) ≡ a [ZMOD M]) :
    bit (baseRow T G N (b % M % T.m)) j = true := by
  obtain ⟨m, hm, rfl⟩ := hT
  simp only [m_mkTable] at hTM ⊢
  rw [Nat.mod_mod_of_dvd _ hTM, bit_baseRow_mkTable hm (Nat.mod_lt _ hm) G N hj,
    natMod_eq_toNat_of_dvd (k := G * j) ((Int.natCast_dvd_natCast.mpr hTM).trans
      (by simpa using hja.dvd))]
  exact admits_mkTable_of_isCandidate hm hc

/-! ### Families -/

/-- The family `F` is sound for the coefficients `c`, the step `G` and masks of `nb` bytes: its
product `F.M` of the moduli is odd, `F.ginv` inverts `G` modulo `F.M`, there is a row for every
residue, each empty or of `F.M + nb` bytes, and the row of the denominator `b` of a candidate
`(a, b)` has the bit `j < 8 (F.M + nb)` set when `G j ≡ a` modulo `F.M`. -/
structure Family.IsSound (c : List ℤ) (G nb : ℕ) (F : Family) : Prop where
  /-- The product of the moduli is odd. -/
  odd : F.M % 2 = 1
  /-- `F.ginv` inverts `G`. -/
  mul_ginv : G * F.ginv % F.M = 1 % F.M
  /-- A row for every residue. -/
  size_rows : F.rows.size = F.M
  /-- Each row is empty or of `F.M + nb` bytes. -/
  size_row (b : ℕ) : F.rows[b % F.M]!.size = 0 ∨ F.rows[b % F.M]!.size = F.M + nb
  /-- The row of `b` keeps the bit `j` of every candidate `(a, b)` with `G j ≡ a`. -/
  bit_row {a : ℤ} {b : ℕ} (hc : IsCandidate c a b) {j : ℕ} (hj : j < 8 * (F.M + nb))
    (hja : (G * j : ℤ) ≡ a [ZMOD F.M]) : bit F.rows[b % F.M]! j = true

/-- The AND of the rows of the tables `T :: rest` of `c` with their moduli dividing `M`, for the
residue of the denominator `b` of a candidate `(a, b)`, has the bit `j` set when `G j ≡ a` modulo
`M`. -/
theorem bit_andRows_baseRow_of_isCandidate {c : List ℤ} {T : Table} {rest : List Table}
    (hts : ∀ T' ∈ T :: rest, ∃ m > 0, T' = mkTable c (BruteForce.degree c) m) {M G N : ℕ}
    (hdvd : ∀ T' ∈ T :: rest, T'.m ∣ M) {a : ℤ} {b j : ℕ} (hc : IsCandidate c a b)
    (hj : j < 8 * N) (hja : (G * j : ℤ) ≡ a [ZMOD M]) :
    bit (andRows ((List.range T.m).toArray.map (baseRow T G N))[b % M % T.m]!
      ((rest.toArray.map fun T' ↦ (T'.m, (List.range T'.m).toArray.map (baseRow T' G N))).map
        fun x ↦ x.2[b % M % x.1]!)
      ((rest.toArray.map fun T' ↦ (T'.m, (List.range T'.m).toArray.map (baseRow T' G N))).map
        fun _ ↦ 0) 0) j = true := by
  have hpos (T' : Table) (h' : T' ∈ T :: rest) : 0 < T'.m :=
    m_pos_of_exists_eq_mkTable (hts T' h')
  refine bit_andRows_eq_true.mpr ⟨?_, fun k hk ↦ ?_⟩
  · rw [Array.getElem!_map_toArray_range _ (Nat.mod_lt _ (hpos T List.mem_cons_self))]
    exact bit_baseRow_of_isCandidate (hts _ List.mem_cons_self) (hdvd _ List.mem_cons_self) hc hj
      hja
  · simp only [Array.size_map, List.size_toArray] at hk
    have hk' := List.mem_cons_of_mem T (List.getElem_mem hk)
    simp only [getElem!_pos, hk, Array.size_map, List.size_toArray, Array.getElem_map,
      List.getElem_toArray, add_zero]
    rw [Array.getElem!_map_toArray_range _ (Nat.mod_lt _ (hpos _ hk'))]
    exact bit_baseRow_of_isCandidate (hts _ hk') (hdvd _ hk') hc hj hja

theorem mkFamily_isSound {c : List ℤ} {G nb : ℕ} {ts : List Table}
    (hts : ∀ T ∈ ts, ∃ m > 0, T = mkTable c (BruteForce.degree c) m) {F : Family}
    (h : mkFamily G nb ts = some F) : F.IsSound c G nb := by
  rcases ts with _ | ⟨T, rest⟩
  · simp [mkFamily] at h
  have hdvd (T' : Table) (h' : T' ∈ T :: rest) : T'.m ∣ (T :: rest).foldl (· * ·.m) 1 :=
    List.dvd_foldl_mul h'
  simp only [mkFamily] at h
  generalize (T :: rest).foldl (· * ·.m) 1 = M at h hdvd
  split_ifs at h with hM
  split at h
  · simp at h
  rename_i hginv
  obtain rfl := (Option.some.inj h).symm
  have hT : 0 < T.m := m_pos_of_exists_eq_mkTable (hts T List.mem_cons_self)
  refine ⟨hM, by simpa using List.find?_some hginv, by simp, fun b ↦ ?_, fun hc j hj hja ↦ ?_⟩
  all_goals simp only [Array.getElem!_map_toArray_range _ (Nat.mod_lt _ (show 0 < M by lia)),
    bit_ite_isZero]
  · refine (size_ite_isZero_andRows_eq_zero_or_eq_size ..).imp id fun h ↦ h.trans ?_
    rw [Array.getElem!_map_toArray_range _ (Nat.mod_lt _ hT), size_baseRow hT]
  · exact bit_andRows_baseRow_of_isCandidate hts hdvd hc hj hja

theorem trivialFamily_isSound (c : List ℤ) (G nb : ℕ) : (trivialFamily nb).IsSound c G nb := by
  refine ⟨rfl, by simp [trivialFamily], rfl, fun b ↦ .inr ?_, fun _ j hj _ ↦ ?_⟩
  · simp only [trivialFamily, Nat.mod_one]
    simp [add_comm]
  · simp only [trivialFamily, Nat.mod_one] at hj ⊢
    simpa using bit_mk_replicate (nb + 1) (j := j) (by lia)

/-! ### The shift -/

theorem Family.shift_lt {F : Family} (hF : 0 < F.M) (a₀ : ℤ) : F.shift a₀ < 8 * F.M := by
  have hs : (a₀ * F.ginv % (F.M : ℤ)).toNat < F.M := by
    lia [Int.emod_lt_of_pos (a₀ * F.ginv) (Int.natCast_pos.mpr hF)]
  simp only [Family.shift]
  generalize (a₀ * F.ginv % (F.M : ℤ)).toNat = s at hs ⊢
  have h7 : (8 - s % 8) * F.M % 8 ≤ 7 := Nat.le_of_lt_succ (Nat.mod_lt _ (by decide))
  lia [Nat.mul_le_mul_left F.M h7]

-- `s` plus `M` times the residue of `(8 - s) M` modulo `8` is a multiple of `8` for odd `M`,
-- since `M ^ 2 ≡ 1` modulo `8`
private theorem eight_dvd_add_mul_mod {s M : ℕ} (hM : M % 2 = 1) :
    8 ∣ s + M * ((8 - s % 8) * M % 8) := by
  have key : ∀ u < 8, ∀ v < 8, v % 2 = 1 → (u + v * ((8 - u) % 8 * v % 8) % 8) % 8 = 0 := by
    decide
  rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, Nat.mul_mod M, Nat.mod_mod, Nat.mul_mod (8 - s % 8)]
  exact key (s % 8) (Nat.mod_lt _ (by decide)) (M % 8) (Nat.mod_lt _ (by decide)) (by lia)

theorem Family.eight_dvd_shift {F : Family} (hF : F.M % 2 = 1) (a₀ : ℤ) : 8 ∣ F.shift a₀ :=
  eight_dvd_add_mul_mod hF

theorem Family.mul_shift_modEq {G : ℕ} {F : Family} (hM : 0 < F.M)
    (h : G * F.ginv % F.M = 1 % F.M) (a₀ : ℤ) : (G * F.shift a₀ : ℤ) ≡ a₀ [ZMOD F.M] := by
  have hg : (G : ℤ) * F.ginv ≡ 1 [ZMOD F.M] := mod_cast (h : G * F.ginv ≡ 1 [MOD F.M])
  have hs : (G : ℤ) * (a₀ * F.ginv % F.M) ≡ a₀ [ZMOD F.M] :=
    calc (G : ℤ) * (a₀ * F.ginv % F.M) ≡ G * (a₀ * F.ginv) [ZMOD F.M] :=
          (Int.mod_modEq _ _).mul_left _
      _ = a₀ * (G * F.ginv) := by ring
      _ ≡ a₀ * 1 [ZMOD F.M] := hg.mul_left _
      _ = a₀ := mul_one a₀
  obtain ⟨k, hk⟩ : ∃ k, F.shift a₀ = (a₀ * F.ginv % (F.M : ℤ)).toNat + F.M * k := ⟨_, rfl⟩
  rw [hk]
  push_cast [Int.toNat_of_nonneg (Int.emod_nonneg (a₀ * F.ginv) (by lia : (F.M : ℤ) ≠ 0))]
  rw [mul_add, mul_left_comm]
  exact Int.modEq_add_fac_self.trans hs

/-- For a sound family and a candidate `(a₀ + G t, b)` with `t < 8 nb`, the row of `b` has the bit
`t` set from the shift of `a₀` on. -/
theorem Family.IsSound.bit_shift_add {c : List ℤ} {G nb : ℕ} {F : Family}
    (hF : F.IsSound c G nb) {a₀ : ℤ} {b t : ℕ} (ht : t < 8 * nb)
    (hc : IsCandidate c (a₀ + G * t) b) : bit F.rows[b % F.M]! (F.shift a₀ + t) = true := by
  have hM : 0 < F.M := by lia [hF.odd]
  refine hF.bit_row hc (by lia [F.shift_lt hM a₀]) ?_
  push_cast
  rw [mul_add]
  exact (Family.mul_shift_modEq hM hF.mul_ginv a₀).add_right _

theorem Family.IsSound.size_row_of_isCandidate {c : List ℤ} {G nb : ℕ} {F : Family}
    (hF : F.IsSound c G nb) {a : ℤ} {b : ℕ} (hc : IsCandidate c a b) :
    F.rows[b % F.M]!.size = F.M + nb := by
  have hM : 0 < F.M := by lia [hF.odd]
  have h := hF.bit_row hc (j := F.shift a) (by lia [F.shift_lt hM a])
    (Family.mul_shift_modEq hM hF.mul_ginv a)
  exact (hF.size_row b).resolve_left (size_pos_of_bit h).ne'

end FastMask

end Ratpoints

end
