/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.CliNumbers
public import Ratpoints.Proof.Rounding
public import Std.WP

import Mathlib.Algebra.Order.Field.Power
import Mathlib.Data.List.SplitBy
import Ratpoints.Mathlib.Order.WithBotTop
import Ratpoints.Proof.Containers
import Std.Tactic.Do

/-!
# The numbers and the search intervals of the program

The ends of the search intervals of the command line of `ratpoints-lean`, as
`Ratpoints.Model.CliNumbers` reads, compares and joins them. `strtod` never reads a NaN
(`Ratpoints.Cli.isNaN_strtod`); `outward` moves a double to the side of the end that its direction
asks, and onto the largest double at most a lower end when it starts close enough to it
(`Ratpoints.Cli.outward_spec`); so an end that `scan_end` reads has a double that is not a NaN,
outward of the end (`Ratpoints.Cli.inf_mem_and_isNaN_eq_false_and_le_of_run_scanEnd_eq_some`). For
a word of fewer than `2 ^ 56` characters, the double of a lower end is the largest double at most
the end (`Ratpoints.Cli.run_scanEnd_isMaxBelow`): the parts of the word give its exact value
(`Ratpoints.Cli.floatParts_bounds_and_isDigit_exponentDigits`, `Ratpoints.Cli.wordValue`), which
lies below the successor of the double that `strtod` reads (`Ratpoints.Cli.lt_nextUp_strtod`), and
the exponent that `scan_end` accumulates, which stops at `LONG_MAX / 20`, is the exact one for the
doubles that are finite and not zero (`Ratpoints.Cli.scanEndValue_eq_wordValue`). The ends of a
missing `-l` and `-u` lie beyond the height bound
(`Ratpoints.Cli.isFinite_heightEnd_and_le_toRat`). The comparisons `cmp_end` and `cmp_end_x`
compare the values (`Ratpoints.Cli.cmpEnd_neg_iff`, `Ratpoints.Cli.cmpEndX_neg_iff`), so that the
binary search of `in_region` over increasing and disjoint intervals decides the membership of
`x / z` (`Ratpoints.Cli.inRegion_spec`); and `join_intervals` keeps what the intervals hold and,
for intervals that join well, gives intervals that the library accepts
(`Ratpoints.Cli.joinIntervals_spec`).

## Main definitions

* `Ratpoints.Cli.ExactEnd.value`, `Ratpoints.Cli.InExactRegion`: the value of an exact end, and the
  exact search region of the command line.
* `Ratpoints.Cli.scanEndValue`, `Ratpoints.Cli.wordValue`: the end that `scan_end` takes, and the
  exact value of a floating constant.
* `Ratpoints.Cli.ChainEnds`: the ends of increasing and disjoint intervals `l ≤ u`.
* `Ratpoints.Cli.InPair`, `Ratpoints.Cli.NoNaN`, `Ratpoints.Cli.JoinsWell`: intervals of doubles.

## Main statements

* `Ratpoints.Cli.outward_spec`,
  `Ratpoints.Cli.inf_mem_and_isNaN_eq_false_and_le_of_run_scanEnd_eq_some`,
  `Ratpoints.Cli.run_scanEnd_isMaxBelow`, `Ratpoints.Cli.isFinite_heightEnd_and_le_toRat`: the
  doubles of the ends.
* `Ratpoints.Cli.lt_nextUp_strtod`: the exact value below the successor of the double of `strtod`.
* `Ratpoints.Cli.inRegion_spec`: the binary search.
* `Ratpoints.Cli.joinIntervals_spec`: the intervals that the library is given.

## Implementation notes

The contracts of the loops are proved with `vcgen`, as those of the model's other loops.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Cli

open Double

/-- The value of an exact end of a search interval of the command line
(`Ratpoints.Cli.ExactEnd`): `⊥` and `⊤` for the infinite ends, and its rational number
otherwise. -/
def ExactEnd.value (e : ExactEnd) : WithBotTop ℚ :=
  if e.inf < 0 then ⊥ else if 0 < e.inf then ⊤ else ((e.q : ℚ) : WithBotTop ℚ)

theorem cmpEnd_neg_iff {e f : ExactEnd} (he : e.inf = -1 ∨ e.inf = 0 ∨ e.inf = 1)
    (hf : f.inf = -1 ∨ f.inf = 0 ∨ f.inf = 1) : cmpEnd e f < 0 ↔ e.value < f.value := by
  rcases he with he | he | he <;> rcases hf with hf | hf | hf <;>
    simp only [cmpEnd, ExactEnd.value, he, hf] <;> norm_num
  split_ifs <;> simp_all [le_of_lt]

theorem cmpEnd_pos_iff {e f : ExactEnd} (he : e.inf = -1 ∨ e.inf = 0 ∨ e.inf = 1)
    (hf : f.inf = -1 ∨ f.inf = 0 ∨ f.inf = 1) : 0 < cmpEnd e f ↔ f.value < e.value := by
  rcases he with he | he | he <;> rcases hf with hf | hf | hf <;>
    simp only [cmpEnd, ExactEnd.value, he, hf] <;> norm_num
  split_ifs <;> simp_all [le_of_lt]

theorem isNaN_nearestBinary (neg : Bool) (m : ℕ) (t : ℤ) :
    (nearestBinary neg m t).isNaN = false := by
  simp only [nearestBinary]
  split_ifs <;>
    simp only [isNaN_ofRatio _ _ one_ne_zero, isNaN_ofDyadic, isNaN_huge, isNaN_huge_neg]

theorem isNaN_nearestDecimal (neg : Bool) (m : ℕ) (t : ℤ) :
    (nearestDecimal neg m t).isNaN = false := by
  simp only [nearestDecimal]
  split_ifs <;> simp only [isNaN_ofRatio _ _ one_ne_zero,
    isNaN_ofRatio _ _ (pow_ne_zero _ (by norm_num : (10 : ℕ) ≠ 0)), isNaN_huge, isNaN_huge_neg]

theorem isNaN_strtod (w : List Char) : (strtod w).isNaN = false := by
  simp only [strtod]
  split_ifs <;> simp only [isNaN_huge, isNaN_huge_neg, isNaN_nearestBinary, isNaN_nearestDecimal]

/-- The invariant of the loop of `Ratpoints.Cli.outward` from the double `x0` towards `v`, `dir < 0`
for a lower end, on the double `x`: it is not a NaN, an infinite `x` is that of the direction, at
the exit a finite `x` is on the side of `v` that the direction asks, and for a lower end, when `v`
lies below the successor of `x0`, every double at most `v` is at most `x`. -/
def OutwardInvariant (x0 : Double) (v : ℚ) (dir : ℤ) : Std.WP.WhileInvariant Double Prop :=
  .mk fun exit x ↦ x.isNaN = false ∧
    (x.isFinite = false →
      (dir < 0 → doubleValue x.bits = ⊥) ∧ (¬dir < 0 → doubleValue x.bits = ⊤)) ∧
    (exit = true → x.isFinite = true → if dir < 0 then x.toRat ≤ v else v ≤ x.toRat) ∧
    (dir < 0 → (v : WithBotTop ℚ) < doubleValue (nextUp x0).bits → ∀ y : Double,
      y.isNaN = false → doubleValue y.bits ≤ v → doubleValue y.bits ≤ doubleValue x.bits)

theorem outwardInvariant_start {x : Double} (v : ℚ) (dir : ℤ) (hf : x.isFinite = true) :
    OutwardInvariant x v dir false x := by
  have hx := isNaN_eq_false_of_isFinite hf
  refine ⟨hx, fun h ↦ absurd hf (by simp [h]), nofun, fun _ hv y hy hyv ↦ ?_⟩
  exact le_of_lt_nextUp hx hy (ne_huge_of_isFinite hf).1 (hyv.trans_lt hv)

theorem OutwardInvariant.exit_of_cond {x0 x : Double} {v : ℚ} {dir : ℤ} {k : ℕ}
    (hc : if dir < 0 then x.toRat ≤ v else v ≤ x.toRat)
    (h : (if dir < 0 then (x.orderValue + maxOrderValue).toNat
      else (maxOrderValue - x.orderValue).toNat) = k ∧ OutwardInvariant x0 v dir false x) :
    OutwardInvariant x0 v dir true x :=
  ⟨h.2.1, h.2.2.1, fun _ _ ↦ hc, h.2.2.2.2⟩

theorem OutwardInvariant.exit_of_not_isFinite {x0 x : Double} {v : ℚ} {dir : ℤ} {k : ℕ}
    (hf : ¬x.isFinite = true)
    (h : (if dir < 0 then (x.orderValue + maxOrderValue).toNat
      else (maxOrderValue - x.orderValue).toNat) = k ∧ OutwardInvariant x0 v dir false x) :
    OutwardInvariant x0 v dir true x :=
  ⟨h.2.1, h.2.2.1, fun _ h' ↦ absurd h' hf, h.2.2.2.2⟩

theorem OutwardInvariant.step {x0 x : Double} {v : ℚ} {dir : ℤ} {k : ℕ}
    (hf : x.isFinite = true) (hc : ¬if dir < 0 then x.toRat ≤ v else v ≤ x.toRat)
    (h : (if dir < 0 then (x.orderValue + maxOrderValue).toNat
      else (maxOrderValue - x.orderValue).toNat) = k ∧ OutwardInvariant x0 v dir false x) :
    (if dir < 0 then ((if dir < 0 then x.nextDown else x.nextUp).orderValue + maxOrderValue).toNat
      else (maxOrderValue - (if dir < 0 then x.nextDown else x.nextUp).orderValue).toNat) < k ∧
      OutwardInvariant x0 v dir false (if dir < 0 then x.nextDown else x.nextUp) := by
  obtain ⟨rfl, hx, -, -, hm⟩ := h
  have ho := (isFinite_iff_natAbs_orderValue_lt hx).mp hf
  obtain ⟨hi, hi'⟩ := ne_huge_of_isFinite hf
  by_cases hd : dir < 0
  · simp only [hd, ↓reduceIte, not_le] at hc ⊢
    obtain ⟨h1, h2⟩ := orderValue_nextDown hx hi'
    refine ⟨by rw [h1]; lia, h2, fun h ↦ ⟨fun _ ↦
      (isFinite_nextDown_or_doubleValue_eq_bot hf).resolve_left (by simp [h]),
      fun h' ↦ absurd hd h'⟩, nofun, fun _ hv y hy hyv ↦ le_nextDown_of_doubleValue_lt hx hy hi' ?_⟩
    rw [doubleValue_eq_toRat hf]; exact hyv.trans_lt (WithBotTop.coe_lt_coe.mpr hc)
  · simp only [hd, ↓reduceIte] at hc ⊢
    obtain ⟨h1, h2⟩ := orderValue_nextUp hx hi
    exact ⟨by rw [h1]; lia, h2, fun h ↦ ⟨fun h' ↦ absurd h' hd,
      fun _ ↦ (isFinite_nextUp_or_doubleValue_eq_top hf).resolve_left (by simp [h])⟩, nofun,
      fun h ↦ absurd h hd⟩

theorem OutwardInvariant.post {x0 x : Double} {v : ℚ} {dir : ℤ}
    (h : OutwardInvariant x0 v dir true x) :
    x.isNaN = false ∧ (dir < 0 → doubleValue x.bits ≤ v) ∧
      (¬dir < 0 → (v : WithBotTop ℚ) ≤ doubleValue x.bits) ∧
      (dir < 0 → (v : WithBotTop ℚ) < doubleValue (nextUp x0).bits → ∀ y : Double,
        y.isNaN = false → doubleValue y.bits ≤ v → doubleValue y.bits ≤ doubleValue x.bits) := by
  obtain ⟨hx, hinf, hc, hm⟩ := h
  refine ⟨hx, fun hd ↦ ?_, fun hd ↦ ?_, hm⟩ <;> cases hf : x.isFinite
  · rw [(hinf hf).1 hd]; exact bot_le
  · have := hc rfl hf; simp only [hd, ↓reduceIte] at this
    rw [doubleValue_eq_toRat hf]; exact WithBotTop.coe_le_coe.mpr this
  · rw [(hinf hf).2 hd]; exact le_top
  · have := hc rfl hf; simp only [hd, ↓reduceIte] at this
    rw [doubleValue_eq_toRat hf]; exact WithBotTop.coe_le_coe.mpr this

attribute [local irreducible] OutwardInvariant in
/-- `outward` moves the double `x` to the side of `v` that the direction asks, below `v` for a
lower end (`dir < 0`) and above it otherwise, and for a lower end it lands on the largest double at
most `v` when it starts from a double whose successor lies above `v`. -/
@[spec]
theorem outward_spec (x : Double) (v : ℚ) (dir : ℤ) :
    ⦃ x.isFinite = true ⦄ outward x v dir
    ⦃ fun r ↦ r.isNaN = false ∧ (dir < 0 → doubleValue r.bits ≤ v) ∧
      (¬dir < 0 → (v : WithBotTop ℚ) ≤ doubleValue r.bits) ∧
      (dir < 0 → (v : WithBotTop ℚ) < doubleValue (nextUp x).bits → ∀ y : Double,
        y.isNaN = false → doubleValue y.bits ≤ v → doubleValue y.bits ≤ doubleValue r.bits) ⦄ := by
  vcgen [outward] invariants
  · OutwardInvariant x v dir
  · Std.WP.Variant.ofMeasure fun x : Double ↦
      if dir < 0 then (x.orderValue + maxOrderValue).toNat else (maxOrderValue - x.orderValue).toNat
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals first
    | exact outwardInvariant_start v dir ‹_›
    | exact OutwardInvariant.post ‹_›
    | exact OutwardInvariant.exit_of_cond ‹_› ‹_›
    | exact OutwardInvariant.exit_of_not_isFinite ‹_› ‹_›
    | exact OutwardInvariant.step ‹_› ‹_› ‹_›

theorem run_outward {x : Double} (v : ℚ) (dir : ℤ) (hf : x.isFinite = true) :
    (Id.run (outward x v dir)).isNaN = false ∧
      (dir < 0 → doubleValue (Id.run (outward x v dir)).bits ≤ v) ∧
      (¬dir < 0 → (v : WithBotTop ℚ) ≤ doubleValue (Id.run (outward x v dir)).bits) ∧
      (dir < 0 → (v : WithBotTop ℚ) < doubleValue (nextUp x).bits → ∀ y : Double,
        y.isNaN = false → doubleValue y.bits ≤ v →
          doubleValue y.bits ≤ doubleValue (Id.run (outward x v dir)).bits) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((outward_spec x v dir).le_wp hf)

/-- The number `q` that `Ratpoints.Cli.scanEnd` takes as the end that the word `w` denotes, `x`
being the double that `strtod` reads from it, copied from `Ratpoints.Cli.scanEnd`
(`Ratpoints.Cli.eq_of_run_scanEnd_eq_some`). -/
def scanEndValue (w : List Char) (x : Double) : ℚ :=
  let (neg, hex, ds, k, rest) := floatParts w
  let (eneg, eds) := exponentDigits rest
  let ex : Int := eds.foldl (fun ex ch ↦
    if ex < (2 ^ 63 - 1) / 20 then 10 * ex + (ch.toNat - '0'.toNat) else ex) 0
  let ex := if eneg then -ex else ex
  let m := natOfDigitsIn (if hex then 16 else 10) ds
  let t := if hex then ex - 4 * k else ex - k
  let q : Rat :=
    if m = 0 then 0
    else if x.beq .zero then Double.zero.nextUp.toRat / 2
    else
      let p := (if hex then 2 else 10) ^ t.natAbs
      if 0 ≤ t then ((m * p : Nat) : Rat) else mkRat m p
  if neg then -q else q

theorem eq_some_of_scanDouble?_eq_some {s : String} {x : Double} (h : scanDouble? s = some x) :
    ∃ w, onlyWord? s = some w ∧ isDoubleWord w = true ∧ x = strtod w := by
  simp only [scanDouble?, Option.bind_eq_some_iff] at h
  obtain ⟨w, hw, h⟩ := h
  split at h
  · exact ⟨w, hw, ‹_›, (Option.some.inj h).symm⟩
  · cases h

theorem eq_of_run_scanEnd_eq_some {s : String} {dir : ℤ} {e : ExactEnd} {d : Double}
    (h : Id.run (scanEnd s dir) = some (e, d)) :
    ∃ w, onlyWord? s = some w ∧ isDoubleWord w = true ∧
      ((strtod w).isInf = true ∧ e = { inf := if Double.zero.lt (strtod w) then 1 else -1 } ∧
          d = strtod w ∨
        (strtod w).isInf = false ∧ e = { q := scanEndValue w (strtod w) } ∧
          d = Id.run (outward (strtod w) (scanEndValue w (strtod w)) dir)) := by
  rcases hx : scanDouble? s with _ | x
  · rw [scanEnd, hx] at h; cases h
  obtain ⟨w, hw, hd, rfl⟩ := eq_some_of_scanDouble?_eq_some hx
  refine ⟨w, hw, hd, ?_⟩
  rw [scanEnd, hx] at h
  dsimp only at h
  by_cases hi : (strtod w).isInf = true
  · rw [ite_eq_left hi] at h
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h)
    exact .inl ⟨hi, rfl, rfl⟩
  rw [ite_eq_right hi, hw] at h
  have h' : some ({ q := scanEndValue w (strtod w) },
      Id.run (outward (strtod w) (scanEndValue w (strtod w)) dir)) = some (e, d) := h
  obtain ⟨rfl, rfl⟩ := Prod.mk.inj (Option.some.inj h')
  exact .inr ⟨by simpa using hi, rfl, rfl⟩

theorem value_inf_eq_doubleValue {x : Double} (hi : x.isInf = true) :
    ExactEnd.value { inf := if Double.zero.lt x then 1 else -1 } = doubleValue x.bits := by
  rw [doubleValue_of_isInf hi, zero_lt_of_isInf hi]
  cases x.signBit <;> simp [ExactEnd.value]

/-- An end that `scan_end` reads: its `inf` is `-1`, `0` or `1`, its double is not a NaN, and it is
outward of the end, below a lower end and above an upper one. -/
theorem inf_mem_and_isNaN_eq_false_and_le_of_run_scanEnd_eq_some {s : String} {dir : ℤ}
    {e : ExactEnd} {d : Double} (h : Id.run (scanEnd s dir) = some (e, d)) :
    (e.inf = -1 ∨ e.inf = 0 ∨ e.inf = 1) ∧ d.isNaN = false ∧
      (dir < 0 → doubleValue d.bits ≤ e.value) ∧ (¬dir < 0 → e.value ≤ doubleValue d.bits) := by
  obtain ⟨w, -, -, ⟨hi, rfl, rfl⟩ | ⟨hi, rfl, rfl⟩⟩ := eq_of_run_scanEnd_eq_some h
  · refine ⟨by split <;> simp, isNaN_strtod w, fun _ ↦ ?_, fun _ ↦ ?_⟩ <;>
      rw [value_inf_eq_doubleValue hi]
  · obtain ⟨h1, h2, h3, -⟩ := run_outward (scanEndValue w (strtod w)) dir
      (isFinite_of_isInf_eq_false (isNaN_strtod w) hi)
    exact ⟨by simp, h1, fun hd ↦ by simpa [ExactEnd.value] using h2 hd,
      fun hd ↦ by simpa [ExactEnd.value] using h3 hd⟩

/-- The end of a missing first `-l` (negated) and of a missing last `-u` for a height bound
`1 ≤ H < 2 ^ 63` is a finite double of a value at least `H`. -/
theorem isFinite_heightEnd_and_le_toRat {H : ℕ} (hH : 1 ≤ H) (hH63 : H < 2 ^ 63) :
    (heightEnd H).isFinite = true ∧ (H : ℚ) ≤ (heightEnd H).toRat :=
  isFinite_and_le_toRat_ofInt64_nextUp hH hH63

/-! ### The largest double below a lower end -/

/-- The digits that `Ratpoints.Cli.mantissaDigits` takes from `s`: as many after the point at most
as in all, no more than the characters of `s`, all digits, and the rest of `s` without the digits
and the points. -/
theorem mantissaDigits_bounds_and_eq_dropWhile (isDigit : Char → Bool) (point : Bool)
    (s : List Char) :
    (mantissaDigits isDigit point s).2.1 ≤ (mantissaDigits isDigit point s).1.length ∧
      (mantissaDigits isDigit point s).1.length ≤ s.length ∧
      (∀ ch ∈ (mantissaDigits isDigit point s).1, isDigit ch = true) ∧
      (mantissaDigits isDigit point s).2.2 = s.dropWhile fun ch ↦ isDigit ch || ch == '.' := by
  fun_induction mantissaDigits isDigit point s with
  | case1 point s ih =>
    obtain ⟨h1, h2, h3, h4⟩ := ih
    exact ⟨h1, by simp; lia, h3, by simp [h4]⟩
  | case2 point ch s hc hd ds k rest he ih =>
    rw [he] at ih
    obtain ⟨h1, h2, h3, h4⟩ := ih
    refine ⟨by split <;> simp <;> lia, by simp; lia, ?_, ?_⟩
    · simp only [List.mem_cons]; rintro c (rfl | hc'); exacts [hd, h3 c hc']
    · simpa [hd] using h4
  | case3 point ch s hc hd => simp [hd, show ch ≠ '.' from hc]
  | case4 => simp

theorem length_dropSign_le (w : List Char) : (dropSign w).length ≤ w.length := by
  fun_cases dropSign w <;> simp

theorem exponentDigits_snd_isDigit {isD : Char → Bool} {exp : List Char} {s : List Char}
    (hexp : ∀ x ∈ exp, "eEpP".contains x = true) (h : isFloatBody isD exp s = true) :
    ∀ ch ∈ (exponentDigits (s.dropWhile fun ch ↦ isD ch || ch == '.')).2, ch.isDigit = true := by
  simp only [isFloatBody, List.span_eq_takeWhile_dropWhile, Bool.and_eq_true] at h
  obtain ⟨-, he⟩ := h
  generalize s.dropWhile (fun ch ↦ isD ch || ch == '.') = e at he ⊢
  rcases e with _ | ⟨x, t⟩
  · simp [exponentDigits]
  simp only [Bool.and_eq_true, List.contains_iff_mem, isDigits, Bool.not_eq_true',
    List.isEmpty_eq_false_iff, List.all_eq_true] at he
  intro ch hch
  simp only [exponentDigits, hexp x he.1, ↓reduceIte] at hch
  split at hch
  · exact he.2.2 ch hch
  · exact he.2.2 ch hch
  · rename_i h1 h2
    exact he.2.2 ch (by rwa [dropSign.eq_3 _ h1 h2])

theorem digitValue_of_isDigit {ch : Char} (h : ch.isDigit = true) :
    digitValue ch = ch.toNat - '0'.toNat := by
  simp [digitValue, h]

theorem digitValue_lt_ten {ch : Char} (h : ch.isDigit = true) : digitValue ch < 10 := by
  rw [digitValue_of_isDigit h]
  simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le] at h
  simp only [Char.toNat, show '0'.val.toNat = 48 from rfl] at h ⊢
  have : '9'.val.toNat = 57 := rfl
  lia

theorem digitValue_lt_sixteen {ch : Char} (h : ch.isHexDigit = true) : digitValue ch < 16 := by
  by_cases hd : ch.isDigit = true
  · exact (digitValue_lt_ten hd).trans (by decide)
  simp only [Char.isHexDigit, hd, Bool.false_or, Bool.or_eq_true, Bool.and_eq_true,
    decide_eq_true_eq, UInt32.le_iff_toNat_le] at h
  simp only [digitValue, hd, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true, decide_eq_true_eq,
    Char.le_def, UInt32.le_iff_toNat_le, Char.toNat]
  have h1 : 'a'.val.toNat = 97 := rfl
  have h2 : 'f'.val.toNat = 102 := rfl
  have h3 : 'A'.val.toNat = 65 := rfl
  have h4 : 'F'.val.toNat = 70 := rfl
  simp only [h1, h2, h3, h4] at h ⊢
  split_ifs <;> lia

theorem foldl_digits_lt (b : ℕ) {ds : List Char} (h : ∀ ch ∈ ds, digitValue ch < b) (n : ℕ) :
    ds.foldl (fun n ch ↦ b * n + digitValue ch) n < (n + 1) * b ^ ds.length := by
  induction ds generalizing n with
  | nil => simp
  | cons ch ds ih =>
    rw [List.foldl_cons, List.length_cons, pow_succ]
    have h1 := ih (fun c hc ↦ h c (.tail _ hc)) (b * n + digitValue ch)
    have h2 := h ch (.head _)
    calc _ < _ := h1
      _ ≤ (b * (n + 1)) * b ^ ds.length := Nat.mul_le_mul_right _ (by lia)
      _ = _ := by ring

theorem natOfDigitsIn_lt (b : ℕ) {ds : List Char} (h : ∀ ch ∈ ds, digitValue ch < b) :
    natOfDigitsIn b ds < b ^ ds.length := by
  simpa [natOfDigitsIn] using foldl_digits_lt b h 0

theorem le_foldl_digits (b : ℕ) (hb : 1 ≤ b) (ds : List Char) (n : ℕ) :
    n ≤ ds.foldl (fun n ch ↦ b * n + digitValue ch) n := by
  induction ds generalizing n with
  | nil => simp
  | cons ch ds ih =>
    rw [List.foldl_cons]
    exact ((Nat.le_mul_of_pos_left n hb).trans (Nat.le_add_right _ _)).trans (ih _)

/-- The exponent that `scan_end` accumulates, which stops taking digits once it reaches `L`, is the
exponent of the digits when that lies below `L`. -/
theorem foldl_capped_eq {L : ℤ} {ds : List Char} (h : ∀ ch ∈ ds, ch.isDigit = true) (n : ℕ)
    (hlt : ((ds.foldl (fun n ch ↦ 10 * n + digitValue ch) n : ℕ) : ℤ) < L) :
    ds.foldl (fun ex ch ↦ if ex < L then 10 * ex + ((ch.toNat : ℤ) - '0'.toNat) else ex) (n : ℤ) =
      ((ds.foldl (fun n ch ↦ 10 * n + digitValue ch) n : ℕ) : ℤ) := by
  induction ds generalizing n with
  | nil => simp
  | cons ch ds ih =>
    rw [List.foldl_cons, List.foldl_cons] at *
    have hn := le_foldl_digits 10 (by decide) ds (10 * n + digitValue ch)
    have hch := h ch (.head _)
    have hd := digitValue_of_isDigit hch
    have h48 : '0'.toNat ≤ ch.toNat := by
      simp only [Char.isDigit, Bool.and_eq_true, decide_eq_true_eq, UInt32.le_iff_toNat_le] at hch
      exact hch.1
    rw [ite_eq_left (by lia), show 10 * (n : ℤ) + ((ch.toNat : ℤ) - '0'.toNat) =
      ((10 * n + digitValue ch : ℕ) : ℤ) by push_cast; rw [hd]; lia]
    exact ih (fun c hc ↦ h c (.tail _ hc)) _ hlt

theorem nearestBinary_eq {neg : Bool} {m : ℕ} {t : ℤ} (hf : (nearestBinary neg m t).isFinite)
    (hz : (nearestBinary neg m t).beq .zero = false) :
    m ≠ 0 ∧ (m.log2 : ℤ) + t < 1024 ∧ -1075 < (m.log2 : ℤ) + 1 + t ∧
      nearestBinary neg m t = ofDyadic neg m t := by
  by_cases h1 : m = 0
  · rw [nearestBinary, ite_eq_left h1, beq_zero_ofRatio_zero] at hz; cases hz
  by_cases h2 : 1024 ≤ (m.log2 : ℤ) + t
  · rw [nearestBinary, ite_eq_right h1, ite_eq_left h2, isFinite_ite_huge] at hf; cases hf
  by_cases h3 : (m.log2 : ℤ) + 1 + t ≤ -1075
  · rw [nearestBinary, ite_eq_right h1, ite_eq_right h2, ite_eq_left h3,
      beq_zero_ofRatio_zero] at hz
    cases hz
  exact ⟨h1, by lia, by lia,
    by rw [nearestBinary, ite_eq_right h1, ite_eq_right h2, ite_eq_right h3]⟩

theorem nearestDecimal_eq {neg : Bool} {m : ℕ} {t : ℤ} (hf : (nearestDecimal neg m t).isFinite)
    (hz : (nearestDecimal neg m t).beq .zero = false) :
    m ≠ 0 ∧ (0 ≤ t → (m.log2 : ℤ) + 3 * t < 1024 ∧
        nearestDecimal neg m t = ofRatio neg (m * 10 ^ t.toNat) 1) ∧
      (t < 0 → 3 * -t < (m.log2 : ℤ) + 1076 ∧
        nearestDecimal neg m t = ofRatio neg m (10 ^ (-t).toNat)) := by
  by_cases h1 : m = 0
  · rw [nearestDecimal, ite_eq_left h1, beq_zero_ofRatio_zero] at hz; cases hz
  refine ⟨h1, fun h2 ↦ ?_, fun h2 ↦ ?_⟩
  · by_cases h3 : 1024 ≤ (m.log2 : ℤ) + 3 * t
    · rw [nearestDecimal, ite_eq_right h1, ite_eq_left h2, ite_eq_left h3, isFinite_ite_huge] at hf
      cases hf
    exact ⟨by lia, by rw [nearestDecimal, ite_eq_right h1, ite_eq_left h2, ite_eq_right h3]⟩
  · by_cases h3 : (m.log2 : ℤ) + 1076 ≤ 3 * -t
    · rw [nearestDecimal, ite_eq_right h1, ite_eq_right (show ¬0 ≤ t by lia), ite_eq_left h3,
        beq_zero_ofRatio_zero] at hz
      cases hz
    exact ⟨by lia, by rw [nearestDecimal, ite_eq_right h1, ite_eq_right (show ¬0 ≤ t by lia),
      ite_eq_right h3]⟩

theorem lt_nextUp_nearestBinary {neg : Bool} {m : ℕ} {t : ℤ}
    (hf : (nearestBinary neg m t).isFinite) (hz : (nearestBinary neg m t).beq .zero = false) :
    ((if neg then -((m : ℚ) * 2 ^ t) else (m : ℚ) * 2 ^ t : ℚ) : WithBotTop ℚ) <
      doubleValue (nextUp (nearestBinary neg m t)).bits := by
  obtain ⟨h1, -, -, he⟩ := nearestBinary_eq hf hz
  rw [he] at hf ⊢
  exact (lt_nextUp_and_nextDown_lt_ofDyadic h1 hf).1

theorem lt_nextUp_nearestDecimal {neg : Bool} {m : ℕ} {t : ℤ}
    (hf : (nearestDecimal neg m t).isFinite) (hz : (nearestDecimal neg m t).beq .zero = false) :
    ((if neg then -((m : ℚ) * 10 ^ t) else (m : ℚ) * 10 ^ t : ℚ) : WithBotTop ℚ) <
      doubleValue (nextUp (nearestDecimal neg m t)).bits := by
  obtain ⟨h1, h2, h3⟩ := nearestDecimal_eq hf hz
  rcases le_or_gt 0 t with ht | ht
  · rw [(h2 ht).2] at hf ⊢
    convert (lt_nextUp_and_nextDown_lt_ofRatio (Nat.mul_ne_zero h1 (by positivity)) one_ne_zero
      hf).1 using 4 <;> push_cast <;> rw [← zpow_natCast, Int.toNat_of_nonneg ht, div_one]
  · rw [(h3 ht).2] at hf ⊢
    convert (lt_nextUp_and_nextDown_lt_ofRatio h1 (by positivity) hf).1 using 4 <;> push_cast <;>
      rw [← zpow_natCast, Int.toNat_of_nonneg (by lia), zpow_neg, div_inv_eq_mul]

/-- The exact value of the floating constant `w` that is not an infinity, from the parts of its
word (`Ratpoints.Cli.floatParts`): `±m 2 ^ (ex - 4 k)` for a hexadecimal constant and
`±m 10 ^ (ex - k)` for a decimal one, for the digits `m` of its mantissa, the number `k` of them
after the point and its exponent `ex`, as `strtod` takes it. -/
def wordValue (w : List Char) : ℚ :=
  let (neg, hex, ds, k, rest) := floatParts w
  let (eneg, eds) := exponentDigits rest
  let ex : ℤ := if eneg then -(natOfDigitsIn 10 eds : ℤ) else natOfDigitsIn 10 eds
  let m := natOfDigitsIn (if hex then 16 else 10) ds
  let v : ℚ := if hex then (m : ℚ) * 2 ^ (ex - 4 * k) else (m : ℚ) * 10 ^ (ex - k)
  if neg then -v else v

theorem strtod_eq {w : List Char} (hi : isInfWord (dropSign w) = false) :
    strtod w = if (floatParts w).2.1 then
        nearestBinary (floatParts w).1 (natOfDigitsIn 16 (floatParts w).2.2.1)
          ((if (exponentDigits (floatParts w).2.2.2.2).1 then
            -(natOfDigitsIn 10 (exponentDigits (floatParts w).2.2.2.2).2 : ℤ)
            else natOfDigitsIn 10 (exponentDigits (floatParts w).2.2.2.2).2) -
            4 * (floatParts w).2.2.2.1)
      else nearestDecimal (floatParts w).1 (natOfDigitsIn 10 (floatParts w).2.2.1)
          ((if (exponentDigits (floatParts w).2.2.2.2).1 then
            -(natOfDigitsIn 10 (exponentDigits (floatParts w).2.2.2.2).2 : ℤ)
            else natOfDigitsIn 10 (exponentDigits (floatParts w).2.2.2.2).2) -
            (floatParts w).2.2.2.1) := by
  rw [strtod, ite_eq_right (by simp [hi])]

/-- The exact value of a floating constant lies below the successor of the finite double other
than a zero that `strtod` reads from it: the upper half of the faithful rounding of
`Ratpoints.Double.ofRatio` and `Ratpoints.Double.ofDyadic`
(`Ratpoints.Double.lt_nextUp_and_nextDown_lt_ofRatio`,
`Ratpoints.Double.lt_nextUp_and_nextDown_lt_ofDyadic`). -/
theorem lt_nextUp_strtod {w : List Char} (hi : isInfWord (dropSign w) = false)
    (hf : (strtod w).isFinite) (hz : (strtod w).beq .zero = false) :
    (wordValue w : WithBotTop ℚ) < doubleValue (nextUp (strtod w)).bits := by
  rw [strtod_eq hi] at hf hz ⊢
  simp only [wordValue]
  by_cases hx : (floatParts w).2.1 = true
  · simp only [hx, ↓reduceIte] at hf hz ⊢
    exact lt_nextUp_nearestBinary hf hz
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hf hz ⊢
    exact lt_nextUp_nearestDecimal hf hz

-- The digits of the mantissa of the part `s` of a floating constant, in the base `b` of the digits
-- `isD`, and the decimal digits of its exponent when `s` is a floating constant.
private theorem mantissaDigits_props {isD : Char → Bool} {b : ℕ} (s : List Char) {exp : List Char}
    (hd : ∀ ch, isD ch = true → digitValue ch < b) (hexp : ∀ x ∈ exp, "eEpP".contains x = true) :
    (mantissaDigits isD false s).2.1 ≤ (mantissaDigits isD false s).1.length ∧
      (mantissaDigits isD false s).1.length ≤ s.length ∧
      (∀ ch ∈ (mantissaDigits isD false s).1, digitValue ch < b) ∧
      (isFloatBody isD exp s = true →
        ∀ ch ∈ (exponentDigits (mantissaDigits isD false s).2.2).2, ch.isDigit = true) := by
  obtain ⟨h1, h2, h3, h4⟩ := mantissaDigits_bounds_and_eq_dropWhile isD false s
  exact ⟨h1, h2, fun ch hch ↦ hd ch (h3 ch hch), fun hf ↦ h4 ▸ exponentDigits_snd_isDigit hexp hf⟩

-- The characters that `Char.toLower` takes to `x` are `x` and `X`.
private theorem toLower_eq_x_iff (c : Char) : c.toLower = 'x' ↔ c = 'x' ∨ c = 'X' := by
  simp only [Char.ext_iff, ← UInt32.toNat_inj]
  have h1 : 'A'.val.toNat = 65 := rfl
  have h2 : 'Z'.val.toNat = 90 := rfl
  have h3 : 'a'.val.toNat = 97 := rfl
  have h4 : 'x'.val.toNat = 120 := rfl
  have h5 : 'X'.val.toNat = 88 := rfl
  by_cases h : c.val ≥ 'A'.val ∧ c.val ≤ 'Z'.val <;>
    simp only [Char.toLower, h, ↓reduceDIte, h4, h5] <;>
    simp only [ge_iff_le, UInt32.le_iff_toNat_le, h1, h2] at h <;> lia

/-- The parts of the word `w` (`Ratpoints.Cli.floatParts`): as many digits after the point at most
as in all, no more than the characters of `w`, all digits of the base, and the decimal digits of the
exponent when `w` is a floating constant that is not an infinity. -/
theorem floatParts_bounds_and_isDigit_exponentDigits (w : List Char) :
    (floatParts w).2.2.2.1 ≤ (floatParts w).2.2.1.length ∧
      (floatParts w).2.2.1.length ≤ w.length ∧
      (∀ ch ∈ (floatParts w).2.2.1, digitValue ch < if (floatParts w).2.1 then 16 else 10) ∧
      (isDoubleWord w = true → isInfWord (dropSign w) = false →
        ∀ ch ∈ (exponentDigits (floatParts w).2.2.2.2).2, ch.isDigit = true) := by
  have hv := length_dropSign_le w
  have hdec := mantissaDigits_props (b := 10) (exp := ['e', 'E']) (dropSign w)
    (fun _ ↦ digitValue_lt_ten) (by simp)
  simp only [floatParts, isDoubleWord]
  split
  · rename_i x t heq
    split
    · rename_i hx
      obtain ⟨h1, h2, h3, h4⟩ := mantissaDigits_props (b := 16) (exp := ['p', 'P']) t
        (fun _ ↦ digitValue_lt_sixteen) (by simp)
      have hl : x.toLower = 'x' := (toLower_eq_x_iff x).mpr (by simpa using hx)
      refine ⟨h1, by rw [heq] at hv; simp at hv; lia, h3, fun hd hi ↦ h4 ?_⟩
      simpa [hi, hl] using hd
    · rename_i hx
      have hl : ¬x.toLower = 'x' := fun h ↦ hx (by simpa using (toLower_eq_x_iff x).mp h)
      exact ⟨hdec.1, by lia, hdec.2.2.1, fun hd hi ↦ hdec.2.2.2 (by simpa [hi, hl] using hd)⟩
  · exact ⟨hdec.1, by lia, hdec.2.2.1, fun hd hi ↦ hdec.2.2.2 (by simpa [hi] using hd)⟩

theorem ite_natCast_mul_pow_eq (m b : ℕ) (t : ℤ) :
    (if 0 ≤ t then ((m * b ^ t.natAbs : ℕ) : ℚ) else mkRat m (b ^ t.natAbs)) =
      (m : ℚ) * (b : ℚ) ^ t := by
  split_ifs with ht
  · push_cast; rw [← zpow_natCast, Int.natAbs_of_nonneg ht]
  · rw [Rat.mkRat_eq_div]; push_cast
    rw [← zpow_natCast, show ((t.natAbs : ℕ) : ℤ) = -t by lia, zpow_neg, div_eq_mul_inv, inv_inv]

-- The exponent `E` of a floating constant of fewer than `2 ^ 56` characters lies below
-- `LONG_MAX / 20` when it meets the bounds of `Ratpoints.Cli.nearestBinary_eq` (hexadecimal) or
-- `Ratpoints.Cli.nearestDecimal_eq` (decimal) for a finite double that is not a zero.
private theorem natAbs_exponent_lt {E k len : ℕ} {l : ℕ} {eneg hex : Bool} (hk : k ≤ len)
    (hlen : len < 2 ^ 56) (hl : l < 4 * len + 1)
    (hb : hex = true → (l : ℤ) + ((if eneg then -(E : ℤ) else E) - 4 * k) < 1024 ∧
      -1075 < (l : ℤ) + 1 + ((if eneg then -(E : ℤ) else E) - 4 * k))
    (hd : hex = false → (0 ≤ (if eneg then -(E : ℤ) else E) - k →
        (l : ℤ) + 3 * ((if eneg then -(E : ℤ) else E) - k) < 1024) ∧
      ((if eneg then -(E : ℤ) else E) - k < 0 →
        3 * -((if eneg then -(E : ℤ) else E) - k) < (l : ℤ) + 1076)) :
    (E : ℤ) < (2 ^ 63 - 1) / 20 := by
  cases hex <;> cases eneg <;> simp at hb hd <;> lia

theorem log2_natOfDigitsIn_lt {w : List Char} :
    (natOfDigitsIn (if (floatParts w).2.1 then 16 else 10) (floatParts w).2.2.1).log2 <
      4 * (floatParts w).2.2.1.length + 1 := by
  have hd := (floatParts_bounds_and_isDigit_exponentDigits w).2.2.1
  have h1 := natOfDigitsIn_lt _ hd
  have h2 : (if (floatParts w).2.1 then 16 else 10) ^ (floatParts w).2.2.1.length ≤
      2 ^ (4 * (floatParts w).2.2.1.length) := by
    rw [pow_mul]; exact Nat.pow_le_pow_left (by split <;> norm_num) _
  rcases Nat.eq_zero_or_pos (natOfDigitsIn (if (floatParts w).2.1 then 16 else 10)
    (floatParts w).2.2.1) with h | h
  · rw [h]; simp
  · have := (Nat.log2_lt h.ne').mpr (h1.trans_le h2); lia

-- The exponent of a floating constant whose double is finite and not a zero, of fewer than `2 ^ 56`
-- characters, lies below the bound `LONG_MAX / 20` at which `scan_end` stops taking digits, and the
-- digits of its mantissa are not all `0`.
private theorem exponent_lt_of_strtod {w : List Char} (hi : isInfWord (dropSign w) = false)
    (hf : (strtod w).isFinite = true) (hz : (strtod w).beq .zero = false)
    (hlen : w.length < 2 ^ 56) :
    (natOfDigitsIn 10 (exponentDigits (floatParts w).2.2.2.2).2 : ℤ) < (2 ^ 63 - 1) / 20 ∧
      natOfDigitsIn (if (floatParts w).2.1 then 16 else 10) (floatParts w).2.2.1 ≠ 0 := by
  obtain ⟨hk, hds, -, -⟩ := floatParts_bounds_and_isDigit_exponentDigits w
  have hl := log2_natOfDigitsIn_lt (w := w)
  rw [strtod_eq hi] at hf hz
  by_cases hx : (floatParts w).2.1 = true
  · simp only [hx, ↓reduceIte] at hf hz hl ⊢
    obtain ⟨h1, h2, h3, -⟩ := nearestBinary_eq hf hz
    exact ⟨natAbs_exponent_lt (hex := true) hk (by lia) hl (fun _ ↦ ⟨h2, h3⟩) nofun, h1⟩
  · simp only [hx, Bool.false_eq_true, ↓reduceIte] at hf hz hl ⊢
    obtain ⟨h1, h2, h3⟩ := nearestDecimal_eq hf hz
    exact ⟨natAbs_exponent_lt (hex := false) hk (by lia) hl nofun
      fun _ ↦ ⟨fun h ↦ (h2 h).1, fun h ↦ (h3 h).1⟩, h1⟩

/-- For a floating constant of fewer than `2 ^ 56` characters whose double is finite and not a
zero, the end that `scan_end` takes is its exact value. -/
theorem scanEndValue_eq_wordValue {w : List Char} (hd : isDoubleWord w = true)
    (hi : isInfWord (dropSign w) = false) (hf : (strtod w).isFinite = true)
    (hz : (strtod w).beq .zero = false) (hlen : w.length < 2 ^ 56) :
    scanEndValue w (strtod w) = wordValue w := by
  obtain ⟨hE, hm⟩ := exponent_lt_of_strtod hi hf hz hlen
  have heds := (floatParts_bounds_and_isDigit_exponentDigits w).2.2.2 hd hi
  have hcap : (exponentDigits (floatParts w).2.2.2.2).2.foldl (fun ex ch ↦
      if ex < 461168601842738790 then 10 * ex + ((ch.toNat : ℤ) - 48) else ex) 0 =
      natOfDigitsIn 10 (exponentDigits (floatParts w).2.2.2.2).2 := by
    simpa [natOfDigitsIn] using foldl_capped_eq heds 0 hE
  rw [scanEndValue, wordValue]
  generalize floatParts w = fp at hm hcap ⊢
  obtain ⟨neg, hex, ds, k, rest⟩ := fp
  dsimp only at hm hcap ⊢
  generalize exponentDigits rest = ep at hcap ⊢
  obtain ⟨eneg, eds⟩ := ep
  dsimp only at hcap ⊢
  cases hex <;> simp only [Bool.false_eq_true, ↓reduceIte] at hm ⊢ <;>
    simp only [hm, hz, ↓reduceIte, Bool.false_eq_true, ite_natCast_mul_pow_eq] <;>
    push_cast <;> simp only [hcap]

/-- When `strtod` reads a zero, the end that `scan_end` takes is `0` or `±2 ^ (-1075)`, below the
least positive double, the successor of the zero. -/
theorem lt_nextUp_of_beq_zero (w : List Char) {x : Double} (hz : x.beq .zero = true) :
    (scanEndValue w x : WithBotTop ℚ) < doubleValue (nextUp x).bits := by
  rw [nextUp_of_beq_zero hz, doubleValue_one, WithBotTop.coe_lt_coe, scanEndValue]
  have ht : (0 : ℚ) < 2 ^ (-1074 : ℤ) := by positivity
  generalize floatParts w = fp
  obtain ⟨neg, hex, ds, k, rest⟩ := fp
  dsimp only
  simp only [hz, ↓reduceIte, toRat_zero_nextUp]
  split_ifs <;> linarith

theorem lt_nextUp_scanEndValue {w : List Char} (hd : isDoubleWord w = true)
    (hi : isInfWord (dropSign w) = false) (hf : (strtod w).isFinite = true)
    (hlen : w.length < 2 ^ 56) :
    (scanEndValue w (strtod w) : WithBotTop ℚ) < doubleValue (nextUp (strtod w)).bits := by
  cases hz : (strtod w).beq .zero
  · rw [scanEndValue_eq_wordValue hd hi hf hz hlen]; exact lt_nextUp_strtod hi hf hz
  · exact lt_nextUp_of_beq_zero w hz

theorem isInfWord_eq_false_of_isInf {w : List Char} (hi : (strtod w).isInf = false) :
    isInfWord (dropSign w) = false := by
  by_contra h
  rw [strtod, ite_eq_left (by simpa using h)] at hi
  split at hi <;> exact absurd hi (by decide)

theorem length_le_of_onlyWord?_eq_some {s : String} {w : List Char} (h : onlyWord? s = some w) :
    w.length ≤ s.length := by
  simp only [onlyWord?] at h
  split at h
  · rename_i w' hw
    obtain rfl := Option.some.inj h
    have hm : w' ∈ words s.toList := by simp [hw]
    simp only [words, List.mem_filter] at hm
    rw [← String.length_toList]
    exact (List.sublist_flatten_of_mem hm.1).length_le.trans_eq
      congr(List.length $(List.flatten_splitBy _ _))
  · cases h

/-- The double that `scan_end` gives for a lower end of fewer than `2 ^ 56` characters is the
largest double at most the end: every double at most the end is at most it. -/
theorem run_scanEnd_isMaxBelow {s : String} {e : ExactEnd} {d : Double}
    (h : Id.run (scanEnd s (-1)) = some (e, d)) (hlen : s.length < 2 ^ 56) (y : Double)
    (hy : y.isNaN = false) (hye : doubleValue y.bits ≤ e.value) :
    doubleValue y.bits ≤ doubleValue d.bits := by
  obtain ⟨w, hw, hdw, ⟨hi, rfl, rfl⟩ | ⟨hi, rfl, rfl⟩⟩ := eq_of_run_scanEnd_eq_some h
  · rwa [← value_inf_eq_doubleValue hi]
  have hf := isFinite_of_isInf_eq_false (isNaN_strtod w) hi
  have hwl := length_le_of_onlyWord?_eq_some hw
  obtain ⟨-, -, -, hm⟩ := run_outward (scanEndValue w (strtod w)) (-1) hf
  exact hm (by decide) (lt_nextUp_scanEndValue hdw (isInfWord_eq_false_of_isInf hi) hf (by lia)) y
    hy (by simpa [ExactEnd.value] using hye)

/-! ### The search region of the command line -/

/-- The rational number `x` lies in one of the `n` search intervals of the command line with the
exact ends `ends`: `ends[2 j] ≤ x ≤ ends[2 j + 1]` for some `j < n`. -/
def InExactRegion (ends : Array ExactEnd) (n : ℕ) (x : ℚ) : Prop :=
  ∃ j < n, ends[2 * j]!.value ≤ (x : WithBotTop ℚ) ∧ (x : WithBotTop ℚ) ≤ ends[2 * j + 1]!.value

theorem cmpEndX_neg_iff (e : ExactEnd) (a b : ℤ) :
    cmpEndX e a b < 0 ↔ e.value < (((a : ℚ) / b : ℚ) : WithBotTop ℚ) := by
  rw [cmpEndX, ExactEnd.value, Rat.divInt_eq_div]
  split_ifs <;> first | lia | simp_all [bot_lt_iff_ne_bot]

theorem cmpEndX_nonpos_iff (e : ExactEnd) (a b : ℤ) :
    cmpEndX e a b ≤ 0 ↔ e.value ≤ (((a : ℚ) / b : ℚ) : WithBotTop ℚ) := by
  rw [cmpEndX, ExactEnd.value, Rat.divInt_eq_div]
  split_ifs <;> first | lia | simp_all [le_of_lt]

/-- The values `v 0, v 1, …, v (m - 1)` of the ends of intervals, in turn a lower and an upper end,
increase, the upper end of each strictly below the lower end of the next, as the checks of error 7
make those of the command line. -/
def ChainEnds (v : ℕ → WithBotTop ℚ) (m : ℕ) : Prop :=
  ∀ i, i + 1 < m → v i ≤ v (i + 1) ∧ (i % 2 = 1 → v i < v (i + 1))

theorem ChainEnds.le {v : ℕ → WithBotTop ℚ} {m : ℕ} (h : ChainEnds v m) {i k : ℕ} (hik : i ≤ k)
    (hk : k < m) : v i ≤ v k := by
  induction k, hik using Nat.le_induction with
  | base => rfl
  | succ k hik ih => exact (ih (by lia)).trans (h k hk).1

theorem ChainEnds.lt {v : ℕ → WithBotTop ℚ} {m : ℕ} (h : ChainEnds v m) {i k : ℕ}
    (hi : i % 2 = 1) (hik : i < k) (hk : k < m) : v i < v k :=
  ((h i (by lia)).2 hi).trans_le (h.le (by lia) hk)

/-- The invariant of the binary search of `Ratpoints.Cli.inRegion` for `x` among the `n` intervals
with the ends of the values `v`, on its state `(lo, hi)`: the upper ends before `lo` lie below `x`,
those from `hi` on not, and `lo = hi` at the exit. -/
def InRegionInvariant (v : ℕ → WithBotTop ℚ) (x : WithBotTop ℚ) (n : ℕ) :
    Std.WP.WhileInvariant (ℕ × ℕ) Prop :=
  .mk fun exit s ↦ s.1 ≤ s.2 ∧ s.2 ≤ n ∧ (∀ j < s.1, v (2 * j + 1) < x) ∧
    (∀ j, s.2 ≤ j → j < n → x ≤ v (2 * j + 1)) ∧ (exit = true → s.2 ≤ s.1)

theorem inRegionInvariant_zero (v : ℕ → WithBotTop ℚ) (x : WithBotTop ℚ) (n : ℕ) :
    InRegionInvariant v x n false (0, n) :=
  ⟨Nat.zero_le n, le_rfl, nofun, fun _ h1 h2 ↦ absurd h2 (by lia), nofun⟩

theorem InRegionInvariant.exit {v : ℕ → WithBotTop ℚ} {x : WithBotTop ℚ} {n lo hi : ℕ}
    (hlt : ¬lo < hi) (h : InRegionInvariant v x n false (lo, hi)) :
    InRegionInvariant v x n true (lo, hi) :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, fun _ ↦ Nat.le_of_not_lt hlt⟩

theorem InRegionInvariant.step_lt {e : Array ExactEnd} {a b : ℤ} {n lo hi k : ℕ}
    (hc : ChainEnds (fun j ↦ e[j]!.value) (2 * n)) (hlt : lo < hi)
    (hx : cmpEndX e[2 * (lo + (hi - lo) / 2) + 1]! a b < 0)
    (h : hi - lo = k ∧
      InRegionInvariant (fun j ↦ e[j]!.value) (((a : ℚ) / b : ℚ) : WithBotTop ℚ) n false (lo, hi)) :
    hi - (lo + (hi - lo) / 2 + 1) < k ∧
      InRegionInvariant (fun j ↦ e[j]!.value) (((a : ℚ) / b : ℚ) : WithBotTop ℚ) n false
        (lo + (hi - lo) / 2 + 1, hi) := by
  obtain ⟨rfl, -, h2, -, h4, -⟩ := h
  rw [cmpEndX_neg_iff] at hx
  refine ⟨by lia, by lia, h2, fun j hj ↦ ?_, h4, nofun⟩
  exact lt_of_le_of_lt (hc.le (by lia) (by lia)) hx

theorem InRegionInvariant.step_ge {e : Array ExactEnd} {a b : ℤ} {n lo hi k : ℕ}
    (hc : ChainEnds (fun j ↦ e[j]!.value) (2 * n)) (hlt : lo < hi)
    (hx : ¬cmpEndX e[2 * (lo + (hi - lo) / 2) + 1]! a b < 0)
    (h : hi - lo = k ∧
      InRegionInvariant (fun j ↦ e[j]!.value) (((a : ℚ) / b : ℚ) : WithBotTop ℚ) n false (lo, hi)) :
    lo + (hi - lo) / 2 - lo < k ∧
      InRegionInvariant (fun j ↦ e[j]!.value) (((a : ℚ) / b : ℚ) : WithBotTop ℚ) n false
        (lo, lo + (hi - lo) / 2) := by
  obtain ⟨rfl, -, h2, h3, -, -⟩ := h
  rw [cmpEndX_neg_iff, not_lt] at hx
  refine ⟨by lia, by lia, by lia, h3, fun j hj hjn ↦ hx.trans (hc.le (by lia) (by lia)), nofun⟩

theorem InRegionInvariant.post {e : Array ExactEnd} {a b : ℤ} {n lo hi : ℕ}
    (hc : ChainEnds (fun j ↦ e[j]!.value) (2 * n))
    (h : InRegionInvariant (fun j ↦ e[j]!.value) (((a : ℚ) / b : ℚ) : WithBotTop ℚ) n true
      (lo, hi)) :
    (decide (lo < n) && decide (cmpEndX e[2 * lo]! a b ≤ 0)) = true ↔
      InExactRegion e n (a / b) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  have hlo : lo = hi := by have := h5 rfl; lia
  subst hlo
  simp only [Bool.and_eq_true, decide_eq_true_eq, cmpEndX_nonpos_iff, InExactRegion]
  refine ⟨fun h ↦ ⟨lo, h.1, h.2, h4 lo le_rfl h.1⟩, fun ⟨j, hj, hl, hu⟩ ↦ ?_⟩
  rcases lt_trichotomy j lo with hjl | rfl | hjl
  · exact absurd hu (not_le.mpr (h3 j hjl))
  · exact ⟨hj, hl⟩
  · exact absurd ((h4 lo le_rfl (by lia)).trans_lt ((hc.lt (by lia) (by lia) (by lia)).trans_le hl))
      (lt_irrefl _)

attribute [local irreducible] InRegionInvariant in
/-- The binary search of `in_region` over increasing and disjoint intervals decides whether
`a / b` lies in one of them. -/
@[spec]
theorem inRegion_spec (a b : ℤ) (e : Array ExactEnd) (n : ℕ) :
    ⦃ ChainEnds (fun j ↦ e[j]!.value) (2 * n) ⦄ inRegion a b e n
    ⦃ fun r ↦ (r = true ↔ InExactRegion e n (a / b)) ⦄ := by
  vcgen [inRegion] invariants
  · InRegionInvariant (fun j ↦ e[j]!.value) (((a : ℚ) / b : ℚ) : WithBotTop ℚ) n
  · Std.WP.Variant.ofMeasure fun s : ℕ × ℕ ↦ s.2 - s.1
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals first
    | exact inRegionInvariant_zero _ _ _
    | exact InRegionInvariant.post ‹_› ‹_›
    | exact InRegionInvariant.step_lt ‹_› ‹_› ‹_› ‹_›
    | exact InRegionInvariant.step_ge ‹_› ‹_› ‹_› ‹_›
    | exact InRegionInvariant.exit ‹_› ‹_ ∧ _›.2

theorem run_inRegion (a b : ℤ) {e : Array ExactEnd} {n : ℕ}
    (hc : ChainEnds (fun j ↦ e[j]!.value) (2 * n)) :
    Id.run (inRegion a b e n) = true ↔ InExactRegion e n (a / b) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((inRegion_spec a b e n).le_wp hc)

/-! ### Joining the intervals -/

/-- `x` lies in the interval `p`, over the values of its ends. -/
def InPair (p : Double × Double) (x : ℚ) : Prop :=
  doubleValue p.1.bits ≤ (x : WithBotTop ℚ) ∧ (x : WithBotTop ℚ) ≤ doubleValue p.2.bits

/-- No end of the intervals `dom` is a NaN. -/
def NoNaN (dom : List (Double × Double)) : Prop :=
  ∀ p ∈ dom, p.1.isNaN = false ∧ p.2.isNaN = false

/-- The intervals `dom` have `l ≤ u`, and their lower ends increase from the second one on, as
those of the command line do. -/
def JoinsWell (dom : List (Double × Double)) : Prop :=
  (∀ p ∈ dom, doubleValue p.1.bits ≤ doubleValue p.2.bits) ∧
    ∀ i j, 1 ≤ i → i ≤ j → j < dom.length →
      doubleValue dom[i]!.1.bits ≤ doubleValue dom[j]!.1.bits

/-- The invariant of the loop of `Ratpoints.Cli.joinIntervals` over the intervals `dom`, after the
intervals up to the `k`-th, on its state `(iv, n)`, the array of the intervals and the index of the
last interval kept. -/
structure JoinInvariant (dom : List (Double × Double)) (k : ℕ) (iv : Array (Double × Double))
    (n : ℕ) : Prop where
  /-- The array has the length of `dom`. -/
  size_eq : iv.size = dom.length
  /-- The last interval kept has an index at most `k`. -/
  le_k : n ≤ k
  /-- The intervals up to the `k`-th are among those of `dom`. -/
  k_lt : k < dom.length
  /-- The intervals after the `k`-th are those of `dom`. -/
  tail_eq : ∀ j, k < j → iv[j]! = dom[j]!
  /-- The intervals kept, `iv[0]` to `iv[n]`, have no NaN. -/
  noNaN : ∀ j ≤ n, iv[j]!.1.isNaN = false ∧ iv[j]!.2.isNaN = false
  /-- The intervals kept hold every interval of `dom` up to the `k`-th. -/
  covers : ∀ i ≤ k, ∀ x, InPair dom[i]! x → ∃ j ≤ n, InPair iv[j]! x
  /-- For intervals that join well, the intervals kept have `l ≤ u` and are increasing and strictly
  apart, and the lower end of the last one, when it is not the first, is at most those of the
  intervals of `dom` still to come. -/
  wellJoined : JoinsWell dom →
    (∀ j ≤ n, doubleValue iv[j]!.1.bits ≤ doubleValue iv[j]!.2.bits) ∧
      (∀ j < n, doubleValue iv[j]!.2.bits < doubleValue iv[j + 1]!.1.bits) ∧
      (n ≠ 0 → ∀ i, k < i → i < dom.length →
        doubleValue iv[n]!.1.bits ≤ doubleValue dom[i]!.1.bits)

theorem joinInvariant_zero {dom : List (Double × Double)} (hnan : NoNaN dom)
    (h : ¬dom.isEmpty = true) : JoinInvariant dom 0 dom.toArray 0 := by
  have hl : 0 < dom.length := by cases dom <;> simp_all
  have hm := List.getElem!_mem hl
  have e0 : dom.toArray[0]! = dom[0]! := by simp
  refine ⟨rfl, le_rfl, hl, fun j _ ↦ by simp, fun j hj ↦ ?_, fun i hi x hx ↦ ⟨0, le_rfl, ?_⟩,
    fun hw ↦ ⟨fun j hj ↦ ?_, fun j hj ↦ absurd hj (by lia), fun h ↦ absurd rfl h⟩⟩
  · obtain rfl : j = 0 := by lia
    rw [e0]; exact hnan _ hm
  · rwa [e0, ← show i = 0 by lia]
  · obtain rfl : j = 0 := by lia
    rw [e0]; exact hw.1 _ hm

theorem doubleValue_pick_lt {a c : Double} (ha : a.isNaN = false) (hc : c.isNaN = false) :
    doubleValue (if c.lt a then c else a).bits = min (doubleValue a.bits) (doubleValue c.bits) := by
  split_ifs with h
  · rw [min_eq_right ((lt_eq_true_iff hc ha).mp h).le]
  · rw [min_eq_left (not_lt.mp fun h' ↦ h ((lt_eq_true_iff hc ha).mpr h'))]

theorem doubleValue_pick_gt {a c : Double} (ha : a.isNaN = false) (hc : c.isNaN = false) :
    doubleValue (if a.lt c then c else a).bits = max (doubleValue a.bits) (doubleValue c.bits) := by
  split_ifs with h
  · rw [max_eq_right ((lt_eq_true_iff ha hc).mp h).le]
  · rw [max_eq_left (not_lt.mp fun h' ↦ h ((lt_eq_true_iff ha hc).mpr h'))]

/-- The order of the intervals kept by the loop of `Ratpoints.Cli.joinIntervals` after the next
interval is joined to the last one kept, `p`, the least lower and the greatest upper end. -/
theorem joinWF_merge {dom : List (Double × Double)} {k n : ℕ} {iv iv' : Array (Double × Double)}
    {p : Double × Double} (hk : k + 1 < dom.length) (hc : iv[k + 1]! = dom[k + 1]!)
    (hp1 : doubleValue p.1.bits = min (doubleValue iv[n]!.1.bits) (doubleValue iv[k + 1]!.1.bits))
    (hp2 : doubleValue p.2.bits = max (doubleValue iv[n]!.2.bits) (doubleValue iv[k + 1]!.2.bits))
    (hn : iv'[n]! = p) (hne : ∀ j, j ≠ n → iv'[j]! = iv[j]!)
    (w1 : ∀ j ≤ n, doubleValue iv[j]!.1.bits ≤ doubleValue iv[j]!.2.bits)
    (w2 : ∀ j < n, doubleValue iv[j]!.2.bits < doubleValue iv[j + 1]!.1.bits)
    (w3 : n ≠ 0 → ∀ i, k < i → i < dom.length →
      doubleValue iv[n]!.1.bits ≤ doubleValue dom[i]!.1.bits) :
    (∀ j ≤ n, doubleValue iv'[j]!.1.bits ≤ doubleValue iv'[j]!.2.bits) ∧
      (∀ j < n, doubleValue iv'[j]!.2.bits < doubleValue iv'[j + 1]!.1.bits) ∧
      (n ≠ 0 → ∀ i, k + 1 < i → i < dom.length →
        doubleValue iv'[n]!.1.bits ≤ doubleValue dom[i]!.1.bits) := by
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_, fun hn0 i hi hil ↦ ?_⟩
  · rcases eq_or_ne j n with rfl | hjn
    · rw [hn, hp1, hp2]
      exact (min_le_left _ _).trans ((w1 j le_rfl).trans (le_max_left _ _))
    · rw [hne j hjn]; exact w1 j (by lia)
  · rw [hne j (by lia)]
    rcases (show j + 1 < n ∨ j + 1 = n by lia) with hj' | hj'
    · rw [hne (j + 1) (by lia)]; exact w2 j (by lia)
    · rw [hj', hn, hp1]
      exact lt_min (hj' ▸ w2 j hj)
        ((hj' ▸ w2 j hj).trans_le (hc ▸ w3 (by lia) (k + 1) (by lia) hk))
  · rw [hn, hp1]; exact (min_le_left _ _).trans (w3 hn0 i (by lia) hil)

theorem JoinInvariant.merge {dom : List (Double × Double)} {k n : ℕ}
    {iv iv' : Array (Double × Double)} {p : Double × Double} (hk : k + 1 < dom.length)
    (h : JoinInvariant dom k iv n)
    (hp1 : doubleValue p.1.bits = min (doubleValue iv[n]!.1.bits) (doubleValue iv[k + 1]!.1.bits))
    (hp2 : doubleValue p.2.bits = max (doubleValue iv[n]!.2.bits) (doubleValue iv[k + 1]!.2.bits))
    (hpn : p.1.isNaN = false ∧ p.2.isNaN = false) (hs : iv'.size = iv.size)
    (hn : iv'[n]! = p) (hne : ∀ j, j ≠ n → iv'[j]! = iv[j]!) :
    JoinInvariant dom (k + 1) iv' n := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hc : iv[k + 1]! = dom[k + 1]! := h4 _ (by lia)
  have hsub (q : Double × Double) (hq1 : doubleValue p.1.bits ≤ doubleValue q.1.bits)
      (hq2 : doubleValue q.2.bits ≤ doubleValue p.2.bits) (x : ℚ) (hx : InPair q x) :
      InPair iv'[n]! x :=
    hn ▸ ⟨hq1.trans hx.1, hx.2.trans hq2⟩
  refine ⟨hs.trans h1, by lia, hk, fun j hj ↦ (hne j (by lia)).trans (h4 j (by lia)),
    fun j hj ↦ ?_, fun i hi x hx ↦ ?_, fun hw ↦ joinWF_merge hk hc hp1 hp2 hn hne (h7 hw).1
      (h7 hw).2.1 (h7 hw).2.2⟩
  · rcases eq_or_ne j n with rfl | hjn
    · rw [hn]; exact hpn
    · rw [hne j hjn]; exact h5 j hj
  rcases (show i ≤ k ∨ i = k + 1 by lia) with hi | rfl
  · obtain ⟨j, hj, hjx⟩ := h6 i hi x hx
    rcases eq_or_ne j n with rfl | hjn
    · exact ⟨j, le_rfl, hsub _ (hp1 ▸ min_le_left _ _) (hp2 ▸ le_max_left _ _) x hjx⟩
    · exact ⟨j, hj, hne j hjn ▸ hjx⟩
  · exact ⟨n, le_rfl, hsub _ (hp1 ▸ min_le_right _ _) (hp2 ▸ le_max_right _ _) x (hc ▸ hx)⟩

/-- The order of the intervals kept by the loop of `Ratpoints.Cli.joinIntervals` after the next
interval, which lies above the last one kept, is kept after it. -/
theorem joinWF_push {dom : List (Double × Double)} {k n : ℕ} {iv : Array (Double × Double)}
    (hw : JoinsWell dom) (hk : k + 1 < dom.length) (hc : iv[k + 1]! = dom[k + 1]!)
    (hs : n + 1 < iv.size) (hgt : doubleValue iv[n]!.2.bits < doubleValue iv[k + 1]!.1.bits)
    (w1 : ∀ j ≤ n, doubleValue iv[j]!.1.bits ≤ doubleValue iv[j]!.2.bits)
    (w2 : ∀ j < n, doubleValue iv[j]!.2.bits < doubleValue iv[j + 1]!.1.bits) :
    (∀ j ≤ n + 1, doubleValue (iv.set! (n + 1) iv[k + 1]!)[j]!.1.bits ≤
        doubleValue (iv.set! (n + 1) iv[k + 1]!)[j]!.2.bits) ∧
      (∀ j < n + 1, doubleValue (iv.set! (n + 1) iv[k + 1]!)[j]!.2.bits <
        doubleValue (iv.set! (n + 1) iv[k + 1]!)[j + 1]!.1.bits) ∧
      (n + 1 ≠ 0 → ∀ i, k + 1 < i → i < dom.length →
        doubleValue (iv.set! (n + 1) iv[k + 1]!)[n + 1]!.1.bits ≤ doubleValue dom[i]!.1.bits) := by
  have hn : (iv.set! (n + 1) iv[k + 1]!)[n + 1]! = dom[k + 1]! := by
    rw [Array.getElem!_set!_self _ _ _ hs, hc]
  have hne (j : ℕ) (hj : j ≠ n + 1) : (iv.set! (n + 1) iv[k + 1]!)[j]! = iv[j]! :=
    Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj)
  refine ⟨fun j hj ↦ ?_, fun j hj ↦ ?_, fun _ i hi hil ↦ ?_⟩
  · rcases eq_or_ne j (n + 1) with rfl | hjn
    · rw [hn]; exact hw.1 _ (List.getElem!_mem hk)
    · rw [hne j hjn]; exact w1 j (by lia)
  · rcases (show j < n ∨ j = n by lia) with hj' | rfl
    · rw [hne j (by lia), hne (j + 1) (by lia)]; exact w2 j hj'
    · rw [hne j (by lia), hn, ← hc]; exact hgt
  · rw [hn]; exact hw.2 (k + 1) i (by lia) (by lia) hil

theorem JoinInvariant.push {dom : List (Double × Double)} {k n : ℕ}
    {iv : Array (Double × Double)} (hnan : NoNaN dom) (hk : k + 1 < dom.length)
    (h : JoinInvariant dom k iv n)
    (hgt : doubleValue iv[n]!.2.bits < doubleValue iv[k + 1]!.1.bits) :
    JoinInvariant dom (k + 1) (iv.set! (n + 1) iv[k + 1]!) (n + 1) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := h
  have hc : iv[k + 1]! = dom[k + 1]! := h4 _ (by lia)
  have hn : (iv.set! (n + 1) iv[k + 1]!)[n + 1]! = dom[k + 1]! := by
    rw [Array.getElem!_set!_self _ _ _ (by lia), hc]
  have hne (j : ℕ) (hj : j ≠ n + 1) : (iv.set! (n + 1) iv[k + 1]!)[j]! = iv[j]! :=
    Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj)
  refine ⟨by simp [h1], by lia, hk, fun j hj ↦ (hne j (by lia)).trans (h4 j (by lia)),
    fun j hj ↦ ?_, fun i hi x hx ↦ ?_, fun hw ↦ joinWF_push hw hk hc (by lia) hgt (h7 hw).1
      (h7 hw).2.1⟩
  · rcases eq_or_ne j (n + 1) with rfl | hjn
    · rw [hn]; exact hnan _ (List.getElem!_mem hk)
    · rw [hne j hjn]; exact h5 j (by lia)
  · rcases (show i ≤ k ∨ i = k + 1 by lia) with hi | rfl
    · obtain ⟨j, hj, hjx⟩ := h6 i hi x hx
      exact ⟨j, by lia, (hne j (by lia)).symm ▸ hjx⟩
    · exact ⟨n + 1, le_rfl, hn ▸ hx⟩

theorem JoinInvariant.lt_cur {dom : List (Double × Double)} {pref suff : List ℕ} {cur n : ℕ}
    {iv : Array (Double × Double)} (hh : ForIn.toList [1:dom.length] = pref ++ cur :: suff)
    (h : JoinInvariant dom pref.length iv n) :
    pref.length + 1 = cur ∧ cur < dom.length ∧ n < cur ∧ cur < iv.size := by
  have h1 := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hh
  have h2 := Std.Legacy.Range.lt_of_toList_eq_append_cons hh
  exact ⟨by lia, h2, by lia [h.le_k], by lia [h.size_eq]⟩

/-- A step of the loop of `Ratpoints.Cli.joinIntervals` that joins the next interval to the last
one kept: the slot of that one holds the least lower and the greatest upper end. -/
theorem JoinInvariant.merge_pick {dom : List (Double × Double)} {pref suff : List ℕ} {cur n : ℕ}
    {iv iv' : Array (Double × Double)} (hnan : NoNaN dom)
    (hh : ForIn.toList [1:dom.length] = pref ++ cur :: suff)
    (h : JoinInvariant dom pref.length iv n) (hle : iv[cur]!.1.le iv[n]!.2 = true)
    (hs : iv'.size = iv.size)
    (hn : iv'[n]! = (if iv[cur]!.1.lt iv[n]!.1 then iv[cur]!.1 else iv[n]!.1,
      if iv[n]!.2.lt iv[cur]!.2 then iv[cur]!.2 else iv[n]!.2))
    (hne : ∀ j, j ≠ n → iv'[j]! = iv[j]!) :
    JoinInvariant dom (pref ++ [cur]).length iv' n := by
  obtain ⟨hc, hcl, hnc, -⟩ := h.lt_cur hh
  subst hc
  have hcd : iv[pref.length + 1]! = dom[pref.length + 1]! := h.tail_eq _ (by lia)
  obtain ⟨ha1, ha2⟩ := h.noNaN n le_rfl
  obtain ⟨hc1, hc2⟩ := hcd ▸ hnan _ (List.getElem!_mem hcl)
  rw [List.length_append, List.length_singleton]
  refine h.merge hcl ?_ ?_ ?_ hs hn hne
  · exact doubleValue_pick_lt ha1 hc1
  · exact doubleValue_pick_gt ha2 hc2
  · exact ⟨by dsimp only; split <;> assumption, by dsimp only; split <;> assumption⟩

theorem JoinInvariant.merge_lt_lt {dom : List (Double × Double)} {pref suff : List ℕ}
    {cur n : ℕ} {iv : Array (Double × Double)} (hnan : NoNaN dom)
    (hh : ForIn.toList [1:dom.length] = pref ++ cur :: suff)
    (h : JoinInvariant dom pref.length iv n) (h1 : iv[cur]!.1.le iv[n]!.2 = true)
    (h2 : iv[cur]!.1.lt iv[n]!.1 = true)
    (h3 : (iv.set! n (iv[cur]!.1, iv[n]!.2))[n]!.2.lt (iv.set! n (iv[cur]!.1, iv[n]!.2))[cur]!.2 =
      true) :
    JoinInvariant dom (pref ++ [cur]).length ((iv.set! n (iv[cur]!.1, iv[n]!.2)).set! n
      ((iv.set! n (iv[cur]!.1, iv[n]!.2))[n]!.1, (iv.set! n (iv[cur]!.1, iv[n]!.2))[cur]!.2))
        n := by
  obtain ⟨-, -, hnc, hcs⟩ := h.lt_cur hh
  simp only [Array.getElem!_set!_self _ _ _ (show n < iv.size by lia),
    Array.getElem!_set!_ne _ _ _ _ (Nat.ne_of_lt hnc)] at h3 ⊢
  refine h.merge_pick hnan hh h1 (by simp) ?_ fun j hj ↦ ?_
  · rw [Array.getElem!_set!_self _ _ _ (by simp; lia)]; simp [h2, h3]
  · rw [Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj), Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj)]

theorem JoinInvariant.merge_lt_ge {dom : List (Double × Double)} {pref suff : List ℕ}
    {cur n : ℕ} {iv : Array (Double × Double)} (hnan : NoNaN dom)
    (hh : ForIn.toList [1:dom.length] = pref ++ cur :: suff)
    (h : JoinInvariant dom pref.length iv n) (h1 : iv[cur]!.1.le iv[n]!.2 = true)
    (h2 : iv[cur]!.1.lt iv[n]!.1 = true)
    (h3 : ¬(iv.set! n (iv[cur]!.1, iv[n]!.2))[n]!.2.lt (iv.set! n (iv[cur]!.1, iv[n]!.2))[cur]!.2 =
      true) :
    JoinInvariant dom (pref ++ [cur]).length (iv.set! n (iv[cur]!.1, iv[n]!.2)) n := by
  obtain ⟨-, -, hnc, hcs⟩ := h.lt_cur hh
  simp only [Array.getElem!_set!_self _ _ _ (show n < iv.size by lia),
    Array.getElem!_set!_ne _ _ _ _ (Nat.ne_of_lt hnc)] at h3
  refine h.merge_pick hnan hh h1 (by simp) ?_ fun j hj ↦ Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj)
  rw [Array.getElem!_set!_self _ _ _ (by lia)]; simp [h2, h3]

theorem JoinInvariant.merge_ge_lt {dom : List (Double × Double)} {pref suff : List ℕ}
    {cur n : ℕ} {iv : Array (Double × Double)} (hnan : NoNaN dom)
    (hh : ForIn.toList [1:dom.length] = pref ++ cur :: suff)
    (h : JoinInvariant dom pref.length iv n) (h1 : iv[cur]!.1.le iv[n]!.2 = true)
    (h2 : ¬iv[cur]!.1.lt iv[n]!.1 = true) (h3 : iv[n]!.2.lt iv[cur]!.2 = true) :
    JoinInvariant dom (pref ++ [cur]).length (iv.set! n (iv[n]!.1, iv[cur]!.2)) n := by
  obtain ⟨-, -, hnc, hcs⟩ := h.lt_cur hh
  refine h.merge_pick hnan hh h1 (by simp) ?_ fun j hj ↦ Array.getElem!_set!_ne _ _ _ _ (Ne.symm hj)
  rw [Array.getElem!_set!_self _ _ _ (by lia)]; simp [h2, h3]

theorem JoinInvariant.merge_ge_ge {dom : List (Double × Double)} {pref suff : List ℕ}
    {cur n : ℕ} {iv : Array (Double × Double)} (hnan : NoNaN dom)
    (hh : ForIn.toList [1:dom.length] = pref ++ cur :: suff)
    (h : JoinInvariant dom pref.length iv n) (h1 : iv[cur]!.1.le iv[n]!.2 = true)
    (h2 : ¬iv[cur]!.1.lt iv[n]!.1 = true) (h3 : ¬iv[n]!.2.lt iv[cur]!.2 = true) :
    JoinInvariant dom (pref ++ [cur]).length iv n :=
  h.merge_pick hnan hh h1 rfl (by simp [h2, h3]) fun _ _ ↦ rfl

theorem JoinInvariant.push_cur {dom : List (Double × Double)} {pref suff : List ℕ}
    {cur n : ℕ} {iv : Array (Double × Double)} (hnan : NoNaN dom)
    (hh : ForIn.toList [1:dom.length] = pref ++ cur :: suff)
    (h : JoinInvariant dom pref.length iv n) (h1 : ¬iv[cur]!.1.le iv[n]!.2 = true) :
    JoinInvariant dom (pref ++ [cur]).length (iv.set! (n + 1) iv[cur]!) (n + 1) := by
  obtain ⟨hc, hcl, -, -⟩ := h.lt_cur hh
  subst hc
  have hcd : iv[pref.length + 1]! = dom[pref.length + 1]! := h.tail_eq _ (by lia)
  obtain ⟨ha1, ha2⟩ := h.noNaN n le_rfl
  obtain ⟨hc1, hc2⟩ := hcd ▸ hnan _ (List.getElem!_mem hcl)
  rw [List.length_append, List.length_singleton]
  exact h.push hnan hcl (not_le.mp fun h' ↦ h1 ((le_eq_true_iff hc1 ha2).mpr h'))

theorem joinIntervals_post_of_isEmpty {dom : List (Double × Double)} (hnan : NoNaN dom)
    (h : dom.isEmpty = true) :
    (dom = [] ↔ dom = []) ∧ NoNaN dom ∧ (∀ x, (∃ p ∈ dom, InPair p x) → ∃ p ∈ dom, InPair p x) ∧
      (JoinsWell dom →
        AreSearchIntervals (dom.map fun p ↦ (doubleValue p.1.bits, doubleValue p.2.bits))) := by
  obtain rfl := List.isEmpty_iff.mp h
  exact ⟨Iff.rfl, hnan, fun _ h ↦ h, fun _ ↦ ⟨nofun, List.IsChain.nil⟩⟩

theorem JoinInvariant.post {dom : List (Double × Double)} {iv : Array (Double × Double)} {n : ℕ}
    (h : JoinInvariant dom (ForIn.toList [1:dom.length]).length iv n) :
    (iv.toList.take (n + 1) = [] ↔ dom = []) ∧ NoNaN (iv.toList.take (n + 1)) ∧
      (∀ x, (∃ p ∈ dom, InPair p x) → ∃ p ∈ iv.toList.take (n + 1), InPair p x) ∧
      (JoinsWell dom → AreSearchIntervals ((iv.toList.take (n + 1)).map
        fun p ↦ (doubleValue p.1.bits, doubleValue p.2.bits))) := by
  obtain ⟨h1, h2, h3, -, h5, h6, h7⟩ := h
  rw [Std.Legacy.Range.length_toList] at h2 h3 h6 h7
  have hl : (iv.toList.take (n + 1)).length = n + 1 := by simp; lia
  have hmem (j : ℕ) (hj : j ≤ n) : iv[j]! ∈ iv.toList.take (n + 1) :=
    Array.mem_take_toList_of_lt (by lia) (by lia)
  refine ⟨⟨fun h ↦ absurd hl (by simp [h]), fun h ↦ by simp [h] at h3⟩, fun p hp ↦ ?_,
    fun x ⟨p, hp, hx⟩ ↦ ?_, fun hw ↦ ⟨fun q hq ↦ ?_, ?_⟩⟩
  · obtain ⟨j, hj, -, rfl⟩ := Array.exists_eq_of_mem_take_toList hp; exact h5 j (by lia)
  · obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    obtain ⟨j, hj, hjx⟩ := h6 i (by lia) x (by rwa [getElem!_pos dom i hi])
    exact ⟨_, hmem j hj, hjx⟩
  · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hq
    obtain ⟨j, hj, -, rfl⟩ := Array.exists_eq_of_mem_take_toList hp; exact (h7 hw).1 j (by lia)
  · refine List.isChain_iff_getElem.mpr fun i hi ↦ ?_
    simp only [List.length_map] at hi
    simp only [List.getElem_map, Array.getElem_take_toList]
    exact (h7 hw).2.1 i (by lia)

/-- `join_intervals` keeps the search intervals of the command line, without NaN: it gives none
exactly when there are none, the intervals it gives hold the values of the intervals it joins, and
for intervals that join well (with `l ≤ u` and the lower ends increasing from the second on) the
intervals it gives have `l ≤ u` and are increasing and strictly apart. -/
@[spec]
theorem joinIntervals_spec (dom : List (Double × Double)) :
    ⦃ NoNaN dom ⦄ joinIntervals dom
    ⦃ fun r ↦ (r = [] ↔ dom = []) ∧ NoNaN r ∧
      (∀ x, (∃ p ∈ dom, InPair p x) → ∃ p ∈ r, InPair p x) ∧
      (JoinsWell dom →
        AreSearchIntervals (r.map fun p ↦ (doubleValue p.1.bits, doubleValue p.2.bits))) ⦄ := by
  vcgen [joinIntervals] invariants
  | inv1 => fun pref _ s ↦ JoinInvariant dom pref.length s.1 s.2
  all_goals first
    | exact joinInvariant_zero ‹_› ‹_›
    | exact JoinInvariant.merge_lt_lt ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact JoinInvariant.merge_lt_ge ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact JoinInvariant.merge_ge_lt ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact JoinInvariant.merge_ge_ge ‹_› ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact JoinInvariant.push_cur ‹_› ‹_› ‹_› ‹_›
    | exact joinIntervals_post_of_isEmpty ‹_› ‹_›
    | exact JoinInvariant.post ‹_›

theorem run_joinIntervals {dom : List (Double × Double)} (h : NoNaN dom) :
    (Id.run (joinIntervals dom) = [] ↔ dom = []) ∧ NoNaN (Id.run (joinIntervals dom)) ∧
      (∀ x, (∃ p ∈ dom, InPair p x) → ∃ p ∈ Id.run (joinIntervals dom), InPair p x) ∧
      (JoinsWell dom → AreSearchIntervals ((Id.run (joinIntervals dom)).map
        fun p ↦ (doubleValue p.1.bits, doubleValue p.2.bits))) :=
  Std.WP.Id.of_run_eq_wp rfl _ ((joinIntervals_spec dom).le_wp h)

end Cli

end Ratpoints

end
