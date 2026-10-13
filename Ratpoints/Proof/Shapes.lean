/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Divisors
public import Ratpoints.Proof.Forbidden

import Ratpoints.Mathlib.Data.Nat.Squarefree
import Ratpoints.Proof.Bits
import Ratpoints.Proof.Jacobi
import Ratpoints.Proof.JacobiTables
import Ratpoints.Proof.Setup
import Ratpoints.Proof.TwoAdic
import Std.Tactic.Do

/-!
# The shapes of the loop over the denominators

The lists of the denominators of the shapes of the loop (`Ratpoints.Sieve.Shape.dens`) and their
tests on a single denominator (`Ratpoints.Sieve.Shape.keep`). The square shape lists the squares of
a range, in increasing order, by the exact integer square roots (`Ratpoints.Sieve.ceilSqrt`,
`Ratpoints.Sieve.floorSqrt`); the divisor shape lists the products `s k ^ 2` of a range, each once
for distinct squarefree divisors `s`, since `s k ^ 2` determines the squarefree `s` and `k`; and the
word shape lists the denominators of a range whose class admits a numerator and which no forbidden
divisor tested with words divides, in increasing order (`Ratpoints.Sieve.wordsDens`), since bit `j`
of word `r` of the words of a prime `p` is clear exactly when `p ∣ 64 r + j`
(`Ratpoints.Sieve.forbiddenRow`) and the walk over the set bits of a word pushes their
denominators, lowest first. The tests let the denominator of every point through: the class test
(`Ratpoints.Sieve.getElem!_twoAdic_ne_zero`), the valuation test of the divisor shape with the
slopes of the divisor set-up (`Ratpoints.Setup.DenInfo.excludes_eq_false_of_sq_eq`), and the tests
of the word shape, the forbidden divisors and both Jacobi tests
(`Ratpoints.Sieve.IsForbiddenEntry.not_dvd`, `Ratpoints.Sieve.IsForbiddenVal.excludes_eq_false`,
`Ratpoints.Sieve.run_jacobi_eq_one_of_sq_eq`, `Ratpoints.Sieve.run_jacobiTest_of_sq_eq`). The
denominators that the C code computes as `long`s are at most the largest denominator.

## Main statements

* `Ratpoints.Sieve.squaresDens_eq_filter`, `Ratpoints.Sieve.mem_squaresDens_iff`: the square shape
  lists the squares of a range, in increasing order.
* `Ratpoints.Sieve.mem_squares1Dens_iff`, `Ratpoints.Sieve.nodup_squares1Dens`: the divisor shape
  lists the products `s k ^ 2` of a range, each once for distinct squarefree divisors.
* `Ratpoints.Sieve.run_denInfoTest_eq_true`, `Ratpoints.Sieve.run_denInfoTest_of_sq_eq`: the
  valuation test of the divisor shape passes a denominator that no entry excludes, so the
  denominator of every point.
* `Ratpoints.Sieve.getLsbD_wordBits`, `Ratpoints.Sieve.wordsDens_spec`,
  `Ratpoints.Sieve.toList_run_wordsDens`: the word shape lists the denominators of a range whose
  class admits a numerator and which no forbidden divisor tested with words divides, in increasing
  order.
* `Ratpoints.Sieve.run_wordsTest_eq_true`: the tests of the word shape pass when the Jacobi tests
  and the valuation entries do.
* `Ratpoints.Sieve.getLsbD_denBits_and_all_of_sq_eq`, `Ratpoints.Sieve.run_wordsTest_of_sq_eq`:
  the class bit, the forbidden divisors tested with words and the tests of the word shape let the
  denominator of every point through.
* `Ratpoints.Sieve.fitsLong_of_mem_squaresDens`, `Ratpoints.Sieve.fitsLong_of_mem_squares1Dens`,
  `Ratpoints.Sieve.fitsLong_of_mem_wordsDens`: the denominators `k ^ 2`, `s k ^ 2` and `64 w + t`
  of the C code are `long`s for a `long` largest denominator.

## Implementation notes

The contracts are proved with `vcgen`, with loop invariants that are named definitions; the tests
read the valuation and the Jacobi tests through private specifications `⦃True⦄ x ⦃fun r ↦ r =
Id.run x⦄`, so that they do not depend on the contracts of these components.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The square shapes -/

theorem ceilSqrt_le_iff {n k : ℕ} (hn : 1 ≤ n) : ceilSqrt n ≤ k ↔ n ≤ k * k := by
  rw [ceilSqrt, Nat.add_one_le_iff, Nat.sqrt_lt]
  lia

theorem le_floorSqrt_iff {n k : ℕ} : k ≤ floorSqrt n ↔ k * k ≤ n :=
  Nat.le_sqrt

theorem mem_squaresDens_iff {bLow bHigh b : ℕ} (hbLow : 1 ≤ bLow) :
    b ∈ squaresDens bLow bHigh ↔ bLow ≤ b ∧ b ≤ bHigh ∧ ∃ k, b = k * k := by
  simp only [squaresDens, List.mem_map, List.mem_range'_1]
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨(ceilSqrt_le_iff hbLow).mp hk.1, le_floorSqrt_iff.mp (by lia), k, rfl⟩
  · rintro ⟨h1, h2, k, rfl⟩
    exact ⟨k, ⟨(ceilSqrt_le_iff hbLow).mpr h1, by have := le_floorSqrt_iff.mpr h2; lia⟩, rfl⟩

theorem pairwise_lt_squaresDens (bLow bHigh : ℕ) : (squaresDens bLow bHigh).Pairwise (· < ·) :=
  List.pairwise_map.mpr ((List.pairwise_lt_range').imp Nat.mul_self_lt_mul_self)

/-- The square shape lists the squares from `bLow ≥ 1` to `bHigh`, in increasing order. -/
theorem squaresDens_eq_filter {bLow : ℕ} (hbLow : 1 ≤ bLow) (bHigh : ℕ) :
    squaresDens bLow bHigh =
      (List.range' bLow (bHigh + 1 - bLow)).filter fun b ↦ Nat.sqrt b * Nat.sqrt b == b := by
  refine (pairwise_lt_squaresDens _ _).eq_of_mem_iff ((List.pairwise_lt_range').filter _)
    fun b ↦ ?_
  simp only [mem_squaresDens_iff hbLow, List.mem_filter, List.mem_range'_1, beq_iff_eq,
    ← Nat.exists_mul_self]
  constructor
  · rintro ⟨h1, h2, k, rfl⟩
    exact ⟨⟨h1, by lia⟩, k, rfl⟩
  · rintro ⟨⟨h1, h2⟩, k, rfl⟩
    exact ⟨h1, by lia, k, rfl⟩

/-- The segment of the divisor `s > 0` in the divisor shape: `bLow ≤ s k ^ 2 ≤ bHigh` exactly for
the `k` from `⌈√(⌊(bLow - 1) / s⌋ + 1)⌉` to `⌊√⌊bHigh / s⌋⌋`, for `bLow ≥ 1`. -/
theorem mem_range'_ceilSqrt_iff {s bLow bHigh k : ℕ} (hs : 0 < s) (hbLow : 1 ≤ bLow) :
    k ∈ List.range' (ceilSqrt ((bLow - 1) / s + 1))
        (floorSqrt (bHigh / s) + 1 - ceilSqrt ((bLow - 1) / s + 1)) ↔
      bLow ≤ s * k * k ∧ s * k * k ≤ bHigh := by
  have h (a b : ℕ) : (a ≤ k ∧ k < a + (b + 1 - a)) ↔ (a ≤ k ∧ k ≤ b) := by lia
  rw [List.mem_range'_1, h, ceilSqrt_le_iff (by lia), le_floorSqrt_iff, Nat.le_div_iff_mul_le hs,
    Nat.add_one_le_iff, Nat.div_lt_iff_lt_mul hs]
  lia

/-- The products `s k ^ 2` of the divisor shape with `bLow ≤ s k ^ 2 ≤ bHigh`, for positive
divisors and `bLow ≥ 1`. -/
theorem mem_squares1Dens_iff {divisors : List ℕ} (hpos : ∀ s ∈ divisors, 0 < s) {bLow : ℕ}
    (hbLow : 1 ≤ bLow) {bHigh b : ℕ} :
    b ∈ squares1Dens divisors bLow bHigh ↔
      bLow ≤ b ∧ b ≤ bHigh ∧ ∃ s ∈ divisors, ∃ k, b = s * k * k := by
  simp only [squares1Dens, List.mem_flatMap, List.mem_map]
  constructor
  · rintro ⟨s, hs, k, hk, rfl⟩
    have := (mem_range'_ceilSqrt_iff (hpos s hs) hbLow).mp hk
    exact ⟨this.1, this.2, s, hs, k, rfl⟩
  · rintro ⟨h1, h2, s, hs, k, rfl⟩
    exact ⟨s, hs, k, (mem_range'_ceilSqrt_iff (hpos s hs) hbLow).mpr ⟨h1, h2⟩, rfl⟩

/-- The divisor shape lists each denominator once, for distinct squarefree divisors: `s k ^ 2`
determines the squarefree `s` (`Nat.eq_of_mul_sq_eq_mul_sq`), and the segments start at `k ≥ 1`. -/
theorem nodup_squares1Dens {divisors : List ℕ} (hnd : divisors.Nodup)
    (hsq : ∀ s ∈ divisors, Squarefree s) (bLow bHigh : ℕ) :
    (squares1Dens divisors bLow bHigh).Nodup := by
  refine List.nodup_flatMap.mpr ⟨fun s hs ↦ ?_, hnd.imp_of_mem fun {s s'} hs hs' hne ↦ ?_⟩
  · exact (List.nodup_range').map_on fun k _ k' _ h ↦ Nat.mul_self_inj.mp
      (Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero (hsq s hs).ne_zero)
        (by rwa [← Nat.mul_assoc, ← Nat.mul_assoc]))
  · refine List.disjoint_left.mpr fun b hb hb' ↦ hne ?_
    obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
    obtain ⟨k', hk', h⟩ := List.mem_map.mp hb'
    have : 1 ≤ k' := (List.mem_range'_1.mp hk').1.trans' (Nat.le_add_left 1 _)
    have h2 : s * k ^ 2 = s' * k' ^ 2 := by rw [sq, sq, ← Nat.mul_assoc, ← Nat.mul_assoc, h]
    exact Nat.eq_of_mul_sq_eq_mul_sq (hsq s hs) (hsq s' hs') (by lia) h2

/-- The denominators `k ^ 2` of the square shape, which the C code computes as `long`s
(`find_points.c:3922`), are at most `bHigh`, and so `long`s for a `long` `bHigh`. -/
theorem fitsLong_of_mem_squaresDens {bLow bHigh b : ℕ} (hb : b ∈ squaresDens bLow bHigh)
    (hH : bHigh < 2 ^ 63) : fitsLong (b : ℤ) = true := by
  obtain ⟨k, hk, rfl⟩ := List.mem_map.mp hb
  have := le_floorSqrt_iff.mp (by have := List.mem_range'_1.mp hk; lia : k ≤ floorSqrt bHigh)
  simp [fitsLong]
  lia

/-- The denominators `s k ^ 2` of the divisor shape, which the C code computes as `long`s
(`find_points.c:3940`), are at most `bHigh`, and so `long`s for a `long` `bHigh`, as is
`s k ≤ s k ^ 2` for `k ≥ 1`. -/
theorem fitsLong_of_mem_squares1Dens {divisors : List ℕ} {bLow bHigh b : ℕ}
    (hb : b ∈ squares1Dens divisors bLow bHigh) (hH : bHigh < 2 ^ 63) :
    fitsLong (b : ℤ) = true := by
  obtain ⟨s, -, k, hk, rfl⟩ : ∃ s ∈ divisors, ∃ k ∈ List.range' (ceilSqrt ((bLow - 1) / s + 1))
      (floorSqrt (bHigh / s) + 1 - ceilSqrt ((bLow - 1) / s + 1)), b = s * k * k := by
    simpa [squares1Dens, eq_comm] using hb
  have := le_floorSqrt_iff.mp (by have := List.mem_range'_1.mp hk; lia : k ≤ floorSqrt (bHigh / s))
  have : s * (k * k) ≤ bHigh := (Nat.mul_le_mul_left s this).trans (Nat.mul_div_le bHigh s)
  simp [fitsLong]
  lia

/-! ### The valuation test of the divisor shape -/

-- The valuation of a denominator, as a value for the contracts of the tests.
private theorem valuation_value (n : ℤ) (p : ℕ) :
    ⦃ True ⦄ Setup.valuation n p ⦃ fun r ↦ r = Id.run (Setup.valuation n p) ⦄ :=
  ⟨fun _ ↦ rfl⟩

-- The test of the loop of `Ratpoints.Sieve.denInfoTest` on an entry that does not exclude `b`.
private theorem not_slope_le_and_odd_of_mem {info pref suff : List Setup.DenInfo}
    {cur : Setup.DenInfo} {b v r : ℕ} (hinfo : ∀ e ∈ info, e.excludes b = false)
    (h : info = pref ++ cur :: suff) (hv : (v, r) = Id.run (Setup.valuation b cur.p)) :
    ¬(decide (cur.slope ≤ v) && (v + cur.val) % 2 == 1) = true := by
  have := hinfo cur (by simp [h])
  rwa [Setup.DenInfo.excludes_eq_false_iff, ← hv] at this

private theorem denInfoTest_spec {info : List Setup.DenInfo} {b : ℕ}
    (hinfo : ∀ e ∈ info, e.excludes b = false) :
    ⦃ True ⦄ denInfoTest info b ⦃ fun r ↦ r = true ⦄ := by
  vcgen [denInfoTest, valuation_value] invariants
  · fun _ _ s ↦ s.1 = none
  all_goals first
    | exact absurd ‹_› (not_slope_le_and_odd_of_mem hinfo ‹_› ‹_›)
    | grind

theorem run_denInfoTest_eq_true {info : List Setup.DenInfo} {b : ℕ}
    (hinfo : ∀ e ∈ info, e.excludes b = false) : Id.run (denInfoTest info b) = true :=
  (denInfoTest_spec hinfo).le_wp trivial

/-- The valuation test of the divisor shape, with the slopes of the divisor set-up, lets the
denominator of every point through: for `v_p(b) ≥ slope` the term `c_d a ^ d b` of `F(a, b)` alone
has the least valuation `v_p(c_d) + v_p(b)`, which is then even
(`Ratpoints.Setup.DenInfo.excludes_eq_false_of_sq_eq`). -/
theorem run_denInfoTest_of_sq_eq {c : List ℤ} {bHigh : ℕ} {info : List Setup.DenInfo}
    {divisors : List ℕ} (hd : degree c % 2 = 1)
    (hs : Id.run (Setup.setupUs1 c (degree c) bHigh) = some (info, divisors)) {a y : ℤ} {b : ℕ}
    (hb : b ≠ 0) (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    Id.run (denInfoTest info b) = true := by
  obtain ⟨fac, ⟨-, hp, -⟩, -, rfl⟩ :=
    Setup.eq_foldl_of_setupUs1_eq_some hs (getD_degree_ne_zero_of_pos (by lia))
  refine run_denInfoTest_eq_true fun e he ↦ ?_
  obtain ⟨x, hx, rfl⟩ := List.mem_map.mp he
  exact Setup.DenInfo.excludes_eq_false_of_sq_eq hd (hp x hx).1 (hp x hx).2.2 hb hab hy

/-! ### The word shape -/

-- The bound masks of `Ratpoints.Sieve.wordBits`: the word of `bLow` from bit `bLow mod 64` on, the
-- word of `bHigh` up to bit `bHigh mod 64`.
private theorem toNat_toUInt64_mod_sixtyFour (n : ℕ) : (n % 64).toUInt64.toNat % 64 = n % 64 := by
  simp [Nat.toUInt64]

private theorem toNat_toUInt64_sub_mod_sixtyFour (n : ℕ) :
    (63 - n % 64).toUInt64.toNat % 64 = 63 - n % 64 := by
  simp [Nat.toUInt64]
  lia

/-- The bits of the word of `Ratpoints.Sieve.wordBits` for a word `w` of the range from
`⌊bLow / 64⌋` to `⌊bHigh / 64⌋`: bit `t` is set exactly when bit `t` of `db` and of word `w mod p`
of every entry `p` are set and `bLow ≤ 64 w + t ≤ bHigh`. -/
theorem getLsbD_wordBits (db : UInt64) (forb : List ForbiddenEntry) {bLow bHigh w : ℕ}
    (hlo : bLow / 64 ≤ w) (hhi : w ≤ bHigh / 64) (t : ℕ) :
    (wordBits db forb bLow bHigh w).toBitVec.getLsbD t =
      (db.toBitVec.getLsbD t && (forb.all fun e ↦ e.words[w % e.p]!.toBitVec.getLsbD t) &&
        decide (bLow ≤ 64 * w + t) && decide (64 * w + t ≤ bHigh)) := by
  rcases Nat.lt_or_ge t 64 with ht | ht
  · simp only [wordBits]
    split_ifs <;> simp only [UInt64.toBitVec_and, BitVec.getLsbD_and, UInt64.getLsbD_foldl_and,
      UInt64.getLsbD_allOnes_shiftLeft, UInt64.getLsbD_allOnes_shiftRight,
      toNat_toUInt64_mod_sixtyFour, toNat_toUInt64_sub_mod_sixtyFour] <;> grind
  · simp [BitVec.getLsbD_of_ge _ _ ht]

attribute [local irreducible] WalkWhileInvariant WalkWordInvariant in
/-- The contract of `Ratpoints.Sieve.wordsDens`: for each word `w` of the range, the denominators
`64 w + t` of the set bits `t` of its word (`Ratpoints.Sieve.wordBits`), lowest first. The loops
over the set bits end, since clearing the lowest set bit makes a word other than `0` smaller. -/
@[spec]
theorem wordsDens_spec (db : UInt64) (forb : List ForbiddenEntry) (bLow bHigh : ℕ) :
    ⦃ True ⦄ wordsDens db forb bLow bHigh
    ⦃ fun out ↦ out.toList = (List.range' (bLow / 64) (bHigh / 64 + 1 - bLow / 64)).flatMap fun w ↦
        ((List.range 64).filter (wordBits db forb bLow bHigh w).toBitVec.getLsbD).map
          (64 * w + ·) ⦄ := by
  vcgen [wordsDens] invariants
  | inv1 => fun pref _ out ↦ out.toList = pref.flatMap fun w ↦
        ((List.range 64).filter (wordBits db forb bLow bHigh w).toBitVec.getLsbD).map (64 * w + ·)
  | inv2 _ cur _ _ out0 _ => WalkWhileInvariant (wordBits db forb bLow bHigh cur)
      (WalkWordInvariant (fun t ↦ [64 * cur + t]) (wordBits db forb bLow bHigh cur) out0)
  | inv3 => .ofMeasure fun s : Array ℕ × UInt64 ↦ s.2.toNat
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals subst_vars
  all_goals first
    | exact walkWhileInvariant_self (walkWordInvariant_zero ..)
    | exact bne_iff_ne.mp ‹_›
    | exact WalkWhileInvariant.exit ‹_› ‹_›
    | exact WalkWhileInvariant.and_sub_one ‹_› ‹_› fun _ hcl hk ↦
        hk.append_ctz hcl (bne_iff_ne.mp ‹_›)
    | grind [WalkWordInvariant.toList_eq, List.map_eq_flatMap]

-- The words of the entries of the word shape: bit `t < 64` of word `w mod p` says whether
-- `p ∤ 64 w + t`.
private theorem all_getLsbD_words {forb : List ForbiddenEntry} (hpos : ∀ e ∈ forb, 0 < e.p)
    (hwords : ∀ e ∈ forb, e.words = forbiddenRow e.p) (w : ℕ) {t : ℕ} (ht : t < 64) :
    (forb.all fun e ↦ e.words[w % e.p]!.toBitVec.getLsbD t) =
      forb.all fun e ↦ (64 * w + t) % e.p != 0 := by
  rw [Bool.eq_iff_iff, List.all_eq_true, List.all_eq_true]
  refine forall₂_congr fun e he ↦ ?_
  rw [hwords e he, getLsbD_getElem!_forbiddenRow (Nat.mod_lt _ (hpos e he)), decide_eq_true ht,
    Bool.true_and]
  simp [Nat.add_mod, Nat.mul_mod]

/-- The word shape lists the denominators `b` from `bLow` to `bHigh`, in increasing order, whose
class `b mod 64` has its bit in `db` and which no forbidden divisor tested with words divides, for
entries with the words of `Ratpoints.Sieve.forbiddenRow`: bit `j` of word `w mod p` of the entry `p`
is clear exactly when `p ∣ 64 w + j`. -/
theorem toList_run_wordsDens {db : UInt64} {forb : List ForbiddenEntry}
    (hpos : ∀ e ∈ forb, 0 < e.p) (hwords : ∀ e ∈ forb, e.words = forbiddenRow e.p)
    (bLow bHigh : ℕ) :
    (Id.run (wordsDens db forb bLow bHigh)).toList =
      (List.range' bLow (bHigh + 1 - bLow)).filter fun b ↦
        db.toBitVec.getLsbD (b % 64) && forb.all fun e ↦ b % e.p != 0 := by
  rw [Std.WP.Id.of_run_eq_wp rfl _ ((wordsDens_spec db forb bLow bHigh).le_wp trivial),
    List.flatMap_range'_map_filter (p := fun b ↦ (db.toBitVec.getLsbD (b % 64) &&
      forb.all fun e ↦ b % e.p != 0) && (decide (bLow ≤ b) && decide (b ≤ bHigh))),
    ← List.filter_filter, List.filter_range'_le_and_le (by lia) (by lia)]
  intro w hw hw' t ht
  rw [getLsbD_wordBits db forb hw (by lia), all_getLsbD_words hpos hwords w ht,
    Nat.mul_add_mod_self_left, Nat.mod_eq_of_lt ht, Bool.and_assoc _ (decide _)]

/-- The denominators `64 w + t` of the word shape, which the C code computes as `long`s
(`base = w << LONG_SHIFT` and `b = base + RP_CTZL(b_bits)`, `find_points.c:3991`,
`find_points.c:4008`), are at most `bHigh`, and so `long`s for a `long` `bHigh`; so is `64 w` for
the words `w ≤ ⌊bHigh / 64⌋` (`Ratpoints.Setup.fitsLong_mul_of_le_div`). -/
theorem fitsLong_of_mem_wordsDens {db : UInt64} {forb : List ForbiddenEntry} {bLow bHigh b : ℕ}
    (hb : b ∈ (Id.run (wordsDens db forb bLow bHigh)).toList) (hH : bHigh < 2 ^ 63) :
    fitsLong (b : ℤ) = true := by
  rw [Std.WP.Id.of_run_eq_wp rfl _ ((wordsDens_spec db forb bLow bHigh).le_wp trivial)] at hb
  obtain ⟨w, hw, hb⟩ := List.mem_flatMap.mp hb
  obtain ⟨t, ht, rfl⟩ := List.mem_map.mp hb
  have hw' := List.mem_range'_1.mp hw
  have := (List.mem_filter.mp ht).2
  rw [getLsbD_wordBits db forb hw'.1 (by lia)] at this
  simp only [Bool.and_eq_true, decide_eq_true_eq] at this
  simp [fitsLong]
  lia

/-! ### The tests of the word shape -/

-- The Jacobi test by tables, as a value for the contract of the tests.
private theorem jacobiTest_value (ji : JacobiInfo) (b : ℕ) :
    ⦃ True ⦄ jacobiTest ji b ⦃ fun r ↦ r = Id.run (jacobiTest ji b) ⦄ :=
  ⟨fun _ ↦ rfl⟩

-- The Jacobi symbol by the binary algorithm, as a value for the contract of the tests.
private theorem jacobi_value (b : ℕ) (lcf : ℤ) :
    ⦃ True ⦄ jacobi b lcf ⦃ fun r ↦ r = Id.run (jacobi b lcf) ⦄ :=
  ⟨fun _ ↦ rfl⟩

-- The test of the loop of `Ratpoints.Sieve.wordsTest` on an entry that does not exclude `b`.
private theorem not_testBit_of_mem {forbVal pref suff : List ForbiddenVal} {cur : ForbiddenVal}
    {b v r : ℕ} (hval : ∀ e ∈ forbVal, e.excludes b = false)
    (h : forbVal = pref ++ cur :: suff) (hv : (v, r) = Id.run (Setup.valuation b cur.p)) :
    ¬ cur.mask.testBit v = true := by
  have := hval cur (by simp [h])
  rwa [ForbiddenVal.excludes_eq_false_iff, ← hv] at this

private theorem wordsTest_spec {forbVal : List ForbiddenVal} {useJacobi : Bool}
    {fast : Option JacobiInfo} {lcf : ℤ} {b : ℕ}
    (hfast : ∀ ji, fast = some ji → Id.run (jacobiTest ji b) = true)
    (hval : ∀ e ∈ forbVal, e.excludes b = false)
    (hjac : fast = none → useJacobi = true → Id.run (jacobi b lcf) = 1) :
    ⦃ True ⦄ wordsTest forbVal useJacobi fast lcf b ⦃ fun r ↦ r = true ⦄ := by
  vcgen [wordsTest, valuation_value, jacobiTest_value, jacobi_value] invariants
  · fun _ _ s ↦ s.1 = none
  · fun _ _ s ↦ s.1 = none
  all_goals first
    | exact absurd ‹_› (not_testBit_of_mem hval ‹_› ‹_›)
    | grind [Option.isSome_iff_ne_none]

/-- The tests of the word shape on the denominator `b` pass when the Jacobi test by the tables
`fast` passes, when they are given, when no forbidden divisor tested by its valuation excludes `b`,
and when the binary algorithm gives the symbol `1`, when the Jacobi test is on without tables. -/
theorem run_wordsTest_eq_true {forbVal : List ForbiddenVal} {useJacobi : Bool}
    {fast : Option JacobiInfo} {lcf : ℤ} {b : ℕ}
    (hfast : ∀ ji, fast = some ji → Id.run (jacobiTest ji b) = true)
    (hval : ∀ e ∈ forbVal, e.excludes b = false)
    (hjac : fast = none → useJacobi = true → Id.run (jacobi b lcf) = 1) :
    Id.run (wordsTest forbVal useJacobi fast lcf b) = true :=
  (wordsTest_spec hfast hval hjac).le_wp trivial

/-! ### The tests let the denominators of the points through -/

/-- For even degree, the class bit in `Ratpoints.Sieve.denBits` and forbidden divisors tested with
words that the loop of the tables and the further primes may record for the largest denominator `H`
(`Ratpoints.Sieve.IsForbiddenEntry`) let the denominator `1 ≤ b ≤ H` of a point `(a, y, b)` through
(`Ratpoints.Sieve.classBit_twoAdic_of_sq_eq`, `Ratpoints.Sieve.IsForbiddenEntry.not_dvd`): the
filter of the list of the word shape (`Ratpoints.Sieve.toList_run_wordsDens`) keeps it. -/
theorem getLsbD_denBits_and_all_of_sq_eq {c : List ℤ} {H : ℕ} (hd : degree c % 2 = 0)
    {forb : List ForbiddenEntry} (hforb : ∀ e ∈ forb, IsForbiddenEntry c (degree c) H e)
    {a y : ℤ} {b : ℕ} (hb : b ≠ 0) (hbH : b ≤ H) (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) :
    ((denBits (Id.run (twoAdic c (degree c)))).toBitVec.getLsbD (b % 64) &&
      forb.all fun e ↦ b % e.p != 0) = true := by
  rw [Bool.and_eq_true, getLsbD_denBits]
  refine ⟨?_, List.all_eq_true.mpr fun e he ↦ ?_⟩
  · simp only [Nat.mod_lt _ (by decide : 0 < 64), decide_true, Bool.true_and, bne_iff_ne]
    exact fun h0 ↦ by simpa [h0] using classBit_twoAdic_of_sq_eq hab hy
  simpa [Nat.dvd_iff_mod_eq_zero] using (hforb e he).not_dvd hd hb hbH hab hy

/-- For even degree, the tests of the word shape, with forbidden divisors tested by their valuations
that the loop of the tables may record for the largest denominator `H`
(`Ratpoints.Sieve.IsForbiddenVal`) and the tables of the Jacobi test when it is on, let the
denominator `1 ≤ b ≤ H` of a point `(a, y, b)` through
(`Ratpoints.Sieve.IsForbiddenVal.excludes_eq_false`, `Ratpoints.Sieve.run_jacobiTest_of_sq_eq`,
`Ratpoints.Sieve.run_jacobi_eq_one_of_sq_eq`). -/
theorem run_wordsTest_of_sq_eq {c : List ℤ} {H : ℕ} (hd : degree c % 2 = 0)
    {forbVal : List ForbiddenVal} (hval : ∀ e ∈ forbVal, IsForbiddenVal c (degree c) H e)
    (useJacobi : Bool) {a y : ℤ} {b : ℕ} (hb : b ≠ 0) (hbH : b ≤ H) (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) :
    Id.run (wordsTest forbVal useJacobi
      (if useJacobi then Id.run (jacobiSetup (c.getD (degree c) 0) H) else none)
      (c.getD (degree c) 0) b) = true := by
  refine run_wordsTest_eq_true (fun ji hji ↦ ?_)
    (fun e he ↦ (hval e he).excludes_eq_false hd hb hab hy)
    fun _ _ ↦ run_jacobi_eq_one_of_sq_eq hd hb hab hy
  cases useJacobi
  · exact absurd hji (by simp)
  · exact run_jacobiTest_of_sq_eq hd hji hb hbH hab hy

end Sieve

end Ratpoints

end
