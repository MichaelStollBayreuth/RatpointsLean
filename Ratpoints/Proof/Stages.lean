/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Words

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Reductions
import Std.Tactic.Do

/-!
# The contracts of the stages of the sieve

The test for common factors on the 64-bit words of the C code (`Ratpoints.Sieve.relprime`) decides
whether a numerator is prime to the denominator, and none of its operations leaves the range of a
`long`. For a numerator `a` prime to the denominator `b` with `|a| ≤ H`, the third stage
(`Ratpoints.Sieve.stage3`) with the sieve entries of primes `1 < p ≤ 2 ^ 32` with their tables and
reciprocals (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`) is the test of the rows of these entries: it
reads the table of each prime at `a b⁻¹ mod p`, in both branches of the bias, and a prime that
divides `b` admits every numerator prime to `b`; the values that the C code holds in `long`s stay in
range. So the test of a candidate (`Ratpoints.Sieve.accepted`), for `|a| < 2 ^ 63` and
`0 < b < 2 ^ 63`, followed by the exact check (`Ratpoints.Sieve.checkPoint`), gives the points of
the check of the reference (`Ratpoints.Sieve.checkNum`) for the numerators that survive these
entries. The second stage on a bit array (`Ratpoints.Sieve.secondStage`), or on one of its words
(`Ratpoints.Sieve.secondStageWord`), gives its words and-ed with the rows of all its moduli
(`Ratpoints.Sieve.andWords`), although it stops when the bit array or the word is zero. The
contracts of the loops are `@[spec]` theorems proved with `vcgen`, the program logic of Lean core,
with loop invariants that are named definitions.

## Main definitions

* `Ratpoints.Sieve.RelprimeOddInvariant`: the invariant of the loop of the binary algorithm.
* `Ratpoints.Sieve.CheckSpec.admits`, `Ratpoints.Sieve.Stage3Invariant`: whether the third stage
  lets a numerator through one of its primes, and the invariant of its loop.
* `Ratpoints.Sieve.SieveEntry.IsPrimeEntry`: the shape of the sieve entries of the third stage.
* `Ratpoints.Sieve.acceptedPoints`: the points that the extraction gives for a numerator, those of
  the exact check when the numerator passes the test of a candidate, the test for common factors
  and the third stage.
* `Ratpoints.Sieve.SecondStageInvariant`: the invariant of the loop of the second stage on a bit
  array.

## Main statements

* `Ratpoints.Sieve.relprimeOdd_spec`, `Ratpoints.Sieve.relprime_spec`: the binary algorithm
  decides whether `gcd(m, n) = 1` for odd positive words `m` and `n`, and for words
  `m > -2 ^ 63` and `n ≥ 1`.
* `Ratpoints.Sieve.stage3_spec`: the third stage is whether all its primes admit the numerator.
* `Ratpoints.Sieve.CheckSpec.index_eq`: the residue at which it reads the table of a prime is
  `(a mod p) binv mod p`, with the bias and without it.
* `Ratpoints.Sieve.CheckSpec.admits_checkOf`, `Ratpoints.Sieve.run_stage3_fillChecks`: for a
  numerator prime to `b` with `|a| ≤ H`, a prime entry admits it in the third stage exactly when
  its row of `b` does, and the third stage is the survivor test of its entries.
* `Ratpoints.Sieve.accepted_spec`: the test of a candidate is the test of `gcd(a, b) = 1` followed
  by the third stage; `Ratpoints.Sieve.acceptedPoints_eq_ite`: for a numerator `a` with
  `|a| ≤ H < 2 ^ 63` and a denominator `0 < b < 2 ^ 63`, the test with the exact check gives the
  points of the check of the reference (`Ratpoints.Sieve.checkNum`) when `a` survives the entries
  of the third stage, and none otherwise.
* `Ratpoints.Sieve.secondStage_spec`, `Ratpoints.Sieve.secondStageWord_spec`: the second stage on a
  bit array, or on one of its words, gives its words and-ed with the rows of all its moduli.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Words` does, on whose words of the rows
(`Ratpoints.Sieve.SieveSpec.wordAt`, `Ratpoints.Sieve.andWords`) the second stage builds. The proofs
use only the facts on the constants that `decide` checks next to them, that
`Ratpoints.mulModLimit < 2 ^ 32` and `Ratpoints.stage3Limit ≤ 2 ^ 32`, never their values. The words
of the test for common factors are read as natural numbers by `Int64.toNatClampNeg`, which is
faithful on the non-negative words that the binary algorithm keeps; the facts on words that are not
about the model are in `Ratpoints.Proof.Bits`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The test for common factors -/

/-- The invariant of the loop of `Ratpoints.Sieve.relprimeOdd`, whose state is `(m, n)`: both words
are odd as natural numbers (`Int64.toNatClampNeg`), and so positive, they have the gcd `g` of the
operands, and `m = n` at the exit. -/
def RelprimeOddInvariant (g : Nat) : Std.WP.WhileInvariant (Int64 × Int64) Prop :=
  .mk fun exit s ↦ s.1.toNatClampNeg % 2 = 1 ∧ s.2.toNatClampNeg % 2 = 1 ∧
    Nat.gcd s.1.toNatClampNeg s.2.toNatClampNeg = g ∧ (exit = true → s.1 = s.2)

theorem relprimeOddInvariant_self {m n : Int64}
    (h : m.toNatClampNeg % 2 = 1 ∧ n.toNatClampNeg % 2 = 1) :
    RelprimeOddInvariant (Nat.gcd m.toNatClampNeg n.toNatClampNeg) false (m, n) :=
  ⟨h.1, h.2, rfl, nofun⟩

/-- In the loop of `Ratpoints.Sieve.relprimeOdd`, from `m ≠ n`, the absolute value of the difference
is a word other than `0`, whose lowest set bit `RP_CTZL` may look for. -/
theorem RelprimeOddInvariant.toUInt64_ne_zero {g k : Nat} {m n : Int64} (hmn : (n != m) = true)
    (h : m.toNatClampNeg + n.toNatClampNeg = k ∧ RelprimeOddInvariant g false (m, n)) :
    ¬((m - n ^^^ (m - n) >>> 63) - (m - n) >>> 63).toUInt64 = 0 := by
  obtain ⟨-, hm, hn, -⟩ := h
  exact Int64.toUInt64_ne_zero_of_pos (Int64.xor_shiftRight_63_sub_pos
    (Int64.le_of_lt ((Int64.toNatClampNeg_pos_iff m).mp (by lia)))
    (Int64.le_of_lt ((Int64.toNatClampNeg_pos_iff n).mp (by lia))) (bne_iff_ne.mp hmn).symm)

/-- A step of the loop of `Ratpoints.Sieve.relprimeOdd` from `m ≠ n`, in the shape of the
verification condition: `n` becomes the smaller of the two and `m` the odd part of their distance
`d`, which keep what the loop keeps, and their sum, the measure, decreases. -/
theorem RelprimeOddInvariant.shiftRight_min {g k t : Nat} {m n d : Int64} (hmn : (n != m) = true)
    (h : m.toNatClampNeg + n.toNatClampNeg = k ∧ RelprimeOddInvariant g false (m, n))
    (hd : d = (m - n ^^^ (m - n) >>> 63) - (m - n) >>> 63)
    (ht : t = d.toUInt64.toBitVec.ctz.toNat) :
    (d >>> Int64.ofNat t).toNatClampNeg + (n + (m - n &&& (m - n) >>> 63)).toNatClampNeg < k ∧
      RelprimeOddInvariant g false (d >>> Int64.ofNat t, n + (m - n &&& (m - n) >>> 63)) := by
  obtain ⟨rfl, hm, hn, rfl, -⟩ := h
  have hm0 := Int64.le_of_lt ((Int64.toNatClampNeg_pos_iff m).mp (by lia))
  have hn0 := Int64.le_of_lt ((Int64.toNatClampNeg_pos_iff n).mp (by lia))
  have hd0 : 0 < d := hd ▸ Int64.xor_shiftRight_63_sub_pos hm0 hn0 (bne_iff_ne.mp hmn).symm
  have h1 := Int64.two_pow_ctz_mul_toNatClampNeg_shiftRight hd0
  rw [hd, Int64.toNatClampNeg_xor_shiftRight_63_sub hm0 hn0, ← hd] at h1
  subst ht
  refine ⟨?_, Int64.toNatClampNeg_shiftRight_ctz_mod_two hd0, ?_, ?_, nofun⟩ <;>
    rw [Int64.toNatClampNeg_add_and_shiftRight_63 hm0 hn0]
  · exact Nat.add_min_lt_add_of_two_pow_mul_eq (by lia) (by lia) h1
  · lia
  · exact Nat.gcd_min_eq_gcd_of_two_pow_mul_eq hm hn h1

theorem RelprimeOddInvariant.exit {g k : Nat} {m n : Int64} (hmn : ¬(n != m) = true)
    (h : m.toNatClampNeg + n.toNatClampNeg = k ∧ RelprimeOddInvariant g false (m, n)) :
    RelprimeOddInvariant g true (m, n) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, fun _ ↦ (bne_eq_false_iff_eq.mp (Bool.eq_false_iff.mpr hmn)).symm⟩

/-- At the exit of the loop of `Ratpoints.Sieve.relprimeOdd`, `m = n` is the gcd `g`. -/
theorem RelprimeOddInvariant.post {g : Nat} {m n : Int64}
    (h : RelprimeOddInvariant g true (m, n)) :
    (m == 1) = decide (g = 1) := by
  obtain ⟨-, -, rfl, h⟩ := h
  rw [← h rfl, Nat.gcd_self, Bool.beq_eq_decide_eq, decide_eq_decide,
    Int64.toNatClampNeg_eq_one_iff]

attribute [local irreducible] RelprimeOddInvariant in
/-- The loop ends, since the sum of the two values decreases, and it ends at `m = n = gcd(m, n)`;
no operation leaves the range of a `long`, since the values stay positive. -/
@[spec]
theorem relprimeOdd_spec (m n : Int64) :
    ⦃ m.toNatClampNeg % 2 = 1 ∧ n.toNatClampNeg % 2 = 1 ⦄ relprimeOdd m n
      ⦃ fun r ↦ r = decide (Nat.gcd m.toNatClampNeg n.toNatClampNeg = 1) ⦄ := by
  vcgen [relprimeOdd] invariants
  · RelprimeOddInvariant (Nat.gcd m.toNatClampNeg n.toNatClampNeg)
  · Std.WP.Variant.ofMeasure fun s : Int64 × Int64 ↦ s.1.toNatClampNeg + s.2.toNatClampNeg
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals first
    | exact relprimeOddInvariant_self ‹_›
    | exact RelprimeOddInvariant.post ‹_›
    | exact RelprimeOddInvariant.toUInt64_ne_zero ‹_› ‹_›
    | exact RelprimeOddInvariant.shiftRight_min ‹_› ‹_› rfl ‹_›
    | exact RelprimeOddInvariant.exit ‹_› ‹_›

-- A numerator `m ≠ 0` other than `-2 ^ 63` by its absolute value, a positive word, which has the
-- gcd of `m` with the positive word `n`.
private theorem ite_neg_pos_and_gcd_eq {m n : Int64} (h : Int64.minValue < m ∧ 0 < n)
    (hm : ¬(m == 0) = true) :
    0 < (if m < 0 then -m else m) ∧ 0 < n ∧ Int.gcd m.toInt n.toInt =
      Nat.gcd (if m < 0 then -m else m).toNatClampNeg n.toNatClampNeg := by
  have h1 := Int64.toNatClampNeg_ite_neg h.1
  refine ⟨(Int64.toNatClampNeg_pos_iff _).mp ?_, h.2, ?_⟩
  · rw [h1, Int.natAbs_pos, ← Int64.toInt_zero, Ne, Int64.toInt_inj]
    exact fun h' ↦ hm (beq_iff_eq.mpr h')
  · rw [h1, Int64.toNatClampNeg_eq_natAbs (Int64.le_of_lt h.2)]
    rfl

-- The numerator `0`, prime to the positive word `n` when `n = 1`.
private theorem beq_one_eq_decide_gcd {m n : Int64} (h : Int64.minValue < m ∧ 0 < n)
    (hm : (m == 0) = true) : (n == 1) = decide (Int.gcd m.toInt n.toInt = 1) := by
  rw [beq_iff_eq.mp hm, Int64.toInt_zero, Int.gcd_zero_left, ← Int64.toNatClampNeg_eq_natAbs
    (Int64.le_of_lt h.2), Bool.beq_eq_decide_eq, decide_eq_decide, Int64.toNatClampNeg_eq_one_iff]

-- Two even positive words, which are not coprime.
private theorem false_eq_decide_gcd {m n x : Int64}
    (hx : 0 < x ∧ 0 < n ∧ Int.gcd m.toInt n.toInt = Nat.gcd x.toNatClampNeg n.toNatClampNeg)
    (hxe : (x &&& 1 == 0) = true) (hne : (n &&& 1 == 0) = true) :
    false = decide (Int.gcd m.toInt n.toInt = 1) := by
  have h1 := (Int64.and_one_beq_zero_iff (Int64.le_of_lt hx.1)).mp hxe
  have h2 := (Int64.and_one_beq_zero_iff (Int64.le_of_lt hx.2.1)).mp hne
  refine (decide_eq_false fun h ↦ ?_).symm
  have := Nat.dvd_gcd (Nat.dvd_of_mod_eq_zero h1) (Nat.dvd_of_mod_eq_zero h2)
  rw [← hx.2.2, h] at this
  lia

-- The odd parts of two positive words.
private theorem toNatClampNeg_shiftRight_mod_two {m n x : Int64} {s t : Nat}
    (hx : 0 < x ∧ 0 < n ∧ Int.gcd m.toInt n.toInt = Nat.gcd x.toNatClampNeg n.toNatClampNeg)
    (ht : t = x.toUInt64.toBitVec.ctz.toNat) (hs : s = n.toUInt64.toBitVec.ctz.toNat) :
    (x >>> Int64.ofNat t).toNatClampNeg % 2 = 1 ∧ (n >>> Int64.ofNat s).toNatClampNeg % 2 = 1 := by
  subst ht hs
  exact ⟨Int64.toNatClampNeg_shiftRight_ctz_mod_two hx.1,
    Int64.toNatClampNeg_shiftRight_ctz_mod_two hx.2.1⟩

-- An odd positive word and the odd part of a positive word.
private theorem toNatClampNeg_mod_two_of_and_one {m n x : Int64} {s : Nat}
    (hx : 0 < x ∧ 0 < n ∧ Int.gcd m.toInt n.toInt = Nat.gcd x.toNatClampNeg n.toNatClampNeg)
    (hxo : ¬(x &&& 1 == 0) = true) (hs : s = n.toUInt64.toBitVec.ctz.toNat) :
    x.toNatClampNeg % 2 = 1 ∧ (n >>> Int64.ofNat s).toNatClampNeg % 2 = 1 := by
  have := mt (Int64.and_one_beq_zero_iff (Int64.le_of_lt hx.1)).mpr hxo
  exact ⟨by lia, hs ▸ Int64.toNatClampNeg_shiftRight_ctz_mod_two hx.2.1⟩

-- The odd parts of a positive word and of an odd positive word have the gcd of the two words.
private theorem eq_decide_gcd_of_shiftRight {m n x : Int64} {s t : Nat} {r : Bool}
    (hx : 0 < x ∧ 0 < n ∧ Int.gcd m.toInt n.toInt = Nat.gcd x.toNatClampNeg n.toNatClampNeg)
    (hno : ¬(n &&& 1 == 0) = true) (hr : r = decide
      (Nat.gcd (x >>> Int64.ofNat t).toNatClampNeg (n >>> Int64.ofNat s).toNatClampNeg = 1))
    (ht : t = x.toUInt64.toBitVec.ctz.toNat) (hs : s = n.toUInt64.toBitVec.ctz.toNat) :
    r = decide (Int.gcd m.toInt n.toInt = 1) := by
  subst ht hs hr
  have := mt (Int64.and_one_beq_zero_iff (Int64.le_of_lt hx.2.1)).mpr hno
  rw [hx.2.2, decide_eq_decide, Nat.gcd_comm, Nat.gcd_eq_of_two_pow_mul_eq
    (Int64.two_pow_ctz_mul_toNatClampNeg_shiftRight hx.2.1)
    (Int64.toNatClampNeg_shiftRight_ctz_mod_two hx.1), Nat.gcd_comm,
    Nat.gcd_eq_of_two_pow_mul_eq (Int64.two_pow_ctz_mul_toNatClampNeg_shiftRight hx.1) (by lia)]

-- An odd positive word and the odd part of a positive word have the gcd of the two words.
private theorem eq_decide_gcd_of_shiftRight_right {m n x : Int64} {s : Nat} {r : Bool}
    (hx : 0 < x ∧ 0 < n ∧ Int.gcd m.toInt n.toInt = Nat.gcd x.toNatClampNeg n.toNatClampNeg)
    (hxo : ¬(x &&& 1 == 0) = true)
    (hr : r = decide (Nat.gcd x.toNatClampNeg (n >>> Int64.ofNat s).toNatClampNeg = 1))
    (hs : s = n.toUInt64.toBitVec.ctz.toNat) :
    r = decide (Int.gcd m.toInt n.toInt = 1) := by
  subst hs hr
  have := mt (Int64.and_one_beq_zero_iff (Int64.le_of_lt hx.1)).mpr hxo
  rw [hx.2.2, decide_eq_decide, Nat.gcd_comm, Nat.gcd_eq_of_two_pow_mul_eq
    (Int64.two_pow_ctz_mul_toNatClampNeg_shiftRight hx.2.1) (by lia), Nat.gcd_comm]

/-- The binary algorithm decides whether the numerator `m` is prime to the denominator `n ≥ 1`, for
`m` other than `-2 ^ 63`, whose negation would leave the range of a `long`; no operation leaves
it. -/
@[spec]
theorem relprime_spec (m n : Int64) :
    ⦃ Int64.minValue < m ∧ 0 < n ⦄ relprime m n
      ⦃ fun r ↦ r = decide (Int.gcd m.toInt n.toInt = 1) ⦄ := by
  vcgen [relprime]
  -- at reducible transparency, so that an alternative that does not fit fails at once instead of
  -- unfolding the operations on the words
  all_goals with_reducible first
    | exact beq_one_eq_decide_gcd ‹_› ‹_›
    | exact Int64.toUInt64_ne_zero_of_pos ‹_ ∧ 0 < n›.2
    | exact Int64.toUInt64_ne_zero_of_pos (ite_neg_pos_and_gcd_eq ‹_› ‹_›).1
    | exact false_eq_decide_gcd (ite_neg_pos_and_gcd_eq ‹_› ‹_›) ‹_› ‹_›
    | exact eq_decide_gcd_of_shiftRight (ite_neg_pos_and_gcd_eq ‹_› ‹_›) ‹_› ‹_› ‹_› ‹_›
    | exact eq_decide_gcd_of_shiftRight_right (ite_neg_pos_and_gcd_eq ‹_› ‹_›) ‹_› ‹_› ‹_›
    | exact toNatClampNeg_shiftRight_mod_two (ite_neg_pos_and_gcd_eq ‹_› ‹_›) ‹_› ‹_›
    | exact toNatClampNeg_mod_two_of_and_one (ite_neg_pos_and_gcd_eq ‹_› ‹_›) ‹_› ‹_›

/-! ### The third stage -/

/-- Whether the third stage lets the numerator `a` through the prime of `cs`: when the prime divides
the denominator (`binv = 0`), or when its table marks the residue at which the stage reads it
(`Ratpoints.Sieve.CheckSpec.index`). -/
def CheckSpec.admits (cs : CheckSpec) (a : Int) : Bool := cs.binv == 0 || cs.isFSquare[cs.index a]!

theorem CheckSpec.admits_of_binv_eq_zero {cs : CheckSpec} (a : Int) (h : cs.binv = 0) :
    cs.admits a = true := by
  simp [admits, h]

theorem CheckSpec.admits_of_not_not {cs : CheckSpec} {a : Int}
    (h : ¬(!cs.isFSquare[cs.index a]!) = true) : cs.admits a = true := by
  simp_all [admits]

theorem CheckSpec.admits_eq_false {cs : CheckSpec} {a : Int} (h0 : ¬cs.binv = 0)
    (h : (!cs.isFSquare[cs.index a]!) = true) : cs.admits a = false := by
  simp_all [admits]

/-- The invariant of the loop of `Ratpoints.Sieve.stage3` over `checks`, after the checks `pref`
with the checks `suff` still to come, on the result of an early return: without one, the checks so
far let `a` through; with one, at the end, the result is whether all the checks do. -/
def Stage3Invariant (a : Int) (checks pref suff : List CheckSpec) (st : Option Bool × PUnit) :
    Prop :=
  st.1.elim (pref.all (·.admits a) = true) fun r ↦ suff = [] ∧ r = checks.all (·.admits a)

theorem stage3Invariant_nil (a : Int) (checks : List CheckSpec) :
    Stage3Invariant a checks [] checks (none, PUnit.unit) :=
  rfl

theorem Stage3Invariant.push {a : Int} {checks pref suff : List CheckSpec} {cur : CheckSpec}
    {o : Option Bool} {u : PUnit} (h : Stage3Invariant a checks pref (cur :: suff) (o, u))
    (hc : cur.admits a = true) :
    Stage3Invariant a checks (pref ++ [cur]) suff (none, PUnit.unit) := by
  cases o with
  | none => simpa [Stage3Invariant, hc] using h
  | some => exact absurd h.1 (List.cons_ne_nil _ _)

theorem stage3Invariant_some_false {a : Int} {checks pref suff : List CheckSpec} {cur : CheckSpec}
    (hl : checks = pref ++ cur :: suff) (hc : cur.admits a = false) :
    Stage3Invariant a checks checks [] (some false, PUnit.unit) :=
  ⟨rfl, by simp [hl, hc]⟩

theorem Stage3Invariant.eq_all_of_some {a : Int} {checks : List CheckSpec} {o : Option Bool}
    {u : PUnit} {r : Bool} (h : Stage3Invariant a checks checks [] (o, u))
    (ho : (o, u).fst = some r) : r = checks.all (·.admits a) := by
  subst ho
  exact h.2

theorem Stage3Invariant.true_eq_all_of_none {a : Int} {checks : List CheckSpec} {o : Option Bool}
    {u : PUnit} (h : Stage3Invariant a checks checks [] (o, u)) (ho : (o, u).fst = none) :
    true = checks.all (·.admits a) := by
  subst ho
  exact h.symm

attribute [local irreducible] Stage3Invariant in
/-- The third stage stops at the first prime that rejects the numerator, which is what all its
primes say then. -/
@[spec]
theorem stage3_spec (a : Int) (checks : List CheckSpec) :
    ⦃ True ⦄ stage3 a checks ⦃ fun r ↦ r = checks.all (·.admits a) ⦄ := by
  vcgen [stage3] invariants
  · Stage3Invariant a checks
  all_goals first
    | exact stage3Invariant_nil a checks
    | exact Stage3Invariant.push ‹_› (CheckSpec.admits_of_binv_eq_zero a ‹_›)
    | exact Stage3Invariant.push ‹_› (CheckSpec.admits_of_not_not ‹_›)
    | exact stage3Invariant_some_false ‹_› (CheckSpec.admits_eq_false ‹_› ‹_›)
    | exact Stage3Invariant.eq_all_of_some ‹_› ‹_›
    | exact Stage3Invariant.true_eq_all_of_none ‹_› ‹_›

@[simp]
theorem p_checkOf (b H : Nat) (e : SieveEntry) (mg : Nat) : (checkOf b H e mg).p = e.p := by
  simp only [checkOf]
  split <;> rfl

@[simp]
theorem magic_checkOf (b H : Nat) (e : SieveEntry) (mg : Nat) :
    (checkOf b H e mg).magic = e.magic := by
  simp only [checkOf]
  split <;> rfl

theorem bias_checkOf (b H p : Nat) (t : Entry) (m mg : Nat) :
    (checkOf b H ⟨p, [.prime t], m⟩ mg).bias = if 2 * p * H < stage3Limit then p * H else 0 :=
  rfl

theorem isFSquare_checkOf (b H p : Nat) (t : Entry) (m mg : Nat) :
    (checkOf b H ⟨p, [.prime t], m⟩ mg).isFSquare = t.isFSquare :=
  rfl

/-- The inverse of the denominator `b` that `Ratpoints.Sieve.checkOf` takes from the table `t` of
the prime `p ≤ 2 ^ 32` with the reciprocal of `p`: `0` when `p` divides `b`, and otherwise the entry
of `t` at `b mod p`, which the reduction by the reciprocal gives for `b ≤ Ratpoints.mulModLimit`. -/
theorem binv_checkOf {b : Nat} (H : Nat) {p : Nat} (t : Entry) (m : Nat) (hp : 0 < p)
    (hp32 : p ≤ 2 ^ 32) :
    (checkOf b H ⟨p, [.prime t], m⟩ (magic p)).binv =
      if b % p = 0 then 0 else t.inverses[b % p]! := by
  have : (if b ≤ mulModLimit then mulMod b p (magic p) else b % p) = b % p := by
    split
    · exact mulMod_magic hp (mul_lt_two_pow_64_of_le_mulModLimit ‹_› hp32)
    · rfl
  simp only [checkOf, this]

/-- The value `a binv + p H` that the third stage reduces with the bias `p H`, for `|a| ≤ H` and
`binv < p`, is at least `H` (`sift.c:303`): a natural number. -/
theorem le_mul_add_natCast_mul {a : Int} {p binv H : Nat} (ha : a.natAbs ≤ H) (hb : binv < p) :
    (H : Int) ≤ a * binv + (p * H : Nat) := by
  have := Int.natAbs_mul_add_le_mul ha hb
  lia

/-- The value `a binv + p H` that the third stage reduces with the bias `p H`, for `|a| ≤ H` and
`binv < p`, is at most `2 p H - H` (`sift.c:303`), below the bound `2 p H < Ratpoints.stage3Limit`
of the bias, and so a `long`. -/
theorem mul_add_natCast_mul_le_two_mul_mul_sub {a : Int} {p binv H : Nat} (ha : a.natAbs ≤ H)
    (hb : binv < p) : a * binv + (p * H : Nat) ≤ 2 * p * H - H := by
  have := Int.natAbs_mul_add_le_mul ha hb
  push_cast
  lia

/-- The product `am binv` that the third stage reduces without the bias, of the residue `am` of the
numerator modulo `p` and the inverse `binv < p`, is below `p ^ 2` (`sift.c:307`), a `long` for the
moduli below `2 ^ 31`. -/
theorem toNat_emod_mul_lt_sq (a : Int) {p binv : Nat} (hb : binv < p) :
    (a % p).toNat * binv < p ^ 2 :=
  Nat.pow_two p ▸ Nat.mul_lt_mul_of_lt_of_lt (Int.toNat_emod_lt a (Nat.zero_lt_of_lt hb)) hb

/-- With the bias `p H`, for `|a| ≤ H`, `binv < p` and `2 p H < 2 ^ 32`, the value `a binv + p H`
reduced by the reciprocal of `p` is the residue of `(a mod p) binv`: the value is below `2 ^ 32`,
and so is `p` unless `a = H = 0`. -/
theorem mulMod_toNat_mul_add_mul_magic {a : Int} {p binv H : Nat} (ha : a.natAbs ≤ H)
    (hb : binv < p) (hH : 2 * p * H < 2 ^ 32) :
    mulMod (a * binv + (p * H : Nat)).toNat p (magic p) = (a % p).toNat * binv % p := by
  have hp := Nat.zero_lt_of_lt hb
  have h1 := le_mul_add_natCast_mul ha hb
  have h2 := mul_add_natCast_mul_le_two_mul_mul_sub ha hb
  have hu : (a * binv + (p * H : Nat)).toNat * p < 2 ^ 64 := by
    rcases Nat.eq_zero_or_pos H with rfl | hH0
    · simp [show a = 0 by lia]
    · have hp32 : p < 2 ^ 32 := by have := Nat.le_mul_of_pos_right p hH0; lia
      have hu32 : (a * binv + (p * H : Nat)).toNat < 2 ^ 32 := by push_cast at h2 ⊢; lia
      exact Nat.lt_of_lt_of_le
        (Nat.mul_lt_mul_of_lt_of_le hu32 (Nat.le_of_lt hp32) (Nat.two_pow_pos 32)) (by decide)
  rw [mulMod_magic hp hu, Int.toNat_mul_add_natCast_mul_mod hp (by lia)]

/-- The residue at which the third stage reads the table of the prime `p` of `cs` for the
numerator `a` with `|a| ≤ H` is `(a mod p) binv mod p`, for `binv < p`, in both branches: with the
bias `p H`, for `2 p H < 2 ^ 32` and the reciprocal of `p`, and without it. -/
theorem CheckSpec.index_eq {cs : CheckSpec} {a : Int} {H : Nat} (hb : cs.binv < cs.p)
    (ha : a.natAbs ≤ H) (hbias : cs.bias ≠ 0 → cs.bias = cs.p * H ∧ 2 * cs.p * H < 2 ^ 32 ∧
      cs.magic = Sieve.magic cs.p) :
    cs.index a = (a % cs.p).toNat * cs.binv % cs.p := by
  have hp := Nat.zero_lt_of_lt hb
  rw [index]
  split
  · obtain ⟨h1, h2, h3⟩ := hbias ‹_›
    rw [h1, h3]
    exact mulMod_toNat_mul_add_mul_magic ha hb h2
  · dsimp only
    rw [Int.ite_tmod_lt_zero_eq_emod a (Int.natCast_pos.mpr hp), Int.tmod_eq_emod_of_nonneg
      (Int.mul_nonneg (Int.emod_nonneg a (by lia)) (Int.natCast_nonneg _)),
      Int.toNat_emod_mul_emod a _ hp]

theorem SieveEntry.admits_prime (t : Entry) (b : Nat) (a : Int) (m : Nat) :
    SieveEntry.admits ⟨t.p, [.prime t], m⟩ b a = t.admits b a := by
  simp [SieveEntry.admits, Factor.admits, Entry.admits]

/-- The third stage with the table `t` of a prime `1 < p ≤ 2 ^ 32`, whose inverses of the nonzero
residues are nonzero residues, and with the reciprocal of `p`, lets a numerator `a` prime to `b`
with `|a| ≤ H` through exactly when the row of `b` in `t` admits it: when `p` divides `b`, since
then `p ∤ a`, and otherwise since the stage reads the table at `(a mod p) b⁻¹ mod p`
(`Ratpoints.Sieve.CheckSpec.index_eq`). -/
theorem CheckSpec.admits_checkOf {t : Entry} {b H : Nat} {a : Int} (h1 : 1 < t.p)
    (h32 : t.p ≤ 2 ^ 32) (hinv : ∀ r < t.p, r ≠ 0 → t.inverses[r]! ≠ 0 ∧ t.inverses[r]! < t.p)
    (hab : Int.gcd a b = 1) (ha : a.natAbs ≤ H) :
    (checkOf b H ⟨t.p, [.prime t], Sieve.magic t.p⟩ (Sieve.magic t.p)).admits a = t.admits b a := by
  have hb := binv_checkOf (b := b) H t (Sieve.magic t.p) (by lia) h32
  by_cases hr : b % t.p = 0
  · simp only [hr, ↓reduceIte] at hb
    simp [CheckSpec.admits_of_binv_eq_zero a hb, Entry.admits, hr,
      Int.toNat_emod_ne_zero_of_gcd_eq_one h1 hab hr]
  obtain ⟨hi0, hilt⟩ := hinv (b % t.p) (Nat.mod_lt _ (by lia)) hr
  simp only [hr, ↓reduceIte] at hb
  have hi : (checkOf b H ⟨t.p, [.prime t], Sieve.magic t.p⟩ (Sieve.magic t.p)).index a =
      (a % t.p).toNat * t.inverses[b % t.p]! % t.p := by
    rw [CheckSpec.index_eq (H := H) (hb ▸ hilt) ha, hb]
    · rfl
    intro h0
    by_cases hc : 2 * t.p * H < stage3Limit
    · simp only [bias_checkOf, p_checkOf, magic_checkOf, hc, ↓reduceIte]
      exact ⟨trivial, Nat.lt_of_lt_of_le hc stage3Limit_le_two_pow_32, trivial⟩
    · simp [bias_checkOf, hc] at h0
  simp [CheckSpec.admits, Entry.admits, hr, hb, hi, hi0, isFSquare_checkOf]

/-- The sieve entry `e` is that of a modulus `1 < p ≤ 2 ^ 32` whose single factor is a table `t` of
`p` with inverses of the residues `0 < r < p` that are residues `0 < t.inverses[r]! < p`, and whose
reciprocal is that of `p` (`Ratpoints.Sieve.magic`): the shape that the third stage needs of its
entries (`Ratpoints.Sieve.checkOf`), whose rows it then tests
(`Ratpoints.Sieve.run_stage3_fillChecks`). The entry of a prime with the table of the reference has
it (`Ratpoints.Sieve.isPrimeEntry_examinePrime`). -/
def SieveEntry.IsPrimeEntry (e : SieveEntry) : Prop :=
  ∃ t : Entry, e = ⟨t.p, [.prime t], Sieve.magic t.p⟩ ∧ 1 < t.p ∧ t.p ≤ 2 ^ 32 ∧
    ∀ r < t.p, r ≠ 0 → t.inverses[r]! ≠ 0 ∧ t.inverses[r]! < t.p

theorem SieveEntry.IsPrimeEntry.admits_checkOf {e : SieveEntry} (he : e.IsPrimeEntry) {b H : Nat}
    {a : Int} (hab : Int.gcd a b = 1) (ha : a.natAbs ≤ H) :
    (checkOf b H e (Sieve.magic e.p)).admits a = e.admits b a := by
  obtain ⟨t, rfl, h1, h32, hinv⟩ := he
  rw [CheckSpec.admits_checkOf h1 h32 hinv hab ha, SieveEntry.admits_prime]

/-- For a numerator `a` prime to `b` with `|a| ≤ H`, what the third stage needs of the sieve entries
`es` of the shape of `Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, with the reciprocals of their
moduli, lets `a` through exactly when `a` survives these entries. -/
theorem all_admits_fillChecks {es : List SieveEntry} (hes : ∀ e ∈ es, e.IsPrimeEntry) {a : Int}
    {b H : Nat} (hab : Int.gcd a b = 1) (ha : a.natAbs ≤ H) :
    (fillChecks b H es (es.map fun e ↦ magic e.p)).all (·.admits a) = survives es b a := by
  refine Bool.eq_iff_iff.mpr ?_
  simp only [fillChecks, List.zipWith_map_right, List.zipWith_self, List.all_map, survives,
    List.all_eq_true, Function.comp_apply]
  exact ⟨fun h e he ↦ (hes e he).admits_checkOf hab ha ▸ h e he,
    fun h e he ↦ ((hes e he).admits_checkOf hab ha).symm ▸ h e he⟩

/-- **The third stage.** For a numerator `a` prime to `b` with `|a| ≤ H`, the third stage with the
sieve entries `es` of its primes and the reciprocals of their moduli, for `b` and `H`, is the
survivor test of these entries. -/
theorem run_stage3_fillChecks {es : List SieveEntry} (hes : ∀ e ∈ es, e.IsPrimeEntry) {a : Int}
    {b H : Nat} (hab : Int.gcd a b = 1) (ha : a.natAbs ≤ H) :
    Id.run (stage3 a (fillChecks b H es (es.map fun e ↦ magic e.p))) = survives es b a := by
  rw [Std.WP.Id.of_run_eq_wp rfl _ ((stage3_spec a _).le_wp trivial),
    all_admits_fillChecks hes hab ha]

/-! ### The test of a candidate -/

/-- The test for common factors on the words of the numerator `|a| < 2 ^ 63` and the denominator
`0 < b < 2 ^ 63` is the test on the integers, and the thunk of the third stage is forced only when
the numerator is prime to `b`. -/
@[spec]
theorem accepted_spec (a : Int) (b : Nat) (checks : Thunk (List CheckSpec)) :
    ⦃ 0 < b ∧ a.natAbs < 2 ^ 63 ∧ b < 2 ^ 63 ⦄ accepted a b checks
    ⦃ fun r ↦ r = (decide (Int.gcd a b = 1) && checks.get.all (·.admits a)) ⦄ := by
  vcgen [accepted]
  all_goals obtain ⟨hb0, ha, hb⟩ := ‹0 < b ∧ a.natAbs < 2 ^ 63 ∧ b < 2 ^ 63›
  all_goals first
    | exact ⟨Int64.minValue_lt_ofInt ha, Int64.ofNat_pos hb0 hb⟩
    | simp_all [Int64.toInt_ofInt_of_le (n := a) (by lia) (by lia), Int64.toInt_ofNat_of_lt hb]

/-- For `|a| ≤ H < 2 ^ 63`, a denominator `0 < b < 2 ^ 63` and the thunk of what the third stage
needs of the sieve entries `es` of the shape of `Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, with the
reciprocals of their moduli, for `b` and `H`, a numerator goes on to the exact check when it is
prime to `b` and survives these entries. -/
theorem run_accepted {es : List SieveEntry} (hes : ∀ e ∈ es, e.IsPrimeEntry) {a : Int}
    {b H : Nat} {checks : Thunk (List CheckSpec)}
    (hc : checks.get = fillChecks b H es (es.map fun e ↦ magic e.p)) (hb : 0 < b)
    (hb63 : b < 2 ^ 63) (ha : a.natAbs ≤ H) (hH : H < 2 ^ 63) :
    Id.run (accepted a b checks) = (decide (Int.gcd a b = 1) && survives es b a) := by
  rw [Std.WP.Id.of_run_eq_wp rfl _ ((accepted_spec a b checks).le_wp ⟨hb, by lia, hb63⟩), hc]
  by_cases hab : Int.gcd a b = 1
  · rw [all_admits_fillChecks hes hab ha]
  · simp [hab]

theorem checkPoint_eq_checkNum (w : Thunk (List Int)) (d : Nat) {b : Int} (rev : Bool) {a : Int}
    (hab : Int.gcd a b = 1) :
    checkPoint w d b rev a = checkNum w.get (if d % 2 = 1 then b else 1) b rev a := by
  simp [checkPoint, checkNum, hab]

/-- The points that the extraction gives for the numerator `a` over the denominator `b`: those of
the exact check (`Ratpoints.Sieve.checkPoint`, with the thunk `w` of the products, the degree `d`
and the flag `rev` of the reversal) when `a` passes the test of a candidate
(`Ratpoints.Sieve.accepted`, with the thunk `checks` of the third stage), and none otherwise. -/
def acceptedPoints (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (checks : Thunk (List CheckSpec)) (a : Int) : List (Int × Int × Int) :=
  if Id.run (accepted a b checks) then checkPoint w d b rev a else []

/-- The points of `Ratpoints.Sieve.acceptedPoints`, the test of `Ratpoints.Sieve.accepted` followed
by the exact check of `Ratpoints.Sieve.checkPoint`, are those that the check of the reference
`Ratpoints.Sieve.checkNum` gives for a numerator `a` with `|a| ≤ H < 2 ^ 63` that survives the sieve
entries `es` of the third stage, of the shape of `Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, and none
for the others, for a denominator `0 < b < 2 ^ 63`. -/
theorem acceptedPoints_eq_ite {es : List SieveEntry} (hes : ∀ e ∈ es, e.IsPrimeEntry) {a : Int}
    {b H : Nat} {checks : Thunk (List CheckSpec)}
    (hc : checks.get = fillChecks b H es (es.map fun e ↦ magic e.p)) (w : Thunk (List Int))
    (d : Nat) (rev : Bool) (hb : 0 < b) (hb63 : b < 2 ^ 63) (ha : a.natAbs ≤ H) (hH : H < 2 ^ 63) :
    acceptedPoints w d b rev checks a =
      if survives es b a then checkNum w.get (if d % 2 = 1 then b else 1) b rev a else [] := by
  rw [acceptedPoints, run_accepted hes hc hb hb63 ha hH]
  by_cases hab : Int.gcd a b = 1
  · simp [hab, checkPoint_eq_checkNum w d rev hab]
  · simp [hab, checkNum]

/-! ### The second stage -/

/-- The invariant of the loop of `Ratpoints.Sieve.secondStage` on the bit array `nums` with the word
number `i`, after the moduli `pref`: word `κ` of the bit array is word `κ` of `nums` and-ed with the
row words of the moduli of `pref`. -/
def SecondStageInvariant (nums : Vector UInt64 rbaPack) (i : Int) (pref : List SieveSpec)
    (v : Vector UInt64 rbaPack) : Prop :=
  ∀ κ < rbaPack, v[κ]! = andWords pref nums[κ]! i κ

theorem secondStageInvariant_nil (nums : Vector UInt64 rbaPack) (i : Int) :
    SecondStageInvariant nums i [] nums :=
  fun _ _ ↦ rfl

theorem SecondStageInvariant.getElem!_eq {nums v : Vector UInt64 rbaPack} {i : Int}
    {specs : List SieveSpec} (h : SecondStageInvariant nums i specs v) {κ : Nat}
    (hκ : κ < rbaPack) : v[κ]! = andWords specs nums[κ]! i κ :=
  h κ hκ

/-- At the stop the bit array is zero, and so is its and with the rows of the other moduli. -/
theorem SecondStageInvariant.of_isZeroAt {nums v : Vector UInt64 rbaPack} {i : Int}
    {specs pref suff : List SieveSpec} {cur : SieveSpec} (hs : specs = pref ++ cur :: suff)
    (h : SecondStageInvariant nums i pref v) (hz : isZeroAt v 0 = true) :
    SecondStageInvariant nums i specs v := by
  intro κ hκ
  have h0 := (isZeroAt_eq_true_iff v 0).mp hz κ hκ
  rw [Nat.mul_zero, Nat.zero_add] at h0
  rw [h0, hs, andWords_append, ← h κ hκ, h0, andWords_zero]

theorem SecondStageInvariant.andBitArray {nums v : Vector UInt64 rbaPack} {i : Int}
    {pref : List SieveSpec} {s : SieveSpec} (h : SecondStageInvariant nums i pref v) :
    SecondStageInvariant nums i (pref ++ [s])
      (Sieve.andBitArray v 0 s.row (i % (s.p : Int)).toNat) := by
  intro κ hκ
  simp only [getElem!_andBitArray _ _ _ _ hκ, Nat.div_eq_of_lt hκ, ↓reduceIte, Nat.mod_eq_of_lt hκ,
    h κ hκ, andWords_concat, SieveSpec.wordAt_of_lt _ _ hκ]

attribute [local irreducible] SecondStageInvariant in
/-- The stop when the bit array is zero loses nothing, since a zero bit array stays zero. -/
@[spec]
theorem secondStage_spec (specs : List SieveSpec) (i : Int) (nums : Vector UInt64 rbaPack) :
    ⦃ True ⦄ secondStage specs i nums
    ⦃ fun r ↦ ∀ κ < rbaPack, r[κ]! = andWords specs nums[κ]! i κ ⦄ := by
  vcgen [secondStage] invariants
  · fun pref _ v ↦ SecondStageInvariant nums i pref v
  all_goals first
    | exact secondStageInvariant_nil nums i
    | exact SecondStageInvariant.getElem!_eq ‹_› ‹_›
    | exact SecondStageInvariant.of_isZeroAt ‹_› ‹_› ‹_›
    | exact SecondStageInvariant.andBitArray ‹_›

theorem andWords_concat_of_eq {x y : UInt64} {pref : List SieveSpec} {i : Int} {κ : Nat}
    {s : SieveSpec} (hy : y = andWords pref x i κ) (hκ : κ < rbaPack) :
    y &&& s.row[rbaPack * (i % (s.p : Int)).toNat + κ]! = andWords (pref ++ [s]) x i κ := by
  rw [andWords_concat, SieveSpec.wordAt_of_lt _ _ hκ, hy]

/-- The stop when the word is zero loses nothing, since a zero word stays zero. -/
@[spec]
theorem secondStageWord_spec (specs : List SieveSpec) (i : Int) {κ : Nat} (hκ : κ < rbaPack)
    (x : UInt64) :
    ⦃ True ⦄ secondStageWord specs i κ x ⦃ fun r ↦ r = andWords specs x i κ ⦄ := by
  vcgen [secondStageWord] invariants
  · fun pref _ r ↦ r = andWords pref x i κ
  all_goals first
    | rfl
    | exact andWords_concat_of_eq ‹_› hκ
    | simp_all [andWords_append]

end Sieve

end Ratpoints

end
