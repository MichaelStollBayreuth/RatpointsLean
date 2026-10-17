/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Words

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Delivery
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
range. The exact check (`Ratpoints.Sieve.checkPoint`) and the points at infinity
(`Ratpoints.Sieve.pointsAtInfinity`), on a delivery whose flag of the stop is clear, are the
reference of the delivery (`Ratpoints.Delivery.deliver`) of the lists of the points they deliver for
the flags of the search: the points of the check of the reference, without the point with `y < 0`
under `RATPOINTS_NO_Y`, or the one survivor with `y = 0` under `RATPOINTS_NO_CHECK`, mapped back
after a reversal. So the test of a candidate (`Ratpoints.Sieve.accepted`), for `|a| < 2 ^ 63` and
`0 < b < 2 ^ 63`, followed by the exact check, delivers the points of the check with the flags
(`Ratpoints.Sieve.checkNumWith`), which is the check of the reference (`Ratpoints.Sieve.checkNum`)
with the flags of the output clear, for the numerators that survive these entries. The second stage
on a bit array (`Ratpoints.Sieve.secondStage`), or on one of its words
(`Ratpoints.Sieve.secondStageWord`), with moduli in the range of the packing and their reciprocals
and the test `small` of the piece, gives its words and-ed with the rows of all its moduli at their
offsets (`Ratpoints.Sieve.andWords`), although it stops when the bit array or the word is zero. The
contracts of the loops are `@[spec]` theorems proved with `vcgen`, the program logic of Lean core,
with loop invariants that are named definitions.

## Main definitions

* `Ratpoints.Sieve.RelprimeOddInvariant`: the invariant of the loop of the binary algorithm.
* `Ratpoints.Sieve.CheckSpec.admits`, `Ratpoints.Sieve.Stage3Invariant`: whether the third stage
  lets a numerator through one of its primes, and the invariant of its loop.
* `Ratpoints.Sieve.SieveEntry.IsPrimeEntry`: the shape of the sieve entries of the third stage.
* `Ratpoints.Sieve.checkPointList`, `Ratpoints.Sieve.checkNumWith`: the points that the exact check
  delivers for a numerator with the flags of the search, and the same when the numerator is prime
  to the denominator, the check of the reference with the flags.
* `Ratpoints.Sieve.acceptedPoints`: the points that the extraction delivers for a numerator, those
  of the exact check when the numerator passes the test of a candidate, the test for common factors
  and the third stage.
* `Ratpoints.Sieve.pointsAtInfinityList`: the points at infinity that the search delivers with the
  flags of the search.
* `Ratpoints.Sieve.SecondStageInvariant`, `Ratpoints.Sieve.SecondStageWordInvariant`: the
  invariants of the loops of the second stage on a bit array and on a word, over the moduli with
  their reciprocals.

## Main statements

* `Ratpoints.Sieve.relprimeOdd_spec`, `Ratpoints.Sieve.relprime_spec`: the binary algorithm
  decides whether `gcd(m, n) = 1` for odd positive words `m` and `n`, and for words
  `m > -2 ^ 63` and `n ≥ 1`.
* `Ratpoints.Sieve.stage3_spec`: the third stage is whether all its primes admit the numerator.
* `Ratpoints.Sieve.CheckSpec.index_eq`: the residue at which it reads the table of a prime is
  `(a mod p) binv mod p`, with the bias and without it.
* `Ratpoints.Sieve.SieveEntry.IsPrimeEntry.admits_checkOf`,
  `Ratpoints.Sieve.run_stage3_fillChecks`: for a numerator prime to `b` with `|a| ≤ H`, a prime
  entry admits it in the third stage exactly when its row of `b` does, and the third stage is the
  survivor test of its entries.
* `Ratpoints.Sieve.accepted_spec`: the test of a candidate is the test of `gcd(a, b) = 1` followed
  by the third stage; `Ratpoints.Sieve.acceptedPoints_eq_ite`: for a numerator `a` with
  `|a| ≤ H < 2 ^ 63` and a denominator `0 < b < 2 ^ 63`, the test with the exact check gives the
  points of the check with the flags (`Ratpoints.Sieve.checkNumWith`) when `a` survives the entries
  of the third stage, and none otherwise.
* `Ratpoints.Sieve.checkPoint_eq_deliver`, `Ratpoints.Sieve.pointsAtInfinity_eq_deliver`: the exact
  check and the points at infinity deliver their lists to the callback, the second call left out
  after a call that stops the search.
* `Ratpoints.Sieve.checkNumWith_of_noCheck_eq_false`,
  `Ratpoints.Sieve.checkNumWith_of_noCheck_eq_true`,
  `Ratpoints.Sieve.flatMap_checkNumWith_of_noCheck_eq_false`,
  `Ratpoints.Sieve.pointsAtInfinityList_of_noCheck_eq_false`,
  `Ratpoints.Sieve.pointsAtInfinityList_of_noCheck_eq_true`: the lists with the flags of the output,
  in terms of the brute-force reference without `RATPOINTS_NO_CHECK`, and the survivors with it.
* `Ratpoints.Sieve.checkNumWith_eq_map`, `Ratpoints.Sieve.pointsAtInfinityList_eq_map`: the lists
  with the flag of the reversal are those without it, mapped;
  `Ratpoints.Sieve.map_checkNumWith_sublist`, `Ratpoints.Sieve.map_pointsAtInfinityList`: without
  `RATPOINTS_NO_CHECK` and with `RATPOINTS_NO_Y`, with `y` replaced by `0`, they are sublists of
  those under `RATPOINTS_NO_CHECK`.
* `Ratpoints.Sieve.secondStage_spec`, `Ratpoints.Sieve.secondStageWord_spec`: the second stage on a
  bit array, or on one of its words, gives its words and-ed with the rows of all its moduli.

## Implementation notes

The file uses Lean core and `Std` only, as `Ratpoints.Proof.Words` and `Ratpoints.Proof.Delivery`
do, on whose words of the rows (`Ratpoints.Sieve.SieveSpec.wordAt`, `Ratpoints.Sieve.andWords`) and
reading of the reciprocals in step with the moduli (`Ratpoints.Sieve.eq_magic_and_of_next?_eq_some`,
`Ratpoints.Sieve.next?_ne_none_of_lt`) the second stage builds. The proofs use only the facts on the
constants that `decide` checks next to them, that `Ratpoints.mulModLimit < 2 ^ 32` and
`Ratpoints.stage3Limit ≤ 2 ^ 32`, never their values. The words of the test for common factors are
read as natural numbers by `Int64.toNatClampNeg`, which is faithful on the non-negative words that
the binary algorithm keeps; the facts on words that are not about the model are in
`Ratpoints.Proof.Bits`.
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

theorem bias_checkOf (b H : Nat) {e : SieveEntry} {t : Entry} (he : e.factors = [.prime t])
    (mg : Nat) : (checkOf b H e mg).bias = if 2 * e.p * H < stage3Limit then e.p * H else 0 := by
  simp only [checkOf, he]

theorem isFSquare_checkOf (b H : Nat) {e : SieveEntry} {t : Entry} (he : e.factors = [.prime t])
    (mg : Nat) : (checkOf b H e mg).isFSquare = t.isFSquare := by
  simp only [checkOf, he]

/-- The inverse of the denominator `b` that `Ratpoints.Sieve.checkOf` takes from the table `t` of
the single factor of the sieve entry `e` of a modulus `0 < p ≤ 2 ^ 32`, with the reciprocal of `p`:
`0` when `p` divides `b`, and otherwise the entry of `t` at `b mod p`, which the reduction by the
reciprocal gives for `b ≤ Ratpoints.mulModLimit`. -/
theorem binv_checkOf {b : Nat} (H : Nat) {e : SieveEntry} {t : Entry} (he : e.factors = [.prime t])
    (hp : 0 < e.p) (hp32 : e.p ≤ 2 ^ 32) :
    (checkOf b H e (magic e.p)).binv = if b % e.p = 0 then 0 else t.inverses[b % e.p]! := by
  have : (if b ≤ mulModLimit then mulMod b e.p (magic e.p) else b % e.p) = b % e.p := by
    split
    · exact mulMod_magic hp (mul_lt_two_pow_64_of_le_mulModLimit ‹_› hp32)
    · rfl
  simp only [checkOf, he, this]

/-- The value `a binv + p H` that the third stage reduces with the bias `p H`, for `|a| ≤ H` and
`binv < p`, is at least `H` (`sift.c:303`): a natural number. -/
theorem le_mul_add_natCast_mul {a : Int} {p binv H : Nat} (ha : a.natAbs ≤ H) (hb : binv < p) :
    (H : Int) ≤ a * binv + (p * H : Nat) := by
  lia [Int.natAbs_mul_add_le_mul ha hb]

/-- The value `a binv + p H` that the third stage reduces with the bias `p H`, for `|a| ≤ H` and
`binv < p`, is at most `2 p H - H` (`sift.c:303`), below the bound `2 p H < Ratpoints.stage3Limit`
of the bias, and so a `long`. -/
theorem mul_add_natCast_mul_le_two_mul_mul_sub {a : Int} {p binv H : Nat} (ha : a.natAbs ≤ H)
    (hb : binv < p) : a * binv + (p * H : Nat) ≤ 2 * p * H - H := by
  push_cast
  lia [Int.natAbs_mul_add_le_mul ha hb]

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
    · have hp32 : p < 2 ^ 32 := by lia [Nat.le_mul_of_pos_right p hH0]
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

/-- The bias of what the third stage needs of the entry `e` of a prime, when it is not `0`, is
`p H` with `2 p H < 2 ^ 32`, and its reciprocal, that of the entry, is that of `p` when the entry's
is. -/
theorem bias_checkOf_eq_and_of_ne_zero {b H : Nat} {e : SieveEntry} {t : Entry}
    (hf : e.factors = [.prime t]) (hm : e.magic = Sieve.magic e.p) {mg : Nat}
    (h0 : (checkOf b H e mg).bias ≠ 0) :
    (checkOf b H e mg).bias = (checkOf b H e mg).p * H ∧
      2 * (checkOf b H e mg).p * H < 2 ^ 32 ∧
        (checkOf b H e mg).magic = Sieve.magic (checkOf b H e mg).p := by
  rw [p_checkOf, magic_checkOf, hm]
  rw [bias_checkOf b H hf] at h0 ⊢
  by_cases hc : 2 * e.p * H < stage3Limit
  · exact ⟨by simp [hc], Nat.lt_of_lt_of_le hc stage3Limit_le_two_pow_32, rfl⟩
  · simp [hc] at h0

theorem SieveEntry.admits_prime {e : SieveEntry} {t : Entry} (he : e.factors = [.prime t])
    (hp : e.p = t.p) (b : Nat) (a : Int) : e.admits b a = t.admits b a := by
  simp [SieveEntry.admits, he, hp, Factor.admits, Entry.admits]

/-- The sieve entry `e` is that of a modulus `1 < p ≤ 2 ^ 32` whose single factor is a table `t` of
`p` with inverses of the residues `0 < r < p` that are residues `0 < t.inverses[r]! < p`, and whose
reciprocal is that of `p` (`Ratpoints.Sieve.magic`): the shape that the third stage needs of its
entries (`Ratpoints.Sieve.checkOf`), whose rows it then tests
(`Ratpoints.Sieve.run_stage3_fillChecks`); the fields of the packing (the bias, the inverses of
`Ratpoints.rbaLength` and of the strides) do not matter. The entry of a prime with the table of the
reference has it (`Ratpoints.Sieve.isPrimeEntry_examinePrime`). -/
def SieveEntry.IsPrimeEntry (e : SieveEntry) : Prop :=
  ∃ t : Entry, e.factors = [.prime t] ∧ e.p = t.p ∧ e.magic = Sieve.magic t.p ∧ 1 < t.p ∧
    t.p ≤ 2 ^ 32 ∧ ∀ r < t.p, r ≠ 0 → t.inverses[r]! ≠ 0 ∧ t.inverses[r]! < t.p

/-- The third stage with the entry of a prime `1 < p ≤ 2 ^ 32` whose single factor is its table, of
the shape of `Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, lets a numerator `a` prime to `b` with
`|a| ≤ H` through exactly when the row of `b` in the entry admits it: when `p` divides `b`, since
then `p ∤ a`, and otherwise since the stage reads the table at `(a mod p) b⁻¹ mod p`
(`Ratpoints.Sieve.CheckSpec.index_eq`). -/
theorem SieveEntry.IsPrimeEntry.admits_checkOf {e : SieveEntry} (he : e.IsPrimeEntry) {b H : Nat}
    {a : Int} (hab : Int.gcd a b = 1) (ha : a.natAbs ≤ H) :
    (checkOf b H e (Sieve.magic e.p)).admits a = e.admits b a := by
  obtain ⟨t, hf, hpt, hm, h1, h32, hinv⟩ := he
  have hb := binv_checkOf (b := b) H hf (by lia) (by lia)
  rw [SieveEntry.admits_prime hf hpt]
  by_cases hr : b % e.p = 0
  · simp only [hr, ↓reduceIte] at hb
    simp [CheckSpec.admits_of_binv_eq_zero a hb, Entry.admits, ← hpt, hr,
      Int.toNat_emod_ne_zero_of_gcd_eq_one (hpt ▸ h1) hab hr]
  obtain ⟨hi0, hilt⟩ := hinv (b % e.p) (hpt ▸ Nat.mod_lt _ (by lia)) hr
  simp only [hr, ↓reduceIte] at hb
  have hi : (checkOf b H e (Sieve.magic e.p)).index a =
      (a % e.p).toNat * t.inverses[b % e.p]! % e.p := by
    rw [CheckSpec.index_eq (H := H) (by rw [hb, p_checkOf]; lia) ha
      (bias_checkOf_eq_and_of_ne_zero hf (hpt ▸ hm)), hb, p_checkOf]
  simp [CheckSpec.admits, Entry.admits, ← hpt, hr, hb, hi, hi0, isFSquare_checkOf b H hf]

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

/-- The map of the reversal keeps the `y`-coordinate. -/
@[simp]
theorem fst_snd_swapPoint (p : Int × Int × Int) : (swapPoint p).2.1 = p.2.1 := by
  simp only [swapPoint]
  split <;> rfl

/-- The map of the reversal and the test of `RATPOINTS_NO_Y` commute, since the map keeps the
`y`-coordinate. -/
theorem filter_map_swapPoint (rev noY : Bool) (L : List (Int × Int × Int)) :
    (L.map (if rev then swapPoint else id)).filter (fun p ↦ !noY || 0 ≤ p.2.1) =
      (L.filter fun p ↦ !noY || 0 ≤ p.2.1).map (if rev then swapPoint else id) := by
  cases rev <;> simp [List.filter_map, Function.comp_def]

/-- The map of the reversal commutes with the replacement of `y` by `0`, since it moves only `x`
and `z`. -/
theorem swapPoint_fst_zero_snd (q : Int × Int × Int) :
    swapPoint (q.1, 0, q.2.2) = ((swapPoint q).1, 0, (swapPoint q).2.2) := by
  simp only [swapPoint]
  split <;> rfl

/-- One call of the callback with the point `(a : y : b)`, mapped back after a reversal, on a
delivery whose flag is clear, is the delivery of that point mapped by `Ratpoints.Sieve.swapPoint`
when `rev` is set. -/
theorem _root_.Ratpoints.Delivery.callMapped_eq_deliver {σ : Type}
    (process : Int → Int → Int → σ → Answer σ) {r : Delivery σ} (hr : r.quit = false) (rev : Bool)
    (a b y : Int) :
    r.callMapped process rev a b y =
      r.deliver process [(if rev then swapPoint else id) (a, y, b)] := by
  rw [Delivery.deliver_singleton_of_quit_eq_false process hr]
  cases rev <;> by_cases ha : 0 ≤ a <;> simp [Delivery.callMapped, swapPoint, ha]

/-- The points that the exact check (`Ratpoints.Sieve.checkPoint`) of the numerator `a` over the
denominator `b` delivers to a callback that does not stop the search, for the products `w`, the
factor `f` and the flags `fl`: unless `fl.noCheck`, the points `(a, y, b)` and, for `y ≠ 0`,
`(a, -y, b)` when the value `v` of Horner's rule in `a` on `w`, times `f`, is `y ^ 2` with `y ≥ 0`
(`Ratpoints.BruteForce.pointsAbove`), the point with `y < 0` left out when `fl.noY` is set; with
`fl.noCheck`, the one survivor `(a, 0, b)`; each mapped by `Ratpoints.Sieve.swapPoint` when the flag
`fl.reversed` of the reversal is set. -/
def checkPointList (w : List Int) (f b : Int) (fl : CheckFlags) (a : Int) :
    List (Int × Int × Int) :=
  (if fl.noCheck then [(a, 0, b)]
    else (BruteForce.pointsAbove a b (BruteForce.horner w a * f)).filter
      fun p ↦ !fl.noY || 0 ≤ p.2.1).map (if fl.reversed then swapPoint else id)

/-- The exact check on a delivery whose flag is clear delivers the points of
`Ratpoints.Sieve.checkPointList`, the call with `-y` left out after a call that stops the search. -/
theorem checkPoint_eq_deliver {σ : Type} (process : Int → Int → Int → σ → Answer σ)
    (w : Thunk (List Int)) (d : Nat) (b : Int) (fl : CheckFlags) (a : Int) {r : Delivery σ}
    (hr : r.quit = false) :
    checkPoint process w d b fl a r =
      r.deliver process (checkPointList w.get (if d % 2 = 1 then b else 1) b fl a) := by
  rw [checkPoint, checkPointList]
  cases hc : fl.noCheck
  · simp only [Bool.not_false, ↓reduceIte, BruteForce.pointsAbove]
    generalize (BruteForce.horner w.get a * if d % 2 = 1 then b else 1) = v
    generalize v.toNat.sqrt = y
    by_cases hv : 0 ≤ v ∧ y * y = v.toNat
    · simp only [hv, and_self, ↓reduceIte, Delivery.callMapped_eq_deliver process hr]
      by_cases hy0 : y = 0
      · cases fl.noY <;> simp [hy0]
      · have hy : (0 : Int) < y := by lia
        cases hn : fl.noY
        · simp only [hy0, ↓reduceIte, Bool.false_eq_true, List.filter_cons, Bool.not_false,
            Bool.true_or, List.filter_nil, List.map_cons, List.map_nil, Bool.and_true]
          conv => rhs; rw [← List.singleton_append, Delivery.deliver_append]
          generalize r.deliver process [(if fl.reversed then swapPoint else id) (a, y, b)] = r1
          cases hq : r1.quit <;> simp [hq, hy0, Delivery.callMapped_eq_deliver process]
        · simp [Int.le_of_lt hy, hy0]
    · simp [hv]
  · simp [Delivery.callMapped_eq_deliver process hr]

/-- The check of the numerator `a` over the denominator `b` with the flags `fl`: the points of
`Ratpoints.Sieve.checkPointList` when `a` is prime to `b`, and none otherwise. With the flags
`RATPOINTS_NO_CHECK` and `RATPOINTS_NO_Y` clear, it is the check of the reference
(`Ratpoints.Sieve.checkNumWith_of_noCheck_eq_false`). -/
def checkNumWith (w : List Int) (f b : Int) (fl : CheckFlags) (a : Int) : List (Int × Int × Int) :=
  if Int.gcd a b = 1 then checkPointList w f b fl a else []

/-- Without `RATPOINTS_NO_CHECK`, the check with the flags is the check of the reference with the
flag of the reversal, without the points with `y < 0` under `RATPOINTS_NO_Y`. -/
theorem checkNumWith_of_noCheck_eq_false {fl : CheckFlags} (hc : fl.noCheck = false)
    (w : List Int) (f b a : Int) :
    checkNumWith w f b fl a =
      (checkNum w f b fl.reversed a).filter fun p ↦ !fl.noY || 0 ≤ p.2.1 := by
  by_cases hab : Int.gcd a b = 1
  · cases hr : fl.reversed <;>
      simp [checkNumWith, checkPointList, checkNum, hab, hc, hr, List.filter_map,
        Function.comp_def, fst_snd_swapPoint]
  · simp [checkNumWith, checkNum, hab]

/-- Under `RATPOINTS_NO_CHECK`, the check with the flags gives the survivor `(a, 0, b)` of a
numerator prime to `b`, mapped after a reversal. -/
theorem checkNumWith_of_noCheck_eq_true {fl : CheckFlags} (hc : fl.noCheck = true)
    (w : List Int) (f b a : Int) :
    checkNumWith w f b fl a =
      if Int.gcd a b = 1 then [(if fl.reversed then swapPoint else id) (a, 0, b)] else [] := by
  simp [checkNumWith, checkPointList, hc]

/-- The check with the flags gives the points of the check without the flag of the reversal, mapped
by `Ratpoints.Sieve.swapPoint` when it is set. -/
theorem checkNumWith_eq_map (w : List Int) (f b : Int) (fl : CheckFlags) (a : Int) :
    checkNumWith w f b fl a = (checkNumWith w f b { fl with reversed := false } a).map
      (if fl.reversed then swapPoint else id) := by
  by_cases h : Int.gcd a b = 1 <;> simp [checkNumWith, checkPointList, h]

theorem mem_checkNumWith_of_noCheck {fl : CheckFlags} (hc : fl.noCheck = true) {w : List Int}
    {f b a : Int} {q : Int × Int × Int} :
    q ∈ checkNumWith w f b fl a ↔
      Int.gcd a b = 1 ∧ q = (if fl.reversed then swapPoint else id) (a, 0, b) := by
  rw [checkNumWith_of_noCheck_eq_true hc]
  by_cases h : Int.gcd a b = 1 <;> simp [h]

-- The points of a value with `y ≥ 0`, with `y` replaced by `0`: at most the triple `(x, 0, z)`.
private theorem map_filter_pointsAbove_sublist (x z v : Int) :
    (((BruteForce.pointsAbove x z v).filter fun p ↦ 0 ≤ p.2.1).map
      fun q ↦ (q.1, 0, q.2.2)).Sublist [(x, (0 : Int), z)] := by
  simp only [BruteForce.pointsAbove]
  have h1 : (0 : Int) ≤ v.toNat.sqrt := Int.natCast_nonneg _
  by_cases h : 0 ≤ v ∧ v.toNat.sqrt * v.toNat.sqrt = v.toNat
  · simp only [h, and_self, ↓reduceIte]
    by_cases h0 : v.toNat.sqrt = 0
    · simp [h0]
    · simp [h0, h1]
  · simp [h]

/-- Without `RATPOINTS_NO_CHECK` and with `RATPOINTS_NO_Y`, the check of a numerator `a` over `b`
gives at most one point, the one with `y ≥ 0`; with `y` replaced by `0` it is the survivor that the
check gives under `RATPOINTS_NO_CHECK`. -/
theorem map_checkNumWith_sublist (w : List Int) (f b : Int) (rev noY : Bool) (a : Int) :
    ((checkNumWith w f b ⟨rev, false, true⟩ a).map fun q ↦ (q.1, 0, q.2.2)).Sublist
      (checkNumWith w f b ⟨rev, true, noY⟩ a) := by
  rw [checkNumWith, checkNumWith]
  by_cases hab : Int.gcd a b = 1 <;> simp only [hab, ↓reduceIte]
  · have h := map_filter_pointsAbove_sublist a b (BruteForce.horner w a * f)
    cases rev
    · simpa [checkPointList] using h
    · simpa [checkPointList, List.map_map, Function.comp_def, ← swapPoint_fst_zero_snd] using
        h.map swapPoint
  · exact .slnil

/-- The points that the extraction delivers for the numerator `a` over the denominator `b`: those of
the exact check (`Ratpoints.Sieve.checkPointList`, with the thunk `w` of the products, the degree
`d` and the flags `fl`) when `a` passes the test of a candidate (`Ratpoints.Sieve.accepted`, with
the thunk `checks` of the third stage), and none otherwise. -/
def acceptedPoints (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags)
    (checks : Thunk (List CheckSpec)) (a : Int) : List (Int × Int × Int) :=
  if Id.run (accepted a b checks) then checkPointList w.get (if d % 2 = 1 then b else 1) b fl a
  else []

/-- The points of `Ratpoints.Sieve.acceptedPoints`, the test of `Ratpoints.Sieve.accepted` followed
by the exact check, are those of the check with the flags `Ratpoints.Sieve.checkNumWith` for a
numerator `a` with `|a| ≤ H < 2 ^ 63` that survives the sieve entries `es` of the third stage, of
the shape of `Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, and none for the others, for a denominator
`0 < b < 2 ^ 63`. -/
theorem acceptedPoints_eq_ite {es : List SieveEntry} (hes : ∀ e ∈ es, e.IsPrimeEntry) {a : Int}
    {b H : Nat} {checks : Thunk (List CheckSpec)}
    (hc : checks.get = fillChecks b H es (es.map fun e ↦ magic e.p)) (w : Thunk (List Int))
    (d : Nat) (fl : CheckFlags) (hb : 0 < b) (hb63 : b < 2 ^ 63) (ha : a.natAbs ≤ H)
    (hH : H < 2 ^ 63) :
    acceptedPoints w d b fl checks a =
      if survives es b a then checkNumWith w.get (if d % 2 = 1 then b else 1) b fl a else [] := by
  rw [acceptedPoints, run_accepted hes hc hb hb63 ha hH]
  by_cases hab : Int.gcd a b = 1 <;> simp [hab, checkNumWith]

/-- The exact check of a numerator that passes the test of a candidate, on a delivery whose flag is
clear, delivers the points of `Ratpoints.Sieve.acceptedPoints`. -/
theorem checkPoint_eq_deliver_acceptedPoints {σ : Type} (process : Int → Int → Int → σ → Answer σ)
    (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags) {checks : Thunk (List CheckSpec)}
    {a : Int} (h : Id.run (accepted a b checks) = true) {r : Delivery σ} (hr : r.quit = false) :
    checkPoint process w d b fl a r = r.deliver process (acceptedPoints w d b fl checks a) := by
  simp only [acceptedPoints, h, ↓reduceIte, checkPoint_eq_deliver process w d b fl a hr]

/-- A numerator that does not pass the test of a candidate has no points to deliver. -/
theorem deliver_acceptedPoints_of_not_accepted {σ : Type}
    (process : Int → Int → Int → σ → Answer σ) (w : Thunk (List Int)) (d b : Nat)
    (fl : CheckFlags) {checks : Thunk (List CheckSpec)} {a : Int}
    (h : ¬Id.run (accepted a b checks) = true) (r : Delivery σ) :
    r.deliver process (acceptedPoints w d b fl checks a) = r := by
  simp [acceptedPoints, h]

/-- Without `RATPOINTS_NO_CHECK`, the checks with the flags of the numerators `xs` over `b` give the
points of the brute-force reference, mapped by `Ratpoints.Sieve.swapPoint` after a reversal,
without those with `y < 0` under `RATPOINTS_NO_Y`. -/
theorem flatMap_checkNumWith_of_noCheck_eq_false {fl : CheckFlags} (hc : fl.noCheck = false)
    (c : List Int) (d : Nat) (b : Int) (xs : List Int) :
    xs.flatMap (checkNumWith (BruteForce.scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b fl) =
      ((BruteForce.pointsOfDen c d b xs).map (if fl.reversed then swapPoint else id)).filter
        fun p ↦ !fl.noY || 0 ≤ p.2.1 := by
  rw [funext (checkNumWith_of_noCheck_eq_false hc _ _ b), ← List.filter_flatMap, flatMap_checkNum,
    pointsOfDen_eq_flatMap_checkNum]

/-! ### The points at infinity -/

/-- The points that `Ratpoints.Sieve.pointsAtInfinity` delivers to a callback that does not stop the
search, for the polynomial of degree `d` with the coefficient list `c` and the flags `fl`: when
there are points at infinity, for odd `d` or `c_d` a square (`Ratpoints.Setup.isSquare`), with
`fl.noCheck` or odd `d` the point `(1, 0, 0)`, and otherwise `(1, s, 0)` for `s = √c_d` followed,
unless `fl.noY`, by `(1, -s, 0)`; each mapped by `Ratpoints.Sieve.swapPoint` to `(0, y, 1)` when the
flag `fl.reversed` of the reversal is set. -/
def pointsAtInfinityList (c : List Int) (d : Nat) (fl : CheckFlags) : List (Int × Int × Int) :=
  if d % 2 == 1 || Setup.isSquare (c.getD d 0) then
    (if fl.noCheck || d % 2 == 1 then [(1, 0, 0)]
      else (1, ((c.getD d 0).toNat.sqrt : Int), 0) ::
        if fl.noY then [] else [(1, -((c.getD d 0).toNat.sqrt : Int), 0)]).map
      (if fl.reversed then swapPoint else id)
  else []

/-- The points at infinity on a delivery whose flag is clear deliver the points of
`Ratpoints.Sieve.pointsAtInfinityList`, the call with `-√c_d` left out after a call that stops the
search. -/
theorem pointsAtInfinity_eq_deliver {σ : Type} (process : Int → Int → Int → σ → Answer σ)
    (c : List Int) (d : Nat) (fl : CheckFlags) {r : Delivery σ} (hr : r.quit = false) :
    pointsAtInfinity process c d fl r = r.deliver process (pointsAtInfinityList c d fl) := by
  have key (r' : Delivery σ) (y : Int) : r'.call process (if fl.reversed then 0 else 1)
      (if fl.reversed then 1 else 0) y = r'.callMapped process fl.reversed 1 0 y := by
    cases fl.reversed <;> simp [Delivery.callMapped]
  simp only [pointsAtInfinity, pointsAtInfinityList, key]
  split
  · cases hc : fl.noCheck <;> by_cases hd : d % 2 = 1 <;>
      simp only [hd, Delivery.callMapped_eq_deliver process hr, Bool.false_or, Bool.true_or,
        beq_iff_eq, ↓reduceIte, Bool.false_eq_true, List.map_cons, List.map_nil]
    conv => rhs; rw [← List.singleton_append, Delivery.deliver_append]
    generalize r.deliver process _ = r1
    cases hq : r1.quit <;> cases fl.noY <;> simp [hq, Delivery.callMapped_eq_deliver process]
  · rfl

/-- Without `RATPOINTS_NO_CHECK`, for odd `d` or `c_d ≠ 0`, the points at infinity delivered are
those of the candidate `(1, 0)` with the value `F(1, 0)`, which is `c_d` for even `d` and `0` for
odd `d`, without the point with `y < 0` under `RATPOINTS_NO_Y`, and mapped after a reversal. (For
even `d` and `c_d = 0`, which the search refuses before, the point `(1 : 0 : 0)` is delivered
twice.) -/
theorem pointsAtInfinityList_of_noCheck_eq_false {fl : CheckFlags} (hc : fl.noCheck = false)
    {c : List Int} {d : Nat} (h : d % 2 = 1 ∨ c.getD d 0 ≠ 0) :
    pointsAtInfinityList c d fl =
      ((BruteForce.pointsAbove 1 0 (c.getD d 0 * if d % 2 = 1 then 0 else 1)).map
        (if fl.reversed then swapPoint else id)).filter fun p ↦ !fl.noY || 0 ≤ p.2.1 := by
  rw [pointsAtInfinityList, filter_map_swapPoint]
  generalize c.getD d 0 = v at h ⊢
  by_cases hd : d % 2 = 1
  · simp [BruteForce.pointsAbove, hd, show Nat.sqrt 0 = 0 by decide]
  · have h0 := h.resolve_left hd
    by_cases hs : 0 ≤ v ∧ v.toNat.sqrt * v.toNat.sqrt = v.toNat
    · have hy : v.toNat.sqrt ≠ 0 := fun h ↦ h0 (by rw [h] at hs; lia)
      cases fl.noY <;> simp [BruteForce.pointsAbove, Setup.isSquare, hd, hc, hs, hy]
    · have hs' : Setup.isSquare v = false := by simpa [Setup.isSquare] using hs
      simp [hd, hs', BruteForce.pointsAbove, hs]

/-- Under `RATPOINTS_NO_CHECK`, the points at infinity delivered are the one survivor `(1, 0, 0)`,
mapped after a reversal, when there are points at infinity. -/
theorem pointsAtInfinityList_of_noCheck_eq_true {fl : CheckFlags} (hc : fl.noCheck = true)
    (c : List Int) (d : Nat) :
    pointsAtInfinityList c d fl = if d % 2 = 1 ∨ Setup.isSquare (c.getD d 0) = true then
      [(if fl.reversed then swapPoint else id) (1, 0, 0)] else [] := by
  simp [pointsAtInfinityList, hc]

/-- The points at infinity are those without the flag of the reversal, mapped by
`Ratpoints.Sieve.swapPoint` when it is set. -/
theorem pointsAtInfinityList_eq_map (c : List Int) (d : Nat) (fl : CheckFlags) :
    pointsAtInfinityList c d fl = (pointsAtInfinityList c d { fl with reversed := false }).map
      (if fl.reversed then swapPoint else id) := by
  obtain ⟨rev, noCheck, noY⟩ := fl
  cases rev <;> simp [pointsAtInfinityList, apply_ite (List.map _)]

theorem eq_of_mem_pointsAtInfinityList_of_noCheck {fl : CheckFlags} (hc : fl.noCheck = true)
    {c : List Int} {d : Nat} {q : Int × Int × Int} (hq : q ∈ pointsAtInfinityList c d fl) :
    q = (if fl.reversed then swapPoint else id) (1, 0, 0) := by
  rw [pointsAtInfinityList_of_noCheck_eq_true hc] at hq
  split at hq <;> simp_all

/-- Without `RATPOINTS_NO_CHECK` and with `RATPOINTS_NO_Y`, the points at infinity, with `y`
replaced by `0`, are those under `RATPOINTS_NO_CHECK`. -/
theorem map_pointsAtInfinityList (c : List Int) (d : Nat) (rev noY : Bool) :
    (pointsAtInfinityList c d ⟨rev, false, true⟩).map (fun q ↦ (q.1, 0, q.2.2)) =
      pointsAtInfinityList c d ⟨rev, true, noY⟩ := by
  cases rev <;> by_cases hd : d % 2 = 1 <;>
    simp [pointsAtInfinityList, hd, apply_ite (List.map _), swapPoint]

/-! ### The second stage -/

/-- The invariant of the loop of `Ratpoints.Sieve.secondStage` over the moduli `specs` and their
reciprocals `mgs` on the bit array `nums` with the word number `i`, after the moduli `pref`, whose
state is the bit array and the reciprocals still to come: before the loop has gone through all the
moduli, these are the reciprocals after the first `pref.length`; and word `κ` of the bit array is
word `κ` of `nums` and-ed with the row words of the moduli of `pref`. -/
def SecondStageInvariant (nums : Vector UInt64 rbaPack) (i : Int) (specs : List SieveSpec)
    (mgs : List Nat) (pref : List SieveSpec) (st : Vector UInt64 rbaPack × List Nat) : Prop :=
  (pref.length < specs.length → st.2 = mgs.drop pref.length) ∧
    ∀ κ < rbaPack, st.1[κ]! = andWords pref nums[κ]! i κ

theorem SecondStageInvariant.next?_ne_none {nums v : Vector UInt64 rbaPack} {i : Int} {small : Bool}
    {specs pref suff : List SieveSpec} {s : SieveSpec} {mgs rest : List Nat}
    (pre : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small i (i + 1))
    (hs : specs = pref ++ s :: suff) (h : SecondStageInvariant nums i specs mgs pref (v, rest)) :
    Std.Stream.next? rest ≠ none :=
  next?_ne_none_of_lt pre.2.1 hs h.1

theorem secondStageInvariant_nil (nums : Vector UInt64 rbaPack) (i : Int) (specs : List SieveSpec)
    (mgs : List Nat) : SecondStageInvariant nums i specs mgs [] (nums, Std.toStream mgs) :=
  ⟨fun _ ↦ rfl, fun _ _ ↦ rfl⟩

theorem SecondStageInvariant.getElem!_eq {nums : Vector UInt64 rbaPack} {i : Int}
    {specs : List SieveSpec} {mgs : List Nat} {st : Vector UInt64 rbaPack × List Nat}
    (h : SecondStageInvariant nums i specs mgs specs st) {κ : Nat} (hκ : κ < rbaPack) :
    st.1[κ]! = andWords specs nums[κ]! i κ :=
  h.2 κ hκ

/-- At the stop the bit array is zero, and so is its and with the rows of the other moduli. -/
theorem SecondStageInvariant.of_isZeroAt {nums v : Vector UInt64 rbaPack} {i : Int}
    {specs pref suff : List SieveSpec} {cur : SieveSpec} {mgs rest rest' : List Nat}
    (hs : specs = pref ++ cur :: suff) (h : SecondStageInvariant nums i specs mgs pref (v, rest))
    (hz : isZeroAt v 0 = true) : SecondStageInvariant nums i specs mgs specs (v, rest') := by
  refine ⟨fun h' ↦ absurd h' (Nat.lt_irrefl _), fun κ hκ ↦ ?_⟩
  have h0 := (isZeroAt_eq_true_iff v 0).mp hz κ hκ
  rw [Nat.mul_zero, Nat.zero_add] at h0
  rw [h0, hs, andWords_append, ← h.2 κ hκ, h0, andWords_zero]

/-- A step of the loop of `Ratpoints.Sieve.secondStage`: the bit array and-ed with bit array
`(i + offset) mod p` of the row of the next modulus `s`, the index that the reduction by the
reciprocal of the cursor gives under the test `small`
(`Ratpoints.Sieve.SieveSpec.Fits.ite_mulMod_modLong_eq_toNat_emod`). -/
theorem SecondStageInvariant.andBitArray {nums v : Vector UInt64 rbaPack} {i : Int} {small : Bool}
    {specs pref suff : List SieveSpec} {s : SieveSpec} {mgs rest rest' : List Nat} {mg : Nat}
    (pre : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small i (i + 1))
    (hs : specs = pref ++ s :: suff) (h : SecondStageInvariant nums i specs mgs pref (v, rest))
    (hnext : Std.Stream.next? rest = some (mg, rest')) :
    SecondStageInvariant nums i specs mgs (pref ++ [s]) (Sieve.andBitArray v 0 s.row
      (if small then mulMod (i + s.offset).toNat s.p mg else (modLong (i + s.offset) s.p).toNat),
        rest') := by
  obtain ⟨rfl, hc⟩ := eq_magic_and_of_next?_eq_some pre.2.1 hs h.1 hnext
  rw [(pre.1 s (by simp [hs])).ite_mulMod_modLong_eq_toNat_emod pre.2.2]
  refine ⟨hc, fun κ hκ ↦ ?_⟩
  simp only [getElem!_andBitArray _ _ _ _ hκ, Nat.div_eq_of_lt hκ, ↓reduceIte, Nat.mod_eq_of_lt hκ,
    h.2 κ hκ, andWords_concat, SieveSpec.wordAt_of_lt _ _ hκ]

attribute [local irreducible] SecondStageInvariant in
/-- The stop when the bit array is zero loses nothing, since a zero bit array stays zero; the
reciprocals run in step with the moduli and do not run out before them. -/
@[spec]
theorem secondStage_spec (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (i : Int)
    (nums : Vector UInt64 rbaPack) :
    ⦃ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small i (i + 1) ⦄
    secondStage specs mgs small i nums
    ⦃ fun r ↦ ∀ κ < rbaPack, r[κ]! = andWords specs nums[κ]! i κ ⦄ := by
  vcgen [secondStage] invariants
  · fun pref _ ↦ SecondStageInvariant nums i specs mgs pref
  all_goals first
    | exact secondStageInvariant_nil nums i specs mgs
    | exact SecondStageInvariant.getElem!_eq ‹_› ‹_›
    | exact SecondStageInvariant.of_isZeroAt ‹_› ‹_› ‹_›
    | exact absurd ‹_› (SecondStageInvariant.next?_ne_none ‹_› ‹_› ‹_›)
    | exact SecondStageInvariant.andBitArray ‹_› ‹_› ‹_› ‹_›

/-- The invariant of the loop of `Ratpoints.Sieve.secondStageWord` over the moduli `specs` and their
reciprocals `mgs` on word `κ` of the bit array with the word number `i`, from the word `x0` on,
after the moduli `pref`, whose state is the word and the reciprocals still to come: before the loop
has gone through all the moduli, these are the reciprocals after the first `pref.length`; and the
word is `x0` and-ed with the row words of the moduli of `pref`. -/
def SecondStageWordInvariant (x0 : UInt64) (i : Int) (κ : Nat) (specs : List SieveSpec)
    (mgs : List Nat) (pref : List SieveSpec) (st : UInt64 × List Nat) : Prop :=
  (pref.length < specs.length → st.2 = mgs.drop pref.length) ∧ st.1 = andWords pref x0 i κ

/-- A step of the loop of `Ratpoints.Sieve.secondStageWord`, as for
`Ratpoints.Sieve.SecondStageInvariant.andBitArray`. -/
theorem SecondStageWordInvariant.and {x0 x : UInt64} {i : Int} {κ : Nat} (hκ : κ < rbaPack)
    {small : Bool} {specs pref suff : List SieveSpec} {s : SieveSpec} {mgs rest rest' : List Nat}
    {mg : Nat}
    (pre : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small i (i + 1))
    (hs : specs = pref ++ s :: suff) (h : SecondStageWordInvariant x0 i κ specs mgs pref (x, rest))
    (hnext : Std.Stream.next? rest = some (mg, rest')) :
    SecondStageWordInvariant x0 i κ specs mgs (pref ++ [s]) (x &&& s.row[rbaPack *
      (if small then mulMod (i + s.offset).toNat s.p mg else (modLong (i + s.offset) s.p).toNat) +
        κ]!, rest') := by
  obtain ⟨rfl, hc⟩ := eq_magic_and_of_next?_eq_some pre.2.1 hs h.1 hnext
  rw [(pre.1 s (by simp [hs])).ite_mulMod_modLong_eq_toNat_emod pre.2.2]
  have h2 : x = andWords pref x0 i κ := h.2
  refine ⟨hc, ?_⟩
  change x &&& _ = _
  rw [h2, andWords_concat, SieveSpec.wordAt_of_lt _ _ hκ]

theorem SecondStageWordInvariant.next?_ne_none {x0 x : UInt64} {i : Int} {κ : Nat} {small : Bool}
    {specs pref suff : List SieveSpec} {s : SieveSpec} {mgs rest : List Nat}
    (pre : (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small i (i + 1))
    (hs : specs = pref ++ s :: suff)
    (h : SecondStageWordInvariant x0 i κ specs mgs pref (x, rest)) :
    Std.Stream.next? rest ≠ none :=
  next?_ne_none_of_lt pre.2.1 hs h.1

theorem secondStageWordInvariant_nil (x0 : UInt64) (i : Int) (κ : Nat) (specs : List SieveSpec)
    (mgs : List Nat) : SecondStageWordInvariant x0 i κ specs mgs [] (x0, Std.toStream mgs) :=
  ⟨fun _ ↦ rfl, rfl⟩

theorem SecondStageWordInvariant.eq {x0 : UInt64} {i : Int} {κ : Nat} {specs : List SieveSpec}
    {mgs : List Nat} {st : UInt64 × List Nat}
    (h : SecondStageWordInvariant x0 i κ specs mgs specs st) :
    st.1 = andWords specs x0 i κ :=
  h.2

/-- At the stop the word is zero, and so is its and with the rows of the other moduli. -/
theorem SecondStageWordInvariant.of_eq_zero {x0 x : UInt64} {i : Int} {κ : Nat}
    {specs pref suff : List SieveSpec} {cur : SieveSpec} {mgs rest rest' : List Nat}
    (hs : specs = pref ++ cur :: suff)
    (h : SecondStageWordInvariant x0 i κ specs mgs pref (x, rest))
    (hz : (x == 0) = true) : SecondStageWordInvariant x0 i κ specs mgs specs (x, rest') := by
  refine ⟨fun h' ↦ absurd h' (Nat.lt_irrefl _), ?_⟩
  rw [beq_iff_eq.mp hz] at h ⊢
  rw [hs, andWords_append, ← h.2, andWords_zero]

attribute [local irreducible] SecondStageWordInvariant in
/-- The stop when the word is zero loses nothing, since a zero word stays zero; the reciprocals run
in step with the moduli and do not run out before them. -/
@[spec]
theorem secondStageWord_spec (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (i : Int)
    {κ : Nat} (hκ : κ < rbaPack) (x : UInt64) :
    ⦃ (∀ s ∈ specs, s.Fits) ∧ mgs = specs.map (magic ·.p) ∧ SmallFits small i (i + 1) ⦄
    secondStageWord specs mgs small i κ x ⦃ fun r ↦ r = andWords specs x i κ ⦄ := by
  vcgen [secondStageWord] invariants
  · fun pref _ ↦ SecondStageWordInvariant x i κ specs mgs pref
  all_goals first
    | exact secondStageWordInvariant_nil x i κ specs mgs
    | exact SecondStageWordInvariant.eq ‹_›
    | exact SecondStageWordInvariant.of_eq_zero ‹_› ‹_› ‹_›
    | exact absurd ‹_› (SecondStageWordInvariant.next?_ne_none ‹_› ‹_› ‹_›)
    | exact SecondStageWordInvariant.and hκ ‹_› ‹_› ‹_› ‹_›

end Sieve

end Ratpoints

end
