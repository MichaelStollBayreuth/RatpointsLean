/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Proof.Rows
public import Std.WP

import Ratpoints.Proof.Bits
import Ratpoints.Proof.Containers
import Std.Tactic.Do

/-!
# The contracts of the builders of the rows of a prime

The contracts of the functions that the build of ratpoints generates for the primes of the table
from `CODE_INIT_SIEVE1` (`Ratpoints.Sieve.sieveInit1`, a prime below 64) and `CODE_INIT_SIEVE2`
(`Ratpoints.Sieve.sieveInit2`, a prime above 64), and of their pieces and macros, as `@[spec]`
theorems proved with `vcgen`, the program logic of Lean core, with loop invariants that are named
definitions: the row of the residue `0 < b < p` of a prime `p` is the closed form of the row of `b`
of its table (`Ratpoints.Sieve.closedRow` of `Ratpoints.Sieve.Entry.admits`), and the builder stores
it into the table of rows of its entry (`Ratpoints.Sieve.RowStore.publish`).

The pattern of a row is computed four bits at a time by four lanes, whose residues step through the
residues `x d mod p` for the inverse `d` of `b` (`Ratpoints.Sieve.LanesAt`,
`Ratpoints.Sieve.lanePattern`); `CODE_INIT_SIEVE1` doubles the pattern of `p` bits up to a word
and rotates it through the first `p` words, `CODE_INIT_SIEVE2` keeps it in a ring of `⌊p / 64⌋ + 1`
words (`Ratpoints.Sieve.RingState`); both end with the copies of `RP_INIT_REPLICATE`.

## Main definitions

* `Ratpoints.Sieve.lanePattern`, `Ratpoints.Sieve.LanesAt`: the pattern of the lanes and the lanes
  at a bit of it.
* `Ratpoints.Sieve.RingState`: the ring of the words of `CODE_INIT_SIEVE2`.

## Main statements

* `Ratpoints.Sieve.initFourDecl_lanes`, `Ratpoints.Sieve.initFourLoop_spec`: the four lanes and the
  bits that they compute.
* `Ratpoints.Sieve.initReplicate_spec`: the copies of `RP_INIT_REPLICATE`.
* `Ratpoints.Sieve.sieveInit1_spec`, `Ratpoints.Sieve.sieveInit2_spec`: the rows of a prime below
  and above 64 are the closed forms of the rows of their tables, stored into the tables of rows of
  their entries.

## Implementation notes

The file uses Lean core and `Std` only, as the contracts of the sieve do. The proofs use only that
`Ratpoints.rbaPack` and `Ratpoints.chunk` are positive, never their values; every shift that the
builders execute is shown to be by an amount below 64, where Lean's shifts and the C code's agree.
The builders need of the prime only the inverse of `b` below `p`, and for `CODE_INIT_SIEVE2` that
`p mod 64 ≠ 0`: no primality and nothing of the table of squares.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The four lanes -/

/-- The pattern of the lanes from the residue `ab₀` on, stepping by `d` modulo `p`: bit `N` is the
entry of `isfs` at `ab₀ + N d mod p`. It has the period `p` (`Ratpoints.Sieve.lanePattern_mod`). -/
def lanePattern (isfs : Array Bool) (p ab0 d N : Nat) : Bool := isfs[(ab0 + N * d) % p]!

theorem lanePattern_mod (isfs : Array Bool) (p ab0 d N : Nat) :
    lanePattern isfs p ab0 d (N % p) = lanePattern isfs p ab0 d N := by
  simp only [lanePattern, Nat.add_mod ab0, Nat.mod_mul_mod]

/-- The four lanes at the bit `x` of the pattern from `ab₀` on: the residues of `ab₀ + (x + k) d`
modulo `p`, `k < 4`. -/
def LanesAt (p d ab0 x ab ab1 ab2 ab3 : Nat) : Prop :=
  ab = (ab0 + x * d) % p ∧ ab1 = (ab0 + (x + 1) * d) % p ∧ ab2 = (ab0 + (x + 2) * d) % p ∧
    ab3 = (ab0 + (x + 3) * d) % p

/-- A lane stepped by `d4 = 4 d mod p`. -/
theorem ite_add_mod_eq_add_four_mul_mod {p d ab0 x : Nat} (hp : 0 < p) :
    (if p ≤ (ab0 + x * d) % p + 4 * d % p then (ab0 + x * d) % p + 4 * d % p - p
      else (ab0 + x * d) % p + 4 * d % p) = (ab0 + (x + 4) * d) % p := by
  rw [Nat.ite_add_mod_mod hp, Nat.add_mul, Nat.add_assoc, Nat.mul_comm 4 d]

/-- `RP_INIT_FOUR_DECL` puts the lanes at the bits `0, 1, 2, 3` of the pattern from `0` on, for
`d < p`, and their step at `4 d mod p`. -/
theorem initFourDecl_lanes {p d : Nat} (hd : d < p) :
    (initFourDecl p d).2.2.2 = 4 * d % p ∧
      LanesAt p d 0 0 0 (initFourDecl p d).1 (initFourDecl p d).2.1 (initFourDecl p d).2.2.1 := by
  have hp : 0 < p := Nat.lt_of_le_of_lt (Nat.zero_le d) hd
  have h2 : (if p ≤ d + d then d + d - p else d + d) = 2 * d % p := by
    rw [← Nat.mod_eq_ite_of_lt_two_mul (by lia), Nat.two_mul]
  have h3 : (if p ≤ 2 * d % p + d then 2 * d % p + d - p else 2 * d % p + d) = 3 * d % p := by
    rw [← Nat.mod_eq_ite_of_lt_two_mul (by lia [Nat.mod_lt (2 * d) hp]), Nat.mod_add_mod]
    congr 1
    lia
  have h4 : (if p ≤ 3 * d % p + d then 3 * d % p + d - p else 3 * d % p + d) = 4 * d % p := by
    rw [← Nat.mod_eq_ite_of_lt_two_mul (by lia [Nat.mod_lt (3 * d) hp]), Nat.mod_add_mod]
    congr 1
    lia
  simp only [initFourDecl, ge_iff_le, h2, h3, h4, LanesAt]
  exact ⟨by simp, by simp, by simp [Nat.mod_eq_of_lt hd], by simp, by simp⟩

/-- The bits `i, …, i + 3` of the four lanes, or-ed into the word of the bits below `i`. -/
theorem PatternBits.or_four {isfs : Array Bool} {p d ab0 i : Nat} {w : UInt64}
    (h : PatternBits (lanePattern isfs p ab0 d) p 0 i w) (hi : i + 4 ≤ 64) :
    PatternBits (lanePattern isfs p ab0 d) p 0 (i + 4)
      (w ||| (isfs[(ab0 + i * d) % p]!.toUInt64 <<< UInt64.ofNat i |||
        isfs[(ab0 + (i + 1) * d) % p]!.toUInt64 <<< UInt64.ofNat (i + 1) |||
        isfs[(ab0 + (i + 2) * d) % p]!.toUInt64 <<< UInt64.ofNat (i + 2) |||
        isfs[(ab0 + (i + 3) * d) % p]!.toUInt64 <<< UInt64.ofNat (i + 3))) := by
  intro t
  simp only [UInt64.toBitVec_or, BitVec.getLsbD_or, h t, Nat.zero_add, lanePattern_mod,
    UInt64.getLsbD_toUInt64_shiftLeft _ (show i < 64 by lia),
    UInt64.getLsbD_toUInt64_shiftLeft _ (show i + 1 < 64 by lia),
    UInt64.getLsbD_toUInt64_shiftLeft _ (show i + 2 < 64 by lia),
    UInt64.getLsbD_toUInt64_shiftLeft _ (show i + 3 < 64 by lia)]
  by_cases h0 : t < i
  · simp [h0, show t < i + 4 by lia, show t ≠ i by lia, show t ≠ i + 1 by lia,
      show t ≠ i + 2 by lia, show t ≠ i + 3 by lia]
  · rcases (show t = i ∨ t = i + 1 ∨ t = i + 2 ∨ t = i + 3 ∨ i + 4 ≤ t by lia) with
      rfl | rfl | rfl | rfl | h4 <;> simp [lanePattern, *] <;> lia

/-- The lanes and the word of the loop of four lanes at the bit `i`, for the step `d` of the lanes
from the residue `ab₀` on. -/
def FourLanes (isfs : Array Bool) (p d ab0 : Nat) (w : UInt64) (ab ab1 ab2 ab3 i : Nat) : Prop :=
  LanesAt p d ab0 i ab ab1 ab2 ab3 ∧ PatternBits (lanePattern isfs p ab0 d) p 0 i w

/-- The invariant of the loop of `Ratpoints.Sieve.initFourLoop` from the bit `0` and the word `0`
on, with the lanes `ab₀, ab1₀, ab2₀, ab3₀` at the start: the bit `i` a multiple of 4 up to `hi`, and
for every step `d` of the lanes with `d4 = 4 d mod p`, the lanes at `i` and the bits below `i` of
the pattern of the lanes in the word. -/
def FourInvariant (isfs : Array Bool) (p d4 ab0 ab10 ab20 ab30 hi : Nat) :
    Std.WP.WhileInvariant (UInt64 × Nat × Nat × Nat × Nat × Nat) Prop :=
  .mk fun exit s ↦ s.2.2.2.2.2 % 4 = 0 ∧ s.2.2.2.2.2 ≤ hi ∧ (exit = true → hi < s.2.2.2.2.2 + 4) ∧
    ∀ d < p, d4 = 4 * d % p → LanesAt p d ab0 0 ab0 ab10 ab20 ab30 →
      FourLanes isfs p d ab0 s.1 s.2.1 s.2.2.1 s.2.2.2.1 s.2.2.2.2.1 s.2.2.2.2.2

theorem fourInvariant_zero (isfs : Array Bool) {p d4 hi ab ab1 ab2 ab3 : Nat} {w : UInt64}
    {lo : Nat} (pre : w = 0 ∧ lo = 0 ∧ 0 < p ∧ hi ≤ 64) :
    FourInvariant isfs p d4 ab ab1 ab2 ab3 hi false (w, ab, ab1, ab2, ab3, lo) := by
  obtain ⟨rfl, rfl, -, -⟩ := pre
  exact ⟨rfl, Nat.zero_le _, nofun, fun _ _ _ h ↦ ⟨h, fun t ↦ by simp⟩⟩

/-- A step of the loop of four lanes. -/
theorem FourInvariant.add_four {isfs : Array Bool} {p d4 ab0 ab10 ab20 ab30 hi mb : Nat}
    {w : UInt64} {lo : Nat} {w' : UInt64} {ab ab1 ab2 ab3 i : Nat}
    (pre : w' = 0 ∧ lo = 0 ∧ 0 < p ∧ hi ≤ 64)
    (h : hi - i = mb ∧
      FourInvariant isfs p d4 ab0 ab10 ab20 ab30 hi false (w, ab, ab1, ab2, ab3, i))
    (hi4 : i + 4 ≤ hi) :
    hi - (i + 4) < mb ∧ FourInvariant isfs p d4 ab0 ab10 ab20 ab30 hi false
      (w ||| (isfs[ab]!.toUInt64 <<< UInt64.ofNat i |||
          isfs[ab1]!.toUInt64 <<< UInt64.ofNat (i + 1) |||
          isfs[ab2]!.toUInt64 <<< UInt64.ofNat (i + 2) |||
          isfs[ab3]!.toUInt64 <<< UInt64.ofNat (i + 3)),
        if p ≤ ab + d4 then ab + d4 - p else ab + d4,
        if p ≤ ab1 + d4 then ab1 + d4 - p else ab1 + d4,
        if p ≤ ab2 + d4 then ab2 + d4 - p else ab2 + d4,
        if p ≤ ab3 + d4 then ab3 + d4 - p else ab3 + d4, i + 4) := by
  obtain ⟨-, -, hp, h64⟩ := pre
  obtain ⟨rfl, hi0, -, -, hl⟩ := h
  dsimp only at hi0 hl ⊢
  refine ⟨by lia, by lia, by lia, nofun, fun d hd hd4 h0 ↦ ?_⟩
  obtain ⟨⟨rfl, rfl, rfl, rfl⟩, hw⟩ := hl d hd hd4 h0
  subst hd4
  refine ⟨⟨?_, ?_, ?_, ?_⟩, hw.or_four (by lia)⟩ <;> dsimp only <;>
    rw [ite_add_mod_eq_add_four_mul_mod hp] <;> simp only [Nat.add_right_comm _ 4]

theorem FourInvariant.exit {isfs : Array Bool} {p d4 ab0 ab10 ab20 ab30 hi mb : Nat} {w : UInt64}
    {ab ab1 ab2 ab3 i : Nat}
    (h : hi - i = mb ∧
      FourInvariant isfs p d4 ab0 ab10 ab20 ab30 hi false (w, ab, ab1, ab2, ab3, i))
    (hi4 : ¬i + 4 ≤ hi) :
    FourInvariant isfs p d4 ab0 ab10 ab20 ab30 hi true (w, ab, ab1, ab2, ab3, i) :=
  ⟨h.2.1, h.2.2.1, fun _ ↦ by lia, h.2.2.2.2⟩

theorem FourInvariant.post {isfs : Array Bool} {p d4 ab0 ab10 ab20 ab30 hi : Nat} {w : UInt64}
    {ab ab1 ab2 ab3 i : Nat}
    (h : FourInvariant isfs p d4 ab0 ab10 ab20 ab30 hi true (w, ab, ab1, ab2, ab3, i)) :
    i = 4 * (hi / 4) ∧ ∀ d < p, d4 = 4 * d % p → LanesAt p d ab0 0 ab0 ab10 ab20 ab30 →
      FourLanes isfs p d ab0 w ab ab1 ab2 ab3 (4 * (hi / 4)) := by
  obtain ⟨h4, hi0, hex, hl⟩ := h
  dsimp only at h4 hi0 hex hl
  have : i = 4 * (hi / 4) := by lia [hex rfl]
  exact ⟨this, this ▸ hl⟩

attribute [local irreducible] FourInvariant in
open Std.WP Lean.Order in
/-- The loop of four lanes from the bit `0` and the word `0` on, as its callers start it, ends at
the bit `4 ⌊hi / 4⌋` with the bits below it of the pattern of the lanes in the word and the lanes
at that bit, for every step `d < p` of the lanes with `d4 = 4 d mod p`. -/
@[spec]
theorem initFourLoop_spec (isfs : Array Bool) (p d4 : Nat) (w : UInt64)
    (lo hi ab ab1 ab2 ab3 : Nat) :
    ⦃ w = 0 ∧ lo = 0 ∧ 0 < p ∧ hi ≤ 64 ⦄ initFourLoop isfs p d4 w lo hi ab ab1 ab2 ab3
    ⦃ fun r ↦ r.2.1 = 4 * (hi / 4) ∧ ∀ d < p, d4 = 4 * d % p → LanesAt p d ab 0 ab ab1 ab2 ab3 →
        FourLanes isfs p d ab r.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 (4 * (hi / 4)) ⦄ := by
  vcgen [initFourLoop] invariants
  · FourInvariant isfs p d4 ab ab1 ab2 ab3 hi
  · Variant.ofMeasure fun s : UInt64 × Nat × Nat × Nat × Nat × Nat ↦ hi - s.2.2.2.2.2
  all_goals try simp only [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
    Variant.evalsBelow_ofMeasure_nat, meet_prop_eq_and, ofProp_prop_eq] at *
  all_goals first
    | exact fourInvariant_zero isfs ‹_›
    | exact FourInvariant.post ‹_›
    | exact FourInvariant.add_four ‹_› ‹_› ‹_›
    | exact FourInvariant.exit ‹_› ‹_›

/-! ### The bits left over -/

/-- The state of a loop that sets the bits from `lo` on one at a time from the first lane, after `c`
of them: the word holds the bits of the pattern of the lanes from `ab₀` on below `lo + c`, and the
lane is at the bit `lo + c`. -/
def RestInvariant (isfs : Array Bool) (p d ab0 lo c : Nat) (st : UInt64 × Nat) : Prop :=
  PatternBits (lanePattern isfs p ab0 d) p 0 (lo + c) st.1 ∧ st.2 = (ab0 + (lo + c) * d) % p

/-- A bit set from the first lane, `RP_INIT_BIT`, and the lane stepped by `d`. -/
theorem RestInvariant.append_initBit {isfs : Array Bool} {p d ab0 lo hi cur : Nat}
    {pref suff : List Nat} {w : UInt64} {ab : Nat} (pre : 0 < p ∧ hi ≤ 64 ∧ d < p)
    (hl : ForIn.toList [lo:hi] = pref ++ cur :: suff)
    (h : RestInvariant isfs p d ab0 lo pref.length (w, ab)) :
    RestInvariant isfs p d ab0 lo (pref ++ [cur]).length
      (initBit w isfs[ab]! cur, if p ≤ ab + d then ab + d - p else ab + d) := by
  obtain ⟨hp, hhi, hd⟩ := pre
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  obtain ⟨hw, rfl⟩ := h
  dsimp only at hw
  rw [hc] at hw
  rw [RestInvariant, List.length_append, List.length_singleton, ← Nat.add_assoc, hc]
  refine ⟨fun x ↦ ?_, ?_⟩
  · simp only [initBit, UInt64.toBitVec_or, BitVec.getLsbD_or, hw x, Nat.zero_add,
      lanePattern_mod, UInt64.getLsbD_toUInt64_shiftLeft _ (show cur < 64 by lia)]
    by_cases h0 : x < cur
    · simp [h0, show x < cur + 1 by lia, show x ≠ cur by lia]
    · by_cases h1 : x = cur
      · subst h1
        simp [lanePattern]
      · simp [h0, h1, show ¬x < cur + 1 by lia]
  · dsimp only
    rw [← Nat.mod_eq_ite_of_lt_two_mul (by lia [Nat.mod_lt (ab0 + cur * d) hp]), Nat.mod_add_mod,
      Nat.add_assoc, Nat.add_one_mul]

/-- The loop of the bits left over from `lo ≤ hi` on ends with the bits below `hi`. -/
theorem RestInvariant.post {isfs : Array Bool} {p d ab0 lo hi : Nat} {st : UInt64 × Nat}
    (hlo : lo ≤ hi) (h : RestInvariant isfs p d ab0 lo (ForIn.toList [lo:hi]).length st) :
    PatternBits (lanePattern isfs p ab0 d) p 0 hi st.1 ∧ st.2 = (ab0 + hi * d) % p := by
  rwa [RestInvariant, Std.Legacy.Range.length_toList, Nat.add_sub_cancel' hlo] at h

/-- The start of the loop of the bits left over, after the loop of four lanes. -/
theorem restInvariant_init {isfs : Array Bool} {p d ab0 i : Nat} {w : UInt64} {ab ab1 ab2 ab3 : Nat}
    (h : FourLanes isfs p d ab0 w ab ab1 ab2 ab3 i) :
    RestInvariant isfs p d ab0 i ([] : List Nat).length (w, ab) :=
  ⟨h.2, h.1.1⟩

/-! ### The rows of a prime below 64 -/

theorem sieve1Pattern_pre {t : Entry} {b : Nat}
    (pre : 0 < t.p ∧ t.p ≤ 64 ∧ t.inverses[b]! < t.p) : 0 < t.p ∧ t.p ≤ 64 :=
  ⟨pre.1, pre.2.1⟩

theorem sieve1Pattern_rest_init {t : Entry} {b : Nat} {r : UInt64 × Nat × Nat × Nat × Nat × Nat}
    (pre : 0 < t.p ∧ t.p ≤ 64 ∧ t.inverses[b]! < t.p)
    (h : r.2.1 = 4 * (t.p / 4) ∧ ∀ d < t.p, (initFourDecl t.p t.inverses[b]!).2.2.2 = 4 * d % t.p →
      LanesAt t.p d 0 0 0 (initFourDecl t.p t.inverses[b]!).1
        (initFourDecl t.p t.inverses[b]!).2.1 (initFourDecl t.p t.inverses[b]!).2.2.1 →
      FourLanes t.isFSquare t.p d 0 r.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 (4 * (t.p / 4))) :
    RestInvariant t.isFSquare t.p t.inverses[b]! 0 r.2.1 ([] : List Nat).length (r.1, r.2.2.1) := by
  obtain ⟨hd4, hl⟩ := initFourDecl_lanes pre.2.2
  rw [h.1]
  exact restInvariant_init (h.2 _ pre.2.2 hd4 hl)

theorem sieve1Pattern_rest_post {t : Entry} {b : Nat} {r : UInt64 × Nat × Nat × Nat × Nat × Nat}
    {st : UInt64 × Nat}
    (hr : r.2.1 = 4 * (t.p / 4) ∧ ∀ d < t.p, (initFourDecl t.p t.inverses[b]!).2.2.2 = 4 * d % t.p →
      LanesAt t.p d 0 0 0 (initFourDecl t.p t.inverses[b]!).1
        (initFourDecl t.p t.inverses[b]!).2.1 (initFourDecl t.p t.inverses[b]!).2.2.1 →
      FourLanes t.isFSquare t.p d 0 r.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2 (4 * (t.p / 4)))
    (h : RestInvariant t.isFSquare t.p t.inverses[b]! 0 r.2.1
      (ForIn.toList [r.2.1:t.p]).length st) :
    PatternBits (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p 0 t.p st.1 :=
  (h.post (by rw [hr.1]; lia)).1

/-- The pattern of the row of the residue `b` of the prime `p = t.p ≤ 64` with the inverse
`d < p` of `b`: bit `a < p` is the entry of the table at `a d mod p`, the higher bits clear. -/
@[spec]
theorem sieve1Pattern_spec (t : Entry) (b : Nat) :
    ⦃ 0 < t.p ∧ t.p ≤ 64 ∧ t.inverses[b]! < t.p ⦄ sieve1Pattern t b
    ⦃ fun w ↦ PatternBits (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p 0 t.p w ⦄ := by
  vcgen [sieve1Pattern] invariants
  | inv1 _ _ i _ _ _ _ _ => fun done _ st ↦
      RestInvariant t.isFSquare t.p t.inverses[b]! 0 i done.length st
  all_goals first
    | exact sieve1Pattern_pre ‹_›
    | exact sieve1Pattern_rest_init ‹_› ‹_›
    | exact sieve1Pattern_rest_post ‹_› ‹_›
    | exact RestInvariant.append_initBit ‹_› ‹_› ‹_›

/-! ### The copies of `RP_INIT_REPLICATE` -/

/-- The invariant of the loops of the copies of `Ratpoints.Sieve.initReplicate` through the first
`p` bit arrays, with the residues below `a` done and of residue `a` the copies up to `a + c p`: the
words below `p` and those done are the words of `si` below `p` that they repeat. -/
def RepInvariant {n : Nat} (p : Nat) (si : Vector UInt64 n) (a c : Nat) (si' : Vector UInt64 n) :
    Prop :=
  ∀ j < p * rbaPack, (j < p ∨ j % p < a ∨ (j % p = a ∧ j / p ≤ c)) → si'[j]! = si[j % p]!

/-- The invariant of the loop of the copies of the first bit arrays after the first `p`, after `c`
of them: the words below `p rbaPack + c` repeat the words of `si` below `p`. -/
def CopyInvariant {n : Nat} (p : Nat) (si : Vector UInt64 n) (c : Nat) (si' : Vector UInt64 n) :
    Prop :=
  ∀ j < p * rbaPack + c, si'[j]! = si[j % p]!

theorem repInvariant_zero {n : Nat} (p : Nat) (si : Vector UInt64 n) :
    RepInvariant p si ([] : List Nat).length 0 si := fun j hj h ↦ by
  have hp : 0 < p := Nat.pos_of_mul_pos_right (Nat.lt_of_le_of_lt (Nat.zero_le j) hj)
  have hjp : j < p := by
    rcases h with h | h | ⟨-, h⟩
    · exact h
    · simp at h
    · lia [(Nat.div_lt_iff_lt_mul hp).mp (show j / p < 1 by lia)]
  rw [Nat.mod_eq_of_lt hjp]

theorem RepInvariant.of_eq {n p a c a' c' : Nat} {si si' : Vector UInt64 n}
    (h : RepInvariant p si a c si') (ha : a = a') (hc : c = c') : RepInvariant p si a' c' si' :=
  ha ▸ hc ▸ h

/-- The copies of residue `a` all done: the residues below `a + 1` are done. -/
theorem RepInvariant.next {n p a : Nat} {si si' : Vector UInt64 n}
    (h : RepInvariant p si a (ForIn.toList [1:rbaPack]).length si') :
    RepInvariant p si (a + 1) 0 si' := by
  intro j hj hj'
  have hp : 0 < p := Nat.pos_of_mul_pos_right (Nat.lt_of_le_of_lt (Nat.zero_le j) hj)
  have := (Nat.div_lt_iff_lt_mul hp).mpr (by rwa [Nat.mul_comm] at hj)
  have := Nat.div_add_mod j p
  have := Nat.mod_lt j hp
  refine h j hj ?_
  rw [Std.Legacy.Range.length_toList]
  grind

/-- A copy of word `a` to word `a + k p`, `1 ≤ k < rbaPack`, after the copies up to
`a + (k - 1) p`. -/
theorem RepInvariant.set! {n p a c : Nat} {si si' : Vector UInt64 n} (ha : a < p)
    (hn : p * rbaPack ≤ n) (h : RepInvariant p si a c si') (hk : c + 1 < rbaPack) :
    RepInvariant p si a (c + 1) (si'.set! (a + (c + 1) * p) si'[a]!) := by
  have hkp : a + (c + 1) * p < p * rbaPack := by
    rw [Nat.mul_comm p]
    lia [Nat.mul_le_mul_right p (show c + 2 ≤ rbaPack by lia)]
  intro j hj hj'
  rw [Vector.getElem!_set! (by lia)]
  by_cases hja : a + (c + 1) * p = j
  · subst hja
    rw [ite_eq_left rfl, h a (by lia) (.inl ha), Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt ha]
  · rw [ite_eq_right hja]
    have := Nat.div_add_mod j p
    refine h j hj ?_
    rcases hj' with h1 | h1 | ⟨h1, h2⟩
    · exact .inl h1
    · exact .inr (.inl h1)
    · refine .inr (.inr ⟨h1, ?_⟩)
      rcases Nat.lt_or_eq_of_le h2 with h2 | h2
      · lia
      · exact absurd (by rw [← this, h1, h2, Nat.mul_comm, Nat.add_comm]) hja

/-- The step of the loop of the copies of a residue, in the shape of the verification condition. -/
theorem RepInvariant.append {p n a cur : Nat} {pref' suff' pref suff : List Nat}
    {si si' : Vector UInt64 n} (pre : 0 < p ∧ n = (p + chunk - 1) * rbaPack)
    (hl' : ForIn.toList [0:p] = pref' ++ a :: suff')
    (hl : ForIn.toList [1:rbaPack] = pref ++ cur :: suff)
    (h : RepInvariant p si a pref.length si') :
    RepInvariant p si a (pref ++ [cur]).length (si'.set! (a + cur * p) si'[a]!) := by
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hk := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hn : p * rbaPack ≤ n := by
    rw [pre.2]; exact Nat.mul_le_mul_right rbaPack (by lia [chunk_pos])
  rw [List.length_append, List.length_singleton, ← hc, Nat.add_comm 1]
  exact h.set! (Std.Legacy.Range.lt_of_toList_eq_append_cons hl') hn (by lia)

theorem RepInvariant.append_of_next {n p cur : Nat} {pref suff : List Nat}
    {si si' : Vector UInt64 n} (hl : ForIn.toList [0:p] = pref ++ cur :: suff)
    (h : RepInvariant p si cur (ForIn.toList [1:rbaPack]).length si') :
    RepInvariant p si (pref ++ [cur]).length 0 si' := by
  rw [List.length_append, List.length_singleton,
    Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl]
  exact h.next

theorem RepInvariant.copyInvariant {n p : Nat} {si si' : Vector UInt64 n}
    (pre : 0 < p ∧ n = (p + chunk - 1) * rbaPack)
    (h : RepInvariant p si (ForIn.toList [0:p]).length 0 si') : CopyInvariant p si 0 si' :=
  fun j hj ↦ h j (by lia) (.inr (.inl (by
    rw [Std.Legacy.Range.length_toList, Nat.sub_zero]; exact Nat.mod_lt _ pre.1)))

/-- A copy of word `k` to word `p rbaPack + k`, in the shape of the verification condition. -/
theorem CopyInvariant.append {p n cur : Nat} {pref suff : List Nat} {si si' : Vector UInt64 n}
    (pre : 0 < p ∧ n = (p + chunk - 1) * rbaPack)
    (hl : ForIn.toList [0:(chunk - 1) * rbaPack] = pref ++ cur :: suff)
    (h : CopyInvariant p si pref.length si') :
    CopyInvariant p si (pref ++ [cur]).length (si'.set! (p * rbaPack + cur) si'[cur]!) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hn : n = p * rbaPack + (chunk - 1) * rbaPack := by
    rw [pre.2, Nat.add_sub_assoc chunk_pos, Nat.add_mul]
  have hpr : 0 < p * rbaPack := Nat.mul_pos pre.1 rbaPack_pos
  intro j hj
  rw [List.length_append, List.length_singleton] at hj
  rw [Vector.getElem!_set! (by lia)]
  by_cases hjk : p * rbaPack + cur = j
  · subst hjk
    rw [ite_eq_left rfl, h cur (by lia), Nat.add_comm, Nat.mul_comm p, Nat.add_mul_mod_self_right]
  · rw [ite_eq_right hjk]
    exact h j (by lia)

theorem CopyInvariant.post {p n : Nat} {si si' : Vector UInt64 n}
    (pre : 0 < p ∧ n = (p + chunk - 1) * rbaPack)
    (h : CopyInvariant p si (ForIn.toList [0:(chunk - 1) * rbaPack]).length si') {j : Nat}
    (hj : j < n) : si'[j]! = si[j % p]! :=
  h j (by rw [Std.Legacy.Range.length_toList, Nat.sub_zero, ← Nat.add_mul,
    ← Nat.add_sub_assoc chunk_pos, ← pre.2]; exact hj)

attribute [local irreducible] RepInvariant CopyInvariant in
/-- After the copies, word `j` of the row is word `j mod p` of the row before, for every `j` below
the size `(p + chunk - 1) rbaPack` of the row. -/
@[spec]
theorem initReplicate_spec {n : Nat} (p : Nat) (si : Vector UInt64 n) :
    ⦃ 0 < p ∧ n = (p + chunk - 1) * rbaPack ⦄ initReplicate p si
    ⦃ fun si' ↦ ∀ j < n, si'[j]! = si[j % p]! ⦄ := by
  vcgen [initReplicate] invariants
  | inv1 => fun done _ si' ↦ RepInvariant p si done.length 0 si'
  | inv2 => fun done _ si' ↦ CopyInvariant p si done.length si'
  | inv3 _ a _ _ _ _ => fun done _ si' ↦ RepInvariant p si a done.length si'
  all_goals first
    | exact repInvariant_zero p si
    | exact RepInvariant.copyInvariant ‹_› ‹_›
    | exact CopyInvariant.post ‹_› ‹_› ‹_›
    | exact CopyInvariant.append ‹_› ‹_› ‹_›
    | exact RepInvariant.of_eq ‹_› (Std.Legacy.Range.length_eq_of_toList_eq_append_cons ‹_›) rfl
    | exact RepInvariant.append_of_next ‹_› ‹_›
    | exact RepInvariant.append ‹_› ‹_› ‹_› ‹_›

/-! ### `CODE_INIT_SIEVE1` -/

/-- The shifts of `CODE_INIT_SIEVE1` for `0 < p < 64`: `diff_shift = (⌊64 / p⌋ + 1) p mod 64` and
`64 mod p` add up to `p`, `64 + diff_shift` is the multiple `(⌊64 / p⌋ + 1) p` of `p`, and
`0 < diff_shift < 64`, so that every shift of the rotation is by an amount below 64. -/
theorem sieve1_shifts : ∀ p < 64, 0 < p →
    64 + (64 / p + 1) * p % 64 = (64 / p + 1) * p ∧ (64 / p + 1) * p % 64 + 64 % p = p ∧
      0 < (64 / p + 1) * p % 64 ∧ (64 / p + 1) * p % 64 < 64 := by
  decide

/-- The rotation of `CODE_INIT_SIEVE1`: from the window at `s` in `x0` and the next `ds` bits in
`x1`, for `64 + ds ≡ 0 (mod p)`, the window at `s + 64` and the `ds` bits after it. -/
theorem PatternBits.rotate {g : Nat → Bool} {p s ds k : Nat} {x0 x1 : UInt64}
    (hk : 64 + ds = k * p) (hds0 : 0 < ds) (hds : ds < 64)
    (h0 : PatternBits g p s 64 x0) (h1 : PatternBits g p (s + 64) ds x1) :
    PatternBits g p (s + 64) 64 (x1 ||| x0 <<< UInt64.ofNat ds) ∧
      PatternBits g p (s + 64 + 64) ds (x0 >>> UInt64.ofNat (64 - ds)) := by
  refine ⟨fun j ↦ ?_, fun j ↦ ?_⟩
  · rw [UInt64.toBitVec_or, BitVec.getLsbD_or, UInt64.getLsbD_shiftLeft_ofNat _ hds, h0, h1]
    by_cases hj : j < ds
    · simp [hj, show j < 64 by lia, show ¬ds ≤ j by lia]
    · have : (s + (j - ds)) % p = (s + 64 + j) % p := by
        rw [show s + 64 + j = s + (j - ds) + p * k by rw [Nat.mul_comm]; lia,
          Nat.add_mul_mod_self_left]
      by_cases hj' : j < 64
      · simp [hj, hj', this, show j - ds < 64 by lia, show ds ≤ j by lia]
      · simp [hj, hj']
  · rw [UInt64.getLsbD_shiftRight_ofNat _ (by lia), h0]
    have : (s + (64 - ds + j)) % p = (s + 64 + 64 + j) % p := by
      rw [show s + 64 + 64 + j = s + (64 - ds + j) + p * k by rw [Nat.mul_comm]; lia,
        Nat.add_mul_mod_self_left]
    by_cases hj : j < ds
    · simp [hj, this, show 64 - ds + j < 64 by lia]
    · simp [hj, show ¬64 - ds + j < 64 by lia]

/-- The invariant of the loop of the rotation of `Ratpoints.Sieve.sieve1Rows` after the words below
`c + 1`: `help0` the window at `64 c`, `help1` the next `ds` bits, and the words below `c + 1` the
windows of the pattern. -/
def RotInvariant (g : Nat → Bool) (p ds c : Nat) {n : Nat}
    (st : UInt64 × UInt64 × Vector UInt64 n) : Prop :=
  PatternBits g p (64 * c) 64 st.1 ∧ PatternBits g p (64 * c + 64) ds st.2.1 ∧
    RowWords g p (c + 1) st.2.2

theorem rotInvariant_init {p : Nat} {help0 help1 : UInt64} (pre : 0 < p ∧ p < 64) (g : Nat → Bool)
    (h0 : PatternBits g p 0 64 help0) (h1 : PatternBits g p 64 ((64 / p + 1) * p % 64) help1) :
    RotInvariant g p ((64 / p + 1) * p % 64) ([] : List Nat).length
      (help0, help1, (Vector.replicate ((p + chunk - 1) * rbaPack) 0).set! 0 help0) := by
  refine ⟨h0, h1, fun j hj ↦ ?_⟩
  obtain rfl : j = 0 := by simpa using hj
  have : 0 < (p + chunk - 1) * rbaPack := Nat.mul_pos (by lia [chunk_pos]) rbaPack_pos
  rw [Vector.getElem!_set! this, ite_eq_left rfl]
  exact h0

/-- A step of the rotation: word `c + 1` of the row the window at `64 (c + 1)`. -/
theorem RotInvariant.append {p cur : Nat} {pref suff : List Nat} {help0 help1 x0 x1 : UInt64}
    {si : Vector UInt64 ((p + chunk - 1) * rbaPack)} (pre : 0 < p ∧ p < 64)
    (hl : ForIn.toList [1:p] = pref ++ cur :: suff)
    (h : ∀ g, PatternBits g p 0 64 help0 → PatternBits g p 64 ((64 / p + 1) * p % 64) help1 →
      RotInvariant g p ((64 / p + 1) * p % 64) pref.length (x0, x1, si)) :
    ∀ g, PatternBits g p 0 64 help0 → PatternBits g p 64 ((64 / p + 1) * p % 64) help1 →
    RotInvariant g p ((64 / p + 1) * p % 64) (pref ++ [cur]).length
      (x1 ||| x0 <<< UInt64.ofNat ((64 / p + 1) * p % 64),
        x0 >>> UInt64.ofNat (64 - (64 / p + 1) * p % 64),
        si.set! cur (x1 ||| x0 <<< UInt64.ofNat ((64 / p + 1) * p % 64))) := by
  intro g h0 h1
  obtain ⟨hk, -, h0', h64⟩ := sieve1_shifts p pre.2 pre.1
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hcp := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hn : p ≤ (p + chunk - 1) * rbaPack :=
    Nat.le_trans (Nat.le_mul_of_pos_right p rbaPack_pos)
      (Nat.mul_le_mul_right _ (by lia [chunk_pos]))
  obtain ⟨hx0, hx1, hsi⟩ := h g h0 h1
  obtain ⟨r0, r1⟩ := hx0.rotate hk h0' h64 hx1
  rw [List.length_append, List.length_singleton, ← hc, Nat.add_comm 1 pref.length]
  refine ⟨by rwa [Nat.mul_add_one], by rwa [Nat.mul_add_one], ?_⟩
  rw [← hc, Nat.add_comm 1] at *
  exact hsi.set!_self (by lia) (by rwa [Nat.mul_add_one])

theorem RotInvariant.post {p : Nat} {help0 help1 : UInt64} {st : UInt64 × UInt64 ×
    Vector UInt64 ((p + chunk - 1) * rbaPack)} (pre : 0 < p ∧ p < 64)
    (h : ∀ g, PatternBits g p 0 64 help0 → PatternBits g p 64 ((64 / p + 1) * p % 64) help1 →
      RotInvariant g p ((64 / p + 1) * p % 64) (ForIn.toList [1:p]).length st) (g : Nat → Bool)
    (h0 : PatternBits g p 0 64 help0) (h1 : PatternBits g p 64 ((64 / p + 1) * p % 64) help1) :
    RowWords g p p st.2.2 := by
  have hsi := (h g h0 h1).2.2
  rwa [Std.Legacy.Range.length_toList, Nat.sub_add_cancel (by lia)] at hsi

attribute [local irreducible] RotInvariant in
/-- The first `p` words of the row of a prime `p < 64`: for every pattern `g` of period `p` whose
window at `0` is `help0` and whose `diff_shift` bits after it are `help1`, word `a < p` is the
window of `g` at `64 a`. -/
@[spec]
theorem sieve1Rows_spec (p : Nat) (help0 help1 : UInt64) :
    ⦃ 0 < p ∧ p < 64 ⦄ sieve1Rows p help0 help1
    ⦃ fun si ↦ ∀ g, PatternBits g p 0 64 help0 →
        PatternBits g p 64 ((64 / p + 1) * p % 64) help1 → RowWords g p p si ⦄ := by
  vcgen [sieve1Rows] invariants
  | inv1 => fun done _ st ↦ ∀ g, PatternBits g p 0 64 help0 →
      PatternBits g p 64 ((64 / p + 1) * p % 64) help1 →
      RotInvariant g p ((64 / p + 1) * p % 64) done.length st
  all_goals first
    | exact rotInvariant_init ‹_› _ ‹_› ‹_›
    | exact RotInvariant.post ‹_› ‹_› _ ‹_› ‹_›
    | exact RotInvariant.append ‹_› ‹_› ‹_›

/-- One doubling `x | x << i` of the pattern of period `p ∣ i` in the bits below `i < 64`. -/
theorem PatternBits.or_shiftLeft {g : Nat → Bool} {p i : Nat} {x : UInt64} (hpi : p ∣ i)
    (hi : i < 64) (h : PatternBits g p 0 i x) :
    PatternBits g p 0 (min (2 * i) 64) (x ||| x <<< UInt64.ofNat i) := fun t ↦ by
  rw [Nat.zero_add]
  exact UInt64.getLsbD_or_shiftLeft_of_dvd hpi hi (fun u ↦ by rw [h u, Nat.zero_add]) t

/-- The invariant of the loop of `Ratpoints.Sieve.sieveInit1` that doubles the pattern of period
`p` through the word, on the word and the shift. -/
def PatternDoubleInvariant (g : Nat → Bool) (p : Nat) : Std.WP.WhileInvariant (UInt64 × Nat) Prop :=
  .mk fun exit s ↦ p ∣ s.2 ∧ 0 < s.2 ∧ (exit = true → 64 ≤ s.2) ∧
    PatternBits g p 0 (min s.2 64) s.1

theorem patternDoubleInvariant_init {g : Nat → Bool} {p : Nat} {x : UInt64} (hp : 0 < p)
    (h64 : p < 64) (h : PatternBits g p 0 p x) : PatternDoubleInvariant g p false (x, p) :=
  ⟨Nat.dvd_refl p, hp, nofun, by rwa [Nat.min_eq_left (by lia)]⟩

theorem PatternDoubleInvariant.or_shiftLeft {g : Nat → Bool} {p i mb : Nat} {x : UInt64}
    (h : 64 - i = mb ∧ PatternDoubleInvariant g p false (x, i)) (hi : i < 64) :
    64 - i <<< 1 < mb ∧ PatternDoubleInvariant g p false (x ||| x <<< UInt64.ofNat i, i <<< 1) := by
  obtain ⟨rfl, hpi, hi0, -, hx⟩ := h
  dsimp only at hpi hi0 hx
  rw [Nat.min_eq_left (by lia)] at hx
  rw [Nat.shiftLeft_eq, Nat.pow_one, Nat.mul_comm]
  exact ⟨by lia, Nat.dvd_trans hpi (Nat.dvd_mul_left i 2), by lia, nofun, hx.or_shiftLeft hpi hi⟩

theorem PatternDoubleInvariant.exit {g : Nat → Bool} {p i mb : Nat} {x : UInt64}
    (h : 64 - i = mb ∧ PatternDoubleInvariant g p false (x, i)) (hi : ¬i < 64) :
    PatternDoubleInvariant g p true (x, i) :=
  ⟨h.2.1, h.2.2.1, fun _ ↦ by lia, h.2.2.2.2⟩

/-- The pattern of the lanes from `0` on with the inverse of `0 < b < p`, read at the residue of a
numerator, is the row of the residue `b` of the table. -/
theorem lanePattern_mod_eq_admits {t : Entry} {b : Nat} (hb0 : 0 < b) (hbp : b < t.p) (N : Nat) :
    lanePattern t.isFSquare t.p 0 t.inverses[b]! (N % t.p) = t.admits b N := by
  simp only [lanePattern, Entry.admits, Nat.mod_eq_of_lt hbp, Nat.pos_iff_ne_zero.mp hb0,
    ↓reduceIte, Int.toNat_natCast_emod, Nat.zero_add]

/-- The row of words whose first `p` words are the windows of the pattern of the lanes, copied
through all the words, is the closed form of the row of `0 < b < p`, and so is what the builder
stores. -/
theorem toArray_eq_closedRow_of_rowWords {t : Entry} {b : Nat} {ref : EntryRef} {store : RowStore}
    {si si' : Vector UInt64 ((t.p + chunk - 1) * rbaPack)} (hb0 : 0 < b) (hbp : b < t.p)
    (hrows : RowWords (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p t.p si)
    (hrep : ∀ j < (t.p + chunk - 1) * rbaPack, si'[j]! = si[j % t.p]!) :
    (si', store.publish ref b si'.toArray).1.toArray = closedRow t.admits t.p b ∧
      (si', store.publish ref b si'.toArray).2 =
        store.publish ref b (closedRow t.admits t.p b) := by
  have h := (hrows.of_mod (by lia) hrep).toArray_eq_closedRow (lanePattern_mod_eq_admits hb0 hbp)
  exact ⟨h, by rw [← h]⟩

theorem sieveInit1_pre {t : Entry} {b : Nat}
    (pre : 0 < b ∧ b < t.p ∧ t.p < 64 ∧ t.inverses[b]! < t.p) :
    0 < t.p ∧ t.p ≤ 64 ∧ t.inverses[b]! < t.p :=
  ⟨by lia, by lia, pre.2.2.2⟩

theorem sieveInit1_pre_rows {t : Entry} {b : Nat}
    (pre : 0 < b ∧ b < t.p ∧ t.p < 64 ∧ t.inverses[b]! < t.p) : 0 < t.p ∧ t.p < 64 :=
  ⟨by lia, pre.2.2.1⟩

theorem doubleInvariant_init_of_pre {t : Entry} {b : Nat} {x : UInt64}
    (pre : 0 < b ∧ b < t.p ∧ t.p < 64 ∧ t.inverses[b]! < t.p)
    (h : PatternBits (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p 0 t.p x) :
    PatternDoubleInvariant (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p false (x, t.p) :=
  patternDoubleInvariant_init (by lia) pre.2.2.1 h

/-- The pattern shifted right by `64 mod p` holds the `diff_shift` bits after the window at `0`. -/
theorem PatternBits.shiftRight_mod {g : Nat → Bool} {p : Nat} {x : UInt64} (hp : 0 < p)
    (h64 : p < 64) (h : PatternBits g p 0 p x) :
    PatternBits g p 64 ((64 / p + 1) * p % 64) (x >>> UInt64.ofNat (64 % p)) := by
  obtain ⟨-, hsum, -, -⟩ := sieve1_shifts p h64 hp
  intro t
  have := Nat.mod_lt 64 hp
  rw [UInt64.getLsbD_shiftRight_ofNat _ (by lia), h]
  have hm : (0 + (64 % p + t)) % p = (64 + t) % p := by
    rw [Nat.zero_add, Nat.add_mod, Nat.mod_mod, ← Nat.add_mod]
  rw [hm]
  exact congrArg (· && _) (decide_eq_decide.mpr (by lia))

theorem sieveInit1_post {t : Entry} {ref : EntryRef} {b : Nat} {store : RowStore} {x h0 : UInt64}
    {i : Nat} {si si' : Vector UInt64 ((t.p + chunk - 1) * rbaPack)}
    (pre : 0 < b ∧ b < t.p ∧ t.p < 64 ∧ t.inverses[b]! < t.p)
    (hx : PatternBits (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p 0 t.p x)
    (hd : PatternDoubleInvariant (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p true (h0, i))
    (hrows : ∀ g, PatternBits g t.p 0 64 h0 →
      PatternBits g t.p 64 ((64 / t.p + 1) * t.p % 64) (x >>> UInt64.ofNat (64 % t.p)) →
        RowWords g t.p t.p si)
    (hrep : ∀ j < (t.p + chunk - 1) * rbaPack, si'[j]! = si[j % t.p]!) :
    (si', store.publish ref b si'.toArray).1.toArray = closedRow t.admits t.p b ∧
      (si', store.publish ref b si'.toArray).2 =
        store.publish ref b (closedRow t.admits t.p b) := by
  obtain ⟨-, -, hex, hw⟩ := hd
  dsimp only at hex hw
  rw [Nat.min_eq_right (hex rfl)] at hw
  exact toArray_eq_closedRow_of_rowWords pre.1 pre.2.1
    (hrows _ hw (hx.shiftRight_mod (by lia) pre.2.2.1)) hrep

attribute [local irreducible] PatternDoubleInvariant in
open Std.WP Lean.Order in
/-- The row of the residue `0 < b < p` of a prime `p < 64` by `CODE_INIT_SIEVE1` is the closed form
of the row of `b` of its table, for the inverse of `b` below `p`, and the builder stores it into the
table of rows of the entry `ref`. -/
@[spec]
theorem sieveInit1_spec (t : Entry) (ref : EntryRef) (b : Nat) (store : RowStore) :
    ⦃ 0 < b ∧ b < t.p ∧ t.p < 64 ∧ t.inverses[b]! < t.p ⦄ sieveInit1 t ref b store
    ⦃ fun r ↦ r.1.toArray = closedRow t.admits t.p b ∧
        r.2 = store.publish ref b (closedRow t.admits t.p b) ⦄ := by
  vcgen [sieveInit1] invariants
  · PatternDoubleInvariant (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p
  · Variant.ofMeasure fun s : UInt64 × Nat ↦ 64 - s.2
  all_goals try simp only [Variant.evalsTo_ofMeasure, Assertion.NondetFun.evalsTo_pure,
    Variant.evalsBelow_ofMeasure_nat, meet_prop_eq_and, ofProp_prop_eq] at *
  all_goals first
    | exact sieveInit1_pre ‹_›
    | exact sieveInit1_pre_rows ‹_›
    | exact (sieveInit1_pre_rows ‹_›).1
    | exact doubleInvariant_init_of_pre ‹_› ‹_›
    | exact sieveInit1_post ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact PatternDoubleInvariant.or_shiftLeft ‹_› ‹_›
    | exact PatternDoubleInvariant.exit ‹_› ‹_›

/-! ### `CODE_INIT_SIEVE2` -/

/-- The lanes at the bit `x` of the pattern from `0` on are at the bit `0` of the pattern from their
first residue on. -/
theorem LanesAt.rebase {p d x ab ab1 ab2 ab3 : Nat}
    (h : LanesAt p d 0 x ab ab1 ab2 ab3) : LanesAt p d ab 0 ab ab1 ab2 ab3 := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  refine ⟨by simp, ?_, ?_, ?_⟩ <;> rw [Nat.zero_add, Nat.mod_add_mod] <;> congr 1 <;>
    simp only [Nat.add_mul] <;> lia

/-- The lanes at the bit `y` of the pattern from the residue `x d mod p` on are at the bit `x + y`
of the pattern from `0` on. -/
theorem LanesAt.unbase {p d x y ab a0 a1 a2 a3 : Nat} (hab : ab = (0 + x * d) % p)
    (h : LanesAt p d ab y a0 a1 a2 a3) : LanesAt p d 0 (x + y) a0 a1 a2 a3 := by
  obtain ⟨rfl, rfl, rfl, rfl⟩ := h
  subst hab
  refine ⟨?_, ?_, ?_, ?_⟩ <;> rw [Nat.mod_add_mod] <;> congr 1 <;> simp only [Nat.add_mul] <;> lia

/-- The pattern of the lanes from the residue `x d mod p` on is the pattern from `0` on at `x`. -/
theorem PatternBits.unbase {isfs : Array Bool} {p d x m ab : Nat} {w : UInt64}
    (hab : ab = (0 + x * d) % p) (h : PatternBits (lanePattern isfs p ab d) p 0 m w) :
    PatternBits (lanePattern isfs p 0 d) p x m w := by
  intro t
  rw [h t, Nat.zero_add, lanePattern_mod, lanePattern_mod, lanePattern, lanePattern, hab,
    Nat.mod_add_mod, Nat.zero_add, Nat.zero_add, Nat.add_mul]

theorem sieve2Word_pre {t : Entry} {d d4 n ab ab1 ab2 ab3 : Nat}
    (pre : (0 < t.p ∧ d < t.p ∧ d4 = 4 * d % t.p) ∧ LanesAt t.p d 0 (64 * n) ab ab1 ab2 ab3) :
    0 < t.p ∧ (if n < t.p / 64 then 64 else t.p % 64) ≤ 64 :=
  ⟨pre.1.1, by split <;> lia [Nat.mod_lt t.p (show 0 < 64 by decide)]⟩

theorem sieve2Word_rest_pre {t : Entry} {d d4 n ab ab1 ab2 ab3 : Nat}
    (pre : (0 < t.p ∧ d < t.p ∧ d4 = 4 * d % t.p) ∧ LanesAt t.p d 0 (64 * n) ab ab1 ab2 ab3) :
    0 < t.p ∧ (if n < t.p / 64 then 64 else t.p % 64) ≤ 64 ∧ d < t.p :=
  ⟨pre.1.1, (sieve2Word_pre pre).2, pre.1.2.1⟩

theorem sieve2Word_rest_init {t : Entry} {d d4 n ab ab1 ab2 ab3 : Nat}
    {r : UInt64 × Nat × Nat × Nat × Nat × Nat}
    (pre : (0 < t.p ∧ d < t.p ∧ d4 = 4 * d % t.p) ∧ LanesAt t.p d 0 (64 * n) ab ab1 ab2 ab3)
    (h : r.2.1 = 4 * ((if n < t.p / 64 then 64 else t.p % 64) / 4) ∧ ∀ d' < t.p,
      d4 = 4 * d' % t.p → LanesAt t.p d' ab 0 ab ab1 ab2 ab3 →
      FourLanes t.isFSquare t.p d' ab r.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2
        (4 * ((if n < t.p / 64 then 64 else t.p % 64) / 4))) :
    RestInvariant t.isFSquare t.p d ab r.2.1 ([] : List Nat).length (r.1, r.2.2.1) := by
  rw [h.1]
  exact restInvariant_init (h.2 d pre.1.2.1 pre.1.2.2 pre.2.rebase)

/-- The word `n` of the pattern of the row and the lanes after it. -/
theorem sieve2Word_post {t : Entry} {d d4 n ab ab1 ab2 ab3 : Nat}
    {r : UInt64 × Nat × Nat × Nat × Nat × Nat} {st : UInt64 × Nat}
    (pre : (0 < t.p ∧ d < t.p ∧ d4 = 4 * d % t.p) ∧ LanesAt t.p d 0 (64 * n) ab ab1 ab2 ab3)
    (hr : r.2.1 = 4 * ((if n < t.p / 64 then 64 else t.p % 64) / 4) ∧ ∀ d' < t.p,
      d4 = 4 * d' % t.p → LanesAt t.p d' ab 0 ab ab1 ab2 ab3 →
      FourLanes t.isFSquare t.p d' ab r.1 r.2.2.1 r.2.2.2.1 r.2.2.2.2.1 r.2.2.2.2.2
        (4 * ((if n < t.p / 64 then 64 else t.p % 64) / 4)))
    (h : RestInvariant t.isFSquare t.p d ab r.2.1
      (ForIn.toList [r.2.1:if n < t.p / 64 then 64 else t.p % 64]).length st) :
    PatternBits (lanePattern t.isFSquare t.p 0 d) t.p (64 * n)
        (if n < t.p / 64 then 64 else t.p % 64) st.1 ∧
      ((if n < t.p / 64 then 64 else t.p % 64) % 4 = 0 →
        LanesAt t.p d 0 (64 * n + if n < t.p / 64 then 64 else t.p % 64) st.2 r.2.2.2.1
          r.2.2.2.2.1 r.2.2.2.2.2) := by
  generalize hM : (if n < t.p / 64 then 64 else t.p % 64) = M at hr h ⊢
  have hab := pre.2.1
  obtain ⟨hw, hst⟩ := h.post (by rw [hr.1]; lia)
  refine ⟨hw.unbase hab, fun h4 ↦ ?_⟩
  have hM4 : 4 * (M / 4) = M := by lia
  have hl := (hr.2 d pre.1.2.1 pre.1.2.2 pre.2.rebase).1
  rw [hM4] at hl
  exact LanesAt.unbase hab ⟨hst, hl.2⟩

/-- Word `n` of the pattern of the row of a prime `p` in `CODE_INIT_SIEVE2`, from the lanes at the
bit `64 n` of the pattern from `0` on: the bits `64 n, …` of the pattern, 64 of them for
`n < ⌊p / 64⌋` and `p mod 64` for the last word, and after a whole word the lanes at the next. -/
@[spec]
theorem sieve2Word_spec (t : Entry) (d d4 n ab ab1 ab2 ab3 : Nat) :
    ⦃ (0 < t.p ∧ d < t.p ∧ d4 = 4 * d % t.p) ∧ LanesAt t.p d 0 (64 * n) ab ab1 ab2 ab3 ⦄
    sieve2Word t d d4 n ab ab1 ab2 ab3
    ⦃ fun r ↦ PatternBits (lanePattern t.isFSquare t.p 0 d) t.p (64 * n)
        (if n < t.p / 64 then 64 else t.p % 64) r.1 ∧
      ((if n < t.p / 64 then 64 else t.p % 64) % 4 = 0 →
        LanesAt t.p d 0 (64 * n + if n < t.p / 64 then 64 else t.p % 64) r.2.1 r.2.2.1
          r.2.2.2.1 r.2.2.2.2) ⦄ := by
  vcgen [sieve2Word] invariants
  | inv1 _ _ i _ _ _ _ _ => fun done _ st ↦ RestInvariant t.isFSquare t.p d ab i done.length st
  all_goals first
    | exact sieve2Word_pre ‹_›
    | exact sieve2Word_rest_init ‹_› ‹_›
    | exact sieve2Word_post ‹_› ‹_› ‹_›
    | exact RestInvariant.append_initBit (sieve2Word_rest_pre ‹_›) ‹_› ‹_›

/-- The invariant of the loop of `Ratpoints.Sieve.sieve2Pattern` over the words of the pattern
after the words below `c`: word `k < c` holds the bits `64 k, …` of the pattern, 64 of them for
`k < wp` and `ds` for `k = wp`, and the four lanes are at the bit `64 c`. -/
def PatInvariant (g : Nat → Bool) (p d wp ds c : Nat) {n : Nat}
    (st : Vector UInt64 n × Nat × Nat × Nat × Nat) : Prop :=
  (∀ k < c, PatternBits g p (64 * k) (if k < wp then 64 else ds) st.1[k]!) ∧
    (c ≤ wp → LanesAt p d 0 (64 * c) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2)

theorem patInvariant_init {t : Entry} {b n : Nat} (help : Vector UInt64 n)
    (pre : 0 < t.p ∧ t.inverses[b]! < t.p) :
    PatInvariant (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p t.inverses[b]! (t.p / 64)
      (t.p % 64) ([] : List Nat).length (help, 0, (initFourDecl t.p t.inverses[b]!).1,
        (initFourDecl t.p t.inverses[b]!).2.1, (initFourDecl t.p t.inverses[b]!).2.2.1) :=
  ⟨nofun, fun _ ↦ (initFourDecl_lanes pre.2).2⟩

/-- The precondition of the word `cur` of the pattern. -/
theorem PatInvariant.pre {t : Entry} {b n cur : Nat} {pref suff : List Nat}
    {st : Vector UInt64 n × Nat × Nat × Nat × Nat} (pre : 0 < t.p ∧ t.inverses[b]! < t.p)
    (hl : ForIn.toList [0:t.p / 64 + 1] = pref ++ cur :: suff)
    (h : PatInvariant (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p t.inverses[b]!
      (t.p / 64) (t.p % 64) pref.length st) :
    (0 < t.p ∧ t.inverses[b]! < t.p ∧
        (initFourDecl t.p t.inverses[b]!).2.2.2 = 4 * t.inverses[b]! % t.p) ∧
      LanesAt t.p t.inverses[b]! 0 (64 * cur) st.2.1 st.2.2.1 st.2.2.2.1 st.2.2.2.2 := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  exact ⟨⟨pre.1, pre.2, (initFourDecl_lanes pre.2).1⟩, hc ▸ h.2 (by lia)⟩

/-- A step of the loop of the pattern: word `cur` of `help` set to the word of the pattern. -/
theorem PatInvariant.set! {t : Entry} {b n cur : Nat} {pref suff : List Nat}
    {st : Vector UInt64 n × Nat × Nat × Nat × Nat} {r : UInt64 × Nat × Nat × Nat × Nat}
    (hn : t.p / 64 + 1 ≤ n) (hl : ForIn.toList [0:t.p / 64 + 1] = pref ++ cur :: suff)
    (h : PatInvariant (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p t.inverses[b]!
      (t.p / 64) (t.p % 64) pref.length st)
    (hw : PatternBits (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p (64 * cur)
        (if cur < t.p / 64 then 64 else t.p % 64) r.1 ∧
      ((if cur < t.p / 64 then 64 else t.p % 64) % 4 = 0 →
        LanesAt t.p t.inverses[b]! 0 (64 * cur + if cur < t.p / 64 then 64 else t.p % 64) r.2.1
          r.2.2.1 r.2.2.2.1 r.2.2.2.2)) :
    PatInvariant (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p t.inverses[b]! (t.p / 64)
      (t.p % 64) (pref ++ [cur]).length
      (st.1.set! cur r.1, r.2.1, r.2.2.1, r.2.2.2.1, r.2.2.2.2) := by
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  rw [hc] at h
  rw [List.length_append, List.length_singleton, hc]
  refine ⟨fun k hk ↦ ?_, fun hk ↦ ?_⟩
  · rw [Vector.getElem!_set! (by lia)]
    by_cases hkc : cur = k
    · subst hkc
      rw [ite_eq_left rfl]
      exact hw.1
    · rw [ite_eq_right hkc]
      exact h.1 k (by lia)
  · have hw2 := hw.2
    simp only [show cur < t.p / 64 by lia, ↓reduceIte] at hw2
    rw [Nat.mul_add_one]
    exact hw2 (by decide)

theorem PatInvariant.post {g : Nat → Bool} {p d n : Nat}
    {st : Vector UInt64 n × Nat × Nat × Nat × Nat}
    (h : PatInvariant g p d (p / 64) (p % 64) (ForIn.toList [0:p / 64 + 1]).length st) (k : Nat)
    (hk : k < p / 64 + 1) :
    PatternBits g p (64 * k) (if k < p / 64 then 64 else p % 64) st.1[k]! :=
  h.1 k (by simpa using hk)

attribute [local irreducible] PatInvariant in
/-- The pattern of the row of the residue `b` of a prime `p` in `CODE_INIT_SIEVE2`, for the inverse
`d < p` of `b`: word `k ≤ ⌊p / 64⌋` of `help` holds the bits `64 k, …` of the pattern of the lanes
from `0` on, 64 of them for `k < ⌊p / 64⌋` and `p mod 64` for the last. -/
@[spec]
theorem sieve2Pattern_spec (t : Entry) (b : Nat) (help : Vector UInt64 (t.p / 64 + 2)) :
    ⦃ 0 < t.p ∧ t.inverses[b]! < t.p ⦄ sieve2Pattern t b help
    ⦃ fun help' ↦ ∀ k < t.p / 64 + 1, PatternBits (lanePattern t.isFSquare t.p 0 t.inverses[b]!)
        t.p (64 * k) (if k < t.p / 64 then 64 else t.p % 64) help'[k]! ⦄ := by
  vcgen [sieve2Pattern] invariants
  | inv1 => fun done _ st ↦ PatInvariant (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p
      t.inverses[b]! (t.p / 64) (t.p % 64) done.length st
  all_goals first
    | exact patInvariant_init help ‹_›
    | exact PatInvariant.post ‹_› _ ‹_›
    | exact PatInvariant.pre ‹_› ‹_› ‹_›
    | exact PatInvariant.set! (by lia) ‹_› ‹_› ‹_›

/-- The words `help[k]`, `k ≤ ⌊p / 64⌋`, hold the pattern `g` of period `p`: word `k` the bits
`64 k, …`, 64 of them for `k < ⌊p / 64⌋` and `p mod 64` for the last. -/
def PatternWords (g : Nat → Bool) (p : Nat) {n : Nat} (help : Vector UInt64 n) : Prop :=
  ∀ k < p / 64 + 1, PatternBits g p (64 * k) (if k < p / 64 then 64 else p % 64) help[k]!

/-- The ring of `CODE_INIT_SIEVE2` at the bit `s` of the pattern with the cursor `a1 ≤ wp`: word
`a1` holds the `ds` bits from `s` on, and word `(a1 + 1 + k) mod (wp + 1)` the 64 bits from
`s + ds + 64 k` on, for `k < wp`. -/
def RingState (g : Nat → Bool) (p wp ds s a1 : Nat) {n : Nat} (help : Vector UInt64 n) : Prop :=
  a1 ≤ wp ∧ PatternBits g p s ds help[a1]! ∧
    ∀ k < wp, PatternBits g p (s + ds + 64 * k) 64 help[(a1 + 1 + k) % (wp + 1)]!

/-- The word that a step of the ring writes: the 64 bits from `s` on. -/
theorem RingState.out {g : Nat → Bool} {p wp ds s a1 n : Nat} {help : Vector UInt64 n}
    (h : RingState g p wp ds s a1 help) (hwp : 0 < wp) (hds : ds < 64) :
    PatternBits g p s 64
      (help[a1]! ||| help[if a1 = wp then 0 else a1 + 1]! <<< UInt64.ofNat ds) := by
  obtain ⟨ha1, hcur, hrest⟩ := h
  have hnext := hrest 0 hwp
  rw [Nat.mul_zero, Nat.add_zero, ← Nat.ite_eq_add_one_mod_add_one ha1] at hnext
  intro j
  rw [UInt64.toBitVec_or, BitVec.getLsbD_or, UInt64.getLsbD_shiftLeft_ofNat _ hds, hcur, hnext]
  by_cases hj : j < ds
  · simp [hj, show j < 64 by lia, show ¬ds ≤ j by lia]
  · by_cases hj' : j < 64
    · simp [hj, hj', show j - ds < 64 by lia, show ds ≤ j by lia,
        show s + ds + (j - ds) = s + j by lia]
    · simp [hj, hj']

/-- After a step of the ring, the word at the new cursor `t`, shifted right by `64 - ds`, holds the
`ds` bits from `s + 64` on. -/
theorem RingState.cur {g : Nat → Bool} {p wp ds s a1 n t : Nat} {help : Vector UInt64 n}
    (h : RingState g p wp ds s a1 help) (hwp : 0 < wp) (hds0 : 0 < ds) (hds : ds < 64)
    (hn : wp < n) (ht : t = (a1 + 1) % (wp + 1)) (hta : a1 ≠ t) (htle : t ≤ wp) (x : UInt64) :
    PatternBits g p (s + 64) ds
      (((help.set! a1 x).set! t ((help.set! a1 x)[t]! >>> UInt64.ofNat (64 - ds)))[t]!) := by
  intro j
  rw [Vector.getElem!_set!_self (by lia), UInt64.getLsbD_shiftRight_ofNat _ (by lia),
    Vector.getElem!_set!_ne hta]
  have := h.2.2 0 hwp (64 - ds + j)
  rw [Nat.add_zero, Nat.mul_zero, Nat.add_zero, ← ht] at this
  rw [this]
  by_cases hj : j < ds
  · simp [hj, show 64 - ds + j < 64 by lia, show s + ds + (64 - ds + j) = s + 64 + j by lia]
  · simp [hj, show ¬64 - ds + j < 64 by lia]

/-- After a step of the ring, the words after the new cursor hold the 64 bits from
`s + 64 + ds + 64 k` on: the old ones moved up by one, the last the word written. -/
theorem RingState.rest {g : Nat → Bool} {p wp ds s a1 n t : Nat} {help : Vector UInt64 n}
    {x : UInt64} (h : RingState g p wp ds s a1 help) (hp : p = 64 * wp + ds) (hn : wp < n)
    (ht : t = (a1 + 1) % (wp + 1)) (hta : a1 ≠ t) (hout : PatternBits g p s 64 x) :
    ∀ k < wp, PatternBits g p (s + 64 + ds + 64 * k) 64
      (((help.set! a1 x).set! t ((help.set! a1 x)[t]! >>> UInt64.ofNat (64 - ds)))[(t + 1 + k) %
        (wp + 1)]!) := by
  intro k hk j
  have ha1 := h.1
  have hidx : (t + 1 + k) % (wp + 1) = (a1 + (k + 2)) % (wp + 1) := by
    rw [ht, Nat.add_assoc, Nat.mod_add_mod]
    exact congrArg (· % (wp + 1)) (by lia)
  rw [Nat.mod_eq_ite_of_lt_two_mul (a := a1 + 1) (q := wp + 1) (by lia)] at ht
  rw [Nat.mod_eq_ite_of_lt_two_mul (a := a1 + (k + 2)) (q := wp + 1) (by lia)] at hidx
  rw [hidx]
  by_cases hk' : k + 1 < wp
  · rw [Vector.getElem!_set!_ne (by split <;> lia), Vector.getElem!_set!_ne (by split <;> lia)]
    have := h.2.2 (k + 1) hk' j
    rw [show a1 + 1 + (k + 1) = a1 + (k + 2) by lia,
      Nat.mod_eq_ite_of_lt_two_mul (a := a1 + (k + 2)) (q := wp + 1) (by lia)] at this
    rw [this, show s + ds + 64 * (k + 1) + j = s + 64 + ds + 64 * k + j by lia]
  · simp only [show wp + 1 ≤ a1 + (k + 2) by lia, ↓reduceIte]
    rw [show a1 + (k + 2) - (wp + 1) = a1 by lia, Vector.getElem!_set!_ne (Ne.symm hta),
      Vector.getElem!_set!_self (by lia), hout j,
      show s + 64 + ds + 64 * k + j = s + j + p * 1 by lia, Nat.add_mul_mod_self_left]

/-- A step of the ring: `help[a1] |= help[t] << ds`, the cursor moved on to `t`, and
`help[t] >>= 64 - ds`, for `p = 64 wp + ds`, `0 < wp`, `0 < ds < 64`: the ring at `s + 64`. -/
theorem RingState.rotate {g : Nat → Bool} {p wp ds s a1 n : Nat} {help : Vector UInt64 n}
    (h : RingState g p wp ds s a1 help) (hp : p = 64 * wp + ds) (hwp : 0 < wp) (hds0 : 0 < ds)
    (hds : ds < 64) (hn : wp < n) :
    RingState g p wp ds (s + 64) (if a1 = wp then 0 else a1 + 1)
      ((help.set! a1 (help[a1]! ||| help[if a1 = wp then 0 else a1 + 1]! <<< UInt64.ofNat ds)).set!
        (if a1 = wp then 0 else a1 + 1)
        ((help.set! a1 (help[a1]! ||| help[if a1 = wp then 0 else a1 + 1]! <<<
          UInt64.ofNat ds))[if a1 = wp then 0 else a1 + 1]! >>> UInt64.ofNat (64 - ds))) := by
  have hout := h.out hwp hds
  have ha1 := h.1
  have ht := Nat.ite_eq_add_one_mod_add_one ha1
  generalize hT : (if a1 = wp then 0 else a1 + 1) = t at ht hout ⊢
  have htle : t ≤ wp := by rw [← hT]; split <;> lia
  have hta : a1 ≠ t := by rw [← hT]; split <;> lia
  exact ⟨htle, h.cur hwp hds0 hds hn ht hta htle _, h.rest hp hn ht hta hout⟩

/-- The shifts of `CODE_INIT_SIEVE2` for `64 ≤ p` with `p mod 64 ≠ 0`. -/
theorem sieve2_shifts {p : Nat} (pre : 64 ≤ p ∧ p % 64 ≠ 0) :
    p = 64 * (p / 64) + p % 64 ∧ 0 < p / 64 ∧ 0 < p % 64 ∧ p % 64 < 64 :=
  ⟨(Nat.div_add_mod p 64).symm, by lia, by lia, Nat.mod_lt _ (by decide)⟩

theorem rowWords_nil {p n : Nat} (si : Vector UInt64 n) (g : Nat → Bool) :
    RowWords g p ([] : List Nat).length si :=
  nofun

/-- A copy of word `cur < ⌊p / 64⌋` of the pattern into the row. -/
theorem RowWords.copy {p cur m : Nat} {pref suff : List Nat}
    {si : Vector UInt64 ((p + chunk - 1) * rbaPack)} {help : Vector UInt64 m}
    (pre : 64 ≤ p ∧ p % 64 ≠ 0) (hl : ForIn.toList [0:p / 64] = pref ++ cur :: suff)
    (h : ∀ g, PatternWords g p help → RowWords g p pref.length si) :
    ∀ g, PatternWords g p help → RowWords g p (pref ++ [cur]).length (si.set! cur help[cur]!) := by
  intro g hg
  have hc := Std.Legacy.Range.length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hw := hg cur (by lia)
  simp only [hcl, ↓reduceIte] at hw
  have hn : p ≤ (p + chunk - 1) * rbaPack :=
    Nat.le_trans (Nat.le_mul_of_pos_right p rbaPack_pos)
      (Nat.mul_le_mul_right _ (by lia [chunk_pos]))
  rw [List.length_append, List.length_singleton, hc]
  exact (hc ▸ h g hg).set!_self (by lia) hw

/-- The start of the ring: the cursor at `wp`, the ring at the bit `64 wp`, the first `wp` words of
the row copied. -/
theorem ringState_init {p m : Nat} {help : Vector UInt64 m}
    {si : Vector UInt64 ((p + chunk - 1) * rbaPack)}
    (h : ∀ g, PatternWords g p help → RowWords g p (ForIn.toList [0:p / 64]).length si)
    (g : Nat → Bool) (hg : PatternWords g p help) :
    RingState g p (p / 64) (p % 64) (64 * (p / 64 + ([] : List Nat).length)) (p / 64) help ∧
      RowWords g p (p / 64 + ([] : List Nat).length) si := by
  have hd := Nat.div_add_mod p 64
  have hsi := h g hg
  simp only [Std.Legacy.Range.length_toList, Nat.sub_zero] at hsi
  refine ⟨⟨Nat.le_refl _, ?_, fun k hk ↦ ?_⟩, hsi⟩
  · simpa using hg (p / 64) (by lia)
  · rw [show (p / 64 + 1 + k) % (p / 64 + 1) = k by
      rw [Nat.add_comm, Nat.add_mod_right, Nat.mod_eq_of_lt (by lia)]]
    have := hg k (by lia)
    simp only [hk, ↓reduceIte] at this
    refine this.congr_left ?_
    rw [List.length_nil, Nat.add_zero,
      show 64 * (p / 64) + p % 64 + 64 * k = 64 * k + p * 1 by lia, Nat.add_mul_mod_self_left]

/-- A step of the loop of the ring, in the shape of the verification condition. -/
theorem RingState.append {p cur m : Nat} {pref suff : List Nat} {help0 : Vector UInt64 m}
    {help : Vector UInt64 m} {si : Vector UInt64 ((p + chunk - 1) * rbaPack)} {a1 : Nat}
    (pre : 64 ≤ p ∧ p % 64 ≠ 0) (hm : p / 64 < m)
    (hl : ForIn.toList [p / 64:p] = pref ++ cur :: suff)
    (h : ∀ g, PatternWords g p help0 →
      RingState g p (p / 64) (p % 64) (64 * (p / 64 + pref.length)) a1 help ∧
        RowWords g p (p / 64 + pref.length) si) :
    ∀ g, PatternWords g p help0 →
    RingState g p (p / 64) (p % 64) (64 * (p / 64 + (pref ++ [cur]).length))
      (if a1 = p / 64 then 0 else a1 + 1)
      ((help.set! a1 (help[a1]! ||| help[if a1 = p / 64 then 0 else a1 + 1]! <<<
          UInt64.ofNat (p % 64))).set! (if a1 = p / 64 then 0 else a1 + 1)
        ((help.set! a1 (help[a1]! ||| help[if a1 = p / 64 then 0 else a1 + 1]! <<<
          UInt64.ofNat (p % 64)))[if a1 = p / 64 then 0 else a1 + 1]! >>>
            UInt64.ofNat (64 - p % 64))) ∧
      RowWords g p (p / 64 + (pref ++ [cur]).length)
        (si.set! cur (help.set! a1 (help[a1]! ||| help[if a1 = p / 64 then 0 else a1 + 1]! <<<
          UInt64.ofNat (p % 64)))[a1]!) := by
  intro g hg
  obtain ⟨hp, hwp, hds0, hds⟩ := sieve2_shifts pre
  have hc := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  have hcl := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hn : p ≤ (p + chunk - 1) * rbaPack :=
    Nat.le_trans (Nat.le_mul_of_pos_right p rbaPack_pos)
      (Nat.mul_le_mul_right _ (by lia [chunk_pos]))
  obtain ⟨hr, hsi⟩ := h g hg
  subst hc
  rw [List.length_append, List.length_singleton, ← Nat.add_assoc, Nat.mul_add_one]
  refine ⟨hr.rotate hp hwp hds0 hds hm, ?_⟩
  rw [Vector.getElem!_set!_self (by lia [hr.1])]
  exact hsi.set!_self (by lia) (hr.out hwp hds)

theorem RingState.post {p m : Nat} {help0 help : Vector UInt64 m}
    {si : Vector UInt64 ((p + chunk - 1) * rbaPack)} {a1 : Nat} (pre : 64 ≤ p ∧ p % 64 ≠ 0)
    (h : ∀ g, PatternWords g p help0 →
      RingState g p (p / 64) (p % 64) (64 * (p / 64 + (ForIn.toList [p / 64:p]).length)) a1 help ∧
        RowWords g p (p / 64 + (ForIn.toList [p / 64:p]).length) si)
    (g : Nat → Bool) (hg : PatternWords g p help0) : RowWords g p p si := by
  have hsi := (h g hg).2
  rwa [Std.Legacy.Range.length_toList, Nat.add_sub_cancel' (by lia)] at hsi

attribute [local irreducible] RingState PatternWords in
/-- The first `p` words of the row of a prime `p > 64` with `p mod 64 ≠ 0` in `CODE_INIT_SIEVE2`:
for every pattern `g` of period `p` held in the words `help` (`Ratpoints.Sieve.PatternWords`),
word `a < p` of the row is the window of `g` at `64 a`. -/
@[spec]
theorem sieve2Rows_spec (p : Nat) (help : Vector UInt64 (p / 64 + 2)) :
    ⦃ 64 ≤ p ∧ p % 64 ≠ 0 ⦄ sieve2Rows p help
    ⦃ fun si ↦ ∀ g, PatternWords g p help → RowWords g p p si ⦄ := by
  vcgen [sieve2Rows] invariants
  | inv1 => fun done _ si ↦ ∀ g, PatternWords g p help → RowWords g p done.length si
  | inv2 => fun done _ st ↦ ∀ g, PatternWords g p help →
      RingState g p (p / 64) (p % 64) (64 * (p / 64 + done.length)) st.2.2 st.1 ∧
        RowWords g p (p / 64 + done.length) st.2.1
  all_goals first
    | exact rowWords_nil _ _
    | exact ringState_init ‹_› _ ‹_›
    | exact RingState.post ‹_› ‹_› _ ‹_›
    | exact RingState.append ‹_› (by lia) ‹_› ‹_›
    | exact RowWords.copy ‹_› ‹_› ‹_›

theorem sieveInit2_pre_pattern {t : Entry} {b : Nat}
    (pre : 0 < b ∧ b < t.p ∧ 64 ≤ t.p ∧ t.p % 64 ≠ 0 ∧ t.inverses[b]! < t.p) :
    0 < t.p ∧ t.inverses[b]! < t.p :=
  ⟨by lia, pre.2.2.2.2⟩

theorem sieveInit2_pre_rows {t : Entry} {b : Nat}
    (pre : 0 < b ∧ b < t.p ∧ 64 ≤ t.p ∧ t.p % 64 ≠ 0 ∧ t.inverses[b]! < t.p) :
    64 ≤ t.p ∧ t.p % 64 ≠ 0 :=
  ⟨pre.2.2.1, pre.2.2.2.1⟩

theorem sieveInit2_post {t : Entry} {ref : EntryRef} {b : Nat} {store : RowStore}
    {help : Vector UInt64 (t.p / 64 + 2)} {si si' : Vector UInt64 ((t.p + chunk - 1) * rbaPack)}
    (pre : 0 < b ∧ b < t.p ∧ 64 ≤ t.p ∧ t.p % 64 ≠ 0 ∧ t.inverses[b]! < t.p)
    (hpat : PatternWords (lanePattern t.isFSquare t.p 0 t.inverses[b]!) t.p help)
    (hrows : ∀ g, PatternWords g t.p help → RowWords g t.p t.p si)
    (hrep : ∀ j < (t.p + chunk - 1) * rbaPack, si'[j]! = si[j % t.p]!) :
    (si', store.publish ref b si'.toArray).1.toArray = closedRow t.admits t.p b ∧
      (si', store.publish ref b si'.toArray).2 = store.publish ref b (closedRow t.admits t.p b) :=
  toArray_eq_closedRow_of_rowWords pre.1 pre.2.1 (hrows _ hpat) hrep

/-- The row of the residue `0 < b < p` of a prime `p ≥ 64` with `p mod 64 ≠ 0` by `CODE_INIT_SIEVE2`
is the closed form of the row of `b` of its table, for the inverse of `b` below `p`, and the builder
stores it into the table of rows of the entry `ref`. The words `help` that the builder clears from
the last are overwritten by the pattern before they are read. -/
@[spec]
theorem sieveInit2_spec (t : Entry) (ref : EntryRef) (b : Nat) (store : RowStore) :
    ⦃ 0 < b ∧ b < t.p ∧ 64 ≤ t.p ∧ t.p % 64 ≠ 0 ∧ t.inverses[b]! < t.p ⦄ sieveInit2 t ref b store
    ⦃ fun r ↦ r.1.toArray = closedRow t.admits t.p b ∧
        r.2 = store.publish ref b (closedRow t.admits t.p b) ⦄ := by
  vcgen [sieveInit2] invariants
  | inv1 => fun _ _ _ ↦ True
  all_goals first
    | exact sieveInit2_pre_pattern ‹_›
    | exact sieveInit2_pre_rows ‹_›
    | exact (sieveInit2_pre_pattern ‹_›).1
    | exact sieveInit2_post ‹_› ‹_› ‹_› ‹_›

end Sieve

end Ratpoints

end
