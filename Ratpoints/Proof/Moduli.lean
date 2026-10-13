/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Basic
public import Ratpoints.Model.Sieve
public import Ratpoints.Spec.Basic
public import Std.WP

import Mathlib.Data.List.GetD
import Ratpoints.Mathlib.Data.ZMod.Basic
import Ratpoints.Proof.Bits
import Ratpoints.Proof.Params
import Ratpoints.Proof.Tables
import Std.Tactic.Do

/-!
# Prime powers and products as moduli

The tables of a prime power `p ^ e` are those of `examine_power` (`Ratpoints.Sieve.examinePower`),
whose inverses come from the extended Euclidean algorithm (`Ratpoints.Sieve.modinv`) in a loop over
the residues (`Ratpoints.Sieve.examinePower_spec`). The tables of a prime power compute what they
claim, and its rows let every point through (`Ratpoints.Sieve.admits_run_examinePower_of_sq_eq`):
for `p ∤ b`, since `f(a / b)` is a square modulo `p ^ e`, and for `p ∣ b`, since then `p ∤ a` and
the reversed polynomial takes a square value at `b / a`, both from the lemmas of
`Ratpoints.Proof.Tables` for any commutative ring, here `ZMod (p ^ e)`. The values of
`examine_power` stay in the range of their C types for the prime powers below
`Ratpoints.maxPrimeEven`: the cofactors of the extended Euclidean algorithm
(`Ratpoints.Sieve.ModinvInvariant.natAbs_add_mul_le`), the steps of Horner's rule and the squares
(`Ratpoints.mul_add_lt_two_pow_64_of_lt_maxPrimeEven`,
`Ratpoints.mul_self_lt_two_pow_63_of_lt_maxPrimeEven`), and the inverses
(`Ratpoints.Sieve.getElem!_inv_run_examinePower_lt_two_pow_16`). The row of a factor of a modulus,
a prime or a prime power whose modulus divides `m`, reads the residues modulo `m` as those of the
numbers (`Ratpoints.Sieve.Entry.admits_mod_of_dvd`, `Ratpoints.Sieve.Power.admits_mod_of_dvd`), so
that the sieve entry of `m` (`Ratpoints.Sieve.SieveEntry`) lets every point through when each of its
factors does, without the Chinese remainder theorem.

## Main definitions

* `Ratpoints.Sieve.ModinvInvariant`, `Ratpoints.Sieve.ExaminePowerInvariant`: the invariants of the
  loop of `Ratpoints.Sieve.modinv` and of the loop over the residues of
  `Ratpoints.Sieve.examinePower`.

## Main statements

* `Ratpoints.Sieve.modinv_spec`: for `x` prime to `m > 1`, `Ratpoints.Sieve.modinv` gives the
  inverse of `x` modulo `m`, below `m`; `Ratpoints.Sieve.ModinvInvariant.natAbs_add_mul_le`: its
  cofactors stay between `-m` and `m`.
* `Ratpoints.Sieve.examinePower_spec`, with its plain forms
  `Ratpoints.Sieve.getElem!_inv_run_examinePower_lt` and
  `Ratpoints.Sieve.mul_getElem!_inv_run_examinePower_mod`: the inverses of a prime power are below
  it and hold the inverses of the units;
  `Ratpoints.Sieve.getElem!_fsq_run_examinePower_of_isSquare`,
  `Ratpoints.Sieve.getElem!_gsq_run_examinePower_of_isSquare`: its tables mark the residues at which
  `f`, or the reversed polynomial at a multiple of `p`, takes a square value.
* `Ratpoints.Sieve.getElem!_inv_run_examinePower_lt_two_pow_16`: the inverses of a prime power below
  `Ratpoints.maxPrimeEven` are below `2 ^ 16`, the range of their C type.
* `Ratpoints.Sieve.admits_run_examinePower_of_sq_eq`: the rows of a prime power let every point
  through.
* `Ratpoints.Sieve.Entry.admits_mod_of_dvd`, `Ratpoints.Sieve.Power.admits_mod_of_dvd`: the row of
  a prime or a prime power reads the residues modulo a multiple of its modulus as those of the
  numbers.

## Implementation notes

The contracts of `Ratpoints.Sieve.modinv` and `Ratpoints.Sieve.examinePower` are proved with
`vcgen`, the program logic of Lean core, with loop invariants that are named definitions, in a file
with Mathlib, next to the soundness of the rows that they serve.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Sieve

/-! ### The inverse modulo `m` by the extended Euclidean algorithm -/

/-- The invariant of the loop of `Ratpoints.Sieve.modinv` for `x` modulo `m`, on the remainders
`r₀, r₁` and the cofactors `s₀, s₁`: `rᵢ ≡ sᵢ x (mod m)`, `gcd(r₀, r₁) = gcd(m, x)`, `r₀ > 0`,
the cofactors are of opposite signs or one of them is `0`, `|s₀| r₁ + |s₁| r₀ = m`, `|s₀| ≤ m`, and
`r₁ = 0` at the exit. -/
def ModinvInvariant (x m : ℕ) : Std.WP.WhileInvariant (ℕ × ℕ × ℤ × ℤ) Prop :=
  .mk fun exit s ↦ ((s.1 : ZMod m) = s.2.2.1 * x ∧ (s.2.1 : ZMod m) = s.2.2.2 * x) ∧
    Nat.gcd s.1 s.2.1 = Nat.gcd m x ∧ 0 < s.1 ∧ s.2.2.1 * s.2.2.2 ≤ 0 ∧
    s.2.2.1.natAbs * s.2.1 + s.2.2.2.natAbs * s.1 = m ∧ s.2.2.1.natAbs ≤ m ∧
    (exit = true → s.2.1 = 0)

theorem modinvInvariant_zero {x m : ℕ} (hm : 0 < m) : ModinvInvariant x m false (m, x % m, 0, 1) :=
  ⟨⟨by simp, by simp⟩, by rw [Nat.gcd_comm, ← Nat.gcd_rec], hm, by simp, by simp, by simp, nofun⟩

/-- The step of the loop of `Ratpoints.Sieve.modinv`, with the measure `r₁`. -/
theorem ModinvInvariant.sub_lt_and_sub_mul {x m r₀ r₁ : ℕ} {s₀ s₁ : ℤ}
    (h : ModinvInvariant x m false (r₀, r₁, s₀, s₁)) (hr : ¬r₁ = 0) :
    r₀ - r₀ / r₁ * r₁ < r₁ ∧
      ModinvInvariant x m false (r₁, r₀ - r₀ / r₁ * r₁, s₁, s₀ - (r₀ / r₁ : ℕ) * s₁) := by
  obtain ⟨⟨h0, h1⟩, hg, hr0, hs, hid, hle, -⟩ := h
  dsimp only at h0 h1 hg hr0 hs hid hle
  have hq : r₀ / r₁ * r₁ ≤ r₀ := Nat.div_mul_le_self r₀ r₁
  have hmod : r₀ - r₀ / r₁ * r₁ = r₀ % r₁ := by rw [Nat.mod_eq_sub_mul_div, Nat.mul_comm]
  refine ⟨hmod ▸ Nat.mod_lt _ (by lia), ⟨h1, ?_⟩, ?_, Nat.pos_of_ne_zero hr, ?_, ?_, ?_, nofun⟩
  · dsimp only
    rw [Nat.cast_sub hq, Nat.cast_mul, Int.cast_sub, Int.cast_mul, Int.cast_natCast, h0, h1]
    ring
  · dsimp only
    rw [hmod, ← hg, Nat.gcd_comm r₀ r₁, Nat.gcd_rec r₁ r₀, Nat.gcd_comm]
  · dsimp only
    nlinarith [mul_self_nonneg s₁]
  · dsimp only
    rw [Int.natAbs_sub_mul_of_mul_nonpos hs]
    zify [hq] at hid ⊢
    nlinarith
  · have : s₁.natAbs * 1 ≤ s₁.natAbs * r₀ := Nat.mul_le_mul_left _ hr0
    dsimp only
    lia

/-- The range obligation of the cofactors of `modinv` (`find_points.c:2246-2249`): in each step of
the loop, the product `q s₁` and the new cofactor `s₀ - q s₁`, `q = ⌊r₀ / r₁⌋`, lie between `-m` and
`m`, as `s₀` and `s₁` do, so that the `long`s do not overflow for `m < 2 ^ 63`. -/
theorem ModinvInvariant.natAbs_add_mul_le {x m r₀ r₁ : ℕ} {s₀ s₁ : ℤ}
    (h : ModinvInvariant x m false (r₀, r₁, s₀, s₁)) (hr : ¬r₁ = 0) :
    s₁.natAbs ≤ m ∧ s₀.natAbs + r₀ / r₁ * s₁.natAbs ≤ m := by
  have h' := (h.sub_lt_and_sub_mul hr).2
  obtain ⟨-, -, -, hs, -, -, -⟩ := h
  obtain ⟨-, -, -, -, hid, hle, -⟩ := h'
  dsimp only at hs hid hle
  rw [Int.natAbs_sub_mul_of_mul_nonpos hs] at hid
  have := Nat.mul_le_mul_left (s₀.natAbs + r₀ / r₁ * s₁.natAbs) (Nat.one_le_iff_ne_zero.mpr hr)
  exact ⟨hle, by lia⟩

theorem ModinvInvariant.exit {x m : ℕ} {s : ℕ × ℕ × ℤ × ℤ} (h : ModinvInvariant x m false s)
    (hr : ¬¬s.2.1 = 0) : ModinvInvariant x m true s :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, fun _ ↦ not_not.mp hr⟩

-- The cofactor `s₀` of the inverse of a unit modulo `m > 1`, with `m` added when it is negative.
private theorem toNat_ite_lt_and_mul_mod {x m : ℕ} {s₀ : ℤ} (hm : 1 < m)
    (h : ((1 : ℕ) : ZMod m) = s₀ * x) (hle : s₀.natAbs ≤ m) :
    (if s₀ < 0 then s₀ + m else s₀).toNat < m ∧
      x * (if s₀ < 0 then s₀ + m else s₀).toNat % m = 1 := by
  have hr : 0 ≤ (if s₀ < 0 then s₀ + m else s₀) ∧ (if s₀ < 0 then s₀ + m else s₀) ≤ m := by
    split <;> lia
  have hcast : (((if s₀ < 0 then s₀ + m else s₀).toNat : ℕ) : ZMod m) = s₀ := by
    rw [ZMod.natCast_toNat _ hr.1]
    split <;> simp
  have hmul : ((x * (if s₀ < 0 then s₀ + m else s₀).toNat : ℕ) : ZMod m) = ((1 : ℕ) : ZMod m) := by
    rw [Nat.cast_mul, hcast, h, mul_comm]
  refine ⟨lt_of_le_of_ne (by lia) fun he ↦ ?_, ?_⟩
  · rw [he, ZMod.natCast_self] at hcast
    rw [← hcast, zero_mul, ← Nat.cast_zero, ZMod.natCast_eq_natCast_iff', Nat.zero_mod,
      Nat.mod_eq_of_lt hm] at h
    exact one_ne_zero h
  · rwa [ZMod.natCast_eq_natCast_iff', Nat.mod_eq_of_lt hm] at hmul

/-- The exit of the loop of `Ratpoints.Sieve.modinv` for `x` prime to `m > 1`: `r₀ = gcd(m, x) = 1`,
so that `s₀ x ≡ 1 (mod m)`, and `|s₀| ≤ m`. -/
theorem ModinvInvariant.post {x m r₀ r₁ : ℕ} {s₀ s₁ : ℤ}
    (h : ModinvInvariant x m true (r₀, r₁, s₀, s₁)) (hm : 1 < m) (hx : Nat.Coprime x m) :
    (if s₀ < 0 then s₀ + m else s₀).toNat < m ∧
      x * (if s₀ < 0 then s₀ + m else s₀).toNat % m = 1 := by
  obtain ⟨⟨h0, -⟩, hg, -, -, -, hle, hr1⟩ := h
  dsimp only at h0 hg hle hr1
  rw [hr1 rfl, Nat.gcd_zero_right, Nat.gcd_comm, hx.gcd_eq_one] at hg
  exact toNat_ite_lt_and_mul_mod hm (hg ▸ h0) hle

attribute [local irreducible] ModinvInvariant in
/-- The contract of `Ratpoints.Sieve.modinv`: for `x` prime to `m > 1`, the extended Euclidean
algorithm gives the inverse of `x` modulo `m`, below `m`. The loop ends, since `r₁` drops; the
cofactors stay between `-m` and `m` (`Ratpoints.Sieve.ModinvInvariant.natAbs_add_mul_le`). -/
@[spec]
theorem modinv_spec (x m : ℕ) :
    ⦃ 1 < m ∧ Nat.Coprime x m ⦄ modinv x m ⦃ fun r ↦ r < m ∧ x * r % m = 1 ⦄ := by
  vcgen [modinv] invariants
  · ModinvInvariant x m
  · .ofMeasure fun s : ℕ × ℕ × ℤ × ℤ ↦ s.2.1
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals try obtain ⟨rfl, _⟩ := ‹_ = _ ∧ ModinvInvariant _ _ false _›
  all_goals obtain ⟨hm, hx⟩ := ‹1 < m ∧ _›
  all_goals first
    | exact modinvInvariant_zero (by lia)
    | exact ModinvInvariant.post ‹_› hm hx
    | exact ModinvInvariant.sub_lt_and_sub_mul ‹_› ‹_›
    | exact ModinvInvariant.exit ‹_› ‹_›

/-! ### The tables of a prime power -/

/-- The table of the squares modulo `m` that a fold over the residues marks holds every residue
that is a square in `ZMod m`. -/
theorem getElem!_foldl_set!_mul_self_mod_of_isSquare {m v : ℕ} (hv : v < m)
    (h : IsSquare (v : ZMod m)) :
    ((List.range m).foldl (fun s x ↦ s.set! (x * x % m) true) (Array.replicate m false))[v]! =
      true := by
  obtain ⟨s, hs, rfl⟩ := ZMod.exists_eq_mul_self_mod_of_isSquare hv h
  simp only [Array.set!_eq_setIfInBounds]
  rw [Array.getElem!_foldl_setIfInBounds _ (fun x ↦ x * x % m) _ (by simpa using hv)]
  simpa using .inr ⟨s, hs, rfl⟩

/-- The path through `long`s, with the helper `mod` of the C code, and the path through GMP
integers give the same tables of a prime power. -/
theorem examinePower_eq_examinePower_false (c : List ℤ) (d p e : ℕ) (u : Bool) :
    examinePower c d p e u = examinePower c d p e false := by
  simp [examinePower, modLong_eq_emod]

@[simp]
theorem p_run_examinePower (c : List ℤ) (d p e : ℕ) (u : Bool) :
    (Id.run (examinePower c d p e u)).p = p :=
  rfl

@[simp]
theorem m_run_examinePower (c : List ℤ) (d p e : ℕ) (u : Bool) :
    (Id.run (examinePower c d p e u)).m = p ^ e :=
  rfl

/-- Entry `x` of the table `fsq` of the prime power `m = p ^ e` is set when `f(x)` is a square
modulo `m`. -/
theorem getElem!_fsq_run_examinePower_of_isSquare {c : List ℤ} {d p e : ℕ} (u : Bool) {x : ℕ}
    (hx : x < p ^ e)
    (h : IsSquare (∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod (p ^ e)) * x ^ k)) :
    (Id.run (examinePower c d p e u)).fsq[x]! = true := by
  have : NeZero (p ^ e) := ⟨by lia⟩
  rw [examinePower_eq_examinePower_false]
  simp only [examinePower, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
    Array.getElem!_map_range _ hx]
  rw [← natCast_evalMod_map_range c d x] at h
  exact getElem!_foldl_set!_mul_self_mod_of_isSquare (evalMod_lt _ (by lia) _) h

/-- Horner's rule modulo `m` on the reversed list of coefficients: the value at `x` of the
polynomial whose coefficient of `x ^ (n - 1 - k)` is entry `k` of the list of length `n`. -/
theorem natCast_evalMod_reverse (cs : List ℕ) (m x : ℕ) :
    (evalMod cs.reverse m x : ZMod m) =
      ∑ k ∈ Finset.range cs.length, (cs.getD k 0 : ZMod m) * x ^ (cs.length - 1 - k) := by
  rw [natCast_evalMod, List.length_reverse, ← Finset.sum_range_reflect]
  refine Finset.sum_congr rfl fun k hk ↦ ?_
  have hk := Finset.mem_range.mp hk
  rw [List.getD_reverse _ (by lia), Nat.sub_sub_self (by lia)]

-- The coefficients of `examinePower`, with `c_D = 0` for odd `d`, reversed: Horner's rule gives the
-- value `∑ cₖ x ^ (D - k)` of the reversed polynomial modulo `m`.
private theorem natCast_evalMod_reverse_ite (c : List ℤ) (d : ℕ) {m : ℕ} [NeZero m] (x : ℕ) :
    (evalMod (if d % 2 = 1 then
        (List.range (d + 1)).map (fun k ↦ (c.getD k 0 % (m : ℤ)).toNat) ++ [0] else
        (List.range (d + 1)).map fun k ↦ (c.getD k 0 % (m : ℤ)).toNat).reverse m x : ZMod m) =
      ∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod m) * x ^ (d + d % 2 - k) := by
  have hc (k : ℕ) (hk : k < d + 1) :
      ((((List.range (d + 1)).map fun k ↦ (c.getD k 0 % (m : ℤ)).toNat).getD k 0 : ℕ) : ZMod m) =
        c.getD k 0 := by
    rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hk, Option.map_some,
      Option.getD_some, ZMod.natCast_toNat_emod]
  split_ifs with hd
  · rw [natCast_evalMod_reverse, List.length_append, List.length_map, List.length_range,
      List.length_singleton, Finset.sum_range_succ, List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero, Nat.cast_zero,
      zero_mul, add_zero]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [List.getD_append _ _ _ _ (by simpa using hk), hc k (Finset.mem_range.mp hk), hd,
      Nat.add_sub_cancel]
  · rw [natCast_evalMod_reverse, List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun k hk ↦ ?_
    rw [hc k (Finset.mem_range.mp hk), show d + d % 2 = d + 1 - 1 by lia]

/-- Entry `t` of the table `gsq` of the prime power `m = p ^ e`, for `p ∣ t`, is set when the
reversed polynomial `∑ cₖ t ^ (D - k)` of the even degree `D = d + d % 2` takes a square value
modulo `m` at `t`. -/
theorem getElem!_gsq_run_examinePower_of_isSquare {c : List ℤ} {d p e : ℕ} (u : Bool) {t : ℕ}
    (ht : t < p ^ e) (htp : t % p = 0)
    (h : IsSquare (∑ k ∈ Finset.range (d + 1),
      (c.getD k 0 : ZMod (p ^ e)) * t ^ (d + d % 2 - k))) :
    (Id.run (examinePower c d p e u)).gsq[t]! = true := by
  have : NeZero (p ^ e) := ⟨by lia⟩
  rw [examinePower_eq_examinePower_false]
  simp only [examinePower, Bool.false_eq_true, ↓reduceIte, Id.run_bind, Id.run_pure,
    Array.getElem!_map_range _ ht, htp, beq_self_eq_true, Bool.true_and]
  rw [← natCast_evalMod_reverse_ite c d t] at h
  exact getElem!_foldl_set!_mul_self_mod_of_isSquare (evalMod_lt _ (by lia) _) h

/-- The invariant of the loop of `Ratpoints.Sieve.examinePower` over the residues `1, …, k` modulo
`m`, on the inverses `inv`: `k + 1` entries, each below `m`, that of a residue prime to `p` its
inverse modulo `m`. -/
def ExaminePowerInvariant (p m k : ℕ) (inv : Array ℕ) : Prop :=
  inv.size = k + 1 ∧ ∀ x < inv.size, inv[x]! < m ∧ (x % p ≠ 0 → x * inv[x]! % m = 1)

theorem examinePowerInvariant_zero (p : ℕ) {m : ℕ} (hm : 0 < m) :
    ExaminePowerInvariant p m 0 #[0] :=
  ⟨rfl, fun x hx ↦ by
    obtain rfl : x = 0 := by simpa using hx
    exact ⟨hm, fun h ↦ absurd (Nat.zero_mod p) h⟩⟩

-- The step of the loop of `Ratpoints.Sieve.examinePower` at the residue `k + 1`, with an entry
-- below `m` that is the inverse of the residue when it is prime to `p`.
private theorem ExaminePowerInvariant.push_of_lt {p m k r : ℕ} {inv : Array ℕ}
    (h : ExaminePowerInvariant p m k inv) (hr : r < m)
    (hinv : (k + 1) % p ≠ 0 → (k + 1) * r % m = 1) :
    ExaminePowerInvariant p m (k + 1) (inv.push r) := by
  obtain ⟨hs, h⟩ := h
  refine ⟨by simp [hs], fun x hx ↦ ?_⟩
  rw [Array.size_push] at hx
  rcases Nat.lt_or_ge x inv.size with hx' | hx'
  · rw [Array.getElem!_push_lt hx']
    exact h x hx'
  · obtain rfl : x = inv.size := by lia
    rw [Array.getElem!_push_eq, hs]
    exact ⟨hr, hinv⟩

/-- The step of the loop of `Ratpoints.Sieve.examinePower` at a residue divisible by `p`, whose
entry is `0`. -/
theorem ExaminePowerInvariant.push_zero {p m cur : ℕ} {pref suff : List ℕ} {inv : Array ℕ}
    (hl : ForIn.toList [1:m] = pref ++ cur :: suff) (h : ExaminePowerInvariant p m pref.length inv)
    (hm : 0 < m) (hc : cur % p = 0) :
    ExaminePowerInvariant p m (pref ++ [cur]).length (inv.push 0) := by
  have := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton]
  exact h.push_of_lt hm fun h' ↦ absurd (by rwa [Nat.add_comm, this]) h'

/-- The step of the loop of `Ratpoints.Sieve.examinePower` at a residue prime to `p`, whose entry
is its inverse modulo `m`, by `Ratpoints.Sieve.modinv`. -/
theorem ExaminePowerInvariant.push {p m cur r : ℕ} {pref suff : List ℕ} {inv : Array ℕ}
    (hl : ForIn.toList [1:m] = pref ++ cur :: suff) (h : ExaminePowerInvariant p m pref.length inv)
    (hr : r < m ∧ cur * r % m = 1) :
    ExaminePowerInvariant p m (pref ++ [cur]).length (inv.push r) := by
  have := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton]
  exact h.push_of_lt hr.1 fun _ ↦ by rw [Nat.add_comm, this]; exact hr.2

/-- At the end of the loop of `Ratpoints.Sieve.examinePower`, for `m > 0`: every entry of the
inverses is below `m`, and that of a residue prime to `p` is its inverse modulo `m`. -/
theorem ExaminePowerInvariant.post {p m : ℕ} {inv : Array ℕ}
    (h : ExaminePowerInvariant p m (ForIn.toList [1:m]).length inv) (hm : 0 < m) (x : ℕ) :
    inv[x]! < m ∧ (x < m → x % p ≠ 0 → x * inv[x]! % m = 1) := by
  obtain ⟨hs, h⟩ := h
  rw [Std.Legacy.Range.length_toList, Nat.sub_add_cancel hm] at hs
  by_cases hx : x < inv.size
  · exact ⟨(h x hx).1, fun _ ↦ (h x hx).2⟩
  · rw [getElem!_neg _ x hx]
    exact ⟨hm, fun hx' ↦ absurd (hs ▸ hx') hx⟩

attribute [local irreducible] ExaminePowerInvariant in
/-- The contract of `Ratpoints.Sieve.examinePower` for a prime `p` and `e ≥ 1`: the inverses of the
prime power `p ^ e` are below `p ^ e`, and that of a unit is its inverse modulo `p ^ e`, by the
extended Euclidean algorithm (`Ratpoints.Sieve.modinv_spec`); the tables `fsq` and `gsq` are folds
and maps that the lemmas on them unfold. -/
@[spec]
theorem examinePower_spec (c : List ℤ) (d p e : ℕ) (u : Bool) :
    ⦃ p.Prime ∧ 1 ≤ e ⦄ examinePower c d p e u
    ⦃ fun pw ↦ ∀ x, pw.inv[x]! < p ^ e ∧
        (x < p ^ e → x % p ≠ 0 → x * pw.inv[x]! % p ^ e = 1) ⦄ := by
  vcgen [examinePower] invariants
  · fun pref _ inv ↦ ExaminePowerInvariant p (p ^ e) pref.length inv
  all_goals obtain ⟨hp, he⟩ := ‹p.Prime ∧ 1 ≤ e›
  all_goals first
    | exact examinePowerInvariant_zero p (pow_pos hp.pos e)
    | exact ExaminePowerInvariant.post ‹_› (pow_pos hp.pos e) _
    | exact ExaminePowerInvariant.push_zero ‹_› ‹_› (pow_pos hp.pos e) ‹_›
    | exact ExaminePowerInvariant.push ‹_› ‹_› ‹_›
    | exact ⟨Nat.one_lt_pow (by lia) hp.one_lt,
        hp.coprime_pow_of_not_dvd fun h ↦ ‹¬_ % p = 0› (Nat.mod_eq_zero_of_dvd h)⟩

theorem getElem!_inv_run_examinePower_lt {c : List ℤ} {d p e : ℕ} (u : Bool) (hp : p.Prime)
    (he : 1 ≤ e) (x : ℕ) : (Id.run (examinePower c d p e u)).inv[x]! < p ^ e :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((examinePower_spec c d p e u).le_wp ⟨hp, he⟩) x).1

/-- Entry `x` of the inverses of the prime power `p ^ e`, for a unit `x`, is its inverse modulo
`p ^ e`, by `Ratpoints.Sieve.modinv`. -/
theorem mul_getElem!_inv_run_examinePower_mod {c : List ℤ} {d p e : ℕ} (u : Bool) (hp : p.Prime)
    (he : 1 ≤ e) {x : ℕ} (hx : x < p ^ e) (hpx : x % p ≠ 0) :
    x * (Id.run (examinePower c d p e u)).inv[x]! % p ^ e = 1 :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((examinePower_spec c d p e u).le_wp ⟨hp, he⟩) x).2 hx hpx

/-- The range obligation of the inverses of `examine_power` (`find_points.c:2303`), which it casts
to the `unsigned short` entries of `inv` (`rp-private.h:533`): for a prime power
`p ^ e < maxPrimeEven`, they are below `p ^ e` (`Ratpoints.Sieve.getElem!_inv_run_examinePower_lt`),
so below `2 ^ 10` (`Ratpoints.maxPrimeEven_le_two_pow_10`) and below `2 ^ 16`: the cast keeps
them. -/
theorem getElem!_inv_run_examinePower_lt_two_pow_16 {c : List ℤ} {d p e : ℕ} (u : Bool)
    (hp : p.Prime) (he : 1 ≤ e) (hm : p ^ e < maxPrimeEven) (x : ℕ) :
    (Id.run (examinePower c d p e u)).inv[x]! < 2 ^ 16 :=
  (getElem!_inv_run_examinePower_lt u hp he x).trans
    (hm.trans_le (maxPrimeEven_le_two_pow_10.trans (by norm_num)))

/-! ### The rows of a prime power let every point through -/

-- The residue modulo `p` of the residue of `a` modulo `m`, for `p ∣ m`.
private theorem toNat_emod_mod_of_dvd (a : ℤ) {m p : ℕ} (hm : 0 < m) (hpm : p ∣ m) :
    (a % (m : ℤ)).toNat % p = (a % (p : ℤ)).toNat := by
  have hp : 0 < p := Nat.pos_of_dvd_of_pos hpm hm
  rw [← Int.natCast_inj, Int.natCast_mod, Int.toNat_of_nonneg (Int.emod_nonneg _ (by lia)),
    Int.toNat_of_nonneg (Int.emod_nonneg _ (by lia)),
    Int.emod_emod_of_dvd _ (Int.natCast_dvd_natCast.mpr hpm)]

-- The cast of the product of a residue and its inverse in the table of a prime power.
private theorem natCast_mul_getElem!_inv_run_examinePower {c : List ℤ} {d p e : ℕ} (u : Bool)
    (hp : p.Prime) (he : 1 ≤ e) {x : ℕ} (hx : x < p ^ e) (hpx : x % p ≠ 0) :
    (x : ZMod (p ^ e)) * (Id.run (examinePower c d p e u)).inv[x]! = 1 := by
  rw [← Nat.cast_mul, ← ZMod.natCast_mod, mul_getElem!_inv_run_examinePower_mod u hp he hx hpx,
    Nat.cast_one]

-- The row of a denominator `b` prime to `p` for the prime power `p ^ e`: the entry of `fsq` at
-- `a b⁻¹`.
private theorem getElem!_fsq_run_examinePower_of_sq_eq {c : List ℤ} {p e : ℕ} (u : Bool)
    (hp : p.Prime) (he : 1 ≤ e) {a y : ℤ} {b : ℕ} (hy : y ^ 2 = binaryForm c a b)
    (hb : b % p ≠ 0) :
    (Id.run (examinePower c (degree c) p e u)).fsq[(a % ((p ^ e : ℕ) : ℤ)).toNat *
      (Id.run (examinePower c (degree c) p e u)).inv[b % p ^ e]! % p ^ e]! = true := by
  have hm : 0 < p ^ e := pow_pos hp.pos e
  have : NeZero (p ^ e) := ⟨hm.ne'⟩
  have hw := natCast_mul_getElem!_inv_run_examinePower (c := c) (d := degree c) u hp he
    (Nat.mod_lt b hm) (by rwa [Nat.mod_mod_of_dvd b (dvd_pow_self p (by lia))])
  rw [ZMod.natCast_mod] at hw
  refine getElem!_fsq_run_examinePower_of_isSquare u (Nat.mod_lt _ hm) ?_
  rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_toNat_emod]
  exact isSquare_sum_mul_pow_of_sq_eq_binaryForm (IsUnit.of_mul_eq_one _ hw)
    (by rw [mul_assoc, mul_comm _ (b : ZMod (p ^ e)), hw, mul_one]) hy

-- The row of a denominator `b` divisible by `p` for the prime power `p ^ e`: `p ∤ a`, and the entry
-- of `gsq` at `b a⁻¹`.
private theorem getElem!_gsq_run_examinePower_of_sq_eq {c : List ℤ} {p e : ℕ} (u : Bool)
    (hp : p.Prime) (he : 1 ≤ e) {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) (hb : b % p = 0) :
    ((a % ((p ^ e : ℕ) : ℤ)).toNat % p != 0 &&
      (Id.run (examinePower c (degree c) p e u)).gsq[b % p ^ e *
        (Id.run (examinePower c (degree c) p e u)).inv[(a % ((p ^ e : ℕ) : ℤ)).toNat]! % p ^ e]!) =
        true := by
  have hm : 0 < p ^ e := pow_pos hp.pos e
  have : NeZero (p ^ e) := ⟨hm.ne'⟩
  have hpm : p ∣ p ^ e := dvd_pow_self p (by lia)
  have hx := toNat_emod_ne_zero_of_gcd_eq_one hp.one_lt hab hb
  rw [← toNat_emod_mod_of_dvd a hm hpm] at hx
  have hw := natCast_mul_getElem!_inv_run_examinePower (c := c) (d := degree c) u hp he
    ((Int.toNat_lt' hm).mpr (Int.emod_lt_of_pos _ (by lia))) hx
  rw [ZMod.natCast_toNat_emod] at hw
  refine Bool.and_eq_true_iff.mpr ⟨by simpa using hx, getElem!_gsq_run_examinePower_of_isSquare u
    (Nat.mod_lt _ hm) (Nat.mod_eq_zero_of_dvd ((Nat.dvd_mod_iff hpm).mpr
      (((Nat.dvd_mod_iff hpm).mpr (Nat.dvd_of_mod_eq_zero hb)).mul_right _))) ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod]
  exact isSquare_sum_mul_pow_sub_of_sq_eq_binaryForm (IsUnit.of_mul_eq_one _ hw)
    (by rw [mul_assoc, mul_comm _ (a : ZMod (p ^ e)), hw, mul_one]) hy

/-- The row of the denominator `b` for the prime power `p ^ e`, `e ≥ 1`, admits the numerator `a`
of every point `(a, y, b)` with `gcd(a, b) = 1`: for `p ∤ b`, since `f(a / b)` is a square modulo
`p ^ e`, and for `p ∣ b`, since `p ∤ a` and the reversed polynomial takes a square value at `b / a`
(`Ratpoints.isSquare_sum_mul_pow_sub_of_sq_eq_binaryForm`). -/
theorem admits_run_examinePower_of_sq_eq {c : List ℤ} {p e : ℕ} (u : Bool) (hp : p.Prime)
    (he : 1 ≤ e) {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    (Id.run (examinePower c (degree c) p e u)).admits b a = true := by
  simp only [Power.admits, p_run_examinePower, m_run_examinePower,
    Nat.mod_mod_of_dvd b (dvd_pow_self p (by lia : e ≠ 0))]
  split
  · exact getElem!_fsq_run_examinePower_of_sq_eq u hp he hy ‹_›
  · exact getElem!_gsq_run_examinePower_of_sq_eq u hp he hab hy (not_not.mp ‹_›)

/-! ### The factors of a modulus -/

theorem Entry.admits_mod_of_dvd (e : Entry) {m : ℕ} (h : e.p ∣ m) (b : ℕ) (a : ℤ) :
    e.admits (b % m) (a % m) = e.admits b a := by
  simp only [Entry.admits, Nat.mod_mod_of_dvd b h,
    Int.emod_emod_of_dvd a (Int.natCast_dvd_natCast.mpr h)]

theorem Power.admits_mod_of_dvd (pw : Power) {m : ℕ} (h : pw.m ∣ m) (b : ℕ) (a : ℤ) :
    pw.admits (b % m) (a % m) = pw.admits b a := by
  simp only [Power.admits, Nat.mod_mod_of_dvd b h,
    Int.emod_emod_of_dvd a (Int.natCast_dvd_natCast.mpr h)]

end Sieve

end Ratpoints

end
