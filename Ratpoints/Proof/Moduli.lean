/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Data.ZMod.Basic
public import Ratpoints.Model.FindPoints
public import Ratpoints.Proof.Packing
public import Ratpoints.Proof.Words
public import Ratpoints.Spec.Basic

import Mathlib.Data.List.GetD
import Mathlib.Tactic.LinearCombination
import Ratpoints.Mathlib.Data.ZMod.Basic
import Ratpoints.Proof.Containers
import Ratpoints.Proof.Params
import Ratpoints.Proof.Tables
import Std.Tactic.Do

/-!
# Prime powers and products as moduli

The sieve entry of a modulus `m` (`Ratpoints.makeModulus?`) is made in a loop over the factors of
`m` over the table (`Ratpoints.modulusFactors`): a prime with its table, kept by the loop of the
tables or examined for `m`, and a prime power `p ^ e` with the tables of `examine_power`
(`Ratpoints.Sieve.examinePower`): the bit arrays of `Ratpoints.modWords` words of the residues at
which `f`, and of the multiples of `p` at which the reversed polynomial, take square values, read
from the bit array of the squares (`Ratpoints.Sieve.setSquareBits_spec`), and the inverses of the
units, from the extended Euclidean algorithm (`Ratpoints.Sieve.modinv`) in a loop over the residues
(`Ratpoints.Sieve.unitInverses_spec`), all in `Ratpoints.Sieve.examinePower_spec`. The tables of a
prime power within the words of its bit arrays compute what they claim, and its rows let every point
through (`Ratpoints.Sieve.admits_run_examinePower_of_sq_eq`): for `p ∤ b`, since `f(a / b)` is a
square modulo `p ^ e`, and for `p ∣ b`, since then `p ∤ a` and the reversed polynomial takes a
square value at `b / a`, both from the lemmas of `Ratpoints.Proof.Tables` for any commutative ring,
here `ZMod (p ^ e)`; the prime powers below `Ratpoints.maxPrimeEven`, the moduli of the parameters,
fit the words (`Ratpoints.Sieve.maxPrimeEven_le_sixty_four_mul_modWords`). The values of
`examine_power` stay in the range of their C types for the prime powers below
`Ratpoints.maxPrimeEven`: the cofactors of the extended Euclidean algorithm
(`Ratpoints.Sieve.ModinvInvariant.natAbs_add_mul_le`), the steps of Horner's rule and the squares
(`Ratpoints.mul_add_lt_two_pow_64_of_lt_maxPrimeEven`,
`Ratpoints.mul_self_lt_two_pow_63_of_lt_maxPrimeEven`), and the inverses
(`Ratpoints.Sieve.getElem!_inv_run_examinePower_lt_two_pow_16`). Each factor divides `m`, so that
its row reads the residues modulo `m` as those of the numbers
(`Ratpoints.Sieve.Entry.admits_mod_of_dvd`, `Ratpoints.Sieve.Power.admits_mod_of_dvd`, in
`Ratpoints.Proof.Words`), and the entry of `m`, which holds the reciprocal of `m`, lets every point
through when the tables of the loop of the tables are those of the reference
(`Ratpoints.makeModulus?_spec`); no Chinese remainder theorem is needed. The tables of inverses of
its factors serve the scaling of the rows by a unit modulo `m`
(`Ratpoints.Sieve.Factor.HasInverses`). For a modulus of well-formed parameters, which factors
completely over the table, the moduli of the factors multiply to `m`, so that the entry of a prime
reads the inverse of `Ratpoints.rbaLength` modulo `m` from its table, as `examine_prime` does, and
that of a prime power or a product computes it with `Ratpoints.Sieve.modinv`; with the bias of `m`,
the entry has what the packing of the numerators reads (`Ratpoints.Sieve.SieveEntry.Packable`). It
holds the reference to its table of rows and the kind of its builder that
`Ratpoints.Sieve.SieveEntry.refInit` gives at its position. When the entry is none, a prime examined
for it has no points modulo it, and the curve has none.

## Main definitions

* `Ratpoints.Sieve.ModinvInvariant`, `Ratpoints.Sieve.SquareBitsInvariant`,
  `Ratpoints.Sieve.UnitInversesInvariant`, `Ratpoints.Sieve.FsqInvariant`,
  `Ratpoints.Sieve.GsqInvariant`: the invariants of the loop of `Ratpoints.Sieve.modinv`, of the
  loops over the residues of `Ratpoints.Sieve.setSquareBits` and `Ratpoints.Sieve.unitInverses`,
  and of the loops of `Ratpoints.Sieve.examinePower` that set the bits of `fsq` and `gsq`.
* `Ratpoints.Sieve.Factor.IsSound`: a factor whose rows admit every point modulo `m` and whose
  tables of inverses serve the scaling.
* `Ratpoints.MakeModulusInvariant`: the invariant of the loop over the factors of
  `Ratpoints.makeModulus?`.
* `Ratpoints.IsModulusEntry`: what the contract of `Ratpoints.makeModulus?` says of the entry.

## Main statements

* `Ratpoints.Sieve.modinv_spec`: for `x` prime to `m > 1`, `Ratpoints.Sieve.modinv` gives the
  inverse of `x` modulo `m`, below `m`; `Ratpoints.Sieve.ModinvInvariant.natAbs_add_mul_le`: its
  cofactors stay between `-m` and `m`.
* `Ratpoints.Sieve.maxPrimeEven_le_sixty_four_mul_modWords`: the moduli of the parameters fit the
  bit arrays of `Ratpoints.modWords` words.
* `Ratpoints.Sieve.setSquareBits_spec`, `Ratpoints.Sieve.unitInverses_spec`: the bits of the squares
  and the inverses of the units of a prime power.
* `Ratpoints.Sieve.examinePower_spec`, with its plain forms
  `Ratpoints.Sieve.getElem!_inv_run_examinePower_lt` and
  `Ratpoints.Sieve.mul_getElem!_inv_run_examinePower_mod`: the inverses of a prime power are below
  it and hold the inverses of the units;
  `Ratpoints.Sieve.bitAt_fsq_run_examinePower_of_isSquare`,
  `Ratpoints.Sieve.bitAt_gsq_run_examinePower_of_isSquare`: its tables mark the residues at which
  `f`, or the reversed polynomial at a multiple of `p`, takes a square value.
* `Ratpoints.Sieve.getElem!_inv_run_examinePower_lt_two_pow_16`: the inverses of a prime power below
  `Ratpoints.maxPrimeEven` are below `2 ^ 16`, the range of their C type.
* `Ratpoints.Sieve.admits_run_examinePower_of_sq_eq`: the rows of a prime power let every point
  through.
* `Ratpoints.makeModulus?_spec`: the sieve entry of a modulus of well-formed parameters has the
  modulus, lets every point through, has the tables of inverses of its factors and the fields that
  the packing reads (`Ratpoints.IsModulusEntry`), and the reference and the kind of builder of its
  position (`Ratpoints.Sieve.SieveEntry.refInit`); that of one of the first `Ratpoints.numPrimes`
  primes of the table has the prime with the table of the reference as its only factor
  (`Ratpoints.factors_eq_of_run_makeModulus?_eq_some`), and when it is none the curve has no
  points.
* `Ratpoints.mod_two_eq_one_of_forall_dvd`, `Ratpoints.coprime_rbaLength_of_mod_two_eq_one`: a
  modulus of well-formed parameters is odd, so prime to `Ratpoints.rbaLength`.

## Implementation notes

The contracts of `Ratpoints.Sieve.modinv`, `Ratpoints.Sieve.setSquareBits`,
`Ratpoints.Sieve.unitInverses`, `Ratpoints.Sieve.examinePower` and `Ratpoints.makeModulus?` are
proved with `vcgen`, the program logic of Lean core, with loop invariants that are named
definitions, in a file with Mathlib, next to the soundness of the rows that they serve; the contract
of `Ratpoints.makeModulus?` reads its components through private specifications
`⦃True⦄ x ⦃fun r ↦ r = Id.run x⦄`, so that its verification conditions speak of the values of the
components.
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
  have hmod : r₀ - r₀ / r₁ * r₁ = r₀ % r₁ := Nat.mod_eq_sub_div_mul.symm
  refine ⟨hmod ▸ Nat.mod_lt _ (by lia), ⟨h1, ?_⟩, ?_, Nat.pos_of_ne_zero hr, ?_, ?_, ?_, nofun⟩
  · dsimp only
    rw [Nat.cast_sub hq, Nat.cast_mul, Int.cast_sub, Int.cast_mul, Int.cast_natCast, h0, h1]
    ring
  · dsimp only
    rw [hmod, ← hg, Nat.gcd_comm r₀ r₁, Nat.gcd_rec r₁ r₀, Nat.gcd_comm]
  · dsimp only
    linear_combination hs + ((r₀ / r₁ : ℕ) : ℤ) * mul_self_nonneg s₁
  · dsimp only
    rw [Int.natAbs_sub_mul_of_mul_nonpos hs]
    zify [hq] at hid ⊢
    linear_combination hid
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

/-- A prime power below `Ratpoints.maxPrimeEven`, the moduli of the parameters, fits the
`Ratpoints.modWords` words of the bit arrays of its tables and of the patterns of its rows. -/
theorem maxPrimeEven_le_sixty_four_mul_modWords : maxPrimeEven ≤ 64 * modWords :=
  Nat.le_mul_add_sub_one_div _ (by decide)

/-- The invariant of the loop of `Ratpoints.Sieve.setSquareBits` after the residues `pref`, on the
bit array: `Ratpoints.modWords` words, the bits of the squares `x ^ 2 mod m` of the residues `x` of
`pref` set. -/
def SquareBitsInvariant (m : ℕ) (pref : List ℕ) (sq : Array UInt64) : Prop :=
  sq.size = modWords ∧ ∀ x ∈ pref, bitAt sq (x * x % m) = true

theorem squareBitsInvariant_nil {m : ℕ} {sq : Array UInt64}
    (h : sq.size = modWords ∧ m ≤ 64 * modWords) : SquareBitsInvariant m [] sq :=
  ⟨h.1, fun _ h ↦ absurd h List.not_mem_nil⟩

/-- The step of the loop of `Ratpoints.Sieve.setSquareBits` at the residue `cur < m`, within the
words of the bit array. -/
theorem SquareBitsInvariant.push {m cur : ℕ} {pref suff : List ℕ} {sq₀ sq : Array UInt64}
    (pre : sq₀.size = modWords ∧ m ≤ 64 * modWords) (hl : ForIn.toList [:m] = pref ++ cur :: suff)
    (h : SquareBitsInvariant m pref sq) :
    SquareBitsInvariant m (pref ++ [cur]) (setBitAt sq (cur * cur % m)) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hs : cur * cur % m / 64 < sq.size :=
    h.1 ▸ Nat.div_lt_of_lt_mul ((Nat.mod_lt _ (by lia)).trans_le pre.2)
  refine ⟨by rw [size_setBitAt, h.1], fun x hx ↦ ?_⟩
  rw [bitAt_setBitAt hs]
  rcases List.mem_append.mp hx with hx | hx
  · rw [h.2 x hx, Bool.true_or]
  · rw [List.mem_singleton.mp hx]
    simp

theorem SquareBitsInvariant.post {m : ℕ} {sq : Array UInt64}
    (h : SquareBitsInvariant m (ForIn.toList [:m]) sq) :
    sq.size = modWords ∧ ∀ x < m, bitAt sq (x * x % m) = true :=
  ⟨h.1, fun x hx ↦ h.2 x (Std.Legacy.Range.mem_toList_of_lt hx)⟩

attribute [local irreducible] SquareBitsInvariant in
/-- The contract of `Ratpoints.Sieve.setSquareBits` on a bit array of `Ratpoints.modWords` words
with room for `m` bits: the bits of the squares modulo `m` are set. -/
@[spec]
theorem setSquareBits_spec (m : ℕ) (sq : Array UInt64) :
    ⦃ sq.size = modWords ∧ m ≤ 64 * modWords ⦄ setSquareBits m sq
    ⦃ fun sq' ↦ sq'.size = modWords ∧ ∀ x < m, bitAt sq' (x * x % m) = true ⦄ := by
  vcgen [setSquareBits] invariants
  | inv1 => fun pref _ sq' ↦ SquareBitsInvariant m pref sq'
  all_goals first
    | exact squareBitsInvariant_nil ‹_›
    | exact SquareBitsInvariant.post ‹_›
    | exact SquareBitsInvariant.push ‹_› ‹_› ‹_›

/-- A bit array in which the bits of the squares modulo `m` are set has the bit of every residue
`v < m` that is a square modulo `m`. -/
theorem bitAt_of_isSquare {m v : ℕ} {sq : Array UInt64}
    (h : ∀ x < m, bitAt sq (x * x % m) = true) (hv : v < m) (hsq : IsSquare (v : ZMod m)) :
    bitAt sq v = true := by
  obtain ⟨s, hs, rfl⟩ := ZMod.exists_eq_mul_self_mod_of_isSquare hv hsq
  exact h s hs

@[simp]
theorem p_run_examinePower (c : List ℤ) (d p e : ℕ) (u : Bool) :
    (Id.run (examinePower c d p e u)).p = p :=
  rfl

@[simp]
theorem m_run_examinePower (c : List ℤ) (d p e : ℕ) (u : Bool) :
    (Id.run (examinePower c d p e u)).m = p ^ e :=
  rfl

/-- The path through `long`s, with the helper `mod` of the C code, and the path through GMP
integers give the same tables of a prime power. -/
theorem examinePower_eq_examinePower_false (c : List ℤ) (d p e : ℕ) (u : Bool) :
    examinePower c d p e u = examinePower c d p e false := by
  simp [examinePower, modLong_eq_emod]

/-- The invariant of the loop of `Ratpoints.Sieve.unitInverses` over the residues `1, …, k` modulo
`m`, on the inverses `inv`: `k + 1` entries, each below `m`, that of a residue not divisible by `p`
its inverse modulo `m`. -/
def UnitInversesInvariant (p m k : ℕ) (inv : Array ℕ) : Prop :=
  inv.size = k + 1 ∧ ∀ x < inv.size, inv[x]! < m ∧ (x % p ≠ 0 → x * inv[x]! % m = 1)

theorem unitInversesInvariant_zero (p : ℕ) {m : ℕ} (hm : 0 < m) :
    UnitInversesInvariant p m 0 #[0] :=
  ⟨rfl, fun x hx ↦ by
    obtain rfl : x = 0 := by simpa using hx
    exact ⟨hm, absurd (Nat.zero_mod p)⟩⟩

-- The step of the loop of `Ratpoints.Sieve.unitInverses` at the residue `k + 1`, with an entry
-- below `m` that is the inverse of the residue when it is prime to `p`.
private theorem UnitInversesInvariant.push_of_lt {p m k r : ℕ} {inv : Array ℕ}
    (h : UnitInversesInvariant p m k inv) (hr : r < m)
    (hinv : (k + 1) % p ≠ 0 → (k + 1) * r % m = 1) :
    UnitInversesInvariant p m (k + 1) (inv.push r) := by
  obtain ⟨hs, h⟩ := h
  refine ⟨by simp [hs], fun x hx ↦ ?_⟩
  rw [Array.size_push] at hx
  rcases Nat.lt_or_ge x inv.size with hx' | hx'
  · rw [Array.getElem!_push_lt hx']
    exact h x hx'
  · obtain rfl : x = inv.size := by lia
    rw [Array.getElem!_push_eq, hs]
    exact ⟨hr, hinv⟩

/-- The step of the loop of `Ratpoints.Sieve.unitInverses` at a residue divisible by `p`, whose
entry is `0`. -/
theorem UnitInversesInvariant.push_zero {p m cur : ℕ} {pref suff : List ℕ} {inv : Array ℕ}
    (hl : ForIn.toList [1:m] = pref ++ cur :: suff) (h : UnitInversesInvariant p m pref.length inv)
    (hm : 0 < m) (hc : cur % p = 0) :
    UnitInversesInvariant p m (pref ++ [cur]).length (inv.push 0) := by
  have := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton]
  exact h.push_of_lt hm (absurd (by rwa [Nat.add_comm, this]))

/-- The step of the loop of `Ratpoints.Sieve.unitInverses` at a residue whose entry `r` is its
inverse modulo `m`, as `Ratpoints.Sieve.modinv` gives it for a residue not divisible by `p`. -/
theorem UnitInversesInvariant.push {p m cur r : ℕ} {pref suff : List ℕ} {inv : Array ℕ}
    (hl : ForIn.toList [1:m] = pref ++ cur :: suff) (h : UnitInversesInvariant p m pref.length inv)
    (hr : r < m ∧ cur * r % m = 1) :
    UnitInversesInvariant p m (pref ++ [cur]).length (inv.push r) := by
  have := Std.Legacy.Range.add_length_eq_of_toList_eq_append_cons hl
  rw [List.length_append, List.length_singleton]
  exact h.push_of_lt hr.1 fun _ ↦ by rw [Nat.add_comm, this]; exact hr.2

/-- At the end of the loop of `Ratpoints.Sieve.unitInverses`, for `m > 0`: every entry of the
inverses is below `m`, and that of a residue not divisible by `p` is its inverse modulo `m`. -/
theorem UnitInversesInvariant.post {p m : ℕ} {inv : Array ℕ}
    (h : UnitInversesInvariant p m (ForIn.toList [1:m]).length inv) (hm : 0 < m) (x : ℕ) :
    inv[x]! < m ∧ (x < m → x % p ≠ 0 → x * inv[x]! % m = 1) := by
  obtain ⟨hs, h⟩ := h
  rw [Std.Legacy.Range.length_toList, Nat.sub_add_cancel hm] at hs
  by_cases hx : x < inv.size
  · exact ⟨(h x hx).1, fun _ ↦ (h x hx).2⟩
  · rw [getElem!_neg _ x hx]
    exact ⟨hm, fun hx' ↦ absurd (hs ▸ hx') hx⟩

attribute [local irreducible] UnitInversesInvariant in
/-- The contract of `Ratpoints.Sieve.unitInverses` for a prime `p` and `e ≥ 1`: the inverses of the
prime power `p ^ e` are below `p ^ e`, and that of a unit is its inverse modulo `p ^ e`, by the
extended Euclidean algorithm (`Ratpoints.Sieve.modinv_spec`). -/
@[spec]
theorem unitInverses_spec (p e : ℕ) :
    ⦃ p.Prime ∧ 1 ≤ e ⦄ unitInverses p (p ^ e)
    ⦃ fun inv ↦ ∀ x, inv[x]! < p ^ e ∧ (x < p ^ e → x % p ≠ 0 → x * inv[x]! % p ^ e = 1) ⦄ := by
  vcgen [unitInverses] invariants
  · fun pref _ inv ↦ UnitInversesInvariant p (p ^ e) pref.length inv
  all_goals obtain ⟨hp, he⟩ := ‹p.Prime ∧ 1 ≤ e›
  all_goals first
    | exact unitInversesInvariant_zero p (pow_pos hp.pos e)
    | exact UnitInversesInvariant.post ‹_› (pow_pos hp.pos e) _
    | exact UnitInversesInvariant.push_zero ‹_› ‹_› (pow_pos hp.pos e) ‹_›
    | exact UnitInversesInvariant.push ‹_› ‹_› ‹_›
    | exact ⟨Nat.one_lt_pow (by lia) hp.one_lt,
        hp.coprime_pow_of_not_dvd fun h ↦ ‹¬_ % p = 0› (Nat.mod_eq_zero_of_dvd h)⟩

-- The coefficients of `examinePower`, with `c_D = 0` for odd `d`, reversed: Horner's rule gives the
-- value `∑ cₖ x ^ (D - k)` of the reversed polynomial modulo `m`.
private theorem natCast_evalMod_reverse_ite (c : List ℤ) (d : ℕ) {m : ℕ} [NeZero m] (x : ℕ) :
    (evalMod (if d % 2 = 1 then
        (List.range (d + 1)).map (fun k ↦ (c.getD k 0 % (m : ℤ)).toNat) ++ [0] else
        (List.range (d + 1)).map fun k ↦ (c.getD k 0 % (m : ℤ)).toNat).reverse m x : ZMod m) =
      ∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod m) * x ^ (d + d % 2 - k) := by
  split_ifs with hd
  · rw [natCast_evalMod_reverse, List.length_append, List.length_map, List.length_range,
      List.length_singleton, Finset.sum_range_succ, List.getD_append_right _ _ _ _ (by simp)]
    simp only [List.length_map, List.length_range, Nat.sub_self, List.getD_cons_zero, Nat.cast_zero,
      zero_mul, add_zero]
    refine Finset.sum_congr rfl fun _ hk ↦ ?_
    rw [List.getD_append _ _ _ _ (by simpa using hk),
      natCast_getD_map_range_toNat_emod c d (Finset.mem_range.mp hk), hd, Nat.add_sub_cancel]
  · rw [natCast_evalMod_reverse, List.length_map, List.length_range]
    refine Finset.sum_congr rfl fun _ hk ↦ ?_
    rw [natCast_getD_map_range_toNat_emod c d (Finset.mem_range.mp hk), Nat.add_one_sub_one,
      Nat.mod_two_ne_one.mp hd, Nat.add_zero]

/-- The invariant of the loop of `Ratpoints.Sieve.examinePower` over the residues that sets the bits
of `fsq`, after the residues `pref`, on the bit array: `Ratpoints.modWords` words, the bit of each
residue `x` of `pref` at which `f` takes a square value modulo `m` set. -/
def FsqInvariant (c : List ℤ) (d m : ℕ) (pref : List ℕ) (fsq : Array UInt64) : Prop :=
  fsq.size = modWords ∧ ∀ x ∈ pref,
    IsSquare (∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod m) * x ^ k) → bitAt fsq x = true

/-- The invariant of the loop of `Ratpoints.Sieve.examinePower` over the multiples `t` of `p` that
sets the bits of `gsq`, on the bit array and the multiple: `Ratpoints.modWords` words, `t` a
multiple of `p`, the bit of each multiple of `p` below `t` at which the reversed polynomial of the
even degree `D = d + d % 2` takes a square value modulo `m` set, and `t ≥ m` at the exit. -/
def GsqInvariant (c : List ℤ) (d p m : ℕ) : Std.WP.WhileInvariant (Array UInt64 × ℕ) Prop :=
  .mk fun exit s ↦ s.1.size = modWords ∧ s.2 % p = 0 ∧ (∀ t < s.2, t % p = 0 →
    IsSquare (∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod m) * t ^ (d + d % 2 - k)) →
      bitAt s.1 t = true) ∧ (exit = true → m ≤ s.2)

theorem size_eq_of_eq_replicate {sq fsq gsq : Array UInt64}
    (h : (sq, fsq, gsq) = (.replicate modWords 0, .replicate modWords 0, .replicate modWords 0)) :
    sq.size = modWords ∧ fsq.size = modWords ∧ gsq.size = modWords := by
  simp only [Prod.mk.injEq] at h
  simp [h]

theorem set!_eq_replicate {sq fsq gsq : Array UInt64} (k : ℕ)
    (h : (sq, fsq, gsq) = (.replicate modWords 0, .replicate modWords 0, .replicate modWords 0)) :
    (sq.set! k 0, fsq.set! k 0, gsq.set! k 0) =
      (.replicate modWords 0, .replicate modWords 0, .replicate modWords 0) := by
  simp only [Prod.mk.injEq] at h
  simp [h.1, h.2.1, h.2.2, Array.set!_eq_setIfInBounds]

theorem fsqInvariant_nil (c : List ℤ) (d m : ℕ) {sq fsq gsq : Array UInt64}
    (h : (sq, fsq, gsq) = (.replicate modWords 0, .replicate modWords 0, .replicate modWords 0)) :
    FsqInvariant c d m [] fsq :=
  ⟨(size_eq_of_eq_replicate h).2.1, fun _ h ↦ absurd h List.not_mem_nil⟩

theorem gsqInvariant_zero (c : List ℤ) (d p m : ℕ) {sq fsq gsq : Array UInt64}
    (h : (sq, fsq, gsq) = (.replicate modWords 0, .replicate modWords 0, .replicate modWords 0)) :
    GsqInvariant c d p m false (gsq, 0) :=
  ⟨(size_eq_of_eq_replicate h).2.2, Nat.zero_mod p, fun t ht ↦ absurd ht (Nat.not_lt_zero t),
    nofun⟩

/-- The step of the loop that sets the bits of `fsq` at the residue `cur`, its bit set when `f(cur)`
is a square modulo `m`, read from the bits of the squares. -/
theorem FsqInvariant.push {c : List ℤ} {d p e cur : ℕ} {pref suff : List ℕ} {sq fsq : Array UInt64}
    (pre : p.Prime ∧ 1 ≤ e ∧ p ^ e ≤ 64 * modWords)
    (hsq : sq.size = modWords ∧ ∀ x < p ^ e, bitAt sq (x * x % p ^ e) = true)
    (hl : ForIn.toList [:p ^ e] = pref ++ cur :: suff) (h : FsqInvariant c d (p ^ e) pref fsq)
    (hb : bitAt sq (evalMod ((List.range (d + 1)).map fun k ↦ (c.getD k 0 % (p ^ e : ℕ)).toNat)
      (p ^ e) cur) = true → bitAt fsq cur = true) :
    FsqInvariant c d (p ^ e) (pref ++ [cur]) fsq := by
  have : NeZero (p ^ e) := ⟨(pow_pos pre.1.pos e).ne'⟩
  refine ⟨h.1, fun x hx hs ↦ ?_⟩
  rcases List.mem_append.mp hx with hx | hx
  · exact h.2 x hx hs
  · obtain rfl := List.mem_singleton.mp hx
    rw [← natCast_evalMod_map_range] at hs
    exact hb (bitAt_of_isSquare hsq.2 (evalMod_lt _ (pow_pos pre.1.pos e) _) hs)

theorem FsqInvariant.push_setBitAt {c : List ℤ} {d p e cur : ℕ} {pref suff : List ℕ}
    {sq fsq : Array UInt64} (pre : p.Prime ∧ 1 ≤ e ∧ p ^ e ≤ 64 * modWords)
    (hsq : sq.size = modWords ∧ ∀ x < p ^ e, bitAt sq (x * x % p ^ e) = true)
    (hl : ForIn.toList [:p ^ e] = pref ++ cur :: suff) (h : FsqInvariant c d (p ^ e) pref fsq)
    (_ : bitAt sq (evalMod ((List.range (d + 1)).map fun k ↦ (c.getD k 0 % (p ^ e : ℕ)).toNat)
      (p ^ e) cur) = true) :
    FsqInvariant c d (p ^ e) (pref ++ [cur]) (setBitAt fsq cur) := by
  have hc := Std.Legacy.Range.lt_of_toList_eq_append_cons hl
  have hs : cur / 64 < fsq.size := h.1 ▸ Nat.div_lt_of_lt_mul (hc.trans_le pre.2.2)
  have h' : FsqInvariant c d (p ^ e) pref (setBitAt fsq cur) :=
    ⟨by rw [size_setBitAt, h.1], fun x hx hx' ↦ by
      rw [bitAt_setBitAt hs, h.2 x hx hx', Bool.true_or]⟩
  exact h'.push pre hsq hl fun _ ↦ by rw [bitAt_setBitAt hs]; simp

theorem FsqInvariant.push_of_not {c : List ℤ} {d p e cur : ℕ} {pref suff : List ℕ}
    {sq fsq : Array UInt64} (pre : p.Prime ∧ 1 ≤ e ∧ p ^ e ≤ 64 * modWords)
    (hsq : sq.size = modWords ∧ ∀ x < p ^ e, bitAt sq (x * x % p ^ e) = true)
    (hl : ForIn.toList [:p ^ e] = pref ++ cur :: suff) (h : FsqInvariant c d (p ^ e) pref fsq)
    (hb : ¬bitAt sq (evalMod ((List.range (d + 1)).map fun k ↦ (c.getD k 0 % (p ^ e : ℕ)).toNat)
      (p ^ e) cur) = true) :
    FsqInvariant c d (p ^ e) (pref ++ [cur]) fsq :=
  h.push pre hsq hl fun h' ↦ absurd h' hb

/-- The step of the loop that sets the bits of `gsq` at the multiple `t < m` of `p`, its bit set
when the reversed polynomial takes a square value modulo `m` at `t`, read from the bits of the
squares, with the measure `m - t`. -/
theorem GsqInvariant.push {c : List ℤ} {d p e t : ℕ} {sq gsq gsq' : Array UInt64}
    (pre : p.Prime ∧ 1 ≤ e ∧ p ^ e ≤ 64 * modWords)
    (hsq : sq.size = modWords ∧ ∀ x < p ^ e, bitAt sq (x * x % p ^ e) = true)
    (ht : t < p ^ e) (h : GsqInvariant c d p (p ^ e) false (gsq, t))
    (hs : gsq'.size = modWords) (hold : ∀ t' < t, bitAt gsq t' = true → bitAt gsq' t' = true)
    (hb : bitAt sq (evalMod (if d % 2 = 1 then
        (List.range (d + 1)).map (fun k ↦ (c.getD k 0 % (p ^ e : ℕ)).toNat) ++ [0] else
        (List.range (d + 1)).map fun k ↦ (c.getD k 0 % (p ^ e : ℕ)).toNat).reverse (p ^ e) t) =
      true → bitAt gsq' t = true) :
    p ^ e - (t + p) < p ^ e - t ∧ GsqInvariant c d p (p ^ e) false (gsq', t + p) := by
  have : NeZero (p ^ e) := ⟨(pow_pos pre.1.pos e).ne'⟩
  obtain ⟨-, hm, hb', -⟩ := h
  refine ⟨by lia [pre.1.pos], hs, by rwa [Nat.add_mod_right], fun t' ht' ht'p hsq' ↦ ?_, nofun⟩
  rcases Nat.lt_or_ge t' t with hlt | hge
  · exact hold t' hlt (hb' t' hlt ht'p hsq')
  · obtain rfl := Nat.eq_of_mod_eq_zero_of_le_of_lt hm ht'p hge ht'
    rw [← natCast_evalMod_reverse_ite] at hsq'
    exact hb (bitAt_of_isSquare hsq.2 (evalMod_lt _ (pow_pos pre.1.pos e) _) hsq')

theorem GsqInvariant.push_setBitAt {c : List ℤ} {d p e t mb : ℕ} {sq gsq : Array UInt64}
    (pre : p.Prime ∧ 1 ≤ e ∧ p ^ e ≤ 64 * modWords)
    (hsq : sq.size = modWords ∧ ∀ x < p ^ e, bitAt sq (x * x % p ^ e) = true)
    (ht : t < p ^ e) (h : p ^ e - t = mb ∧ GsqInvariant c d p (p ^ e) false (gsq, t))
    (_ : bitAt sq (evalMod (if d % 2 = 1 then
        (List.range (d + 1)).map (fun k ↦ (c.getD k 0 % (p ^ e : ℕ)).toNat) ++ [0] else
        (List.range (d + 1)).map fun k ↦ (c.getD k 0 % (p ^ e : ℕ)).toNat).reverse (p ^ e) t) =
      true) :
    p ^ e - (t + p) < mb ∧ GsqInvariant c d p (p ^ e) false (setBitAt gsq t, t + p) := by
  have hs : t / 64 < gsq.size := h.2.1 ▸ Nat.div_lt_of_lt_mul (ht.trans_le pre.2.2)
  obtain ⟨rfl, h⟩ := h
  exact GsqInvariant.push pre hsq ht h (by rw [size_setBitAt, h.1])
    (fun t' _ h' ↦ by rw [bitAt_setBitAt hs, h', Bool.true_or])
    fun _ ↦ by rw [bitAt_setBitAt hs]; simp

theorem GsqInvariant.push_of_not {c : List ℤ} {d p e t mb : ℕ} {sq gsq : Array UInt64}
    (pre : p.Prime ∧ 1 ≤ e ∧ p ^ e ≤ 64 * modWords)
    (hsq : sq.size = modWords ∧ ∀ x < p ^ e, bitAt sq (x * x % p ^ e) = true)
    (ht : t < p ^ e) (h : p ^ e - t = mb ∧ GsqInvariant c d p (p ^ e) false (gsq, t))
    (hb : ¬bitAt sq (evalMod (if d % 2 = 1 then
        (List.range (d + 1)).map (fun k ↦ (c.getD k 0 % (p ^ e : ℕ)).toNat) ++ [0] else
        (List.range (d + 1)).map fun k ↦ (c.getD k 0 % (p ^ e : ℕ)).toNat).reverse (p ^ e) t) =
      true) :
    p ^ e - (t + p) < mb ∧ GsqInvariant c d p (p ^ e) false (gsq, t + p) := by
  obtain ⟨rfl, h⟩ := h
  exact GsqInvariant.push pre hsq ht h h.1 (fun _ _ h' ↦ h') fun h' ↦ absurd h' hb

theorem GsqInvariant.exit {c : List ℤ} {d p m t mb : ℕ} {gsq : Array UInt64} (ht : ¬t < m)
    (h : m - t = mb ∧ GsqInvariant c d p m false (gsq, t)) : GsqInvariant c d p m true (gsq, t) :=
  ⟨h.2.1, h.2.2.1, h.2.2.2.1, fun _ ↦ Nat.le_of_not_lt ht⟩

/-- The precondition of `Ratpoints.Sieve.setSquareBits` in `Ratpoints.Sieve.examinePower`. -/
theorem setSquareBits_pre {sq fsq gsq : Array UInt64} {p e : ℕ}
    (h : (sq, fsq, gsq) = (.replicate modWords 0, .replicate modWords 0, .replicate modWords 0))
    (pre : p.Prime ∧ 1 ≤ e ∧ p ^ e ≤ 64 * modWords) : sq.size = modWords ∧ p ^ e ≤ 64 * modWords :=
  ⟨(size_eq_of_eq_replicate h).1, pre.2.2⟩

/-- The precondition of `Ratpoints.Sieve.unitInverses` in `Ratpoints.Sieve.examinePower`. -/
theorem unitInverses_pre {p e : ℕ} (pre : p.Prime ∧ 1 ≤ e ∧ p ^ e ≤ 64 * modWords) :
    p.Prime ∧ 1 ≤ e :=
  ⟨pre.1, pre.2.1⟩

/-- The end of `Ratpoints.Sieve.examinePower`: the inverses of the units, and the bits of `fsq` and
`gsq` of the residues and the multiples of `p` at which the polynomial and the reversed polynomial
take square values modulo `m`. -/
theorem examinePower_post {c : List ℤ} {d p m : ℕ} {fsq gsq : Array UInt64} {t : ℕ}
    {inv : Array ℕ} (hinv : ∀ x, inv[x]! < m ∧ (x < m → x % p ≠ 0 → x * inv[x]! % m = 1))
    (hf : FsqInvariant c d m (ForIn.toList [:m]) fsq) (hg : GsqInvariant c d p m true (gsq, t)) :
    (∀ x, inv[x]! < m ∧ (x < m → x % p ≠ 0 → x * inv[x]! % m = 1)) ∧
      (∀ x < m, IsSquare (∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod m) * x ^ k) →
        bitAt fsq x = true) ∧
      ∀ t' < m, t' % p = 0 → IsSquare (∑ k ∈ Finset.range (d + 1),
        (c.getD k 0 : ZMod m) * t' ^ (d + d % 2 - k)) → bitAt gsq t' = true :=
  ⟨hinv, fun x hx ↦ hf.2 x (Std.Legacy.Range.mem_toList_of_lt hx),
    fun t' ht' ↦ hg.2.2.1 t' (ht'.trans_le (hg.2.2.2 rfl))⟩

attribute [local irreducible] FsqInvariant GsqInvariant in
open Std.WP Std.WP.Assertion Lean.Order in
/-- The contract of `Ratpoints.Sieve.examinePower` for a prime `p`, `e ≥ 1` and `p ^ e` within the
words of its bit arrays: the inverses of the prime power `p ^ e` are below `p ^ e`, and that of a
unit is its inverse modulo `p ^ e` (`Ratpoints.Sieve.unitInverses_spec`); bit `x` of `fsq` is set
when `f(x)` is a square modulo `p ^ e`, and bit `t` of `gsq`, for `p ∣ t`, when the reversed
polynomial of the even degree `D = d + d % 2` takes a square value at `t`, read from the bits of the
squares (`Ratpoints.Sieve.setSquareBits_spec`). -/
@[spec]
theorem examinePower_spec (c : List ℤ) (d p e : ℕ) (u : Bool) :
    ⦃ p.Prime ∧ 1 ≤ e ∧ p ^ e ≤ 64 * modWords ⦄ examinePower c d p e u
    ⦃ fun pw ↦ (∀ x, pw.inv[x]! < p ^ e ∧ (x < p ^ e → x % p ≠ 0 → x * pw.inv[x]! % p ^ e = 1)) ∧
      (∀ x < p ^ e, IsSquare (∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod (p ^ e)) * x ^ k) →
        bitAt pw.fsq x = true) ∧
      ∀ t < p ^ e, t % p = 0 → IsSquare (∑ k ∈ Finset.range (d + 1),
        (c.getD k 0 : ZMod (p ^ e)) * t ^ (d + d % 2 - k)) → bitAt pw.gsq t = true ⦄ := by
  rw [examinePower_eq_examinePower_false]
  vcgen [examinePower] invariants
  | inv1 => fun _ _ st ↦ st = (.replicate modWords 0, .replicate modWords 0, .replicate modWords 0)
  | inv2 => fun pref _ fsq ↦ FsqInvariant c d (p ^ e) pref fsq
  | inv3 => GsqInvariant c d p (p ^ e)
  | inv4 => .ofMeasure fun s : Array UInt64 × ℕ ↦ p ^ e - s.2
  all_goals try simp only [Variant.evalsTo_ofMeasure, Variant.evalsBelow_ofMeasure_nat,
    NondetFun.evalsTo_pure, meet_prop_eq_and, ofProp_prop_eq, Bool.false_eq_true, ↓reduceIte] at *
  all_goals first
    | exact setSquareBits_pre ‹_› ‹_›
    | exact unitInverses_pre ‹_›
    | exact fsqInvariant_nil c d _ ‹_›
    | exact gsqInvariant_zero c d p _ ‹_›
    | exact set!_eq_replicate _ ‹_›
    | exact examinePower_post ‹_› ‹_› ‹_›
    | exact FsqInvariant.push_setBitAt ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact FsqInvariant.push_of_not ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact GsqInvariant.push_setBitAt ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact GsqInvariant.push_of_not ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact GsqInvariant.exit ‹_› ‹_›

theorem getElem!_inv_run_examinePower_lt {c : List ℤ} {d p e : ℕ} (u : Bool) (hp : p.Prime)
    (he : 1 ≤ e) (x : ℕ) : (Id.run (examinePower c d p e u)).inv[x]! < p ^ e :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((unitInverses_spec p e).le_wp ⟨hp, he⟩) x).1

/-- Entry `x` of the inverses of the prime power `p ^ e`, for a unit `x`, is its inverse modulo
`p ^ e`, by `Ratpoints.Sieve.modinv`. -/
theorem mul_getElem!_inv_run_examinePower_mod {c : List ℤ} {d p e : ℕ} (u : Bool) (hp : p.Prime)
    (he : 1 ≤ e) {x : ℕ} (hx : x < p ^ e) (hpx : x % p ≠ 0) :
    x * (Id.run (examinePower c d p e u)).inv[x]! % p ^ e = 1 :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((unitInverses_spec p e).le_wp ⟨hp, he⟩) x).2 hx hpx

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

/-- Bit `x` of the table `Ratpoints.Sieve.Power.fsq` of `m = p ^ e`
(`Ratpoints.Sieve.examinePower`), for `m` within the words of its bit arrays, is set when `f(x)` is
a square modulo `m`. -/
theorem bitAt_fsq_run_examinePower_of_isSquare {c : List ℤ} {d p e : ℕ} (u : Bool) (hp : p.Prime)
    (he : 1 ≤ e) (hm : p ^ e ≤ 64 * modWords) {x : ℕ} (hx : x < p ^ e)
    (h : IsSquare (∑ k ∈ Finset.range (d + 1), (c.getD k 0 : ZMod (p ^ e)) * x ^ k)) :
    bitAt (Id.run (examinePower c d p e u)).fsq x = true :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((examinePower_spec c d p e u).le_wp ⟨hp, he, hm⟩)).2.1 x hx h

/-- Bit `t` of the table `Ratpoints.Sieve.Power.gsq` of `m = p ^ e`
(`Ratpoints.Sieve.examinePower`), for `m` within the words of its bit arrays and `p ∣ t`, is set
when the reversed polynomial `∑ cₖ t ^ (D - k)` of the even degree `D = d + d % 2` takes a square
value modulo `m` at `t`. -/
theorem bitAt_gsq_run_examinePower_of_isSquare {c : List ℤ} {d p e : ℕ} (u : Bool) (hp : p.Prime)
    (he : 1 ≤ e) (hm : p ^ e ≤ 64 * modWords) {t : ℕ} (ht : t < p ^ e) (htp : t % p = 0)
    (h : IsSquare (∑ k ∈ Finset.range (d + 1),
      (c.getD k 0 : ZMod (p ^ e)) * t ^ (d + d % 2 - k))) :
    bitAt (Id.run (examinePower c d p e u)).gsq t = true :=
  (Std.WP.Id.of_run_eq_wp rfl _ ((examinePower_spec c d p e u).le_wp ⟨hp, he, hm⟩)).2.2 t ht htp h

/-! ### The rows of a prime power let every point through -/

-- The cast of the product of a residue and its inverse in the table of a prime power.
private theorem natCast_mul_getElem!_inv_run_examinePower {c : List ℤ} {d p e : ℕ} (u : Bool)
    (hp : p.Prime) (he : 1 ≤ e) {x : ℕ} (hx : x < p ^ e) (hpx : x % p ≠ 0) :
    (x : ZMod (p ^ e)) * (Id.run (examinePower c d p e u)).inv[x]! = 1 := by
  rw [← Nat.cast_mul, ← ZMod.natCast_mod, mul_getElem!_inv_run_examinePower_mod u hp he hx hpx,
    Nat.cast_one]

-- The row of a denominator `b` prime to `p` for the prime power `p ^ e`: the bit of `fsq` at
-- `a b⁻¹`.
private theorem bitAt_fsq_run_examinePower_of_sq_eq {c : List ℤ} {p e : ℕ} (u : Bool)
    (hp : p.Prime) (he : 1 ≤ e) (hm : p ^ e ≤ 64 * modWords) {a y : ℤ} {b : ℕ}
    (hy : y ^ 2 = binaryForm c a b) (hb : b % p ≠ 0) :
    bitAt (Id.run (examinePower c (degree c) p e u)).fsq ((a % ((p ^ e : ℕ) : ℤ)).toNat *
      (Id.run (examinePower c (degree c) p e u)).inv[b % p ^ e]! % p ^ e) = true := by
  have hm0 : 0 < p ^ e := pow_pos hp.pos e
  have : NeZero (p ^ e) := ⟨hm0.ne'⟩
  have hw := natCast_mul_getElem!_inv_run_examinePower (c := c) (d := degree c) u hp he
    (Nat.mod_lt b hm0) (by rwa [Nat.mod_mod_of_dvd b (dvd_pow_self p (by lia))])
  rw [ZMod.natCast_mod] at hw
  refine bitAt_fsq_run_examinePower_of_isSquare u hp he hm (Nat.mod_lt _ hm0) ?_
  rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_toNat_emod]
  exact isSquare_sum_mul_pow_of_sq_eq_binaryForm (IsUnit.of_mul_eq_one _ hw)
    (by rw [mul_assoc, mul_comm _ (b : ZMod (p ^ e)), hw, mul_one]) hy

-- The row of a denominator `b` divisible by `p` for the prime power `p ^ e`: `p ∤ a`, and the bit
-- of `gsq` at `b a⁻¹`.
private theorem bitAt_gsq_run_examinePower_of_sq_eq {c : List ℤ} {p e : ℕ} (u : Bool)
    (hp : p.Prime) (he : 1 ≤ e) (hm : p ^ e ≤ 64 * modWords) {a y : ℤ} {b : ℕ}
    (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) (hb : b % p = 0) :
    ((a % ((p ^ e : ℕ) : ℤ)).toNat % p != 0 &&
      bitAt (Id.run (examinePower c (degree c) p e u)).gsq (b % p ^ e *
        (Id.run (examinePower c (degree c) p e u)).inv[(a % ((p ^ e : ℕ) : ℤ)).toNat]! % p ^ e)) =
        true := by
  have hm0 : 0 < p ^ e := pow_pos hp.pos e
  have : NeZero (p ^ e) := ⟨hm0.ne'⟩
  have hpm : p ∣ p ^ e := dvd_pow_self p (by lia)
  have hx := Int.toNat_emod_ne_zero_of_gcd_eq_one hp.one_lt hab hb
  rw [← Int.toNat_emod_mod_of_dvd a hm0 hpm] at hx
  have hw := natCast_mul_getElem!_inv_run_examinePower (c := c) (d := degree c) u hp he
    (Int.toNat_emod_lt a hm0) hx
  rw [ZMod.natCast_toNat_emod] at hw
  refine Bool.and_eq_true_iff.mpr ⟨by simpa using hx, bitAt_gsq_run_examinePower_of_isSquare u hp
    he hm (Nat.mod_lt _ hm0) (Nat.mod_eq_zero_of_dvd ((Nat.dvd_mod_iff hpm).mpr
      (((Nat.dvd_mod_iff hpm).mpr (Nat.dvd_of_mod_eq_zero hb)).mul_right _))) ?_⟩
  rw [ZMod.natCast_mod, Nat.cast_mul, ZMod.natCast_mod]
  exact isSquare_sum_mul_pow_sub_of_sq_eq_binaryForm (IsUnit.of_mul_eq_one _ hw)
    (by rw [mul_assoc, mul_comm _ (a : ZMod (p ^ e)), hw, mul_one]) hy

/-- The row of the denominator `b` for the prime power `p ^ e`, `e ≥ 1`, within the words of its
bit arrays, admits the numerator `a` of every point `(a, y, b)` with `gcd(a, b) = 1`: for `p ∤ b`,
since `f(a / b)` is a square modulo `p ^ e`, and for `p ∣ b`, since `p ∤ a` and the reversed
polynomial takes a square value at `b / a`
(`Ratpoints.isSquare_sum_mul_pow_sub_of_sq_eq_binaryForm`). -/
theorem admits_run_examinePower_of_sq_eq {c : List ℤ} {p e : ℕ} (u : Bool) (hp : p.Prime)
    (he : 1 ≤ e) (hm : p ^ e ≤ 64 * modWords) {a y : ℤ} {b : ℕ} (hab : Int.gcd a b = 1)
    (hy : y ^ 2 = binaryForm c a b) :
    (Id.run (examinePower c (degree c) p e u)).admits b a = true := by
  simp only [Power.admits, p_run_examinePower, m_run_examinePower,
    Nat.mod_mod_of_dvd b (dvd_pow_self p (by lia : e ≠ 0))]
  split
  · exact bitAt_fsq_run_examinePower_of_sq_eq u hp he hm hy ‹_›
  · exact bitAt_gsq_run_examinePower_of_sq_eq u hp he hm hab hy (not_not.mp ‹_›)

/-! ### The sieve entry of a modulus -/

/-- A factor that `Ratpoints.makeModulus?` makes for the modulus `m` of the curve `y ^ 2 = F(x, z)`
with the coefficient list `c`: it admits every point `(a, y, b)` with `gcd(a, b) = 1` at the
residues of `b` and `a` modulo `m`, its tables of inverses serve the scaling of the rows by a unit
modulo `m` (`Ratpoints.Sieve.Factor.HasInverses`), and a prime has the inverses of the reference
(`Ratpoints.Sieve.inversesMod`). -/
structure Factor.IsSound (c : List ℤ) (m : ℕ) (f : Factor) : Prop where
  /-- The factor admits every point at the residues modulo `m`. -/
  admits_of_sq_eq ⦃a y : ℤ⦄ ⦃b : ℕ⦄ (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    f.admits (b % m) (a % m) = true
  /-- The tables of inverses serve the scaling of the rows by a unit modulo `m`. -/
  hasInverses : f.HasInverses m
  /-- A prime has the inverses of the reference. -/
  inverses_eq (t : Entry) (h : f = .prime t) : t.inverses = inversesMod t.p

-- The factor of a prime `p = primeTable[pn]` of `m` over the table, with its table.
private theorem isSound_prime_examinePrime {c : List ℤ} {m pn : ℕ}
    (hpe : (pn, 1) ∈ (Id.run (modulusFactors m)).1) :
    (Factor.prime (examinePrime c (degree c) primeTable[pn]!)).IsSound c m := by
  have hpn := lt_numPrimes_of_mem_run_modulusFactors hpe
  have hp := prime_getElem!_primeTable (hpn.trans_le numPrimes_le_size_primeTable)
  have hd := pow_dvd_of_mem_run_modulusFactors hpe
  rw [pow_one] at hd
  refine ⟨fun a y b hab hy ↦ ?_, ⟨hd, fun r hr hr0 ↦ getElem!_inversesMod_mul_mod hp hr hr0⟩,
    fun _ ht ↦ by obtain rfl := Factor.prime.inj ht; rfl⟩
  rw [Factor.admits, Entry.admits_mod_of_dvd (examinePrime c (degree c) primeTable[pn]!) hd]
  exact admits_examinePrime_of_sq_eq hp hab hy

-- The factor of a prime power `primeTable[pn] ^ e` of a modulus `0 < m < maxPrimeEven` over the
-- table, with its tables.
private theorem isSound_power_run_examinePower {c : List ℤ} {m pn e : ℕ} (u : Bool)
    (hm0 : 0 < m) (hm : m < maxPrimeEven) (hpe : (pn, e) ∈ (Id.run (modulusFactors m)).1) :
    (Factor.power (Id.run (examinePower c (degree c) primeTable[pn]! e u))).IsSound c m := by
  have hpn := lt_numPrimes_of_mem_run_modulusFactors hpe
  have hp := prime_getElem!_primeTable (hpn.trans_le numPrimes_le_size_primeTable)
  have he := one_le_of_mem_run_modulusFactors hpe
  have hd := pow_dvd_of_mem_run_modulusFactors hpe
  have hle : primeTable[pn]! ^ e ≤ 64 * modWords :=
    ((Nat.le_of_dvd hm0 hd).trans hm.le).trans maxPrimeEven_le_sixty_four_mul_modWords
  refine ⟨fun a y b hab hy ↦ ?_, ⟨?_, by simpa using hd, fun x hx hpx ↦ ?_⟩, nofun⟩
  · rw [Factor.admits, Power.admits_mod_of_dvd _ hd]
    exact admits_run_examinePower_of_sq_eq u hp he hle hab hy
  · simpa using dvd_pow_self primeTable[pn]! (by lia : e ≠ 0)
  · rw [Nat.mul_comm]
    exact mul_getElem!_inv_run_examinePower_mod u hp he (by simpa using hx) (by simpa using hpx)

end Sieve

open Sieve

/-- The invariant of the loop of `Ratpoints.makeModulus?` over the factors of `m` over the table,
after the factors `pref` and with the factors `suff` still to come, on the result of an early return
and the factors made: before a return, every factor made is sound for `m`
(`Ratpoints.Sieve.Factor.IsSound`) and the moduli of the factors made multiply to the product of
the powers `pref`; a result, which is `none` and comes when the curve has no points, only at the
end. -/
def MakeModulusInvariant (c : List ℤ) (m : ℕ) (pref suff : List (ℕ × ℕ))
    (st : Option (Option SieveEntry) × Array Factor) : Prop :=
  st.1.elim ((∀ f ∈ st.2, f.IsSound c m) ∧
      (st.2.toList.map Factor.modulus).prod = (pref.map fun f ↦ primeTable[f.1]! ^ f.2).prod)
    fun r ↦ suff = [] ∧ r = none ∧ ∀ H q, ¬IsPoint c H q

theorem makeModulusInvariant_empty (c : List ℤ) (m : ℕ) (suff : List (ℕ × ℕ)) :
    MakeModulusInvariant c m [] suff (none, #[]) :=
  ⟨nofun, rfl⟩

-- The step of the loop of `Ratpoints.makeModulus?` that makes the factor `f` of the power `x`.
private theorem MakeModulusInvariant.push {c : List ℤ} {m : ℕ} {x : ℕ × ℕ}
    {pref suff : List (ℕ × ℕ)} {o : Option (Option SieveEntry)} {factors : Array Factor}
    {f : Factor} (h : MakeModulusInvariant c m pref (x :: suff) (o, factors))
    (hf : f.IsSound c m) (hm : f.modulus = primeTable[x.1]! ^ x.2) :
    MakeModulusInvariant c m (pref ++ [x]) suff (none, factors.push f) := by
  cases o with
  | none =>
    refine ⟨Array.forall_mem_push.mpr ⟨hf, h.1⟩, ?_⟩
    rw [Array.toList_push, List.map_append, List.map_append, List.prod_append, List.prod_append,
      h.2]
    simp [hm]
  | some _ => exact absurd h.1 (List.cons_ne_nil _ _)

-- The factor at the cursor of the loop of `Ratpoints.makeModulus?` is one of the factors of `m`
-- over the table.
private theorem mem_run_modulusFactors_of_eq {m r : ℕ} {fac pref suff : List (ℕ × ℕ)}
    {x : ℕ × ℕ} (hfac : (fac, r) = Id.run (modulusFactors m)) (hl : fac = pref ++ x :: suff) :
    x ∈ (Id.run (modulusFactors m)).1 := by
  rw [← hfac, hl]
  simp

/-- The step of the loop of `Ratpoints.makeModulus?` at a prime factor whose table the loop of the
tables has kept, the table of the reference. -/
theorem MakeModulusInvariant.push_getElem? {c : List ℤ} {tables : Array Entry} {m r pn e : ℕ}
    {fac pref suff : List (ℕ × ℕ)} {o : Option (Option SieveEntry)} {factors : Array Factor}
    {t : Entry}
    (htab : ∀ (i : ℕ) (hi : i < tables.size), tables[i] = examinePrime c (degree c) primeTable[i]!)
    (hfac : (fac, r) = Id.run (modulusFactors m)) (hl : fac = pref ++ (pn, e) :: suff)
    (h : MakeModulusInvariant c m pref ((pn, e) :: suff) (o, factors)) (he : e = 1)
    (ht : tables[pn]? = some t) :
    MakeModulusInvariant c m (pref ++ [(pn, e)]) suff (none, factors.push (.prime t)) := by
  obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
  subst he
  rw [htab pn hi]
  exact h.push (isSound_prime_examinePrime (c := c) (mem_run_modulusFactors_of_eq hfac hl))
    (pow_one _).symm

/-- The step of the loop of `Ratpoints.makeModulus?` at a prime factor whose examination
(`Ratpoints.Sieve.examinePrime?`) gives a table, that of the reference. -/
theorem MakeModulusInvariant.push_run_examinePrime? {c : List ℤ} {u : Bool} {m r pn e : ℕ}
    {fac pref suff : List (ℕ × ℕ)} {o : Option (Option SieveEntry)} {factors : Array Factor}
    {t : Entry} {cm : Array ℕ}
    (hfac : (fac, r) = Id.run (modulusFactors m)) (hl : fac = pref ++ (pn, e) :: suff)
    (h : MakeModulusInvariant c m pref ((pn, e) :: suff) (o, factors)) (he : e = 1)
    (ht : Id.run (examinePrime? c (degree c) primeTable[pn]! u) = some (t, cm)) :
    MakeModulusInvariant c m (pref ++ [(pn, e)]) suff (none, factors.push (.prime t)) := by
  subst he
  have hpe := mem_run_modulusFactors_of_eq hfac hl
  rw [eq_examinePrime_of_lt_numPrimes_of_run_examinePrime?_eq_some
    (lt_numPrimes_of_mem_run_modulusFactors hpe) ht]
  exact h.push (isSound_prime_examinePrime (c := c) hpe) (pow_one _).symm

/-- The step of the loop of `Ratpoints.makeModulus?` at a factor that is a prime power, for a
modulus `0 < m < Ratpoints.maxPrimeEven`. -/
theorem MakeModulusInvariant.push_run_examinePower {c : List ℤ} {u : Bool} {m r pn e : ℕ}
    {fac pref suff : List (ℕ × ℕ)} {o : Option (Option SieveEntry)} {factors : Array Factor}
    (hm0 : 0 < m) (hm : m < maxPrimeEven) (hfac : (fac, r) = Id.run (modulusFactors m))
    (hl : fac = pref ++ (pn, e) :: suff)
    (h : MakeModulusInvariant c m pref ((pn, e) :: suff) (o, factors)) :
    MakeModulusInvariant c m (pref ++ [(pn, e)]) suff
      (none, factors.push (.power (Id.run (examinePower c (degree c) primeTable[pn]! e u)))) :=
  h.push (isSound_power_run_examinePower u hm0 hm (mem_run_modulusFactors_of_eq hfac hl)) rfl

/-- The early return of the loop of `Ratpoints.makeModulus?` at a prime factor whose examination
(`Ratpoints.Sieve.examinePrime?`) gives none: the curve has no points modulo the prime, so none at
all. -/
theorem makeModulusInvariant_some_none {c : List ℤ} {u : Bool} {m r pn e : ℕ}
    {fac pref suff : List (ℕ × ℕ)} {factors : Array Factor} {x : Option (Entry × Array ℕ)}
    (hfac : (fac, r) = Id.run (modulusFactors m)) (hl : fac = pref ++ (pn, e) :: suff)
    (hx : ∀ t cm, x = some (t, cm) → False)
    (he : Id.run (examinePrime? c (degree c) primeTable[pn]! u) = x) (l : List (ℕ × ℕ)) :
    MakeModulusInvariant c m l [] (some none, factors) := by
  have hpn := lt_numPrimes_of_mem_run_modulusFactors (mem_run_modulusFactors_of_eq hfac hl)
  exact ⟨rfl, rfl, not_isPoint_of_lt_numPrimes_of_run_examinePrime?_eq_none hpn
    (he.trans (Option.eq_none_iff_forall_ne_some.mpr fun ⟨t, cm⟩ h ↦ hx t cm h))⟩

/-- What the contract of `Ratpoints.makeModulus?` says of the sieve entry `s` of the modulus `m`
for the curve with the coefficient list `c`: its modulus is `m`, it admits every point `(a, y, b)`
with `gcd(a, b) = 1`, its factors have their tables of inverses for `m`
(`Ratpoints.Sieve.Factor.HasInverses`), and it has the fields that the packing reads
(`Ratpoints.Sieve.SieveEntry.Packable`). -/
structure IsModulusEntry (c : List ℤ) (m : ℕ) (s : SieveEntry) : Prop where
  /-- The modulus is `m`. -/
  p_eq : s.p = m
  /-- The entry admits every point. -/
  admits_of_sq_eq ⦃a y : ℤ⦄ ⦃b : ℕ⦄ (hab : Int.gcd a b = 1) (hy : y ^ 2 = binaryForm c a b) :
    s.admits b a = true
  /-- The factors have their tables of inverses for `m`. -/
  hasInverses : ∀ f ∈ s.factors, f.HasInverses m
  /-- The entry has the fields that the packing reads. -/
  packable : s.Packable

/-- The end of the loop of `Ratpoints.makeModulus?` after an early return. -/
theorem MakeModulusInvariant.post_some {c : List ℤ} {m n : ℕ} {fac : List (ℕ × ℕ)}
    {o : Option (Option SieveEntry)} {factors : Array Factor} {r : Option SieveEntry}
    (h : MakeModulusInvariant c m fac [] (o, factors)) (ho : o = some r) :
    (∀ s, r = some s → IsModulusEntry c m s ∧ (s.ref, s.init) = SieveEntry.refInit n s.factors) ∧
      (r = none → ∀ H q, ¬IsPoint c H q) := by
  subst ho
  obtain ⟨-, rfl, h⟩ := h
  exact ⟨nofun, fun _ ↦ h⟩

/-- A modulus each of whose divisors above `1` is divisible by one of the first
`Ratpoints.numPrimes` primes of the table is odd, since the table holds no `2`. -/
theorem mod_two_eq_one_of_forall_dvd {m : ℕ}
    (h : ∀ q > 1, q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q) : m % 2 = 1 := by
  by_contra h2
  obtain ⟨pn, hpn, hd⟩ := h 2 (by decide) (Nat.dvd_of_mod_eq_zero (by lia))
  have h3 : primeTable[0]! ≤ primeTable[pn]! :=
    getElem!_primeTable_le_of_le (Nat.zero_le pn) (hpn.trans_le numPrimes_le_size_primeTable)
  have := Nat.le_of_dvd (by decide) hd
  have : primeTable[0]! = 3 := by decide +kernel
  lia

/-- After the loop of `Ratpoints.makeModulus?` over all the factors, with an inverse `x < m` of
`Ratpoints.rbaLength` modulo `m`: the sieve entry of `m` with the factors made, the reciprocal and
the bias of `m`, the inverse `x` and any reference and kind of builder admits every point and has
the fields that the packing reads. -/
theorem MakeModulusInvariant.isModulusEntry {c : List ℤ} {m : ℕ} {fac : List (ℕ × ℕ)}
    {o : Option (Option SieveEntry)} {factors : Array Factor} {x : ℕ}
    (hm : 1 < m ∧ m < maxPrimeEven ∧ ∀ q > 1, q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q)
    (h : MakeModulusInvariant c m fac [] (o, factors)) (ho : o = none)
    (hx : x * rbaLength % m = 1 ∧ x < m) (ref : EntryRef) (init : RowInit) :
    IsModulusEntry c m
      ⟨m, factors.toList, magic m, m * ((rowBias + m - 1) / m), x, #[], ref, init⟩ := by
  subst ho
  exact ⟨rfl, fun _ _ _ hab hy ↦ List.all_eq_true.mpr fun f hf ↦
      (h.1 f (Array.mem_toList_iff.mp hf)).admits_of_sq_eq hab hy,
    fun f hf ↦ (h.1 f (Array.mem_toList_iff.mp hf)).hasInverses,
    ⟨hm.1, mod_two_eq_one_of_forall_dvd hm.2.2, hm.2.1.le, rfl, hx.1, hx.2, Nat.mul_mod_right _ _,
      Nat.le_mul_add_sub_one_div _ (Nat.zero_lt_of_lt hm.1),
      Nat.mul_add_sub_one_div_lt _ (Nat.zero_lt_of_lt hm.1)⟩⟩

/-- The end of the loop of `Ratpoints.makeModulus?` over all the factors, with an inverse `x < m`
of `Ratpoints.rbaLength` modulo `m`: the sieve entry of `m` at the position `n`, with the reference
and the kind of builder of `Ratpoints.Sieve.SieveEntry.refInit`
(`Ratpoints.MakeModulusInvariant.isModulusEntry`). -/
theorem MakeModulusInvariant.post_none {c : List ℤ} {m n : ℕ} {fac : List (ℕ × ℕ)}
    {o : Option (Option SieveEntry)} {factors : Array Factor} {x : ℕ}
    (hm : 1 < m ∧ m < maxPrimeEven ∧ ∀ q > 1, q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q)
    (h : MakeModulusInvariant c m fac [] (o, factors)) (ho : o = none)
    (hx : x * rbaLength % m = 1 ∧ x < m) :
    (∀ s, some (⟨m, factors.toList, magic m, m * ((rowBias + m - 1) / m), x, #[],
          (SieveEntry.refInit n factors.toList).1, (SieveEntry.refInit n factors.toList).2⟩ :
          SieveEntry) = some s →
        IsModulusEntry c m s ∧ (s.ref, s.init) = SieveEntry.refInit n s.factors) ∧
      (some (⟨m, factors.toList, magic m, m * ((rowBias + m - 1) / m), x, #[],
          (SieveEntry.refInit n factors.toList).1, (SieveEntry.refInit n factors.toList).2⟩ :
          SieveEntry) = none → ∀ H q, ¬IsPoint c H q) := by
  refine ⟨fun _ hs ↦ ?_, nofun⟩
  obtain rfl := Option.some.inj hs
  exact ⟨h.isModulusEntry hm ho hx _ _, rfl⟩

/-- The moduli of the factors of `m` over the table multiply to `m` when its factorization is
complete. -/
private theorem prod_modulus_eq {c : List ℤ} {m r : ℕ} {fac : List (ℕ × ℕ)}
    {o : Option (Option SieveEntry)} {factors : Array Factor}
    (hm : 1 < m ∧ m < maxPrimeEven ∧ ∀ q > 1, q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q)
    (hfac : (fac, r) = Id.run (modulusFactors m))
    (h : MakeModulusInvariant c m fac [] (o, factors)) (ho : o = none) :
    (factors.toList.map Factor.modulus).prod = m := by
  subst ho
  have h1 := snd_run_modulusFactors_eq_one (Nat.zero_lt_of_lt hm.1) hm.2.2
  have h2 := eq_mul_prod_run_modulusFactors m
  rw [← hfac] at h1 h2
  rw [h.2, h2, h1, Nat.one_mul]

/-- `Ratpoints.rbaLength`, a power of 2 (`Ratpoints.rbaLength_eq_two_pow_rbaShift`), is prime to
every odd modulus. -/
theorem coprime_rbaLength_of_mod_two_eq_one {m : ℕ} (hm : m % 2 = 1) :
    Nat.Coprime rbaLength m := by
  rw [rbaLength_eq_two_pow_rbaShift]
  exact (Nat.coprime_two_left.mpr (Nat.odd_iff.mpr hm)).pow_left _

-- The product of `Ratpoints.rbaLength < 2 ^ 32` (`Ratpoints.rbaShift_lt_thirty_two`) and a
-- modulus `m ≤ 2 ^ 32` is below `2 ^ 64`, so that the remainder of `Ratpoints.rbaLength` by the
-- reciprocal of `m` is exact.
private theorem rbaLength_mul_lt_two_pow_64 {m : ℕ} (hm : m ≤ 2 ^ 32) : rbaLength * m < 2 ^ 64 := by
  have h := Nat.pow_lt_pow_right (by decide : 1 < 2) rbaShift_lt_thirty_two
  rw [← rbaLength_eq_two_pow_rbaShift] at h
  calc rbaLength * m < 2 ^ 32 * 2 ^ 32 := Nat.mul_lt_mul_of_lt_of_le h hm (by decide)
    _ = 2 ^ 64 := by norm_num

/-- The inverse of `Ratpoints.rbaLength` modulo a prime modulus `m`, read from its table with the
remainder of `rbaLength` by the reciprocal of `m`, as `examine_prime` reads it. -/
theorem MakeModulusInvariant.rbainv_prime {c : List ℤ} {m r : ℕ} {fac : List (ℕ × ℕ)}
    {o : Option (Option SieveEntry)} {factors : Array Factor} {t : Entry}
    (hm : 1 < m ∧ m < maxPrimeEven ∧ ∀ q > 1, q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q)
    (hfac : (fac, r) = Id.run (modulusFactors m))
    (h : MakeModulusInvariant c m fac [] (o, factors)) (ho : o = none)
    (ht : factors.toList = [.prime t]) :
    t.inverses[mulMod rbaLength m (magic m)]! * rbaLength % m = 1 ∧
      t.inverses[mulMod rbaLength m (magic m)]! < m := by
  have hp := prod_modulus_eq hm hfac h ho
  rw [ht] at hp
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, Nat.mul_one,
    Factor.modulus] at hp
  subst ho
  have hs := h.1 (.prime t) (Array.mem_toList_iff.mp (by simp [ht]))
  have hc := coprime_rbaLength_of_mod_two_eq_one (mod_two_eq_one_of_forall_dvd hm.2.2)
  have hr0 : rbaLength % m ≠ 0 := fun h0 ↦ absurd (Nat.Coprime.eq_one_of_dvd hc.symm
    (Nat.dvd_of_mod_eq_zero h0)) hm.1.ne'
  rw [mulMod_magic (by lia) (rbaLength_mul_lt_two_pow_64
    (hm.2.1.le.trans maxPrimeEven_le_two_pow_32)), hs.inverses_eq t rfl, ← Nat.mul_mod_mod, ← hp]
  exact ⟨hs.inverses_eq t rfl ▸ hs.hasInverses.2 _ (Nat.mod_lt _ (by lia)) (hp ▸ hr0),
    getElem!_inversesMod_lt (Nat.mod_lt _ (by lia))⟩

-- The precondition of `Ratpoints.Sieve.modinv` for the inverse of `Ratpoints.rbaLength` modulo a
-- modulus `m > 1` all of whose divisors above `1` are divisible by primes of the table, an odd
-- modulus (`Ratpoints.mod_two_eq_one_of_forall_dvd`).
private theorem one_lt_and_coprime_rbaLength_mod {m : ℕ}
    (hm : 1 < m ∧ m < maxPrimeEven ∧ ∀ q > 1, q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q) :
    1 < m ∧ Nat.Coprime (rbaLength % m) m :=
  ⟨hm.1, (ZMod.coprime_mod_iff_coprime _ _).mpr
    (coprime_rbaLength_of_mod_two_eq_one (mod_two_eq_one_of_forall_dvd hm.2.2))⟩

-- The inverse of `Ratpoints.rbaLength` that `Ratpoints.Sieve.modinv` gives, in the form of
-- `Ratpoints.Sieve.SieveEntry.Packable`.
private theorem mul_rbaLength_mod_and_lt {m r : ℕ} (h : r < m ∧ rbaLength % m * r % m = 1) :
    r * rbaLength % m = 1 ∧ r < m :=
  ⟨by rw [Nat.mul_comm, ← Nat.mod_mul_mod]; exact h.2, h.1⟩

-- The factors of a modulus, the table of a prime and the tables of a prime power, as values for
-- the contract of the sieve entry of a modulus.
private theorem modulusFactors_value (m : ℕ) :
    ⦃ True ⦄ modulusFactors m ⦃ fun r ↦ r = Id.run (modulusFactors m) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem examinePrime?_value (c : List ℤ) (d p : ℕ) (u : Bool) :
    ⦃ True ⦄ examinePrime? c d p u ⦃ fun r ↦ r = Id.run (examinePrime? c d p u) ⦄ :=
  ⟨fun _ ↦ rfl⟩

private theorem examinePower_value (c : List ℤ) (d p e : ℕ) (u : Bool) :
    ⦃ True ⦄ examinePower c d p e u ⦃ fun r ↦ r = Id.run (examinePower c d p e u) ⦄ :=
  ⟨fun _ ↦ rfl⟩

attribute [local irreducible] MakeModulusInvariant mulMod in
-- The contract of `Ratpoints.makeModulus?` without the shape of the entry of a prime of the table.
private theorem makeModulus?_isModulusEntry_spec (c : List ℤ) (u : Bool) (tables : Array Entry)
    (n m : ℕ) :
    ⦃ (∀ (i : ℕ) (hi : i < tables.size), tables[i] = examinePrime c (degree c) primeTable[i]!) ∧
        1 < m ∧ m < maxPrimeEven ∧ ∀ q > 1, q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q ⦄
    makeModulus? c (degree c) u tables n m
    ⦃ fun r ↦ (∀ s, r = some s →
          IsModulusEntry c m s ∧ (s.ref, s.init) = SieveEntry.refInit n s.factors) ∧
        (r = none → ∀ H q, ¬IsPoint c H q) ⦄ := by
  vcgen [makeModulus?, modulusFactors_value, examinePrime?_value, examinePower_value] invariants
  · fun pref suff st ↦ MakeModulusInvariant c m pref suff st
  all_goals try dsimp only at *
  all_goals try obtain rfl := ‹_ = Id.run (examinePrime? _ _ _ _)›
  all_goals try obtain rfl := ‹_ = Id.run (examinePower _ _ _ _ _)›
  all_goals obtain ⟨htab, hm⟩ := ‹(∀ (i : ℕ) (hi : i < tables.size), _) ∧ _›
  all_goals first
    | exact one_lt_and_coprime_rbaLength_mod hm
    | exact makeModulusInvariant_empty c m _
    | exact MakeModulusInvariant.post_some ‹_› ‹_›
    | exact MakeModulusInvariant.push_getElem? htab ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact MakeModulusInvariant.push_run_examinePrime? ‹_› ‹_› ‹_› ‹_› ‹_›
    | exact MakeModulusInvariant.push_run_examinePower (Nat.zero_lt_of_lt hm.1) hm.2.1 ‹_› ‹_› ‹_›
    | exact makeModulusInvariant_some_none ‹_› ‹_› ‹_› ‹_› _
    | exact MakeModulusInvariant.post_none hm ‹_› ‹_› (mul_rbaLength_mod_and_lt ‹_›)
    | exact MakeModulusInvariant.post_none hm ‹_› ‹_›
        (MakeModulusInvariant.rbainv_prime hm ‹_› ‹_› ‹_› ‹_›)

/-- The sieve entry of one of the first `Ratpoints.numPrimes` primes of the table, when the tables
of the loop of the tables are those of the reference, has the prime as its only factor, with the
table of the reference: the prime is its only factor over the table
(`Ratpoints.fst_run_modulusFactors_getElem!_primeTable`), whose table the loop of the tables has
kept or `Ratpoints.Sieve.examinePrime?` gives
(`Ratpoints.Sieve.eq_examinePrime_of_lt_numPrimes_of_run_examinePrime?_eq_some`). -/
theorem factors_eq_of_run_makeModulus?_eq_some {c : List ℤ} {u : Bool} {tables : Array Entry}
    {n pn : ℕ} (hpn : pn < numPrimes)
    (htab : ∀ (i : ℕ) (hi : i < tables.size), tables[i] = examinePrime c (degree c) primeTable[i]!)
    {s : SieveEntry} (h : Id.run (makeModulus? c (degree c) u tables n primeTable[pn]!) = some s) :
    s.factors = [.prime (examinePrime c (degree c) primeTable[pn]!)] := by
  simp only [makeModulus?, Id.run_bind, fst_run_modulusFactors_getElem!_primeTable hpn,
    List.forIn_cons, List.forIn_nil, ↓reduceIte] at h
  cases ht : tables[pn]? with
  | some t =>
    obtain ⟨hi, rfl⟩ := Array.getElem?_eq_some_iff.mp ht
    simp only [ht, List.push_toArray, List.nil_append, pure_bind, Id.run_pure,
      Option.some.injEq] at h
    rw [← h, htab]
  | none =>
    cases he : Id.run (examinePrime? c (degree c) primeTable[pn]! u) with
    | none => simp [ht, he] at h
    | some x =>
      simp only [ht, List.push_toArray, List.nil_append, Id.run_bind, he, pure_bind, Id.run_pure,
        Option.some.injEq] at h
      rw [← h, eq_examinePrime_of_lt_numPrimes_of_run_examinePrime?_eq_some hpn he]

/-- The contract of `Ratpoints.makeModulus?`, when the tables of the loop of the tables are those of
the reference and `m > 1` is a modulus below `Ratpoints.maxPrimeEven` that factors completely over
the table (the moduli of `Ratpoints.Params.WF`): on a sieve entry, its modulus is `m`, and it admits
every point `(a, y, b)` with `gcd(a, b) = 1`, since each factor of `m` over the table, a prime or a
prime power, divides `m` (`Ratpoints.pow_dvd_of_mem_run_modulusFactors`), so that its row reads the
residues modulo `m` as those of `b` and `a`, and admits every point
(`Ratpoints.Sieve.admits_examinePrime_of_sq_eq`,
`Ratpoints.Sieve.admits_run_examinePower_of_sq_eq`); no Chinese remainder theorem is needed. Its
factors have their tables of inverses for `m`, and it holds the reciprocal and the bias of `m` and
the inverse of `Ratpoints.rbaLength` modulo `m`, read from the table of a prime with the remainder
by the reciprocal and computed by `Ratpoints.Sieve.modinv` otherwise (`Ratpoints.IsModulusEntry`).
It holds the reference to the entry whose table of rows holds its rows and the kind of its builder
of its position `n` (`Ratpoints.Sieve.SieveEntry.refInit`). For one of the first
`Ratpoints.numPrimes` primes of the table, its only factor is the prime with the table of the
reference (`Ratpoints.factors_eq_of_run_makeModulus?_eq_some`), the shape that the third stage of
the sieve needs. On none, a prime examined for `m` beyond the loop of the tables has no points
modulo it, where `sieving_info` returns that prime and the search ends, and the curve has no points
(`Ratpoints.Sieve.not_isPoint_of_run_examinePrime?_eq_none`). -/
@[spec]
theorem makeModulus?_spec (c : List ℤ) (u : Bool) (tables : Array Entry) (n m : ℕ) :
    ⦃ (∀ (i : ℕ) (hi : i < tables.size), tables[i] = examinePrime c (degree c) primeTable[i]!) ∧
        1 < m ∧ m < maxPrimeEven ∧ ∀ q > 1, q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q ⦄
    makeModulus? c (degree c) u tables n m
    ⦃ fun r ↦ (∀ s, r = some s → IsModulusEntry c m s ∧
        (s.ref, s.init) = SieveEntry.refInit n s.factors ∧ ∀ pn < numPrimes, primeTable[pn]! = m →
          s.factors = [.prime (examinePrime c (degree c) m)]) ∧
      (r = none → ∀ H q, ¬IsPoint c H q) ⦄ :=
  ⟨fun hpre ↦
    have h := Std.WP.Id.of_run_eq_wp rfl _
      ((makeModulus?_isModulusEntry_spec c u tables n m).le_wp hpre)
    ⟨fun s hs ↦ ⟨(h.1 s hs).1, (h.1 s hs).2, fun _ hpn hm ↦
      hm ▸ factors_eq_of_run_makeModulus?_eq_some hpn hpre.1 (hm ▸ hs)⟩, h.2⟩⟩

end Ratpoints

end
