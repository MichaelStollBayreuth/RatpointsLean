/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.Padics.PadicVal.Defs
public import Ratpoints.Model.Setup
public import Std.WP

import Ratpoints.Mathlib.NumberTheory.Padics.PadicVal.Basic
import Std.Tactic.Do

/-!
# The valuation of an integer at a prime

The loop of `Ratpoints.Setup.valuation`, repeated division with remainder, gives for `n ≠ 0` and
`p > 1` an exponent `v` and the remainder `r ≠ 0` with `|n| = p ^ v m` and `m mod p = r`; for a
prime `p` these are the `p`-adic valuation of `|n|` and the unit part of `|n|` modulo `p`.

## Main statements

* `Ratpoints.Setup.valuation_spec`: for `p > 1` the loop ends with `|n| = p ^ v m` and
  `m mod p = r ≠ 0`, and with `(Ratpoints.veryBig, 0)` for `n = 0`;
  `Ratpoints.Setup.exists_eq_run_valuation` states this for `n ≠ 0` without the program logic, and
  `Ratpoints.Setup.exists_eq_of_eq_run_valuation` for a natural number `w ≠ 0`, as `w = p ^ v m`
  with `p ∤ m`.
* `Ratpoints.Setup.fst_run_valuation`, `Ratpoints.Setup.snd_run_valuation`: for a prime `p` and
  `n ≠ 0`, the valuation is `padicValNat p |n|` and the remainder the unit part of `|n|` modulo
  `p`.

## Implementation notes

The contract is proved with `vcgen`, the program logic of Lean core, with a loop invariant that is
a named definition, in a file with Mathlib, since the valuation of the C code is Mathlib's
`padicValNat`.
-/

@[expose] public section

set_option experimental.vcgen true

open scoped Std.WP

namespace Ratpoints

namespace Setup

/-- The invariant of the loop of `Ratpoints.Setup.valuation` on `n` and `p`, on the quotient `q`,
the remainder `r` and the count `v`: `|n| = p ^ v (p q + r)` with `r < p`, and `r ≠ 0` at the
exit. -/
def ValuationInvariant (n : ℤ) (p : ℕ) : Std.WP.WhileInvariant (ℕ × ℕ × ℕ) Prop :=
  .mk fun exit s ↦ n.natAbs = p ^ s.2.2 * (p * s.1 + s.2.1) ∧ s.2.1 < p ∧
    (exit = true → s.2.1 ≠ 0)

theorem valuationInvariant_div_mod {n : ℤ} {p : ℕ} (hp : 1 < p) :
    ValuationInvariant n p false (n.natAbs / p, n.natAbs % p, 0) :=
  ⟨by rw [Nat.pow_zero, Nat.one_mul, Nat.div_add_mod], Nat.mod_lt _ (Nat.zero_lt_of_lt hp), nofun⟩

theorem ValuationInvariant.add_one {n : ℤ} {p q r v mb : ℕ} (hp : 1 < p) (hn : n ≠ 0)
    (h : q = mb ∧ ValuationInvariant n p false (q, r, v)) (hr : (r == 0) = true) :
    q / p < mb ∧ ValuationInvariant n p false (q / p, q % p, v + 1) := by
  obtain ⟨rfl, h1, h2, -⟩ := h
  obtain rfl : r = 0 := by simpa using hr
  have hq : q ≠ 0 := fun h0 ↦ hn (by simpa [h0] using h1)
  refine ⟨Nat.div_lt_self (by lia) hp, ?_, Nat.mod_lt _ (Nat.zero_lt_of_lt hp), nofun⟩
  rw [h1, Nat.pow_succ, Nat.add_zero, Nat.mul_assoc, Nat.div_add_mod]

theorem ValuationInvariant.exit {n : ℤ} {p q r v mb : ℕ}
    (h : q = mb ∧ ValuationInvariant n p false (q, r, v)) (hr : ¬(r == 0) = true) :
    ValuationInvariant n p true (q, r, v) :=
  ⟨h.2.1, h.2.2.1, fun _ ↦ by simpa using hr⟩

theorem ValuationInvariant.exists_eq {n : ℤ} {p q r v : ℕ}
    (h : ValuationInvariant n p true (q, r, v)) :
    ∃ m, n.natAbs = p ^ v * m ∧ m % p = r ∧ r ≠ 0 :=
  ⟨p * q + r, h.1, by rw [Nat.mul_add_mod, Nat.mod_eq_of_lt h.2.1], h.2.2 rfl⟩

/- The invariant is irreducible from here on: the verification conditions of
`Ratpoints.Setup.valuation` are closed by its lemmas, never by unfolding it. -/
attribute [local irreducible] ValuationInvariant

/-- The loop ends, since the quotient drops with every pass while the remainder is `0`, `|n|` being
`p ^ v` times a positive multiple of `p`; for `p = 1` and `n ≠ 0` it would not. -/
@[spec]
theorem valuation_spec (n : ℤ) (p : ℕ) :
    ⦃ 1 < p ⦄ valuation n p
    ⦃ fun r ↦ (n = 0 ∧ r = (veryBig, 0)) ∨
        (n ≠ 0 ∧ ∃ m, n.natAbs = p ^ r.1 * m ∧ m % p = r.2 ∧ r.2 ≠ 0) ⦄ := by
  vcgen [valuation] invariants
  · ValuationInvariant n p
  · .ofMeasure fun s : ℕ × ℕ × ℕ ↦ s.1
  all_goals try simp only [Std.WP.Variant.evalsTo_ofMeasure,
    Std.WP.Variant.evalsBelow_ofMeasure_nat, Std.WP.Assertion.NondetFun.evalsTo_pure,
    Lean.Order.meet_prop_eq_and, Lean.Order.ofProp_prop_eq] at *
  all_goals first
    | exact .inl ⟨‹_›, trivial⟩
    | exact valuationInvariant_div_mod ‹_›
    | exact .inr ⟨‹_›, ‹ValuationInvariant _ _ true _›.exists_eq⟩
    | exact ValuationInvariant.add_one ‹_› ‹_› ‹_› ‹_›
    | exact ValuationInvariant.exit ‹_› ‹_›

/-- `Ratpoints.Setup.valuation_spec` for `n ≠ 0` as a plain statement, which the proofs use without
the program logic. -/
theorem exists_eq_run_valuation {n : ℤ} (hn : n ≠ 0) {p : ℕ} (hp : 1 < p) :
    ∃ m, n.natAbs = p ^ (Id.run (valuation n p)).1 * m ∧ m % p = (Id.run (valuation n p)).2 ∧
      (Id.run (valuation n p)).2 ≠ 0 :=
  ((Std.WP.Id.of_run_eq_wp rfl _ ((valuation_spec n p).le_wp hp)).resolve_left fun h ↦ hn h.1).2

theorem fst_run_valuation {n : ℤ} (hn : n ≠ 0) {p : ℕ} (hp : p.Prime) :
    (Id.run (valuation n p)).1 = padicValNat p n.natAbs := by
  obtain ⟨m, hm, hmr, hr⟩ := exists_eq_run_valuation hn hp.one_lt
  exact (padicValNat_eq_of_eq_pow_mul_of_not_dvd hp.one_lt hm
    fun h ↦ hr (hmr ▸ Nat.mod_eq_zero_of_dvd h)).symm

theorem snd_run_valuation {n : ℤ} (hn : n ≠ 0) {p : ℕ} (hp : p.Prime) :
    (Id.run (valuation n p)).2 = n.natAbs / p ^ padicValNat p n.natAbs % p := by
  obtain ⟨m, hm, hmr, -⟩ := exists_eq_run_valuation hn hp.one_lt
  rw [← fst_run_valuation hn hp, hm, Nat.mul_div_cancel_left _ (Nat.pow_pos hp.pos), hmr]

/-- The valuation of a natural number `w ≠ 0` at `p > 1` by `Ratpoints.Setup.valuation`, in the form
in which a loop that binds its result reads it: `w = p ^ v m` with `p ∤ m`. -/
theorem exists_eq_of_eq_run_valuation {w v r p : ℕ} (hw : w ≠ 0) (hp : 1 < p)
    (hv : (v, r) = Id.run (valuation (w : ℤ) p)) : ∃ m, w = p ^ v * m ∧ ¬p ∣ m := by
  obtain ⟨m, hm, hmr, hr⟩ := exists_eq_run_valuation (Int.natCast_ne_zero.mpr hw) hp
  simp only [← hv, Int.natAbs_natCast] at hm hmr hr
  exact ⟨m, hm, fun h ↦ hr (hmr ▸ Nat.mod_eq_zero_of_dvd h)⟩

end Setup

end Ratpoints

end
