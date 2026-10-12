/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The Jacobi symbol of a product, a sign and a prime

Candidates for `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`: for odd `b`, the sign of `a`
comes out of `J(a | b)` as a power of `χ₄ b` (`jacobiSym.eq_χ₄_pow_mul_natAbs`), a power of `2` and
a product of prime powers as a power of `χ₈ b` times the product of the powers of the symbols
(`jacobiSym.natCast_two_pow_mul_prod`), and the symbol of an odd prime `q` as the Legendre symbol of
`b mod q` times the sign of the reciprocity (`jacobiSym.natCast_eq_ite_mul_legendreSym`); and
subtracting `b` from a numerator at least `b` keeps the symbol (`jacobiSym.natCast_sub_self`).

## Main statements

* `jacobiSym.eq_χ₄_pow_mul_natAbs`: `J(a | b) = χ₄(b) ^ [a < 0] J(|a| | b)` for odd `b`.
* `jacobiSym.natCast_two_pow_mul_prod`: `J(2 ^ v ∏ qᵢ ^ eᵢ | b) = χ₈(b) ^ v ∏ J(qᵢ | b) ^ eᵢ` for
  odd `b`.
* `jacobiSym.natCast_eq_ite_mul_legendreSym`: `J(q | b) = ± (b mod q / q)` for an odd prime `q` and
  odd `b`, with `-` exactly when `q ≡ b ≡ 3 (mod 4)`.
* `jacobiSym.natCast_sub_self`: `J(x - b | b) = J(x | b)` for `b ≤ x`.
-/

@[expose] public section

open scoped NumberTheorySymbols

namespace jacobiSym

theorem natCast_sub_self {x b : ℕ} (h : b ≤ x) : J((x - b : ℕ) | b) = J(x | b) :=
  mod_left' (by rw [Nat.cast_sub h, Int.sub_emod_right])

theorem eq_χ₄_pow_mul_natAbs (a : ℤ) {b : ℕ} (hb : b % 2 = 1) :
    J(a | b) = ZMod.χ₄ b ^ (if a < 0 then 1 else 0) * J(a.natAbs | b) := by
  rcases lt_or_ge a 0 with h | h
  · nth_rw 1 [Int.eq_neg_natAbs_of_nonpos h.le]
    simp [jacobiSym.neg _ (Nat.odd_iff.mpr hb), h]
  · simp [h.not_gt, Int.natAbs_of_nonneg h]

theorem natCast_two_pow_mul_prod {b : ℕ} (hb : b % 2 = 1) (v : ℕ) {α : Type*} (l : List α)
    (q e : α → ℕ) :
    J(((2 ^ v * (l.map fun x ↦ q x ^ e x).prod : ℕ) : ℤ) | b) =
      ZMod.χ₈ b ^ v * (l.map fun x ↦ J(q x | b) ^ e x).prod := by
  push_cast
  rw [mul_left, pow_left, at_two (Nat.odd_iff.mpr hb), list_prod_left]
  simp [List.map_map, Function.comp_def, pow_left]

/-- **The symbol of an odd prime by its Legendre symbol.** For an odd prime `q` and odd `b`,
`J(q | b)` is the Legendre symbol of `b mod q` times the sign of the quadratic reciprocity, `-1`
exactly when `q ≡ b ≡ 3 (mod 4)`. -/
theorem natCast_eq_ite_mul_legendreSym {q b : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hb : b % 2 = 1) :
    J(q | b) = (if q % 4 = 3 ∧ b % 4 = 3 then -1 else 1) * legendreSym q (b % q : ℕ) := by
  have hq2 : q % 2 = 1 := hq.out.eq_two_or_odd.resolve_left hq2
  rw [← quadratic_reciprocity_if hq2 hb, Int.natCast_mod, ← legendreSym.mod,
    legendreSym.to_jacobiSym]
  split_ifs <;> simp

end jacobiSym

end
