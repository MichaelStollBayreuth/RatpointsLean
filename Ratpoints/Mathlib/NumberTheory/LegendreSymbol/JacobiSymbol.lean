/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol

/-!
# The Jacobi symbol of an odd prime and of a difference

Candidates for `Mathlib.NumberTheory.LegendreSymbol.JacobiSymbol`: the symbol of an odd prime `q`
over an odd `b` as the Legendre symbol of `b` times the sign of the reciprocity
(`jacobiSym.natCast_eq_ite_mul_legendreSym`), and subtracting `b` from the numerator keeps the
symbol (`jacobiSym.sub_natCast_left_self`).

## Main statements

* `jacobiSym.natCast_eq_ite_mul_legendreSym`: `J(q | b) = ± (b / q)` for an odd prime `q` and odd
  `b`, with `-` exactly when `q ≡ b ≡ 3 (mod 4)`.
* `jacobiSym.sub_natCast_left_self`: `J(a - b | b) = J(a | b)`.
-/

@[expose] public section

open scoped NumberTheorySymbols

namespace jacobiSym

theorem sub_natCast_left_self (a : ℤ) (b : ℕ) : J(a - b | b) = J(a | b) :=
  mod_left' (Int.sub_emod_right a b)

/-- **The symbol of an odd prime by its Legendre symbol.** For an odd prime `q` and odd `b`,
`J(q | b)` is the Legendre symbol of `b` modulo `q` times the sign of the quadratic reciprocity,
`-1` exactly when `q ≡ b ≡ 3 (mod 4)`. -/
theorem natCast_eq_ite_mul_legendreSym {q b : ℕ} [hq : Fact q.Prime] (hq2 : q ≠ 2)
    (hb : b % 2 = 1) :
    J(q | b) = (if q % 4 = 3 ∧ b % 4 = 3 then -1 else 1) * legendreSym q b := by
  have hq2 : q % 2 = 1 := hq.out.eq_two_or_odd.resolve_left hq2
  rw [← quadratic_reciprocity_if hq2 hb, legendreSym.to_jacobiSym]
  split_ifs <;> simp

end jacobiSym

end
