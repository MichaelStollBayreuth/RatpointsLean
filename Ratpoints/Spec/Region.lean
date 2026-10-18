/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Mathlib.Algebra.Order.Field.Rat
public import Mathlib.Order.WithBotTop

/-!
# The values of the doubles

The ends of the search intervals of ratpoints are IEEE binary64 doubles, given here by their bits.
A double has a value in `ℚ` extended by `⊥` and `⊤` (`WithBotTop ℚ`), the two infinities; a NaN has
none (its value here is junk), and both zeros have the value `0`. The specification uses Mathlib
and nothing of the model.

## Main definitions

* `Ratpoints.IsNaN`, `Ratpoints.doubleValue`: whether the bits of a double are a NaN, and the value
  of a double.

## Implementation notes

The file imports `Mathlib.Order.WithBotTop` for the extended values and
`Mathlib.Algebra.Order.Field.Rat` for the order and the field operations of `ℚ`, both publicly: the
comparator challenge imports the Mathlib modules among the public imports of the files of the
specification that it restates, so that the definitions it restates elaborate to the same terms as
here.
-/

@[expose] public section

namespace Ratpoints

/-- Whether the IEEE binary64 bits `x` are a NaN: the exponent field all ones and the fraction
nonzero. -/
def IsNaN (x : UInt64) : Prop := (x.toNat / 2 ^ 52) % 2 ^ 11 = 2047 ∧ x.toNat % 2 ^ 52 ≠ 0

instance instDecidableIsNaN (x : UInt64) : Decidable (IsNaN x) :=
  inferInstanceAs (Decidable (_ ∧ _))

/-- The value of the IEEE binary64 double with the bits `x`: `±f 2 ^ (-1074)` for the exponent
field `0` (the zeros and the subnormals, both zeros giving `0`), `±(2 ^ 52 + f) 2 ^ (e - 1075)` for
an exponent field `e` from `1` to `2046`, and `⊥` and `⊤` for the infinities, where `f` is the
fraction and the sign is that of the top bit. The value of a NaN (the exponent field `2047` with a
nonzero fraction) is junk, an infinity: ratpoints refuses search intervals with a NaN end. -/
def doubleValue (x : UInt64) : WithBotTop ℚ :=
  let e : ℕ := (x.toNat / 2 ^ 52) % 2 ^ 11
  let f : ℕ := x.toNat % 2 ^ 52
  if e = 2047 then (if 2 ^ 63 ≤ x.toNat then ⊥ else ⊤)
  else
    let a : ℚ := if e = 0 then f * 2 ^ (-1074 : ℤ) else (2 ^ 52 + f) * 2 ^ ((e : ℤ) - 1075)
    ((if 2 ^ 63 ≤ x.toNat then -a else a : ℚ) : WithBotTop ℚ)

/-! ### Examples, checked by `decide` -/

-- The values of `1`, `-0.0`, `-∞`, `+∞`, the least subnormal `2 ^ (-1074)`, `2 ^ 63` and `-1.5`.
example : doubleValue 0x3ff0000000000000 = ((1 : ℚ) : WithBotTop ℚ) ∧
    doubleValue 0x8000000000000000 = ((0 : ℚ) : WithBotTop ℚ) ∧
    doubleValue 0xfff0000000000000 = ⊥ ∧ doubleValue 0x7ff0000000000000 = ⊤ ∧
    doubleValue 1 = (((2 : ℚ) ^ (-1074 : ℤ) : ℚ) : WithBotTop ℚ) ∧
    doubleValue 0x43e0000000000000 = (((2 : ℚ) ^ 63 : ℚ) : WithBotTop ℚ) ∧
    doubleValue 0xbff8000000000000 = ((-3 / 2 : ℚ) : WithBotTop ℚ) := by
  decide +kernel

end Ratpoints

end
