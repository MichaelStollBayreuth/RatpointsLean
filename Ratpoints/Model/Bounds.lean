/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Candidate
public import Ratpoints.Model.Double
public import Ratpoints.Model.Tables

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Candidate
meta import Ratpoints.Model.Double
meta import Ratpoints.Model.Tables

/-!
# The exact bounds of the search intervals

The search intervals of a run in the form in which the sieve of one denominator reads them, made
once per run from the doubles of the search region (`Ratpoints.Sieve.exactBounds`): for the
denominator `b` the numerators of an interval `[l, u]` are `⌈b l⌉, …, ⌊b u⌋` within the height
bound, computed exactly. An end `x` is an exact binary fraction, `|x| = m 2 ^ (-s)`
(`Ratpoints.Sieve.ExactEnd`, made by `Ratpoints.Sieve.exactEnd` from the bits of the double), and
`b |x|` rounded as the end wants it is computed in 128 bits (`Ratpoints.Sieve.exactScale`); mostly,
though, the sieve computes `⌈b l⌉` and `⌊b u⌋` in a `long` from a form `(b M + C) >> sh` of each
end (`Ratpoints.Sieve.endForm`), which is exact for an end with a short mantissa and for an end
beyond the height bound on its side. The intervals with both forms are taken inline (`fast`), the
others by the products in 128 bits (`Ratpoints.Sieve.IntervalBounds`). The functions that turn the
bounds of an interval into the bits of the numerators of a class, `interval_bits` and
`interval_bits_exact` of the C code, are `Ratpoints.Sieve.intervalBits` and
`Ratpoints.Sieve.intervalBitsExact` in `Ratpoints.Model.Sieve`, next to the conversion of
numerators to bits that they end with (`Ratpoints.Sieve.numeratorsToBits`). The bounds are made
once for the run (`Ratpoints.Sieve.runSetup`) and read by the sieve of one denominator
(`Ratpoints.Sieve.sift`).

## Main definitions

* `Ratpoints.Sieve.ExactEnd`, `Ratpoints.Sieve.exactEnd`: an end of a search interval as an exact
  binary fraction with the rounding of its side.
* `Ratpoints.Sieve.exactScale`: `b |x|` rounded as the end wants it, in 128 bits, capped at
  `2 ^ 64 - 1`.
* `Ratpoints.Sieve.endForm`: the form `(b M + C) >> sh` of an end.
* `Ratpoints.Sieve.IntervalBounds`, `Ratpoints.Sieve.exactBounds`: the bounds of the search
  intervals of a run.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-- An end `x = ±m 2 ^ (-s)` of a search interval as `exact_end` makes it
(`Ratpoints.Sieve.exactEnd`), with the rounding `r = rh 2 ^ 64 + rl` that
`Ratpoints.Sieve.exactScale` adds to `b m`, `2 ^ s - 1` when the end wants `b |x|` rounded up and
`0` when it wants it rounded down, and whether `x < 0`.

C: `find_points.c:3217-3218`

Deviation: a natural number for the `int` `s`, which is from `0` to `127`, and a Boolean for the
`int` `neg`. -/
structure ExactEnd where
  /-- The mantissa: odd, or `s = 0`. -/
  m : UInt64
  /-- The low 64 bits of the rounding. -/
  rl : UInt64
  /-- The high 64 bits of the rounding. -/
  rh : UInt64
  /-- The exponent: `|x| = m 2 ^ (-s)`. -/
  s : Nat
  /-- Whether `x < 0`. -/
  neg : Bool
  deriving Inhabited, Repr

/-- The bounds of a search interval as the sieve of one denominator reads them, `rp_bounds`: the
forms `(b lM + lC) >> lsh` of the lower end and `(b uM + uC) >> ush` of the upper end
(`Ratpoints.Sieve.endForm`), whether the interval is taken inline (`fast`), and both ends as exact
binary fractions (`Ratpoints.Sieve.ExactEnd`). An interval that is not taken inline has the forms of
an empty one, `0` at the lower end and `-2 ^ 63` at the upper end.

C: `find_points.c:3219-3221`

Deviation: natural numbers for the `int` shifts `lsh` and `ush`, which are from `0` to `63`, and a
Boolean for the `int` `fast`. -/
structure IntervalBounds where
  /-- The multiplier of the form of the lower end. -/
  lM : Int64
  /-- The constant of the form of the lower end. -/
  lC : Int64
  /-- The multiplier of the form of the upper end. -/
  uM : Int64
  /-- The constant of the form of the upper end. -/
  uC : Int64
  /-- The shift of the form of the lower end. -/
  lsh : Nat
  /-- The shift of the form of the upper end. -/
  ush : Nat
  /-- Whether the interval is taken inline, from the forms of its ends. -/
  fast : Bool
  /-- The lower end. -/
  low : ExactEnd
  /-- The upper end. -/
  up : ExactEnd
  deriving Inhabited, Repr

/-- `min (2 ^ 64 - 1) ⌊(b m + r) / 2 ^ s⌋` for the end `e = ±m 2 ^ (-s)` with the rounding `r`
(`Ratpoints.Sieve.ExactEnd`) and the denominator `b`, which is `b |x|` rounded as the end wants it,
unless that does not fit 64 bits. The product `b m` in two 64-bit halves, the low half the product
of the words and the high half by `Ratpoints.Sieve.mulHi`; `r` added with the carry from the low
half; the 128-bit sum shifted right by `s`, from `0` to `127`, in its halves; and `2 ^ 64 - 1` when
the high half of the quotient is not `0`. As `b m < 2 ^ 126` and `r < 2 ^ 127`, the sum is below
`2 ^ 128` and nothing is lost.

C: `find_points.c:3231-3238`, `find_points.c:3257`

Deviation: the 128-bit product, sum and shift on two 64-bit halves, the high half of the product by
`Ratpoints.Sieve.mulHi`, for the `unsigned __int128` of the arm that the builds of the model compile
(the compiler defines `__SIZEOF_INT128__`, and `RP_NO_INT128` is not set), which Lean core does not
have; the other arm (lines 3239-3256), for a build without a 128-bit type, is excluded; the `long`
`b` converted to a 64-bit word, as the C code converts it to an `unsigned long`. -/
def exactScale (b : Int64) (e : ExactEnd) : UInt64 :=
  let lo := b.toUInt64 * e.m + e.rl
  let hi := mulHi b.toUInt64 e.m + e.rh + (if lo < e.rl then 1 else 0)
  let (qh, ql) : UInt64 × UInt64 :=
    if e.s = 0 then (hi, lo)
    else if e.s < 64 then
      (hi >>> e.s.toUInt64, (lo >>> e.s.toUInt64) ||| (hi <<< (64 - e.s).toUInt64))
    else (0, hi >>> (e.s - 64).toUInt64)
  if qh != 0 then ~~~0 else ql

/-- The mantissa `m` and the exponent `s` of a double `ax` with `0 ≤ ax < 2 ^ 63`, the absolute
value of an end, as `exact_end` makes them: `ax = f 2 ^ ex` with `1/2 ≤ f < 1`
(`Ratpoints.Double.frexp`), `m = f 2 ^ 53` (`Ratpoints.Double.ldexp`, converted by
`Ratpoints.Double.toUInt64`) and `s = 53 - ex`, so that `ax = m 2 ^ (-s)`; then `s = 0` for `m = 0`,
and else, while `s > 0`, the trailing zero bits of `m` dropped (`Ratpoints.Sieve.ctz`), at most `s`
of them; `m` shifted up by `-s` when `s < 0`; and `s` capped at `127`, which leaves
`⌊b m 2 ^ (-s)⌋ = 0` and `⌈b m 2 ^ (-s)⌉ = 1` for every `b < 2 ^ 63`, as they are for `s = 127`.

C: `find_points.c:3272-3291`

Deviation: an integer for the `int` `s` while it is computed, and a natural number when it is
returned; the lowest set bit by the loop of `RP_CTZL` (`Ratpoints.Sieve.ctz`), where gcc and clang
take `__builtin_ctzl`; the mantissa and the exponent returned, for the fields `m` and `s` of the
`rp_end` that the C code writes. -/
def exactMantissa (ax : Double) : Id (UInt64 × Nat) := do
  let (f, ex) := ax.frexp
  let mut m := (f.ldexp (Double.mantDig : Int)).toUInt64
  let mut s : Int := 53 - ex
  if m = 0 then s := 0
  else if 0 < s then
    let z : Int := min ((← ctz m) : Int) s
    m := m >>> z.toNat.toUInt64
    s := s - z
  if s < 0 then
    m := m <<< (-s).toNat.toUInt64
    s := 0
  if 127 < s then s := 127
  return (m, s.toNat)

/-- The end `x` of a search interval, at its lower end if `lower` and at its upper end otherwise,
as `exact_end` makes it (`Ratpoints.Sieve.ExactEnd`): `neg` for `x < 0` (`Ratpoints.Double.lt`, so
that `-0.0` is not negative); `m = 2 ^ 63` and `s = 0` when `|x| < 2 ^ 63` fails, an infinity
included, which is beyond every numerator, and otherwise the mantissa and the exponent of `|x|`
(`Ratpoints.Sieve.exactMantissa`); and the rounding `2 ^ s - 1`, in two halves for `s ≥ 64`, when
the end wants `b |x|` rounded up, which is when `lower` and `neg` differ (the lower end wants
`⌈b x⌉`, which is `b |x|` rounded up for `x ≥ 0` and minus `b |x|` rounded down for `x < 0`, and
the upper end the other way round), and `0` otherwise.

C: `find_points.c:3264-3271`, `find_points.c:3292-3299`

Deviation: the double as its bits, with `fabs` and the comparisons of the C language on them
(`Ratpoints.Double.fabs`, `Ratpoints.Double.lt`); a Boolean for the `int` `lower`; the end returned,
for the `rp_end` that the C code writes through its pointer. -/
def exactEnd (x : Double) (lower : Bool) : Id ExactEnd := do
  let ax := x.fabs
  let neg := x.lt .zero
  let (m, s) ← if !ax.lt .twoPow63 then pure ((1 : UInt64) <<< 63, 0) else exactMantissa ax
  let (rl, rh) : UInt64 × UInt64 :=
    if lower != neg then
      if s < 64 then (((1 : UInt64) <<< s.toUInt64) - 1, 0)
      else (~~~0, ((1 : UInt64) <<< (s - 64).toUInt64) - 1)
    else (0, 0)
  return { m, rl, rh, s, neg }

/-- The form `w = (b M + C) >> sh` of the end `e` of a search interval, at its lower end if `lower`
and at its upper end otherwise, for the height bound `height` and the denominators up to
`bHigh ≥ 1`, as `end_form` makes it, or none: for an end that can lie beyond the bound on its side
(`x < 0` at the lower end, `x ≥ 0` at the upper end), whose `|x|` is rounded down, with
`Ratpoints.Sieve.exactScale` at `b = 1` at least `height`, so that `|x| ≥ height`, the form
`(0, -height, 0)` at the lower end and `(0, height, 0)` at the upper end; and for `s < 64` and
`m ≤ ⌊(2 ^ 63 - 1 - C) / bHigh⌋` the form `(±m, C, s)`, the sign of `x`, with `C = 2 ^ s - 1` at the
lower end and `0` at the upper end, for which `b M + C` stays within the `long`s for every
`b ≤ bHigh`.

C: `find_points.c:3304-3318`

Deviation: the form returned as an option, for the pointers `M`, `C` and `sh` through which the C
code writes it and the `int` that says whether it has one; `Int64` for the `long`s, with the
division of `Int64`, which truncates as the C division does, on the non-negative `long`s
`LONG_MAX - c` and `b_high`; a Boolean for the `int` `lower`; a natural number for the `int`
`sh`. -/
def endForm (e : ExactEnd) (lower : Bool) (height bHigh : Int64) : Option (Int64 × Int64 × Nat) :=
  let c : Int64 := if lower && e.s < 64 then (((1 : UInt64) <<< e.s.toUInt64) - 1).toInt64 else 0
  if e.neg == lower && height.toUInt64 ≤ exactScale 1 e then
    some (0, if lower then -height else height, 0)
  else if e.s < 64 && e.m ≤ ((9223372036854775807 - c) / bHigh).toUInt64 then
    some (if e.neg then -e.m.toInt64 else e.m.toInt64, c, e.s)
  else none

/-- The bounds of the search intervals `domain`, increasing, disjoint and without a NaN, for the
height bound `height` and the denominators up to `bHigh ≥ 1`, as `exact_bounds` makes them
(`Ratpoints.Sieve.IntervalBounds`): for each interval `[l, u]` in turn, its ends
(`Ratpoints.Sieve.exactEnd`, `l` as a lower end and `u` as an upper end), and the interval taken
inline when `height ≤ 2 ^ 63 - 65`, so that `Ratpoints.Sieve.numeratorsToBits` needs no split
form, and both ends have a form (`Ratpoints.Sieve.endForm`), with these forms; otherwise the forms
of an empty interval, `0` at the lower end and `-2 ^ 63` at the upper end.

C: `find_points.c:3323-3340`

Deviation: the search intervals and the bounds as arguments, for the fields `domain`, `num_inter`,
`height` and `b_high` of the arguments, and the array of the bounds returned, for the array that
`run_setup` allocates and `exact_bounds` fills through its pointer; `Int64` for the `long`s; the
conjunction of the tests, whose `&&` makes the form of the upper end only when the lower end has
one, as a bind of options, and the forms as the options that `Ratpoints.Sieve.endForm` returns, for
the fields that `end_form` writes. -/
def exactBounds (domain : List (Double × Double)) (height bHigh : Int64) :
    Id (Array IntervalBounds) := do
  let mut bd := #[]
  for (l, u) in domain do
    let low ← exactEnd l true
    let up ← exactEnd u false
    let forms := if height ≤ 9223372036854775807 - 64 then
      (endForm low true height bHigh).bind fun lf ↦ (endForm up false height bHigh).map (lf, ·)
      else none
    bd := bd.push <| match forms with
      | some ((lM, lC, lsh), (uM, uC, ush)) => { lM, lC, uM, uC, lsh, ush, fast := true, low, up }
      | none =>
        { lM := 0, lC := 0, uM := 0, uC := -9223372036854775808, lsh := 0, ush := 0,
          fast := false, low, up }
  return bd

/-! ### Examples

The ends that `exact_end` makes and the values of `exact_scale` for them, against a C program that
runs these functions of the pinned commit verbatim, on doubles of every kind (both zeros, the
subnormals, the infinities, `2 ^ 63` and its neighbours, integers and fractions of either sign); the
numerator intervals of the search intervals of a run are in the examples of
`Ratpoints.Model.Sieve`, against the build of ratpoints with `DEBUG`. -/

-- For each double, at the lower and at the upper end: the fields `m`, `rl`, `rh`, `s` and `neg` of
-- `exact_end` (`M = 2 ^ 64 - 1`), `exact_scale` at the denominators `1`, `12345`, `2 ^ 62 + 1`,
-- `2 ^ 63 - 1` and `3 · 2 ^ 40`, and `end_form` for the height bounds and the largest denominators
-- `(1000, 1000)`, `(2 ^ 62, 7)` and `(10 ^ 9, 10 ^ 6)`.
#guard
  let M : Nat := 2 ^ 64 - 1
  let bs : List Int64 := [1, 12345, 2 ^ 62 + 1, 9223372036854775807, 3 * 2 ^ 40]
  let hb : List (Int64 × Int64) := [(1000, 1000), (2 ^ 62, 7), (1000000000, 1000000)]
  ([
    (0x0000000000000000, true, 0, 0, 0, 0, false, [0, 0, 0, 0, 0],
      [some (0, 0, 0), some (0, 0, 0), some (0, 0, 0)]),
    (0x0000000000000000, false, 0, 0, 0, 0, false, [0, 0, 0, 0, 0],
      [some (0, 0, 0), some (0, 0, 0), some (0, 0, 0)]),
    (0x8000000000000000, true, 0, 0, 0, 0, false, [0, 0, 0, 0, 0],
      [some (0, 0, 0), some (0, 0, 0), some (0, 0, 0)]),
    (0x8000000000000000, false, 0, 0, 0, 0, false, [0, 0, 0, 0, 0],
      [some (0, 0, 0), some (0, 0, 0), some (0, 0, 0)]),
    (0x0000000000000001, true, 1, M, 9223372036854775807, 127, false, [1, 1, 1, 1, 1],
      [none, none, none]),
    (0x0000000000000001, false, 1, 0, 0, 127, false, [0, 0, 0, 0, 0],
      [none, none, none]),
    (0x8000000000000001, true, 1, 0, 0, 127, true, [0, 0, 0, 0, 0],
      [none, none, none]),
    (0x8000000000000001, false, 1, M, 9223372036854775807, 127, true, [1, 1, 1, 1, 1],
      [none, none, none]),
    (0x000fffffffffffff, true, 4503599627370495, M, 9223372036854775807, 127, false,
      [1, 1, 1, 1, 1],
      [none, none, none]),
    (0x000fffffffffffff, false, 4503599627370495, 0, 0, 127, false, [0, 0, 0, 0, 0],
      [none, none, none]),
    (0x0010000000000000, true, 1, M, 9223372036854775807, 127, false, [1, 1, 1, 1, 1],
      [none, none, none]),
    (0x0010000000000000, false, 1, 0, 0, 127, false, [0, 0, 0, 0, 0],
      [none, none, none]),
    (0x3ff0000000000000, true, 1, 0, 0, 0, false,
      [1, 12345, 4611686018427387905, 9223372036854775807, 3298534883328],
      [some (1, 0, 0), some (1, 0, 0), some (1, 0, 0)]),
    (0x3ff0000000000000, false, 1, 0, 0, 0, false,
      [1, 12345, 4611686018427387905, 9223372036854775807, 3298534883328],
      [some (1, 0, 0), some (1, 0, 0), some (1, 0, 0)]),
    (0xbff0000000000000, true, 1, 0, 0, 0, true,
      [1, 12345, 4611686018427387905, 9223372036854775807, 3298534883328],
      [some (-1, 0, 0), some (-1, 0, 0), some (-1, 0, 0)]),
    (0xbff0000000000000, false, 1, 0, 0, 0, true,
      [1, 12345, 4611686018427387905, 9223372036854775807, 3298534883328],
      [some (-1, 0, 0), some (-1, 0, 0), some (-1, 0, 0)]),
    (0x3fe0000000000000, true, 1, 1, 0, 1, false,
      [1, 6173, 2305843009213693953, 4611686018427387904, 1649267441664],
      [some (1, 1, 1), some (1, 1, 1), some (1, 1, 1)]),
    (0x3fe0000000000000, false, 1, 0, 0, 1, false,
      [0, 6172, 2305843009213693952, 4611686018427387903, 1649267441664],
      [some (1, 0, 1), some (1, 0, 1), some (1, 0, 1)]),
    (0xbfe0000000000000, true, 1, 0, 0, 1, true,
      [0, 6172, 2305843009213693952, 4611686018427387903, 1649267441664],
      [some (-1, 1, 1), some (-1, 1, 1), some (-1, 1, 1)]),
    (0xbfe0000000000000, false, 1, 1, 0, 1, true,
      [1, 6173, 2305843009213693953, 4611686018427387904, 1649267441664],
      [some (-1, 0, 1), some (-1, 0, 1), some (-1, 0, 1)]),
    (0x3fd5555555555555, true, 6004799503160661, 18014398509481983, 0, 54, false,
      [1, 4115, 1537228672809129217, 3074457345618258432, 1099511627776],
      [some (6004799503160661, 18014398509481983, 54),
        some (6004799503160661, 18014398509481983, 54), none]),
    (0x3fd5555555555555, false, 6004799503160661, 0, 0, 54, false,
      [0, 4114, 1537228672809129216, 3074457345618258431, 1099511627775],
      [some (6004799503160661, 0, 54), some (6004799503160661, 0, 54), none]),
    (0xbfd5555555555555, true, 6004799503160661, 0, 0, 54, true,
      [0, 4114, 1537228672809129216, 3074457345618258431, 1099511627775],
      [some (-6004799503160661, 18014398509481983, 54),
        some (-6004799503160661, 18014398509481983, 54), none]),
    (0xbfd5555555555555, false, 6004799503160661, 18014398509481983, 0, 54, true,
      [1, 4115, 1537228672809129217, 3074457345618258432, 1099511627776],
      [some (-6004799503160661, 0, 54), some (-6004799503160661, 0, 54), none]),
    (0x4059000000000000, true, 100, 0, 0, 0, false, [100, 1234500, M, M, 329853488332800],
      [some (100, 0, 0), some (100, 0, 0), some (100, 0, 0)]),
    (0x4059000000000000, false, 100, 0, 0, 0, false, [100, 1234500, M, M, 329853488332800],
      [some (100, 0, 0), some (100, 0, 0), some (100, 0, 0)]),
    (0xc08f400000000000, true, 1000, 0, 0, 0, true, [1000, 12345000, M, M, 3298534883328000],
      [some (0, -1000, 0), some (-1000, 0, 0), some (-1000, 0, 0)]),
    (0xc08f400000000000, false, 1000, 0, 0, 0, true, [1000, 12345000, M, M, 3298534883328000],
      [some (-1000, 0, 0), some (-1000, 0, 0), some (-1000, 0, 0)]),
    (0x43e0000000000000, true, 9223372036854775808, 0, 0, 0, false,
      [9223372036854775808, M, M, M, M],
      [none, none, none]),
    (0x43e0000000000000, false, 9223372036854775808, 0, 0, 0, false,
      [9223372036854775808, M, M, M, M],
      [some (0, 1000, 0), some (0, 4611686018427387904, 0), some (0, 1000000000, 0)]),
    (0xc3e0000000000000, true, 9223372036854775808, 0, 0, 0, true,
      [9223372036854775808, M, M, M, M],
      [some (0, -1000, 0), some (0, -4611686018427387904, 0), some (0, -1000000000, 0)]),
    (0xc3e0000000000000, false, 9223372036854775808, 0, 0, 0, true,
      [9223372036854775808, M, M, M, M],
      [none, none, none]),
    (0x43dfffffffffffff, true, 9223372036854774784, 0, 0, 0, false,
      [9223372036854774784, M, M, M, M],
      [none, none, none]),
    (0x43dfffffffffffff, false, 9223372036854774784, 0, 0, 0, false,
      [9223372036854774784, M, M, M, M],
      [some (0, 1000, 0), some (0, 4611686018427387904, 0), some (0, 1000000000, 0)]),
    (0xc3dfffffffffffff, true, 9223372036854774784, 0, 0, 0, true,
      [9223372036854774784, M, M, M, M],
      [some (0, -1000, 0), some (0, -4611686018427387904, 0), some (0, -1000000000, 0)]),
    (0xc3dfffffffffffff, false, 9223372036854774784, 0, 0, 0, true,
      [9223372036854774784, M, M, M, M],
      [none, none, none]),
    (0x7ff0000000000000, true, 9223372036854775808, 0, 0, 0, false,
      [9223372036854775808, M, M, M, M],
      [none, none, none]),
    (0x7ff0000000000000, false, 9223372036854775808, 0, 0, 0, false,
      [9223372036854775808, M, M, M, M],
      [some (0, 1000, 0), some (0, 4611686018427387904, 0), some (0, 1000000000, 0)]),
    (0xfff0000000000000, true, 9223372036854775808, 0, 0, 0, true,
      [9223372036854775808, M, M, M, M],
      [some (0, -1000, 0), some (0, -4611686018427387904, 0), some (0, -1000000000, 0)]),
    (0xfff0000000000000, false, 9223372036854775808, 0, 0, 0, true,
      [9223372036854775808, M, M, M, M],
      [none, none, none]),
    (0x7fefffffffffffff, true, 9223372036854775808, 0, 0, 0, false,
      [9223372036854775808, M, M, M, M],
      [none, none, none]),
    (0x7fefffffffffffff, false, 9223372036854775808, 0, 0, 0, false,
      [9223372036854775808, M, M, M, M],
      [some (0, 1000, 0), some (0, 4611686018427387904, 0), some (0, 1000000000, 0)]),
    (0x3cb0000000000000, true, 1, 4503599627370495, 0, 52, false, [1, 1, 1025, 2048, 1],
      [some (1, 4503599627370495, 52), some (1, 4503599627370495, 52),
        some (1, 4503599627370495, 52)]),
    (0x3cb0000000000000, false, 1, 0, 0, 52, false, [0, 0, 1024, 2047, 0],
      [some (1, 0, 52), some (1, 0, 52), some (1, 0, 52)]),
    (0x3b40000000000000, true, 1, M, 2047, 75, false, [1, 1, 1, 1, 1],
      [none, none, none]),
    (0x3b40000000000000, false, 1, 0, 0, 75, false, [0, 0, 0, 0, 0],
      [none, none, none]),
    (0x3b3fffffffffffff, true, 9007199254740991, M, 9223372036854775807, 127, false,
      [1, 1, 1, 1, 1],
      [none, none, none]),
    (0x3b3fffffffffffff, false, 9007199254740991, 0, 0, 127, false, [0, 0, 0, 0, 0],
      [none, none, none]),
    (0x4340000000000001, true, 9007199254740994, 0, 0, 0, false, [9007199254740994, M, M, M, M],
      [some (9007199254740994, 0, 0), some (9007199254740994, 0, 0), none]),
    (0x4340000000000001, false, 9007199254740994, 0, 0, 0, false, [9007199254740994, M, M, M, M],
      [some (0, 1000, 0), some (9007199254740994, 0, 0), some (0, 1000000000, 0)]),
    (0xc340000000000001, true, 9007199254740994, 0, 0, 0, true, [9007199254740994, M, M, M, M],
      [some (0, -1000, 0), some (-9007199254740994, 0, 0), some (0, -1000000000, 0)]),
    (0xc340000000000001, false, 9007199254740994, 0, 0, 0, true, [9007199254740994, M, M, M, M],
      [some (-9007199254740994, 0, 0), some (-9007199254740994, 0, 0), none]),
    (0x41dfffffffc00000, true, 2147483647, 0, 0, 0, false, [2147483647, 26510685622215, M, M, M],
      [some (2147483647, 0, 0), some (2147483647, 0, 0), some (2147483647, 0, 0)]),
    (0x41dfffffffc00000, false, 2147483647, 0, 0, 0, false, [2147483647, 26510685622215, M, M, M],
      [some (0, 1000, 0), some (2147483647, 0, 0), some (0, 1000000000, 0)]),
    (0x3f50624dd2f1a9fc, true, 1152921504606847, 1152921504606846975, 0, 60, false,
      [1, 13, 4611686018427389, 9223372036854776, 3298534884],
      [some (1152921504606847, 1152921504606846975, 60),
        some (1152921504606847, 1152921504606846975, 60), none]),
    (0x3f50624dd2f1a9fc, false, 1152921504606847, 0, 0, 60, false,
      [0, 12, 4611686018427388, 9223372036854775, 3298534883],
      [some (1152921504606847, 0, 60), some (1152921504606847, 0, 60), none])
    ] : List (UInt64 × Bool × Nat × Nat × Nat × Nat × Bool × List Nat ×
      List (Option (Int × Int × Nat)))).all fun (x, lower, m, rl, rh, s, neg, sc, fs) ↦
    let e := Id.run (exactEnd ⟨x⟩ lower)
    e.m.toNat == m && e.rl.toNat == rl && e.rh.toNat == rh && e.s == s && e.neg == neg &&
      bs.map (fun b ↦ (exactScale b e).toNat) == sc &&
      hb.map (fun (h, bh) ↦ (endForm e lower h bh).map fun (M, C, sh) ↦ (M.toInt, C.toInt, sh)) ==
        fs

end Sieve

end Ratpoints

end
