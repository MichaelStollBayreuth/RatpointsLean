/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Constants

-- The `#guard` examples use the constants at compile time.
meta import Ratpoints.Model.Constants

/-!
# The set-up of a search

What ratpoints does with its input before the sieve, as far as the model has it: the refusals of a
search, each with the error of the program (`Ratpoints.Refusal`); the reversal check of
`find_points_work_1`, which refuses the binary form when the degree `d` of the polynomial is even
and `X ^ 2` divides the form (`c₀ = c₁ = 0`), and otherwise may reverse the polynomial, in three
cases, exchanging `x` and `z` in the binary form (`Ratpoints.Setup.reversal`); and the test whether
the coefficients are C `long`s (`Ratpoints.fitsLong`, `Ratpoints.Setup.useCLong`), which chooses the
path of the table of a prime (`Ratpoints.Sieve.examinePrime?`). `Ratpoints.findPoints` runs the
reversal check after the test of the leading zeros, with the switch of its options, and the search
that it runs on the polynomial handed on (`Ratpoints.searchPoints`) makes the test of the `long`s.
For the tests on the denominators (`Ratpoints.Sieve.denInfoTest`, `Ratpoints.Sieve.wordsTest`), the
C code computes the valuation of an integer at a prime, with its unit part, by repeated division
(`Ratpoints.Setup.valuation`), and for a polynomial of odd degree whose leading coefficient is not
`±1` it factors that coefficient over `2` and the odd primes of the table and lists its squarefree
divisors up to the largest denominator, with the slopes of a valuation test
(`Ratpoints.Setup.setupUs1`): the denominators of the points are such divisors times squares.

## Main definitions

* `Ratpoints.Refusal`: the refusals of a search.
* `Ratpoints.fitsLong`: the C `long`s.
* `Ratpoints.Setup.isSquare`: the squares as GMP decides them.
* `Ratpoints.Setup.reversal`: the reversal check.
* `Ratpoints.Setup.useCLong`: whether the coefficients are `long`s.
* `Ratpoints.Setup.valuation`: the valuation of an integer at a prime, with its unit part.
* `Ratpoints.Setup.factorLcf`, `Ratpoints.Setup.squarefreeDivisors`, `Ratpoints.Setup.slope`: the
  factorization of the leading coefficient over the table, its squarefree divisors, and the slopes
  of the valuation test.
* `Ratpoints.Setup.DenInfo`, `Ratpoints.Setup.setupUs1`: for odd degree, the factorization of the
  leading coefficient and its squarefree divisors, which restrict the denominators.
-/

@[expose] public section

namespace Ratpoints

/-- The refusals of a search, each with the number of the error with which the program `ratpoints`
refuses the input. The program itself refuses too many or too few coefficients and the height bound
`0`, before it calls the library; the library refuses a binary form that is not squarefree in the
set-up of the search: when the leading zeros of `n + 1` coefficients lower `⌈n / 2⌉`, in the
reversal check (`Ratpoints.Setup.reversal`) and with the remainder chain of the Sturm step
(`Ratpoints.Sturm.chain`). -/
inductive Refusal where
  /-- More than `Ratpoints.maxDegree + 1` coefficients: error 3. -/
  | tooManyCoefficients
  /-- Fewer than two coefficients: error 5. -/
  | tooFewCoefficients
  /-- The height bound `0`: error 4. -/
  | incorrectHeight
  /-- A binary form that is not squarefree: error 8. -/
  | notSquarefree
  deriving DecidableEq, Repr

/-- Whether the integer `a` is a C `long`, `-2 ^ 63 ≤ a < 2 ^ 63`, as `mpz_fits_slong_p` of GMP
decides it: ratpoints needs a `long` of 64 bits since version 3.0.0.

C: `rp-private.h:41-43`, `rp-private.h:47`

Deviation: the bounds of a `long` of 64 bits, fixed, where the C code does not compile unless an
`unsigned long` has exactly 64 bits. -/
def fitsLong (a : Int) : Bool := -2 ^ 63 ≤ a && a < 2 ^ 63

namespace Setup

/-- Whether `a` is a square, as `mpz_perfect_square_p` of GMP decides it: `0` and the squares of
the positive integers, so that no negative integer is a square. -/
def isSquare (a : Int) : Bool := 0 ≤ a && a.toNat.sqrt * a.toNat.sqrt == a.toNat

/-- The reversal check on the coefficients `c` of degree `d`, the leading zeros dropped, with the
switch `allow` of the reversal: the list that the search goes on with, its degree, and whether it is
reversed. If the switch is off, `c` itself. Otherwise, for even `d` with `c₀ = 0`, the refusal
`Ratpoints.Refusal.notSquarefree` if also `c₁ = 0`, since `X ^ 2` then divides the binary form, and
else the list `c_d, …, c₁, c₀` with the degree `d - 1` (case 1); for even `d` with `c_d` a square
and `c₀` not (`Ratpoints.Setup.isSquare`), the list `c_d, …, c₀` (case 2); for odd `d` with
`|c_d| ≠ 1`, `c₀ = 0` and `|c₁| = 1`, the list `c₀, c_d, …, c₁` (case 3); and otherwise `c` itself.
In each case the reversed list is the reflection of `c` in the even degree `d + d % 2` of the binary
form, so that its binary form is that of `c` with `x` and `z` exchanged
(`Ratpoints.Setup.binaryForm_eq_of_reversal_eq_ok`).

C: `find_points.c:4732-4803`

Deviation: a new list for the reversal in place, and nothing written back to the caller: the
reversed coefficients, the degree and the flag `RATPOINTS_REVERSED` are returned instead; the
switch for the test of the flags `RATPOINTS_NO_REVERSE` and `RATPOINTS_NO_REVERSE_AUTO`, so that
the check runs whenever the switch allows it, without `RATPOINTS_NO_REVERSE_AUTO`, which a search
region or a denominator range sets (stage H); the square test of `c_d` made here, where the C code
reads the flag `lcfsq` that the set-up computes before (line 4634), and no flag `lcfsq` for the
reversed list, which case 2 clears, since `Ratpoints.Sieve.pointsAtInfinity` tests the leading
coefficient of the list it is given; integers and their absolute values for the GMP integers, with
no scratch integers `work[0]` and `work[1]`; no output under `RATPOINTS_VERBOSE`. -/
def reversal (allow : Bool) (c : List Int) (d : Nat) : Except Refusal (List Int × Nat × Bool) :=
  if !allow then .ok (c, d, false)
  else if d % 2 = 0 then
    if c.getD 0 0 = 0 then
      if c.getD 1 0 = 0 then .error .notSquarefree
      else .ok ((c.take (d + 1)).reverse, d - 1, true)
    else if isSquare (c.getD d 0) && !isSquare (c.getD 0 0) then
      .ok ((c.take (d + 1)).reverse, d, true)
    else .ok (c, d, false)
  else if (c.getD d 0).natAbs ≠ 1 ∧ c.getD 0 0 = 0 ∧ (c.getD 1 0).natAbs = 1 then
    .ok (c.getD 0 0 :: ((c.take (d + 1)).drop 1).reverse, d, true)
  else .ok (c, d, false)

/-- Whether the coefficients `c₀, …, c_d` are all C `long`s (`Ratpoints.fitsLong`): the flag
`use_c_long`, with which the table of a prime reduces the coefficients on the path through `long`s,
by the helper `mod` of the C code (`Ratpoints.Sieve.modLong`), and otherwise on the path through
GMP integers (`Ratpoints.Sieve.examinePrime?`); on the first path the inputs of `mod` are `long`s
(`Ratpoints.Setup.fitsLong_getD_of_useCLong`).

C: `find_points.c:4599-4600`, `find_points.c:4814-4823`

Deviation: no array `c_long`: the coefficients stay integers, which `Ratpoints.Sieve.modLong` reads
as `long`s, as `mpz_get_si` gives them exactly when they fit; the flag is returned, for the `int`
that the loop sets, and the loop, which stops at the first coefficient that is not a `long`, is
`List.all`. -/
def useCLong (c : List Int) (d : Nat) : Bool :=
  (List.range (d + 1)).all fun i ↦ fitsLong (c.getD i 0)

/-- The valuation of the integer `n` at `p` and the unit part of `n` modulo `p`: for `n ≠ 0`, the
pair `(v, r)` with `p ^ v ∣ |n|`, `p ∤ |n| / p ^ v` and `r = (|n| / p ^ v) mod p`, by repeated
division with remainder; for `n = 0`, `(Ratpoints.veryBig, 0)`. For `p = 1` and `n ≠ 0` the loop
does not end, as in the C code.

C: `find_points.c:424-454`

Deviation: one function for `valuation` on GMP integers, with its scratch integer `vvv`, and
`valuation1` on `long`s, which gives `v` alone and is the first component; natural numbers for
`|n|`, the quotients and the remainders; the pair returned, for the remainder that `valuation`
stores through its pointer `r`. -/
def valuation (n : Int) (p : Nat) : Id (Nat × Nat) := do
  if n = 0 then return (veryBig, 0)
  let mut q := n.natAbs / p
  let mut rem := n.natAbs % p
  let mut v := 0
  while rem == 0 do
    v := v + 1
    rem := q % p
    q := q / p
  return (v, rem)

/-- What the valuation test of the divisor shape (`Ratpoints.Sieve.denInfoTest`) knows of a prime
`p` of the leading coefficient `c_d` of a polynomial of odd degree `d`: `p`, its valuation `val` in
`c_d`, and the slope, the least `n ≥ 1` with `(d - k) n > val - v_p(c_k)` for every `k < d`, with
`v_p(0) = Ratpoints.veryBig`. A denominator `b` with `v_p(b) ≥ slope` and `v_p(b) + val` odd carries
no point (`Ratpoints.Setup.DenInfo.excludes_eq_false_of_sq_eq`).

C: `find_points.c:155`

Deviation: natural numbers for the `int` fields, which the primes fit, a cofactor below the square
of a prime of the table among them (`Ratpoints.Setup.mul_self_lt_of_mem_primeTable`), and the
valuations and the slopes for coefficients below `2 ^ (2 ^ 31 - 1)`. -/
structure DenInfo where
  /-- The prime. -/
  p : Nat
  /-- Its valuation in the leading coefficient. -/
  val : Nat
  /-- The slope. -/
  slope : Nat
  deriving DecidableEq, Repr

/-- The factorization of `w ≥ 1` over `2` and the odd primes of `Ratpoints.primeTable`, as
`setup_us1` makes it, with the cofactor that it leaves: the power of `2` is divided off; then for
the odd primes `p` of the table in turn, while the cofactor is not `1`, a cofactor below `p ^ 2`,
which has no prime factor below `p` and so is a prime, is taken with the valuation `1` (when it is
a `long`, which it always is) and leaves the cofactor `1`, and otherwise `p` is divided off with its
valuation when it divides. The factorization is complete exactly when the cofactor is `1`: when the
part of `w` prime to `2 · 3 ⋯ 1019` is below `1021 ^ 2` or a power of `1021`.

C: `find_points.c:777-860`

Deviation: the valuations by `Ratpoints.Setup.valuation`, for `mpz_scan1` at `2` and for the loop of
divisions with remainder at the odd primes, the power then divided off at once; natural numbers for
the GMP integers `work[0]` and `work[1]`, the `long`s, and the `int` `p` with its square `p * p`
(line 800), which is below `2 ^ 31` (`Ratpoints.Setup.mul_self_lt_of_mem_primeTable`); a list of
pairs of natural numbers and the cofactor returned, for the `int` fields `p` and `val` of the
entries of `den_info` (they hold the primes, the cofactor below `p ^ 2` and, for coefficients below
`2 ^ (2 ^ 31 - 1)`, the valuations: `Ratpoints.Setup.DenInfo`), for their count, the terminating
zero and the integer `work[0]`; no output under `DEBUG`. -/
def factorLcf (w : Nat) : Id (List (Nat × Nat) × Nat) := do
  let mut w := w
  let mut fac : Array (Nat × Nat) := #[]
  let (v2, _) ← valuation w 2
  if 0 < v2 then
    fac := fac.push (2, v2)
    w := w / 2 ^ v2
  for p in primeTable do
    if w == 1 then break
    if w < p * p then
      if fitsLong w then
        fac := fac.push (w, 1)
        w := 1
      break
    let (v, _) ← valuation w p
    if 0 < v then
      fac := fac.push (p, v)
      w := w / p ^ v
  return (fac.toList, w)

/-- The squarefree divisors at most `bHigh` of a product of the distinct primes `ps`, as `setup_us1`
lists them: from `[1]`, for each prime `p` in turn, each divisor `x` found so far with
`x ≤ ⌊bHigh / p⌋` gives `x p`, appended in the order of the `x`; the list stops as soon as it has
`Ratpoints.maxDivisors` entries. So it lists the products at most `bHigh` of the subsets of the
primes in the order of binary counting, the first prime the lowest bit, unless it stops.

C: `find_points.c:864-880`

Deviation: a list, for the array `divisors` and its pointers `div`, `div0` and `div1`; natural
numbers for the `long`s, the products `x p` being formed only for `x ≤ ⌊bHigh / p⌋`, so that they
are at most `bHigh` and `long`s for a `long` `bHigh` (`Ratpoints.Setup.fitsLong_mul_of_le_div`). -/
def squarefreeDivisors (ps : List Nat) (bHigh : Nat) : Id (List Nat) := do
  let mut divs : Array Nat := #[1]
  for p in ps do
    let n := divs.size
    for i in [0:n] do
      if divs[i]! ≤ bHigh / p then divs := divs.push (divs[i]! * p)
      if maxDivisors ≤ divs.size then break
    if maxDivisors ≤ divs.size then break
  return divs.toList

/-- The slope of the valuation test of the divisor shape (`Ratpoints.Sieve.denInfoTest`) at the
prime `p` with the valuation `val` in the leading coefficient `c_d` of the polynomial of odd degree
`d` with the coefficient list `c`: the largest of `1` and the `⌈(1 + val - v_p(c_k)) / (d - k)⌉` for
`k = d - 1, …, 0`, with the valuations of `Ratpoints.Setup.valuation`, by the macro `CEIL`, which
rounds up for every sign: the least `n ≥ 1` with `(d - k) n > val - v_p(c_k)` for every `k < d`,
with `v_p(0) = Ratpoints.veryBig`, so that a zero coefficient imposes nothing when
`val ≤ Ratpoints.veryBig`.

C: `find_points.c:894-912`, `rp-private.h:87`

Deviation: integers for the `int`s, and the slope as a natural number; no output under `DEBUG`. -/
def slope (c : List Int) (d p val : Nat) : Id Nat := do
  let mut n : Int := 1
  for j in [0:d] do
    let k := d - 1 - j
    let (vk, _) ← valuation (c.getD k 0) p
    let t : Int := 1 + (val : Int) - vk
    let m : Int := if t ≤ 0 then -((-t) / ((d - k : Nat) : Int)) else 1 + (t - 1) / (d - k : Nat)
    if n < m then n := m
  return n.toNat

/-- For a polynomial of odd degree `d` with the coefficient list `c` and `|c_d| ≠ 1`, and the
largest denominator `bHigh`: the primes of `|c_d|` with their valuations and slopes
(`Ratpoints.Setup.DenInfo`, `Ratpoints.Setup.slope`) and the squarefree divisors of `c_d` at most
`bHigh` (`Ratpoints.Setup.squarefreeDivisors`), or `none` when the factorization over `2` and the
odd primes of the table is not complete (`Ratpoints.Setup.factorLcf`) or there are
`Ratpoints.maxDivisors` divisors or more. The denominators of the points are then these divisors
times squares, which the divisor shape of the loop over the denominators visits divisor by divisor
(`Ratpoints.Sieve.squares1Dens`).

C: `find_points.c:766-776`, `find_points.c:863`, `find_points.c:881-893`, `find_points.c:914-935`

Deviation: the leading coefficient read from the list, for the integer `work[0]` that the caller
sets to `|c_d|` (lines 4911-4912); lists, for the arrays `den_info` and `divisors` of the arguments
with their terminating zeros; `none` for a factorization that is not complete or too many divisors,
where `setup_us1` leaves the flag `RATPOINTS_USE_SQUARES1` clear, and the lists returned, where it
sets the flag; no output under `DEBUG`. -/
def setupUs1 (c : List Int) (d bHigh : Nat) : Id (Option (List DenInfo × List Nat)) := do
  let (fac, w) ← factorLcf (c.getD d 0).natAbs
  if w != 1 then return none
  let divs ← squarefreeDivisors (fac.map (·.1)) bHigh
  if maxDivisors ≤ divs.length then return none
  let mut info : Array DenInfo := #[]
  for (p, val) in fac do
    info := info.push ⟨p, val, ← slope c d p val⟩
  return some (info.toList, divs)

/-! ### Examples

What ratpoints 3.1.1 does at the pinned commit: with `-v` it says whether it reverses and in which
case, and prints the coefficients of case 3; `-k` switches the reversal off; and
`ratpoints '0 0 1 1 1' 5 -q -s`, without the Sturm step, which would refuse the form too, ends with
error 8, which `-s -k` does not. The test of the `long`s is checked at the ends of their range. The
valuation is checked at 2, 3 and 5 and at 0; the factorizations over the table with their cofactors,
the squarefree divisors and the slopes against what the build of ratpoints with `DEBUG` prints with
`-v`, a factorization that is not complete among them; and the boundary of `Ratpoints.maxDivisors`
divisors (511 at the height 2066, 512 at 2067). -/

#guard [0, 1, 4, 9, 2 ^ 126].all isSquare && !([2, 3, -1, -4, 2 ^ 127].any isSquare)

-- Case 1, for `0 1 0 0 4` and `0 -3 -5`; case 2, for `-1 0 9`; and case 3, for `0 1 0 2` and for
-- `0 1 0 2 0`, its leading zero dropped.
#guard (reversal true [0, 1, 0, 0, 4] 4).toOption == some ([4, 0, 0, 1, 0], 3, true) &&
  (reversal true [0, -3, -5] 2).toOption == some ([-5, -3, 0], 1, true)
#guard (reversal true [-1, 0, 9] 2).toOption == some ([9, 0, -1], 2, true)
#guard (reversal true [0, 1, 0, 2] 3).toOption == some ([0, 2, 0, 1], 3, true) &&
  (reversal true [0, 1, 0, 2, 0] 3).toOption == some ([0, 2, 0, 1], 3, true)

-- `c₀ = c₁ = 0` for even `d`: the refusal, unless the switch is off.
#guard reversal true [0, 0, 1, 1, 1] 4 matches .error .notSquarefree
#guard (reversal false [0, 0, 1, 1, 1] 4).toOption == some ([0, 0, 1, 1, 1], 4, false)

-- The switch off, and lists that meet no case: `c₀` a square, `c_d` not, `|c₁| ≠ 1`, `|c_d| = 1`,
-- `c₀ ≠ 0`.
#guard (reversal false [-1, 0, 9] 2).toOption == some ([-1, 0, 9], 2, false)
#guard ([([4, 0, 9], 2), ([-1, 0, -9], 2), ([0, 2, 0, 3], 3), ([0, 1, 0, -1], 3),
    ([-2, 1, 0, 2], 3), ([1, 2, 3, 4, 5, 6, 7], 6)] : List (List Int × Nat)).all fun (c, d) ↦
  (reversal true c d).toOption == some (c, d, false)

-- The `long`s: `-2 ^ 63` and `2 ^ 63 - 1` are, `-2 ^ 63 - 1` and `2 ^ 63` are not; and of the
-- coefficients, only `c₀, …, c_d` count, an entry beyond the list counting as `0`.
#guard fitsLong (-2 ^ 63) && fitsLong (2 ^ 63 - 1) && !fitsLong (-2 ^ 63 - 1) && !fitsLong (2 ^ 63)
#guard useCLong [2 ^ 63 - 1, 0, -2 ^ 63] 2 && !useCLong [1, 2 ^ 63, 1] 2 &&
  !useCLong [1, 1, -2 ^ 63 - 1] 2 && useCLong [1, 1, 2 ^ 70] 1 && useCLong [1, -1] 3

-- The valuation and the unit part: `v_3(-162) = 4` with `162 / 81 = 2`, `v_5(7) = 0` with
-- `7 mod 5`, `v_2(2 ^ 70) = 70`, and `0`, whose valuation is `veryBig`.
#guard [Id.run (valuation (-162) 3), Id.run (valuation 7 5), Id.run (valuation (2 ^ 70) 2),
    Id.run (valuation 0 7)] == [(4, 2), (0, 2), (70, 1), (veryBig, 0)]

-- The factorizations over the table with their cofactors: `30`; `1021 · 1031`, which leaves the
-- cofactor 1031; `2 · 1031`, whose cofactor 1031 is taken as a prime at 37, since `1031 < 37 ^ 2`;
-- the divisors at most 100 and 12 of `2 · 3 · 5`; and the slopes of `1 0 0 32` at 2 and of
-- `3 5 0 96` at 2 and 3.
#guard Id.run (factorLcf 30) == ([(2, 1), (3, 1), (5, 1)], 1) &&
  Id.run (factorLcf 1052651) == ([(1021, 1)], 1031) &&
  Id.run (factorLcf 2062) == ([(2, 1), (1031, 1)], 1) &&
  Id.run (squarefreeDivisors [2, 3, 5] 100) == [1, 2, 3, 6, 5, 10, 15, 30] &&
  Id.run (squarefreeDivisors [2, 3, 5] 12) == [1, 2, 3, 6, 5, 10] &&
  [Id.run (slope [1, 0, 0, 32] 3 2 5), Id.run (slope [3, 5, 0, 96] 3 2 5),
    Id.run (slope [3, 5, 0, 96] 3 3 1)] == [2, 3, 1]

-- The factorizations, slopes and divisors that the build of ratpoints with `DEBUG` and `-v` print
-- (with `-k`): `1 0 0 30` at the height 100, `1 0 0 32` at 100 (slope 2), `3 5 0 96` at 50 (slope
-- 3), `7 0 18 0 0 250` at 200, `0 3 -2991 -2062` at 1300, whose cofactor 1031 is a prime beyond the
-- table, and `1 0 0 1052651`, the product `1021 · 1031`, which it does not factor completely.
#guard Id.run (setupUs1 [1, 0, 0, 30] 3 100) ==
    some ([⟨2, 1, 1⟩, ⟨3, 1, 1⟩, ⟨5, 1, 1⟩], [1, 2, 3, 6, 5, 10, 15, 30]) &&
  Id.run (setupUs1 [1, 0, 0, 32] 3 100) == some ([⟨2, 5, 2⟩], [1, 2]) &&
  Id.run (setupUs1 [3, 5, 0, 96] 3 50) == some ([⟨2, 5, 3⟩, ⟨3, 1, 1⟩], [1, 2, 3, 6]) &&
  Id.run (setupUs1 [7, 0, 18, 0, 0, 250] 5 200) == some ([⟨2, 1, 1⟩, ⟨5, 3, 2⟩], [1, 2, 5, 10]) &&
  Id.run (setupUs1 [0, 3, -2991, -2062] 3 1300) == some ([⟨2, 1, 2⟩, ⟨1031, 1, 2⟩], [1, 2, 1031]) &&
  Id.run (setupUs1 [1, 0, 0, 1052651] 3 100) == none

-- The leading coefficient `2 · 3 ⋯ 97`, the product of the 25 primes below 100: 511 squarefree
-- divisors at most 2066 and 512 at most 2067, so that ratpoints visits the divisor shape at the
-- height 2066 and every denominator at 2067; and the divisors at most 30 of `30 = 2 · 3 · 5`.
#guard (Id.run (setupUs1 [1, 0, 0, 2305567963945518424753102147331756070] 3 2066)).map
    (·.2.length) == some 511 &&
  (Id.run (setupUs1 [1, 0, 0, 2305567963945518424753102147331756070] 3 2067)).isNone &&
  (Id.run (setupUs1 [1, 0, 0, 30] 3 12)).map (·.2) == some [1, 2, 3, 6, 5, 10]

end Setup

end Ratpoints

end
