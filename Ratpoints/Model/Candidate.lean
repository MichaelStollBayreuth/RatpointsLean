/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.BruteForce
public import Ratpoints.Model.Constants
public import Ratpoints.Model.Tables

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.BruteForce
meta import Ratpoints.Model.Constants
meta import Ratpoints.Model.Tables

/-!
# The test of a candidate and the exact check

The components of the sieve that take one numerator at a time, each in its place in the C function
`find_points_work_1`: the test of a candidate that survives the first two stages of the sieve, the
test for common factors by the binary algorithm on the 64-bit words of the C code
(`Ratpoints.Sieve.relprime`), with the lowest set bit of a word (`Ratpoints.Sieve.ctz`), and the
third stage, one numerator at a time against the tables of its primes (`Ratpoints.Sieve.stage3`,
`Ratpoints.Sieve.fillChecks`), and the exact check (`Ratpoints.Sieve.accepted`,
`Ratpoints.Sieve.checkPoint`), whose reference is the check of a numerator
(`Ratpoints.Sieve.checkNum`); the point of the caller's curve for a point of a reversed curve
(`Ratpoints.Sieve.swapPoint`); and the points at infinity (`Ratpoints.Sieve.pointsAtInfinity`). The
third stage removes only numerators that the rows of its primes would remove, or that have a common
factor with the denominator, so that the test of a candidate and the exact check give the points of
the check of the reference for the numerators that survive the rows of these primes. The exact check
and the points at infinity deliver the points mapped by `Ratpoints.Sieve.swapPoint` when their flag
of the reversal is set, and so does the check of the reference. The sieve that calls these
components, on the bit arrays of 64-bit words, is in `Ratpoints.Model.Sieve`; the tables of the
primes and the sieve entries of the moduli, with the rows of a denominator, are in
`Ratpoints.Model.Tables`.

## Main definitions

* `Ratpoints.Sieve.swapPoint`: the point of the caller's curve for a point of the reversed curve.
* `Ratpoints.Sieve.ctz`: the lowest set bit of a word.
* `Ratpoints.Sieve.relprimeOdd`, `Ratpoints.Sieve.relprime`: the test for common factors of a
  numerator and a denominator by the binary algorithm on the 64-bit words of the C code.
* `Ratpoints.Sieve.CheckSpec`, `Ratpoints.Sieve.checkOf`, `Ratpoints.Sieve.fillChecks`,
  `Ratpoints.Sieve.CheckSpec.index`, `Ratpoints.Sieve.stage3`: the third stage, what it needs of
  its primes for a denominator, and its test of one numerator.
* `Ratpoints.Sieve.accepted`, `Ratpoints.Sieve.checkPoint`: the test of a candidate, the test for
  common factors and the third stage, and the exact check of one numerator, its points mapped by
  `Ratpoints.Sieve.swapPoint` when the flag of the reversal is set.
* `Ratpoints.Sieve.checkNum`: the check of the reference, the test for common factors by the gcd
  and the exact check of one numerator, its points mapped by `Ratpoints.Sieve.swapPoint` when the
  flag of the reversal is set.
* `Ratpoints.Sieve.pointsAtInfinity`: the points at infinity, mapped by `Ratpoints.Sieve.swapPoint`
  when the flag of the reversal is set.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The points of a reversed search -/

/-- The point of the caller's curve for the point `(a, y, b)` of the reversed curve: `(b, y, a)` for
`a ≥ 0` and `(-b, y, -a)` for `a < 0`. After the reversal check has reversed the polynomial
(`Ratpoints.Setup.reversal`), the C code delivers the mapped points: the exact check maps each point
that it finds by this map, and the points at infinity take the candidate `(0, 1)` in place of
`(1, 0)`, which gives the image of `(1, y, 0)`; the two components deliver the mapped points when
their flag of the reversal is set (`Ratpoints.Sieve.checkPoint`,
`Ratpoints.Sieve.pointsAtInfinity`), and so does the check of the reference
(`Ratpoints.Sieve.checkNum`). It maps the normalized points of height at most `H` of the reversed
curve one to one onto those of the caller's curve (`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`).
Its negations `-b` and `-a` stay in the range of a `long`, since `|a| ≤ H`, `1 ≤ b ≤ H` and
`H < 2 ^ 63` (`Ratpoints.fitsLong_neg`). -/
def swapPoint (q : Int × Int × Int) : Int × Int × Int :=
  if 0 ≤ q.1 then (q.2.2, q.2.1, q.1) else (-q.2.2, q.2.1, -q.1)

/-! ### The lowest set bit -/

/-- The position of the lowest set bit of a word `w ≠ 0`: `w` is shifted right while its lowest
bit is clear, and the steps are counted. On `0` the loop does not end, as in the C code.

C: `rp-private.h:429-444`

Deviation: the loop for a compiler without the builtin, where gcc and clang take
`__builtin_ctzl`. -/
def ctz (w : UInt64) : Id Nat := do
  let mut w := w
  let mut t := 0
  while w &&& 1 == 0 do
    w := w >>> 1
    t := t + 1
  return t

/-! ### The test for common factors -/

/-- Whether the odd positive words `m` and `n`, `long`s of the C code, are coprime, by the loop of
the binary algorithm of `relprime`: while `n ≠ m`, with the difference `d = m - n` and its mask
`msk = d >>> 63`, `-1` for `d < 0` and `0` otherwise, `n` becomes `n + (d &&& msk)`, the smaller of
the two, and `m` the word `(d ^^^ msk) - msk`, the absolute difference `|m - n|`, which is even and
nonzero, shifted right by its number of trailing zeros (`Ratpoints.Sieve.ctz`, on the word read as
unsigned), its odd part. The two stay odd and positive, their gcd stays the same and their sum
decreases, so that the loop ends at `m = n = gcd(m, n)`, and the numbers are coprime when that is
`1`; no operation leaves the range of a `long` (`Ratpoints.Sieve.relprimeOdd_spec`).

C: `sift.c:328-342`

Deviation: `Int64` for `long`, `toUInt64` for the cast to `unsigned long`, and the `toInt64` of the
count for the `long` that `RP_CTZL` returns; `63` for `LONG_LENGTH - 1`; `Int64` in two's
complement, the representation of the negative `long`s on which the and `d &&& msk` and the
exclusive or `d ^^^ msk` of the step act, and `>>>` on `Int64` the arithmetic shift, for the `>>` of
a negative `long`, both of which the C standard leaves to the implementation (the representation
before C23) and gcc defines so; the lowest set bit by the loop of `RP_CTZL` for a compiler without
the builtin (`Ratpoints.Sieve.ctz`), where gcc and clang take `__builtin_ctzl`; the loop a function
of its own, for the end of the function `relprime`. -/
def relprimeOdd (m n : Int64) : Id Bool := do
  let mut m := m
  let mut n := n
  while n != m do
    let d := m - n
    let msk := d >>> 63
    n := n + (d &&& msk)
    let d := (d ^^^ msk) - msk
    m := d >>> (← ctz d.toUInt64).toInt64
  return m == 1

/-- Whether the words `m` and `n`, the `long`s of the C code for a numerator and a denominator
`n ≥ 1`, are coprime, by the binary algorithm of `relprime`: for `m = 0`, whether `n = 1`; otherwise
`m` replaced by `-m` when it is negative, false when `m` and `n` are both even, and else whether
their odd parts are coprime (`Ratpoints.Sieve.relprimeOdd`), each word shifted right by its number
of trailing zeros (`Ratpoints.Sieve.ctz`, on the word read as unsigned), `m` only when it is even.
It is `gcd(m, n) = 1` for `m > -2 ^ 63` and `n ≥ 1`, and no operation leaves the range of a `long`
(`Ratpoints.Sieve.relprime_spec`); for `n = 0` it is that too when `m` is `0` or even, and for an
odd `m` the loop of `Ratpoints.Sieve.ctz` on `0` does not end, as the fallback loop of `RP_CTZL`
does not.

C: `sift.c:318-327`, `sift.c:343`

Deviation: `Int64` for `long`, `toUInt64` for the cast to `unsigned long`, and the `toInt64` of the
count for the `long` that `RP_CTZL` returns; the negation of a negative `m` as a conditional
expression, for the statement `if(m < 0)`; for `m = -2 ^ 63`, whose negation overflows in the C
code, the model wraps; the contract excludes that value, which the search never passes, its
numerators being at most `H < 2 ^ 63` in absolute value; `m &&& 1 == 0` for `!(m & 1)`; the lowest
set bit by the loop of `RP_CTZL` for a compiler without the builtin (`Ratpoints.Sieve.ctz`), where
gcc and clang take `__builtin_ctzl`; the builtin is undefined on `0` and the loop does not end
there, which the contract excludes, with `n ≥ 1` and `m ≠ 0` at the calls; the loop of the binary
algorithm a function of its own (`Ratpoints.Sieve.relprimeOdd`); a Boolean for the `int`. -/
def relprime (m n : Int64) : Id Bool := do
  if m == 0 then return n == 1
  let mut m := if m < 0 then -m else m
  if m &&& 1 == 0 then
    if n &&& 1 == 0 then return false
    m := m >>> (← ctz m.toUInt64).toInt64
  relprimeOdd m (n >>> (← ctz n.toUInt64).toInt64)

/-! ### The third stage -/

/-- What the third stage of the sieve needs to test a numerator against one of its primes, for the
denominator at hand (`Ratpoints.Sieve.checkOf`): the prime `p`, the inverse `binv` of the
denominator modulo `p`, `0` when `p` divides it, the bias `bias`, the multiple of `p` by which the
stage shifts the value it reduces, `0` when it divides instead, the reciprocal `magic` of `p`, and
the table `isFSquare` of the prime, entry `x < p` whether `f(x)` is a square modulo `p`.

C: `rp-private.h:465-466`

Deviation: natural numbers for the `long`s and the `unsigned long`; the table an array of Booleans,
for the pointer to the integers `is_f_square` of the sieve entry of the prime. -/
structure CheckSpec where
  /-- The prime. -/
  p : Nat
  /-- The inverse of the denominator modulo `p`, `0` when `p` divides the denominator. -/
  binv : Nat
  /-- The multiple of `p` by which the third stage shifts the value it reduces, `0` when it
  divides. -/
  bias : Nat
  /-- The reciprocal of `p` (`Ratpoints.Sieve.magic`). -/
  magic : Nat
  /-- For each residue `x` modulo `p`, whether `f(x)` is a square modulo `p`. -/
  isFSquare : Array Bool

/-- What the third stage needs of the sieve entry `e` of a prime `p`, whose single factor is its
table `t`, for the denominator `b`, the height bound `H` and the reciprocal `mg` of `p` that the
array `magics` holds at the position of the entry (`Ratpoints.Sieve.CheckSpec`): `p`; the inverse
`t.inverses[r]` of the residue `r = b mod p`, computed by a multiplication with `mg`
(`Ratpoints.Sieve.mulMod`) for `b ≤ Ratpoints.mulModLimit` and by `%` above, or `0` for `r = 0`;
the bias `p H` when `2 p H < Ratpoints.stage3Limit` and `0` otherwise; the reciprocal of the entry;
and the table of `t`. With the reciprocal `Ratpoints.Sieve.magic p` for `mg`, as the array of
`Ratpoints.sievingInfo` holds it, the residue is `b mod p` for `p ≤ 2 ^ 32`
(`Ratpoints.Sieve.binv_checkOf`). An entry of another shape, which the third stage of well-formed
parameters never holds (`Ratpoints.Params.WF`), gets the inverse `0`, so that the stage skips it, as
it skips a prime that divides `b`.

C: `sift.c:414-428`

Deviation: the entry of one prime, for one pass of the loop of `fill_checks`
(`Ratpoints.Sieve.fillChecks`), with the reciprocal `magics[n]` as the argument `mg`; the fields of
the prime read from its table, the single factor of its sieve entry, where the C code reads them
from the sieve entry of the prime, which has them itself; the exact comparison `2 p H < stage3Limit`
of natural numbers, for the comparison of the `double` product `p · 2.0 · H` with the `double`
`RP_STAGE3_LIMIT`, which has the same outcome for every `H < 2 ^ 63`, the product being exact below
`2 ^ 53` and rounded monotonically above, beyond the bound; natural numbers for the `long`s, the
product `p H` computed only when it is below `2 ^ 31`; the inverse `0` for an entry of another
shape, for which the C code has no case. -/
def checkOf (b H : Nat) (e : SieveEntry) (mg : Nat) : CheckSpec :=
  match e.factors with
  | [.prime t] =>
    let p := e.p
    let bp := if b ≤ mulModLimit then mulMod b p mg else b % p
    { p, binv := if bp = 0 then 0 else t.inverses[bp]!,
      bias := if 2 * p * H < stage3Limit then p * H else 0, magic := e.magic,
      isFSquare := t.isFSquare }
  | _ => { p := e.p, binv := 0, bias := 0, magic := e.magic, isFSquare := #[] }

/-- What the third stage needs for the denominator `b` and the height bound `H` from the sieve
entries `es` of its primes with the reciprocals `mgs` of their moduli, in their order
(`Ratpoints.Sieve.checkOf`). The sieve of one denominator makes it a thunk for each denominator
(`Ratpoints.Sieve.sift`), which the third stage forces when the first numerator of the denominator
reaches it (`Ratpoints.Sieve.accepted`).

C: `sift.c:405-413`, `sift.c:429-431`

Deviation: a list, made by a map over the entries of the third stage and their reciprocals
(`List.zipWith`), for the loop over the positions `sp2, …, sp3 - 1` of `sieve_list` and `magics`
that fills the array `checks` of the sieving thread; no bound `RATPOINTS_NUM_PRIMES` on its length
(`stage3_list` and the arrays of the pool, `find_points.c:339`, `find_points.c:4372`), which
ratpoints never reaches since each entry of `sieve_list` owns its own prime
(`find_points.c:329-331`), where well-formed parameters may repeat a prime; the thunk that the sieve
of one denominator makes of it (`Ratpoints.Sieve.sift`), for the flag `stage3_filled` of the sieving
thread, which `sift` clears and `fill_checks` sets. -/
def fillChecks (b H : Nat) (es : List SieveEntry) (mgs : List Nat) : List CheckSpec :=
  List.zipWith (checkOf b H) es mgs

/-- The residue `a b⁻¹ mod p` at which the third stage reads the table of the prime `p` of `cs` for
the numerator `a`: with the bias `p H ≠ 0`, the value `a binv + p H`, a natural number below
`2 p H < 2 ^ 32` for `|a| ≤ H` and `binv < p`, reduced by a multiplication with the reciprocal of
`p` (`Ratpoints.Sieve.mulMod`); without it, the remainder of `a` by C's division, which truncates
(`Int.tmod`), plus `p` if it is negative, times `binv`, and the remainder of that by `p`.

C: `sift.c:302-308`

Deviation: a function of its own for the lines of the loop of `stage3` that compute the residue;
integers for the `long`s, `Int.tmod` for C's `%`, which truncates, and the value made a natural
number, for the `long` that `RP_MULMOD` converts to an `unsigned long`, and for the `long` residue,
both non-negative; the obligations that the `long`s `a binv + bias` and `am binv` stay in range left
to lemmas: for `|a| ≤ H` and `binv < p`, `a binv + p H` lies between `H` and `2 p H - H`
(`Ratpoints.Sieve.le_mul_add_natCast_mul`,
`Ratpoints.Sieve.mul_add_natCast_mul_le_two_mul_mul_sub`), below `2 ^ 32` with the bias, and
`am binv < p ^ 2` (`Ratpoints.Sieve.toNat_emod_mul_lt_sq`). -/
def CheckSpec.index (cs : CheckSpec) (a : Int) : Nat :=
  if cs.bias ≠ 0 then mulMod (a * cs.binv + cs.bias).toNat cs.p cs.magic
  else
    let am := a.tmod cs.p
    let am := if am < 0 then am + cs.p else am
    ((am * cs.binv).tmod cs.p).toNat

/-- The third stage for the numerator `a`: for each prime of `checks` in turn
(`Ratpoints.Sieve.CheckSpec`), skipped when it divides the denominator (`binv = 0`), `a` is rejected
when the table of the prime says that `f` is not a square modulo `p` at the residue `a b⁻¹ mod p`
(`Ratpoints.Sieve.CheckSpec.index`); the numerator passes when no prime rejects it. For a numerator
prime to the denominator `b` with `|a| ≤ H`, and the sieve entries of primes `1 < p ≤ 2 ^ 32` with
their tables and reciprocals (`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`,
`Ratpoints.Sieve.fillChecks`), it is the test of the rows of these entries
(`Ratpoints.Sieve.survives`): a prime that divides `b` admits every numerator prime to `b`
(`Ratpoints.Sieve.run_stage3_fillChecks`). A numerator with a common factor would pass the primes
that do not divide `b` too, and the stage runs after the test for common factors
(`Ratpoints.Sieve.accepted`).

C: `sift.c:291-301`, `sift.c:309-312`

Deviation: a list for the array `csp` and its length `n`; the residue computed by
`Ratpoints.Sieve.CheckSpec.index`; a Boolean for the `int`. -/
def stage3 (a : Int) (checks : List CheckSpec) : Id Bool := do
  for cs in checks do
    if cs.binv = 0 then continue
    if !cs.isFSquare[cs.index a]! then return false
  return true

/-! ### The test of a candidate and the exact check -/

/-- Whether the numerator `a` goes on to the exact check for the denominator `b ≥ 1`: it is prime to
`b` (`Ratpoints.Sieve.relprime`, on the words of `a` and `b`) and passes the third stage
(`Ratpoints.Sieve.stage3`) with `checks`, the thunk of what that stage needs for `b`
(`Ratpoints.Sieve.fillChecks`), which is forced when the first numerator of `b` gets this far. The
walk through the set bits of a word calls it (`Ratpoints.Sieve.walkWord`).

C: `sift.c:438-446`

Deviation: the integer `a` and the natural number `b` of the loops of the model converted to the
64-bit words that they are in the C code (`Int.toInt64`, `Nat.toInt64`), which is exact for
`|a| < 2 ^ 63` and `b < 2 ^ 63`, as the numerators and the denominators of a search with a height
bound below `2 ^ 63` are (`Ratpoints.findPoints`); the thunk `checks`, which the sieve of one
denominator makes for each denominator (`Ratpoints.Sieve.sift`), for the array of the sieving thread
and its flag `stage3_filled`, which `accepted` tests before it fills the array when the stage has
primes (`n ≠ 0`); no counts of the numerators that pass the test for common factors and the third
stage (`n_coprime`, `n_checks`), which ratpoints reads to correct the moduli between the blocks of
the run (stage I); a Boolean for the `int`. -/
def accepted (a : Int) (b : Nat) (checks : Thunk (List CheckSpec)) : Id Bool := do
  if !(← relprime a.toInt64 b.toInt64) then return false
  stage3 a checks.get

/-- The points of the numerator `a` over the denominator `b` by the exact check, each mapped by
`Ratpoints.Sieve.swapPoint` when the flag `rev` of the reversal is set: `(a, y, b)` and, for
`y ≠ 0`, `(a, -y, b)` when `v = y ^ 2` with `y ≥ 0`, for the value `v` of Horner's rule in `a` on
the products `w`, times `b` if the degree `d` is odd. For the products `w` of the coefficients `cₖ`
with the powers `b^(d - k)` (`Ratpoints.BruteForce.scaledCoeffs`), `v` is the value `F(a, b)` of the
binary form. For a numerator prime to `b` it is the check of the reference
(`Ratpoints.Sieve.checkNum`) with the factor `b` for odd `d` and `1` for even `d`. The walk through
the set bits of a word calls it (`Ratpoints.Sieve.walkWord`).

C: `sift.c:202-205`, `find_points.c:3122`, `find_points.c:5250-5338`, `rp-private.h:576`,
`rp-private.h:596-597`

Deviation: the products `w` as a thunk, which the sieve of one denominator makes for each
denominator (`Ratpoints.Sieve.sift`) and which is forced when the first numerator of `b` reaches the
check, for the array `work` of the sieving thread, which `worker_init` gives it, and its flag
`compute_bc`, which `sift` sets and `_ratpoints_check_point` clears when it computes the products;
the degree `d` and the flag `rev` as arguments, handed down from `Ratpoints.Sieve.sieveRun` through
the components that call the check, for the degree and the bit `RATPOINTS_REVERSED` of the flags of
the search, which `_ratpoints_check_point` reads through its worker (`args->degree`, `args->flags`);
a list of points, for the callback `process` and for the count of points that
`_ratpoints_check_point` returns, with no stop that `process` may request, and no `RATPOINTS_NO_Y`
and no `RATPOINTS_NO_CHECK` (stage G); integers for the `long`s `a` and `b` (the negations of
`Ratpoints.Sieve.swapPoint` stay `long`s by `Ratpoints.fitsLong_neg`); no measurements of the time
of the check and of its products (`RP_CHECK`, `RP_BC_TIC`, `RP_BC_TOC` under `RP_PHASE_TIMING`), and
no output under `DEBUG`. -/
def checkPoint (w : Thunk (List Int)) (d : Nat) (b : Int) (rev : Bool) (a : Int) :
    List (Int × Int × Int) :=
  let pts := BruteForce.pointsAbove a b (BruteForce.horner w.get a * if d % 2 = 1 then b else 1)
  if rev then pts.map swapPoint else pts

/-- The points of the numerator `a` over the denominator `b`, as the brute-force reference checks it
(`Ratpoints.BruteForce.pointsOfDen`), each mapped by `Ratpoints.Sieve.swapPoint` when the flag `rev`
of the reversal is set: none when `a` and `b` have a common factor, and otherwise `(a, y, b)` and,
for `y ≠ 0`, `(a, -y, b)` when `v = y ^ 2` with `y ≥ 0`, for the value `v` of Horner's rule in `a`
on `w`, times `f`. For the products `w` of the coefficients `cₖ` with the powers `b^(d - k)`
(`Ratpoints.BruteForce.scaledCoeffs`), and `f = b` for odd `d` and `f = 1` for even `d`, `v` is the
value `F(a, b)` of the binary form, and these are the points of the exact check of the degree `d`
(`Ratpoints.Sieve.checkPoint`). So the check with the flag set gives the points of the check without
it, mapped (`Ratpoints.Sieve.checkNum_eq_map`), which after a reversal are points of the caller's
curve. It is the reference of the test of a candidate and the exact check
(`Ratpoints.Sieve.accepted`, `Ratpoints.Sieve.checkPoint`), which test for common factors by the
binary algorithm (`Ratpoints.Sieve.relprime`) and run the third stage before the exact check, and
give the same points for the numerators that the rows of the primes of the third stage admit
(`Ratpoints.Sieve.acceptedPoints_eq_ite`). -/
def checkNum (w : List Int) (f b : Int) (rev : Bool) (a : Int) : List (Int × Int × Int) :=
  if Int.gcd a b = 1 then
    let pts := BruteForce.pointsAbove a b (BruteForce.horner w a * f)
    if rev then pts.map swapPoint else pts
  else []

/-! ### The points at infinity -/

/-- The points at infinity of the polynomial of degree `d` with the coefficient list `c`, for the
flag `rev` of the reversal: for the candidate `(a, b) = (1, 0)`, or `(0, 1)` when `rev` is set, the
point `(a, 0, b)` for odd `d`; for even `d`, `(a, s, b)` and `(a, -s, b)` when `c_d = s ^ 2` with
`s > 0`, `(a, 0, b)` when `c_d = 0`, and none when `c_d` is not a square. With the flag clear these
are the points of the candidate `(1, 0)` of the brute-force reference
(`Ratpoints.Sieve.pointsAtInfinity_eq_pointsOfDen`), and with the flag set the same points mapped by
`Ratpoints.Sieve.swapPoint` (`Ratpoints.Sieve.pointsAtInfinity_eq_map`): after a reversal, the
points `(0, y, 1)` of the caller's curve.

C: `find_points.c:4634`, `find_points.c:4894-4899`, `find_points.c:5068-5105`

Deviation: the flag `rev` as an argument, for the bit `RATPOINTS_REVERSED` of the flags of the
search (`args->flags`); a list of points for the callback `process`, with no stop it may request, no
`RATPOINTS_NO_Y` and no `RATPOINTS_NO_CHECK` (stage G), and no output under `RATPOINTS_VERBOSE` or
`DEBUG`; the square test of `c_d` and the decision whether there are points at infinity are made on
the list that it is given, after the reversal check, when the points are delivered, where the C code
computes `lcfsq` before the check (line 4634), which clears it when it reverses a polynomial of even
degree and leaves it, unread, with the odd degree of the other reversals, and sets `point_at_infty`
before the exits of the search (lines 4894-4899); the case `c_d = 0`, that of the zero polynomial,
which ratpoints refuses before it gets here, gives the one point `(a, 0, b)`, which the cited lines,
delivering `-y` without a test `y ≠ 0`, would deliver twice. -/
def pointsAtInfinity (c : List Int) (d : Nat) (rev : Bool) : List (Int × Int × Int) :=
  let a : Int := if rev then 0 else 1
  let b : Int := if rev then 1 else 0
  if d % 2 = 1 then [(a, 0, b)] else BruteForce.pointsAbove a b (c.getD d 0)

/-! ### Examples -/

-- The sieve entries of the examples have the bias, the inverse of `rbaLength` and the inverses of
-- the strides `0`, `0` and the empty array, which `[k]!` reads as `0`: fields that only the packing
-- of the numerators reads, the row offsets (`Ratpoints.Sieve.classOffsets`) the first two and the
-- residues of `fill_bp_list` (stage F) the third.

-- The points of a reversed search: `ratpoints '-1 0 9' 10 -q` reverses the polynomial to `9 0 -1`
-- and prints the points of the brute-force reference of `y ^ 2 = 9 z ^ 2 - x ^ 2`, in its order,
-- each mapped, `(1 : 3 : 0)` for `(0 : 3 : 1)` among them; so do `ratpoints '0 1 0 0 4' 10 -q` and
-- `ratpoints '0 1 0 2' 10 -q`, which reverse the polynomials to `4 0 0 1 0` and `0 2 0 1`.
#guard swapPoint (2, 5, 3) == (3, 5, 2) && swapPoint (-2, 5, 3) == (-3, 5, 2) &&
  swapPoint (0, 3, 1) == (1, 3, 0) && swapPoint (1, 3, 0) == (0, 3, 1)
#guard (bruteForce [9, 0, -1] 10).map swapPoint ==
    [(-1, 0, 3), (1, 3, 0), (1, -3, 0), (1, 0, 3), (-5, 12, 9), (-5, -12, 9), (5, 12, 9),
      (5, -12, 9)] &&
  (bruteForce [4, 0, 0, 1, 0] 10).map swapPoint == [(0, 0, 1), (1, 2, 0), (1, -2, 0)] &&
  (bruteForce [0, 2, 0, 1] 10).map swapPoint == [(0, 0, 1), (1, 0, 0)]

-- The lowest set bit: `k` for the word with the bits `k` and `63` set, `k < 64`, and the trailing
-- zeros of a few other words.
#guard (List.range 64).all fun k ↦ Id.run (ctz (1 <<< k.toUInt64 ||| 0x8000000000000000)) == k
#guard [1, 2, 40, 0xfff0, 0x8000000000000000].all fun w : UInt64 ↦
  Id.run (ctz w) == w.toBitVec.ctz.toNat

-- The binary algorithm on words against `Int.gcd`: every numerator of `-40, …, 40` with every
-- denominator `1, …, 60`, and numerators and denominators around `2 ^ 62` and up to the largest
-- `long` `2 ^ 63 - 1 = 7 ^ 2 · 73 · 127 · 337 · 92737 · 649657`, with common factors and without,
-- both even among them.
#guard (List.range 81).all fun i ↦ (List.range' 1 60).all fun b ↦
  Id.run (relprime ((i : Int) - 40).toInt64 b.toInt64) == (Int.gcd ((i : Int) - 40) b == 1)
#guard ([(2 ^ 62, 3), (2 ^ 62, 2), (2 ^ 62 + 1, 1), (-2 ^ 62, 2 ^ 62 + 1), (2 ^ 63 - 1, 2 ^ 63 - 2),
    (-(2 ^ 63 - 1), 7 * 73 * 127 * 337 * 92737 * 649657), (3 * 2 ^ 60, 9 * 2 ^ 59 + 9),
    (2 ^ 62 - 1, 2 ^ 62 + 1), (-(2 ^ 62 - 2), 2 ^ 61 - 1), (0, 1), (0, 2), (5 * 2 ^ 40, 5 ^ 3),
    (-6, 3 * 2 ^ 61), (-(2 ^ 63 - 1), 1)] : List (Int × Nat)).all fun (a, b) ↦
  Id.run (relprime a.toInt64 b.toInt64) == (Int.gcd a b == 1)

-- The third stage after `fill_checks` against the rows of its primes, and with the test for common
-- factors before it against both: for numerators prime to `b` with `|a| ≤ H`, at the ends of that
-- range and around zero; with the bias for every prime (`H = 50`, and `H = 8555711`, the largest
-- height with `2 · 251 · H < 2 ^ 32`), for every prime but `251` (`H = 8555712`) and for none
-- (`2 p H ≥ 2 ^ 32`); and for denominators reduced by the multiplication
-- (`b ≤ Ratpoints.mulModLimit`) and by division (beyond it), divisible by primes of the stage and
-- not.
#guard
  let c := [1, 2, 3, 4, 5, 6, 7]
  let es := [3, 5, 7, 11, 13, 251].map fun p ↦
    (⟨p, [.prime (examinePrime c 6 p)], magic p, 0, 0, #[]⟩ : SieveEntry)
  ([(50, List.replicate 6 true), (8555711, List.replicate 6 true),
    (8555712, [true, true, true, true, true, false]), (2 ^ 31, List.replicate 6 false),
    (2 ^ 62, List.replicate 6 false)] : List (Nat × List Bool)).all fun (H, biased) ↦
    [1, 2, 3, 7, 15, 3 * 251, mulModLimit, mulModLimit + 1, 2 ^ 32 + 7, 2 ^ 40 + 3].all fun b ↦
      let checks := fillChecks b H es (es.map (·.magic))
      checks.map (·.bias != 0) == biased &&
      ((List.range 61).map (fun i : Nat ↦ (i : Int) - 30) ++
          [-(H : Int), -(H : Int) + 1, (H : Int) - 1, H]).all fun a ↦
        (Int.gcd a b != 1 || Id.run (stage3 a checks) == survives es b a) &&
        Id.run (accepted a b (.pure checks)) == (Int.gcd a b == 1 && survives es b a)

-- The third stage skips an entry of another shape than a prime with its table: the prime power 9.
#guard
  let pw := Id.run (examinePower [1, 2, 3, 4, 5, 6, 7] 6 3 2 true)
  (List.range 40).all fun a : Nat ↦
    Id.run (stage3 a [checkOf 7 100 ⟨9, [.power pw], magic 9, 0, 0, #[]⟩ (magic 9)])

-- The exact check with the test for common factors in front is the check of the reference.
#guard ([([-2, 0, 0, 1], 3), ([1, 0, 126, 0, 441], 4)] : List (List Int × Nat)).all fun (c, d) ↦
  [1, 2, 21, 100].all fun b : Nat ↦ [false, true].all fun rev ↦
    (BruteForce.numerators 130).all fun a ↦
      let w := BruteForce.scaledCoeffs c d b
      let f : Int := if d % 2 = 1 then b else 1
      checkNum w f b rev a == if Int.gcd a b = 1 then checkPoint (.pure w) d b rev a else []

-- The check of a numerator against the reference: the point `(129 : 3830 : 100)` on
-- `y ^ 2 = x ^ 3 - 2` and none for `(258 : 15320 : 200)`, the same point with the common factor 2;
-- the point `(-1 : 0 : 1)` on `y ^ 2 = x ^ 3 + x ^ 2 + x + 1`, given once; and the numerators of
-- the reference for a few curves and denominators.
#guard
  checkNum (BruteForce.scaledCoeffs [-2, 0, 0, 1] 3 100) 100 100 false 129 ==
      [(129, 3830, 100), (129, -3830, 100)] &&
    checkNum (BruteForce.scaledCoeffs [-2, 0, 0, 1] 3 200) 200 200 false 258 == [] &&
    checkNum (BruteForce.scaledCoeffs [1, 1, 1, 1] 3 1) 1 1 false (-1) == [(-1, 0, 1)] &&
    ([([-2, 0, 0, 1], 3), ([1, 2, 3, 4, 5, 6, 7], 6), ([1, 0, 126, 0, 441], 4)] :
        List (List Int × Nat)).all fun (c, d) ↦ [1, 2, 7, 21, 100].all fun b : Nat ↦
      (BruteForce.numerators 130).flatMap
          (checkNum (BruteForce.scaledCoeffs c d b) (if d % 2 = 1 then b else 1) b false) ==
        BruteForce.pointsOfDen c d b (BruteForce.numerators 130)

-- The check with the flag of the reversal: the points `(-9 : 12 : 5)` and `(9 : 12 : 5)` of the
-- polynomial `9 0 -1`, to which ratpoints reverses `-1 0 9`, mapped to the points `(-5 : 12 : 9)`
-- and `(5 : 12 : 9)` that `ratpoints '-1 0 9' 10 -q` prints; and the check with the flag against
-- the check without it, mapped, for a few curves, denominators and numerators.
#guard
  checkNum (BruteForce.scaledCoeffs [9, 0, -1] 2 5) 1 5 true (-9) ==
      [(-5, 12, 9), (-5, -12, 9)] &&
    checkNum (BruteForce.scaledCoeffs [9, 0, -1] 2 5) 1 5 true 9 == [(5, 12, 9), (5, -12, 9)] &&
    ([([9, 0, -1], 2), ([-2, 0, 0, 1], 3), ([1, 0, 126, 0, 441], 4)] :
        List (List Int × Nat)).all fun (c, d) ↦ [1, 2, 5, 100].all fun b : Nat ↦
      (BruteForce.numerators 130).all fun a ↦
        let w := BruteForce.scaledCoeffs c d b
        let f : Int := if d % 2 = 1 then b else 1
        checkNum w f b true a == (checkNum w f b false a).map swapPoint

#guard pointsAtInfinity [1, 0, 0, 0, 9] 4 false == [(1, 3, 0), (1, -3, 0)] &&
  pointsAtInfinity [1, 0, 0, 0, 2] 4 false == [] &&
  pointsAtInfinity [1, 2, 3, 4] 3 false == [(1, 0, 0)]

-- With the flag of the reversal, the points at infinity mapped: `(0 : y : 1)` for `(1 : y : 0)`.
#guard pointsAtInfinity [1, 0, 0, 0, 9] 4 true == [(0, 3, 1), (0, -3, 1)] &&
  pointsAtInfinity [1, 0, 0, 0, 2] 4 true == [] &&
  pointsAtInfinity [1, 2, 3, 4] 3 true == [(0, 0, 1)] &&
  [[1, 0, 0, 0, 9], [0, 0, 0, 0, 0], [-3, 1, 4]].all fun c ↦ [2, 3, 4].all fun d ↦
    pointsAtInfinity c d true == (pointsAtInfinity c d false).map swapPoint

end Sieve

end Ratpoints

end
