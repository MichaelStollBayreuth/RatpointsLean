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
# The sieve

The components of the sieve, each in its place in the C function `find_points_work_1`: the bit
arrays of 64-bit words of the C code with their operations and the rows as words
(`Ratpoints.Sieve.SieveEntry.row`); the test of a candidate that survives the first two stages, the
test for common factors by the binary algorithm (`Ratpoints.Sieve.relprime`) and the third stage,
one numerator at a time against the tables of its primes (`Ratpoints.Sieve.stage3`,
`Ratpoints.Sieve.fillChecks`), and the exact check (`Ratpoints.Sieve.accepted`,
`Ratpoints.Sieve.checkPoint`), whose reference is the check of a numerator
(`Ratpoints.Sieve.checkNum`); the second stage, on a bit array that the first leaves nonzero or on
one of its words (`Ratpoints.Sieve.secondStage`, `Ratpoints.Sieve.secondStageWord`); one bit array
through the second stage and the extraction of the points of its numerators, in either arm of the
second stage (`Ratpoints.Sieve.siftBitArray`); one piece of bit arrays from the first stage, with
the first moduli, through the second, with the others, to the points of its numerators
(`Ratpoints.Sieve.siftPiece`); the numerators of one denominator in pieces, from a class word, the
numerators modulo 64 from which the first stage starts, with the products of the check and what the
third stage needs as thunks (`Ratpoints.Sieve.sift`); and the points at infinity
(`Ratpoints.Sieve.pointsAtInfinity`). The third stage removes only numerators that the rows of its
primes would remove, or that have a common factor with the denominator, so that the test of a
candidate and the exact check give the points of the check of the reference for the numerators that
survive the rows of these primes. The tables of the primes and of the prime powers and the sieve
entries of the moduli, with the rows of a denominator, are in `Ratpoints.Model.Tables`; the loop
over the denominators (`Ratpoints.Sieve.sieveRun`), with the 2-adic information that gives the words
of the classes of the denominators modulo 64, is in `Ratpoints.Model.Denominators`. The plain sieve
of one denominator, one Boolean per numerator (`Ratpoints.Sieve.sieveDen`), and the test for common
factors and the exact check of its survivors (`Ratpoints.Sieve.checkDen`) are not part of the run:
they are the reference of the bit arrays of words (`Ratpoints.Sieve.toList_run_sift_eq_checkDen`).
Every row, and the word of the class of a denominator in the 2-adic information, let every point
through, so the sieve of a denominator finds exactly its points in the brute-force reference
`Ratpoints.bruteForce`, in the same order, each mapped by `Ratpoints.Sieve.swapPoint` when the flag
of the reversal is set: the map gives the point of the caller's curve for a point of a polynomial
that the reversal check has reversed (`Ratpoints.Setup.reversal`), the exact check and the points at
infinity deliver the mapped points when their flag is set, and the components from the run down to
the check hand the flag on. The rows of `0` that the build of ratpoints generates are computed here
as words, by `Ratpoints.Sieve.SieveEntry.row`.

## Main definitions

* `Ratpoints.Sieve.sieveDen`, `Ratpoints.Sieve.checkDen`: the plain sieve of one denominator and the
  points of its survivors, the reference of the bit arrays of words.
* `Ratpoints.Sieve.andBitArray`, `Ratpoints.Sieve.clearLowBits`, `Ratpoints.Sieve.clearHighBits`,
  `Ratpoints.Sieve.isZeroAt`, `Ratpoints.Sieve.ctz`: the operations on the bit arrays of 64-bit
  words of the C code, and the lowest set bit of a word.
* `Ratpoints.Sieve.SieveEntry.row`, `Ratpoints.Sieve.SieveEntry.rows`,
  `Ratpoints.Sieve.SieveSpec`: the row of a denominator as words, the rows of the residues, each
  made when first needed, and a modulus with its row for the denominator at hand.
* `Ratpoints.Sieve.swapPoint`: the point of the caller's curve for a point of the reversed curve.
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
* `Ratpoints.Sieve.secondStage`, `Ratpoints.Sieve.secondStageWord`: the second stage on a bit array
  and on one of its words, the rows of its moduli and-ed in while a bit is left.
* `Ratpoints.Sieve.andRows`: the first stage over a piece of bit arrays, from a class word, the rows
  of the moduli and-ed into its words.
* `Ratpoints.Sieve.walkWord`: the walk through the set bits of a word, lowest first, each
  numerator going to the test of a candidate and, if it passes, to the exact check.
* `Ratpoints.Sieve.siftBitArray`: one bit array that the first stage leaves nonzero, through the
  second stage, in either arm, and the walks through its words.
* `Ratpoints.Sieve.scanPiece`: the scan over the bit arrays of a piece up to a sentinel, stepping
  over those that are zero, and a copy of each of the others through the second stage and the
  extraction.
* `Ratpoints.Sieve.siftPiece`: one piece of bit arrays, from the first stage and the masks at its
  two ends, through the second stage, to the points of its numerators.
* `Ratpoints.Sieve.sift`: the points of one denominator, its numerators `-H, …, H` in pieces of bit
  arrays, from a class word.
* `Ratpoints.Sieve.pointsAtInfinity`: the points at infinity, mapped by `Ratpoints.Sieve.swapPoint`
  when the flag of the reversal is set.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The plain sieve -/

/-- The plain sieve of the denominator `b`: an array of `2H + 1` Booleans, one for each numerator
`a = i - H`, all true at the start; for each sieve entry of `entries` in turn, every Boolean is
replaced by its conjunction with the row of `b` at its numerator
(`Ratpoints.Sieve.SieveEntry.admits`). With `Ratpoints.Sieve.checkDen` it is the reference of the
bit arrays of words: for pieces of at least one bit array, moduli `p > 0`, a denominator
`0 < b < 2 ^ 63`, `H < 2 ^ 63` and entries of the third stage of the shape of
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, with the reciprocals of their moduli, the points that
`Ratpoints.Sieve.sift` finds with the rows of the entries of its first two stages
(`Ratpoints.Sieve.SieveEntry.rows`) from a class word are those that `Ratpoints.Sieve.checkDen`
finds on the plain sieve with all these entries whose numerators pass the class word, all of them
for the word `~~~0` or any class word that admits the numerators of the points (such as the word
`nb[b mod 64]` of `Ratpoints.Sieve.twoAdic`), each mapped by `Ratpoints.Sieve.swapPoint` when the
flag of the reversal is set (`Ratpoints.Sieve.toList_run_sift_eq_checkDen`). -/
def sieveDen (H b : Nat) (entries : List SieveEntry) : Id (Vector Bool (2 * H + 1)) := do
  let mut surv := Vector.replicate (2 * H + 1) true
  for e in entries do
    for h : i in [0:2 * H + 1] do
      surv := surv.set i (surv[i] && e.admits b ((i : Int) - H))
  return surv

/-- The points `(a, y, b)` with the denominator `b` and a numerator `a = i - H` whose entry in
`surv` is true, by increasing `a`: each such numerator is tested for common factors with `b` and
checked exactly, as the brute-force reference checks it (`Ratpoints.BruteForce.pointsOfDen`):
`F(a, b)` by Horner's rule on the products `cₖ b^(d - k)`, computed once, with one more factor `b`
for odd `d`, then `(a, y, b)` and, for `y ≠ 0`, `(a, -y, b)` when `F(a, b) = y ^ 2` with `y ≥ 0`.
With the plain sieve `Ratpoints.Sieve.sieveDen` it is the reference of the bit arrays of words: for
a denominator `0 < b < 2 ^ 63`, `H < 2 ^ 63`, sieve entries with `p > 0` in the first two stages and
entries of the shape of `Ratpoints.Sieve.SieveEntry.IsPrimeEntry` with the reciprocals of their
moduli in the third, `Ratpoints.Sieve.sift` with the rows of the first
(`Ratpoints.Sieve.SieveEntry.rows`), in pieces of at least one bit array, finds the points that it
finds on the plain sieve with all these entries whose numerators pass the class word, all of them
from the class word `~~~0` or from any class word that admits the numerators of the points (such as
the word `nb[b mod 64]` of `Ratpoints.Sieve.twoAdic`), each mapped by `Ratpoints.Sieve.swapPoint`
when the flag of the reversal is set (`Ratpoints.Sieve.toList_run_sift_eq_checkDen`). -/
def checkDen (c : List Int) (d H b : Nat) (surv : Vector Bool (2 * H + 1)) :
    Id (Array (Int × Int × Int)) := do
  let w := BruteForce.scaledCoeffs c d b
  let f : Int := if d % 2 = 1 then b else 1
  let mut out := #[]
  for h : i in [0:2 * H + 1] do
    if surv[i] then
      let a := (i : Int) - H
      if Int.gcd a b = 1 then
        out := out ++ (BruteForce.pointsAbove a b (BruteForce.horner w a * f)).toArray
  return out

/-! ### Words and bit arrays -/

/-- Bit array `j` of the words `v` and-ed with bit array `x` of the row `row`, one word at a time:
for `κ < rbaPack` (`Ratpoints.rbaPack`, the number of words of a bit array), word
`rbaPack * j + κ` of `v` with word `rbaPack * x + κ` of `row`.

C: `rp-private.h:134`, `rp-private.h:176`, `rp-private.h:237`, `rp-private.h:263`,
`rp-private.h:287`

Deviation: one definition for every build, on bit arrays given by their indices in arrays of
words, each bit array `rbaPack` consecutive words, for the `&` on the vector type of the build. -/
def andBitArray {m : Nat} (v : Vector UInt64 m) (j : Nat) (row : Array UInt64) (x : Nat) :
    Vector UInt64 m :=
  Nat.fold rbaPack (fun κ _ v ↦
    v.set! (rbaPack * j + κ) (v[rbaPack * j + κ]! &&& row[rbaPack * x + κ]!)) v

/-- The lowest `s` bits of bit array `0` of the words `v` cleared, for `s < Ratpoints.rbaLength`:
the words below `s / 64` are set to `0`, and word `s / 64` is and-ed with `~~~0 <<< (s % 64)`.

C: `rp-private.h:153-155`, `rp-private.h:206-213`, `rp-private.h:242-244`,
`rp-private.h:268-270`, `rp-private.h:291`

Deviation: one definition for every build, the loop of the build with 512-bit bit arrays, of which
the macros of the builds with 256-bit and 128-bit bit arrays are unrolled cases and that of the
build with 64-bit bit arrays the case of one word; the bit array is the first `Ratpoints.rbaPack`
words of an array, for the vector type of the build. -/
def clearLowBits {m : Nat} (v : Vector UInt64 m) (s : Nat) : Vector UInt64 m :=
  let q := s / 64
  let v := Nat.fold q (fun l _ v ↦ v.set! l 0) v
  v.set! q (v[q]! &&& ~~~0 <<< (s % 64).toUInt64)

/-- The highest `s` bits of bit array `j` of the words `v` cleared, for `s < Ratpoints.rbaLength`:
for the number `rbaPack` of words of a bit array (`Ratpoints.rbaPack`), word
`q = rbaPack - 1 - s / 64` of the bit array is and-ed with `~~~0 >>> (s % 64)`, and its words
above `q` are set to `0`.

C: `rp-private.h:156-159`, `rp-private.h:214-221`, `rp-private.h:245-247`,
`rp-private.h:271-273`, `rp-private.h:292`

Deviation: one definition for every build, the loop of the build with 512-bit bit arrays, of which
the macros of the builds with 256-bit and 128-bit bit arrays are unrolled cases and that of the
build with 64-bit bit arrays the case of one word; the bit array is given by its index in an array
of words, `rbaPack` consecutive words, for a pointer to a value of the vector type of the
build. -/
def clearHighBits {m : Nat} (v : Vector UInt64 m) (j s : Nat) : Vector UInt64 m :=
  let q := rbaPack - 1 - s / 64
  let v := v.set! (rbaPack * j + q) (v[rbaPack * j + q]! &&& ~~~0 >>> (s % 64).toUInt64)
  Nat.fold (rbaPack - 1 - q) (fun l _ v ↦ v.set! (rbaPack * j + q + 1 + l) 0) v

/-- Whether bit array `pos` of the words `v` is zero: for the number `rbaPack` of words of a bit
array (`Ratpoints.rbaPack`), its words `rbaPack * pos + κ`, `κ < rbaPack`, are all `0`.

C: `rp-private.h:137-152`, `rp-private.h:179-202`, `rp-private.h:241`, `rp-private.h:267`,
`rp-private.h:290`, `rp-private.h:306-308`

Deviation: one definition for every build, on a bit array given by its index in an array of words,
`rbaPack` consecutive words that it compares with `0` one at a time, for the tests of the builds on
the vector type, with vector instructions or by or-ing its words; the test for zero `TESTZ` also
stands for its negation `TEST`. -/
def isZeroAt {m : Nat} (v : Vector UInt64 m) (pos : Nat) : Bool :=
  Nat.all rbaPack fun κ _ ↦ v[rbaPack * pos + κ]! == 0

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

/-! ### The rows as words -/

/-- The pattern `pat` of period `p` packed into `p / 64 + 2` words, over the positions
`0, …, p + 63` and a little beyond: bit `t` of word `q` is the entry of `pat` at
`(64 q + t) mod p`, so that the 64 positions from any position below `p` on lie in two
consecutive words (`Ratpoints.Sieve.window`). -/
def packedPattern (pat : Array Bool) (p : Nat) : Array UInt64 :=
  (Array.range (p / 64 + 2)).map fun q ↦
    Nat.fold 64 (fun t _ w ↦ if pat[(64 * q + t) % p]! then w ||| 1 <<< t.toUInt64 else w) 0

/-- The 64 bits of the packed words `E` from position `s` on, where bit `t` of word `q` is at
position `64 q + t`: word `s / 64` shifted right by `r = s % 64`, and for `r ≠ 0` the lowest `r`
bits of the next word above them. -/
def window (E : Array UInt64) (s : Nat) : UInt64 :=
  let q := s / 64
  let r := s % 64
  if r = 0 then E[q]! else E[q]! >>> r.toUInt64 ||| E[q + 1]! <<< (64 - r).toUInt64

/-- The row of the denominator `b` in the sieve entry `e` of the modulus `p = e.p`, as `p` bit
arrays of `Ratpoints.rbaPack` words: the pattern of one period, whether the row admits the
numerator `N` for `N < p` (`Ratpoints.Sieve.SieveEntry.admits`), packed into words
(`Ratpoints.Sieve.packedPattern`); for `j < p`, word `j` the 64 bits of the packed pattern from
position `64 j mod p` on (`Ratpoints.Sieve.window`); and these `p` words repeated `rbaPack` times.
Bit `t` of word `j` says whether the row admits `64 j + t`, since
`Ratpoints.Sieve.SieveEntry.admits` depends only on the residue modulo `p`.

C: `init.c:42-46`, `init.c:62-83`, `init.c:99-111`, `init.c:118-246`, `init.c:259-297`,
`init.c:387`, `init.c:391-393`, `init.c:415-418`, `init.c:430`, `init.c:443-445`,
`gen_find_points_h.c:102-134`, `gen_init_sieve_h.c:48-62`

Deviation: one function for every kind of modulus, the pattern of one period from
`Ratpoints.Sieve.SieveEntry.admits` laid out in words by windows into its packed form, as
`lay_out_pattern` lays out the pattern of a prime power, for the builders of the rows of a prime in
`init.c`, which step through the residues `a b⁻¹ mod p` four at a time and rotate the pattern
through the words, one function for each prime that the build generates, for the pattern `sieves0`
that the build generates for the row of `0` of a prime, and for the row of a product, which
`_ratpoints_sieve_init_product` lays down from the rows of its factors (stage F4); in
`lay_out_pattern`, the packed pattern made bit by bit, where it is or-ed together from shifted
copies of the pattern, the position of each window computed, where it is stepped by `64 mod p`, and
the first `p` words repeated, where all `p rbaPack` are computed; a fresh array, for the space that
the builders take from the buffer of the tables (`ba_next`), and the row returned, where the
builders also store it in the field `sieve` of the entry, with a release store for the threads
(`RP_PUBLISH`), which the thunks of `Ratpoints.Sieve.SieveEntry.rows` do; the copies of the first
bit arrays that the builders append at the end of a row, which only the chunked first stage reads,
are none in the build of the model (`RATPOINTS_CHUNK` = 1; stage F4). -/
def SieveEntry.row (e : SieveEntry) (b : Nat) : Array UInt64 :=
  let pat := (Array.range e.p).map fun N : Nat ↦ e.admits b N
  let E := packedPattern pat e.p
  let base := (Array.range e.p).map fun j ↦ window E (64 * j % e.p)
  (Array.range (e.p * rbaPack)).map fun j ↦ base[j % e.p]!

/-- The rows of the residues `r = 0, …, e.p - 1` in the sieve entry `e`
(`Ratpoints.Sieve.SieveEntry.row`), each a thunk: it is made when a denominator first needs it and
kept from then on, as long as the array is. -/
def SieveEntry.rows (e : SieveEntry) : Array (Thunk (Array UInt64)) :=
  (Array.range e.p).map fun r ↦ Thunk.mk fun _ ↦ e.row r

/-- A modulus with its row for the denominator at hand, `p` bit arrays of `Ratpoints.rbaPack`
words: bit array `x` of the row says which numerators of the bit array with the word number `w` the
row admits, for every `w ≡ x (mod p)`.

C: `rp-private.h:378-379`

Deviation: the row for the pointer `ptr` to it, with no `offset`, which carries the shift of the
packing of the 2-adic classes and a multiple of `p` of at least `RP_ROW_BIAS` that keeps the index
non-negative, with the check at compile time that twice that bias stays within `RP_MULMOD_LIMIT`
(`rp-private.h:387`, `rp-private.h:426-427`; stage F3), and no pointers `start` and `end` into the
row, which only the chunked first stage reads (stage F4): the components index the row by the word
number modulo `p`. -/
structure SieveSpec where
  /-- The modulus. -/
  p : Nat
  /-- The row: `p` bit arrays of `Ratpoints.rbaPack` words. -/
  row : Array UInt64

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

/-! ### The second stage -/

/-- The second stage on the bit array `nums` with the word number `i`, a copy of a bit array that
the first stage left nonzero: for each modulus `p` of `specs` with its row in turn, while `nums` is
not zero (`Ratpoints.Sieve.isZeroAt`), `nums` is and-ed with bit array `i mod p` of the row
(`Ratpoints.Sieve.andBitArray`). Stopping early loses nothing, since a zero bit array stays zero, so
that the result is `nums` and-ed with the rows of all the moduli.

C: `sift.c:1083`, `sift.c:1085`, `sift.c:1175-1202`

Deviation: the row of the word number `i` at index `i mod p`, where ratpoints adds the offset of the
packing and a multiple of `p` that keeps the index non-negative, and reduces by a multiplication
with the reciprocal of `p` from the array `magics` where that is exact (`small`) and by the helper
`mod` otherwise (stage F3); the moduli of the stage with their rows as a list, for the pointers
`ssp` and `mg` that step through the sieve specs and the array `magics` from position `sp1` on and
the count `sp2 - sp1`, with no bound `2 RATPOINTS_NUM_PRIMES` on their number (the length of
`magics`, `find_points.c:347`), which ratpoints never reaches since each entry of `sieve_list` owns
its own prime (`find_points.c:329-331`), where well-formed parameters may repeat a modulus; one bit
array of `Ratpoints.rbaPack` words, for the vector `nums`; natural numbers and integers for the
`long`s; no count of the ands of the second stage under `RP_PHASE_COUNTS`, and no output under
`DEBUG`. -/
def secondStage (specs : List SieveSpec) (i : Int) (nums : Vector UInt64 rbaPack) :
    Id (Vector UInt64 rbaPack) := do
  let mut nums := nums
  for s in specs do
    if isZeroAt nums 0 then break
    nums := andBitArray nums 0 s.row (i % (s.p : Int)).toNat
  return nums

/-- The second stage on word `κ < Ratpoints.rbaPack` of the bit array with the word number `i`, the
arm of the second stage for one word at a time: for each modulus `p` of `specs` with its row in
turn, while `x ≠ 0`, `x` is and-ed with word `κ` of bit array `i mod p` of the row. Stopping early
loses nothing, and the result is word `κ` of the result of `Ratpoints.Sieve.secondStage` on a bit
array whose word `κ` is `x`.

C: `sift.c:1135-1136`, `sift.c:1141-1152`

Deviation: the row of the word number `i` at index `i mod p`, where ratpoints adds the offset of the
packing and a multiple of `p` that keeps the index non-negative, and reduces by a multiplication
with the reciprocal of `p` from the array `magics` where that is exact (`small`) and by the helper
`mod` otherwise (stage F3); the moduli of the stage with their rows as a list, for the pointers
`sspk` and `mg` that step through the sieve specs and the array `magics` from position `sp1` on and
the count `sp2 - sp1`, with no bound `2 RATPOINTS_NUM_PRIMES` on their number (the length of
`magics`, `find_points.c:347`), which ratpoints never reaches since each entry of `sieve_list` owns
its own prime (`find_points.c:329-331`), where well-formed parameters may repeat a modulus; natural
numbers and integers for the `long`s; no count of the ands of the second stage under
`RP_PHASE_COUNTS`. -/
def secondStageWord (specs : List SieveSpec) (i : Int) (κ : Nat) (x : UInt64) : Id UInt64 := do
  let mut x := x
  for s in specs do
    if x == 0 then break
    x := x &&& s.row[rbaPack * (i % (s.p : Int)).toNat + κ]!
  return x

/-! ### One piece -/

/-- The first stage over a piece, the bit arrays with the word numbers `w0, …, w0 + n - 1`, which
are the first `n` bit arrays of `surv`: their words are set to the class word `cw`, the numerators
modulo 64 that the 2-adic information admits for the denominator (`Ratpoints.Sieve.twoAdic`; bit `t`
of every word stands for a numerator `≡ t (mod 64)`, since `64` divides `Ratpoints.rbaLength`); then
for each modulus `p` of `specs` with its row and for `r = (-w0) mod p`, bit array `j` is and-ed with
bit array `(w0 + j) mod p` of the row (`Ratpoints.Sieve.andBitArray`), in three loops: if `n < r`,
with the `n` bit arrays of the row from `p - r` on, and otherwise with the `r` bit arrays from
`p - r` on, then with whole periods of `p` bit arrays from `0`, then with the rest from `0`. The
last bit array of `surv`, the place of the sentinel, is left as it is.

C: `sift.c:943-1022`, `find_points.c:1098`, `rp-private.h:129-132`, `rp-private.h:203-204`,
`rp-private.h:235`, `rp-private.h:261`, `rp-private.h:285`

Deviation: the first stage of the builds with one register per chunk, for the chunks of sixteen
registers of the default build with the legs over the tail of a piece (stage F4); the class word
written one word at a time from the first, where ratpoints writes the 2-adic pattern of the class of
`b` into the bit arrays from the last, and the pattern of the plain layout, one word repeated, for
the packed pattern of a stride `2^k` (stage F3), the class word written into each word of a bit
array, for the vector `RBA(packed)` that `get_2adic_info` makes once per class
(`find_points.c:1098`) and `_ratpoints_sift0` copies into each bit array (`bits64`, `sift.c:519`,
`sift.c:954`); the row of the word number `w` at index `w mod p`, where ratpoints adds the offset of
the packing and a multiple of `p` that keeps the index non-negative, and reduces by a multiplication
with the reciprocal of `p` where that is exact and by the helper `mod` otherwise (`mod_mul` and
`mod` of `sift.c`, stage F3); indices for the pointers into the rows and into the survivors, and the
number of whole periods and the rest computed before their loops; natural numbers and integers for
the `long`s; no output under `DEBUG`. -/
def andRows (specs : List SieveSpec) (cw : UInt64) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    Id (Vector UInt64 ((n + 1) * rbaPack)) := do
  let mut surv := surv
  for i in [0:n * rbaPack] do
    surv := surv.set! i cw
  for s in specs do
    let p := s.p
    let r := ((-w0) % (p : Int)).toNat
    if n < r then
      for j in [0:n] do
        surv := andBitArray surv j s.row (p - r + j)
    else
      for j in [0:r] do
        surv := andBitArray surv j s.row (p - r + j)
      let left := n - r
      for k in [0:left / p] do
        for i in [0:p] do
          surv := andBitArray surv (r + k * p + i) s.row i
      for i in [0:left % p] do
        surv := andBitArray surv (r + left / p * p + i) s.row i
  return surv

/-- The set bits of the word `x`, lowest first, bit `t` standing for the numerator `a0 + t`: while
`x ≠ 0`, for the lowest set bit `t` of `x` (`Ratpoints.Sieve.ctz`), the numerator `a0 + t` goes to
the test for common factors with the denominator `b` and the third stage
(`Ratpoints.Sieve.accepted`, with the thunk `checks` of what that stage needs), and if it passes,
its points by the exact check (`Ratpoints.Sieve.checkPoint`, with the thunk `w` of the products, the
degree `d` and the flag `rev` of the reversal) are appended to `out`; then that bit is cleared by
`x &&& (x - 1)`. This is the loop `RP_EACH_SET_BIT` of the C code with the body that the extraction
runs for each set bit.

C: `sift.c:262-264`, `sift.c:1161-1171`, `sift.c:1227-1255`, `sift.c:1265-1292`

Deviation: bit `t` for the numerator `a0 + t`, where the step from one bit to the next is the stride
`2^k` of the packing of the 2-adic class of `b` (stage F3); the lowest set bit by the loop of
`RP_CTZL` for a compiler without the builtin (`Ratpoints.Sieve.ctz`); one definition for the body at
the three places of the extraction, the first word of a bit array, the others, and a word of the arm
of the second stage for one word at a time; natural numbers and integers for the `long`s; no count
of the numerators that reach the test for common factors (`n_bits`), which ratpoints reads to
correct the moduli between the blocks of the run (stage I), and no counts under `RP_PHASE_COUNTS`;
no stop that the callback `process` may request (`quit`, stage G), and no output under `DEBUG`. -/
def walkWord (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (checks : Thunk (List CheckSpec)) (x : UInt64) (a0 : Int) (out : Array (Int × Int × Int)) :
    Id (Array (Int × Int × Int)) := do
  let mut x := x
  let mut out := out
  while x != 0 do
    let t ← ctz x
    if ← accepted (a0 + t) b checks then
      out := out ++ (checkPoint w d b rev (a0 + t)).toArray
    x := x &&& (x - 1)
  return out

/-- One bit array that the first stage left nonzero, with the word number `i`, from a copy `nums` of
it, the points of its numerators appended to `out`, in the arm of the second stage that `useLong`
chooses (`Ratpoints.useLongInPhase2` in the run): for `useLong = false`, the second stage on the
whole bit array (`Ratpoints.Sieve.secondStage`), and, if it is still nonzero, the set bits of its
words walked through in turn (`Ratpoints.Sieve.walkWord`); for `useLong = true`, for each word that
is not zero, the second stage on that word (`Ratpoints.Sieve.secondStageWord`) and the walk through
its set bits. Bit `t` of word `κ` stands for the numerator `rbaLength i + 64 κ + t`, for the number
`rbaLength` of bits of a bit array (`Ratpoints.rbaLength`), and each numerator goes to the test of a
candidate (`Ratpoints.Sieve.accepted`, with the thunk `checks` of the third stage) and, if it
passes, to the exact check, with the thunk `w` of the products, the degree `d`, the denominator `b`
and the flag `rev`. Both arms walk through the set bits of the same words, the words of `nums`
and-ed with the rows of all the moduli of `specs`, in the same order.

C: `sift.c:1094-1111`, `sift.c:1126-1134`, `sift.c:1137-1139`, `sift.c:1154-1159`,
`sift.c:1172-1173`, `sift.c:1204-1210`, `sift.c:1213-1226`, `sift.c:1257-1264`,
`sift.c:1293-1296`, `rp-private.h:135-136`, `rp-private.h:177-178`, `rp-private.h:238-239`,
`rp-private.h:264-266`, `rp-private.h:288-289`

Deviation: the arm chosen by the argument `useLong`, so that the guards run both in the same build,
for the arm that the build compiles (`#ifdef USE_LONG_IN_PHASE_2`); a function of its own for the
body of the loop of the scan over one bit array; the plain layout, bit `t` of the bit array with the
word number `i` for the numerator `rbaLength i + t`, where bit `t` stands for the numerator
`a₀ + 2^k (rbaLength i + t)` of the packing of the 2-adic class of `b` (stage F3); the words of the
bit array read as entries of the vector, for `EXT0` and `EXT`, with one loop over the words, for the
read of the first word and the loop over the others; natural numbers and integers for the `long`s;
no counts under `RP_PHASE_COUNTS`, no stop after a phase (`RP_STOP_AFTER`), and no output under
`DEBUG`. -/
def siftBitArray (useLong : Bool) (w : Thunk (List Int)) (d b : Nat) (rev : Bool)
    (specs : List SieveSpec) (checks : Thunk (List CheckSpec)) (i : Int)
    (nums : Vector UInt64 rbaPack) (out : Array (Int × Int × Int)) :
    Id (Array (Int × Int × Int)) := do
  let mut out := out
  if useLong then
    for κ in [0:rbaPack] do
      if nums[κ]! != 0 then
        let x ← secondStageWord specs i κ nums[κ]!
        out ← walkWord w d b rev checks x (i * rbaLength + 64 * κ) out
  else
    let nums ← secondStage specs i nums
    if !isZeroAt nums 0 then
      let mut a0 := i * rbaLength
      for κ in [0:rbaPack] do
        out ← walkWord w d b rev checks nums[κ]! a0 out
        a0 := a0 + 64
  return out

/-- The scan over a piece, the bit arrays with the word numbers `w0, …, w0 + n - 1`, which are the
first `n` bit arrays of `surv`, and the second stage and the extraction of the points of their
numerators: a sentinel, a bit array of ones, is written into bit array `n`, just past the piece;
then from bit array `0` on, the bit arrays that are zero (`Ratpoints.Sieve.isZeroAt`) are stepped
over, the scan stops at the sentinel, and each of the other bit arrays `pos` is copied and goes,
with its word number `w0 + pos`, through the second stage with the moduli and rows of `specs` and
the extraction (`Ratpoints.Sieve.siftBitArray`, in the arm `Ratpoints.useLongInPhase2`, with the
thunk `w` of the products, the degree `d`, the denominator `b`, the flag `rev` and the thunk
`checks` of the third stage).

C: `sift.c:1061-1082`, `sift.c:1088-1092`, `sift.c:1298-1299`, `rp-private.h:133`,
`rp-private.h:205`, `rp-private.h:236`, `rp-private.h:262`, `rp-private.h:286`

Deviation: indices for the pointers into the survivors, and a scan that holds its position as an
index, where ratpoints recovers the word number from a pointer difference; the copy `nums` of the
bit array a vector of `Ratpoints.rbaPack` words; the sentinel `~zero` of every build as
`Ratpoints.rbaPack` words `~~~0`, written one at a time; natural numbers and integers for the
`long`s; no count of the bit arrays that survive the first stage (`n_arrays`), which ratpoints reads
to correct the moduli between the blocks of the run (stage I). -/
def scanPiece (w : Thunk (List Int)) (d b : Nat) (rev : Bool) (specs : List SieveSpec)
    (checks : Thunk (List CheckSpec)) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    Id (Array (Int × Int × Int)) := do
  let mut surv := surv
  for κ in [0:rbaPack] do
    surv := surv.set! (rbaPack * n + κ) (~~~0)
  let mut pos := 0
  let mut out := #[]
  repeat
    while isZeroAt surv pos do
      pos := pos + 1
    if n ≤ pos then break
    let nums : Vector UInt64 rbaPack := .ofFn fun κ ↦ surv[rbaPack * pos + κ]!
    out ← siftBitArray useLongInPhase2 w d b rev specs checks (w0 + pos) nums out
    pos := pos + 1
  return out

/-- One piece, the bit arrays with the word numbers `w0, …, w0 + n - 1`, and the points of its
numerators: a fresh array of `n + 1` bit arrays, the last one the place of the sentinel; the first
stage with the first `sp1` moduli of `specs` and their rows, from the class word `cw`
(`Ratpoints.Sieve.andRows`); the lowest `maskLow` bits of the first bit array cleared if
`maskLow ≠ 0` (`Ratpoints.Sieve.clearLowBits`), and the highest `maskHigh` bits of the last bit
array of the piece, `n - 1`, if `maskHigh ≠ 0` (`Ratpoints.Sieve.clearHighBits`); and the scan with
the second stage, with the other moduli of `specs`, and the extraction (`Ratpoints.Sieve.scanPiece`,
with the thunk `w` of the products, the degree `d`, the denominator `b`, the flag `rev` and the
thunk `checks` of the third stage). This is `_ratpoints_sift0` of the C code, with the allocation of
the survivors array that it works in.

C: `find_points.c:3119-3121`, `sift.c:498-531`, `sift.c:548`, `sift.c:1030-1041`,
`sift.c:1056-1058`, `sift.c:1300-1305`, `rp-private.h:575`, `rp-private.h:610-614`

Deviation: a fresh array of zeros for each piece, for the survivors array of the sieving thread,
which every piece reuses, with one bit array more for the alignment, and whose words `malloc` leaves
uninitialized; the piece by its first word number `w0` and its number `n` of bit arrays, for `w_low`
and `w_high`, and an index for the pointer to its last bit array; the moduli of the first two stages
with their rows as the list `specs` and the end `sp1` of the first stage, for the sieve specs
`sieves` and the number `sp1` that the sieving thread keeps, and the thunk `checks`, for the table
`checks` of the third stage and its length `nchecks = sp3 - sp2`; the class word `cw`, the pattern
`bits` of the class `cls` (`sift.c:519`) at the stride 1, for the class itself, whose stride `k` and
residue `a0`, which the extraction reads (`sift.c:1221-1222`, `sift.c:1130-1131`), come with the
packing (stage F3); no `magics` and no test `small` of whether the reductions modulo the moduli of
the first two stages can multiply by a reciprocal (stage F3); no count of the words of the piece
(`n_words`), which ratpoints reads to correct the moduli between the blocks of the run (stage I);
the thunk `w` of the products of the check as an argument, where `_ratpoints_check_point` computes
the products when the first survivor of `b` reaches it; a list of points, for the callback `process`
with its argument `info` and for the count `total` of points that `_ratpoints_sift0` returns, with
no flag `quit` for a stop that `process` may request (stage G); natural numbers and integers for the
`long`s; no measurements of the phases (`RP_TIC`, `RP_TOC`, `RP_PHASE_TIMING`) and no stop after one
of them (`RP_STOP_AFTER`). -/
def siftPiece (w : Thunk (List Int)) (d b : Nat) (rev : Bool) (sp1 : Nat)
    (specs : List SieveSpec) (checks : Thunk (List CheckSpec)) (cw : UInt64) (w0 : Int)
    (n maskLow maskHigh : Nat) :
    Id (Array (Int × Int × Int)) := do
  let mut surv ← andRows (specs.take sp1) cw w0 n (Vector.replicate ((n + 1) * rbaPack) 0)
  if maskLow ≠ 0 then surv := clearLowBits surv maskLow
  if maskHigh ≠ 0 then surv := clearHighBits surv (n - 1) maskHigh
  scanPiece w d b rev (specs.drop sp1) checks w0 n surv

/-! ### One denominator -/

/-- The points of the denominator `b`, its numerators `-H, …, H` in pieces of at most `A` bit
arrays, for `A ≥ 1` (for `A = 0` the loop does not end), from the class word `cw` of `b`, the
numerators modulo 64 that the 2-adic information admits (`Ratpoints.Sieve.twoAdic`): for each
modulus `p` of the first two stages with its rows `rs` in `rows`, the row of `b` is that of the
residue `b mod p`, which its thunk makes when it is first needed
(`Ratpoints.Sieve.SieveEntry.rows`); the first stage ends after `sp1` of them; what the third stage
needs of the sieve entries `es3` of its primes, with the reciprocals `mgs3` of their moduli, for `b`
and `H` (`Ratpoints.Sieve.fillChecks`) is a thunk, and so are the products `w` of the coefficients
`cₖ` with the powers `b^(d - k)` (`Ratpoints.BruteForce.scaledCoeffs`), both forced when the first
numerator of `b` needs them; the check gets the degree `d` and the flag `rev` of the reversal; for
the number `rbaLength` of bits of a bit array (`Ratpoints.rbaLength`), the bit arrays have the word
numbers from `wLow = ⌊-H / rbaLength⌋` to `wHigh - 1`, for `wHigh = ⌊H / rbaLength⌋ + 1`; and while
`w0 < wHigh`, the piece of the word numbers `w0, …, w1 - 1`, for `w1 = min (w0 + A) wHigh`, gives
its points (`Ratpoints.Sieve.siftPiece`, with the class word), with the low mask
`-H - rbaLength wLow` if it is the first piece and the high mask `rbaLength - 1 - (H mod rbaLength)`
if it is the last, so that the numerators that the masks leave lie end to end and make up
`-H, …, H`.

C: `find_points.c:3112-3114`, `find_points.c:3123-3124`, `find_points.c:3129`,
`find_points.c:3149-3170`, `find_points.c:3442-3488`, `find_points.c:3490-3561`,
`find_points.c:3563-3617`, `rp-private.h:577-578`, `rp-private.h:583`

Deviation: the plain layout, bit `t` of the bit array with the word number `w` for the numerator
`rbaLength w + t`, and every numerator from `-H` to `H`, as the bits from `-H` to `H`, for the
intervals of the search region that the Sturm step keeps (stage H), whose numerators ratpoints takes
into the packing of the 2-adic class of `b` (`interval_bits`, `numerators_to_bits`; stage F3),
returning at the first interval beyond `H` and skipping an empty one; the class word `cw` of `b`,
the pattern of its class at the stride 1, for the class `cls` itself, whose stride `k` and residue
`a0` (read through `interval_bits` by `numerators_to_bits`) and row offsets (read by `set_rows`)
come with the packing (stage F3); the row of `b mod p`, read in `sift` from the rows of the run and
made by its thunk when it is first needed, for the row of `b 2^(-k) mod p` that `set_rows` reads
from the residues that `fill_bp_list` computes before the call (stage F3), with a test for the rows
that are missing and their construction by the function `init` of the entry under the lock of the
tables, which threads share; the moduli of the first two stages with their rows, for the sieve specs
(`sieve_spec`) with the offsets of the packing (stage F3) and the ends of the rows, which only the
chunked first stage reads (stage F4); the end `sp1` of the first stage, the entries `es3` of the
third stage and their reciprocals `mgs3` as arguments, for the numbers `sp1`, `sp2` and `sp3` that
the sieving thread keeps (`worker_init`) and the entries `sieve_list[sp2], …, sieve_list[sp3 - 1]`
and the reciprocals `magics[sp2], …, magics[sp3 - 1]` of the arguments, which `fill_checks` reads,
with no correction of `sp2` and `sp3` between the blocks of the run (stage I); the thunk of
`Ratpoints.Sieve.fillChecks`, for the table `checks` of the sieving thread, which `fill_checks`
fills, and its flag `stage3_filled`, which `sift` clears; the thunk of the products `w`, for the
flag `compute_bc`, which `sift` sets and `_ratpoints_check_point` clears when it computes the
products; no count of the denominators sieved (`n_sifts`), which ratpoints reads to correct the
moduli between the blocks of the run (stage I); a list of points, for the callback `process` with
its argument `info` and for the count `total` of points that `sift` returns, with no stop that
`process` may request (`quit`, which `worker_init` clears, stage G); the arguments of the run passed
explicitly, for the pointer `args` of the sieving thread (`rp-private.h:574`), which `worker_init`
sets and through which `sift` reads them; no search intervals `iv` of the sieving thread, which
`worker_init` clears (`find_points.c:3130`) and `run_block` sets for each block (`rp-private.h:574`;
stage H); no pool, slot and stop flag of a thread of the pool, the flag by which the pool of threads
tells it to abandon its block (`pool`, `slot`, `stop`, `rp-private.h:584-585`; stage I); natural
numbers and integers for the `long`s; no measurements of the phases (`RP_SIFT_TIC`, `RP_SETUP_TIC`,
`RP_INIT_TIC` and their `TOC`) and no output under `DEBUG`. -/
def sift (c : List Int) (d H A b : Nat) (rev : Bool) (sp1 : Nat)
    (rows : List (Nat × Array (Thunk (Array UInt64)))) (es3 : List SieveEntry) (mgs3 : List Nat)
    (cw : UInt64) :
    Id (Array (Int × Int × Int)) := do
  let specs : List SieveSpec := rows.map fun (p, rs) ↦ ⟨p, rs[b % p]!.get⟩
  let w : Thunk (List Int) := .mk fun _ ↦ BruteForce.scaledCoeffs c d b
  let checks : Thunk (List CheckSpec) := .mk fun _ ↦ fillChecks b H es3 mgs3
  let wLow := -(H : Int) / rbaLength
  let wHigh := (H : Int) / rbaLength + 1
  let mut range := A
  let mut w0 := wLow
  let mut w1 := wLow + A
  let mut out := #[]
  while w0 < wHigh do
    if wHigh < w1 then
      w1 := wHigh
      range := (w1 - w0).toNat
    let maskLow := if w0 = wLow then (-(H : Int) - rbaLength * wLow).toNat else 0
    let maskHigh := if w1 = wHigh then rbaLength - 1 - ((H : Int) % rbaLength).toNat else 0
    out := out ++ (← siftPiece w d b rev sp1 specs checks cw w0 range maskLow maskHigh)
    w0 := w1
    w1 := w1 + range
  return out

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

-- Curves without points modulo 3, 5 and 7, on which ratpoints takes the exit at that prime
-- (`ratpoints '20 6 -14 12 -10' 30 -v` says `no points mod p = 3`, and so do
-- `ratpoints '-2 -20 7 15 2' 30 -v` for 5 and `ratpoints '20 7 -18 0 3' 30 -v` for 7): on both
-- paths the table of that prime is none and those of the primes before it are not, and the curve
-- has no points of height at most 30.
#guard ([([20, 6, -14, 12, -10], [false]), ([-2, -20, 7, 15, 2], [true, false]),
    ([20, 7, -18, 0, 3], [true, true, false])] : List (List Int × List Bool)).all
  fun (c, tables) ↦ bruteForce c 30 == [] && [true, false].all fun u ↦
    ([3, 5, 7].take tables.length).map (fun p ↦ (Id.run (examinePrime? c 4 p u)).isSome) == tables

-- The plain sieve of a denominator is the survivor test of the numerators.
#guard
  let es := [3, 5, 7].map fun p ↦
    (⟨p, [.prime (examinePrime [1, 2, 3, 4, 5, 6, 7] 6 p)], magic p⟩ : SieveEntry)
  (Id.run (sieveDen 20 7 es)).toList ==
    (List.range 41).map fun i : Nat ↦ survives es 7 ((i : Int) - 20)

-- The survivors of the plain sieve of `y ^ 2 = x ^ 3 - 2` for the denominator 100 give the point
-- `(129 : 3830 : 100)`, which every numerator gives as well.
#guard
  let es := [3, 5, 7, 11, 13].map fun p ↦
    (⟨p, [.prime (examinePrime [-2, 0, 0, 1] 3 p)], magic p⟩ : SieveEntry)
  (Id.run (checkDen [-2, 0, 0, 1] 3 130 100 (Id.run (sieveDen 130 100 es)))).toList ==
    [(129, 3830, 100), (129, -3830, 100)] &&
  (Id.run (checkDen [-2, 0, 0, 1] 3 130 100 (Vector.replicate _ true))).toList ==
    [(129, 3830, 100), (129, -3830, 100)]

-- `andBitArray` on two bit arrays: bit array 1 is and-ed with bit array 2 of a row, word by word,
-- and bit array 0 stays as it is.
#guard
  let v : Vector UInt64 (2 * rbaPack) := .ofFn fun i ↦ 0x0123456789abcdef * (i.val.toUInt64 + 1)
  let row : Array UInt64 := .ofFn (n := 3 * rbaPack) fun i ↦ ~~~(1 <<< i.val.toUInt64)
  (List.range (2 * rbaPack)).all fun y ↦ (andBitArray v 1 row 2)[y]! ==
    if y / rbaPack = 1 then v[y]! &&& row[rbaPack * 2 + y % rbaPack]! else v[y]!

-- The masks on two bit arrays: the low mask keeps bit `t` of word `y` exactly when
-- `s ≤ 64 y + t`, and the high mask on bit array 1 exactly when `64 y + t + s < 2 rbaLength`.
#guard
  let v : Vector UInt64 (2 * rbaPack) := .ofFn fun i ↦ 0x0123456789abcdef * (i.val.toUInt64 + 1)
  ([0, 1, 63, 64, 65, 130, rbaLength - 1].filter (· < rbaLength)).all fun s ↦
    (List.range (2 * rbaPack)).all fun y ↦ (List.range 64).all fun t ↦
      (clearLowBits v s)[y]!.toBitVec.getLsbD t ==
        (v[y]!.toBitVec.getLsbD t && decide (s ≤ 64 * y + t)) &&
      (clearHighBits v 1 s)[y]!.toBitVec.getLsbD t ==
        (v[y]!.toBitVec.getLsbD t && decide (64 * y + t + s < rbaLength * 2))

-- `isZeroAt` on three bit arrays: the first has a set bit in its last word, the second none, the
-- third one in its first word.
#guard
  let v : Vector UInt64 (3 * rbaPack) :=
    ((Vector.replicate _ 0).set! (rbaPack - 1) 0x8000000000000000).set! (2 * rbaPack) 1
  [isZeroAt v 0, isZeroAt v 1, isZeroAt v 2] == [false, true, false]

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
    (⟨p, [.prime (examinePrime c 6 p)], magic p⟩ : SieveEntry)
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
    Id.run (stage3 a [checkOf 7 100 ⟨9, [.power pw], magic 9⟩ (magic 9)])

-- The exact check with the test for common factors in front is the check of the reference.
#guard ([([-2, 0, 0, 1], 3), ([1, 0, 126, 0, 441], 4)] : List (List Int × Nat)).all fun (c, d) ↦
  [1, 2, 21, 100].all fun b : Nat ↦ [false, true].all fun rev ↦
    (BruteForce.numerators 130).all fun a ↦
      let w := BruteForce.scaledCoeffs c d b
      let f : Int := if d % 2 = 1 then b else 1
      checkNum w f b rev a == if Int.gcd a b = 1 then checkPoint (.pure w) d b rev a else []

-- The second stage on a bit array and on one of its words against the words and-ed with the rows of
-- all its moduli, for bit arrays that the rows leave nonzero and that they clear on the way, at
-- word numbers below and above zero.
#guard
  let es := [3, 5, 7, 11, 13].map fun p ↦
    (⟨p, [.prime (examinePrime [1, 2, 3, 4, 5, 6, 7] 6 p)], magic p⟩ : SieveEntry)
  let specs : List SieveSpec := es.map fun e ↦ ⟨e.p, e.row 7⟩
  ([.replicate rbaPack (~~~0), .ofFn fun κ ↦ 1 <<< (κ.val * 13).toUInt64,
      .ofFn fun κ ↦ 0x0123456789abcdef * (κ.val.toUInt64 + 1), .replicate rbaPack 0] :
      List (Vector UInt64 rbaPack)).all fun nums ↦ [-5, 0, 7, 1000].all fun i ↦
    (List.range rbaPack).all fun κ ↦
      let ref := specs.foldl (fun x s ↦ x &&& s.row[rbaPack * (i % (s.p : Int)).toNat + κ]!)
        nums[κ]!
      (Id.run (secondStage specs i nums))[κ]! == ref &&
        Id.run (secondStageWord specs i κ nums[κ]!) == ref

-- The rows as words against the row test: bit `t` of word `j` of the row of `b` says whether the
-- row admits `64 j + t`, for denominators of several residues modulo `p`, `0` among them, and for
-- a prime above 64.
#guard
  [3, 5, 7, 13, 67].all fun p ↦
    let e : SieveEntry := ⟨p, [.prime (examinePrime [1, 2, 3, 4, 5, 6, 7] 6 p)], magic p⟩
    [0, 1, 2, 5, p + 3].all fun b ↦
      let row := e.row b
      row.size == p * rbaPack && (List.range (p * rbaPack)).all fun j ↦
        (List.range 64).all fun t ↦ row[j]!.toBitVec.getLsbD t == e.admits b (64 * j + t)

-- The rows as words of composite moduli against the row test: the prime power 9, and the products
-- 15 = 3 · 5 and 45 = 9 · 5, for denominators prime to them and not.
#guard
  let c := [1, 2, 3, 4, 5, 6, 7]
  let p9 : Factor := .power (Id.run (examinePower c 6 3 2 true))
  let e3 : Factor := .prime (examinePrime c 6 3)
  let e5 : Factor := .prime (examinePrime c 6 5)
  ([⟨9, [p9], magic 9⟩, ⟨15, [e3, e5], magic 15⟩, ⟨45, [p9, e5], magic 45⟩] :
      List SieveEntry).all fun e ↦ [0, 1, 3, 5, 6, 10, 18].all fun b ↦
    let row := e.row b
    row.size == e.p * rbaPack && (List.range (e.p * rbaPack)).all fun j ↦
      (List.range 64).all fun t ↦ row[j]!.toBitVec.getLsbD t == e.admits b (64 * j + t)

-- The row of `0` against the pattern `sieves0` that the build of ratpoints generates, for 3, 5, 7,
-- 11 and 13: the first `p` of its `RBA_PACK * p` words, which repeat them.
#guard
  ([(3, #[0x6db6db6db6db6db6, 0xb6db6db6db6db6db, 0xdb6db6db6db6db6d]),
    (5, #[0xef7bdef7bdef7bde, 0xdef7bdef7bdef7bd, 0xbdef7bdef7bdef7b, 0x7bdef7bdef7bdef7,
      0xf7bdef7bdef7bdef]),
    (7, #[0x7efdfbf7efdfbf7e, 0xbf7efdfbf7efdfbf, 0xdfbf7efdfbf7efdf, 0xefdfbf7efdfbf7ef,
      0xf7efdfbf7efdfbf7, 0xfbf7efdfbf7efdfb, 0xfdfbf7efdfbf7efd]),
    (11, #[0xff7feffdffbff7fe, 0xfdffbff7feffdffb, 0xf7feffdffbff7fef, 0xdffbff7feffdffbf,
      0x7feffdffbff7feff, 0xffbff7feffdffbff, 0xfeffdffbff7feffd, 0xfbff7feffdffbff7,
      0xeffdffbff7feffdf, 0xbff7feffdffbff7f, 0xffdffbff7feffdff]),
    (13, #[0xffefff7ffbffdffe, 0xffdffefff7ffbffd, 0xffbffdffefff7ffb, 0xff7ffbffdffefff7,
      0xfefff7ffbffdffef, 0xfdffefff7ffbffdf, 0xfbffdffefff7ffbf, 0xf7ffbffdffefff7f,
      0xefff7ffbffdffeff, 0xdffefff7ffbffdff, 0xbffdffefff7ffbff, 0x7ffbffdffefff7ff,
      0xfff7ffbffdffefff])] : List (Nat × Array UInt64)).all fun (p, ws) ↦
    ((⟨p, [.prime (examinePrime [1, 0, 1] 2 p)], magic p⟩ : SieveEntry).row 0).extract 0 p == ws

-- The rows of the residues: one thunk for each of the `p` residues, the thunk of `r` giving the
-- row of `r`.
#guard
  let e : SieveEntry := ⟨7, [.prime (examinePrime [1, 2, 3, 4, 5, 6, 7] 6 7)], magic 7⟩
  e.rows.size == 7 && (List.range 7).all fun r ↦ e.rows[r]!.get == e.row r

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

-- The first stage against the survivor test: bit `t` of word `y` of a piece is bit `t` of the class
-- word and the survivor test of the numerator `rbaLength w0 + 64 y + t`, for pieces from below and
-- above zero with the moduli 3, 5 and 7, and with `n < r`, `r = 0`, and whole periods and a rest
-- after the first `r` bit arrays; the class words all ones, the word of the denominators
-- `≡ 1 (mod 4)` of `1 2 3 4 5 6 7` (the numerators `≢ 1 (mod 4)`), and the numerators
-- `≡ 1 (mod 8)`.
#guard
  let es := [3, 5, 7].map fun p ↦
    (⟨p, [.prime (examinePrime [1, 2, 3, 4, 5, 6, 7] 6 p)], magic p⟩ : SieveEntry)
  ([(-9, 1), (-9, 12), (-35, 4), (6, 2), (15, 17)] : List (Int × Nat)).all fun (w0, n) ↦
    [1, 10].all fun b ↦
      [~~~0, 0xdddddddddddddddd, 0x0202020202020202].all fun cw ↦
        let v := Id.run (andRows (es.map fun e ↦ ⟨e.p, e.row b⟩) cw w0 n (Vector.replicate _ 0))
        (List.range (n * rbaPack)).all fun y ↦ (List.range 64).all fun t ↦
          v[y]!.toBitVec.getLsbD t ==
            (cw.toBitVec.getLsbD t && survives es b (rbaLength * w0 + 64 * y + t))

-- One bit array in both arms of the second stage against the reference: the points of the
-- numerators of its set bits that the rows of the moduli of the second stage admit, and the rows of
-- the primes of the third stage, for the point `(129 : 3830 : 100)` of `y ^ 2 = x ^ 3 - 2` and
-- other denominators, bit arrays below and above zero, and the moduli cut into the two stages in
-- several places.
#guard
  let c := [-2, 0, 0, 1]
  let es := [3, 5, 7, 11, 13].map fun p ↦ (⟨p, [.prime (examinePrime c 3 p)], magic p⟩ : SieveEntry)
  [0, 2, 5].all fun sp2 ↦ [1, 7, 100].all fun b : Nat ↦ [-2, 0, 3].all fun i : Int ↦
    ([.replicate rbaPack (~~~0), .ofFn fun κ ↦ 0x0123456789abcdef * (κ.val.toUInt64 + 1)] :
        List (Vector UInt64 rbaPack)).all fun nums ↦
      let w := BruteForce.scaledCoeffs c 3 b
      let es3 := es.drop sp2
      let checks := fillChecks b 2000 es3 (es3.map (·.magic))
      let run (useLong : Bool) := (Id.run (siftBitArray useLong (.pure w) 3 b false
        ((es.take sp2).map fun e ↦ ⟨e.p, e.row b⟩) (.pure checks) i nums #[])).toList
      let ref := (((List.range rbaLength).filter fun k ↦
          nums[k / 64]!.toBitVec.getLsbD (k % 64)).map fun k : Nat ↦ i * rbaLength + k).flatMap
        fun a ↦ if survives es b a then checkNum w b b false a else []
      run false == ref && run true == ref

-- The set bits of a word, lowest first: with `F(a, 1) = a ^ 2` and no third stage, every numerator
-- `a0 + t` of a set bit `t` gives its points, after the points already in the array; the
-- numerators, each once, are those of the set bits in increasing order.
#guard
  ([0, 1, 0x8000000000000000, 0xf0f0f0f0f0f0f0f0, 0x123456789abcdef1] : List UInt64).all fun x ↦
    let pts :=
      (Id.run (walkWord (.pure [0, 0, 1]) 2 1 false (.pure []) x (-37) #[(5, 5, 5)])).toList
    pts == (5, 5, 5) :: ((List.range 64).filter x.toBitVec.getLsbD).flatMap
      (fun t : Nat ↦ checkNum [0, 0, 1] 1 1 false (-37 + t)) &&
    ((pts.drop 1).map (·.1)).eraseDups ==
      ((List.range 64).filter x.toBitVec.getLsbD).map fun t : Nat ↦ -37 + (t : Int)

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

-- The scan of pieces made by hand, with `F(a, 1) = a ^ 2` and no second or third stage: the points
-- of the numerators of the set bits of the words in increasing order, for pieces from below and
-- above zero, with a zero bit array between, before and after bit arrays whose words have bits at
-- both ends, of one bit array, and of zero bit arrays only; the place of the sentinel holds other
-- words at first.
#guard
  ([(3, -2, [1]), (2, 1, [0]), (2, -1, [1]), (1, 5, []), (2, 0, [0, 1])] :
      List (Nat × Int × List Nat)).all fun (n, w0, zeros) ↦
    let v : Vector UInt64 ((n + 1) * rbaPack) := .ofFn fun ⟨y, _⟩ ↦
      if zeros.contains (y / rbaPack) then 0
      else if y % 2 = 0 then 0x8000000000000001 else 1 <<< (y * 7 % 64).toUInt64
    (Id.run (scanPiece (.pure [0, 0, 1]) 2 1 false [] (.pure []) w0 n v)).toList ==
      ((List.range (n * rbaPack)).flatMap fun y : Nat ↦
        ((List.range 64).filter v[y]!.toBitVec.getLsbD).map fun t : Nat ↦
          rbaLength * w0 + 64 * y + t).flatMap (checkNum [0, 0, 1] 1 1 false)

-- The scan of pieces whose bits are a test of their numerators, with no second or third stage: the
-- points of the numerators of the piece that pass the test, in increasing order.
#guard
  let keep (a : Int) : Bool := a % 5 == 2 || a % 64 == 63
  ([(2, -1), (1, 3)] : List (Nat × Int)).all fun (n, w0) ↦
    let v : Vector UInt64 ((n + 1) * rbaPack) := .ofFn fun ⟨y, _⟩ ↦
      (List.range 64).foldl (fun x (t : Nat) ↦
        if keep (rbaLength * w0 + 64 * (y : Int) + t) then x ||| 1 <<< t.toUInt64 else x) 0
    (Id.run (scanPiece (.pure [0, 0, 1]) 2 1 false [] (.pure []) w0 n v)).toList ==
      (((List.range (n * rbaLength)).map fun k : Nat ↦ rbaLength * w0 + k).filter keep).flatMap
        (checkNum [0, 0, 1] 1 1 false)

-- One piece against the reference over its survivors: the points of the numerators from
-- `rbaLength w0 + maskLow` to `rbaLength (w0 + n) - 1 - maskHigh` that survive the moduli, for
-- pieces from below and above zero with no mask, with one of them and with both, among them the
-- piece of the numerators `-130, …, 130`, and the moduli in the three stages cut in several places,
-- among them all in the first stage, none, and all in the second or in the third; the masks around
-- the numerator 129 of the point `(129 : 3830 : 100)` of `y ^ 2 = x ^ 3 - 2` keep it or drop it.
#guard
  let c := [-2, 0, 0, 1]
  let es := [3, 5, 7, 11, 13].map fun p ↦ (⟨p, [.prime (examinePrime c 3 p)], magic p⟩ : SieveEntry)
  let piece (sp1 sp2 b : Nat) (w0 : Int) (n mL mH : Nat) : List (Int × Int × Int) :=
    let es3 := es.drop sp2
    (Id.run (siftPiece (.pure (BruteForce.scaledCoeffs c 3 b)) 3 b false sp1
      ((es.take sp2).map fun e ↦ ⟨e.p, e.row b⟩) (.pure (fillChecks b 1000 es3 (es3.map (·.magic))))
      (~~~0) w0 n mL mH)).toList
  piece 5 5 100 0 1 129 0 == [(129, 3830, 100), (129, -3830, 100)] &&
    piece 2 3 100 0 1 130 0 == [] &&
    piece 1 4 100 0 1 0 (rbaLength - 130) == [(129, 3830, 100), (129, -3830, 100)] &&
    piece 0 0 100 0 1 0 (rbaLength - 129) == [] &&
    ([(5, 5), (0, 0), (0, 5), (2, 4), (3, 3), (1, 2), (4, 2)] : List (Nat × Nat)).all
      fun (sp1, sp2) ↦
    ([(-1, 2, 0, 0), (-1, 2, rbaLength - 130, rbaLength - 131), (0, 1, 129, 0), (0, 1, 130, 0),
        (0, 1, 0, rbaLength - 130), (0, 1, 0, rbaLength - 129), (-3, 2, 5, 7), (1, 3, 0, 0)] :
        List (Int × Nat × Nat × Nat)).all fun (w0, n, mL, mH) ↦ [1, 7, 100].all fun b ↦
      piece sp1 sp2 b w0 n mL mH == BruteForce.pointsOfDen c 3 b
        (((List.range (n * rbaLength - mL - mH)).map fun k : Nat ↦ rbaLength * w0 + mL + k).filter
          (survives es b))

-- One denominator against the plain sieve: the points of the numerators `-300, …, 300` of a few
-- denominators, with pieces of one, two and three bit arrays, the last piece cut at `wHigh`, the
-- moduli in the three stages cut at every pair of positions `sp1 ≤ sp2`, and at `sp1 > sp2`; and
-- with the flag of the reversal the same points, mapped.
#guard
  let c := [-2, 0, 0, 1]
  let es := [3, 5, 7, 11, 13].map fun p ↦ (⟨p, [.prime (examinePrime c 3 p)], magic p⟩ : SieveEntry)
  let cuts := (List.range 6).flatMap fun sp2 ↦ (List.range (sp2 + 1)).map (·, sp2)
  ((4, 2) :: cuts).all fun (sp1, sp2) ↦
    [1, 7, 100].all fun b ↦ [1, 2, 3].all fun A ↦ [false, true].all fun rev ↦
      let ref := (Id.run (checkDen c 3 300 b (Id.run (sieveDen 300 b es)))).toList
      let es3 := es.drop sp2
      (Id.run (sift c 3 300 A b rev sp1 ((es.take sp2).map fun e ↦ (e.p, e.rows)) es3
        (es3.map (·.magic)) (~~~0))).toList == if rev then ref.map swapPoint else ref

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
