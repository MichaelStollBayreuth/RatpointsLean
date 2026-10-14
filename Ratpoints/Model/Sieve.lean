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
(`Ratpoints.Sieve.SieveEntry.row`), one piece of bit arrays from the first stage to the points of
its numerators (`Ratpoints.Sieve.siftPiece`), the numerators of one denominator in pieces, from a
class word, the numerators modulo 64 from which the first stage starts (`Ratpoints.Sieve.sift`), and
the points at infinity (`Ratpoints.Sieve.pointsAtInfinity`). The tables of the primes and of the
prime powers and the sieve entries of the moduli, with the rows of a denominator, are in
`Ratpoints.Model.Tables`; the loop over the denominators (`Ratpoints.Sieve.sieveRun`), with the
2-adic information that gives the words of the classes of the denominators modulo 64, is in
`Ratpoints.Model.Denominators`. The plain sieve of one denominator, one Boolean per numerator
(`Ratpoints.Sieve.sieveDen`), and the test for common factors and the exact check of its survivors
(`Ratpoints.Sieve.checkDen`) are not part of the run: they are the reference of the bit arrays of
words (`Ratpoints.Sieve.toList_run_sift_eq_checkDen`). Every row, and the word of the class of a
denominator in the 2-adic information, let every point through, so the sieve of a denominator finds
exactly its points in the brute-force reference `Ratpoints.bruteForce`, in the same order, each
mapped by `Ratpoints.Sieve.swapPoint` when the flag of the reversal is set: the map gives the point
of the caller's curve for a point of a polynomial that the reversal check has reversed
(`Ratpoints.Setup.reversal`), the check of a numerator and the points at infinity deliver the mapped
points when their flag is set, and the components from the run down to the check hand the flag on.
The rows of `0` that the build of ratpoints generates are computed here as words, by
`Ratpoints.Sieve.SieveEntry.row`.

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
* `Ratpoints.Sieve.andRows`: the first stage over a piece of bit arrays, from a class word, the rows
  of the moduli and-ed into its words.
* `Ratpoints.Sieve.checkNum`, `Ratpoints.Sieve.walkWord`: the test for common factors and the exact
  check of one numerator, its points mapped by `Ratpoints.Sieve.swapPoint` when the flag of the
  reversal is set, and the walk through the set bits of a word, lowest first, each giving the check
  of its numerator.
* `Ratpoints.Sieve.scanPiece`: the scan over the bit arrays of a piece up to a sentinel, stepping
  over those that are zero, and the walk through the words of the others.
* `Ratpoints.Sieve.siftPiece`: one piece of bit arrays, from the first stage and the masks at its
  two ends to the points of its numerators.
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
bit arrays of words: for pieces of at least one bit array and moduli `p > 0`, the points that
`Ratpoints.Sieve.sift` finds with the rows of these entries (`Ratpoints.Sieve.SieveEntry.rows`) from
a class word are those that `Ratpoints.Sieve.checkDen` finds on it whose numerators pass the class
word, all of them for the word `~~~0` or any class word that admits the numerators of the points
(such as the word `nb[b mod 64]` of `Ratpoints.Sieve.twoAdic`), each mapped by
`Ratpoints.Sieve.swapPoint` when the flag of the reversal is set
(`Ratpoints.Sieve.toList_run_sift_eq_checkDen`). -/
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
for odd `d`, then `(a, y, b)` and, for `y ≠ 0`, `(a, -y, b)` when `F(a, b) = y ^ 2` with `y ≥ 0`. On
the plain sieve `Ratpoints.Sieve.sieveDen` of sieve entries with `p > 0` it is the reference of the
bit arrays of words: `Ratpoints.Sieve.sift` with the rows of these entries
(`Ratpoints.Sieve.SieveEntry.rows`), in pieces of at least one bit array, finds the points that it
finds whose numerators pass the class word, all of them from the class word `~~~0` or from any class
word that admits the numerators of the points (such as the word `nb[b mod 64]` of
`Ratpoints.Sieve.twoAdic`), each mapped by `Ratpoints.Sieve.swapPoint` when the flag of the reversal
is set (`Ratpoints.Sieve.toList_run_sift_eq_checkDen`). -/
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
packing of the 2-adic classes and a multiple of `p` that keeps the index non-negative (stage F3),
and no pointers `start` and `end` into the row, which only the chunked first stage reads (stage F4):
the components index the row by the word number modulo `p`. -/
structure SieveSpec where
  /-- The modulus. -/
  p : Nat
  /-- The row: `p` bit arrays of `Ratpoints.rbaPack` words. -/
  row : Array UInt64

/-! ### The points of a reversed search -/

/-- The point of the caller's curve for the point `(a, y, b)` of the reversed curve: `(b, y, a)` for
`a ≥ 0` and `(-b, y, -a)` for `a < 0`. After the reversal check has reversed the polynomial
(`Ratpoints.Setup.reversal`), the C code delivers the mapped points: the check of a numerator maps
each point that it finds by this map, and the points at infinity take the candidate `(0, 1)` in
place of `(1, 0)`, which gives the image of `(1, y, 0)`; the two components deliver the mapped
points when their flag of the reversal is set (`Ratpoints.Sieve.checkNum`,
`Ratpoints.Sieve.pointsAtInfinity`). It maps the normalized points of height at most `H` of the
reversed curve one to one onto those of the caller's curve
(`Ratpoints.Sieve.perm_map_swapPoint_bruteForce`). Its negations `-b` and `-a` stay in the range of
a `long`, since `|a| ≤ H`, `1 ≤ b ≤ H` and `H < 2 ^ 63` (`Ratpoints.fitsLong_neg`). -/
def swapPoint (q : Int × Int × Int) : Int × Int × Int :=
  if 0 ≤ q.1 then (q.2.2, q.2.1, q.1) else (-q.2.2, q.2.1, -q.1)

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

C: `sift.c:291-312`, `sift.c:943-1022`, `sift.c:1083-1086`, `sift.c:1174-1202`,
`find_points.c:1098`, `rp-private.h:129-132`, `rp-private.h:203-204`, `rp-private.h:235`,
`rp-private.h:261`, `rp-private.h:285`

Deviation: every modulus in the first stage, over every bit array, for the second stage, which and-s
the rows of its moduli, one after the other, into each bit array that the scan finds nonzero, and
stops as soon as no bit of it is left, and the third stage, which tests one numerator at a time
after the test for common factors, stops at the first prime that rejects it and skips the primes
that divide `b` (stage F2); the first stage of the builds with one register per chunk, for the
chunks of sixteen registers of the default build with the legs over the tail of a piece (stage F4);
the class word written one word at a time from the first, where ratpoints writes the 2-adic pattern
of the class of `b` into the bit arrays from the last, and the pattern of the plain layout, one word
repeated, for the packed pattern of a stride `2^k` (stage F3), the class word written into each word
of a bit array, for the vector `RBA(packed)` that `get_2adic_info` makes once per class
(`find_points.c:1098`) and `_ratpoints_sift0` copies into each bit array (`bits64`, `sift.c:519`,
`sift.c:954`); the row of the word number `w` at index `w mod p`, where ratpoints adds the offset of
the packing and a multiple of `p` that keeps the index non-negative, and reduces by a multiplication
when that is exact (stages F2 and F3); indices for the pointers into the rows and into the
survivors, and the number of whole periods and the rest computed before their loops; natural numbers
and integers for the `long`s (stage F); no count of the ands of the second stage under
`RP_PHASE_COUNTS`, and no output under `DEBUG`. -/
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

/-- The points of the numerator `a` over the denominator `b`, as the brute-force reference checks
it (`Ratpoints.BruteForce.pointsOfDen`), each mapped by `Ratpoints.Sieve.swapPoint` when the flag
`rev` of the reversal is set: none when `a` and `b` have a common factor, and otherwise
`(a, y, b)` and, for `y ≠ 0`, `(a, -y, b)` when `v = y ^ 2` with `y ≥ 0`, for the value `v` of
Horner's rule in `a` on `w`, times `f`. For the products `w` of the coefficients `cₖ` with the
powers `b^(d - k)` (`Ratpoints.BruteForce.scaledCoeffs`), and `f = b` for odd `d` and `f = 1` for
even `d`, `v` is the value `F(a, b)` of the binary form. So the check with the flag set gives the
points of the check without it, mapped (`Ratpoints.Sieve.checkNum_eq_map`), which after a reversal
are points of the caller's curve.

C: `sift.c:202-205`, `sift.c:318-343`, `sift.c:438-446`, `find_points.c:5250-5338`

Deviation: a plain `gcd`, for the binary `gcd` of `relprime`, whose loop body has no branch (stage
F2); the third stage of `accepted` is applied with the other moduli in the first stage
(`Ratpoints.Sieve.andRows`, stage F2); the products `w` and the factor `f` come in as arguments,
computed for every denominator, where `_ratpoints_check_point` computes the products when the first
survivor of `b` reaches it; the flag `rev` comes in as an argument too, handed down from
`Ratpoints.Sieve.sieveRun` through the components that call the check, for the bit
`RATPOINTS_REVERSED` of the flags of the search, which `_ratpoints_check_point` reads through its
worker (`args->flags`); a list of points, for the callback `process` and for the count of points
that `_ratpoints_check_point` returns, with no stop that `process` may request, and no
`RATPOINTS_NO_Y` and no `RATPOINTS_NO_CHECK` (stage G); no counts of the numerators that pass the
test for common factors and the third stage (`n_coprime`, `n_checks`), which ratpoints reads to
correct the moduli between the blocks of the run (stage I); integers for the `long`s `a` and `b` and
the operands of `relprime` (stage F2; the negations of `Ratpoints.Sieve.swapPoint` stay `long`s by
`Ratpoints.fitsLong_neg`); no measurements of the time of the check and of its products (`RP_CHECK`,
`RP_BC_TIC`, `RP_BC_TOC` under `RP_PHASE_TIMING`), and no output under `DEBUG`. -/
def checkNum (w : List Int) (f b : Int) (rev : Bool) (a : Int) : List (Int × Int × Int) :=
  if Int.gcd a b = 1 then
    let pts := BruteForce.pointsAbove a b (BruteForce.horner w a * f)
    if rev then pts.map swapPoint else pts
  else []

/-- The set bits of the word `x`, lowest first, bit `t` standing for the numerator `a0 + t`: while
`x ≠ 0`, the points of the numerator `a0 + t` for the lowest set bit `t` of `x`
(`Ratpoints.Sieve.ctz`) over the denominator `b` (`Ratpoints.Sieve.checkNum`, with the products
`w`, the factor `f` and the flag `rev` of the reversal) are appended to `out`, and that bit is
cleared by `x &&& (x - 1)`. This is the loop `RP_EACH_SET_BIT` of the C code with the body that the
extraction runs for each set bit.

C: `sift.c:262-264`, `sift.c:1227-1255`, `sift.c:1265-1292`

Deviation: bit `t` for the numerator `a0 + t`, where the step from one bit to the next is the stride
`2^k` of the packing of the 2-adic class of `b` (stage F3); the lowest set bit by the loop of
`RP_CTZL` for a compiler without the builtin (`Ratpoints.Sieve.ctz`); one definition for the body at
both places of the extraction, the first word of a bit array and the others; natural numbers and
integers for the `long`s (stage F); no count of the numerators that reach the test for common
factors (`n_bits`), which ratpoints reads to correct the moduli between the blocks of the run (stage
I), and no counts under `RP_PHASE_COUNTS`; no stop that the callback `process` may request (`quit`,
stage G), and no output under `DEBUG`. -/
def walkWord (w : List Int) (f : Int) (b : Nat) (rev : Bool) (x : UInt64) (a0 : Int)
    (out : Array (Int × Int × Int)) :
    Id (Array (Int × Int × Int)) := do
  let mut x := x
  let mut out := out
  while x != 0 do
    let t ← ctz x
    out := out ++ (checkNum w f b rev (a0 + t)).toArray
    x := x &&& (x - 1)
  return out

/-- The scan over a piece, the bit arrays with the word numbers `w0, …, w0 + n - 1`, which are the
first `n` bit arrays of `surv`, and the extraction of the points of their numerators: a sentinel, a
bit array of ones, is written into bit array `n`, just past the piece; then from bit array `0` on,
the bit arrays that are zero (`Ratpoints.Sieve.isZeroAt`) are stepped over, the scan stops at the
sentinel, and the words of each of the other bit arrays `pos` are walked through in turn
(`Ratpoints.Sieve.walkWord`, with the products `w`, the factor `f`, the denominator `b` and the flag
`rev` of the check), bit `t` of word `κ` standing for the numerator
`rbaLength (w0 + pos) + 64 κ + t`, for the number `rbaLength` of bits of a bit array
(`Ratpoints.rbaLength`). The test of the C code that the bit array is still nonzero after the second
stage, which the model applies in the first (`Ratpoints.Sieve.andRows`), is kept and always passes.

C: `sift.c:1061-1082`, `sift.c:1088-1092`, `sift.c:1213-1226`, `sift.c:1257-1264`,
`sift.c:1293-1299`, `rp-private.h:133`, `rp-private.h:135-136`, `rp-private.h:177-178`,
`rp-private.h:205`, `rp-private.h:236`, `rp-private.h:238-239`, `rp-private.h:262`,
`rp-private.h:264-266`, `rp-private.h:286`, `rp-private.h:288-289`

Deviation: the plain layout, bit `t` of the bit array with the word number `w` for the numerator
`rbaLength w + t`, where bit `t` stands for the numerator `a₀ + 2^k (rbaLength w + t)` of the
packing of the 2-adic class of `b` (stage F3); indices for the pointers into the survivors, and a
scan that holds its position as an index and reads the words of the bit array that it finds in
place, where ratpoints recovers the word number from a pointer difference and copies the bit array;
the sentinel `~zero` of every build as `Ratpoints.rbaPack` words `~~~0`, written one at a time, and
the reads `EXT0` and `EXT` as words of the array, for the vector type of the build, with one loop
over the words of a bit array for the read of the first word and the loop over the others; natural
numbers and integers for the `long`s (stage F); no count of the bit arrays that survive the first
stage (`n_arrays`), which ratpoints reads to correct the moduli between the blocks of the run (stage
I). -/
def scanPiece (w : List Int) (f : Int) (b : Nat) (rev : Bool) (w0 : Int) (n : Nat)
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
    let i := w0 + pos
    if !isZeroAt surv pos then
      let mut a0 := i * rbaLength
      for κ in [0:rbaPack] do
        out ← walkWord w f b rev surv[rbaPack * pos + κ]! a0 out
        a0 := a0 + 64
    pos := pos + 1
  return out

/-- One piece, the bit arrays with the word numbers `w0, …, w0 + n - 1`, and the points of its
numerators: a fresh array of `n + 1` bit arrays, the last one the place of the sentinel; the first
stage with the moduli and their rows `specs`, from the class word `cw` (`Ratpoints.Sieve.andRows`);
the lowest `maskLow` bits of the first bit array cleared if `maskLow ≠ 0`
(`Ratpoints.Sieve.clearLowBits`), and the highest `maskHigh` bits of the last bit array of the
piece, `n - 1`, if `maskHigh ≠ 0` (`Ratpoints.Sieve.clearHighBits`); and the scan with the
extraction (`Ratpoints.Sieve.scanPiece`, with the products `w`, the factor `f`, the denominator `b`
and the flag `rev` of the check). This is `_ratpoints_sift0` of the C code, with the allocation of
the survivors array that it works in.

C: `find_points.c:3119-3121`, `sift.c:498-531`, `sift.c:548`, `sift.c:1030-1041`,
`sift.c:1056-1058`, `sift.c:1300-1305`

Deviation: a fresh array of zeros for each piece, for the survivors array of the sieving thread,
which every piece reuses, with one bit array more for the alignment, and whose words `malloc` leaves
uninitialized; the piece by its first word number `w0` and its number `n` of bit arrays, for `w_low`
and `w_high`, and an index for the pointer to its last bit array; the moduli of all three stages
with their rows in `specs`, for the moduli of the first two stages with their rows in `sieves`, the
numbers `sp1`, `sp2` and `nchecks` of the moduli of the stages, which the sieving thread `wk` keeps,
and the table `checks` of the third stage (stage F2); the class word `cw`, the pattern `bits` of the
class `cls` (`sift.c:519`) at the stride 1, for the class itself, whose stride `k` and residue `a0`,
which the extraction reads (`sift.c:1221-1222`, `Ratpoints.Sieve.scanPiece`; `sift.c:1130-1131`
under `USE_LONG_IN_PHASE_2`), come with the packing (stage F3); no `magics` and no test `small` of
whether the reductions modulo the moduli can multiply by a reciprocal (stages F2 and F3); no count
of the words of the piece (`n_words`), which ratpoints reads to correct the moduli between the
blocks of the run (stage I); the products `w` and the factor `f` of the check as arguments, where
`_ratpoints_check_point` computes the products when the first survivor of `b` reaches it and
multiplies each value by `b` for odd `d`; a list of points, for the callback `process` with its
argument `info` and for the count `total` of points that `_ratpoints_sift0` returns, with no flag
`quit` for a stop that `process` may request (stage G); natural numbers and integers for the `long`s
(stage F); no measurements of the phases (`RP_TIC`, `RP_TOC`, `RP_PHASE_TIMING`) and no stop after
one of them (`RP_STOP_AFTER`). -/
def siftPiece (w : List Int) (f : Int) (b : Nat) (rev : Bool) (specs : List SieveSpec)
    (cw : UInt64) (w0 : Int) (n maskLow maskHigh : Nat) :
    Id (Array (Int × Int × Int)) := do
  let mut surv ← andRows specs cw w0 n (Vector.replicate ((n + 1) * rbaPack) 0)
  if maskLow ≠ 0 then surv := clearLowBits surv maskLow
  if maskHigh ≠ 0 then surv := clearHighBits surv (n - 1) maskHigh
  scanPiece w f b rev w0 n surv

/-! ### One denominator -/

/-- The points of the denominator `b`, its numerators `-H, …, H` in pieces of at most `A` bit
arrays, for `A ≥ 1` (for `A = 0` the loop does not end), from the class word `cw` of `b`, the
numerators modulo 64 that the 2-adic information admits (`Ratpoints.Sieve.twoAdic`): for each
modulus `p` with its rows `rs` in `rows`, the row of `b` is that of the residue `b mod p`, which its
thunk makes when it is first needed (`Ratpoints.Sieve.SieveEntry.rows`); the products `w` of the
coefficients `cₖ` with the powers `b^(d - k)` (`Ratpoints.BruteForce.scaledCoeffs`) and the factor
`f`, `b` for odd `d` and `1` for even `d`, are those of the check, which gets the flag `rev` of the
reversal too; for the number `rbaLength` of bits of a bit array (`Ratpoints.rbaLength`), the bit
arrays have the word numbers from `wLow = ⌊-H / rbaLength⌋` to `wHigh - 1`, for
`wHigh = ⌊H / rbaLength⌋ + 1`; and while `w0 < wHigh`, the piece of the word numbers
`w0, …, w1 - 1`, for `w1 = min (w0 + A) wHigh`, gives its points (`Ratpoints.Sieve.siftPiece`, with
the class word), with the low mask `-H - rbaLength wLow` if it is the first piece and the high mask
`rbaLength - 1 - (H mod rbaLength)` if it is the last, so that the numerators that the masks leave
lie end to end and make up `-H, …, H`.

C: `find_points.c:3149-3170`, `find_points.c:3442-3488`, `find_points.c:3490-3561`,
`find_points.c:3563-3617`, `sift.c:405-431`

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
tables, which threads share; every modulus with its row, those of the third stage too, for the
moduli of the first two stages with their rows, the offset of the packing and the end of the row
(`sieve_spec`), and the table `checks` of the third stage, which `fill_checks` fills when the first
numerator of `b` reaches that stage, with the inverse of `b` modulo each of its moduli, from
`b mod p` by a multiplication when `b` is small, and the magic and the bias of the reductions (stage
F2); the products `w` and the factor `f` computed for every denominator, where
`_ratpoints_check_point` computes the products when the first survivor of `b` reaches it
(`compute_bc`) and multiplies each value by `b` for odd `d`; no count of the denominators sieved
(`n_sifts`), which ratpoints reads to correct the moduli between the blocks of the run (stage I),
and no flag `stage3_filled` (stage F2); a list of points, for the callback `process` with its
argument `info` and for the count `total` of points that `sift` returns, with no stop that `process`
may request (`quit`, stage G) or that the pool of threads sends (`stop`); natural numbers and
integers for the `long`s (stage F); no measurements of the phases (`RP_SIFT_TIC`, `RP_SETUP_TIC`,
`RP_INIT_TIC` and their `TOC`) and no output under `DEBUG`. -/
def sift (c : List Int) (d H A b : Nat) (rev : Bool)
    (rows : List (Nat × Array (Thunk (Array UInt64)))) (cw : UInt64) :
    Id (Array (Int × Int × Int)) := do
  let specs : List SieveSpec := rows.map fun (p, rs) ↦ ⟨p, rs[b % p]!.get⟩
  let w := BruteForce.scaledCoeffs c d b
  let f : Int := if d % 2 = 1 then b else 1
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
    out := out ++ (← siftPiece w f b rev specs cw w0 range maskLow maskHigh)
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
      List SieveEntry).all fun e ↦
    [0, 1, 3, 5, 6, 10, 18].all fun b ↦
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

-- The set bits of a word, lowest first: with `F(a, 1) = a ^ 2`, every numerator `a0 + t` of a set
-- bit `t` gives its points, after the points already in the array; the numerators, each once, are
-- those of the set bits in increasing order.
#guard
  ([0, 1, 0x8000000000000000, 0xf0f0f0f0f0f0f0f0, 0x123456789abcdef1] : List UInt64).all fun x ↦
    let pts := (Id.run (walkWord [0, 0, 1] 1 1 false x (-37) #[(5, 5, 5)])).toList
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

-- The scan of pieces made by hand, with `F(a, 1) = a ^ 2`: the points of the numerators of the set
-- bits of the words in increasing order, for pieces from below and above zero, with a zero bit
-- array between, before and after bit arrays whose words have bits at both ends, of one bit array,
-- and of zero bit arrays only; the place of the sentinel holds other words at first.
#guard
  ([(3, -2, [1]), (2, 1, [0]), (2, -1, [1]), (1, 5, []), (2, 0, [0, 1])] :
      List (Nat × Int × List Nat)).all fun (n, w0, zeros) ↦
    let v : Vector UInt64 ((n + 1) * rbaPack) := .ofFn fun ⟨y, _⟩ ↦
      if zeros.contains (y / rbaPack) then 0
      else if y % 2 = 0 then 0x8000000000000001 else 1 <<< (y * 7 % 64).toUInt64
    (Id.run (scanPiece [0, 0, 1] 1 1 false w0 n v)).toList ==
      ((List.range (n * rbaPack)).flatMap fun y : Nat ↦
        ((List.range 64).filter v[y]!.toBitVec.getLsbD).map fun t : Nat ↦
          rbaLength * w0 + 64 * y + t).flatMap (checkNum [0, 0, 1] 1 1 false)

-- The scan of pieces whose bits are a test of their numerators: the points of the numerators of the
-- piece that pass the test, in increasing order.
#guard
  let keep (a : Int) : Bool := a % 5 == 2 || a % 64 == 63
  ([(2, -1), (1, 3)] : List (Nat × Int)).all fun (n, w0) ↦
    let v : Vector UInt64 ((n + 1) * rbaPack) := .ofFn fun ⟨y, _⟩ ↦
      (List.range 64).foldl (fun x (t : Nat) ↦
        if keep (rbaLength * w0 + 64 * (y : Int) + t) then x ||| 1 <<< t.toUInt64 else x) 0
    (Id.run (scanPiece [0, 0, 1] 1 1 false w0 n v)).toList ==
      (((List.range (n * rbaLength)).map fun k : Nat ↦ rbaLength * w0 + k).filter keep).flatMap
        (checkNum [0, 0, 1] 1 1 false)

-- One piece against the reference over its survivors: the points of the numerators from
-- `rbaLength w0 + maskLow` to `rbaLength (w0 + n) - 1 - maskHigh` that survive the moduli, for
-- pieces from below and above zero with no mask, with one of them and with both, among them the
-- piece of the numerators `-130, …, 130`; the masks around the numerator 129 of the point
-- `(129 : 3830 : 100)` of `y ^ 2 = x ^ 3 - 2` keep it or drop it.
#guard
  let c := [-2, 0, 0, 1]
  let es := [3, 5, 7, 11, 13].map fun p ↦ (⟨p, [.prime (examinePrime c 3 p)], magic p⟩ : SieveEntry)
  let piece (b : Nat) (w0 : Int) (n mL mH : Nat) : List (Int × Int × Int) :=
    (Id.run (siftPiece (BruteForce.scaledCoeffs c 3 b) b b false (es.map fun e ↦ ⟨e.p, e.row b⟩)
      (~~~0) w0 n mL mH)).toList
  piece 100 0 1 129 0 == [(129, 3830, 100), (129, -3830, 100)] && piece 100 0 1 130 0 == [] &&
    piece 100 0 1 0 (rbaLength - 130) == [(129, 3830, 100), (129, -3830, 100)] &&
    piece 100 0 1 0 (rbaLength - 129) == [] &&
    ([(-1, 2, 0, 0), (-1, 2, rbaLength - 130, rbaLength - 131), (0, 1, 129, 0), (0, 1, 130, 0),
        (0, 1, 0, rbaLength - 130), (0, 1, 0, rbaLength - 129), (-3, 2, 5, 7), (1, 3, 0, 0)] :
        List (Int × Nat × Nat × Nat)).all fun (w0, n, mL, mH) ↦ [1, 7, 100].all fun b ↦
      piece b w0 n mL mH == BruteForce.pointsOfDen c 3 b
        (((List.range (n * rbaLength - mL - mH)).map fun k : Nat ↦ rbaLength * w0 + mL + k).filter
          (survives es b))

-- One denominator against the plain sieve: the points of the numerators `-300, …, 300` of a few
-- denominators, with pieces of one, two and three bit arrays, the last piece cut at `wHigh`, and
-- with the flag of the reversal the same points, mapped.
#guard
  let c := [-2, 0, 0, 1]
  let es := [3, 5, 7, 11, 13].map fun p ↦ (⟨p, [.prime (examinePrime c 3 p)], magic p⟩ : SieveEntry)
  [1, 7, 100].all fun b ↦ [1, 2, 3].all fun A ↦ [false, true].all fun rev ↦
    let ref := (Id.run (checkDen c 3 300 b (Id.run (sieveDen 300 b es)))).toList
    (Id.run (sift c 3 300 A b rev (es.map fun e ↦ (e.p, e.rows)) (~~~0))).toList ==
      if rev then ref.map swapPoint else ref

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
