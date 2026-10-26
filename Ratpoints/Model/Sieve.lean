/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Bounds
public import Ratpoints.Model.BruteForce
public import Ratpoints.Model.Candidate
public import Ratpoints.Model.Constants
public import Ratpoints.Model.Delivery
public import Ratpoints.Model.FirstStage
public import Ratpoints.Model.Rows
public import Ratpoints.Model.Tables

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Bounds
meta import Ratpoints.Model.BruteForce
meta import Ratpoints.Model.Candidate
meta import Ratpoints.Model.Constants
meta import Ratpoints.Model.Delivery
meta import Ratpoints.Model.FirstStage
meta import Ratpoints.Model.Rows
meta import Ratpoints.Model.Tables

/-!
# The sieve

The components of the sieve, each in its place in the C function `find_points_work_1`: the
operations on the bit arrays of 64-bit words of the C code that the masks and the second stage use;
the packing of the numerators of a class of the denominators modulo 64 into one class modulo a power
of 2 (`Ratpoints.Sieve.NumClass`); the second stage, on a bit array that the first leaves nonzero or
on one of its words, with the rows read at the word number plus their offsets
(`Ratpoints.Sieve.secondStage`, `Ratpoints.Sieve.secondStageWord`); one bit array through the second
stage and the extraction of the points of its numerators in the packing of a class, in either arm of
the second stage, one word at a time or on the whole bit array (`Ratpoints.Sieve.siftBitArray`,
`Ratpoints.Sieve.siftBitArrayByWords`, `Ratpoints.Sieve.siftBitArrayWhole`); one piece of bit arrays
from the first stage, with the first moduli, in the arm that the chunk chooses, through the second,
with the others, to the points of its numerators (`Ratpoints.Sieve.siftPiece`); the bits of an
interval of numerators in the packing of a class (`Ratpoints.Sieve.numeratorsToBits`), the bits of
the numerators of a search interval at a denominator, from the forms of its ends or from the
products in 128 bits (`Ratpoints.Sieve.intervalBits`, `Ratpoints.Sieve.intervalBitsExact`, with the
bounds of `Ratpoints.Model.Bounds`), the rows of the moduli for a denominator from the tables of
rows of their entries with the row offsets of its class (`Ratpoints.Sieve.setRows`), the rows that
are not built yet built into their tables of rows (`Ratpoints.Sieve.buildRows`), and the points of
the bits of one interval in pieces (`Ratpoints.Sieve.siftBits`); and the numerators of one
denominator in the search intervals, in the packing of its class, with the products of the check and
what the third stage needs as thunks (`Ratpoints.Sieve.sift`). The components that take one
numerator at a time, the test of a candidate that survives the first two stages, with the test for
common factors and the third stage (`Ratpoints.Sieve.accepted`), the exact check
(`Ratpoints.Sieve.checkPoint`) and its reference, the check of a numerator
(`Ratpoints.Sieve.checkNum`), and the points at infinity (`Ratpoints.Sieve.pointsAtInfinity`), are
in `Ratpoints.Model.Candidate`; the first stage in both arms, with the operations on bit arrays that
it uses and the sieve specs (`Ratpoints.Sieve.andRowsChunked`, `Ratpoints.Sieve.andRows`,
`Ratpoints.Sieve.SieveSpec`), is in `Ratpoints.Model.FirstStage`. The tables of the primes and of
the prime powers and the sieve entries of the moduli, with the admission tests of the rows of a
denominator, are in `Ratpoints.Model.Tables`; the classes of the denominators modulo 64 with their
packings, the row offsets of the packings and the residues of a denominator divided by the stride of
its class (`Ratpoints.Sieve.numClasses`, `Ratpoints.Sieve.classOffsets`,
`Ratpoints.Sieve.fillBpList`) are in `Ratpoints.Model.Packing`; the 2-adic information that gives
the words of the classes is in `Ratpoints.Model.Denominators`; the counters of the sieve
(`Ratpoints.Sieve.Counters`) are in `Ratpoints.Model.Candidate`, and the loop over the denominators
in blocks, with the correction of the moduli from those counters (`Ratpoints.Sieve.sieveRun`), in
`Ratpoints.Model.Blocks`. The plain sieve of one denominator, one Boolean per numerator
(`Ratpoints.Sieve.sieveDen`), and the test for common factors and the exact check of its survivors
(`Ratpoints.Sieve.checkDen`) are not part of the run: they are the reference of the bit arrays of
words (`Ratpoints.Sieve.run_sift_eq_deliver_checkDen`). Every row, and the word of the class of a
denominator in the 2-adic information, let every point through, and the packing keeps every
numerator that the word admits, the rows of the residue of the denominator divided by the stride,
read at the row offsets of the class, admitting the numerators of the class that the rows of the
denominator admit; so the sieve of a denominator delivers exactly its points in the brute-force
reference `Ratpoints.bruteForce` whose `x / z` lies in a search interval (all of them for the one
interval `[-h, h]`, `h ≥ H`), in the same order, to the callback of the search
(`Ratpoints.Delivery`), each mapped by `Ratpoints.Sieve.swapPoint` when the flag of the reversal is
set: the map gives the point of the caller's curve for a point of a polynomial that the reversal
check has reversed (`Ratpoints.Setup.reversal`), the exact check delivers the mapped points when its
flag is set, as the points at infinity give them, and the components from the run down to the check
hand the flags (`Ratpoints.CheckFlags`) and the delivery on. Each component tests the flag of a stop
of the callback after each call that can set it and returns when it is set; under
`RATPOINTS_NO_CHECK` the sieve delivers every numerator that passes it, and under `RATPOINTS_NO_Y`
only the points with `y ≥ 0`. The rows of the moduli as words, with the row of `0` of a prime that
the build of ratpoints generates (`Ratpoints.Sieve.sieves0`), the builders of the rows of the
primes, the prime powers and the products, the row of a sieve entry read from its table of rows or
built into it (`Ratpoints.Sieve.SieveEntry.fetchRow`) and the tables of rows of a run
(`Ratpoints.Sieve.RowStore`), are in `Ratpoints.Model.Rows`.

## Main definitions

* `Ratpoints.Sieve.sieveDen`, `Ratpoints.Sieve.checkDen`: the plain sieve of one denominator and the
  points of its survivors, the reference of the bit arrays of words.
* `Ratpoints.Sieve.clearLowBits`, `Ratpoints.Sieve.clearHighBits`, `Ratpoints.Sieve.isZeroAt`:
  the masks on the bit arrays of 64-bit words of the C code and the test for zero.
* `Ratpoints.Sieve.NumClass`: the packing of the numerators of a class of the denominators modulo
  64, its stride, its residue, its pattern and the position of its row offsets.
* `Ratpoints.Sieve.secondStage`, `Ratpoints.Sieve.secondStageWord`: the second stage on a bit array
  and on one of its words, the rows of its moduli, read at the word number plus their offsets,
  and-ed in while a bit is left.
* `Ratpoints.Sieve.walkWord`: the walk through the set bits of a word, lowest first, each numerator
  going to the test of a candidate and, if it passes, to the exact check, which delivers its points
  to the callback; the walk returns when the callback stops the search.
* `Ratpoints.Sieve.siftBitArrayByWords`, `Ratpoints.Sieve.siftBitArrayWhole`,
  `Ratpoints.Sieve.siftBitArray`: one bit array that the first stage leaves nonzero, through the
  second stage one word at a time or on the whole bit array, and the walks through its words; and
  the choice between the two arms.
* `Ratpoints.Sieve.scanPiece`: the scan over the bit arrays of a piece up to a sentinel, stepping
  over those that are zero, and a copy of each of the others through the second stage and the
  extraction.
* `Ratpoints.Sieve.siftPiece`: one piece of bit arrays, from the first stage and the masks at its
  two ends, through the second stage, to the points of its numerators.
* `Ratpoints.Sieve.numeratorsToBits`: the bits of an interval of numerators in the packing of a
  class.
* `Ratpoints.Sieve.intervalBitsExact`, `Ratpoints.Sieve.intervalBits`: the bits of the numerators
  of a search interval at a denominator, from the products in 128 bits and from the forms of its
  ends.
* `Ratpoints.Sieve.setRows`, `Ratpoints.Sieve.buildRows`: the moduli of the first two stages with
  their rows from the tables of rows and their offsets for a denominator, the start `0` and the end
  `p`, and the rows that are not built yet built into their tables of rows.
* `Ratpoints.Sieve.siftBits`: the points of the numerators of an interval of bits, in pieces.
* `Ratpoints.Sieve.sift`: the points of one denominator, its numerators in the search intervals in
  the packing of its class, in pieces of bit arrays.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The plain sieve -/

/-- The plain sieve of the denominator `b`: an array of `2H + 1` Booleans, one for each numerator
`a = i - H`, all true at the start; for each sieve entry of `entries` in turn, every Boolean is
replaced by its conjunction with the row of `b` at its numerator
(`Ratpoints.Sieve.SieveEntry.admits`). With `Ratpoints.Sieve.checkDen` it is the reference of the
bit arrays of words: for pieces of at least one bit array, a denominator `0 < b < 2 ^ 63`,
`H < 2 ^ 63`, a class that packs a word (`Ratpoints.Sieve.NumClass.Packs`) and has a row of offsets,
entries of the first two stages whose tables of inverses invert and that are packed for the class at
its offsets (`Ratpoints.Sieve.SieveEntry.PackedFor`), with the reciprocals of their moduli and the
residues of `b` divided by the stride of the class, and entries of the third stage of the shape of
`Ratpoints.Sieve.SieveEntry.IsPrimeEntry`, with the reciprocals of their moduli, the points that
`Ratpoints.Sieve.sift` delivers in the packing of the class with the rows of the entries of its
first two stages, from a store of the tables of rows that fits these entries
(`Ratpoints.Sieve.RowStore.Fits`), and bounds of the search intervals that give the ranges of the
numerators at `b` (`Ratpoints.Sieve.RangesFor`; all of `-H, …, H` for the one search interval
`[-h, h]`, `h ≥ H`), without `RATPOINTS_NO_CHECK`, are those that `Ratpoints.Sieve.checkDen` finds
on the plain sieve with all these entries whose numerators lie in one of the ranges
(`Ratpoints.Sieve.inRanges`) and pass the word, all of them for any word that admits the numerators
of the points (such as the word `nb[b mod 64]` of `Ratpoints.Sieve.twoAdic`), each mapped by
`Ratpoints.Sieve.swapPoint` when the flag of the reversal is set, and those with `y < 0` left out
under `RATPOINTS_NO_Y` (`Ratpoints.Sieve.run_sift_eq_deliver_checkDen`). -/
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
With the plain sieve `Ratpoints.Sieve.sieveDen` it is the reference of the bit arrays of words:
under the hypotheses of `Ratpoints.Sieve.run_sift_eq_deliver_checkDen`, `Ratpoints.Sieve.sift` in
the packing of a class of a word, with bounds of the search intervals that give the ranges of the
numerators at `b` (`Ratpoints.Sieve.RangesFor`; all of `-H, …, H` for the one search interval
`[-h, h]`, `h ≥ H`), delivers the points that it finds on the plain sieve with all the sieve entries
whose numerators lie in one of the ranges (`Ratpoints.Sieve.inRanges`) and pass the word, all of
them for any word that admits the numerators of the points (such as the word `nb[b mod 64]` of
`Ratpoints.Sieve.twoAdic`), each mapped by `Ratpoints.Sieve.swapPoint` when the flag of the reversal
is set, those with `y < 0` left out under `RATPOINTS_NO_Y`, without `RATPOINTS_NO_CHECK`. -/
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

/-- The packing of the numerators of the denominators of one class modulo 64, `rp_num_class`: the
admissible numerators modulo 64 of the class (the word of the class in the 2-adic information,
`Ratpoints.Sieve.twoAdic`) lie in one class `a₀ mod 2 ^ k`, with `k` the largest below
`Ratpoints.numStrides` and at most 6 that allows this, so that the sieve in the packing holds only
those, bit `t` of the bit array with the word number `0` standing for the numerator `a₀ + 2 ^ k t`;
`bits` is the pattern of the class in that packing, bit `t` the bit `(a₀ + 2 ^ k t) mod 64` of the
word, from which the first stage starts in the packing, and `0` for a class without admissible
numerators, which the run never sifts; `offset` is the position in the array of the row offsets of
the run at which the offsets of the row of the packing `(k, a₀)` begin, one for each modulus, none
until the row offsets of the packings are made (`Ratpoints.Sieve.classOffsets`). The classes of a
run are made by `Ratpoints.Sieve.numClasses`.

C: `rp-private.h:494-495`

Deviation: one word for the bit array `bits`, the vector `RBA(packed)` of `RBA_PACK` copies of the
word, which the first stage writes into every word of a bit array; natural numbers for the `long`s
`k` and `a0`; the position of the row of offsets in the array of the offsets as an option, for the
pointer `offset` into that array, none for `NULL`. -/
structure NumClass where
  /-- The pattern of the class in its packing, `0` for a class without admissible numerators. -/
  bits : UInt64
  /-- The exponent of the stride `2 ^ k` of the packing. -/
  k : Nat
  /-- The residue `a₀ < 2 ^ k` of the admissible numerators. -/
  a0 : Nat
  /-- Where the offsets of the row of the packing begin in the array of the row offsets, none until
  they are made. -/
  offset : Option Nat
  deriving Inhabited

/-! ### The second stage -/

/-- The second stage on the bit array `nums` with the word number `i`, a copy of a bit array that
the first stage left nonzero: for each modulus `p` of `specs` with its row and its offset, and its
reciprocal `mg` from `mgs`, in turn, while `nums` is not zero (`Ratpoints.Sieve.isZeroAt`), `nums`
is and-ed with bit array `(i + offset) mod p` of the row (`Ratpoints.Sieve.andBitArray`), the
remainder by a multiplication with `mg` (`Ratpoints.Sieve.mulMod`) when `small` says that the word
numbers of the piece allow it, and by the helper `mod` of the C code otherwise
(`Ratpoints.Sieve.modLong`). Stopping early loses nothing, since a zero bit array stays zero, so
that the result is `nums` and-ed with the rows of all the moduli.

C: `sift.c:1083`, `sift.c:1085`, `sift.c:1175-1202`

Deviation: the moduli of the stage with their rows and their reciprocals as two lists, for the
pointers `ssp` and `mg` that step through the sieve specs and the array `magics` from position `sp1`
on and the count `sp2 - sp1`, with no bound `2 RATPOINTS_NUM_PRIMES` on their number (the length of
`magics`, `find_points.c:347`), which ratpoints never reaches since each entry of `sieve_list` owns
its own prime (`find_points.c:329-331`), where the model takes any moduli, which may repeat; one bit
array of `Ratpoints.rbaPack` words, for the vector `nums`; natural numbers and integers for the
`long`s, and the sum `v` a natural number for the `long` that `RP_MULMOD` converts to an
`unsigned long`, which is not negative under `small`, and which stays a `long` where the helper
`mod` reduces it outside `small` (`Ratpoints.Sieve.fitsLong_neg_sub_and_fitsLong_add`); a Boolean
for the `int` `small`; no count of the ands of the second stage under `RP_PHASE_COUNTS`, and no
output under `DEBUG`. -/
def secondStage (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (i : Int)
    (nums : Vector UInt64 rbaPack) :
    Id (Vector UInt64 rbaPack) := do
  let mut nums := nums
  for s in specs, mg in mgs do
    if isZeroAt nums 0 then break
    let v := i + s.offset
    let row := if small then mulMod v.toNat s.p mg else (modLong v s.p).toNat
    nums := andBitArray nums 0 s.row row
  return nums

/-- The second stage on word `κ < Ratpoints.rbaPack` of the bit array with the word number `i`, the
arm of the second stage for one word at a time: for each modulus `p` of `specs` with its row and its
offset, and its reciprocal `mg` from `mgs`, in turn, while `x ≠ 0`, `x` is and-ed with word `κ` of
bit array `(i + offset) mod p` of the row, the remainder by a multiplication with `mg` when `small`
says that the word numbers of the piece allow it, and by the helper `mod` otherwise. Stopping early
loses nothing, and the result is word `κ` of the result of `Ratpoints.Sieve.secondStage` on a bit
array whose word `κ` is `x`.

C: `sift.c:1135-1136`, `sift.c:1141-1152`

Deviation: the moduli of the stage with their rows and their reciprocals as two lists, for the
pointers `sspk` and `mg` that step through the sieve specs and the array `magics` from position
`sp1` on and the count `sp2 - sp1`, with no bound `2 RATPOINTS_NUM_PRIMES` on their number (the
length of `magics`, `find_points.c:347`), which ratpoints never reaches since each entry of
`sieve_list` owns its own prime (`find_points.c:329-331`), where the model takes any moduli, which
may repeat; natural numbers and integers for the `long`s, and the sum `v` a natural number for the
`long` that `RP_MULMOD` converts to an `unsigned long`, which is not negative under `small`, and
which stays a `long` where the helper `mod` reduces it outside `small`
(`Ratpoints.Sieve.fitsLong_neg_sub_and_fitsLong_add`); a Boolean for the `int` `small`; no count of
the ands of the second stage under `RP_PHASE_COUNTS`. -/
def secondStageWord (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (i : Int) (κ : Nat)
    (x : UInt64) :
    Id UInt64 := do
  let mut x := x
  for s in specs, mg in mgs do
    if x == 0 then break
    let v := i + s.offset
    let row := if small then mulMod v.toNat s.p mg else (modLong v s.p).toNat
    x := x &&& s.row[rbaPack * row + κ]!
  return x

/-! ### One piece -/

/-- The set bits of the word `x`, lowest first, bit `t` standing for the numerator
`a = a0 + step t`: while `x ≠ 0`, for the lowest set bit `t` of `x` (`Ratpoints.Sieve.ctz`), the
numerator `a` goes to the test for common factors with the denominator `b` and the third stage
(`Ratpoints.Sieve.accepted`, with the thunk `checks` of what that stage needs), and if it passes, to
the exact check (`Ratpoints.Sieve.checkPoint`, with the thunk `w` of the products, the degree `d`
and the flags `fl`), which delivers its points to the callback `process` on the delivery `r`, after
which the walk returns if the callback has stopped the search; then that bit is cleared by
`x &&& (x - 1)`. Each numerator counts one up the count `bits` of the counters `cnt`
(`Ratpoints.Sieve.Counters`), and the test of a candidate counts its own. This is the loop
`RP_EACH_SET_BIT` of the C code with the body that the extraction runs for each set bit; the step is
the stride `2 ^ k` of the packing of the class of `b`. The callers call it only while the flag
`quit` of `r` is clear, and return when it is set after it.

C: `sift.c:262-264`, `sift.c:1161-1171`, `sift.c:1227-1255`, `sift.c:1265-1292`

Deviation: the lowest set bit by the loop of `RP_CTZL` for a compiler without the builtin
(`Ratpoints.Sieve.ctz`); one definition for the body at the three places of the extraction, the
first word of a bit array, the others, and a word of the arm of the second stage for one word at a
time; natural numbers and integers for the `long`s; the delivery `r` passed and returned, for the
pointers `info` and `wk->quit` and the count `total` of `_ratpoints_sift0`, to which
`RP_CHECK_POINT` adds the count of the check (lines 1168, 1240, 1250, 1279, 1287); the return after
a stop (lines 1169, 1241, 1251, 1280, 1288) a return from the walk, which its callers pass on,
testing the flag after it (`Ratpoints.Sieve.siftBitArrayByWords`,
`Ratpoints.Sieve.siftBitArrayWhole`, then `Ratpoints.Sieve.scanPiece` after the bit array), where
the C code returns from `_ratpoints_sift0`; the counters passed and returned, for the field
`n_bits` of the sieving thread (lines 1166, 1233, 1271); no counts under `RP_PHASE_COUNTS`; no
output under `DEBUG`. -/
def walkWord {σ : Type} (process : Int → Int → Int → σ → Answer σ) (w : Thunk (List Int))
    (d b : Nat) (fl : CheckFlags) (checks : Thunk (List CheckSpec)) (x : UInt64) (a0 : Int)
    (step : Nat) (r : Delivery σ) (cnt : Counters) :
    Id (Delivery σ × Counters) := do
  let mut x := x
  let mut r := r
  let mut cnt := cnt
  while x != 0 do
    let t ← ctz x
    let a := a0 + step * t
    cnt := { cnt with bits := cnt.bits + 1 }
    let (ok, c') ← accepted a b checks cnt
    cnt := c'
    if ok then
      r := checkPoint process w d b fl a r
      if r.quit then return (r, cnt)
    x := x &&& (x - 1)
  return (r, cnt)

/-- The arm of the second stage one word at a time, for the bit array that the first stage left
nonzero with the word number `i`, from a copy `nums` of it, the points of its numerators delivered
to the callback `process` on the delivery `r`: for each word `κ` of `nums` that is not zero, the
second stage on that word (`Ratpoints.Sieve.secondStageWord`, with the moduli of `specs`, their
reciprocals `mgs` and the test `small`) and the walk through its set bits
(`Ratpoints.Sieve.walkWord`) from the first numerator of the word, after which it returns if the
callback has stopped the search. For the stride `2 ^ k` and the residue `a₀` of the class `cl` of
the denominator (`Ratpoints.Sieve.NumClass`), bit `t` of word `κ` stands for the numerator
`a₀ + 2 ^ k (rbaLength i + 64 κ + t)`, for the number `rbaLength` of bits of a bit array
(`Ratpoints.rbaLength`): the first numerator of the bit array is `a₀ + 2 ^ k rbaLength i`, computed
before the loop over the words, that of word `κ` is that plus `κ` times the step `64 2 ^ k` from
one word to the next, and the step from one bit to the next is `2 ^ k`. Each numerator goes to the
test of a candidate (`Ratpoints.Sieve.accepted`, with the thunk `checks` of the third stage) and,
if it passes, to the exact check, with the thunk `w` of the products, the degree `d`, the
denominator `b` and the flags `fl`. This is the arm that a build of ratpoints with
`USE_LONG_IN_PHASE_2` compiles.

C: `sift.c:1126-1134`, `sift.c:1137-1139`, `sift.c:1154-1159`, `sift.c:1172-1173`

Deviation: the stride, the first numerator and the steps as natural numbers and integers, the
powers `2 ^ k` for the shifts `1L << k`, `RBA_LENGTH << k` and `LONG_LENGTH << k`, the last two of
which stay `int`s, while the first numerators of the words, the numerators of bits of the bit
arrays of a height bound below `2 ^ 63`, stay `long`s
(`Ratpoints.Sieve.NumClass.fitsLong_numerator`); the words of the bit array read as entries of the
vector, for `EXT`; natural numbers and integers for the `long`s; the delivery `r` passed and
returned, for the pointers `info` and `wk->quit` and the count `total` of `_ratpoints_sift0`, and
the flag `quit` tested after each walk through the set bits of a word, where the C code returns
from `_ratpoints_sift0` within the walk (`Ratpoints.Sieve.walkWord`); no counts under
`RP_PHASE_COUNTS` and no stop after a phase (`RP_STOP_AFTER`). -/
def siftBitArrayByWords {σ : Type} (process : Int → Int → Int → σ → Answer σ)
    (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags) (specs : List SieveSpec) (mgs : List Nat)
    (small : Bool) (checks : Thunk (List CheckSpec)) (cl : NumClass) (i : Int)
    (nums : Vector UInt64 rbaPack) (r : Delivery σ) (cnt : Counters) :
    Id (Delivery σ × Counters) := do
  let a0 := cl.a0 + i * (rbaLength * 2 ^ cl.k)
  let da := 64 * 2 ^ cl.k
  let mut r := r
  let mut cnt := cnt
  for κ in [0:rbaPack] do
    if nums[κ]! != 0 then
      let x ← secondStageWord specs mgs small i κ nums[κ]!
      (r, cnt) ← walkWord process w d b fl checks x (a0 + κ * da) (2 ^ cl.k) r cnt
      if r.quit then return (r, cnt)
  return (r, cnt)

/-- The arm of the second stage on the whole bit array, for the bit array that the first stage left
nonzero with the word number `i`, from a copy `nums` of it, the points of its numerators delivered
to the callback `process` on the delivery `r`: the second stage on the whole bit array
(`Ratpoints.Sieve.secondStage`, with the moduli of `specs`, their reciprocals `mgs` and the test
`small`), and, if it is still nonzero, the set bits of its words walked through in turn
(`Ratpoints.Sieve.walkWord`), the first word from the first numerator of the bit array and each
further word from the first numerator of the word before it plus the step from one word to the
next, both computed when the second stage has left the bit array nonzero; it returns after a walk
at which the callback has stopped the search. For the stride `2 ^ k` and the residue `a₀` of the
class `cl` of the denominator (`Ratpoints.Sieve.NumClass`), bit `t` of word `κ` stands for the
numerator `a₀ + 2 ^ k (rbaLength i + 64 κ + t)`, for the number `rbaLength` of bits of a bit array
(`Ratpoints.rbaLength`): the first numerator of word `κ` is `a₀ + 2 ^ k rbaLength i + κ 64 2 ^ k`,
and the step from one bit to the next `2 ^ k`. Each numerator goes to the test of a candidate
(`Ratpoints.Sieve.accepted`, with the thunk `checks` of the third stage) and, if it passes, to the
exact check, with the thunk `w` of the products, the degree `d`, the denominator `b` and the flags
`fl`. This is the arm that the default build of ratpoints compiles.

C: `sift.c:1204-1210`, `sift.c:1213-1226`, `sift.c:1257-1264`, `sift.c:1293-1296`,
`rp-private.h:135-136`, `rp-private.h:177-178`, `rp-private.h:238-239`, `rp-private.h:264-266`,
`rp-private.h:288-289`

Deviation: the stride, the first numerator and the steps as natural numbers and integers, the
powers `2 ^ k` for the shifts `1L << k`, `RBA_LENGTH << k` and `LONG_LENGTH << k`, the last two of
which stay `int`s, while the first numerators of the words, the numerators of bits of the bit
arrays of a height bound below `2 ^ 63`, stay `long`s
(`Ratpoints.Sieve.NumClass.fitsLong_numerator`); the words of the bit array read as entries of the
vector, for `EXT0` and `EXT`; natural numbers and integers for the `long`s; the delivery `r` passed
and returned, for the pointers `info` and `wk->quit` and the count `total` of `_ratpoints_sift0`,
and the flag `quit` tested after each walk through the set bits of a word and the rest of the bit
array left at a stop, where the C code returns from `_ratpoints_sift0` within the walk
(`Ratpoints.Sieve.walkWord`); no counts under `RP_PHASE_COUNTS` and no stop after a phase
(`RP_STOP_AFTER`). -/
def siftBitArrayWhole {σ : Type} (process : Int → Int → Int → σ → Answer σ)
    (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags) (specs : List SieveSpec) (mgs : List Nat)
    (small : Bool) (checks : Thunk (List CheckSpec)) (cl : NumClass) (i : Int)
    (nums : Vector UInt64 rbaPack) (r : Delivery σ) (cnt : Counters) :
    Id (Delivery σ × Counters) := do
  let nums ← secondStage specs mgs small i nums
  let mut r := r
  let mut cnt := cnt
  if !isZeroAt nums 0 then
    let mut a0 := cl.a0 + i * (rbaLength * 2 ^ cl.k)
    let da := 64 * 2 ^ cl.k
    (r, cnt) ← walkWord process w d b fl checks nums[0]! a0 (2 ^ cl.k) r cnt
    if r.quit then return (r, cnt)
    for κ in [1:rbaPack] do
      a0 := a0 + da
      (r, cnt) ← walkWord process w d b fl checks nums[κ]! a0 (2 ^ cl.k) r cnt
      if r.quit then return (r, cnt)
  return (r, cnt)

/-- One bit array that the first stage left nonzero, with the word number `i`, from a copy `nums` of
it, the points of its numerators delivered to the callback `process` on the delivery `r`, in the arm
of the second stage that `useLong` chooses (`Ratpoints.useLongInPhase2` in the run): the second
stage on the whole bit array and then the walks through its words for `useLong = false`
(`Ratpoints.Sieve.siftBitArrayWhole`), and for `useLong = true` the second stage on each word that
is not zero and the walk through it (`Ratpoints.Sieve.siftBitArrayByWords`), with the moduli of
`specs`, their reciprocals `mgs` and the test `small`, the thunk `w` of the products, the degree
`d`, the denominator `b`, the flags `fl`, the thunk `checks` of the third stage and the packing of
the class `cl` of the denominator. Both arms walk through the set bits of the same words, the words
of `nums` and-ed with the rows of all the moduli of `specs`, in the same order, and return after a
walk at which the callback has stopped the search.

C: `sift.c:1094-1111`

Deviation: the arm chosen by the argument `useLong`, so that the guards run both in the same build,
for the arm that the build compiles (`#ifdef USE_LONG_IN_PHASE_2`), each arm a function of its own;
a function of its own for the body of the loop of the scan over one bit array; no counts under
`RP_PHASE_COUNTS`, no stop after a phase (`RP_STOP_AFTER`), and no output under `DEBUG`. -/
def siftBitArray {σ : Type} (process : Int → Int → Int → σ → Answer σ) (useLong : Bool)
    (w : Thunk (List Int)) (d b : Nat) (fl : CheckFlags) (specs : List SieveSpec) (mgs : List Nat)
    (small : Bool) (checks : Thunk (List CheckSpec)) (cl : NumClass) (i : Int)
    (nums : Vector UInt64 rbaPack) (r : Delivery σ) (cnt : Counters) :
    Id (Delivery σ × Counters) :=
  if useLong then siftBitArrayByWords process w d b fl specs mgs small checks cl i nums r cnt
  else siftBitArrayWhole process w d b fl specs mgs small checks cl i nums r cnt

/-- The scan over a piece, the bit arrays with the word numbers `w0, …, w0 + n - 1`, which are the
first `n` bit arrays of `surv`, and the second stage and the extraction of the points of their
numerators: a sentinel, a bit array of ones, is written into bit array `n`, just past the piece;
then from bit array `0` on, the bit arrays that are zero (`Ratpoints.Sieve.isZeroAt`) are stepped
over, the scan stops at the sentinel, and each of the other bit arrays `pos` is copied and goes,
with its word number `w0 + pos`, through the second stage with the moduli, rows and offsets of
`specs`, their reciprocals `mgs` and the test `small`, and the extraction in the packing of the
class `cl` (`Ratpoints.Sieve.siftBitArray`, in the arm `Ratpoints.useLongInPhase2`, with the thunk
`w` of the products, the degree `d`, the denominator `b`, the flags `fl` and the thunk `checks` of
the third stage), which delivers the points of its numerators to the callback `process` on the
delivery `r`; the scan returns when the callback has stopped the search.

C: `sift.c:1061-1082`, `sift.c:1088-1092`, `sift.c:1298-1299`, `rp-private.h:133`,
`rp-private.h:205`, `rp-private.h:236`, `rp-private.h:262`, `rp-private.h:286`

Deviation: indices for the pointers into the survivors, and a scan that holds its position as an
index, where ratpoints recovers the word number from a pointer difference; the copy `nums` of the
bit array a vector of `Ratpoints.rbaPack` words; the sentinel `~zero` of every build as
`Ratpoints.rbaPack` words `~~~0`, written one at a time; natural numbers and integers for the
`long`s; the counters `cnt` passed and returned, for the field `n_arrays` of the sieving thread,
which counts one up for each bit array that is not zero (line 1092); the delivery `r` passed and
returned, for the pointers `info` and `wk->quit` and the count `total` of `_ratpoints_sift0`, and
the flag `quit` tested after each bit array, where the C code returns from `_ratpoints_sift0` within
the walk through the set bits of a word (`Ratpoints.Sieve.walkWord`). -/
def scanPiece {σ : Type} (process : Int → Int → Int → σ → Answer σ) (w : Thunk (List Int))
    (d b : Nat) (fl : CheckFlags) (specs : List SieveSpec) (mgs : List Nat) (small : Bool)
    (checks : Thunk (List CheckSpec)) (cl : NumClass) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) (r : Delivery σ) (cnt : Counters) :
    Id (Delivery σ × Counters) := do
  let mut surv := surv
  for κ in [0:rbaPack] do
    surv := surv.set! (rbaPack * n + κ) (~~~0)
  let mut pos := 0
  let mut r := r
  let mut cnt := cnt
  repeat
    while isZeroAt surv pos do
      pos := pos + 1
    if n ≤ pos then break
    let nums : Vector UInt64 rbaPack := .ofFn fun κ ↦ surv[rbaPack * pos + κ]!
    cnt := { cnt with arrays := cnt.arrays + 1 }
    (r, cnt) ← siftBitArray process useLongInPhase2 w d b fl specs mgs small checks cl (w0 + pos)
      nums r cnt
    if r.quit then return (r, cnt)
    pos := pos + 1
  return (r, cnt)

/-- One piece, the bit arrays with the word numbers `w0, …, w0 + n - 1`, and the points of its
numerators: whether the reductions of the row indices modulo the moduli of the first two stages can
multiply by the reciprocals, `small`, when the word numbers lie between `-Ratpoints.rowBias` and
`Ratpoints.rowBias - 2 Ratpoints.maxPrimeEven`, so that the sum of a word number and an offset, the
least multiple of the modulus of at least `Ratpoints.rowBias` (below `Ratpoints.rowBias` plus the
modulus) plus less than the modulus, is not negative and below `2 Ratpoints.rowBias`, at most
`Ratpoints.mulModLimit`; a fresh array of `n + 1` bit arrays, the last one the place of the
sentinel; the first stage with the first `sp1` moduli of `specs`, their rows and offsets, and their
reciprocals in `mgs`, from the pattern of the class `cl` of the denominator, in the arm that the
chunk `Ratpoints.chunk` chooses as the conditional compilation of the C code does: `chunk` bit
arrays at a time for a chunk from 2 to 16 (`Ratpoints.Sieve.andRowsChunked`), and one row at a time
otherwise (`Ratpoints.Sieve.andRows`), which leave the same bit arrays; the lowest `maskLow` bits of
the first bit array cleared if `maskLow ≠ 0` (`Ratpoints.Sieve.clearLowBits`), and the highest
`maskHigh` bits of the last bit array of the piece, `n - 1`, if `maskHigh ≠ 0`
(`Ratpoints.Sieve.clearHighBits`); and the scan with the second stage, with the other moduli of
`specs` and their reciprocals, and the extraction in the packing of `cl`
(`Ratpoints.Sieve.scanPiece`, with the thunk `w` of the products, the degree `d`, the denominator
`b`, the flags `fl` and the thunk `checks` of the third stage), which delivers the points to the
callback `process` on the delivery `r` and returns when the callback stops the search. This is
`_ratpoints_sift0` of the C code, with the allocation of the survivors array that it works in.

C: `find_points.c:3119-3121`, `sift.c:498-531`, `sift.c:548`, `sift.c:1030-1041`,
`sift.c:1056-1058`, `sift.c:1300-1305`, `rp-private.h:575`, `rp-private.h:610-614`

Deviation: the arm of the first stage chosen by a test on the constant `Ratpoints.chunk`, for the
conditional compilation `#if (RATPOINTS_CHUNK > 1) && (RATPOINTS_CHUNK <= 16)` (`sift.c:452`,
`sift.c:575`, `sift.c:943`), which compiles one arm only, and `tail_leg` with the chunked one; a
fresh array of zeros for each piece, for the survivors array of the sieving thread, which every
piece reuses, with one bit array more for the alignment, and whose words `malloc` leaves
uninitialized; the piece by its first word number `w0` and its number `n` of bit arrays, for `w_low`
and `w_high`, and an index for the pointer to its last bit array; the moduli of the first two stages
with their rows and offsets as the list `specs` and the end `sp1` of the first stage, for the sieve
specs `sieves` and the number `sp1` that the sieving thread keeps, the reciprocals of their moduli
as the list `mgs`, for the array `magics` of the arguments, and the thunk `checks`, for the table
`checks` of the third stage and its length `nchecks = sp3 - sp2`; the class `cl` as a value, for the
pointer `cls`; integers for the `long`s of the test `small`, which stay `long`s, and a Boolean for
its `int`; the counters `cnt` passed and returned, for the field `n_words` of the sieving thread,
which counts the `n Ratpoints.rbaPack` words of the piece (line 548), the product of `UInt64`s as
the C code multiplies the `unsigned long` by `RBA_PACK`; the thunk `w` of the products of the check
as an argument, where `_ratpoints_check_point` computes the products when the first survivor of `b`
reaches it; the delivery `r` passed and returned, for the pointers `info` and `wk->quit` and the
count `total` that `_ratpoints_sift0` keeps from zero and returns, and its returns at a stop within
the walk through the set bits of a word passed on by the scan (`Ratpoints.Sieve.scanPiece`); natural
numbers and integers for the `long`s; no measurements of the phases (`RP_TIC`, `RP_TOC`,
`RP_PHASE_TIMING`) and no stop after one of them (`RP_STOP_AFTER`). -/
def siftPiece {σ : Type} (process : Int → Int → Int → σ → Answer σ) (w : Thunk (List Int))
    (d b : Nat) (fl : CheckFlags) (sp1 : Nat) (specs : List SieveSpec) (mgs : List Nat)
    (checks : Thunk (List CheckSpec)) (cl : NumClass) (w0 : Int) (n maskLow maskHigh : Nat)
    (r : Delivery σ) (cnt : Counters) :
    Id (Delivery σ × Counters) := do
  let small := decide (-rowBias ≤ w0 ∧ w0 + n ≤ rowBias - 2 * maxPrimeEven)
  let cnt := { cnt with words := cnt.words + n.toUInt64 * rbaPack.toUInt64 }
  let zeros := Vector.replicate ((n + 1) * rbaPack) 0
  let mut surv ← if 1 < chunk ∧ chunk ≤ 16 then
      andRowsChunked (specs.take sp1) (mgs.take sp1) small cl.bits w0 n zeros
    else andRows (specs.take sp1) (mgs.take sp1) small cl.bits w0 n zeros
  if maskLow ≠ 0 then surv := clearLowBits surv maskLow
  if maskHigh ≠ 0 then surv := clearHighBits surv (n - 1) maskHigh
  scanPiece process w d b fl (specs.drop sp1) (mgs.drop sp1) small checks cl w0 n surv r cnt

/-! ### One denominator -/

/-- The bits of the numerators `low, …, high` in the packing of the class `cl`, whose bit `t` stands
for the numerator `a₀ + 2 ^ k t` (`Ratpoints.Sieve.NumClass`): from
`⌈(low - a₀) / 2 ^ k⌉ = -⌊(a₀ - low) / 2 ^ k⌋` to `⌊(high - a₀) / 2 ^ k⌋`, by arithmetic shifts.
With `split` clear, as the shifts of the differences `a₀ - low` and `high - a₀`, which stay in the
range of a `long` for `|low|, |high| ≤ 2 ^ 63 - 65`; with `split` set, each end split into its
multiple of `2 ^ k`, the end shifted right by `k`, and its rest, the end and-ed with the mask
`2 ^ k - 1`, from which `a₀` is taken, so that nothing leaves the range of a `long` also for an end
within `2 ^ k` of its bounds. Both forms give the same bits where both stay in range.

C: `find_points.c:3355-3370`

Deviation: `Int64` for the `long`s, in two's complement, the representation on which the and with
the mask acts, also on a negative end, and `>>>` on `Int64` the arithmetic shift, for the `>>` of a
negative `long`, both of which the C standard leaves to the implementation (the representation
before C23) and gcc defines so; the arithmetic of `Int64` wrapping where that of the `long`s
overflows, which the C standard leaves undefined: the differences of the plain form for an end
within `a₀` of `-2 ^ 63`, so beyond `2 ^ 63 - 65` in absolute value, where neither the C code nor
`Ratpoints.Sieve.sift` takes the plain form; the stride `k` and the residue `a₀` of the class
converted to `Int64`; the two ends returned as a pair, for the pointers `low` and `high` through
which the function reads and writes them; a Boolean for the `int` `split`, an argument: clear on the
path of the forms of the ends (`Ratpoints.Sieve.intervalBits`), which `exact_bounds` gives an
interval only for `H ≤ 2 ^ 63 - 65`, and on the path of the products in 128 bits
(`Ratpoints.Sieve.intervalBitsExact`) set exactly for the heights above `2 ^ 63 - 65`. -/
-- The parentheses are those of the C code, in which `>>` binds looser than `+` and `-`.
def numeratorsToBits (low high : Int64) (cl : NumClass) (split : Bool) : Int64 × Int64 :=
  let k := cl.k.toInt64
  let a0 := cl.a0.toInt64
  if split then
    let mask := (1 <<< k) - 1
    ((low >>> k) + (((low &&& mask) - a0 + mask) >>> k),
      (high >>> k) + (((high &&& mask) - a0) >>> k))
  else (-((a0 - low) >>> k), (high - a0) >>> k)

/-- The bits of the numerators of the search interval with the bounds `bd`
(`Ratpoints.Sieve.IntervalBounds`) at the denominator `b`, for the height bound `height` and the
class `cl`, from the products of `b` and the ends in 128 bits (`Ratpoints.Sieve.exactScale`), as
`interval_bits_exact` computes them for an interval that is not taken inline: `⌈b l⌉`, which is
`-⌊b |l|⌋` for `l < 0`, clipped to `-height`, and the code `2` when it is beyond `height` for
`l ≥ 0`, so that neither this interval nor a later one holds a numerator within the bound; then
`⌊b u⌋`, which is `-⌈b |u|⌉` for `u < 0`, and the code `1` when it is below `-height`, so that this
interval holds none, and otherwise clipped to `height`; and the code `0` with the bits of
`⌈b l⌉, …, ⌊b u⌋` (`Ratpoints.Sieve.numeratorsToBits`), in the form that splits the ends for the
heights above `2 ^ 63 - 65`.

C: `find_points.c:3381-3406`

Deviation: the code and the bits returned as a triple, for the `int` and the pointers `low` and
`high` through which the C code writes the bits, the bits `(0, 0)` with the codes `1` and `2`, for
which the C code writes nothing; `Int64` for the `long`s, the `unsigned long` products compared
with the height bound converted to a 64-bit word, as the C code compares them; no output under
`DEBUG`. -/
def intervalBitsExact (b : Int64) (bd : IntervalBounds) (height : Int64) (cl : NumClass) :
    Nat × Int64 × Int64 :=
  let t := exactScale b bd.low
  let low? : Option Int64 :=
    if bd.low.neg then some (if height.toUInt64 ≤ t then -height else -t.toInt64)
    else if height.toUInt64 < t then none else some t.toInt64
  match low? with
  | none => (2, 0, 0)
  | some low =>
    let t := exactScale b bd.up
    if bd.up.neg && height.toUInt64 < t then (1, 0, 0)
    else
      let high := if bd.up.neg then -t.toInt64 else if height.toUInt64 ≤ t then height
        else t.toInt64
      let (l, h) := numeratorsToBits low high cl (decide (9223372036854775807 - 64 < height))
      (0, l, h)

/-- The bits of the numerators of the search interval with the bounds `bd`
(`Ratpoints.Sieve.IntervalBounds`) at the denominator `b`, for the height bound `height` and the
class `cl`, as `interval_bits` computes them: `lo = ⌈b l⌉` and `hi = ⌊b u⌋` from the forms of the
ends, `(b M + C) >> sh`, by arithmetic shifts; the code `2` for `lo > height`; for `hi < -height`
the code `1` if the interval is taken inline, and otherwise what the products in 128 bits give
(`Ratpoints.Sieve.intervalBitsExact`), the forms of an interval that is not taken inline being those
of an empty one; and otherwise the code `0` with the bits of `lo, …, hi` clipped to
`-height, …, height` (`Ratpoints.Sieve.numeratorsToBits`, in the form that does not split the ends).
The code `0` comes also for an interval that holds no numerator, when `lo > hi`.

C: `find_points.c:3410-3434`

Deviation: the code and the bits returned as a triple, for the `int` and the pointers `low` and
`high` through which the C code writes the bits, the bits `(0, 0)` with the codes `1` and `2`, for
which the C code writes nothing; `Int64` for the `long`s, and `>>>` on `Int64` the arithmetic shift,
for the `>>` of a negative `long`, which the C standard leaves to the implementation and gcc defines
so; the arithmetic of `Int64` wrapping where that of the `long`s overflows, which it does not here,
by the bound of `Ratpoints.Sieve.endForm` on the forms of an interval taken inline and the forms of
an empty one otherwise; no output under `DEBUG`. -/
def intervalBits (b : Int64) (bd : IntervalBounds) (height : Int64) (cl : NumClass) :
    Nat × Int64 × Int64 :=
  let lo := (b * bd.lM + bd.lC) >>> bd.lsh.toInt64
  let hi := (b * bd.uM + bd.uC) >>> bd.ush.toInt64
  if height < lo then (2, 0, 0)
  else if hi < -height then
    if bd.fast then (1, 0, 0) else intervalBitsExact b bd height cl
  else
    let (l, h) := numeratorsToBits (if lo < -height then -height else lo)
      (if height < hi then height else hi) cl false
    (0, l, h)

/-- The moduli of the first two stages with their rows and offsets for the denominator at hand, as
`set_rows` makes the sieve specs, and whether a row is missing: for the `n`-th sieve entry `e` of
`es`, its modulus `p`, the offset of the row of the packing of the class `cl` for the `n`-th
modulus, at the position `n` after the start `cl.offset` of that row in the array `offsets`
(`Ratpoints.Sieve.classOffsets`), the row of the residue `bp[n]`, the denominator divided by the
stride of its class modulo `p` (`Ratpoints.Sieve.fillBpList`), from the table of rows of the entry
in the store `store` (`Ratpoints.Sieve.RowStore.row?`), the empty array when it is not built yet,
the start `0`, which the chunked first stage sets before it reads it
(`Ratpoints.Sieve.chunkStarts`), and the end `p` of the walk of the chunked first stage through the
row; a row is missing when one of them is not built yet, and `Ratpoints.Sieve.buildRows` builds it.

C: `find_points.c:3149-3170`

Deviation: a list of the moduli with their rows and offsets, for the array of sieve specs `ssp` that
`set_rows` fills; the empty array for the null pointer of a row not built yet; the start set to
`0`, where the C code leaves the field as it is until the first stage sets it; the end `p` also for
a row not built yet, where the C code adds `p` to the null pointer; the row read plainly, for the
acquire load that the flag `shared` chooses when threads share the tables of rows; the store of the
tables of rows of the run as an argument, for the arrays `sieve` of the entries that the pointers in
`sieve_list` reach; the array of the row offsets of the run as an argument, which the C code reaches
through the pointer `offset` of the class, and a class without a row of offsets (none, for `NULL`),
which the run never sifts, reads the offsets from position `0`; natural numbers for the `long`s. -/
def setRows (store : RowStore) (es : List SieveEntry) (bp : List Nat) (cl : NumClass)
    (offsets : Array Nat) :
    List SieveSpec × Bool :=
  let rows := (es.zip bp).map fun (e, r) ↦ store.row? e.ref r
  ((es.zip rows).mapIdx fun n (e, row) ↦
    ⟨e.p, offsets[cl.offset.getD 0 + n]!, row.getD #[], 0, e.p⟩, rows.any (·.isNone))

/-- The rows that are missing from the sieve specs `specs` of the first two stages, built, when
`missing` says that one is (`Ratpoints.Sieve.setRows`): for each spec whose row is not built yet, of
the `n`-th sieve entry `e` of `es` and the residue `bp[n]`, the row of `bp[n]` from the table of
rows of its entry, read again, and otherwise built into it by the builder of the entry
(`Ratpoints.Sieve.SieveEntry.fetchRow`), and the end `p` of the walk of the chunked first stage
through the row; the specs and the store with the rows built.

C: `find_points.c:3522-3554`

Deviation: the specs and the store of the tables of rows of the run passed and returned, for the
array of the sieve specs and the arrays `sieve` of the entries; the empty array for the null pointer
of a row not built yet; no lock of the tables (`rp_tables_lock`, `rp_tables_unlock`), and the
pointer read again plainly, for the acquire load, both for the threads that share the tables of
rows, which the model does not have; no measurement of the construction (`RP_INIT_TIC`,
`RP_INIT_TOC`) and no output under `DEBUG`. -/
def buildRows (missing : Bool) (es : List SieveEntry) (bp : List Nat) (specs : List SieveSpec)
    (store : RowStore) :
    Id (List SieveSpec × RowStore) := do
  let mut specs := specs
  let mut store := store
  if missing then
    for n in [0:specs.length] do
      if specs[n]!.row.isEmpty then
        let e := es[n]!
        let (row, st) ← e.fetchRow bp[n]! store
        store := st
        specs := specs.set n { specs[n]! with row, stop := e.p }
  return (specs, store)

/-- The points of the numerators of the bits `low, …, high` of the class `cl` of the denominator `b`
(`Ratpoints.Sieve.numeratorsToBits`), delivered to the callback `process` on the delivery `r`, in
pieces of at most `A` bit arrays, for `A ≥ 1` (for `A = 0` the loop does not end), with the moduli
of the first two stages, their rows and offsets in `specs` and their reciprocals in `mgs`, the first
stage ending after `sp1` of them, the thunk `checks` of the third stage, the thunk `w` of the
products of the check, the degree `d` and the flags `fl`; none if `high < low`. Otherwise, for the
number `rbaLength` of bits of a bit array (`Ratpoints.rbaLength`), the bit arrays have the word
numbers from `wLow = ⌊low / rbaLength⌋` to `wHigh - 1`, for `wHigh = ⌊high / rbaLength⌋ + 1`; and
while `w0 < wHigh`, the piece of the word numbers `w0, …, w1 - 1`, for `w1 = min (w0 + A) wHigh`,
gives its points (`Ratpoints.Sieve.siftPiece`), with the low mask `low - rbaLength wLow` if it is
the first piece and the high mask `rbaLength - 1 - (high mod rbaLength)` if it is the last, so that
the bits that the masks leave lie end to end and make up `low, …, high`; after each piece the loop
returns if the callback has stopped the search.

C: `find_points.c:3563-3612`

Deviation: a function of its own for the bits of one interval of the numerators, the part of the
loop over the intervals of `sift` after the set-up; the size `A` of the pieces as an argument, for
`args->array_size` (line 3571), which `sift` reads through the pointer `args` of the sieving thread;
natural numbers and integers for the `long`s, the word numbers and the masks by the division and the
remainder, rounding down, by `Ratpoints.rbaLength`, for the shift by `RBA_SHIFT` and the mask by
`RBA_LENGTH - 1` (with `Ratpoints.rbaLength = 2 ^ Ratpoints.rbaShift`), which gcc makes the floor
division and the Euclidean remainder on a negative `long` too, the first bits of the bit arrays
staying `long`s for the bits of a height bound below `2 ^ 63`
(`Ratpoints.Sieve.neg_two_pow_le_rbaLength_mul_ediv`,
`Ratpoints.Sieve.rbaLength_mul_ediv_add_one_le_two_pow`); the delivery `r` passed and returned, for
the pointers `info` and `wk->quit` and the count `total` that `sift` keeps from zero and returns,
and the counters `cnt` passed and returned, for those of the sieving thread; no test of the flag
`stop` of a thread of the pool after a piece (line 3610), which is null on the calling thread (line
5129, with the pool excluded with the threads), and no measurement (`RP_SIFT_TOC`) on the return at
a stop. -/
def siftBits {σ : Type} (process : Int → Int → Int → σ → Answer σ) (w : Thunk (List Int))
    (d b A : Nat) (fl : CheckFlags) (sp1 : Nat) (specs : List SieveSpec) (mgs : List Nat)
    (checks : Thunk (List CheckSpec)) (cl : NumClass) (low high : Int) (r : Delivery σ)
    (cnt : Counters) :
    Id (Delivery σ × Counters) := do
  let mut r := r
  let mut cnt := cnt
  if low ≤ high then
    let wLow := low / rbaLength
    let wHigh := high / rbaLength + 1
    let mut range := A
    let mut w0 := wLow
    let mut w1 := wLow + A
    while w0 < wHigh do
      if wHigh < w1 then
        w1 := wHigh
        range := (w1 - w0).toNat
      let maskLow := if w0 = wLow then (low - rbaLength * wLow).toNat else 0
      let maskHigh := if w1 = wHigh then rbaLength - 1 - (high % rbaLength).toNat else 0
      (r, cnt) ← siftPiece process w d b fl sp1 specs mgs checks cl w0 range maskLow maskHigh r cnt
      if r.quit then return (r, cnt)
      w0 := w1
      w1 := w1 + range
  return (r, cnt)

/-- The points of the denominator `b`, for `H < 2 ^ 63`, its numerators in the search intervals with
the bounds `iv` (`Ratpoints.Sieve.exactBounds`, increasing and disjoint), delivered to the callback
`process` on the delivery `r`, in pieces of at most `A` bit arrays, for `A ≥ 1`, in the packing of
its class `cl` (`Ratpoints.Sieve.NumClass`), and the store of the tables of rows with the rows built
for it. What the third stage needs of the sieve entries `es3` of its primes, with the reciprocals
`mgs3` of their moduli, for `b` and `H` (`Ratpoints.Sieve.fillChecks`) is a thunk, and so are the
products `w` of the coefficients `cₖ` with the powers `b^(d - k)`
(`Ratpoints.BruteForce.scaledCoeffs`), both forced when the first numerator of `b` needs them. For
each interval in turn, the bits of its numerators `⌈b l⌉, …, ⌊b u⌋` within the height bound
(`Ratpoints.Sieve.intervalBits`): the code `2` returns, since no later interval holds a numerator
within the bound, and the code `1` goes on to the next interval; at the first interval with the code
`0`, also one without numerators, the sieve specs of the moduli of the first two stages are made,
of the sieve entries `es`, the row of the residue `bp[n]` of `b` divided by the stride of the class
modulo the `n`-th modulus from the table of rows of its entry in `store`, and the offset of the row
of the class for that modulus in `offsets` (`Ratpoints.Sieve.setRows`), with the rows that are not
built yet built into their tables of rows (`Ratpoints.Sieve.buildRows`); and then the points of the
bits of the interval (`Ratpoints.Sieve.siftBits`, with the reciprocals `mgs` of the moduli of the
first two stages, the first stage ending after `sp1` of them, the degree `d` and the flags `fl`),
which returns when the callback stops the search. With the one interval `[-h, h]` of a search
without search intervals, for `h ≥ H`, the numerators are `-H, …, H`.

C: `find_points.c:3112-3114`, `find_points.c:3123-3124`, `find_points.c:3129-3130`,
`find_points.c:3435-3440`, `find_points.c:3442-3488`, `find_points.c:3490-3521`,
`find_points.c:3555-3561`, `find_points.c:3613-3617`, `rp-private.h:574`, `rp-private.h:577-578`,
`rp-private.h:583`, `rp-private.h:585`

Deviation: the height bound converted to `Int64`, which is exact for `H < 2 ^ 63`, and the
denominator too, and the bits back to integers; the bounds of the search intervals an array, for the
struct `rp_intervals` with its pointers `bd` and `end`, which `sift` reaches through the field `iv`
of the sieving thread, which `worker_init` clears (line 3130) and `run_block` sets for each block
(line 3913; here `Ratpoints.Sieve.runBlock`, which passes the array of the run on); one call of
`Ratpoints.Sieve.setRows`, for the two calls with the flag `shared` a constant, between which the
pool of threads chooses, which the model does not have; the store of the tables of rows passed and
returned, for the arrays `sieve` of the entries of the arguments, which `sift` reaches through
`sieve_list` and which keep the rows built for the rest of the run; the end `sp1` of the first
stage, the entries `es` and the reciprocals `mgs` of the first two stages, the entries `es3` of the
third stage and their reciprocals `mgs3` as arguments, for the numbers `sp1`, `sp2` and `sp3` that
the sieving thread keeps (`worker_init`), the entries `sieve_list[0], …, sieve_list[sp2 - 1]`, the
array `magics` of the arguments, which `_ratpoints_sift0` reads, and the entries
`sieve_list[sp2], …, sieve_list[sp3 - 1]` and the reciprocals `magics[sp2], …, magics[sp3 - 1]`,
which `fill_checks` reads, the cut points of the decision of the block (`Ratpoints.Sieve.runBlock`);
the residues `bp` and the class `cl` as values, for the pointers `bp_list` and `cls`, and the array
`offsets` of the row offsets of the run as an argument, which the C code reaches through the pointer
`offset` of the class; the thunk of `Ratpoints.Sieve.fillChecks`, for the table `checks` of the
sieving thread, which `fill_checks` fills, and its flag `stage3_filled`, which `sift` clears; the
thunk of the products `w`, for the flag `compute_bc`, which `sift` sets and `_ratpoints_check_point`
clears when it computes the products; the counters `cnt` passed and returned, for those of the
sieving thread, the count `sifts` one up at the start (line 3461); the delivery `r` passed and
returned, for the pointers `info` and `wk->quit`, which `worker_init` clears, and the count `total`
that `sift` keeps from zero and returns; the arguments of the run passed explicitly, for the pointer
`args` of the sieving thread (`rp-private.h:574`), which `worker_init` sets and through which `sift`
reads them; no pool, slot and stop flag of a thread of the pool, the flag by which the pool of
threads tells it to abandon its block (`pool`, `slot`, `stop`, `rp-private.h:584`, excluded with the
threads); natural numbers and integers for the `long`s; no measurements of the phases
(`RP_SIFT_TIC`, `RP_SETUP_TIC` and their `TOC`) and no output under `DEBUG`. -/
def sift {σ : Type} (process : Int → Int → Int → σ → Answer σ) (c : List Int) (d H A b : Nat)
    (fl : CheckFlags) (sp1 : Nat) (es : List SieveEntry) (mgs bp : List Nat) (cl : NumClass)
    (offsets : Array Nat) (es3 : List SieveEntry) (mgs3 : List Nat) (iv : Array IntervalBounds)
    (store : RowStore) (r : Delivery σ) (cnt : Counters) :
    Id (Delivery σ × RowStore × Counters) := do
  let w : Thunk (List Int) := .mk fun _ ↦ BruteForce.scaledCoeffs c d b
  let checks : Thunk (List CheckSpec) := .mk fun _ ↦ fillChecks b H es3 mgs3
  let mut r := r
  let mut store := store
  let mut cnt := { cnt with sifts := cnt.sifts + 1 }
  let mut doSetup := true
  let mut specs : List SieveSpec := []
  for bd in iv do
    let (empty, low, high) := intervalBits b.toInt64 bd H.toInt64 cl
    if empty = 2 then return (r, store, cnt)
    if empty = 1 then continue
    if doSetup then
      doSetup := false
      let (sp, missing) := setRows store es bp cl offsets
      (specs, store) ← buildRows missing es bp sp store
    (r, cnt) ← siftBits process w d b A fl sp1 specs mgs checks cl low.toInt high.toInt r cnt
    if r.quit then return (r, store, cnt)
  return (r, store, cnt)

/-! ### Examples -/

-- The sieve entries of the examples have the bias, the inverse of `rbaLength` and the inverses of
-- the strides `0`, `0` and the empty array, which `[k]!` reads as `0`: fields that only the packing
-- of the numerators reads, the row offsets (`Ratpoints.Sieve.classOffsets`) the first two and the
-- residues of a denominator (`Ratpoints.Sieve.fillBpList`) the third. The offsets of the sieve
-- specs here are the biases of the moduli, the offsets of the stride 1, or carry a shift that the
-- examples check; the sieve of one denominator in the packings of strided classes, with the row
-- offsets and the residues that the run computes, is an example of `Ratpoints.Model.FindPoints`.

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
    let t := examinePrime [1, 2, 3, 4, 5, 6, 7] 6 p
    (⟨p, [.prime t], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩ : SieveEntry)
  (Id.run (sieveDen 20 7 es)).toList ==
    (List.range 41).map fun i : Nat ↦ survives es 7 ((i : Int) - 20)

-- The survivors of the plain sieve of `y ^ 2 = x ^ 3 - 2` for the denominator 100 give the point
-- `(129 : 3830 : 100)`, which every numerator gives as well.
#guard
  let es := [3, 5, 7, 11, 13].map fun p ↦
    let t := examinePrime [-2, 0, 0, 1] 3 p
    (⟨p, [.prime t], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩ : SieveEntry)
  (Id.run (checkDen [-2, 0, 0, 1] 3 130 100 (Id.run (sieveDen 130 100 es)))).toList ==
    [(129, 3830, 100), (129, -3830, 100)] &&
  (Id.run (checkDen [-2, 0, 0, 1] 3 130 100 (Vector.replicate _ true))).toList ==
    [(129, 3830, 100), (129, -3830, 100)]

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

-- The second stage on a bit array and on one of its words against the words and-ed with the rows of
-- all its moduli, each read at the word number plus its offset, for bit arrays that the rows leave
-- nonzero and that they clear on the way, at word numbers below and above zero, with the
-- reductions by the reciprocals (`small`) and by `mod`, for offsets of at least `rowBias` and
-- below `rowBias + 2 p`, and by `mod` also for offsets `0, …, p - 1`, where the sum can be
-- negative.
#guard
  let es := [3, 5, 7, 11, 13].map fun p ↦
    let t := examinePrime [1, 2, 3, 4, 5, 6, 7] 6 p
    (⟨p, [.prime t], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩ : SieveEntry)
  let row (e : SieveEntry) (b : Nat) : Array UInt64 :=
    (Id.run (e.fetchRow (b % e.p) (e.addTables {}))).1
  let bias (p : Nat) : Nat := p * ((rowBias + p - 1) / p)
  ([(fun p ↦ bias p, true), (fun p ↦ bias p + p - 2, true), (fun p ↦ bias p + 1, false),
      (fun p ↦ p - 1, false)] : List ((Nat → Nat) × Bool)).all fun (off, sm) ↦
  let specs : List SieveSpec := es.map fun e ↦ ⟨e.p, off e.p, row e 7, 0, e.p⟩
  let mgs := es.map (·.magic)
  ([.replicate rbaPack (~~~0), .ofFn fun κ ↦ 1 <<< (κ.val * 13).toUInt64,
      .ofFn fun κ ↦ 0x0123456789abcdef * (κ.val.toUInt64 + 1), .replicate rbaPack 0] :
      List (Vector UInt64 rbaPack)).all fun nums ↦ [-5, 0, 7, 1000].all fun i ↦
    [false, sm].all fun small ↦ (List.range rbaPack).all fun κ ↦
      let ref := specs.foldl (fun x s ↦
        x &&& s.row[rbaPack * ((i + s.offset) % (s.p : Int)).toNat + κ]!) nums[κ]!
      (Id.run (secondStage specs mgs small i nums))[κ]! == ref &&
        Id.run (secondStageWord specs mgs small i κ nums[κ]!) == ref

-- The first stage against the survivor test: bit `t` of word `y` of a piece is bit `t` of the class
-- word and, for every modulus, the row test of the numerator `rbaLength (w0 + offset) + 64 y + t`,
-- for pieces from below and above zero with the moduli 3, 5 and 7, and with `n < r`, `r = 0`, and
-- whole periods and a rest after the first `r` bit arrays; the class words all ones, the word of
-- the denominators `≡ 1 (mod 4)` of `1 2 3 4 5 6 7` (the numerators `≢ 1 (mod 4)`), and the
-- numerators `≡ 1 (mod 8)`; the offsets the biases of the moduli, which leave the numerator
-- `rbaLength w0 + 64 y + t` modulo `p`, and those plus shifts, with the reduction by the
-- reciprocals (`small`) and by `mod`, and offsets below `p`, where the index can be negative, by
-- `mod`.
#guard
  let es := [3, 5, 7].map fun p ↦
    let t := examinePrime [1, 2, 3, 4, 5, 6, 7] 6 p
    (⟨p, [.prime t], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩ : SieveEntry)
  let row (e : SieveEntry) (b : Nat) : Array UInt64 :=
    (Id.run (e.fetchRow (b % e.p) (e.addTables {}))).1
  let bias (p : Nat) : Nat := p * ((rowBias + p - 1) / p)
  ([(fun p ↦ bias p, true), (fun p ↦ bias p + p - 1, true), (fun p ↦ bias p + 2, false),
      (fun p ↦ p - 2, false)] : List ((Nat → Nat) × Bool)).all fun (off, sm) ↦
  ([(-9, 1), (-9, 12), (-35, 4), (6, 2), (15, 17)] : List (Int × Nat)).all fun (w0, n) ↦
    [1, 10].all fun b ↦ [false, sm].all fun small ↦
      [~~~0, 0xdddddddddddddddd, 0x0202020202020202].all fun cw ↦
        let v := Id.run (andRows (es.map fun e ↦ ⟨e.p, off e.p, row e b, 0, e.p⟩) (es.map (·.magic))
          small cw w0 n (Vector.replicate _ 0))
        (List.range (n * rbaPack)).all fun y ↦ (List.range 64).all fun t ↦
          v[y]!.toBitVec.getLsbD t == (cw.toBitVec.getLsbD t &&
            es.all fun e ↦ e.admits b (rbaLength * (w0 + off e.p) + 64 * y + t))

-- One bit array in both arms of the second stage against the reference: the points of the
-- numerators of its set bits that the rows of the moduli of the second stage admit, and the rows of
-- the primes of the third stage, for the point `(129 : 3830 : 100)` of `y ^ 2 = x ^ 3 - 2` and
-- other denominators, bit arrays below and above zero, and the moduli cut into the two stages in
-- several places; in the packings of the stride 1 and of the stride 4 with the residue 3, whose
-- bit `t` of word `κ` stands for the numerator `3 + 4 (rbaLength i + 64 κ + t)`, with the rows of
-- `b 4⁻¹ mod p` read at the offsets `3 (4 rbaLength)⁻¹ mod p` plus the biases, with the reductions
-- by the reciprocals and by `mod`.
#guard
  let c := [-2, 0, 0, 1]
  let es := [3, 5, 7, 11, 13].map fun p ↦
    let t := examinePrime c 3 p
    (⟨p, [.prime t], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩ : SieveEntry)
  let row (e : SieveEntry) (b : Nat) : Array UInt64 :=
    (Id.run (e.fetchRow (b % e.p) (e.addTables {}))).1
  let bias (p : Nat) : Nat := p * ((rowBias + p - 1) / p)
  let inv (x p : Nat) : Nat := Id.run (modinv (x % p) p)
  [(0, 0), (2, 3)].all fun (k, a0) ↦ [0, 2, 5].all fun sp2 ↦ [1, 7, 100].all fun b : Nat ↦
    [-2, 0, 3].all fun i : Int ↦
    ([.replicate rbaPack (~~~0), .ofFn fun κ ↦ 0x0123456789abcdef * (κ.val.toUInt64 + 1)] :
        List (Vector UInt64 rbaPack)).all fun nums ↦
      let w := BruteForce.scaledCoeffs c 3 b
      let es3 := es.drop sp2
      let checks := fillChecks b 2000 es3 (es3.map (·.magic))
      let specs : List SieveSpec := (es.take sp2).map fun e ↦ ⟨e.p,
        a0 * inv (2 ^ k * rbaLength) e.p % e.p + bias e.p, row e (b * inv (2 ^ k) e.p), 0, e.p⟩
      let run (useLong small : Bool) := (Id.run (siftBitArray appendPoint useLong (.pure w) 3 b {}
        specs (specs.map (magic ·.p)) small (.pure checks) ⟨~~~0, k, a0, none⟩ i nums
        ⟨#[], 0, false⟩ {})).1.info.toList
      let ref := (((List.range rbaLength).filter fun t ↦
          nums[t / 64]!.toBitVec.getLsbD (t % 64)).map fun t : Nat ↦
            a0 + 2 ^ k * (i * rbaLength + t)).flatMap
        fun a ↦ if survives es b a then checkNum w b b false a else []
      [false, true].all fun useLong ↦ [false, true].all fun small ↦ run useLong small == ref

-- The set bits of a word, lowest first: with `F(a, 1) = a ^ 2` and no third stage, every numerator
-- `a0 + step t` of a set bit `t` gives its points, after the points already in the array, for the
-- steps 1, 2 and 64; the numerators, each once, are those of the set bits in increasing order.
#guard
  ([0, 1, 0x8000000000000000, 0xf0f0f0f0f0f0f0f0, 0x123456789abcdef1] : List UInt64).all fun x ↦
    [1, 2, 64].all fun step ↦
    let pts := (Id.run (walkWord appendPoint (.pure [0, 0, 1]) 2 1 {} (.pure []) x (-37) step
      ⟨#[(5, 5, 5)], 1, false⟩ {})).1.info.toList
    pts == (5, 5, 5) :: ((List.range 64).filter x.toBitVec.getLsbD).flatMap
      (fun t : Nat ↦ checkNum [0, 0, 1] 1 1 false (-37 + step * t)) &&
    ((pts.drop 1).map (·.1)).eraseDups ==
      ((List.range 64).filter x.toBitVec.getLsbD).map fun t : Nat ↦ -37 + (step * t : Int)

-- The scan of pieces made by hand, with `F(a, 1) = a ^ 2` and no second or third stage: the points
-- of the numerators of the set bits of the words in increasing order, for pieces from below and
-- above zero, with a zero bit array between, before and after bit arrays whose words have bits at
-- both ends, of one bit array, and of zero bit arrays only; the place of the sentinel holds other
-- words at first; in the packings of the stride 1, of the stride 2 with the residue 1 and of the
-- stride 64 with the residue 63, bit `t` of word `y` standing for the numerator
-- `a₀ + 2 ^ k (rbaLength w0 + 64 y + t)`.
#guard
  [(0, 0), (1, 1), (6, 63)].all fun (k, a0) ↦
  ([(3, -2, [1]), (2, 1, [0]), (2, -1, [1]), (1, 5, []), (2, 0, [0, 1])] :
      List (Nat × Int × List Nat)).all fun (n, w0, zeros) ↦
    let v : Vector UInt64 ((n + 1) * rbaPack) := .ofFn fun ⟨y, _⟩ ↦
      if zeros.contains (y / rbaPack) then 0
      else if y % 2 = 0 then 0x8000000000000001 else 1 <<< (y * 7 % 64).toUInt64
    (Id.run (scanPiece appendPoint (.pure [0, 0, 1]) 2 1 {} [] [] false (.pure [])
        ⟨~~~0, k, a0, none⟩ w0 n v ⟨#[], 0, false⟩ {})).1.info.toList ==
      ((List.range (n * rbaPack)).flatMap fun y : Nat ↦
        ((List.range 64).filter v[y]!.toBitVec.getLsbD).map fun t : Nat ↦
          a0 + 2 ^ k * (rbaLength * w0 + 64 * y + t)).flatMap (checkNum [0, 0, 1] 1 1 false)

-- The scan of pieces whose bits are a test of their numerators, with no second or third stage: the
-- points of the numerators of the piece that pass the test, in increasing order.
#guard
  let keep (a : Int) : Bool := a % 5 == 2 || a % 64 == 63
  ([(2, -1), (1, 3)] : List (Nat × Int)).all fun (n, w0) ↦
    let v : Vector UInt64 ((n + 1) * rbaPack) := .ofFn fun ⟨y, _⟩ ↦
      (List.range 64).foldl (fun x (t : Nat) ↦
        if keep (rbaLength * w0 + 64 * (y : Int) + t) then x ||| 1 <<< t.toUInt64 else x) 0
    (Id.run (scanPiece appendPoint (.pure [0, 0, 1]) 2 1 {} [] [] false (.pure [])
        ⟨~~~0, 0, 0, none⟩ w0 n v ⟨#[], 0, false⟩ {})).1.info.toList ==
      (((List.range (n * rbaLength)).map fun k : Nat ↦ rbaLength * w0 + k).filter keep).flatMap
        (checkNum [0, 0, 1] 1 1 false)

-- One piece against the reference over its survivors: the points of the numerators from
-- `rbaLength w0 + maskLow` to `rbaLength (w0 + n) - 1 - maskHigh` that survive the moduli, for
-- pieces from below and above zero with no mask, with one of them and with both, among them the
-- piece of the numerators `-130, …, 130`, and the moduli in the three stages cut in several places,
-- among them all in the first stage, none, and all in the second or in the third; the masks around
-- the numerator 129 of the point `(129 : 3830 : 100)` of `y ^ 2 = x ^ 3 - 2` keep it or drop it;
-- the stride 1, the offsets the biases of the moduli and the word numbers small, so that the
-- reductions multiply by the reciprocals.
#guard
  let c := [-2, 0, 0, 1]
  let es := [3, 5, 7, 11, 13].map fun p ↦
    let t := examinePrime c 3 p
    (⟨p, [.prime t], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩ : SieveEntry)
  let row (e : SieveEntry) (b : Nat) : Array UInt64 :=
    (Id.run (e.fetchRow (b % e.p) (e.addTables {}))).1
  let piece (sp1 sp2 b : Nat) (w0 : Int) (n mL mH : Nat) : List (Int × Int × Int) :=
    let es3 := es.drop sp2
    let specs : List SieveSpec :=
      (es.take sp2).map fun e ↦ ⟨e.p, e.p * ((rowBias + e.p - 1) / e.p), row e b, 0, e.p⟩
    (Id.run (siftPiece appendPoint (.pure (BruteForce.scaledCoeffs c 3 b)) 3 b {} sp1 specs
      (specs.map (magic ·.p)) (.pure (fillChecks b 1000 es3 (es3.map (·.magic))))
      ⟨~~~0, 0, 0, none⟩ w0 n mL mH ⟨#[], 0, false⟩ {})).1.info.toList
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
-- with the flag of the reversal the same points, mapped. The class of the stride 1 with all
-- numerators, whose row offsets are the biases of the moduli, and the residues `b mod p`; the
-- strided classes are examples of `Ratpoints.Model.FindPoints`.
#guard
  let c := [-2, 0, 0, 1]
  let es := [3, 5, 7, 11, 13].map fun p ↦
    let t := examinePrime c 3 p
    (⟨p, [.prime t], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩ : SieveEntry)
  let offsets := (es.map fun e ↦ e.p * ((rowBias + e.p - 1) / e.p)).toArray
  let cuts := (List.range 6).flatMap fun sp2 ↦ (List.range (sp2 + 1)).map (·, sp2)
  let iv := Id.run (exactBounds [((Double.ofInt64 300).neg, Double.ofInt64 300)] 300 300)
  ((4, 2) :: cuts).all fun (sp1, sp2) ↦
    [1, 7, 100].all fun b ↦ [1, 2, 3].all fun A ↦ [false, true].all fun rev ↦
      let ref := (Id.run (checkDen c 3 300 b (Id.run (sieveDen 300 b es)))).toList
      let es3 := es.drop sp2
      (Id.run (sift appendPoint c 3 300 A b { reversed := rev } sp1 (es.take sp2)
        ((es.take sp2).map (·.magic)) ((es.take sp2).map (b % ·.p)) ⟨~~~0, 0, 0, some 0⟩ offsets es3
        (es3.map (·.magic)) iv (es.foldl (fun s e ↦ e.addTables s) {})
        ⟨#[], 0, false⟩ {})).1.info.toList == if rev then ref.map swapPoint else ref

-- The numerator intervals of the search intervals, as the build of ratpoints with `DEBUG` at the
-- pinned commit prints them (`sift: numerator interval [low, high]`) for each interval that `sift`
-- takes, on `ratpoints '1 0 1' H -q -s -dl b0 -du b1` with the intervals given by `-l` and `-u` as
-- hexadecimal doubles, which the program reads exactly: for each case the height bound, the largest
-- denominator `b1`, the ends of the intervals as bits (both zeros, subnormals, infinities, `2 ^ 63`
-- and its neighbours, fractions with long and short mantissas), and the intervals that the run
-- takes at each denominator that it sifts, in the class of the stride 1 and the residue 0, whose
-- bits are the numerators; both paths, the forms of the ends and the products in 128 bits, and the
-- heights around `2 ^ 63 - 65`, where `exact_bounds` stops taking intervals inline.
#guard
  ([
    (2147483648, 1, [(0xc08dd68a00000000, 0xc08dd68a00000000),
        (0x3f64247e90f5380e, 0x40bf56d800000000), (0x43180796d1000000, 0x43e0000000000000)], [(1,
          [(-954, -955), (1, 8022)])]),
    (9223372036854775743, 9223372036854775743, [(0x4103e4eead322000, 0x4103e4eead322000)],
      [(9223372036854775741, []), (9223372036854775743, [])]),
    (9007199254740993, 801010271151204, [(0xc60ba1901eff0258, 0xc12531469ffd6a18),
        (0x3b30000000000000, 0x3c824fdd9bdeb398)], [(801010271151203, [(1, 0)]), (801010271151204,
          [(1, 0)])]),
    (9223372036854775807, 9223372036854775807, [(0xc08d8dae00000000, 0xc08d8dae00000000),
        (0x40fa37f200000000, 0x43dfffffffffffff)], [(9223372036854775807, [])]),
    (10, 3, [(0xc06e9f3400000000, 0x3e3bcc40ceb0c71e), (0x3ea12858b6d3e879, 0x4098826000000000),
        (0x40ecd17600000000, 0x41500368853a7037)], [(1, [(-10, 0), (1, 10)]), (3, [(-10, 0),
            (1, 10)])]),
    (10, 5, [(0xc12567b600000000, 0xbc3d1ea000000000)], [(4, [(-10, -1)]), (5, [(-10, -1)])]),
    (1, 1, [(0xc37f860000000000, 0xc1adc95310ded65a)], [(1, [])]),
    (1, 1, [(0xc0f3d79800000000, 0xc0f3d79800000000), (0xbe58400000000000, 0xbb98000000000000),
        (0x410c7fb000000000, 0x44801fb744320000)], [(1, [(0, -1)])]),
    (10, 9, [(0xc187a8a05c0ca7f4, 0xbb46b9046e19ce13), (0x3b80400000000000, 0x3dfb04330a76f50a)],
      [(8, [(-10, -1), (1, 0)]), (9, [(-10, -1), (1, 0)])]),
    (10, 9, [(0xc12316ec00000000, 0xc0e87cc37401a390), (0xbddd295800000000, 0x4049f5f3de1a7712),
        (0x4081780000000000, 0x4085ea06b8fe90a6)], [(7, [(0, 10)]), (8, [(0, 10)]), (9,
          [(0, 10)])]),
    (10, 8, [(0xc4f1607000000000, 0xc0e8635d99de7a2f), (0xc0a16cc200000000, 0xc031060000000000),
        (0xbee4425c30a5746d, 0x3e177f4000000000)], [(8, [(0, 0)])]),
    (2147483648, 1, [(0xc3e0000000000000, 0xc2cf685da1901fe2),
        (0xc09c8e6c00000000, 0x3da82f6a128ee3f5)], [(1, [(-1827, 0)])]),
    (10, 10, [(0xc11ecf8000000000, 0xc0758a9000000000), (0x40d3f47c00000000, 0x4185084cc0000000)],
      [(8, []), (9, [])]),
    (10, 10, [(0xc190f77d8e000000, 0xc190f77d8e000000), (0x3c6cc97438a17111, 0x3dec7ce5cc0d9ea1),
        (0x4092a35400000000, 0x411d959c00000000)], [(8, [(1, 0)]), (9, [(1, 0)])]),
    (1, 1, [(0xbd96d3403f1e1c8d, 0x3b14d2270d8d8f28), (0x3f3a4c37c59d5725, 0x41bfcbdde6946000)],
      [(1, [(0, 0), (1, 1)])]),
    (10, 5, [(0xc2347d8db94a6f6b, 0xc2347d8db94a6f6b), (0xc08e3dbe00000000, 0x3cb2000000000000)],
      [(5, [(-10, 0)])]),
    (1, 1, [(0xfff0000000000000, 0xc1e2536ac56d7e23)], [(1, [])]),
    (1000, 663, [(0xbefcd299ba18a1ca, 0xbe51d49b1b35069c), (0x3d99642ac9deb1ad, 0x3f30f4e09bcd793e),
        (0x40b4d75000000000, 0x40d79cd000000000)], [(663, [(0, -1), (1, 0)])]),
    (9223372036854775744, 9223372036854775743, [(0xc2f31ed81857c400, 0xc0e9003a00000000)],
      [(9223372036854775743, [])]),
    (9223372036854775743, 9223372036854775741, [(0xc0f873f600000000, 0xc0f873f600000000)],
      [(9223372036854775741, [])]),
    (1000, 1000, [(0xc3dfffffffffffff, 0xc378bedcca5d8da0),
        (0xbdb0972ac5900000, 0x3f0ca7ca00000000), (0x42743dcd46dea5b3, 0x4315cae144d9e2a2)], [(1000,
          [(0, 0)])]),
    (9223372036854775807, 9223372036854775805, [(0x406de31e00000000, 0x406de31e00000000)],
      [(9223372036854775805, [])])] :
      List (Nat × Nat × List (UInt64 × UInt64) × List (Nat × List (Int × Int)))).all
    fun (H, b1, ivs, dens) ↦
  let iv := Id.run (exactBounds (ivs.map fun (l, u) ↦ (⟨l⟩, ⟨u⟩)) H.toInt64 b1.toInt64)
  dens.all fun (b, exp) ↦ (Id.run do
    let mut out : List (Int × Int) := []
    for bd in iv do
      let (e, lo, hi) := intervalBits b.toInt64 bd H.toInt64 ⟨~~~0, 0, 0, none⟩
      if e = 2 then return out
      if e = 1 then continue
      out := out ++ [(lo.toInt, hi.toInt)]
    return out) == exp

-- One denominator in several search intervals against the plain sieve: the points of `-2 0 0 1` at
-- `H = 300` of the denominators 1, 7 and 100 whose `x / z` lies in one of the intervals
-- (`(129 : ±3830 : 100)` in the first region, `(3 : ±5 : 1)` in the second), for intervals with
-- infinite ends, ends at integers, at fractions and beyond the height bound, a degenerate interval
-- at `-0.0` and `0.0`, and an interval with no numerator at `b = 1`; the store of the tables of
-- rows gets rows only when an interval has the code `0` before one has the code `2`, also one
-- without numerators.
#guard
  let c := [-2, 0, 0, 1]
  let es := [3, 5, 7, 11, 13].map fun p ↦
    (⟨p, [.prime (examinePrime c 3 p)], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩ :
      SieveEntry)
  let offsets := (es.map fun e ↦ e.p * ((rowBias + e.p - 1) / e.p)).toArray
  let dy (n : Int) (e : Int) : Double := Double.ofDyadic (n < 0) n.natAbs e
  let inf := Double.huge
  -- `x ≤ a / b` and `a / b ≤ x` for the exact value of a double `x`, an infinity included
  let le (x : Double) (a : Int) (b : Nat) : Bool := if x.isInf then x.signBit else
    let (m, e) := x.toDyadic
    if 0 ≤ e then m * 2 ^ e.toNat * b ≤ a else m * b ≤ a * 2 ^ (-e).toNat
  let ge (x : Double) (a : Int) (b : Nat) : Bool := if x.isInf then !x.signBit else
    let (m, e) := x.toDyadic
    if 0 ≤ e then a ≤ m * 2 ^ e.toNat * b else a * 2 ^ (-e).toNat ≤ m * b
  let regions : List (List (Double × Double) × Bool) :=
    [([(dy (-5) (-1), dy (-3) (-1)), (dy 1 0, dy 5 (-1))], true),
      ([(inf.neg, dy (-401) (-2)), (.zero, .zero), (dy 3 0, dy 31 (-2)), (dy 401 (-1), inf)], true),
      ([(dy 1000 0, inf)], false), ([(inf.neg, dy (-400) 0)], false),
      ([(Double.zero.neg, .zero)], true), ([(⟨0x3fb999999999999a⟩, ⟨0x3fc999999999999a⟩)], true)]
  regions.all fun (dom, built) ↦
    let iv := Id.run (exactBounds dom 300 300)
    [1, 7, 100].all fun b ↦
      let ref := (Id.run (checkDen c 3 300 b (Id.run (sieveDen 300 b es)))).toList.filter
        fun (x, _, _) ↦ dom.any fun (l, u) ↦ le l x b && ge u x b
      let (r, s, _) := Id.run (sift appendPoint c 3 300 2 b {} 2 (es.take 4)
        ((es.take 4).map (·.magic)) ((es.take 4).map (b % ·.p)) ⟨~~~0, 0, 0, some 0⟩ offsets
        (es.drop 4) [magic 13] iv
        (es.foldl (fun s e ↦ e.addTables s) {}) ⟨#[], 0, false⟩ {})
      r.info.toList == ref &&
        (s.row? (.prime 3) (b % 3) |>.isSome) == (built || b % 3 == 0)

-- The stop and the flags of the output through the sieve of one denominator, on `y ^ 2 = x ^ 2`,
-- where every numerator prime to the denominator gives a point, with pieces of one bit array: a
-- callback that stops at its `k`-th call gets the first `k` calls of the search without a stop,
-- the count is their number, and the flag is set when the search has that many calls; under
-- `RATPOINTS_NO_Y` the points with `y ≥ 0`; under `RATPOINTS_NO_CHECK` the numerators that survive
-- the moduli, prime to the denominator, with `y = 0`.
#guard
  let c := [0, 0, 1]
  let es := [3, 5, 7, 11, 13].map fun p ↦
    (⟨p, [.prime (examinePrime c 2 p)], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩ :
      SieveEntry)
  let offsets := (es.map fun e ↦ e.p * ((rowBias + e.p - 1) / e.p)).toArray
  let stopAt (k : Nat) (x z y : Int) (pts : Array (Int × Int × Int)) :
      Answer (Array (Int × Int × Int)) := ⟨1, pts.size + 1 == k, pts.push (x, y, z)⟩
  let iv := Id.run (exactBounds [((Double.ofInt64 300).neg, Double.ofInt64 300)] 300 300)
  let run (k b : Nat) (fl : CheckFlags) : Delivery (Array (Int × Int × Int)) :=
    (Id.run (sift (stopAt k) c 2 300 1 b fl 2 (es.take 4) ((es.take 4).map (·.magic))
      ((es.take 4).map (b % ·.p)) ⟨~~~0, 0, 0, some 0⟩ offsets (es.drop 4) [magic 13] iv
      (es.foldl (fun s e ↦ e.addTables s) {}) ⟨#[], 0, false⟩ {})).1
  [1, 7].all fun b ↦
    let full := (run 0 b {}).info.toList
    let surv := (BruteForce.numerators 300).filter fun a ↦ Int.gcd a b == 1 && survives es b a
    full == (Id.run (checkDen c 2 300 b (Id.run (sieveDen 300 b es)))).toList &&
    ([1, 2, 3, 9, 100, full.length - 1, full.length, full.length + 1].all fun k ↦
      let r := run k b {}
      r.info.toList == full.take k && r.total == min k full.length &&
        r.quit == decide (k ≤ full.length)) &&
    (run 0 b { noY := true }).info.toList == full.filter (0 ≤ ·.2.1) &&
    (run 0 b { noCheck := true }).info.toList == surv.map (fun a ↦ (a, 0, (b : Int))) &&
    (run 3 b { noCheck := true }).info.toList == (surv.take 3).map fun a ↦ (a, 0, (b : Int))

-- The tables of rows through a run of three denominators: the sieve entries of the primes 3, 5, 7
-- and 11, of the prime power 9 and of the product 15 = 3 · 5, which shares the tables of rows of 3
-- and 5, the first five in the first two stages and 11 in the third, their tables of rows made by
-- `Ratpoints.Sieve.SieveEntry.addTables`; the denominators 1, 7 and 100 sifted in turn with one
-- store, each finding the points of the plain sieve; afterwards every table of rows holds the row
-- of `0` of a prime and the rows of the residues of the denominators that the first two stages
-- read, those that the product built for its factors among them, each the closed form of its row,
-- and no others: the prime 11 of the third stage needs none.
#guard
  let c := [-2, 0, 0, 1]
  let closed (adm : Nat → Bool) (n : Nat) : Array UInt64 := (Array.range n).map fun j ↦
    (List.range 64).foldl (fun w t ↦ if adm (64 * j + t) then w ||| 1 <<< t.toUInt64 else w) 0
  let pr (p : Nat) : SieveEntry :=
    ⟨p, [.prime (examinePrime c 3 p)], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩
  let pw9 := Id.run (examinePower c 3 3 2 true true)
  let e15 : SieveEntry := ⟨15, [.prime (examinePrime c 3 3), .prime (examinePrime c 3 5)],
    magic 15, 0, 0, #[], .product 2, .product, 0.0, 2⟩
  let e9 : SieveEntry := ⟨9, [.power pw9], magic 9, 0, 0, #[], .power 3 2, .power, 0.0, 1⟩
  let es := [pr 3, e9, e15, pr 5, pr 7, pr 11]
  let offsets := (es.map fun e ↦ e.p * ((rowBias + e.p - 1) / e.p)).toArray
  let es2 := es.take 5
  let iv := Id.run (exactBounds [((Double.ofInt64 300).neg, Double.ofInt64 300)] 300 300)
  let (ok, s) := [1, 7, 100].foldl (fun (ok, s) b ↦
    let ref := (Id.run (checkDen c 3 300 b (Id.run (sieveDen 300 b es)))).toList
    let (r, s, _) := Id.run (sift appendPoint c 3 300 2 b {} 2 es2 (es2.map (·.magic))
      (es2.map (b % ·.p)) ⟨~~~0, 0, 0, some 0⟩ offsets [pr 11] [magic 11] iv s ⟨#[], 0, false⟩ {})
    (ok && r.info.toList == ref, s)) (true, es.foldl (fun s e ↦ e.addTables s) {})
  let present (k : EntryRef) : List Nat :=
    (List.range (s.getD k #[]).size).filter fun r ↦ (s.row? k r).isSome
  ok && s.size == 6 && present (.prime 3) == [0, 1] && present (.power 3 2) == [1, 7] &&
    present (.product 2) == [1, 7, 10] && present (.prime 5) == [0, 1, 2] &&
    present (.prime 7) == [0, 1, 2] && present (.prime 11) == [0] &&
    es.all fun e ↦ (present e.ref).all fun r ↦
      s.row? e.ref r == some (closed (fun N ↦ e.admits r N) ((e.p + chunk - 1) * rbaPack))

-- The bits of the numerators `-H, …, H` in the packings of the strides `2 ^ k`, `k ≤ 6`, with every
-- residue: both forms give `⌈(-H - a₀) / 2 ^ k⌉` and `⌊(H - a₀) / 2 ^ k⌋`, for heights from 0 up,
-- around `2 ^ 63 - 65`, where the C code changes forms, and up to the largest `long` `2 ^ 63 - 1`;
-- the plain form only up to `2 ^ 63 - 65`, the split form for all of them.
#guard (List.range 7).all fun k ↦ (List.range (2 ^ k)).all fun a0 ↦
  ([0, 1, 2, 3, 63, 64, 1000, 2 ^ 62, 2 ^ 63 - 129, 2 ^ 63 - 66, 2 ^ 63 - 65, 2 ^ 63 - 64,
      2 ^ 63 - 2, 2 ^ 63 - 1] : List Nat).all fun H ↦
    let cl : NumClass := ⟨1, k, a0, none⟩
    let lo : Int := -((H + a0 : Nat) / (2 ^ k : Nat) : Int)
    let hi : Int := ((H : Int) - a0) / (2 ^ k : Nat)
    let bits (split : Bool) := numeratorsToBits (-H.toInt64) H.toInt64 cl split
    (bits true).1.toInt == lo && (bits true).2.toInt == hi &&
      (2 ^ 63 - 65 < H || (bits false).1.toInt == lo && (bits false).2.toInt == hi)

-- The interval of bits is empty for `H = 1`, `k = 2`, `a₀ = 2`, whose class has no numerator in
-- `-1, 0, 1`: the bits from `0` to `-1`; and it ends below `0` for `H = 3`, `k = 3`, `a₀ = 5`,
-- whose only numerator `-3` has the bit `-1`.
#guard numeratorsToBits (-1) 1 ⟨1, 2, 2, none⟩ false == (0, -1) &&
  numeratorsToBits (-3) 3 ⟨1, 3, 5, none⟩ false == (-1, -1)

-- The plain form wraps at the largest `long` `H = 2 ^ 63 - 1` for `k = 1`, `a₀ = 1`: `a₀ + H` is
-- `2 ^ 63`, which wraps to `-2 ^ 63`, so that its low bit is `2 ^ 62` in place of `-2 ^ 62`, the
-- low bit of the split form, which the C code takes there.
#guard
  let H : Nat := 2 ^ 63 - 1
  (numeratorsToBits (-H.toInt64) H.toInt64 ⟨1, 1, 1, none⟩ false).1.toInt == 2 ^ 62 &&
    (numeratorsToBits (-H.toInt64) H.toInt64 ⟨1, 1, 1, none⟩ true).1.toInt == -2 ^ 62

end Sieve

end Ratpoints

end
