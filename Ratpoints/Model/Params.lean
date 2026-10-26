/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Constants
public import Ratpoints.Model.Double

-- The `#guard` examples use the constants and the doubles at compile time.
meta import Ratpoints.Model.Constants
meta import Ratpoints.Model.Double

/-!
# The sieving parameters

The free choices of the sieve: which moduli it uses, in which order and in which stage, at most how
many forbidden divisors of the denominators it tests, whether it runs the Jacobi test, and at most
how many bit arrays it treats at a time. ratpoints chooses the moduli and their stages from the
curve and corrects the choice during the run, and takes the other choices from its options or its
defaults (the program passes the array size `Ratpoints.defaultArraySize`); none of this changes the
points found or their order, since a modulus only removes candidates that are not points, the pieces
of the numerators follow one another in increasing order, a test on the denominators removes only
denominators without points, and the two shapes of the loop over the denominators between which
these choices decide, the words of 64 denominators and every denominator, both run in increasing
order. The model makes the choice inside the search, as `find_points` does, and the theorems hold
for every value of the options of the sieve, whatever moduli the search chooses.

The parameters are the result of the choice of the moduli from the curve (`Ratpoints.sievingInfo`),
from the options of the sieve that the caller gives (`Ratpoints.SieveOptions`) as the search
normalizes them (`Ratpoints.SieveOptions.normalize`), with the end of the third stage, the number of
primes looked at in all and the estimates of the run that the correction of the moduli reads. The
sieve reads the moduli, the cut points of its stages and the array size, and the tests on the
denominators read the bound on the forbidden divisors and the switch of the Jacobi test.

## Main definitions

* `Ratpoints.Params`: the sieving parameters, the result of the choice of the moduli.
* `Ratpoints.arraySizeAt`, `Ratpoints.Params.arraySizeAt`: at most how many bit arrays a piece of
  the numerators has, for a height bound.
* `Ratpoints.SieveOptions`: the values of the options of the program that tune the sieve.
* `Ratpoints.SieveOptions.normalize`: those values as the search normalizes them.
-/

@[expose] public section

namespace Ratpoints

/-- The sieving parameters: the free choices of the sieve, internal to the search, as the choice of
the moduli gives them to the run (`Ratpoints.sievingInfo`): the moduli, cut into stages,
the first `sp1` of them, then those up to `sp2`, then those up to `sp3`, the rest being the reserve
from which the correction of the moduli may take further primes; how many primes the loop of the
tables examined and how many were looked at in all; at most how many forbidden divisors are tested,
whether the Jacobi test may run, at most how many bit arrays a piece of the numerators has; and the
estimates of the run, the cost of one exact check and the number of words at which the first
correction of the moduli is made. The run of the search reads the cut points of the stages and the
array size, and the correction of the moduli between its blocks the estimates of the run, the cost
of a check and the words of the first correction; the moduli come to the run as their sieve entries
(`Ratpoints.SievingInfo`).

C: `ratpoints.h:368`, `ratpoints.h:395-397`, `ratpoints.h:406`

Deviation: the parameters as a structure of their own, for the fields of the arguments that
`find_points_work` normalizes and `sieving_info` sets (`sp1`, `sp2`, `sp3`, `sp3_max` as the length
of the moduli, `max_forbidden`, `array_size`, `run_words`, `run_denoms`, `adapt_at`, `check_rel`)
and the local `pn_lim` of `sieving_info`, after the loop of the tables (`examined`) and at the end
(`lookedAt`); the Jacobi switch a Boolean (`Ratpoints.Params.jacobi`), true when the bit
`RATPOINTS_NO_JACOBI` of the flags is clear, for that bit of `args->flags`, which `main.c` clears
with the others; a natural number for the `long` field `array_size` (`Ratpoints.Params.arraySize`),
`0` for the default, which the library takes for every value `≤ 0`
(`Ratpoints.Params.arraySizeAt`); `Float`s for the doubles and a `UInt64` for the
`unsigned long`. -/
structure Params where
  /-- The moduli in the order of the stages, the reserve last: primes of `Ratpoints.primeTable`,
  powers of them and products of such powers, below `Ratpoints.maxPrimeEven`. -/
  moduli : List Nat
  /-- How many primes the loop of the tables examines, the first of `Ratpoints.primeTable`: the
  curve has no points when it has none modulo one of them, they give the first forbidden divisors,
  and the moduli take the tables of those among their prime factors. -/
  examined : Nat
  /-- How many primes were looked at in all, the third stage included. -/
  lookedAt : Nat
  /-- The end of the first stage, a position in `Ratpoints.Params.moduli`. -/
  sp1 : Nat
  /-- The end of the second stage, a position in `Ratpoints.Params.moduli`. -/
  sp2 : Nat
  /-- The end of the third stage, a position in `Ratpoints.Params.moduli`; the reserve is the
  rest. -/
  sp3 : Nat
  /-- At most how many forbidden divisors of the denominators are tested. -/
  maxForbidden : Nat
  /-- Whether the Jacobi test on the denominators may run: it runs when also the polynomial
  searched, after the reversal check, has even degree and a leading coefficient that is not a
  square. -/
  jacobi : Bool
  /-- At most how many bit arrays a piece of the numerators has, the field `array_size` of the
  arguments of the library; `0` for `Ratpoints.defaultArraySize`. -/
  arraySize : Nat := 0
  /-- The estimate of the number of words that the run sweeps, `run_words`. -/
  runWords : Float := 1.0
  /-- The estimate of the number of denominators that the run sifts, `run_denoms`. -/
  runDenoms : Float := 1.0
  /-- The cost of one exact check relative to `Ratpoints.checkReference`, `check_rel`. -/
  checkRel : Float := 1.0
  /-- The number of words at which the first correction of the moduli is made, `adapt_at`, or
  `2 ^ 64 - 1` when the search may not correct its choice. -/
  adaptAt : UInt64

/-- At most how many bit arrays a piece of the numerators has for the field `a` of the array size,
`0` for `Ratpoints.defaultArraySize`, and the height bound `H`: `a`, or `Ratpoints.defaultArraySize`
for `0`, capped at `2 ⌈H / 64⌉` and at `Ratpoints.maxArraySize`, then rounded up to a multiple of
`Ratpoints.chunk`, which stays at most the cap `Ratpoints.maxArraySize`, a multiple of the chunk; at
least 1 for `H ≥ 1` (`Ratpoints.one_le_arraySizeAt`).

C: `rp-private.h:87`, `find_points.c:4666-4677`

Deviation: a `Nat` for the `long` field, so that only `0` stands for the default, which the library
takes for every value `≤ 0`; `64` for `LONG_LENGTH`; and the macro `CEIL` of a natural number `x` by
`d` as `(x + d - 1) / d`, which is its value for every `x ≥ 0`. -/
def arraySizeAt (a H : Nat) : Nat :=
  let a := min (min (if a = 0 then defaultArraySize else a) (2 * ((H + 63) / 64))) maxArraySize
  (a + chunk - 1) / chunk * chunk

/-- At most how many bit arrays a piece of the numerators has for the height bound `H`, by the
field `arraySize` of the parameters `P` (`Ratpoints.arraySizeAt`); at least 1 for `H ≥ 1`
(`Ratpoints.Params.one_le_arraySizeAt`). It models no C code of its own. -/
def Params.arraySizeAt (P : Params) (H : Nat) : Nat := Ratpoints.arraySizeAt P.arraySize H

/-- The values of the options of ratpoints that tune the sieve, as the program reads them into the
fields of its `ratpoints_args` (`Ratpoints.SieveOptions.store`): `-p`, `-n`, `-N`, `-R`, `-A`, `-P`
and `-F` give C `long`s, which are `-1`, as in `main.c`, when the option is absent; `-r`, `-U`,
`-C`, `-Q` and `-W` give doubles, `-1.0` when absent; `-j` switches the Jacobi test off and `-J` on
again; and the array size is `Ratpoints.defaultArraySize`, which the program sets.

C: `main.c:337-347`, `main.c:349-350`, `main.c:352`, `ratpoints.h:365-367`

Deviation: integers for the `long`s of the fields, doubles by their bits (`Ratpoints.Double`) for
the doubles, as the program reads doubles (`Ratpoints.Cli.scanDouble?`), and a Boolean for the bit
`RATPOINTS_NO_JACOBI` of the flags, which `main.c` clears with the others; the bit of the reversal
is in `Ratpoints.Options`. -/
structure SieveOptions where
  /-- The value of `-p`: how many primes are looked at (examined). -/
  numPrimes : Int := -1
  /-- The value of `-n`: the end of the first stage, negative to choose it from the curve. -/
  sp1 : Int := -1
  /-- The value of `-N`: the end of the second stage, negative to choose it from the curve. -/
  sp2 : Int := -1
  /-- The value of `-r`: the target of the rule that ends the first stage, `survivors_per_word`;
  values not `> 0`, that is `≤ 0` or NaN, for `Ratpoints.survivorsPerWord`. -/
  survivorsPerWord : Double := Double.minusOne
  /-- The value of `-R`: how many moduli the second stage adds in a long run, `sp2_extra`;
  negative for `Ratpoints.sp2Extra`. -/
  sp2Extra : Int := -1
  /-- The value of `-U`: the run length at which a modulus of the second stage pays for itself,
  `sp2_u0`; values not `≥ 0`, that is negative or NaN, for `Ratpoints.sp2U0`. -/
  sp2U0 : Double := Double.minusOne
  /-- The value of `-C`: what one row of a sieve table costs, `cost_table`; values not `≥ 0`, that
  is negative or NaN, for `Ratpoints.costTable`. -/
  costTable : Double := Double.minusOne
  /-- The value of `-A`: how much of the choice is corrected during the run, `adapt`: `0` none,
  `1` the third stage, `2` and more the second too, negative for `1`. -/
  adapt : Int := -1
  /-- The value of `-P`: how many primes the third stage adds, negative to choose it from the
  curve. -/
  sp3Extra : Int := -1
  /-- The value of `-Q`: what one prime of the third stage costs per denominator, `sp3_per_denom`;
  values not `≥ 0`, that is negative or NaN, for `Ratpoints.sp3PerDenom`. -/
  sp3PerDenom : Double := Double.minusOne
  /-- The value of `-W`: what one exact check costs, `check_cost`; values not `> 0`, that is `≤ 0`
  or NaN, to estimate it from the curve (`Ratpoints.checkCost`). -/
  checkCost : Double := Double.minusOne
  /-- The array size, `array_size`: at most how many bit arrays a piece of the numerators has;
  values `≤ 0` for `Ratpoints.defaultArraySize`. -/
  arraySize : Int := defaultArraySize
  /-- The value of `-F`: at most how many forbidden divisors are tested. -/
  maxForbidden : Int := -1
  /-- Whether the Jacobi test runs: `false` when `-j` is the last of `-j` and `-J`. -/
  jacobi : Bool := true

/-- The options `s` as `find_points_work_1` normalizes the fields of the arguments that hold them:
the number of the primes looked at `Ratpoints.defaultNumPrimes` for a negative one and at most
`Ratpoints.numPrimes`; the end of the second stage at most that number, and that of the first at
most that of the second when the second is given (`≥ 0`); at most `Ratpoints.defaultMaxForbidden`
forbidden divisors for a negative bound and at most the size of the table. Whether the caller left
the number of primes to the search (`np_is_default`) is read from `s` before this normalization.
The search normalizes the options so (`Ratpoints.findPointsWork`) and makes the choice of the moduli
with the normalized options (`Ratpoints.sievingInfo`).

C: `find_points.c:4643-4649`, `find_points.c:4655-4656`, `find_points.c:4662-4665`

Deviation: the normalized options returned, for the fields of the arguments that the C code
normalizes in place and restores in `find_points_work` (lines 4542-4545 and 4560-4563); the array
size normalized with the height bound where it is read (`Ratpoints.arraySizeAt`); no enlargement of
the buffer of the rows (line 4654), which the model does not have; integers for the `long`s. -/
def SieveOptions.normalize (s : SieveOptions) : SieveOptions :=
  let numPrimes : Int :=
    min (if s.numPrimes < 0 then defaultNumPrimes else s.numPrimes) Ratpoints.numPrimes
  let sp2 : Int := if numPrimes < s.sp2 then numPrimes else s.sp2
  let sp1 : Int := if 0 ≤ sp2 && sp2 < s.sp1 then sp2 else s.sp1
  let mf : Int := if s.maxForbidden < 0 then defaultMaxForbidden else s.maxForbidden
  { s with numPrimes, sp1, sp2, maxForbidden := min mf primeTable.size }

/-! ### Examples -/

-- The array size: `2 ⌈H / 64⌉` rounded up to a multiple of the chunk 16, up to the default 256,
-- which it reaches at `H = 8129` and, rounded up, at `H = 7681`; the default for the field `0`;
-- fields of 10, rounded up, and of 48, a multiple of the chunk; and the cap `2 ^ 20`, a multiple
-- of the chunk, from `H = 2 ^ 25 + 1` on, which the rounding up does not pass.
#guard [1, 64, 65, 1000, 7680, 7681, 8128, 8129, 100000].map (arraySizeAt 256) ==
  [16, 16, 16, 32, 240, 256, 256, 256, 256]
#guard arraySizeAt 0 100000 == 256 && arraySizeAt 10 100000 == 16 && arraySizeAt 48 100000 == 48
#guard [2 ^ 25, 2 ^ 25 + 1].map (arraySizeAt 3000000) == [2 ^ 20, 2 ^ 20]

-- The defaults of a run without options as the search normalizes them, and the normalization of
-- `-p 100 -N 40 -n 50 -F 200`: 53 primes, both cut points at 40, 171 forbidden divisors; `-N 60`
-- capped at the 30 primes of the default, and `-n 50` without `-N` left as it is.
#guard let s := ({} : SieveOptions).normalize
  s.numPrimes == 30 && s.sp1 == -1 && s.sp2 == -1 && s.maxForbidden == 64 && s.jacobi &&
    s.arraySize == 256 && s.adapt == -1 && s.checkCost.bits == 0xbff0000000000000
#guard let s := ({ numPrimes := 100, sp1 := 50, sp2 := 40, maxForbidden := 200 } :
    SieveOptions).normalize
  s.numPrimes == 53 && s.sp1 == 40 && s.sp2 == 40 && s.maxForbidden == 171
#guard ({ sp2 := 60 } : SieveOptions).normalize.sp2 == 30 &&
  ({ sp1 := 50 } : SieveOptions).normalize.sp1 == 50

end Ratpoints

end
