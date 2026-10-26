/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

/-!
# The compile-time constants of ratpoints

The constants that the C code of ratpoints fixes when it is compiled, each a definition with the
value of the default build and a docstring that names its macro, and the table of primes from which
the sieve takes its moduli. Changing a constant changes the model as changing the macro changes the
C program: no proof depends on the values of the constants beyond the facts checked here by
`decide`, that `Ratpoints.rbaPack`, `Ratpoints.chunk`, `Ratpoints.defaultArraySize` and
`Ratpoints.maxArraySize` are positive, that `Ratpoints.mulModLimit` is below `2 ^ 64` and `2 ^ 32`
(`Ratpoints.mulModLimit_lt_size`, `Ratpoints.mulModLimit_lt_two_pow_32`), that `Ratpoints.rbaLength`
is `2 ^ Ratpoints.rbaShift` with `Ratpoints.rbaShift < 32`
(`Ratpoints.rbaLength_eq_two_pow_rbaShift`, `Ratpoints.rbaShift_lt_thirty_two`), that
`2 Ratpoints.rowBias - 1` is at most `Ratpoints.mulModLimit`
(`Ratpoints.two_mul_rowBias_sub_one_le_mulModLimit`), that `Ratpoints.numStrides` is at least 1
(`Ratpoints.one_le_numStrides`), that `Ratpoints.hornerSteps` is at least 1
(`Ratpoints.one_le_hornerSteps`), that `Ratpoints.maxBitsInPrime` is at most 10
(`Ratpoints.maxBitsInPrime_le_ten`), that `Ratpoints.stage3Limit` is at most `2 ^ 32`
(`Ratpoints.stage3Limit_le_two_pow_32`), that `Ratpoints.maxDegree` is positive and below `2 ^ 57`
(`Ratpoints.zero_lt_maxDegree`, `Ratpoints.maxDegree_lt_two_pow_57`) and that a block length that
`Ratpoints.blockLen` fixes is positive (`Ratpoints.blockLen_pos`), and of the table
the proofs use only that its entries are the odd primes below 1022, in increasing order
(`Ratpoints.prime_of_mem_primeTable`, which checks them one by one, and
`Ratpoints.lt_of_mem_primeTable`, `Ratpoints.mem_primeTable_of_prime` and
`Ratpoints.pairwise_lt_toList_primeTable`, which `decide` checks).

## Main definitions

* `Ratpoints.maxDegree`: the largest degree that ratpoints accepts.
* `Ratpoints.primeTable`: the odd primes below 1024, among which the moduli are chosen.
* `Ratpoints.maxBitsInPrime`, `Ratpoints.numPrimes`, `Ratpoints.maxPrimeEven`: the moduli are
  chosen among the primes of the table below `maxPrimeEven = 2 ^ maxBitsInPrime`, the first
  `numPrimes` of them, and the prime powers and products of them below `maxPrimeEven`.
* `Ratpoints.modWords`: the number of 64-bit words of a pattern of `maxPrimeEven` bits.
* `Ratpoints.hornerSteps`: after how many steps Horner's rule reduces its accumulator in the table
  of a prime.
* `Ratpoints.defaultNumPrimes`, `Ratpoints.defaultMaxForbidden`: how many primes the sieve takes
  and at most how many forbidden divisors it tests, unless the options say.
* `Ratpoints.defaultSp1`, `Ratpoints.sp2Extra`: where the first stage of the sieve ends, and how
  many moduli the second stage adds, unless the options say.
* `Ratpoints.survivorsPerWord`, `Ratpoints.sp2U0`, `Ratpoints.sp3PerSurvivor`,
  `Ratpoints.sp3PerDenom`, `Ratpoints.sp3Coprime`, `Ratpoints.costTable`, `Ratpoints.compositeMax`,
  `Ratpoints.costBp`, `Ratpoints.costSetup`, `Ratpoints.costCall`, `Ratpoints.costLine`,
  `Ratpoints.costPhase2`, `Ratpoints.costSurvivor`, `Ratpoints.costCheck`, `Ratpoints.checkStep`,
  `Ratpoints.checkLimb`, `Ratpoints.checkCall`, `Ratpoints.checkRoot`,
  `Ratpoints.checkReference`: the tuning of the cost model by which ratpoints chooses its moduli,
  the macros of `ratpoints.h`, doubles but for the largest composite modulus.
* `Ratpoints.maxModuli`, `Ratpoints.maxFactors`, `Ratpoints.modulusTableMax`,
  `Ratpoints.runShapeSamples`, `Ratpoints.invStride`: the bounds and the constants of the choice
  of the moduli in `find_points.c` and `rp-private.h`.
* `Ratpoints.adaptWords`, `Ratpoints.adaptArrays`, `Ratpoints.adaptBits`, `Ratpoints.adaptLag`:
  when the run first corrects its moduli, and how many blocks later a correction takes effect.
* `Ratpoints.blocksWanted`, `Ratpoints.blockMin`, `Ratpoints.blockLen`: the blocks into which the
  run cuts its steps.
* `Ratpoints.defaultSturm`: the depth of the Sturm step, unless the options say.
* `Ratpoints.rbaPack`, `Ratpoints.rbaLength`, `Ratpoints.rbaShift`: how many words and how many
  bits a bit array of the sieve has, and the logarithm of the second.
* `Ratpoints.chunk`: the number of bit arrays that the first stage of the sieve takes at a time.
* `Ratpoints.defaultArraySize`, `Ratpoints.maxArraySize`: at most how many bit arrays a piece of
  the numerators has, unless the parameters say, and in any case.
* `Ratpoints.maxDivisors`: the bound, never reached, on the number of squarefree divisors of the
  leading coefficient that `Ratpoints.Setup.setupUs1` gives for the loop over the denominators of a
  polynomial of odd degree.
* `Ratpoints.veryBig`: the valuation of `0` in the C code.
* `Ratpoints.jacobiPrimes`, `Ratpoints.jacobiTable`, `Ratpoints.mulModLimit`: the bounds of the
  Jacobi test by tables; the last is the largest value that the C code reduces by a multiplication,
  in the Jacobi test and in the third stage of the sieve.
* `Ratpoints.stage3Limit`: the bound below which the third stage of the sieve reduces by a
  multiplication.
* `Ratpoints.useLongInPhase2`: whether the second stage of the sieve runs one word at a time.
* `Ratpoints.rowBias`: the lower bound of the multiple of a modulus that the offset of a row
  carries.
* `Ratpoints.numStrides`: the number of the strides with which the numerators are packed.
-/

@[expose] public section

namespace Ratpoints

/-- The largest degree of a polynomial that ratpoints accepts, `RATPOINTS_MAX_DEGREE`: a list of
coefficients has at most `maxDegree + 1` entries.

C: `ratpoints.h:33` -/
def maxDegree : Nat := 100

/-- The odd primes below 1024, in increasing order: the table `prime` of `primes.h`, of size
`PRIMES1000`, which `find_points.c` includes, among which ratpoints chooses its moduli.

C: `primes.h:29-40`, `find_points.c:32` -/
def primeTable : Array Nat :=
  #[3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97,
    101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193,
    197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307,
    311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421,
    431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547,
    557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659,
    661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797,
    809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929,
    937, 941, 947, 953, 967, 971, 977, 983, 991, 997, 1009, 1013, 1019, 1021]

/-- The size in bits of the moduli, `RATPOINTS_MAX_BITS_IN_PRIME`: the sieve chooses its moduli
among the primes of `Ratpoints.primeTable` below `2 ^ maxBitsInPrime`.

C: `rp-private.h:321-323`

Deviation: 8, the value of the default build, which the Makefile of ratpoints passes to the
compiler (its variable `PRIME_SIZE`), for the value 7 that the header takes when it is given
none. -/
def maxBitsInPrime : Nat := 8

/-- The number of primes of `Ratpoints.primeTable` below `2 ^ Ratpoints.maxBitsInPrime`, among
which the sieve chooses its moduli, `RATPOINTS_NUM_PRIMES`: 53 in the default build.

C: `rp-private.h:325-361`

Deviation: computed from `Ratpoints.maxBitsInPrime`, where the header lists the values for 5 to 10
bits, the numbers that the computation gives, and takes 7 bits for any other value; the largest such
prime, `RATPOINTS_MAX_PRIME`, has no counterpart; the power of 2 above it is
`Ratpoints.maxPrimeEven`. -/
def numPrimes : Nat := (primeTable.toList.filter (· < 2 ^ maxBitsInPrime)).length

/-- The power of 2 above the moduli, `RATPOINTS_MAX_PRIME_EVEN`: the moduli of the sieve, primes,
prime powers and products of them, are below it, as are the primes of `Ratpoints.primeTable` among
which the sieve chooses its moduli.

C: `rp-private.h:325-361`

Deviation: computed from `Ratpoints.maxBitsInPrime`, where the header lists the values for 5 to
10 bits, the powers of 2 that the computation gives, and takes 7 bits for any other value. -/
def maxPrimeEven : Nat := 2 ^ maxBitsInPrime

/-- The number of 64-bit words of a pattern of `Ratpoints.maxPrimeEven` bits, `RP_MODWORDS`: the
size of the bit arrays of the tables of a prime power, one bit for each residue modulo the prime
power (`Ratpoints.Sieve.Power`).

C: `rp-private.h:523`

Deviation: `64` for `LONG_LENGTH`. -/
def modWords : Nat := (maxPrimeEven + 64 - 1) / 64

/-- After how many steps Horner's rule modulo a prime reduces its accumulator in `examine_prime`
(`Ratpoints.Sieve.hornerBarrett`), `RP_HORNER_STEPS`: `64 / maxBitsInPrime - 1`. After `k` steps
from a value below `p` with coefficients and argument below `p`, the accumulator is below
`p ^ (k + 1)`, so that for `p < 2 ^ maxBitsInPrime` it stays below `2 ^ 64` up to `hornerSteps`
steps. The schedule reduces at all only for `1 ≤ hornerSteps`, that is for `maxBitsInPrime ≤ 32`
(`Ratpoints.one_le_hornerSteps`).

C: `find_points.c:1652-1655`

Deviation: computed from `Ratpoints.maxBitsInPrime` as the macro computes it from
`RATPOINTS_MAX_BITS_IN_PRIME`, with `64` for `LONG_LENGTH`. -/
def hornerSteps : Nat := 64 / maxBitsInPrime - 1

/-- How many primes the sieve takes when the option `-p` does not say,
`RATPOINTS_DEFAULT_NUM_PRIMES`; like the value of `-p`, it is capped at `Ratpoints.numPrimes`.

C: `ratpoints.h:333-340` -/
def defaultNumPrimes : Nat := 30

/-- The depth of the Sturm step when the options do not say, `RATPOINTS_DEFAULT_STURM`: the default
of `Ratpoints.Options.sturm` and the depth that the option `-S` of the program sets without an
argument; `-s` sets `-1`, and `-S` with an argument the depth that it gives. The bisection of the
Sturm step (`Ratpoints.Sturm.iterate`) splits the intervals that it cannot decide up to this depth,
which the search caps at `55` (`Ratpoints.Options.normalize`).

C: `ratpoints.h:341-343` -/
def defaultSturm : Int := 10

/-- At most how many forbidden divisors of the denominators are tested when the option `-F` does
not say, `RATPOINTS_DEFAULT_MAX_FORBIDDEN`.

C: `ratpoints.h:345-352` -/
def defaultMaxForbidden : Nat := 64

/-- The number of 64-bit words of a bit array of the sieve, `RBA_PACK`: 4 in the default build,
whose bit arrays have 256 bits, and 8, 2 and 1 in the builds with 512-bit, 128-bit and 64-bit bit
arrays. The proofs use only that it is positive (`Ratpoints.rbaPack_pos`) and that
`64 rbaPack = 2 ^ Ratpoints.rbaShift` (`Ratpoints.rbaLength_eq_two_pow_rbaShift`), which the
packing of the numerators needs (`Ratpoints.Sieve.classOffsets`, `Ratpoints.Sieve.siftBits`).

C: `rp-private.h:55-58`, `rp-private.h:113`, `rp-private.h:127-128`, `rp-private.h:167`,
`rp-private.h:174-175`, `rp-private.h:226`, `rp-private.h:233-234`, `rp-private.h:252`,
`rp-private.h:259-260`, `rp-private.h:278`, `rp-private.h:283-284`, `rp-private.h:300`

Deviation: the value of the default build, set here, where the C code chooses the build by the
macros that the compiler is given; the vector type of a bit array becomes `rbaPack` consecutive
words of an array of `UInt64`. -/
def rbaPack : Nat := 4

/-- The number of bits of a bit array of the sieve, `RBA_LENGTH`: `Ratpoints.rbaPack` words of
`LONG_LENGTH = 64` bits.

C: `rp-private.h:49-51`, `rp-private.h:125`, `rp-private.h:172`, `rp-private.h:231`,
`rp-private.h:257`, `rp-private.h:281`

Deviation: computed from `Ratpoints.rbaPack`, where each build sets `RBA_LENGTH` by a literal, and
the build with 64-bit bit arrays by `LONG_LENGTH`, and its logarithm `RBA_SHIFT` likewise
(`Ratpoints.rbaShift`); the shifts by `RBA_SHIFT` and by `LONG_SHIFT` are divisions by `rbaLength`
and by 64, which round down also for a negative value, as the arithmetic shifts of gcc do, and the
masks by `RBA_LENGTH - 1` and by `LONG_MASK` Euclidean remainders. -/
def rbaLength : Nat := 64 * rbaPack

/-- The logarithm of the number of bits of a bit array of the sieve, `RBA_SHIFT`: 8 in the default
build, whose bit arrays have `2 ^ 8 = 256` bits, and 9, 7 and 6 in the builds with 512-bit, 128-bit
and 64-bit bit arrays, so that `Ratpoints.rbaLength = 2 ^ rbaShift`
(`Ratpoints.rbaLength_eq_two_pow_rbaShift`). That `Ratpoints.rbaLength` is a power of 2 makes it a
unit modulo every odd modulus, which the row offsets of the packing of the numerators need
(`Ratpoints.Sieve.classOffsets`), and keeps the word numbers of the bit arrays and the numerators
they stand for within the range of a `long`; the proofs use only that and `rbaShift < 32`
(`Ratpoints.rbaShift_lt_thirty_two`).

C: `rp-private.h:126`, `rp-private.h:173`, `rp-private.h:232`, `rp-private.h:258`,
`rp-private.h:282`

Deviation: the value of the default build, set here, where each build sets it by a literal, and the
build with 64-bit bit arrays by `LONG_SHIFT`; the model shifts by none of them: the shifts by
`RBA_SHIFT` are divisions by `Ratpoints.rbaLength`. -/
def rbaShift : Nat := 8

/-- At most how many bit arrays a piece of the numerators has when the parameters do not say,
`RATPOINTS_ARRAY_SIZE`.

C: `ratpoints.h:354-356` -/
def defaultArraySize : Nat := 256

/-- The number of bit arrays that the first stage of the sieve takes at a time, `RATPOINTS_CHUNK`:
the number of registers of the chunked first stage (`Ratpoints.Sieve.andRowsChunked`), which the C
code compiles for a chunk from 2 to 16 and which the model takes on the same condition
(`Ratpoints.Sieve.siftPiece`), and otherwise the first stage one row at a time
(`Ratpoints.Sieve.andRows`); every row of the sieve has `chunk - 1` bit arrays more than its
modulus, copies of its first ones, which the chunked first stage reads past the end of the row; and
the largest number of bit arrays of a piece of the numerators is a multiple of the chunk
(`Ratpoints.Params.arraySizeAt`, `Ratpoints.maxArraySize`), so that of the pieces of an interval
only the last one can end in a partial chunk, which the tail legs take. The proofs use only that it
is positive (`Ratpoints.chunk_pos`).

C: `rp-private.h:160-165`, `rp-private.h:222-224`, `rp-private.h:248-250`,
`rp-private.h:274-276`, `rp-private.h:293-295`

Deviation: 16, the value of the default build (`USE_AVX`), set here, where the C code chooses the
value by the macros that the compiler is given, each build with vector registers taking 16 and the
build with 64-bit bit arrays 1 unless `RATPOINTS_CHUNK` is given. -/
def chunk : Nat := 16

/-- The largest number of bit arrays of a piece of the numerators, `RP_ARRAY_SIZE_MAX`: the largest
multiple of `Ratpoints.chunk` up to `2 ^ 20`.

C: `find_points.c:124` -/
def maxArraySize : Nat := 2 ^ 20 / chunk * chunk

/-- The bound on the number of squarefree divisors of the leading coefficient that the loop over
the denominators takes for a polynomial of odd degree, `MAX_DIVISORS`: `setup_us1` gives the
divisors only when it finds fewer than this many at most the largest denominator
(`Ratpoints.Setup.setupUs1`), and otherwise the loop visits every denominator
(`Ratpoints.Sieve.runSetup`).

C: `find_points.c:121` -/
def maxDivisors : Nat := 512

/-- The valuation that `valuation` and `valuation1` of the C code give for `0`, `VERY_BIG`
(`Ratpoints.Setup.valuation`). For a zero coefficient it enters the slopes of the valuation test of
the divisors of the leading coefficient (`Ratpoints.Setup.slope`), where any value can only make a
slope larger.

C: `find_points.c:422` -/
def veryBig : Nat := 1000

/-- At most how many odd prime factors the leading coefficient may have for the Jacobi test by
tables, `RP_JACOBI_PRIMES` (`Ratpoints.Sieve.jacobiSetup`).

C: `find_points.c:669` -/
def jacobiPrimes : Nat := 16

/-- At most how many entries the tables of the non-squares of the Jacobi test by tables have in
all, `RP_JACOBI_TABLE` (`Ratpoints.Sieve.jacobiSetup`).

C: `find_points.c:670` -/
def jacobiTable : Nat := 8192

/-- The largest value that the C code reduces by a multiplication with a reciprocal,
`RP_MULMOD_LIMIT`: the third stage of the sieve reduces a denominator up to this by a multiplication
and a larger one by a division (`Ratpoints.Sieve.checkOf`), and the set-up of the Jacobi test by
tables gives tables only when the denominators stay at most this (`Ratpoints.Sieve.jacobiSetup`).

C: `rp-private.h:421` -/
def mulModLimit : Nat := 2 ^ 32 - 1

/-- The bound that the third stage of the sieve (`Ratpoints.Sieve.checkOf`) compares `2 p H` with,
for a prime `p` of the stage and the height bound `H`, `RP_STAGE3_LIMIT`: below it, the third stage
shifts the product of a numerator and the inverse of the denominator modulo `p` by the multiple
`p H` of `p`, which makes it a natural number below the bound, and reduces that by a multiplication
with the reciprocal of `p` (`Ratpoints.Sieve.mulMod`), exact below `2 ^ 64 / p`; at or above it, the
stage divides. The proofs use only that it is at most `2 ^ 32`
(`Ratpoints.stage3Limit_le_two_pow_32`).

C: `rp-private.h:472`

Deviation: a natural number for the `double` `4294967296.0`, which the C code compares with the
`double` product `2 p H`. -/
def stage3Limit : Nat := 2 ^ 32

/-- Whether the second stage of the sieve runs one 64-bit word at a time, `USE_LONG_IN_PHASE_2`:
`false` in the default build, whose second stage and-s the rows of its moduli into a whole bit array
at a time; the build `long2` of `make test4configs` sets it. The model has both arms, on a bit array
(`Ratpoints.Sieve.secondStage`) and on one of its words (`Ratpoints.Sieve.secondStageWord`), which
leave the same bits, and the scan takes the arm that this constant chooses
(`Ratpoints.Sieve.scanPiece`, `Ratpoints.Sieve.siftBitArray`).

C: `sift.c:1084`, `sift.c:1086`, `sift.c:1113`, `sift.c:1174`, `sift.c:1297`

Deviation: a constant of the model, set here, for the macro that the compiler is given or not
(`-DUSE_LONG_IN_PHASE_2`), which the C code tests with `#ifdef` and `#ifndef`. -/
def useLongInPhase2 : Bool := false

/-- The end of the first stage of the sieve when the option `-n` does not say,
`RATPOINTS_DEFAULT_SP1`: the fixed choice of the versions 2.x, which the header of ratpoints keeps
(`Ratpoints.sieveParams`).

C: `ratpoints.h:42`

Deviation: the parameters of the program take it for an absent `-n`, where ratpoints, which reads
the macro nowhere, chooses the end of the first stage from the curve by its costs (`sieving_info`,
with the target `Ratpoints.survivorsPerWord`; stage I). -/
def defaultSp1 : Nat := 11

/-- How many moduli the second stage of the sieve adds to the first when neither the option `-N` nor
`-R` says, `RATPOINTS_SP2_EXTRA`, the compiled-in default of `-R`: the offset that ratpoints takes
as it is under `-U 0` and otherwise scales by the length of the run (`Ratpoints.phase2Offset`), and
that the parameters of the executable take as it is (`Ratpoints.sieveParams`); also the number of
the next candidates whose mean density stands for the second stage of a long run
(`Ratpoints.downstreamFactor`).

C: `ratpoints.h:95-97` -/
def sp2Extra : Nat := 11

/-- The survivors per 64-bit word swept that one more modulus of the first stage has to remove, for
a modulus that costs one and per word, `RATPOINTS_SURVIVORS_PER_WORD`: the target of the rule that
ends the first stage (`Ratpoints.phase1Wants`), unless the option `-r` gives a positive value.

C: `ratpoints.h:92-94` -/
def survivorsPerWord : Float := 0.002

/-- The run length, in numerator words, at which setting a modulus of the second stage up costs as
much as sieving with it, `RATPOINTS_SP2_U0`: the scale of the offset of the second stage
(`Ratpoints.phase2Offset`), unless the option `-U` gives a value `≥ 0`.

C: `ratpoints.h:120-122` -/
def sp2U0 : Float := 1.6e6

/-- What one prime of the third stage costs per survivor, as a fraction of one exact check,
`RATPOINTS_SP3_PER_SURVIVOR`, in the rule that chooses the third stage (`Ratpoints.thirdOf`, and
`adapt_primes`; stage I).

C: `ratpoints.h:150-152` -/
def sp3PerSurvivor : Float := 0.055

/-- What one prime of the third stage costs per denominator, as a fraction of one exact check,
`RATPOINTS_SP3_PER_DENOM`, in the rule that chooses the third stage (`Ratpoints.thirdOf`, and
`adapt_primes`; stage I), unless the option `-Q` gives a value `≥ 0`.

C: `ratpoints.h:153-155` -/
def sp3PerDenom : Float := 0.013

/-- The share of the survivors of the first two stages that the test for common factors leaves,
`RATPOINTS_SP3_COPRIME`, in the estimate of the survivors that reach the third stage
(`Ratpoints.survivorsAtThird`).

C: `ratpoints.h:164-166` -/
def sp3Coprime : Float := 0.7

/-- What building one row of a sieve table costs, in units of one and of the first stage per word,
`RATPOINTS_COST_TABLE`, unless the option `-C` gives a value `≥ 0` (`Ratpoints.primeCost`,
`Ratpoints.addModuli`).

C: `ratpoints.h:192-194` -/
def costTable : Float := 38.0

/-- The largest composite modulus that ratpoints offers, `RATPOINTS_COMPOSITE_MAX`: the odd
composites from 9 up to it and below `Ratpoints.maxPrimeEven` (`Ratpoints.addModuli`).

C: `ratpoints.h:210-212` -/
def compositeMax : Nat := 64

/-- What one entry of `bp_list` costs per denominator, `RATPOINTS_COST_BP` (`Ratpoints.primeCost`).

C: `ratpoints.h:213-218` -/
def costBp : Float := 8.0

/-- What the sieve spec of a modulus of the first two stages costs per denominator,
`RATPOINTS_COST_SETUP` (`Ratpoints.primeCost`).

C: `ratpoints.h:224-226` -/
def costSetup : Float := 30.0

/-- What one call of the sieve costs a modulus of the first stage, `RATPOINTS_COST_CALL`
(`Ratpoints.choiceEstimate`).

C: `ratpoints.h:241-243` -/
def costCall : Float := 50.0

/-- What fetching one line of 64 bytes of a row costs per denominator, `RATPOINTS_COST_LINE`
(`Ratpoints.phase1Key`).

C: `ratpoints.h:258-260` -/
def costLine : Float := 4.5

/-- What one and on a surviving bit array of the second stage costs, `RATPOINTS_COST_PHASE2`
(`Ratpoints.downstreamFactor`, and the keys of the second stage; stage I).

C: `ratpoints.h:261-263` -/
def costPhase2 : Float := 110.0

/-- What one survivor of the second stage costs to extract and test, `RATPOINTS_COST_SURVIVOR`
(`Ratpoints.downstreamFactor`, and `adapt_primes`; stage I).

C: `ratpoints.h:270-272` -/
def costSurvivor : Float := 1400.0

/-- What one exact check costs relative to the cost of an and, `RATPOINTS_COST_CHECK`, read by the
correction of the second stage during the run (`adapt_primes`; stage I).

C: `ratpoints.h:280-282` -/
def costCheck : Float := 1600.0

/-- The cost of one step of Horner's rule in the exact check, `RATPOINTS_CHECK_STEP`
(`Ratpoints.checkCost`).

C: `ratpoints.h:312-314` -/
def checkStep : Float := 29.0

/-- The cost of one step of Horner's rule per limb it carries, `RATPOINTS_CHECK_LIMB`
(`Ratpoints.checkCost`).

C: `ratpoints.h:315-317` -/
def checkLimb : Float := 8.0

/-- The cost of the call of the exact check and of a square root of one limb,
`RATPOINTS_CHECK_CALL` (`Ratpoints.checkCost`).

C: `ratpoints.h:318-320` -/
def checkCall : Float := 94.0

/-- The cost of each further limb of the square root of the exact check, `RATPOINTS_CHECK_ROOT`
(`Ratpoints.checkCost`).

C: `ratpoints.h:321-323` -/
def checkRoot : Float := 170.0

/-- The cost of one exact check on the curves on which the third stage was tuned,
`RATPOINTS_CHECK_REFERENCE`, which the cost of the check of the curve is divided by
(`Ratpoints.checkRelOf`).

C: `ratpoints.h:329-331` -/
def checkReference : Float := 306.0

/-- A bound on the number of composite moduli offered, `RP_MAX_MODULI`: half of
`Ratpoints.maxPrimeEven`; the pool of the candidates holds at most `Ratpoints.numPrimes` primes and
this many composites (`Ratpoints.phase2Offset`, `Ratpoints.addModuli`).

C: `find_points.c:153` -/
def maxModuli : Nat := maxPrimeEven / 2

/-- The largest number of prime-power factors of a modulus, `RP_MAX_FACTORS`
(`Ratpoints.takeFactor`).

C: `rp-private.h:520` -/
def maxFactors : Nat := 3

/-- The largest cost of the table of a composite modulus per numerator word at which it is offered,
`RP_MODULUS_TABLE_MAX` (`Ratpoints.offerModulus`).

C: `find_points.c:2337` -/
def modulusTableMax : Float := 2.0

/-- The number of the samples of the denominators by which the run is estimated,
`RUN_SHAPE_SAMPLES` (`Ratpoints.runShape`).

C: `find_points.c:1917` -/
def runShapeSamples : Nat := 64

/-- The share of the numerators of a class of the stride `2 ^ k` that its bit arrays hold, `2 ^ -k`,
the table `rp_inv_stride` of the strides `k < Ratpoints.numStrides` (`Ratpoints.runShape`,
`Ratpoints.bpwAdd`).

C: `find_points.c:1921-1922`

Deviation: an array of the seven doubles of the table, which `rp_inv_stride` sizes by
`RP_NUM_STRIDES`, read by `getD` with `0.0`, the value of the entries beyond the seven initializers
when `RP_NUM_STRIDES` is larger; the stride of a class is at most `2 ^ 6`. -/
def invStride : Array Float := #[1.0, 0.5, 0.25, 0.125, 0.0625, 0.03125, 0.015625]

/-- How many numerator words the run sweeps before the first correction of the moduli,
`RP_ADAPT_WORDS`: the field `adapt_at` of the arguments, when the search may correct its choice
(`Ratpoints.adaptStart`).

C: `find_points.c:1354` -/
def adaptWords : Nat := 1000000

/-- How many bit arrays that survive the first stage the run must have counted before it corrects
the moduli, `RP_ADAPT_ARRAYS` (`adapt_primes`; stage I).

C: `find_points.c:1355` -/
def adaptArrays : Nat := 1000

/-- How many numerators that survive the second stage the run must have counted before it corrects
the moduli, `RP_ADAPT_BITS` (`adapt_primes`; stage I).

C: `find_points.c:1356` -/
def adaptBits : Nat := 200

/-- How many blocks after the block at whose fold a correction of the moduli is decided the
correction takes effect, less one, `RP_ADAPT_LAG`: a decision made at the fold of block `j` is for
the blocks from `j + adaptLag + 1` on (`run_fold`; stage I), so that the decision of a block
depends only on the folds of the blocks at least `adaptLag + 1` before it, whatever the number of
threads.

C: `find_points.c:1379-1381` -/
def adaptLag : Nat := 32

/-- About how many blocks the steps of a run are cut into, `RP_BLOCKS_WANTED`
(`Ratpoints.Sieve.blockLength`).

C: `find_points.c:3729-3731` -/
def blocksWanted : Nat := 1024

/-- The least number of steps of a block, `RP_BLOCK_MIN` (`Ratpoints.Sieve.blockLength`).

C: `find_points.c:3732-3734` -/
def blockMin : Nat := 16

/-- The fixed length of the blocks that a build of ratpoints may set, `RP_BLOCK_LEN`, to test the
boundaries of the blocks: none, as in the default build, which does not define the macro, and
`some n` for a build with `-DRP_BLOCK_LEN=n` (`Ratpoints.Sieve.blockLength`). It models no line of
the C code: the macro is defined only on the command line of the compiler, and the conditional
compilation that reads it is part of `Ratpoints.Sieve.blockLength`. -/
def blockLen : Option Nat := none

/-- The lower bound of the multiple of a modulus `p` that the offset of a row of the sieve carries,
`RP_ROW_BIAS`: in the packing of the numerators the offset of the row of `p` carries the least
multiple of `p` that is at least `rowBias` (`Ratpoints.Sieve.SieveEntry.bias`,
`Ratpoints.Sieve.classOffsets`), so that the sum of a word number `w ≥ -rowBias` and an offset is
never negative; the first two stages of the sieve reduce that sum, or its negation, by a
multiplication with the reciprocal of `p` when the word numbers of a piece lie between `-rowBias`
and `rowBias - 2 Ratpoints.maxPrimeEven` (the test `small` of `Ratpoints.Sieve.siftPiece`), the
value then staying below `2 rowBias` in absolute value, which the C code checks at compile time to
be at most `RP_MULMOD_LIMIT` (`Ratpoints.two_mul_rowBias_sub_one_le_mulModLimit`).

C: `rp-private.h:387`, `rp-private.h:426-427`

Deviation: the check at compile time that `2 RP_ROW_BIAS - 1 ≤ RP_MULMOD_LIMIT`, an array of
negative size otherwise, a theorem checked by `decide`
(`Ratpoints.two_mul_rowBias_sub_one_le_mulModLimit`). -/
def rowBias : Nat := 2 ^ 31

/-- The number of the strides with which the sieve packs the numerators of the denominators of a
class modulo 64, `RP_NUM_STRIDES`: the strides are the powers `2 ^ k` with `k < numStrides` and
`k ≤ 6`, up to the modulus `64 = 2 ^ 6` of the 2-adic information; for a larger value the stride
stays at most `2 ^ 6`, the masks of the classes having seven entries, read as `0` beyond
(`Ratpoints.Sieve.classMasks`, `Ratpoints.Sieve.numClasses`). The proofs use only that it is at
least 1 (`Ratpoints.one_le_numStrides`), for the stride `2 ^ 0`.

C: `rp-private.h:476` -/
def numStrides : Nat := 7

theorem rbaPack_pos : 0 < rbaPack := by decide
theorem defaultArraySize_pos : 0 < defaultArraySize := by decide
theorem maxArraySize_pos : 0 < maxArraySize := by decide

/-- The fixed length of the blocks, when a build sets one (`Ratpoints.blockLen`), is positive, as
the C code assumes when it divides by it (`find_points.c:3847`): so the length of the blocks of a
run is at least 1 (`Ratpoints.Sieve.blockLength`), and the loops of the shapes over the steps of a
block end. -/
theorem blockLen_pos : ∀ n ∈ blockLen, 0 < n := by decide

/-- The chunk is positive, which the C code assumes without a check: the largest number of bit
arrays of a piece of the numerators is rounded up to a multiple of it
(`Ratpoints.Params.arraySizeAt`), which is then positive. -/
theorem chunk_pos : 0 < chunk := by decide

/-- The bound `Ratpoints.mulModLimit` on the denominators of the Jacobi test by tables is below
`2 ^ 64`, so that `Ratpoints.Sieve.jacobiTest` reads them as words. -/
theorem mulModLimit_lt_size : mulModLimit < UInt64.size := by decide

/-- The values that the C code reduces by a multiplication with a reciprocal, at most
`Ratpoints.mulModLimit`, are below `2 ^ 32`, as `RP_MULMOD_LIMIT` says: so the product of such a
value and a modulus below `2 ^ 32` is below `2 ^ 64`, where the reduction is exact
(`Ratpoints.Sieve.mulMod`, `Ratpoints.Sieve.mulDiv`). -/
theorem mulModLimit_lt_two_pow_32 : mulModLimit < 2 ^ 32 := by decide

/-- The Horner steps of the table of a prime reduce their accumulator at all
(`Ratpoints.hornerSteps`), as the C code would check at compile time: `maxBitsInPrime ≤ 32`. -/
theorem one_le_hornerSteps : 1 ≤ hornerSteps := by decide

/-- The moduli have at most 10 bits (`Ratpoints.maxBitsInPrime`), as the C code assumes: the
header knows only the sizes 5 to 10 and takes 7 for any other (`rp-private.h:321-361`), and the
comment on Horner's rule in `examine_power` relies on `m < 2 ^ 10` (`find_points.c:2286-2287`). -/
theorem maxBitsInPrime_le_ten : maxBitsInPrime ≤ 10 := by decide

/-- The third stage of the sieve reduces by a multiplication only values below `2 ^ 32`
(`Ratpoints.stage3Limit`), the bound below which the reciprocal of every modulus below `2 ^ 32`
reduces exactly, as the C code assumes of `RP_STAGE3_LIMIT` without a check. -/
theorem stage3Limit_le_two_pow_32 : stage3Limit ≤ 2 ^ 32 := by decide

/-- The bit arrays have `2 ^ Ratpoints.rbaShift` bits, as `RBA_SHIFT` says of `RBA_LENGTH`
(`rp-private.h:91`). -/
theorem rbaLength_eq_two_pow_rbaShift : rbaLength = 2 ^ rbaShift := by decide

/-- The number of bits of a bit array is below `2 ^ 32`, so that its product with a modulus below
`2 ^ 32` is below `2 ^ 64` and its remainder by the multiplication with the reciprocal exact, as the
C code assumes at `find_points.c:1816`. -/
theorem rbaShift_lt_thirty_two : rbaShift < 32 := by decide

/-- The check at compile time of `rp-private.h:426-427`: the values that the first two stages of the
sieve reduce by a multiplication, a word number plus an offset or its negation, at most
`2 Ratpoints.rowBias - 1` in absolute value, are at most `Ratpoints.mulModLimit`. -/
theorem two_mul_rowBias_sub_one_le_mulModLimit : 2 * rowBias - 1 ≤ mulModLimit := by decide

/-- There is at least the stride `2 ^ 0`. -/
theorem one_le_numStrides : 1 ≤ numStrides := by decide

/-- The degree is below `2 ^ 57`, so that the exponents `denexp (deg + 1)` of Horner's rule in
`eval_sign` (`sturm.c:67-84`) stay within a `long` at the depths up to `55` of the Sturm step, as
the C code assumes of `RATPOINTS_MAX_DEGREE` without a check. -/
theorem maxDegree_lt_two_pow_57 : maxDegree < 2 ^ 57 := by decide

/-- There is room for one search interval of the command line, which `read_input` of `main.c`
fills without a check when `-u` comes before any `-l` (`main.c:417-436`). -/
theorem zero_lt_maxDegree : 0 < maxDegree := by decide

/-! ### Examples -/

#guard primeTable.size == 171 && numPrimes == 53 && primeTable[numPrimes - 1]! == 251

#guard maxPrimeEven == 256 && hornerSteps == 7 &&
  (primeTable.toList.take numPrimes).all (· < maxPrimeEven) && maxPrimeEven ≤ primeTable[numPrimes]!

#guard rbaLength == 256 && rbaShift == 8 && chunk == 16 && defaultArraySize == 256 &&
  maxArraySize == 1048576 && modWords == 4

#guard maxDivisors == 512 && veryBig == 1000 && jacobiPrimes == 16 && jacobiTable == 8192 &&
  mulModLimit == 4294967295

#guard stage3Limit == 4294967296 && !useLongInPhase2 && defaultSp1 == 11 && sp2Extra == 11 &&
  rowBias == 2147483648 && numStrides == 7

-- The numbers of primes that the header lists for the builds with moduli of 5 to 10 bits.
#guard [5, 6, 7, 8, 9, 10].map (fun b ↦ (primeTable.toList.filter (· < 2 ^ b)).length) ==
  [10, 17, 30, 53, 96, 171]

-- The doubles of the cost model, bit for bit as gcc compiles the literals of the C code (the
-- values of the tuning macros of `ratpoints.h` and the table `rp_inv_stride`).
#guard [survivorsPerWord, sp2U0, sp3PerSurvivor, sp3PerDenom, sp3Coprime, costTable, costBp,
    costSetup, costCall, costLine, costPhase2, costSurvivor, costCheck, checkStep, checkLimb,
    checkCall, checkRoot, checkReference, modulusTableMax].map Float.toBits ==
  [0x3F60624DD2F1A9FC, 0x41386A0000000000, 0x3FAC28F5C28F5C29, 0x3F8A9FBE76C8B439,
    0x3FE6666666666666, 0x4043000000000000, 0x4020000000000000, 0x403E000000000000,
    0x4049000000000000, 0x4012000000000000, 0x405B800000000000, 0x4095E00000000000,
    0x4099000000000000, 0x403D000000000000, 0x4020000000000000, 0x4057800000000000,
    0x4065400000000000, 0x4073200000000000, 0x4000000000000000]
#guard invStride.map Float.toBits == [0, 1, 2, 3, 4, 5, 6].toArray.map fun k ↦
  ((1023 - k) <<< 52 : Nat).toUInt64
#guard compositeMax == 64 && maxModuli == 128 && maxFactors == 3 && runShapeSamples == 64 &&
  adaptWords == 1000000 && adaptArrays == 1000 && adaptBits == 200 && adaptLag == 32 &&
  blocksWanted == 1024 && blockMin == 16 && blockLen == none

end Ratpoints

end
