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
`decide`, that `Ratpoints.rbaPack`, `Ratpoints.defaultArraySize` and `Ratpoints.maxArraySize` are
positive, that `Ratpoints.mulModLimit` is below `2 ^ 64` (`Ratpoints.mulModLimit_lt_size`), that
`Ratpoints.hornerSteps` is at least 1 (`Ratpoints.one_le_hornerSteps`) and that
`Ratpoints.maxBitsInPrime` is at most 10 (`Ratpoints.maxBitsInPrime_le_ten`), and of the table the
proofs use only that its entries are the odd primes below 1022, in increasing order
(`Ratpoints.prime_of_mem_primeTable`, which checks them one by one, and
`Ratpoints.lt_of_mem_primeTable`, `Ratpoints.mem_primeTable_of_prime` and
`Ratpoints.pairwise_lt_toList_primeTable`, which `decide` checks).

## Main definitions

* `Ratpoints.maxDegree`: the largest degree that ratpoints accepts.
* `Ratpoints.primeTable`: the odd primes below 1024, among which the moduli are chosen.
* `Ratpoints.maxBitsInPrime`, `Ratpoints.numPrimes`, `Ratpoints.maxPrimeEven`: the moduli are
  chosen among the primes of the table below `maxPrimeEven = 2 ^ maxBitsInPrime`, the first
  `numPrimes` of them, and the prime powers and products of them below `maxPrimeEven`.
* `Ratpoints.hornerSteps`: after how many steps Horner's rule reduces its accumulator in the table
  of a prime.
* `Ratpoints.defaultNumPrimes`, `Ratpoints.defaultMaxForbidden`: how many primes the sieve takes
  and at most how many forbidden divisors it tests, unless the options say.
* `Ratpoints.defaultSturm`: the depth of the Sturm step, unless the options say.
* `Ratpoints.rbaPack`, `Ratpoints.rbaLength`: how many words and how many bits a bit array of the
  sieve has.
* `Ratpoints.defaultArraySize`, `Ratpoints.maxArraySize`: at most how many bit arrays a piece of
  the numerators has, unless the parameters say, and in any case.
* `Ratpoints.maxDivisors`: the bound, never reached, on the number of squarefree divisors of the
  leading coefficient that `Ratpoints.Setup.setupUs1` gives for the loop over the denominators of a
  polynomial of odd degree.
* `Ratpoints.veryBig`: the valuation of `0` in the C code.
* `Ratpoints.jacobiPrimes`, `Ratpoints.jacobiTable`, `Ratpoints.mulModLimit`: the bounds of the
  Jacobi test by tables.
-/

@[expose] public section

namespace Ratpoints

/-- The largest degree of a polynomial that ratpoints accepts, `RATPOINTS_MAX_DEGREE`: a list of
coefficients has at most `maxDegree + 1` entries.

C: `ratpoints.h:33` -/
def maxDegree : Nat := 100

/-- The odd primes below 1024, in increasing order: the table `prime` of `primes.h`, of size
`PRIMES1000`, among which ratpoints chooses its moduli.

C: `primes.h:29-40` -/
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
argument; `-s` sets `-1`, and `-S` with an argument the depth that it gives. Of the depth, the model
reads only whether it is negative; the rest of the Sturm step, which reads the depth itself, is
stage H.

C: `ratpoints.h:341-343` -/
def defaultSturm : Int := 10

/-- At most how many forbidden divisors of the denominators are tested when the option `-F` does
not say, `RATPOINTS_DEFAULT_MAX_FORBIDDEN`.

C: `ratpoints.h:345-352` -/
def defaultMaxForbidden : Nat := 64

/-- The number of 64-bit words of a bit array of the sieve, `RBA_PACK`: 4 in the default build,
whose bit arrays have 256 bits, and 8, 2 and 1 in the builds with 512-bit, 128-bit and 64-bit bit
arrays. The proofs use only that it is positive (`Ratpoints.rbaPack_pos`).

C: `rp-private.h:55-58`, `rp-private.h:113`, `rp-private.h:127-128`, `rp-private.h:167`,
`rp-private.h:174-175`, `rp-private.h:226`, `rp-private.h:233-234`, `rp-private.h:252`,
`rp-private.h:259-260`, `rp-private.h:278`, `rp-private.h:283-284`, `rp-private.h:300`

Deviation: the value of the default build, set here, where the C code chooses the build by the
macros that the compiler is given; the vector type of a bit array becomes `rbaPack` consecutive
words of an array of `UInt64`. -/
def rbaPack : Nat := 4

/-- The number of bits of a bit array of the sieve, `RBA_LENGTH`: `Ratpoints.rbaPack` words of
`LONG_LENGTH = 64` bits.

C: `rp-private.h:49-51`, `rp-private.h:125-126`, `rp-private.h:172-173`, `rp-private.h:231-232`,
`rp-private.h:257-258`, `rp-private.h:281-282`

Deviation: computed from `Ratpoints.rbaPack`, where each build sets `RBA_LENGTH` and its logarithm
`RBA_SHIFT` by literals; the shifts by `RBA_SHIFT` and by `LONG_SHIFT` are divisions by
`rbaLength` and by 64, and the masks by `RBA_LENGTH - 1` and by `LONG_MASK` remainders. -/
def rbaLength : Nat := 64 * rbaPack

/-- At most how many bit arrays a piece of the numerators has when the parameters do not say,
`RATPOINTS_ARRAY_SIZE`.

C: `ratpoints.h:354-356` -/
def defaultArraySize : Nat := 256

/-- The largest number of bit arrays of a piece of the numerators, `RP_ARRAY_SIZE_MAX`.

C: `find_points.c:124`

Deviation: `2 ^ 20`, the value for a chunk of one bit array, where the C code takes the largest
multiple of the chunk `RATPOINTS_CHUNK` up to `2 ^ 20` (stage F4). -/
def maxArraySize : Nat := 2 ^ 20

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
`RP_MULMOD_LIMIT`: the set-up of the Jacobi test by tables gives tables only when the denominators
stay at most this (`Ratpoints.Sieve.jacobiSetup`).

C: `rp-private.h:421` -/
def mulModLimit : Nat := 2 ^ 32 - 1

theorem rbaPack_pos : 0 < rbaPack := by decide
theorem defaultArraySize_pos : 0 < defaultArraySize := by decide
theorem maxArraySize_pos : 0 < maxArraySize := by decide

/-- The bound `Ratpoints.mulModLimit` on the denominators of the Jacobi test by tables is below
`2 ^ 64`, so that `Ratpoints.Sieve.jacobiTest` reads them as words. -/
theorem mulModLimit_lt_size : mulModLimit < UInt64.size := by decide

/-- The Horner steps of the table of a prime reduce their accumulator at all
(`Ratpoints.hornerSteps`), as the C code would check at compile time: `maxBitsInPrime ≤ 32`. -/
theorem one_le_hornerSteps : 1 ≤ hornerSteps := by decide

/-- The moduli have at most 10 bits (`Ratpoints.maxBitsInPrime`), as the C code assumes: the
header knows only the sizes 5 to 10 and takes 7 for any other (`rp-private.h:321-361`), and the
comment on Horner's rule in `examine_power` relies on `m < 2 ^ 10` (`find_points.c:2286-2287`). -/
theorem maxBitsInPrime_le_ten : maxBitsInPrime ≤ 10 := by decide

/-! ### Examples -/

#guard primeTable.size == 171 && numPrimes == 53 && primeTable[numPrimes - 1]! == 251

#guard maxPrimeEven == 256 && hornerSteps == 7 &&
  (primeTable.toList.take numPrimes).all (· < maxPrimeEven) && maxPrimeEven ≤ primeTable[numPrimes]!

#guard rbaLength == 256 && defaultArraySize == 256 && maxArraySize == 1048576

#guard maxDivisors == 512 && veryBig == 1000 && jacobiPrimes == 16 && jacobiTable == 8192 &&
  mulModLimit == 4294967295

-- The numbers of primes that the header lists for the builds with moduli of 5 to 10 bits.
#guard [5, 6, 7, 8, 9, 10].map (fun b ↦ (primeTable.toList.filter (· < 2 ^ b)).length) ==
  [10, 17, 30, 53, 96, 171]

end Ratpoints

end
