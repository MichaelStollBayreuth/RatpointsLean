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
the sieve takes its moduli. Changing a constant changes the model as changing the macro changes
the C program: no proof depends on the values of the constants, and of the table the proofs use
only that its entries are primes (`Ratpoints.prime_of_mem_primeTable`, which checks them one by
one).

## Main definitions

* `Ratpoints.maxDegree`: the largest degree that ratpoints accepts.
* `Ratpoints.primeTable`: the odd primes below 1024, among which the moduli are chosen.
* `Ratpoints.maxBitsInPrime`, `Ratpoints.numPrimes`: the moduli are chosen among the primes of the
  table below `2 ^ maxBitsInPrime`, the first `numPrimes` of them.
* `Ratpoints.defaultNumPrimes`, `Ratpoints.defaultMaxForbidden`: how many primes the sieve takes
  and at most how many forbidden divisors it tests, unless the options say.
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

Deviation: computed from `Ratpoints.maxBitsInPrime`, where the header lists the values for 5 to
10 bits, the numbers that the computation gives, and takes 7 bits for any other value; the largest
such prime and the power of 2 above it, which size the tables of the C code, have no
counterpart. -/
def numPrimes : Nat := (primeTable.toList.filter (· < 2 ^ maxBitsInPrime)).length

/-- How many primes the sieve takes when the option `-p` does not say,
`RATPOINTS_DEFAULT_NUM_PRIMES`; like the value of `-p`, it is capped at `Ratpoints.numPrimes`.

C: `ratpoints.h:333-340` -/
def defaultNumPrimes : Nat := 30

/-- At most how many forbidden divisors of the denominators are tested when the option `-F` does
not say, `RATPOINTS_DEFAULT_MAX_FORBIDDEN`.

C: `ratpoints.h:345-352` -/
def defaultMaxForbidden : Nat := 64

/-! ### Examples -/

#guard primeTable.size == 171 && numPrimes == 53 && primeTable[numPrimes - 1]! == 251

-- The numbers of primes that the header lists for the builds with moduli of 5 to 10 bits.
#guard [5, 6, 7, 8, 9, 10].map (fun b ↦ (primeTable.toList.filter (· < 2 ^ b)).length) ==
  [10, 17, 30, 53, 96, 171]

end Ratpoints

end
