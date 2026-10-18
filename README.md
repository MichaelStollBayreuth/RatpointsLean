# RatpointsLean

A Lean 4 model of [ratpoints](https://github.com/MichaelStollBayreuth/ratpoints), the C program that
finds the rational points of bounded height on the curves `y² = F(x, z)`, where `F` is a binary form
of even degree with integer coefficients, by sieving; with proofs that the model meets a short
specification for every well-formed choice of the sieving parameters, and a record, checked in CI,
of which Lean definition models which lines of C.

The C code is that of ratpoints 3.1.1; the project moves to each new release of ratpoints, and a
new optimization of the C code comes, as far as possible, with its soundness proof here.

**Status.** Stage A is done: the repository, the libraries, CI, the blueprint skeleton, the
correspondence record and its checks, the comparator harness, and the blueprint chapter that settles
the specification. Stage B is done: the specification is in Lean, the brute-force reference lists
exactly its points, each once (certified by Comparator), and the command-line program
`ratpoints-lean` prints them; differential tests in CI compare it with the C program. Stage C1 is
done: the plain sieve returns, for every well-formed choice of the sieving parameters, the list of
the brute-force reference (the membership, no-duplicates and refusal theorems certified by
Comparator), and `ratpoints-lean` runs it. Stage C2 is done: it put the sieve on the bit arrays of
64-bit words of the C code, as its build `chunk1` has them (256-bit bit arrays, one at a time in the
first stage; since F4 the model is the default build), with the same theorems, and the differential
tests search up to height 30000 (up to 100000 in a suite run locally). Stage D is done: the set-up
of the search as the C code does it
before the sieve, with the options of the library that change the refusals and the order of the
output: the refusal of a binary form that is not squarefree (when the leading zeros lower its even
degree, in the reversal check, and by the remainder chain of the Sturm step, computed row by row as
the C code computes it), the reversal of the polynomial in its three cases with the map of the
points, the coefficients as C `long`s, and the exit when the curve has no points modulo a prime. The
output of `findPoints` is a permutation of the brute-force reference, so that the main theorems hold
for every option, and two refusal theorems, with the Sturm step on and off, say exactly which inputs
it refuses; the challenge of Comparator states them. `ratpoints-lean` reads `-k -K -s -S`, and the
differential tests compare the refusals and these options. Stage E is done: the side of the
denominators as the C code has it: the 2-adic information with the classes of the denominators
modulo 64 (the first stage of the sieve starts from the word of the class, and the search ends when
no class admits a numerator); for odd degree the squares and the divisors of the leading coefficient
times squares, with the valuation test of their slopes; for even degree the forbidden divisors,
tested with words of 64 denominators and by their valuations, and the Jacobi test, by the binary
algorithm and by tables, both proved to compute the Jacobi symbol of Mathlib; and the loop over the
denominators in the four shapes of the C code, in its order. The output of `findPoints` is the list
of the points at infinity followed by the points of the brute-force reference of the polynomial
searched over the denominators in the order of the loop of its search, mapped back after a reversal,
so that `ratpoints-lean` prints the points in the order of ratpoints; the main theorems, the refusal
theorems and the challenge of Comparator keep their statements. Stage F, the side of the numerators,
runs in four sub-stages, F1 to F4, all of them done. F1 models the tables and the moduli as the
C code has them. The table of a prime is computed as `examine_prime` computes it, by Horner's rule
with the Barrett reduction on its fixed schedule, and hands back the coefficients modulo the prime
and its entry at infinity to the forbidden divisors, prime by prime in the loop of the tables of
`sieving_info`, which ends the search at a prime modulo which the curve has no points; the moduli
may be prime powers, with the tables of `examine_power` and the inverses by the extended Euclidean
algorithm, and products of prime powers, whose rows are those of their factors, combined, so that
the rows of every modulus let every point through without the Chinese remainder theorem; the range
obligations of the C `long`s of these computations are lemmas. The parameters gain the number of
primes examined, and their well-formedness, which the challenge of Comparator imports from the
model, now admits the moduli below `2^maxBitsInPrime` that factor over the first `numPrimes` primes
of the table, composite ones included, and no longer the primes of the table from `2^maxBitsInPrime`
on; the main theorems, the refusal theorems and the challenge keep their text, and change only
through the parameters they quantify over. F2 models the stages of the sieve and the check as the C
code has them: the first stage with the first moduli of the parameters, the second on each bit array
that the first leaves nonzero, in both arms of the build (the whole bit array, or one word at a
time), and for each numerator that survives, the test for common factors by the binary algorithm of
the C code on its 64-bit `long`s, then the third stage, which tests the numerator against the tables
of the primes from the second cut point on, before the exact check; the third stage and the Jacobi
test reduce a value `u` by a modulus `p` with a multiplication by the reciprocal of `p`, a field of
the sieve entries and of the tables of the Jacobi test, as `RP_MULMOD` and `RP_MULDIV` do, where
that is exact (`u p < 2^64`), and divide otherwise, as the C code does; the table of the third stage
and the products of the check are made once per denominator, when its first numerator needs them.
The stages give the numerators of the sieve with all the moduli in the first stage, in the same
order, so that the main theorems keep their statements. `findPoints` refuses a height bound of
`2^63` or more, which is not a C `long`, with error 4, as the program does when it reads one, so
that the refusal theorems refuse `H = 0` or `H ≥ 2^63`, and the parameters of the command line take
the cut points of the stages by the counting rules of ratpoints where these do not depend on the
curve: a run without options uses all three stages, 11, 11 and 8 of the first 30 primes. The
differential tests compare every point list in its order: 3315 comparisons in the default suites,
among them option sets that run the second and the third stage after few moduli in the first, and 13
in the suite run locally. F3 models the packing of the numerators as the C code has it: the
numerators of a class of the denominators modulo 64 that the 2-adic information admits lie in one
residue class `a0` modulo a stride `2^k`, and the sieve of a denominator holds only those, bit `t`
standing for the numerator `a0 + 2^k t`, from the pattern of the class packed to its stride; the
rows of offsets that the packings share, the fields of the sieve entries that serve them, the
residues of a denominator divided by its stride, in the three branches of `fill_bp_list`, the bits
of the heights on 64-bit signed words in both forms of `numerators_to_bits`, and the row indices of
the first two stages with the offsets, reduced by a multiplication with the reciprocal of the
modulus where the word numbers of the piece allow it (the test `small`) and by a division otherwise,
are those of the C code, with the range obligations of its `long`s as lemmas; the reductions by a
reciprocal compute on 64-bit words, the high half of the 128-bit product from the 32-bit halves. A
row is unchanged when the residue and the numerator are multiplied by the same unit, so the packed
sieve keeps exactly the numerators that the unpacked one keeps, in the same order: the output, the
main theorems, the refusal theorems, the challenge of Comparator, the parameters and their
well-formedness do not change. F4 models the first stage as the default build of the C code compiles
it, with the chunk `RATPOINTS_CHUNK` = 16 as a constant: the chunked arm, which takes 16 bit arrays
at a time in registers, and-s the rows of the moduli into them from starts that it steps through
each row, and does the tail of a piece in legs of 8, 4, 2 and 1 bit arrays, and the arm one row at a
time for the other chunks, chosen as the conditional compilation of the C code chooses them; and the
rows as ratpoints builds and keeps them: every row of a modulus `m` has `m + 15` bit arrays, the
last ones copies of the first, which the chunked arm reads; the row of 0 of a prime is the pattern
`sieves0` that the build generates, the other rows of a prime come from the functions that the
build generates from `CODE_INIT_SIEVE1` and `CODE_INIT_SIEVE2`, those of a prime power from
`lay_out_pattern` and those of a product from the rows of its factors; the rows are kept in the
tables of rows of the entries of the C code, the missing rows of a denominator are built before it,
and the tables of rows are handed on through the run; the tables of a prime power are bit arrays of
words, as `examine_power` fills them, and the forbidden divisors among the first `numPrimes` primes
of the table read their words from `sieves0`. The rows that the builders build are the closed forms
of the admission tests, proved for every value of the chunk, so the output, the main theorems, the
refusal theorems, the challenge of Comparator, the parameters and their well-formedness do not
change. Stage G is done: the delivery of the points as the C code has it. The search hands each
point to a callback of the caller with the caller's data, adds up the values that the calls return
and stops when a call asks it to: the callback and the delivery are threaded through the components
that the C code passes `process` and `info` through, and the stop is tested where the C code tests
`quit`, so that `ratpoints-lean '1 0 1' 1000000000000 -q -1` returns at once after the point at
infinity, as ratpoints does. `findPointsWith` is the search with a callback, and `findPoints` its
instance with a callback that appends each point to an array and never stops the search. The options
of the output of the library, `RATPOINTS_NO_CHECK` and `RATPOINTS_NO_Y`, are fields of the options,
and the bits of the flags that the program reads after the search are written back. A new file of
the specification states the order in which ratpoints finds the points: the points at infinity of
the polynomial searched first, then its denominators in the order of the loop of the search,
ascending but for the divisors of the leading coefficient in the order of binary counting over its
primes, the numerators ascending and the point with `y > 0` before that with `y < 0`, mapped back
after a reversal; a theorem says that `findPoints` returns that list. The challenge of Comparator
restates that file and has twelve statements: membership now holds with `RATPOINTS_NO_CHECK` clear
and gives `y ≥ 0` under `RATPOINTS_NO_Y`; no duplicates, the refusal theorems and the
well-formedness of the parameters of the program keep their text; and the order theorem, three
statements on the output under `RATPOINTS_NO_CHECK` and the protocol of the delivery, by which the
search with any callback gives the data and the count of the delivery of the list of `findPoints`,
up to the first stop, are new. `ratpoints-lean` runs the search with the callback of the `main.c` of
ratpoints, with its options of the output, formats, strings and report, and a theorem says what it
prints; the differential tests compare the reports exactly: 3784 comparisons in the default suites
and 13 in the suite run locally. The blueprint and the API documentation will be at
<https://michaelstollbayreuth.github.io/RatpointsLean/> once the repository is public.

## Layout

| part | contents | depends on |
|---|---|---|
| `Ratpoints/Model` | the executable model as plain code, one definition per component of the C code; no Mathlib, no contracts, no experimental options | Lean core, `Std` |
| `Ratpoints/Spec` | the specification: the binary form, the normalized points of height at most `H`, their order in the output of ratpoints, the value of a double of the C code from its bits, the search intervals that ratpoints accepts and the points in the search region | Mathlib |
| `Ratpoints/Proof` | the contract of each component as a theorem, the main theorems, and the lemmas that Lean core lacks, on vectors, arrays, lists, ranges, natural numbers, integers, characters and strings (`Ratpoints/Proof/Containers.lean`) and on words (`Ratpoints/Proof/Bits.lean`) | Mathlib, the specification, the model, the candidates for Mathlib |
| `Ratpoints/Mathlib` | statements of general interest, as candidates for Mathlib | Mathlib |
| `comparator/` | the specification restated, and the main theorems with `sorry`, for [Comparator](https://github.com/leanprover/comparator); their proofs by the library | Mathlib, the model (the challenge); the library (the solution) |
| `correspondence/` | the pin of the C code and the record of its correspondence with the model | — |
| `blueprint/` | the blueprint: specification, components with their contracts, links to the C code | — |

The model is a separate library, `RatpointsModel`, so that the executable and the differential
tests depend on it alone.

## Building and checking

```bash
lake exe cache get
lake build                                   # the model, the library and ratpoints-lean
lake exe ratpoints-lean '-2 0 0 1' 130       # the points of height at most 130 on y² = x³ - 2
python3 scripts/check_layout.py              # imports, the restrictions on the model, axioms
python3 scripts/correspondence.py check      # the correspondence with the C code at the pin
python3 scripts/difftest.py                  # ratpoints-lean against the C program
python3 scripts/difftest.py --suites test4high   # the runs of test4.sh above height 30000
```

`scripts/correspondence.py` and `scripts/difftest.py` read the C code and the test suites from a
clone of ratpoints that contains the pinned commit, given by `--repo PATH` or the environment
variable `RATPOINTS_REPO`; `scripts/difftest.py` also runs the C program built there (or the one
that `--c PATH` or `RATPOINTS_BIN` names). CI runs these checks and more
(`.github/workflows/build-project.yml`). `scripts/run-comparator.sh --paranoid` runs Comparator,
built into Lake as `lake comparator` (`comparator/README.md`).

## The program `ratpoints-lean`

`ratpoints-lean 'a_0 a_1 ... a_n' H [options]` has the command line of ratpoints. It reads the
coefficients (constant term first), the height bound and the options as ratpoints does, with its
checks, messages and exit statuses, and prints the points of height at most `H` on
`y² = a_n xⁿ + ⋯ + a_0` as ratpoints does, through the callback of its `main.c`: by default one line
`(x : y : z)` per point, with the options of the output `-x -X -y -Y -z -Z -1 -i -I` and the formats
and strings of `-f -fs -fm -fe`, and without `-q` the report that ratpoints prints around them, but
for the messages on the search intervals that the search gives back and on the moduli used and,
under `-v`, the report of the library; under `-x` (no exact check) it prints the pairs that pass its
sieve, which are those of ratpoints when it sieves with the same moduli and the Sturm step is off,
as it does under `-p 30 -N 30 -s` unless it chooses other moduli from the curve. It finds the points
by the sieve on bit arrays of words in its three stages, the first in chunks of 16 bit arrays with
the rows that the builders of ratpoints build, the numerators of each denominator packed by the
stride of its class, with the parameters that the options `-p -n -N -P -F -j -J` set; `-k` and `-K`
forbid and allow the reversal of the polynomial, and `-s` and `-S [depth]` switch the Sturm step off
and on, of which the model has the test for a repeated factor so far; `-l` and `-u` give the search
intervals, read as ratpoints reads them, the ends as the numbers they are and the doubles outward of
them, and `-dl` and `-du` the range of the denominators; it accepts the other options that tune the
sieve of ratpoints, checking their arguments, but ignores them (until stage I, but for `-t` for
good). It refuses a binary form that is not squarefree with error 8 as ratpoints does with the same
options, and prints the points of the search region of its command line in the order of
ratpoints.

## Licence

Apache 2.0 (`LICENSE`). The C code of ratpoints is under the GPL; its copyright notices name
Michael Stoll alone.
