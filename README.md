# RatpointsLean

[![Website](https://img.shields.io/badge/Website-ready-green)](https://michaelstollbayreuth.github.io/RatpointsLean/)
[![Blueprint](https://img.shields.io/badge/Blueprint-complete-green)](https://michaelstollbayreuth.github.io/RatpointsLean/blueprint/)
[![Blueprint PDF](https://img.shields.io/badge/Blueprint-PDF-blue)](https://michaelstollbayreuth.github.io/RatpointsLean/blueprint.pdf)
[![Documentation](https://img.shields.io/badge/Documentation-API-green)](https://michaelstollbayreuth.github.io/RatpointsLean/docs/)
[![License: Apache 2.0](https://img.shields.io/badge/License-Apache_2.0-lightblue.svg)](https://opensource.org/licenses/Apache-2.0)

A Lean 4 model of [`ratpoints`](https://github.com/MichaelStollBayreuth/ratpoints), the C program
that finds the rational points of bounded height on the curves `y² = F(x, z)`, where `F` is a binary
form of even degree with integer coefficients, by sieving; with proofs that the model meets a short
specification for every value of the options of the sieve, and a record, checked in CI, of which
Lean definition models which lines of C.

The C code is that of `ratpoints` 3.1.1. The project follows the releases of `ratpoints`, and future
changes to the C code come, as far as possible, with their soundness proofs here.

## What is verified

The development has four parts: the specification (`Ratpoints/Spec`), short enough to read in full;
the executable model (`Ratpoints/Model`), plain code on Lean core and `Std` without Mathlib, which
mirrors the hardware-independent structure of the C code function by function, with the same loops,
tables, bit arrays of 64-bit words and index arithmetic; the proofs (`Ratpoints/Proof`) that the
model meets the specification; and the link to the C code (`correspondence/` and the differential
tests).

The specification says what `ratpoints` computes. For a list `c` of integer coefficients and a
height bound `H`, the points are the triples `(x, y, z)` with `y² = F(x, z)`, where `F` is the
binary form of `c` of even degree, normalized as `ratpoints` prints them (`gcd(x, z) = 1`, and
`z > 0` or `(x, z) = (1, 0)`), of height at most `H` (`|x| ≤ H` and `z ≤ H`), with both signs of
`y`. The specification also gives the order in which `ratpoints` finds the points; the search region
that the caller may give, made of search intervals whose ends are doubles, read by their values, and
a range of the denominators; and Sturm's theorem, as a proposition that the theorems on the Sturm
step assume, since Mathlib does not have it (yet).

For every coefficient list, height bound, options of the search and options of the sieve, with no
hypothesis on the latter (from them and from the curve the search chooses its moduli, as `ratpoints`
does), the search `Ratpoints.findPoints`

- refuses exactly the inputs that `ratpoints` refuses: with the Sturm step on, fewer than two or
  more than `maxDegree + 1 = 101` coefficients, `H = 0` or `H ≥ 2^63` (a height that is not a C
  `long`), a binary form that is not squarefree, and search intervals that are not well formed; with
  the Sturm step off, exactly what `ratpoints` refuses under `-s`;
- returns otherwise, with the exact check on, exactly the points of height at most `H` in the
  search region, of each pair `(x, ±y, z)` only the one with `y ≥ 0` under `RATPOINTS_NO_Y`, each
  once, in the order in which `ratpoints` finds them, assuming Sturm's theorem when the Sturm step
  is on (a hypothesis, not an axiom);
- returns, with the exact check off (`RATPOINTS_NO_CHECK`), triples `(x, 0, z)` of normalized pairs
  of height at most `H` in the search region, each once, among them those of all the points in it
  (assuming Sturm's theorem when the Sturm step is on), in the order of the search with the check;
- delivers the points to the callback of the caller as `find_points` does: the search with a
  callback, `Ratpoints.findPointsWith`, gives the data and the count of the delivery of the list of
  `findPoints` to the callback (`Ratpoints.Delivery.deliver`, a fold of a few lines), up to and
  including the first call that stops the search.

The brute-force reference `Ratpoints.bruteForce` lists exactly the points, each once, and so does
the fast search `Ratpoints.FastMask.fastPoints` of `ratpoints-lean`, for every range of the
denominators. These thirteen statements are certified by Comparator: `lake comparator --paranoid`
accepted them on 2026-10-30 (`comparator/README.md`). Also proved, but not certified: what
`ratpoints-model` prints (`Ratpoints.Cli.run_eq_of_findPointsWith_eq_ok`); that the Sturm step keeps
every point, under Sturm's theorem, so that with the exact check on its depth does not change the
output (`Ratpoints.findPoints_sturm_neg_eq_ok`); and that the blocks of the loop over the
denominators, sifted apart and delivered in their order, give what the run delivers
(`Ratpoints.Sieve.run_deliverSlots_eq_fst_run_sieveRun`). The threads of `ratpoints`, which the
model leaves out, sift the blocks apart and deliver their points in the order of the blocks, so the
model, which sifts the blocks in turn on one thread, gives the output of every number of threads,
provided that the pool of threads of `ratpoints` behaves as its code says.

## What one has to trust

One has to trust the specification, which the challenge of Comparator restates verbatim,
with the definitions of Lean core and Mathlib that it is written in;
the reference of the delivery, of which the protocol speaks; the fact that the executables
`ratpoints-model` and `ratpoints-lean` run the model and the fast search, and for `ratpoints-lean`
that the C code of the two primitives on bit masks (`Ratpoints/Fast/Mask.lean`) computes their Lean
reference definitions, which `lake exe masktest` checks but no proof covers; Lean's kernel and
Comparator; and, in the statements with the Sturm step on, Sturm's theorem. The search chooses
its moduli by the cost model of `ratpoints`, in doubles, which the model computes as Lean's
`Float`, with the `log` and `pow` of the C library of the platform, as `ratpoints` does; no proof
reads the value of a double, so the theorems hold for every choice of the moduli that the search
makes.

Lean has no semantics of C, so the link between the model and the C code is not a proof. Every line
of code of the C files is recorded, with the Lean declarations that model it or the reason why the
model leaves it out, and `scripts/correspondence.py` checks the record against the C code at the
pinned commit (`correspondence/README.md`). The differential tests run `ratpoints-model` and the C
program on the same inputs and compare the outputs byte for byte, the points in their order, the
exit statuses and the reports: 5397 comparisons in the default suites, 13 in the suite of the runs
of `test4.sh` above height 30000 and 92 in the suite of the searches in which `ratpoints` corrects
its moduli, none failed. Since the choice of the moduli computes with the `log` and `pow` of the
platform, the tests run the C program on the same machine and compare exactly what depends on the
choice: the pairs under `-x`, the numbers of the moduli used (message 4) and the output under `-v`.
The model leaves out the threads, the management of memory, the calling conventions of the library
and the instrumentation for development and debugging, each excluded range with its reason in the
record; the vector code of the C builds is modelled by the operations on 64-bit words that it
implements, and the first stage of the sieve is that of the default build, with chunks of 16 bit
arrays. The compile-time constants of the C code are definitions of the model
(`Ratpoints/Model/Constants.lean`), and no proof depends on their values beyond a few facts checked
by `decide`, which its module docstring lists (`scripts/constants_check.py` checks this).

## Layout

| part | contents | depends on |
|---|---|---|
| `Ratpoints/Model` | the executable model as plain code, one definition per component of the C code; no Mathlib, no contracts, no experimental options | Lean core, `Std` |
| `Ratpoints/Fast` | the fast search of `ratpoints-lean`, not a model of the C code, and the program; plain code like the model, except for the C code of two primitives on bit masks in `Ratpoints/Fast/Mask.lean` | Lean core, `Std`, the model |
| `Ratpoints/Spec` | the specification: the binary form, the normalized points of height at most `H`, their order in the output of `ratpoints`, the value of a double of the C code from its bits, the search intervals that `ratpoints` accepts, the points in the search region and Sturm's theorem as a proposition | Mathlib |
| `Ratpoints/Proof` | the contract of each component as a theorem, the main theorems, and the lemmas that Lean core lacks, on vectors, arrays, lists, ranges, natural numbers, integers, characters and strings (`Ratpoints/Proof/Containers.lean`) and on words (`Ratpoints/Proof/Bits.lean`), and the tactic `vc_simp` that the proofs by `vcgen` share (`Ratpoints/Proof/VCSimp.lean`) | Mathlib, the specification, the model, the candidates for Mathlib |
| `Ratpoints/Mathlib` | statements of general interest, as candidates for Mathlib | Mathlib |
| `comparator/` | the specification restated, and the main theorems with `sorry`, for [Comparator](https://github.com/leanprover/comparator); their proofs by the library | Mathlib, the model and the fast search (the challenge); the library (the solution) |
| `correspondence/` | the pin of the C code and the record of its correspondence with the model | — |
| `blueprint/` | the blueprint: the specification, the main theorems with their proofs in outline, the components with their contracts, the link to the C code | — |

The model is a separate library, `RatpointsModel`, so that the executable and the differential
tests depend on it alone.

## Building and checking

```bash
lake exe cache get
lake build                                   # the model, the library and both programs
lake exe ratpoints-lean '-2 0 0 1' 130       # the points of height at most 130 on y² = x³ - 2
python3 scripts/check_layout.py              # imports, the restrictions on the model, axioms
python3 scripts/correspondence.py check --complete   # the record of the C code at the pin
python3 scripts/difftest.py --lean .lake/build/bin/ratpoints-model   # the model's program against C
python3 scripts/fasttest.py --c C --repo DIR # ratpoints-lean against the C program, as point sets
python3 scripts/difftest.py --lean .lake/build/bin/ratpoints-model --suites test4high
python3 scripts/difftest.py --lean .lake/build/bin/ratpoints-model --suites adapt
python3 scripts/constants_check.py --workdir tmp/cc   # builds with other values of the constants
```

`scripts/correspondence.py` and `scripts/difftest.py` read the C code and the test suites from a
clone of `ratpoints` that contains the pinned commit, given by `--repo PATH` or the environment
variable `RATPOINTS_REPO`; `scripts/difftest.py` also runs the C program built there (or the one
that `--c PATH` or `RATPOINTS_BIN` names), which must be the default build at the pin, without a
`tuning.mk`, which the harness refuses, on the same machine as `ratpoints-model`, since the choice
of the moduli computes with the `log` and `pow` of the C library of the platform. CI runs these
checks and more (`.github/workflows/build-project.yml`). `scripts/run-comparator.sh --paranoid` runs
Comparator, built into Lake as `lake comparator` (`comparator/README.md`).
`scripts/constants_check.py` builds copies of the committed project with eleven other sets of
values of the compile-time constants, one after the other, each without the `#guard` examples of
the model, and reports whether the library still builds; it uses the built packages of the
repository and runs on demand, not in CI.

The blueprint and the API documentation are at <https://michaelstollbayreuth.github.io/RatpointsLean/>.

## The programs `ratpoints-lean` and `ratpoints-model`

`ratpoints-lean 'a_0 a_1 ... a_n' H [-dl b] [-du b] [-q]` prints the points of height at most `H` on
`y² = a_n xⁿ + ⋯ + a_0` (coefficients constant term first), one line `(x : y : z)` per point, the
points at infinity included; `-dl` and `-du` bound the denominators from below and above, and `-q`
is accepted and ignored. It runs the fast search `Ratpoints.FastMask.fastPoints`
(`Ratpoints/Fast/Search.lean`), which is not a model of the C code. The numerators are split into
their classes modulo 16, a class searched for a denominator only where the residues allow a point;
each class is sieved in chunks, bit masks with one bit per numerator, ANDed with the rows of
families of odd moduli, built once and shifted to each chunk by whole bytes; the denominators are
the outer loop, so that the rows of a denominator serve all its chunks in turn; the candidates that
survive go to the exact check of the brute force; for odd degree only the denominators `s k²` with
`s` dividing the leading coefficient are searched. The masks are byte arrays, and the two operations
on them that take the time are primitives with a few lines of C each (`Ratpoints/Fast/Mask.lean`, in
`@[extern c inline]`): the AND of a mask with a row shifted to the right, in place, 64 bits at a
time, and the next set bit of a mask. Their Lean bodies are reference definitions, which the proofs
use; `lake exe masktest` compares the C code with them on five million cases, in CI. The same sieve
with the masks in natural numbers (GMP integers), `Ratpoints.Fast.fastPoints`
(`Ratpoints/Fast/Sieve.lean`), has no C of its own and is four to fourteen times slower;
`Ratpoints.FastMask.fastPoints_perm` proves that the two list the same points, and
`Ratpoints.FastMask.mem_fastPoints_iff` and `Ratpoints.FastMask.nodup_fastPoints`
(`Ratpoints/Proof/FastMask.lean`) that the list holds exactly the points of height at most `H` with
their denominator in the range, each once, in an order of its own, for every input and every setting
of the parameters of the sieve; both are certified by Comparator. `scripts/fasttest.py` compares the
points, as sets, with those of `ratpoints` on its test suites, in CI.

Running times against `ratpoints` (C) and the program of the model (`ratpoints-model`), on one
core of an Intel Core i7-1355U (wall times, one process per curve):

| curve | H | C | `ratpoints-model` | `ratpoints-lean` |
| --- | ---: | ---: | ---: | ---: |
| generic genus 2 (`testdata.h` 776) | 10^5 | 0.18 s | 22.3 s | 0.33 s |
| point-rich genus 2 (`testdata-many.h` 90) | 10^5 | 0.55 s | 48 s | 1.5 s |
| degree 8 (`testdata-degrees.h` 100) | 10^5 | 0.02 s | 1.8 s | 0.10 s |
| the 1206 curves of the three test suites | 16383 | 4.3 s | 162 s | 20 s |

`ratpoints-model 'a_0 a_1 ... a_n' H [options]` is the program of the faithful model; it has the
command line of `ratpoints`. It reads the coefficients (constant term first), the height bound and
the options as `ratpoints` does, with its checks, messages and exit statuses, and prints the points
of height at most `H` on `y² = a_n xⁿ + ⋯ + a_0` as `ratpoints` does, through the callback of its
`main.c`: by default one line `(x : y : z)` per point, with the options of the output
`-x -X -y -Y -z -Z -1 -i -I` and the formats and strings of `-f -fs -fm -fe`, and without `-q` the
report that `ratpoints` prints around them, under `-v` with the report of the library between them;
under `-x` (no exact check) it prints the pairs that pass its sieve, with the moduli that it chooses
from the curve and corrects between the blocks of the run as `ratpoints` does, which are those that
`ratpoints` prints on the same machine. It finds the points by the sieve on bit arrays of words in
its three stages, the first in chunks of 16 bit arrays with the rows that the builders of
`ratpoints` build, the numerators of each denominator packed by the stride of its class, with the
moduli that it chooses from the curve and the options `-p -n -N -r -R -U -C -A -P -Q -W -F -j -J`;
`-k` and `-K` forbid and allow the reversal of the polynomial, `-s` and `-S [depth]` switch the
Sturm step off and on, which narrows the search intervals to those where the polynomial may be
`≥ 0`; `-l` and `-u` give the search intervals, read as `ratpoints` reads them, the ends as the
numbers they are and the doubles outward of them, and `-dl` and `-du` the range of the denominators;
it accepts `-t`, the number of threads of `ratpoints`, checking its argument, but ignores it,
sieving the blocks in turn on one thread, which gives the output of every number of threads if the
pool of `ratpoints` behaves as its code says. It refuses a binary form that is not squarefree with
error 8 as `ratpoints` does with the same options, and prints the points of the search region of its
command line in the order of `ratpoints`.

At large height bounds, `ratpoints-model` runs about 100 times slower than `ratpoints`.
This is mostly due to the bit arrays: the C code ANDs 256 bits with one vector instruction, while
the model ANDs the four 64-bit words one by one into a new array of boxed words, allocating and
freeing memory for every bit array. The purpose of the model is to get as close as reasonably
possible to certifying the correctness of the original `ratpoints` code, so that the C program
offers both efficiency and a good level of trust; the verified program for computing rational
points in Lean is `ratpoints-lean`.

## Licence

Apache 2.0 (`LICENSE`). The C code of `ratpoints` is under the GPL; its copyright notices name
Michael Stoll alone.
