/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Denominators
public import Ratpoints.Model.Params
public import Ratpoints.Model.Setup
public import Ratpoints.Model.Sieve
public import Ratpoints.Model.Sturm

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Denominators
meta import Ratpoints.Model.Params
meta import Ratpoints.Model.Setup
meta import Ratpoints.Model.Sieve
meta import Ratpoints.Model.Sturm

/-!
# The search for the points

`Ratpoints.findPoints c H P o` is the model of the library function `find_points` of ratpoints, with
the options `o` of the library that change the refusals or the order of the output
(`Ratpoints.Options`): it refuses, as the program does (`Ratpoints.Refusal`), more than
`Ratpoints.maxDegree + 1` coefficients, fewer than two and the height bound `0`, and then the binary
forms that are not squarefree as the set-up of the library finds them: when the leading zeros of the
`n + 1` coefficients lower `⌈n / 2⌉`, in the reversal check (`Ratpoints.Setup.reversal`), which may
also reverse the polynomial, and with the Sturm step on, by the remainder chain
(`Ratpoints.Sturm.chain`). Otherwise it runs the search of the polynomial that the set-up hands on
(`Ratpoints.searchPoints`), which returns no points when no class of the denominators modulo 64
admits a numerator and there is no point at infinity, or when the curve has none modulo one of the
primes examined for the parameters `P`, and otherwise the points of height at most `H` on
`y ^ 2 = F(x, z)`, the points at infinity first and then those of the denominators in the order of
the loop of the search (`Ratpoints.Sieve.Shape`), increasing unless it runs over the divisors of the
leading coefficient, found by the sieve on the bit arrays of words with the moduli, primes, prime
powers and products of them, and the array size of `P`, each mapped back to the caller's curve after
a reversal. What `sieving_info` computes for the search, the loop of the tables of the primes
examined with the exit and the forbidden divisors, the further forbidden divisors and the sieve
entries of the moduli, is `Ratpoints.sievingInfo`.

## Main definitions

* `Ratpoints.Options`: the options of a search.
* `Ratpoints.makeModulus?`, `Ratpoints.sievingInfo`: the sieve entry of a modulus, and the tables,
  the forbidden divisors and the sieve entries of the moduli of a search.
* `Ratpoints.searchPoints`: the search of the polynomial that the set-up hands on.
* `Ratpoints.findPoints`: the points.
-/

@[expose] public section

namespace Ratpoints

/-- The options of a search that change the refusals or the order of the output, with the defaults
of a run of the program without options: whether the set-up may reverse the polynomial
(`Ratpoints.Setup.reversal`), and the depth of the Sturm step, negative for none. Unlike the
sieving parameters (`Ratpoints.Params`), which change neither the points nor their order, these
change the order of the output (the reversal) and the refusals (the Sturm step, and without it the
reversal check); the options of the output and of the search region come with stages G and H.

C: `main.c:348`, `main.c:352`

Deviation: a structure for the fields of `ratpoints_args` that hold these options: a Boolean for
the bit `RATPOINTS_NO_REVERSE` of the flags, which `main.c` clears with the others, whose Jacobi
switch is that of the sieving parameters (`Ratpoints.Params.jacobi`) and whose bits of the output
are stage G's; and an integer for `args->sturm`, of which the model reads only whether it is
negative, as the switch of the test for a repeated factor (the depth itself is stage H's). -/
structure Options where
  /-- Whether the set-up may reverse the polynomial: the bit `RATPOINTS_NO_REVERSE` of the flags
  clear, which the option `-k` of the program sets and `-K` clears. -/
  reverse : Bool := true
  /-- `args->sturm`, the depth of the Sturm step, negative for none: `Ratpoints.defaultSturm`
  unless the option `-s` of the program sets `-1` or `-S` a depth. -/
  sturm : Int := defaultSturm

open Sieve in
/-- The sieve entry of the modulus `m` for the polynomial of degree `d` with the coefficient list
`c` and the flag `useCLong` of the `long`s, from its factors over the table
(`Ratpoints.modulusFactors`) and the tables `tables` of the primes examined in the loop of the
tables, by their positions (`Ratpoints.Sieve.examinePrimes`): in a loop over the factors, for a
factor `p ^ e` with `e = 1`, the table of `p` from the loop of the tables when `p` is among the
primes examined there, and otherwise the table that its examination gives now
(`Ratpoints.Sieve.examinePrime?`), with none at once when the curve has no points modulo `p`; and
for `e ≥ 2` the tables of the prime power (`Ratpoints.Sieve.examinePower`). A prime or a prime
power has one factor, a product two or more.

C: `find_points.c:2387-2395`, `find_points.c:2414-2429`, `find_points.c:2434-2475`,
`find_points.c:2546`, `find_points.c:2976-2978`, `find_points.c:2994-2998`

Deviation: the entry of every modulus made here, by its factors, where `sieving_info` takes the
entry of a prime from the loop of the tables (`prec[n].ssp`) and makes those of the prime powers and
the products by `make_modulus`; the primes and prime powers as factors of the entry, for the fields
`nf`, `pw` and `factor` and the entries of the prime powers that `make_power` makes; the tables of a
prime power (`Ratpoints.Sieve.Factor.power`) computed for each modulus that needs them, where
`add_moduli` examines a prime power once, when the first modulus offered needs it, and keeps its
tables by its index (`pw_idx`, lines 2387-2394), and `make_modulus` makes the entry of a prime power
once and keeps it by its index (`power_se`); the tables of a prime power computed also when they say
nothing, where `add_moduli` refuses a modulus with such a factor (line 2395), and a prime factor
whose prime says nothing (`examine_prime` returns `0`, and `prime_se[pn]` stays `NULL`) taken with
its table from the loop of the tables, where `add_moduli` offers no composite with such a factor
(line 2383); a prime beyond those of the loop of the tables examined, with the exit, when the entry
of a modulus needs it, where `sieving_info` examines the primes from `prime[pn_lim]` on, in the
order of the table, with the exit, for the third stage only (lines 2976-3016) and only when the
number of primes was left to the library (line 2980), also those that it then skips, and
`add_moduli` makes composites, prime powers and products alike, of the primes of the loop of the
tables only (line 2370): the output does not depend on the primes examined, since the exit is taken
only when the curve has no points; every modulus of the parameters taken, any product of powers of
primes of the table below `Ratpoints.maxPrimeEven` (`Ratpoints.Params.WF`), where `add_moduli`
offers a composite only for an odd `9 ≤ m ≤ RATPOINTS_COMPOSITE_MAX` (line 2361;
`ratpoints.h:210-211`, 64 by default), with room in the buffer of the prime powers for its new prime
powers (line 2390), a density `r < 1` (line 2402) and at most `RP_MAX_MODULI` candidates (line
2403), restrictions that the model lifts as choices of the moduli (stage I); no reciprocal `magic`,
bias `bias` and inverse `rbainv`, which serve the reduction of the sieve and the packing (stage F),
no density `r` (stage I), and no field `init`, the rows of every kind being made by one function
(`Ratpoints.Sieve.SieveEntry.row`); the entry a fresh value, for the space that `make_power` and
`make_modulus` take from the buffer of the sieve entries (`se_next`), and the exit as `none`, for
the prime that `sieving_info` returns. -/
def makeModulus? (c : List Int) (d : Nat) (useCLong : Bool) (tables : Array Entry) (m : Nat) :
    Id (Option SieveEntry) := do
  let (fac, _) ← modulusFactors m
  let mut factors : Array Factor := #[]
  for (pn, e) in fac do
    if e = 1 then
      match tables[pn]? with
      | some t => factors := factors.push (.prime t)
      | none =>
        let some (t, _) ← examinePrime? c d primeTable[pn]! useCLong | return none
        factors := factors.push (.prime t)
    else
      let pw ← examinePower c d primeTable[pn]! e useCLong
      factors := factors.push (.power pw)
  return some { p := m, factors := factors.toList }

open Sieve in
/-- What `sieving_info` computes for the search of the polynomial with the coefficient list `c` of
degree `d`, the flag `useCLong` of the `long`s, the switch `checkDenom` of the forbidden divisors,
the parameters `P` and the largest denominator `bHigh`: the loop of the tables over the first
`P.examined` primes of the table, with at most `P.maxForbidden` forbidden divisors
(`Ratpoints.Sieve.examinePrimes`), and none when the curve has no points modulo one of them; for the
switch on, the forbidden divisors among the further primes (`Ratpoints.Sieve.forbidden`); and, in a
loop over the moduli of `P` in their order, the sieve entry of each (`Ratpoints.makeModulus?`), and
none at once when the curve has no points modulo a prime examined for it. Then the sieve entries of
the moduli and the forbidden divisors tested with words and by their valuations.

C: `find_points.c:2522-2532`, `find_points.c:2892-2900`, `find_points.c:3102-3103`

Deviation: the arguments that serve the choice of the moduli (the mean number of bits per word,
whether the number of primes was left to the library, the word `den_bits` and the classes `cls`) are
not modelled, nor that choice (stage I): the moduli and their stages are those of the parameters,
and the primes examined in the loop of the tables their first `P.examined`, beyond which
`Ratpoints.makeModulus?` examines a prime when a modulus needs it; the sieve entries of every
modulus made here, those of the third stage included, which `sieving_info` puts into `sieve_list`
later, in the choice of the third stage; the flag `RATPOINTS_CHECK_DENOM` as the switch
`checkDenom`, which the search clears, with the flag, when there is no forbidden divisor and no
Jacobi test (`Ratpoints.searchPoints`); the sieve entries and the forbidden divisors returned as
lists, for the array `sieve_list` and the arrays of the arguments, and the exit as `none`, for the
prime returned; no failure for lack of memory, which the model cannot meet; no output under
`RATPOINTS_VERBOSE`, `RP_PRIME_STATS` or `DEBUG`. -/
def sievingInfo (c : List Int) (d : Nat) (useCLong checkDenom : Bool) (P : Params) (bHigh : Nat) :
    Id (Option (List SieveEntry × List ForbiddenEntry × List ForbiddenVal)) := do
  let some (tables, ba, val) ←
      examinePrimes c d useCLong checkDenom P.examined P.maxForbidden bHigh | return none
  let (forb, forbVal) ← if checkDenom then forbidden c d P.examined P.maxForbidden bHigh ba val
    else pure (ba.toList, val.toList)
  let mut entries : Array SieveEntry := #[]
  for m in P.moduli do
    let some e ← makeModulus? c d useCLong tables m | return none
    entries := entries.push e
  return some (entries.toList, forb, forbVal)

open Sieve in
/-- The search of the polynomial with the coefficient list `c` of degree `d` that the set-up hands
on, for the height `H`, the parameters `P` and the flag `rev` of the reversal, over the denominators
`bLow = 1, …, bHigh = H`. First the flags of the tests on the denominators: the checked loop for
even degree; the Jacobi test for even degree, `c_d` not a square (`Ratpoints.Setup.isSquare`) and
the switch `P.jacobi`; the squares for odd degree and `|c_d| = 1`; and for odd degree otherwise the
divisors of `c_d` (`Ratpoints.Setup.setupUs1`). Then the 2-adic information
(`Ratpoints.Sieve.twoAdic`, `Ratpoints.Sieve.denBits`), and no points when no class of the
denominators admits a numerator and there is no point at infinity, as there is for odd degree or
`c_d` a square. Then the tables of the primes examined, the forbidden divisors for even degree and
the sieve entries of the moduli of `P` (`Ratpoints.sievingInfo`), with the flag of the `long`s
(`Ratpoints.Setup.useCLong`), and no points when the curve has no points modulo one of the primes
examined; the checked loop off when there are no forbidden divisors and no Jacobi test; the shape of
the run (`Ratpoints.Sieve.runSetup`); and the points at infinity
(`Ratpoints.Sieve.pointsAtInfinity`), followed by those of the denominators of the shape
(`Ratpoints.Sieve.sieveRun`) with the sieve entries of the moduli and pieces of at most
`Ratpoints.Params.arraySizeAt P H` bit arrays, each point mapped by `Ratpoints.Sieve.swapPoint`
when `rev` is set. For well-formed parameters, `H ≥ 1` and `d` the degree of `c`, these are the
points at infinity followed by the points of the brute-force reference over the denominators of the
search (`Ratpoints.searchDens`), in the order of its loop, increasing unless the shape is that of
the divisors, each mapped when `rev` is set, also when an exit is taken
(`Ratpoints.run_searchPoints`).

C: `find_points.c:2793-2795`, `find_points.c:4573`, `find_points.c:4588-4589`,
`find_points.c:4595-4596`, `find_points.c:4603-4604`, `find_points.c:4607`,
`find_points.c:4900-4943`, `find_points.c:4948`, `find_points.c:4954-4963`,
`find_points.c:4992-5012`, `find_points.c:5106`, `find_points.c:5116`, `find_points.c:5137-5139`,
`find_points.c:5167`

Deviation: the arguments of `sieving_info` that serve the choice of the moduli (the mean number of
bits per word, whether the number of primes was left to the library, the 2-adic classes and the word
`den_bits`) are not modelled; the denominators from `1` to `H`, for the range `b_low, …, b_high`
(stage H); the flags of the denominators as Booleans, for the bits of `args->flags`; the forbidden
divisors and the divisors of the leading coefficient with their records as lists, for the arrays
`args->forb_ba`, `args->forbidden`, `args->den_info` and `args->divisors` of the arguments; the
square test `lcfsq` of line 4906 made on the polynomial searched (`Ratpoints.Setup.isSquare`), where
the C code computes it before the reversal check (line 4634) and clears it in case 2 (line 4770):
the same value for an even degree, the only one that reads it; the test on `point_at_infty` of the
2-adic exit recomputed, as `Ratpoints.Sieve.pointsAtInfinity` decides it; the exits give the empty
list, where `sieving_info` returns the prime and `find_points_work_1` the number `0` of points
found; the Sturm step does not restrict the search region before stage H, so that the return when it
leaves nothing to search is never taken, and the run always follows the points at infinity; no
failure for lack of memory, which the model cannot meet; no output under `RATPOINTS_VERBOSE` or
`DEBUG`. -/
def searchPoints (c : List Int) (d H : Nat) (P : Params) (rev : Bool) :
    Id (List (Int × Int × Int)) := do
  let bHigh := H
  let lcf := c.getD d 0
  let useCLong := Setup.useCLong c d
  let mut checkDenom := d % 2 == 0
  let useJacobi := d % 2 == 0 && !Setup.isSquare lcf && P.jacobi
  let useSquares := d % 2 == 1 && lcf.natAbs == 1
  let us1 ← if d % 2 == 1 && lcf.natAbs != 1 then Setup.setupUs1 c d bHigh else pure none
  let nb ← twoAdic c d
  let db := denBits nb
  if db == 0 && !(d % 2 == 1 || Setup.isSquare lcf) then return []
  let some (entries, forb, forbVal) ← sievingInfo c d useCLong checkDenom P bHigh | return []
  if forb.isEmpty && forbVal.isEmpty && !useJacobi then checkDenom := false
  let shape ← runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf bHigh
  let pts ← sieveRun c d H (P.arraySizeAt H) rev entries nb db shape 1 bHigh
  return pointsAtInfinity c d rev ++ pts.toList

/-- The points of height at most `H` on `y ^ 2 = F(x, z)` for the coefficient list `c`, found by the
sieve with the moduli and the array size of the parameters `P` and the options `o`, by default those
of a run of the program without options. More than `Ratpoints.maxDegree + 1` coefficients, fewer
than two and `H = 0` are refused, in the order of the program (errors 3, 5 and 4); then, as not
squarefree (error 8), a list whose leading zeros lower `⌈n / 2⌉`, where `n + 1` is its length, that
is `⌈d / 2⌉ < ⌈n / 2⌉` for the degree `d = Ratpoints.BruteForce.degree c`. Then comes the reversal
check with the switch `o.reverse` (`Ratpoints.Setup.reversal`), which may refuse the form too or
reverse the polynomial; with the Sturm step on, `0 ≤ o.sturm`, the form is refused when the
remainder chain of the polynomial searched is none (`Ratpoints.Sturm.chain`), that is when that
polynomial has a repeated factor. Otherwise the points are those of the search of the polynomial
that the reversal check hands on, with its flag of the reversal (`Ratpoints.searchPoints`): none
when no class of the denominators modulo 64 admits a numerator and there is no point at infinity, or
when the curve has no points modulo one of the primes examined, and else the points at infinity
first, then those of the denominators in the order of the loop of the search
(`Ratpoints.Sieve.sieveRun`), each mapped back to the caller's curve after a reversal.

C: `find_points.c:4523-4528`, `find_points.c:4546`, `find_points.c:4557-4559`,
`find_points.c:4564-4565`, `find_points.c:4567-4571`, `find_points.c:4578-4585`,
`find_points.c:4606`, `find_points.c:4624-4633`, `find_points.c:4658`, `find_points.c:4857-4892`,
`find_points.c:5219-5220`, `find_points.c:5226-5229`, `find_points.c:5235`,
`find_points.c:5241-5242`

Deviation: one function for `find_points`, `find_points_work` and `find_points_work_1`, which the
library calls in turn. The refusals of the program, in its order and with its errors
(`Ratpoints.Refusal`), for the codes and the order of the library: fewer than two coefficients are
refused on the length of `c`, as the program refuses them, where the library refuses an empty list
as a negative degree and one coefficient as the degree 0 (a longer list of degree 0 fails the test
of the leading zeros first); and the height bound, which the program checks before it calls the
library, comes before the test of the leading zeros, which the library makes first, so that `5 0`
with `H = 0` is error 4, as the program gives it. The degree with the leading zeros dropped is
`Ratpoints.BruteForce.degree c`. A natural number `H` for the `long` `height`, so that `H = 0`
stands for the heights below 1 that line 4658 refuses, and with no bound `2 ^ 63 - 1`, which only
the program's reading of the height imposes (`Ratpoints.Cli.heightBound`). A list for the array of
GMP integers and its scratch integers `work`, with nothing written back to the caller (the reversed
coefficients, the degree, the flags), so that there is no state between calls and the reset of the
flags clears nothing; the points are returned as a list, for the count `total` and the flag `quit`
of the callback (stage G); the points at infinity and the square test of the leading coefficient are
decided where they are used (`Ratpoints.Sieve.pointsAtInfinity`, `Ratpoints.Setup.reversal`,
`Ratpoints.searchPoints`). Of the Sturm step only its test for a repeated factor: the rest, which
restricts the search region and its exit when the polynomial is negative on the whole of it, is
stage H, so that `sturm_empty` is never set. No search region (stage H); no failure for lack of
memory, which the model cannot meet; no output under `RATPOINTS_VERBOSE`. -/
def findPoints (c : List Int) (H : Nat) (P : Params) (o : Options := {}) :
    Except Refusal (List (Int × Int × Int)) :=
  if maxDegree + 1 < c.length then .error .tooManyCoefficients
  else if c.length < 2 then .error .tooFewCoefficients
  else if H = 0 then .error .incorrectHeight
  else
    let d := BruteForce.degree c
    if (d + 1) / 2 < c.length / 2 then .error .notSquarefree
    else match Setup.reversal o.reverse c d with
      | .error e => .error e
      | .ok (c', d', rev) =>
        if 0 ≤ o.sturm ∧ Id.run (Sturm.chain c' d') = none then .error .notSquarefree
        else .ok (Id.run (searchPoints c' d' H P rev))

/-! ### Examples

The points that `ratpoints c H -q` prints at the pinned commit, in the same order, also after a
reversal and in the divisor shape, and with `-k` (`{ reverse := false }`); the list of the
brute-force reference `Ratpoints.bruteForce` for other parameters, among them pieces of a few bit
arrays; the refusals of forms that are not squarefree as the program makes them, with and without
`-s` (`{ sturm := -1 }`) and `-k`, and the points of such forms that it searches; the search with
the flag of the reversal, for polynomials to which ratpoints reverses others, and on curves without
points modulo `3`, `5` and `7`, where it takes an exit, and without points modulo 64, where it takes
the 2-adic exit; the tables of inverses and squares (`Ratpoints.Sieve.inversesMod`,
`Ratpoints.Sieve.squaresMod`) of the `Ratpoints.numPrimes` primes among which the moduli are chosen;
and the refusals in the order of the program, the coefficients before the height bound and the
height bound before the leading zeros. -/

#guard (findPoints [-2, 0, 0, 1] 130 defaultParams).toOption ==
  some [(1, 0, 0), (3, 5, 1), (3, -5, 1), (129, 3830, 100), (129, -3830, 100)]

#guard (findPoints [1, 2, 3, 4, 5, 6, 7] 20 defaultParams).toOption ==
  some [(-1, 2, 1), (-1, -2, 1), (0, 1, 1), (0, -1, 1), (8, 2401, 7), (8, -2401, 7)]

#guard (findPoints [1, 1, 1, 1, 0] 25 defaultParams).toOption ==
  some [(1, 0, 0), (-1, 0, 1), (0, 1, 1), (0, -1, 1), (1, 2, 1), (1, -2, 1), (7, 20, 1),
    (7, -20, 1), (-3, 10, 4), (-3, -10, 4)]

#guard (findPoints [1, 0, 126, 0, 441] 30 defaultParams).toOption ==
  some [(1, 21, 0), (1, -21, 0), (0, 1, 1), (0, -1, 1), (-1, 31, 2), (-1, -31, 2), (1, 31, 2),
    (1, -31, 2), (-2, 651, 21), (-2, -651, 21), (2, 651, 21), (2, -651, 21)]

-- The divisor shape: `ratpoints '1 2' 20 -q` (the divisors `1 2`, so the denominator 9 before 2),
-- `ratpoints '1 0 0 6' 200 -q` (the divisors `1 2 3 6`) and `ratpoints '0 3 -2991 -2062' 1300 -q
-- -k` (the divisors `1 2 1031`, so the denominator 1250 before 1031).
#guard (findPoints [1, 2] 20 defaultParams).toOption ==
  some [(1, 0, 0), (0, 1, 1), (0, -1, 1), (4, 3, 1), (4, -3, 1), (12, 5, 1), (12, -5, 1),
    (-4, 3, 9), (-4, -3, 9), (8, 15, 9), (8, -15, 9), (20, 21, 9), (20, -21, 9), (-1, 0, 2),
    (3, 4, 2), (3, -4, 2), (15, 8, 2), (15, -8, 2), (-3, 4, 8), (-3, -4, 8), (5, 12, 8),
    (5, -12, 8), (-5, 12, 18), (-5, -12, 18), (7, 24, 18), (7, -24, 18)]
#guard (findPoints [1, 0, 0, 6] 200 defaultParams).toOption ==
  some [(1, 0, 0), (0, 1, 1), (0, -1, 1), (2, 7, 1), (2, -7, 1), (20, 2849, 49), (20, -2849, 49),
    (-1, 2, 2), (-1, -2, 2), (35, 1436, 8), (35, -1436, 8), (2, 15, 3), (2, -15, 3),
    (-28, 4665, 75), (-28, -4665, 75)]
#guard (findPoints [0, 3, -2991, -2062] 1300 defaultParams { reverse := false }).toOption ==
  some [(1, 0, 0), (-4, 290, 1), (-4, -290, 1), (0, 0, 1), (-3, 60, 2), (-3, -60, 2),
    (1, 34400, 1250), (1, -34400, 1250), (1, 10310, 1031), (1, -10310, 1031)]

-- Polynomials that the program reverses, in the cases 2, 1 and 3 of the reversal check: the points
-- of `ratpoints c 4 -q` in its order, and those of `ratpoints c 4 -q -k`, which are those of the
-- brute-force reference.
#guard ([([-1, 0, 9], [(-1, 0, 3), (1, 3, 0), (1, -3, 0), (1, 0, 3)]),
    ([0, 1, 0, 0, 4], [(0, 0, 1), (1, 2, 0), (1, -2, 0)]), ([0, 1, 0, 2], [(0, 0, 1), (1, 0, 0)])] :
      List (List Int × List (Int × Int × Int))).all fun (c, pts) ↦
  (findPoints c 4 defaultParams).toOption == some pts &&
    (findPoints c 4 defaultParams { reverse := false }).toOption == some (bruteForce c 4)

-- No moduli, all 53 primes, the 53 primes in three stages, and moduli in another order: without the
-- reversal and the Sturm step the list of the reference, also for `0 0 1`, which the program
-- refuses unless run with `-k -s`, and with them the reference of the reversed polynomial mapped
-- back, for `-1 0 9`.
#guard [⟨[], 0, 0, 0, 64, true, 0⟩, sieveParams { numPrimes := 53 },
    ⟨primeTable.toList.take 53, 53, 10, 40, 64, true, 0⟩,
    ⟨[7, 3, 251, 5], 0, 1, 2, 0, false, 0⟩].all fun P ↦
  ([([1, 1, 1, 1, 0], 25), ([-1, 0, 9], 20), ([1, 0, 1], 12), ([0, 0, 1], 15)].all fun (c, H) ↦
    (findPoints c H P { reverse := false, sturm := -1 }).toOption == some (bruteForce c H)) &&
  (findPoints [-1, 0, 9] 20 P).toOption == some ((bruteForce [9, 0, -1] 20).map Sieve.swapPoint)

-- Composite moduli, prime powers and products of them in any order, and primes beyond those
-- examined, which are examined when their modulus is made: without the reversal and the Sturm step
-- the list of the reference, and with them the reference of the reversed polynomial mapped back.
#guard [⟨[45, 9, 77, 25, 3, 231, 49, 11], 2, 3, 7, 64, true, 0⟩,
    ⟨[243, 125, 169, 121, 7, 13], 0, 0, 4, 64, true, 0⟩, ⟨[255, 195, 61, 3], 53, 2, 2, 0, false, 0⟩,
    ⟨[147], 1, 1, 1, 64, true, 0⟩].all fun P : Params ↦ decide P.WF &&
  ([([1, 1, 1, 1, 0], 25), ([-2, 0, 0, 1], 130), ([1, 0, 126, 0, 441], 30),
      ([1, 2, 3, 4, 5, 6, 7], 20), ([0, 0, 1], 15)].all fun (c, H) ↦
    (findPoints c H P { reverse := false, sturm := -1 }).toOption == some (bruteForce c H)) &&
  (findPoints [-1, 0, 9] 20 P).toOption == some ((bruteForce [9, 0, -1] 20).map Sieve.swapPoint)

-- The sieve entries of moduli of each kind for `1 2 3 4 5 6 7` with the tables of the first two
-- primes: the prime 3 and the prime 67 examined anew, the prime powers 9 and 243, the product 15
-- of two primes, 45 = 9 · 5 of a prime power and a prime, and 231 = 3 · 7 · 11 of three primes;
-- and the exit of the curve `20 6 -14 12 -10`, which has no points modulo 3, at the modulus 15
-- when 3 is not examined in the loop of the tables, and none at the prime power 9.
#guard
  let c : List Int := [1, 2, 3, 4, 5, 6, 7]
  let fs (f : Sieve.Factor) : Nat := match f with | .prime e => e.p | .power pw => pw.m
  match Id.run (Sieve.examinePrimes c 6 true false 2 0 0) with
  | some (tables, _, _) =>
    tables.size == 2 && [3, 67, 9, 243, 15, 45, 231].map (fun m ↦
        (Id.run (makeModulus? c 6 true tables m)).map fun se ↦ (se.p, se.factors.map fs)) ==
      [some (3, [3]), some (67, [67]), some (9, [9]), some (243, [243]), some (15, [3, 5]),
        some (45, [9, 5]), some (231, [3, 7, 11])]
  | none => false
#guard
  let c : List Int := [20, 6, -14, 12, -10]
  (Id.run (sievingInfo c 4 true true ⟨[15], 0, 1, 1, 64, true, 0⟩ 30)).isNone &&
    (Id.run (sievingInfo c 4 true true ⟨[9], 0, 1, 1, 64, true, 0⟩ 30)).isSome &&
    (Id.run (sievingInfo c 4 true true ⟨[9], 1, 1, 1, 64, true, 0⟩ 30)).isNone &&
    Id.run (searchPoints c 4 30 ⟨[9], 0, 1, 1, 64, true, 0⟩ false) == []

-- Pieces of one, two and three bit arrays, at heights around the multiples of 64 and of
-- `rbaLength`: several pieces, the masks on the same piece and on different ones, and no low mask
-- when `H` is a multiple of `rbaLength`.
#guard [([-2, 0, 0, 1], [63, 64, 65, 255, 256, 257]), ([1, 1, 1, 1, 0], [128, 129])].all
  fun (c, Hs) ↦ Hs.all fun H ↦
    let bf := bruteForce c H
    [1, 2, 3].all fun A ↦
      let P := { defaultParams with moduli := primeTable.toList.take 5, arraySize := A }
      (findPoints c H P).toOption == some bf

-- The zero polynomial and polynomials of degree 0 with two or more coefficients, whose leading
-- zeros lower `⌈n / 2⌉`: refused as not squarefree whatever the options, as `ratpoints c H -q`
-- does, also with `-s` and `-s -k`.
#guard [([0, 0], 7), ([5, 0, 0, 0], 9), ([4, 0], 6)].all fun (c, H) ↦
  [{}, { sturm := -1 }, { reverse := false, sturm := -1 }].all fun o ↦
    findPoints c H defaultParams o matches .error .notSquarefree

-- `1 2 1`, with a repeated factor: refused by the remainder chain, and searched without the Sturm
-- step, as `ratpoints '1 2 1' 3 -q -s` does, which prints the 31 points of the reference.
#guard findPoints [1, 2, 1] 3 defaultParams matches .error .notSquarefree
#guard (findPoints [1, 2, 1] 3 defaultParams { sturm := -1 }).toOption.map List.length == some 31 &&
  (findPoints [1, 2, 1] 3 defaultParams { sturm := -1 }).toOption == some (bruteForce [1, 2, 1] 3)

-- `0 0 1 1 1`, of even degree with `c₀ = c₁ = 0`: refused by the reversal check, also without the
-- Sturm step, and searched under `-s -k`, as the program does.
#guard [{}, { sturm := -1 }].all fun o ↦
  findPoints [0, 0, 1, 1, 1] 3 defaultParams o matches .error .notSquarefree
#guard (findPoints [0, 0, 1, 1, 1] 3 defaultParams { reverse := false, sturm := -1 }).toOption ==
  some [(1, 1, 0), (1, -1, 0), (-1, 1, 1), (-1, -1, 1), (0, 0, 1)]

-- The search of the polynomials `9 0 -1`, `4 0 0 1 0` and `0 2 0 1`, to which ratpoints reverses
-- `-1 0 9`, `0 1 0 0 4` and `0 1 0 2`, with the flag of the reversal: the points that
-- `ratpoints '-1 0 9' 10 -q`, `ratpoints '0 1 0 0 4' 10 -q` and `ratpoints '0 1 0 2' 10 -q` print,
-- in their order.
#guard
  ([([9, 0, -1], 2, [(-1, 0, 3), (1, 3, 0), (1, -3, 0), (1, 0, 3), (-5, 12, 9), (-5, -12, 9),
      (5, 12, 9), (5, -12, 9)]),
    ([4, 0, 0, 1, 0], 3, [(0, 0, 1), (1, 2, 0), (1, -2, 0)]),
    ([0, 2, 0, 1], 3, [(0, 0, 1), (1, 0, 0)])] :
      List (List Int × Nat × List (Int × Int × Int))).all fun (c, d, pts) ↦
    Id.run (searchPoints c d 10 defaultParams true) == pts

-- Curves without points modulo 3, 5 and 7, for which `ratpoints c 30 -q` prints nothing: the table
-- of one of the default moduli is none, and the search returns no points, with either flag.
#guard [[20, 6, -14, 12, -10], [-2, -20, 7, 15, 2], [20, 7, -18, 0, 3]].all fun c ↦
  (defaultParams.moduli.mapM (Id.run <| Sieve.examinePrime? c 4 · (Setup.useCLong c 4))).isNone &&
    [false, true].all fun rev ↦ Id.run (searchPoints c 4 30 defaultParams rev) == []

-- The 2-adic exit: no class of the denominators of `2 0 3` admits a numerator modulo 64, and there
-- is no point at infinity, so that `ratpoints '2 0 3' 300000 -q` prints nothing at once.
#guard (findPoints [2, 0, 3] 300000 defaultParams).toOption == some []

-- The tables of the 53 primes of the default build: each nonzero residue times its entry in the
-- table of inverses is 1, and the table of squares marks `(p + 1) / 2` residues.
#guard (primeTable.toList.take numPrimes).all fun p ↦
  let inv := Sieve.inversesMod p
  (List.range' 1 (p - 1)).all (fun r ↦ inv[r]! * r % p == 1) &&
    (Sieve.squaresMod p).count true == (p + 1) / 2

#guard findPoints (List.replicate (maxDegree + 2) 1) 0 defaultParams matches
  .error .tooManyCoefficients
#guard findPoints (List.replicate (maxDegree + 1) 1) 1 ⟨[], 0, 0, 0, 64, true, 0⟩ matches .ok _
#guard findPoints [1] 0 defaultParams matches .error .tooFewCoefficients
#guard findPoints [1, 0, 1] 0 defaultParams matches .error .incorrectHeight
#guard findPoints [5, 0] 0 defaultParams matches .error .incorrectHeight

end Ratpoints

end
