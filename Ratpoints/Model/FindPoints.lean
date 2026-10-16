/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Denominators
public import Ratpoints.Model.Packing
public import Ratpoints.Model.Params
public import Ratpoints.Model.Setup
public import Ratpoints.Model.Sieve
public import Ratpoints.Model.Sturm

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Denominators
meta import Ratpoints.Model.Packing
meta import Ratpoints.Model.Params
meta import Ratpoints.Model.Setup
meta import Ratpoints.Model.Sieve
meta import Ratpoints.Model.Sturm

/-!
# The search for the points

`Ratpoints.findPoints c H P o` is the model of the library function `find_points` of ratpoints, with
the options `o` of the library that change the refusals or the order of the output
(`Ratpoints.Options`): it refuses, as the program does (`Ratpoints.Refusal`), more than
`Ratpoints.maxDegree + 1` coefficients, fewer than two, the height bound `0` and the heights that
are not `long`s, and then the binary forms that are not squarefree as the set-up of the library
finds them: when the leading zeros of the `n + 1` coefficients lower `⌈n / 2⌉`, in the reversal
check (`Ratpoints.Setup.reversal`), which may also reverse the polynomial, and with the Sturm step
on, by the remainder chain (`Ratpoints.Sturm.chain`). Otherwise it runs the search of the polynomial
that the set-up hands on (`Ratpoints.searchPoints`), which returns no points when no class of the
denominators modulo 64 admits a numerator and there is no point at infinity, or when the curve has
none modulo one of the primes examined for the parameters `P`, and otherwise the points of height at
most `H` on `y ^ 2 = F(x, z)`, the points at infinity first and then those of the denominators in
the order of the loop of the search (`Ratpoints.Sieve.Shape`), increasing unless it runs over the
divisors of the leading coefficient, found by the sieve on the bit arrays of words with the moduli,
primes, prime powers and products of them, and the array size of `P`, each mapped back to the
caller's curve after a reversal. What `sieving_info` computes for the search, the loop of the tables
of the primes examined with the exit and the forbidden divisors, the further forbidden divisors and
the sieve entries of the moduli with their reciprocals and the tables of their rows, is
`Ratpoints.sievingInfo`.

## Main definitions

* `Ratpoints.Options`: the options of a search.
* `Ratpoints.makeModulus?`, `Ratpoints.sievingInfo`: the sieve entry of a modulus, and the tables,
  the forbidden divisors and the sieve entries of the moduli of a search, with their reciprocals and
  the tables of their rows.
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
/-- The sieve entry of the modulus `m` at the position `n` of the moduli, for the polynomial of
degree `d` with the coefficient list `c` and the flag `useCLong` of the `long`s, from its factors
over the table (`Ratpoints.modulusFactors`) and the tables `tables` of the primes examined in the
loop of the tables, by their positions (`Ratpoints.Sieve.examinePrimes`): in a loop over the
factors, for a factor `p ^ e` with `e = 1`, the table of `p` from the loop of the tables when `p` is
among the primes examined there, and otherwise the table that its examination gives now
(`Ratpoints.Sieve.examinePrime?`), with none at once when the curve has no points modulo `p`; and
for `e ≥ 2` the tables of the prime power (`Ratpoints.Sieve.examinePower`). A prime or a prime power
has one factor, a product two or more; the entry holds the reference to the entry whose table of
rows holds its rows and the kind of its builder (`Ratpoints.Sieve.EntryRef`,
`Ratpoints.Sieve.RowInit`), for a prime or a prime power those of the entry of its one factor, whose
entry it shares, and for a product its own entry, by the position `n`, with the builder of the rows
of a product (`Ratpoints.Sieve.SieveEntry.refInit`); and it holds the reciprocal of `m`
(`Ratpoints.Sieve.magic`), the bias `m ⌈Ratpoints.rowBias / m⌉`, the least multiple of `m` that is
at least `Ratpoints.rowBias`, and the inverse of `Ratpoints.rbaLength` modulo `m`: for a prime, the
entry of the table of inverses of its table at the remainder of `Ratpoints.rbaLength` by the
multiplication with the reciprocal (`Ratpoints.Sieve.mulMod`), and otherwise the inverse by the
extended Euclidean algorithm (`Ratpoints.Sieve.modinv`); its inverses of the strides are made with
the row offsets of the packing of the numerators (`Ratpoints.Sieve.classOffsets`).

C: `find_points.c:2350-2354`, `find_points.c:2358-2359`, `find_points.c:2387-2395`,
`find_points.c:2414-2426`, `find_points.c:2428-2429`, `find_points.c:2434-2470`,
`find_points.c:2472-2475`, `find_points.c:2546`, `find_points.c:2548`, `find_points.c:2976-2978`,
`find_points.c:2994-2998`

Deviation: the entry of every modulus made here, by its factors computed again from `m`
(`Ratpoints.modulusFactors`), where `make_modulus` reads the codes `fac` of the factors and their
number `nf` that `add_moduli` stores with the candidate (lines 2405-2406), and where `sieving_info`
takes the entry of a prime from the loop of the tables (`prec[n].ssp`) and makes those of the prime
powers and the products by `make_modulus`; the primes and prime powers as factors of the entry, for
the fields `nf`, `pw` and `factor` and the entries of the prime powers that `make_power` makes; the
tables of a prime power (`Ratpoints.Sieve.Factor.power`) computed for each modulus that needs them,
where `add_moduli` examines a prime power once, when the factorization of the first candidate that
reaches it needs it (the power itself), whether or not that candidate is then offered, and keeps its
tables in its buffer `pws` by its index (`pw_idx`, lines 2350-2354, 2358-2359 and 2387-2394, with
the count `npw` of line 2548), and `make_modulus` makes the entry of a prime power once and keeps it
by its index (`power_se`), whose table of rows the model makes once too, for the prime power by its
prime and its exponent, as the C code keeps the index of its entry in `pw_idx[pn][e]`
(`Ratpoints.Sieve.EntryRef.power`, `Ratpoints.Sieve.SieveEntry.addTables`); the tables of a prime
power computed also when they say nothing, where `add_moduli` refuses a modulus with such a factor
(line 2395), and a prime factor whose prime says nothing (`examine_prime` returns `0`, and
`prime_se[pn]` stays `NULL`) taken with its table from the loop of the tables, where `add_moduli`
offers no composite with such a factor (line 2383); a prime beyond those of the loop of the tables
examined, with the exit, when the entry of a modulus needs it, where `sieving_info` examines the
primes from `prime[pn_lim]` on, in the order of the table, with the exit, in the loop of the tables
while its first two stages want more primes (lines 2693-2705; there they also give forbidden
divisors) and for the third stage (lines 2976-3016), both only when the number of primes was left to
the library (lines 2693 and 2980), also those that it then skips, and `add_moduli` makes composites,
prime powers and products alike, of the primes of the loop of the tables only (line 2370): the
output does not depend on the primes examined, since the exit is taken only when the curve has no
points; every modulus of the parameters taken, any product of powers of primes of the table below
`Ratpoints.maxPrimeEven` (`Ratpoints.Params.WF`), where `add_moduli` offers a composite only for an
odd `9 ≤ m ≤ RATPOINTS_COMPOSITE_MAX` (line 2361; `ratpoints.h:210-211`, 64 by default) whose table
is not too dear for the run (line 2368), a density `r < 1` (line 2402) and at most `RP_MAX_MODULI`
candidates (line 2403), restrictions that the model lifts as choices of the moduli (stage I); the
test of room in the buffer of the prime powers (lines 2351 and 2390) not made, which never fails,
since `add_moduli` runs once for the curve (line 2821, `npw = 0` at line 2548) and examines each
power `p^e < RATPOINTS_MAX_PRIME_EVEN` of the first `RATPOINTS_NUM_PRIMES` primes at most once
(`pw_idx`, lines 2358-2359 and 2387-2393), all of which `num_powers` counts; the reciprocal `magic`,
the bias `bias` and the inverse `rbainv` of every kind of modulus set here, with the formulas of the
C code, where `examine_prime` sets those of a prime with its table (lines 1808, 1815 and 1816),
`make_power` those of a prime power (lines 2422, 2424 and 2425) and `make_modulus` those of a
product (lines 2454, 2456 and 2457), the inverse of a prime read from its table, as from the table
`inverses[pn]` of the build; natural numbers for the `long`s of these formulas; the inverses `dinv`
empty, which the row offsets of the packing fill (`Ratpoints.Sieve.classOffsets`); no density `r`
(stage I); the kind `init` of the builder set here for every kind of modulus, where `examine_prime`
sets that of a prime with its table (line 1800); the reference to the entry whose table of rows
holds its rows (`Ratpoints.Sieve.EntryRef`), for the pointer to the entry, the position `n` of a
product its own entry; the tables of rows of the entry and of its factors, which `make_power` (line
2427) and `make_modulus` (line 2471) clear, made in the store of the run by the loop over the moduli
after the entry (`Ratpoints.Sieve.SieveEntry.addTables`); the entry a fresh value, for the space
that `make_power` and `make_modulus` take from the buffer of the sieve entries (`se_next`), and the
exit as `none`, for the prime that `sieving_info` returns. -/
def makeModulus? (c : List Int) (d : Nat) (useCLong : Bool) (tables : Array Entry) (n m : Nat) :
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
  let rbainv ← match factors.toList with
    | [.prime t] => pure t.inverses[mulMod rbaLength m (magic m)]!
    | _ => modinv (rbaLength % m) m
  let (ref, init) := SieveEntry.refInit n factors.toList
  return some
    { p := m, factors := factors.toList, magic := magic m, bias := m * ((rowBias + m - 1) / m),
      rbainv, dinv := #[], ref, init }

open Sieve in
/-- What `sieving_info` computes for the search of the polynomial with the coefficient list `c` of
degree `d`, the flag `useCLong` of the `long`s, the switch `checkDenom` of the forbidden divisors,
the parameters `P` and the largest denominator `bHigh`: the loop of the tables over the first
`P.examined` primes of the table, with at most `P.maxForbidden` forbidden divisors
(`Ratpoints.Sieve.examinePrimes`), and none when the curve has no points modulo one of them; for the
switch on, the forbidden divisors among the further primes (`Ratpoints.Sieve.forbidden`); and, in a
loop over the moduli of `P` in their order, the sieve entry of each at its position, the number of
the entries made before it (`Ratpoints.makeModulus?`), with the tables of rows of the entry and of
its factors in the store of the run when they are absent (`Ratpoints.Sieve.SieveEntry.addTables`),
and none at once when the curve has no points modulo a prime examined for it. Then the sieve entries
of the moduli, their reciprocals in their order (`Ratpoints.Sieve.SieveEntry.magic`), the forbidden
divisors tested with words and by their valuations, and the store of the tables of rows that the
loop of the tables and the entries of the moduli make (`Ratpoints.Sieve.RowStore`).

C: `find_points.c:2522-2532`, `find_points.c:2892-2900`, `find_points.c:3064-3070`,
`find_points.c:3102-3103`

Deviation: the arguments that serve the choice of the moduli (the mean number of bits per word,
whether the number of primes was left to the library, the word `den_bits` and the classes `cls`) are
not modelled, nor that choice (stage I): the moduli and their stages are those of the parameters,
and the primes examined in the loop of the tables their first `P.examined`, beyond which
`Ratpoints.makeModulus?` examines a prime when a modulus needs it; the sieve entries of every
modulus made here, those of the third stage included, which `sieving_info` puts into `sieve_list` in
the choice of the third stage (line 3014), and again, sorted by density with the reserve of
`adapt_primes`, after it (lines 3026-3030; stage I), and the reciprocals of the entries of the
moduli, where `sieving_info` collects those of the reserve too (stage I); the flag
`RATPOINTS_CHECK_DENOM` as the switch `checkDenom`, which the search clears, with the flag, when
there is no forbidden divisor and no Jacobi test (`Ratpoints.searchPoints`); the sieve entries and
the forbidden divisors returned as lists and the reciprocals as an array, for the arrays
`sieve_list` and `magics` and the arrays of the arguments, with no bound `2 RATPOINTS_NUM_PRIMES` on
the number of the entries and the reciprocals (lines 332-333 and 347), which ratpoints never reaches
since each of its entries owns a prime, where well-formed parameters may repeat a modulus; the store
of the tables of rows returned, for the arrays `sieve` of the entries that `sieving_info` makes; the
position of a modulus the number of the entries made before it, the reference to a product
(`Ratpoints.makeModulus?`); and the exit as `none`, for the prime returned; no failure for lack of
memory, which the model cannot meet; no output under `RATPOINTS_VERBOSE`, `RP_PRIME_STATS` or
`DEBUG`. -/
def sievingInfo (c : List Int) (d : Nat) (useCLong checkDenom : Bool) (P : Params) (bHigh : Nat) :
    Id (Option
      (List SieveEntry × Array Nat × List ForbiddenEntry × List ForbiddenVal × RowStore)) := do
  let some (tables, ba, val, store) ←
      examinePrimes c d useCLong checkDenom P.examined P.maxForbidden bHigh | return none
  let (forb, forbVal) ← if checkDenom then forbidden c d P.examined P.maxForbidden bHigh ba val
    else pure (ba.toList, val.toList)
  let mut entries : Array SieveEntry := #[]
  let mut store := store
  for m in P.moduli do
    let some e ← makeModulus? c d useCLong tables entries.size m | return none
    entries := entries.push e
    store := e.addTables store
  let magics := entries.map (·.magic)
  return some (entries.toList, magics, forb, forbVal, store)

open Sieve in
/-- The search of the polynomial with the coefficient list `c` of degree `d` that the set-up hands
on, for the height `H`, the parameters `P` and the flag `rev` of the reversal, over the denominators
`bLow = 1, …, bHigh = H`. First the flags of the tests on the denominators: the checked loop for
even degree; the Jacobi test for even degree, `c_d` not a square (`Ratpoints.Setup.isSquare`) and
the switch `P.jacobi`; the squares for odd degree and `|c_d| = 1`; and for odd degree otherwise the
divisors of `c_d` (`Ratpoints.Setup.setupUs1`). Then the 2-adic information
(`Ratpoints.Sieve.twoAdic`) with the packings of the classes of the denominators modulo 64 and the
word `den_bits` of the classes that admit a numerator (`Ratpoints.Sieve.numClasses`), and no points
when no class admits a numerator and there is no point at infinity, as there is for odd degree or
`c_d` a square. Then the tables of the primes examined, the forbidden divisors for even degree and
the sieve entries of the moduli of `P` and their reciprocals (`Ratpoints.sievingInfo`), with the
flag of the `long`s (`Ratpoints.Setup.useCLong`), and no points when the curve has no points modulo
one of the primes examined; the checked loop off when there are no forbidden divisors and no Jacobi
test; an array of `Ratpoints.Sieve.numPackings` rows of one offset for each sieve entry, and the row
offsets of the classes in it, with the inverses of the strides in the entries
(`Ratpoints.Sieve.classOffsets`); the shape of the run (`Ratpoints.Sieve.runSetup`); and the points
at infinity (`Ratpoints.Sieve.pointsAtInfinity`), followed by those of the denominators of the shape
(`Ratpoints.Sieve.sieveRun`) with the classes and their row offsets, the sieve entries of the moduli
in the three stages that the cut points `P.sp1` and `P.sp2` give, their reciprocals, the store of
the tables of rows that `Ratpoints.sievingInfo` makes, and pieces of at most
`Ratpoints.Params.arraySizeAt P H` bit arrays, each point mapped by `Ratpoints.Sieve.swapPoint`
when `rev` is set. For well-formed parameters, `1 ≤ H < 2 ^ 63` and `d` the degree of `c`, these are
the points at infinity followed by the points of the brute-force reference over the denominators of
the search (`Ratpoints.searchDens`), in the order of its loop, increasing unless the shape is that
of the divisors, each mapped when `rev` is set, also when an exit is taken
(`Ratpoints.run_searchPoints`).

C: `find_points.c:2793-2795`, `find_points.c:4573`, `find_points.c:4588-4589`,
`find_points.c:4595-4596`, `find_points.c:4602`, `find_points.c:4603-4604`, `find_points.c:4607`,
`find_points.c:4900-4943`, `find_points.c:4948`, `find_points.c:4954-4963`,
`find_points.c:4992-5012`, `find_points.c:5106`, `find_points.c:5116`, `find_points.c:5119`,
`find_points.c:5132`, `find_points.c:5137-5139`, `find_points.c:5167`

Deviation: the arguments of `sieving_info` that serve the choice of the moduli (the mean number of
bits per word, whether the number of primes was left to the library, the 2-adic classes and the word
`den_bits`) are not modelled; the denominators from `1` to `H`, for the range `b_low, …, b_high`
(stage H); the flags of the denominators as Booleans, for the bits of `args->flags`; the forbidden
divisors and the divisors of the leading coefficient with their records as lists, for the arrays
`args->forb_ba`, `args->forbidden`, `args->den_info` and `args->divisors` of the arguments, and the
sieve entries as a list, for the array `args->sieve_list` that `sieving_info` fills and
`class_offsets` reads; the square test `lcfsq` of line 4906 made on the polynomial searched
(`Ratpoints.Setup.isSquare`), where the C code computes it before the reversal check (line 4634) and
clears it in case 2 (line 4770): the same value for an even degree, the only one that reads it; the
store of the tables of rows that `Ratpoints.sievingInfo` returns handed to the run as a value, for
the arrays `sieve` of the entries of `args->sieve_list`; the test on `point_at_infty` of the 2-adic
exit recomputed, as `Ratpoints.Sieve.pointsAtInfinity` decides it; the exits give the empty list,
where `sieving_info` returns the prime and `find_points_work_1` the number `0` of points found; the
Sturm step does not restrict the search region before stage H, so that the return when it leaves
nothing to search is never taken, and the run always follows the points at infinity; no failure for
lack of memory, which the model cannot meet; the array of the row offsets made with zeros, for the
array on the stack, whose entries the C code leaves unset until `class_offsets` writes them, with
one offset in each row for each sieve entry of the run, those of its three stages, for the `sp3_max`
entries with the reserve of further primes (stage I); no output under `RATPOINTS_VERBOSE` or
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
  let (cls, db) ← numClasses nb
  if db == 0 && !(d % 2 == 1 || Setup.isSquare lcf) then return []
  let some (entries, magics, forb, forbVal, store) ← sievingInfo c d useCLong checkDenom P bHigh
    | return []
  if forb.isEmpty && forbVal.isEmpty && !useJacobi then checkDenom := false
  let offsets := Array.replicate ((← numPackings cls) * max entries.length 1) 0
  let (cls, entries, offsets) ← classOffsets cls entries offsets
  let shape ← runSetup useSquares us1 checkDenom useJacobi forb forbVal lcf bHigh
  let pts ← sieveRun c d H (P.arraySizeAt H) rev P.sp1 P.sp2 entries magics cls offsets db shape 1
    bHigh store
  return pointsAtInfinity c d rev ++ pts.toList

/-- The points of height at most `H` on `y ^ 2 = F(x, z)` for the coefficient list `c`, found by the
sieve with the moduli and the array size of the parameters `P` and the options `o`, by default those
of a run of the program without options. More than `Ratpoints.maxDegree + 1` coefficients, fewer
than two, and the height bound `0` or one of `2 ^ 63` or more, which is not a `long`
(`Ratpoints.fitsLong`), are refused, in the order of the program (errors 3, 5 and 4); then, as not
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
`find_points.c:5241-5242`, `ratpoints.h:362`

Deviation: one function for `find_points`, `find_points_work` and `find_points_work_1`, which the
library calls in turn. The refusals of the program, in its order and with its errors
(`Ratpoints.Refusal`), for the codes and the order of the library: fewer than two coefficients are
refused on the length of `c`, as the program refuses them, where the library refuses an empty list
as a negative degree and one coefficient as the degree 0 (a longer list of degree 0 fails the test
of the leading zeros first); and the height bound, which the program checks before it calls the
library, comes before the test of the leading zeros, which the library makes first, so that `5 0`
with `H = 0` is error 4, as the program gives it. The degree with the leading zeros dropped is
`Ratpoints.BruteForce.degree c`. A natural number `H` for the `long` `height` of the arguments
(`ratpoints.h:362`), so that `H = 0` stands for the heights below 1 that line 4658 refuses; a height
that is not a `long`, `2 ^ 63` or more, is refused with error 4, as the program refuses it when it
reads the height (`Ratpoints.Cli.heightBound`), where the library cannot be given one, its height
being a `long`. A list for the array of GMP integers and its scratch integers `work`, with nothing
written back to the caller (the reversed coefficients, the degree, the flags), so that there is no
state between calls and the reset of the flags clears nothing; the points are returned as a list,
for the count `total` and the flag `quit` of the callback (stage G); the points at infinity and the
square test of the leading coefficient are decided where they are used
(`Ratpoints.Sieve.pointsAtInfinity`, `Ratpoints.Setup.reversal`, `Ratpoints.searchPoints`). Of the
Sturm step only its test for a repeated factor: the rest, which restricts the search region and its
exit when the polynomial is negative on the whole of it, is stage H, so that `sturm_empty` is never
set. No search region (stage H); no failure for lack of memory, which the model cannot meet; no
output under `RATPOINTS_VERBOSE`. -/
def findPoints (c : List Int) (H : Nat) (P : Params) (o : Options := {}) :
    Except Refusal (List (Int × Int × Int)) :=
  if maxDegree + 1 < c.length then .error .tooManyCoefficients
  else if c.length < 2 then .error .tooFewCoefficients
  else if H = 0 ∨ !fitsLong H then .error .incorrectHeight
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
the 2-adic exit; composite moduli, prime powers and products of them, in any order and with primes
beyond those examined; the sieve entries of each kind, and the exits of `Ratpoints.sievingInfo`; the
packing of `-2 0 0 1` as the build of ratpoints with `DEBUG` prints it, with its classes, the word
of the classes that admit a numerator, its seven packings, the biases of its moduli and the residues
and row offsets of four denominators; the row offsets of the packing and the inverses of the strides
against their rule (`Ratpoints.Sieve.classOffsets`); the sieve of one denominator in the packing of
its class, with the residues of the denominator divided by the stride and the row offsets of the
class, against the plain sieve of the numerators that the word of the class admits, also for words
whose bits of the heights 1 to 3 can be none or end below `0`, with either flag of the reversal; the
tables of inverses and squares (`Ratpoints.Sieve.inversesMod`, `Ratpoints.Sieve.squaresMod`) of the
`Ratpoints.numPrimes` primes among which the moduli are chosen; and the refusals in the order of the
program, the coefficients before the height bound and the height bound before the leading zeros, for
the height bound `0` and for `2 ^ 63`, the least height that is not a `long`, while `2 ^ 63 - 1`
passes on to the test of the leading zeros. -/

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
-- primes: the prime 3 from the loop of the tables and the prime 67 examined anew, the prime powers
-- 9 and 243, the product 15 of two primes, 45 = 9 · 5 of a prime power and a prime, and
-- 231 = 3 · 7 · 11 of three primes, each with the reference and the kind of builder of its
-- position, the position 5 for a product; and the exit of the curve `20 6 -14 12 -10`, which has no
-- points modulo 3, at the modulus 15 when 3 is not examined in the loop of the tables, none at the
-- prime power 9, the exit in the loop of the tables when 3 is examined there, and no points from
-- the search.
#guard
  let c : List Int := [1, 2, 3, 4, 5, 6, 7]
  let fs (f : Sieve.Factor) : Nat := match f with | .prime e => e.p | .power pw => pw.m
  match Id.run (Sieve.examinePrimes c 6 true false 2 0 0) with
  | some (tables, _, _, _) =>
    tables.size == 2 && [3, 67, 9, 243, 15, 45, 231].map (fun m ↦
        (Id.run (makeModulus? c 6 true tables 5 m)).map fun se ↦
          (se.p, se.factors.map fs, se.ref, se.init)) ==
      [some (3, [3], .prime 3, .sieve1), some (67, [67], .prime 67, .sieve2),
        some (9, [9], .power 3 2, .power), some (243, [243], .power 3 5, .power),
        some (15, [3, 5], .product 5, .product), some (45, [9, 5], .product 5, .product),
        some (231, [3, 7, 11], .product 5, .product)]
  | none => false
#guard
  let c : List Int := [20, 6, -14, 12, -10]
  (Id.run (sievingInfo c 4 true true ⟨[15], 0, 1, 1, 64, true, 0⟩ 30)).isNone &&
    (Id.run (sievingInfo c 4 true true ⟨[9], 0, 1, 1, 64, true, 0⟩ 30)).isSome &&
    (Id.run (sievingInfo c 4 true true ⟨[9], 1, 1, 1, 64, true, 0⟩ 30)).isNone &&
    Id.run (searchPoints c 4 30 ⟨[9], 0, 1, 1, 64, true, 0⟩ false) == []

-- The tables of rows that `Ratpoints.sievingInfo` makes: for `1 2 3 4 5 6 7` with the first two
-- primes examined in the loop of the tables, both of which say something, and the moduli 3, the
-- prime 67 beyond the loop, the prime power 9, the products 15 = 3 · 5 and 45 = 9 · 5, and the
-- prime power 243, one table of rows for each prime, each prime power and each product, keyed by
-- the prime, the prime and the exponent of the prime power and the position of the product, of the
-- size of the modulus, with the row of `0` of a prime from the build and no other row; and for
-- `1 0 2`, for which 3 says nothing (`f(x)` a square modulo 3 for every `x`, and `2` not a square),
-- no table of rows of 3 from the loop of the tables, and one when 3 is a modulus.
#guard
  let tabs (c : List Int) (d : Nat) (P : Params) : Option Sieve.RowStore :=
    (Id.run (sievingInfo c d true false P 30)).map fun (_, _, _, _, s) ↦ s
  let rows (s : Sieve.RowStore) (k : Sieve.EntryRef) : List Nat :=
    (List.range (s.getD k #[]).size).filter fun r ↦ (s.row? k r).isSome
  match tabs [1, 2, 3, 4, 5, 6, 7] 6 ⟨[3, 67, 9, 15, 45, 243], 2, 6, 6, 64, true, 0⟩,
      tabs [1, 0, 2] 2 ⟨[], 2, 0, 0, 64, true, 0⟩, tabs [1, 0, 2] 2 ⟨[3], 2, 1, 1, 64, true, 0⟩ with
  | some s, some s', some s'' =>
    let ks : List (Sieve.EntryRef × Nat) := [(.prime 3, 3), (.prime 5, 5), (.prime 67, 67),
      (.power 3 2, 9), (.product 3, 15), (.product 4, 45), (.power 3 5, 243)]
    s.size == 7 && ks.all (fun (k, m) ↦ (s.getD k #[]).size == m &&
      rows s k == match k with | .prime _ => [0] | _ => []) &&
    s.row? (.prime 67) 0 == some (Sieve.sieves0 67) &&
    !s'.contains (.prime 3) && s'.contains (.prime 5) && s''.contains (.prime 3)
  | _, _, _ => false

-- The reciprocals that `Ratpoints.sievingInfo` collects for `1 2 3 4 5 6 7` are those of the
-- moduli, in their order, each sieve entry holding the reciprocal of its modulus, the bias, a
-- multiple of the modulus from `rowBias` to below `rowBias + p`, and the inverse of `rbaLength`,
-- read from the table of a prime and computed by `modinv` for a product and a prime power.
#guard
  match Id.run (sievingInfo [1, 2, 3, 4, 5, 6, 7] 6 true true ⟨[45, 7, 9, 67], 2, 2, 4, 64, true, 0⟩
      30) with
  | some (entries, magics, _, _, _) => entries.map (·.p) == [45, 7, 9, 67] &&
    magics.toList == [45, 7, 9, 67].map Sieve.magic &&
    entries.all fun e ↦ e.magic == Sieve.magic e.p && e.bias % e.p == 0 && rowBias ≤ e.bias &&
      e.bias < rowBias + e.p && e.rbainv < e.p && e.rbainv * rbaLength % e.p == 1 && e.dinv.isEmpty
  | none => false

-- The packing of `-2 0 0 1` with the moduli 3, 7, 5 and 11, those of the first stage of ratpoints
-- at the height 30, as the build of ratpoints with `DEBUG` at the pinned commit prints it
-- (`ratpoints '-2 0 0 1' 30`): the word of the classes that admit a numerator, and the classes
-- `b ≡ 0, 1, 4, 9, 16, 48 (mod 64)` with the strides 2, 8, 8, 8, 4, 4 and the residues 1, 3, 1, 3,
-- 1, 3, all of them with the pattern of ones; seven packings; the biases of the moduli; and for the
-- denominators 1, 4, 9 and 16 the residues `bp` of `b` divided by the stride of its class and the
-- offsets of the rows of the class, less the biases
-- (`p = 7, bp = 1, offset = 6 (+ bias 2147483653)` for `b = 1`).
#guard
  let c : List Int := [-2, 0, 0, 1]
  match Id.run (sievingInfo c 3 true false ⟨[3, 7, 5, 11], 0, 2, 4, 64, true, 0⟩ 30) with
  | some (entries, magics, _, _, store) =>
    let (cls, db) := Id.run (Sieve.numClasses (Id.run (Sieve.twoAdic c 3)))
    let np := Id.run (Sieve.numPackings cls)
    let (cls, entries, offsets) :=
      Id.run (Sieve.classOffsets cls entries (Array.replicate (np * entries.length) 0))
    db == 0xbabbbabababbbabb && np == 7 &&
      ([0, 1, 4, 9, 16, 48].map fun b ↦ (cls[b]!.bits, cls[b]!.k, cls[b]!.a0)) ==
        [(~~~0, 1, 1), (~~~0, 3, 3), (~~~0, 3, 1), (~~~0, 3, 3), (~~~0, 2, 1), (~~~0, 2, 3)] &&
      entries.map (·.bias) == [2147483649, 2147483653, 2147483650, 2147483657] &&
      ([(1, [2, 1, 2, 7], [0, 6, 1, 7]), (4, [2, 4, 3, 6], [2, 2, 2, 6]),
          (9, [0, 2, 3, 8], [0, 6, 1, 7]), (16, [1, 4, 4, 4], [1, 4, 4, 1])] :
          List (Nat × List Nat × List Nat)).all fun (b, bp, off) ↦
        let cl := cls[b % 64]!
        let bp' := Sieve.fillBpList b cl.k entries magics.toList
        bp' == bp && (Sieve.setRows store entries bp' cl offsets).1.map (·.offset) ==
          List.zipWith (· + ·.bias) off entries
  | none => false

-- The row offsets and the inverses of the strides that `class_offsets` makes, against their rule,
-- for the classes with a pattern of four curves and moduli of every kind up to 255: the offset of a
-- class of the stride `2 ^ k` and the residue `a₀` for the modulus `p` times `2 ^ k rbaLength` is
-- `a₀` modulo `p`, between `rowBias` and `rowBias + 2 p`; `dinv[k] 2 ^ k ≡ 1 (mod p)` with
-- `dinv[k] < p`, and `rbainv rbaLength ≡ 1`; the classes of one packing share a row, and there are
-- as many rows as packings.
#guard
  ([([-2, 0, 0, 1], 3), ([1, 2, 3, 4, 5, 6, 7], 6), ([1, 0, 126, 0, 441], 4),
      ([6, -3, 5, 2, 75], 4)] : List (List Int × Nat)).all fun (c, d) ↦
  match Id.run (sievingInfo c d true false
      ⟨[3, 7, 5, 11, 9, 15, 25, 45, 77, 121, 243, 255, 251], 0, 2, 13, 64, true, 0⟩ 30) with
  | some (entries, _, _, _, _) =>
    let (cls, _) := Id.run (Sieve.numClasses (Id.run (Sieve.twoAdic c d)))
    let np := Id.run (Sieve.numPackings cls)
    let (cls', entries', offsets) :=
      Id.run (Sieve.classOffsets cls entries (Array.replicate (np * entries.length) 0))
    let rows := ((List.range 64).filterMap fun b ↦ cls'[b]!.offset).eraseDups
    rows.length == np && entries'.map (·.p) == entries.map (·.p) &&
      entries.all (fun e ↦ e.rbainv * rbaLength % e.p == 1) &&
      (List.range 64).all fun b ↦ let cl := cls'[b]!
        cl.bits == 0 && cl.offset == none || (List.range entries.length).all fun n ↦
          let e := entries'[n]!
          let o := offsets[cl.offset.getD 0 + n]!
          o * (2 ^ cl.k * rbaLength) % e.p == cl.a0 % e.p && rowBias ≤ o && o < rowBias + 2 * e.p &&
            e.dinv[cl.k]! * 2 ^ cl.k % e.p == 1 && e.dinv[cl.k]! < e.p &&
            (List.range 64).all fun b' ↦ cls'[b']!.bits == 0 || cls'[b']!.k != cl.k ||
              cls'[b']!.a0 != cl.a0 || cls'[b']!.offset == cl.offset
  | none => false

-- The sieve of one denominator in the packing of its class against the plain sieve of the
-- numerators that the word of the class admits, for `-2 0 0 1` (strides up to 8), `1 2 3 4 5 6 7`
-- and `1 0 126 0 441`, with primes, a prime power and products among the moduli of the first two
-- stages and primes in the third, the numerators `-300, …, 300` of the denominators `1, …, 40`,
-- pieces of one and three bit arrays, and with the flag of the reversal the same points, mapped.
#guard
  ([([-2, 0, 0, 1], 3), ([1, 2, 3, 4, 5, 6, 7], 6), ([1, 0, 126, 0, 441], 4)] :
      List (List Int × Nat)).all fun (c, d) ↦
  match Id.run (sievingInfo c d true false ⟨[3, 7, 9, 5, 11, 15, 13, 17, 19], 0, 3, 7, 0, true, 0⟩
      300) with
  | some (entries, magics, _, _, store) =>
    let nb := Id.run (Sieve.twoAdic c d)
    let (cls, _) := Id.run (Sieve.numClasses nb)
    let np := Id.run (Sieve.numPackings cls)
    let (cls, entries, offsets) :=
      Id.run (Sieve.classOffsets cls entries (Array.replicate (np * entries.length) 0))
    let mgs := magics.toList
    (List.range' 1 40).all fun b ↦ cls[b % 64]!.bits == 0 || [1, 3].all fun A ↦
      let cl := cls[b % 64]!
      let bp := Sieve.fillBpList b cl.k (entries.take 7) (mgs.take 7)
      let surv : Vector Bool (2 * 300 + 1) := .ofFn fun i ↦
        nb[b % 64]!.toBitVec.getLsbD ((i.val + 64 * 5 - 300) % 64) &&
          Sieve.survives entries b ((i.val : Int) - 300)
      let ref := (Id.run (Sieve.checkDen c d 300 b surv)).toList
      [false, true].all fun rev ↦
        (Id.run (Sieve.sift c d 300 A b rev 3 (entries.take 7) (mgs.take 7) bp cl offsets
          (entries.drop 7) (mgs.drop 7) store)).1.toList ==
          if rev then ref.map Sieve.swapPoint else ref
  | none => false

-- The sieve of one denominator in the packings of words that are not those of a curve, against the
-- plain sieve of the numerators that the word admits, at the heights 1, 2 and 3, where the interval
-- of the bits can be empty or end below 0: the words of the numerators `2 (mod 4)` (`k = 2`,
-- `a₀ = 2`; no numerator of `-1, …, 1`, so no bit at `H = 1`), `5 (mod 8)` (`k = 3`, `a₀ = 5`; the
-- numerator `-3` of bit `-1` at `H = 3`), `3 (mod 8)`, `1 (mod 2)` and all, for the denominators
-- `1, …, 12` with the moduli of `-2 0 0 1` in the three stages, and the flag of the reversal.
#guard
  let c : List Int := [-2, 0, 0, 1]
  match Id.run (sievingInfo c 3 true false ⟨[3, 7, 9, 5, 11, 15, 13, 17, 19], 0, 3, 7, 0, true, 0⟩
      12) with
  | some (entries, magics, _, _, store) =>
    let word (m r : Nat) : UInt64 := (List.range 64).foldl (fun w a ↦
      if a % m = r then w ||| 1 <<< a.toUInt64 else w) 0
    let words := [word 4 2, word 8 5, word 8 3, word 2 1, ~~~0, 0]
    let nb : Vector UInt64 64 := .ofFn fun b ↦ words.getD (b.val % 6) 0
    let (cls, _) := Id.run (Sieve.numClasses nb)
    let np := Id.run (Sieve.numPackings cls)
    let (cls, entries, offsets) :=
      Id.run (Sieve.classOffsets cls entries (Array.replicate (np * entries.length) 0))
    let mgs := magics.toList
    (cls[1]!.k, cls[1]!.a0, cls[2]!.k, cls[2]!.a0) == (3, 5, 3, 3) && [1, 2, 3].all fun H ↦
      (List.range' 1 12).all fun b ↦ cls[b % 64]!.bits == 0 || [false, true].all fun rev ↦
        let cl := cls[b % 64]!
        let bp := Sieve.fillBpList b cl.k (entries.take 7) (mgs.take 7)
        let surv : Vector Bool (2 * H + 1) := .ofFn fun i ↦
          nb[b % 64]!.toBitVec.getLsbD ((((i.val : Int) - H) % 64).toNat) &&
            Sieve.survives entries b ((i.val : Int) - H)
        let ref := (Id.run (Sieve.checkDen c 3 H b surv)).toList
        (Id.run (Sieve.sift c 3 H 1 b rev 3 (entries.take 7) (mgs.take 7) bp cl offsets
          (entries.drop 7) (mgs.drop 7) store)).1.toList ==
          if rev then ref.map Sieve.swapPoint else ref
  | none => false

-- The array size 1, which `arraySizeAt` rounds up to the chunk 16, at heights around the multiples
-- of 64 and of `rbaLength`, with five moduli in the three stages: each class runs as one piece of
-- 16 bit arrays, with the low and the high mask on the same piece, the last bit array cut at
-- `wHigh` inside the piece, and no low mask when `H` is a multiple of `rbaLength`. Several pieces
-- and the masks on different pieces are in the examples of `sift` (pieces of one, two and three
-- bit arrays at `H = 300`, `Ratpoints.Model.Sieve`) and of the run (the array size 1,
-- `Ratpoints.Model.Denominators`), and through `findPoints` in the differential tests of the suite
-- `test4high`; those at the heights 5000 and 30000 have pieces of several chunks.
#guard [([-2, 0, 0, 1], [63, 64, 65, 255, 256, 257]), ([1, 1, 1, 1, 0], [128, 129])].all
  fun (c, Hs) ↦ Hs.all fun H ↦
    let P : Params := { defaultParams with
      moduli := primeTable.toList.take 5, sp1 := 2, sp2 := 4, arraySize := 1 }
    decide P.WF && (findPoints c H P).toOption == some (bruteForce c H)

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
#guard findPoints [1] (2 ^ 63) defaultParams matches .error .tooFewCoefficients
#guard findPoints [1, 0, 1] (2 ^ 63) defaultParams matches .error .incorrectHeight
#guard findPoints [5, 0] (2 ^ 63) defaultParams matches .error .incorrectHeight
#guard findPoints [5, 0, 0, 0] (2 ^ 63 - 1) defaultParams matches .error .notSquarefree

end Ratpoints

end
