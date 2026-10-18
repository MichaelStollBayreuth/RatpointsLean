/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Delivery
public import Ratpoints.Model.Denominators
public import Ratpoints.Model.Packing
public import Ratpoints.Model.Params
public import Ratpoints.Model.Setup
public import Ratpoints.Model.Sieve
public import Ratpoints.Model.Sturm

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Delivery
meta import Ratpoints.Model.Denominators
meta import Ratpoints.Model.Packing
meta import Ratpoints.Model.Params
meta import Ratpoints.Model.Setup
meta import Ratpoints.Model.Sieve
meta import Ratpoints.Model.Sturm

/-!
# The search for the points

`Ratpoints.findPointsWith c H P o process info` is the model of the library function `find_points`
of ratpoints, with the options `o` of the library that change the refusals, the order of the output
or what is delivered (`Ratpoints.Options`), the callback `process` of the caller and its data
`info`: it refuses, as the program does (`Ratpoints.Refusal`), more than `Ratpoints.maxDegree + 1`
coefficients, fewer than two, the height bound `0` and the heights that are not `long`s, and then
the binary forms that are not squarefree as the set-up of the library finds them: when the leading
zeros of the `n + 1` coefficients lower `⌈n / 2⌉`, in the reversal check
(`Ratpoints.Setup.reversal`), which may also reverse the polynomial, and with the Sturm step on, by
the remainder chain (`Ratpoints.Sturm.chain`); between the last two it refuses malformed search
intervals (`Ratpoints.searchIntervals`). The options are normalized first
(`Ratpoints.Options.normalize`), the search intervals are `[-h, h]` when none are given, and the
Sturm step (`Ratpoints.sturmRegion`, `Ratpoints.Sturm.computeSturm`) narrows them to the intervals
where the polynomial may be `≥ 0`, or returns at once when it is negative on all of them and there
is no point at infinity. Otherwise it runs the search of the polynomial that the set-up hands on
(`Ratpoints.searchPoints`), which delivers no points when no class of the denominators modulo 64
admits a numerator and there is no point at infinity, or when the curve has none modulo one of the
primes examined for the parameters `P`, and otherwise the points of height at most `H` on
`y ^ 2 = F(x, z)` in the search region (the denominators in the range of the options and `x / z` in
a search interval) to the callback (`Ratpoints.Delivery`), the points at infinity first and then,
unless the Sturm step has left no interval, those of the denominators in the order of the loop of
the search (`Ratpoints.Sieve.Shape`), increasing unless it runs over the divisors of the leading
coefficient, found by the sieve on the bit arrays of words with the moduli, primes, prime powers and
products of them, and the array size of `P`, each mapped back to the caller's curve after a
reversal, until a call of the callback stops the search, and returns the data of the callback, the
count, the sum of the values that the calls returned, the bits of the flags that the program reads
after the search and the search intervals as the search leaves them (`Ratpoints.Outcome`). Under the
options of the output it delivers only the points with `y ≥ 0` (`RATPOINTS_NO_Y`), or, each with
`y = 0`, the candidate at infinity and every numerator that passes the sieve, the test for common
factors and the third stage (`RATPOINTS_NO_CHECK`). `Ratpoints.findPoints c H P o` is the list of
what it delivers, by the callback that appends each point to an array (`Ratpoints.appendPoint`).
What `sieving_info` computes for the search, the loop of the tables of the primes examined with the
exit and the forbidden divisors, the further forbidden divisors and the sieve entries of the moduli
with their reciprocals and the tables of their rows, is `Ratpoints.sievingInfo`.

## Main definitions

* `Ratpoints.Options`, `Ratpoints.Options.normalize`: the options of a search, and as the search
  normalizes them.
* `Ratpoints.makeModulus?`, `Ratpoints.sievingInfo`: the sieve entry of a modulus, and the tables,
  the forbidden divisors and the sieve entries of the moduli of a search, with their reciprocals and
  the tables of their rows.
* `Ratpoints.Outcome`: what a search returns and writes back.
* `Ratpoints.searchIntervals`, `Ratpoints.sturmRegion`: the search intervals of a search, the
  default one or the caller's checked, and the Sturm step on them.
* `Ratpoints.sieving`, `Ratpoints.searchPoints`: the sieving of a search, and the search of the
  polynomial that the set-up hands on.
* `Ratpoints.findPointsWith`: the search with a callback.
* `Ratpoints.findPoints`: the points, as a list.
-/

@[expose] public section

namespace Ratpoints

/-- The options of a search that change the refusals, the order of the output or what is delivered,
with the defaults of a run of the program without options: whether the set-up may reverse the
polynomial (`Ratpoints.Setup.reversal`), the depth of the Sturm step, negative for none, the two
options of the output, whether the numerators that pass the sieve are delivered without the exact
check (`RATPOINTS_NO_CHECK`) and whether only the point with `y ≥ 0` of a pair is delivered
(`RATPOINTS_NO_Y`), and the search region: the search intervals and the range of the denominators.
Unlike the sieving parameters (`Ratpoints.Params`), which change neither the points nor their order,
these change the order of the output (the reversal, and the range of the denominators, which also
decides the shape of the divisors), the refusals (the Sturm step, the search intervals, and without
the Sturm step the reversal check), what is delivered (the options of the output and the search
region; under the first of the output, the reversal, the parameters and the Sturm step change it
too), and with its intervals what the search writes back (`Ratpoints.Outcome`).

C: `main.c:348`, `main.c:352`, `ratpoints.h:359`, `ratpoints.h:363-364`, `ratpoints.h:369`,
`ratpoints.h:403-405`

Deviation: a structure for the fields of `ratpoints_args` that hold these options: Booleans for the
bits `RATPOINTS_NO_CHECK`, `RATPOINTS_NO_Y` and `RATPOINTS_NO_REVERSE` of the flags, `noCheck` and
`noY` true when their bits are set, `reverse` true when `RATPOINTS_NO_REVERSE` is clear, so that all
three defaults are those of the cleared flags (`main.c`, line 352); of the other bits of the flags,
which `main.c` clears with these, the Jacobi switch is that of the sieving parameters
(`Ratpoints.Params.jacobi`), and `RATPOINTS_VERBOSE` is kept by the program in
`Ratpoints.Cli.Output.verbose` for the report of `main.c`, the report of the library under it being
instrumentation; an integer for `args->sturm`; a list of pairs of doubles (`Ratpoints.Double`) for
the array `domain` of the type `ratpoints_interval` with the number `num_inter` of its intervals,
the empty list for `num_inter = 0`, so that no number of intervals is negative and the room in the
array for the intervals of the Sturm step is no concern of the caller; integers for the `long`s
`b_low` and `b_high`; of the fields that share their lines in `ratpoints.h`, `sp1` and `sp2` are
those of the sieving parameters (`Ratpoints.Params.sp1`, `Ratpoints.Params.sp2`), `sp3` is the
choice of the third stage (stage I), and `num_primes` and `max_forbidden` are read by the options of
the program (`Ratpoints.SieveOptions`). -/
structure Options where
  /-- Whether the set-up may reverse the polynomial: the bit `RATPOINTS_NO_REVERSE` of the flags
  clear, which the option `-k` of the program sets and `-K` clears. -/
  reverse : Bool := true
  /-- `args->sturm`, the depth of the Sturm step, negative for none: `Ratpoints.defaultSturm`
  unless the option `-s` of the program sets `-1` or `-S` a depth; a depth above
  `Ratpoints.Double.mantDig + 2 = 55` is taken as `55` (`Ratpoints.Options.normalize`). -/
  sturm : Int := defaultSturm
  /-- The bit `RATPOINTS_NO_CHECK` of the flags, which the option `-x` of the program sets and `-X`
  clears: every numerator that passes the sieve is delivered, with `y = 0`, without the exact
  check. -/
  noCheck : Bool := false
  /-- The bit `RATPOINTS_NO_Y` of the flags, which the option `-y` of the program sets and `-Y`
  clears: of a pair of points `(x : ±y : z)` only the one with `y ≥ 0` is delivered. -/
  noY : Bool := false
  /-- `args->domain` with `args->num_inter`, the search intervals `[l, u]` of the caller, which the
  options `-l` and `-u` of the program give, and `[]` for none, the whole line: they must have
  `l ≤ u`, be increasing and strictly apart and have no NaN end, and may have infinite ends. -/
  domain : List (Double × Double) := []
  /-- `args->b_low`, the least denominator, which the option `-dl` of the program gives; values
  below `1` stand for `1`. -/
  bLow : Int := 1
  /-- `args->b_high`, the largest denominator, which the option `-du` of the program gives; values
  below `1` and above the height bound stand for the height bound. -/
  bHigh : Int := 0

/-- The options `o` as `find_points_work_1` normalizes the fields of the arguments that hold them,
for the height bound `H ≥ 1`: the least denominator `1` for one below `1`, the largest denominator
`H` for one below `1` or above `H`, the depth of the Sturm step capped at
`Ratpoints.Double.mantDig + 2 = 55`, beyond which the ends of the intervals that the step keeps
would not all be doubles, and the switch of the reversal off (`RATPOINTS_NO_REVERSE_AUTO`) when the
caller gives search intervals or the range of the denominators is not `1, …, H`.

C: `find_points.c:4640-4641`, `find_points.c:4659-4661`, `find_points.c:4678-4689`,
`ratpoints.h:421-424`

Deviation: the normalized options returned, for the fields of the arguments that the C code
normalizes in place and restores in `find_points_work` (lines 4542-4545 and 4560-4563), which the
caller does not see either; no clamp of the number of the search intervals, which a list cannot make
negative; the bit `RATPOINTS_NO_REVERSE_AUTO`, which the C code sets in the flags and the reversal
check tests with `RATPOINTS_NO_REVERSE` (line 4739), as the switch `reverse` cleared; integers for
the `long`s. -/
def Options.normalize (o : Options) (H : Nat) : Options :=
  let bLow : Int := if o.bLow < 1 then 1 else o.bLow
  let bHigh : Int := if o.bHigh < 1 ∨ H < o.bHigh then H else o.bHigh
  let sturm : Int := if Double.mantDig + 2 < o.sturm then Double.mantDig + 2 else o.sturm
  { o with
    bLow, bHigh, sturm
    reverse := o.reverse && !(!o.domain.isEmpty || 1 < bLow || bHigh < H) }

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

/-- What a search gives its caller, `find_points` with the callback `process` and its data `info`:
the data `info` that the callback leaves, the count `total` of the search, the sum of the values
that the calls of the callback returned, which `find_points` returns, and the bits of the flags of
the arguments that the search writes back and the program `ratpoints` reads after it (its message
7): `RATPOINTS_REVERSED`, set when the reversal check has reversed the polynomial,
`RATPOINTS_USE_SQUARES`, set for odd degree and `|c_d| = 1`, when the denominators are the squares,
and `RATPOINTS_USE_SQUARES1`, set for odd degree otherwise when the divisor set-up has succeeded
(`Ratpoints.Setup.setupUs1`), when the denominators are divisors of `c_d` times squares; the search
sets the last two before its exits after the Sturm step and before the points at infinity, and the
return after the Sturm step (`find_points.c:4889`) comes only for an even degree, where neither is
set, so that they are written back on every path that does not refuse the input; and the search
intervals as the search leaves them, which the program prints after the search (its message 8):
`[-h, h]` when the caller gives none (`Ratpoints.searchIntervals`), narrowed by the Sturm step to
the intervals it leaves, in the coordinates of the polynomial searched (`Ratpoints.sturmRegion`),
and none when it leaves none.

C: `ratpoints.h:377`, `ratpoints.h:414`, `ratpoints.h:416-417`

Deviation: a structure for what the C code returns and writes back into the arguments: the data of
the callback, which the caller has behind its pointer `info`, the count, which `find_points` returns
as a `long` that also carries its error codes (`Ratpoints.findPointsWith` returns the refusals
apart), and Booleans for three bits of `args->flags`; nothing else written back: neither the
reversed coefficients and the degree (`args->cof`, `args->degree`), which nothing reads after the
search; nor the other internal bits of the flags, `RATPOINTS_CHECK_DENOM`, `RATPOINTS_USE_JACOBI`
and `RATPOINTS_NO_REVERSE_AUTO`, which the program does not read either, the bits of the input
coming back as the caller set them (`find_points.c:4606`), which the program takes from its own
options and settings (`Ratpoints.Options`, `Ratpoints.Params.jacobi`,
`Ratpoints.Cli.Output.verbose`); nor the numbers of the moduli used (`sp1_used`, `sp2_used`,
`sp3_used`; stage I); the search intervals as a list, for the array `args->domain` and the number
`args->num_inter` that the search writes back and the program reads after it. -/
structure Outcome (σ : Type) where
  /-- The data of the callback after the search. -/
  info : σ
  /-- The count, the sum of the values that the calls of the callback returned. -/
  total : Int
  /-- `RATPOINTS_REVERSED`: the reversal check has reversed the polynomial. -/
  reversed : Bool
  /-- `RATPOINTS_USE_SQUARES`: the denominators are the squares. -/
  useSquares : Bool
  /-- `RATPOINTS_USE_SQUARES1`: the denominators are divisors of `c_d` times squares. -/
  useSquares1 : Bool
  /-- `args->domain` with `args->num_inter`: the search intervals as the search leaves them. -/
  domain : List (Double × Double)

/-- The search intervals of a search for the height bound `H ≥ 1` and the intervals `domain` of the
caller, as `find_points_work_1` deals with them, or none for intervals that it refuses
(`RATPOINTS_BAD_ARGS`): for none given, the default interval `[-h, h]`, `h` the double of `H`
(`Ratpoints.Double.ofInt64`), moved up to the next double (`Ratpoints.Double.nextUp`) when it is
below `2 ^ 63` and below `H`, so that it holds every `x = a / b` of the search; otherwise the
intervals given, refused when an interval has not `l ≤ u` or does not begin above the end of the
one before it, the comparisons of doubles (`Ratpoints.Double.le`, `Ratpoints.Double.lt`), so that a
NaN end is refused too.

C: `find_points.c:4829`, `find_points.c:4831-4855`

Deviation: the intervals returned as a list, for the array `domain` and the number `num_inter` of
the arguments, which the C code sets to the default interval in place; none for the code
`RATPOINTS_BAD_ARGS` that the C code returns (`Ratpoints.Refusal.badArgs`); the test of a null
pointer `domain` (line 4830) excluded, the interface of the library; natural numbers for the `long`
index. -/
def searchIntervals (H : Nat) (domain : List (Double × Double)) :
    Id (Option (List (Double × Double))) := do
  if domain.isEmpty then
    let h := Double.ofInt64 H.toInt64
    let h := if h.lt .twoPow63 && h.toInt64 < H.toInt64 then h.nextUp else h
    return some [(h.neg, h)]
  let iv := domain.toArray
  for n in [0:iv.size] do
    if !iv[n]!.1.le iv[n]!.2 || 0 < n && !iv[n - 1]!.2.lt iv[n]!.1 then return none
  return some domain

/-- The Sturm step of `find_points_work_1` on the polynomial `f` with the coefficient list `c` of
degree `d` that the reversal check hands on, with the depth `sturm`, for the search intervals `dom`
(`Ratpoints.searchIntervals`): with the step off, `sturm < 0`, the intervals as they are; with it
on, the refusal `Ratpoints.Refusal.notSquarefree` when the remainder chain of `f` is none
(`Ratpoints.Sturm.computeSturm`), and otherwise the intervals that the step leaves, when there are
some; when there are none, `f` negative on all of them, none for an even `d` whose leading
coefficient is not a square (`Ratpoints.Setup.isSquare`), when there is no point at infinity either,
so that the search returns at once, and otherwise no intervals with the flag `sturm_empty` set, so
that the search delivers the points at infinity only.

C: `find_points.c:4857-4892`

Deviation: the result as a refusal, none, or the intervals with the flag `sturm_empty`, for the
codes that the C code returns at lines 4879 and 4889, the intervals that it leaves in `domain` with
their number `num_inter`, and its local flag `sturm_empty`; the square test `lcfsq` made on the
polynomial searched (`Ratpoints.Setup.isSquare`), where the C code computes it before the reversal
check (line 4634) and clears it in case 2 (line 4770): the same value for an even degree, the only
one that reads it; no failure for lack of memory (`RATPOINTS_NO_MEMORY`), which the model cannot
meet; no output under `RATPOINTS_VERBOSE`. -/
def sturmRegion (c : List Int) (d : Nat) (sturm : Int) (dom : List (Double × Double)) :
    Id (Except Refusal (Option (List (Double × Double) × Bool))) := do
  if sturm < 0 then return .ok (some (dom, false))
  match ← Sturm.computeSturm c d sturm.toNat dom.toArray with
  | none => return .error .notSquarefree
  | some iv =>
    if !iv.isEmpty then return .ok (some (iv.toList, false))
    if d % 2 = 1 || Setup.isSquare (c.getD d 0) then return .ok (some ([], true))
    return .ok none

open Sieve in
/-- The sieving of the search of the polynomial with the coefficient list `c` of degree `d`, for the
height `H`, the parameters `P` and the flags `fl`, delivered to the callback `process` on the
delivery `r`, whose flag `quit` is clear, with the sieve entries `entries` of the moduli of `P` and
their reciprocals `magics`, the classes `cls` of the denominators modulo 64 with the word `db` of
those that admit a numerator, and the store `store` of the tables of rows, from
`Ratpoints.sievingInfo`: an array of `Ratpoints.Sieve.numPackings` rows of one offset for each sieve
entry, and the row offsets of the classes in it, with the inverses of the strides in the entries
(`Ratpoints.Sieve.classOffsets`); the shape of the run and the bounds of the search intervals
`domain` (`Ratpoints.Sieve.runSetup`, with the flags of the denominators `useSquares`, `us1`,
`checkDenom` and `useJacobi`, the forbidden divisors `forb` and `forbVal` and the largest
denominator `bHigh`); and the points of the denominators `bLow, …, bHigh` of the shape in the
search intervals (`Ratpoints.Sieve.sieveRun`) with the cut points `P.sp1` and `P.sp2` and pieces of
at most `Ratpoints.Params.arraySizeAt P H` bit arrays, which returns when the callback stops the
search. This is the block that the C code introduces as "now do the sieving".

C: `find_points.c:4573`, `find_points.c:5116`, `find_points.c:5119`, `find_points.c:5132`,
`find_points.c:5137-5139`, `find_points.c:5167`

Deviation: a function of its own for the block of the sieving in `find_points_work_1`; the range of
the denominators and the search intervals as arguments, for the fields `b_low`, `b_high`, `domain`
and `num_inter` of the arguments that `run_setup` and the run read; the flags of the
denominators as Booleans and an option, for the bits of `args->flags` and the arrays
`args->den_info` and `args->divisors` that `run_setup` reads; the array of the row offsets made with
zeros, for the array on the stack, whose entries the C code leaves unset until `class_offsets`
writes them, with one offset in each row for each sieve entry of the run, those of its three stages,
for the `sp3_max` entries with the reserve of further primes (stage I); the delivery passed and
returned, for the pointers `info` and `wk.quit` and the count `total`; no sieving thread made
(`worker_init`, `worker_clear`), whose fields the components that the run calls take as arguments,
and no pool of threads (stage I); no failure for lack of memory, which the model cannot meet. -/
def sieving {σ : Type} (process : Int → Int → Int → σ → Answer σ) (c : List Int) (d H : Nat)
    (P : Params) (fl : CheckFlags) (useSquares : Bool)
    (us1 : Option (List Setup.DenInfo × List Nat)) (checkDenom useJacobi : Bool)
    (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal) (entries : List SieveEntry)
    (magics : Array Nat) (cls : Vector NumClass 64) (db : UInt64) (store : RowStore)
    (bLow bHigh : Nat) (domain : List (Double × Double)) (r : Delivery σ) :
    Id (Delivery σ) := do
  let offsets := Array.replicate ((← numPackings cls) * max entries.length 1) 0
  let (cls, entries, offsets) ← classOffsets cls entries offsets
  let (shape, iv) ←
    runSetup useSquares us1 checkDenom useJacobi forb forbVal (c.getD d 0) H bHigh domain
  sieveRun process c d H (P.arraySizeAt H) fl P.sp1 P.sp2 entries magics cls offsets db shape iv
    bLow bHigh store r

open Sieve in
/-- The search of the polynomial with the coefficient list `c` of degree `d` that the set-up hands
on, for the height bound `H`, the parameters `P` and the flags `fl`, over the denominators
`bLow, …, bHigh` and the search intervals `domain` that the Sturm step leaves, with its flag
`sturmEmpty` (`Ratpoints.sturmRegion`), delivered to the callback `process` on the delivery `r`,
whose flag `quit` is clear. First the flags of the tests on the denominators: the checked loop for
even degree; the Jacobi test for even degree, `c_d` not a square (`Ratpoints.Setup.isSquare`) and
the switch `P.jacobi`; the squares for odd degree and `|c_d| = 1`; and for odd degree otherwise the
divisors of `c_d` up to `bHigh` (`Ratpoints.Setup.setupUs1`). Then the 2-adic information
(`Ratpoints.Sieve.twoAdic`) with the packings of the classes of the denominators modulo 64 and the
word `den_bits` of the classes that admit a numerator (`Ratpoints.Sieve.numClasses`), and nothing
delivered when no class admits a numerator and there is no point at infinity, as there is for odd
degree or `c_d` a square. Then the tables of the primes examined, the forbidden divisors for even
degree and the sieve entries of the moduli of `P` and their reciprocals (`Ratpoints.sievingInfo`),
with the flag of the `long`s (`Ratpoints.Setup.useCLong`), and nothing delivered when the curve has
no points modulo one of the primes examined; the checked loop off when there are no forbidden
divisors and no Jacobi test. Then the points at infinity (`Ratpoints.Sieve.pointsAtInfinity`), after
which the search returns if the callback has stopped it or the Sturm step has left no interval, and
then the sieving (`Ratpoints.sieving`), each point mapped by `Ratpoints.Sieve.swapPoint` when
`fl.reversed` is set. It returns the data and the count of the delivery with the bits of the flags
of the search that the program reads and the search intervals (`Ratpoints.Outcome`): `fl.reversed`,
the squares, the success of the divisor set-up, and `domain`. For well-formed parameters,
`1 ≤ H < 2 ^ 63`, `1 ≤ bLow`, `bHigh ≤ H`, `d` the degree of `c` and `1 ≤ d`, the flags of the
output clear, a callback that does not stop the search, well-formed search intervals and
`sturmEmpty` false, the calls are those of the points at infinity followed by the points of the
brute-force reference over the denominators of the search from `bLow` to `bHigh`
(`Ratpoints.searchDens`) whose `x / z` lies in a search interval, in the order of its loop,
increasing unless the shape is that of the divisors, each mapped when `fl.reversed` is set, also
when an exit is taken; with `sturmEmpty` set, only the points at infinity.

C: `find_points.c:2793-2795`, `find_points.c:4588-4589`, `find_points.c:4595-4596`,
`find_points.c:4602`, `find_points.c:4603-4604`, `find_points.c:4607`, `find_points.c:4900-4943`,
`find_points.c:4948`, `find_points.c:4954-4963`, `find_points.c:4992-5012`,
`find_points.c:5100-5106`, `ratpoints.h:415`, `ratpoints.h:418`

Deviation: the arguments of `sieving_info` that serve the choice of the moduli (the mean number of
bits per word, whether the number of primes was left to the library, the 2-adic classes and the word
`den_bits`) are not modelled; the range of the denominators, the search intervals and the flag
`sturm_empty` as arguments, for the fields `b_low`, `b_high`, `domain` and `num_inter` of the
arguments and the local flag of `find_points_work_1`; the flags of the denominators as Booleans, for
the bits of `args->flags`; the forbidden divisors and the divisors of the leading coefficient with
their records as lists, for the arrays `args->forb_ba`, `args->forbidden`, `args->den_info` and
`args->divisors` of the arguments, and the sieve entries as a list, for the array
`args->sieve_list` that `sieving_info` fills and `class_offsets` reads; the square test `lcfsq` of
line 4906 made on the polynomial searched (`Ratpoints.Setup.isSquare`), where the C code computes it
before the reversal check (line 4634) and clears it in case 2 (line 4770): the same value for an
even degree, the only one that reads it; the store of the tables of rows that
`Ratpoints.sievingInfo` returns handed to the sieving as a value, for the arrays `sieve` of the
entries of `args->sieve_list`; the test on `point_at_infty` of the 2-adic exit recomputed, as
`Ratpoints.Sieve.pointsAtInfinity` decides it; the exits return the delivery as it came, with
nothing delivered, where `sieving_info` returns the prime and `find_points_work_1` the count `0`;
the delivery passed and returned, for the pointer `info`, the local flag `quit` of
`find_points_work_1` and the count `total`, and the result with the bits of the flags written back
and the search intervals (`Ratpoints.Outcome`), for the bits that `find_points_work_1` sets in
`args->flags` and the intervals that it leaves in `args->domain`; no failure for lack of memory,
which the model cannot meet; no output under `RATPOINTS_VERBOSE` or `DEBUG`. -/
def searchPoints {σ : Type} (process : Int → Int → Int → σ → Answer σ) (c : List Int) (d H : Nat)
    (P : Params) (fl : CheckFlags) (bLow bHigh : Nat) (domain : List (Double × Double))
    (sturmEmpty : Bool) (r : Delivery σ) :
    Id (Outcome σ) := do
  let lcf := c.getD d 0
  let mut checkDenom := d % 2 == 0
  let useJacobi := d % 2 == 0 && !Setup.isSquare lcf && P.jacobi
  let useSquares := d % 2 == 1 && lcf.natAbs == 1
  let us1 ← if d % 2 == 1 && lcf.natAbs != 1 then Setup.setupUs1 c d bHigh else pure none
  let done (r : Delivery σ) : Outcome σ :=
    ⟨r.info, r.total, fl.reversed, useSquares, us1.isSome, domain⟩
  let (cls, db) ← numClasses (← twoAdic c d)
  if db == 0 && !(d % 2 == 1 || Setup.isSquare lcf) then return done r
  let some (entries, magics, forb, forbVal, store) ←
      sievingInfo c d (Setup.useCLong c d) checkDenom P bHigh | return done r
  if forb.isEmpty && forbVal.isEmpty && !useJacobi then checkDenom := false
  let r := pointsAtInfinity process c d fl r
  if r.quit then return done r
  if sturmEmpty then return done r
  return done (← sieving process c d H P fl useSquares us1 checkDenom useJacobi forb forbVal
    entries magics cls db store bLow bHigh domain r)

/-- The search of `find_points` with the callback `process` and its data `info`: the points of
height at most `H` on `y ^ 2 = F(x, z)` for the coefficient list `c` in the search region of the
options `o`, found by the sieve with the moduli and the array size of the parameters `P`, delivered
to `process`. More than `Ratpoints.maxDegree + 1` coefficients, fewer than two, and the height bound
`0` or one of `2 ^ 63` or more, which is not a `long` (`Ratpoints.fitsLong`), are refused, in the
order of the program (errors 3, 5 and 4); then, as not squarefree (error 8), a list whose leading
zeros lower `⌈n / 2⌉`, where `n + 1` is its length, that is `⌈d / 2⌉ < ⌈n / 2⌉` for the degree
`d = Ratpoints.BruteForce.degree c`. The options are normalized (`Ratpoints.Options.normalize`: the
range of the denominators within `1, …, H`, the depth of the Sturm step at most `55`, and the switch
of the reversal off for a search region); then comes the reversal check
(`Ratpoints.Setup.reversal`), which may refuse the form too or reverse the polynomial; then the
search intervals (`Ratpoints.searchIntervals`), `[-h, h]` for none, and the refusal
`Ratpoints.Refusal.badArgs` (error 9) for intervals without `l ≤ u`, not increasing and strictly
apart, or with a NaN end; then the Sturm step (`Ratpoints.sturmRegion`), which with `0 ≤ o.sturm`
refuses the form when the remainder chain of the polynomial searched is none
(`Ratpoints.Sturm.chain`), that is when that polynomial has a repeated factor, returns at once, with
nothing delivered and no interval, when that polynomial is negative on the search intervals and has
no point at infinity, and otherwise narrows the search intervals to those where it may be `≥ 0`.
Otherwise the search of the polynomial that the reversal check hands on (`Ratpoints.searchPoints`),
with the flag of the reversal and the options of the output `o.noCheck` and `o.noY`
(`Ratpoints.CheckFlags`), the normalized range of the denominators and the search intervals that the
Sturm step leaves, from the data `info`, the count `0` and the flag `quit` clear, delivers the
points to `process` (under `o.noCheck` the candidate at infinity and the numerators that pass the
sieve, the test for common factors and the third stage, each with `y = 0`), none when no class of
the denominators modulo 64 admits a numerator and there is no point at infinity, or when the curve
has no points modulo one of the primes examined, and else the points at infinity first, then, unless
the Sturm step has left no interval, those of the denominators in the order of the loop of the
search (`Ratpoints.Sieve.sieveRun`) whose `x / z` lies in a search interval, each mapped back to the
caller's curve after a reversal, until a call of `process` stops the search; it returns the data
that `process` leaves, the count, the bits of the flags that the program reads after the search and
the search intervals as the search leaves them (`Ratpoints.Outcome`).

C: `find_points.c:4523-4528`, `find_points.c:4546`, `find_points.c:4557-4559`,
`find_points.c:4564-4565`, `find_points.c:4567-4571`, `find_points.c:4578-4585`,
`find_points.c:4606`, `find_points.c:4624-4633`, `find_points.c:4658`, `find_points.c:5219-5220`,
`find_points.c:5226-5229`, `find_points.c:5235`, `find_points.c:5241-5242`, `ratpoints.h:362`,
`ratpoints.h:409-411`, `ratpoints.h:427-430`, `ratpoints.h:436-437`, `ratpoints.h:441-442`

Deviation: one function for `find_points`, `find_points_work` and `find_points_work_1`, which the
library calls in turn. The refusals of the program, in its order and with its errors
(`Ratpoints.Refusal`), returned apart from the outcome, for the negative codes of the library
(`RATPOINTS_NON_SQUAREFREE` and `RATPOINTS_BAD_ARGS`; `RATPOINTS_WORK_LENGTH_TOO_SMALL` and
`RATPOINTS_NO_MEMORY` cannot arise), which share the `long` that `find_points` returns with the
count: fewer than two coefficients are refused on the length of `c`, as the program refuses them,
where the library refuses an empty list as a negative degree and one coefficient as the degree 0 (a
longer list of degree 0 fails the test of the leading zeros first); and the height bound, which the
program checks before it calls the library, comes before the test of the leading zeros, which the
library makes first, so that `5 0` with `H = 0` is error 4, as the program gives it. The degree with
the leading zeros dropped is `Ratpoints.BruteForce.degree c`. A natural number `H` for the `long`
`height` of the arguments (`ratpoints.h:362`), so that `H = 0` stands for the heights below 1 that
line 4658 refuses; a height that is not a `long`, `2 ^ 63` or more, is refused with error 4, as the
program refuses it when it reads the height (`Ratpoints.Cli.heightBound`), where the library cannot
be given one, its height being a `long`. A list for the array of GMP integers and its scratch
integers `work`, with nothing written back to the caller but the data of the callback, the count,
three bits of the flags and the search intervals (`Ratpoints.Outcome`), so that there is no state
between calls and the reset of the flags clears nothing; the return of line 4889, which leaves the
flags of the squares clear and no interval, as the outcome with the data `info`, the count `0`, the
flag of the reversal and no interval, the flag being in fact clear there (the cases 1 and 3 of the
reversal check leave an odd degree, and in case 2 the reversed polynomial takes the value `c_d > 0`
at `0`, in the default interval, which the Sturm step keeps); the callback a function that returns
what the call gives (`Ratpoints.Answer`), and its data a value, for the pointer `info`; the options
of the output as fields of the options (`Ratpoints.Options`), copied into the flags of the check
(`Ratpoints.CheckFlags`) with the flag of the reversal, for the bits of `args->flags` that the mask
of line 4606 keeps; the points at infinity and the square test of the leading coefficient are
decided where they are used (`Ratpoints.Sieve.pointsAtInfinity`, `Ratpoints.Setup.reversal`,
`Ratpoints.sturmRegion`, `Ratpoints.searchPoints`); the test of the `long`s
(`Ratpoints.Setup.useCLong`), which the C code makes between the reversal check and the search
intervals, made by the search, where it is used; no failure for lack of memory, which the model
cannot meet; no output under `RATPOINTS_VERBOSE`. -/
def findPointsWith {σ : Type} (c : List Int) (H : Nat) (P : Params) (o : Options)
    (process : Int → Int → Int → σ → Answer σ) (info : σ) :
    Except Refusal (Outcome σ) :=
  if maxDegree + 1 < c.length then .error .tooManyCoefficients
  else if c.length < 2 then .error .tooFewCoefficients
  else if H = 0 ∨ !fitsLong H then .error .incorrectHeight
  else
    let d := BruteForce.degree c
    if (d + 1) / 2 < c.length / 2 then .error .notSquarefree
    else
      let o' := o.normalize H
      match Setup.reversal o'.reverse c d with
      | .error e => .error e
      | .ok (c', d', rev) =>
        match Id.run (searchIntervals H o.domain) with
        | none => .error .badArgs
        | some dom =>
          match Id.run (sturmRegion c' d' o'.sturm dom) with
          | .error e => .error e
          | .ok none => .ok ⟨info, 0, rev, false, false, []⟩
          | .ok (some (dom, empty)) => .ok (Id.run (searchPoints process c' d' H P
              { reversed := rev, noCheck := o.noCheck, noY := o.noY } o'.bLow.toNat
              o'.bHigh.toNat dom empty ⟨info, 0, false⟩))

/-- The points that the search with the parameters `P` and the options `o`, by default those of a
run of the program without options, delivers for the coefficient list `c` and the height `H`, as a
list in their order: the search of `Ratpoints.findPointsWith` with the callback that appends each
point `(x, y, z)` to an array and never stops the search (`Ratpoints.appendPoint`), from the empty
array, or its refusal. With the options of the output clear these are the points of height at most
`H` on `y ^ 2 = F(x, z)` in the search region of `o` (`z = 0`, or `bLow ≤ z ≤ bHigh` after the
normalization and `x / z` in a search interval): the points at infinity first, then those of the
denominators in the order of the loop of the search, each mapped back to the caller's curve after a
reversal; with `o.noY` those of them with `y ≥ 0`; and with `o.noCheck`, where there are points at
infinity, `(a, 0, b)` for the candidate at infinity, then the numerators that pass the sieve, the
test for common factors and the third stage, of the denominators of the same range and with `x / z`
in a search interval as the Sturm step leaves them, each as `(x, 0, z)`, mapped back after a
reversal. It models no C code: it is `Ratpoints.findPointsWith` with the appending callback of the
model. -/
def findPoints (c : List Int) (H : Nat) (P : Params) (o : Options := {}) :
    Except Refusal (List (Int × Int × Int)) :=
  (findPointsWith c H P o appendPoint #[]).map (·.info.toList)

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
`Ratpoints.numPrimes` primes among which the moduli are chosen; the search with a callback
(`Ratpoints.findPointsWith`), with a callback that stops at its `k`-th call for every `k`, a stop at
the first point at infinity at the heights `10 ^ 12` and `2 ^ 63 - 1`, and the bits of the flags
written back as `ratpoints` reports them; the options of the output (`{ noY := true }`,
`{ noCheck := true }`), against the output of `ratpoints` under `-y` and, with the moduli pinned,
under `-x`; the search region and the Sturm step against `find_points` of the pinned library, with
the search intervals that it leaves, and the refusals of malformed search intervals; and the
refusals in the order of the program, the coefficients before the height bound and the height bound
before the leading zeros, for the height bound `0` and for `2 ^ 63`, the least height that is not a
`long`, while `2 ^ 63 - 1` passes on to the test of the leading zeros. -/

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
    (Id.run (searchPoints appendPoint c 4 30 ⟨[9], 0, 1, 1, 64, true, 0⟩ {} 1 30
      ((Id.run (searchIntervals 30 [])).getD []) false ⟨#[], 0, false⟩)).info.isEmpty

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
    let iv := Id.run (Sieve.exactBounds ((Id.run (searchIntervals 300 [])).getD []) 300 300)
    (List.range' 1 40).all fun b ↦ cls[b % 64]!.bits == 0 || [1, 3].all fun A ↦
      let cl := cls[b % 64]!
      let bp := Sieve.fillBpList b cl.k (entries.take 7) (mgs.take 7)
      let surv : Vector Bool (2 * 300 + 1) := .ofFn fun i ↦
        nb[b % 64]!.toBitVec.getLsbD ((i.val + 64 * 5 - 300) % 64) &&
          Sieve.survives entries b ((i.val : Int) - 300)
      let ref := (Id.run (Sieve.checkDen c d 300 b surv)).toList
      [false, true].all fun rev ↦
        (Id.run (Sieve.sift appendPoint c d 300 A b { reversed := rev } 3 (entries.take 7)
          (mgs.take 7) bp cl offsets (entries.drop 7) (mgs.drop 7) iv store
          ⟨#[], 0, false⟩)).1.info.toList == if rev then ref.map Sieve.swapPoint else ref
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
        (Id.run (Sieve.sift appendPoint c 3 H 1 b { reversed := rev } 3 (entries.take 7)
          (mgs.take 7) bp cl offsets (entries.drop 7) (mgs.drop 7)
          (Id.run (Sieve.exactBounds ((Id.run (searchIntervals H [])).getD []) H.toInt64
            H.toInt64)) store
          ⟨#[], 0, false⟩)).1.info.toList == if rev then ref.map Sieve.swapPoint else ref
  | none => false

-- The array size 1, which `arraySizeAt` rounds up to the chunk 16, at heights around the multiples
-- of 64 and of `rbaLength`, with five moduli in the three stages: each class runs as one piece of
-- at most 4 bit arrays, the piece cut at `wHigh`, fewer than the chunk, so that the chunked first
-- stage runs only its tail legs; the low and the high mask fall on the same piece, and the stride 1
-- has no low mask when `H` is a multiple of `rbaLength`. Whole chunks are in the examples of
-- `Ratpoints.Model.FirstStage`. Several pieces and the masks on different pieces are in the
-- examples of `sift` (pieces of one, two and three bit arrays at `H = 300`,
-- `Ratpoints.Model.Sieve`) and of the run (the array size 1, `Ratpoints.Model.Denominators`), and
-- through `findPoints` in the differential tests, whose runs at the heights 2000, 5000 and 30000
-- and in the suite `test4high` have pieces of whole chunks.
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
    (Id.run (searchPoints appendPoint c d 10 defaultParams { reversed := true } 1 10
      ((Id.run (searchIntervals 10 [])).getD []) false ⟨#[], 0, false⟩)).info.toList == pts

-- Curves without points modulo 3, 5 and 7, for which `ratpoints c 30 -q` prints nothing: the table
-- of one of the default moduli is none, and the search returns no points, with either flag.
#guard [[20, 6, -14, 12, -10], [-2, -20, 7, 15, 2], [20, 7, -18, 0, 3]].all fun c ↦
  (defaultParams.moduli.mapM (Id.run <| Sieve.examinePrime? c 4 · (Setup.useCLong c 4))).isNone &&
    [false, true].all fun rev ↦ (Id.run (searchPoints appendPoint c 4 30 defaultParams
      { reversed := rev } 1 30 ((Id.run (searchIntervals 30 [])).getD []) false
      ⟨#[], 0, false⟩)).info.isEmpty

-- The 2-adic exit: no class of the denominators of `2 0 3` admits a numerator modulo 64, and there
-- is no point at infinity, so that `ratpoints '2 0 3' 300000 -q` prints nothing at once.
#guard (findPoints [2, 0, 3] 300000 defaultParams).toOption == some []

-- The tables of the 53 primes of the default build: each nonzero residue times its entry in the
-- table of inverses is 1, and the table of squares marks `(p + 1) / 2` residues.
#guard (primeTable.toList.take numPrimes).all fun p ↦
  let inv := Sieve.inversesMod p
  (List.range' 1 (p - 1)).all (fun r ↦ inv[r]! * r % p == 1) &&
    (Sieve.squaresMod p).count true == (p + 1) / 2

-- The search with a callback: a callback that stops at its `k`-th call, with the weight `2` for
-- each, gets the first `k` points of `findPoints` and the count `2 k`, for the twelve points of
-- `1 0 126 0 441` at the height 30, the stop at infinity, after `+y`, and in the sieve; the
-- appending callback gets all twelve and the count 12.
#guard
  let c : List Int := [1, 0, 126, 0, 441]
  let stopAt (k : Nat) (x z y : Int) (pts : Array (Int × Int × Int)) :
      Answer (Array (Int × Int × Int)) := ⟨2, pts.size + 1 == k, pts.push (x, y, z)⟩
  match findPoints c 30 defaultParams, findPointsWith c 30 defaultParams {} appendPoint #[] with
  | .ok L, .ok o =>
    L.length == 12 && o.info.toList == L && o.total == 12 && (List.range' 1 13).all fun k ↦
      match findPointsWith c 30 defaultParams {} (stopAt k) #[] with
      | .ok o => o.info.toList == L.take k && o.total == 2 * min k 12
      | .error _ => false
  | _, _ => false

-- A stop at the first point at infinity returns before the sieve, at once also at the heights
-- `10 ^ 12` and `2 ^ 63 - 1`, as `ratpoints '1 0 1' 1000000000000 -q -1` prints `(1 : 1 : 0)` at
-- once.
#guard
  let stop1 (x z y : Int) (pts : Array (Int × Int × Int)) : Answer (Array (Int × Int × Int)) :=
    ⟨1, true, pts.push (x, y, z)⟩
  [10 ^ 12, 2 ^ 63 - 1].all fun H ↦
    match findPointsWith [1, 0, 1] H defaultParams {} stop1 #[] with
    | .ok o => o.info.toList == [(1, 1, 0)] && o.total == 1
    | .error _ => false

-- The bits of the flags written back, which `ratpoints c 20` reports after the points (its message
-- 7): the reversal for `-1 0 9`, `0 1 0 2` and `0 1 0 0 4`, the squares for `-2 0 0 1` and for the
-- reversed `0 1 0 2` and `0 1 0 0 4`, the divisors for `1 2`, and none for `1 0 126 0 441`.
#guard
  ([([-1, 0, 9], true, false, false), ([1, 2], false, false, true),
      ([-2, 0, 0, 1], false, true, false), ([0, 1, 0, 2], true, true, false),
      ([1, 0, 126, 0, 441], false, false, false), ([0, 1, 0, 0, 4], true, true, false)] :
      List (List Int × Bool × Bool × Bool)).all fun (c, rev, sq, sq1) ↦
    match findPointsWith c 20 defaultParams {} appendPoint #[] with
    | .ok o => o.reversed == rev && o.useSquares == sq && o.useSquares1 == sq1
    | .error _ => false

-- The options of the output, as `ratpoints '1 0 126 0 441' 200 -q -y` and
-- `ratpoints '1 0 126 0 441' 200 -q -x -n 15 -N 30 -p 30` print them: the points with `y ≥ 0`,
-- and, with the moduli pinned so that every prime of the table up to 127 sieves, the survivors,
-- which are the same `x` and `z` with `y = 0`; under both options the survivors; and for `0 1 2`
-- at 40, which ratpoints reverses, the first four survivors in the order of the reversed search,
-- `(0 : 1)` first, as `ratpoints '0 1 2' 40 -q -x -n 15 -N 30 -p 30` prints them.
#guard
  let pinned := sieveParams { numPrimes := 30, sp1 := 15, sp2 := 30 }
  let c : List Int := [1, 0, 126, 0, 441]
  let xz : List (Int × Int) := [(1, 0), (0, 1), (-1, 2), (1, 2), (-2, 21), (2, 21)]
  (findPoints c 200 defaultParams { noY := true }).toOption ==
      some [(1, 21, 0), (0, 1, 1), (-1, 31, 2), (1, 31, 2), (-2, 651, 21), (2, 651, 21)] &&
    (findPoints c 200 pinned { noCheck := true }).toOption ==
      some (xz.map fun (x, z) ↦ (x, 0, z)) &&
    (findPoints c 200 pinned { noCheck := true, noY := true }).toOption ==
      some (xz.map fun (x, z) ↦ (x, 0, z)) &&
    ((findPoints [0, 1, 2] 40 pinned { noCheck := true }).toOption.map
        fun L ↦ (L.take 4).map fun (x, _, z) ↦ (x, z)) ==
      some [(0, 1), (-1, 2), (-1, 1), (1, 2)]

-- The search region and the Sturm step against `find_points` of the pinned library, called by a C
-- program with the same arguments that prints the count, the bits written back, the points in
-- their order and the search intervals that the library leaves in `domain`, as bits: for each case
-- the coefficients, the height bound, the depth of the Sturm step, the switch of the reversal,
-- `RATPOINTS_NO_CHECK` (with the moduli pinned, `-p 30 -N 30`), `b_low`, `b_high`, the intervals
-- of the caller as bits, and the outcome. `-1 0 9`, reversed, searched on `[-3, 3]`, and with
-- `-k` on `[-10, -0.33203125] ∪ [0.33203125, 10]`; `0 1 0 2`, reversed unless a range of the
-- denominators other than `1, …, H` or a search interval is given (`RATPOINTS_NO_REVERSE_AUTO`);
-- `-1 0 0 0 -1`, negative everywhere, with nothing delivered and no interval (the return of
-- line 4889), also under `RATPOINTS_NO_CHECK`; `17 0 0 1` with the denominators from 4 to 9;
-- `-0.0` kept at the end of an interval; intervals that meet the region; the depths 200 (taken as
-- 55), 55 and 0; infinite ends; and `x ^ 3 - 1` and `x ^ 4 - 1` on intervals where they are
-- negative (`sturm_empty`: only the points at infinity, under `RATPOINTS_NO_CHECK` the candidate).
#guard
  let pinned := sieveParams { numPrimes := 30, sp2 := 30 }
  ([
    ([-1, 0, 9], 10, 10, true, false, 1, 0, [], 8, true, false, false, [(-1, 0, 3), (1, 3, 0),
        (1, -3, 0), (1, 0, 3), (-5, 12, 9), (-5, -12, 9), (5, 12, 9), (5, -12, 9)],
      [(0xc008000000000000, 0x4008000000000000)]),
    ([-1, 0, 9], 10, 10, false, false, 1, 0, [], 8, false, false, false, [(1, 3, 0), (1, -3, 0),
        (-1, 0, 3), (1, 0, 3), (-5, 12, 9), (-5, -12, 9), (5, 12, 9), (5, -12, 9)],
      [(0xc024000000000000, 0xbfd5400000000000), (0x3fd5400000000000, 0x4024000000000000)]),
    ([0, 1, 0, 2], 10, 10, true, false, 1, 0, [], 2, true, true, false, [(0, 0, 1), (1, 0, 0)],
      [(0x0000000000000000, 0x4024000000000000)]),
    ([0, 1, 0, 2], 10, 10, true, false, 1, 2, [], 2, false, false, true, [(1, 0, 0), (0, 0, 1)],
      [(0x0000000000000000, 0x4024000000000000)]),
    ([0, 1, 0, 2], 10, 10, true, false, 2, 0, [], 1, false, false, true, [(1, 0, 0)],
      [(0x0000000000000000, 0x4024000000000000)]),
    ([0, 1, 0, 2], 10, 10, true, false, 1, 10, [], 2, true, true, false, [(0, 0, 1), (1, 0, 0)],
      [(0x0000000000000000, 0x4024000000000000)]),
    ([0, 1, 0, 2], 10, 10, true, false, 1, 0,
      [(0xbff0000000000000, 0x3ff0000000000000)], 2, false, false, true, [(1, 0, 0), (0, 0, 1)],
      [(0x0000000000000000, 0x3ff0000000000000)]),
    ([-1, 0, 0, 0, -1], 10, 10, true, false, 1, 0, [], 0, false, false, false, [], []),
    ([-1, 0, 0, 0, -1], 10, 10, true, true, 1, 0, [], 0, false, false, false, [], []),
    ([0, 1, -100, 10], 10, 10, true, false, 1, 0, [], 2, true, true, false, [(0, 0, 1), (1, 0, 0)],
      [(0x0000000000000000, 0x3fba000000000000)]),
    ([17, 0, 0, 1], 300, 10, true, false, 4, 9, [], 7, false, true, false, [(1, 0, 0), (1, 66, 4),
        (1, -66, 4), (-8, 327, 9), (-8, -327, 9), (106, 3291, 9), (106, -3291, 9)],
      [(0xc004c00000000000, 0x4072c00000000000)]),
    ([1, 0, 1], 10, 3, true, false, 1, 0,
      [(0x8000000000000000, 0x3f80000000000000)], 4, false, false, false, [(1, 1, 0), (1, -1, 0),
        (0, 1, 1), (0, -1, 1)], [(0x8000000000000000, 0x3f80000000000000)]),
    ([1, 0, 126, 0, 441], 200, 10, true, false, 1, 0,
      [(0x0000000000000000, 0x3ff0000000000000)], 8, false, false, false, [(1, 21, 0), (1, -21, 0),
        (0, 1, 1), (0, -1, 1), (1, 31, 2), (1, -31, 2), (2, 651, 21), (2, -651, 21)],
      [(0x0000000000000000, 0x3ff0000000000000)]),
    ([36, 0, -49, 0, 14, 0, -1], 100, 10, true, false, 1, 0,
      [(0xc004000000000000, 0xbff8000000000000),
        (0x3ff8000000000000, 0x4004000000000000)], 2, false, false, false, [(-2, 0, 1), (2, 0, 1)],
      [(0xc004000000000000, 0xc000000000000000), (0x4000000000000000, 0x4004000000000000)]),
    ([1, 0, -5, 0, 1], 30, 200, true, false, 1, 0, [], 4, false, false, false, [(1, 1, 0),
        (1, -1, 0), (0, 1, 1), (0, -1, 1)], [(0xc03e000000000000, 0xc00182de8eff8f9e),
        (0xbfdd3d08d69b4a52, 0x3fdd3d08d69b4a52), (0x400182de8eff8f9e, 0x403e000000000000)]),
    ([1, 0, -5, 0, 1], 30, 55, true, false, 1, 0, [], 4, false, false, false, [(1, 1, 0),
        (1, -1, 0), (0, 1, 1), (0, -1, 1)], [(0xc03e000000000000, 0xc00182de8eff8f9e),
        (0xbfdd3d08d69b4a52, 0x3fdd3d08d69b4a52), (0x400182de8eff8f9e, 0x403e000000000000)]),
    ([1, 0, -5, 0, 1], 30, 0, true, false, 1, 0, [(0xfff0000000000000, 0xbff0000000000000),
        (0x3fd0000000000000, 0x7ff0000000000000)], 2, false, false, false, [(1, 1, 0), (1, -1, 0)],
      [(0xc3e0000000000000, 0xbff0000000000000), (0x3fd0000000000000, 0x43e0000000000000)]),
    ([1, 0, 1], 10, 10, true, false, 50, 3, [], 2, false, false, false, [(1, 1, 0), (1, -1, 0)],
      [(0xc024000000000000, 0x4024000000000000)]),
    ([-1, 0, 0, 1], 10, 10, true, false, 1, 0,
      [(0xc014000000000000, 0x0000000000000000)], 1, false, true, false, [(1, 0, 0)], []),
    ([-1, 0, 0, 1], 10, 10, true, true, 1, 0,
      [(0xc014000000000000, 0x0000000000000000)], 1, false, true, false, [(1, 0, 0)], []),
    ([-1, 0, 0, 0, 1], 10, 10, true, false, 1, 0,
      [(0xbfe0000000000000, 0x3fe0000000000000)], 2, false, false, false, [(1, 1, 0), (1, -1, 0)],
      []),
    ([-1, 0, 0, 0, 1], 10, 10, true, true, 1, 0,
      [(0xbfe0000000000000, 0x3fe0000000000000)], 1, false, false, false, [(1, 0, 0)], []),
    ([-1, 0, 0, 0, -1], 10, 10, true, true, 1, 0,
      [(0xbfe0000000000000, 0x3fe0000000000000)], 0, false, false, false, [], [])
    ] : List (List Int × Nat × Int × Bool × Bool × Int × Int × List (UInt64 × UInt64) ×
      Int × Bool × Bool × Bool × List (Int × Int × Int) × List (UInt64 × UInt64))).all
    fun (c, H, sturm, reverse, noCheck, bLow, bHigh, dom, total, rev, sq, sq1, pts, out) ↦
  let o : Options := {
    sturm, reverse, noCheck, bLow, bHigh, domain := dom.map fun (l, u) ↦ (⟨l⟩, ⟨u⟩) }
  match findPointsWith c H (if noCheck then pinned else defaultParams) o appendPoint #[] with
  | .ok r => r.total == total && r.reversed == rev && r.useSquares == sq && r.useSquares1 == sq1 &&
    r.info.toList == pts && r.domain.map (fun (l, u) ↦ (l.bits, u.bits)) == out
  | .error _ => false

-- The refusals of malformed search intervals (`RATPOINTS_BAD_ARGS`), as the library makes them: an
-- end that is a NaN, an interval with `l > u`, intervals that meet, also only at `-0.0` and `0.0`,
-- which are equal; the intervals are refused before the Sturm step finds `1 2 1` not squarefree.
#guard
  ([
    ([1, 0, 1], 10, 10, true, false, 1, 0, [(0x7ff8000000000000, 0x3ff0000000000000)], .badArgs),
    ([1, 0, 1], 10, 10, true, false, 1, 0, [(0x4000000000000000, 0x3ff0000000000000)], .badArgs),
    ([1, 0, 1], 10, 10, true, false, 1, 0, [(0xbff0000000000000, 0x3ff0000000000000),
        (0x3ff0000000000000, 0x4000000000000000)], .badArgs),
    ([1, 0, 1], 10, 10, true, false, 1, 0, [(0xbff0000000000000, 0x8000000000000000),
        (0x0000000000000000, 0x3ff0000000000000)], .badArgs),
    ([1, 2, 1], 10, 10, true, false, 1, 0, [(0x7ff8000000000000, 0x3ff0000000000000)], .badArgs)
    ] : List (List Int × Nat × Int × Bool × Bool × Int × Int × List (UInt64 × UInt64) ×
      Refusal)).all fun (c, H, sturm, reverse, noCheck, bLow, bHigh, dom, e) ↦
  let o : Options := {
    sturm, reverse, noCheck, bLow, bHigh, domain := dom.map fun (l, u) ↦ (⟨l⟩, ⟨u⟩) }
  match findPoints c H defaultParams o with | .error e' => e' == e | .ok _ => false

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
