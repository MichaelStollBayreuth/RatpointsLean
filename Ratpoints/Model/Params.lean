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
denominators read the bound on the forbidden divisors and the switch of the Jacobi test. The
parameters of the executable of the options (`Ratpoints.sieveParams`), which take the first primes
of the table by the counting rules of the options, are not called by the search.

## Main definitions

* `Ratpoints.modulusFactors`: the factors of a modulus over the primes of the table.
* `Ratpoints.Params`: the sieving parameters.
* `Ratpoints.Params.WF`: the parameters are well-formed.
* `Ratpoints.arraySizeAt`, `Ratpoints.Params.arraySizeAt`: at most how many bit arrays a piece of
  the numerators has, for a height bound.
* `Ratpoints.SieveOptions`: the values of the options of the program that tune the sieve.
* `Ratpoints.SieveOptions.normalize`: those values as the search normalizes them.
* `Ratpoints.sieveParams`: the parameters that these values give, with the defaults and caps of
  ratpoints and its rules for the sizes of the stages; `Ratpoints.defaultParams`, those of a run
  without options.
-/

@[expose] public section

namespace Ratpoints

/-- The factors of `m` over the first `Ratpoints.numPrimes` primes of `Ratpoints.primeTable`, as
`add_moduli` finds them, and the cofactor that is left: for the primes `p` of the table in turn,
while the cofactor is above `1`, a cofactor below `p ^ 2`, which has no odd prime factor below `p`
and so, for odd `m`, is a prime, is looked up among the primes from `p` on and, when it is one of
them, taken as a factor with the exponent `1`, which leaves the cofactor `1`, and otherwise left as
it is; else `p` is divided off as often as it divides, giving the factor `(pn, e)` with the position
`pn` of `p` in the table and the exponent `e ≥ 1`. The factorization is complete exactly when the
cofactor is `1`; the factors are in the order of the table. The table holds no `2`, so an even
modulus never factors completely, as `add_moduli` offers odd `m` only.

It models no C code of its own: the explicit sieve entry of a modulus given by its value
(`Ratpoints.makeModulus?`) uses it, while the choice of the moduli factors a candidate as
`add_moduli` does (`Ratpoints.factorCandidate`, `Ratpoints.takeFactor`): over the primes looked at,
refusing a modulus with more than `Ratpoints.maxFactors` factors, a prime factor whose prime says
nothing, a prime-power factor whose tables say nothing or a prime beyond the first 64, with the
densities of the factors and the mask of their primes, and recording the codes of the factors, the
position of the prime for a prime factor and the index of the tables of a prime power for a
prime-power factor, where this function returns the positions and the exponents. The factorization
is complete for the moduli of well-formed parameters (`Ratpoints.Params.WF`,
`Ratpoints.snd_run_modulusFactors_eq_one`). -/
def modulusFactors (m : Nat) : Id (List (Nat × Nat) × Nat) := do
  let mut rest := m
  let mut fac : Array (Nat × Nat) := #[]
  for pn in [0:numPrimes] do
    if rest ≤ 1 then break
    let p := primeTable[pn]!
    if rest < p * p then
      if let some pn' := (List.range' pn (numPrimes - pn)).find? (primeTable[·]! == rest) then
        fac := fac.push (pn', 1)
        rest := 1
      break
    if rest % p = 0 then
      let mut e := 0
      while rest % p = 0 do
        rest := rest / p
        e := e + 1
      fac := fac.push (pn, e)
  return (fac.toList, rest)

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

/-- The parameters `P` are well-formed: every modulus is above `1`, below `Ratpoints.maxPrimeEven`
and a product of powers of primes among the first `Ratpoints.numPrimes` of `Ratpoints.primeTable`,
each of its divisors above `1` being divisible by one of them, so that its factorization over the
table (`Ratpoints.modulusFactors`) is complete (`Ratpoints.snd_run_modulusFactors_eq_one`); the
moduli of the third stage are primes of the table; at most `Ratpoints.numPrimes` primes are
examined; and the cut points are in order and within the list of moduli. The table holds no `2`, so
an even modulus is never well-formed, as ratpoints offers odd moduli only. -/
structure Params.WF (P : Params) : Prop where
  /-- Every modulus is above `1`, below `Ratpoints.maxPrimeEven` and a product of powers of primes
  among the first `Ratpoints.numPrimes` of `Ratpoints.primeTable`: each of its divisors above `1` is
  divisible by one of them. -/
  modulus : ∀ m ∈ P.moduli, 1 < m ∧ m < maxPrimeEven ∧
    ∀ q > 1, q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q
  /-- The moduli of the third stage, from the position `sp2` on, are primes of
  `Ratpoints.primeTable`. -/
  mem_primeTable_of_mem_drop : ∀ m ∈ P.moduli.drop P.sp2, m ∈ primeTable
  /-- At most `Ratpoints.numPrimes` primes are examined. -/
  examined_le : P.examined ≤ numPrimes
  /-- The first stage ends no later than the second. -/
  sp1_le_sp2 : P.sp1 ≤ P.sp2
  /-- The second stage ends within the list of moduli. -/
  sp2_le_length : P.sp2 ≤ P.moduli.length

-- The divisors of a modulus `m > 1` are at most `m`, which makes the condition on them decidable.
instance Params.instDecidableWF (P : Params) : Decidable P.WF :=
  decidable_of_iff ((∀ m ∈ P.moduli, 1 < m ∧ m < maxPrimeEven ∧
      ∀ q ≤ m, 1 < q → q ∣ m → ∃ pn < numPrimes, primeTable[pn]! ∣ q) ∧
      (∀ m ∈ P.moduli.drop P.sp2, m ∈ primeTable) ∧ P.examined ≤ numPrimes ∧ P.sp1 ≤ P.sp2 ∧
      P.sp2 ≤ P.moduli.length)
    ⟨fun ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨fun m hm ↦ ⟨(h1 m hm).1, (h1 m hm).2.1, fun q hq hd ↦
        (h1 m hm).2.2 q (Nat.le_of_dvd (Nat.zero_lt_of_lt (h1 m hm).1) hd) hq hd⟩, h2, h3, h4, h5⟩,
      fun ⟨h1, h2, h3, h4, h5⟩ ↦ ⟨fun m hm ↦ ⟨(h1 m hm).1, (h1 m hm).2.1, fun q _ hq hd ↦
        (h1 m hm).2.2 q hq hd⟩, h2, h3, h4, h5⟩⟩

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
fields of its `ratpoints_args`: `-p`, `-n`, `-N`, `-R`, `-A`, `-P` and `-F` give C `long`s, which
are `-1`, as in `main.c`, when the option is absent; `-r`, `-U`, `-C`, `-Q` and `-W` give doubles,
`-1.0` when absent; `-j` switches the Jacobi test off and `-J` on again; and the array size is
`Ratpoints.defaultArraySize`, which the program sets. The program reads `-r -R -U -C -A -Q -W`
with stage I, and leaves those fields at their defaults until then.

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

/-- The sieving parameters that the options `o` give, with the defaults and caps of ratpoints and
the rules by which it counts the moduli of its stages, where these do not depend on the curve: the
number `q` of the primes looked at is the value `k ≥ 0` of `-p` or else
`Ratpoints.defaultNumPrimes`, at most `Ratpoints.numPrimes`, and the first `q` primes of the table
are examined; the moduli are the first primes of `Ratpoints.primeTable`, at most the first `L` of
them, `L = q` when `-p` is given and `L = Ratpoints.numPrimes` when it is absent or negative. For
the value `n ≥ 0` of `-n` and the value `N ≥ 0` of `-N`, the latter capped at `q`, the first stage
ends at `s₁ = min(n, N)` and the second at `s₂ = max(s₁, N)`; without `-N` (absent or negative), the
first stage ends at `s₁ = min(n, L)` and the second at `s₂ = min(s₁ + Ratpoints.sp2Extra, L)`;
without `-n`, the first stage ends at `s₁ = min(Ratpoints.defaultSp1, L)`, also with `-N`. The third
stage has the next `min(P, L - s₂)` primes for the value `P ≥ 0` of `-P`, and without `-P` the rest
of the first `q` primes, if any. At most `F` forbidden divisors are tested for the value `F ≥ 0` of
`-F` or else `Ratpoints.defaultMaxForbidden`, at most as many as the table has primes; the Jacobi
test runs unless `-j` is the last of `-j` and `-J`; and a piece of the numerators has at most as
many bit arrays as the array size of the options, `0` (for `Ratpoints.defaultArraySize`) for one
`≤ 0` (`Ratpoints.arraySizeAt`), which the program sets to `Ratpoints.defaultArraySize`
(`Ratpoints.Cli.run`), the default of the field of the options. The fields that
the run of the search does not read are fixed values: the end of the third stage the number of
moduli, the primes looked at those examined, the estimates of the run and the cost of a check `1.0`,
and the words of the first correction `2 ^ 64 - 1`, no correction; and none of the tuning fields of
the options (`-r -R -U -C -A -Q -W`) is read, which the choice of the moduli reads
(`Ratpoints.SieveOptions.tuning`, `Ratpoints.checkRelOf`, `Ratpoints.adaptStart`).
In the default build, a run without options has 11 moduli in the first stage, 22 in the first two
and 30 in all (`Ratpoints.defaultParams`).

It models no C code of its own: the search makes the choice of the moduli (`Ratpoints.sievingInfo`)
and does not call it; these parameters stand for that choice in these ways: the defaults and caps of
the options applied here again, which the search applies before (lines 4643-4649, 4655-4656 and
4662-4665, `Ratpoints.SieveOptions.normalize`, in `Ratpoints.findPointsWork`) and which leave
normalized options as they are, and the counts of the stages by these rules, for the choice of the
moduli: the number of the primes to look at and its raise (lines 2566 and 2693-2705,
`Ratpoints.TableLoop`, `Ratpoints.raiseLimit`), the offset of the second stage (lines 2571-2572,
2599, 2808 and 2815, `Ratpoints.SieveOptions.tuning`, `Ratpoints.choiceEstimate`), the stages that
ratpoints takes from the pool of its candidates (among them lines 2503, 2845-2846, 2864-2869, 2922,
2949, 2973-2975, 2980 and 3015, `Ratpoints.takeEntries`, `Ratpoints.firstStages`,
`Ratpoints.thirdStage`), the number of primes that its third stage wants (lines 2926-2928,
`Ratpoints.thirdOf`) and the end of the third stage (line 3017, `Ratpoints.choiceEnd`); the moduli
are the first primes of the table, in increasing order, where ratpoints ranks the primes by what
they say about the curve and adds composite moduli (`Ratpoints.sievingInfo`), and takes the entries
of its stages from that ranking, skipping a modulus that shares a prime with one taken
(`Ratpoints.takeEntries`); it leaves the primes that say nothing out of its pool (lines 1764-1765
and 2613-2622), and those that say only that the numerator is prime to the denominator stay in the
pool of the first two stages without counting toward the primes that it looks for (`n_weak`, line
2704) and leave the pool of the third stage with the composite moduli not taken (lines 2873-2890 and
2999-3000); so the counts that the options fix, of the first stage under `-n`, of the first two
stages under `-n` and `-N` (or `-n` and `-U 0` without `-R`) and of all the moduli under `-n`, `-N`
and `-P`, bound those of ratpoints, which can be smaller, while where an option is absent ratpoints
can take more moduli in a stage or fewer (no bound on a stage for `-N` without `-n`, nor for `-P`
alone); without `-n`, the first stage ends at `Ratpoints.defaultSp1`, the fixed choice of the
header, where ratpoints chooses the end from the curve by its costs (`Ratpoints.takeEntries`);
without `-N`, the second stage adds the flat offset `Ratpoints.sp2Extra`, as ratpoints does under
`-U 0` (`phase_2_offset` for `u0 = 0`, `Ratpoints.phase2Offset`), where it otherwise scales the
offset by the length of the run, and these parameters ignore `-R`, whose value ratpoints takes in
place of `RATPOINTS_SP2_EXTRA` (lines 2571-2572 and 2808, `Ratpoints.SieveOptions.tuning`); without
`-P`, the third stage is the rest of the first `q` primes, where ratpoints takes the primes of its
pool in increasing order of their density `r`, the most selective first, stops by its cost rule
(`Ratpoints.thirdStage`) and may look past the first `q` when `-p` is absent; the primes examined
are the first `q`, where ratpoints, when `-p` is absent, looks at further primes while its pool is
short of the moduli that its first two stages want, and later for its third stage, `-p` being a hard
limit of the first two stages (line 2693) as of the third (line 2980), and the entries of given
moduli examine the primes of their moduli beyond the first `q` (`Ratpoints.makeModulus?`); no
correction of the moduli during the run, which ratpoints makes (`Ratpoints.Sieve.adaptPrimes`);
natural numbers for the `long`s, so that the sums of the counts cannot overflow. -/
def sieveParams (o : SieveOptions) : Params :=
  let q := min (if o.numPrimes < 0 then defaultNumPrimes else o.numPrimes.toNat) numPrimes
  let lim := if o.numPrimes < 0 then numPrimes else q
  let n2 : Option Nat := if o.sp2 < 0 then none else some (min o.sp2.toNat q)
  let s1 := if o.sp1 < 0 then min defaultSp1 lim else min o.sp1.toNat (n2.getD lim)
  let s2 := match n2 with
    | some t => max s1 t
    | none => min (s1 + sp2Extra) lim
  let n := if o.sp3Extra < 0 then max s2 q else min (s2 + o.sp3Extra.toNat) lim
  { moduli := primeTable.toList.take n
    examined := q
    sp1 := s1
    sp2 := s2
    maxForbidden :=
      min (if o.maxForbidden < 0 then defaultMaxForbidden else o.maxForbidden.toNat) primeTable.size
    jacobi := o.jacobi
    arraySize := if o.arraySize ≤ 0 then 0 else o.arraySize.toNat
    lookedAt := q
    sp3 := (primeTable.toList.take n).length
    adaptAt := 0xFFFFFFFFFFFFFFFF }

/-- The sieving parameters of a run without options (`Ratpoints.sieveParams` of the defaults): the
first `Ratpoints.defaultNumPrimes` primes of `Ratpoints.primeTable` examined, at most
`Ratpoints.numPrimes`; the first `Ratpoints.defaultSp1` primes of the table in the first stage and
the next `Ratpoints.sp2Extra` in the second, the end of each stage at most `Ratpoints.numPrimes`,
and the rest of the examined primes, if any, in the third; at most `Ratpoints.defaultMaxForbidden`
forbidden divisors, the Jacobi test, and pieces of at most `Ratpoints.defaultArraySize` bit arrays.
With the values of the default build, the first stage has 11 moduli, the first two 22 and all three
30. -/
def defaultParams : Params := sieveParams {}

/-! ### Examples -/

-- A run without options: 11 moduli in the first stage and 22 in the first two, as
-- `ratpoints c H -v -n 11 -U 0` reports for each of the curves of the guard of the stage sizes
-- below, and 30 in all.
#guard defaultParams.moduli == primeTable.toList.take 30 && defaultParams.examined == 30 &&
  defaultParams.sp1 == 11 && defaultParams.sp2 == 22 && defaultParams.maxForbidden == 64 &&
  defaultParams.jacobi && defaultParams.arraySize == 256 && defaultParams.sp3 == 30 &&
  defaultParams.lookedAt == 30 && defaultParams.adaptAt == 0xFFFFFFFFFFFFFFFF

#guard defaultParams.WF

-- `-p 100 -N 40 -n 50 -P 5 -F 200 -j`: 53 primes examined, both cut points at 40, five primes in
-- the third stage, 171 forbidden divisors.
#guard
  let P := sieveParams
    { numPrimes := 100, sp1 := 50, sp2 := 40, sp3Extra := 5, maxForbidden := 200, jacobi := false }
  P.examined == 53 && P.moduli.length == 45 && P.sp1 == 40 && P.sp2 == 40 &&
    P.maxForbidden == 171 && !P.jacobi

-- The sizes of the stages that `ratpoints c H -v` reports with the same options, and with `-U 0`
-- where `-N` is absent (the flat offset `Ratpoints.sp2Extra`), for each of the curves
-- `1 2 3 -4 5 6 1`, `1 0 126 0 441`, `3 2 -1 12`, `1 -3 2 5 -7 1 4 -2 3` and the second and the
-- last of `testdata-many.h`, at the heights 500 and 20000: the moduli in the first stage, in the
-- first two and in all, for `-n 3 -N 5 -P 2`, `-n 11 -N 22 -P 8`, `-n 50 -N 40 -P 5 -p 100`,
-- `-n 3 -P 10 -p 53`, `-n 100 -N 0 -P 10`, `-n 0 -P 8`, `-n 5 -N 10 -P 3`, `-n 20 -N 10 -P 8 -p 53`
-- and `-n 1 -N 25 -P 60 -p 0`.
#guard ([({ sp1 := 3, sp2 := 5, sp3Extra := 2 }, (3, 5, 7)),
    ({ sp1 := 11, sp2 := 22, sp3Extra := 8 }, (11, 22, 30)),
    ({ sp1 := 50, sp2 := 40, sp3Extra := 5, numPrimes := 100 }, (40, 40, 45)),
    ({ sp1 := 3, sp3Extra := 10, numPrimes := 53 }, (3, 14, 24)),
    ({ sp1 := 100, sp2 := 0, sp3Extra := 10 }, (0, 0, 10)),
    ({ sp1 := 0, sp3Extra := 8 }, (0, 11, 19)),
    ({ sp1 := 5, sp2 := 10, sp3Extra := 3 }, (5, 10, 13)),
    ({ sp1 := 20, sp2 := 10, sp3Extra := 8, numPrimes := 53 }, (10, 10, 18)),
    ({ sp1 := 1, sp2 := 25, sp3Extra := 60, numPrimes := 0 }, (0, 0, 0))] :
      List (SieveOptions × Nat × Nat × Nat)).all fun (o, s) ↦
  let P := sieveParams o
  (P.sp1, P.sp2, P.moduli.length) == s

-- `-p 10 -n 4 -P 3`: the first ten primes, the first stage ends at 4 and the second at 10, with no
-- prime left for the third stage, since `-p` is a hard limit.
#guard
  let P := sieveParams { numPrimes := 10, sp1 := 4, sp3Extra := 3 }
  P.moduli == primeTable.toList.take 10 && P.sp1 == 4 && P.sp2 == 10 && decide P.WF

-- Well-formed parameters with the prime power 9, and with the products 15 = 3 · 5 and
-- 245 = 5 · 7 ^ 2 and the prime powers 27 and 243, the primes 3, 5 and 7 among the first ten
-- examined, 251 not; and well-formedness that fails: 9 in the third stage, a modulus that is not
-- below `maxPrimeEven` (257, a prime of the table, 3 · 103), an even modulus, the modulus 1, and
-- more primes examined than `numPrimes`.
#guard
  let P (moduli : List Nat) (examined sp1 sp2 : Nat) : Params :=
    { moduli, examined, lookedAt := examined, sp1, sp2, sp3 := moduli.length, maxForbidden := 64,
      jacobi := true, adaptAt := 0xFFFFFFFFFFFFFFFF }
  decide (Params.WF (P [3, 9] 0 2 2)) && decide (Params.WF (P [15, 245, 27, 243, 251, 7] 10 2 4)) &&
    ([([3, 9], 0, 0, 0), ([257], 0, 1, 1), ([309], 0, 1, 1), ([6], 0, 1, 1), ([1], 0, 1, 1),
      ([3], 54, 1, 1)] : List (List Nat × Nat × Nat × Nat)).all fun (moduli, examined, sp1, sp2) ↦
    !decide (Params.WF (P moduli examined sp1 sp2))

-- The factors of moduli over the table: positions and exponents, and the cofactor; for 6, 771 and
-- 1024 the cofactor below the square of the next prime, 6, 257 and 1024, is no prime among the
-- first `numPrimes`.
#guard [9, 15, 245, 231, 255, 251, 1, 0, 6, 3 * 257, 2 ^ 10].map (Id.run <| modulusFactors ·) ==
  [([(0, 2)], 1), ([(0, 1), (1, 1)], 1), ([(1, 1), (2, 2)], 1), ([(0, 1), (2, 1), (3, 1)], 1),
    ([(0, 1), (1, 1), (5, 1)], 1), ([(52, 1)], 1), ([], 1), ([], 0), ([], 6),
    ([(0, 1)], 257), ([], 1024)]

-- The array size: `2 ⌈H / 64⌉` rounded up to a multiple of the chunk 16, up to the default 256,
-- which it reaches at `H = 8129` and, rounded up, at `H = 7681`; the default for the field `0`;
-- fields of 10, rounded up, and of 48, a multiple of the chunk; and the cap `2 ^ 20`, a multiple
-- of the chunk, from `H = 2 ^ 25 + 1` on, which the rounding up does not pass.
#guard [1, 64, 65, 1000, 7680, 7681, 8128, 8129, 100000].map defaultParams.arraySizeAt ==
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

-- The parameters of the executable of the normalized options, with the number of primes `-1` when
-- the caller left it to the library, as the search takes them, are those of the options as the
-- caller gave them, for the numbers of primes `-1`, `0`, `10` and `100`, the cut points `-1`, `0`,
-- `4`, `10`, `40` and `60` and the numbers of primes of the third stage `-1`, `0`, `5` and `60`.
#guard ([-1, 0, 10, 100] : List Int).all fun np ↦ ([-1, 0, 4, 10, 40, 60] : List Int).all fun n1 ↦
  ([-1, 0, 4, 10, 40, 60] : List Int).all fun n2 ↦ ([-1, 0, 5, 60] : List Int).all fun n3 ↦
    let s : SieveOptions := { numPrimes := np, sp1 := n1, sp2 := n2, sp3Extra := n3 }
    let P := sieveParams s
    let P' := sieveParams (if s.numPrimes < 0 then { s.normalize with numPrimes := -1 }
      else s.normalize)
    (P'.moduli, P'.examined, P'.sp1, P'.sp2, P'.sp3, P'.maxForbidden, P'.arraySize) ==
      (P.moduli, P.examined, P.sp1, P.sp2, P.sp3, P.maxForbidden, P.arraySize)

end Ratpoints

end
