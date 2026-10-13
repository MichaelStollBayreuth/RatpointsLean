/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Constants

-- The `#guard` examples use the constants at compile time.
meta import Ratpoints.Model.Constants

/-!
# The sieving parameters

The free choices of the sieve, which the theorems quantify over: which moduli it uses, in which
order and in which stage, at most how many forbidden divisors of the denominators it tests, whether
it runs the Jacobi test, and at most how many bit arrays it treats at a time. ratpoints chooses the
moduli and their stages from the curve and corrects the choice during the run, and takes the other
choices from its options or its defaults (the program passes the array size
`Ratpoints.defaultArraySize`); none of this changes the points found or their order, since a modulus
only removes candidates that are not points, the pieces of the numerators follow one another in
increasing order, a test on the denominators removes only denominators without points, and the two
shapes of the loop over the denominators between which these choices decide, the words of 64
denominators and every denominator, both run in increasing order. So the model takes the choice as
an input, and the theorems hold for every well-formed choice. The sieve reads the moduli and the
array size, the loop of the tables reads the number of primes examined, which give the exit and the
first forbidden divisors, and the tests on the denominators read the bound on the forbidden divisors
and the switch of the Jacobi test.

## Main definitions

* `Ratpoints.modulusFactors`: the factors of a modulus over the primes of the table.
* `Ratpoints.Params`: the sieving parameters.
* `Ratpoints.Params.WF`: the parameters are well-formed.
* `Ratpoints.Params.arraySizeAt`: at most how many bit arrays a piece of the numerators has, for a
  height bound.
* `Ratpoints.SieveOptions`: the values of the options of the program that set the parameters.
* `Ratpoints.sieveParams`: the parameters that these values give, with the defaults and caps of
  ratpoints; `Ratpoints.defaultParams`, those of a run without options.
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

C: `find_points.c:2362`, `find_points.c:2365`, `find_points.c:2369-2386`,
`find_points.c:2396-2400`

Deviation: the positions in the table and the exponents as a list of pairs, for the codes `fac` of
the factors and their count `nf`, with no bound `RP_MAX_FACTORS` on their number and no bound 64 on
the positions (no mask of the primes involved, which serves the choice of the moduli), and with the
position of the prime for a prime power, where the code of a prime power is that of its entry
`pws[idx]`, which `add_moduli` examines when it first needs it (lines 2387-2395, modelled by
`Ratpoints.makeModulus?`); no densities `r` of the factors (lines 2384 and 2396) and no refusal of a
prime factor whose prime says nothing (line 2383), which serve the choice of the moduli (stage I),
`Ratpoints.makeModulus?` taking the table of such a factor from the loop of the tables; the cofactor
returned, for the flag `ok` and the test that the factorization is complete (line 2400), which it is
for the moduli of well-formed parameters (`Ratpoints.Params.WF`,
`Ratpoints.snd_run_modulusFactors_eq_one`); the prime below `p ^ 2` looked up by `List.find?`, for
the loop that steps over the primes below it; the first `Ratpoints.numPrimes` primes of the table,
for the primes looked at, `prime[0]` to `prime[pn_lim - 1]`; natural numbers for the `long`s. -/
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

/-- The sieving parameters: the free choices of the sieve, which the theorems quantify over. The
moduli are cut into three stages: the first `sp1` of them, then those up to `sp2`, then the
rest. -/
structure Params where
  /-- The moduli in the order of the stages: primes of `Ratpoints.primeTable`, powers of them and
  products of such powers, below `Ratpoints.maxPrimeEven`. -/
  moduli : List Nat
  /-- How many primes the loop of the tables examines, the first of `Ratpoints.primeTable`: the
  curve has no points when it has none modulo one of them, they give the first forbidden divisors,
  and the moduli take the tables of those among their prime factors. -/
  examined : Nat
  /-- The end of the first stage, a position in `Ratpoints.Params.moduli`. -/
  sp1 : Nat
  /-- The end of the second stage, a position in `Ratpoints.Params.moduli`; the third stage is
  the rest. -/
  sp2 : Nat
  /-- At most how many forbidden divisors of the denominators are tested. -/
  maxForbidden : Nat
  /-- Whether the Jacobi test on the denominators may run: it runs when also the polynomial
  searched, after the reversal check, has even degree and a leading coefficient that is not a
  square. -/
  jacobi : Bool
  /-- At most how many bit arrays a piece of the numerators has, the field `array_size` of the
  arguments of the library; `0` for `Ratpoints.defaultArraySize`. -/
  arraySize : Nat := 0

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

/-- At most how many bit arrays a piece of the numerators has for the height bound `H`: the field
`arraySize` of the parameters `P`, or `Ratpoints.defaultArraySize` for `0`, capped at `2 ⌈H / 64⌉`
and at `Ratpoints.maxArraySize`; at least 1 for `H ≥ 1` (`Ratpoints.Params.one_le_arraySizeAt`).

C: `rp-private.h:87`, `find_points.c:4666-4677`

Deviation: a `Nat` for the `long` field, so that only `0` stands for the default, which the library
takes for every value `≤ 0`; no rounding up to a multiple of the chunk, which is one bit array in
the build of the model (`RATPOINTS_CHUNK`, stage F4). -/
def Params.arraySizeAt (P : Params) (H : Nat) : Nat :=
  min (min (if P.arraySize = 0 then defaultArraySize else P.arraySize) (2 * ((H + 63) / 64)))
    maxArraySize

/-- The values of the options of ratpoints that set the sieving parameters, as the program reads
them into the fields of its `ratpoints_args`: `-p`, `-n`, `-N`, `-P` and `-F` give C `long`s,
which are `-1`, as in `main.c`, when the option is absent; `-j` switches the Jacobi test off and
`-J` on again.

C: `main.c:337-338`, `main.c:344`, `main.c:349-350`, `main.c:352`

Deviation: integers for the `long`s of the fields, and a Boolean for the bit `RATPOINTS_NO_JACOBI`
of the flags, which `main.c` clears with the others; the bit of the reversal is in
`Ratpoints.Options`. -/
structure SieveOptions where
  /-- The value of `-p`: how many primes are taken. -/
  numPrimes : Int := -1
  /-- The value of `-n`: the end of the first stage. -/
  sp1 : Int := -1
  /-- The value of `-N`: the end of the second stage. -/
  sp2 : Int := -1
  /-- The value of `-P`: how many primes the third stage adds. -/
  sp3Extra : Int := -1
  /-- The value of `-F`: at most how many forbidden divisors are tested. -/
  maxForbidden : Int := -1
  /-- Whether the Jacobi test runs: `false` when `-j` is the last of `-j` and `-J`. -/
  jacobi : Bool := true

/-- The sieving parameters that the options `o` give, with the defaults and caps of ratpoints: `q`
primes are taken, the value `k ≥ 0` of `-p` or else `Ratpoints.defaultNumPrimes`, at most
`Ratpoints.numPrimes`, and the first `q` primes of the table are examined; the second stage ends at
`s₂ = min(N, q)` and the first at `min(n, s₂)` for the values `N` of `-N` and `n` of `-n`, at `q`
and at `s₂` when these are absent or negative; the moduli are the first `min(q + P, numPrimes)`
primes of `Ratpoints.primeTable` for the value `P ≥ 0` of `-P`, the first `q` when it is absent or
negative; at most `F` forbidden divisors are tested for the value `F ≥ 0` of `-F` or else
`Ratpoints.defaultMaxForbidden`, at most as many as the table has primes; the Jacobi test runs
unless `-j` is the last of `-j` and `-J`; and a piece of the numerators has at most
`Ratpoints.defaultArraySize` bit arrays, the array size that the program sets when it reads the
arguments and again before the search.

C: `find_points.c:2566`, `find_points.c:4643-4649`, `find_points.c:4655-4656`,
`find_points.c:4662-4665`, `main.c:221-222`, `main.c:347`

Deviation: the moduli are the first primes of the table, in increasing order, where ratpoints ranks
the primes by what they say about the curve (`sieving_info`), looks past the first `q` when `-p` is
absent and the curve needs it, chooses the cut points from the curve when `-n` or `-N` is absent or
negative, and corrects the choice during the run (`adapt_primes`); the third stage is the rest of
the list after `s₂`, where ratpoints takes up to `P` primes after `s₂`, or primes up to all
`Ratpoints.numPrimes` when `-P` is absent or negative, from those it has looked at, which are among
the first `q` when `-p` is given (line 2980, `may_extend = 0`); the model examines the primes of the
third stage beyond the first `q` when it makes their entries (`Ratpoints.makeModulus?`); the number
`examined` of the primes examined, which stands for `pn_lim` of `sieving_info` (line 2566), is `q`,
as in ratpoints when `-p` is given, where it looks at more primes when `-p` is absent and the choice
of the moduli needs them. -/
def sieveParams (o : SieveOptions) : Params :=
  let q := min (if o.numPrimes < 0 then defaultNumPrimes else o.numPrimes.toNat) numPrimes
  let sp2 := if o.sp2 < 0 then q else min o.sp2.toNat q
  { moduli := primeTable.toList.take
      (if o.sp3Extra < 0 then q else min (q + o.sp3Extra.toNat) numPrimes)
    examined := q
    sp1 := if o.sp1 < 0 then sp2 else min o.sp1.toNat sp2
    sp2
    maxForbidden :=
      min (if o.maxForbidden < 0 then defaultMaxForbidden else o.maxForbidden.toNat) primeTable.size
    jacobi := o.jacobi
    arraySize := defaultArraySize }

/-- The sieving parameters of a run without options (`Ratpoints.sieveParams` of the defaults): the
first `Ratpoints.defaultNumPrimes` primes of `Ratpoints.primeTable` (at most
`Ratpoints.numPrimes`), all in the first stage, at most `Ratpoints.defaultMaxForbidden` forbidden
divisors, the Jacobi test, and pieces of at most `Ratpoints.defaultArraySize` bit arrays. -/
def defaultParams : Params := sieveParams {}

/-! ### Examples -/

#guard defaultParams.moduli == primeTable.toList.take 30 && defaultParams.examined == 30 &&
  defaultParams.sp1 == 30 && defaultParams.sp2 == 30 && defaultParams.maxForbidden == 64 &&
  defaultParams.jacobi && defaultParams.arraySize == 256

#guard defaultParams.WF

-- `-p 100 -N 40 -n 50 -P 5 -F 200 -j`: 53 primes, both cut points at 40, 171 forbidden divisors.
#guard
  let P := sieveParams
    { numPrimes := 100, sp1 := 50, sp2 := 40, sp3Extra := 5, maxForbidden := 200, jacobi := false }
  P.moduli.length == 53 && P.sp1 == 40 && P.sp2 == 40 && P.maxForbidden == 171 && !P.jacobi

-- `-p 10 -n 4 -P 3`: 13 primes, the first stage ends at 4 and the second at 10.
#guard
  let P := sieveParams { numPrimes := 10, sp1 := 4, sp3Extra := 3 }
  P.moduli == primeTable.toList.take 13 && P.sp1 == 4 && P.sp2 == 10 && decide P.WF

-- Well-formed parameters with the prime power 9, and with the products 15 = 3 · 5 and
-- 245 = 5 · 7 ^ 2 and the prime powers 27 and 243, the primes 3, 5 and 7 among the first ten
-- examined, 251 not; and well-formedness that fails: 9 in the third stage, a modulus that is not
-- below `maxPrimeEven` (257, a prime of the table, 3 · 103), an even modulus, the modulus 1, and
-- more primes examined than `numPrimes`.
#guard decide (Params.WF ⟨[3, 9], 0, 2, 2, 64, true, 0⟩) &&
  decide (Params.WF ⟨[15, 245, 27, 243, 251, 7], 10, 2, 4, 64, true, 0⟩)
#guard [⟨[3, 9], 0, 0, 0, 64, true, 0⟩, ⟨[257], 0, 1, 1, 64, true, 0⟩,
    ⟨[309], 0, 1, 1, 64, true, 0⟩, ⟨[6], 0, 1, 1, 64, true, 0⟩, ⟨[1], 0, 1, 1, 64, true, 0⟩,
    ⟨[3], 54, 1, 1, 64, true, 0⟩].all
  fun P : Params ↦ !decide P.WF

-- The factors of moduli over the table: positions and exponents, and the cofactor; for 6, 771 and
-- 1024 the cofactor below the square of the next prime, 6, 257 and 1024, is no prime among the
-- first `numPrimes`.
#guard [9, 15, 245, 231, 255, 251, 1, 0, 6, 3 * 257, 2 ^ 10].map (Id.run <| modulusFactors ·) ==
  [([(0, 2)], 1), ([(0, 1), (1, 1)], 1), ([(1, 1), (2, 2)], 1), ([(0, 1), (2, 1), (3, 1)], 1),
    ([(0, 1), (1, 1), (5, 1)], 1), ([(52, 1)], 1), ([], 1), ([], 0), ([], 6),
    ([(0, 1)], 257), ([], 1024)]

-- The array size: `2 ⌈H / 64⌉` up to the default 256, which it reaches at `H = 8129`; the default
-- for the field `0`; a field of 10; and the cap `2 ^ 20` from `H = 2 ^ 25 + 1` on.
#guard [1, 64, 65, 1000, 8128, 8129, 100000].map defaultParams.arraySizeAt ==
  [2, 2, 4, 32, 254, 256, 256]
#guard (⟨[], 0, 0, 0, 64, true, 0⟩ : Params).arraySizeAt 100000 == 256
#guard { defaultParams with arraySize := 10 }.arraySizeAt 100000 == 10
#guard [2 ^ 25, 2 ^ 25 + 1].map { defaultParams with arraySize := 3000000 }.arraySizeAt ==
  [2 ^ 20, 2 ^ 20]

end Ratpoints

end
