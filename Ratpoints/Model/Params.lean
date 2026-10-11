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
only removes candidates that are not points and the pieces of the numerators follow one another in
increasing order. So the model takes the choice as an input, and the theorems hold for every
well-formed choice. The sieve reads only the moduli and the array size.

## Main definitions

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

/-- The sieving parameters: the free choices of the sieve, which the theorems quantify over. The
moduli are cut into three stages: the first `sp1` of them, then those up to `sp2`, then the
rest. -/
structure Params where
  /-- The moduli, primes in the order of the stages. -/
  moduli : List Nat
  /-- The end of the first stage, a position in `Ratpoints.Params.moduli`. -/
  sp1 : Nat
  /-- The end of the second stage, a position in `Ratpoints.Params.moduli`; the third stage is
  the rest. -/
  sp2 : Nat
  /-- At most how many forbidden divisors of the denominators are tested. -/
  maxForbidden : Nat
  /-- Whether the Jacobi test on the denominators runs. -/
  jacobi : Bool
  /-- At most how many bit arrays a piece of the numerators has, the field `array_size` of the
  arguments of the library; `0` for `Ratpoints.defaultArraySize`. -/
  arraySize : Nat := 0

/-- The parameters `P` are well-formed: every modulus is a prime of `Ratpoints.primeTable`, and the
cut points are in order and within the list of moduli. -/
structure Params.WF (P : Params) : Prop where
  /-- Every modulus is a prime of `Ratpoints.primeTable`. -/
  mem_primeTable : ∀ m ∈ P.moduli, m ∈ primeTable
  /-- The first stage ends no later than the second. -/
  sp1_le_sp2 : P.sp1 ≤ P.sp2
  /-- The second stage ends within the list of moduli. -/
  sp2_le_length : P.sp2 ≤ P.moduli.length

instance Params.instDecidableWF (P : Params) : Decidable P.WF :=
  decidable_of_iff ((∀ m ∈ P.moduli, m ∈ primeTable) ∧ P.sp1 ≤ P.sp2 ∧ P.sp2 ≤ P.moduli.length)
    ⟨fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩, fun ⟨h1, h2, h3⟩ ↦ ⟨h1, h2, h3⟩⟩

/-- At most how many bit arrays a piece of the numerators has for the height bound `H`: the field
`arraySize` of the parameters `P`, or `Ratpoints.defaultArraySize` for `0`, capped at `2 ⌈H / 64⌉`
and at `Ratpoints.maxArraySize`; at least 1 for `H ≥ 1` (`Ratpoints.Params.one_le_arraySizeAt`).

C: `rp-private.h:87`, `find_points.c:4666-4677`

Deviation: a `Nat` for the `long` field, so that only `0` stands for the default, which the library
takes for every value `≤ 0`; no rounding up to a multiple of the chunk, which is one bit array in
the build of the model (`RATPOINTS_CHUNK`, stage F). -/
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
`Ratpoints.numPrimes`; the second stage ends at `s₂ = min(N, q)` and the first at `min(n, s₂)` for
the values `N` of `-N` and `n` of `-n`, at `q` and at `s₂` when these are absent or negative; the
moduli are the first `min(q + P, numPrimes)` primes of `Ratpoints.primeTable` for the value
`P ≥ 0` of `-P`, the first `q` when it is absent or negative; at most `F` forbidden divisors are
tested for the value `F ≥ 0` of `-F` or else `Ratpoints.defaultMaxForbidden`, at most as many as
the table has primes; the Jacobi test runs unless `-j` is the last of `-j` and `-J`; and a piece
of the numerators has at most `Ratpoints.defaultArraySize` bit arrays, the array size that the
program sets when it reads the arguments and again before the search.

C: `find_points.c:4643-4649`, `find_points.c:4655-4656`, `find_points.c:4662-4665`,
`main.c:221-222`, `main.c:347`

Deviation: the moduli are the first primes of the table, in increasing order, where ratpoints
ranks the primes by what they say about the curve (`sieving_info`), looks past the first `q` when
`-p` is absent and the curve needs it, chooses the cut points from the curve when `-n` or `-N` is
absent or negative, and corrects the choice during the run (`adapt_primes`); the third stage is the
rest of the list after `s₂`, where ratpoints takes `P` primes after `s₂`, or primes up to all
`Ratpoints.numPrimes` when `-P` is absent or negative. -/
def sieveParams (o : SieveOptions) : Params :=
  let q := min (if o.numPrimes < 0 then defaultNumPrimes else o.numPrimes.toNat) numPrimes
  let sp2 := if o.sp2 < 0 then q else min o.sp2.toNat q
  { moduli := primeTable.toList.take
      (if o.sp3Extra < 0 then q else min (q + o.sp3Extra.toNat) numPrimes)
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

#guard defaultParams.moduli == primeTable.toList.take 30 && defaultParams.sp1 == 30 &&
  defaultParams.sp2 == 30 && defaultParams.maxForbidden == 64 && defaultParams.jacobi &&
  defaultParams.arraySize == 256

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

-- A well-formedness that fails: a modulus that is not a prime of the table.
#guard !decide (Params.WF ⟨[3, 9], 0, 0, 64, true, 0⟩)

-- The array size: `2 ⌈H / 64⌉` up to the default 256, which it reaches at `H = 8129`; the default
-- for the field `0`; a field of 10; and the cap `2 ^ 20` from `H = 2 ^ 25 + 1` on.
#guard [1, 64, 65, 1000, 8128, 8129, 100000].map defaultParams.arraySizeAt ==
  [2, 2, 4, 32, 254, 256, 256]
#guard (⟨[], 0, 0, 64, true, 0⟩ : Params).arraySizeAt 100000 == 256
#guard { defaultParams with arraySize := 10 }.arraySizeAt 100000 == 10
#guard [2 ^ 25, 2 ^ 25 + 1].map { defaultParams with arraySize := 3000000 }.arraySizeAt ==
  [2 ^ 20, 2 ^ 20]

end Ratpoints

end
