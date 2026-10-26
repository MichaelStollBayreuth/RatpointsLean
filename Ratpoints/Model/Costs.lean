/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Denominators

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Denominators

/-!
# The cost model of the choice of the moduli

ratpoints chooses the moduli of its sieve and the cut points of its stages from the curve, by a
model of what each modulus costs and what it says (`sieving_info`, which the model has with stage
I): the candidates are ranked by their keys, what a modulus costs per word swept divided by what it
says, `-log r` for its density `r`; the first stage takes them while the survivors per word that the
next one removes are worth its cost; the second adds an offset that grows with the length of the
run; and the third stage takes further primes while the survivors they remove are worth the
denominators they are carried through. This module holds the arithmetic of that model, in doubles,
expression by expression as the C code computes them: the record of a candidate and its two orders,
the costs and keys, the cost of the exact check, the rule that ends the first stage, the offset of
the second, and the estimate of the run (the denominators, the words and the calls of the sieve)
with the mean number of bits per word of the bit arrays. Nothing calls them yet: the choice of the
moduli that does comes with stage I.

The doubles are Lean's `Float`, IEEE 754 binary64 with the arithmetic of the platform: `+`, `-`,
`*`, `/` and `sqrt` correctly rounded, as the C code compiled without fused multiply-adds and
without `-ffast-math` computes them; `ceil` and `floor`, which are exact, computed by the C library
of the platform, where ratpoints computes them inline (gcc's `roundsd` under `-mavx2`); and `log`
and `pow` the functions of the C library of the platform that the Lean runtime binds, on glibc an
older symbol version of the routines that ratpoints binds (`log@GLIBC_2.2.5` and `pow@GLIBC_2.2.5`,
where ratpoints binds `log@GLIBC_2.29` and `pow@GLIBC_2.29`), which give the same values on every
argument that occurs here (`x ≥ 0` for `log`, and for `pow` a base in `(0, 1]` and a positive
exponent) and differ only in `errno` and in the sign of the NaN of the logarithm of a negative
number. glibc's `log` and `pow` are not correctly rounded and choose between variants by the
processor, so that the choice of ratpoints and that of the model depend on the machine, and agree on
one machine. Every expression keeps the order of the operations of the C code, and every comparison
is the C code's; no fact about the values is needed by the theorems, which hold for every choice.

## Main definitions

* `Ratpoints.ModulusCandidate`, `Ratpoints.ModulusCandidate.keyLe`,
  `Ratpoints.ModulusCandidate.rLe`, `Ratpoints.sortFrom`: a candidate modulus of the ranking, its
  two orders and the stable sort of the tail of the pool.
* `Ratpoints.checkCost`, `Ratpoints.primeCost`, `Ratpoints.primeKey`, `Ratpoints.phase1Key`: the
  cost of one exact check, the cost and the key of a modulus, and the key of the first stage.
* `Ratpoints.downstreamFactor`, `Ratpoints.phase1Wants`, `Ratpoints.primesForPhase1`,
  `Ratpoints.phase2Offset`: the rule that ends the first stage and the offset of the second.
* `Ratpoints.ShapeArgs`, `Ratpoints.RunEstimate`, `Ratpoints.runShape`: the estimate of the run.
* `Ratpoints.meanBitsPerWord`: the mean number of bits per word of the bit arrays of the run.
-/

@[expose] public section

namespace Ratpoints

open Sieve

/-! ### The candidates -/

/-- A candidate modulus of the ranking of `sieving_info`, the record `entry` of the C code: its
density `r`, its key, the cost the key was made from, the modulus `p`, the mask of the indices of
the primes it involves (a prime from the 65th of the table on is in no mask), its sieve entry, made
for a prime by its examination and for a composite modulus when the ranking takes it, the count of
its factors `nf` (`0` for a prime, `-1` for a prime that says only that numerator and denominator
are coprime, the number of factors of a composite modulus) and the codes of its factors: the index
`pn` of the prime `prime[pn]`, or `Ratpoints.numPrimes` plus the index of an examined prime power.

C: `find_points.c:147-149`

Deviation: a natural number for the `long` modulus, a `UInt64` for the `unsigned long` mask, an
integer for the `short` count, the codes a list of natural numbers, for the array of
`RP_MAX_FACTORS` `short`s, and the sieve entry an option, `none` for the null pointer. -/
structure ModulusCandidate where
  /-- The density. -/
  r : Float
  /-- The key of the ranking. -/
  key : Float
  /-- The cost the key was made from. -/
  cost : Float
  /-- The modulus. -/
  p : Nat
  /-- The mask of the indices of the primes involved. -/
  mask : UInt64
  /-- The sieve entry, if made. -/
  ssp : Option SieveEntry
  /-- The count of the factors. -/
  nf : Int
  /-- The codes of the factors. -/
  fac : List Nat
  deriving Inhabited

/-- The order of the ranking by keys, `compare_entries`: `a` before `b` unless `a.key - b.key > 0`,
the test of the merge sort of `qsort` that the comparison is at most `0`. On keys that are finite
or `+∞`, never a NaN, it is a total preorder, `∞ - ∞` a NaN that compares as a tie.

C: `find_points.c:1194-1198`

Deviation: the test of the merge sort, whether the comparison is at most `0`, for the comparison
of the C code, which returns `1`, `-1` or `0`. -/
def ModulusCandidate.keyLe (a b : ModulusCandidate) : Bool := !(a.key - b.key > 0.0)

/-- The order by density, `compare_by_r`: `a` before `b` unless `a.r - b.r > 0`.

C: `find_points.c:1202-1206`

Deviation: the test of the merge sort, whether the comparison is at most `0`, for the comparison
of the C code, which returns `1`, `-1` or `0`. -/
def ModulusCandidate.rLe (a b : ModulusCandidate) : Bool := !(a.r - b.r > 0.0)

/-- The pool `pool` with its entries from the position `s` on sorted by the order `le`, stably, as
`qsort(&prec[s], pnp - s, sizeof(entry), cmp)` sorts them.

It models no C code of its own: it is the call of `qsort` at the four places where `sieving_info`
sorts. Lean's `List.mergeSort` is a stable merge sort, as glibc's `qsort` is on the records of the
ranking when it can allocate its buffer, which it always can in the model, where no allocation fails
(glibc falls back to a sort that is not stable when `malloc` fails), and the orders are total
preorders on the keys and densities that occur, so that every stable sort gives the same order, also
on ties (`-C 0`, `-C inf`). -/
def sortFrom (pool : Array ModulusCandidate) (s : Nat)
    (le : ModulusCandidate → ModulusCandidate → Bool) : Array ModulusCandidate :=
  pool.extract 0 s ++ ((pool.extract s pool.size).toList.mergeSort le).toArray

/-! ### Costs and keys -/

/-- What one exact check costs on the curve of degree `d` with the coefficient list `c`, for the
height bound `H`, in the units of `Ratpoints.checkReference`: the value `field` of `-W` when it is
positive; else, with `hbits = log(H + 1) / log 2` and `cbits` the largest bit length of a nonzero
coefficient, at least `1`, the bits `fbits = cbits + d hbits` of `F(a, b)`, its limbs
`limbs = fbits / 64`, the mean limbs `mid = 0.5 (cbits + fbits) / 64` over Horner's rule, the limbs
`root = max(1, ⌈0.5 limbs⌉)` of the square root, and the cost
`d (CHECK_STEP + CHECK_LIMB mid) + CHECK_CALL + CHECK_ROOT (root - 1)`, with
`CHECK_STEP + CHECK_LIMB limbs` more for odd `d`.

C: `find_points.c:1285-1318`

Deviation: the coefficients, the degree and the height bound as arguments, for the fields of the
arguments that `check_cost` reads; `log` the function of the C library of the platform that the Lean
runtime binds (`Float.log`), on glibc an older symbol version of the routine that ratpoints binds,
which gives the same values on every argument that occurs here, and which glibc does not round
correctly and chooses by the processor, so that the value is that of the C program on the same
machine; `log 2` computed at run time, where gcc folds `log(2.0)` into the same double; `ceil` the
function of the C library of the platform (`Float.ceil`), which is exact, where gcc compiles an
instruction; the bit length of `|c_k|` (`Nat.log2 + 1`) for `mpz_sizeinbase(c_k, 2)`, which it is
for `c_k ≠ 0`; `64` for `LONG_LENGTH`. -/
def checkCost (c : List Int) (d H : Nat) (field : Float) : Id Float := do
  let hbits := Float.log (Float.ofNat H + 1.0) / Float.log 2.0
  let mut cbits := 1.0
  if 0.0 < field then return field
  for k in [0:d + 1] do
    let ck := c.getD k 0
    if ck != 0 then
      let b := Float.ofNat (ck.natAbs.log2 + 1)
      if cbits < b then cbits := b
  let fbits := cbits + Float.ofNat d * hbits
  let limbs := fbits / 64.0
  let mid := 0.5 * (cbits + fbits) / 64.0
  let root := Float.ceil (0.5 * limbs)
  let root := if root < 1.0 then 1.0 else root
  let cost := Float.ofNat d * (checkStep + checkLimb * mid) + checkCall + checkRoot * (root - 1.0)
  return if d % 2 = 1 then cost + (checkStep + checkLimb * limbs) else cost

/-- What one more modulus `p` costs the sieve per word swept, in units of an and of the first
stage, for the run of `U` words and `D` denominators: `perWord`, the part paid for every word, plus
`COST_BP D / U` for its entry of `bp_list`, and for a modulus of the first two stages (`tabled`)
`COST_SETUP D / U` for its sieve spec and, for a positive cost `ct` of a row of a table,
`ct p min(D, p) / U` for its table.

C: `find_points.c:1220-1235` -/
def primeCost (p : Nat) (perWord : Float) (tabled : Bool) (ct U D : Float) : Float :=
  let cost := perWord + costBp * D / U
  if !tabled then cost
  else
    let cost := cost + costSetup * D / U
    let builds := if D < Float.ofNat p then D else Float.ofNat p
    if 0.0 < ct then cost + ct * Float.ofNat p * builds / U else cost

/-- The key of a modulus `p` of density `r`: its cost (`Ratpoints.primeCost`) divided by what it
says, `info = -log r`, and `10 ^ 300` when `info ≤ 0`.

C: `find_points.c:1241-1247`

Deviation: `log` the function of the C library of the platform that the Lean runtime binds
(`Float.log`), on glibc an older symbol version of the routine that ratpoints binds, which gives the
same values on every argument that occurs here, and which glibc does not round correctly and chooses
by the processor, so that the value is that of the C program on the same machine. -/
def primeKey (r : Float) (p : Nat) (perWord : Float) (tabled : Bool) (ct U D : Float) : Float :=
  let info := -Float.log r
  if info ≤ 0.0 then 1.0e300 else primeCost p perWord tabled ct U D / info

/-- The candidate `e` with its key for the first stage and the cost it was made from, for the cost
`ct` of a row of a table, the run of `U` words and `D` denominators and the cost `cc` of the calls
of the sieve per word: the cost of a modulus of the first stage (`Ratpoints.primeCost` with the cost
`1` per word) plus `cc` plus `COST_LINE walk (32 / 64) D / U` for the part of its row that a
denominator walks, `walk = min(p, U / (4 D))` bit arrays of 32 bytes; the key that cost divided by
`-log r`, or `10 ^ 300` when that is not positive.

C: `find_points.c:1256-1270`

Deviation: `log` the function of the C library of the platform that the Lean runtime binds
(`Float.log`), on glibc an older symbol version of the routine that ratpoints binds, which gives the
same values on every argument that occurs here, and which glibc does not round correctly and chooses
by the processor, so that the value is that of the C program on the same machine; the candidate
returned with its key and cost, for the fields of the record that `phase_1_key` sets;
`Ratpoints.rbaPack` for `RBA_PACK` and `8 Ratpoints.rbaPack` for the size of a bit array in
bytes. -/
def phase1Key (ct U D cc : Float) (e : ModulusCandidate) : ModulusCandidate :=
  let info := -Float.log e.r
  let arrays := U / (D * Float.ofNat rbaPack)
  let walk := if Float.ofNat e.p < arrays then Float.ofNat e.p else arrays
  let cost := primeCost e.p 1.0 true ct U D + cc +
    costLine * walk * (Float.ofNat (8 * rbaPack) / 64.0) * D / U
  { e with cost, key := if info ≤ 0.0 then 1.0e300 else cost / info }

/-! ### The first two stages -/

/-- What a word that survives the first stage costs from the candidate `n` of the pool on, relative
to what it costs in a long run: the next `extra` candidates (as far as the pool goes) and the
survivor that is left, `COST_PHASE2` for each and per surviving word and `COST_SURVIVOR` per
survivor, `cost (1 - ρ) / COST_PHASE2` with `ρ` the geometric mean of the densities of the next
`Ratpoints.sp2Extra` candidates (the density of `n` when there are none), at least `1`.

C: `find_points.c:1539-1561`

Deviation: `pow` the function of the C library of the platform that the Lean runtime binds
(`Float.pow`), on glibc an older symbol version of the routine that ratpoints binds, which gives the
same values on every argument that occurs here, and which glibc does not round correctly and chooses
by the processor, so that the value is that of the C program on the same machine; natural numbers
for the `long` positions, the comparisons with the candidates left after `n` made on integers. -/
def downstreamFactor (pool : Array ModulusCandidate) (n pnp extra : Nat) : Id Float := do
  let rest : Int := (pnp : Int) - n - 1
  let stop := if rest ≤ extra then pnp else n + 1 + extra
  let stopRef := if rest ≤ sp2Extra then pnp else n + 1 + sp2Extra
  let mut rate := 1.0
  let mut cost := 0.0
  for j in [n + 1:stop] do
    cost := cost + costPhase2 * rate
    rate := rate * pool[j]!.r
  cost := cost + rate * costSurvivor
  let mut rho := pool[n]!.r
  if n + 1 < stopRef then
    let mut ref := 1.0
    for j in [n + 1:stopRef] do ref := ref * pool[j]!.r
    rho := Float.pow ref (1.0 / Float.ofNat (stopRef - n - 1))
  let k := cost * (1.0 - rho) / costPhase2
  return if k < 1.0 then 1.0 else k

/-- The rule that ends the first stage: the candidate `n` of the pool of `pnp` candidates is taken
when it is the first (`taken = 0`), or when the survivors per word it removes, `bpw rate (1 - r)`,
weighted by what they cost downstream (`Ratpoints.downstreamFactor`), exceed the target times its
cost.

C: `find_points.c:1583-1589` -/
def phase1Wants (pool : Array ModulusCandidate) (n pnp taken : Nat) (bpw rate target : Float)
    (extra : Nat) : Id Bool := do
  if taken = 0 then return true
  let df ← downstreamFactor pool n pnp extra
  return bpw * rate * (1.0 - pool[n]!.r) * df > target * pool[n]!.cost

/-- How many candidates of the pool, sorted by keys, the first stage would take by its rule
(`Ratpoints.phase1Wants`, with the product of the densities so far): the first that it refuses, or
all of them, at least `1`.

C: `find_points.c:1598-1609` -/
def primesForPhase1 (pool : Array ModulusCandidate) (bpw target : Float) (extra : Nat) :
    Id Nat := do
  let pnp := pool.size
  let mut rate := 1.0
  for n in [0:pnp] do
    if !(← phase1Wants pool n pnp n bpw rate target extra) then return n
    rate := rate * pool[n]!.r
  return if 0 < pnp then pnp else 1

/-- How many moduli the second stage adds to the first, for the offset `extra` of a long run, the
scale `u0` and the run of `U` words: for `u0 ≤ 0` or `U ≤ 0` the offset itself, capped at
`most = Ratpoints.numPrimes + Ratpoints.maxModuli`; else `e = extra / (1 + u0 / U)` rounded to the
nearest integer when below `most`, and `most` otherwise.

C: `find_points.c:1619-1626`

Deviation: natural numbers for the `long`s, which are not negative here; the conversion of
`e + 0.5` to a `long`, which truncates, by `Float.toUInt64`, which truncates `e + 0.5 < most` as
well. -/
def phase2Offset (extra : Nat) (u0 U : Float) : Nat :=
  let most := numPrimes + maxModuli
  if u0 ≤ 0.0 ∨ U ≤ 0.0 then min extra most
  else
    let e := Float.ofNat extra / (1.0 + u0 / U)
    if e < Float.ofNat most then (e + 0.5).toUInt64.toNat else most

/-! ### The estimate of the run -/

/-- The numerators that the denominator `b` considers, for the height bound `H`, as doubles: over
the search intervals `domain`, the interval `[b l, b u]` clipped to `[-H, H]`, its width added when
it is not empty, with the number of such intervals and of their ends that the height bound cut,
below and above.

C: `find_points.c:1836-1854`

Deviation: the search intervals as an argument, for the fields `domain` and `num_inter` of the
arguments, their ends doubles by their bits (`Ratpoints.Double.toFloat`); the sum and the three
counts returned, the counts as doubles, as the C code hands them back through its pointers. -/
def numeratorsFor (domain : List (Double × Double)) (b H : Float) :
    Id (Float × Float × Float × Float) := do
  let mut sum := 0.0
  let mut n := 0
  let mut clo := 0
  let mut chi := 0
  for (l, u) in domain do
    let (lo, cl) := if b * l.toFloat ≤ -H then (-H, 1) else (b * l.toFloat, 0)
    let (up, ch) := if H ≤ b * u.toFloat then (H, 1) else (b * u.toFloat, 0)
    if lo < up then (sum, n, clo, chi) := (sum + (up - lo), n + 1, clo + cl, chi + ch)
  return (sum, Float.ofNat n, Float.ofNat clo, Float.ofNat chi)

/-- The sums `padLo` and `padHi` with what the rounding of an interval to whole bit arrays adds at
an end that the height bound `H` cut, for the class `cl` of the stride `2 ^ k` and the residue `a₀`:
the first bit `lo = -(⌊(H - 2 ^ k + a₀) / 2 ^ k⌋ + 1)` and minus the one past the last,
`hi = -⌊(H - a₀) / 2 ^ k⌋ - 1`, each modulo `Ratpoints.rbaLength`.

C: `find_points.c:1863-1876`

Deviation: the two sums passed and returned, for the pointers; integers for the `long`s, the
arithmetic shifts as divisions that round down and the masks by `RBA_LENGTH - 1` as Euclidean
remainders. -/
def clippedPadding (cl : NumClass) (H : Nat) (padLo padHi : Float) : Float × Float :=
  let k : Int := 2 ^ cl.k
  let loBit : Int := -(((H : Int) - k + cl.a0) / k + 1)
  let hiNeg : Int := -(((H : Int) - cl.a0) / k) - 1
  (padLo + Float.ofInt (loBit % rbaLength), padHi + Float.ofInt (hiNeg % rbaLength))

/-- The fraction of the integers `b` whose valuation at `p` is in the set that `mask` describes, bit
`m` for `v_p(b) = m`: the sum of `(1 / p ^ m) (1 - 1 / p)` over the bits `m ≥ 1` of the mask, while
`m < 64` and bits are left.

C: `find_points.c:1926-1937`

Deviation: natural numbers for the `long` and the `unsigned long` mask; `64` for `LONG_LENGTH`. -/
def forbiddenFraction (p mask : Nat) : Id Float := do
  let mut f := 0.0
  let mut q := 1.0 / Float.ofNat p
  let mut m := 1
  while m < 64 && mask >>> m != 0 do
    if (mask >>> m) % 2 = 1 then f := f + q * (1.0 - 1.0 / Float.ofNat p)
    q := q / Float.ofNat p
    m := m + 1
  return f

/-- What the estimate of the run reads of the search: the shape of the denominators (the squares,
the divisors of the leading coefficient times squares, or every denominator), whether the Jacobi
test runs, the height bound, the range of the denominators, the search intervals, the word of the
classes of the denominators modulo 64 that admit a numerator, the classes, and the array size.

It models no C code of its own: a structure for the fields of the arguments and the arguments of
`run_shape` and `mean_bits_per_word` that describe the run (`find_points.c:1939-1943`,
`find_points.c:2134-2136`), the bits `RATPOINTS_USE_SQUARES`, `RATPOINTS_USE_SQUARES1` (with
`args->divisors`) and `RATPOINTS_USE_JACOBI` of the flags as Booleans and an option, natural
numbers for the `long`s, and the array size normalized for the height bound
(`Ratpoints.Params.arraySizeAt`). -/
structure ShapeArgs where
  /-- Whether the denominators are the squares. -/
  useSquares : Bool
  /-- The divisors of the leading coefficient, when the denominators are those times squares. -/
  divisors : Option (List Nat)
  /-- Whether the Jacobi test runs. -/
  useJacobi : Bool
  /-- The height bound. -/
  H : Nat
  /-- The least denominator. -/
  bLow : Nat
  /-- The largest denominator. -/
  bHigh : Nat
  /-- The search intervals. -/
  domain : List (Double × Double)
  /-- The word `den_bits` of the classes that admit a numerator. -/
  db : UInt64
  /-- The classes of the denominators modulo 64. -/
  cls : Vector NumClass 64
  /-- The array size, normalized for the height bound. -/
  arraySize : Nat

/-- The local variables of `run_shape`: the fraction `keep` of the candidates that reach the sieve,
the candidate denominators, the numerators they sweep, their nonempty intervals and the ends of
those that the height bound cut, the classes kept, the sum of their shares `2 ^ -k` and the sums of
what a cut end pads.

C: `find_points.c:1945-1957`

Deviation: a structure for the local variables, with their initial values. -/
structure ShapeAcc where
  /-- The fraction of the candidates that reach the sieve. -/
  keep : Float := 1.0
  /-- The candidate denominators. -/
  count : Float := 0.0
  /-- The numerators they sweep. -/
  nums : Float := 0.0
  /-- Their nonempty intervals. -/
  inters : Float := 0.0
  /-- The ends that the height bound cut below. -/
  clo : Float := 0.0
  /-- The ends that the height bound cut above. -/
  chi : Float := 0.0
  /-- The classes kept. -/
  good : Nat := 0
  /-- The sum of the shares of their numerators. -/
  packed : Float := 0.0
  /-- The sum of what a cut end pads below. -/
  padLo : Float := 0.0
  /-- The sum of what a cut end pads above. -/
  padHi : Float := 0.0

/-- The estimate of the run: the denominators it sifts, the words it sweeps, padding included, of
which padding, and the calls of the sieve.

It models no C code of its own: a structure for the four results that `run_shape` hands back
through its pointers (`find_points.c:1942-1943`). -/
structure RunEstimate where
  /-- The denominators sifted, `run_denoms`. -/
  denoms : Float
  /-- The words swept, `run_words`. -/
  words : Float
  /-- Of these, the padding to whole bit arrays, `u_pad`. -/
  pad : Float
  /-- The calls of the sieve, `n_calls`. -/
  calls : Float

/-- The accumulators `acc` with the denominators `lo, …, hi` of the steps `k` (the squares `k ^ 2`
for `square`, the denominators themselves otherwise): `count = hi - lo + 1` when `hi ≥ lo`, and the
numerators, intervals and cut ends of the 64 midpoint samples `k = lo + (hi - lo)(i + 0.5) / 64`
(`Ratpoints.numeratorsFor`), each sum scaled by `count / 64`.

C: `find_points.c:1964-1973`, `find_points.c:2028-2037`

Deviation: one function for the samples of the squares and of every denominator, which the C code
writes out twice. -/
def sampleSteps (domain : List (Double × Double)) (H lo hi : Float) (square : Bool)
    (acc : ShapeAcc) : Id ShapeAcc := do
  if !(lo ≤ hi) then return acc
  let count := hi - lo + 1.0
  let mut (nums, inters, clo, chi) := (acc.nums, acc.inters, acc.clo, acc.chi)
  for i in [0:runShapeSamples] do
    let k := lo + (hi - lo) * (Float.ofNat i + 0.5) / Float.ofNat runShapeSamples
    let (s, ni, nlo, nhi) ← numeratorsFor domain (if square then k * k else k) H
    nums := nums + s
    inters := inters + ni
    clo := clo + nlo
    chi := chi + nhi
  let f := count / Float.ofNat runShapeSamples
  return { acc with count, nums := nums * f, inters := inters * f, clo := clo * f, chi := chi * f }

/-- The accumulators `acc` with the class `cl` kept: one class more, its share `2 ^ -k` of the
numerators, and what its cut ends pad (`Ratpoints.clippedPadding`).

C: `find_points.c:1980-1981`, `find_points.c:2017-2018`, `find_points.c:2045-2046`

Deviation: one function for the three places of the C code. -/
def addClass (cl : NumClass) (H : Nat) (acc : ShapeAcc) : ShapeAcc :=
  let (padLo, padHi) := clippedPadding cl H acc.padLo acc.padHi
  { acc with good := acc.good + 1, packed := acc.packed + invStride.getD cl.k 0.0, padLo, padHi }

/-- The accumulators of the squares in the range of the denominators: the steps
`⌈√bLow⌉, …, ⌊√bHigh⌋` (`Ratpoints.sampleSteps`), and the classes `k ^ 2 mod 64` for `k < 32`, those
with a pattern kept, with `keep` the share of those kept.

C: `find_points.c:1960-1962`, `find_points.c:1976-1979`, `find_points.c:1982-1985`

Deviation: `ceil` and `floor` the functions of the C library of the platform (`Float.ceil`,
`Float.floor`), which are exact, where gcc compiles instructions. -/
def shapeSquares (a : ShapeArgs) : Id ShapeAcc := do
  let klo := Float.ceil (Float.sqrt (Float.ofNat a.bLow))
  let khi := Float.floor (Float.sqrt (Float.ofNat a.bHigh))
  let mut acc ← sampleSteps a.domain (Float.ofNat a.H) klo khi true {}
  for j in [0:32] do
    let cl := a.cls[j * j % 64]!
    if cl.bits != 0 then acc := addClass cl a.H acc
  return { acc with keep := Float.ofNat acc.good / 32.0 }

/-- The accumulators `acc` with the denominators `d k ^ 2` of the divisor `d`, for
`k = max(1, ⌈√(bLow / d)⌉), …, ⌊√(bHigh / d)⌋`: their count `c` and the numerators, intervals and
cut ends of the 64 midpoint samples, each times `c / 64`.

C: `find_points.c:1993-2009`

Deviation: `ceil` and `floor` the functions of the C library of the platform (`Float.ceil`,
`Float.floor`), which are exact, where gcc compiles instructions. -/
def sampleDivisor (domain : List (Double × Double)) (H : Float) (bLow bHigh d : Nat)
    (acc : ShapeAcc) : Id ShapeAcc := do
  let df := Float.ofNat d
  let klo := Float.ceil (Float.sqrt (Float.ofNat bLow / df))
  let khi := Float.floor (Float.sqrt (Float.ofNat bHigh / df))
  let klo := if klo < 1.0 then 1.0 else klo
  if !(klo ≤ khi) then return acc
  let c := khi - klo + 1.0
  let S := Float.ofNat runShapeSamples
  let mut acc := acc
  for i in [0:runShapeSamples] do
    let k := klo + (khi - klo) * (Float.ofNat i + 0.5) / S
    let (s, ni, nlo, nhi) ← numeratorsFor domain (df * k * k) H
    acc := { acc with
      nums := acc.nums + c * s / S, inters := acc.inters + c * ni / S,
      clo := acc.clo + c * nlo / S, chi := acc.chi + c * nhi / S }
  return { acc with count := acc.count + c }

/-- The accumulators of the divisors `ds` of the leading coefficient times squares: for each divisor
`d` its denominators (`Ratpoints.sampleDivisor`) and the classes `d k ^ 2 mod 64` for `k < 32`,
those with a pattern kept; `keep` the share of the classes kept among those tried, when any were.

C: `find_points.c:1987-1992`, `find_points.c:2010-2016`, `find_points.c:2019-2023`

Deviation: the divisors as a list, for the zero-terminated array `args->divisors`. -/
def shapeSquares1 (a : ShapeArgs) (ds : List Nat) : Id ShapeAcc := do
  let mut acc : ShapeAcc := {}
  let mut tried := 0
  for d in ds do
    acc ← sampleDivisor a.domain (Float.ofNat a.H) a.bLow a.bHigh d acc
    for j in [0:32] do
      let cl := a.cls[d * (j * j) % 64]!
      if cl.bits != 0 then acc := addClass cl a.H acc
      tried := tried + 1
  if tried ≠ 0 then acc := { acc with keep := Float.ofNat acc.good / Float.ofNat tried }
  return acc

/-- The share of the denominators that reach the sieve in the shape of every denominator, from the
share `keep` of the classes kept: for the checked loop (`checkDenom`), times `1 - 1 / p` for each
forbidden divisor `p` tested with words, times `1 - f` for each tested by its valuations with the
fraction `f` of its excluded valuations (`Ratpoints.forbiddenFraction`), and times `0.53` when the
Jacobi test runs.

C: `find_points.c:2051-2065`

Deviation: the forbidden divisors as lists, for the arrays of the arguments with their counts `fba`
and `fdc`. -/
def keepChecked (keep : Float) (checkDenom useJacobi : Bool) (forb : List ForbiddenEntry)
    (forbVal : List ForbiddenVal) : Id Float := do
  if !checkDenom then return keep
  let mut keep := keep
  for f in forb do keep := keep * (1.0 - 1.0 / Float.ofNat f.p)
  for f in forbVal do keep := keep * (1.0 - (← forbiddenFraction f.p f.mask))
  if useJacobi then keep := keep * 0.53
  return keep

/-- The accumulators of every denominator in the range: the denominators `bLow, …, bHigh`
(`Ratpoints.sampleSteps`), the classes of the set bits of `den_bits` in increasing order, all kept,
`keep` their share of the 64 classes, and that for the checked loop (`Ratpoints.keepChecked`).

C: `find_points.c:2025-2027`, `find_points.c:2038-2044`, `find_points.c:2047-2050`,
`find_points.c:2066`

Deviation: the set bits of the word visited by the lowest set bit (`Ratpoints.Sieve.ctz`), as the C
code visits them with `RP_CTZL`. -/
def shapeAll (a : ShapeArgs) (checkDenom : Bool) (forb : List ForbiddenEntry)
    (forbVal : List ForbiddenVal) : Id ShapeAcc := do
  let mut acc ← sampleSteps a.domain (Float.ofNat a.H) (Float.ofNat a.bLow) (Float.ofNat a.bHigh)
    false {}
  let mut w := a.db
  while w != 0 do
    let j ← ctz w
    w := w &&& (w - 1)
    acc := addClass a.cls[j]! a.H acc
  let keep ← keepChecked (Float.ofNat acc.good / 64.0) checkDenom a.useJacobi forb forbVal
  return { acc with keep }

/-- The estimate of the run from the accumulators `acc` and the array size `asz`: the numerators
times the mean share of the classes kept; the padding, what a cut end pads by its class and half a
bit array for an end inside the bound; the bit arrays per interval and the calls of the sieve, one
per interval and denominator and as many as `asz` bit arrays take; the denominators `keep count`,
the words `keep (nums + pad) / 64`, the padding `keep pad / 64` and the calls
`keep inters ⌈per / asz⌉`; each at least `1`, the padding `0` when the words are floored.

C: `find_points.c:2074-2105`

Deviation: the estimate returned as a structure, for the four pointers of `run_shape`; `ceil` the
function of the C library of the platform (`Float.ceil`), which is exact, where gcc compiles an
instruction; `64` for `LONG_LENGTH`. -/
def shapeEstimate (asz : Nat) (acc : ShapeAcc) : RunEstimate :=
  let good := Float.ofNat acc.good
  let nums := if 0 < acc.good then acc.nums * (acc.packed / good) else acc.nums
  let pad := if 0 < acc.good then acc.clo * acc.padLo / good + acc.chi * acc.padHi / good +
      (2.0 * acc.inters - acc.clo - acc.chi) * 0.5 * Float.ofNat rbaLength else 0.0
  let asz := if 0 < asz then Float.ofNat asz else Float.ofNat defaultArraySize
  let per := if 0.0 < acc.inters then (nums + pad) / acc.inters / Float.ofNat rbaLength else 0.0
  let denoms := acc.keep * acc.count
  let words := acc.keep * (nums + pad) / 64.0
  let upad := acc.keep * pad / 64.0
  let calls := acc.keep * acc.inters * Float.ceil (per / asz)
  { denoms := if denoms < 1.0 then 1.0 else denoms, words := if words < 1.0 then 1.0 else words,
    pad := if words < 1.0 then 0.0 else upad, calls := if calls < 1.0 then 1.0 else calls }

/-- How big the run is, as `run_shape` estimates it before any sieving, for the switch `checkDenom`
of the checked loop and the forbidden divisors `forb` and `forbVal` known so far: by the shape
(`Ratpoints.shapeSquares`, `Ratpoints.shapeSquares1`, `Ratpoints.shapeAll`), then the estimate
(`Ratpoints.shapeEstimate`).

C: `find_points.c:1939-1944`, `find_points.c:1959`, `find_points.c:1986`, `find_points.c:2024`,
`find_points.c:2106`

Deviation: the switch `checkDenom` for the bit `RATPOINTS_CHECK_DENOM` of the flags, and the
forbidden divisors as lists, for the arrays with their counts `fba` and `fdc`. -/
def runShape (a : ShapeArgs) (checkDenom : Bool) (forb : List ForbiddenEntry)
    (forbVal : List ForbiddenVal) : Id RunEstimate := do
  let acc ← if a.useSquares then shapeSquares a
    else match a.divisors with
      | some ds => shapeSquares1 a ds
      | none => shapeAll a checkDenom forb forbVal
  return shapeEstimate a.arraySize acc

/-! ### The bits per word -/

/-- The number of the set bits of the word `w`, `__builtin_popcountl`.

It models no C code of its own: the builtin of gcc at `find_points.c:2129`, in the range of
`Ratpoints.bpwAdd`, as a loop over the 64 bits. -/
def popcount (w : UInt64) : Id Nat := do
  let mut n := 0
  for i in [0:64] do
    if (w >>> i.toUInt64) &&& 1 == 1 then n := n + 1
  return n

/-- The sums `tot` and `wsum` with the class `cl`, when its pattern has a set bit: its bits per word
times its share `2 ^ -k` of the numerators, and that share.

C: `find_points.c:2128-2132`

Deviation: the two sums passed and returned, for the pointers; the number of the set bits of the
word a loop over its bits (`Ratpoints.popcount`), for gcc's builtin `__builtin_popcountl`. -/
def bpwAdd (cl : NumClass) (tot wsum : Float) : Id (Float × Float) := do
  let c ← popcount cl.bits
  if c = 0 then return (tot, wsum)
  let s := invStride.getD cl.k 0.0
  return (tot + s * Float.ofNat c, wsum + s)

/-- The sums of `Ratpoints.bpwAdd` over the classes that the divisors `ds` of the leading
coefficient times squares visit: the classes `d k ^ 2 mod 64` for each divisor `d` and `k < 32`.

C: `find_points.c:2143-2151` -/
def bpwSquares1 (cls : Vector NumClass 64) (ds : List Nat) : Id (Float × Float) := do
  let mut (tot, wsum) := (0.0, 0.0)
  for d in ds do
    for j in [0:32] do
      (tot, wsum) ← bpwAdd cls[d * (j * j) % 64]! tot wsum
  return (tot, wsum)

/-- The mean number of bits set per word of a bit array on entry to the sieve, over the classes of
the denominators that the run visits, weighted by the words they sweep: the classes `k ^ 2 mod 64`
for `k < 32` for the squares, those of the divisors for the divisors times squares
(`Ratpoints.bpwSquares1`), and those of the set bits of `den_bits` otherwise (`Ratpoints.bpwAdd`);
`0` when no class has a pattern.

C: `find_points.c:2134-2142`, `find_points.c:2152-2159`

Deviation: the set bits of the word visited by the lowest set bit (`Ratpoints.Sieve.ctz`), as the C
code visits them with `RP_CTZL`. -/
def meanBitsPerWord (a : ShapeArgs) : Id Float := do
  let mut (tot, wsum) := (0.0, 0.0)
  if a.useSquares then
    for j in [0:32] do (tot, wsum) ← bpwAdd a.cls[j * j % 64]! tot wsum
  else match a.divisors with
    | some ds => (tot, wsum) ← bpwSquares1 a.cls ds
    | none =>
      let mut w := a.db
      while w != 0 do
        let j ← ctz w
        w := w &&& (w - 1)
        (tot, wsum) ← bpwAdd a.cls[j]! tot wsum
  return if 0.0 < wsum then tot / wsum else 0.0

/-! ### Examples -/

-- The sentinels of the C code, bit for bit as gcc compiles them: the key `1.0e300` and the bound
-- `1 - 1.0e-9` of a useful prime power.
#guard (1.0e300 : Float).toBits == 0x7E37E43C8800759C &&
  (1.0 - 1.0e-9 : Float).toBits == 0x3FEFFFFFFF768FA1

-- The order of the ranking: a tie at `+∞`, where `∞ - ∞` is a NaN, and a stable sort.
#guard
  let e (k : Float) (p : Nat) : ModulusCandidate :=
    { r := 0.5, key := k, cost := 0, p, mask := 0, ssp := none, nf := 0, fac := [] }
  let inf := (1.0 : Float) / 0.0
  ModulusCandidate.keyLe (e inf 3) (e inf 5) && ModulusCandidate.keyLe (e inf 5) (e inf 3) &&
    (sortFrom #[e 2 3, e inf 5, e 1 7, e inf 9, e 1 11] 1 ModulusCandidate.keyLe).map (·.p) ==
      #[3, 7, 11, 5, 9]

-- The offset of the second stage: flat for `u0 = 0`, capped at 181, and scaled.
#guard phase2Offset 11 0.0 1000.0 == 11 && phase2Offset 500 0.0 1000.0 == 181 &&
  phase2Offset 11 1.6e6 1.6e6 == 6 && phase2Offset 11 1.6e6 1.0 == 0

-- The fraction of the excluded valuations: `v_3(b) = 1` and `v_3(b) = 2`.
#guard Id.run (forbiddenFraction 3 0b110) == (1.0 / 3.0) * (1.0 - 1.0 / 3.0) +
  (1.0 / 3.0 / 3.0) * (1.0 - 1.0 / 3.0)

-- The padding of a cut end: for the stride 1 and `H = 255` the bits `-255, …, 255`, one bit below
-- the first and none above the last.
#guard clippedPadding ⟨1, 0, 0, none⟩ 255 0.0 0.0 == (1.0, 0.0)

end Ratpoints

end
