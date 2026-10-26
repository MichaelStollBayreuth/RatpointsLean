/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Costs
public import Ratpoints.Model.Params

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Costs

/-!
# The choice of the moduli

ratpoints chooses the moduli of its sieve and the cut points of its stages from the curve
(`sieving_info`, which the model has with stage I). This module holds the components of that choice
that work on the pool of the candidate moduli (`Ratpoints.ModulusCandidate`): the sieve entry and
the candidate of a prime that says something; the composite moduli, the prime powers and products
of them below `RATPOINTS_COMPOSITE_MAX` whose tables the run can pay for (`Ratpoints.addModuli`),
with the sieve entry of a composite modulus taken (`Ratpoints.makeModulus`); the first stage by its
rule and the second by its offset, each taking the candidates in the order of their keys and passing
over one that shares a prime with one taken (`Ratpoints.takeEntries`, `Ratpoints.firstStages`); and
the third stage by its cost rule, which may look at further primes (`Ratpoints.thirdStage`). The
search does not call them yet: the loop of the tables, which fills the pool, and the choice that
runs these components come with stage I.

## Main definitions

* `Ratpoints.primeEntry`, `Ratpoints.ModulusCandidate.ofPrime`: the sieve entry and the candidate
  of a prime.
* `Ratpoints.addModuli`: the composite moduli offered.
* `Ratpoints.makeModulus`: the sieve entry of a composite modulus taken.
* `Ratpoints.takeEntries`, `Ratpoints.firstStages`: the candidates that a stage takes, and the
  first two stages.
* `Ratpoints.thirdStage`: the third stage.
-/

@[expose] public section

namespace Ratpoints

open Sieve

/-! ### The candidates of the primes -/

/-- The sieve entry of the prime `p` of the table `t` with the density `r`, as `examine_prime` makes
it: its one factor, its reciprocal (`Ratpoints.Sieve.magic`), the bias `p ⌈Ratpoints.rowBias / p⌉`,
the inverse of `Ratpoints.rbaLength` modulo `p` from its table of inverses at the remainder of
`Ratpoints.rbaLength` by the multiplication with the reciprocal, the inverses of the strides empty,
the reference to its own table of rows, the builder of the build for `p`
(`Ratpoints.Sieve.sieveInit`), the density and the count `0` of factors.

It models no C code of its own: it is the part of `examine_prime` that makes the sieve entry
(`find_points.c:1795-1819`, in the range of `Ratpoints.Sieve.examinePrime?`), as a value. -/
def primeEntry (t : Entry) (r : Float) : SieveEntry :=
  let p := t.p
  { p, factors := [.prime t], magic := magic p, bias := p * ((rowBias + p - 1) / p),
    rbainv := t.inverses[mulMod rbaLength p (magic p)]!, dinv := #[], ref := .prime p,
    init := sieveInit p, r, nf := 0 }

/-- The candidate of the prime of the table `t`, at the position `pn` of `Ratpoints.primeTable`,
with the density `r` and the code `code` of its examination (`Ratpoints.Sieve.examinePrime?`): the
density, the prime, the mask `2 ^ pn` for `pn < 64` and `0` otherwise, the count `-1` of factors for
the code `2`, when the prime says only that numerator and denominator are coprime, and `0`
otherwise, and its sieve entry (`Ratpoints.primeEntry`); the key and the cost are set by the caller.

C: `find_points.c:1782-1785`

Deviation: the record returned, for the record `prec_entry` that `examine_prime` fills, its key and
cost `0.0` until the caller sets them, where the C code leaves them as they are; the count `-1` read
from the code, which is `2` exactly when `np ≥ p`. -/
def ModulusCandidate.ofPrime (pn : Nat) (t : Entry) (r : Float) (code : Nat) : ModulusCandidate :=
  { r, key := 0.0, cost := 0.0, p := t.p, mask := if pn < 64 then 1 <<< pn.toUInt64 else 0,
    ssp := some (primeEntry t r), nf := if code == 2 then -1 else 0, fac := [] }

/-! ### The composite moduli -/

/-- The prime powers examined so far by `add_moduli`: the records of the useful ones, by their index
(`pws`), and for each prime power `p ^ e` examined, by the position `pn` of `p` and the exponent
`e`, its index, or none when it says nothing (`pw_idx`).

C: `find_points.c:2350`, `find_points.c:2352-2354`, `find_points.c:2358-2359`

Deviation: a structure for the buffer `pws`, the count `npw` of its records and the array `pw_idx`
of indices with its markers `-1` (not examined) and `-2` (useless): an array of the records, and a
list of the pairs examined with an option, `none` for `-2`, a pair not in the list for `-1`. -/
structure PowerTable where
  /-- The records of the useful prime powers, by their index. -/
  pws : Array Power := #[]
  /-- The prime powers examined, by the position of their prime and their exponent: the index of
  the record, or none when it says nothing. -/
  idx : List ((Nat × Nat) × Option Nat) := []

/-- The index of the prime power `p ^ e`, `p` at the position `pn` of the table, among the useful
prime powers of `tab`, examining it when it is examined for the first time
(`Ratpoints.Sieve.examinePower`, with `pinf` whether denominators divisible by `p` occur), and none
when it says nothing (`Ratpoints.Sieve.Power.useful`).

C: `find_points.c:2387-2394`

Deviation: the table passed and returned, for the buffer `pws`, the count `npw` and the array
`pw_idx` of `add_moduli`; no test of room in the buffer (line 2390), which never fails, since
`add_moduli` examines each prime power at most once and `num_powers` counts them all. -/
def powerIndex (c : List Int) (d : Nat) (useCLong pinf : Bool) (pn p e : Nat) (tab : PowerTable) :
    Id (Option Nat × PowerTable) := do
  match tab.idx.lookup (pn, e) with
  | some i => return (i, tab)
  | none =>
    let pw ← examinePower c d p e useCLong pinf
    let i := if pw.useful then some tab.pws.size else none
    return (i, {
      pws := if pw.useful then tab.pws.push pw else tab.pws
      idx := ((pn, e), i) :: tab.idx })

/-- The state of the factorization of a candidate modulus in `add_moduli`: the cofactor left, the
position of the next prime, whether the candidate is still possible, the product of the densities
of the factors, the mask of their primes, their codes and the table of the prime powers examined.

C: `find_points.c:2362`, `find_points.c:2364-2365`

Deviation: a structure for the local variables of the loop over the candidates. -/
structure FacState where
  /-- The cofactor left. -/
  rest : Nat
  /-- The position of the next prime of the table. -/
  pn : Nat := 0
  /-- Whether the candidate is still possible. -/
  ok : Bool := true
  /-- The product of the densities of the factors. -/
  r : Float := 1.0
  /-- The mask of the primes of the factors. -/
  mask : UInt64 := 0
  /-- The codes of the factors. -/
  fac : Array Nat := #[]
  /-- The prime powers examined. -/
  tab : PowerTable

/-- The state `st` of the factorization with the factor `p ^ e`, `p` at the position `st.pn`:
refused when it would be the `Ratpoints.maxFactors`-th factor or more, or `p` is beyond the first 64
primes; for `e = 1` the density of the prime from the loop of the tables (`primeSe`), refused when
the prime says nothing; for `e > 1` that of the prime power (`Ratpoints.powerIndex`), refused when
it says nothing; the code of the factor and the bit of its prime.

C: `find_points.c:2381-2386`, `find_points.c:2395-2398`

Deviation: the densities of the primes from the array `primeSe` of the tables and densities of the
loop of the tables, for the entries `prime_se` and their fields `r`. -/
def takeFactor (c : List Int) (d : Nat) (useCLong : Bool) (primeSe : Array (Option (Entry × Float)))
    (pinf : Array Bool) (p e : Nat) (st : FacState) : Id FacState := do
  if maxFactors ≤ st.fac.size || 64 ≤ st.pn then return { st with ok := false }
  if e = 1 then
    match primeSe.getD st.pn none with
    | none => return { st with ok := false }
    | some (_, rp) => return { st with
        r := st.r * rp, fac := st.fac.push st.pn, mask := st.mask ||| 1 <<< st.pn.toUInt64
        pn := st.pn + 1 }
  let (i, tab) ← powerIndex c d useCLong (pinf.getD st.pn false) st.pn p e st.tab
  match i with
  | none => return { st with ok := false, tab }
  | some i => return { st with
      r := st.r * tab.pws[i]!.r, fac := st.fac.push (numPrimes + i)
      mask := st.mask ||| 1 <<< st.pn.toUInt64, pn := st.pn + 1, tab }

/-- The factorization of the candidate `m` over the first `pnLim` primes of the table, from the
state `st` (`Ratpoints.FacState`), as `add_moduli` makes it: for the primes `p` in turn, while the
candidate is possible and the cofactor above `1`, a cofactor below `p ^ 2`, a prime, is looked up
among the primes from `p` on and refused when it is not among the first `pnLim`; a prime that does
not divide the cofactor is passed over; else it is divided off as often as it divides and taken as
a factor (`Ratpoints.takeFactor`).

C: `find_points.c:2370-2380`, `find_points.c:2399`

Deviation: a `while` loop with the position of the prime in the state, for the loop `for` whose
variable `pn` the search for the prime below `p ^ 2` advances; natural numbers for the `long`s. -/
def factorCandidate (c : List Int) (d : Nat) (useCLong : Bool)
    (primeSe : Array (Option (Entry × Float))) (pinf : Array Bool) (pnLim : Nat) (st : FacState) :
    Id FacState := do
  let mut st := st
  while st.ok && 1 < st.rest && st.pn < pnLim do
    let mut p := primeTable[st.pn]!
    if st.rest < p * p then
      let mut pn := st.pn
      while pn < pnLim && primeTable[pn]! < st.rest do pn := pn + 1
      if pnLim ≤ pn || primeTable[pn]! != st.rest then return { st with ok := false }
      st := { st with pn }
      p := st.rest
    if st.rest % p != 0 then
      st := { st with pn := st.pn + 1 }
      continue
    let mut (rest, e) := (st.rest, 0)
    while rest % p = 0 do (rest, e) := (rest / p, e + 1)
    st ← takeFactor c d useCLong primeSe pinf p e { st with rest }
  return st

/-- The candidate of the odd composite `m`, as `add_moduli` offers it, or none, with the table of
the prime powers examined: none when its table alone is too dear for the run of `U` words and `D`
denominators (`ct m min(D, m) / U` above `Ratpoints.modulusTableMax`), when it does not factor over
the primes looked at into factors that say something (`Ratpoints.factorCandidate`), when it is a
prime, and when the product of the densities of its factors is not below `1`; else its density, its
mask and the codes of its factors, and its count of factors.

C: `find_points.c:2363`, `find_points.c:2368`, `find_points.c:2400-2402`, `find_points.c:2404-2406`

Deviation: the candidate returned, for the record `prec[pnp]` that `add_moduli` fills, with the key
and the cost `0.0`, which the caller sets, and no sieve entry. -/
def offerModulus (c : List Int) (d : Nat) (useCLong : Bool)
    (primeSe : Array (Option (Entry × Float))) (pinf : Array Bool) (pnLim : Nat) (ct U D : Float)
    (m : Nat) (tab : PowerTable) : Id (Option ModulusCandidate × PowerTable) := do
  let builds := if D < Float.ofNat m then D else Float.ofNat m
  if modulusTableMax < ct * Float.ofNat m * builds / U then return (none, tab)
  let st ← factorCandidate c d useCLong primeSe pinf pnLim { rest := m, tab }
  if !st.ok || 1 < st.rest then return (none, st.tab)
  if st.fac.size == 1 && st.fac[0]! < numPrimes then return (none, st.tab)
  if 1.0 ≤ st.r then return (none, st.tab)
  return (some {
    r := st.r, key := 0.0, cost := 0.0, p := m, mask := st.mask, ssp := none, nf := st.fac.size
    fac := st.fac.toList }, st.tab)

/-- The pool `pool` of the candidates with the composite moduli offered (`Ratpoints.offerModulus`),
the odd `m` from 9 below `Ratpoints.maxPrimeEven` and up to `Ratpoints.compositeMax`, each keyed for
the first stage (`Ratpoints.phase1Key`), until the pool holds `Ratpoints.numPrimes +
Ratpoints.maxModuli` candidates; with the useful prime powers examined, by their index.

C: `find_points.c:2346-2349`, `find_points.c:2351`, `find_points.c:2355-2356`, `find_points.c:2361`,
`find_points.c:2403`, `find_points.c:2407-2411`

Deviation: the pool passed and returned, for the array `prec` and the count `pnp`, and the records
of the prime powers returned, for the buffer `pws` of the arguments; the tables and the densities of
the primes of the loop of the tables (`primeSe`) and whether denominators divisible by them occur
(`pinf`) as arrays by their positions; the estimates of the run as arguments, for the fields of the
arguments; a `while` loop over the candidates; natural numbers for the `long`s; no bound `npw_max`
(`num_powers`, line 2351), which never binds. -/
def addModuli (c : List Int) (d : Nat) (useCLong : Bool) (pool : Array ModulusCandidate)
    (primeSe : Array (Option (Entry × Float))) (pinf : Array Bool) (pnLim : Nat)
    (ct cc U D : Float) : Id (Array ModulusCandidate × Array Power) := do
  let mut pool := pool
  let mut tab : PowerTable := {}
  let mut m := 9
  while m < maxPrimeEven && m ≤ compositeMax do
    let (e?, tab') ← offerModulus c d useCLong primeSe pinf pnLim ct U D m tab
    tab := tab'
    if let some e := e? then
      if numPrimes + maxModuli ≤ pool.size then break
      pool := pool.push (phase1Key ct U D cc e)
    m := m + 2
  return (pool, tab.pws)

/-- The sieve entry of the composite modulus `e`, at the position `n` of the moduli, as `make_power`
and `make_modulus` make it from the codes of its factors: a code below `Ratpoints.numPrimes` the
table of the prime at that position from the loop of the tables (`primeSe`), another the record of
the prime power of its index (`pws`); a prime power, one factor, with the reference to its own table
of rows and the builder of a prime power; a product with the reference to its own table of rows by
its position and the builder of a product; the reciprocal, the bias, the inverse of
`Ratpoints.rbaLength` by the extended Euclidean algorithm (`Ratpoints.Sieve.modinv`), the density of
the candidate and its count of factors.

C: `find_points.c:2414-2426`, `find_points.c:2428-2429`, `find_points.c:2434-2470`,
`find_points.c:2472-2475`

Deviation: the entry returned as a fresh value, for the space that `make_power` and `make_modulus`
take from the buffer of the sieve entries, and the entry of a prime power made for each modulus that
needs it, where `make_modulus` makes it once and keeps it by its index (`power_se`), with the
density of the first modulus that makes it, the density of the prime power in both cases; the
factors as a list (`Ratpoints.Sieve.Factor`), the tables of a prime from the loop of the tables and
the records of the prime powers, for the pointers `factor` to their entries; the tables of rows,
which `make_power` (line 2427) and `make_modulus` (line 2471) clear, made in the store of the run
after the choice (`Ratpoints.Sieve.SieveEntry.addTables`). -/
def makeModulus (e : ModulusCandidate) (n : Nat) (primeSe : Array (Option (Entry × Float)))
    (pws : Array Power) : Id SieveEntry := do
  let m := e.p
  let factors := e.fac.map fun code ↦
    if code < numPrimes then .prime ((primeSe.getD code none).elim default (·.1))
    else .power pws[code - numPrimes]!
  let (ref, init) := SieveEntry.refInit n factors
  return {
    p := m, factors, magic := magic m, bias := m * ((rowBias + m - 1) / m)
    rbainv := ← modinv (rbaLength % m) m, dinv := #[], ref, init, r := e.r, nf := e.nf }

/-! ### The stages -/

/-- The pool `pool` with the candidates whose mask meets `used` dropped from the position `start`
on, in their order.

C: `find_points.c:2509-2518` -/
def dropUsed (pool : Array ModulusCandidate) (start : Nat) (used : UInt64) :
    Id (Array ModulusCandidate) := do
  let mut pool := pool
  let mut k := start
  while k < pool.size do
    if pool[k]!.mask &&& used != 0 then pool := pool.eraseIdxIfInBounds k
    else k := k + 1
  return pool

/-- The candidates that one stage takes from the pool `pool`, from the position `start` on, in the
order they are in, with the mask `used` of the primes of the moduli taken and the product `rate` of
their densities: a candidate that shares a prime with one taken is dropped from the pool; with
`want ≥ 0` that many are taken, and with `want < 0` the rule of the first stage decides
(`Ratpoints.phase1Wants`, with the bits per word `bpw`, the target and the offset `extra` of the
second stage); then every later candidate that shares a prime with one taken is dropped
(`Ratpoints.dropUsed`). Returns the pool, the mask, the product of the densities and the number
taken.

C: `find_points.c:2490-2508`, `find_points.c:2519-2520`

Deviation: the pool, the mask and the product passed and returned, for the pointers `prec`, `pnp`,
`used` and `rate`; an integer for the `long` `want` and natural numbers for the other `long`s; the
candidate dropped by `Array.eraseIdxIfInBounds`, for the loop that moves the rest down. -/
def takeEntries (pool : Array ModulusCandidate) (start : Nat) (used : UInt64) (want : Int)
    (rate bpw target : Float) (extra : Nat) :
    Id (Array ModulusCandidate × UInt64 × Float × Nat) := do
  let mut (pool, used, rate) := (pool, used, rate)
  let mut n := start
  let mut taken : Nat := 0
  while n < pool.size do
    if pool[n]!.mask &&& used != 0 then
      pool := pool.eraseIdxIfInBounds n
      continue
    let stop ← if 0 ≤ want then pure (decide (want ≤ (taken : Int)))
      else (!·) <$> phase1Wants pool n pool.size taken bpw rate target extra
    if stop then break
    used := used ||| pool[n]!.mask
    rate := rate * pool[n]!.r
    n := n + 1
    taken := taken + 1
  return (← dropUsed pool n used, used, rate, taken)

/-- The pool `pool` keyed again for the second stage from the position `sp1` on, when there are
candidates left: the product `rate` of the densities of the first stage times the bits per word
swept `bpws`, and the key of each candidate left (`Ratpoints.primeKey` with the cost `COST_PHASE2
rate` per word, its table and the run of `U` words and `D` denominators), then those sorted by
their keys; with the product.

C: `find_points.c:2853-2863`

Deviation: the sort by `qsort` with `compare_entries` as Lean's stable merge sort
(`Ratpoints.sortFrom`), which gives the order of glibc's `qsort`, stable when it can allocate its
buffer, as always in the model, also on ties, since the keys are finite or `+∞`. -/
def rankSecond (pool : Array ModulusCandidate) (sp1 : Nat) (rate bpws ct U D : Float) :
    Array ModulusCandidate × Float :=
  if sp1 < pool.size then
    let rate := rate * bpws
    let pool := pool.mapIdx fun n e ↦
      if sp1 ≤ n then { e with key := primeKey e.r e.p (costPhase2 * rate) true ct U D } else e
    (sortFrom pool sp1 ModulusCandidate.keyLe, rate)
  else (pool, rate)

/-- The pool `pool` with the candidates from the position `sp2` on that are not primes that say more
than coprimality dropped (count of factors not `0`): the composite moduli not taken and the primes
that say only that numerator and denominator are coprime.

C: `find_points.c:2879-2890` -/
def dropComposites (pool : Array ModulusCandidate) (sp2 : Nat) : Id (Array ModulusCandidate) := do
  let mut pool := pool
  let mut n := sp2
  while n < pool.size do
    if pool[n]!.nf != 0 then pool := pool.eraseIdxIfInBounds n
    else n := n + 1
  return pool

/-- The pool `pool` with the sieve entries of the composite moduli among its first `sp2` candidates
made (`Ratpoints.makeModulus`), each at its position.

C: `find_points.c:2894-2900`

Deviation: the entries kept in the candidates, for the array `sieve_list` into which `sieving_info`
puts them (line 2898), which the caller reads from the candidates. -/
def stageEntries (pool : Array ModulusCandidate) (sp2 : Nat)
    (primeSe : Array (Option (Entry × Float))) (pws : Array Power) :
    Id (Array ModulusCandidate) := do
  let mut pool := pool
  for n in [0:sp2] do
    if pool[n]!.ssp.isNone then
      let se ← makeModulus pool[n]! n primeSe pws
      pool := pool.set! n { pool[n]! with ssp := some se }
  return pool

/-- The first two stages of the choice on the pool `pool`, sorted by keys, for the options `s`, the
target, the cost `ct` of a row, the estimate `est`, the bits per word swept `bpws` and the offset
`sp2e` of the second stage: the first stage takes the value of `-n` candidates when given, and
otherwise as many as its rule wants (`Ratpoints.takeEntries`); the rest keyed again
(`Ratpoints.rankSecond`); the second takes the value of `-N` minus the first when given, else
`sp2e`, at least `0`; then the composite moduli and the primes that say only coprimality dropped
from the end of the second stage on (`Ratpoints.dropComposites`). Returns the pool and the two cut
points.

C: `find_points.c:2843-2846`, `find_points.c:2864-2871`

Deviation: integers for the `long`s that may be negative. -/
def firstStages (pool : Array ModulusCandidate) (s : SieveOptions) (target ct : Float)
    (est : RunEstimate) (bpws : Float) (sp2e : Nat) : Id (Array ModulusCandidate × Nat × Nat) := do
  let (pool, used, rate, sp1) ← takeEntries pool 0 0 s.sp1 1.0 bpws target sp2e
  let (pool, rate) := rankSecond pool sp1 rate bpws ct est.words est.denoms
  let want : Int := if 0 ≤ s.sp2 then s.sp2 - sp1 else sp2e
  let (pool, _, _, taken) ← takeEntries pool sp1 used (max 0 want) rate 0.0 0.0 0
  return (← dropComposites pool (sp1 + taken), sp1, sp1 + taken)

/-! ### The third stage -/

/-- The position of the candidate of least density in the pool `pool` from the position `sp3` on,
the first of them on ties; none when there is none.

C: `find_points.c:2955-2961` -/
def bestByR (pool : Array ModulusCandidate) (sp3 : Nat) : Id (Option Nat) := do
  if pool.size ≤ sp3 then return none
  let mut best := sp3
  for m in [sp3 + 1:pool.size] do
    if pool[m]!.r < pool[best]!.r then best := m
  return some best

/-- The mean density of the candidates of the pool that say more than coprimality (count of factors
`≥ 0`), `1` when there are none, the quality of a prime that the third stage expects to find.

C: `find_points.c:2982-2991` -/
def rTyp (pool : Array ModulusCandidate) : Id Float := do
  if pool.size = 0 then return 1.0
  let mut sum := 0.0
  let mut cnt := 0
  for e in pool do
    if 0 ≤ e.nf then
      sum := sum + e.r
      cnt := cnt + 1
  return if 0 < cnt then sum / Float.ofNat cnt else 1.0

/-- The state of the third stage: the pool, the end `sp3` of the stage, the survivors `S` expected
per denominator, and the number of primes looked at.

C: `find_points.c:2922`, `find_points.c:2933`

Deviation: a structure for the local variables of the stage. -/
structure ThirdState where
  /-- The pool of the candidates. -/
  pool : Array ModulusCandidate
  /-- The end of the third stage. -/
  sp3 : Nat
  /-- The survivors expected per denominator. -/
  S : Float
  /-- The number of primes looked at. -/
  pnLim : Nat

/-- The third stage with one more prime looked at, the prime at the position `st.pnLim` of the
table, when the stage finds no prime in the pool that pays for itself: none when the curve has no
points modulo it; the pool as it is when it says nothing or only coprimality; else its candidate
with its density as its key and the cost `0`.

C: `find_points.c:2976-2978`, `find_points.c:2994-3008` -/
def lookFurther (c : List Int) (d : Nat) (useCLong : Bool) (st : ThirdState) :
    Id (Option ThirdState) := do
  let pn := st.pnLim
  let ex ← examinePrime? c d primeTable[pn]! useCLong
  let st := { st with pnLim := pn + 1 }
  match ex with
  | none => return none
  | some (t, _, code, r) =>
    if code == 0 || code == 2 then return some st
    let e := ModulusCandidate.ofPrime pn t r code
    return some { st with pool := st.pool.push { e with key := r, cost := 0.0 } }

/-- The third stage from the state `st`, up to `sp3Want` primes in all, with the costs `perSurv` and
`perDenom` of a prime per survivor and per denominator: while the stage has fewer, the prime of
least density not yet taken (`Ratpoints.bestByR`) is taken, moved to the end of the stage, and the
survivors multiplied by its density, unless there is none or, with `-P` absent (`sp3Extra < 0`), it
does not pay for itself, `S (1 - perSurv - r) ≤ perDenom`; then, when the caller left the number of
primes to the library (`mayExtend`) and fewer than `Ratpoints.numPrimes` have been looked at, unless
with `-P` absent a prime of the mean density of the pool (`Ratpoints.rTyp`) would not pay for itself
either, one more prime is looked at (`Ratpoints.lookFurther`); otherwise the stage ends. The exit,
when the curve has no points modulo a prime looked at, returns that prime.

C: `find_points.c:2949-2950`, `find_points.c:2973-2975`, `find_points.c:2980-2981`,
`find_points.c:2992-2993`, `find_points.c:3009-3016`

Deviation: a `while` loop over the state, the candidates swapped by `Array.swapIfInBounds`; the
sieve entry of the prime taken kept in its candidate, for the array `sieve_list` (line 3014). -/
def thirdStage (c : List Int) (d : Nat) (useCLong mayExtend : Bool) (sp3Extra : Int)
    (sp3Want : Nat) (perSurv perDenom : Float) (st : ThirdState) : Id (Except Nat ThirdState) := do
  let mut st := st
  while st.sp3 < sp3Want do
    let best ← bestByR st.pool st.sp3
    let poor := match best with
      | none => true
      | some b => sp3Extra < 0 && st.S * (1.0 - perSurv - st.pool[b]!.r) ≤ perDenom
    if poor then
      if !mayExtend || numPrimes ≤ st.pnLim then break
      if sp3Extra < 0 && st.S * (1.0 - perSurv - (← rTyp st.pool)) ≤ perDenom then break
      let some st' ← lookFurther c d useCLong st | return .error primeTable[st.pnLim]!
      st := st'
      continue
    let b := best.getD st.sp3
    let pool := st.pool.swapIfInBounds st.sp3 b
    st := { st with pool, S := st.S * pool[st.sp3]!.r, sp3 := st.sp3 + 1 }
  return .ok st

/-- The survivors per denominator that the third stage expects at its start, for the estimate `est`
of the run, the mean bits per word `bpw` and the densities of the moduli of the first two stages:
the numerators per denominator `(U - pad) 64 / D`, times the bits per word `bpw / 64`, times the
densities of the moduli of the first two stages, times `Ratpoints.sp3Coprime` for the test for
common factors.

C: `find_points.c:2941-2947`

Deviation: `64` for `LONG_LENGTH`. -/
def survivorsAtThird (est : RunEstimate) (bpw : Float) (pool : Array ModulusCandidate) (sp2 : Nat) :
    Float :=
  let S := (est.words - est.pad) * 64.0 / est.denoms
  let S := (List.range sp2).foldl (fun S n ↦ S * pool[n]!.r) (S * (bpw / 64.0))
  S * sp3Coprime

/-! ### Examples -/

-- A stage takes the candidates in their order and passes over one that shares a prime with one
-- taken: with `want = 2`, of the candidates 3, 9 (the mask of 3), 5, 7 and 15 (the masks of 3 and
-- 5) it takes 3 and 5, drops 9 on the way and 15 after the last taken (`Ratpoints.dropUsed`), with
-- the mask of 3 and 5 and the product of the densities.
#guard
  let e (p : Nat) (mask : UInt64) : ModulusCandidate :=
    { r := 0.5, key := 0.0, cost := 0.0, p, mask, ssp := none, nf := 0, fac := [] }
  let (pool, used, rate, taken) :=
    Id.run (takeEntries #[e 3 1, e 9 1, e 5 2, e 7 4, e 15 3] 0 0 2 1.0 0.0 0.0 0)
  pool.map (·.p) == #[3, 5, 7] && used == 3 && rate == 0.25 && taken == 2

-- The composite moduli of `1 0 2` with the tables and the densities of the first four primes, as
-- the loop of the tables keeps them, of which 3 says nothing: 15 = 3 · 5 is not offered, 45 = 9 · 5
-- is, the prime power 9 saying something, and so are 35 = 5 · 7, 25 and 49; the prime 7 is no
-- composite modulus.
#guard
  let c : List Int := [1, 0, 2]
  let ex := (List.range 4).map fun pn ↦ Id.run (examinePrime? c 2 primeTable[pn]! true)
  let primeSe := (ex.map fun x ↦ x.bind fun (t, _, code, r) ↦
    if 0 < code then some (t, r) else none).toArray
  let pinf := (ex.map fun x ↦ x.elim false fun (t, _) ↦ t.isFSquare[t.p]!).toArray
  primeSe.map Option.isSome == #[false, true, true, true] &&
    [(15, false), (45, true), (35, true), (25, true), (49, true), (7, false)].all fun (m, b) ↦
      (Id.run (offerModulus c 2 true primeSe pinf 4 0.0 1.0 1.0 m {})).1.isSome == b

-- The third stage takes the candidate of least density, the first of them on ties, and none when
-- no candidate is left.
#guard
  let e (r : Float) (p : Nat) : ModulusCandidate :=
    { r, key := r, cost := 0.0, p, mask := 0, ssp := none, nf := 0, fac := [] }
  let pool := #[e 0.5 3, e 0.3 5, e 0.3 7, e 0.7 11]
  Id.run (bestByR pool 0) == some 1 && Id.run (bestByR pool 2) == some 2 &&
    Id.run (bestByR pool 4) == none

-- The third stage looking at one more prime: none for `20 6 -14 12 -10`, which has no points modulo
-- 3, the next prime; and for `1 2 3 4 5 6 7` the prime 5, which says something, as a candidate with
-- its density as its key.
#guard
  (Id.run (lookFurther [20, 6, -14, 12, -10] 4 true ⟨#[], 0, 1.0, 0⟩)).isNone &&
    (Id.run (lookFurther [1, 2, 3, 4, 5, 6, 7] 6 true ⟨#[], 0, 1.0, 1⟩)).map
      (fun st ↦ (st.pnLim, st.pool.map (·.p), st.pool.all fun e ↦ e.key == e.r)) ==
      some (2, #[5], true)

end Ratpoints

end
