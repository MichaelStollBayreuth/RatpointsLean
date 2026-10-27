/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Constants

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Constants

/-!
# The tables and the sieve entries

The tables from which the sieve makes its rows, each in its place in the C function
`find_points_work_1`: the table of a prime with the exit when the curve has no points modulo it, on
the coefficients reduced by the helper `mod` of the C code for `long`s or by the Euclidean `%` for
GMP integers, by Horner's rule with Barrett's reduction on a fixed schedule, handing back the
coefficients reduced modulo the prime (`Ratpoints.Sieve.examinePrime?`, `Ratpoints.Sieve.modLong`,
`Ratpoints.Sieve.hornerBarrett`), the tables of a prime power (`Ratpoints.Sieve.examinePower`), and
the sieve entry of a modulus, a prime, a prime power or a product of them, by its factors and with
the reciprocal of the modulus and what the packing of the numerators needs
(`Ratpoints.Sieve.SieveEntry`), with the admission test of the rows of a denominator
(`Ratpoints.Sieve.SieveEntry.admits`), the kinds of the builders of the rows
(`Ratpoints.Sieve.RowInit`) and the references to the entries that hold the tables of rows
(`Ratpoints.Sieve.EntryRef`). The reciprocal of a modulus gives the remainder and the quotient by a
multiplication on 64-bit words, with the high half of the 128-bit product from the products of the
32-bit halves (`Ratpoints.Sieve.magic`, `Ratpoints.Sieve.mulHi`, `Ratpoints.Sieve.mulMod`,
`Ratpoints.Sieve.mulDiv`), and the remainder of a `long` of either sign (`Ratpoints.Sieve.modMul`).
The table of a prime without the exit (`Ratpoints.Sieve.examinePrime`) is the reference of the table
with it, which gives the same table for `0 < p < Ratpoints.maxPrimeEven` whenever it gives one
(`Ratpoints.Sieve.examinePrime?_spec`). The tables that the build of ratpoints generates are
computed here: the squares and the inverses by `Ratpoints.Sieve.squaresMod` and
`Ratpoints.Sieve.inversesMod`, and the table `sieve_init` of the builders of the rows of the primes
by `Ratpoints.Sieve.sieveInit`; the row of `0` of a prime, `Ratpoints.Sieve.sieves0`, and the
builders of the rows are in `Ratpoints.Model.Rows`, and the admission tests here are their
reference. The loop of the tables (`Ratpoints.tablesLoop`, `Ratpoints.examineInLoop`), the sieve
entries of the primes and of the composite moduli (`Ratpoints.primeEntry`, `Ratpoints.makeModulus`)
and the prime powers that the composite moduli are made of (`Ratpoints.powerIndex`) are in
`Ratpoints.Model.Choice`; the sieve that reads the rows from the tables of rows of the run, and has
the missing ones built (`Ratpoints.Sieve.buildRows`), is in `Ratpoints.Model.Sieve`.

## Main definitions

* `Ratpoints.Sieve.squaresMod`, `Ratpoints.Sieve.inversesMod`: the squares and the inverses
  modulo `p`.
* `Ratpoints.Sieve.examinePrime`: the table of a prime, the reference of the table with the exit.
* `Ratpoints.Sieve.modLong`: the helper `mod` of the C code, the remainder of a `long` modulo a
  positive `long`.
* `Ratpoints.Sieve.barrett`, `Ratpoints.Sieve.hornerBarrett`: Barrett's reduction, and Horner's
  rule modulo a prime with it on a fixed schedule.
* `Ratpoints.Sieve.examinePrime?`: the table of a prime on the path through `long`s or GMP
  integers, with the coefficients reduced modulo the prime, the code of `examine_prime` and the
  density of the prime, or none when the curve has no points modulo the prime.
* `Ratpoints.Sieve.modinv`, `Ratpoints.Sieve.bitAt`, `Ratpoints.Sieve.setBitAt`,
  `Ratpoints.Sieve.Power`, `Ratpoints.Sieve.setSquareBits`, `Ratpoints.Sieve.unitInverses`,
  `Ratpoints.Sieve.powerDensity`, `Ratpoints.Sieve.setRevBits`, `Ratpoints.Sieve.Power.useful`,
  `Ratpoints.Sieve.examinePower`: the inverse modulo `m` by the extended Euclidean algorithm, a bit
  of a bit array of words read and set, and the tables of a prime power, with the bit array of the
  squares, the inverses of the units, its density and whether it says more than nothing.
* `Ratpoints.Sieve.magic`, `Ratpoints.Sieve.mulHi`, `Ratpoints.Sieve.mulMod`,
  `Ratpoints.Sieve.mulDiv`, `Ratpoints.Sieve.modMul`: the reciprocal of a modulus, the high half of
  the product of two 64-bit words, the remainder and the quotient by a multiplication with the
  reciprocal, and the remainder of a `long` of either sign.
* `Ratpoints.Sieve.Entry.admits`, `Ratpoints.Sieve.Power.admits`, `Ratpoints.Sieve.Factor`,
  `Ratpoints.Sieve.Factor.modulus`, `Ratpoints.Sieve.SieveEntry`,
  `Ratpoints.Sieve.SieveEntry.admits`, `Ratpoints.Sieve.survives`: the admission tests of the rows
  of a denominator for a prime, for a prime power, and for a modulus by its factors, with the
  modulus of a factor.
* `Ratpoints.Sieve.RowInit`, `Ratpoints.Sieve.sieveInit`, `Ratpoints.Sieve.EntryRef`: the kinds of
  the builders of the rows, that of a prime of the table, and the references to the entries that
  hold the tables of rows.
* `Ratpoints.Sieve.Factor.ref`, `Ratpoints.Sieve.Factor.init`, `Ratpoints.Sieve.SieveEntry.refInit`:
  the reference and the kind of the builder of the entry of a factor, and of the sieve entry of a
  modulus at its position.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The tables of a prime -/

/-- The squares modulo `p`, as a table of Booleans indexed by the residues: zero and the squares
of the odd residues `i < p`, as the generator of the tables of ratpoints marks them; for odd `p`,
the squares of `i` and of `p - i` agree, so these are all the squares.

C: `find_points.c:37`, `gen_find_points_h.c:69-88`

Deviation: a function of `p`, computed when it is called, for the row of `p` in the table
`squares` that the build generates and that `find_points.c` includes. -/
def squaresMod (p : Nat) : Array Bool :=
  (List.range' 1 (p / 2) 2).foldl (fun w i ↦ w.set! (i * i % p) true)
    ((Array.replicate p false).set! 0 true)

/-- The inverses modulo `p`, as a table indexed by the residues: `0` for `0`, and for every other
residue `b` the least `i ≥ 1` with `i b ≡ 1 (mod p)`, found by trial.

C: `find_points.c:37`, `gen_find_points_h.c:33-44`, `gen_find_points_h.c:90-100`

Deviation: a function of `p`, computed when it is called, for the row of `p` in the table `inverses`
that the build generates and that `find_points.c` includes; the trial stops before `p` and gives `0`
when it finds nothing, where `inv_mod_p` would not stop, which never happens for a prime `p` and a
residue other than `0`. -/
def inversesMod (p : Nat) : Array Nat :=
  (Array.range p).map fun b ↦ ((List.range' 1 (p - 1)).find? (· * b % p == 1)).getD 0

/-- Horner's rule modulo `p`: the value modulo `p` at `x` of the polynomial with the coefficient
list `cs`, constant term first, reduced at every step. -/
def evalMod (cs : List Nat) (p x : Nat) : Nat := cs.foldr (fun a v ↦ (a + x * v) % p) 0

/-- What the sieve keeps of a prime `p`: `p`, the table of `p + 1` entries, entry `x < p` whether
`f(x)` is a square modulo `p` and entry `p` whether there are points at infinity modulo `p`, and
the inverses modulo `p`.

C: `rp-private.h:542-555`

Deviation: only the fields that the rows of a prime read; the rows of the residues, which ratpoints
keeps in the field `sieve`, that of `0` from the build and the others made by `init` when a
denominator first needs them, are kept in the table of rows of the prime in the store of the run
(`Ratpoints.Sieve.EntryRef.prime`, `Ratpoints.Sieve.primeRows`), from which the run reads them and
into which it builds them (`Ratpoints.Sieve.setRows`, `Ratpoints.Sieve.buildRows`); the fields
`init`, `magic`, `nf`, `factor` and `pw` are those of the sieve entry `Ratpoints.Sieve.SieveEntry`,
of which the prime is the single factor, and so are `bias`, `rbainv`, `dinv` and the density `r`.
-/
structure Entry where
  /-- The prime. -/
  p : Nat
  /-- For each residue `x` modulo `p`, whether `f(x)` is a square modulo `p`; and at `p`, whether
  there are points at infinity modulo `p`. -/
  isFSquare : Array Bool
  /-- The inverses modulo `p` of the residues. -/
  inverses : Array Nat
  deriving Inhabited

/-- The table of the prime `p` for the polynomial `f` of degree `d` with the coefficient list `c`:
for each residue `x` modulo `p`, whether `f(x)` is a square modulo `p`, with `f(x)` by Horner's rule
modulo `p` (`Ratpoints.Sieve.evalMod`) on the coefficients reduced modulo `p` by the Euclidean `%`,
and the squares of `Ratpoints.Sieve.squaresMod`, and as entry `p` whether there are points at
infinity modulo `p`, for odd `d` or `c_d` a square modulo `p`; kept with `p` and the inverses modulo
`p` (`Ratpoints.Sieve.inversesMod`). It is the reference of the table of a prime with the exit,
`Ratpoints.Sieve.examinePrime?`, which models `examine_prime` and gives this table, on both of its
paths, for `0 < p < Ratpoints.maxPrimeEven` whenever it gives one
(`Ratpoints.Sieve.examinePrime?_spec`); the lemmas on the table and its rows are stated for it. -/
def examinePrime (c : List Int) (d p : Nat) : Entry :=
  let cs := (List.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : Int)).toNat
  let sq := squaresMod p
  { p, isFSquare := ((Array.range p).map fun x ↦ sq[evalMod cs p x]!).push
      (d % 2 == 1 || sq[cs.getD d 0]!), inverses := inversesMod p }

/-- The helper `mod` of the C code, the remainder of the `long` `a` modulo the `long` `b > 0`: for
`a < -16 b`, by C's division, which truncates (`Int.tmod`), with `b` added to a negative remainder;
for `a ≥ 16 b`, by C's division; and otherwise by adding `16 b` to a negative `a`, then subtracting
`8 b`, `4 b`, `2 b` and `b` where it can. For every integer `a` and every `b ≥ 0` it is the
Euclidean `%` (`Ratpoints.Sieve.modLong_eq_emod`). Its copy in `find_points.c` reduces, among
others, the coefficients in `examine_prime` and `examine_power` (`Ratpoints.Sieve.examinePrime?`,
`Ratpoints.Sieve.examinePower`) and a denominator above `Ratpoints.mulModLimit` in `fill_bp_list`
(`Ratpoints.Sieve.fillBpList`), and its copy in `sift.c` the row indices of the first two stages of
the sieve where they cannot be reduced by a multiplication with the reciprocal
(`Ratpoints.Sieve.andRows`, `Ratpoints.Sieve.chunkStarts`, `Ratpoints.Sieve.secondStage`,
`Ratpoints.Sieve.secondStageWord`).

C: `find_points.c:477-492`, `sift.c:370-389`

Deviation: one definition for the two copies of the function, in `find_points.c` and in `sift.c`,
which are the same but for the hooks of the counts of the reductions in `sift.c` (`RP_MOD_TICK`,
`RP_MOD_DIV`), empty unless `RP_MOD_COUNTS` is set; integers for the `long`s, with the obligations
that the values it computes stay in the range of a `long` stated as lemmas: for `0 ≤ b < 2 ^ 59`,
`16 b` (`Ratpoints.fitsLong_sixteen_mul`), its negation (`Ratpoints.fitsLong_neg`), and `a + 16 b`
for `-16 b ≤ a < 0` (`Ratpoints.fitsLong_add_sixteen_mul`), its other values lying between `-b` and
`16 b`; `Int.tmod` for C's division of `long`s, which truncates; the multiples `16 b`, `8 b`, `4 b`
and `2 b` as products, for the shifts of `b1`. -/
def modLong (a b : Int) : Int :=
  let b1 := 16 * b
  if a < -b1 then
    let a := a.tmod b
    if a < 0 then a + b else a
  else if 0 ≤ a ∧ b1 ≤ a then a.tmod b
  else
    let a := if a < 0 then a + b1 else a
    let a := if 8 * b ≤ a then a - 8 * b else a
    let a := if 4 * b ≤ a then a - 4 * b else a
    let a := if 2 * b ≤ a then a - 2 * b else a
    if b ≤ a then a - b else a

/-- The remainder of `u` modulo `p ≥ 1` by Barrett's reduction with the reciprocal `m`: the
quotient `⌊u m / 2 ^ 64⌋` times `p` subtracted from `u`, and `p` once more when the difference is
still at least `p`. For `m = ⌊(2 ^ 64 - 1) / p⌋` and `u < 2 ^ 64` the quotient is `⌊u / p⌋` or one
less, so that the result is `u % p`.

C: `find_points.c:1639-1650`

Deviation: natural numbers for the `unsigned long`s, the product `u m` exact as the 128-bit product
of the C code, and the difference exact, which does not wrap since the quotient times `p` is at most
`u` for `m ≤ (2 ^ 64 - 1) / p`; the obligation that `u` is below `2 ^ 64`, which the C type gives, a
hypothesis of the lemma that the result is `u % p` (`Ratpoints.Sieve.barrett_eq`); the form with the
128-bit product, which the modelled builds compile (the compiler defines `__SIZEOF_INT128__`,
and `RP_NO_INT128` is not set), for the division `u % p` of the other builds, which gives the same
remainder. -/
def barrett (u p m : Nat) : Nat :=
  let r := u - u * m / 2 ^ 64 * p
  if p ≤ r then r - p else r

/-- The value modulo the prime `p` at the residue `a` of the polynomial of degree `d` whose
coefficients reduced modulo `p` are `cm`, constant term first, as `examine_prime` computes it by
Horner's rule: from `cm[d]`, the steps `s ↦ s a + cm[n]` for `n = d - 1, …, 0`, and Barrett's
reduction with the reciprocal `recip` (`Ratpoints.Sieve.barrett`) at the end, for
`d ≤ Ratpoints.hornerSteps`; for larger `d` also after every `Ratpoints.hornerSteps` steps. For
`p < Ratpoints.maxPrimeEven`, `a < p`, the entries of `cm` below `p` and
`recip = ⌊(2 ^ 64 - 1) / p⌋`, the accumulator stays below `2 ^ 64`, and the value is that of
Horner's rule reduced at every step (`Ratpoints.Sieve.evalMod`).

C: `find_points.c:1724`, `find_points.c:1726-1731`, `find_points.c:1735`,
`find_points.c:1737-1744`

Deviation: the choice between the two branches made for each residue, where `examine_prime` makes it
once, around its loop over the residues; natural numbers for the `unsigned long` accumulator, with
the obligation that it stays below `2 ^ 64` stated as a lemma
(`Ratpoints.Sieve.HornerInvariant.lt_two_pow_64`); the steps counted up from `0` to
`d - 1`, for the index `n` that counts down. -/
def hornerBarrett (cm : Array Nat) (d p recip a : Nat) : Id Nat := do
  let mut s := cm[d]!
  if d ≤ hornerSteps then
    for i in [0:d] do
      s := s * a + cm[d - 1 - i]!
  else
    let mut k := 0
    for i in [0:d] do
      s := s * a + cm[d - 1 - i]!
      k := k + 1
      if k = hornerSteps then
        s := barrett s p recip
        k := 0
  return barrett s p recip

/-- The table of the prime `p` for the polynomial `f` of degree `d` with the coefficient list `c`,
as `examine_prime` makes it, with the flag `useCLong` of the `long`s (`Ratpoints.Setup.useCLong`),
and the coefficients reduced modulo `p`, which it hands back: the coefficients reduced on the path
that the flag chooses, by the helper `mod` of the C code (`Ratpoints.Sieve.modLong`) for `long`s and
by the Euclidean `%` for GMP integers (`mpz_fdiv_r_ui`), two paths with the same result
(`Ratpoints.Sieve.examinePrime?_eq_examinePrime?_false`); entry `0` of the table, whether `c_0` is
a square modulo `p` (`Ratpoints.Sieve.squaresMod`); then, in the loop over the residues
`a = 1, …, p - 1`, whether `f(a)` is a square modulo `p`, by Horner's rule with Barrett's reduction
on its fixed schedule (`Ratpoints.Sieve.hornerBarrett`, with the reciprocal `⌊(2 ^ 64 - 1) / p⌋`);
entry `p`, whether there are points at infinity modulo `p`, for odd `d` or `c_d` a square modulo
`p`; and `none` when the curve has no points modulo `p`, no entry of the table being true, where
`examine_prime` returns `-1` and the search ends with no points. Otherwise the entry with `p`, the
table and the inverses modulo `p` (`Ratpoints.Sieve.inversesMod`), that of the reference
`Ratpoints.Sieve.examinePrime` for `0 < p < Ratpoints.maxPrimeEven`
(`Ratpoints.Sieve.examinePrime?_spec`), with the array of the `d + 1` coefficients reduced modulo
`p`, the code of `examine_prime` and the density of the prime: the code `0` when `f(x)` is a square
modulo `p` for every residue, `np = p` in the count `np` of the residues with a square value, and
there are no points at infinity modulo `p`, so that the prime says nothing; else the density `r`,
`(np + 1)(p - 1) / p ^ 2` with points at infinity modulo `p` and `np / p` without, in doubles, and
the code `2` for `np = p`, when the prime says only that numerator and denominator are coprime, and
`1` otherwise. A curve without points modulo a prime has no points
(`Ratpoints.Sieve.not_isPoint_of_run_examinePrime?_eq_none`).

C: `find_points.c:1683-1697`, `find_points.c:1703-1723`, `find_points.c:1725`,
`find_points.c:1732-1734`, `find_points.c:1736`, `find_points.c:1745-1749`,
`find_points.c:1761-1781`, `find_points.c:1795-1819`, `find_points.c:1822-1826`

Deviation: the prime `p` itself, for its index `pn` in the table `prime`; the table a fresh array of
`p + 1` entries, for the integers that `examine_prime` takes from the buffer `int_next` and hands
back through `is_f_square_p`, and the coefficients a fresh array returned with the entry, for the
array `coeffs_mod_p` of its caller, which it fills; one loop over the residues, for the two loops of
the two branches of the schedule of Horner's rule, between which `Ratpoints.Sieve.hornerBarrett`
chooses for each residue; the exit `-1` as `none`, and the codes `0`, `1` and `2` returned with the
entry, the coefficients and the density, as natural numbers, the entry made and returned for the
code `0` too, where `examine_prime` makes none, and the density `0.0` for that code, which
`examine_prime` does not compute; the fields `p`, `mask` and `nf` of the record `prec_entry` of the
ranking, which `examine_prime` sets with the density (lines 1782-1785), made by the caller from the
table, the position of the prime and the code (`Ratpoints.ModulusCandidate.ofPrime`); the entry is a
fresh value, for the space that `examine_prime` takes from the buffer of the sieve entries
(`se_next`), and returned, where `examine_prime` stores it in the field `ssp` of `prec_entry`; it
keeps only `p`, the table and the inverses (`Ratpoints.Sieve.Entry`), and no rows: the table of rows
of the prime, with the row of `0` from the build and the others absent (lines 1820-1821,
`Ratpoints.Sieve.primeRows`), is made in the store of the run by the loop of the tables when the
prime says something (`Ratpoints.examineInLoop`), and for a prime that the third stage takes into
the pool by the end of the choice (`Ratpoints.choiceEnd`, with
`Ratpoints.Sieve.SieveEntry.addTables`); the fields `init`, `nf` and `pw` that `examine_prime` sets
(lines 1800 and 1817) and its reciprocal `magic` (line 1808) are those of the sieve entry of the
prime (`Ratpoints.Sieve.SieveEntry`), of which the prime is the single factor, made by the entries
that the choice of the moduli makes (`Ratpoints.primeEntry`), which set the reciprocal there, and so
are the bias `bias`, the inverse `rbainv` of `Ratpoints.rbaLength`, the density and the count of
factors (lines 1811 and 1815-1817), which they set there with the formulas of these lines. -/
def examinePrime? (c : List Int) (d p : Nat) (useCLong : Bool) :
    Id (Option (Entry × Array Nat × Nat × Float)) := do
  let cm := (Array.range (d + 1)).map fun n ↦
    (if useCLong then modLong (c.getD n 0) p else c.getD n 0 % (p : Int)).toNat
  let sq := squaresMod p
  let recip := (2 ^ 64 - 1) / p
  let mut np := if sq[cm[0]!]! then 1 else 0
  let mut isFSquare := #[sq[cm[0]!]!]
  for a in [1:p] do
    let s ← hornerBarrett cm d p recip a
    isFSquare := isFSquare.push sq[s]!
    if sq[s]! then np := np + 1
  let atInf := d % 2 == 1 || sq[cm[d]!]!
  isFSquare := isFSquare.push atInf
  if np == 0 && !atInf then return none
  let e : Entry := { p, isFSquare, inverses := inversesMod p }
  if p ≤ np && !atInf then return some (e, cm, 0, 0.0)
  let r : Float := if atInf then Float.ofNat ((np + 1) * (p - 1)) / Float.ofNat (p * p)
    else Float.ofNat np / Float.ofNat p
  return some (e, cm, if p ≤ np then 2 else 1, r)

/-! ### The tables of a prime power -/

/-- The inverse of `x` modulo `m` for `x` prime to `m`, by the extended Euclidean algorithm: from
`r₀ = m`, `r₁ = x mod m` and the cofactors `s₀ = 0`, `s₁ = 1`, which keep `rᵢ ≡ sᵢ x (mod m)`,
while `r₁ ≠ 0`, with `q = ⌊r₀ / r₁⌋`, `(r₀, r₁)` becomes `(r₁, r₀ - q r₁)` and `(s₀, s₁)` becomes
`(s₁, s₀ - q s₁)`; then `s₀`, plus `m` if it is negative.

C: `find_points.c:2241-2252`

Deviation: natural numbers for `x`, `m` and the remainders, which are never negative for `x ≥ 0`,
so that the correction of a negative `x % m` has no counterpart; integers for the `long`
cofactors, which stay between `-m` and `m` (`Ratpoints.Sieve.ModinvInvariant.natAbs_add_mul_le`);
the result a natural number. -/
def modinv (x m : Nat) : Id Nat := do
  let mut r0 := m
  let mut r1 := x % m
  let mut s0 : Int := 0
  let mut s1 : Int := 1
  while r1 ≠ 0 do
    let q := r0 / r1
    let t := r0 - q * r1
    r0 := r1
    r1 := t
    let u := s0 - q * s1
    s0 := s1
    s1 := u
  return (if s0 < 0 then s0 + m else s0).toNat

/-- Bit `x` of the bit array `ws` of 64-bit words, bit `x mod 64` of word `⌊x / 64⌋`, as the C code
reads the bit arrays of the tables of a prime power and the local bit array of the squares of
`examine_power` (`RP_SQ_M`), `(ws[x >> LONG_SHIFT] >> (x & LONG_MASK)) & 1`, with the division and
the remainder by 64 for the shift and the mask. -/
def bitAt (ws : Array UInt64) (x : Nat) : Bool := (ws[x / 64]! >>> (x % 64).toUInt64) &&& 1 != 0

/-- The bit array `ws` of 64-bit words with bit `x` set, as the C code sets a bit of the bit arrays
of the tables of a prime power, of the local bit array of the squares of `examine_power` and of the
pattern of a row, `ws[x >> LONG_SHIFT] |= 1UL << (x & LONG_MASK)`, with the division and the
remainder by 64 for the shift and the mask. -/
def setBitAt (ws : Array UInt64) (x : Nat) : Array UInt64 :=
  ws.set! (x / 64) (ws[x / 64]! ||| 1 <<< (x % 64).toUInt64)

/-- What the sieve keeps of a prime power `m = p ^ e` for the polynomial `f` of degree `d`: `p`,
`e` and `m`; the bit array `fsq` of `Ratpoints.modWords` words, its bit `x < m`
(`Ratpoints.Sieve.bitAt`) set when `f(x)` is a square modulo `m`; the bit array `gsq` of
`modWords` words, its bit `t < m` set when `p ∣ t` and `frev(t)` is a square modulo `m`, for the
reversed polynomial `frev(t) = ∑ₖ cₖ t ^ (D - k)` of the even degree `D = d + d % 2`; and the
inverses modulo `m` of the units, `0` for the other residues; and the density `r` of the prime
power (`Ratpoints.Sieve.powerDensity`).

C: `rp-private.h:531-534`

Deviation: an array of `m` natural numbers for the `unsigned short` inverses, for an array sized by
`RATPOINTS_MAX_PRIME_EVEN`; no count `np`, which `examine_power` stores (`find_points.c:2304`) and
nothing reads. -/
structure Power where
  /-- The prime. -/
  p : Nat
  /-- The exponent. -/
  e : Nat
  /-- The modulus `p ^ e`. -/
  m : Nat
  /-- The bit array of `Ratpoints.modWords` words whose bit `x < m` is set when `f(x)` is a square
  modulo `m`. -/
  fsq : Array UInt64
  /-- The bit array of `Ratpoints.modWords` words whose bit `t < m` is set when `p ∣ t` and
  `frev(t)` is a square modulo `m`. -/
  gsq : Array UInt64
  /-- The inverses modulo `m` of the units, `0` for the other residues. -/
  inv : Array Nat
  /-- The density: the mean over the classes of the denominator modulo `m` of the share of the
  numerators that its row admits (`Ratpoints.Sieve.powerDensity`). -/
  r : Float
  deriving Inhabited

/-- The bit array `sq` of 64-bit words with the bits of the squares `x ^ 2 mod m` of the residues
`x < m` set (`Ratpoints.Sieve.setBitAt`), in `examine_power`.

C: `find_points.c:2283-2284`

Deviation: the bit array passed and returned, for the local array `sq` of `examine_power`; natural
numbers for the `long`s, the squares `x x` with `x < m` staying below `m ^ 2`, with the obligation
stated as a lemma (`Ratpoints.mul_self_lt_two_pow_63_of_lt_maxPrimeEven`). -/
def setSquareBits (m : Nat) (sq : Array UInt64) : Id (Array UInt64) := do
  let mut sq := sq
  for x in [0:m] do
    sq := setBitAt sq (x * x % m)
  return sq

/-- The inverses modulo the prime power `m = p ^ e` of the residues below `m`, as `examine_power`
makes them: `0` for the residue `0`, and then, in the loop over the residues `x = 1, …, m - 1`, the
inverse of a unit by the extended Euclidean algorithm (`Ratpoints.Sieve.modinv`) and `0` for the
other residues.

C: `find_points.c:2302-2303`

Deviation: the inverses a fresh array, returned, for the array `inv` of the entry `pw` that
`examine_power` fills; natural numbers for the `long`s and for the `unsigned short` inverses, which
are below `m`, with the obligation stated as a lemma
(`Ratpoints.Sieve.getElem!_inv_run_examinePower_lt_two_pow_16`). -/
def unitInverses (p m : Nat) : Id (Array Nat) := do
  let mut inv := #[0]
  for x in [1:m] do
    if x % p = 0 then inv := inv.push 0
    else inv := inv.push (← modinv x m)
  return inv

/-- The density of the prime power `m = p ^ e`, from the count `np` of the residues `x` with `f(x)`
a square modulo `m`, the bit array `gsq` of the multiples `t` of `p` with `frev(t)` a square modulo
`m` (`Ratpoints.Sieve.Power`), and whether denominators divisible by `p` occur at all (`pinf`, the
entry at infinity of the table of `p`), as `examine_power` computes it in doubles: with
`u = m - m / p` the number of the units, first `u np / m`; with `pinf`, for each valuation `v` from
`1` to `e` the count `good` of the residues `t` of the valuation `v` (all multiples of `p ^ e` for
`v = e`, and those whose quotient by `p ^ v` is prime to `p` for `v < e`) with bit `t` of `gsq` set,
`good u / m` added, and the sum divided by `m`; without `pinf`, `u np / m` divided by `u`.

C: `find_points.c:2306-2329`

Deviation: the density returned, for the field `r` of the record `pw` that `examine_power` sets;
natural numbers for the `long`s; the residues `t` stepped through by a `while` loop. -/
def powerDensity (p e m np : Nat) (gsq : Array UInt64) (pinf : Bool) : Id Float := do
  let units := Float.ofNat (m - m / p)
  let mut r := units * Float.ofNat np / Float.ofNat m
  if !pinf then return r / units
  let mut pv := p
  for v in [1:e + 1] do
    let mut good := 0
    let mut t := 0
    while t < m do
      if !(v < e && t / pv % p = 0) && bitAt gsq t then good := good + 1
      t := t + pv
    r := r + Float.ofNat good * units / Float.ofNat m
    pv := pv * p
  return r / Float.ofNat m

/-- The bit array `gsq` with the bits of the multiples `t = 0, p, 2 p, …` of `p` below `m` set at
which `frev(t)`, by Horner's rule modulo `m` on the reversed coefficients `cmD.reverse`
(`Ratpoints.Sieve.evalMod`), is a square modulo `m`, read from the bit array `sq` of the squares
(`Ratpoints.Sieve.bitAt`, `Ratpoints.Sieve.setBitAt`), as `examine_power` sets them.

C: `find_points.c:2294-2300`

Deviation: the bit array passed and returned, for the array of the entry `pw`; the variable `t` for
the multiples of `p`, where the C code reuses `x`; a `while` loop for the loop `for` with the step
`p`; natural numbers for the `long`s and `unsigned long`s. -/
def setRevBits (cmD : List Nat) (m p : Nat) (sq gsq : Array UInt64) : Id (Array UInt64) := do
  let mut gsq := gsq
  let mut t := 0
  while t < m do
    if bitAt sq (evalMod cmD.reverse m t) then gsq := setBitAt gsq t
    t := t + p
  return gsq

/-- Whether the prime power `pw` says more than nothing, the code that `examine_power` returns: its
density below `1 - 10 ^ -9`.

C: `find_points.c:2330`

Deviation: a Boolean read from the density of the record, for the code `1` or `0` that
`examine_power` returns. -/
def Power.useful (pw : Power) : Bool := pw.r < 1.0 - 1.0e-9

/-- The tables of the prime power `m = p ^ e` for the polynomial `f` of degree `d` with the
coefficient list `c`, as `examine_power` makes them, with the flag `useCLong` of the `long`s
(`Ratpoints.Setup.useCLong`): the coefficients `c_0, …, c_d` reduced modulo `m` on the path that the
flag chooses, by the helper `mod` of the C code (`Ratpoints.Sieve.modLong`) for `long`s and by the
Euclidean `%` for GMP integers (`mpz_fdiv_ui`), with `c_D = 0` for odd `d` and `D = d + 1`; the bit
arrays `sq`, `fsq` and `gsq` of `Ratpoints.modWords` words cleared in one loop; the bit array `sq`
of the squares `x ^ 2 mod m` of the residues `x`, set bit by bit (`Ratpoints.Sieve.setSquareBits`)
and read by `Ratpoints.Sieve.bitAt`; in the loop over the residues `x`, bit `x` of `fsq` set
(`Ratpoints.Sieve.setBitAt`) when `f(x)` is a square modulo `m`, by Horner's rule reduced at every
step (`Ratpoints.Sieve.evalMod`); in the loop over the multiples `t = 0, p, 2 p, …` of `p` below
`m`, bit `t` of `gsq` set when `frev(t) = ∑ₖ cₖ t ^ (D - k)` is a square modulo `m`, by Horner's
rule on the reversed coefficients (`Ratpoints.Sieve.setRevBits`); the inverses modulo `m` of the
units, `0` for the other residues (`Ratpoints.Sieve.unitInverses`); and the density of the prime
power from the count of the residues `x` with `f(x)` a square modulo `m` and the switch `pinf`
(`Ratpoints.Sieve.powerDensity`), whether denominators divisible by `p` occur.

C: `find_points.c:2267-2282`, `find_points.c:2285-2293`, `find_points.c:2301`, `find_points.c:2331`

Deviation: the tables returned as a fresh value, for the entry `pw` of the buffer of the prime
powers that `examine_power` fills; `m` as `p ^ e`, for the product of `e` factors `p`; the bit
arrays `sq`, `fsq` and `gsq` fresh arrays of `Ratpoints.modWords` words, which the loop at line 2282
clears, for the local array that the function leaves unset and the arrays of the entry `pw`; natural
numbers for the `long`s and `unsigned long`s, the variable `t` for the multiples of `p`, where the C
code reuses `x`, and the steps `v x + c` of Horner's rule, with `v`, `x` and `c` below `m`, staying
below `m ^ 2`, with the obligation stated as a lemma
(`Ratpoints.mul_add_lt_two_pow_64_of_lt_maxPrimeEven`); the code that `examine_power` returns read
from the density by `Ratpoints.Sieve.Power.useful`. -/
def examinePower (c : List Int) (d p e : Nat) (useCLong pinf : Bool) : Id Power := do
  let m := p ^ e
  let cm := (List.range (d + 1)).map fun k ↦
    (if useCLong then modLong (c.getD k 0) m else c.getD k 0 % (m : Int)).toNat
  let cmD := if d % 2 = 1 then cm ++ [0] else cm
  let mut sq : Array UInt64 := .replicate modWords 0
  let mut fsq : Array UInt64 := .replicate modWords 0
  let mut gsq : Array UInt64 := .replicate modWords 0
  for k in [0:modWords] do
    sq := sq.set! k 0
    fsq := fsq.set! k 0
    gsq := gsq.set! k 0
  sq ← setSquareBits m sq
  let mut np := 0
  for x in [0:m] do
    if bitAt sq (evalMod cm m x) then
      fsq := setBitAt fsq x
      np := np + 1
  gsq ← setRevBits cmD m p sq gsq
  return { p, e, m, fsq, gsq, inv := ← unitInverses p m, r := ← powerDensity p e m np gsq pinf }

/-! ### The reductions by a reciprocal -/

/-- The reciprocal `⌊(2 ^ 64 - 1) / p⌋ + 1` of the modulus `p ≥ 2`, which is `2 ^ 64 / p` rounded
up: with it, the remainder (`Ratpoints.Sieve.mulMod`) and the quotient (`Ratpoints.Sieve.mulDiv`) by
`p` of every `u` with `u p < 2 ^ 64` are computed by multiplications. The C code computes it as
`ULONG_MAX/p + 1` where it sets a field `magic`: in the sieve entries of the moduli, which
`examine_prime`, `make_power` and `make_modulus` make (lines 1808, 2422 and 2454 of `find_points.c`;
here `Ratpoints.primeEntry` and `Ratpoints.makeModulus`), in the tables of the Jacobi test (line
700; here `Ratpoints.Sieve.jacobiSetup`), and in the entries of the forbidden divisors tested with
words (lines 2648, 2668 and 2738; here `Ratpoints.Sieve.ForbiddenEntry.magic`), with which the C
code reduces the word number of the first word of a block (`Ratpoints.Sieve.forbStarts`). For
`p = 1`, which is no modulus, it is `2 ^ 64`, where `ULONG_MAX / 1 + 1` wraps to `0` in the C code;
the reductions, which read it as a 64-bit word, read `0` too. -/
def magic (p : Nat) : Nat := (2 ^ 64 - 1) / p + 1

/-- The high 64 bits of the 128-bit product of the 64-bit words `a` and `b`, `⌊a b / 2 ^ 64⌋`, from
the four products of their 32-bit halves: the high half of the low product and the low halves of the
two middle products make `mid`, whose high half is the carry into the high half of the result, the
high product plus the high halves of the middle products and the carry; no product and no partial
sum leaves the range of a 64-bit word. It is the shift by 64 bits of the 128-bit product of
`RP_MULMOD` (`Ratpoints.Sieve.mulMod`) and of `RP_MULDIV` (`Ratpoints.Sieve.mulDiv`).

C: `rp-private.h:404-408`, `rp-private.h:409-410`

Deviation: the high half of the product from the products of the 32-bit halves, for the product of
type `__uint128_t` that gcc provides and Lean core does not. -/
def mulHi (a b : UInt64) : UInt64 :=
  let a0 := a &&& 0xffffffff
  let a1 := a >>> 32
  let b0 := b &&& 0xffffffff
  let b1 := b >>> 32
  let mid := (a0 * b0) >>> 32 + ((a0 * b1) &&& 0xffffffff) + ((a1 * b0) &&& 0xffffffff)
  a1 * b1 + (a0 * b1) >>> 32 + (a1 * b0) >>> 32 + mid >>> 32

/-- The remainder of `u` modulo `p` by a multiplication with the reciprocal `m`, `RP_MULMOD`: the
low 64 bits of `m u`, times `p`, shifted right by 64 bits, on 64-bit words
(`Ratpoints.Sieve.mulHi`). For the reciprocal `m = Ratpoints.Sieve.magic p` of a modulus `p ≥ 1` it
is `u % p` whenever `u p < 2 ^ 64`, which the C code ensures by reducing only values below `2 ^ 32`
modulo moduli below `2 ^ 32`.

C: `rp-private.h:404-408`, `rp-private.h:411`, `rp-private.h:413-414`, `rp-private.h:417`

Deviation: natural numbers for the `unsigned long` reciprocal, the `long`s `u` and `p`, and the
`long` result, which is below `p`; the arguments converted to `UInt64`, as the macro converts `u`
and `p` to `unsigned long`s, so that the product `m u` wraps as the product of `unsigned long`s
does; the argument `u` a natural number, for the `long` that the C code passes non-negative; the
high half of the 128-bit product by `Ratpoints.Sieve.mulHi`; the form with the 128-bit product,
which the modelled builds compile (the compiler defines `__SIZEOF_INT128__`, and neither
`RP_MULMOD_DIVIDE` nor `RP_NO_INT128` is set), for the division `u % p` of the other builds, which
gives the same remainder where the multiplication is exact. -/
def mulMod (u p m : Nat) : Nat := (mulHi (m.toUInt64 * u.toUInt64) p.toUInt64).toNat

/-- The quotient of `u` by `p` by a multiplication with the reciprocal `m`, `RP_MULDIV`: the high 64
bits of `u m`, on 64-bit words (`Ratpoints.Sieve.mulHi`). For the reciprocal
`m = Ratpoints.Sieve.magic p` of a modulus `p ≥ 2` it is `u / p` whenever `u p < 2 ^ 64`.

C: `rp-private.h:409-410`, `rp-private.h:415-416`

Deviation: natural numbers for the `unsigned long` reciprocal, the `long` `u` and the `long`
result, the arguments converted to `UInt64`, as the macro converts `u` to an `unsigned long`; the
high half of the 128-bit product by `Ratpoints.Sieve.mulHi`; no argument `p`, which that form does
not read; the form with the 128-bit product, which the modelled builds compile, for the
division `u / p` of the other builds, which gives the same quotient where the multiplication is
exact. -/
def mulDiv (u m : Nat) : Nat := (mulHi u.toUInt64 m.toUInt64).toNat

/-- The remainder of `a` modulo `p` by a multiplication with the reciprocal `m`, `mod_mul` of
`sift.c`: the remainder `r` of `|a|` by `Ratpoints.Sieve.mulMod`, and `p - r` for a negative `a`
with `r ≠ 0`. For the reciprocal `m = Ratpoints.Sieve.magic p` of a modulus `p ≥ 1` it is the
Euclidean `a % p` whenever `|a| p < 2 ^ 64`, which the C code ensures by reducing only
`|a| ≤ RP_MULMOD_LIMIT` modulo moduli below `2 ^ 32`: the first stage of the sieve reduces its first
row index so when the word numbers of the piece allow it (`Ratpoints.Sieve.andRows`,
`Ratpoints.Sieve.chunkStarts`, the test `small` of `Ratpoints.Sieve.siftPiece`).

C: `sift.c:243-247`

Deviation: integers for the `long`s `a` and the result, and natural numbers for the `long` `p` and
the `unsigned long` reciprocal `m`; `|a|` a natural number, for the `long` that `RP_MULMOD` converts
to an `unsigned long`. -/
def modMul (a : Int) (p m : Nat) : Int :=
  let r : Int := mulMod (if a < 0 then -a else a).toNat p m
  if a < 0 ∧ r ≠ 0 then p - r else r

/-! ### The admission tests of the rows of a denominator -/

/-- Whether the row of the denominator `b` in the table `e` of the prime `p` admits the numerator
`a`: for the residues `r = b mod p` and `x = a mod p`, the entry of the table at `x r⁻¹ mod p` if
`r ≠ 0`, and whether `x ≠ 0` if `r = 0`. It is the reference of the rows of a prime: ratpoints
builds the row of a residue `r ≠ 0` once, when a denominator first needs it, as a bit pattern of
`p` bits repeated through words, by a function for each prime that the build generates
(`Ratpoints.Sieve.sieveInit1`, `Ratpoints.Sieve.sieveInit2`), and takes the row of `0` from the
pattern `sieves0` that the build generates (`Ratpoints.Sieve.sieves0`), whose bit `N` is clear
exactly when `p` divides `N`. -/
def Entry.admits (e : Entry) (b : Nat) (a : Int) : Bool :=
  let r := b % e.p
  let x := (a % (e.p : Int)).toNat
  if r = 0 then x != 0 else e.isFSquare[x * e.inverses[r]! % e.p]!

/-- Whether the row of the denominator `b` for the prime power `pw` of the modulus `m = p ^ e`
admits the numerator `a`: for the residues `r = b mod m` and `x = a mod m`, the bit of `fsq` at
`x r⁻¹ mod m` if `p ∤ r`, and for `p ∣ r` whether `p ∤ x` and the bit of `gsq` at `r x⁻¹ mod m`
(`Ratpoints.Sieve.bitAt`). It is the reference of the rows of a prime power:
`_ratpoints_sieve_init_power` builds the pattern of the row of a residue once, when a denominator
first needs it, stepping through the residues `x r⁻¹` by additions of `r⁻¹` for a unit `r`, and lays
it out in words (`Ratpoints.Sieve.sieveInitPower`). -/
def Power.admits (pw : Power) (b : Nat) (a : Int) : Bool :=
  let r := b % pw.m
  let x := (a % (pw.m : Int)).toNat
  if r % pw.p ≠ 0 then bitAt pw.fsq (x * pw.inv[r]! % pw.m)
  else x % pw.p != 0 && bitAt pw.gsq (r * pw.inv[x]! % pw.m)

/-- A factor of a modulus of the sieve: a prime with its table (`Ratpoints.Sieve.Entry`) or a prime
power with its tables (`Ratpoints.Sieve.Power`), as the sieve entry of a product points to the
entries of its factors, which are those of primes and prime powers
(`Ratpoints.Sieve.SieveEntry`). -/
inductive Factor where
  /-- A prime with its table. -/
  | prime (e : Entry)
  /-- A prime power with its tables. -/
  | power (pw : Power)
  deriving Inhabited

/-- `f.admits b a`: whether the row of the denominator `b` for the factor `f` admits the numerator
`a`: the row of the prime (`Ratpoints.Sieve.Entry.admits`) or of the prime power
(`Ratpoints.Sieve.Power.admits`). -/
def Factor.admits : Factor → Nat → Int → Bool
  | .prime e, b, a => e.admits b a
  | .power pw, b, a => pw.admits b a

/-- The modulus of a factor of a sieve entry, the field `p` of the entry of the factor that the C
code reads in `_ratpoints_sieve_init_product`: the prime of a prime, the prime power `m` of a prime
power. -/
def Factor.modulus : Factor → Nat
  | .prime t => t.p
  | .power pw => pw.m

/-- The builder of the rows of a sieve entry, `init`, by its kind: the function that the build
generates for a prime below 64 from `CODE_INIT_SIEVE1` (`Ratpoints.Sieve.sieveInit1`) and for a
prime above 64 from `CODE_INIT_SIEVE2` (`Ratpoints.Sieve.sieveInit2`), the builder of the rows of a
prime power (`Ratpoints.Sieve.sieveInitPower`), and that of the rows of a product
(`Ratpoints.Sieve.sieveInitProduct`).

C: `rp-private.h:497-498`

Deviation: the kind of the builder, for the pointer to the function of the type
`ratpoints_init_fun`, which for a prime points to the function that the build generates for it;
the call through the pointer a match on the kind (`Ratpoints.Sieve.SieveEntry.initRow`,
`Ratpoints.Sieve.initFactorRow`). -/
inductive RowInit where
  /-- The function of a prime below 64, from `CODE_INIT_SIEVE1`. -/
  | sieve1
  /-- The function of a prime above 64, from `CODE_INIT_SIEVE2`. -/
  | sieve2
  /-- The builder of the rows of a prime power, `_ratpoints_sieve_init_power`. -/
  | power
  /-- The builder of the rows of a product, `_ratpoints_sieve_init_product`. -/
  | product
  deriving DecidableEq, Repr, Inhabited

/-- The kind of the builder of the rows of the prime `p` of the table, the entry of `p` in the table
`sieve_init` that the build generates: the function from `CODE_INIT_SIEVE1` for `p < 64`, and that
from `CODE_INIT_SIEVE2` otherwise.

C: `find_points.c:133`, `gen_init_sieve_h.c:48-62`, `init.c:246`

Deviation: a function of `p`, for the entry of `p` in the table of the pointers to the functions
that the build generates, one for each prime, and that `init.c` includes; the kind of the function,
for the pointer to it. -/
def sieveInit (p : Nat) : RowInit := if p < 64 then .sieve1 else .sieve2

/-- A reference to the entry that holds a table of rows (`Ratpoints.Sieve.RowStore`), for a pointer
to a sieve entry of ratpoints, whose array `sieve` holds the rows of the residues: a prime `p` by
itself, for the entry `prime_se[pn]` of the prime `p = prime[pn]` that `examine_prime` makes; a
prime power `p ^ e` by its prime and its exponent, for the entry `power_se[idx]` that `make_power`
makes once, when a modulus first needs it, and that the prime power as a modulus and as a factor of
products shares, whose index `idx` `add_moduli` keeps in `pw_idx[pn][e]` (lines 2352-2354 and
2387-2393 of `find_points.c`); and a product by the position `n` of its modulus among the moduli of
the parameters, for the entry of its own that `make_modulus` makes. -/
inductive EntryRef where
  /-- The entry of the prime `p`. -/
  | prime (p : Nat)
  /-- The entry of the prime power `p ^ e`. -/
  | power (p e : Nat)
  /-- The entry of the product that is the modulus at the position `n` of the parameters. -/
  | product (n : Nat)
  deriving DecidableEq, Hashable, Repr, Inhabited

/-- The reference to the entry of a factor (`Ratpoints.Sieve.EntryRef`), the entry to which the
field `factor` of the sieve entry of a product points: that of the prime, `prime_se[pn]`, by the
prime, or that of the prime power `p ^ e`, `power_se[idx]` with the index `idx` in `pw_idx[pn][e]`,
by its prime and its exponent. -/
def Factor.ref : Factor → EntryRef
  | .prime t => .prime t.p
  | .power pw => .power pw.p pw.e

/-- The kind of the builder of the rows of the entry of a factor (`Ratpoints.Sieve.RowInit`), the
field `init` of that entry: for a prime the function that the build generates for it
(`Ratpoints.Sieve.sieveInit`), which `examine_prime` sets (line 1800 of `find_points.c`), and for a
prime power the builder of the rows of a prime power, which `make_power` sets (line 2420). -/
def Factor.init : Factor → RowInit
  | .prime t => sieveInit t.p
  | .power _ => .power

/-- The sieve entry of a modulus `p` of the sieve, a prime, a prime power or a product of primes and
prime powers, given by its factors (`Ratpoints.Sieve.Factor`): one for a prime or a prime power, two
or more for a product; with the reciprocal of `p` (`Ratpoints.Sieve.magic`), which the third stage
of the sieve copies for its primes (`Ratpoints.Sieve.checkOf`) and with which the first two stages
reduce their row indices (`Ratpoints.Sieve.andRows`, `Ratpoints.Sieve.chunkStarts`,
`Ratpoints.Sieve.secondStage`); and with what the packing of the numerators needs: the bias, the
least multiple of `p` that is at least `Ratpoints.rowBias`, which the row offsets carry
(`Ratpoints.Sieve.classOffsets`), the inverse of `Ratpoints.rbaLength` modulo `p`, from which the
row offsets are computed, and the inverses of the strides `2 ^ k` modulo `p` for the strides in use,
with which `fill_bp_list` divides the denominator by the stride (`Ratpoints.Sieve.fillBpList`). Its
row for a denominator is the and of the rows of its factors (`Ratpoints.Sieve.SieveEntry.admits`).

C: `rp-private.h:542-555`

Deviation: the kinds of modulus as the list of the factors: one prime factor for a prime, whose
entry has `nf = 0` and the tables `is_f_square` and `inverses` of its own; one prime-power factor
for a prime power, whose entry has `nf = 1` and its tables `pw`; and two or more for a product,
whose entry has `nf ≥ 2` and points to the entries `factor` of its factors; no bound
`RP_MAX_FACTORS` on the number of factors, which the choice of the moduli keeps when it offers a
composite modulus (`Ratpoints.takeFactor`); the rows of the residues, which ratpoints keeps in the
array `sieve` of the entry, kept in the store of the run (`Ratpoints.Sieve.RowStore`) in the table
of rows of the reference `ref`; the reference `ref` to the entry whose table of rows holds its rows
(`Ratpoints.Sieve.EntryRef`), for the pointer to the entry: a prime or a prime power that of its one
factor, so that the modulus and the products with it as a factor read one table of rows, as they
read one entry in the C code, and a product its own; the kind of its builder `init`
(`Ratpoints.Sieve.RowInit`), for the pointer to the function; a natural number for the
`unsigned long` reciprocal `magic`, and natural numbers for the `long`s `bias` and `rbainv`; the
inverses `dinv` an array, for the array of `RP_NUM_STRIDES` `long`s, which the row offsets of the
packing fill (`Ratpoints.Sieve.classOffsets`) with an entry for each stride up to the largest in
use, where the entries of the C code beyond it stay unset and unread; the density `r`, which the
correction of the moduli during the run reads (`Ratpoints.Sieve.adaptPrimes`), a `Float` for the
`double`, and the count `nf` of the factors, an integer for the `long`, `0` for a prime, `1` for a
prime power and the number of factors for a product, kept with the list of the factors. -/
structure SieveEntry where
  /-- The modulus. -/
  p : Nat
  /-- The factors: one for a prime or a prime power, two or more for a product. -/
  factors : List Factor
  /-- The reciprocal of the modulus (`Ratpoints.Sieve.magic`). -/
  magic : Nat
  /-- The bias of the row offsets: the least multiple of the modulus that is at least
  `Ratpoints.rowBias`. -/
  bias : Nat
  /-- The inverse of `Ratpoints.rbaLength` modulo the modulus. -/
  rbainv : Nat
  /-- Entry `k` the inverse of `2 ^ k` modulo the modulus, for the strides `2 ^ k` in use; empty
  until the row offsets of the packing fill it (`Ratpoints.Sieve.classOffsets`). -/
  dinv : Array Nat
  /-- The reference to the entry whose table of rows holds the rows (`Ratpoints.Sieve.EntryRef`):
  that of the one factor of a prime or a prime power, and the product's own. -/
  ref : EntryRef
  /-- The kind of the builder of the rows (`Ratpoints.Sieve.RowInit`). -/
  init : RowInit
  /-- The density of the modulus. -/
  r : Float
  /-- The count of the factors: `0` for a prime, `1` for a prime power, else the number of
  factors. -/
  nf : Int
  deriving Inhabited

/-- The reference to the entry that holds the rows of a modulus with the factors `fs`, at the
position `n` among the moduli of the parameters, and the kind of its builder: for a prime or a
prime power, those of the entry of its one factor (`Ratpoints.Sieve.Factor.ref`,
`Ratpoints.Sieve.Factor.init`), whose entry the modulus shares, as `sieve_list[n]` is
`prime_se[pn]` or `power_se[idx]` in the C code; for a product, its own entry with the builder of
the rows of a product. -/
def SieveEntry.refInit (n : Nat) : List Factor → EntryRef × RowInit
  | [f] => (f.ref, f.init)
  | _ => (.product n, .product)

/-- Whether the row of the denominator `b` in the sieve entry `e` of the modulus `p` admits the
numerator `a`: for the residues `r = b mod p` and `x = a mod p`, the row of `r` of every factor
admits `x` (`Ratpoints.Sieve.Factor.admits`), each factor reading `r` and `x` modulo its own
modulus, which divides `p`. It is the reference of the rows of a modulus:
`_ratpoints_sieve_init_product` builds the row of a product once, when a denominator first needs
it, as the and of the rows of its factors for `r` modulo the modulus of the factor, laid down in
blocks of the length of the factor (`Ratpoints.Sieve.sieveInitProduct`); and a prime or a prime
power has the row of its one factor, the entry of the prime or the prime power being the factor's
own. -/
def SieveEntry.admits (e : SieveEntry) (b : Nat) (a : Int) : Bool :=
  e.factors.all (·.admits (b % e.p) (a % (e.p : Int)))

/-- Whether the numerator `a` survives the sieve entries `entries` for the denominator `b`: the row
of `b` in every entry admits `a` (`Ratpoints.Sieve.SieveEntry.admits`). This test, a function of
the numerator, is the interface between the sieve and the check. -/
def survives (entries : List SieveEntry) (b : Nat) (a : Int) : Bool := entries.all (·.admits b a)

/-! ### Examples -/

-- The rows of 3, 5, 7, 11 and 13 in the tables `squares` and `inverses` that the build of
-- ratpoints generates.
#guard squaresMod 3 == #[true, true, false] &&
  squaresMod 5 == #[true, true, false, false, true] &&
  squaresMod 7 == #[true, true, true, false, true, false, false] &&
  squaresMod 11 == #[true, true, false, true, true, true, false, false, false, true, false] &&
  squaresMod 13 ==
    #[true, true, false, true, true, false, false, false, false, true, true, false, true]

#guard inversesMod 3 == #[0, 1, 2] && inversesMod 5 == #[0, 1, 3, 2, 4] &&
  inversesMod 7 == #[0, 1, 4, 5, 2, 3, 6] &&
  inversesMod 11 == #[0, 1, 6, 4, 3, 9, 2, 8, 7, 5, 10] &&
  inversesMod 13 == #[0, 1, 7, 9, 10, 8, 11, 2, 5, 3, 4, 6, 12]

-- The row of `0`, that of `sieves0`: the numerators not divisible by `p`.
#guard (List.range 41).all fun i ↦
  (examinePrime [1, 2, 3] 2 7).admits 14 ((i : Int) - 20) == (((i : Int) - 20) % 7 != 0)

-- `y ^ 2 = x ^ 2 + 1` modulo 5: `f(x)` is a square for `x = 0, 2, 3` (`f = 1, 0, 0`), and there
-- are points at infinity (`c_2 = 1`).
#guard (examinePrime [1, 0, 1] 2 5).isFSquare == #[true, false, true, true, false, true]

-- The helper `mod` of the C code is the Euclidean `%` at the ends of the range of a `long` and
-- around `-16 b`, `0` and `16 b`, for small moduli and for moduli near `2 ^ 59`.
#guard [1, 3, 7, 251, 1021, 2 ^ 58 + 3, 2 ^ 59 - 1].all fun b : Int ↦
  [-2 ^ 63, -2 ^ 63 + 1, -16 * b - 1, -16 * b, -16 * b + 1, -b, -1, 0, 1, b, 16 * b - 1, 16 * b,
    16 * b + 1, 2 ^ 63 - 2, 2 ^ 63 - 1].all fun a ↦ modLong a b == a % b

-- The table with the exit on both paths against the reference, for curves with points modulo every
-- prime, one of them with coefficients that are not `long`s.
#guard ([([1, 2, 3, 4, 5, 6, 7], 6), ([-2, 0, 0, 1], 3), ([3, 0, 0, 0, 5], 4),
    ([2 ^ 70 + 1, -2 ^ 64, 7], 2)] : List (List Int × Nat)).all fun (c, d) ↦
  [3, 5, 7, 11, 13, 251].all fun p ↦ [true, false].all fun u ↦
    match Id.run (examinePrime? c d p u) with
    | some (e, cm, _, _) => e.p == p && e.isFSquare == (examinePrime c d p).isFSquare &&
      cm.toList == (List.range (d + 1)).map (fun n ↦ (c.getD n 0 % (p : Int)).toNat) &&
      e.inverses == inversesMod p
    | none => false

-- Barrett's reduction with the reciprocal `⌊(2 ^ 64 - 1) / p⌋` is the remainder for `u < 2 ^ 64`:
-- at the ends of the range, at the multiples of `p` and next to them, and at the powers of 2, for
-- the primes of the table, `1`, `2` and moduli near `2 ^ 32`, `2 ^ 63` and `2 ^ 64`.
#guard ([1, 2, 2 ^ 32 - 5, 2 ^ 32 + 15, 2 ^ 63 - 25, 2 ^ 64 - 59] ++ primeTable.toList).all
  fun p ↦
    let m := (2 ^ 64 - 1) / p
    ([0, 1, p - 1, p, p + 1, 2 * p - 1, 2 * p, 2 ^ 64 - 1, 2 ^ 64 - p, m * p, m * p - 1] ++
        (List.range 64).map (2 ^ ·)).all fun u ↦
      2 ^ 64 ≤ u || barrett u p m == u % p

-- Horner's rule with Barrett's reduction on its schedule against Horner's rule reduced at every
-- step, for the primes below `2 ^ maxBitsInPrime` with the largest coefficients and residues, where
-- the accumulator comes nearest to `2 ^ 64`, at degrees around the schedule and at `maxDegree`.
#guard (primeTable.toList.take numPrimes).all fun p ↦
  [0, 1, 6, 7, 8, 13, 14, 15, 100].all fun d ↦
    let cm := Array.replicate (d + 1) (p - 1)
    [1, 2, p - 2, p - 1].all fun a ↦
      Id.run (hornerBarrett cm d p ((2 ^ 64 - 1) / p) a) == evalMod cm.toList p a

-- The coefficients modulo `p` and the tables of `p + 1` entries, the last for the points at
-- infinity, that `examine_prime` makes for `1 2 3 4 5 6 7`, `6 -3 5 2 75` and `1 0 126 0 441` at
-- 3, 5 and 7, read from a build of ratpoints at the pinned commit.
#guard ([([1, 2, 3, 4, 5, 6, 7], 6, 3, [1, 2, 0, 1, 2, 0, 1], "1111"),
    ([1, 2, 3, 4, 5, 6, 7], 6, 5, [1, 2, 3, 4, 0, 1, 2], "101010"),
    ([1, 2, 3, 4, 5, 6, 7], 6, 7, [1, 2, 3, 4, 5, 6, 0], "11001011"),
    ([6, -3, 5, 2, 75], 4, 3, [0, 0, 2, 2, 0], "1111"),
    ([6, -3, 5, 2, 75], 4, 5, [1, 2, 0, 2, 0], "111101"),
    ([6, -3, 5, 2, 75], 4, 7, [6, 4, 5, 2, 5], "01110000"),
    ([1, 0, 126, 0, 441], 4, 7, [1, 0, 0, 0, 0], "11111111")] :
      List (List Int × Nat × Nat × List Nat × String)).all fun (c, d, p, cm, t) ↦
  [true, false].all fun u ↦ match Id.run (examinePrime? c d p u) with
    | some (e, cm', _, _) => cm'.toList == cm && e.isFSquare.toList == t.toList.map (· == '1')
    | none => false

-- The inverses by the extended Euclidean algorithm: `x x⁻¹ ≡ 1 (mod m)` for every unit `x` of every
-- odd `m < 256`, and the table of inverses of the build for the first ten primes.
#guard (List.range 127).all fun i ↦
  let m := 2 * i + 3
  (List.range m).all fun x ↦ Nat.gcd x m != 1 || Id.run (modinv x m) < m &&
    Id.run (modinv x m) * x % m == 1
#guard (primeTable.toList.take 10).all fun p ↦
  (List.range' 1 (p - 1)).all fun x ↦ Id.run (modinv x p) == (inversesMod p)[x]!

-- The tables of the prime powers 9 for `6 -3 5 2 75` and 25 for `1 0 126 0 441` that
-- `examine_power` makes, read from a build of ratpoints at the pinned commit: the bits of `fsq` and
-- `gsq` (set only at multiples of `p`), bit arrays of `modWords` words with no bit set from `m` on,
-- and the inverses of the units.
#guard
  let bs (s : String) : List Bool := s.toList.map (· == '1')
  let p9 := Id.run (examinePower [6, -3, 5, 2, 75] 4 3 2 true true)
  let p25 := Id.run (examinePower [1, 0, 126, 0, 441] 4 5 2 false true)
  let bits (ws : Array UInt64) (m : Nat) : List Bool := (List.range (64 * modWords)).map fun x ↦
    x < m && bitAt ws x
  p9.m == 9 && p9.fsq.size == modWords && p9.gsq.size == modWords &&
    bits p9.fsq 9 == (List.range (64 * modWords)).map (bitAt p9.fsq) &&
    bits p9.gsq 9 == (List.range (64 * modWords)).map (bitAt p9.gsq) &&
    (bits p9.fsq 9).take 9 == bs "010011010" && (bits p9.gsq 9).take 9 == bs "000100000" &&
    p9.inv.toList == [0, 1, 5, 0, 7, 2, 0, 4, 8] && p25.m == 25 &&
    (bits p25.fsq 25).take 25 == bs "1011010110101101011010110" &&
    (bits p25.gsq 25).take 25 == bs "1000010000100001000010000" &&
    p25.inv.toList ==
      [0, 1, 13, 17, 19, 0, 21, 18, 22, 14, 0, 16, 23, 2, 9, 0, 11, 3, 7, 4, 0, 6, 8, 12, 24]

-- The rows of the prime power 25 let the point `(129 : 3830 : 100)` of `y ^ 2 = x ^ 3 - 2` through,
-- for its denominator `100 ≡ 0 (mod 5)`, while the numerators `a ≡ 0 (mod 5)` and those with
-- `F(a, 100)` not a square modulo 25 do not pass; and the row of a product is the and of the rows
-- of its factors: for `45 = 9 · 5` and `6 -3 5 2 75`, the sieve entry admits `a` for `b` exactly
-- when both factors do, and the sieve entry of a prime with its table as its one factor admits what
-- the table admits. The bias, the inverse of `rbaLength` and the inverses of the strides of these
-- sieve entries, `0`, `0` and the empty array, which `[k]!` reads as `0`, are fields that only the
-- packing of the numerators reads, the row offsets (`Ratpoints.Sieve.classOffsets`) the first two
-- and the residues of a denominator (`Ratpoints.Sieve.fillBpList`) the third.
#guard
  let pw := Id.run (examinePower [-2, 0, 0, 1] 3 5 2 true true)
  pw.admits 100 129 && !pw.admits 100 130 && (List.range 25).all fun a ↦
    pw.admits 100 a == (a % 5 != 0 && (List.range 25).any fun y ↦
      (y * y - (a ^ 3 - 2 * 100 ^ 3) * 100 : Int) % 25 == 0)
#guard
  let c := [6, -3, 5, 2, 75]
  let pw := Id.run (examinePower c 4 3 2 true true)
  let e5 := examinePrime c 4 5
  let se : SieveEntry :=
    ⟨45, [.power pw, .prime e5], magic 45, 0, 0, #[], .product 0, .product, 0.0, 2⟩
  (List.range 45).all fun b ↦ (List.range 90).all fun a : Nat ↦
    se.admits b a == (pw.admits b a && e5.admits b a)
#guard [3, 5, 7, 13].all fun p ↦
  let e := examinePrime [6, -3, 5, 2, 75] 4 p
  (List.range (2 * p)).all fun b ↦ (List.range (3 * p)).all fun a : Nat ↦
    let se : SieveEntry := ⟨p, [.prime e], magic p, 0, 0, #[], .prime p, sieveInit p, 0.0, 0⟩
    se.admits b a == e.admits b a

-- The reductions by the reciprocal against the remainder and the quotient, at the ends of their
-- range `u p < 2 ^ 64` (the largest such `u`, its neighbours below, the multiples of `p` and next
-- to them, and the bound `Ratpoints.mulModLimit` of the callers), for every prime of the table,
-- the composite moduli 9, 15, 45 and 255, and `2`; and the reciprocals of 3, 5 and 251.
#guard (primeTable.toList ++ [2, 9, 15, 45, 255]).all fun p ↦
  let top := (2 ^ 64 - 1) / p
  ([0, 1, p - 1, p, p + 1, 2 * p - 1, 2 * p, mulModLimit, mulModLimit + 1, top, top - 1, top - p,
      top / p * p, top / p * p - 1] ++ (List.range 64).map (2 ^ ·)).all fun u ↦
    2 ^ 64 ≤ u * p || mulMod u p (magic p) == u % p && mulDiv u (magic p) == u / p
#guard magic 3 == 6148914691236517206 && magic 5 == 3689348814741910324 &&
  magic 251 == 73493004277727298

-- The high half of the 128-bit product of two words against the product of natural numbers, for
-- words at the ends of the range and around the powers `2 ^ 32` of the halves.
#guard
  let ws : List UInt64 := [0, 1, 2, 0xffffffff, 0x100000000, 0x100000001, 0x123456789abcdef0,
    0x8000000000000000, 0xfffffffeffffffff, 0xffffffff00000000, 0xfffffffffffffffe, ~~~0]
  ws.all fun a ↦ ws.all fun b ↦ (mulHi a b).toNat == a.toNat * b.toNat / 2 ^ 64

-- The remainder `mod_mul` of a value of either sign against the Euclidean `%`, at the ends of the
-- range `|a| ≤ Ratpoints.mulModLimit` of its callers and around the multiples of the modulus, for
-- every prime of the table and the composite moduli 9, 15, 45 and 255.
#guard (primeTable.toList ++ [9, 15, 45, 255]).all fun p ↦
  ([0, 1, p - 1, p, p + 1, 2 * p - 1, 2 * p, 7 * p + 3, mulModLimit - 1, mulModLimit] :
      List Nat).all fun u ↦
    [(u : Int), -(u : Int)].all fun a ↦ modMul a p (magic p) == a % p

-- The row of `b = 3` modulo 5 admits `a` when `f(a / 3)` is a square modulo 5.
#guard (List.range 5).map (fun a : Nat ↦ (examinePrime [1, 0, 1] 2 5).admits 3 a) ==
  [true, true, false, false, true]

end Sieve

end Ratpoints

end
