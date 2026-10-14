/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Setup
public import Ratpoints.Model.Sieve

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Setup
meta import Ratpoints.Model.Sieve

/-!
# The denominators

The side of the denominators of the sieve, each component in its place in `find_points_work_1`: the
2-adic information, which says for each class of the denominators modulo 64 which numerators modulo
64 it admits (`Ratpoints.Sieve.twoAdic`), the word of a class being the pattern from which ratpoints
starts the first stage (the class word of `Ratpoints.Sieve.andRows`), and which classes admit a
numerator at all (`Ratpoints.Sieve.denBits`); the forbidden divisors of the denominators of a
polynomial of even degree, primes tested with words of 64 denominators or by their valuations, that
an examined prime gives from what its table hands back in the loop of the tables of `sieving_info`,
which also takes the exit (`Ratpoints.Sieve.examinePrimes`, `Ratpoints.Sieve.forbiddenOfPrime`), and
that the further primes give (`Ratpoints.Sieve.forbidden`); the Jacobi test, by the binary algorithm
(`Ratpoints.Sieve.jacobi`) or by tables (`Ratpoints.Sieve.jacobiSetup`,
`Ratpoints.Sieve.jacobiTest`); and the loop over the denominators in its four shapes, as `run_setup`
chooses them (`Ratpoints.Sieve.Shape`, `Ratpoints.Sieve.runSetup`): the squares, the divisors of the
leading coefficient times squares (`Ratpoints.Setup.setupUs1`), the words of 64 denominators, and
every denominator, each with the list of its denominators in the order of its loop and its tests on
a single denominator (`Ratpoints.Sieve.Shape.dens`, `Ratpoints.Sieve.Shape.keep`), and the run
itself (`Ratpoints.Sieve.sieveRun`). Every class word lets every numerator of a point through; no
forbidden divisor excludes the denominator of a point, the primes examined for them being primes of
the table; both Jacobi tests let it through, and so does every test of a shape, so that the run
finds the points of the denominators of its shape, in the order of its loop: increasing, except for
the divisors.

## Main definitions

* `Ratpoints.Sieve.squares64`: the squares modulo 64 as a word.
* `Ratpoints.Sieve.coeffsMod64`, `Ratpoints.Sieve.fsq`, `Ratpoints.Sieve.gsq`: the coefficients
  modulo 64 and the residues at which the polynomial and its reversal are squares modulo 64.
* `Ratpoints.Sieve.twoAdic`, `Ratpoints.Sieve.denBits`: the numerators modulo 64 that each class
  of the denominators admits, and the classes that admit one.
* `Ratpoints.Sieve.ForbiddenEntry`, `Ratpoints.Sieve.ForbiddenVal`: the forbidden divisors tested
  with words and by their valuations.
* `Ratpoints.Sieve.unitParts`, `Ratpoints.Sieve.forbiddenAt`, `Ratpoints.Sieve.forbiddenValuations`,
  `Ratpoints.Sieve.allValuations`: the valuations at a prime of the leading coefficient that no
  denominator of a point has, and those that a denominator can have at all.
* `Ratpoints.Sieve.forbiddenRow`, `Ratpoints.Sieve.forbiddenOfPrime`,
  `Ratpoints.Sieve.examinePrimes`, `Ratpoints.Sieve.forbidden`: the words of a forbidden divisor,
  the forbidden divisor of an examined prime, the loop of the tables with the exit and the forbidden
  divisors of the examined primes, and the forbidden divisors among the further primes.
* `Ratpoints.Sieve.jacobi`: the Jacobi test by the binary algorithm, with its helpers
  `Ratpoints.Sieve.twoSign`, `Ratpoints.Sieve.jacobiReduce` and `Ratpoints.Sieve.jacobiRound`.
* `Ratpoints.Sieve.JacobiInfo`, `Ratpoints.Sieve.nonSquares`, `Ratpoints.Sieve.jacobiSigns`,
  `Ratpoints.Sieve.jacobiSetup`, `Ratpoints.Sieve.jacobiTest`: the Jacobi test by tables.
* `Ratpoints.Sieve.ceilSqrt`, `Ratpoints.Sieve.floorSqrt`: the bounds of the square shapes.
* `Ratpoints.Sieve.denInfoTest`, `Ratpoints.Sieve.wordsTest`: the tests of the divisor shape and the
  word shape on a single denominator.
* `Ratpoints.Sieve.wordBits`, `Ratpoints.Sieve.wordsDens`, `Ratpoints.Sieve.squaresDens`,
  `Ratpoints.Sieve.squares1Dens`: the denominators of the shapes.
* `Ratpoints.Sieve.Shape`, `Ratpoints.Sieve.Shape.dens`, `Ratpoints.Sieve.Shape.keep`,
  `Ratpoints.Sieve.runSetup`: the shapes, their denominators and tests, and the choice of the shape.
* `Ratpoints.Sieve.sieveRun`: the points of the denominators of a shape.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The 2-adic information -/

/-- The squares modulo 64 as a word, `RP_SQUARES64`: bit `s` is set exactly when `s` is a square
modulo 64, for the twelve residues `0, 1, 4, 9, 16, 17, 25, 33, 36, 41, 49, 57`.

C: `find_points.c:981` -/
def squares64 : UInt64 := 0x0202021202030213

/-- The coefficients modulo 64 of the polynomial of degree `d` with the coefficient list `c`, as the
binary form of the even degree `D = d + d % 2` reads them: the non-negative residue of `c_k` for
`k ≤ d`, and `0` for `k = D = d + 1` when `d` is odd.

C: `find_points.c:1002-1004`

Deviation: an array of `D + 1` words, for the array `cm` on the stack; the Euclidean `%` of the
integers, for `mpz_fdiv_ui`. -/
def coeffsMod64 (c : List Int) (d : Nat) : Array UInt64 :=
  (Array.range (d + d % 2 + 1)).map fun k ↦ if k ≤ d then (c.getD k 0 % 64).toNat.toUInt64 else 0

/-- The residues `k` modulo 64 at which the polynomial `f` with the coefficients `cm` modulo 64
(`Ratpoints.Sieve.coeffsMod64`) is a square modulo 64, as a word: bit `k` is set when `f(k) mod 64`
is a square modulo 64 (`Ratpoints.Sieve.squares64`), with `f(k)` by Horner's rule in the arithmetic
of `UInt64`, which is exact modulo `2 ^ 64` and so modulo 64.

C: `find_points.c:1006-1014`

Deviation: Horner's rule from `0`, where the C code starts from `cm[D]`, with the same value. -/
def fsq (cm : Array UInt64) : UInt64 :=
  Nat.fold 64 (fun k _ w ↦
    let s := cm.foldr (fun a s ↦ s * k.toUInt64 + a) 0
    if squares64 >>> (s &&& 0x3f) &&& 1 != 0 then w ||| 1 <<< k.toUInt64 else w) 0

/-- The even residues `t` modulo 64 at which the reversed polynomial
`frev(t) = c₀ t^D + c₁ t^(D - 1) + ⋯ + c_D` with the coefficients `cm` modulo 64
(`Ratpoints.Sieve.coeffsMod64`) is a square modulo 64, as a word: bit `t`, for even `t`, is set
when `frev(t) mod 64` is a square modulo 64 (`Ratpoints.Sieve.squares64`), by Horner's rule in the
arithmetic of `UInt64`; the bits of the odd `t` are clear.

C: `find_points.c:1015-1021`

Deviation: Horner's rule from `0`, where the C code starts from `cm[0]`, with the same value. -/
def gsq (cm : Array UInt64) : UInt64 :=
  Nat.fold 32 (fun i _ w ↦
    let t := 2 * i
    let s := cm.foldl (fun s a ↦ s * t.toUInt64 + a) 0
    if squares64 >>> (s &&& 0x3f) &&& 1 != 0 then w ||| 1 <<< t.toUInt64 else w) 0

/-- The 2-adic information of the polynomial of degree `d` with the coefficient list `c`: for each
residue `b` modulo 64 the word `nb[b]` of the numerators modulo 64 that the denominators `≡ b`
admit, bit `a` set exactly when `a` or `b` is odd and `F(a, b) mod 64` is a square modulo 64. The
words start at `0`; for each set bit `k` of the word of `f` (`Ratpoints.Sieve.fsq`), lowest first
(`Ratpoints.Sieve.ctz`), bit `k b mod 64` is set in the word of every odd `b`, and for each set bit
`t` of the word of the reversed polynomial (`Ratpoints.Sieve.gsq`), bit `a` in the word of
`t a mod 64` for every odd `a`. The word of the class of a denominator is the pattern from which
ratpoints starts the first stage, the class word of `Ratpoints.Sieve.andRows`, and a denominator
whose class has the word `0` carries no point (`Ratpoints.Sieve.denBits`).

C: `find_points.c:983-994`, `find_points.c:996-1000`, `find_points.c:1023-1050`,
`find_points.c:1106-1115`

Deviation: the words returned, for the classes `cls` and the word `den_bits` that `get_2adic_info`
fills, `den_bits` computed from the words (`Ratpoints.Sieve.denBits`); the stride 1 for every class,
`k = 0` and `a₀ = 0`, so that the pattern of a class is its word itself, for the packing of the
numerators of a class into the residues `a₀ mod 2^k` that hold all of its admissible numerators,
with its row offsets and its packed pattern (stage F3); the lowest set bit by the loop of `RP_CTZL`
(`Ratpoints.Sieve.ctz`); remainders for the masks by `0x3f`; natural numbers for the `long`s `k`,
`b`, `t` and `a`; no output under `DEBUG`. -/
def twoAdic (c : List Int) (d : Nat) : Id (Vector UInt64 64) := do
  let cm := coeffsMod64 c d
  let mut nb : Vector UInt64 64 := Vector.replicate 64 0
  let mut w := fsq cm
  while w != 0 do
    let k ← ctz w
    w := w &&& (w - 1)
    for i in [0:32] do
      let b := 2 * i + 1
      nb := nb.set! b (nb[b]! ||| 1 <<< (k * b % 64).toUInt64)
  w := gsq cm
  while w != 0 do
    let t ← ctz w
    w := w &&& (w - 1)
    for i in [0:32] do
      let a := 2 * i + 1
      nb := nb.set! (t * a % 64) (nb[t * a % 64]! ||| 1 <<< a.toUInt64)
  return nb

/-- The classes of the denominators modulo 64 that admit a numerator, for the words `nb` of the
2-adic information (`Ratpoints.Sieve.twoAdic`): bit `b` is set exactly when `nb[b] ≠ 0`. A
denominator whose class has its bit clear carries no point; when no bit is set, the curve has no
point at all, not even at infinity (`Ratpoints.Sieve.not_isPoint_of_denBits_eq_zero`), and ratpoints
ends the search with none, after a test of the points at infinity that then always passes (the
2-adic exit of `Ratpoints.searchPoints`).

C: `find_points.c:995`, `find_points.c:1064-1065`, `find_points.c:1070`,
`find_points.c:1096-1097`, `find_points.c:1102-1104`

Deviation: computed from the words apart, where `get_2adic_info` sets the bit in the loop that makes
the classes. -/
def denBits (nb : Vector UInt64 64) : UInt64 :=
  Nat.fold 64 (fun b h db ↦ if nb[b] != 0 then db ||| 1 <<< b.toUInt64 else db) 0

/-! ### The forbidden divisors -/

/-- A forbidden divisor tested with words: a prime `p` that divides no denominator of a point, with
its `p` words, word `r` with bit `j` clear exactly when `p ∣ 64 r + j`
(`Ratpoints.Sieve.forbiddenRow`), so that word `w mod p` says which of the 64 denominators
`64 w + j` the prime leaves.

C: `find_points.c:157-161`

Deviation: the words as an array, for the pointers `start` and `end` into the pattern `sieves0` of
the build or into the buffer of the arguments, and no reciprocal `magic`, with which the C code
reduces the word number by a multiplication; a natural number for the `long` `p`. -/
structure ForbiddenEntry where
  /-- The prime. -/
  p : Nat
  /-- Its `p` words. -/
  words : Array UInt64

/-- A forbidden divisor tested by its valuation: a prime `p` and the mask of the valuations that no
denominator of a point has at `p`, bit `m` of `mask` set when `v_p(b) = m` is excluded
(`Ratpoints.Sieve.forbiddenValuations`).

C: `find_points.c:166`

Deviation: a natural number for the `long` `p`, and one for the `unsigned long` mask, so that it
holds every valuation of a denominator, also beyond the 64 bits of a word
(`Ratpoints.Sieve.forbiddenValuations`). -/
structure ForbiddenVal where
  /-- The prime. -/
  p : Nat
  /-- The mask of the excluded valuations. -/
  mask : Nat

/-- The coefficients of the polynomial of degree `d` with the coefficient list `c` at the prime `p`,
from the leading one down, with the coefficients `cm` reduced modulo `p` that the table of `p`
hands back (`Ratpoints.Sieve.examinePrime?`): for each `j ≤ d`, none when `c_{d-j} = 0`, and
otherwise, when `cm[d - j] = 0`, the valuation `w_j` of `c_{d-j}` at `p` with its unit part `r_j`
modulo `p`, the sign included (`Ratpoints.Setup.valuation`), and when `cm[d - j] ≠ 0`, `w_j = 0`
and `r_j = cm[d - j]`.

C: `find_points.c:2198-2200`, `find_points.c:2204-2215`

Deviation: an array of options of pairs, for the arrays `present`, `w` and `r` on the stack;
natural numbers for the `long`s. -/
def unitParts (c : List Int) (d p : Nat) (cm : Array Nat) : Id (Array (Option (Nat × Nat))) := do
  let mut us := #[]
  for j in [0:d + 1] do
    let ck := c.getD (d - j) 0
    if ck = 0 then us := us.push none
    else if cm[d - j]! = 0 then
      let (w, r) ← Setup.valuation ck p
      us := us.push (some (w, if ck < 0 then p - r else r))
    else us := us.push (some (0, cm[d - j]!))
  return us

/-- Whether no denominator `b` with `v_p(b) = m` carries a point, by the terms of `F(a, b)` at the
prime `p` with the valuations and unit parts `us` of the coefficients (`Ratpoints.Sieve.unitParts`)
and the squares `sq` modulo `p`: the least of the `w_j + j m` over the coefficients present is taken
at one `j` only, `j₀`, and is odd, or `j₀` is even and `r_{j₀}` is not a square modulo `p`; the term
with the least valuation then makes `F(a, b)` a non-square.

C: `find_points.c:2218-2228`

Deviation: the valuations and unit parts of the coefficients as the array of options `us`
(`Ratpoints.Sieve.unitParts`), for the arrays `present`, `w` and `r`, its size `d + 1` for the bound
`degree` of the loop, and the squares modulo `p` as the argument `sq`
(`Ratpoints.Sieve.squaresMod`), for the row `squares[pn]` of the table of the build; the test
returned, for the bit that the caller sets; remainders by 2 for the masks `& 1`; natural numbers for
the `long`s. -/
def forbiddenAt (us : Array (Option (Nat × Nat))) (sq : Array Bool) (m : Nat) : Id Bool := do
  let mut jmin := 0
  let mut vmin := (us[0]!.getD (0, 0)).1
  let mut tie := false
  for j in [1:us.size] do
    if let some (w, _) := us[j]! then
      let v := w + j * m
      if v < vmin then
        vmin := v
        jmin := j
        tie := false
      else if v = vmin then tie := true
  return !tie && (vmin % 2 == 1 || (jmin % 2 == 0 && !sq[(us[jmin]!.getD (0, 0)).2]!))

/-- The valuations at the prime `p ∣ c_d` that no denominator `b ≤ bHigh` of a point has, for the
polynomial of even degree `d` with the coefficient list `c` and its coefficients `cm` reduced
modulo `p`, as a mask: bit `m` is set, for `m = 1, 2, …` while `p ^ m ≤ bHigh`, when the terms of
`F(a, b)` exclude the valuation `m` (`Ratpoints.Sieve.forbiddenAt`, with the valuations and unit
parts of the coefficients, `Ratpoints.Sieve.unitParts`, and the squares modulo `p`,
`Ratpoints.Sieve.squaresMod`).

C: `find_points.c:2192-2197`, `find_points.c:2201-2203`, `find_points.c:2216-2217`,
`find_points.c:2229-2234`

Deviation: the prime `p` itself, for its index `pn` in the table `prime`, and the squares modulo `p`
by `Ratpoints.Sieve.squaresMod`, for the row of `p` in the table `squares` of the build; an array
for the pointer `coeffs_mod_p`; a natural number for the `unsigned long` mask, without the cap
`m < LONG_LENGTH - 1` of the loop, which never binds for a `long` `b_high` and an odd prime, the
loop ending before `m = 40`, and for `p ≤ 1`, which the C code never examines, the loop, once
entered, does not end; natural numbers for the `long`s. -/
def forbiddenValuations (c : List Int) (d p bHigh : Nat) (cm : Array Nat) : Id Nat := do
  let us ← unitParts c d p cm
  let sq := squaresMod p
  let mut mask : Nat := 0
  let mut m := 1
  let mut pm := p
  while pm ≤ bHigh do
    if ← forbiddenAt us sq m then mask := mask ||| 1 <<< m
    if bHigh / p < pm then break
    pm := pm * p
    m := m + 1
  return mask

/-- The valuations at the prime `p` that a denominator `b ≤ bHigh` can have at all, as a mask: bit
`m` set for `m = 1, 2, …` with `p ^ m ≤ bHigh`. A mask of forbidden valuations
(`Ratpoints.Sieve.forbiddenValuations`) that holds all of them says that `p` divides no denominator
of a point.

C: `find_points.c:2632-2641`

Deviation: a natural number for the `unsigned long` mask, without the cap `m < LONG_LENGTH - 1` of
the loop, which never binds for a `long` `b_high` and an odd prime, the loop ending before `m = 40`,
and for `p ≤ 1`, which the C code never examines, the loop, once entered, does not end; natural
numbers for the `long`s. -/
def allValuations (p bHigh : Nat) : Id Nat := do
  let mut all : Nat := 0
  let mut m := 1
  let mut pm := p
  while pm ≤ bHigh do
    all := all ||| 1 <<< m
    if bHigh / p < pm then break
    pm := pm * p
    m := m + 1
  return all

/-- The words of the forbidden divisor `p`: `p` words, word `r` with bit `j` clear exactly when
`p ∣ 64 r + j`, made as the C code makes them: all ones, then for `i < 64` the bit of the position
`p i` cleared, the position `N` being bit `N mod 64` of word `⌊N / 64⌋`.

C: `find_points.c:2773-2777`, `gen_find_points_h.c:102-134`

Deviation: one function for the primes of the table of the build, whose words are the first `p`
words of the pattern `sieves0` that the build generates (the row of `0` of a prime,
`Ratpoints.Sieve.SieveEntry.row`), those between `start` and `end`, and the primes beyond it, whose
words `sieving_info` makes in the buffer `forb_words` of the arguments; a fresh array for each
prime; divisions and remainders for the shifts and masks by `LONG_SHIFT` and `LONG_MASK`. -/
def forbiddenRow (p : Nat) : Array UInt64 :=
  Nat.fold 64 (fun i _ row ↦ row.modify (p * i / 64) (· &&& ~~~(1 <<< (p * i % 64).toUInt64)))
    (Array.replicate p (~~~0))

/-- The forbidden divisor that the examined prime `p` gives for the polynomial of even degree `d`
with the coefficient list `c` and the largest denominator `bHigh`, if any, from what the table of
`p` hands back (`Ratpoints.Sieve.examinePrime?`), the coefficients `cm` reduced modulo `p` and the
entry `atInf` of the table at `p`, whether there are points at infinity modulo `p`: for
`cm[d] = 0`, that is `p ∣ c_d`, the mask of the forbidden valuations
(`Ratpoints.Sieve.forbiddenValuations`), when it is not `0`, gives `p` with its words
(`Ratpoints.Sieve.forbiddenRow`) if it holds every valuation that a denominator can have
(`Ratpoints.Sieve.allValuations`), and `p` with the mask otherwise; for `p ∤ c_d`, `p` with its
words when there are no points at infinity modulo `p`, which for even `d` says that `c_d` is not a
square modulo `p`.

C: `find_points.c:2627-2631`, `find_points.c:2642-2676`

Deviation: the entry returned, for the entries that the C code writes into the arrays
`args->forb_ba` and `args->forbidden` and counts; the words of the prime made with its entry, for
the pointers into the pattern `sieves0` of the build, and no reciprocal `magic`; natural numbers
for the `long`s; no output under `DEBUG`. -/
def forbiddenOfPrime (c : List Int) (d p bHigh : Nat) (cm : Array Nat) (atInf : Bool) :
    Id (Option (ForbiddenEntry ⊕ ForbiddenVal)) := do
  if cm[d]! = 0 then
    let mask ← forbiddenValuations c d p bHigh cm
    if mask == 0 then return none
    let all ← allValuations p bHigh
    if mask &&& all == all then return some (.inl ⟨p, forbiddenRow p⟩)
    return some (.inr ⟨p, mask⟩)
  if !atInf then return some (.inl ⟨p, forbiddenRow p⟩)
  return none

/-- The loop of the tables over the first `n` primes of `Ratpoints.primeTable`, in the order of the
table, for the polynomial of degree `d` with the coefficient list `c` and the flag `useCLong` of the
`long`s: the table of each prime (`Ratpoints.Sieve.examinePrime?`), and none as soon as the curve
has no points modulo one of them; the tables kept by the position of the prime in the table; and,
when the switch `checkDenom` of the forbidden divisors is on and fewer than `maxForbidden` have been
found, the forbidden divisor of each prime for the largest denominator `bHigh`, from the
coefficients modulo the prime and the entry at infinity that its table hands back
(`Ratpoints.Sieve.forbiddenOfPrime`); the forbidden divisors tested with words and those tested by
their valuations each in the order found.

C: `find_points.c:2537`, `find_points.c:2545`, `find_points.c:2601-2602`,
`find_points.c:2605-2614`, `find_points.c:2616`, `find_points.c:2619`, `find_points.c:2622`,
`find_points.c:2624-2626`, `find_points.c:2677`, `find_points.c:2707`

Deviation: the number `n` of the primes examined as an argument (`Ratpoints.Params.examined`), for
`pn_lim`, which is `num_primes` at the start and which the loop raises when the number of primes was
left to the library and the choice of the moduli needs more (stage I); the table of every prime
kept, also when `examine_prime` returns `0` and `prime_se` stays `NULL`; an array of the tables, for
`prime_se`, and the exit as `none`, for the prime that `sieving_info` returns; no `pinf`, no keys,
counts `pnp` and `n_weak` and entries `prec`, which serve the choice of the moduli (stage I); no
cache `power_se` of the entries of prime powers (`Ratpoints.makeModulus?`); the switch `checkDenom`
for the flag `RATPOINTS_CHECK_DENOM`; the arrays of the forbidden divisors returned, for the arrays
of the arguments and their counts `fba` and `fdc`. -/
def examinePrimes (c : List Int) (d : Nat) (useCLong checkDenom : Bool)
    (n maxForbidden bHigh : Nat) :
    Id (Option (Array Entry × Array ForbiddenEntry × Array ForbiddenVal)) := do
  let mut tables := #[]
  let mut ba := #[]
  let mut val := #[]
  for pn in [0:n] do
    let p := primeTable[pn]!
    let some (e, cm) ← examinePrime? c d p useCLong | return none
    tables := tables.push e
    if checkDenom && ba.size + val.size < maxForbidden then
      match ← forbiddenOfPrime c d p bHigh cm e.isFSquare[p]! with
      | some (.inl f) => ba := ba.push f
      | some (.inr f) => val := val.push f
      | none => pure ()
  return some (tables, ba, val)

/-- The forbidden divisors of the denominators of the polynomial of even degree `d` with the
coefficient list `c`, at most `maxForbidden` of them, for the largest denominator `bHigh`, from
those found in the loop of the tables over the first `examined` primes of `Ratpoints.primeTable`,
`ba` tested with words (`Ratpoints.Sieve.ForbiddenEntry`) and `val` by their valuations
(`Ratpoints.Sieve.ForbiddenVal`): unless `c_d` is a square (`Ratpoints.Setup.isSquare`), the primes
`p` of the table from the position `examined` on, while fewer than `maxForbidden` are found and
`p ^ 2 ≤ bHigh`, each with its words (`Ratpoints.Sieve.forbiddenRow`) when `c_d` is not a square
modulo `p`, that is when the Kronecker symbol `(c_d / p)` is `-1`; both lists in the order found.

C: `find_points.c:2533-2536`, `find_points.c:2561-2562`, `find_points.c:2709-2772`,
`find_points.c:2778-2789`

Deviation: the position `examined` as an argument, for the final `pn_lim` of the loop of the tables;
the Kronecker symbol by the table of the squares modulo `p`, which marks `0` as a square, for
`mpz_kronecker_si`; the flag `RATPOINTS_CHECK_DENOM` not tested, since the search computes the
forbidden divisors only when the flag is set, for even degree (`Ratpoints.sievingInfo`); lists, for
the two arrays of the arguments with their terminating zeros; the words of a prime made with its
entry, for the pointers into `sieves0` and the buffer `forb_words`, with no failure for lack of
memory, where `sieving_info` drops the primes beyond the table whose words it cannot store; no
reciprocals `magic`; natural numbers for the `long`s; no output under `DEBUG`. -/
def forbidden (c : List Int) (d examined maxForbidden bHigh : Nat) (ba : Array ForbiddenEntry)
    (val : Array ForbiddenVal) :
    Id (List ForbiddenEntry × List ForbiddenVal) := do
  let lcf := c.getD d 0
  let mut ba := ba
  if !Setup.isSquare lcf then
    for n in [examined:primeTable.size] do
      if maxForbidden ≤ ba.size + val.size then break
      let p := primeTable[n]!
      if bHigh < p * p then break
      if !(squaresMod p)[(lcf % (p : Int)).toNat]! then ba := ba.push ⟨p, forbiddenRow p⟩
  return (ba.toList, val.toList)

/-! ### The Jacobi test -/

/-- The sign `s` times `(2 / m)` for odd `m`: negated when bit 1 of `m` is set (`m ≡ 3, 7 (mod 8)`)
and again when bit 2 is (`m ≡ 5, 7 (mod 8)`), so negated in all exactly for `m ≡ 3, 5 (mod 8)`,
where `(2 / m) = -1`. -/
def twoSign (m : Nat) (s : Int) : Int :=
  let s := if m &&& 2 != 0 then -s else s
  if m &&& 4 != 0 then -s else s

/-- One subtraction loop of the binary algorithm (`Ratpoints.Sieve.jacobi`) on the odd `x` and `y`:
while `x > y`, `x` becomes `x - y` and is then halved until it is odd again, the sign `s` taking the
factor `(2 / y)` at each halving (`Ratpoints.Sieve.twoSign`); the new `x` and the sign. -/
def jacobiReduce (x y : Nat) (s : Int) : Id (Nat × Int) := do
  let mut x := x
  let mut s := s
  while y < x do
    x := x - y
    repeat
      s := twoSign y s
      x := x / 2
      if x % 2 == 1 then break
  return (x, s)

/-- One round of the binary algorithm (`Ratpoints.Sieve.jacobi`) for the symbol `(f / b)`, `f > 0`
and `b` odd: from `n = f` and `m = b`, the factors `2` are taken out of `n` with the sign of
`(2 / m)`; then the two are exchanged, with the sign of the reciprocity when both are `≡ 3 (mod 4)`,
and the larger reduced by the smaller (`Ratpoints.Sieve.jacobiReduce`), in turn, until they are
equal. The common value `g`, the gcd of `f` and `b`, is returned with the sign, which is the symbol
`(f / b)` when `g = 1`. -/
def jacobiRound (f b : Nat) : Id (Nat × Int) := do
  let mut s : Int := 1
  let mut n := f
  let mut m := b
  while n % 2 == 0 do
    s := twoSign m s
    n := n / 2
  repeat
    if n &&& m &&& 2 != 0 then s := -s
    (m, s) ← jacobiReduce m n s
    if m == n then break
    if n &&& m &&& 2 != 0 then s := -s
    (n, s) ← jacobiReduce n m s
    if m == n then break
  return (m, s)

/-- The Jacobi symbol `(lcf / b*)` for `b > 0`, where `b*` is `b` with the prime factors of `2 lcf`
taken out, so that it is `±1`, by the binary algorithm of the C code: the factors `2` are taken out
of `b`, and `f = lcf mod b`; while `f ≠ 0`, a round of the algorithm (`Ratpoints.Sieve.jacobiRound`)
gives the symbol `(f / b)` when `f` and `b` are coprime, and otherwise their gcd, which is divided
out of `b`, `f` being reduced modulo the new `b` when it is not smaller. When `f` is `0`, `b*` is
`1`, and so is the symbol. For `b = 0` the loop does not end.

C: `find_points.c:498-566`, `find_points.c:568-641`

Deviation: one function for `jacobi`, on the GMP integer `lcf`, and `jacobi1`, on a `long`, which
the run calls when all coefficients are `long`s (`use_c_long`), with the steps of `jacobi`:
`jacobi1` takes the sign of `lcf` out as `(-1 / b)^neg` and its value `LONG_MIN` as `LONG_MIN / 4`,
reduces `|lcf|` modulo `b` only for `b < 2^59`, and does not reduce it after dividing `b` by the
gcd, which changes the steps but not the symbol; the round of the algorithm and its two subtraction
loops, which the C code writes out twice each, as helpers (`Ratpoints.Sieve.jacobiRound`,
`Ratpoints.Sieve.jacobiReduce`, `Ratpoints.Sieve.twoSign`); natural numbers for the `long`s `b`,
`f`, `n` and `m`, and integers for the `long` sign `s` and the `long` `lcf` of `jacobi1`; `f` the
Euclidean `lcf % b`, for `mpz_fdiv_r_ui` with its scratch integer `tmp`; the tests `f = 0` of the C
code, at the start and after each division of `b`, as the condition of the outer loop; the masks of
the signs by `&&&` on natural numbers; the symbol as an integer, for the `int`. -/
def jacobi (b : Nat) (lcf : Int) : Id Int := do
  let mut b := b
  while b % 2 == 0 do
    b := b / 2
  let mut f := (lcf % (b : Int)).toNat
  while f != 0 do
    let (g, s) ← jacobiRound f b
    if g == 1 then return s
    b := b / g
    if b ≤ f then f := f % b
  return 1

/-- What the Jacobi test by tables knows of the leading coefficient `lcf = ±2^v ∏ q_i^(e_i)`: its
odd primes `q_i` in increasing order, each with the table of the non-squares modulo `q_i` when
`e_i` is odd (entry `r` true when `r` is not a nonzero square modulo `q_i`) and none when `e_i` is
even, and the eight signs, entry `i` true when `(-1 / b)^neg (2 / b)^v` times the signs of the
reciprocity of the `q_i` with odd `e_i` is `-1` for `b ≡ i (mod 8)`.

C: `find_points.c:672-681`

Deviation: a list of pairs for the arrays `q` and `nonsq` and their count `nq`, with no reciprocals
`magic`, the model dividing; the tables as arrays of their own, for the space that they take from
the table `jtab` of the run; natural numbers for the `long`s `q`, and Booleans for the
`unsigned char`s of the tables and of the signs. -/
structure JacobiInfo where
  /-- The odd primes of the leading coefficient, each with its table of non-squares when its
  exponent is odd. -/
  primes : List (Nat × Option (Array Bool))
  /-- The eight signs, indexed by the residues modulo 8. -/
  sign : Array Bool

/-- The non-squares modulo the odd prime `q`, as a table: all entries true, then the entry of
`x ^ 2 mod q` cleared for `0 < x ≤ q / 2`, the squares reached by the steps `2 x + 1`, with one
subtraction of `q`; the entry of `0` stays true and is never read.

C: `find_points.c:709-713`

Deviation: a fresh array, for the space in the table `jtab` of the run; Booleans for the
`unsigned char`s, natural numbers for the `long`s `x` and `s`. -/
def nonSquares (q : Nat) : Id (Array Bool) := do
  let mut ns := Array.replicate q true
  let mut s := 1
  for x in [1:q / 2 + 1] do
    ns := ns.set! s false
    s := s + 2 * x + 1
    if q ≤ s then s := s - q
  return ns

/-- The eight signs of the Jacobi test by tables, entry `i` for `b* ≡ i (mod 8)`: the parity of
`[i ≡ 3 (mod 4)] (n₃ + neg) + [i ≡ 3, 5 (mod 8)] v`, for the number `n₃` of the primes `≡ 3 (mod 4)`
of the leading coefficient with an odd exponent, whether it is negative (`neg`) and the exponent `v`
of `2` in it: the product of `(-1 / b*)^neg`, `(2 / b*)^v` and the signs of the reciprocity.

C: `find_points.c:721-729`

Deviation: Booleans for the bits. -/
def jacobiSigns (n3 : Nat) (neg : Bool) (v : Nat) : Array Bool :=
  (Array.range 8).map fun i ↦
    (i &&& 3 == 3 && (n3 + if neg then 1 else 0) % 2 == 1) ^^ ((i == 3 || i == 5) && v % 2 == 1)

/-- The tables of the Jacobi test by tables (`Ratpoints.Sieve.JacobiInfo`) for the leading
coefficient `lcf ≠ 0` and the largest denominator `bHigh`, or `none` where they do not apply: when
`bHigh > Ratpoints.mulModLimit`, when the odd part of `|lcf|` has a prime factor beyond
`Ratpoints.primeTable` or more than `Ratpoints.jacobiPrimes` distinct prime factors, or when the
primes with an odd exponent sum to more than `Ratpoints.jacobiTable`. The power `2^v` is divided
off; then each prime `q` of the table that divides the cofactor, in turn while the cofactor is not
`1`, with its exponent, and for an odd exponent the table of the non-squares modulo `q`
(`Ratpoints.Sieve.nonSquares`); and the signs (`Ratpoints.Sieve.jacobiSigns`).

C: `find_points.c:683-708`, `find_points.c:714-720`, `find_points.c:730-731`

Deviation: the tables as fresh arrays, for the table `jtab` of the run that `tab` and `tab_len`
give, whose bound `Ratpoints.jacobiTable` on their total size is kept; the valuations by
`Ratpoints.Setup.valuation`, for `mpz_scan1` at `2` and the loop of exact divisions at the odd
primes, the power then divided off at once; the number `n3` of the primes `≡ 3 (mod 4)` with an odd
exponent counted in the list at the end, where the C code counts them in its loop; natural numbers
for the GMP integer `tmp` and the `long`s; no reciprocals `magic`; `none` and the tables returned,
for the return values `0` and `1` and the structure that `ji` points to. -/
def jacobiSetup (lcf : Int) (bHigh : Nat) : Id (Option JacobiInfo) := do
  if mulModLimit < bHigh then return none
  let (v, _) ← Setup.valuation lcf 2
  let mut w := lcf.natAbs / 2 ^ v
  let mut qs : Array (Nat × Option (Array Bool)) := #[]
  let mut used := 0
  for q in primeTable do
    if w == 1 then break
    if w % q != 0 then continue
    let (e, _) ← Setup.valuation w q
    w := w / q ^ e
    if qs.size == jacobiPrimes then return none
    if e % 2 == 1 then
      if jacobiTable < used + q then return none
      used := used + q
      qs := qs.push (q, some (← nonSquares q))
    else qs := qs.push (q, none)
  if w != 1 then return none
  let n3 := (qs.filter fun (q, ns) ↦ ns.isSome && q &&& 2 != 0).size
  return some ⟨qs.toList, jacobiSigns n3 (lcf < 0) v⟩

/-- Whether `(lcf / b*) = 1` for the denominator `0 < b < 2 ^ 64`, by the tables `ji` of the leading
coefficient `lcf` (`Ratpoints.Sieve.jacobiSetup`): the odd part of `b` (`Ratpoints.Sieve.ctz`), out
of which every prime `q` of `lcf` is divided as often as it divides, is `b*`; the sign of `b* mod 8`
is combined by exclusive or with the entry of `b* mod q` in the table of each prime with an odd
exponent, and the test passes when the result is false. For `b = 0` and every multiple of `2 ^ 64`,
whose word `b.toUInt64` is `0`, the loop of `Ratpoints.Sieve.ctz` does not end; the tables apply
only for `b ≤ Ratpoints.mulModLimit < 2 ^ 64` (`Ratpoints.mulModLimit_lt_size`).

C: `find_points.c:734-759`, `rp-private.h:409-410`, `rp-private.h:415-416`

Deviation: divisions and remainders for `RP_MULDIV`, which divides in a build without a 128-bit
integer type (`rp-private.h:415-416`) and otherwise multiplies by the reciprocal
(`rp-private.h:409-410`), exact below `2^32`, the bound `Ratpoints.mulModLimit` on the denominators
for which the tables are made; the odd part as the shift by the lowest set bit of the word `b`
(`Ratpoints.Sieve.ctz`, the loop of `RP_CTZL`); `b mod 8` for `b & 7`; natural numbers for the
`long`s; a Boolean for the `unsigned char` `s`, with exclusive or for `^=` and negation for the test
`s == 0`, and the test returned as a Boolean, for the `int`. -/
def jacobiTest (ji : JacobiInfo) (b : Nat) : Id Bool := do
  let t ← ctz b.toUInt64
  let mut b := b >>> t
  for (q, _) in ji.primes do
    repeat
      if b % q != 0 then break
      b := b / q
  let mut s := ji.sign[b % 8]!
  for (q, ns) in ji.primes do
    if let some ns := ns then s := s ^^ ns[b % q]!
  return !s

/-! ### The shapes of the run -/

/-- The least `k ≥ 1` with `k ^ 2 ≥ n`, for `n ≥ 1`: `⌊√(n - 1)⌋ + 1`.

C: `find_points.c:464-471`

Deviation: the exact square root of the natural numbers (`Nat.sqrt`), for the square root in
`double` corrected by a step either way; `1` for `n = 0`, where the C code divides by `0`; natural
numbers for the `long`s, so that a negative argument, whose square root in `double` is not a
number, cannot occur. -/
def ceilSqrt (n : Nat) : Nat := Nat.sqrt (n - 1) + 1

/-- The largest `k` with `k ^ 2 ≤ n`, `⌊√n⌋`.

C: `find_points.c:3766-3774`

Deviation: the exact square root of the natural numbers (`Nat.sqrt`), for the square root in
`double` corrected by a step either way; natural numbers for the `long`s, so that `0` is the only
case `n < 1`. -/
def floorSqrt (n : Nat) : Nat := Nat.sqrt n

/-- The valuation test of the divisor shape on the denominator `b`: false when for some prime `p` of
the leading coefficient, with its valuation `val` and its slope (`Ratpoints.Setup.DenInfo`, made by
`Ratpoints.Setup.setupUs1`), the valuation `v = v_p(b)` (`Ratpoints.Setup.valuation`) has
`v ≥ slope` and `v + val` odd, and true otherwise.

C: `find_points.c:3944-3953`

Deviation: the test returned, for the flag `flag`; natural numbers for the `int`s and `long`s. -/
def denInfoTest (info : List Setup.DenInfo) (b : Nat) : Id Bool := do
  for e in info do
    let (v, _) ← Setup.valuation b e.p
    if e.slope ≤ v && (v + e.val) % 2 == 1 then return false
  return true

/-- The tests of the word shape on a denominator `b` that its word leaves
(`Ratpoints.Sieve.wordsDens`): with the tables `fast` of the Jacobi test, their test
(`Ratpoints.Sieve.jacobiTest`); then that no forbidden divisor tested by its valuation excludes
`v_p(b)` (`Ratpoints.Setup.valuation`); then, with the Jacobi test on (`useJacobi`) and no tables,
that the binary algorithm (`Ratpoints.Sieve.jacobi`) gives `(lcf / b*) = 1`.

C: `find_points.c:4010-4011`, `find_points.c:4013-4041`

Deviation: the binary algorithm of `jacobi` also where the run calls `jacobi1` on the `long`
`lcf_long` (`Ratpoints.Sieve.jacobi`); bit `v_p(b)` of the mask of a natural number, false beyond
its bits (`Nat.testBit`), for the shift and the mask of the `unsigned long`; the test returned,
where the loop goes on to the sieve or to the next denominator; natural numbers for the `long`s; no
output under `DEBUG`. -/
def wordsTest (forbVal : List ForbiddenVal) (useJacobi : Bool) (fast : Option JacobiInfo)
        (lcf : Int) (b : Nat) :
    Id Bool := do
  if let some ji := fast then
    if !(← jacobiTest ji b) then return false
  for e in forbVal do
    let (v, _) ← Setup.valuation b e.p
    if e.mask.testBit v then return false
  if fast.isSome || !useJacobi then return true
  return (← jacobi b lcf) == 1

/-- The word of the 64 denominators `64 w + j` that pass the class test and the forbidden divisors
tested with words: the word `db` of the classes that admit a numerator (`Ratpoints.Sieve.denBits`),
and-ed with word `w mod p` of each entry of `forb` (`Ratpoints.Sieve.ForbiddenEntry`); in the word
of `bLow` the bits below `bLow mod 64` are cleared, and in the word of `bHigh` those above
`bHigh mod 64`.

C: `find_points.c:3981-3988`, `find_points.c:3990`, `find_points.c:3993-4006`

Deviation: word `w mod p` read at its index, for the pointers `cur` that the C code sets to the
words of the first word of a block, by `RP_MULMOD` or the helper `mod`, and steps on with every
word, wrapping at the end; divisions and remainders for the shifts and masks by `LONG_SHIFT` and
`LONG_MASK`; no output under `DEBUG`. -/
def wordBits (db : UInt64) (forb : List ForbiddenEntry) (bLow bHigh w : Nat) : UInt64 :=
  let x := forb.foldl (fun x e ↦ x &&& e.words[w % e.p]!) db
  let x := if w = bLow / 64 then x &&& ~~~0 <<< (bLow % 64).toUInt64 else x
  if w = bHigh / 64 then x &&& ~~~0 >>> (63 - bHigh % 64).toUInt64 else x

/-- The denominators of the word shape that their words leave, in increasing order: for each word
`w` from `⌊bLow / 64⌋` to `⌊bHigh / 64⌋`, the set bits `j` of its word (`Ratpoints.Sieve.wordBits`),
lowest first (`Ratpoints.Sieve.ctz`), each giving the denominator `64 w + j`.

C: `find_points.c:3826-3828`, `find_points.c:3967-3980`, `find_points.c:3989`,
`find_points.c:3991`, `find_points.c:4007-4008`, `find_points.c:4012`, `find_points.c:4053-4058`

Deviation: the denominators listed, to be tested and sifted one after the other
(`Ratpoints.Sieve.sieveRun`), where the C code tests and sifts each as the loop reaches it; the
words of the whole run, one segment with no blocks, for the words `a, …, e` of a block (stage I);
the lowest set bit by the loop of `RP_CTZL` (`Ratpoints.Sieve.ctz`); products and quotients by 64
for the shifts by `LONG_SHIFT`; natural numbers for the `long`s. -/
def wordsDens (db : UInt64) (forb : List ForbiddenEntry) (bLow bHigh : Nat) : Id (Array Nat) := do
  let mut out := #[]
  for w in [bLow / 64:bHigh / 64 + 1] do
    let mut x := wordBits db forb bLow bHigh w
    while x != 0 do
      let t ← ctz x
      out := out.push (64 * w + t)
      x := x &&& (x - 1)
  return out

/-- The denominators of the square shape, `k ^ 2` for `k` from `⌈√bLow⌉` to `⌊√bHigh⌋`
(`Ratpoints.Sieve.ceilSqrt`, `Ratpoints.Sieve.floorSqrt`), in increasing order; for odd degree
and `|c_d| = 1` the denominator of every point is a square.

C: `find_points.c:3816-3818`, `find_points.c:3919-3922`

Deviation: the denominators listed, to be tested and sifted one after the other
(`Ratpoints.Sieve.sieveRun`), where the C code tests and sifts each as the loop reaches it; one
segment with no blocks (stage I); natural numbers for the `long`s. -/
def squaresDens (bLow bHigh : Nat) : List Nat :=
  let lo := ceilSqrt bLow
  let hi := floorSqrt bHigh
  (List.range' lo (hi + 1 - lo)).map fun k ↦ k * k

/-- The denominators of the divisor shape: for each divisor `s` in turn
(`Ratpoints.Setup.setupUs1`), `s k ^ 2` for `k` from `⌈√(⌊(bLow - 1) / s⌋ + 1)⌉` to `⌊√⌊bHigh / s⌋⌋`
(`Ratpoints.Sieve.ceilSqrt`, `Ratpoints.Sieve.floorSqrt`), that is for the `k` with
`bLow ≤ s k ^ 2 ≤ bHigh`, in increasing order of `k`; in increasing order for each divisor, not as a
whole.

C: `find_points.c:3819-3825`, `find_points.c:3937-3940`

Deviation: the denominators listed, to be tested and sifted one after the other
(`Ratpoints.Sieve.sieveRun`), where the C code tests and sifts each as the loop reaches it; one
segment per divisor, with no blocks (stage I); natural numbers for the `long`s. -/
def squares1Dens (divisors : List Nat) (bLow bHigh : Nat) : List Nat :=
  divisors.flatMap fun s ↦
    let lo := ceilSqrt ((bLow - 1) / s + 1)
    let hi := floorSqrt (bHigh / s)
    (List.range' lo (hi + 1 - lo)).map fun k ↦ s * k * k

/-- The shape of the loop over the denominators, as `run_setup` chooses it
(`Ratpoints.Sieve.runSetup`), with its data: the squares (odd degree, `|c_d| = 1`); the divisors of
the leading coefficient times squares, with the primes of the valuation test and the divisors (odd
degree otherwise, when `Ratpoints.Setup.setupUs1` succeeds); the words of 64 denominators, with
the forbidden divisors tested with words and by their valuations, the switch of the Jacobi test,
its tables when they apply and the leading coefficient (even degree, when there is a test); and
every denominator.

C: `find_points.c:3725-3728`, `find_points.c:3736-3763`

Deviation: an inductive type with the data of each shape, for the constant `shape` and the fields of
`rp_run` that the shapes read, with these exceptions: the forbidden divisors as lists, for `forb_ba`
and `forbidden` with no count `nfb`, a list having its length; the tables of the Jacobi test as an
option, for `ji`, `jtab` and `fast_jacobi`; with the words, the bit `RATPOINTS_USE_JACOBI` of the
flags and the leading coefficient `args->cof[args->degree]`, which `run_block` reads through the
field `args`, the run taking the rest of what it reads of the arguments as its own arguments
(`Ratpoints.Sieve.sieveRun`); no copies of `use_c_long` and `lcf_long`, which only `jacobi1` reads
(`Ratpoints.Sieve.jacobi`); no blocks and segments (stage I), no search intervals (stage H), no
counters and decisions of the correction of the moduli (stage I); the words of the classes and
`den_bits` passed to the run apart (`Ratpoints.Sieve.sieveRun`). -/
inductive Shape where
  /-- `RP_SHAPE_SQUARES`: the squares. -/
  | squares
  /-- `RP_SHAPE_SQUARES1`: the divisors of the leading coefficient times squares. -/
  | squares1 (info : List Setup.DenInfo) (divisors : List Nat)
  /-- `RP_SHAPE_WORDS`: the words of 64 denominators. -/
  | words (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal) (useJacobi : Bool)
      (fast : Option JacobiInfo) (lcf : Int)
  /-- `RP_SHAPE_ALL`: every denominator. -/
  | all

/-- The denominators of the shape `s` from `bLow` to `bHigh`, in the order of its loop, before its
tests on a single denominator: for the squares and the divisors those of
`Ratpoints.Sieve.squaresDens` and `Ratpoints.Sieve.squares1Dens`, for the words those that their
words leave (`Ratpoints.Sieve.wordsDens`, with the class test and the forbidden divisors tested with
words, for the word `db` of the classes that admit a numerator), and otherwise `bLow, …, bHigh`.

C: `find_points.c:3812-3815`, `find_points.c:3829-3837`, `find_points.c:4060-4062`,
`find_points.c:4073-4074`

Deviation: the denominators listed, to be tested and sifted one after the other
(`Ratpoints.Sieve.sieveRun`), where the C code tests and sifts each as the loop reaches it; the
bounds of each segment computed where the denominators are listed (`Ratpoints.Sieve.sieveRun`), for
the arrays `seg_lo` and `seg_hi` that `run_setup` fills and `run_block` reads; one segment per
divisor, else one, with no blocks and no count of the steps (stage I); natural numbers for the
`long`s. -/
def Shape.dens (s : Shape) (db : UInt64) (bLow bHigh : Nat) : Id (List Nat) := do
  match s with
  | .squares => return squaresDens bLow bHigh
  | .squares1 _ divisors => return squares1Dens divisors bLow bHigh
  | .words forb .. => return (← wordsDens db forb bLow bHigh).toList
  | .all => return List.range' bLow (bHigh + 1 - bLow)

/-- The tests of the shape `s` on a single denominator `b`: the class test, that the word
`nb[b mod 64]` of the class of `b` in the 2-adic information (`Ratpoints.Sieve.twoAdic`) is not `0`,
and for the divisors then the valuation test (`Ratpoints.Sieve.denInfoTest`); for the words the
tests of `Ratpoints.Sieve.wordsTest`, the class test being made by the words.

C: `find_points.c:3923-3925`, `find_points.c:3941-3943`, `find_points.c:4063-4065`

Deviation: the word of the class read from the words `nb`, for the first word of the pattern of the
class `cls` (`EXT0(cl->bits)`), which is nonzero exactly when the word is, at every stride
(`find_points.c:1070-1098`). -/
def Shape.keep (s : Shape) (nb : Vector UInt64 64) (b : Nat) : Id Bool := do
  match s with
  | .squares => return nb[b % 64]! != 0
  | .squares1 info _ => if nb[b % 64]! != 0 then denInfoTest info b else return false
  | .words _ forbVal useJacobi fast lcf => wordsTest forbVal useJacobi fast lcf b
  | .all => return nb[b % 64]! != 0

/-- The shape of the run (`Ratpoints.Sieve.Shape`), as `run_setup` chooses it from the flags of the
search: the squares when `useSquares`; the divisors with their data when the divisor set-up has
succeeded (`us1`, `Ratpoints.Setup.setupUs1`); the words when `checkDenom`, with the forbidden
divisors `forb` and `forbVal`, the switch `useJacobi` of the Jacobi test, its tables when the test
is on and they apply to the leading coefficient `lcf` and the largest denominator `bHigh`
(`Ratpoints.Sieve.jacobiSetup`), and `lcf`; and every denominator otherwise.

C: `find_points.c:3778-3806`, `find_points.c:3876-3877`

Deviation: the shape returned with its data, for the fields of the run that `run_setup` fills, and
Booleans and an option for the bits `RATPOINTS_USE_SQUARES`, `RATPOINTS_USE_SQUARES1`,
`RATPOINTS_CHECK_DENOM` and `RATPOINTS_USE_JACOBI` of the flags; no count `nfb`, a list having its
length; no copies of `use_c_long` and `lcf_long`, which only `jacobi1` reads
(`Ratpoints.Sieve.jacobi`); no segments and blocks (stage I), no counters and decisions of the
correction of the moduli (stage I), no search intervals (stage H), no failure for lack of memory. -/
def runSetup (useSquares : Bool) (us1 : Option (List Setup.DenInfo × List Nat))
    (checkDenom useJacobi : Bool) (forb : List ForbiddenEntry) (forbVal : List ForbiddenVal)
        (lcf : Int) (bHigh : Nat) :
    Id Shape := do
  if useSquares then return .squares
  match us1 with
  | some (info, divisors) => return .squares1 info divisors
  | none =>
    if checkDenom then
      let fast ← if useJacobi then jacobiSetup lcf bHigh else pure none
      return .words forb forbVal useJacobi fast lcf
    else return .all

/-- The points of the denominators from `bLow` to `bHigh` of the shape `shape`, for the polynomial
of degree `d` with the coefficient list `c`: the rows of the sieve entries `entries` of the moduli
are made once for the run, each residue's row as a thunk (`Ratpoints.Sieve.SieveEntry.rows`); for
each denominator `b` of the shape, in the order of its loop (`Ratpoints.Sieve.Shape.dens`, with the
word `db` of the classes that admit a numerator), that passes its tests
(`Ratpoints.Sieve.Shape.keep`, with the words `nb` of the 2-adic information), the points that
`Ratpoints.Sieve.sift` finds from the word `nb[b mod 64]` of its class, with pieces of at most `A`
bit arrays, for `A ≥ 1`, and the flag `rev` of the reversal, are appended in turn.

C: `find_points.c:3889-3904`, `find_points.c:3917-3918`, `find_points.c:3926-3936`,
`find_points.c:3954-3966`, `find_points.c:4009`, `find_points.c:4042-4052`, `find_points.c:4059`,
`find_points.c:4066-4072`, `find_points.c:4075-4078`, `find_points.c:5120`,
`find_points.c:5152-5160`

Deviation: the denominators of the shape listed first, then tested and sifted one after the other,
where `run_block` tests and sifts each as its loop reaches it; no blocks (stage I): the steps of
each segment in order, for the blocks of `len` consecutive steps, which the threads share and which
deliver their points in the same order; the word `nb[b mod 64]` of the 2-adic information, for the
class `cls[b & 0x3f]` that `sift` receives, whose pattern it is at the stride 1 (its `k`, `a0` and
row offsets come with the packing, stage F3); the residues `b mod p` that choose the rows computed
by `Ratpoints.Sieve.sift`, for the residues of `b` divided by `2^k` that `fill_bp_list` computes
before each call (`k` the stride of the packing; stage F3); a list of points, for the counts `total`
of points that `sift` and `run_block` return, with no stop by the callback (stage G); natural
numbers for the `long`s (stage F); no correction of the moduli between the blocks (stage I); no
output under `DEBUG`. -/
def sieveRun (c : List Int) (d H A : Nat) (rev : Bool) (entries : List SieveEntry)
    (nb : Vector UInt64 64) (db : UInt64) (shape : Shape) (bLow bHigh : Nat) :
    Id (Array (Int × Int × Int)) := do
  let rows := entries.map fun e ↦ (e.p, e.rows)
  let dens ← shape.dens db bLow bHigh
  let mut out := #[]
  for b in dens do
    if ← shape.keep nb b then
      out := out ++ (← sift c d H A b rev rows nb[b % 64]!)
  return out

/-! ### Examples

The words of the 2-adic information, the forbidden divisors, the tables of the Jacobi test and the
denominators that the run sifts against those that a build of ratpoints at the pinned commit prints
with a dump of the side of the denominators on the standard error (the words `fsq`, `gsq` and `nb`
of `get_2adic_info`, `den_bits`, the forbidden divisors, with the first 30 primes of the table
examined, `-p 30`, the shape, the tables of the Jacobi test and the denominators that the run
sifts), and against their rule; and the run of the divisor shape against the points that ratpoints
prints. -/

-- The squares modulo 64.
#guard (List.range 64).all fun s ↦
  squares64.toBitVec.getLsbD s == (List.range 64).any fun x ↦ x * x % 64 == s

-- The coefficients modulo 64, with the coefficient `c_D = 0` for odd degree.
#guard coeffsMod64 [1, 2] 1 == #[1, 2, 0] && coeffsMod64 [-2, 0, 0, 1] 3 == #[62, 0, 0, 1, 0] &&
  coeffsMod64 [6, -3, 5, 2, 75] 4 == #[6, 61, 5, 2, 11]

-- `fsq`, `gsq` and `den_bits` of the dump for `1 2`, `-2 0 0 1`, `1 0 126 0 441`, `6 -3 5 2 75`,
-- `3 0 3` (no class admits a numerator) and `2 0 0 0 0 0 0 0 1`.
#guard ([([1, 2], 1, 0x1111111111111111, 0x4040010140400101, 0xefeeefefefeeefef),
    ([-2, 0, 0, 1], 3, 0x0808080808080808, 0x0000001000010011, 0xbabbbabababbbabb),
    ([1, 0, 126, 0, 441], 4, 0x5555555555555555, 0x5555555555555555, 0xffffffffffffffff),
    ([6, -3, 5, 2, 75], 4, 0x6024202020246020, 0, 0xaaaaaaaaaaaaaaaa),
    ([3, 0, 3], 2, 0, 0, 0),
    ([2, 0, 0, 0, 0, 0, 0, 0, 1], 8, 0, 0x5555555555555555, 0x5555555555555555)] :
      List (List Int × Nat × UInt64 × UInt64 × UInt64)).all fun (c, d, f, g, db) ↦
  fsq (coeffsMod64 c d) == f && gsq (coeffsMod64 c d) == g && denBits (Id.run (twoAdic c d)) == db

-- The words `nb` of the dump for `1 2 3 4 5 6 7`: `0xdddddddddddddddd` for `b ≡ 1 (mod 4)`,
-- `0x7777777777777777` for `b ≡ 3 (mod 4)`, `0` for even `b`.
#guard (Id.run (twoAdic [1, 2, 3, 4, 5, 6, 7] 6)).toList == (List.range 64).map fun b ↦
  if b % 4 = 1 then 0xdddddddddddddddd else if b % 4 = 3 then 0x7777777777777777 else 0

-- The words against their rule: bit `a` of `nb[b]` is set exactly when `a` or `b` is odd and the
-- binary form `F(a, b)` (by Horner's rule, with the factor `b` for odd degree) is a square modulo
-- 64, over all residues, for curves of degree 3, 4 and 6.
#guard ([([-2, 0, 0, 1], 3), ([1, 0, 126, 0, 441], 4), ([6, -3, 5, 2, 75], 4),
    ([3, -7, 0, 11, 5, -1, 2], 6)] : List (List Int × Nat)).all fun (c, d) ↦
  let nb := Id.run (twoAdic c d)
  (List.range 64).all fun b ↦ (List.range 64).all fun a ↦
    let F := BruteForce.horner (BruteForce.scaledCoeffs c d b) a * (if d % 2 = 1 then b else 1)
    nb[b]!.toBitVec.getLsbD a ==
      ((a % 2 == 1 || b % 2 == 1) && (List.range 64).any fun x ↦ (x * x : Int) % 64 == F % 64)

-- The coefficients of `6 -3 5 2 75` at 3, from `c_4 = 75 = 3 · 25` down: the valuations and the
-- unit parts with their signs (`-3 = 3 · (-1)`, so `3 - 1`); the valuation 1 is not excluded (the
-- terms of `j = 0` and `j = 1` tie), the valuation 2 is (the term of `j = 0`, of the odd valuation
-- 1); and the forbidden divisor that 3, 7 (`75 ≡ 5`, not a square modulo 7) and 11 (`75 ≡ 9`) give.
#guard
  let c : List Int := [6, -3, 5, 2, 75]
  let tab (p : Nat) : Array Nat × Bool :=
    match Id.run (examinePrime? c 4 p true) with
    | some (e, cm) => (cm, e.isFSquare[p]!)
    | none => (#[], true)
  let us := Id.run (unitParts c 4 3 (tab 3).1)
  us == #[some (1, 1), some (0, 2), some (0, 2), some (1, 2), some (1, 2)] &&
    !Id.run (forbiddenAt us (squaresMod 3) 1) && Id.run (forbiddenAt us (squaresMod 3) 2) &&
    (match Id.run (forbiddenOfPrime c 4 3 1000 (tab 3).1 (tab 3).2) with
      | some (.inr e) => e.p == 3 && e.mask == 0x7c | _ => false) &&
    (match Id.run (forbiddenOfPrime c 4 7 1000 (tab 7).1 (tab 7).2) with
      | some (.inl e) => e.p == 7 && e.words == forbiddenRow 7 | _ => false) &&
    (Id.run (forbiddenOfPrime c 4 11 1000 (tab 11).1 (tab 11).2)).isNone

-- The forbidden valuations of `6 -3 5 2 75` (`c_4 = 75 = 3 · 5 ^ 2`) at 3 and 5, for the largest
-- denominators 1000 and 50, and the valuations a denominator can have at all.
#guard
  let fv (p bHigh : Nat) : Nat := Id.run (forbiddenValuations [6, -3, 5, 2, 75] 4 p bHigh
    ((Array.range 5).map fun n ↦ ([6, -3, 5, 2, 75].getD n 0 % (p : Int)).toNat))
  [fv 3 1000, fv 5 1000, fv 3 50, fv 5 50] == [0x7c, 0x1a, 0xc, 0x2] &&
  [Id.run (allValuations 3 1000), Id.run (allValuations 5 1000), Id.run (allValuations 7 6)] ==
    [0x7e, 0x1e, 0]

-- The valuations from 63 on: `3 0 3^128`, the form `3^128 x^2 + 3 z^2`, has the point
-- `(1, 2 · 3^64, 3^64)`; at 3 the valuations 1 to 63 are excluded (the term `3 z^2` alone has the
-- least valuation `1 + 2 m`) and the valuation 64 is not, so that 3 is tested by its valuation,
-- whose mask lets the denominator `3^64` through.
#guard
  let c : List Int := [3, 0, 3 ^ 128]
  Id.run (forbiddenValuations c 2 3 (3 ^ 64) #[0, 0, 0]) == 2 ^ 64 - 2 &&
    match Id.run (forbiddenOfPrime c 2 3 (3 ^ 64) #[0, 0, 0] true) with
    | some (.inr e) => e.p == 3 && !e.mask.testBit (Id.run (Setup.valuation (3 ^ 64) 3)).1
    | _ => false

-- The words of a forbidden divisor: bit `j` of word `r` is clear exactly when `p ∣ 64 r + j`,
-- for primes of the table of the build and beyond it; and for the primes of the table they are the
-- pattern `sieves0`, the row of `0`.
#guard [3, 5, 7, 251, 257, 1021].all fun p ↦
  let row := forbiddenRow p
  row.size == p && (List.range p).all fun r ↦ (List.range 64).all fun j ↦
    row[r]!.toBitVec.getLsbD j == ((64 * r + j) % p != 0)
#guard [3, 5, 7, 13, 251].all fun p ↦
  forbiddenRow p ==
    ((⟨p, [.prime (examinePrime [1, 0, 1] 2 p)], magic p⟩ : SieveEntry).row 0).extract 0 p

-- The forbidden divisors of the dump, for the first 30 primes of the table as the examined primes
-- (the loop of the tables, then the further primes): `1 2 3 4 5 6 7` at the height 100,
-- `6 -3 5 2 75` at 1000 and at 50 with at most 3 of them (`-F 3`), and `1 0 1 0 2` at 200, where 3
-- is forbidden though it says nothing as a modulus.
#guard
  let fb (c : List Int) (d F bHigh : Nat) : List Nat × List (Nat × Nat) :=
    let (ba, val) := match Id.run (examinePrimes c d true true 30 F bHigh) with
      | some (_, ba, val) => Id.run (forbidden c d 30 F bHigh ba val)
      | none => ([], [])
    (ba.map (·.p), val.map fun e ↦ (e.p, e.mask))
  fb [1, 2, 3, 4, 5, 6, 7] 6 64 100 ==
      ([5, 11, 13, 17, 23, 41, 43, 61, 67, 71, 73, 79, 89, 97, 101, 107, 127], [(7, 4)]) &&
    fb [6, -3, 5, 2, 75] 4 64 1000 ==
      ([7, 17, 19, 29, 31, 41, 43, 53, 67, 79, 89, 101, 103, 113, 127], [(3, 0x7c), (5, 0x1a)]) &&
    fb [6, -3, 5, 2, 75] 4 3 50 == ([7], [(3, 0xc), (5, 0x2)]) &&
    fb [1, 0, 1, 0, 2] 4 64 200 ==
      ([3, 5, 11, 13, 19, 29, 37, 43, 53, 59, 61, 67, 83, 101, 107, 109], [])

-- The Jacobi symbol by the binary algorithm: `(2 / 7) = 1`, `(3 / 7) = -1`, `(-1 / 3) = -1`,
-- `(5 / 21) = 1`, `(10 / 21) = -1`; `b*` without the primes of `2 lcf`: `(6 / 9)` over `b* = 1`,
-- `(3 / 28)` over `b* = 7`, `(-12 / 75)` over `b* = 25`.
#guard [Id.run (jacobi 7 2), Id.run (jacobi 7 3), Id.run (jacobi 3 (-1)), Id.run (jacobi 21 5),
    Id.run (jacobi 21 10), Id.run (jacobi 9 6), Id.run (jacobi 28 3), Id.run (jacobi 75 (-12))] ==
  [1, -1, -1, 1, -1, 1, -1, 1]

-- The binary algorithm against a direct computation of `(lcf / b*)`: the product over the odd
-- primes `q ∤ lcf` of `b`, each as often as it divides `b`, of Euler's criterion
-- `lcf ^ ((q - 1) / 2) mod q`, read as `1` or `-1`, for the denominators up to 300.
#guard
  let primes := (List.range' 3 298).filter fun q ↦ (List.range' 2 (q - 2)).all (q % · != 0)
  [7, -12, 18, 2, -1, 3 * 5 * 7 * 11, -(2 ^ 63)].all fun (lcf : Int) ↦
    let euler (q : Nat) : Int := if (lcf % q).toNat ^ ((q - 1) / 2) % q == 1 then 1 else -1
    (List.range' 1 300).all fun b ↦
      Id.run (jacobi b lcf) == (primes.filter fun q ↦ b % q == 0 && lcf % q != 0).foldl
        (fun s q ↦ s * euler q ^ ((List.range 10).filter fun k ↦ b % q ^ (k + 1) == 0).length) 1

-- The helpers of the binary algorithm: `(2 / m)` for `m = 1, 3, 5, 7`; one subtraction loop on
-- `15` and `3`; the rounds for `(2 / 7)`, which ends at the gcd 1 with the symbol 1, and for
-- `(6 / 9)`, which ends at the gcd 3.
#guard [twoSign 1 1, twoSign 3 1, twoSign 5 1, twoSign 7 1] == [1, -1, -1, 1] &&
  Id.run (jacobiReduce 15 3 1) == (3, 1) && Id.run (jacobiRound 2 7) == (1, 1) &&
  (Id.run (jacobiRound 6 9)).1 == 3

-- The non-squares modulo 7 (the squares 1, 2 and 4) and modulo 13, and the signs of `7`.
#guard Id.run (nonSquares 7) == #[true, false, false, true, false, true, true] &&
  (List.range 13).all (fun x ↦ (Id.run (nonSquares 13))[x]! ==
    (x == 0 || !(List.range' 1 12).any fun y ↦ y * y % 13 == x)) &&
  jacobiSigns 1 false 0 == #[false, false, false, true, false, false, false, true]

-- The tables of the Jacobi test in the dump: `7` (`JI 7o SIGN 00010001`), `-12` (`JI 3o SIGN
-- 00000000`), `18` (`JI 3e SIGN 00010100`), `2` (`JI SIGN 00010100`), and none for `-1031`, whose
-- prime is beyond the table, for the product of the first 17 odd primes and beyond `2 ^ 32 - 1`.
#guard
  let ji (lcf : Int) (bHigh : Nat) : Option (List (Nat × Bool) × List Bool) :=
    (Id.run (jacobiSetup lcf bHigh)).map fun ji ↦
      (ji.primes.map fun (q, ns) ↦ (q, ns.isSome), ji.sign.toList)
  let sg (s : String) : List Bool := s.toList.map (· == '1')
  ji 7 100 == some ([(7, true)], sg "00010001") &&
    ji (-12) 100 == some ([(3, true)], sg "00000000") &&
    ji 18 100 == some ([(3, false)], sg "00010100") && ji 2 100 == some ([], sg "00010100") &&
    ji (-1031) 100 == none &&
    ji (((primeTable.toList.take 17).foldl (· * ·) 1 : Nat) : Int) 100 == none &&
    ji 7 (2 ^ 32) == none

-- The test by tables against the binary algorithm, for leading coefficients with odd and even
-- exponents, signs and powers of 2, and the denominators up to 600.
#guard [7, -12, 18, 2, -1, 3 * 5 * 7 * 11, 2 ^ 5 * 3 ^ 3 * 1021, -(2 ^ 63), 1019 * 1021 * 9].all
  fun lcf ↦ match Id.run (jacobiSetup lcf 600) with
    | some ji => (List.range' 1 600).all fun b ↦
        Id.run (jacobiTest ji b) == (Id.run (jacobi b lcf) == 1)
    | none => false

-- The bounds of the square shapes.
#guard (List.range 200).all fun n ↦
  floorSqrt n * floorSqrt n ≤ n && n < (floorSqrt n + 1) * (floorSqrt n + 1) &&
    (n = 0 || (ceilSqrt n - 1) * (ceilSqrt n - 1) < n && n ≤ ceilSqrt n * ceilSqrt n)

-- The denominators of the square shapes: the squares up to 20 and from 5 to 100; for the divisors
-- `1 2` of `1 2` at 20, `1, 4, 9, 16`, then `2, 8, 18`; and for `1 2 1031` at 1300, the squares,
-- twice the squares, then `1031`.
#guard squaresDens 1 20 == [1, 4, 9, 16] && squaresDens 5 100 == [9, 16, 25, 36, 49, 64, 81, 100] &&
  squares1Dens [1, 2] 1 20 == [1, 4, 9, 16, 2, 8, 18] &&
  squares1Dens [1, 2, 1031] 1 1300 ==
    (List.range' 1 36).map (fun k ↦ k * k) ++ (List.range' 1 25).map (fun k ↦ 2 * k * k) ++ [1031]

-- The tests of the word shape: with no valuation entries and no tables, the binary algorithm; with
-- the valuation entry `7 : 0x4` of `1 2 3 4 5 6 7`, the denominators `49 k` with `7 ∤ k` fail.
#guard (List.range' 1 200).all (fun b ↦ Id.run (wordsTest [] true none 7 b) ==
    (Id.run (jacobi b 7) == 1)) &&
  (List.range' 1 200).all fun b ↦ Id.run (wordsTest [⟨7, 4⟩] false none 7 b) ==
    !(b % 49 == 0 && b % 343 != 0)

-- The valuation test of `1 2` (`2 : 1 : 2`): `4` and `16` fail it.
#guard [1, 4, 9, 16, 2, 8, 18].map (fun b ↦ Id.run (denInfoTest [⟨2, 1, 2⟩] b)) ==
  [true, false, true, false, true, true, true]

-- The denominators that the words leave against their rule: `b` from `bLow` to `bHigh`, in
-- increasing order, whose class admits a numerator and which no forbidden divisor tested with words
-- divides, for `1 2 3 4 5 6 7` and ranges within one word and over several.
#guard
  let c : List Int := [1, 2, 3, 4, 5, 6, 7]
  let db := denBits (Id.run (twoAdic c 6))
  let forb := match Id.run (examinePrimes c 6 true true 30 64 1000) with
    | some (_, ba, val) => (Id.run (forbidden c 6 30 64 1000 ba val)).1
    | none => []
  ([(1, 1000), (1, 63), (64, 64), (5, 70), (130, 520)] : List (Nat × Nat)).all fun (lo, hi) ↦
    (Id.run (wordsDens db forb lo hi)).toList == (List.range' lo (hi + 1 - lo)).filter fun b ↦
      db.toBitVec.getLsbD (b % 64) && forb.all fun e ↦ b % e.p != 0

-- The run as ratpoints chooses and runs it: the shape and the denominators that the dump says the
-- run sifts, for `1 2` at 20 (the divisors), `1 2 3 4 5 6 7` at 100 (the words with the tables of
-- the Jacobi test), `1 0 0 0 -1031` at 100 (the words with the binary algorithm; the first twelve
-- denominators), `1 1 1 1 1 1 1` at 100 with no forbidden divisors (`-F 0`, every denominator) and
-- `-2 0 0 1` at 130 (the squares).
#guard
  let sifted (c : List Int) (d H F : Nat) : Nat × List Nat :=
    let lcf := c.getD d 0
    let useJacobi := d % 2 == 0 && !Setup.isSquare lcf
    let us1 := if d % 2 == 1 && lcf.natAbs != 1 then Id.run (Setup.setupUs1 c d H) else none
    let nb := Id.run (twoAdic c d)
    let (forb, forbVal) := match Id.run (examinePrimes c d true (d % 2 == 0) 30 F H) with
      | some (_, ba, val) => if d % 2 == 0 then Id.run (forbidden c d 30 F H ba val) else ([], [])
      | none => ([], [])
    let checkDenom := d % 2 == 0 && (!forb.isEmpty || !forbVal.isEmpty || useJacobi)
    let shape := Id.run (runSetup (d % 2 == 1 && lcf.natAbs == 1) us1 checkDenom useJacobi forb
      forbVal lcf H)
    let code := match shape with | .squares => 0 | .squares1 .. => 1 | .words .. => 2 | .all => 3
    (code, (Id.run (shape.dens (denBits nb) 1 H)).filter fun b ↦ Id.run (shape.keep nb b))
  sifted [1, 2] 1 20 64 == (1, [1, 9, 2, 8, 18]) &&
    sifted [1, 2, 3, 4, 5, 6, 7] 6 100 64 ==
      (2, [1, 3, 7, 9, 19, 21, 27, 29, 31, 37, 47, 53, 57, 59, 63, 81, 83, 87, 93]) &&
    (sifted [1, 0, 0, 0, -1031] 4 100 64).1 == 2 &&
    (sifted [1, 0, 0, 0, -1031] 4 100 64).2.take 12 == [1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13] &&
    sifted [1, 1, 1, 1, 1, 1, 1] 6 100 0 == (3, (List.range' 1 100).filter fun b ↦
      b % 2 = 1 || b % 8 = 0) &&
    sifted [-2, 0, 0, 1] 3 130 64 == (0, (List.range' 1 11).map fun k ↦ k * k)

-- The run of `1 2` at 20 in the divisor shape: the affine points that `ratpoints '1 2' 20 -q`
-- prints, by the divisors `1` and `2`, so with the denominator 9 before 2.
#guard
  let c : List Int := [1, 2]
  let nb := Id.run (twoAdic c 1)
  let entries := (primeTable.toList.take 30).filterMap fun p ↦
    (Id.run (examinePrime? c 1 p true)).map fun (e, _) ↦ (⟨p, [.prime e], magic p⟩ : SieveEntry)
  (Id.run (sieveRun c 1 20 1 false entries nb (denBits nb) (.squares1 [⟨2, 1, 2⟩] [1, 2]) 1
      20)).toList ==
    [(0, 1, 1), (0, -1, 1), (4, 3, 1), (4, -3, 1), (12, 5, 1), (12, -5, 1), (-4, 3, 9), (-4, -3, 9),
      (8, 15, 9), (8, -15, 9), (20, 21, 9), (20, -21, 9), (-1, 0, 2), (3, 4, 2), (3, -4, 2),
      (15, 8, 2), (15, -8, 2), (-3, 4, 8), (-3, -4, 8), (5, 12, 8), (5, -12, 8), (-5, 12, 18),
      (-5, -12, 18), (7, 24, 18), (7, -24, 18)]

end Sieve

end Ratpoints

end
