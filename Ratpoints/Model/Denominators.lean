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
polynomial of even degree, primes tested with words of 64 denominators or by their valuations
(`Ratpoints.Sieve.forbidden`); and the Jacobi test, by the binary algorithm
(`Ratpoints.Sieve.jacobi`) or by tables (`Ratpoints.Sieve.jacobiSetup`,
`Ratpoints.Sieve.jacobiTest`). Every class word lets every numerator of a point through; when the
moduli that the forbidden divisors examine are primes, no forbidden divisor excludes the denominator
of a point; and both Jacobi tests let it through.

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
* `Ratpoints.Sieve.forbiddenRow`, `Ratpoints.Sieve.forbiddenOfPrime`, `Ratpoints.Sieve.forbidden`:
  the words of a forbidden divisor, the forbidden divisor of an examined prime, and the forbidden
  divisors.
* `Ratpoints.Sieve.jacobi`: the Jacobi test by the binary algorithm, with its helpers
  `Ratpoints.Sieve.twoSign`, `Ratpoints.Sieve.jacobiReduce` and `Ratpoints.Sieve.jacobiRound`.
* `Ratpoints.Sieve.JacobiInfo`, `Ratpoints.Sieve.nonSquares`, `Ratpoints.Sieve.jacobiSigns`,
  `Ratpoints.Sieve.jacobiSetup`, `Ratpoints.Sieve.jacobiTest`: the Jacobi test by tables.
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
    if (squares64 >>> (s &&& 0x3f)) &&& 1 != 0 then w ||| 1 <<< k.toUInt64 else w) 0

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
    if (squares64 >>> (s &&& 0x3f)) &&& 1 != 0 then w ||| 1 <<< t.toUInt64 else w) 0

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
with its row offsets and its packed pattern (stage F); the lowest set bit by the loop of `RP_CTZL`
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
denominator whose class has its bit clear carries no point; when no bit is set and there is no
point at infinity, the curve has no point at all, and ratpoints ends the search with none (the
2-adic exit, stage E).

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
from the leading one down: for each `j ≤ d`, none when `c_{d-j} = 0`, and otherwise the valuation
`w_j` of `c_{d-j}` at `p` with its unit part `r_j` modulo `p`, the sign included
(`Ratpoints.Setup.valuation`), or `w_j = 0` and `r_j = c_{d-j} mod p` when `p ∤ c_{d-j}`.

C: `find_points.c:2198-2200`, `find_points.c:2204-2215`

Deviation: an array of options of pairs, for the arrays `present`, `w` and `r` on the stack; the
coefficients reduced modulo `p` by the Euclidean `%`, computed here, for the array `coeffs_mod_p`
that `examine_prime` fills (`Ratpoints.Sieve.examinePrime?`), the same residues, until stage F;
natural numbers for the `long`s. -/
def unitParts (c : List Int) (d p : Nat) : Id (Array (Option (Nat × Nat))) := do
  let mut us := #[]
  for j in [0:d + 1] do
    let ck := c.getD (d - j) 0
    if ck = 0 then us := us.push none
    else if ck % (p : Int) = 0 then
      let (w, r) ← Setup.valuation ck p
      us := us.push (some (w, if ck < 0 then p - r else r))
    else us := us.push (some (0, (ck % (p : Int)).toNat))
  return us

/-- Whether no denominator `b` with `v_p(b) = m` carries a point, by the terms of `F(a, b)` at the
prime `p` with the valuations and unit parts `us` of the coefficients (`Ratpoints.Sieve.unitParts`)
and the squares `sq` modulo `p`: the least of the `w_j + j m` over the coefficients present is taken
at one `j` only, `j₀`, and is odd, or `j₀` is even and `r_{j₀}` is not a square modulo `p`; the term
with the least valuation then makes `F(a, b)` a non-square.

C: `find_points.c:2218-2228`

Deviation: the test returned, for the bit that the caller sets; remainders by 2 for the masks `& 1`;
natural numbers for the `long`s. -/
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
polynomial of even degree `d` with the coefficient list `c`, as a mask: bit `m` is set, for
`m = 1, 2, …` while `p ^ m ≤ bHigh`, when the terms of `F(a, b)` exclude the valuation `m`
(`Ratpoints.Sieve.forbiddenAt`, with the valuations and unit parts of the coefficients,
`Ratpoints.Sieve.unitParts`, and the squares modulo `p`, `Ratpoints.Sieve.squaresMod`).

C: `find_points.c:2192-2197`, `find_points.c:2201-2203`, `find_points.c:2216-2217`,
`find_points.c:2229-2234`

Deviation: the prime `p` itself, for its index `pn` in the table `prime`, and the squares modulo `p`
by `Ratpoints.Sieve.squaresMod`, for the row of `p` in the table `squares` of the build; no argument
`coeffs_mod_p`, whose residues `Ratpoints.Sieve.unitParts` computes again until stage F; a natural
number for the `unsigned long` mask, without the cap `m < LONG_LENGTH - 1` of the loop, which never
binds for a `long` `b_high` and an odd prime, the loop ending before `m = 40`, and for `p ≤ 1`,
which the C code never examines, the loop, once entered, does not end; natural numbers for the
`long`s. -/
def forbiddenValuations (c : List Int) (d p bHigh : Nat) : Id Nat := do
  let us ← unitParts c d p
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
words of the pattern `sieves0` that the build generates (the row of `0` of the sieve,
`Ratpoints.Sieve.Entry.row`), those between `start` and `end`, and the primes beyond it, whose words
`sieving_info` makes in the buffer `forb_words` of the arguments; a fresh array for each prime;
divisions and remainders for the shifts and masks by `LONG_SHIFT` and `LONG_MASK`. -/
def forbiddenRow (p : Nat) : Array UInt64 :=
  Nat.fold 64 (fun i _ row ↦ row.modify (p * i / 64) (· &&& ~~~(1 <<< (p * i % 64).toUInt64)))
    (Array.replicate p (~~~0))

/-- The forbidden divisor that the examined prime `p` gives for the polynomial of even degree `d`
with the coefficient list `c` and the largest denominator `bHigh`, if any: for `p ∣ c_d`, the mask
of the forbidden valuations (`Ratpoints.Sieve.forbiddenValuations`), when it is not `0`, gives `p`
with its words (`Ratpoints.Sieve.forbiddenRow`) if it holds every valuation that a denominator can
have (`Ratpoints.Sieve.allValuations`), and `p` with the mask otherwise; for `p ∤ c_d`, `p` with its
words when `c_d` is not a square modulo `p` (`Ratpoints.Sieve.squaresMod`).

C: `find_points.c:2627-2631`, `find_points.c:2642-2676`

Deviation: the entry returned, for the entries that the C code writes into the arrays
`args->forb_ba` and `args->forbidden` and counts; the coefficients modulo `p` and whether `c_d` is a
square modulo `p` computed here, for the array `coeffs_mod_p` and the last entry of the table
`is_f_square` that `examine_prime` hands back, until stage F; the words of the prime made with its
entry, for the pointers into the pattern `sieves0` of the build, and no reciprocal `magic`; natural
numbers for the `long`s; no output under `DEBUG`. -/
def forbiddenOfPrime (c : List Int) (d p bHigh : Nat) :
    Id (Option (ForbiddenEntry ⊕ ForbiddenVal)) := do
  let lcf := c.getD d 0
  if lcf % (p : Int) = 0 then
    let mask ← forbiddenValuations c d p bHigh
    if mask == 0 then return none
    let all ← allValuations p bHigh
    if mask &&& all == all then return some (.inl ⟨p, forbiddenRow p⟩)
    return some (.inr ⟨p, mask⟩)
  if !(squaresMod p)[(lcf % (p : Int)).toNat]! then return some (.inl ⟨p, forbiddenRow p⟩)
  return none

/-- The forbidden divisors of the denominators of the polynomial of even degree `d` with the
coefficient list `c`, for the examined primes `moduli`, at most `maxForbidden` of them, and the
largest denominator `bHigh`: those tested with words (`Ratpoints.Sieve.ForbiddenEntry`) and those
tested by their valuations (`Ratpoints.Sieve.ForbiddenVal`), each in the order found. For each
examined prime in turn, while fewer than `maxForbidden` are found, its forbidden divisor
(`Ratpoints.Sieve.forbiddenOfPrime`); then, unless `c_d` is a square (`Ratpoints.Setup.isSquare`),
the primes `p` of `Ratpoints.primeTable` from the position `moduli.length` on, while fewer than
`maxForbidden` are found and `p ^ 2 ≤ bHigh`, each with its words (`Ratpoints.Sieve.forbiddenRow`)
when `c_d` is not a square modulo `p`, that is when the Kronecker symbol `(c_d / p)` is `-1`.

C: `find_points.c:2533-2536`, `find_points.c:2561-2562`, `find_points.c:2624-2626`,
`find_points.c:2677`, `find_points.c:2709-2772`, `find_points.c:2778-2789`

Deviation: the examined primes are the moduli of the parameters, and the further primes start at the
position in the table that is their number, where `sieving_info` examines the first `pn_lim` primes
of the table, `num_primes` of them or more when their number was left to the library (stage I), and
goes on from `prime[pn_lim]`; the moduli are taken in their order, where `sieving_info` takes the
primes in the order of the table, so that under the cap `maxForbidden` other primes may be recorded,
a modulus at a position of the table at least the number of the moduli may be recorded again by the
second loop, and a prime below that position that is no modulus is examined by neither loop; the
lists are those of `sieving_info` when the moduli are its first `pn_lim` primes in increasing order,
as in the program with `-p` and without `-P`; the Kronecker symbol by the table of the squares
modulo `p`, which marks `0` as a square, for `mpz_kronecker_si`; the flag `RATPOINTS_CHECK_DENOM`
not tested in either loop, since the search computes the forbidden divisors only for even degree,
where the flag is set (stage E); lists, for the two arrays of the arguments with their terminating
zeros; the words of a prime made with its entry, for the pointers into `sieves0` and the buffer
`forb_words`, with no failure for lack of memory, where `sieving_info` drops the primes beyond the
table whose words it cannot store; no reciprocals `magic`; natural numbers for the `long`s; no
output under `DEBUG`. -/
def forbidden (c : List Int) (d : Nat) (moduli : List Nat) (maxForbidden bHigh : Nat) :
    Id (List ForbiddenEntry × List ForbiddenVal) := do
  let lcf := c.getD d 0
  let mut ba : Array ForbiddenEntry := #[]
  let mut val : Array ForbiddenVal := #[]
  for p in moduli do
    if ba.size + val.size < maxForbidden then
      match ← forbiddenOfPrime c d p bHigh with
      | some (.inl e) => ba := ba.push e
      | some (.inr e) => val := val.push e
      | none => pure ()
  if !Setup.isSquare lcf then
    for n in [moduli.length:primeTable.size] do
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
`Ratpoints.Sieve.jacobiReduce`, `Ratpoints.Sieve.twoSign`); natural numbers for the `long`s, and `f`
the Euclidean `lcf % b`, for `mpz_fdiv_r_ui` with its scratch integer `tmp`; the tests `f = 0` of
the C code, at the start and after each division of `b`, as the condition of the outer loop; the
masks of the signs by `&&&` on natural numbers; the symbol as an integer, for the `int`. -/
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

/-- Whether `(lcf / b*) = 1` for the denominator `b > 0`, by the tables `ji` of the leading
coefficient `lcf` (`Ratpoints.Sieve.jacobiSetup`): the odd part of `b` (`Ratpoints.Sieve.ctz`),
out of which every prime `q` of `lcf` is divided as often as it divides, is `b*`; the sign of
`b* mod 8` is combined by exclusive or with the entry of `b* mod q` in the table of each prime with
an odd exponent, and the test passes when the result is false. For `b = 0` the loop of
`Ratpoints.Sieve.ctz` does not end.

C: `find_points.c:734-759`

Deviation: divisions and remainders for `RP_MULDIV`, which multiplies by the reciprocal and is
exact below `2^32`, the bound `Ratpoints.mulModLimit` on the denominators for which the tables are
made; the odd part as the shift by the lowest set bit of the word `b` (`Ratpoints.Sieve.ctz`, the
loop of `RP_CTZL`); `b mod 8` for `b & 7`; natural numbers for the `long`s. -/
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

/-! ### Examples

The words of the 2-adic information, the forbidden divisors and the tables of the Jacobi test
against those that a build of ratpoints at the pinned commit prints with a dump of the side of the
denominators on the standard error (the words `fsq`, `gsq` and `nb` of `get_2adic_info`,
`den_bits`, the forbidden divisors, with the moduli of the model, `-p 30`, and the tables of the
Jacobi test), and against their rule. -/

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
  let us := Id.run (unitParts [6, -3, 5, 2, 75] 4 3)
  us == #[some (1, 1), some (0, 2), some (0, 2), some (1, 2), some (1, 2)] &&
    !Id.run (forbiddenAt us (squaresMod 3) 1) && Id.run (forbiddenAt us (squaresMod 3) 2) &&
    (match Id.run (forbiddenOfPrime [6, -3, 5, 2, 75] 4 3 1000) with
      | some (.inr e) => e.p == 3 && e.mask == 0x7c | _ => false) &&
    (match Id.run (forbiddenOfPrime [6, -3, 5, 2, 75] 4 7 1000) with
      | some (.inl e) => e.p == 7 && e.words == forbiddenRow 7 | _ => false) &&
    (Id.run (forbiddenOfPrime [6, -3, 5, 2, 75] 4 11 1000)).isNone

-- The forbidden valuations of `6 -3 5 2 75` (`c_4 = 75 = 3 · 5 ^ 2`) at 3 and 5, for the largest
-- denominators 1000 and 50, and the valuations a denominator can have at all.
#guard [Id.run (forbiddenValuations [6, -3, 5, 2, 75] 4 3 1000),
    Id.run (forbiddenValuations [6, -3, 5, 2, 75] 4 5 1000),
    Id.run (forbiddenValuations [6, -3, 5, 2, 75] 4 3 50),
    Id.run (forbiddenValuations [6, -3, 5, 2, 75] 4 5 50)] == [0x7c, 0x1a, 0xc, 0x2] &&
  [Id.run (allValuations 3 1000), Id.run (allValuations 5 1000), Id.run (allValuations 7 6)] ==
    [0x7e, 0x1e, 0]

-- The valuations from 63 on: `3 0 3^128`, the form `3^128 x^2 + 3 z^2`, has the point
-- `(1, 2 · 3^64, 3^64)`; at 3 the valuations 1 to 63 are excluded (the term `3 z^2` alone has the
-- least valuation `1 + 2 m`) and the valuation 64 is not, so that 3 is tested by its valuation,
-- whose mask lets the denominator `3^64` through.
#guard
  let c : List Int := [3, 0, 3 ^ 128]
  Id.run (forbiddenValuations c 2 3 (3 ^ 64)) == 2 ^ 64 - 2 &&
    match Id.run (forbiddenOfPrime c 2 3 (3 ^ 64)) with
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
  forbiddenRow p == ((examinePrime [1, 0, 1] 2 p).row 0).extract 0 p

-- The forbidden divisors of the dump, for the first 30 primes of the table as the examined primes:
-- `1 2 3 4 5 6 7` at the height 100, `6 -3 5 2 75` at 1000 and at 50 with at most 3 of them
-- (`-F 3`), and `1 0 1 0 2` at 200, where 3 is forbidden though it says nothing as a modulus.
#guard
  let fb (c : List Int) (d F bHigh : Nat) : List Nat × List (Nat × Nat) :=
    let (ba, val) := Id.run (forbidden c d (primeTable.toList.take 30) F bHigh)
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

end Sieve

end Ratpoints

end
