/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.BruteForce
public import Ratpoints.Model.Constants

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.BruteForce
meta import Ratpoints.Model.Constants

/-!
# The plain sieve

The components of the plain sieve, each in the simplest form of its place in the C function
`find_points_work_1`: the table of a prime (`Ratpoints.Sieve.examinePrime`), the rows of a
denominator (`Ratpoints.Sieve.Entry.admits`), the sieve of one denominator with one Boolean per
numerator (`Ratpoints.Sieve.sieveDen`), the test for common factors and the exact check of its
survivors (`Ratpoints.Sieve.checkDen`), the denominators `1, …, H` in turn
(`Ratpoints.Sieve.sieveRun`), and the points at infinity (`Ratpoints.Sieve.pointsAtInfinity`).
Every row lets every point through, so the sieve finds exactly the points of the brute-force
reference `Ratpoints.bruteForce`, in the same order. The tables that the build of ratpoints
generates are computed here: the squares and the inverses by `Ratpoints.Sieve.squaresMod` and
`Ratpoints.Sieve.inversesMod`, and the row of `0` by `Ratpoints.Sieve.Entry.admits`, in its case
`r = 0`, and as words by `Ratpoints.Sieve.Entry.row`.

## Main definitions

* `Ratpoints.Sieve.squaresMod`, `Ratpoints.Sieve.inversesMod`: the squares and the inverses
  modulo `p`.
* `Ratpoints.Sieve.examinePrime`: the table of a prime.
* `Ratpoints.Sieve.Entry.admits`, `Ratpoints.Sieve.survives`: the rows of a denominator.
* `Ratpoints.Sieve.sieveDen`, `Ratpoints.Sieve.checkDen`, `Ratpoints.Sieve.sieveRun`: the sieve
  of one denominator, the points of its survivors, and the points of all denominators.
* `Ratpoints.Sieve.pointsAtInfinity`: the points at infinity.
* `Ratpoints.Sieve.andBitArray`, `Ratpoints.Sieve.clearLowBits`, `Ratpoints.Sieve.clearHighBits`,
  `Ratpoints.Sieve.isZeroAt`, `Ratpoints.Sieve.ctz`: the operations on the bit arrays of 64-bit
  words of the C code, and the lowest set bit of a word.
* `Ratpoints.Sieve.Entry.row`, `Ratpoints.Sieve.Entry.rows`, `Ratpoints.Sieve.SieveSpec`: the row
  of a denominator as words, the rows of the residues, each made when first needed, and a modulus
  with its row for the denominator at hand.
* `Ratpoints.Sieve.andRows`: the first stage over a piece of bit arrays, the rows of the moduli
  and-ed into its words.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The tables of a prime -/

/-- The squares modulo `p`, as a table of Booleans indexed by the residues: zero and the squares
of the odd residues `i < p`, as the generator of the tables of ratpoints marks them; for odd `p`,
the squares of `i` and of `p - i` agree, so these are all the squares.

C: `gen_find_points_h.c:69-88`

Deviation: a function of `p`, computed when it is called, for the row of `p` in the table
`squares` that the build generates. -/
def squaresMod (p : Nat) : Array Bool :=
  (List.range' 1 (p / 2) 2).foldl (fun w i ↦ w.set! (i * i % p) true)
    ((Array.replicate p false).set! 0 true)

/-- The inverses modulo `p`, as a table indexed by the residues: `0` for `0`, and for every other
residue `b` the least `i ≥ 1` with `i b ≡ 1 (mod p)`, found by trial.

C: `gen_find_points_h.c:33-44`, `gen_find_points_h.c:90-100`

Deviation: a function of `p`, computed when it is called, for the row of `p` in the table
`inverses` that the build generates; the trial stops before `p` and gives `0` when it finds
nothing, where `inv_mod_p` would not stop, which never happens for a prime `p` and a residue other
than `0`. -/
def inversesMod (p : Nat) : Array Nat :=
  (Array.range p).map fun b ↦ ((List.range' 1 (p - 1)).find? (· * b % p == 1)).getD 0

/-- Horner's rule modulo `p`: the value modulo `p` at `x` of the polynomial with the coefficient
list `cs`, constant term first, reduced at every step. -/
def evalMod (cs : List Nat) (p x : Nat) : Nat := cs.foldr (fun a v ↦ (a + x * v) % p) 0

/-- What the sieve keeps of a prime `p`: `p`, the table of the residues `x` modulo `p` for which
`f(x)` is a square modulo `p`, and the inverses modulo `p`.

C: `rp-private.h:542-555`

Deviation: only the fields that the rows of a prime read; the rows of the residues, which ratpoints
keeps in the field `sieve`, that of `0` from the build and the others made by `init` when a
denominator first needs them, are `Ratpoints.Sieve.Entry.rows`, made from
`Ratpoints.Sieve.Entry.admits` when first needed and kept for the run; the other fields serve the
composite moduli, the packing and the reduction of the sieve (stage F), and the choice of the
moduli. -/
structure Entry where
  /-- The prime. -/
  p : Nat
  /-- For each residue `x` modulo `p`, whether `f(x)` is a square modulo `p`. -/
  isFSquare : Array Bool
  /-- The inverses modulo `p` of the residues. -/
  inverses : Array Nat

/-- The table of the prime `p` for the polynomial `f` of degree `d` with the coefficient list `c`:
for each residue `x` modulo `p`, whether `f(x)` is a square modulo `p`, with `f(x)` by Horner's
rule modulo `p` (`Ratpoints.Sieve.evalMod`) on the coefficients reduced modulo `p`, and the squares
of `Ratpoints.Sieve.squaresMod`; kept, as the sieve entry of ratpoints keeps it, with `p` and the
inverses modulo `p` (`Ratpoints.Sieve.inversesMod`).

C: `find_points.c:1703-1749`, `find_points.c:1761-1765`, `find_points.c:1795-1824`

Deviation: the coefficients are integers, reduced by the Euclidean `%`, for the two paths of
ratpoints through `long`s and GMP integers (stage D), and they are not handed back, where
`examine_prime` leaves them in its caller's array for the test on the forbidden divisors of the
denominators (stage E); Horner's rule reduces at every step, for the reduction on a fixed schedule
(stage F), and also gives `f(0)`, which ratpoints reads off the constant term; the table has no
last entry, whether there are points at infinity modulo `p`, which ratpoints reads only for its
exits, the density, the prime powers and the forbidden divisors, never in a row or in the third
stage; the entry is made for every prime it is given, where `examine_prime` makes none when there
is no point at infinity modulo `p` and `f(x)` is a square for no residue (it returns `-1`, and the
search ends with no points: stage D) or for every residue (it returns `0`, and `p` is never a
modulus: the choice of the moduli, an input of the model), so that the residues with a square value
are not counted either; the entry keeps only `p`, the table and the inverses
(`Ratpoints.Sieve.Entry`), and no rows: `Ratpoints.Sieve.Entry.rows` makes them from it when they
are first needed, also the row of `0`, which `examine_prime` installs from the build. -/
def examinePrime (c : List Int) (d p : Nat) : Entry :=
  let cs := (List.range (d + 1)).map fun n ↦ (c.getD n 0 % (p : Int)).toNat
  let sq := squaresMod p
  { p, isFSquare := (Array.range p).map fun x ↦ sq[evalMod cs p x]!, inverses := inversesMod p }

/-! ### The rows of a denominator -/

/-- Whether the row of the denominator `b` in the table `e` of the prime `p` admits the numerator
`a`: for the residues `r = b mod p` and `x = a mod p`, the entry of the table at `x r⁻¹ mod p` if
`r ≠ 0`, and whether `x ≠ 0` if `r = 0`.

C: `init.c:42-46`, `init.c:62-83`, `init.c:99-111`, `init.c:118-246`, `gen_find_points_h.c:102-134`,
`gen_init_sieve_h.c:48-62`

Deviation: the bit of `a` in the row of `r`, computed from the tables for each numerator, where
ratpoints builds the row of a residue `r ≠ 0` once, when a denominator first needs it, as a bit
pattern of `p` bits repeated through words, by a function for each prime that the build generates,
and takes the row of `0` from the pattern `sieves0` that the build generates, whose bit `N` is
clear exactly when `p` divides `N`. -/
def Entry.admits (e : Entry) (b : Nat) (a : Int) : Bool :=
  let r := b % e.p
  let x := (a % (e.p : Int)).toNat
  if r = 0 then x != 0 else e.isFSquare[x * e.inverses[r]! % e.p]!

/-- Whether the numerator `a` survives the tables `entries` for the denominator `b`: the row of
`b` in every table admits `a` (`Ratpoints.Sieve.Entry.admits`). This test, a function of the
numerator, is the interface between the sieve and the check. -/
def survives (entries : List Entry) (b : Nat) (a : Int) : Bool := entries.all (·.admits b a)

/-! ### The sieve -/

/-- The sieve of the denominator `b`: an array of `2H + 1` Booleans, one for each numerator
`a = i - H`, all true at the start; for each table of `entries` in turn, every Boolean is replaced
by its conjunction with the row of `b` at its numerator (`Ratpoints.Sieve.Entry.admits`).

C: `sift.c:291-312`, `sift.c:405-431`, `sift.c:943-1022`, `sift.c:1030-1041`, `sift.c:1083-1086`,
`sift.c:1184-1202`

Deviation: one Boolean per numerator, for the bit arrays of words, the pieces of the numerator range
and the masks at their ends (stage C2); every numerator from `-H` to `H`, for the search region
(stage H) and the 2-adic classes (stages E and F); every table applied to every numerator, one after
the other, for the stages of ratpoints with their composite moduli, their packing and their
correction during the run (stage F): the second stage stops when no bit is left, and the third
tests one numerator at a time, only those that pass the test for common factors, stops at the first
prime that rejects it and skips the primes that divide `b`, with the inverses of `b` that
`fill_checks` looks up when the first such numerator of `b` reaches the stage; the cited lines are
the first stage of the build with 64-bit bit arrays, which the default build does in chunks of
registers, its second stage with the masks at the ends of the range, and its third stage. -/
def sieveDen (H b : Nat) (entries : List Entry) : Id (Vector Bool (2 * H + 1)) := do
  let mut surv := Vector.replicate (2 * H + 1) true
  for e in entries do
    for h : i in [0:2 * H + 1] do
      surv := surv.set i (surv[i] && e.admits b ((i : Int) - H))
  return surv

/-- The points `(a, y, b)` with the denominator `b` and a numerator `a = i - H` whose entry in
`surv` is true, by increasing `a`: each such numerator is tested for common factors with `b` and
checked exactly, as the brute-force reference checks it (`Ratpoints.BruteForce.pointsOfDen`):
`F(a, b)` by Horner's rule on the products `cₖ b^(d - k)`, computed once, with one more factor `b`
for odd `d`, then `(a, y, b)` and, for `y ≠ 0`, `(a, -y, b)` when `F(a, b) = y ^ 2` with `y ≥ 0`.

C: `sift.c:203-204`, `sift.c:262-264`, `sift.c:318-343`, `sift.c:438-446`, `sift.c:1061-1082`,
`sift.c:1088-1092`, `sift.c:1213-1299`, `find_points.c:5250-5338`

Deviation: the walk upwards through every Boolean, for the scan that steps over the bit arrays that
the first stage left empty, up to a sentinel past the range, and the walk by trailing zeros through
the words of the others (stage C2); entry `i` for the numerator `i - H`, where bit `t` of the bit
array stands for the numerator `a₀ + 2^k t` of the packing of the 2-adic class of `b`, which holds
only the numerators congruent to `a₀` modulo `2^k` (stages E and F); a plain `gcd`, for the binary
`gcd` of `relprime`, whose loop body has no branch (stage F); the third stage of `accepted` is
applied with the other moduli in `Ratpoints.Sieve.sieveDen` (stage F); no counts of the bit arrays
that survive the first stage and of the numerators that reach the test for common factors, pass it
and pass the third stage (`n_arrays`, `n_bits`, `n_coprime`, `n_checks`), which ratpoints reads to
correct the moduli during the run (stage F); the products `cₖ b^(d - k)` are computed for every
denominator, where ratpoints computes them when the first survivor reaches the check; a list of
points for the callback `process`, with no stop it may request, no reversal (stage D), and no
`RATPOINTS_NO_Y` and no `RATPOINTS_NO_CHECK` (stage G). -/
def checkDen (c : List Int) (d H b : Nat) (surv : Vector Bool (2 * H + 1)) :
    Id (Array (Int × Int × Int)) := do
  let w := BruteForce.scaledCoeffs c d b
  let f : Int := if d % 2 = 1 then b else 1
  let mut out := #[]
  for h : i in [0:2 * H + 1] do
    if surv[i] then
      let a := (i : Int) - H
      if Int.gcd a b = 1 then
        out := out ++ (BruteForce.pointsAbove a b (BruteForce.horner w a * f)).toArray
  return out

/-! ### Words and bit arrays -/

/-- Bit array `j` of the words `v` and-ed with bit array `x` of the row `row`, one word at a time:
for `κ < rbaPack` (`Ratpoints.rbaPack`, the number of words of a bit array), word
`rbaPack * j + κ` of `v` with word `rbaPack * x + κ` of `row`.

C: `rp-private.h:134`, `rp-private.h:176`, `rp-private.h:237`, `rp-private.h:263`,
`rp-private.h:287`

Deviation: one definition for every build, on bit arrays given by their indices in arrays of
words, each bit array `rbaPack` consecutive words, for the `&` on the vector type of the build. -/
def andBitArray {m : Nat} (v : Vector UInt64 m) (j : Nat) (row : Array UInt64) (x : Nat) :
    Vector UInt64 m :=
  Nat.fold rbaPack (fun κ _ v ↦
    v.set! (rbaPack * j + κ) (v[rbaPack * j + κ]! &&& row[rbaPack * x + κ]!)) v

/-- The lowest `s` bits of bit array `0` of the words `v` cleared, for `s < Ratpoints.rbaLength`:
the words below `s / 64` are set to `0`, and word `s / 64` is and-ed with `~~~0 <<< (s % 64)`.

C: `rp-private.h:153-155`, `rp-private.h:206-213`, `rp-private.h:242-244`,
`rp-private.h:268-270`, `rp-private.h:291`

Deviation: one definition for every build, the loop of the build with 512-bit bit arrays, of which
the macros of the builds with 256-bit and 128-bit bit arrays are unrolled cases and that of the
build with 64-bit bit arrays the case of one word; the bit array is the first `Ratpoints.rbaPack`
words of an array, for the vector type of the build. -/
def clearLowBits {m : Nat} (v : Vector UInt64 m) (s : Nat) : Vector UInt64 m :=
  let q := s / 64
  let v := Nat.fold q (fun l _ v ↦ v.set! l 0) v
  v.set! q (v[q]! &&& ~~~0 <<< (s % 64).toUInt64)

/-- The highest `s` bits of bit array `j` of the words `v` cleared, for `s < Ratpoints.rbaLength`:
for the number `rbaPack` of words of a bit array (`Ratpoints.rbaPack`), word
`q = rbaPack - 1 - s / 64` of the bit array is and-ed with `~~~0 >>> (s % 64)`, and its words
above `q` are set to `0`.

C: `rp-private.h:156-159`, `rp-private.h:214-221`, `rp-private.h:245-247`,
`rp-private.h:271-273`, `rp-private.h:292`

Deviation: one definition for every build, the loop of the build with 512-bit bit arrays, of which
the macros of the builds with 256-bit and 128-bit bit arrays are unrolled cases and that of the
build with 64-bit bit arrays the case of one word; the bit array is given by its index in an array
of words, `rbaPack` consecutive words, for a pointer to a value of the vector type of the
build. -/
def clearHighBits {m : Nat} (v : Vector UInt64 m) (j s : Nat) : Vector UInt64 m :=
  let q := rbaPack - 1 - s / 64
  let v := v.set! (rbaPack * j + q) (v[rbaPack * j + q]! &&& ~~~0 >>> (s % 64).toUInt64)
  Nat.fold (rbaPack - 1 - q) (fun l _ v ↦ v.set! (rbaPack * j + q + 1 + l) 0) v

/-- Whether bit array `pos` of the words `v` is zero: for the number `rbaPack` of words of a bit
array (`Ratpoints.rbaPack`), its words `rbaPack * pos + κ`, `κ < rbaPack`, are all `0`.

C: `rp-private.h:137-152`, `rp-private.h:179-202`, `rp-private.h:241`, `rp-private.h:267`,
`rp-private.h:290`, `rp-private.h:306-308`

Deviation: one definition for every build, on a bit array given by its index in an array of words,
`rbaPack` consecutive words that it compares with `0` one at a time, for the tests of the builds on
the vector type, with vector instructions or by or-ing its words; the test for zero `TESTZ` also
stands for its negation `TEST`. -/
def isZeroAt {m : Nat} (v : Vector UInt64 m) (pos : Nat) : Bool :=
  Nat.all rbaPack fun κ _ ↦ v[rbaPack * pos + κ]! == 0

/-- The position of the lowest set bit of a word `w ≠ 0`: `w` is shifted right while its lowest
bit is clear, and the steps are counted. On `0` the loop does not end, as in the C code.

C: `rp-private.h:429-444`

Deviation: the loop for a compiler without the builtin, where gcc and clang take
`__builtin_ctzl`. -/
def ctz (w : UInt64) : Id Nat := do
  let mut w := w
  let mut t := 0
  while w &&& 1 == 0 do
    w := w >>> 1
    t := t + 1
  return t

/-! ### The rows as words -/

/-- The pattern `pat` of period `p` packed into `p / 64 + 2` words, over the positions
`0, …, p + 63` and a little beyond: bit `t` of word `q` is the entry of `pat` at
`(64 q + t) mod p`, so that the 64 positions from any position below `p` on lie in two
consecutive words (`Ratpoints.Sieve.window`). -/
def packedPattern (pat : Array Bool) (p : Nat) : Array UInt64 :=
  (Array.range (p / 64 + 2)).map fun q ↦
    Nat.fold 64 (fun t _ w ↦ if pat[(64 * q + t) % p]! then w ||| (1 : UInt64) <<< t.toUInt64
      else w) 0

/-- The 64 bits of the packed words `E` from position `s` on, where bit `t` of word `q` is at
position `64 q + t`: word `s / 64` shifted right by `r = s % 64`, and for `r ≠ 0` the lowest `r`
bits of the next word above them. -/
def window (E : Array UInt64) (s : Nat) : UInt64 :=
  let q := s / 64
  let r := s % 64
  if r = 0 then E[q]! else (E[q]! >>> r.toUInt64) ||| (E[q + 1]! <<< (64 - r).toUInt64)

/-- The row of the denominator `b` in the table `e`, as `e.p` bit arrays of `Ratpoints.rbaPack`
words: the pattern of one period, whether the row admits the numerator `N` for `N < e.p`
(`Ratpoints.Sieve.Entry.admits`), packed into words (`Ratpoints.Sieve.packedPattern`); for
`j < e.p`, word `j` the 64 bits of the packed pattern from position `64 j mod e.p` on
(`Ratpoints.Sieve.window`); and these `e.p` words repeated `rbaPack` times. Bit `t` of word `j`
says whether the row admits `64 j + t`, since `Ratpoints.Sieve.Entry.admits` depends only on the
residue modulo `e.p`.

C: `init.c:42-46`, `init.c:62-83`, `init.c:99-111`, `init.c:118-246`, `gen_find_points_h.c:102-134`,
`gen_init_sieve_h.c:48-62`

Deviation: the pattern of one period from `Ratpoints.Sieve.Entry.admits`, laid out in words by
windows into its packed form, for the builders of `init.c`, which step through the residues
`a b⁻¹ mod p` four at a time and rotate the pattern through the words, one function for each prime
that the build generates, and for the pattern `sieves0` that the build generates for the row of `0`
(stage F); no copies of the first bit arrays at the end of the row, which only the chunked first
stage reads. -/
def Entry.row (e : Entry) (b : Nat) : Array UInt64 :=
  let pat := (Array.range e.p).map fun N : Nat ↦ e.admits b N
  let E := packedPattern pat e.p
  let base := (Array.range e.p).map fun j ↦ window E (64 * j % e.p)
  (Array.range (e.p * rbaPack)).map fun j ↦ base[j % e.p]!

/-- The rows of the residues `r = 0, …, e.p - 1` in the table `e` (`Ratpoints.Sieve.Entry.row`),
each a thunk: it is made when a denominator first needs it and kept from then on, as long as the
array is. -/
def Entry.rows (e : Entry) : Array (Thunk (Array UInt64)) :=
  (Array.range e.p).map fun r ↦ Thunk.mk fun _ ↦ e.row r

/-- A modulus with its row for the denominator at hand, `p` bit arrays of `Ratpoints.rbaPack`
words: bit array `x` of the row says which numerators of the bit array with the word number `w` the
row admits, for every `w ≡ x (mod p)`.

C: `rp-private.h:378-379`

Deviation: the row for the pointer `ptr` to it, with no `offset`, which carries the shift of the
packing of the 2-adic classes and a multiple of `p` that keeps the index non-negative (stage F),
and no pointers `start` and `end` into the row, which serve the first stage: the components index
the row by the word number modulo `p`. -/
structure SieveSpec where
  /-- The modulus. -/
  p : Nat
  /-- The row: `p` bit arrays of `Ratpoints.rbaPack` words. -/
  row : Array UInt64

/-! ### One piece -/

/-- The first stage over a piece, the bit arrays with the word numbers `w0, …, w0 + n - 1`, which
are the first `n` bit arrays of `surv`: their words are set to all ones; then for each modulus `p`
of `specs` with its row and for `r = (-w0) mod p`, bit array `j` is and-ed with bit array
`(w0 + j) mod p` of the row (`Ratpoints.Sieve.andBitArray`), in three loops: if `n < r`, with the
`n` bit arrays of the row from `p - r` on, and otherwise with the `r` bit arrays from `p - r` on,
then with whole periods of `p` bit arrays from `0`, then with the rest from `0`. The last bit
array of `surv`, the place of the sentinel, is left as it is.

C: `sift.c:291-312`, `sift.c:405-431`, `sift.c:943-1022`, `sift.c:1083-1086`

Deviation: every modulus in the first stage, over every bit array, for the second stage, which
and-s the rows of its moduli into the nonzero bit arrays until none is left, and the third stage,
which tests one numerator at a time after the test for common factors, stops at the first prime
that rejects it, skips the primes that divide `b`, and looks up the inverses of `b` when the first
numerator of `b` reaches it (stage F); the first stage of the builds with one register per chunk,
for the chunks of sixteen registers of the default build with the legs over the tail of a piece
(stage F); all ones, written one word at a time from the first, where ratpoints writes the 2-adic
pattern of the class of `b` into the bit arrays from the last (stage E); the row of the word
number `w` at index `w mod p`, where ratpoints adds the offset of the packing and a multiple of
`p` that keeps the index non-negative, and reduces by a multiplication when that is exact
(stage F); indices for the pointers into the rows and into the survivors, and the number of whole
periods and the rest computed before their loops. -/
def andRows (specs : List SieveSpec) (w0 : Int) (n : Nat)
    (surv : Vector UInt64 ((n + 1) * rbaPack)) : Id (Vector UInt64 ((n + 1) * rbaPack)) := do
  let mut surv := surv
  for i in [0:n * rbaPack] do
    surv := surv.set! i (~~~0)
  for s in specs do
    let p := s.p
    let r := ((-w0) % (p : Int)).toNat
    if n < r then
      for j in [0:n] do
        surv := andBitArray surv j s.row (p - r + j)
    else
      for j in [0:r] do
        surv := andBitArray surv j s.row (p - r + j)
      let left := n - r
      for k in [0:left / p] do
        for i in [0:p] do
          surv := andBitArray surv (r + k * p + i) s.row i
      for i in [0:left % p] do
        surv := andBitArray surv (r + left / p * p + i) s.row i
  return surv

/-! ### The run and the points at infinity -/

/-- The points with the denominators `b = 1, …, H`, in increasing order: each denominator is
sieved with the tables `entries` (`Ratpoints.Sieve.sieveDen`), its survivors are checked
(`Ratpoints.Sieve.checkDen`), and the points are appended in turn.

C: `find_points.c:4059-4075`, `find_points.c:5152-5160`

Deviation: every denominator from `1` to `H`, one after the other, for the denominator range
`b_low, …, b_high` (stage H), the loop shapes, the tests on the denominators and the blocks
(stage E), and for the threads, which deliver the blocks in the same order; the residues of `b`
divided by `2^k` modulo the moduli of the first two stages, which ratpoints computes once per
denominator (`fill_bp_list`, `k` the stride of the packing), are the residues `b mod p` that
`Ratpoints.Sieve.Entry.admits` computes for each numerator (stage F); no stop by the callback
(stage G), and no correction of the moduli between the blocks (stage F). -/
def sieveRun (c : List Int) (d H : Nat) (entries : List Entry) : Id (Array (Int × Int × Int)) := do
  let mut out := #[]
  for j in [0:H] do
    let surv ← sieveDen H (j + 1) entries
    let pts ← checkDen c d H (j + 1) surv
    out := out ++ pts
  return out

/-- The points at infinity of the polynomial of degree `d` with the coefficient list `c`:
`(1, 0, 0)` for odd `d`; for even `d`, `(1, s, 0)` and `(1, -s, 0)` when `c_d = s ^ 2` with
`s > 0`, `(1, 0, 0)` when `c_d = 0`, and none when `c_d` is not a square.

C: `find_points.c:4634`, `find_points.c:4894-4899`, `find_points.c:5068-5105`

Deviation: a list of points for the callback `process`, with no stop it may request, no reversal
(stage D), no `RATPOINTS_NO_Y` and no `RATPOINTS_NO_CHECK` (stage G), and no output under
`RATPOINTS_VERBOSE`; the case `c_d = 0`, that of the zero polynomial, which ratpoints refuses before
it gets here, gives the one point `(1, 0, 0)`, which the cited lines, delivering `-y` without a
test `y ≠ 0`, would deliver twice. -/
def pointsAtInfinity (c : List Int) (d : Nat) : List (Int × Int × Int) :=
  if d % 2 = 1 then [(1, 0, 0)] else BruteForce.pointsAbove 1 0 (c.getD d 0)

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

-- `y ^ 2 = x ^ 2 + 1` modulo 5: `f(x)` is a square for `x = 0, 2, 3` (`f = 1, 0, 0`).
#guard (examinePrime [1, 0, 1] 2 5).isFSquare == #[true, false, true, true, false]

-- The row of `b = 3` modulo 5 admits `a` when `f(a / 3)` is a square modulo 5.
#guard (List.range 5).map (fun a : Nat ↦ (examinePrime [1, 0, 1] 2 5).admits 3 a) ==
  [true, true, false, false, true]

-- The sieve of a denominator is the survivor test of the numerators.
#guard
  let es := [3, 5, 7].map (examinePrime [1, 2, 3, 4, 5, 6, 7] 6)
  (Id.run (sieveDen 20 7 es)).toList ==
    (List.range 41).map fun i : Nat ↦ survives es 7 ((i : Int) - 20)

-- The survivors of the sieve of `y ^ 2 = x ^ 3 - 2` for the denominator 100 give the point
-- `(129 : 3830 : 100)`, which every numerator gives as well.
#guard
  let es := [3, 5, 7, 11, 13].map (examinePrime [-2, 0, 0, 1] 3)
  (Id.run (checkDen [-2, 0, 0, 1] 3 130 100 (Id.run (sieveDen 130 100 es)))).toList ==
    [(129, 3830, 100), (129, -3830, 100)] &&
  (Id.run (checkDen [-2, 0, 0, 1] 3 130 100 (Vector.replicate _ true))).toList ==
    [(129, 3830, 100), (129, -3830, 100)]

-- `andBitArray` on two bit arrays: bit array 1 is and-ed with bit array 2 of a row, word by word,
-- and bit array 0 stays as it is.
#guard
  let v : Vector UInt64 (2 * rbaPack) := .ofFn fun i ↦ 0x0123456789abcdef * (i.val.toUInt64 + 1)
  let row : Array UInt64 := .ofFn (n := 3 * rbaPack) fun i ↦ ~~~(1 <<< i.val.toUInt64)
  (List.range (2 * rbaPack)).all fun y ↦ (andBitArray v 1 row 2)[y]! ==
    if y / rbaPack = 1 then v[y]! &&& row[rbaPack * 2 + y % rbaPack]! else v[y]!

-- The masks on two bit arrays: the low mask keeps bit `t` of word `y` exactly when
-- `s ≤ 64 y + t`, and the high mask on bit array 1 exactly when `64 y + t + s < 2 rbaLength`.
#guard
  let v : Vector UInt64 (2 * rbaPack) := .ofFn fun i ↦ 0x0123456789abcdef * (i.val.toUInt64 + 1)
  let bit (w : UInt64) (t : Nat) : Bool := (w >>> t.toUInt64) &&& 1 == 1
  ([0, 1, 63, 64, 65, 130, rbaLength - 1].filter (· < rbaLength)).all fun s ↦
    (List.range (2 * rbaPack)).all fun y ↦ (List.range 64).all fun t ↦
      bit (clearLowBits v s)[y]! t == (bit v[y]! t && decide (s ≤ 64 * y + t)) &&
      bit (clearHighBits v 1 s)[y]! t == (bit v[y]! t && decide (64 * y + t + s < rbaLength * 2))

-- `isZeroAt` on three bit arrays: the first has a set bit in its last word, the second none, the
-- third one in its first word.
#guard
  let v : Vector UInt64 (3 * rbaPack) :=
    ((Vector.replicate _ 0).set! (rbaPack - 1) 0x8000000000000000).set! (2 * rbaPack) 1
  [isZeroAt v 0, isZeroAt v 1, isZeroAt v 2] == [false, true, false]

-- The lowest set bit: `k` for `2 ^ k + 2 ^ 63`, `k < 64`, and the trailing zeros of a few other
-- words.
#guard (List.range 64).all fun k ↦ Id.run (ctz ((1 <<< k.toUInt64) ||| 0x8000000000000000)) == k
#guard [1, 2, 40, 0xfff0, 0x8000000000000000].all fun w : UInt64 ↦
  Id.run (ctz w) == w.toBitVec.ctz.toNat

-- The rows as words against the row test: bit `t` of word `j` of the row of `b` says whether the
-- row admits `64 j + t`, for denominators of several residues modulo `p`, `0` among them, and for
-- a prime above 64.
#guard
  let bit (w : UInt64) (t : Nat) : Bool := (w >>> t.toUInt64) &&& 1 == 1
  [3, 5, 7, 13, 67].all fun p ↦
    let e := examinePrime [1, 2, 3, 4, 5, 6, 7] 6 p
    [0, 1, 2, 5, p + 3].all fun b ↦
      let row := e.row b
      row.size == p * rbaPack && (List.range (p * rbaPack)).all fun j ↦
        (List.range 64).all fun t ↦ bit row[j]! t == e.admits b (64 * j + t)

-- The row of `0` against the pattern `sieves0` that the build of ratpoints generates, for 3, 5, 7,
-- 11 and 13: the first `p` of its `RBA_PACK * p` words, which repeat them.
#guard
  ([(3, #[0x6db6db6db6db6db6, 0xb6db6db6db6db6db, 0xdb6db6db6db6db6d]),
    (5, #[0xef7bdef7bdef7bde, 0xdef7bdef7bdef7bd, 0xbdef7bdef7bdef7b, 0x7bdef7bdef7bdef7,
      0xf7bdef7bdef7bdef]),
    (7, #[0x7efdfbf7efdfbf7e, 0xbf7efdfbf7efdfbf, 0xdfbf7efdfbf7efdf, 0xefdfbf7efdfbf7ef,
      0xf7efdfbf7efdfbf7, 0xfbf7efdfbf7efdfb, 0xfdfbf7efdfbf7efd]),
    (11, #[0xff7feffdffbff7fe, 0xfdffbff7feffdffb, 0xf7feffdffbff7fef, 0xdffbff7feffdffbf,
      0x7feffdffbff7feff, 0xffbff7feffdffbff, 0xfeffdffbff7feffd, 0xfbff7feffdffbff7,
      0xeffdffbff7feffdf, 0xbff7feffdffbff7f, 0xffdffbff7feffdff]),
    (13, #[0xffefff7ffbffdffe, 0xffdffefff7ffbffd, 0xffbffdffefff7ffb, 0xff7ffbffdffefff7,
      0xfefff7ffbffdffef, 0xfdffefff7ffbffdf, 0xfbffdffefff7ffbf, 0xf7ffbffdffefff7f,
      0xefff7ffbffdffeff, 0xdffefff7ffbffdff, 0xbffdffefff7ffbff, 0x7ffbffdffefff7ff,
      0xfff7ffbffdffefff])] : List (Nat × Array UInt64)).all fun (p, ws) ↦
    ((examinePrime [1, 0, 1] 2 p).row 0).extract 0 p == ws

-- The rows of the residues, each made when first needed.
#guard
  let e := examinePrime [1, 2, 3, 4, 5, 6, 7] 6 7
  e.rows.size == 7 && (List.range 7).all fun r ↦ (e.rows[r]!).get == e.row r

-- The first stage against the survivor test: bit `t` of word `y` of a piece is the survivor test
-- of the numerator `rbaLength w0 + 64 y + t`, for pieces from below and above zero with the
-- moduli 3, 5 and 7, and with `n < r`, `r = 0`, and whole periods and a rest after the first `r`
-- bit arrays.
#guard
  let bit (w : UInt64) (t : Nat) : Bool := (w >>> t.toUInt64) &&& 1 == 1
  let es := [3, 5, 7].map (examinePrime [1, 2, 3, 4, 5, 6, 7] 6)
  ([(-9, 1), (-9, 12), (-35, 4), (6, 2), (15, 17)] : List (Int × Nat)).all fun (w0, n) ↦
    [1, 10].all fun b ↦
      let v := Id.run (andRows (es.map fun e ↦ ⟨e.p, e.row b⟩) w0 n (Vector.replicate _ 0))
      (List.range (n * rbaPack)).all fun y ↦ (List.range 64).all fun t ↦
        bit v[y]! t == survives es b (rbaLength * w0 + 64 * y + t)

-- The denominators `1, …, 130`: the affine points of `ratpoints '-2 0 0 1' 130 -q`.
#guard (Id.run (sieveRun [-2, 0, 0, 1] 3 130
    ([3, 5, 7, 11, 13].map (examinePrime [-2, 0, 0, 1] 3)))).toList ==
  [(3, 5, 1), (3, -5, 1), (129, 3830, 100), (129, -3830, 100)]

#guard pointsAtInfinity [1, 0, 0, 0, 9] 4 == [(1, 3, 0), (1, -3, 0)] &&
  pointsAtInfinity [1, 0, 0, 0, 2] 4 == [] && pointsAtInfinity [1, 2, 3, 4] 3 == [(1, 0, 0)]

end Sieve

end Ratpoints

end
