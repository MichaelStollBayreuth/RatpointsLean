/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Constants
public import Ratpoints.Model.FirstStage
public import Ratpoints.Model.Tables
public import Std.Data.HashMap.Basic

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Constants
meta import Ratpoints.Model.FirstStage
meta import Ratpoints.Model.Tables

/-!
# The rows of the moduli

The rows of the sieve entries as words, built as the C code builds them in `init.c` and in the
generators of the headers of the build, and the tables in which the C code keeps them: every row of
the modulus `m` has `m + chunk - 1` bit arrays of `Ratpoints.rbaPack` words, for the chunk
`Ratpoints.chunk`, `m` bit arrays and copies of the first `chunk - 1` of them, which the chunked
first stage reads past the first `m` (`Ratpoints.Sieve.andRowsChunked`); word `j` of the row of the
residue `b` has bit `t` set exactly when the row admits the numerator `64 j + t`
(`Ratpoints.Sieve.Entry.admits`, the reference of the rows of a prime). The row of `0` of a prime of
the table is the pattern `sieves0` that the build generates, from the words of the forbidden divisor
`p` (`Ratpoints.Sieve.sieves0`, `Ratpoints.Sieve.forbiddenRow`); the rows of the other residues of a
prime are built by the function that the build generates for the prime, from the code
`CODE_INIT_SIEVE1` for a prime below 64 (`Ratpoints.Sieve.sieveInit1`) and `CODE_INIT_SIEVE2` for a
prime above 64 (`Ratpoints.Sieve.sieveInit2`), which compute the pattern of the row four bits at a
time (`Ratpoints.Sieve.initFourDecl`, `Ratpoints.Sieve.initFourLoop`, `Ratpoints.Sieve.initBit`),
rotate it through the words and copy them (`Ratpoints.Sieve.initReplicate`). The row of a prime
power is laid out from its pattern (`Ratpoints.Sieve.sieveInitPower`,
`Ratpoints.Sieve.layOutPattern`), and the row of a product is the and of the rows of its factors,
laid down in blocks of the length of each factor (`Ratpoints.Sieve.sieveInitProduct`), which builds
the rows of its factors that are absent first (`Ratpoints.Sieve.factorRows`). The rows are kept in
tables, one for each entry of the C code, by the residue (`Ratpoints.Sieve.RowStore`), into which
each builder stores the row that it builds (`Ratpoints.Sieve.RowStore.publish`); the row of a sieve
entry is read from its table of rows or built into it by the builder of its kind
(`Ratpoints.Sieve.SieveEntry.fetchRow`, `Ratpoints.Sieve.SieveEntry.initRow`,
`Ratpoints.Sieve.initFactorRow`). The run does not call the builders yet: it takes its rows from the
plain builder (`Ratpoints.Sieve.SieveEntry.row`), which gives the same words, until stage F4 makes
the tables of rows of a run and builds its rows into them.

## Main definitions

* `Ratpoints.Sieve.forbiddenRow`, `Ratpoints.Sieve.sieves0`: the words of a forbidden divisor, and
  the row of `0` of a prime of the table.
* `Ratpoints.Sieve.RowStore`, `Ratpoints.Sieve.RowStore.row?`, `Ratpoints.Sieve.RowStore.publish`:
  the tables of rows, a row read from them, and a row stored into them.
* `Ratpoints.Sieve.initBit`, `Ratpoints.Sieve.initFourDecl`, `Ratpoints.Sieve.initFourLoop`,
  `Ratpoints.Sieve.initReplicate`: the macros of `init.c` with which the rows of the primes are
  built.
* `Ratpoints.Sieve.sieveInit1`, `Ratpoints.Sieve.sieveInit2`: the rows of a prime below 64 and above
  64, each stored into the table of rows of its entry.
* `Ratpoints.Sieve.window`, `Ratpoints.Sieve.repeatPattern`, `Ratpoints.Sieve.layOutPattern`: the
  64 bits of packed words from a position on, and a pattern of period `m` repeated through words
  and laid out as a row.
* `Ratpoints.Sieve.powerPatternUnit`, `Ratpoints.Sieve.powerPatternNonunit`,
  `Ratpoints.Sieve.sieveInitPower`: the patterns of the rows of a prime power, and its rows, each
  stored into the table of rows of its entry.
* `Ratpoints.Sieve.initFactorRow`, `Ratpoints.Sieve.factorRows`, `Ratpoints.Sieve.productCopy`,
  `Ratpoints.Sieve.productAnd`, `Ratpoints.Sieve.sieveInitProduct`: the builder of the entry of a
  factor by its kind, the rows of the factors of a product, built into their tables of rows when
  absent, the blocks of the rows of the factors, and the rows of a product, each stored into the
  table of rows of its entry.
* `Ratpoints.Sieve.SieveEntry.initRow`, `Ratpoints.Sieve.SieveEntry.fetchRow`: the row of a sieve
  entry built by the builder of its kind, and read from its table of rows or built into it.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### The row of `0` of a prime -/

/-- The words of the forbidden divisor `p`, and of the row of `0` of a prime `p` of the table: `p`
words, word `r` with bit `j` clear exactly when `p ∣ 64 r + j`, made as the generator of the tables
of the build makes its array `work` and as `sieving_info` makes the words of a forbidden divisor
beyond the table: all ones, then for `i < 64` the bit of the position `p i` cleared, the position
`N` being bit `N mod 64` of word `⌊N / 64⌋`. The pattern `sieves0` repeats them
(`Ratpoints.Sieve.sieves0`).

C: `find_points.c:2773-2777`, `gen_find_points_h.c:118-120`

Deviation: one function for the two codes that make these words, the array `work` of the generator
of `find_points.h`, for the primes of the table, and the words that `sieving_info` makes in the
buffer `forb_words` for the forbidden divisors beyond the table (`Ratpoints.Sieve.forbidden`), with
the positions `p i` for `i < 64`, for the positions `m = 0, p, 2 p, …` below `64 p` there; a fresh
array of `p` words, for the array `work` of `RATPOINTS_MAX_PRIME` words and for the space in the
buffer; divisions and remainders for the shifts and masks by `LONG_SHIFT` and `LONG_MASK`. -/
def forbiddenRow (p : Nat) : Array UInt64 :=
  Nat.fold 64 (fun i _ row ↦ row.modify (p * i / 64) (· &&& ~~~(1 <<< (p * i % 64).toUInt64)))
    (Array.replicate p (~~~0))

/-- The row of `0` of the prime `p` of the table, the pattern `sieves0[pn]` that the generator of
the tables of the build writes for the prime `p = prime[pn]`: the `p` words `work` of the forbidden
divisor `p` (`Ratpoints.Sieve.forbiddenRow`) written `Ratpoints.rbaPack` times, the first `p` bit
arrays, and then the `rbaPack (chunk - 1)` words `work[i mod p]`, the copies of the first
`Ratpoints.chunk - 1` bit arrays, so that word `x` is word `x mod p` of `work` for
`x < (p + chunk - 1) rbaPack`. Bit `t` of word `x` is set exactly when `p ∤ 64 x + t`. The
forbidden divisors that are primes of the table read its first `p` words
(`Ratpoints.Sieve.forbiddenOfPrime`, `Ratpoints.Sieve.forbidden`); in the C code the sieve entry of
a prime of the table has it as its row of `0`, which the run of the model reads from stage F4 on,
and until then the same words from the plain builder (`Ratpoints.Sieve.SieveEntry.row`).

C: `find_points.c:37`, `gen_find_points_h.c:102-116`, `gen_find_points_h.c:122-134`

Deviation: a function of `p`, computed when it is called, for the row of `p` in the table `sieves0`
that the build generates and that `find_points.c` includes; its first `(p + chunk - 1) rbaPack`
words, for the row of `RBA_PACK (RATPOINTS_MAX_PRIME_EVEN + RATPOINTS_CHUNK - 1)` words whose other
words are `0` and never read. -/
def sieves0 (p : Nat) : Array UInt64 :=
  let work := forbiddenRow p
  Nat.fold rbaPack (fun _ _ s ↦ s ++ work) #[] ++
    (Array.range (rbaPack * (chunk - 1))).map fun i ↦ work[i % p]!

/-! ### The tables of rows -/

/-- The tables of rows of the entries of a run: for the reference to an entry
(`Ratpoints.Sieve.EntryRef`), the table of its rows by the residue of the denominator modulo its
modulus, `m` of them for the modulus `m`, each `none` until it is built. These are the arrays
`sieve` of the sieve entries of ratpoints, which the C code reaches through the pointers to the
entries (`sieve_list[n]`, and the field `factor` of the entry of a product), with `none` for `NULL`.
The builders store the rows that they build into the table of their entry
(`Ratpoints.Sieve.RowStore.publish`); the tables of a run, made where the C code makes the entries
and handed through the run, come with stage F4. -/
abbrev RowStore := Std.HashMap EntryRef (Array (Option (Array UInt64)))

/-- The row of the residue `r` in the table of the entry `ref`, the pointer `se->sieve[r]`: none
when the row is not built yet, or when there is no such table or row. -/
def RowStore.row? (s : RowStore) (ref : EntryRef) (r : Nat) : Option (Array UInt64) :=
  (s.getD ref #[]).getD r none

/-- The store with the row `row` of the residue `r` in the table of the entry `ref`, the store
`RP_PUBLISH(&se->sieve[b], row)` of the row into its entry with which each builder ends
(`Ratpoints.Sieve.sieveInit1`, `Ratpoints.Sieve.sieveInit2`, `Ratpoints.Sieve.sieveInitPower`,
`Ratpoints.Sieve.sieveInitProduct`); the store as it is when it has no table of `ref`. -/
def RowStore.publish (s : RowStore) (ref : EntryRef) (r : Nat) (row : Array UInt64) : RowStore :=
  s.modify ref (·.set! r (some row))

/-! ### The rows of a prime -/

/-- The word `w` with bit `i < 64` or-ed with the Boolean `v`, `RP_INIT_BIT` in its form without a
branch, `w | v << i`.

C: `init.c:42-46`

Deviation: the form of the production builds, where `RP_INIT_BRANCH` is not set; a Boolean for the
`int` entry of `is_f_square`, which is `0` or `1`. -/
def initBit (w : UInt64) (v : Bool) (i : Nat) : UInt64 := w ||| v.toUInt64 <<< i.toUInt64

/-- `RP_INIT_FOUR_DECL`: from the inverse `d < p` of the residue of the denominator, the residues
`ab1 = d`, `ab2 = 2 d mod p` and `ab3 = 3 d mod p` of the second, third and fourth of the four lanes
that compute the pattern of a row of the prime `p` four bits at a time, and their step
`d4 = 4 d mod p`, each by one conditional subtraction of `p`.

C: `init.c:62-63`, `init.c:65-70`

Deviation: the form of the production builds, where `RP_INIT_ONEWAY` is not set; the residues
returned, for the variables that the macro declares in its caller; natural numbers for the
`long`s. -/
def initFourDecl (p d : Nat) : Nat × Nat × Nat × Nat :=
  let ab1 := d
  let ab2 := ab1 + d
  let ab2 := if ab2 ≥ p then ab2 - p else ab2
  let ab3 := ab2 + d
  let ab3 := if ab3 ≥ p then ab3 - p else ab3
  let d4 := ab3 + d
  let d4 := if d4 ≥ p then d4 - p else d4
  (ab1, ab2, ab3, d4)

/-- `RP_INIT_FOUR_LOOP`: the bits of the word `w` from bit `i = lo` on, four at a time while
`i + 4 ≤ hi`, bit `i + k` the entry of the table `isfs` at the residue of lane `k` (`ab`, `ab1`,
`ab2`, `ab3`), each lane then stepped by `d4` modulo `p` by a conditional subtraction; the word,
the bit `i` reached and the residues of the lanes, with which the caller goes on.

C: `init.c:64`, `init.c:72-83`

Deviation: the form of the production builds, where `RP_INIT_ONEWAY` is not set; the table, the
prime, the step, the word, the residues and the bounds as arguments and the word, the bit and the
residues returned, for the variables of its caller that the macro reads and writes; Booleans for the
`int` entries of `is_f_square`; the steps `ab += d4; if (ab >= p) ab -= p;` as conditional
values. -/
def initFourLoop (isfs : Array Bool) (p d4 : Nat) (w : UInt64) (lo hi ab ab1 ab2 ab3 : Nat) :
    Id (UInt64 × Nat × Nat × Nat × Nat × Nat) := do
  let mut w := w
  let mut ab := ab
  let mut ab1 := ab1
  let mut ab2 := ab2
  let mut ab3 := ab3
  let mut i := lo
  while i + 4 ≤ hi do
    w := w ||| (isfs[ab]!.toUInt64 <<< i.toUInt64 ||| isfs[ab1]!.toUInt64 <<< (i + 1).toUInt64 |||
      isfs[ab2]!.toUInt64 <<< (i + 2).toUInt64 ||| isfs[ab3]!.toUInt64 <<< (i + 3).toUInt64)
    ab := if ab + d4 ≥ p then ab + d4 - p else ab + d4
    ab1 := if ab1 + d4 ≥ p then ab1 + d4 - p else ab1 + d4
    ab2 := if ab2 + d4 ≥ p then ab2 + d4 - p else ab2 + d4
    ab3 := if ab3 + d4 ≥ p then ab3 + d4 - p else ab3 + d4
    i := i + 4
  return (w, i, ab, ab1, ab2, ab3)

/-- `RP_INIT_REPLICATE` for the prime `p`: the first `p` words of the row `si` repeated through the
words of its first `p` bit arrays, word `a + k p` set to word `a` for `a < p` and
`1 ≤ k < Ratpoints.rbaPack`; then the copies of the first `(chunk - 1) rbaPack` words after the
first `p rbaPack`, word `p rbaPack + k` set to word `k`, in this order, so that they copy words
already copied when `p < chunk - 1` (`Ratpoints.chunk`). Word `j` of the result is word `j mod p` of
`si` for `j < (p + chunk - 1) rbaPack`.

C: `init.c:99-111`

Deviation: the row passed and returned, for the pointer `si` of its caller. -/
def initReplicate {n : Nat} (p : Nat) (si : Vector UInt64 n) : Id (Vector UInt64 n) := do
  let mut si := si
  for a in [0:p] do
    for k in [1:rbaPack] do
      si := si.set! (a + k * p) si[a]!
  for k in [0:(chunk - 1) * rbaPack] do
    si := si.set! (p * rbaPack + k) si[k]!
  return si

/-- The pattern of the row of the residue `b` of the prime `p = t.p < 64` in `CODE_INIT_SIEVE1`: the
word `help0` whose bit `a < p` is the entry of the table of `t` at `a d mod p`, for the inverse `d`
of `b` modulo `p` from the table of inverses of `t`: four bits at a time from the four lanes of the
residues `a d mod p` (`Ratpoints.Sieve.initFourDecl`, `Ratpoints.Sieve.initFourLoop`), and the bits
left over, `p mod 4` of them, one at a time from the first lane (`Ratpoints.Sieve.initBit`), its
residue stepped by `d` modulo `p`.

C: `init.c:131-143`

Deviation: the steps `ab += d; if (ab >= p) ab -= p;` as conditional values; the results of the
loop of four bits read as the components of its tuple; natural numbers for the `long`s. -/
def sieve1Pattern (t : Entry) (b : Nat) : Id UInt64 := do
  let d := t.inverses[b]!
  let lanes := initFourDecl t.p d
  let r ← initFourLoop t.isFSquare t.p lanes.2.2.2 0 0 t.p 0 lanes.1 lanes.2.1 lanes.2.2.1
  let mut he0 := r.1
  let mut ab := r.2.2.1
  for a in [r.2.1:t.p] do
    he0 := initBit he0 t.isFSquare[ab]! a
    ab := if ab + d ≥ t.p then ab + d - t.p else ab + d
  return he0

/-- The first `p` words of the row of a prime `p < 64` in `CODE_INIT_SIEVE1`, from the word
`help0`, the pattern of the row repeated through the word, and the word `help1`, the pattern
shifted right by `64 mod p`: word `0` of the row `help0`, and for `a = 1, …, p - 1` word `a` the
rotation `help1 | help0 << diff_shift`, for `diff_shift = (⌊64 / p⌋ + 1) p mod 64`, with `help1`
then the bits of the old `help0` shifted out by `diff = 64 - diff_shift`.

C: `init.c:160-177`

Deviation: `ldp`, `p1`, `diff_shift` and `diff` computed where they are used, for the variables of
the function; the mask `p1 & LONG_MASK` as the remainder by 64; a fresh vector of
`(p + chunk - 1) rbaPack` words, for the space that the builder takes from the buffer of the tables
(`ba_next`); natural numbers for the `long`s. -/
def sieve1Rows (p : Nat) (help0 help1 : UInt64) :
    Id (Vector UInt64 ((p + chunk - 1) * rbaPack)) := do
  let ldp := 64 / p
  let p1 := (ldp + 1) * p
  let diffShift := p1 % 64
  let diff := 64 - diffShift
  let mut help0 := help0
  let mut help1 := help1
  let mut si : Vector UInt64 ((p + chunk - 1) * rbaPack) := .replicate _ 0
  si := si.set! 0 help0
  for a in [1:p] do
    let temp := help0 >>> diff.toUInt64
    help0 := help1 ||| help0 <<< diffShift.toUInt64
    si := si.set! a help0
    help1 := temp
  return si

/-- The row of the residue `b` of the prime `p = t.p < 64` with the tables `t`, as the function that
the build generates for `p` from `CODE_INIT_SIEVE1` builds it, `p + chunk - 1` bit arrays, and the
store `store` with the row stored into the table of the entry `ref`
(`Ratpoints.Sieve.RowStore.publish`): the pattern of `p` bits in `help0`
(`Ratpoints.Sieve.sieve1Pattern`); `help1` the pattern shifted right by `64 mod p`; the pattern
repeated in `help0` by or-ing in `help0` shifted left by `i` for `i = p, 2 p, 4 p, …` below 64; the
first `p` words of the row rotated out of `help0` and `help1` (`Ratpoints.Sieve.sieve1Rows`); then
the copies (`Ratpoints.Sieve.initReplicate`).

C: `init.c:118-130`, `init.c:144-159`, `init.c:178-183`

Deviation: one function for every prime below 64, the prime that of its tables, for the function
that the build generates for each prime with the prime a constant (`init_sieve.h`); the tables of
the prime and the reference to its entry (`Ratpoints.Sieve.EntryRef`) as arguments, for the sieve
entry `se` from which the C code reads them and into which it stores the row, and the store of the
tables of the rows of the run passed and returned, for the arrays `sieve` of the entries; the row
stored plainly, for the release store of `RP_PUBLISH` in a build with threads (stage I); no copy
`pattern` of `help0`, which the C code shifts for `help1`. -/
def sieveInit1 (t : Entry) (ref : EntryRef) (b : Nat) (store : RowStore) :
    Id (Vector UInt64 ((t.p + chunk - 1) * rbaPack) × RowStore) := do
  let lmp := 64 % t.p
  let mut help0 ← sieve1Pattern t b
  let help1 := help0 >>> lmp.toUInt64
  let mut i := t.p
  while i < 64 do
    help0 := help0 ||| help0 <<< i.toUInt64
    i := i <<< 1
  let si ← sieve1Rows t.p help0 help1
  let si ← initReplicate t.p si
  return (si, store.publish ref b si.toArray)

/-- Word `n ≤ ⌊p / 64⌋` of the pattern of the row of the prime `p = t.p > 64` in `CODE_INIT_SIEVE2`:
the bits `i` below `m`, `64` for `n < ⌊p / 64⌋` and `p mod 64` for the last word, four at a time
from the four lanes (`Ratpoints.Sieve.initFourLoop`) and the bits left over one at a time from the
first lane (`Ratpoints.Sieve.initBit`), its residue stepped by `d` modulo `p`; the word and the
residues of the lanes, which go on to the next word.

C: `init.c:209-216`

Deviation: the residues of the lanes passed and returned, for the variables of the function; the
steps `ab += d; if (ab >= p) ab -= p;` as conditional values; the results of the loop of four bits
read as the components of its tuple; natural numbers for the `long`s. -/
def sieve2Word (t : Entry) (d d4 n ab ab1 ab2 ab3 : Nat) :
    Id (UInt64 × Nat × Nat × Nat × Nat) := do
  let m := if n < t.p / 64 then 64 else t.p % 64
  let r ← initFourLoop t.isFSquare t.p d4 0 0 m ab ab1 ab2 ab3
  let mut work := r.1
  let mut ab := r.2.2.1
  for i in [r.2.1:m] do
    work := initBit work t.isFSquare[ab]! i
    ab := if ab + d ≥ t.p then ab + d - t.p else ab + d
  return (work, ab, r.2.2.2.1, r.2.2.2.2.1, r.2.2.2.2.2)

/-- The pattern of the row of the residue `b` of the prime `p = t.p > 64` in `CODE_INIT_SIEVE2`, in
the words `help[0], …, help[⌊p / 64⌋]`: word `n` the bits `64 n, …` of the pattern, bit `a < p` the
entry of the table of `t` at `a d mod p` for the inverse `d` of `b` modulo `p`, each word from
`Ratpoints.Sieve.sieve2Word`, the four lanes (`Ratpoints.Sieve.initFourDecl`) going on from word to
word.

C: `init.c:204-208`, `init.c:217-219`

Deviation: the words `help` passed and returned, for the array of the function; `⌊p / 64⌋` computed
where it is used, for the variable `wp`; natural numbers for the `long`s. -/
def sieve2Pattern (t : Entry) (b : Nat) (help : Vector UInt64 (t.p / 64 + 2)) :
    Id (Vector UInt64 (t.p / 64 + 2)) := do
  let d := t.inverses[b]!
  let lanes := initFourDecl t.p d
  let mut help := help
  let mut ab := 0
  let mut ab1 := lanes.1
  let mut ab2 := lanes.2.1
  let mut ab3 := lanes.2.2.1
  for n in [0:t.p / 64 + 1] do
    let r ← sieve2Word t d lanes.2.2.2 n ab ab1 ab2 ab3
    ab := r.2.1
    ab1 := r.2.2.1
    ab2 := r.2.2.2.1
    ab3 := r.2.2.2.2
    help := help.set! n r.1
  return help

/-- The first `p` words of the row of a prime `p > 64` in `CODE_INIT_SIEVE2`, from the words
`help[0], …, help[wp]` of its pattern, `wp = ⌊p / 64⌋`, `p = 64 wp + ds` with `0 < ds < 64`: words
`a < wp` the words of the pattern; then for `a = wp, …, p - 1`, with the cursor `a1` from `wp` on
and the next position `t` after it in the ring of the `wp + 1` words: `help[a1] |= help[t] << ds`,
word `a` of the row `help[a1]`, the cursor moved on to `t` and `help[t] >>= 64 - ds`.

C: `init.c:220-238`

Deviation: the words `help` passed, for the array of the function; `wp`, `diff_shift` and `diff`
computed where they are used, for the variables of the function; a fresh vector of
`(p + chunk - 1) rbaPack` words, for the space that the builder takes from the buffer of the tables
(`ba_next`); the shift by `LONG_SHIFT` and the mask by `LONG_MASK` as the division and the
remainder by 64. -/
def sieve2Rows (p : Nat) (help : Vector UInt64 (p / 64 + 2)) :
    Id (Vector UInt64 ((p + chunk - 1) * rbaPack)) := do
  let wp := p / 64
  let diffShift := p % 64
  let diff := 64 - diffShift
  let mut help := help
  let mut si : Vector UInt64 ((p + chunk - 1) * rbaPack) := .replicate _ 0
  for a in [0:wp] do
    si := si.set! a help[a]!
  let mut a1 := wp
  for a in [wp:p] do
    let t := if a1 = wp then 0 else a1 + 1
    help := help.set! a1 (help[a1]! ||| help[t]! <<< diffShift.toUInt64)
    si := si.set! a help[a1]!
    a1 := t
    help := help.set! a1 (help[a1]! >>> diff.toUInt64)
  return si

/-- The row of the residue `b` of the prime `p = t.p > 64` with the tables `t`, as the function that
the build generates for `p` from `CODE_INIT_SIEVE2` builds it, `p + chunk - 1` bit arrays, and the
store `store` with the row stored into the table of the entry `ref`
(`Ratpoints.Sieve.RowStore.publish`): the `⌊p / 64⌋ + 2` words `help` cleared from the last, the
pattern of the row in them (`Ratpoints.Sieve.sieve2Pattern`), the first `p` words of the row rotated
out of them (`Ratpoints.Sieve.sieve2Rows`), and the copies (`Ratpoints.Sieve.initReplicate`).

C: `init.c:186-203`, `init.c:239-244`

Deviation: one function for every prime above 64, the prime that of its tables, for the function
that the build generates for each prime with the prime a constant (`init_sieve.h`); the tables of
the prime and the reference to its entry (`Ratpoints.Sieve.EntryRef`) as arguments, for the sieve
entry `se` from which the C code reads them and into which it stores the row, and the store of the
tables of the rows of the run passed and returned, for the arrays `sieve` of the entries; the words
`help` a fresh vector, which the loop clears from the last, for the array whose words the function
leaves unset until it clears them; the row stored plainly, for the release store of `RP_PUBLISH` in
a build with threads (stage I). -/
def sieveInit2 (t : Entry) (ref : EntryRef) (b : Nat) (store : RowStore) :
    Id (Vector UInt64 ((t.p + chunk - 1) * rbaPack) × RowStore) := do
  let mut help : Vector UInt64 (t.p / 64 + 2) := .replicate _ 0
  for k in [0:t.p / 64 + 2] do
    help := help.set! (t.p / 64 + 1 - k) 0
  help ← sieve2Pattern t b help
  let si ← sieve2Rows t.p help
  let si ← initReplicate t.p si
  return (si, store.publish ref b si.toArray)

/-! ### The rows of a prime power -/

/-- The 64 bits of the packed words `E` from position `s` on, where bit `t` of word `q` is at
position `64 q + t`: word `s / 64` shifted right by `r = s % 64`, and for `r ≠ 0` the lowest `r`
bits of the next word above them, as `lay_out_pattern` cuts each word of a row out of the repeated
pattern at line 291 of `init.c` (`Ratpoints.Sieve.layOutPattern`). -/
def window (E : Array UInt64) (s : Nat) : UInt64 :=
  let q := s / 64
  let r := s % 64
  if r = 0 then E[q]! else E[q]! >>> r.toUInt64 ||| E[q + 1]! <<< (64 - r).toUInt64

/-- The words `rep` of `lay_out_pattern`: its first `words` words cleared, and the pattern `pat` of
period `m` or-ed in at the bit offsets `o = 0, m, 2 m, …` below `64 words`, at each offset the
`⌈m / 64⌉` words of the pattern, shifted left by `o mod 64` into the words from `⌊o / 64⌋` on and,
for a nonzero shift, right by `64 - o mod 64` into the next words, those beyond the first `words`
words cut. For a pattern without bits from `m` on, bit `N < 64 words` of the result is bit
`N mod m` of the pattern.

C: `init.c:268-279`

Deviation: the words `rep` passed and returned, for the array of `lay_out_pattern`; the two loops
as `while` loops, for the `for` loops that step `o` by `m` and test `i` against two bounds; the
or-ing into the next word as a conditional value; the shifts by `LONG_SHIFT` and the masks by
`LONG_MASK` as divisions and remainders by 64. -/
def repeatPattern (pat : Array UInt64) (m words : Nat) (rep : Vector UInt64 (modWords + 2)) :
    Id (Vector UInt64 (modWords + 2)) := do
  let mut rep := rep
  for i in [0:words] do
    rep := rep.set! i 0
  let mut o := 0
  while o < words * 64 do
    let q := o / 64
    let s := o % 64
    let pw := (m + 64 - 1) / 64
    let mut i := 0
    while i < pw ∧ q + i < words do
      rep := rep.set! (q + i) (rep[q + i]! ||| pat[i]! <<< s.toUInt64)
      rep := if s ≠ 0 ∧ q + i + 1 < words then
          rep.set! (q + i + 1) (rep[q + i + 1]! ||| pat[i]! >>> (64 - s).toUInt64)
        else rep
      i := i + 1
    o := o + m
  return rep

/-- The row of the pattern `pat` of period `m`, as `lay_out_pattern` lays it out, `m + chunk - 1`
bit arrays: the pattern repeated through `words = ⌊(m + 127) / 64⌋` words, `64 words ≥ m + 64`
(`Ratpoints.Sieve.repeatPattern`); for `x < m rbaPack`, word `x` of the row the 64 bits of the
repeated pattern from the offset `o = 64 x mod m` on (`Ratpoints.Sieve.window`), the offset stepped
by `64 mod m` modulo `m`; then the copies of the first `(chunk - 1) rbaPack` words after the first
`m rbaPack`. For `0 < m ≤ 64 Ratpoints.modWords` and a pattern without bits from `m` on, bit `t` of
word `j` of the row is bit `(64 j + t) mod m` of the pattern.

C: `init.c:259-267`, `init.c:280-297`

Deviation: the words `rep` a fresh vector of `RP_MODWORDS + 2` zeros, for the array whose first
`words` words `lay_out_pattern` clears and whose other words it leaves unset and never reads; a
fresh vector of `(m + chunk - 1) rbaPack` words for the row, for the space that it takes from the
buffer of the tables (`ba_next`); the step of the offset as a conditional value; the shifts by
`LONG_SHIFT` and the masks by `LONG_MASK` as divisions and remainders by 64. -/
def layOutPattern (pat : Array UInt64) (m : Nat) :
    Id (Vector UInt64 ((m + chunk - 1) * rbaPack)) := do
  let rep : Vector UInt64 (modWords + 2) := .replicate _ 0
  let mut si : Vector UInt64 ((m + chunk - 1) * rbaPack) := .replicate _ 0
  let words := (m + 64 + 64 - 1) / 64
  let rep ← repeatPattern pat m words rep
  let step := 64 % m
  let mut o := 0
  for x in [0:m * rbaPack] do
    si := si.set! x (window rep.toArray o)
    o := if o + step ≥ m then o + step - m else o + step
  for i in [0:(chunk - 1) * rbaPack] do
    si := si.set! (m * rbaPack + i) si[i]!
  return si

/-- The pattern of the row of a unit `b` modulo the prime power `m` with the tables `pw`, in
`_ratpoints_sieve_init_power`: for `x < m`, bit `x` of `pat` set (`Ratpoints.Sieve.setBitAt`) when
bit `r` of `fsq` is (`Ratpoints.Sieve.bitAt`), for the residue `r = x b⁻¹ mod m`, stepped by the
inverse of `b` modulo `m` from the table of inverses.

C: `init.c:369-375`

Deviation: the pattern passed and returned, for the array of the function; the step
`r += binv; if (r >= m) r -= m;` as a conditional value; natural numbers for the `long`s. -/
def powerPatternUnit (pw : Power) (b : Nat) (pat : Array UInt64) : Id (Array UInt64) := do
  let binv := pw.inv[b]!
  let mut pat := pat
  let mut r := 0
  for x in [0:pw.m] do
    if bitAt pw.fsq r then pat := setBitAt pat x
    r := if r + binv ≥ pw.m then r + binv - pw.m else r + binv
  return pat

/-- The pattern of the row of a residue `b` divisible by `p` modulo the prime power `m = p ^ e` with
the tables `pw`, in `_ratpoints_sieve_init_power`: for the units `x` below `m`, bit `x` of `pat` set
(`Ratpoints.Sieve.setBitAt`) when bit `b x⁻¹ mod m` of `gsq` is (`Ratpoints.Sieve.bitAt`), with the
inverse of `x` modulo `m` from the table of inverses.

C: `init.c:378-385`

Deviation: the pattern passed and returned, for the array of the function; natural numbers for the
`long`s and `unsigned long`s, the product `b inv[x]` below `m ^ 2`. -/
def powerPatternNonunit (pw : Power) (b : Nat) (pat : Array UInt64) : Id (Array UInt64) := do
  let mut pat := pat
  for x in [1:pw.m] do
    if x % pw.p = 0 then continue
    let t := b * pw.inv[x]! % pw.m
    if bitAt pw.gsq t then pat := setBitAt pat x
  return pat

/-- The row of the residue `b` of the prime power `m = p ^ e` with the tables `pw`, as
`_ratpoints_sieve_init_power` builds it, and the store `store` with the row stored into the table of
rows of the entry `ref` (`Ratpoints.Sieve.RowStore.publish`): the pattern `pat` of
`Ratpoints.modWords` words cleared; for a unit `b`, bit `x` set when `f(x b⁻¹)` is a square modulo
`m` (`Ratpoints.Sieve.powerPatternUnit`), and for `p ∣ b`, bit `x` of a unit `x` set when
`frev(b x⁻¹)` is a square modulo `m` (`Ratpoints.Sieve.powerPatternNonunit`); then the pattern laid
out as a row of `m + chunk - 1` bit arrays (`Ratpoints.Sieve.layOutPattern`).

C: `init.c:359-368`, `init.c:376-377`, `init.c:386-387`, `init.c:391-393`, `rp-private.h:592`

Deviation: the tables of the prime power and the reference to its entry
(`Ratpoints.Sieve.EntryRef`) as arguments, for the sieve entry `se` whose field `pw` points to the
tables and into which the C code stores the row, and the store of the tables of rows of the run
passed and returned, for the arrays `sieve` of the entries; the pattern a fresh array, which the
loop clears, for the array whose words the function leaves unset until it clears them; the row
stored plainly, for the release store of `RP_PUBLISH` in a build with threads (stage I). -/
def sieveInitPower (pw : Power) (ref : EntryRef) (b : Nat) (store : RowStore) :
    Id (Vector UInt64 ((pw.m + chunk - 1) * rbaPack) × RowStore) := do
  let mut pat : Array UInt64 := .replicate modWords 0
  for x in [0:modWords] do
    pat := pat.set! x 0
  if b % pw.p ≠ 0 then
    pat ← powerPatternUnit pw b pat
  else
    pat ← powerPatternNonunit pw b pat
  let row ← layOutPattern pat pw.m
  return (row, store.publish ref b row.toArray)

/-! ### The rows of a product -/

/-- The row of the residue `b` built by the builder of the kind `init` on the tables of the factor
`f`, whose entry is `ref`, and the store with the row that the builder stores into the table of rows
of that entry: the call `(*(se->init))(se, b, args)` for the entry of a prime or a prime power, the
function that the build generates for a prime below 64 (`Ratpoints.Sieve.sieveInit1`) or above 64
(`Ratpoints.Sieve.sieveInit2`), and the builder of the rows of a prime power
(`Ratpoints.Sieve.sieveInitPower`). A kind that does not fit the factor, which the entries of the
model never have (`Ratpoints.Sieve.SieveEntry.refInit`, `Ratpoints.makeModulus?`), gives the empty
row and the store as it is. The row of `0` of a prime is never built: it is in the table of rows of
the prime from the start, the pattern `sieves0` that `examine_prime` installs
(`Ratpoints.Sieve.sieves0`). -/
def initFactorRow (init : RowInit) (ref : EntryRef) (f : Factor) (b : Nat) (store : RowStore) :
    Id (Array UInt64 × RowStore) := do
  match init, f with
  | .sieve1, .prime t =>
    let (row, store) ← sieveInit1 t ref b store
    return (row.toArray, store)
  | .sieve2, .prime t =>
    let (row, store) ← sieveInit2 t ref b store
    return (row.toArray, store)
  | .power, .power pw =>
    let (row, store) ← sieveInitPower pw ref b store
    return (row.toArray, store)
  | _, _ => return (#[], store)

/-- The rows of the factors of the product `e` for the residue `b` modulo their moduli, as
`_ratpoints_sieve_init_product` takes them, and the store: for each factor `f` with the modulus `q`,
the row of `b mod q` in the table of rows of its entry (`Ratpoints.Sieve.RowStore.row?`), and when
it is absent the row that the builder of the entry of the factor builds and stores into that table
(`Ratpoints.Sieve.initFactorRow` with `Ratpoints.Sieve.Factor.init` and
`Ratpoints.Sieve.Factor.ref`).

C: `init.c:407-414`

Deviation: the rows of the factors an array returned with the store, for the array `frow` of the
function and the tables of rows in the entries of the factors; the row read plainly, for the acquire
load `RP_ACQUIRE` of a build with threads (stage I); the number of the factors the length of their
list, for the count `nf`. -/
def factorRows (e : SieveEntry) (b : Nat) (store : RowStore) :
    Id (Array (Array UInt64) × RowStore) := do
  let mut store := store
  let mut frows := #[]
  for f in e.factors do
    let bf := b % f.modulus
    match store.row? f.ref bf with
    | some fr => frows := frows.push fr
    | none =>
      let (fr, s) ← initFactorRow f.init f.ref f bf store
      store := s
      frows := frows.push fr
  return (frows, store)

/-- The row of a product `m` laid down from the row `frows[0]` of its first factor, of the modulus
`q`, in `_ratpoints_sieve_init_product`: for `x = 0, q, 2 q, …` below `m` and `j < q`, bit array
`x + j` of `row` set to bit array `j` of the row of the factor (`Ratpoints.Sieve.storeBitArray`).

C: `init.c:419-423`

Deviation: the row passed and returned, for the pointer of the function; the loop over `x` as a
`while` loop, for the `for` loop that steps `x` by `q`; the row of the factor as the vector of its
words, which the store of a bit array reads. -/
def productCopy {n : Nat} (row : Vector UInt64 n) (e : SieveEntry) (frows : Array (Array UInt64)) :
    Id (Vector UInt64 n) := do
  let mut row := row
  let q := e.factors[0]!.modulus
  let mut x := 0
  while x < e.p do
    for j in [0:q] do
      row := storeBitArray row (x + j) frows[0]!.toVector j
    x := x + q
  return row

/-- The rows `frows[i]` of the other factors of the product `m = e.p`, each of the modulus `q` of
its factor, and-ed into the row, in `_ratpoints_sieve_init_product`: for each factor `i ≥ 1`, for
`x = 0, q, 2 q, …` below `m` and `j < q`, bit array `x + j` of `row` and-ed with bit array `j` of
the row of the factor (`Ratpoints.Sieve.andBitArray`).

C: `init.c:424-429`

Deviation: the row passed and returned, for the pointer of the function; the loop over `x` as a
`while` loop, for the `for` loop that steps `x` by `q`; the number of the factors the length of
their list, for the count `nf`. -/
def productAnd {n : Nat} (row : Vector UInt64 n) (e : SieveEntry) (frows : Array (Array UInt64)) :
    Id (Vector UInt64 n) := do
  let mut row := row
  for i in [1:e.factors.length] do
    let q := e.factors[i]!.modulus
    let mut x := 0
    while x < e.p do
      for j in [0:q] do
        row := andBitArray row (x + j) frows[i]! j
      x := x + q
  return row

/-- The row of the residue `b` of the product `m = e.p` of the sieve entry `e`, as
`_ratpoints_sieve_init_product` builds it, `m + chunk - 1` bit arrays, and the store `store` with
the rows of the factors that it builds and with the row stored into the table of rows of the entry
(`Ratpoints.Sieve.RowStore.publish`): the rows of the factors for `b` modulo their moduli, from the
tables of rows of their entries or built into them (`Ratpoints.Sieve.factorRows`); the row of the
first factor laid down in blocks of its length (`Ratpoints.Sieve.productCopy`), the rows of the
others and-ed in, in blocks of theirs (`Ratpoints.Sieve.productAnd`), and the copies of the first
`chunk - 1` bit arrays after the first `m` (`Ratpoints.Sieve.storeBitArray`). Since the moduli of
the factors divide `m`, bit array `y < m + chunk - 1` of the row is the and of the bit arrays
`y mod q` of the rows of the factors.

C: `init.c:399-406`, `init.c:415-418`, `init.c:430`, `init.c:443-445`, `rp-private.h:593`

Deviation: the store of the tables of rows passed and returned, for the entries of the factors
that the C code reaches through the pointers `factor` and for the entry `se` into which it stores
the row; a fresh vector of `(m + chunk - 1) rbaPack` words, for the space that the builder takes
from the buffer of the tables (`ba_next`) after the rows of the factors; the row stored plainly, for
the release store of `RP_PUBLISH` in a build with threads (stage I); the number of the factors the
length of their list, for the count `nf`. -/
def sieveInitProduct (e : SieveEntry) (b : Nat) (store : RowStore) :
    Id (Vector UInt64 ((e.p + chunk - 1) * rbaPack) × RowStore) := do
  let (frows, store) ← factorRows e b store
  let mut row : Vector UInt64 ((e.p + chunk - 1) * rbaPack) := .replicate _ 0
  row ← productCopy row e frows
  row ← productAnd row e frows
  for j in [0:chunk - 1] do
    row := storeBitArray row (e.p + j) row j
  return (row, store.publish e.ref b row.toArray)

/-! ### The rows of the entries of a run -/

/-- The row of the residue `b < e.p` of the sieve entry `e` built by its builder, the call
`(*(se->init))(se, b, args)` of the run, and the store with the row that the builder stores into the
table of rows of the entry: for a product the builder of the rows of a product
(`Ratpoints.Sieve.sieveInitProduct`), which builds the rows of its factors that are absent into
their tables of rows first, and for a prime or a prime power the builder of its kind on the tables
of its one factor, with the reference to the entry (`Ratpoints.Sieve.initFactorRow`). -/
def SieveEntry.initRow (e : SieveEntry) (b : Nat) (store : RowStore) :
    Id (Array UInt64 × RowStore) := do
  if e.init = .product then
    let (row, store) ← sieveInitProduct e b store
    return (row.toArray, store)
  initFactorRow e.init e.ref e.factors[0]! b store

/-- The row of the residue `b < e.p` of the sieve entry `e` and the store: the row in the table of
rows of its entry (`Ratpoints.Sieve.RowStore.row?`) when it is there, and otherwise the row that its
builder builds into that table of rows (`Ratpoints.Sieve.SieveEntry.initRow`). This is the body of
the loop of `sift` that builds the rows that are missing, which reads the pointer to the row again
before it calls the builder (`Ratpoints.Sieve.buildRows`). -/
def SieveEntry.fetchRow (e : SieveEntry) (b : Nat) (store : RowStore) :
    Id (Array UInt64 × RowStore) :=
  match store.row? e.ref b with
  | some row => pure (row, store)
  | none => e.initRow b store

/-! ### Examples -/

-- The words of a forbidden divisor: bit `j` of word `r` is clear exactly when `p ∣ 64 r + j`,
-- for primes of the table of the build and beyond it.
#guard [3, 5, 7, 251, 257, 1021].all fun p ↦
  let row := forbiddenRow p
  row.size == p && (List.range p).all fun r ↦ (List.range 64).all fun j ↦
    row[r]!.toBitVec.getLsbD j == ((64 * r + j) % p != 0)

-- The row of `0` against the pattern `sieves0` that the build of ratpoints generates, for 3, 5, 7,
-- 11 and 13: the first `p` of its words, which the others repeat.
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
    (sieves0 p).extract 0 p == ws

-- The pattern `sieves0` over all its `(p + chunk - 1) rbaPack` words: word `x` is word `x mod p` of
-- the words of the forbidden divisor `p`, for every prime of the table of the build.
#guard (primeTable.toList.take numPrimes).all fun p ↦
  (sieves0 p).size == (p + chunk - 1) * rbaPack &&
    (List.range ((p + chunk - 1) * rbaPack)).all fun x ↦ (sieves0 p)[x]! == (forbiddenRow p)[x % p]!

end Sieve

end Ratpoints

end
