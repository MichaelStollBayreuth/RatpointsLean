/-
Copyright (c) 2026 Michael Stoll. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michael Stoll
-/
module

public import Ratpoints.Model.Constants
public import Ratpoints.Model.Tables

-- The `#guard` examples run code of the imported modules at compile time.
meta import Ratpoints.Model.Constants
meta import Ratpoints.Model.Tables

/-!
# The first stage of the sieve

The first stage of the sieve over a piece of bit arrays, the part of `_ratpoints_sift0` of the C
code before the masks and the scan: every bit array of the piece the pattern of the class of the
denominator in its packing, and-ed with the rows of the moduli of the stage, each read at the word
number plus its offset. The C code has two arms, which the preprocessor chooses by the chunk
`RATPOINTS_CHUNK` (`Ratpoints.chunk`), and the model has both, chosen on the same condition by
`Ratpoints.Sieve.siftPiece`: for a chunk from 2 to 16, the chunked arm
(`Ratpoints.Sieve.andRowsChunked`), which walks each row with a start that it steps on by the chunk
and back by the modulus, takes `chunk` bit arrays at a time in registers
(`Ratpoints.Sieve.andChunks`, `Ratpoints.Sieve.chunkSieve`) and the tail of fewer than `chunk` bit
arrays in legs of 8, 4, 2 and 1 (`Ratpoints.Sieve.tailLegs`, `Ratpoints.Sieve.tailLeg`), reading up
to `chunk - 1` bit arrays past the first `p` bit arrays of a row of the modulus `p`, which are
copies of its first ones; for the other chunks, the arm that and-s each row into the bit arrays of
the piece in three loops (`Ratpoints.Sieve.andRows`). Both leave the same bit arrays. Here are also
the operations on bit arrays of 64-bit words that the first stage uses, the bit arrays given by
their indices in arrays of words, and the sieve specs, a modulus with its row and its offset for the
denominator at hand and the start and the end of the walk of the chunked arm through the row
(`Ratpoints.Sieve.SieveSpec`).

## Main definitions

* `Ratpoints.Sieve.andBitArray`, `Ratpoints.Sieve.loadBitArray`, `Ratpoints.Sieve.storeBitArray`,
  `Ratpoints.Sieve.fillBitArray`: the operations on bit arrays of the first stage, a bit array
  and-ed with one of a row, set to the class word and-ed with one of a row, set to one of the
  registers, and set to the class word.
* `Ratpoints.Sieve.SieveSpec`: a modulus with its row, its offset and the start and the end of the
  walk of the chunked first stage through the row.
* `Ratpoints.Sieve.andRows`: the first stage over a piece, one row at a time, the arm of the builds
  with a chunk of 1 or above 16.
* `Ratpoints.Sieve.chunkStarts`, `Ratpoints.Sieve.wrapStart`: the starts of the rows at the first
  word number of a piece, and a start stepped back by the modulus.
* `Ratpoints.Sieve.chunkSieve`, `Ratpoints.Sieve.andChunks`: one chunk of `Ratpoints.chunk` bit
  arrays in registers through the first stage, and the whole chunks of a piece.
* `Ratpoints.Sieve.tailLeg`, `Ratpoints.Sieve.tailLegs`: one leg over the tail of a piece, and the
  tail in legs of 8, 4, 2 and 1 bit arrays.
* `Ratpoints.Sieve.andRowsChunked`: the first stage over a piece, `Ratpoints.chunk` bit arrays at a
  time, the arm of the builds with a chunk from 2 to 16.
-/

@[expose] public section

namespace Ratpoints

namespace Sieve

/-! ### Bit arrays -/

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

/-- Bit array `j` of the words `v` set to the class word `cw` and-ed with bit array `x` of the row
`row`, one word at a time: for `κ < rbaPack`, word `rbaPack * j + κ` of `v` set to `cw` and-ed with
word `rbaPack * x + κ` of `row`; the load `reg = bits64 & *siv` of a register of the chunked first
stage, with the class word in each word of the bit array `bits64`. -/
def loadBitArray {m : Nat} (v : Vector UInt64 m) (j : Nat) (cw : UInt64) (row : Array UInt64)
    (x : Nat) : Vector UInt64 m :=
  Nat.fold rbaPack (fun κ _ v ↦ v.set! (rbaPack * j + κ) (cw &&& row[rbaPack * x + κ]!)) v

/-- Bit array `y` of the words `v` set to bit array `j` of the words `regs`, one word at a time: for
`κ < rbaPack`, word `rbaPack * y + κ` of `v` set to word `rbaPack * j + κ` of `regs`; the store
`surv[y] = reg` of a register of the chunked first stage into the survivors. -/
def storeBitArray {m k : Nat} (v : Vector UInt64 m) (y : Nat) (regs : Vector UInt64 k) (j : Nat) :
    Vector UInt64 m :=
  Nat.fold rbaPack (fun κ _ v ↦ v.set! (rbaPack * y + κ) regs[rbaPack * j + κ]!) v

/-- Bit array `y` of the words `v` set to the class word `cw` in each of its words: the store
`survivors[y] = bits64` of the first stage, with the class word in each word of the bit array
`bits64`. -/
def fillBitArray {m : Nat} (v : Vector UInt64 m) (y : Nat) (cw : UInt64) : Vector UInt64 m :=
  Nat.fold rbaPack (fun κ _ v ↦ v.set! (rbaPack * y + κ) cw) v

/-! ### The sieve specs -/

/-- A modulus with its row for the denominator at hand, the offset of the row, and the start and
the end of the walk of the chunked first stage through the row. The row has `p + chunk - 1` bit
arrays of `Ratpoints.rbaPack` words, for the chunk `Ratpoints.chunk`: `p` bit arrays and copies of
the first `chunk - 1` of them, so that bit array `x` of the row is bit array `x mod p` for
`x < p + chunk - 1`. The bit array with the word number `w` reads bit array `(w + offset) mod p` of
the row. The offset is the shift of the row that the packing of the class of the denominator needs,
`a₀ (2 ^ k Ratpoints.rbaLength)⁻¹ mod p` for the stride `2 ^ k` and the residue `a₀` of the class,
plus the bias of the modulus, the least multiple of `p` of at least `Ratpoints.rowBias`, which keeps
`w + offset` non-negative (`Ratpoints.Sieve.classOffsets`); with the row of the denominator divided
by the stride modulo `p` (`Ratpoints.Sieve.fillBpList`), bit `t` of that bit array says whether the
row of the denominator admits the numerator `a₀ + 2 ^ k (Ratpoints.rbaLength w + t)`. The chunked
first stage (`Ratpoints.Sieve.andRowsChunked`) reads the row from the bit array `start` on, which it
sets at the first word number of a piece and steps on by the chunk and back by `p` while it is at
least the end `stop`, which is `p` (`Ratpoints.Sieve.setRows`); the other stages read neither.

C: `rp-private.h:378-379`

Deviation: the row for the pointer `ptr` to it, and indices into the row for the pointers `start`
and `end` into it, the end named `stop` (`end` is a keyword of Lean); natural numbers for the
`long`s `p` and `offset`, the offset below `2 ^ 32`
(`Ratpoints.Sieve.SieveEntry.PackedFor.lt_two_pow_32`). -/
structure SieveSpec where
  /-- The modulus. -/
  p : Nat
  /-- The offset of the row: the bit array with the word number `w` reads bit array
  `(w + offset) mod p` of the row. -/
  offset : Nat
  /-- The row: `p + Ratpoints.chunk - 1` bit arrays of `Ratpoints.rbaPack` words, the last
  `chunk - 1` of them copies of the first ones. -/
  row : Array UInt64
  /-- The bit array of the row from which the chunked first stage reads next. -/
  start : Nat
  /-- The end of the first `p` bit arrays of the row: the chunked first stage steps its start back
  by `p` while it is at least this. -/
  stop : Nat
  deriving Inhabited

/-! ### The first stage, one row at a time -/

/-- The first stage over a piece, the bit arrays with the word numbers `w0, …, w0 + n - 1`, which
are the first `n` bit arrays of `surv`, one row at a time, the arm of `_ratpoints_sift0` for a chunk
`Ratpoints.chunk` of 1 or above 16 (for the others, `Ratpoints.Sieve.andRowsChunked`): the bit
arrays are set to the class word `cw` (`Ratpoints.Sieve.fillBitArray`), from the last, the pattern
of the class of the denominator in its packing (`Ratpoints.Sieve.NumClass`; bit `t` of every word
stands for a numerator `a₀ + 2 ^ k t'` with `t' ≡ t (mod 64)`, since `64` divides
`Ratpoints.rbaLength`); then for each modulus `p` of `specs` with its row and its offset, and its
reciprocal `mg` from `mgs`, and for `r = (-w0 - offset) mod p`, the remainder by a multiplication
with `mg` (`Ratpoints.Sieve.modMul`) when `small` says that the word numbers of the piece allow it
and by the helper `mod` of the C code otherwise (`Ratpoints.Sieve.modLong`), bit array `j` is and-ed
with bit array `(w0 + offset + j) mod p` of the row (`Ratpoints.Sieve.andBitArray`), in three loops:
if `n < r`, with the `n` bit arrays of the row from `p - r` on, and otherwise with the `r` bit
arrays from `p - r` on, then with whole periods of `p` bit arrays from `0`, then with the rest from
`0`. It reads only the first `p` bit arrays of a row. The last bit array of `surv`, the place of the
sentinel, is left as it is.

C: `sift.c:943-1022`, `find_points.c:1098`, `rp-private.h:129-132`, `rp-private.h:203-204`,
`rp-private.h:235`, `rp-private.h:261`, `rp-private.h:285`

Deviation: the bit arrays set to the class word by a loop that counts up, bit array `n - 1 - i` at
the step `i`, for the loop that counts down from the last; the class word written into each word of
a bit array, for the vector `RBA(packed)` that `get_2adic_info` makes once per class
(`find_points.c:1098`) and `_ratpoints_sift0` copies into each bit array (`bits64`, `sift.c:519`,
`sift.c:954`); the moduli of the stage with their rows and their reciprocals as two lists, for the
first `sp1` sieve specs and the array `magics` from position `0` on; the value `-w_low - offset`
written out in both reductions, for the `long` `a`, which stays a `long` where the helper `mod`
reduces it outside `small` (`Ratpoints.Sieve.fitsLong_neg_sub_and_fitsLong_add`); indices for the
pointers into the rows and into the survivors, and the number of whole periods and the rest
computed before their loops; natural numbers and integers for the `long`s; a Boolean for the `int`
`small`; no output under `DEBUG`. -/
def andRows (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (cw : UInt64) (w0 : Int)
    (n : Nat) (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    Id (Vector UInt64 ((n + 1) * rbaPack)) := do
  let mut surv := surv
  for i in [0:n] do
    surv := fillBitArray surv (n - 1 - i) cw
  for s in specs, mg in mgs do
    let p := s.p
    let r := (if small then modMul (-w0 - s.offset) p mg else modLong (-w0 - s.offset) p).toNat
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

/-! ### The first stage, a chunk at a time -/

/-- The sieve specs `specs` of the first stage with their starts for the piece from the word number
`w0` on, a local array of them: for each modulus `p` with its offset, and its reciprocal `mg` from
`mgs`, the start `(w0 + offset) mod p`, the remainder by a multiplication with `mg`
(`Ratpoints.Sieve.modMul`) when `small` says that the word numbers of the piece allow it, and by the
helper `mod` of the C code otherwise (`Ratpoints.Sieve.modLong`): the bit array of the row that the
bit array with the word number `w0` reads.

C: `sift.c:596-606`

Deviation: a local array of the sieve specs, in which the starts are set, for the sieve specs
`sieves` of the sieving thread, whose field `start` the C code writes and nothing reads after the
first stage; the moduli of the stage with their rows and their reciprocals as two lists, for the
first `sp1` sieve specs and the array `magics` from position `0` on; the reduction by the
reciprocal under `small` alone, for `small && RP_USE_MOD_MUL`, with `RP_USE_MOD_MUL` the constant 1
of the production build (`sift.c:236-238`, excluded with the switch of the development builds); the
start an index into the row, for the pointer `ptr` plus the remainder; integers for the `long`s, the
sum `a = w_low + offset` staying a `long` where the helper `mod` reduces it outside `small`
(`Ratpoints.Sieve.fitsLong_neg_sub_and_fitsLong_add`); a Boolean for the `int` `small`. -/
def chunkStarts (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (w0 : Int) :
    Id (Array SieveSpec) := do
  let mut sv := #[]
  for s in specs, mg in mgs do
    let a := w0 + s.offset
    sv := sv.push { s with start := (if small then modMul a s.p mg else modLong a s.p).toNat }
  return sv

/-- The index `st` stepped back by the modulus `p` while it is at least the end `stop`,
`while (siv >= end) siv -= p`: for the end `stop = p` of a row (`Ratpoints.Sieve.setRows`) and
`p > 0`, `st mod p`, the start of the row moved back into its first `p` bit arrays after a chunk of
the first stage.

C: `sift.c:683`, `sift.c:805`

Deviation: one definition for the loop at its two places, after the first modulus of a chunk and
after each further one; indices into the row for the pointers. -/
def wrapStart (st stop p : Nat) : Id Nat := do
  let mut st := st
  while st ≥ stop do
    st := st - p
  return st

/-- One chunk of `Ratpoints.chunk` bit arrays through the first stage, from the starts of the rows
of the local sieve specs `sv` on: the registers, `chunk` bit arrays, loaded with the class word `cw`
and-ed with the bit arrays `start, …, start + chunk - 1` of the row of the first modulus
(`Ratpoints.Sieve.loadBitArray`), and its start moved on by `chunk` and stepped back
(`Ratpoints.Sieve.wrapStart`); then for each further modulus in turn, the registers and-ed with the
bit arrays from its start on (`Ratpoints.Sieve.andBitArray`), and its start moved on and stepped
back in the same way. A start below `p` reads up to bit array `p + chunk - 2` of the row, one of the
copies of its first bit arrays. Returns the registers and the sieve specs with the new starts.

C: `sift.c:625-681`, `sift.c:684-804`, `sift.c:806-863`

Deviation: the registers `reg0, …, reg15` a vector of `chunk` bit arrays, made of zeros and then
loaded, and the loads and the ands of the registers loops over its bit arrays, for the variables
that the build declares and the code that it unrolls under `#if (RATPOINTS_CHUNK >= k)`, for `k` up
to 16; the pointers `siv0` and `siv1` after the loads and the ands as the start plus `chunk`, for
the pointers that each load and each and steps on by one bit array; indices into the rows for the
pointers `start` and `end`; the local array of the sieve specs, for the sieve specs of the sieving
thread, and its size for the number `sp1` of the moduli of the stage; no output under `DEBUG`. -/
def chunkSieve (sv : Array SieveSpec) (cw : UInt64) :
    Id (Vector UInt64 (chunk * rbaPack) × Array SieveSpec) := do
  let mut sv := sv
  let mut regs : Vector UInt64 (chunk * rbaPack) := .replicate _ 0
  let s := sv[0]!
  for j in [0:chunk] do
    regs := loadBitArray regs j cw s.row (s.start + j)
  let st ← wrapStart (s.start + chunk) s.stop s.p
  sv := sv.set! 0 { s with start := st }
  for q in [1:sv.size] do
    let s := sv[q]!
    for j in [0:chunk] do
      regs := andBitArray regs j s.row (s.start + j)
    let st ← wrapStart (s.start + chunk) s.stop s.p
    sv := sv.set! q { s with start := st }
  return (regs, sv)

/-- The whole chunks of a piece through the first stage, the bit arrays below `full`, a multiple of
`Ratpoints.chunk`: for `c = 0, chunk, 2 chunk, …` below `full`, the chunk from the starts of the
rows of the local sieve specs `sv` on (`Ratpoints.Sieve.chunkSieve`), its registers stored into the
bit arrays `c, …, c + chunk - 1` of `surv` (`Ratpoints.Sieve.storeBitArray`), and the starts moved
on for the next one. Returns the bit arrays and the sieve specs with the starts after the last
chunk, from which the tail reads.

C: `sift.c:624`, `sift.c:864-913`

Deviation: the index `c` of the first bit array of the chunk in `surv`, from `0`, for the word
number `w_low_new`, from `w_low`, and the pointer `surv` into the survivors, which the loop steps on
together, and `full` the index of the end of the whole chunks, for the word number `w_high_full`;
the stores a loop over the registers, for the code that the build unrolls under
`#if (RATPOINTS_CHUNK >= k)`, for `k` up to 16; the local array of the sieve specs, for the sieve
specs of the sieving thread. -/
def andChunks (sv : Array SieveSpec) (cw : UInt64) (full : Nat) {m : Nat}
    (surv : Vector UInt64 m) : Id (Vector UInt64 m × Array SieveSpec) := do
  let mut sv := sv
  let mut surv := surv
  let mut c := 0
  while c < full do
    let (regs, sv') ← chunkSieve sv cw
    sv := sv'
    for j in [0:chunk] do
      surv := storeBitArray surv (c + j) regs j
    c := c + chunk
  return (surv, sv)

/-- One leg of the first stage over the tail of a piece, `tail_leg`: `w ≤ 8` registers, loaded with
the class word `cw` and-ed with the bit arrays `start + off, …, start + off + w - 1` of the row of
the first modulus of the local sieve specs `sv` (`Ratpoints.Sieve.loadBitArray`), and-ed with the
bit arrays from `start + off` on of the rows of the further moduli in turn
(`Ratpoints.Sieve.andBitArray`), and stored into the bit arrays `base + off, …, base + off + w - 1`
of `surv` (`Ratpoints.Sieve.storeBitArray`), where `base` is the first bit array of the tail; the
starts stay as they are. The legs of a tail together read fewer than `Ratpoints.chunk` bit arrays
from the starts on, which the copies of the first bit arrays at the end of the rows cover.

C: `sift.c:452-465`, `sift.c:473-496`

Deviation: the registers a vector of 8 bit arrays, made of zeros, for the array `reg[8]`; the
pointer `surv` as the array `surv` and the index `base` of the first bit array of the tail, past
the whole chunks; indices into the rows for the pointers; the size of the local array of the sieve
specs for the number `sp1` of the moduli; no pragmas that make the compiler unroll the loops over
the registers (`RP_UNROLL_REGS`, `sift.c:466-472`, excluded); natural numbers for the `long`s `w`
and `off`. -/
def tailLeg (w off : Nat) {m : Nat} (surv : Vector UInt64 m) (base : Nat) (cw : UInt64)
    (sv : Array SieveSpec) : Id (Vector UInt64 m) := do
  let mut reg : Vector UInt64 (8 * rbaPack) := .replicate _ 0
  let s := sv[0]!
  for i in [0:w] do
    reg := loadBitArray reg i cw s.row (s.start + off + i)
  for q in [1:sv.size] do
    let s := sv[q]!
    for i in [0:w] do
      reg := andBitArray reg i s.row (s.start + off + i)
  let mut surv := surv
  for i in [0:w] do
    surv := storeBitArray surv (base + off + i) reg i
  return surv

/-- The tail of a piece of `n` bit arrays through the first stage, the `t = n - full` bit arrays
after the whole chunks, which end at `full`, fewer than `Ratpoints.chunk` of them: in legs of 8, 4,
2 and 1 bit arrays (`Ratpoints.Sieve.tailLeg`), one for each set bit of `t`, the widest first, each
from the part of `t` above its own bit on, `0`, `t &&& 8`, `t &&& 12` and `t &&& 14`, and the first
three only for a chunk above 8, 4 and 2, below which `t` cannot have that bit; from the starts of
the rows of the local sieve specs `sv` after the whole chunks, the first bit array of the tail being
`full`.

C: `sift.c:915-940`

Deviation: the conditions on the chunk tested with those on `t`, for the conditional compilation
`#if (RATPOINTS_CHUNK > 8)`, `> 4` and `> 2`; no check at compile time that the chunk is at most 16,
the `#error` of the C code, which its place inside the conditional compilation of the chunked first
stage for a chunk up to 16 makes dead code: a chunk above 16 compiles the first stage one row at a
time, and the model chooses the arm by the same test (`Ratpoints.Sieve.siftPiece`,
`Ratpoints.Sieve.andRows`); natural numbers for the `long`s. -/
def tailLegs (sv : Array SieveSpec) (cw : UInt64) (full n : Nat) {m : Nat}
    (surv : Vector UInt64 m) : Id (Vector UInt64 m) := do
  let t := n - full
  let mut surv := surv
  if 8 < chunk ∧ t &&& 8 ≠ 0 then surv ← tailLeg 8 0 surv full cw sv
  if 4 < chunk ∧ t &&& 4 ≠ 0 then surv ← tailLeg 4 (t &&& 8) surv full cw sv
  if 2 < chunk ∧ t &&& 2 ≠ 0 then surv ← tailLeg 2 (t &&& 12) surv full cw sv
  if t &&& 1 ≠ 0 then surv ← tailLeg 1 (t &&& 14) surv full cw sv
  return surv

/-- The first stage over a piece, the bit arrays with the word numbers `w0, …, w0 + n - 1`, which
are the first `n` bit arrays of `surv`, `Ratpoints.chunk` bit arrays at a time, the arm of
`_ratpoints_sift0` for a chunk from 2 to 16 (for the others, `Ratpoints.Sieve.andRows`): the local
sieve specs of the moduli of `specs`, with their reciprocals in `mgs`, and their starts at the word
number `w0` (`Ratpoints.Sieve.chunkStarts`, with the test `small` of the reduction); with no
modulus, each bit array set to the class word `cw` (`Ratpoints.Sieve.fillBitArray`), from the last;
otherwise the whole chunks, the bit arrays below `full = n - n mod chunk`
(`Ratpoints.Sieve.andChunks`), then the tail (`Ratpoints.Sieve.tailLegs`), so that bit array `j` is
the class word and-ed with bit array `(w0 + offset + j) mod p` of the row of each modulus `p` of
`specs`. The rows must have their copies of the first `chunk - 1` bit arrays after the first `p`.
The last bit array of `surv`, the place of the sentinel, is left as it is.

C: `sift.c:575`, `sift.c:608-620`, `sift.c:941`, `find_points.c:1098`, `rp-private.h:129-132`,
`rp-private.h:203-204`, `rp-private.h:235`, `rp-private.h:261`, `rp-private.h:285`

Deviation: no moduli tested by the size of the local array of the sieve specs, for `sp1 == 0`; the
bit arrays set to the class word by a loop that counts up, bit array `n - 1 - i` at the step `i`,
for the loop that counts down from the last; the class word written into each word of a bit array,
for the vector `RBA(packed)` that `get_2adic_info` makes once per class (`find_points.c:1098`) and
`_ratpoints_sift0` copies into each bit array (`bits64`, `sift.c:519`); the end of the whole chunks
the index `full`, for the word number `w_high_full`, which is also the index of the first bit array
of the tail, for the pointer `surv` after the chunks; natural numbers and integers for the
`long`s. -/
def andRowsChunked (specs : List SieveSpec) (mgs : List Nat) (small : Bool) (cw : UInt64)
    (w0 : Int) (n : Nat) (surv : Vector UInt64 ((n + 1) * rbaPack)) :
    Id (Vector UInt64 ((n + 1) * rbaPack)) := do
  let sv ← chunkStarts specs mgs small w0
  let mut surv := surv
  if sv.size = 0 then
    for i in [0:n] do
      surv := fillBitArray surv (n - 1 - i) cw
  else
    let full := n - n % chunk
    let (surv', sv) ← andChunks sv cw full surv
    surv ← tailLegs sv cw full n surv'
  return surv

/-! ### Examples -/

-- The operations on one bit array, on two bit arrays: `andBitArray` and-s bit array 1 with bit
-- array 2 of a row, word by word, `loadBitArray` sets it to the class word and-ed with that bit
-- array, `storeBitArray` sets bit array 0 to bit array 1 of the registers, `fillBitArray` sets bit
-- array 1 to the class word; the other bit array stays as it is.
#guard
  let v : Vector UInt64 (2 * rbaPack) := .ofFn fun i ↦ 0x0123456789abcdef * (i.val.toUInt64 + 1)
  let regs : Vector UInt64 (3 * rbaPack) := .ofFn fun i ↦ 0xfedcba9876543210 + i.val.toUInt64
  let row : Array UInt64 := .ofFn (n := 3 * rbaPack) fun i ↦ ~~~(1 <<< i.val.toUInt64)
  let cw : UInt64 := 0x5555aaaa5555aaaa
  (List.range (2 * rbaPack)).all fun y ↦
    (andBitArray v 1 row 2)[y]! ==
        (if y / rbaPack = 1 then v[y]! &&& row[rbaPack * 2 + y % rbaPack]! else v[y]!) &&
      (loadBitArray v 1 cw row 2)[y]! ==
        (if y / rbaPack = 1 then cw &&& row[rbaPack * 2 + y % rbaPack]! else v[y]!) &&
      (storeBitArray v 0 regs 1)[y]! ==
        (if y / rbaPack = 0 then regs[rbaPack + y % rbaPack]! else v[y]!) &&
      (fillBitArray v 1 cw)[y]! == if y / rbaPack = 1 then cw else v[y]!

-- The step back of a start by its modulus, at the end `p`: the remainder modulo `p`, for starts
-- below `p + 16`, where the start of a modulus below the chunk 16 steps back several times.
#guard [3, 5, 7, 13, 17, 67].all fun p ↦ (List.range (p + 16)).all fun st ↦
  Id.run (wrapStart st p p) == st % p

-- The legs over the tail (`Ratpoints.Sieve.tailLegs`), for every tail of `t < 16` bit arrays after
-- one whole chunk, on one modulus 17 whose row has the word `x + 1` in each word of bit array `x`,
-- read from the start 3 with the class word of all ones: bit arrays `16, …, 16 + t - 1` of the
-- survivors set from bit arrays `3, …, 3 + t - 1` of the row, in order, and the whole chunk and the
-- place of the sentinel left as they were, so that the legs cover the tail; the cover that the
-- proofs state as a lemma by `decide` over `t < 16`. The chunk 16 leaves out no leg.
#guard chunk == 16 && (List.range 16).all fun t ↦
  let row : Array UInt64 := .ofFn (n := (17 + chunk - 1) * rbaPack) fun j ↦
    (j.val / rbaPack).toUInt64 + 1
  let n := 16 + t
  let out := Id.run (tailLegs #[⟨17, 0, row, 3, 17⟩] (~~~0) 16 n
    (Vector.replicate ((n + 1) * rbaPack) 0))
  (List.range ((n + 1) * rbaPack)).all fun y ↦
    out.toArray[y]! == if 16 ≤ y / rbaPack ∧ y / rbaPack < n then (y / rbaPack - 16 + 4).toUInt64
      else 0

-- The chunked first stage against the first stage one row at a time, word for word, the place of
-- the sentinel included: the rows made of pseudo-random words, `p rbaPack` of them and then the
-- copies of the first `(chunk - 1) rbaPack`, read at offsets that are the biases of the moduli
-- plus shifts, with the reductions by the reciprocals (`small`) and by `mod`, and at offsets below
-- the moduli and word numbers far below zero, by `mod`, where the sum of the word number and the
-- offset is negative; pieces of every length from 1 to 40, so every tail of fewer than 16 bit
-- arrays, with no whole chunk, one and two, for the moduli 3, 5, 7, 11 and 13, below the chunk 16;
-- the moduli 17 and 3, 67, and 251 and 5 on some lengths; and no modulus, where both set every bit
-- array to the class word.
#guard
  let bias (p : Nat) : Nat := p * ((rowBias + p - 1) / p)
  let word (p j : Nat) : UInt64 :=
    let x := (p * 1000003 + j).toUInt64 * 0x9e3779b97f4a7c15
    x ^^^ x >>> 29 ||| x >>> 7
  let row (p : Nat) : Array UInt64 :=
    .ofFn (n := (p + chunk - 1) * rbaPack) fun j ↦ word p (j.val % (p * rbaPack))
  let agree (ps : List Nat) (off : Nat → Nat) (small : Bool) (w0 : Int) (n : Nat) : Bool :=
    let specs : List SieveSpec := ps.map fun p ↦ ⟨p, off p, row p, 0, p⟩
    let mgs := ps.map magic
    let surv : Vector UInt64 ((n + 1) * rbaPack) := .ofFn fun i ↦ i.val.toUInt64 * 0x1234567
    [~~~0, 0x0202020202020202].all fun cw ↦
      (Id.run (andRowsChunked specs mgs small cw w0 n surv)).toArray ==
        (Id.run (andRows specs mgs small cw w0 n surv)).toArray
  (List.range' 1 40).all (fun n ↦ agree [3, 5, 7, 11, 13] (fun p ↦ bias p + p - 1) true (-9) n &&
    agree [3, 5, 7, 11, 13] (fun p ↦ p - 2) false (-35) n && agree [] bias true 0 n) &&
  ([[17, 3], [67], [251, 5]] : List (List Nat)).all fun ps ↦
    ([(fun p ↦ bias p, true, 6), (fun p ↦ bias p + 2, false, -3000000000),
        (fun p ↦ p - 1, false, -7)] : List ((Nat → Nat) × Bool × Int)).all fun (off, sm, w0) ↦
      [1, 7, 16, 23, 37].all fun n ↦ [false, sm].all fun small ↦ agree ps off small w0 n

end Sieve

end Ratpoints

end
