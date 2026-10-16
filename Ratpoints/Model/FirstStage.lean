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
`RATPOINTS_CHUNK` (`Ratpoints.chunk`): for a chunk from 2 to 16, the chunked arm, which walks each
row with a start that it steps on by the chunk and back by the modulus and reads up to `chunk - 1`
bit arrays past the first `p` bit arrays of a row of the modulus `p`, which are copies of its first
ones, and which comes with stage F4; for the other chunks, the arm that and-s each row into the bit
arrays of the piece in three loops (`Ratpoints.Sieve.andRows`). Here are also the operations on bit
arrays of 64-bit words that the first stage uses, the bit arrays given by their indices in arrays of
words, and the sieve specs, a modulus with its row and its offset for the denominator at hand and
the start and the end of the walk of the chunked arm through the row (`Ratpoints.Sieve.SieveSpec`).

## Main definitions

* `Ratpoints.Sieve.andBitArray`, `Ratpoints.Sieve.fillBitArray`: the operations on bit arrays of the
  first stage, a bit array and-ed with one of a row, and set to the class word.
* `Ratpoints.Sieve.SieveSpec`: a modulus with its row, its offset and the start and the end of the
  walk of the chunked first stage through the row.
* `Ratpoints.Sieve.andRows`: the first stage over a piece, one row at a time, the arm of the builds
  with a chunk of 1 or above 16.
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
first stage (stage F4) reads the row from the bit array `start` on, which it sets at the first word
number of a piece and steps on by the chunk and back by `p` while it is at least the end `stop`,
which is `p` (`Ratpoints.Sieve.setRows`); the other stages read neither.

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
`Ratpoints.chunk` of 1 or above 16: the bit arrays are set to the class word `cw`
(`Ratpoints.Sieve.fillBitArray`), from the last, the pattern of the class of the denominator in its
packing (`Ratpoints.Sieve.NumClass`; bit `t` of every word stands for a numerator `a₀ + 2 ^ k t'`
with `t' ≡ t (mod 64)`, since `64` divides `Ratpoints.rbaLength`); then for each modulus `p` of
`specs` with its row and its offset, and its reciprocal `mg` from `mgs`, and for
`r = (-w0 - offset) mod p`, the remainder by a multiplication with `mg` (`Ratpoints.Sieve.modMul`)
when `small` says that the word numbers of the piece allow it and by the helper `mod` of the C code
otherwise (`Ratpoints.Sieve.modLong`), bit array `j` is and-ed with bit array
`(w0 + offset + j) mod p` of the row (`Ratpoints.Sieve.andBitArray`), in three loops: if `n < r`,
with the `n` bit arrays of the row from `p - r` on, and otherwise with the `r` bit arrays from
`p - r` on, then with whole periods of `p` bit arrays from `0`, then with the rest from `0`. It
reads only the first `p` bit arrays of a row. The last bit array of `surv`, the place of the
sentinel, is left as it is.

C: `sift.c:943-1022`, `find_points.c:1098`, `rp-private.h:129-132`, `rp-private.h:203-204`,
`rp-private.h:235`, `rp-private.h:261`, `rp-private.h:285`

Deviation: the first stage of the builds with one register per chunk, for the chunks of sixteen
registers of the default build with the legs over the tail of a piece (stage F4); the bit arrays set
to the class word by a loop that counts up, bit array `n - 1 - i` at the step `i`, for the loop that
counts down from the last; the class word written into each word of a bit array, for the vector
`RBA(packed)` that `get_2adic_info` makes once per class (`find_points.c:1098`) and
`_ratpoints_sift0` copies into each bit array (`bits64`, `sift.c:519`, `sift.c:954`); the moduli of
the stage with their rows and their reciprocals as two lists, for the first `sp1` sieve specs and
the array `magics` from position `0` on; the value `-w_low - offset` written out in both reductions,
for the `long` `a`, which stays a `long` where the helper `mod` reduces it outside `small`
(`Ratpoints.Sieve.fitsLong_neg_sub_and_fitsLong_add`); indices for the pointers into the rows and
into the survivors, and the number of whole periods and the rest computed before their loops;
natural numbers and integers for the `long`s; a Boolean for the `int` `small`; no output under
`DEBUG`. -/
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

/-! ### Examples -/

-- The operations on one bit array, on two bit arrays: `andBitArray` and-s bit array 1 with bit
-- array 2 of a row, word by word, and `fillBitArray` sets bit array 1 to the class word; the other
-- bit array stays as it is.
#guard
  let v : Vector UInt64 (2 * rbaPack) := .ofFn fun i ↦ 0x0123456789abcdef * (i.val.toUInt64 + 1)
  let row : Array UInt64 := .ofFn (n := 3 * rbaPack) fun i ↦ ~~~(1 <<< i.val.toUInt64)
  let cw : UInt64 := 0x5555aaaa5555aaaa
  (List.range (2 * rbaPack)).all fun y ↦
    (andBitArray v 1 row 2)[y]! ==
        (if y / rbaPack = 1 then v[y]! &&& row[rbaPack * 2 + y % rbaPack]! else v[y]!) &&
      (fillBitArray v 1 cw)[y]! == if y / rbaPack = 1 then cw else v[y]!

end Sieve

end Ratpoints

end
